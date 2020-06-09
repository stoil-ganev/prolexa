%:- module(prolexa_engine,
%	[
%		prove_question/3,		% main question-answering engine
%		explain_question/3,		% extended version that constructs a proof tree
%		known_rule/2,			% test if a rule can be deduced from stored rules
%		all_rules/1,			% collect all stored rules 
%		all_answers/2,			% everything that can be proved about a particular Proper Noun
%	]).

:- consult(library).


%%% Main question-answering engine adapted from nl_shell.pl %%%

prove_question(Query,SessionId,Answer):-
	findall(R,prolexa:stored_rule(SessionId,R),Rulebase),
	( prove_rb(Query,Rulebase) ->
		transform(Query,Clauses),
		phrase(sentence(Clauses),AnswerAtomList),
		atomics_to_string(AnswerAtomList," ",Answer)
	; Answer = 'Sorry, I don\'t think this is the case'
	).	

% two-argument version that can be used in maplist/3 (see all_answers/2)
prove_question(Query,Answer):-
	findall(R,prolexa:stored_rule(_SessionId,R),Rulebase),
	( prove_rb(Query,Rulebase) ->
		transform(Query,Clauses),
		phrase(sentence(Clauses),AnswerAtomList),
		atomics_to_string(AnswerAtomList," ",Answer)
	; Answer = ""
	).	


%%% Extended version of prove_question/3 that constructs a proof tree %%%
explain_question(Query,SessionId,Answer):-
	findall(R,prolexa:stored_rule(SessionId,R),Rulebase),
	( prove_rb(Query,Rulebase,[],Proof) ->
		maplist(pstep2message,Proof,Msg),
		phrase(sentence1([(Query:-true)]),L),
		atomic_list_concat([therefore|L]," ",Last),
		append(Msg,[Last],Messages),
		atomic_list_concat(Messages,"; ",Answer)
	; Answer = 'Sorry, I don\'t think this is the case'
	).

% convert proof step to message
pstep2message(p(_,Rule),Message):-
	rule2message(Rule,Message).
pstep2message(n(Fact),Message):-
	rule2message([(Fact:-true)],FM),
	atomic_list_concat(['It is not known that',FM]," ",Message).


%%% test if a rule can be deduced from stored rules %%%
known_rule([Rule],SessionId):-
	findall(R,prolexa:stored_rule(SessionId,R),Rulebase),
	try((numbervars(Rule,0,_),
	     Rule=(H:-B),
	     add_body_to_rulebase(B,Rulebase,RB2),
	     prove_rb(H,RB2)
	   )).

counterfactual_statement(Int, [Rule], SessionId, Answer):-
    phrase(sentence1([Rule]), RuleS),
	findall(R,prolexa:stored_rule(SessionId,R),RB),
	( interventions(Int, RB, DoRB) ->
        Rule=(H:-B),
        add_body_to_rulebase(B, DoRB, RBFinal),
        ( prove_rb(H, RBFinal) ->
            atomic_list_concat(["Yes, it would be the case that"|RuleS]," ",Answer)
        ; otherwise ->
            atomic_list_concat(["No, it would not be the case that"|RuleS]," ",Answer)
        )
    ; Answer = "The provided assumptions are inconsistent with what I know, so it would not be the case"
    ).


contradicting_rule([Rule],SessionId, Answer):-
	findall(R,prolexa:stored_rule(SessionId,R),Rulebase),
    ( contradiction(Rule, Rulebase, Proof) ->
        maplist(pstep2message,Proof,Msg),
        negate_rule(Rule, NRule),
        phrase(sentence1([NRule]),L),
        append(["False,"|L], ["because I know that"], Pre),
        atomic_list_concat(Pre," ",First),
        append([First], Msg ,Messages),
        atomic_list_concat(Messages,"; ",Answer)
    ; false
    ).

inconsistent_rule([Rule],SessionId, Answer):-
	findall(R,prolexa:stored_rule(SessionId,R),Rulebase),
    ( inconsistency(Rule, Rulebase, Imp, P1, P2) ->
        maplist(pstep2message,P1,Msg1),
        maplist(pstep2message,P2,Msg2),
        negate_rule(Rule, NRule),
        phrase(potential([NRule]),NRuleS),
        phrase(sentence1([Imp]),ImpS),
        append(["False,"|NRuleS], ["because otherwise it would imply that"|ImpS], Pre),
        append(Pre, [", since "], Pre2),
        atomic_list_concat(Pre2," ",First),
        append([First], Msg1 ,Messages1),
        atomic_list_concat(Messages1,"; ",Part1),
        append([Part1], [". However"], Pre3),
        atomic_list_concat(Pre3," ",Second),
        append([Second], Msg2, Messages2),
        atomic_list_concat(Messages2,"; ",Answer)
    ; false
    ).

negate_rule((not(H):-B), (H:-B)).
negate_rule((H:-B), (not(H):-B)).

add_body_to_rulebase((A,B),Rs0,Rs):-!,
	add_body_to_rulebase(A,Rs0,Rs1),
	add_body_to_rulebase(B,Rs1,Rs).
add_body_to_rulebase(A,Rs0,[[(A:-true)]|Rs0]).


%%% meta-interpreter that constructs proofs %%%

% 3d argument is accumulator for proofs
prove_rb(true,_Rulebase,P,P):-!.
prove_rb((A,A),_Rulebase,P,P):-!.
prove_rb((A,B),Rulebase,P0,P):-!,
	find_clause((A:-C),Rule,Rulebase),
	conj_append(C,B,D),
    prove_rb(D,Rulebase,[p((A,B),Rule)|P0],P).
prove_rb(A,Rulebase,P0,P):-
    find_clause((A:-B),Rule,Rulebase),
	prove_rb(B,Rulebase,[p(A,Rule)|P0],P).

% top-level version that ignores proof
prove_rb(Q,RB):-
	prove_rb(Q,RB,[],_P).

contradiction((not(H):-B), RB, P):-!,
    prove_rb((H,B), RB, [], P).
contradiction((H:-B), RB, P):-
    prove_rb((not(H),B), RB, [], P).

contradiction(Q, RB):-
    contradiction(Q, RB, _P).


inconsistency((H:-B), RB, (H:-B), [ p(H,[(H:-B)]) ], P2):-
    \+ find_clause((_A:-H),_Rule, [ [(H:-B)]  | RB ]),
    contradiction((H:-B), RB, P2).
inconsistency((H:-B), RB, Imp, [ p((A),[(A:-H)]) | P1 ], P2):-
	find_clause((A:-H),_Rule, [[(H:-B)]|RB]),
    inconsistency((A:-B), RB, Imp, P1, P2).


interventions([[Int]|Ints], RB, DoRB):-
    remove_clause(Int, RB, RB2),
    \+ inconsistency(Int, RB2, _, _, _),
    interventions(Ints, [[Int]|RB2], DoRB).
interventions([], DoRB, DoRB).

remove_clause(Clause, Rules, DoRules):-
    negate_rule(Clause, NClause),
    remove_clause(Clause, NClause, Rules, DoRules).

remove_clause(Clause, NClause, [[Rule]|Rules], Rules):-
    copy_term(Rule,Clause);copy_term(Rule,NClause).
remove_clause(Clause, NClause, [Rule|Rules], [Rule|DoRules]):-
	remove_clause(Clause, NClause, Rules, DoRules).
remove_clause(_Clause, _NClause, [], []).

%%% Utilities from nl_shell.pl %%%

find_clause(Clause,Rule,[Rule|_Rules]):-
	copy_term(Rule,[Clause]).	% do not instantiate Rule
find_clause(Clause,Rule,[_Rule|Rules]):-
	find_clause(Clause,Rule,Rules).

% transform instantiated, possibly conjunctive, query to list of clauses
transform((A,B),[(A:-true)|Rest]):-!,
    transform(B,Rest).
transform(A,[(A:-true)]).


%%% Two more commands: all_rules/1 and all_answers/2

% collect all stored rules 
all_rules(Answer):-
	findall(R,prolexa:stored_rule(_ID,R),Rules),
	maplist(rule2message,Rules,Messages),
	( Messages=[] -> Answer = "I know nothing"
	; otherwise -> atomic_list_concat(Messages,". ",Answer)
	).

% convert rule to sentence (string)
rule2message(Rule,Message):-
	phrase(sentence1(Rule),Sentence),
	atomics_to_string(Sentence," ",Message).

% collect everything that can be proved about a particular Proper Noun
all_answers(PN,Answer):-
	findall(Q,(pred(P,1,_),Q=..[P,PN]),Queries), % collect known predicates from grammar
	maplist(prove_question,Queries,Msg),
	delete(Msg,"",Messages),
	( Messages=[] -> atomic_list_concat(['I know nothing about',PN],' ',Answer)
	; otherwise -> atomic_list_concat(Messages,". ",Answer)
	).


