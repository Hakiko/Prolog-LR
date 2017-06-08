startingSit(gramatyka(Start, _), situation('Z' , [], [nt(Start), '#'])).

remove(_, [], A, A).

remove(X, [X | L], A, R):-
	remove(X, L, A, R).

remove(X, [Y | L], A, R):-
	X \== Y,
	remove(X, L, [Y | A], R).

unique([], A, A).

unique([X | XS], A, R):-
	remove(X, A, [], AR),
	unique(XS, [X | AR], R).

%uniquePush(Element, Set, Result).
%push Element to the Set only if it's not already present
%store the result in Result
uniquePush(X, L, [X | L]):-
	\+ member(X, L).

uniquePush(X, L, L):-
	member(X, L).

closeOne(_, _, Sit, Accum, Accum):-
	Sit = situation(_, _, []).

closeOne(_, _, Sit, Accum, Accum):-
	Sit = situation(_, _, [S | _]),
	S \= nt(_).

closeOne(_, GT, Sit, Accum, Accum):-
	Sit = situation(_, _, [S | _]),
	S = nt(_),
	GT = gramatyka(_, []).

closeOne(G, GT, Sit, Accum, CSits):-
	Sit = situation(_, _, [S | _]),
	S = nt(NS),
	GT = gramatyka(B, [prod(PL, _) | Prods]),
	NS \= PL,
	closeOne(G, gramatyka(B, Prods), Sit, Accum, CSits).

closeOne(G, GT, Sit, Accum, CSits):-
	Sit = situation(_, _, [S | _]),
	S = nt(NS),
	GT = gramatyka(B, [prod(NS, []) | Prods]),
	closeOne(G, gramatyka(B, Prods), Sit, Accum, CSits).

closeOne(G, GT, Sit, Accum, CSits):-
	Sit = situation(_, _, [S | _]),
	S = nt(NS),
	GT = gramatyka(B, [prod(NS, [Right | Rights]) | Prods]),
	New = situation(NS, [], Right),
	member(New, Accum),
	closeOne(G, gramatyka(B, [prod(NS, Rights) | Prods]), Sit, Accum, CSits).

closeOne(G, GT, Sit, Accum, CSits):-
	Sit = situation(_, _, [S | _]),
	S = nt(NS),
	GT = gramatyka(B, [prod(NS, [Right | Rights]) | Prods]),
	New = situation(NS, [], Right),
	\+ member(New, Accum),
	closeOne(G, G, New, [New | Accum], NewCSits),
	closeOne(G, gramatyka(B, [prod(NS, Rights) | Prods]), Sit, NewCSits, CSits).

closureAux(_, [], Accum, Accum).

closureAux(G, [Sit | Sits], Accum, CSits):-
	closeOne(G, G, Sit, Accum, CSit),
	\+ member(Sit, CSit),
	closureAux(G, Sits, [Sit | CSit], CSits).

closureAux(G, [Sit | Sits], Accum, CSits):-
	closeOne(G, G, Sit, Accum, CSit),
	member(Sit, CSit),
	closureAux(G, Sits, CSit, CSits).

%true if CSits is a closure of Sits wrt the grammar G
closure(G, Sits, CSits):-
	closureAux(G, Sits, [], CSits).

%check if there is a situation in Sit which should be reduced
isReduce([Sit | _]):-
	Sit = situation(_, _, R),
	R == [].

isReduce([Sit | Sits]):-
	Sit = situation(_, _, R),
	R \== [],
	isReduce(Sits).

%check if the the situation set contains a reduce/reduce conflict
hasRRConflict([Sit | T]):-
	Sit = situation(_, _, R),
	R == [],
	isReduce(T).

hasRRConflict([Sit | T]):-
	Sit = situation(_, _, R),
	R \== [],
	hasRRConflict(T).

%symbols(Grammar, Accum, Result)
%generate all the symbols appearing in Grammar and store them in Result.
symbols(G, Accum, HAccum):-
	G = gramatyka(E, []),
	uniquePush(nt(E), Accum, EAccum),
	uniquePush('#', EAccum, HAccum).

symbols(G, Accum, Res):-
	G = gramatyka(B, [prod(S, []) | Prods]),
	uniquePush(nt(S), Accum, SAccum),
	symbols(gramatyka(B, Prods), SAccum, Res).

symbols(G, Accum, Res):-
	G = gramatyka(B, [prod(S, [[] | Rights]) | Prods]),
	symbols(gramatyka(B, [prod(S, Rights) | Prods]), Accum, Res).

symbols(G, Accum, Res):-
	G = gramatyka(B, [prod(S, [[Sym | Syms] | Rights]) | Prods]),
	uniquePush(Sym, Accum, SAccum),
	symbols(gramatyka(B, [prod(S, [Syms | Rights]) | Prods]), SAccum, Res).

%goto(Grammar, Set, Symbol, Result).
%calculate the value of GOTO[Set, Symbol] (as described in the lecture).
goto(G, Set, Sym, Res):-
	goto(G, Set, Sym, [], Res).

goto(G, [], _, Accum, CAccum):-
	closure(G, Accum, CAccum).

goto(G, [Sit | Sits], Sym, Accum, GSits):-
	Sit = situation(_, _, []),
	goto(G, Sits, Sym, Accum, GSits).

goto(G, [Sit | Sits], Sym, Accum, GSits):-
	Sit = situation(_, _, [NSym | _]),
	NSym \== Sym,
	goto(G, Sits, Sym, Accum, GSits).

goto(G, [Sit | Sits], Sym, Accum, GSits):-
	Sit = situation(L, M, [Sym | R]),
	New = situation(L, MS, R),
	append(M, [Sym], MS),
	uniquePush(New, Accum, NAccum),
	goto(G, Sits, Sym, NAccum, GSits).

%check if the situation set would generate a particular action
action_accept(_, Set, '#'):-
	Set = [Sit | _],
	Sit = situation(_, _, ['#']).

action_accept(G, Set, '#'):-
	Set = [Sit | Tail],
	Sit = situation(_, _, R),
	R \== ['#'],
	action_accept(G, Tail, '#').

%L and R store the left and right side of the production to reduce
action_reduce(G, Set, Sym, L, R):-
	Set = [Sit | Tail],
	Sit = situation(L, R, []),
	\+ action_reduce(G, Tail, Sym, _, _).

action_reduce(G, Set, Sym, L, R):-
	Set = [Sit | Tail],
	Sit = situation(_, _, R),
	R \== [],
	action_reduce(G, Tail, Sym, L, R).

%last argument stores the set which should be pushed onto the stack
action_shift(G, Set, Sym, CQ):-
	action_shift(G, Set, Sym, [], Q),
	Q = [_ | _],
	closure(G, Q, CQ).

action_shift(G, Set, Sym, Accum, Q):-
	Set = [Sit | Tail],
	Sit = situation(_, _, []),
	action_shift(G, Tail, Sym, Accum, Q).

action_shift(G, Set, Sym, Accum, Q):-
	Set = [Sit | Tail],
	Sit = situation(_, _, [NSym | _]),
	NSym \== Sym,
	action_shift(G, Tail, Sym, Accum, Q).

action_shift(_, [], _, Accum, Accum):-
	Accum = [_ | _].

action_shift(G, Set, Sym, Accum, Q):-
	Set = [Sit | Tail],
	Sit = situation(L, M, [Sym | T]),
	append(M, [Sym], MS),
	New = situation(L, MS, T),
	uniquePush(New, Accum, NAccum),
	action_shift(G, Tail, Sym, NAccum, Q).

action_error(_, Set, _, error('reduce/reduce conflict')):-
	hasRRConflict(Set).

action_error(G, Set, Sym, error('accept/reduce conflict')):-
	action_accept(G, Set, Sym),
	action_reduce(G, Set, Sym, _, _).

action_error(G, Set, Sym, error('shift/reduce conflict')):-
	action_reduce(G, Set, Sym, _, _),
	action_shift(G, Set, Sym, _).

action_syntax_error(G, Set, Sym):-
	\+ action_accept(G, Set, Sym),
	\+ action_shift(G, Set, Sym, _),
	\+ action_reduce(G, Set, Sym, _, _).

%pop the values from the stack for every symbol in the given rule
popStackRule(Stack, [], Stack).

popStackRule([_ | Stack], [_ | Rule], Result):-
	popStackRule(Stack, Rule, Result).

%walk through the parsing graph according to the LR(0) algorithm
walk(_, _, [], error('stack shouldnt be empty')).

walk(_, [], _, error('finished without accepting')).

walk(G, [Sym | _], [Top | _], error(Info)):-
	action_error(G, Top, Sym, error(Info)).

walk(G, [Sym | _], [Top | _], error('syntax error')):-
	\+ action_error(G, Top, Sym, _),
	action_syntax_error(G, Top, Sym).

walk(G, [Sym | _], [Top | _], yes):-
	\+ action_error(G, Top, Sym, _),
	\+ action_syntax_error(G, Top, Sym),
	action_accept(G, Top, Sym).

walk(G, [Sym | Word], [Top | Stack], Info):-
	\+ action_error(G, Top, Sym, _),
	\+ action_syntax_error(G, Top, Sym),
	action_shift(G, Top, Sym, Q),
	walk(G, Word, [Q, Top | Stack], Info).

walk(G, [Sym | Word], [Top | Stack], Info):-
	\+ action_error(G, Top, Sym, _),
	\+ action_syntax_error(G, Top, Sym),
	action_reduce(G, Top, Sym, L, R),
	popStackRule([Top | Stack], R, [Q | NStack]),
	goto(G, Q, nt(L), New),
	walk(G, [Sym | Word], [New, Q | NStack], Info).

%verifyAux, verify - DFS validator, checks every possible symbol for every state
%verifyAux(G, SymsAll, Syms, Current, Seen, Working, ResultSeen, Info),
%G - grammar
%SymsAll - set of all possible symbols in G
%Syms - symbols left to check for this state
%Current - the current situation
%Seen - set of all the checked states
%Working - set of all the states that have not yet finished verification
%ResultSeen - new value of Seen after the check
%Info - if there is a conflict then this argument will be filled with error(Info), yes otherwise.
verifyAux(_, _, [], Current, Seen, _, RSeen, yes):-
	\+ member(Current, Seen),
	RSeen = [Current | Seen].

verifyAux(_, _, _, Current, Seen, _, Seen, yes):-
	member(Current, Seen).

verifyAux(G, _, [Sym | _], Current, Seen, _, Seen, error(Info)):-
	\+ member(Current, Seen),
	action_error(G, Current, Sym, error(Info)).

verifyAux(G, SymsAll, [Sym | Syms], Current, Seen, Working, RSeen, Info):-
	\+ member(Current, Seen),
	\+ action_error(G, Current, Sym, _),
	action_accept(G, Current, Sym),
	verifyAux(G, SymsAll, Syms, Current, Seen, Working, RSeen, Info).

verifyAux(G, SymsAll, [Sym | Syms], Current, Seen, Working, RSeen, Info):-
	\+ member(Current, Seen),
	\+ action_error(G, Current, Sym, _),
	action_reduce(G, Current, Sym, _, _),
	verifyAux(G, SymsAll, Syms, Current, Seen, Working, RSeen, Info).

verifyAux(G, SymsAll, [Sym | Syms], Current, Seen, Working, RSeen, Info):-
	\+ member(Current, Seen),
	\+ action_error(G, Current, Sym, _),
	action_syntax_error(G, Current, Sym),
	verifyAux(G, SymsAll, Syms, Current, Seen, Working, RSeen, Info).

verifyAux(G, SymsAll, [Sym | _], Current, Seen, Working, RSeen, error(Info)):-
	\+ member(Current, Seen),
	\+ action_error(G, Current, Sym, _),
	action_shift(G, Current, Sym, Q),
	\+ member(Q, Working),
	verifyAux(G, SymsAll, SymsAll, Q, Seen, [Q | Working], RSeen, error(Info)).

verifyAux(G, SymsAll, [Sym | Syms], Current, Seen, Working, RSeen, Info):-
	\+ member(Current, Seen),
	\+ action_error(G, Current, Sym, _),
	action_shift(G, Current, Sym, Q),
	\+ member(Q, Working),
	verifyAux(G, SymsAll, SymsAll, Q, Seen, [Q | Working], TSeen, yes),
	verifyAux(G, SymsAll, Syms, Current, TSeen, Working, RSeen, Info).

verifyAux(G, SymsAll, [Sym | Syms], Current, Seen, Working, RSeen, Info):-
	\+ member(Current, Seen),
	\+ action_error(G, Current, Sym, _),
	action_shift(G, Current, Sym, Q),
	member(Q, Working),
	verifyAux(G, SymsAll, Syms, Current, Seen, Working, RSeen, Info).

%check the grammar for conflicts
verify(Grammar, Info):-
	startingSit(Grammar, S),
	closure(Grammar, [S], CS),
	symbols(Grammar, [], Syms),
	verifyAux(Grammar, Syms, Syms, CS, [], [CS], _, Info).

createLR(Gramatyka, Gramatyka, yes):-
	verify(Gramatyka, yes).

createLR(Gramatyka, null, error(Info)):-
	verify(Gramatyka, error(Info)).

accept(Gramatyka, Slowo):-
	startingSit(Gramatyka, Starter),
	closure(Gramatyka, [Starter], CStarter),
	Stack = [CStarter],
	append(Slowo, ['#'], HSlowo),
	walk(Gramatyka, HSlowo, Stack, yes).