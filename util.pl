% util.pl
:- module(util, [sub/4, claimsin/2, isclause/1, isatom/1, isweaker/4]).

:- use_module(library(clpfd)).

sub(X, T, X, T).

sub(D, _, X, D) :-
    atom(D),
    D \= X.

sub(uni(sort(Y, SSigma), D), _, X, uni(sort(Y, SSigma), D)) :-
    X == Y, !.

sub(uni(sort(Y, SSigma), D1), T, X, uni(sort(Y, SSigma), D2)) :-
    X \= Y,
    sub(D1, T, X, D2).

sub(D, T, X, DSub) :-
    D =.. [F|Args],
    maplist(sub_helper(T, X), Args, SubArgs),
    DSub =.. [F|SubArgs].

sub_helper(T, X, Arg, SubArg) :-
    sub(Arg, T, X, SubArg).


claimsin([], []).

claimsin([claims(K, D) | Tail], [claims(K, D) | Tailp]) :-
    claimsin(Tail, Tailp).

claimsin([Head | Tail], Tailp) :-
    \+ Head = claims(_, _),
    claimsin(Tail, Tailp).

	
isclause(V) :-
	(	isatom(V)
	;	V = sup(_, _)
	;	V = and(_, _)
	;	V = top
	;	V = uni(_, _)
	).

isatom(V) :- 
	(	V \= and(_, _)
	,	V \= or(_, _)
	, 	V \= sup(_, _)
	,	V \= top
	,	V \= bot
	, 	V \= uni(_, _)
	,	V \= exi(_, _)
	,	V \= says(_, _)
	,	V \= cert(_, _)
	).

apply_op(A, <, N) :- A #< N.
apply_op(A, <=, N) :- A #=< N.
apply_op(A, >, N) :- A #> N.
apply_op(A, >=, N) :- A #>= N.
apply_op(A, =, N) :- A #= N.
apply_op(A, \=, N) :- A #\= N.

isweaker(Op1, N1, Op2, N2) :-
    A in 0..18446744073709551615,  % adjust as needed
    apply_op(A, Op1, N1),
    \+ (label([A]), \+ apply_op(A, Op2, N2)).