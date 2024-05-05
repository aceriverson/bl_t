% seq.pl
:- [util].

%% R sequents

r_atom(Sigma, [], Delta, K, P) :- 
	isatom(P), 
	saturate(Sigma, [], Delta, Omegap, Deltap), 
	n(Sigma, Omegap, Deltap, K, P).
r_atom(Sigma, Omega, Delta, K, P) :- isatom(P), n(Sigma, Omega, Delta, K, P).
r_says(Sigma, Omega, Delta, _, says(K, G)) :- 
	claimsin(Delta, Deltap), 
	r(Sigma, Omega, Deltap, K, G).
r_and(Sigma, Omega, Delta, K, and(G, Gp)) :- 
	r(Sigma, Omega, Delta, K, G), 
	r(Sigma, Omega, Delta, K, Gp).
r_or1(Sigma, Omega, Delta, K, or(G, _)) :- r(Sigma, Omega, Delta, K, G).
r_or2(Sigma, Omega, Delta, K, or(_, Gp)) :- r(Sigma, Omega, Delta, K, Gp).
r_top(_, _, _, _, top).
r_sup(Sigma, Omega, Delta, K, sup(H, Gp)) :- l(Sigma, Omega, Delta, K, H, Gp).
r_uni(Sigma, Omega, Delta, K, uni(sort(X, SSigma), G)) :- 
	r([sort(X, SSigma) | Sigma], Omega, Delta, K, G).
r_exi(Sigma, Omega, Delta, K, exi(sort(X, SSigma), G)) :- 
	sub(G, T, X, Gp), r(Sigma, Omega, Delta, K, Gp), 
	member(sort(T, SSigma), Sigma).

r(Sigma, Omega, Delta, K, G) :- 
	(	r_atom(Sigma, Omega, Delta, K, G)
	;	r_says(Sigma, Omega, Delta, K, G)
	;	r_and(Sigma, Omega, Delta, K, G)
	;	r_or1(Sigma, Omega, Delta, K, G)
	;	r_or2(Sigma, Omega, Delta, K, G)
	;	r_top(Sigma, Omega, Delta, K, G)
	;	r_sup(Sigma, Omega, Delta, K, G)
	;	r_uni(Sigma, Omega, Delta, K, G)
	;	r_exi(Sigma, Omega, Delta, K, G)
	).


%% L sequents

l_tor(Sigma, Omega, Delta, [], K, G) :- r(Sigma, Omega, Delta, K, G).
l_pr(Sigma, Omega, Delta, Xi, K, G) :- 
	select(D, Xi, Xip), isclause(D), 
	l(Sigma, Omega, [D | Delta], Xip, K, G).
l_says(Sigma, Omega, Delta, Xi, K0, G) :- 
	select(says(K, D), Xi, Xip), 
	l(Sigma, Omega, [claims(K, D) | Delta], Xip, K0, G).
l_cert(Sigma, Omega, Delta, Xi, K0, G) :- 
	select(cert(K, D), Xi, Xip), 
	l(Sigma, Omega, [claims(K, D) | Delta], Xip, K0, G).
l_and(Sigma, Omega, Delta, Xi, K, G) :- 
	select(and(H, Hp), Xi, Xip), 
	l(Sigma, Omega, Delta, [H, Hp | Xip], K, G).
l_or(Sigma, Omega, Delta, Xi, K, G) :- 
	select(or(H, Hp), Xi, Xip), 
	l(Sigma, Omega, Delta, [H | Xip], K, G),
	 l(Sigma, Omega, Delta, [Hp | Xip], K, G).
l_top(Sigma, Omega, Delta, Xi, K, G) :- 
	select(top, Xi, Xip), 
	l(Sigma, Omega, Delta, Xip, K, G).
l_bot(_, _, _, Xi, _, _) :- select(bot, Xi, _).
l_exi(Sigma, Omega, Delta, Xi, K, G) :- 
	select(exi(sort(x, SSigma), H), Xi, Xip), 
	l([sort(x, SSigma) | Sigma], Omega, Delta, [H | Xip], K, G).

l(Sigma, Omega, Delta, Xi, K, G) :-
	(	l_tor(Sigma, Omega, Delta, Xi, K, G)
	;	l_pr(Sigma, Omega, Delta, Xi, K, G)
	;	l_says(Sigma, Omega, Delta, Xi, K, G)
	;	l_cert(Sigma, Omega, Delta, Xi, K, G)
	;	l_and(Sigma, Omega, Delta, Xi, K, G)
	;	l_or(Sigma, Omega, Delta, Xi, K, G)
	;	l_top(Sigma, Omega, Delta, Xi, K, G)
	;	l_bot(Sigma, Omega, Delta, Xi, K, G)
	;	l_exi(Sigma, Omega, Delta, Xi, K, G)
	).


%% F sequents

f_init(_, P, P, []).
f_ineq(_, D, P, []) :- 
	D =.. [OP1, A, N1], 
	P =.. [OP2, A, N2], isweaker(OP1, N1, OP2, N2).
f_and1(Sigma, and(D1, _), P, G) :- f(Sigma, D1, P, G).
f_and2(Sigma, and(_, D2), P, G) :- f(Sigma, D2, P, G).
f_sup(Sigma, sup(G1, D2), P, [G1 | G]) :- f(Sigma, D2, P, G).
f_uni(Sigma, uni(sort(X, SSigma), D), P, G) :- 
	member(sort(T, SSigma), Sigma), 
	sub(D, T, X, Dp), 
	f(Sigma, Dp, P, G).

f(Sigma, D, P, G) :-
	(	f_init(Sigma, D, P, G) 
	;	f_and1(Sigma, D, P, G) 
	;	f_and2(Sigma, D, P, G) 
	;	f_sup(Sigma, D, P, G) 
	;	f_uni(Sigma, D, P, G) 
	;	f_ineq(Sigma, D, P, G)
	).


%% N sequents

n_b1(Sigma, Omega, Delta, K, P) :- 
	member(D, Delta), 
	f(Sigma, D, P, G), 
	forall(member(Gi, G), r(Sigma, Omega, Delta, K, Gi)).
n_b2(Sigma, Omega, Delta, K0, P) :- 
	member(claims(K, D), Delta), 
	member(sf(K, K0), Omega), 
	f(Sigma, D, P, G), 
	forall(member(Gi, G), r(Sigma, Omega, Delta, K0, Gi)).

n(Sigma, Omega, Delta, K, P) :-
	(	n_b1(Sigma, Omega, Delta, K, P)
	;	n_b2(Sigma, Omega, Delta, K, P)
	).


saturate(Sigma, Omega, Delta, Omegap, Deltap) :-
    saturate_fixpoint(Sigma, Omega, Delta, Omegap, Deltap).

saturate_fixpoint(Sigma, Omega, Delta, Omegapp, Deltapp) :-
    saturate_iteration(Sigma, Omega, Delta, Omegap, Deltap),
    (   (Omega == Omegap, Delta == Deltap)
    ->  (Omegapp = Omegap, Deltapp = Deltap)
    ;   saturate(Sigma, Omegap, Deltap, Omegapp, Deltapp)
    ).

saturate_iteration(Sigma, Omega, Delta, Omegapppp, Deltapp) :-
	findall(sf(X, X), member(claims(X, _), Delta), PrincipalsList),
	list_to_set(PrincipalsList, Principals),
	append(Omega, Principals, Omegap),

	findall(sf(Y, X), member(claims(X, sf(Y, X)), Delta), SFClaimsList),
	list_to_set(SFClaimsList, SFClaims),
	append(Omegap, SFClaims, Omegapp),

	findall(sf(X, Y), 
			(member(X, Principals), member(Y, Principals)), SFCombinations),
	findall(sf(X, Y),
            (member(sf(X, Y), SFCombinations), 
            	n(Sigma, Omegapp, Delta, Y, sf(X, Y))),
            SuccessfulSFCombinations),
	append(Omegapp, SuccessfulSFCombinations, OmegapppList),
	list_to_set(OmegapppList, Omegappp),

	findall(sf(A, C), 
            (member(sf(A, B), Omegappp), member(sf(B, C), Omegappp), A \= C),
            SFTransList),
	append(Omegappp, SFTransList, OmegappppList),
	list_to_set(OmegappppList, Omegapppp),

	findall(claims(A, sf(B, A)), member(sf(B, A), Omegapppp), SFClaimsForDelta),
	append(Delta, SFClaimsForDelta, Deltap),
	list_to_set(Deltap, Deltapp).


prove(Sigma, Theta, Gamma, P) :- 
	append(Theta, Gamma, Xi), 
	l(Sigma, [], [], Xi, 0, P).