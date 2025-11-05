% =========================================================================
% TRADUCTION DU BICONDITIONNELLE INTERNE
% A <=> B devient (A => B) & (B => A)
% =========================================================================

subst_bicond(A <=> B, (A1 => B1) & (B1 => A1)) :-
    !,
    subst_bicond(A, A1),
    subst_bicond(B, B1).

% Quantificateurs : passer récursivement dans le corps
subst_bicond(![Z-X]:A, ![Z-X]:A1) :-
        !,
        subst_bicond(A, A1).

subst_bicond(?[Z-X]:A, ?[Z-X]:A1) :-
        !,
        subst_bicond(A, A1).

% Connecteurs propositionnels
subst_bicond(A & B, A1 & B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(A | B, A1 | B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(A => B, A1 => B1) :-
        !,
        subst_bicond(A, A1),
        subst_bicond(B, B1).

subst_bicond(~A, ~A1) :-
        !,
        subst_bicond(A, A1).

% Cas de base : formules atomiques
subst_bicond(A, A).

% =========================================================================
% SUBSTITUTION DE LA NÉGATION (prétraitement)
% =========================================================================
/*
% Quantificateurs : traiter le corps uniquement
% --- cas spécial : négation d'un existentiel ---
% ~ ( ?(:([Z],A)) )   ==>   !(:([Z], ~A))
subst_neg(~( ?(:([Z],A)) ), !(:([Z],NA))) :-
    !,
    subst_neg(~A, NA).
*/

% Double négation
subst_neg(~ ~A, ((A1 => #) => #)) :-
        !,
        subst_neg(A, A1).

% Négation simple
subst_neg(~A, (A1 => #)) :-
        !,
        subst_neg(A, A1).


subst_neg(![Z-X]:A, ![Z-X]:A1) :-
        !,
        subst_neg(A, A1).

subst_neg(?[Z-X]:A, ?[Z-X]:A1) :-
        !,
        subst_neg(A, A1).

% Conjonction
subst_neg(A & B, A1 & B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Disjonction
subst_neg(A | B, A1 | B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Implication
subst_neg(A => B, A1 => B1) :-
        !,
        subst_neg(A, A1),
        subst_neg(B, B1).

% Biconditionnelle
subst_neg(A <=> B, A1 <=> B1) :-
    !,
    subst_neg(A, A1),
    subst_neg(B, B1).

% Cas de base : formules atomiques et constantes (#, prédicats, etc.)
subst_neg(A, A).
