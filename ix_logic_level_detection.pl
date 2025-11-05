% =========================================================================
% LOGIC LEVEL DETECTION - Analyse holophrastique (Quine)
% Détection automatique : calcul propositionnel vs. calcul des prédicats
% =========================================================================

:- dynamic formula_level/1.

% =========================================================================
% DÉTECTION PRINCIPALE
% =========================================================================

detect_and_set_logic_level(Formula) :-
    retractall(formula_level(_)),
    ( is_fol_formula(Formula) ->
        assertz(formula_level(fol))
    ;
        assertz(formula_level(propositional))
    ).

% =========================================================================
% HEURISTIQUES DE DÉTECTION FOL
% Une formule est FOL si elle contient :
% - Des quantificateurs (∀, ∃)
% - Des applications de prédicats p(t1,...,tn) avec n > 0
% - Des égalités entre termes
% - Des fonctions de Skolem
% =========================================================================

is_fol_formula(Formula) :-
    (   contains_quantifier(Formula)
    ;   contains_predicate_application(Formula)  
    ;   contains_equality(Formula)
    ;   contains_function_symbol(Formula)
    ), !.

% =========================================================================
% DÉTECTION DES COMPOSANTS
% =========================================================================

% Quantificateurs
contains_quantifier(![_-_]:_) :- !.
contains_quantifier(?[_-_]:_) :- !.
contains_quantifier(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    contains_quantifier(Arg).


% Applications de prédicats (termes composés qui ne sont pas des connecteurs)
contains_predicate_application(Term) :-
    compound(Term),
    \+ is_logical_connective_structure(Term),
    Term =.. [_F|Args],
    Args \= [],  % Doit avoir au moins un argument
    !.
contains_predicate_application(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    contains_predicate_application(Arg).

% Structures de connecteurs logiques (à exclure)
is_logical_connective_structure(_ => _).
is_logical_connective_structure(_ & _).
is_logical_connective_structure(_ | _).
is_logical_connective_structure(_ <=> _).
is_logical_connective_structure(_ = _).  % Égalité traitée séparément
is_logical_connective_structure(~ _).
is_logical_connective_structure(#).
is_logical_connective_structure(![_-_]:_).
is_logical_connective_structure(?[_-_]:_).

% Égalité
contains_equality(_ = _) :- !.
contains_equality(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    contains_equality(Arg).

% Fonctions de Skolem
contains_function_symbol(f_sk(_,_)) :- !.
contains_function_symbol(Term) :-
    compound(Term),
    Term =.. [_|Args],
    member(Arg, Args),
    contains_function_symbol(Arg).

% =========================================================================
% EXTRACTION DE LA FORMULE DEPUIS UNE PREUVE G4
% =========================================================================

extract_formula_from_proof(Proof, Formula) :-
    Proof =.. [_RuleName, Sequent|_],
    ( Sequent = (_ > [Formula]) -> 
        true
    ; Sequent = (_ > Goals), Goals = [Formula|_] -> 
        true
    ; 
        Formula = unknown
    ).
