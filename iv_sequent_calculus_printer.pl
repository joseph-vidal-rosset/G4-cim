% =========================================================================
% G4 PRINTER SPÉCIALISÉ POUR BUSSPROOFS
% Rendu LaTeX optimisé pour les règles G4 authentiques
% =========================================================================

:- use_module(library(lists)).

% Directive pour éviter les warnings
:- discontiguous render_bussproofs/3.

% =========================================================================
% G4 rules 
% =========================================================================

% 1. Ax.
render_bussproofs(ax(Seq, _), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $Ax.$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% 2. L0→ 
render_bussproofs(l0cond(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $L0\\to$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 3. L∧→ 
render_bussproofs(landto(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $L\\land\\to$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% DNE_m : Double Negation Elimination (minimal)

% DNE_m : Double Negation Elimination (Slaney)
render_bussproofs(dne_m(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $DNE_m$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

render_bussproofs(tne(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $R \\to$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 4. L∨→ : Disjonction vers implication
render_bussproofs(lorto(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $L\\lor\\to$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.


% L∃∨ 
render_bussproofs(lex_lor(Seq, P1, P2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P1, VarCounter, Temp1),
    render_bussproofs(P2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize $L\\exists\\lor$}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% 5. L∧ 
render_bussproofs(land(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $L\\land$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 6. L∨ 
render_bussproofs(lor(Seq, P1, P2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P1, VarCounter, Temp1),
    render_bussproofs(P2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize $L\\lor$}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% 7. R→
render_bussproofs(rcond(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $R\\to$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 8. R∨ 
render_bussproofs(ror(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $R\\lor$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 9. L→→ 
render_bussproofs(ltoto(Seq, P1, P2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P1, VarCounter, Temp1),
    render_bussproofs(P2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize $L\\to\\to$}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% 10. R∧ 
render_bussproofs(rand(Seq, P1, P2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P1, VarCounter, Temp1),
    render_bussproofs(P2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize $R\\land$}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% 11. L⊥
render_bussproofs(lbot(Seq, _), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $L\\bot$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% IP : Indirect proof (avec détection DNE_m)
render_bussproofs(ip(Seq, P), VarCounter, FinalCounter) :-
    !,
    Seq = (_ > [Goal]),
    render_bussproofs(P, VarCounter, TempCounter),
    ( Goal = (_ => #) ->
        write('\\RightLabel{\\scriptsize $DNE_m$}'), nl
    ;
        write('\\RightLabel{\\scriptsize $IP$}'), nl
    ),
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% =========================================================================
% RÈGLES DE QUANTIFICATION FOL
% =========================================================================

% 12. R∀ : Quantificateur universel à droite
render_bussproofs(rall(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $R\\forall$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 13. L∃ : Quantificateur existentiel à gauche
render_bussproofs(lex(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $L\\exists$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 14. R∃ : Quantificateur existentiel à droite
render_bussproofs(rex(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $R\\exists$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% 15. L∀ : Quantificateur universel à gauche
render_bussproofs(lall(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $L\\forall$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% =========================================================================
% RÈGLES LK CLASSIQUES (si présentes)
% =========================================================================

% L→ classique (si utilisé)
render_bussproofs(lcond(Seq, P1, P2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P1, VarCounter, Temp1),
    render_bussproofs(P2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize $L\\to$}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

/*
% L<=> : Biconditionnelle à gauche (élimination)
render_bussproofs(lbicond(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $L\\leftrightarrow$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% R<=> : Biconditionnelle à droite (introduction - branchante)
render_bussproofs(rbicond(Seq, P1, P2), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P1, VarCounter, Temp1),
    render_bussproofs(P2, Temp1, Temp2),
    write('\\RightLabel{\\scriptsize $R\\leftrightarrow$}'), nl,
    write('\\BinaryInfC{$'),
    render_sequent(Seq, Temp2, FinalCounter),
    write('$}'), nl.

% L<=> variante 3 : Substitution dans prédicats
render_bussproofs(lbicond_subst(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $L\\Leftrightarrow_{subst}$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.
*/

% CQ_c : Règle de conversion classique (∀x:A => B) => ∃x:(A => B)
render_bussproofs(cq_c(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $CQ_c$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% CQ_m : Règle de conversion minimale (∃x:A => B) => ∀x:(A => B)
render_bussproofs(cq_m(Seq, P), VarCounter, FinalCounter) :-
    !,
    render_bussproofs(P, VarCounter, TempCounter),
    write('\\RightLabel{\\scriptsize $CQ_m$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, TempCounter, FinalCounter),
    write('$}'), nl.

% AJOUTEZ après les règles de quantification (ligne ~150)

% REMPLACEZ toutes les règles d'égalité (ligne ~150) par :

% =========================================================================
% RÈGLES D'ÉGALITÉ - VERSION CORRIGÉE
% =========================================================================

% Réflexivité : Seq = [t = t] (pas de tuple)
render_bussproofs(eq_refl(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $Refl$}'), nl,
    write('\\UnaryInfC{$'),
    write(' \\vdash '),
    ( Seq = [Goal] -> 
        rewrite(Goal, VarCounter, FinalCounter, GoalLatex),
        write(GoalLatex)
    ;
        render_sequent(Seq, VarCounter, FinalCounter)
    ),
    write('$}'), nl.

% Symétrie
render_bussproofs(eq_sym(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $Sym$}'),  nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Transitivité simple
render_bussproofs(eq_trans(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $Trans$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Transitivité chaînée
render_bussproofs(eq_trans_chain(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $Trans^*$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Congruence
render_bussproofs(eq_cong(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $Cong$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Substitution dans égalité
render_bussproofs(eq_subst_eq(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $Subst_{eq}$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Substitution (Leibniz)
render_bussproofs(eq_subst(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $Leibniz$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% Substitution pour équivalence logique
render_bussproofs(equiv_subst(Seq), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $\\equiv$}'), nl,
    write('\\UnaryInfC{$'),
    render_sequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.

% =========================================================================
% RÈGLE D'ÉCHEC
% =========================================================================
/*
% Antiséquent : échec de preuve
render_bussproofs(asq(Seq, _), VarCounter, FinalCounter) :-
    !,
    write('\\AxiomC{}'), nl,
    write('\\RightLabel{\\scriptsize $Asq.$}'), nl,
    write('\\UnaryInfC{$'),
    render_antisequent(Seq, VarCounter, FinalCounter),
    write('$}'), nl.
*/
% =========================================================================
% RENDU DES SÉQUENTS
% =========================================================================

% Séquent normal : Γ ⊢ Δ
% Filtre ⊤ (représenté comme (# => #) ou ~ #) de Γ pour l'affichage
% Utilise premise_list si disponible pour afficher les prémisses originales
/*
render_sequent(G > D, VarCounter, FinalCounter) :-
    % Vérifier si on a une liste de prémisses originale
    ( premise_list(OriginalPremises), OriginalPremises = [_|_] ->
        % Utiliser la liste originale au lieu de décomposer la conjonction
        filter_top_from_gamma(OriginalPremises, FilteredG)
    ;
        % Comportement normal : filtrer ⊤ de G
        filter_top_from_gamma(G, FilteredG)
    ),
    ( FilteredG = [] ->
        % Théorème : pas de prémisses à afficher
        write(' \\vdash '),
        TempCounter = VarCounter
    ;
        % Séquent avec prémisses
        render_formula_list(FilteredG, VarCounter, TempCounter),
        write(' \\vdash ')
    ),
    ( D = [] ->
        write('\\bot'),
        FinalCounter = TempCounter
    ;
        render_formula_list(D, TempCounter, FinalCounter)
    ).
*/
% Séquent normal : Γ ⊢ Δ
% Filtre ⊤ (représenté comme (# => #) ou ~ #) de Γ pour l'affichage
render_sequent(G > D, VarCounter, FinalCounter) :-
    % TOUJOURS utiliser G du séquent, PAS premise_list !
    filter_top_from_gamma(G, FilteredG),
    
    ( FilteredG = [] ->
        % Théorème : pas de prémisses à afficher
        write(' \\vdash '),
        TempCounter = VarCounter
    ;
        % Séquent avec prémisses
        render_formula_list(FilteredG, VarCounter, TempCounter),
        write(' \\vdash ')
    ),
    ( D = [] ->
        write('\\bot'),
        FinalCounter = TempCounter
    ;
        render_formula_list(D, TempCounter, FinalCounter)
    ).


% filter_top_from_gamma/2: Enlève ⊤ (top) de la liste de prémisses
filter_top_from_gamma([], []).
filter_top_from_gamma([H|T], Filtered) :-
    ( is_top_formula(H) ->
        filter_top_from_gamma(T, Filtered)
    ;
        filter_top_from_gamma(T, RestFiltered),
        Filtered = [H|RestFiltered]
    ).

% is_top_formula/1: Détecte si une formule est ⊤ (top)
% ⊤ est représenté comme (# => #) ou parfois ~ #
is_top_formula((# => #)) :- !.
is_top_formula(((# => #) => #) => #) :- !.  % Double négation de ⊥
is_top_formula(_) :- fail.
/*
% Antiséquent : Γ ⊬ Δ (pour les échecs)
render_antisequent(G > D, VarCounter, FinalCounter) :-
    render_formula_list(G, VarCounter, TempCounter),
    write(' \\nvdash '),
    ( D = [] ->
        write('\\bot'),
        FinalCounter = TempCounter
    ;
        render_formula_list(D, TempCounter, FinalCounter)
    ).
*/
% =========================================================================
% RENDU DES LISTES DE FORMULES
% =========================================================================

% Liste vide
render_formula_list([], VarCounter, VarCounter) :- !.

% Formule unique
render_formula_list([F], VarCounter, FinalCounter) :-
    !,
    rewrite(F, VarCounter, FinalCounter, F_latex),
    write_formula_with_parens(F_latex).

% Liste de formules avec virgules
render_formula_list([F|Rest], VarCounter, FinalCounter) :-
    rewrite(F, VarCounter, TempCounter, F_latex),
    write(F_latex),
    write(', '),
    render_formula_list(Rest, TempCounter, FinalCounter).

% =========================================================================
% INTÉGRATION AVEC LE SYSTÈME PRINCIPAL
% =========================================================================

% Interface compatible avec decide/1
render_g4_bussproofs_from_decide(Proof) :-
    render_g4_proof(Proof).

% Interface compatible avec prove_formula_clean/3
render_g4_bussproofs_from_clean(Proof) :-
    render_g4_proof(Proof).

% =========================================================================
% COMMENTAIRES ET DOCUMENTATION
% =========================================================================

% Ce printer G4 est spécialement optimisé pour :
% 
% 1. LES RÈGLES G4 AUTHENTIQUES :
%    - L0→ (modus ponens signature de G4)
%    - L∧→, L∨→ (transformations curryifiées)
%    - L→→ (règle G4 spéciale)
%    - Ordre exact du multiprover.pl
%
% 2. COMPATIBILITÉ MULTIFORMATS :
%    - Utilise le système rewrite/4 de latex_utilities.pl
%    - Compatible avec les quantificateurs FOL
%    - Gère les antiséquents pour les échecs
%
% 3. RENDU LATEX PROFESSIONNEL :
%    - bussproofs.sty standard
%    - Labels compacts et clairs
%    - Gestion automatique des compteurs de variables
%
% USAGE :
% ?- decide(Formula).  % Utilise automatiquement ce printer
% ?- render_g4_proof(Proof).  % Rendu direct d'une preuve

% =========================================================================
% FIN DU G4 PRINTER
% =========================================================================
