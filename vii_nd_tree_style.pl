% =========================================================================
% NATURAL DEDUCTION PRINTER IN TREE STYLE  
% =========================================================================
% =========================================================================
% DISPLAY PREMISS FOR TREE STYLE 
% =========================================================================
% render_premise_list_silent/5: Silent version for  tree style
render_premise_list_silent([], _, Line, Line, []) :- !.

render_premise_list_silent([LastPremiss], Scope, CurLine, NextLine, [CurLine:LastPremiss]) :-
    !,
    assert_safe_fitch_line(CurLine, LastPremiss, premise, Scope),
    NextLine is CurLine + 1.

render_premise_list_silent([Premiss|Rest], Scope, CurLine, NextLine, [CurLine:Premiss|RestContext]) :-
    assert_safe_fitch_line(CurLine, Premiss, premise, Scope),
    NextCurLine is CurLine + 1,
    render_premise_list_silent(Rest, Scope, NextCurLine, NextLine, RestContext).
% =========================================================================
% INTERFACE TREE STYLE
% =========================================================================
render_nd_tree_proof(Proof) :-
    retractall(fitch_line(_, _, _, _)),
    retractall(abbreviated_line(_)),
    extract_formula_from_proof(Proof, TopFormula),
    detect_and_set_logic_level(TopFormula),
    catch(
        (
            ( premise_list(PremissList), PremissList = [_|_] ->
                render_premise_list_silent(PremissList, 0, 1, NextLine, InitialContext),
                LastPremLine is NextLine - 1,  % ✅ CORRECTION
                % ✅ CORRECTION : Scope=1, CurLine=LastPremLine
                with_output_to(atom(_), fitch_g4_proof(Proof, InitialContext, 1, LastPremLine, _, _, 0, _))
            ;
                with_output_to(atom(_), fitch_g4_proof(Proof, [], 1, 0, _, _, 0, _))
            ),
            collect_and_render_tree()
        ),
        Error,
        (
            format('% Error rendering ND tree: ~w~n', [Error]),
            write('% Skipping tree visualization'), nl
        )
    ).
% =========================================================================
% COLLECT AND RENDER TREE
% =========================================================================

collect_and_render_tree() :-
    findall(N-Formula-Just-Scope, 
            (fitch_line(N, Formula, Just, Scope), \+ abbreviated_line(N)), 
            Lines),
    predsort(compare_lines, Lines, SortedLines),
    ( SortedLines = [] ->
        write('% Empty proof tree'), nl
    ;
        build_hypothesis_map(SortedLines, [], HypMap),
        findall(N, member(N-_-_-_, SortedLines), Ns),
        max_list(Ns, LastLineNum),
        
        % Détecter les prémisses
        findall(N-F, member(N-F-premise-_, SortedLines), Premises),
        
        ( build_buss_tree(LastLineNum, SortedLines, Tree) ->
            write('\\begin{prooftree}'), nl,
            % Si prémisses détectées, vérifier si weakening nécessaire
            ( Premises \= [] ->
                ( needs_weakening(Tree, Premises) ->
                    render_tree_with_weakening(Premises, SortedLines)
                ;
                    % Pas de weakening : simple réitération
                    render_tree_simple_sequent(Premises, SortedLines)
                )
            ;
                % Pas de prémisses : rendu normal
                render_buss_tree(Tree, SortedLines, HypMap)
            ),
            write('\\end{prooftree}'), nl
        ;
            write('% Warning: missing referenced line(s), skipping tree visualization'), nl
        )
    ).

compare_lines(Delta, N1-_-_-_, N2-_-_-_) :-
    compare(Delta, N1, N2).

% =========================================================================
% GESTION DU WEAKENING POUR TREE STYLE
% =========================================================================

% Pas de weakening pour les règles d'égalité
needs_weakening(Tree, _Premises) :-
    is_equality_tree(Tree),
    !,
    fail.  % Force l'utilisation de render_buss_tree

needs_weakening(Tree, Premises) :-
    findall(PremFormula, member(_-PremFormula, Premises), PremFormulas),
    \+ all_premises_used(Tree, PremFormulas).

% Helper : détecter un arbre d'égalité
is_equality_tree(binary_node(eq_subst, _, _, _)) :- !.
is_equality_tree(binary_node(eq_trans, _, _, _)) :- !.
is_equality_tree(binary_node(eq_subst_eq, _, _, _)) :- !.
is_equality_tree(unary_node(eq_sym, _, _)) :- !.
is_equality_tree(unary_node(eq_cong, _, _)) :- !.
is_equality_tree(axiom_node(_)) :- !.

all_premises_used(_, []) :- !.
all_premises_used(Tree, [P|Ps]) :-
    tree_contains_formula(Tree, P),
    all_premises_used(Tree, Ps).

% Helper : enlever les annotations de variables
strip_annotations(![_-X]:Body, ![X]:StrippedBody) :- 
    !, strip_annotations(Body, StrippedBody).
strip_annotations(?[_-X]:Body, ?[X]:StrippedBody) :- 
    !, strip_annotations(Body, StrippedBody).
strip_annotations(A & B, SA & SB) :- 
    !, strip_annotations(A, SA), strip_annotations(B, SB).
strip_annotations(A | B, SA | SB) :- 
    !, strip_annotations(A, SA), strip_annotations(B, SB).
strip_annotations(A => B, SA => SB) :- 
    !, strip_annotations(A, SA), strip_annotations(B, SB).
strip_annotations(A <=> B, SA <=> SB) :- 
    !, strip_annotations(A, SA), strip_annotations(B, SB).
strip_annotations(F, F).

% Matcher avec normalisation des annotations
tree_contains_formula(premise_node(F), P) :- 
    !,
    strip_annotations(F, F_stripped),
    strip_annotations(P, P_stripped),
    (F_stripped == P_stripped ; subsumes_term(F_stripped, P_stripped) ; subsumes_term(P_stripped, F_stripped)).

tree_contains_formula(axiom_node(F), P) :- 
    !,
    strip_annotations(F, F_stripped),
    strip_annotations(P, P_stripped),
    (F_stripped == P_stripped ; subsumes_term(F_stripped, P_stripped) ; subsumes_term(P_stripped, F_stripped)).

tree_contains_formula(hypothesis(_, F), P) :- 
    !,
    strip_annotations(F, F_stripped),
    strip_annotations(P, P_stripped),
    (F_stripped == P_stripped ; subsumes_term(F_stripped, P_stripped) ; subsumes_term(P_stripped, F_stripped)).

tree_contains_formula(unary_node(_, _, SubTree), F) :- 
    tree_contains_formula(SubTree, F).
tree_contains_formula(binary_node(_, _, TreeA, TreeB), F) :-
    (tree_contains_formula(TreeA, F) ; tree_contains_formula(TreeB, F)).
tree_contains_formula(ternary_node(_, _, _, _, TreeA, TreeB, TreeC), F) :-
    (tree_contains_formula(TreeA, F) ; tree_contains_formula(TreeB, F) ; tree_contains_formula(TreeC, F)).
tree_contains_formula(discharged_node(_, _, _, SubTree), F) :-
    tree_contains_formula(SubTree, F).
tree_contains_formula(discharged_node(_, _, _, TreeA, TreeB), F) :-
    (tree_contains_formula(TreeA, F) ; tree_contains_formula(TreeB, F)).

% Rendu simple : toutes prémisses utilisées
render_tree_simple_sequent(_Premises, FitchLines) :-
    % TOUJOURS construire l'arbre complet via render_buss_tree
    findall(N, member(N-_-_-_, FitchLines), Ns),
    max_list(Ns, LastLineNum),
    build_buss_tree(LastLineNum, FitchLines, Tree),
    build_hypothesis_map(FitchLines, [], HypMap),
    render_buss_tree(Tree, FitchLines, HypMap).

% Rendu avec Weakening
render_tree_with_weakening(Premises, _FitchLines) :-
    % Afficher toutes les prémisses
    forall(member(_-PremFormula, Premises), (
        write('\\AxiomC{}'), nl,
        write('\\noLine'), nl,
        write('\\UnaryInfC{$'),
        render_formula_for_buss(PremFormula),
        write('$}'), nl
    )),
    
    % Extraire la conclusion depuis le séquent stocké
    current_proof_sequent((_ > [Conclusion])),
    
    length(Premises, NumPremises),
    ( NumPremises = 1 ->
        write('\\RightLabel{$\\scriptsize{R}$}'), nl,
        write('\\UnaryInfC{$'),
        render_formula_for_buss(Conclusion),
        write('$}'), nl
    ; NumPremises = 2 ->
        write('\\RightLabel{$\\scriptsize{Wk.}$}'), nl,
        write('\\BinaryInfC{$'),
        render_formula_for_buss(Conclusion),
        write('$}'), nl
    ; NumPremises = 3 ->
        write('\\RightLabel{$\\scriptsize{Wk.}$}'), nl,
        write('\\TrinaryInfC{$'),
        render_formula_for_buss(Conclusion),
        write('$}'), nl
    ).


% =========================================================================
% CONSTRUCTION D'ARBRE BUSSPROOFS
% =========================================================================
build_buss_tree(LineNum, FitchLines, Tree) :-
    ( member(LineNum-Formula-Just-_Scope, FitchLines) ->
        build_tree_from_just(Just, LineNum, Formula, FitchLines, Tree)
    ;
        fail
    ).

build_tree_from_just(assumption, LineNum, Formula, _FitchLines, hypothesis(LineNum, Formula)) :- !.
build_tree_from_just(axiom, _LineNum, Formula, _FitchLines, axiom_node(Formula)) :- !.
build_tree_from_just(premise, _LineNum, Formula, _FitchLines, premise_node(Formula)) :- !.
build_tree_from_just(reiteration(SourceLine), _LineNum, Formula, FitchLines, reiteration_node(Formula, SubTree)) :-
    !,
    build_buss_tree(SourceLine, FitchLines, SubTree).

% R→
build_tree_from_just(rcond(HypNum, GoalNum), _LineNum, Formula, FitchLines, discharged_node(rcond, HypNum, Formula, SubTree)) :-
    !, build_buss_tree(GoalNum, FitchLines, SubTree).

% L0→
build_tree_from_just(l0cond(MajLine, MinLine), _LineNum, Formula, FitchLines, binary_node(l0cond, Formula, TreeA, TreeB)) :-
    !, build_buss_tree(MajLine, FitchLines, TreeA), build_buss_tree(MinLine, FitchLines, TreeB).

% R∨
build_tree_from_just(ror(SubLine), _LineNum, Formula, FitchLines, unary_node(ror, Formula, SubTree)) :-
    !, build_buss_tree(SubLine, FitchLines, SubTree).

% L∨
build_tree_from_just(lor(DisjLine, HypA, HypB, GoalA, GoalB), _LineNum, Formula, FitchLines,
                     ternary_node(lor, HypA, HypB, Formula, DisjTree, TreeA, TreeB)) :-
    !, build_buss_tree(DisjLine, FitchLines, DisjTree),
    build_buss_tree(GoalA, FitchLines, TreeA),
    build_buss_tree(GoalB, FitchLines, TreeB).

% L⊥
build_tree_from_just(lbot(BotLine), _LineNum, Formula, FitchLines, unary_node(lbot, Formula, SubTree)) :-
    !, build_buss_tree(BotLine, FitchLines, SubTree).

% L∧
build_tree_from_just(land(ConjLine, _Which), _LineNum, Formula, FitchLines, unary_node(land, Formula, SubTree)) :-
    !, build_buss_tree(ConjLine, FitchLines, SubTree).
build_tree_from_just(land(ConjLine), _LineNum, Formula, FitchLines, unary_node(land, Formula, SubTree)) :-
    !, build_buss_tree(ConjLine, FitchLines, SubTree).

% R∧
build_tree_from_just(rand(LineA, LineB), _LineNum, Formula, FitchLines, binary_node(rand, Formula, TreeA, TreeB)) :-
    !, build_buss_tree(LineA, FitchLines, TreeA), build_buss_tree(LineB, FitchLines, TreeB).

% IP
build_tree_from_just(ip(HypNum, BotNum), _LineNum, Formula, FitchLines, discharged_node(ip, HypNum, Formula, SubTree)) :-
    !, build_buss_tree(BotNum, FitchLines, SubTree).

% L∃
build_tree_from_just(lex(ExistLine, WitNum, GoalNum), _LineNum, Formula, FitchLines, 
                     discharged_node(lex, WitNum, Formula, ExistTree, GoalTree)) :-
    !,
    build_buss_tree(ExistLine, FitchLines, ExistTree), build_buss_tree(GoalNum, FitchLines, GoalTree).

% R∃
build_tree_from_just(rex(WitLine), _LineNum, Formula, FitchLines, unary_node(rex, Formula, SubTree)) :-
    !, build_buss_tree(WitLine, FitchLines, SubTree).

% L∀
build_tree_from_just(lall(UnivLine), _LineNum, Formula, FitchLines, unary_node(lall, Formula, SubTree)) :-
    !, build_buss_tree(UnivLine, FitchLines, SubTree).

% R∀
build_tree_from_just(rall(BodyLine), _LineNum, Formula, FitchLines, unary_node(rall, Formula, SubTree)) :-
    !, build_buss_tree(BodyLine, FitchLines, SubTree).

% L∧→
build_tree_from_just(landto(Line), _LineNum, Formula, FitchLines, unary_node(landto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% L∨→
build_tree_from_just(lorto(Line), _LineNum, Formula, FitchLines, unary_node(lorto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% L→→
build_tree_from_just(ltoto(Line), _LineNum, Formula, FitchLines, unary_node(ltoto, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% CQ_c
build_tree_from_just(cq_c(Line), _LineNum, Formula, FitchLines, unary_node(cq_c, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% CQ_m
build_tree_from_just(cq_m(Line), _LineNum, Formula, FitchLines, unary_node(cq_m, Formula, SubTree)) :-
    !, build_buss_tree(Line, FitchLines, SubTree).

% =========================================================================
% RÈGLES D'ÉGALITÉ - AJOUT CRITIQUE
% =========================================================================

% eq_refl : pas de sous-arbre
build_tree_from_just(eq_refl, _LineNum, Formula, _FitchLines, axiom_node(Formula)) :- !.

% eq_sym : un sous-arbre
build_tree_from_just(eq_sym(SourceLine), _LineNum, Formula, FitchLines, 
                     unary_node(eq_sym, Formula, SubTree)) :-
    !,
    build_buss_tree(SourceLine, FitchLines, SubTree).

% eq_trans : deux sous-arbres
build_tree_from_just(eq_trans(Line1, Line2), _LineNum, Formula, FitchLines, 
                     binary_node(eq_trans, Formula, Tree1, Tree2)) :-
    !, 
    build_buss_tree(Line1, FitchLines, Tree1),
    build_buss_tree(Line2, FitchLines, Tree2).

% eq_subst : DEUX SOUS-ARBRES (CRITIQUE)
build_tree_from_just(eq_subst(Line1, Line2), _LineNum, Formula, FitchLines,
                     binary_node(eq_subst, Formula, Tree1, Tree2)) :-
    !,
    build_buss_tree(Line1, FitchLines, Tree1),
    build_buss_tree(Line2, FitchLines, Tree2).

% eq_cong : un sous-arbre
build_tree_from_just(eq_cong(SourceLine), _LineNum, Formula, FitchLines, 
                     unary_node(eq_cong, Formula, SubTree)) :-
    !,
    build_buss_tree(SourceLine, FitchLines, SubTree).

% eq_subst_eq : deux sous-arbres
build_tree_from_just(eq_subst_eq(Line1, Line2), _LineNum, Formula, FitchLines,
                     binary_node(eq_subst_eq, Formula, Tree1, Tree2)) :-
    !,
    build_buss_tree(Line1, FitchLines, Tree1),
    build_buss_tree(Line2, FitchLines, Tree2).

% eq_trans_chain : pas de sous-arbre
build_tree_from_just(eq_trans_chain, _LineNum, Formula, _FitchLines, 
                     axiom_node(Formula)) :- !.

% =========================================================================
% FALLBACK (DOIT ÊTRE EN DERNIER)
% =========================================================================
build_tree_from_just(Just, LineNum, Formula, _FitchLines, unknown_node(Just, LineNum, Formula)) :-
    format('% WARNING: Unknown justification type: ~w~n', [Just]).
