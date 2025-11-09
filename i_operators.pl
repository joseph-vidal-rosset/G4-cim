% =========================================================================
% OPERATEURS COMMUNS - Module centralise
% A inclure dans tous les modules du prouveur
% =========================================================================
:- use_module(library(lists)).
:- use_module(library(statistics)).
% =========================================================================
% OPERATEURS TPTP (syntaxe d'entree)
% =========================================================================
:- op( 500, fy, ~).             % negation
:- op(1000, xfy, &).            % conjunction
:- op(1100, xfy, '|').          % disjunction
:- op(1110, xfy, =>).           % conditional
:- op(1120, xfy, <=>).          % biconditional
:- op( 500, fy, !).             % universal quanti
:- op( 500, fy, !).             % universal quantifier:  ![X]:
:- op( 500, fy, ?).             % existential quantifier:  ?[X]:
:- op( 500, xfy, :).            % quantifier separator
% Syntaxe d'entree : sequent turnstile
% Equivalence operator for sequents (bidirectional provability)
:- op(800, xfx, <>).
% :- op(400, fx, f).             % falsity (?)
% :- op(400, fx, #).             % falsity (?)
% =========================================================================
% OPERATEURS LATEX (sortie formatee)
% ATTENTION : Respecter exactement les espaces !
% =========================================================================
:- op( 500, fy, ' \\lnot ').     % negation
:- op(1000, xfy, ' \\land ').    % conjunction
:- op(1100, xfy, ' \\lor ').     % disjunction
:- op(1110, xfx, ' \\to ').      % conditional
:- op(1120, xfx, ' \\leftrightarrow ').  % biconditional
:- op( 500, fy, ' \\forall ').   % universal quantifier
:- op( 500, fy, ' \\exists ').   % existential quantifier
:- op( 500, xfy, ' ').           % espace pour quantificateurs
:- op(400, fx, ' \\bot ').      % falsity (?)
% Syntaxe LaTeX : sequent turnstile  
:- op(1150, xfx, ' \\vdash ').

% =========================================================================
% DOCUMENTATION DES OPERATEURS
% =========================================================================

% Priorites (ordre croissant) :
% 500  : ~, !, ?, :
% 1000 : &
% 1100 : |
% 1110 : =>
% 1120 : <=>
% 1200 : f (?)

% Associativite :
% fy  : prefixe, associatif a droite (ex: ~ ~p)
% xfy : infixe, associatif a droite (ex: p & q & r)
% xfx : infixe, non associatif (ex: p <=> q)
% fx  : prefixe, non associatif (ex: f)

% Usage dans les modules :
% :- [operators].  % Inclure en debut de fichier
% =========================================================================
% OPERATEURS POUR SEQUENTS - AJOUT
% =========================================================================

