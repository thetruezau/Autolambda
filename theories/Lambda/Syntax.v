From Autosubst Require Import Autosubst.

Inductive term: Type :=
| Var (x: var)
| Lam (s: {bind term})
| App (s t: term).

(* Autosubst substitution *)
(* ---------------------- *)

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Defined.
