From Autosubst Require Import Autosubst.

From Coq Require Import Relations.Relation_Definitions.
From Coq Require Import Relations.Relation_Operators.

Require Import Syntax.

Reserved Notation "s '-->' t" (at level 40).
Inductive step : relation term :=
| Step_Beta (s: {bind term}) (s' u: term) :
  s' = s.[u .: ids] ->
  (App (Lam s) u) --> s'
| Step_Abs s s' :
  s --> s' ->
  (Lam s) --> (Lam s')
| Step_App1 s s' t :
  s --> s' ->
  (App s t) --> (App s' t)
| Step_App2 s t t':
  t --> t' ->
  (App s t) --> (App s t')
where "s '-->' t" := (step s t).

Reserved Notation "s '-->*' t" (at level 40).
Notation "s '-->*' t" := (clos_refl_trans_1n _ step s t).
