From Autosubst Require Import Autosubst.

Require Import Syntax.

(* simple types *)
(* -------------*)

Inductive type: Type :=
| Base
| Arr (A B: type) : type.

Reserved Notation "Γ |- s : A"
  (at level 68, s at level 99, no associativity,
    format "Γ  |-  s  :  A").
Inductive typing (Γ: var->type) : term -> type -> Prop := 
| Ax (x: var) (A: type) :
  Γ x = A ->
  Γ |- (Var x) : A
| Intro (s: term) (A B: type) :
  (A .: Γ) |- s : B ->
  Γ |- (Lam s) : (Arr A B)
| Elim (s u: term) (A B: type) :
  Γ |- s : (Arr A B) ->
  Γ |- u : A ->
  Γ |- (App s u) : B
where "Γ |- s : A" := (typing Γ s A).
