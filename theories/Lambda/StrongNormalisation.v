From Autosubst Require Import Autosubst.

From Coq Require Import Streams.
From Coq Require Import Relations.Relation_Definitions.

Require Import Syntax Reduction.

Set Implicit Arguments.

Inductive accessible A (R: relation A) (x: A) : Prop :=
| AccIntro : (forall y, R x y -> accessible R y) ->
             accessible R x.

CoInductive infinite A (R: relation A) : Stream A -> Prop :=
| SCons u u' S : R u u' -> infinite R (Cons u' S) ->
                 infinite R (Cons u (Cons u' S)).

Lemma acc_implies_finite A (R: relation A) u :
  accessible R u -> forall S, ~infinite R (Cons u S).
Proof.
  induction 1 as [u]. intro S. intro Hi.
  
Qed.
