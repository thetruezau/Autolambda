From Autosubst Require Import Autosubst.

Require Import Syntax Reduction Typing ContextMorphism.

Theorem subject_reduction s s' :
  s --> s' -> forall Γ A, Γ |- s : A -> Γ |- s' : A.
Proof.
  induction 1 ; intros ; subst ; ainv ;
    try (econstructor ; eauto).
  - apply type_substitution with (A0 .: Γ).
    + easy.
    + destruct x ; simpl.
      * easy.
      * now constructor.
Qed.
