From Autosubst Require Import Autosubst.

Require Import Syntax Reduction Typing.

Lemma type_renaming Γ s A :
  Γ |- s : A -> forall Δ ξ, Γ = (ξ >>> Δ) -> Δ |- s.[ren ξ] : A.
Proof.
  induction 1 ; intros ; subst ; econstructor ; eauto.
  - asimpl. apply IHtyping. autosubst.
Qed.

Lemma type_substitution Γ s A :
  Γ |- s : A -> forall Δ σ, (forall x, Δ |- (σ x) : (Γ x)) -> Δ |- s.[σ] : A.
Proof.
  induction 1 ; intros ; subst ; try econstructor ; eauto.
  - apply IHtyping. destruct x ; asimpl.
    + now constructor.
    + eapply type_renaming ; eauto.
Qed.
