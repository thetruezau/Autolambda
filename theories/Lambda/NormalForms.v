From Autosubst Require Import Autosubst.

From Coq Require Import Relations.Relation_Definitions.
From Coq Require Import Relations.Relation_Operators.

Require Import Syntax.

Inductive normal: term -> Prop :=
| nLam s : normal s -> normal (Lam s)
| nApps s : apps s -> normal s
  
with apps: term -> Prop :=
| nVar x : apps (Var x)
| nApp s1 s2: apps s1 -> normal s2 -> apps (App s1 s2).

Scheme sim_normal_ind := Induction for normal Sort Prop
  with sim_apps_ind := Induction for apps Sort Prop.  
Combined Scheme mut_normal_ind from sim_normal_ind, sim_apps_ind.

(* a term is normal iff it is irreducible *)
(* -------------------------------------- *)

Require Import Reduction.

Definition irreducible s := ~exists s', step s s'.

Proposition normal_is_irreducible :
  (forall s, normal s -> irreducible s)
  /\
  (forall s, apps s -> irreducible s).
Proof.
  apply mut_normal_ind ; intros.
  - intro H0.
    apply H.
    destruct H0 as [s0 Hs0].
    inversion Hs0. now exists s'.
    - intro H0.
      apply H.
      destruct H0 as [s0 Hs0]. now exists s0.
    - intro H. now destruct H.
    - intro H1.
      destruct H1 as [s0 Hs0].
      inversion Hs0 ; subst.
      + inversion a.
      + apply H. now exists s'.
      + apply H0. now exists t'.
Qed.

Proposition irreducible_is_normal s :
  irreducible s -> normal s.
Proof.
  induction s ; intro H.
  - constructor. constructor.
  - constructor. apply IHs.
    intro. apply H.
    inversion H0.
    apply Step_Abs in H1.
    now exists (Lam x).
  - constructor. constructor.
    + cut (irreducible s1).
      * intro is1.
        apply IHs1 in is1. inversion is1.
        ** cut False ; [contradiction |]. subst. apply H.
           exists (s.[s2/]). now constructor.
        ** assumption.
      * intro. apply H.
        inversion H0.
        eapply Step_App1 in H1. eauto.
    + apply IHs2. intro. apply H.
      inversion H0.
      apply Step_App2 with (s:=s1) in H1. 
      now exists (App s1 x).
Qed.
