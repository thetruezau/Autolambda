From Autosubst Require Import Autosubst.

Require Import Syntax Reduction.

Theorem substitutivity s s' :
  s --> s' -> forall σ, s.[σ] --> s'.[σ].
Proof.
  induction 1 ; intros ; subst ; asimpl.
  all: constructor ; autosubst.
Qed.
