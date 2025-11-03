Theorem and_iff_compat_l : forall A B C : Prop, (B <-> C) -> (A /\ B <-> A /\ C).
Proof.
  intros A B C H.
  split.
  all: intros [H0 H1].
  all: split; [exact H0 | apply H; exact H1].
Qed.

