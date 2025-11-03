Theorem asd: forall (A B: Prop), (~A /\ ~B) -> ~(A \/ B).
Proof.
  intros A B H.
  unfold not in *.
  induction H as [].
  intros [].
  all: apply H + apply H0; exact H1.
Qed.

(*
Notation "∃ x" := (exists x).

Theorem frobenius (A: Set)(p: A -> Prop)(q: Prop): x ∈ A, q ∧ p x) <-> (q ∧ ∃ x ∈ A, p x).
  split.
  intros.
  destruct H as [y [H1 H2]].
  split.
  assumption.
  exists y.
  assumption.
  intros.
  destruct H as [H1 [y H2]].
  exists y.
  split.
  assumption.
  assumption.
Qed.
 *)
