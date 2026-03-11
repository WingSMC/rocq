Require Import Classical.

Example pierce: forall (A B: Prop), ((A -> B) -> A) -> A.
Proof.
    intros A B H.
    destruct (classic A) as [HA | HnA].
    - exact HA.
    - apply H.
      intro HA.
      (* contradiction. *)
      exfalso.
      apply HnA.
      exact HA.
Qed.

Example hf1: forall (A B C: Prop), (A /\ B -> C) -> (A -> B -> C).
Proof.
    intros.
    apply H.
    split.
    - apply H0.
    - apply H1.
Qed.

Example hf2_a: forall (A B C: Prop), (A \/ (B /\ C)) -> ((A \/ B) /\ (A \/ C)).
intros A B C [|[]].
all: split.
- left. exact H.
- left. exact H.
- right. exact H.
- right. exact H0.
Qed.

Example hf2_b: forall (A B C: Prop), (A \/ (B /\ C)) -> ((A \/ B) /\ (A \/ C)).
intros.
split.
all: destruct H as [|[]].
- left. exact H.
- right. exact H.
- left. exact H.
- right. exact H0.
Qed.