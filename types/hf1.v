Theorem problem_3 : forall A B C : Prop, (A -> (B -> C)) -> (A /\ B -> C).  
Proof.
	intros A B C H [HA HB].
	apply H.
	exact HA.
	exact HB.
Qed.

Theorem problem_4 : forall A B C : Prop,  (A /\ B -> C) -> (A -> (B -> C)).
Proof.
	intros A B C H HA HB.
	apply H.
	split.
	exact HA.
	exact HB.
Qed.
