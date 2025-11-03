Example e1: forall (A B C: Prop), (A -> C) /\ (B -> C) -> (A \/ B) -> C.
Proof.
	intros A B C H1 H2.
	destruct H1 as [H1a H1b].
	destruct H2 as [H2a | H2b].
	- apply H1a. apply H2a.
	- apply H1b. apply H2b.
Qed.

Example e2: forall (A B C: Prop), ((A \/ B) -> C) -> (A -> C) /\ (B -> C).
Proof.
	intros.
	split.
	all: intros; apply H.
	- left. apply H0.
	- right. apply H0.
Qed.

Example e3: forall (A B: Prop), (~A \/ B) -> (A -> B).
Proof.
	intros.
	inversion H.
	- contradiction.
	- exact H1.
Qed.

Example e4: forall (A B: Prop), (A \/ ~A) -> (A -> B) -> (~A \/ B).
Proof.
	intros.
	destruct H.
	- right. apply H0. apply H.
	- left. exact H.
Qed.

Example e5: forall (A: Prop), ~~(A \/ ~A).
Proof.
	intros.
	unfold not.
	intros.
	apply H.
	right.
	intros.
	apply H.
	left.
	exact H0.
Qed.

Example e6: forall (U: Type) (A B: U -> Prop),
	(exists x: U, A x /\ B x) -> (exists y: U, A y) /\ (exists z: U, B z).
Proof.
	intros.
	split.
	all: destruct H.
	all: destruct H as [H1 H2].
	all: exists x.
	- exact H1.
	- exact H2.
Qed.

Theorem drinkers_paradox_dual: forall (U: Type) (P: U -> Prop),
	((exists y: U, P y) \/ ~ (exists y: U, P y)) ->
	(inhabited U) ->
	(exists x: U, (exists y: U, P y) -> P x).
Proof.
	intros.
	inversion H.
	destruct H as [K|L].
	inversion K.
	exists x.
	intuition.

	inversion H0.
	exists x.
	
	intros.
	contradiction.
	split.




Theorem drinkers_paradox: forall (U: Type) (P: U -> Prop),
	exists x: U, ~P x -> forall y: U, P y.
Proof.
	intros.
