Inductive TreeTerm : Set :=
  | leaf : TreeTerm
  | node1 : TreeTerm -> TreeTerm
  | node2 : TreeTerm -> TreeTerm -> TreeTerm.


Inductive isTree : TreeTerm -> Prop :=
  | TreeTerm0 : isTree leaf
  | TreeTerm1 : forall t,
      isTree t -> isTree (node1 t)
  | TreeTerm2 : forall t s,
      isTree t -> isTree s -> isTree (node2 t s).


Notation "⊢ t [:] Tree" := (isTree t) (at level 40, no associativity).


Example term : ⊢ (node2 (node1 leaf) (node2 leaf (node1 leaf))) [:] Tree.
Proof.
	apply TreeTerm2.
	apply TreeTerm1.
	apply TreeTerm0.
	apply TreeTerm2.
	apply TreeTerm0.
	apply TreeTerm1.
	apply TreeTerm0.
Qed.

Lemma pr_3 : forall A B C : Prop, ((A -> B) /\ (A -> C)) -> (A -> C).
Proof.
  intros.
  induction H.
  apply H1.
  assumption.
  Show Proof.
Qed.

Lemma dist : forall (A B C : Prop) (H : (A /\ B) \/ (A /\ C)), A /\ (B \/ C).
Proof.
	intros A B C H.
	split.
	induction H as [H1|H2]. 
	induction H1 as [H11 H12].
	exact H11.
	induction H2 as [H21 H22].
	exact H21.
	induction H as [H1|H2]. 
	induction H1 as [H11 H12].
	left.

	exact H12.
	induction H2 as [H21 H22].
	right.
	exact H22.
Qed.

Compute forall (U : Type) (A B : U -> Prop), ((exists x, A x) -> (exists x, B x)) -> (forall x, A x -> (exists x, B x)).
Compute forall (U : Type) (A B : U -> Prop), ((exists x, A x) -> (exists x, B x)) -> (exists x, A x -> (exists x, B x)) .
Compute forall (U : Type) (A B : U -> Prop),  (exists x, A x  -> (exists x, B x)) -> ((exists x, A x) -> (exists x, B x)).

Theorem prop1 : forall (U : Type) (A B : U -> Prop), ((exists x, A x) -> (exists x, B x)) -> (forall x, A x -> (exists x, B x)).
Proof.
  intros U A B H x HA.
  apply H.
  exists x.
  exact HA.
Qed.

Example t1: forall (A B C: Prop), ((A/\B) -> C) -> A -> B -> C.
Proof.
	intros A B C H H1 H2.
	apply H.
	split.
	exact H1.
	exact H2.
Qed.

Example t2: forall (U: Type) (A B: U -> Prop), (exists (x: U), ((A x) /\ (B x))) -> (exists (x: U), (A x)) /\ (exists (x: U), (B x)).
Proof.
  intros U A B [x [H1 H2]].
  split;
    exists x;
    [exact H1 | exact H2].
Qed.

Lemma problem : forall (A B : Prop) (H : ~A \/ B), A -> B.

(* intros A B H K.
induction H.
apply H in K.
contradiction.
exact H. *)


intros A B [] H0;
	[contradiction | exact H].
Qed.
