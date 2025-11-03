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
      
Notation "⊢ t [:] Tree" :=
  (isTree t) (at level 40, no associativity).

Example term : ⊢
  (node2
    (node1 leaf)
    (node2 leaf (node1 leaf))
  ) [:] Tree.
Proof.
apply TreeTerm2.
apply TreeTerm1.
apply TreeTerm0.
apply TreeTerm2.
apply TreeTerm0.
apply TreeTerm1.
apply TreeTerm0.
Qed.

Lemma pr_2 : forall A B C : Prop, ((A -> B) /\ (A -> C)) -> (A -> C /\ B).
intros A B C H H0.
induction H.
split.
apply H1.
apply H0.
apply H.
apply H0.
Show Proof.
Qed.

Lemma dist : forall (A B C : Prop) (H : (A /\ B) \/ (A /\ C)), A /\ (B \/ C).
Proof.
intros A B C H.
induction H as [H1|H2]. 
induction H1 as [H11 H12].
split.
exact H11.
left.

exact H12.
induction H2 as [H21 H22].
split.
exact H21.
right.
exact H22.
Qed.

Lemma idk0: forall A B C: Prop, (A -> B -> C) -> (A /\ B -> C).
Proof.
intros A B C H H1.

assert (H2 : B -> C).
apply H.
destruct H1 as [H11 H12].
exact H11.

apply H2.
destruct H1 as [H11 H12].
exact H12.
Qed.

Lemma problem : forall (A B : Prop) (H : ~A \/ A) (K : A -> B), ~A \/ B.
Proof.
intros A B H K.
induction H.
rename H into H1.
left.
exact H1.
right.
apply K in H.
exact H.
Qed.

Lemma idk: forall (U: Type) (A B: U -> Prop), (exists x, (A x /\ B x)) -> ((exists x, A x) /\ (exists x, B x)).
Proof.
intros U A B H.
split.
induction H as [x H1].
exists x. 
destruct H1 as [H11 H12].
exact H11.
induction H as [x H2].
exists x.
destruct H2 as [H21 H22].
exact H22.
Qed.

Require Import Coq.Logic.ConstructiveEpsilon.
Require Import Coq.Logic.Classical.

Lemma idk00: forall (U: Type) (A: U -> Prop), (exists x, (exists x, A x) -> A x) -> ((exists x, A x) -> (exists x, A x)).
Proof.
intros U A H H1.
induction H as [].
exists x.
apply H.
exact H1.
Qed.

Theorem exists_from_forall:
  forall (U : Type) (A : U -> Prop),
  (exists x : U, True) ->
  (forall x : U, A x) ->
  exists x : U, A x.
Proof.
  intros U A H H1.
  induction H.
  exists x.
  apply H1.
Qed.

Lemma idk02: forall (U: Type) (A: U -> Prop), (forall x, (exists x, A x) -> A x) -> ((forall x, A x) -> (exists x, A x)).
Proof.
intros U A H H1.
exists (arbitrary_x: U).
induction H as [].
intros.

Lemma idk01: forall (U: Type) (A: U -> Prop), (forall x,  (exists x, A x) -> A x) -> ((forall x, A x) -> ~ (forall x, A x)).

Compute forall (U : Type) (A : U -> Prop),
(exists x, (exists x, A x) -> A x) -> ((exists x, A x) -> (exists x, A x)).

Compute forall (U : Type) (A : U -> Prop),
(forall x,  (exists x, A x) -> A x) ->
((forall x, A x) -> ~ (forall x, A x)).

Compute forall (U : Type) (A : U -> Prop),
(forall x, (exists x, A x) -> A x) -> ((forall x, A x) -> (exists x, A x)).
