(*Definition ret {A : Type} (x : A) : option A := Some x.

Definition bind {A B : Type} (m : option A) (f : A -> option B) : option B :=
  match m with
  | Some x => f x
  | None => None
  end.

*)
Lemma dualexp1 : forall (A B C : Prop) (H : (A -> B) \/ (A -> C)), A -> (B \/ C). 
Proof.
intros A B C H.
induction H as [H1|H2].
intros K.
left.
apply H1 in K.
exact K.
intros K.
right.
apply H2 in K.
exact K.
Qed.

Lemma dualexp2 : forall (A B C : Prop) (H : (A -> B) \/ (A -> C)), A -> (B \/ C).
Proof.
intros A B C H.
elim H.
intros H1 H2.
left.
apply H1 in H2.
exact H2.
intros H1 H2.
right.
apply H1 in H2.
exact H2.
Qed.

Inductive Term : Set :=
  | tt : Term
  | ff : Term
  | if_then_else : Term -> Term -> Term -> Term.

Inductive Mon (A : Type) : Type :=
  | MonNone : Mon A
  | MonSome : A -> Mon A.

Definition bind {A B : Type} (x : Mon A) (f : A -> Mon B) : Mon B :=
  match x with
  | MonNone _ => MonNone _
  | MonSome _ a => f a
  end.

Inductive has_type : Term -> Prop :=
| T_True : has_type tt
| T_False : has_type ff
| T_If : forall p q r,
    has_type p ->
    has_type q ->
    has_type r ->
    has_type (if_then_else p q r).

Notation "⊢ t [:] bool" := (has_type t) (at level 40, no associativity).

Example term : ⊢ (if_then_else (if_then_else ff tt ff) tt ff) [:] bool.
apply T_If.
apply T_If.
apply T_False.
apply T_True.
apply T_False.
apply T_True.
apply T_False.
Qed.


Definition ret {A : Type} (x : A) : Mon A := MonSome A x.

Definition example_term := if_then_else
  tt
  (if_then_else 
    (if_then_else
        ff
        (if_then_else ff ff tt)
        tt)
    tt
    tt)
  tt.



Fixpoint beta_red_cbv (limit : nat) (t : Term) : Mon Term :=
  match limit with
  | 0 => MonNone Term
  | S limit' =>
      match t with
      | tt => ret tt
      | ff => ret ff
      | if_then_else p q r =>
          bind (beta_red_cbv limit' p) (fun p' =>
            match p' with
            | tt => beta_red_cbv limit' q
            | ff => beta_red_cbv limit' r
            | _ => MonNone Term
            end)
      end
  end.

Compute beta_red_cbv 3 example_term.


Example a: forall A B C: Prop, (A->B)->(B->C)->(A->C).
Proof.
intros A B C H K H1.
apply K.
apply H.
exact H1.
Qed.

Example b: forall (U : Type) (A : U -> Prop), (exists x, (exists x, A x) -> A x) -> ((exists x, A x) -> (exists x, A x)).
intros.
exact H0.
Qed.

Example d: forall (U : Type) (A : U -> Prop), (forall x, (exists x, A x) -> A x) -> ((forall x, A x) -> (exists x, A x)).
intros.



Example c: forall (U : Type) (A : U -> Prop), (forall x, (exists x, A x) -> A x) -> ((forall x, A x) -> ~ (forall x, A x)).
intros.
unfold not in *.
intro.
exists A.


