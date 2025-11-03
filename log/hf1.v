Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Inductive Term : Set :=
  | tt : Term
  | ff : Term
  | if_then_else : Term -> Term -> Term -> Term.
  
Inductive has_type : Term -> Prop :=
  | T_True : has_type tt
  | T_False : has_type ff
  | T_If : forall p q r,
      has_type p ->
      has_type q ->
      has_type r ->
      has_type (if_then_else p q r).

Notation "⊢ t [:] bool" := (has_type t) (at level 40, no associativity).


(* Példák a típusolás használatára *)
Example example1 : ⊢ tt [:] bool.
Proof.
  apply T_True.
Qed.

Example example2 : ⊢ (if_then_else ff tt ff) [:] bool.
Proof.
  apply T_If.
  apply T_False.
  apply T_True.
  apply T_False.
Qed.



Example term : ⊢ (if_then_else tt (if_then_else tt ff tt) ff) [:] bool.
Proof.
apply T_If.
  - apply T_True.
  - apply T_If.
  -- apply T_True.
  -- apply T_False.
  -- apply T_True.
  - apply T_False.
Qed.

Reserved Notation "⊢ t ≡ s" (at level 70, no associativity).


Inductive D_equiv : Term -> Term -> Prop :=
  | E_Refl : forall t,
      ⊢ t ≡ t 
  | E_Symm : forall t s,
      ⊢ t ≡ s ->
      ⊢ s ≡ t
  | E_Trans : forall t s u,
      ⊢ t ≡ s  ->
      ⊢ s ≡ u  ->
      ⊢ t ≡ u 
  | E_If : forall p1 p2 q1 q2 r1 r2,
      ⊢ p1 ≡ p2  ->
      ⊢ q1 ≡ q2  ->
      ⊢ r1 ≡ r2  ->
      ⊢ (if_then_else p1 q1 r1) ≡ (if_then_else p2 q2 r2)
  | E_beta_True : forall p q,
      ⊢ (if_then_else tt p q) ≡ p
  | E_beta_False : forall p q,
      ⊢ (if_then_else ff p q) ≡ q
where "⊢ t ≡ s" := (D_equiv t s).


Add Parametric Relation : Term (D_equiv)
  reflexivity proved by (E_Refl)
  symmetry proved by (E_Symm)
  transitivity proved by (E_Trans)
  as D_equiv_rel.
  
Lemma problem_0 : ⊢ (if_then_else ff ff tt) ≡ tt.
Proof.
rewrite E_beta_False.
reflexivity.
Qed.

Example red : ⊢ (if_then_else tt (if_then_else tt ff tt) ff) ≡ ff.
Proof.
rewrite E_beta_True.
rewrite E_beta_True.
apply E_Refl.
Qed.
