(*Házi*)

Require stlc.
Import stlc.
Require sttsogat_cat.
Import sttsogat_cat.

(* 1. stlc.v ből *)

Lemma vex : forall A B : stlc.Typ, exists t, ⊢ t [:] (A ⊃ (B ⊃ A)).
intros.
exists (stlc.lam A (stlc.lam B (stlc.hyp 1))).
apply STT_lam.
apply STT_lam.
apply STT_hypS.
apply STT_hyp0.
Qed.

Lemma currying_1 : forall A B C: stlc.Typ, exists t, ⊢ t [:] ((A ⊃ (B ⊃ C)) ⊃ ((A ∧ B) ⊃ C)).
  intros.
  exists (
    stlc.lam (A ⊃ (B ⊃ C))            (* lambda f : A -> B -> C *)
      (stlc.lam (A ∧ B)                (* lambda p : A /\ B *)
        (stlc.app (stlc.app (stlc.hyp 1) (stlc.proj_1 (stlc.hyp 0)))
                  (stlc.proj_2 (stlc.hyp 0)))
      )
  ).
  apply STT_lam.
  apply STT_lam.
  apply STT_app with (A:=B).
  apply STT_app with (A:=A).
  - apply STT_hypS.               (* ⊢ hyp 1 [:] A ⊃ B ⊃ C *)
	  apply STT_hyp0.               (* ⊢ hyp 0 [:] A ⊃ B ⊃ C *)
  - apply STT_proj1 with (B:=B).  (* ⊢ proj_1 (hyp 0) [:] A *)
	  apply STT_hyp0.               (* ⊢ hyp 0 [:] A /\ B *)
  - apply STT_proj2 with (A:=A).  (* ⊢ proj_2 (hyp 0) [:] B *)
	  apply STT_hyp0.
Qed.

Lemma currying_2 : forall A B C: stlc.Typ, exists t, ⊢ t [:] ( ((A ∧ B) ⊃ C) ⊃ (A ⊃ (B ⊃ C)) ).
  intros A B C.
  (* The term is: λf. λx. λy. f (pair x y) *)
  (* Indices: f=2, x=1, y=0 *)
  exists (stlc.lam ((A ∧ B) ⊃ C) (stlc.lam A (stlc.lam B (stlc.app (stlc.hyp 2) (stlc.cnj (stlc.hyp 1) (stlc.hyp 0)))))).
  
  (* 1. λf *)
  apply STT_lam.
  (* 2. λx *)
  apply STT_lam.
  (* 3. λy *)
  apply STT_lam.
  
  (* 4. Apply f (hyp 2) to the pair *)
  apply STT_app with (A := (A ∧ B)).
  
  (* 4a. Prove f has type (A /\ B) -> C *)
  - apply STT_hypS.
    apply STT_hypS.
    apply STT_hyp0.
    
  (* 4b. Prove (x, y) has type A /\ B *)
  - apply STT_cnj.
    (* Prove x (hyp 1) has type A *)
    + apply STT_hypS.
      apply STT_hyp0.
    (* Prove y (hyp 0) has type B *)
    + apply STT_hyp0.
Qed.

(* 2. sttsogat_cat.v *)

Lemma curry_s_1 (S : STTSOGAT) : forall A B C : Typ, (Pf A -> (Pf B -> Pf C)) -> Pf (Cnj A B) -> Pf C.
  intros A B C.
  intro f.
  intro Pair.
  apply f.
  apply pr1 in Pair.
  assumption.
  apply pr2 in Pair.
  assumption.
Qed.

Lemma curry_s_2 (S : STTSOGAT) : forall A B C : Typ, Pf (Imp A (Imp B C)) -> Pf (Imp (Cnj A B) C).
  intros A B C f.
  apply lam.
  intro.
  apply app with (A := B).
  - apply app with (A := A).
  -- assumption.
  -- apply pr1 with (B := B).
     assumption.
  - apply pr2 with (A := A).
    assumption.
Qed.


(* 3.  *)

  Lemma kvant_1 : forall (U : Type) (A B : U -> Prop), (forall x, A x /\ B x) <-> (forall x, A x) /\ (forall x, B x). 
  intros U A B.
  split.
  - all: intro H.
    all: split.
    all: intro x.
    all: destruct (H x) as [].
    all: assumption.
  - intros [].
    exists.
    apply H. 
    apply H0.
Qed.

Lemma kvant_2 : forall (U : Type) (A B : U -> Prop), ((exists x, A x) \/ ~(exists x, A x)) ->  ((exists x, A x) -> ((exists x, B x))) -> (forall x, A x ->  (exists x, B x)).
  intros U A B [|].
  all: intros H0 H1 H2.
  all: apply H0.
  - assumption.
  - unfold not in *.
Qed.

