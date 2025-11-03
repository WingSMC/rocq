(*Házi*)

Require stlc.
Require sttsogat_cat.

Import stlc.
Import sttsogat_cat.


(* 1. stlc.v ből *)

Lemma vex : forall A B : stlc.Typ, exists t, ⊢ t [:] (A ⊃ (B ⊃ A)).
Proof.
intros.
exists (stlc.lam A (stlc.lam B (stlc.hyp 1))).
apply STT_lam.
apply STT_lam.
apply STT_hypS.
apply STT_hyp0.
Qed.

Lemma currying_1 : forall A B C: stlc.Typ, exists t, ⊢ t [:] ((A ⊃ (B ⊃ C)) ⊃ ((A ∧ B) ⊃ C)).
Proof.
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
Proof.
intros.
exists (stlc.lam (A ∧ B) (
		stlc.app (stlc.hyp 1) (stlc.proj_1 (stlc.hyp 0))
	)).
apply STT_lam.
apply STT_app with (A:=B).
- apply STT_hypS.
- apply STT_proj1 with (B:=B).
  apply STT_hyp0.
Qed.

(* 2. sttsogat_cat.v *)

Lemma curry_s_1 (S : STTSOGAT) : forall A B C : Typ, (Pf A -> (Pf B -> Pf C)) -> Pf (Cnj A B) -> Pf C.

Lemma curry_s_2 (S : STTSOGAT) : forall A B C : Typ, Pf (Imp A (Imp B C)) -> Pf (Imp (Cnj A B) C).

(* 3.  *)

Lemma kvant_1 : forall (U : Type) (A B : U -> Prop), (forall x, A x /\ B x) <-> (forall x, A x) /\ (forall x, B x). 
Abort.

Lemma kvant_2 : forall (U : Type) (A B : U -> Prop), ((exists x, A x) \/ ~(exists x, A x)) ->  ((exists x, A x) -> ((exists x, B x))) -> (forall x, A x ->  (exists x, B x)).

