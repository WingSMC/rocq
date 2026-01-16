Inductive BinOp : Set :=
 | plus : BinOp
 | mult : BinOp.

Inductive BinTree: Type :=
	| leaf: nat -> BinTree
	| node: BinOp -> BinTree -> BinTree -> BinTree.


Print BinTree_rec.

Theorem prop3 : forall (U : Type) (A B : U -> Prop), 
  (exists x, A x -> (exists x, B x)) -> ((forall x, A x) -> (exists x, B x)).
Proof.
  intros U A B [x0 H_imp] H_forall_A.
  (* H_imp : A x0 -> exists x, B x *)
  (* H_forall_A : forall x, A x *)
  apply H_imp.
  apply H_forall_A.
Qed.

Theorem prop2 : forall (U : Type) (A B : U -> Prop), 
  (forall x, A x -> (exists x, B x)) -> ((forall x, A x) -> (exists x, B x)).
Proof.
  intros U A B H H_forall_A.
  (* H : forall x, A x -> exists y, B y *)
  (* H_forall_A : forall x, A x *)
  (* Cél: exists x, B x *)
  
  (* Vegyünk egy tetszőleges elemet, ha U lakott *)
  (* De valójában csak alkalmaznunk kell H-t egy tetszőleges x-re *)
  
  (* Klasszikus megközelítés: *)
  destruct (H_forall_A) as [x H_Ax].  (* Ez nem működik, mert forall nem destruktálható így *)
  
  (* Helyes megközelítés: *)
  (* Ha U üres, akkor H_forall_A triviálisan igaz, de akkor nem tudunk tanút adni *)
  (* Ha U nem üres, akkor van legalább egy x₀ *)
  
  (* A bizonyítás attól függ, hogy U lakott-e *)
  (* De ha (forall x, A x) igaz, és U nem üres, akkor van egy konkrét x₀ *)
Abort.