(********************************************)
(** 4. Sorting algorithm as a theorem      **)
(********************************************)

From hahn Require Import Hahn.
Require Import Lia.
Require Import List.
Export ListNotations.
Require Import Arith Arith.EqNat.
Require Extraction.

(* And `is_smallest` consequently. *)
Inductive is_smallest : nat -> list nat -> Prop :=
  smallest_unit : forall n, is_smallest n [n]
| smallest_head : forall n m tl, 
    n <= m -> is_smallest m tl -> is_smallest n (n::tl)
| smallest_tail : forall n m tl, 
    m <  n -> is_smallest m tl -> is_smallest m (n::tl).

#[local]
Hint Constructors is_smallest : myconstr.

Inductive is_sorted : list nat -> Prop :=
  sorted_nil  : is_sorted []
| sorted_one  : forall n, is_sorted [n]
| sorted_cons : forall n tl
                       (STL : is_sorted tl)
                       (SST : is_smallest n (n::tl)),
    is_sorted (n::tl).

#[local]
Hint Constructors is_sorted : myconstr.

Inductive is_inserted : nat -> list nat -> list nat -> Prop :=
  ins_head : forall n tl, is_inserted n tl (n::tl)
| ins_tail : forall n m tl tl'
                    (INS : is_inserted n tl tl'),
    is_inserted n (m::tl) (m::tl').

#[local]
Hint Constructors is_inserted : myconstr.

Lemma is_inserted_perm a l l' (INS : is_inserted a l l') : Permutation (a :: l) l'.
(* Hint: perm_swap *)
Proof.
  generalize dependent l'.
  generalize dependent a.
  induction l; ins; inv INS.
  apply IHl in INS0.
  etransitivity.
  { by apply perm_swap. }
    by constructor.
Qed.

Lemma insert_sorted a l (SORT : is_sorted l) :
  {l' | is_inserted a l l' & is_sorted l'}.
(* Hint: le_gt_dec *)
Proof.
  induction l; eauto with myconstr.
  edestruct IHl as [l'].
  { clear -SORT. inv SORT. auto with myconstr. }
  destruct (le_gt_dec a a0).
  { exists (a::a0::l); auto with myconstr.
    apply sorted_cons; auto.
    eapply smallest_head; eauto.
    inv SORT. auto with myconstr. }
  exists (a0::l'); auto. constructor; auto.
  
  clear -SORT i i0 g.
  induction i; auto.
  { constructor; auto.
    apply smallest_head with (m:=n).
    { lia. }
    inv i0. constructor. }
  constructor; auto.
  apply smallest_head with (m:=m).
  2: { inv i0. constructor. }
  
  clear -SORT.
  inv SORT. inv STL.
  { inv SST.
    { inv H2. inv H5. }
    lia. }
  inv SST.
  { inv H2. lia. }
  lia.
Defined.

Definition p1 {X L B} (l : L) (A : L -> Prop) (x : {x : X | (A l) & B}) := (proj1_sig (sig_of_sig2 x)).

Theorem sort l : {l' | Permutation l l' & is_sorted l'}.
Proof.
  intros. induction l; eauto with myconstr.
  inv IHl.
  apply (insert_sorted a) in H0. inv H0.
  exists x0; auto.
  etransitivity.
  2: eby apply is_inserted_perm.
    by constructor.
Defined.
Eval compute in (p1 (sort [3;2;4;1])).

Print sort.

Extraction Language OCaml.
Recursive Extraction sort.