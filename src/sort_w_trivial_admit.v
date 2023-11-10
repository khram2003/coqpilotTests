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
  induction l.
  { intros. inversion INS; subst.
    inversion INS as [|? ? ? EQ EQ' EQ'']; subst.
    apply Permutation_refl. }
  intros. inversion INS; subst.
  { auto. }
  etransitivity.
  { apply perm_swap. }
  auto.
Admitted.

Lemma insert_sorted a l (SORT : is_sorted l) :
  {l' | is_inserted a l l' & is_sorted l'}.
(* Hint: le_gt_dec *)
Proof.
  admit.
Admitted.

Definition sort (l : list nat) : {l' | Permutation l l' & is_sorted l'}.
  induction l.
  { exists []; auto with myconstr. }
  destruct IHl.
  destruct insert_sorted with a x as [l' INS SORT]; auto.
  exists l'; auto.
  transitivity (a::x); auto.
  now apply is_inserted_perm.
Defined.

Theorem sort' l : {l' | Permutation l l' & is_sorted l'}.
Proof.
  admit.
Admitted.

Print sort.

Extraction Language OCaml.
Recursive Extraction sort.