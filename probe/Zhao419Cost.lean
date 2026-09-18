import Mathlib.Data.List.Permutation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin

/- Independent probe of arXiv:2410.17057v1, preregistered in issue #8634.
   Public stack words are read from top to bottom; entries are one-based.
   No new-top-only shortcut is used. -/
namespace ZhaoProbe

/-- Whole-word containment of 1_23 (false) or 3_21 (true). -/
def Contains (descending : Bool) (w : List Nat) : Prop :=
  ∃ i : Fin w.length, ∃ j : Fin w.length,
    i.val < j.val ∧ j.val + 1 < w.length ∧
      if descending then w[i.val]! > w[j.val]! ∧ w[j.val]! > w[j.val + 1]!
      else w[i.val]! < w[j.val]! ∧ w[j.val]! < w[j.val + 1]!

instance (d : Bool) (w : List Nat) : Decidable (Contains d w) := by
  unfold Contains
  infer_instance

/-- Push iff the proposed stack avoids; otherwise emit the top and retry. -/
def Push (descending : Bool) (x : Nat) : List Nat → List Nat × List Nat
  | [] => ([], [x])
  | a :: s =>
    if Contains descending (x :: a :: s) then
      let r := Push descending x s
      (a :: r.1, r.2)
    else ([], x :: a :: s)

/-- Process input from left to right, then drain the remaining stack. -/
def Process (descending : Bool) : List Nat → List Nat → List Nat
  | [], s => s
  | x :: xs, s =>
    let r := Push descending x s
    r.1 ++ Process descending xs r.2

/-- Zhao's right-greedy map on one-line words. -/
def SC (descending : Bool) (input : List Nat) : List Nat :=
  Process descending input []

/-- Membership in S_n: exactly a permutation of the list 1,...,n. -/
def IsPerm (n : Nat) (p : List Nat) : Prop := p.Perm (List.range' 1 n)

instance (n : Nat) (p : List Nat) : Decidable (IsPerm n p) := by
  unfold IsPerm
  infer_instance

/-- Finite enumeration of S_n without repetitions (List.nodup_permutations). -/
def Sn (n : Nat) : List (List Nat) := (List.range' 1 n).permutations'

/-- The fibre as an actual finite set of inputs in S_n. -/
def Fibre (descending : Bool) (n : Nat) (pi : List Nat) : Finset (List Nat) :=
  ((Sn n).filter (fun t => SC descending t == pi)).toFinset

/-- Cardinality of the fibre. -/
def F (descending : Bool) (n : Nat) (pi : List Nat) : Nat :=
  (Fibre descending n pi).card

/-- The maximum over S_n is attained and bounds every value. -/
def MaximumIs (descending : Bool) (n m : Nat) : Prop :=
  (∃ pi, IsPerm n pi ∧ F descending n pi = m) ∧
  ∀ pi, IsPerm n pi → F descending n pi ≤ m

/-- Second-largest distinct value: attained, with exactly one larger value. -/
def SecondLargestIs (n k : Nat) : Prop :=
  (∃ pi, IsPerm n pi ∧ F false n pi = k) ∧
  ∃ m, k < m ∧ (∃ pi, IsPerm n pi ∧ F false n pi = m) ∧
    ∀ pi, IsPerm n pi → k < F false n pi → F false n pi = m

/-- Number of output permutations having a given fibre size. -/
def Multiplicity (n k : Nat) : Nat :=
  ((Sn n).filter (fun pi => F false n pi == k)).length


/- COST-ONLY: no conjecture result is claimed in this file. -/
private def block (tail : List Nat) : List (List Nat) :=
  (List.permutations'Aux 3 tail).flatMap fun t =>
    (List.permutations'Aux 2 t).flatMap (List.permutations'Aux 1)

-- Block 0: 336 inputs, 0 preimages.
example : ((block [4,5,6,7,8]).filter
    (fun p => SC false p == [7,6,5,4,3,2,1,8])).length = 0 := by
  simp only [block, List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

-- Block 1: 336 inputs, 0 preimages.
example : ((block [5,4,6,7,8]).filter
    (fun p => SC false p == [7,6,5,4,3,2,1,8])).length = 0 := by
  simp only [block, List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

-- Block 2: 336 inputs, 0 preimages.
example : ((block [5,6,4,7,8]).filter
    (fun p => SC false p == [7,6,5,4,3,2,1,8])).length = 0 := by
  simp only [block, List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

-- Block 3: 336 inputs, 0 preimages.
example : ((block [5,6,7,4,8]).filter
    (fun p => SC false p == [7,6,5,4,3,2,1,8])).length = 0 := by
  simp only [block, List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

-- Block 4: 336 inputs, 0 preimages.
example : ((block [5,6,7,8,4]).filter
    (fun p => SC false p == [7,6,5,4,3,2,1,8])).length = 0 := by
  simp only [block, List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

-- Block 5: 336 inputs, 0 preimages.
example : ((block [4,6,5,7,8]).filter
    (fun p => SC false p == [7,6,5,4,3,2,1,8])).length = 0 := by
  simp only [block, List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

-- Block 6: 336 inputs, 0 preimages.
example : ((block [6,4,5,7,8]).filter
    (fun p => SC false p == [7,6,5,4,3,2,1,8])).length = 0 := by
  simp only [block, List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

-- Block 7: 336 inputs, 0 preimages.
example : ((block [6,5,4,7,8]).filter
    (fun p => SC false p == [7,6,5,4,3,2,1,8])).length = 0 := by
  simp only [block, List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

-- Block 8: 336 inputs, 0 preimages.
example : ((block [6,5,7,4,8]).filter
    (fun p => SC false p == [7,6,5,4,3,2,1,8])).length = 0 := by
  simp only [block, List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

-- Block 9: 336 inputs, 0 preimages.
example : ((block [6,5,7,8,4]).filter
    (fun p => SC false p == [7,6,5,4,3,2,1,8])).length = 0 := by
  simp only [block, List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

-- Block 10: 336 inputs, 0 preimages.
example : ((block [4,6,7,5,8]).filter
    (fun p => SC false p == [7,6,5,4,3,2,1,8])).length = 0 := by
  simp only [block, List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

-- Block 11: 336 inputs, 0 preimages.
example : ((block [6,4,7,5,8]).filter
    (fun p => SC false p == [7,6,5,4,3,2,1,8])).length = 0 := by
  simp only [block, List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

-- Block 12: 336 inputs, 0 preimages.
example : ((block [6,7,4,5,8]).filter
    (fun p => SC false p == [7,6,5,4,3,2,1,8])).length = 0 := by
  simp only [block, List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

-- Block 13: 336 inputs, 0 preimages.
example : ((block [6,7,5,4,8]).filter
    (fun p => SC false p == [7,6,5,4,3,2,1,8])).length = 0 := by
  simp only [block, List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

-- Block 14: 336 inputs, 0 preimages.
example : ((block [6,7,5,8,4]).filter
    (fun p => SC false p == [7,6,5,4,3,2,1,8])).length = 0 := by
  simp only [block, List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

-- Block 15: 336 inputs, 0 preimages.
example : ((block [4,6,7,8,5]).filter
    (fun p => SC false p == [7,6,5,4,3,2,1,8])).length = 0 := by
  simp only [block, List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

end ZhaoProbe
