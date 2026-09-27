/- GID: D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/ZhaoVincularPreimageRefutations
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.claimMaximum; result=D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.resultMaximum; claim=D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.claimMaximum
   digest: Zhao's maximum and second-largest vincular-stack fibre conjectures are false. -/

import Mathlib.Data.List.Permutation
import Mathlib.Data.Finset.Card

/-!
# Refutations of Zhao's vincular-stack preimage conjectures

Words have one-based entries; stack words are read from top to bottom.
The right-greedy convention tests avoidance of the entire proposed stack.
-/
namespace D5.S1.Words.Patterns.ZhaoVincularPreimageRefutations

/-- Whole-word containment of 1_23 (false) or 3_21 (true). -/
def Contains (descending : Bool) (w : List Nat) : Prop :=
  ∃ i : Fin w.length, ∃ j : Fin w.length,
    i.val < j.val ∧ j.val + 1 < w.length ∧
      if descending then w[i.val]! > w[j.val]! ∧ w[j.val]! > w[j.val + 1]!
      else w[i.val]! < w[j.val]! ∧ w[j.val]! < w[j.val + 1]!

instance decidableContains (d : Bool) (w : List Nat) : Decidable (Contains d w) := by
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

instance decidableIsPerm (n : Nat) (p : List Nat) : Decidable (IsPerm n p) := by
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

def claimMaximum : Prop :=
  ∀ n : Nat, 2 ≤ n →
    MaximumIs false n (2 ^ (n - 2)) ∧ MaximumIs true n (2 ^ (n - 2))



def claimSecondLargest : Prop :=
  ∀ n : Nat, 3 ≤ n →
    SecondLargestIs n (2 ^ (n - 3)) ∧ Multiplicity n (2 ^ (n - 3)) = 2 * n - 2





/-- A counterexample at n = 9; each of 129 preimages is checked separately. -/
theorem resultMaximum : ¬ claimMaximum := by
  intro h
  let witnesses : List (List Nat) := [
    [9,1,8,2,3,4,5,6,7],
    [9,1,8,3,4,5,6,7,2],
    [9,1,8,4,5,6,7,2,3],
    [9,1,8,4,5,6,7,3,2],
    [9,1,8,5,6,7,2,3,4],
    [9,1,8,5,6,7,3,4,2],
    [9,1,8,5,6,7,4,2,3],
    [9,1,8,5,6,7,4,3,2],
    [9,1,8,6,7,2,3,4,5],
    [9,1,8,6,7,3,4,5,2],
    [9,1,8,6,7,4,5,2,3],
    [9,1,8,6,7,4,5,3,2],
    [9,1,8,6,7,5,2,3,4],
    [9,1,8,6,7,5,3,4,2],
    [9,1,8,6,7,5,4,2,3],
    [9,1,8,6,7,5,4,3,2],
    [9,1,8,7,2,3,4,5,6],
    [9,1,8,7,3,4,5,6,2],
    [9,1,8,7,4,5,6,2,3],
    [9,1,8,7,4,5,6,3,2],
    [9,1,8,7,5,6,2,3,4],
    [9,1,8,7,5,6,3,4,2],
    [9,1,8,7,5,6,4,2,3],
    [9,1,8,7,5,6,4,3,2],
    [9,1,8,7,6,2,3,4,5],
    [9,1,8,7,6,3,4,5,2],
    [9,1,8,7,6,4,5,2,3],
    [9,1,8,7,6,4,5,3,2],
    [9,1,8,7,6,5,2,3,4],
    [9,1,8,7,6,5,3,4,2],
    [9,1,8,7,6,5,4,2,3],
    [9,1,8,7,6,5,4,3,2],
    [9,2,3,4,5,6,7,1,8],
    [9,3,4,5,6,7,1,8,2],
    [9,3,4,5,6,7,2,1,8],
    [9,4,5,6,7,1,8,2,3],
    [9,4,5,6,7,1,8,3,2],
    [9,4,5,6,7,2,3,1,8],
    [9,4,5,6,7,3,1,8,2],
    [9,4,5,6,7,3,2,1,8],
    [9,5,6,7,1,8,2,3,4],
    [9,5,6,7,1,8,3,4,2],
    [9,5,6,7,1,8,4,2,3],
    [9,5,6,7,1,8,4,3,2],
    [9,5,6,7,2,3,4,1,8],
    [9,5,6,7,3,4,1,8,2],
    [9,5,6,7,3,4,2,1,8],
    [9,5,6,7,4,1,8,2,3],
    [9,5,6,7,4,1,8,3,2],
    [9,5,6,7,4,2,3,1,8],
    [9,5,6,7,4,3,1,8,2],
    [9,5,6,7,4,3,2,1,8],
    [9,6,7,1,8,2,3,4,5],
    [9,6,7,1,8,3,4,5,2],
    [9,6,7,1,8,4,5,2,3],
    [9,6,7,1,8,4,5,3,2],
    [9,6,7,1,8,5,2,3,4],
    [9,6,7,1,8,5,3,4,2],
    [9,6,7,1,8,5,4,2,3],
    [9,6,7,1,8,5,4,3,2],
    [9,6,7,2,3,4,5,1,8],
    [9,6,7,3,4,5,1,8,2],
    [9,6,7,3,4,5,2,1,8],
    [9,6,7,4,5,1,8,2,3],
    [9,6,7,4,5,1,8,3,2],
    [9,6,7,4,5,2,3,1,8],
    [9,6,7,4,5,3,1,8,2],
    [9,6,7,4,5,3,2,1,8],
    [9,6,7,5,1,8,2,3,4],
    [9,6,7,5,1,8,3,4,2],
    [9,6,7,5,1,8,4,2,3],
    [9,6,7,5,1,8,4,3,2],
    [9,6,7,5,2,3,4,1,8],
    [9,6,7,5,3,4,1,8,2],
    [9,6,7,5,3,4,2,1,8],
    [9,6,7,5,4,1,8,2,3],
    [9,6,7,5,4,1,8,3,2],
    [9,6,7,5,4,2,3,1,8],
    [9,6,7,5,4,3,1,8,2],
    [9,6,7,5,4,3,2,1,8],
    [9,7,1,8,2,3,4,5,6],
    [9,7,1,8,3,4,5,6,2],
    [9,7,1,8,4,5,6,2,3],
    [9,7,1,8,4,5,6,3,2],
    [9,7,1,8,5,6,2,3,4],
    [9,7,1,8,5,6,3,4,2],
    [9,7,1,8,5,6,4,2,3],
    [9,7,1,8,5,6,4,3,2],
    [9,7,1,8,6,2,3,4,5],
    [9,7,1,8,6,3,4,5,2],
    [9,7,1,8,6,4,5,2,3],
    [9,7,1,8,6,4,5,3,2],
    [9,7,1,8,6,5,2,3,4],
    [9,7,1,8,6,5,3,4,2],
    [9,7,1,8,6,5,4,2,3],
    [9,7,1,8,6,5,4,3,2],
    [9,7,2,3,4,5,6,1,8],
    [9,7,3,4,5,6,1,8,2],
    [9,7,3,4,5,6,2,1,8],
    [9,7,4,5,6,1,8,2,3],
    [9,7,4,5,6,1,8,3,2],
    [9,7,4,5,6,2,3,1,8],
    [9,7,4,5,6,3,1,8,2],
    [9,7,4,5,6,3,2,1,8],
    [9,7,5,6,1,8,2,3,4],
    [9,7,5,6,1,8,3,4,2],
    [9,7,5,6,1,8,4,2,3],
    [9,7,5,6,1,8,4,3,2],
    [9,7,5,6,2,3,4,1,8],
    [9,7,5,6,3,4,1,8,2],
    [9,7,5,6,3,4,2,1,8],
    [9,7,5,6,4,1,8,2,3],
    [9,7,5,6,4,1,8,3,2],
    [9,7,5,6,4,2,3,1,8],
    [9,7,5,6,4,3,1,8,2],
    [9,7,5,6,4,3,2,1,8],
    [9,7,6,1,8,2,3,4,5],
    [9,7,6,1,8,3,4,5,2],
    [9,7,6,1,8,4,5,2,3],
    [9,7,6,1,8,4,5,3,2],
    [9,7,6,1,8,5,2,3,4],
    [9,7,6,1,8,5,3,4,2],
    [9,7,6,1,8,5,4,2,3],
    [9,7,6,1,8,5,4,3,2],
    [9,7,6,2,3,4,5,1,8],
    [9,7,6,3,4,5,1,8,2],
    [9,7,6,3,4,5,2,1,8],
    [9,7,6,4,5,1,8,2,3],
    [9,7,6,4,5,1,8,3,2]]
  have hw : ∀ t ∈ witnesses,
      IsPerm 9 t ∧ SC false t = [7,6,5,4,3,2,8,1,9] := by
    simp only [witnesses, List.forall_mem_cons]
    repeat' apply And.intro
    all_goals decide +kernel
  have hdistinct : witnesses.toFinset.card = 129 := by decide +kernel
  have hsubset : witnesses.toFinset ⊆ Fibre false 9 [7,6,5,4,3,2,8,1,9] := by
    intro t ht
    have ht' := hw t (List.mem_toFinset.mp ht)
    simpa only [Fibre, Sn, List.mem_toFinset, List.mem_filter,
      List.mem_permutations', beq_iff_eq, IsPerm] using ht'
  have hlower := Finset.card_le_card hsubset
  rw [hdistinct] at hlower
  have hupper := ((h 9 (by decide)).1).2 [7,6,5,4,3,2,8,1,9] (by decide +kernel)
  change F false 9 [7,6,5,4,3,2,8,1,9] ≤ 128 at hupper
  change 129 ≤ F false 9 [7,6,5,4,3,2,8,1,9] at hlower
  omega



/-- Two distinct fibre values greater than 4 refute the first conjunct at n = 5. -/
theorem resultSecondLargest : ¬ claimSecondLargest := by
  intro h
  have h5 := (h 5 (by decide)).1
  obtain ⟨m, hm, _, hunique⟩ := h5.2
  have hsmall : F false 5 [3,2,4,1,5] = 5 := by decide +kernel
  have hlarge : F false 5 [4,3,2,1,5] = 8 := by decide +kernel
  have hfirst := hunique [3,2,4,1,5] (by decide +kernel) (by omega)
  have hsecond := hunique [4,3,2,1,5] (by decide +kernel) (by omega)
  omega



end D5.S1.Words.Patterns.ZhaoVincularPreimageRefutations
