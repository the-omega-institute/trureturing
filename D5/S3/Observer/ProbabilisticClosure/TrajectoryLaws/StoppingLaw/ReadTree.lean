/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/ReadTree
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/ReadTree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unpadded binary read trees preserve actual records and nonreturn paid depths. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.Source
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.TakeDrop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

/-- A none leaf means permanent internal continuation after the reads already made. -/
inductive ReadTree where
  | leaf (output : Option Hidden)
  | read (address : ℤ) (zero one : ReadTree)
  deriving DecidableEq

abbrev Record := List (ℤ × Bool)

structure Execution where
  output : Option Hidden
  record : Record
  deriving DecidableEq

namespace Execution

def paid (v : Execution) : ℕ := v.record.length

def returned (v : Execution) : Bool := v.output.isSome

def prepend (t : ℤ) (b : Bool) (v : Execution) : Execution :=
  ⟨v.output, (t,b) :: v.record⟩

@[simp] theorem paid_prepend (t : ℤ) (b : Bool) (v : Execution) :
    (v.prepend t b).paid = v.paid + 1 := by simp [paid, prepend]

@[simp] theorem output_prepend (t : ℤ) (b : Bool) (v : Execution) :
    (v.prepend t b).output = v.output := rfl

end Execution

namespace ReadTree

def height : ReadTree → ℕ
  | .leaf _ => 0
  | .read _ z o => max z.height o.height + 1

/-- Repeated and separator reads are recorded and charged separately. -/
def run : ReadTree → (ℤ → Bool) → Execution
  | .leaf a, _ => ⟨a, []⟩
  | .read t z o, x => (if x t then o.run x else z.run x).prepend t (x t)

/-- Every potential queried address, including nodes not visited in this execution. -/
def addresses : ReadTree → Finset ℤ
  | .leaf _ => ∅
  | .read t z o => insert t (z.addresses ∪ o.addresses)

/-- Every spin coordinate used by a potential read in either source phase. -/
def support : ReadTree → Finset ℤ
  | .leaf _ => ∅
  | .read t z o => {t / 2, t / 2 + 1, (t - 1) / 2, (t - 1) / 2 + 1} ∪
      (z.support ∪ o.support)

@[simp] theorem run_leaf (a : Option Hidden) (x : ℤ → Bool) :
    (leaf a).run x = ⟨a, []⟩ := rfl

@[simp] theorem height_leaf (a : Option Hidden) : (leaf a).height = 0 := rfl

@[simp] theorem paid_leaf (a : Option Hidden) (x : ℤ → Bool) :
    ((leaf a).run x).paid = 0 := rfl

theorem paid_le_height (T : ReadTree) (x : ℤ → Bool) : (T.run x).paid ≤ T.height := by
  induction T with
  | leaf a => exact le_rfl
  | read t z o hz ho =>
    simp only [run, height]
    split
    · simpa using Nat.add_le_add_right (ho.trans (le_max_right _ _)) 1
    · simpa using Nat.add_le_add_right (hz.trans (le_max_left _ _)) 1

theorem paid_cap (T : ReadTree) {k : ℕ} (h : T.height ≤ k) (x : ℤ → Bool) :
    (T.run x).paid ≤ k := (T.paid_le_height x).trans h

theorem record_addresses (T : ReadTree) (x : ℤ → Bool) :
    ∀ a ∈ (T.run x).record, a.1 ∈ T.addresses := by
  induction T with
  | leaf a => simp [run]
  | read t z o hz ho =>
    simp only [run, Execution.prepend, addresses]
    split <;> intro a ha
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (ho a ha))
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (hz a ha))

theorem run_eq_of_agree (T : ReadTree) (x y : ℤ → Bool)
    (h : ∀ t ∈ T.addresses, x t = y t) : T.run x = T.run y := by
  induction T with
  | leaf a => rfl
  | read t z o hz ho =>
    have ht := h t (Finset.mem_insert_self _ _)
    have hz' : z.run x = z.run y := hz fun a ha =>
      h a (Finset.mem_insert_of_mem (Finset.mem_union_left _ ha))
    have ho' : o.run x = o.run y := ho fun a ha =>
      h a (Finset.mem_insert_of_mem (Finset.mem_union_right _ ha))
    simp only [run, ht, hz', ho']

theorem source_run_eq_of_agree (T : ReadTree) (φ : Bool) (S R : Spins)
    (h : ∀ i ∈ T.support, S i = R i) :
    T.run (visible φ S) = T.run (visible φ R) := by
  induction T with
  | leaf a => rfl
  | read t z o hz ho =>
    have ht : visible φ S t = visible φ R t := by
      have hs (i : ℤ) (hi : i ∈ ({t / 2, t / 2 + 1,
          (t - 1) / 2, (t - 1) / 2 + 1} : Finset ℤ)) : S i = R i :=
        h i (Finset.mem_union_left _ hi)
      cases φ <;> simp only [visible, Bool.toInt_false, Bool.toInt_true, sub_zero]
      · rw [hs _ (by simp), hs _ (by simp)]
      · rw [hs _ (by simp), hs _ (by simp)]
    have hz' := hz (fun i hi => h i (Finset.mem_union_right _
      (Finset.mem_union_left _ hi)))
    have ho' := ho (fun i hi => h i (Finset.mem_union_right _
      (Finset.mem_union_right _ hi)))
    simp only [run, ht, hz', ho']

/-- A zero paid count forces an actual leaf, including for a nonreturning execution. -/
theorem leaf_of_paid_zero (T : ReadTree) (x : ℤ → Bool) (h : (T.run x).paid = 0) :
    T = .leaf (T.run x).output := by
  cases T with
  | leaf a => rfl
  | read t z o =>
    simp only [run] at h
    split at h <;> simp at h

def stopComb : List ℤ → ReadTree
  | [] => .leaf (some (.a false))
  | t :: ts => .read t (stopComb ts) (.leaf (some (.a true)))

@[simp] theorem height_stopComb (ts : List ℤ) : (stopComb ts).height = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [stopComb, height, ih]

theorem stopComb_all_zero (ts : List ℤ) (x : ℤ → Bool)
    (h : ∀ t ∈ ts, x t = false) :
    (stopComb ts).run x = ⟨some (.a false), ts.map (fun t => (t, false))⟩ := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [stopComb, run, h t (by simp), Bool.false_eq_true, ↓reduceIte]
    rw [ih (fun a ha => h a (by simp [ha]))]
    rfl

end ReadTree
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
