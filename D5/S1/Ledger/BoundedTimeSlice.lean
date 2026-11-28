/- GID: D5/S1/Ledger/BoundedTimeSlice
   generality: G
   mirror-B: D5/B/S1/Ledger/BoundedTimeSlice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=terminal=atom:d3af207c13235ebefa554d30155a712ff57b6730d9fa67f63e271edc92df39c0
   digest: Bounded fixed-sum slices saturate the tail box exactly on the plateau; capacities (4;2,1,1) have unique maximum 12 at time 4. -/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.List.Range
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order
public import Mathlib.Tactic.Ring

set_option backward.privateInPublic true
@[expose] public section

/- Library search (2026-09-07): D5 bounded-vector/cardinality and 5040 searches,
   pinned Mathlib slice/antidiagonal/product-of-chains searches, and external Lean
   code searches found no saturation iff for bounded fixed-sum vectors. Mathlib's
   finite injection/cardinality and dependent-product theorems are reused below.
   Dhand, arXiv:1402.1199, Lemma 2.1 concerns related classical product-of-chains
   unimodality; no mathematical novelty is claimed. The new Lean bridge deletes
   the head and reconstructs it by bounded subtraction, with the zero and maximal
   tails forcing the two endpoints. The general coefficient identity below uses
   Mathlib's Fintype.prod_sum, finsetSum_coeff, and cardinality-as-indicator sums
   (focused search 2026-09-08). The nine counts follow from that identity; the
   unique-maximum theorem independently uses the general plateau criterion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S1.Ledger.BoundedTimeSlice

variable {I : Type*} [Fintype I]

/-- Each tail coordinate independently ranges from zero to its capacity. -/
abbrev TailBox (a : I → ℕ) := (i : I) → Fin (a i + 1)

def tailSum {a : I → ℕ} (b : TailBox a) : ℕ := ∑ i, (b i).val

/-- The actual bounded head/tail vectors at time `t`. -/
abbrev TimeSlice (A : ℕ) (a : I → ℕ) (t : ℕ) :=
  {x : Fin (A + 1) × TailBox a // x.1.val + tailSum x.2 = t}

def sliceCount [DecidableEq I] (A : ℕ) (a : I → ℕ) (t : ℕ) : ℕ :=
  Fintype.card (TimeSlice A a t)

def forgetHead {A : ℕ} {a : I → ℕ} {t : ℕ}
    (x : TimeSlice A a t) : TailBox a := x.val.2

private theorem tail_sum_le {a : I → ℕ} (b : TailBox a) :
    tailSum b ≤ ∑ i, a i :=
  Finset.sum_le_sum fun i _ => Nat.le_of_lt_succ (b i).isLt

/-- The fixed-sum equation determines the head from the tails. -/
theorem time_slice_head_eq {A : ℕ} {a : I → ℕ} {t : ℕ}
    (x : TimeSlice A a t) : x.val.1.val = t - tailSum (forgetHead x) := by
  have hx := x.property
  change x.val.1.val + tailSum (forgetHead x) = t at hx
  omega

/-- Deleting the head loses no distinction between states in one slice. -/
theorem forget_head_injective (A : ℕ) (a : I → ℕ) (t : ℕ) :
    Function.Injective (forgetHead (A := A) (a := a) (t := t)) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    rw [time_slice_head_eq x, time_slice_head_eq y, h]
  · exact h

/-- Every tail extends precisely when the time lies between total tail and head capacity. -/
theorem forget_head_surjective_iff (A : ℕ) (a : I → ℕ) (t : ℕ) :
    Function.Surjective (forgetHead (A := A) (a := a) (t := t)) ↔
      (∑ i, a i) ≤ t ∧ t ≤ A := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h (fun i => ⟨a i, Nat.lt_succ_self _⟩)
    obtain ⟨y, hy⟩ := h (fun _ => ⟨0, Nat.zero_lt_succ _⟩)
    have hmax := x.property
    have hzero := y.property
    change x.val.1.val + tailSum (forgetHead x) = t at hmax
    change y.val.1.val + tailSum (forgetHead y) = t at hzero
    rw [hx] at hmax
    rw [hy] at hzero
    simp only [tailSum, Finset.sum_const_zero, add_zero] at hmax hzero
    have hybound := y.val.1.isLt
    omega
  · rintro ⟨hR, hA⟩ b
    have hb : tailSum b ≤ t := (tail_sum_le b).trans hR
    have hhead : t - tailSum b < A + 1 :=
      Nat.lt_succ_of_le ((Nat.sub_le _ _).trans hA)
    exact ⟨⟨(⟨t - tailSum b, hhead⟩, b), Nat.sub_add_cancel hb⟩, rfl⟩

variable [DecidableEq I]

/-- Ordinary generating functions count the actual bounded fixed-sum subtype.
This upstream-identity companion supplies the formula used by the nine-count table. -/
theorem time_slice_count_eq_coeff (A : ℕ) (a : I → ℕ) (t : ℕ) :
    sliceCount A a t =
      ((∑ h ∈ Finset.range (A + 1), (Polynomial.X : Polynomial ℕ) ^ h) *
        ∏ i, ∑ k ∈ Finset.range (a i + 1), Polynomial.X ^ k).coeff t := by
  simp_rw [← Fin.sum_univ_eq_sum_range, Fintype.prod_sum,
    Finset.prod_pow_eq_pow_sum, Finset.sum_mul, Finset.mul_sum, ← pow_add,
    Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
  rw [← Fintype.sum_prod_type']
  simp [sliceCount, Fintype.card_subtype, tailSum, eq_comm]

/-- The full tail box bounds the cardinality of every actual slice. -/
theorem time_slice_count_le (A : ℕ) (a : I → ℕ) (t : ℕ) :
    sliceCount A a t ≤ ∏ i, (a i + 1) := by
  simpa [sliceCount, TailBox, Fintype.card_pi] using
    Fintype.card_le_of_injective _ (forget_head_injective A a t)

/-- Saturation has no extra hypothesis comparing head and total tail capacity. -/
theorem time_slice_plateau_iff (A : ℕ) (a : I → ℕ) (t : ℕ) :
    sliceCount A a t = (∏ i, (a i + 1)) ↔ (∑ i, a i) ≤ t ∧ t ≤ A := by
  rw [← forget_head_surjective_iff A a t]
  have hcard : Fintype.card (TailBox a) = ∏ i, (a i + 1) := by
    simp [TailBox, Fintype.card_pi]
  rw [sliceCount, ← hcard]
  constructor
  · intro h
    exact ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨forget_head_injective A a t, h⟩).2
  · intro h
    exact Fintype.card_of_bijective ⟨forget_head_injective A a t, h⟩

/-- Source-facing saturation criterion retaining the head-dominates-tail domain.
This is a bind-only companion of `time_slice_plateau_iff`, with no new escape witness. -/
theorem time_slice_plateau_iff_of_tail_le_head (A : ℕ) (a : I → ℕ) (t : ℕ)
    (_hRA : (∑ i, a i) ≤ A) :
    sliceCount A a t = (∏ i, (a i + 1)) ↔ (∑ i, a i) ≤ t ∧ t ≤ A :=
  time_slice_plateau_iff A a t

/-- Outside the plateau at least one tail fails to extend, so the bound is strict. -/
theorem time_slice_strict_lt_iff (A : ℕ) (a : I → ℕ) (t : ℕ) :
    sliceCount A a t < (∏ i, (a i + 1)) ↔ t < (∑ i, a i) ∨ A < t := by
  have hle := time_slice_count_le A a t
  have heq := time_slice_plateau_iff A a t
  omega

/-- The plateau has multiple times, one time, or is unattainable in the three cases. -/
theorem time_slice_plateau_trichotomy (A : ℕ) (a : I → ℕ) :
    ((∑ i, a i) < A →
      (∑ i, a i) ≠ A ∧
      sliceCount A a (∑ i, a i) = (∏ i, (a i + 1)) ∧
      sliceCount A a A = (∏ i, (a i + 1))) ∧
    (A = (∑ i, a i) → ∀ t,
      sliceCount A a t ≤ (∏ i, (a i + 1)) ∧
      (sliceCount A a t = (∏ i, (a i + 1)) ↔ t = (∑ i, a i))) ∧
    (A < (∑ i, a i) → ∀ t, sliceCount A a t < (∏ i, (a i + 1))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact ⟨Nat.ne_of_lt h, (time_slice_plateau_iff A a _).mpr ⟨le_rfl, h.le⟩,
      (time_slice_plateau_iff A a A).mpr ⟨h.le, le_rfl⟩⟩
  · intro h t
    refine ⟨time_slice_count_le A a t, ?_⟩
    rw [time_slice_plateau_iff]
    omega
  · intro h t
    rw [time_slice_strict_lt_iff]
    omega

/-- Source-facing regimes with the distinguished head a longest chain.
This is a bind-only companion of `time_slice_plateau_trichotomy`. -/
theorem time_slice_plateau_trichotomy_of_head_maximal (A : ℕ) (a : I → ℕ)
    (_hmax : ∀ i, a i ≤ A) :
    ((∑ i, a i) < A →
      (∑ i, a i) ≠ A ∧
      sliceCount A a (∑ i, a i) = (∏ i, (a i + 1)) ∧
      sliceCount A a A = (∏ i, (a i + 1))) ∧
    (A = (∑ i, a i) → ∀ t,
      sliceCount A a t ≤ (∏ i, (a i + 1)) ∧
      (sliceCount A a t = (∏ i, (a i + 1)) ↔ t = (∑ i, a i))) ∧
    (A < (∑ i, a i) → ∀ t, sliceCount A a t < (∏ i, (a i + 1))) :=
  time_slice_plateau_trichotomy A a

/-- No state remains after the sum of all capacities. -/
theorem time_slice_count_eq_zero_of_total_lt (A : ℕ) (a : I → ℕ) (t : ℕ)
    (ht : A + (∑ i, a i) < t) : sliceCount A a t = 0 := by
  have hempty : IsEmpty (TimeSlice A a t) := ⟨by
    intro x
    have hx := x.property
    have hhead := x.val.1.isLt
    have htail := tail_sum_le x.val.2
    omega⟩
  exact Fintype.card_eq_zero

/-- Tail axes are the exponents of 3, 5, and 7, in that order. -/
def tailCapacities5040 : Fin 3 → ℕ := ![2, 1, 1]

abbrev timeSlice5040Count (t : ℕ) : ℕ := sliceCount 4 tailCapacities5040 t

/-- Arithmetic data connecting the bounded vector to 5040. -/
theorem time_slice_5040_capacities :
    5040 = 2 ^ 4 * 3 ^ 2 * 5 * 7 ∧
    (∑ i, tailCapacities5040 i) = 4 ∧
    (∏ i, (tailCapacities5040 i + 1)) = 12 := by
  decide

/-- The general counting theorem reduces all nine counts to polynomial coefficients. -/
theorem time_slice_5040_sequence :
    (List.range 9).map timeSlice5040Count = [1, 4, 8, 11, 12, 11, 8, 4, 1] := by
  let p : Polynomial ℕ := (∑ h ∈ Finset.range 5, Polynomial.X ^ h) *
    ∏ i, ∑ k ∈ Finset.range (tailCapacities5040 i + 1), Polynomial.X ^ k
  have hp : p = 1 + 4 * Polynomial.X + 8 * Polynomial.X ^ 2 + 11 * Polynomial.X ^ 3 +
      12 * Polynomial.X ^ 4 + 11 * Polynomial.X ^ 5 + 8 * Polynomial.X ^ 6 +
      4 * Polynomial.X ^ 7 + Polynomial.X ^ 8 := by
    dsimp [p]
    norm_num [tailCapacities5040, Fin.prod_univ_succ, Finset.sum_range_succ]
    ring
  calc
    (List.range 9).map timeSlice5040Count = (List.range 9).map (fun t => p.coeff t) := by
      apply List.map_congr_left
      intro t _
      exact time_slice_count_eq_coeff 4 tailCapacities5040 t
    _ = _ := by
      rw [hp]
      norm_num [List.range_succ, Polynomial.coeff_X_pow, Polynomial.coeff_one,
        Polynomial.coeff_X]

/-- The displayed sequence includes every possibly nonzero time. -/
theorem time_slice_5040_zero_after_eight (t : ℕ) (ht : 8 < t) :
    timeSlice5040Count t = 0 := by
  apply time_slice_count_eq_zero_of_total_lt
  rw [time_slice_5040_capacities.2.1]
  exact ht

/-- The general plateau criterion gives the unique global maximum for 5040. -/
theorem time_slice_5040_unique_maximum (t : ℕ) :
    timeSlice5040Count t ≤ 12 ∧ (timeSlice5040Count t = 12 ↔ t = 4) := by
  have hR := time_slice_5040_capacities.2.1
  have hP := time_slice_5040_capacities.2.2
  constructor
  · simpa [hP] using time_slice_count_le 4 tailCapacities5040 t
  · rw [← hP, time_slice_plateau_iff, hR]
    omega

/-- At time four every bounded tail has exactly one head, given by subtraction. -/
theorem time_slice_5040_tail_extension (b : TailBox tailCapacities5040) :
    ∃! h : Fin 5, h.val + tailSum b = 4 ∧ h.val = 4 - tailSum b := by
  have hsurj := (forget_head_surjective_iff 4 tailCapacities5040 4).mpr
    ⟨time_slice_5040_capacities.2.1.le, le_rfl⟩
  obtain ⟨x, hx⟩ := hsurj b
  refine ⟨x.val.1, ⟨?_, ?_⟩, ?_⟩
  · have hp := x.property
    change x.val.1.val + tailSum (forgetHead x) = 4 at hp
    rwa [hx] at hp
  · rw [time_slice_head_eq x, hx]
  · intro h hh
    apply Fin.ext
    rw [hh.2, time_slice_head_eq x, hx]

example : TimeSlice 4 tailCapacities5040 4 :=
  ⟨(⟨4, by decide⟩, fun _ => ⟨0, Nat.zero_lt_succ _⟩), by simp [tailSum]⟩

example : (∑ i, tailCapacities5040 i) ≤ 4 ∧ 4 ≤ (4 : ℕ) :=
  ⟨time_slice_5040_capacities.2.1.le, le_rfl⟩

example : timeSlice5040Count 4 = 12 := (time_slice_5040_unique_maximum 4).2.mpr rfl

#print axioms time_slice_plateau_iff
#print axioms time_slice_count_eq_coeff
#print axioms time_slice_5040_sequence
#print axioms time_slice_5040_unique_maximum

end D5.S1.Ledger.BoundedTimeSlice
