/- GID: D5/S3/Arith/Lattices/RectangularDeltaChain
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/RectangularDeltaChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A sign-selected corner attains the minimum coordinate quotient chain bound. -/

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.RectangularDeltaChain

variable {ι : Type*} [Fintype ι]

/-- The first `n` points of the integer progression all lie in the closed rectangle. -/
def IsChain (L : ι → ℕ) (δ a : ι → ℤ) (n : ℕ) : Prop :=
  ∀ m : Fin n, ∀ p, 0 ≤ a p + (m.val : ℤ) * δ p ∧
    a p + (m.val : ℤ) * δ p ≤ (L p : ℤ)

instance (L : ι → ℕ) (δ a : ι → ℤ) (n : ℕ) : Decidable (IsChain L δ a n) :=
  inferInstanceAs (Decidable (∀ m : Fin n, ∀ p,
    0 ≤ a p + (m.val : ℤ) * δ p ∧ a p + (m.val : ℤ) * δ p ≤ (L p : ℤ)))

/-- Start at the upper face in negative directions and the lower face otherwise. -/
def corner (L : ι → ℕ) (δ : ι → ℤ) : ι → ℤ :=
  fun p => if δ p < 0 then (L p : ℤ) else 0

/-- Coordinates that actually move. -/
def active (δ : ι → ℤ) : Finset ι := Finset.univ.filter (fun p => δ p ≠ 0)

private lemma active_nonempty (δ : ι → ℤ) (hδ : ∃ p, δ p ≠ 0) :
    (active δ).Nonempty := by
  obtain ⟨p, hp⟩ := hδ
  exact ⟨p, by simp [active, hp]⟩

/-- The smallest integer quotient over the explicitly nonempty moving coordinates. -/
def stepLimit (L : ι → ℕ) (δ : ι → ℤ) (hδ : ∃ p, δ p ≠ 0) : ℕ :=
  (active δ).inf' (active_nonempty δ hδ) (fun p => L p / (δ p).natAbs)

private lemma step_limit_le (L : ι → ℕ) (δ : ι → ℤ) (hδ : ∃ p, δ p ≠ 0)
    (p : ι) (hp : δ p ≠ 0) : stepLimit L δ hδ ≤ L p / (δ p).natAbs := by
  exact Finset.inf'_le _ (by simp [active, hp])

omit [Fintype ι] in
private lemma coordinate_span (L : ι → ℕ) (δ a : ι → ℤ) {n : ℕ}
    (hn : 0 < n) (hc : IsChain L δ a n) (p : ι) :
    (n - 1) * (δ p).natAbs ≤ L p := by
  have hfirst := hc ⟨0, hn⟩ p
  have hlast := hc ⟨n - 1, by omega⟩ p
  change 0 ≤ a p + ((n - 1 : ℕ) : ℤ) * δ p ∧
    a p + ((n - 1 : ℕ) : ℤ) * δ p ≤ (L p : ℤ) at hlast
  simp only [Nat.cast_zero, zero_mul, add_zero] at hfirst
  have hspan : ((n - 1 : ℕ) : ℤ) * |δ p| ≤ (L p : ℤ) := by
    rcases le_total 0 (δ p) with hd | hd
    · rw [abs_of_nonneg hd]
      omega
    · rw [abs_of_nonpos hd, mul_neg]
      omega
  rw [← Int.natCast_natAbs] at hspan
  exact_mod_cast hspan

omit [Fintype ι] in
/-- Every nonzero coordinate bounds the length of every chain. -/
theorem chain_length_le_coordinate (L : ι → ℕ) (δ a : ι → ℤ) {n : ℕ}
    (hc : IsChain L δ a n) (p : ι) (hp : δ p ≠ 0) :
    n ≤ 1 + L p / (δ p).natAbs := by
  by_cases hn : n = 0
  · subst n
    exact Nat.zero_le _
  have hpos : 0 < (δ p).natAbs := Int.natAbs_pos.mpr hp
  have hdiv := (Nat.le_div_iff_mul_le hpos).mpr
    (coordinate_span L δ a (by omega) hc p)
  omega

/-- All moving coordinates jointly bound a chain by one plus their minimum quotient. -/
theorem chain_length_le (L : ι → ℕ) (δ a : ι → ℤ) (hδ : ∃ p, δ p ≠ 0)
    {n : ℕ} (hc : IsChain L δ a n) : n ≤ 1 + stepLimit L δ hδ := by
  by_cases hn : n = 0
  · omega
  have hmin : n - 1 ≤ stepLimit L δ hδ := by
    apply Finset.le_inf'
    intro p hp
    have hp' : δ p ≠ 0 := (Finset.mem_filter.mp hp).2
    have := chain_length_le_coordinate L δ a hc p hp'
    omega
  omega

private lemma corner_coordinate (L : ℕ) (d : ℤ) (m : ℕ)
    (hbound : m * d.natAbs ≤ L) :
    0 ≤ (if d < 0 then (L : ℤ) else 0) + (m : ℤ) * d ∧
    (if d < 0 then (L : ℤ) else 0) + (m : ℤ) * d ≤ (L : ℤ) := by
  have hcast : (m : ℤ) * (d.natAbs : ℤ) ≤ (L : ℤ) := by exact_mod_cast hbound
  rw [Int.natCast_natAbs] at hcast
  have hm : (0 : ℤ) ≤ m := Nat.cast_nonneg m
  by_cases hd : d < 0
  · rw [if_pos hd]
    rw [abs_of_neg hd, mul_neg] at hcast
    have hmul : (m : ℤ) * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm (le_of_lt hd)
    omega
  · rw [if_neg hd]
    have hd' : 0 ≤ d := by omega
    rw [abs_of_nonneg hd'] at hcast
    have hmul := mul_nonneg hm hd'
    omega

/-- The explicit sign-selected corner realizes every step through the minimum quotient. -/
theorem corner_chain (L : ι → ℕ) (δ : ι → ℤ) (hδ : ∃ p, δ p ≠ 0) :
    IsChain L δ (corner L δ) (1 + stepLimit L δ hδ) := by
  intro m p
  apply corner_coordinate
  by_cases hp : δ p = 0
  · simp [hp]
  · have hm : m.val ≤ stepLimit L δ hδ := by omega
    exact (Nat.le_div_iff_mul_le (Int.natAbs_pos.mpr hp)).mp
      (hm.trans (step_limit_le L δ hδ p hp))

/-- A chain of `n` points exists exactly up to one plus the minimum coordinate quotient. -/
theorem exists_chain_iff (L : ι → ℕ) (δ : ι → ℤ) (hδ : ∃ p, δ p ≠ 0)
    (n : ℕ) : (∃ a, IsChain L δ a n) ↔ n ≤ 1 + stepLimit L δ hδ := by
  constructor
  · rintro ⟨a, ha⟩
    exact chain_length_le L δ a hδ ha
  · intro hn
    refine ⟨corner L δ, ?_⟩
    intro m p
    exact corner_chain L δ hδ ⟨m.val, lt_of_lt_of_le m.isLt hn⟩ p

/-- The maximum point count is attained and equals one plus the minimum quotient. -/
theorem longest_chain_length (L : ι → ℕ) (δ : ι → ℤ) (hδ : ∃ p, δ p ≠ 0) :
    IsGreatest {n : ℕ | ∃ a, IsChain L δ a n} (1 + stepLimit L δ hδ) := by
  refine ⟨⟨corner L δ, corner_chain L δ hδ⟩, ?_⟩
  rintro n ⟨a, ha⟩
  exact chain_length_le L δ a hδ ha

omit [Fintype ι] in
/-- With no moving coordinate, the lower corner gives sequences of every length. -/
theorem zero_direction_unbounded (L : ι → ℕ) (δ : ι → ℤ) (hδ : ∀ p, δ p = 0)
    (n : ℕ) : IsChain L δ (fun _ => 0) n := by
  intro m p
  simp [hδ p]

#print axioms longest_chain_length
#print axioms exists_chain_iff
#print axioms zero_direction_unbounded

end D5.S3.Arith.Lattices.RectangularDeltaChain
