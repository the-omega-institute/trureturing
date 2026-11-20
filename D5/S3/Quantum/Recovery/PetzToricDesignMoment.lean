import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-!
# The finite harmonic second moment

This is the character average in Section 1 of `toric-design-transpose-recovery.txt`.
The unordered-pair condition is the one in `ProjectiveToricDesignNonGroup.design2`,
including pairs with repeated indices. The two matrix entries in the Haar numerator
are the identity and swap contractions used in `CollisionConservation`.
-/

open scoped BigOperators Kronecker

noncomputable section

namespace PetzToricDesignMoment

variable {G : Type*} [AddCommGroup G] {d : ℕ}

abbrev PairMatrix (d : ℕ) := Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ

def pairSum (s : Fin d → G) (a : Fin d × Fin d) : G := s a.1 + s a.2

/-- Equality of unordered pairs allows the two orderings and retains multiplicities. -/
def Sidon (s : Fin d → G) : Prop :=
  ∀ a b : Fin d × Fin d, pairSum s a = pairSum s b ↔ a = b ∨ a = b.swap

private theorem pairSum_eq_of_match (s : Fin d → G) {a b : Fin d × Fin d}
    (h : a = b ∨ a = b.swap) : pairSum s a = pairSum s b := by
  rcases h with h | h
  · exact congrArg (pairSum s) h
  · exact (congrArg (pairSum s) h).trans (add_comm (s b.2) (s b.1))

/-- The anchored phase vector, with unit-modulus entries and phase `1` at `base`. -/
def phaseVector (s : Fin d → G) (base : Fin d) (χ : AddChar G ℂ) : Fin d → ℂ :=
  fun i => χ (s i - s base)

/-- Entries of the normalized character outer product. -/
def characterProjector (s : Fin d → G) (χ : AddChar G ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => (d : ℂ)⁻¹ * χ (s i - s j)

/-- The character projector is the scaled rank-one matrix for any choice of anchor. -/
theorem characterProjector_eq_vecMulVec [Finite G]
    (s : Fin d → G) (base : Fin d) (χ : AddChar G ℂ) :
    characterProjector s χ = (d : ℂ)⁻¹ • Matrix.vecMulVec (phaseVector s base χ)
      (fun j => star (phaseVector s base χ j)) := by
  apply Matrix.ext
  intro i j
  change (d : ℂ)⁻¹ * χ (s i - s j) =
    (d : ℂ)⁻¹ * (χ (s i - s base) * star (χ (s j - s base)))
  rw [Complex.star_def, ← χ.map_neg_eq_conj, ← χ.map_add_eq_mul]
  have hphase : s i - s base + -(s j - s base) = s i - s j := by abel
  rw [hphase]

def coordinateProjector (r : Fin d) : Matrix (Fin d) (Fin d) ℂ := Matrix.single r r 1

/-- The swap matrix sends the column basis vector at `(k,l)` to `(l,k)`. -/
def swapMatrix (d : ℕ) : PairMatrix d := Matrix.of fun a b => if a = b.swap then 1 else 0

def haarMoment (d : ℕ) : PairMatrix d :=
  ((d : ℂ) * ((d : ℂ) + 1))⁻¹ • ((1 : PairMatrix d) + swapMatrix d)

/-- Sum over the character labels, with a term for each label. -/
def flatSum [Fintype G] (s : Fin d → G) : PairMatrix d :=
  ∑ χ : AddChar G ℂ, characterProjector s χ ⊗ₖ characterProjector s χ

def coordinateSum (d : ℕ) : PairMatrix d :=
  ∑ r : Fin d, coordinateProjector r ⊗ₖ coordinateProjector r

def flatWeight (G : Type*) [Fintype G] (d : ℕ) : ℝ :=
  (d : ℝ) / (((d : ℝ) + 1) * (Fintype.card G : ℝ))

def coordinateWeight (d : ℕ) : ℝ := ((d : ℝ) * ((d : ℝ) + 1))⁻¹

def weightedMoment [Fintype G] (s : Fin d → G) : PairMatrix d :=
  (flatWeight G d : ℂ) • flatSum s + (coordinateWeight d : ℂ) • coordinateSum d

theorem weights_positive_and_sum [Fintype G] (hd : 0 < d) :
    0 < flatWeight G d ∧ 0 < coordinateWeight d ∧
      (∑ _ : AddChar G ℂ, flatWeight G d) + (∑ _ : Fin d, coordinateWeight d) = 1 := by
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hGR : 0 < (Fintype.card G : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hd1R : 0 < (d : ℝ) + 1 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold flatWeight
    exact div_pos hdR (mul_pos hd1R hGR)
  · unfold coordinateWeight
    exact inv_pos.mpr (mul_pos hdR hd1R)
  · simp only [Finset.sum_const, Finset.card_univ, AddChar.card_eq, Fintype.card_fin,
      nsmul_eq_mul, flatWeight, coordinateWeight]
    field_simp [hdR.ne', hGR.ne', hd1R.ne']

private theorem coordinateWeight_cast (d : ℕ) :
    (coordinateWeight d : ℂ) = ((d : ℂ) * ((d : ℂ) + 1))⁻¹ := by
  simp only [coordinateWeight, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one]

private theorem dimension_factors_ne_zero (hd : 0 < d) :
    (d : ℂ) ≠ 0 ∧ (d : ℂ) + 1 ≠ 0 := by
  refine ⟨Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd), ?_⟩
  simpa only [Nat.cast_succ] using
    (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d) : (↑(d.succ) : ℂ) ≠ 0)

private theorem characterTensor_apply (s : Fin d → G) (χ : AddChar G ℂ)
    (a b : Fin d × Fin d) :
    (characterProjector s χ ⊗ₖ characterProjector s χ) a b =
      ((d : ℂ)⁻¹) ^ 2 * χ (pairSum s a - pairSum s b) := by
  calc
    _ = ((d : ℂ)⁻¹) ^ 2 * (χ (s a.1 - s b.1) * χ (s a.2 - s b.2)) := by
      simp only [Matrix.kroneckerMap_apply, characterProjector, Matrix.of_apply]
      ring
    _ = _ := by
      rw [← χ.map_add_eq_mul]
      have hdiff : (s a.1 - s b.1) + (s a.2 - s b.2) = pairSum s a - pairSum s b := by
        unfold pairSum
        abel
      rw [hdiff]

/-- The unnormalized character sum, entrywise. The factor `d⁻²` comes from the two projectors. -/
theorem flatSum_apply [Fintype G] [DecidableEq G] (s : Fin d → G) (a b : Fin d × Fin d) :
    flatSum s a b = ((d : ℂ)⁻¹) ^ 2 *
      (if pairSum s a = pairSum s b then (Fintype.card G : ℂ) else 0) := by
  calc
    flatSum s a b = ((d : ℂ)⁻¹) ^ 2 *
        (∑ χ : AddChar G ℂ, χ (pairSum s a - pairSum s b)) := by
      simp only [flatSum, Matrix.sum_apply, characterTensor_apply, Finset.mul_sum]
    _ = _ := by
      rw [AddChar.sum_apply_eq_ite]
      simp only [sub_eq_zero]

/-- A coordinate term contributes exactly at the intersection of identity and swap support. -/
theorem coordinateSum_apply (a b : Fin d × Fin d) :
    coordinateSum d a b = if a = b ∧ a = b.swap then 1 else 0 := by
  have hdiag : (a.1 = a.2 ∧ a.1 = b.1 ∧ a.1 = b.2) ↔ a = b ∧ a = b.swap := by
    rcases a with ⟨i, j⟩
    rcases b with ⟨k, l⟩
    change (i = j ∧ i = k ∧ i = l) ↔ (i, j) = (k, l) ∧ (i, j) = (l, k)
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, hik, hil⟩
      exact ⟨⟨hik, hil⟩, ⟨hil, hik⟩⟩
    · rintro ⟨⟨hik, hjl⟩, ⟨hil, _⟩⟩
      exact ⟨hil.trans hjl.symm, hik, hil⟩
  rw [coordinateSum, Matrix.sum_apply]
  calc
    _ = (coordinateProjector a.1 ⊗ₖ coordinateProjector a.1) a b := by
      apply Finset.sum_eq_single a.1
      · intro r _ hr
        simp [Matrix.kroneckerMap_apply, coordinateProjector, Matrix.single_apply, hr]
      · simp
    _ = _ := by
      by_cases h : a.1 = b.1 <;>
        simp [Matrix.kroneckerMap_apply, coordinateProjector, Matrix.single_apply, ← hdiag, h]

/-- The weighted entry is the Haar weight times the sum of the pair-sum
and coordinate indicators. -/
theorem weightedMoment_apply [Fintype G] [DecidableEq G] (hd : 0 < d)
    (s : Fin d → G) (a b : Fin d × Fin d) :
    weightedMoment s a b = ((d : ℂ) * ((d : ℂ) + 1))⁻¹ *
      ((if pairSum s a = pairSum s b then 1 else 0) +
        (if a = b ∧ a = b.swap then 1 else 0)) := by
  obtain ⟨hdC, hd1C⟩ := dimension_factors_ne_zero hd
  have hGC : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hflat : (flatWeight G d : ℂ) * (((d : ℂ)⁻¹) ^ 2 * (Fintype.card G : ℂ)) =
      (coordinateWeight d : ℂ) := by
    simp only [flatWeight, coordinateWeight_cast, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
    field_simp [hdC, hd1C, hGC]
  simp only [weightedMoment, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    flatSum_apply, coordinateSum_apply]
  by_cases h : pairSum s a = pairSum s b
  · simp only [ite_eq_left h, hflat, coordinateWeight_cast, mul_add, mul_one]
  · simp [h, coordinateWeight_cast]

/-- The flat character frame and coordinate projectors have Haar second moment under Sidon. -/
theorem weightedMoment_eq_haar [Fintype G] (hd : 0 < d) (s : Fin d → G) (hs : Sidon s) :
    weightedMoment s = haarMoment d := by
  classical
  apply Matrix.ext
  intro a b
  simp only [weightedMoment_apply hd, haarMoment, Matrix.smul_apply, smul_eq_mul,
    Matrix.add_apply, Matrix.one_apply, swapMatrix, Matrix.of_apply, hs a b]
  by_cases hab : a = b <;> by_cases hswap : a = b.swap <;> simp [hab, hswap, add_comm]

/-- A repeated sum from unmatched pairs gives an extra entry at the specified row and column. -/
theorem repeated_pair_sum_entry [Fintype G] (hd : 0 < d) (s : Fin d → G)
    (a b : Fin d × Fin d) (hsum : pairSum s a = pairSum s b)
    (hmatch : ¬ (a = b ∨ a = b.swap)) :
    weightedMoment s a b = ((d : ℂ) * ((d : ℂ) + 1))⁻¹ ∧ haarMoment d a b = 0 := by
  classical
  have hab : a ≠ b := fun h => hmatch (Or.inl h)
  have hswap : a ≠ b.swap := fun h => hmatch (Or.inr h)
  constructor
  · simp [weightedMoment_apply hd, hsum, hab]
  · simp [haarMoment, swapMatrix, hab, hswap, smul_eq_mul]

/-- The exact Haar matrix identity characterizes Sidon for this weighted construction. -/
theorem weightedMoment_eq_haar_iff [Fintype G] (hd : 0 < d) (s : Fin d → G) :
    weightedMoment s = haarMoment d ↔ Sidon s := by
  constructor
  · intro hm a b
    constructor
    · intro hsum
      by_contra hmatch
      obtain ⟨hw, hh⟩ := repeated_pair_sum_entry hd s a b hsum hmatch
      obtain ⟨hdC, hd1C⟩ := dimension_factors_ne_zero hd
      have hentry := congrArg (fun M : PairMatrix d => M a b) hm
      exact (inv_ne_zero (mul_ne_zero hdC hd1C)) (hw.symm.trans (hentry.trans hh))
    · exact pairSum_eq_of_match s
  · exact weightedMoment_eq_haar hd s

end PetzToricDesignMoment
