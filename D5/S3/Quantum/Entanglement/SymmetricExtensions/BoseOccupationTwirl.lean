/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Diagonal tensor actions and occupation twirling of Bose extensions. -/

import D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
import D5.S3.Quantum.Entanglement.OccupancyWordSectors
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! Diagonal tensor conjugation acts on the original computational basis.
The diagonal twirl is due to Gulati--Nechita--Park, Corollary 8.18,
and Gulati--Nechita--Pellegrini, Lemma 5.8. -/

open scoped BigOperators ComplexOrder
open Matrix
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
open D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

/-- The diagonal entry of the genuine repeated local tensor operator. -/
def tensorPhase (u : L → ℂ) (x : I → L) : ℂ := ∏ i, u (x i)

/-- Conjugation by the diagonal tensor operator in the computational basis. -/
def diagonalAction (u : L → ℂ) (E : Matrix (I → L) (I → L) ℂ) :
    Matrix (I → L) (I → L) ℂ :=
  diagonal (tensorPhase u) * E * (diagonal (tensorPhase u))ᴴ

private lemma diagonalAction_apply (u : L → ℂ)
    (E : Matrix (I → L) (I → L) ℂ) (x y : I → L) :
    diagonalAction u E x y = tensorPhase u x * E x y * star (tensorPhase u y) := by
  simp [diagonalAction, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
    Matrix.mul_diagonal]

/-- Positivity is preserved by the actual tensor conjugation. -/
theorem diagonalAction_posSemidef (u : L → ℂ)
    (E : Matrix (I → L) (I → L) ℂ) (hE : E.PosSemidef) :
    (diagonalAction u E).PosSemidef :=
  hE.mul_mul_conjTranspose_same _

/-- The local diagonal at a transposed site is complex conjugated. -/
def cutPhase (S : Finset I) (u : L → ℂ) (x : I → L) : ℂ :=
  ∏ i, if i ∈ S then star (u (x i)) else u (x i)

private lemma transposed_phase (S : Finset I) (u : L → ℂ) (x y : I → L) :
    tensorPhase u (S.piecewise y x) * star (tensorPhase u (S.piecewise x y)) =
      cutPhase S u x * star (cutPhase S u y) := by
  simp only [tensorPhase, cutPhase, star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : i ∈ S <;> simp [Finset.piecewise, h, mul_comm]

/-- Every partial transpose of a summand is a conjugation of the same cut of E.
The formula includes the empty and full cuts. -/
theorem partialTranspose_diagonalAction (S : Finset I) (u : L → ℂ)
    (E : Matrix (I → L) (I → L) ℂ) :
    partialTransposeOn S (diagonalAction u E) =
      diagonal (cutPhase S u) * partialTransposeOn S E *
        (diagonal (cutPhase S u))ᴴ := by
  ext x y
  simp only [partialTransposeOn, diagonalAction_apply, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply]
  calc
    _ = (tensorPhase u (S.piecewise y x) *
        star (tensorPhase u (S.piecewise x y))) *
          E (S.piecewise y x) (S.piecewise x y) := by ring
    _ = _ := by rw [transposed_phase]; ring

/-- The same proper-cut PPT inequalities survive each diagonal tensor summand. -/
theorem diagonalAction_fullyPPT (u : L → ℂ)
    (E : Matrix (I → L) (I → L) ℂ) (hE : FullyPPT E) :
    FullyPPT (diagonalAction u E) := by
  intro S hS hp
  rw [partialTranspose_diagonalAction]
  exact (hE S hS hp).mul_mul_conjTranspose_same _

private lemma phase_unit (u : L → ℂ) (hu : ∀ a, ‖u a‖ = 1) (x : I → L) :
    tensorPhase u x * star (tensorPhase u x) = 1 := by
  have hn : ‖tensorPhase u x‖ = 1 := by simp [tensorPhase, norm_prod, hu]
  simpa only [Complex.star_def, hn, one_pow, Complex.ofReal_one] using
    Complex.mul_conj' (tensorPhase u x)

/-- The repeated local diagonal is an actual unitary matrix when its local entries are phases. -/
theorem tensor_diagonal_unitary (u : L → ℂ) (hu : ∀ a, ‖u a‖ = 1) :
    diagonal (tensorPhase (I := I) u) ∈ Matrix.unitaryGroup (I → L) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Pi.mul_def, Pi.star_apply, phase_unit u hu,
    Matrix.diagonal_one]

private lemma split_phase_product (u : L → ℂ) (hu : ∀ a, ‖u a‖ = 1)
    (a b : I) (hab : a ≠ b) (v w : L × L)
    (c : {i : I // i ≠ a ∧ i ≠ b} → L) :
    tensorPhase u ((edgeSplit a b hab).symm (v,c)) *
      star (tensorPhase u ((edgeSplit a b hab).symm (w,c))) =
        (u v.1 * u v.2) * star (u w.1 * u w.2) := by
  simp only [tensorPhase, star_prod, ← Finset.prod_mul_distrib]
  have h (i : I) :
      u ((edgeSplit a b hab).symm (v,c) i) *
        star (u ((edgeSplit a b hab).symm (w,c) i)) =
      (if i = a then u v.1 * star (u w.1) else 1) *
        (if i = b then u v.2 * star (u w.2) else 1) := by
    by_cases ha : i = a
    · subst i
      simp [edgeSplit, hab]
    by_cases hb : i = b
    · subst i
      simp [edgeSplit, hab.symm]
    · have hm : u (c ⟨i,ha,hb⟩) * star (u (c ⟨i,ha,hb⟩)) = 1 := by
        simpa only [Complex.star_def, hu, one_pow, Complex.ofReal_one] using
          Complex.mul_conj' (u (c ⟨i,ha,hb⟩))
      simpa [edgeSplit, ha, hb] using hm
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true, star_mul]
  ring

/-- Every ordered two-register marginal transforms by the corresponding local diagonal.
All complement phases cancel, so the unnormalized partial trace has no dimension factor. -/
theorem edgeMarginal_diagonalAction (u : L → ℂ) (hu : ∀ a, ‖u a‖ = 1)
    (E : Matrix (I → L) (I → L) ℂ) (a b : I) (hab : a ≠ b) :
    edgeMarginal a b hab (diagonalAction u E) =
      diagonal (fun v : L × L => u v.1 * u v.2) * edgeMarginal a b hab E *
        (diagonal (fun v : L × L => u v.1 * u v.2))ᴴ := by
  ext v w
  simp only [edgeMarginal,
    D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
    Matrix.submatrix_apply, diagonalAction_apply, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply, Finset.mul_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  calc
    _ = (tensorPhase u ((edgeSplit a b hab).symm (v,c)) *
          star (tensorPhase u ((edgeSplit a b hab).symm (w,c)))) *
            E ((edgeSplit a b hab).symm (v,c)) ((edgeSplit a b hab).symm (w,c)) := by ring
    _ = _ := by rw [split_phase_product u hu]; ring

end
end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl
