/- GID: D5/S3/Quantum/Matrix/StolarskyMean/Spectral
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/StolarskyMean/Spectral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional negativity and positive subspaces control positive eigenvalue counts. -/

import D5.S3.Quantum.Matrix.StolarskyMean.Defs
import D5.S3.Weil.ZetaLinear.Sylvester

/-! Conditional negativity bounds the dimension of every positive spectral subspace. -/

noncomputable section
open Finset Matrix
open scoped BigOperators

namespace D5.S3.Quantum.Matrix.StolarskyMean.Spectral

open Defs

/-- Conditional negativity on the hyperplane of vectors whose coordinates sum to zero. -/
def ConditionallyNegative {n : ℕ} (M : _root_.Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ c : Fin n → ℝ, (∑ i, c i) = 0 → c ⬝ᵥ (M *ᵥ c) ≤ 0

private theorem numPosEig_eq_posIndex {n : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) :
    numPosEig M = RHLinalg.posIndex hM := by
  simp only [numPosEig, dite_eq_left hM, RHLinalg.posIndex]

/-- A conditionally negative real symmetric matrix with one positive diagonal
entry has exactly one strictly positive eigenvalue. -/
theorem numPosEig_eq_one {n : ℕ} {M : _root_.Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) (hcnd : ConditionallyNegative M)
    (hdiag : ∃ i, 0 < M i i) : numPosEig M = 1 := by
  classical
  rw [numPosEig_eq_posIndex hM]
  obtain ⟨W, hW, hdim⟩ := RHLinalg.posIndex_eq_max_finrank_posDefOn hM
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ i, x i
      map_add' := by intros; simp [Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.mul_sum] }
  have hinj : Function.Injective (L.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxW⟩ hx
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hx
    change (∑ i, x i) = 0 at hx
    change (⟨x, hxW⟩ : W) = 0
    apply Subtype.ext
    by_contra hne
    have hp := hW x hxW hne
    have hn := hcnd x hx
    simpa only [RHLinalg.hermForm, RCLike.re_to_real, star_trivial] using
      (not_lt_of_ge hn hp)
  have hu : RHLinalg.posIndex hM ≤ 1 := by
    rw [← hdim]
    simpa using (LinearMap.finrank_le_finrank_of_injective hinj)
  have hl : 0 < RHLinalg.posIndex hM := by
    by_contra hz
    have hz' : RHLinalg.posIndex hM = 0 := by omega
    have he : ∀ i, hM.eigenvalues i ≤ 0 := by
      intro i
      have hn : ¬ 0 < hM.eigenvalues i := by
        intro hi
        have hm : i ∈ (univ.filter fun j => 0 < hM.eigenvalues j) := by simp [hi]
        have := Finset.card_pos.mpr ⟨i, hm⟩
        change 0 < RHLinalg.posIndex hM at this
        omega
      exact le_of_not_gt hn
    obtain ⟨i, hi⟩ := hdiag
    have hn := RHLinalg.hermForm_le_of_eigenvalues_le hM he (Pi.single i 1)
    have hv : RHLinalg.hermForm M (Pi.single i 1) = M i i := by
      simp [RHLinalg.hermForm, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv, zero_mul] at hn
    exact (not_lt_of_ge hn hi)
  omega

/-- Positive entries and conditional negativity place a nonempty symmetric
matrix in class A. -/
theorem inClassA_of_conditionallyNegative {n : ℕ}
    {M : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hM : M.IsHermitian) (hpos : ∀ i j, 0 < M i j)
    (hcnd : ConditionallyNegative M) : InClassA M :=
  ⟨hpos, numPosEig_eq_one hM hcnd ⟨0, hpos 0 0⟩⟩

/-- A positive definite subspace of dimension at least two forces at least
two strictly positive eigenvalues, counted with multiplicity. -/
theorem two_le_numPosEig_of_posDefOn {n : ℕ}
    {M : _root_.Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    {W : Submodule ℝ (Fin n → ℝ)} (hdim : 2 ≤ Module.finrank ℝ W)
    (hW : RHLinalg.PosDefOn M W) : 2 ≤ numPosEig M := by
  rw [numPosEig_eq_posIndex hM]
  exact hdim.trans (RHLinalg.finrank_le_posIndex_of_posDefOn hM hW)

end D5.S3.Quantum.Matrix.StolarskyMean.Spectral
