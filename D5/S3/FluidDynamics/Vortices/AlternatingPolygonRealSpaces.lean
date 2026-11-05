/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual real stable and unstable spaces, with dimensions 2*(m-2). -/

import D5.S3.FluidDynamics.Vortices.AlternatingPolygonComplexSpectrum
import Mathlib.LinearAlgebra.DFinsupp

/-! Real eigenspaces and their complete positive and negative spectral sums. -/
noncomputable section
open scoped BigOperators

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
open AlternatingPolygonSpectrum AlternatingPolygonModes AlternatingPolygonMultiplicity
open AlternatingPolygonJordan AlternatingPolygonComplexSpectrum

abbrev RealCartesian (m : ℕ) := Fin (2 * m) ⊕ Fin (2 * m) → ℝ

def realOperator (m : ℕ) : Module.End ℝ (RealCartesian m) := (jacobian (2 * m)).toLin'

/-- The faithful real inclusion into the actual complexified Cartesian space. -/
def complexify (m : ℕ) : RealCartesian m →ₗ[ℝ] Cartesian m where
  toFun v p := (v p : ℂ)
  map_add' v w := by ext p; simp
  map_smul' c v := by ext p; simp

theorem complexify_injective (m : ℕ) : Function.Injective (complexify m) := by
  intro v w h
  funext p
  exact Complex.ofReal_inj.mp (congrFun h p)

theorem complexify_operator (m : ℕ) (v : RealCartesian m) :
    complexify m (realOperator m v) = actualOperator m (complexify m v) := by
  ext p
  simp [complexify, realOperator, actualOperator, Matrix.mulVec, dotProduct]

private theorem complexify_shift (m : ℕ) (μ : ℝ) (v : RealCartesian m) :
    complexify m ((realOperator m - μ • (1 : Module.End ℝ (RealCartesian m))) v) =
      (actualOperator m - (μ : ℂ) • (1 : Module.End ℂ (Cartesian m))) (complexify m v) := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    map_sub, complexify_operator, map_smul]
  rfl

private theorem complexify_shift_pow (m : ℕ) (μ : ℝ) (n : ℕ) (v : RealCartesian m) :
    complexify m (((realOperator m - μ • (1 : Module.End ℝ (RealCartesian m))) ^ n) v) =
      ((actualOperator m - (μ : ℂ) • (1 : Module.End ℂ (Cartesian m))) ^ n)
        (complexify m v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [complexify_shift, ih]

/-- Nonzero semisimplicity also holds over the original real displacement space. -/
theorem real_nonzero_semisimple (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
    {μ : ℝ} (hμ : μ ≠ 0) :
    (realOperator m).maxGenEigenspace μ = (realOperator m).eigenspace μ := by
  apply le_antisymm
  · intro v hv
    obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hv
    have hv' : complexify m v ∈ (actualOperator m).maxGenEigenspace (μ : ℂ) := by
      apply (Module.End.mem_maxGenEigenspace _ _ _).mpr
      exact ⟨n, by rw [← complexify_shift_pow, hn, map_zero]⟩
    rw [actual_nonzero_semisimple m hm (Complex.ofReal_ne_zero.mpr hμ),
      Module.End.mem_eigenspace_iff] at hv'
    rw [Module.End.mem_eigenspace_iff]
    apply complexify_injective m
    rw [complexify_operator, map_smul]
    exact hv'
  · exact Module.End.eigenspace_le_maxGenEigenspace

/-- Every signed real root has a two-dimensional real eigenspace. -/
theorem real_geometric_multiplicity (m : ℕ) [NeZero (2 * m)] (hm : 3 ≤ m)
    {r : ℕ} (hr : 2 ≤ r) (hrm : r < m) (μ : ℝ)
    (hμ : μ = positiveRoot m r ∨ μ = -positiveRoot m r) :
    Module.finrank ℝ ((realOperator m).eigenspace μ) = 2 := by
  have hn : μ ≠ 0 := by
    rcases hμ with rfl | rfl
    · exact ne_of_gt (positiveRoot_pos m r hr hrm)
    · exact neg_ne_zero.mpr (ne_of_gt (positiveRoot_pos m r hr hrm))
  rw [← real_nonzero_semisimple m (by omega) hn,
    LinearMap.finrank_maxGenEigenspace_eq, realOperator, Matrix.charpoly_toLin',
    Polynomial.eq_rootMultiplicity_map (f := Complex.ofRealHom) Complex.ofReal_injective μ,
    ← Matrix.charpoly_map]
  have hs : (μ : ℂ) ^ 2 = (squaredValue m r : ℂ) := by
    rw [← Complex.ofReal_pow]
    congr 1
    rcases hμ with rfl | rfl
    · exact positiveRoot_sq m r hr
    · rw [neg_sq]; exact positiveRoot_sq m r hr
  simpa [show r ≠ 0 by omega, show r ≠ m by omega] using
    algebraic_multiplicity_of_mode m (by omega) (le_of_lt hrm) (μ : ℂ)
      (Complex.ofReal_ne_zero.mpr hn) hs

private theorem positiveRoot_injective (m : ℕ) (hm : 3 ≤ m) :
    Function.Injective (fun k : Fin (m - 2) => positiveRoot m (k.val + 2)) := by
  intro k l h
  have hk : k.val + 2 < m := by omega
  have hl : l.val + 2 < m := by omega
  have hs := congrArg (fun x : ℝ => x ^ 2) h
  rw [positiveRoot_sq m _ (by omega), positiveRoot_sq m _ (by omega)] at hs
  have he := (squaredValue_injective m (by omega) (le_of_lt hk) (le_of_lt hl)).mp hs
  apply Fin.ext
  omega

/-- The ordinary spectral sum for one sign; each summand is an actual real eigenspace. -/
def spectralSum (m : ℕ) (s : ℝ) :
    (∀ k : Fin (m - 2), (realOperator m).eigenspace (s * positiveRoot m (k.val + 2)))
      →ₗ[ℝ] RealCartesian m where
  toFun v := ∑ k, (v k).val
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum]

def unstableSpace (m : ℕ) : Submodule ℝ (RealCartesian m) := (spectralSum m 1).range
def stableSpace (m : ℕ) : Submodule ℝ (RealCartesian m) := (spectralSum m (-1)).range

private theorem spectralSum_injective (m : ℕ) (hm : 3 ≤ m) (s : ℝ) (hs : s ≠ 0) :
    Function.Injective (spectralSum m s) := by
  have hi : Function.Injective (fun k : Fin (m - 2) => s * positiveRoot m (k.val + 2)) :=
    (mul_right_injective₀ hs).comp (positiveRoot_injective m hm)
  have hind := (realOperator m).eigenspaces_iSupIndep.comp hi
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hz := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind
    Finset.univ (fun k => (v k).val) (fun k _ => (v k).property) hv
  funext k
  apply Subtype.ext
  exact hz k (Finset.mem_univ _)

theorem unstable_finrank (m : ℕ) [NeZero (2 * m)] (hm : 3 ≤ m) :
    Module.finrank ℝ (unstableSpace m) = 2 * (m - 2) := by
  rw [unstableSpace, LinearMap.finrank_range_of_inj
    (spectralSum_injective m hm 1 one_ne_zero), Module.finrank_pi_fintype]
  have he (k : Fin (m - 2)) :
      Module.finrank ℝ ((realOperator m).eigenspace (1 * positiveRoot m (k.val + 2))) = 2 := by
    apply real_geometric_multiplicity m hm (r := k.val + 2) (by omega) (by omega)
    exact Or.inl (one_mul _)
  simp_rw [he]
  simp [mul_comm]

theorem stable_finrank (m : ℕ) [NeZero (2 * m)] (hm : 3 ≤ m) :
    Module.finrank ℝ (stableSpace m) = 2 * (m - 2) := by
  rw [stableSpace, LinearMap.finrank_range_of_inj
    (spectralSum_injective m hm (-1) (by norm_num)), Module.finrank_pi_fintype]
  have he (k : Fin (m - 2)) :
      Module.finrank ℝ ((realOperator m).eigenspace (-1 * positiveRoot m (k.val + 2))) = 2 := by
    apply real_geometric_multiplicity m hm (r := k.val + 2) (by omega) (by omega)
    exact Or.inr (neg_one_mul _)
  simp_rw [he]
  simp [mul_comm]

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
