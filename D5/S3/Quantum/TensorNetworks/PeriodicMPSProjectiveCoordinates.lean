/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSProjectiveCoordinates
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSProjectiveCoordinates
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Basic]
   utility: none
   digest: Compact projector coordinates and affine ratios for complex projective space. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Matrix.Mul

/-! A trace-one rank-one projector represents its complex ray in compact
matrix coordinates. Ratios in a nonzero column recover the affine chart. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectiveCoordinates

open Set Matrix
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι]

noncomputable section

/-- Squared Euclidean mass of complex coordinates indexed by a finite set. -/
def mass (p : ι → ℂ) : ℝ := ∑ i, Complex.normSq (p i)

private theorem mass_nonneg (p : ι → ℂ) : 0 ≤ mass p :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (p i)

theorem mass_pos (p : ι → ℂ) (hp : p ≠ 0) : 0 < mass p := by
  apply lt_of_le_of_ne (mass_nonneg p)
  intro h
  apply hp
  funext i
  exact Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Complex.normSq_nonneg (p j))).mp h.symm i (Finset.mem_univ _))

private theorem mass_scale (z : ℂ) (p : ι → ℂ) :
    mass (z • p) = Complex.normSq z * mass p := by
  simp [mass, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum]

/-- The rank-one matrix with entries `p i * conj (p j)`. -/
def outer (p : ι → ℂ) : Matrix ι ι ℂ := fun i j => p i * conj (p j)

theorem continuous_mass : Continuous (mass (ι := ι)) :=
  continuous_finsetSum _ fun i _ => Complex.continuous_normSq.comp (continuous_apply i)

theorem continuous_outer : Continuous (outer (ι := ι)) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply i).mul (Complex.continuous_conj.comp (continuous_apply j))

/-- Compact coordinates for the complex projective space of the given dimension. -/
def projective : Set (Matrix ι ι ℂ) := outer '' {p : ι → ℂ | mass p = 1}

theorem isCompact_projective : IsCompact (projective (ι := ι)) := by
  have hc : IsClosed {p : ι → ℂ | mass p = 1} := isClosed_eq continuous_mass continuous_const
  have hsubset : {p : ι → ℂ | mass p = 1} ⊆
      Set.pi Set.univ (fun _ : ι => Metric.closedBall (0 : ℂ) 1) := by
    intro p hp i _
    rw [Metric.mem_closedBall, dist_zero_right]
    have hi : Complex.normSq (p i) ≤ mass p :=
      Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (p j)) (Finset.mem_univ i)
    change mass p = 1 at hp
    rw [hp, ← Complex.sq_norm] at hi
    nlinarith [norm_nonneg (p i)]
  exact ((isCompact_univ_pi fun _ : ι =>
    isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hc hsubset).image continuous_outer

/-- Every nonzero vector has a trace-one rank-one projector. -/
def projector (p : ι → ℂ) : Matrix ι ι ℂ := (mass p)⁻¹ • outer p

theorem continuousAt_projector {p : ι → ℂ} (hp : p ≠ 0) :
    ContinuousAt projector p :=
  (continuous_mass.continuousAt.inv₀ (mass_pos p hp).ne').smul continuous_outer.continuousAt

theorem projector_mem (p : ι → ℂ) (hp : p ≠ 0) : projector p ∈ projective := by
  let z : ℝ := (Real.sqrt (mass p))⁻¹
  have hm := mass_pos p hp
  have hz : z ^ 2 = (mass p)⁻¹ := by
    dsimp [z]
    rw [inv_pow, Real.sq_sqrt hm.le]
  have hn : Complex.normSq (z : ℂ) = (mass p)⁻¹ := by
    simpa [Complex.normSq_ofReal, pow_two] using hz
  refine ⟨(z : ℂ) • p, ?_, ?_⟩
  · change mass ((z : ℂ) • p) = 1
    rw [mass_scale, hn, inv_mul_cancel₀ hm.ne']
  · ext i j
    simp only [outer, Pi.smul_apply, smul_eq_mul, map_mul, projector, Matrix.smul_apply]
    rw [← hn, Complex.real_smul, ← Complex.mul_conj]
    ring

/-- On an affine chart with representative coordinate `j` nonzero, the
projector column recovers each ratio `p i / p j`. -/
theorem projector_ratio (p : ι → ℂ) (i j : ι) (hj : p j ≠ 0) :
    projector p i j / projector p j j = p i / p j := by
  have hp : p ≠ 0 := fun h => hj (congrFun h j)
  have hm := mass_pos p hp
  have hc : conj (p j) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hj
  change ((mass p)⁻¹ : ℝ) • (p i * conj (p j)) /
      (((mass p)⁻¹ : ℝ) • (p j * conj (p j))) = _
  rw [Complex.real_smul, Complex.real_smul]
  let c : ℂ := (((mass p)⁻¹ : ℝ) : ℂ) * conj (p j)
  have hn : c ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero hm.ne')) hc
  have rearrange (x : ℂ) :
      (((mass p)⁻¹ : ℝ) : ℂ) * (x * conj (p j)) = x * c := by dsimp [c]; ring
  rw [rearrange, rearrange, mul_div_mul_right _ _ hn]

theorem projector_diag_ne_zero_iff (p : ι → ℂ) (j : ι) :
    projector p j j ≠ 0 ↔ p j ≠ 0 := by
  constructor
  · intro h hj
    exact h (by simp [projector, outer, hj, Matrix.smul_apply])
  · intro hj
    have hm := (mass_pos p (fun h => hj (congrFun h j))).ne'
    have hc := (map_ne_zero (starRingEnd ℂ)).2 hj
    exact smul_ne_zero (inv_ne_zero hm) (mul_ne_zero hj hc)

/-- Equal projectors identify the underlying nonzero complex rays. -/
theorem eq_smul_of_projector_eq {p q : ι → ℂ} (hp : p ≠ 0)
    (h : projector p = projector q) :
    ∃ z : ℂ, z ≠ 0 ∧ q = z • p := by
  have hex : ∃ j : ι, p j ≠ 0 := by
    by_contra! hzero
    exact hp (funext hzero)
  obtain ⟨j, hj⟩ := hex
  have hq : q j ≠ 0 := by
    apply (projector_diag_ne_zero_iff q j).1
    rw [← h]
    exact (projector_diag_ne_zero_iff p j).2 hj
  refine ⟨q j / p j, div_ne_zero hq hj, ?_⟩
  funext i
  have hr : p i / p j = q i / q j := by
    rw [← projector_ratio _ _ _ hj, ← projector_ratio _ _ _ hq, h]
  change q i = (q j / p j) * p i
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hj).2
  exact (div_eq_div_iff hj hq).1 hr |>.symm.trans (mul_comm _ _)

/-- Multiplying a representative by a nonzero complex number preserves the
projector coordinates. -/
theorem projector_scale (p : ι → ℂ) {z : ℂ} (hz : z ≠ 0) :
    projector (z • p) = projector p := by
  have hm : Complex.normSq z ≠ 0 := fun h => hz (Complex.normSq_eq_zero.mp h)
  have ho : outer (z • p) = Complex.normSq z • outer p := by
    ext i j
    simp only [outer, Matrix.smul_apply, Complex.real_smul, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← Complex.mul_conj]
    ring
  rw [projector, mass_scale, ho, mul_inv, smul_smul, projector, mul_right_comm,
    inv_mul_cancel₀ hm, one_mul]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSProjectiveCoordinates
