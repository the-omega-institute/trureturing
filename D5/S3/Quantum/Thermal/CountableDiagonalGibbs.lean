/- GID: D5/S3/Quantum/Thermal/CountableDiagonalGibbs
   generality: G
   mirror-B: D5/B/S3/Quantum/Thermal/CountableDiagonalGibbs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct the maximal real diagonal Hamiltonian on actual l2, characterize its adjoint graph, and construct an absolutely summable rank-one Gibbs expansion. -/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-!
The carrier is Mathlib's infinite-dimensional complex Hilbert space l2 of the declared index type.
The Hamiltonian has its maximal square-summability domain. The adjoint graph
is defined by the usual inner-product test against every domain vector and
is proved to coincide with that graph. Gibbs operators are actual bounded
linear maps and are obtained as absolutely summable rank-one operator series.

This constructs the countable diagonal spectral model. It does not assert
that a given differential Schrodinger operator has already been unitarily
conjugated to this model, or that a general metaplectic factorization has
been proved. The canonical-basis trace below is not a proof of arbitrary
basis independence for a general trace-class operator.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Thermal.CountableDiagonalGibbs

open scoped ENNReal BigOperators ComplexInnerProductSpace Topology
open Filter

abbrev Hilbert (ι : Type*) := lp (fun _ : ι => ℂ) (2 : ℝ≥0∞)

section Diagonal
variable {ι : Type*} [DecidableEq ι]

/-- The maximal domain of multiplication by a real energy sequence. -/
def energyDomain (E : ι → ℝ) : Submodule ℂ (Hilbert ι) where
  carrier := {x | Memℓp (fun n => (E n : ℂ) * x n) 2}
  zero_mem' := by
    simpa only [lp.coeFn_zero, Pi.zero_apply, mul_zero] using
      (zero_mem_ℓp' : Memℓp (fun _ : ι => (0 : ℂ)) 2)
  add_mem' := by
    intro x y hx hy
    simpa only [lp.coeFn_add, Pi.add_apply, mul_add] using hx.add hy
  smul_mem' := by
    intro c x hx
    simpa only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm] using
      hx.const_smul c

/-- The unbounded operator, with the domain included in its type. -/
def hamiltonian (E : ι → ℝ) : energyDomain E →ₗ[ℂ] (Hilbert ι) where
  toFun x := ⟨fun n => (E n : ℂ) * x.val n, x.property⟩
  map_add' x y := by ext n; exact mul_add _ _ _
  map_smul' c x := by ext n; exact mul_left_comm _ _ _

@[simp] theorem hamiltonian_apply (E : ι → ℝ) (x : energyDomain E) (n : ι) :
    hamiltonian E x n = (E n : ℂ) * x.val n := rfl

/-- All canonical finitely supported vectors belong to the actual domain. -/
theorem single_mem_domain (E : ι → ℝ) (n : ι) (z : ℂ) :
    (lp.single 2 n z : (Hilbert ι)) ∈ energyDomain E := by
  have he : (fun k => (E k : ℂ) * (lp.single 2 n z : (Hilbert ι)) k) =
      (fun k => (lp.single 2 n ((E n : ℂ) * z) : (Hilbert ι)) k) := by
    funext k
    by_cases hk : k = n
    · subst k; simp
    · simp [lp.single_apply, hk, Ne.symm hk]
  change Memℓp _ 2
  rw [he]
  exact lp.memℓp _

def domainSingle (E : ι → ℝ) (n : ι) (z : ℂ) : energyDomain E :=
  ⟨lp.single 2 n z, single_mem_domain E n z⟩

@[simp] theorem hamiltonian_single (E : ι → ℝ) (n : ι) (z : ℂ) :
    hamiltonian E (domainSingle E n z) = lp.single 2 n ((E n : ℂ) * z) := by
  ext k
  by_cases hk : k = n
  · subst k; simp [domainSingle]
  · simp [domainSingle, lp.single_apply, hk, Ne.symm hk]

/-- Density follows from the convergent canonical finite-support expansions. -/
theorem energyDomain_dense (E : ι → ℝ) : Dense (energyDomain E : Set (Hilbert ι)) := by
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
  filter_upwards [] with s
  exact (energyDomain E).sum_mem (fun n _ => single_mem_domain E n (x n))

/-- Symmetry is proved by the actual summable l2 inner products. -/
theorem hamiltonian_symmetric (E : ι → ℝ) (x y : energyDomain E) :
    ⟪hamiltonian E x, y.val⟫_ℂ = ⟪x.val, hamiltonian E y⟫_ℂ := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [hamiltonian_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- The standard adjoint-graph test for the densely defined operator. -/
def InAdjointGraph (E : ι → ℝ) (y z : (Hilbert ι)) : Prop :=
  ∀ x : energyDomain E, ⟪hamiltonian E x, y⟫_ℂ = ⟪x.val, z⟫_ℂ

/-- Testing against canonical basis vectors constructs the adjoint domain.
This proves self-adjointness at the graph level, not just formal symmetry. -/
theorem adjoint_graph_iff (E : ι → ℝ) (y z : (Hilbert ι)) :
    InAdjointGraph E y z ↔
      ∃ hy : y ∈ energyDomain E, hamiltonian E ⟨y, hy⟩ = z := by
  constructor
  · intro h
    have he (n : ι) : (E n : ℂ) * y n = z n := by
      have hn := h (domainSingle E n 1)
      rw [hamiltonian_single] at hn
      simpa only [domainSingle, mul_one, lp.inner_single_left,
        RCLike.inner_apply, Complex.conj_ofReal, map_one, one_mul, mul_comm] using hn
    have hy : y ∈ energyDomain E := by
      change Memℓp (fun n => (E n : ℂ) * y n) 2
      simpa only [he] using lp.memℓp z
    refine ⟨hy, ?_⟩
    ext n
    exact he n
  · rintro ⟨hy, rfl⟩ x
    exact hamiltonian_symmetric E x ⟨y, hy⟩

/-- A bounded coordinate functional of norm at most one. -/
def coordinate (n : ι) : (Hilbert ι) →L[ℂ] ℂ :=
  (show (Hilbert ι) →ₗ[ℂ] ℂ from
    { toFun := fun x => x n
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }).mkContinuous 1 (fun x => by
        simpa only [one_mul] using lp.norm_apply_le_norm (by norm_num) x n)

@[simp] theorem coordinate_apply (n : ι) (x : (Hilbert ι)) : coordinate n x = x n := rfl

/-- A true rank-one orthogonal coordinate projection on the infinite (Hilbert ι) space. -/
def coordinateProjection (n : ι) : (Hilbert ι) →L[ℂ] (Hilbert ι) :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ι => ℂ) 2 n).comp (coordinate n)

@[simp] theorem coordinateProjection_apply (n : ι) (x : (Hilbert ι)) :
    coordinateProjection n x = lp.single 2 n (x n) := rfl

theorem coordinateProjection_norm (n : ι) : ‖coordinateProjection n‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound (by norm_num)
    intro x
    rw [coordinateProjection_apply, lp.norm_single (by norm_num), one_mul]
    exact lp.norm_apply_le_norm (by norm_num) x n
  · have h := (coordinateProjection n).le_opNorm (lp.single 2 n (1 : ℂ))
    simpa only [coordinateProjection_apply, lp.single_apply_self,
      lp.norm_single (by norm_num), norm_one, mul_one] using h

/-- Operator evaluation is continuous. It is used to identify an operator series
with its pointwise coordinate action, not to infer a norm limit from pointwise limits. -/
def evaluateAt (x : (Hilbert ι)) : ((Hilbert ι) →L[ℂ] (Hilbert ι)) →L[ℂ] (Hilbert ι) :=
  (show ((Hilbert ι) →L[ℂ] (Hilbert ι)) →ₗ[ℂ] (Hilbert ι) from
    { toFun := fun T => T x
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }).mkContinuous ‖x‖ (fun T => by
        simpa only [mul_comm] using T.le_opNorm x)

/-- Summability of diagonal coefficients gives operator-norm absolute summability. -/
theorem diagonal_series_summable (w : ι → ℂ) (hw : Summable (fun n => ‖w n‖)) :
    Summable (fun n => w n • coordinateProjection n) := by
  apply Summable.of_norm
  simpa only [norm_smul, coordinateProjection_norm, mul_one] using hw

/-- The operator is constructed by an absolutely convergent rank-one series. -/
def diagonalNuclear (w : ι → ℂ) : (Hilbert ι) →L[ℂ] (Hilbert ι) :=
  ∑' n, w n • coordinateProjection n

theorem diagonalNuclear_apply (w : ι → ℂ) (hw : Summable (fun n => ‖w n‖))
    (x : (Hilbert ι)) (k : ι) : diagonalNuclear w x k = w k * x k := by
  have hs := diagonal_series_summable w hw
  change ((coordinate k).comp (evaluateAt x)) (∑' n, w n • coordinateProjection n) = _
  rw [((coordinate k).comp (evaluateAt x)).map_tsum hs, tsum_eq_single k]
  · simp [evaluateAt, coordinateProjection_apply, smul_eq_mul]
  · intro n hn
    simp [evaluateAt, coordinateProjection_apply, lp.single_apply, hn, Ne.symm hn]

/-- Explicit normalized rank-one expansion: both its absolute summability and
its sum are proved for the operator just constructed. -/
theorem diagonal_nuclear_expansion (w : ι → ℂ) (hw : Summable (fun n => ‖w n‖)) :
    HasSum (fun n => w n • coordinateProjection n) (diagonalNuclear w) ∧
      Summable (fun n => ‖w n • coordinateProjection n‖) := by
  refine ⟨(diagonal_series_summable w hw).hasSum, ?_⟩
  simpa only [norm_smul, coordinateProjection_norm, mul_one] using hw

/-- The trace in the fixed complete canonical orthonormal basis. -/
def canonicalTrace (T : (Hilbert ι) →L[ℂ] (Hilbert ι)) : ℂ :=
  ∑' n, ⟪(lp.single 2 n 1 : (Hilbert ι)), T (lp.single 2 n 1)⟫_ℂ

theorem canonicalTrace_diagonal (w : ι → ℂ) (hw : Summable (fun n => ‖w n‖)) :
    canonicalTrace (diagonalNuclear w) = ∑' n, w n := by
  unfold canonicalTrace
  apply tsum_congr
  intro n
  rw [lp.inner_single_left, diagonalNuclear_apply w hw]
  simp [RCLike.inner_apply]

end Diagonal

/-- Positive one-mode harmonic-oscillator energies, including the zero-point term. -/
def energy (ω : ℝ) (n : ℕ) : ℝ := ω * ((n : ℝ) + 1 / 2)

def weight (β ω : ℝ) (n : ℕ) : ℝ := Real.exp (-β * energy ω n)

def partition (β ω : ℝ) : ℝ :=
  Real.exp (-β * ω / 2) / (1 - Real.exp (-β * ω))

theorem weight_geometric (β ω : ℝ) (n : ℕ) :
    weight β ω n = Real.exp (-β * ω / 2) * Real.exp (-β * ω) ^ n := by
  unfold weight energy
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

theorem weight_pos (β ω : ℝ) (n : ℕ) : 0 < weight β ω n := Real.exp_pos _

/-- Infinite thermal normalization, derived from the actual energies. -/
theorem oscillator_hasSum (β ω : ℝ) (hβ : 0 < β) (hω : 0 < ω) :
    HasSum (weight β ω) (partition β ω) := by
  have hr0 : 0 ≤ Real.exp (-β * ω) := (Real.exp_pos _).le
  have hr1 : Real.exp (-β * ω) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  simpa only [← weight_geometric, partition, div_eq_mul_inv] using
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-β * ω / 2))

theorem oscillator_weight_norm_summable (β ω : ℝ) (hβ : 0 < β) (hω : 0 < ω) :
    Summable (fun n => ‖(weight β ω n : ℂ)‖) := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_pos β ω _)] using
    (oscillator_hasSum β ω hβ hω).summable

/-- An actual bounded Gibbs operator on infinite l2, defined by its rank-one expansion. -/
def gibbsOperator (β ω : ℝ) : (Hilbert ℕ) →L[ℂ] (Hilbert ℕ) :=
  diagonalNuclear (fun n => (weight β ω n : ℂ))

theorem gibbsOperator_coordinates (β ω : ℝ) (hβ : 0 < β) (hω : 0 < ω)
    (x : (Hilbert ℕ)) (n : ℕ) :
    gibbsOperator β ω x n = (Real.exp (-β * energy ω n) : ℂ) * x n :=
  diagonalNuclear_apply _ (oscillator_weight_norm_summable β ω hβ hω) x n

/-- The full operator-norm rank-one series is absolutely convergent, not just its
scalar diagonal trace. This supplies an explicit nuclear decomposition. -/
theorem gibbs_nuclear_expansion (β ω : ℝ) (hβ : 0 < β) (hω : 0 < ω) :
    HasSum (fun n => (weight β ω n : ℂ) • coordinateProjection n) (gibbsOperator β ω) ∧
      Summable (fun n => ‖(weight β ω n : ℂ) • coordinateProjection n‖) :=
  diagonal_nuclear_expansion _ (oscillator_weight_norm_summable β ω hβ hω)

theorem gibbs_canonical_trace (β ω : ℝ) (hβ : 0 < β) (hω : 0 < ω) :
    canonicalTrace (gibbsOperator β ω) = (partition β ω : ℂ) := by
  rw [gibbsOperator, canonicalTrace_diagonal _ (oscillator_weight_norm_summable β ω hβ hω)]
  exact ((oscillator_hasSum β ω hβ hω).map Complex.ofRealCLM
    Complex.ofRealCLM.continuous).tsum_eq

/-- Composition is the thermal semigroup law for the actual infinite-dimensional operators. -/
theorem gibbs_semigroup (β γ ω : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (hω : 0 < ω) :
    (gibbsOperator β ω).comp (gibbsOperator γ ω) = gibbsOperator (β + γ) ω := by
  ext x n
  simp only [ContinuousLinearMap.comp_apply,
    gibbsOperator_coordinates β ω hβ hω,
    gibbsOperator_coordinates γ ω hγ hω,
    gibbsOperator_coordinates (β + γ) ω (add_pos hβ hγ) hω]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- Exact tail, with no finite (Hilbert ℕ)-space truncation hidden in the theorem. -/
theorem oscillator_tail_hasSum (β ω : ℝ) (hβ : 0 < β) (hω : 0 < ω) (N : ℕ) :
    HasSum (fun n => weight β ω (n + N))
      (partition β ω * Real.exp (-β * ω) ^ N) := by
  have hs := (oscillator_hasSum β ω hβ hω).mul_right (Real.exp (-β * ω) ^ N)
  convert hs using 1
  funext n
  simp only [weight_geometric, pow_add, mul_assoc]

/-- The oscillator is genuinely unbounded on its dense maximal domain. -/
theorem oscillator_unbounded (ω : ℝ) (hω : 0 < ω) (C : ℝ) :
    ∃ x : energyDomain (energy ω), ‖x.val‖ = 1 ∧ C < ‖hamiltonian (energy ω) x‖ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C / ω)
  have hC : C < energy ω n := by
    have hn' : C < (n : ℝ) * ω := (div_lt_iff₀ hω).mp hn
    unfold energy
    nlinarith
  have hE : 0 < energy ω n := by unfold energy; positivity
  refine ⟨domainSingle (energy ω) n 1, ?_, ?_⟩
  · simp [domainSingle, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  · rw [hamiltonian_single, lp.norm_single (by norm_num), mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE]
    exact hC

#print axioms adjoint_graph_iff
#print axioms energyDomain_dense
#print axioms gibbs_nuclear_expansion
#print axioms gibbs_canonical_trace
#print axioms oscillator_unbounded
end D5.S3.Quantum.Thermal.CountableDiagonalGibbs
