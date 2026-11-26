/- GID: D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Criterion
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Criterion
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Scalar criteria for coincident weak limits of symmetric hypercube walks. -/

import D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.ShellCoefficients
import D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.ExchangeableLaws
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Identify the finite position averages with the existing exchangeable-law interface. -/

section

open Finset MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace HypercubeWalsh

variable {d : ℕ}

def coordinatePerm (σ : Equiv.Perm (Fin d)) : Cube d ≃ Cube d where
  toFun x := x ∘ σ
  invFun x := x ∘ σ.symm
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

private theorem character_coordinatePerm (σ : Equiv.Perm (Fin d)) (a x : Cube d) :
    character (coordinatePerm σ a) (coordinatePerm σ x) = character a x :=
  Equiv.prod_comp σ (fun i => sign (a i && x i))

@[simp] private theorem weight_coordinatePerm (σ : Equiv.Perm (Fin d)) (x : Cube d) :
    weight (coordinatePerm σ x) = weight x := by
  unfold weight
  have h : support (coordinatePerm σ x) = (support x).map σ.symm.toEmbedding := by
    ext i
    simp only [mem_support, mem_map, Equiv.toEmbedding_apply]
    change x (σ i) = true ↔ ∃ j, x j = true ∧ σ.symm j = i
    constructor
    · intro hi
      exact ⟨σ i, hi, σ.symm_apply_apply i⟩
    · rintro ⟨j, hj, he⟩
      have he' : j = σ i := by simpa using congrArg σ he
      exact he' ▸ hj
  rw [h, card_map]

private theorem positionExpansion_coordinatePerm (σ : Equiv.Perm (Fin d))
    (f : Cube d → Cube d → ℝ)
    (hf : ∀ a b, f (coordinatePerm σ a) (coordinatePerm σ b) = f a b) (x : Cube d) :
    positionExpansion f (coordinatePerm σ x) = positionExpansion f x := by
  unfold positionExpansion
  congr 1
  let e := coordinatePerm σ
  rw [← e.sum_comp (fun a => ∑ b, (basis a (e x) * basis b (e x)) * f a b)]
  apply sum_congr rfl
  intro a _
  rw [← e.sum_comp (fun b => (basis (e a) (e x) * basis b (e x)) * f (e a) b)]
  apply sum_congr rfl
  intro b _
  change (basis (coordinatePerm σ a) (coordinatePerm σ x) *
      basis (coordinatePerm σ b) (coordinatePerm σ x)) *
      f (coordinatePerm σ a) (coordinatePerm σ b) = _
  simp only [basis, character_coordinatePerm, hf]

variable (K : Kernel (Cube d)) (ρ : ℕ → ℝ)
    (hρ : ∀ a, eigen K a = ρ (weight a))

include hρ in
private theorem continuousLimit_coordinatePerm (σ : Equiv.Perm (Fin d)) (a b : Cube d) :
    K.continuousLimit (characterBit (coordinatePerm σ a)) (characterBit (coordinatePerm σ b)) =
      K.continuousLimit (characterBit a) (characterBit b) := by
  unfold Kernel.continuousLimit
  change (if eigen K (coordinatePerm σ a) = eigen K (coordinatePerm σ b) then 1 else 0) =
    if eigen K a = eigen K b then 1 else 0
  simp only [hρ, weight_coordinatePerm]

include hρ in
private theorem pairGap_coordinatePerm (σ : Equiv.Perm (Fin d)) (a b : Cube d) :
    K.pairGap (characterBit (coordinatePerm σ a)) (characterBit (coordinatePerm σ b)) =
      K.pairGap (characterBit a) (characterBit b) := by
  unfold Kernel.pairGap
  simp only [← characterBit_xor]
  change (if eigen K (coordinatePerm σ a) = eigen K (coordinatePerm σ b) ∧
      |eigen K (coordinatePerm σ a)| < 1 then
      (1 - eigen K (coordinatePerm σ (xor a b))) /
        (2 * (1 - eigen K (coordinatePerm σ a) ^ 2)) else 0) =
    if eigen K a = eigen K b ∧ |eigen K a| < 1 then
      (1 - eigen K (xor a b)) / (2 * (1 - eigen K a ^ 2)) else 0
  simp only [hρ, weight_coordinatePerm]

include hρ in
private theorem discreteLimit_coordinatePerm (σ : Equiv.Perm (Fin d)) (a b : Cube d) :
    K.discreteLimit (characterBit (coordinatePerm σ a)) (characterBit (coordinatePerm σ b)) =
      K.discreteLimit (characterBit a) (characterBit b) := by
  have h := K.pair_limit_sub (characterBit (coordinatePerm σ a)) (characterBit (coordinatePerm σ b))
  rw [pairGap_coordinatePerm K ρ hρ, continuousLimit_coordinatePerm K ρ hρ, ← K.pair_limit_sub] at h
  linarith

include hρ in
private theorem continuousAverage_coordinatePerm (σ : Equiv.Perm (Fin d)) (x : Cube d) :
    continuousAverage K (coordinatePerm σ x) = continuousAverage K x :=
  positionExpansion_coordinatePerm σ _ (continuousLimit_coordinatePerm K ρ hρ σ) x

include hρ in
private theorem discreteAverage_coordinatePerm (σ : Equiv.Perm (Fin d)) (x : Cube d) :
    discreteAverage K (coordinatePerm σ x) = discreteAverage K x :=
  positionExpansion_coordinatePerm σ _ (discreteLimit_coordinatePerm K ρ hρ σ) x

noncomputable def pmfOfMass (p : Cube d → ℝ) (hp : ∀ x, 0 ≤ p x) (ht : ∑ x, p x = 1) :
    PMF (Cube d) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (p x))
    (by rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hp x), ht, ENNReal.ofReal_one])

noncomputable def probabilityOfMass (p : Cube d → ℝ) (hp : ∀ x, 0 ≤ p x) (ht : ∑ x, p x = 1) :
    ProbabilityMeasure (Cube d) :=
  (pmfOfMass p hp ht).toMeasure.toProbabilityMeasure

private theorem probabilityOfMass_exchangeable (p : Cube d → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ht : ∑ x, p x = 1)
    (hperm : ∀ (σ : Equiv.Perm (Fin d)) (x : Cube d), p (coordinatePerm σ x) = p x) :
    HypercubeExchangeable.Exchangeable (probabilityOfMass p hp ht) := by
  intro σ
  let e := coordinatePerm σ
  have he : Measurable (e : Cube d → Cube d) := measurable_of_finite _
  refine ⟨he, ?_⟩
  change Measure.map e (pmfOfMass p hp ht).toMeasure = (pmfOfMass p hp ht).toMeasure
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply he hs, PMF.toMeasure_apply_fintype, PMF.toMeasure_apply_fintype]
  rw [← e.sum_comp (fun x => s.indicator (pmfOfMass p hp ht) x)]
  apply sum_congr rfl
  intro x _
  simp only [Set.indicator, Set.mem_preimage, pmfOfMass, PMF.ofFintype_apply, e, hperm]
  rfl

def embeddingCharacter {k : ℕ} (c : Fin k ↪ Fin d) : Cube d :=
  ofSupport (univ.map c)

@[simp] private theorem weight_embeddingCharacter {k : ℕ} (c : Fin k ↪ Fin d) :
    weight (embeddingCharacter c) = k := by simp [weight, embeddingCharacter]

private theorem character_embeddingCharacter {k : ℕ} (c : Fin k ↪ Fin d) (x : Cube d) :
    character (embeddingCharacter c) x = HypercubeExchangeable.tupleSign x c := by
  unfold character HypercubeExchangeable.tupleSign
  have h (i : Fin d) : sign (embeddingCharacter c i && x i) =
      if i ∈ univ.map c then sign (x i) else 1 := by
    by_cases hi : i ∈ univ.map c <;> simp [embeddingCharacter, ofSupport, hi]
  simp_rw [h, ← prod_filter]
  rw [filter_mem_eq_inter, univ_inter, prod_map]
  rfl

private theorem probabilityOfMass_walshCoefficient
    (p : Cube d → ℝ) (hp : ∀ x, 0 ≤ p x) (ht : ∑ x, p x = 1)
    {k : ℕ} (c : Fin k ↪ Fin d) :
    HypercubeExchangeable.walshCoefficient (probabilityOfMass p hp ht) c =
      walshCoefficient p (embeddingCharacter c) := by
  change (∫ x, HypercubeExchangeable.tupleSign x c ∂(pmfOfMass p hp ht).toMeasure) = _
  rw [PMF.integral_eq_sum]
  unfold walshCoefficient
  apply sum_congr rfl
  intro x _
  simp [pmfOfMass, ENNReal.toReal_ofReal (hp x), character_embeddingCharacter, mul_comm]

noncomputable def continuousLaw : ProbabilityMeasure (Cube d) :=
  probabilityOfMass (continuousAverage K) (continuousAverage_nonneg K) (continuousAverage_total K)

noncomputable def discreteLaw : ProbabilityMeasure (Cube d) :=
  probabilityOfMass (discreteAverage K) (discreteAverage_nonneg K) (discreteAverage_total K)

include hρ in
private theorem continuousLaw_exchangeable : HypercubeExchangeable.Exchangeable (continuousLaw K) :=
  probabilityOfMass_exchangeable _ _ _ (continuousAverage_coordinatePerm K ρ hρ)

include hρ in
private theorem discreteLaw_exchangeable : HypercubeExchangeable.Exchangeable (discreteLaw K) :=
  probabilityOfMass_exchangeable _ _ _ (discreteAverage_coordinatePerm K ρ hρ)

include hρ in
private theorem law_walsh_gap_of_profile {k : ℕ} (c : Fin k ↪ Fin d) :
    HypercubeExchangeable.walshCoefficient (continuousLaw K) c -
      HypercubeExchangeable.walshCoefficient (discreteLaw K) c = delta d ρ k := by
  unfold continuousLaw discreteLaw
  simp only [probabilityOfMass_walshCoefficient, ← weight_embeddingCharacter c]
  exact finite_shell_gap_of_profile K ρ hρ (embeddingCharacter c)

include hρ in
private theorem law_walsh_collisions_of_profile {k : ℕ} (c : Fin k ↪ Fin d) :
    HypercubeExchangeable.walshCoefficient (continuousLaw K) c = collisions d ρ k := by
  unfold continuousLaw
  rw [probabilityOfMass_walshCoefficient, finite_shell_collisions_of_profile K ρ hρ,
    weight_embeddingCharacter]

end HypercubeWalsh

end

section

/-! Apply the previously checked weak-limit bridge to the concrete shell kernels. -/

open Filter Finset MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false

namespace HypercubeWalsh

variable (w : ℕ → ℕ → ℝ) (hw : ∀ d h, h ≤ d → 0 ≤ w d h)
  (ht : ∀ d, ∑ h ∈ range (d + 1), w d h = 1)

noncomputable def continuousShellLaw (d : ℕ) : ProbabilityMeasure (Cube d) :=
  continuousLaw (shellKernel d (w d) (hw d) (ht d))

noncomputable def discreteShellLaw (d : ℕ) : ProbabilityMeasure (Cube d) :=
  discreteLaw (shellKernel d (w d) (hw d) (ht d))

private theorem continuousShellLaw_exchangeable (d : ℕ) :
    HypercubeExchangeable.Exchangeable (continuousShellLaw w hw ht d) :=
  continuousLaw_exchangeable _ _ (eigen_eq_krawtchouk (w d) (hw d) (ht d))

private theorem discreteShellLaw_exchangeable (d : ℕ) :
    HypercubeExchangeable.Exchangeable (discreteShellLaw w hw ht d) :=
  discreteLaw_exchangeable _ _ (eigen_eq_krawtchouk (w d) (hw d) (ht d))

private theorem eventually_gap (k : ℕ) :
    ∀ᶠ d in atTop, ∃ c : Fin k ↪ Fin d,
      delta d (rho d (w d)) k =
        HypercubeExchangeable.walshCoefficient (continuousShellLaw w hw ht d) c -
        HypercubeExchangeable.walshCoefficient (discreteShellLaw w hw ht d) c := by
  filter_upwards [eventually_ge_atTop k] with d hd
  exact ⟨Fin.castLEEmb hd, (law_walsh_gap_of_profile _ _
    (eigen_eq_krawtchouk (w d) (hw d) (ht d)) _).symm⟩

private theorem eventually_collisions (k : ℕ) :
    ∀ᶠ d in atTop, ∃ c : Fin k ↪ Fin d,
      collisions d (rho d (w d)) k =
        HypercubeExchangeable.walshCoefficient (continuousShellLaw w hw ht d) c := by
  filter_upwards [eventually_ge_atTop k] with d hd
  exact ⟨Fin.castLEEmb hd, (law_walsh_collisions_of_profile _ _
    (eigen_eq_krawtchouk (w d) (hw d) (ht d)) _).symm⟩

theorem exists_common_shell_weakLimit_iff :
    (∃ π : ProbabilityMeasure HypercubeWeakLimit.UnitInterval,
      Tendsto (fun d => HypercubeExchangeable.radialLaw (continuousShellLaw w hw ht d))
        atTop (𝓝 π) ∧
      Tendsto (fun d => HypercubeExchangeable.radialLaw (discreteShellLaw w hw ht d)) atTop (𝓝 π)) ↔
    (∀ k : ℕ, 0 < k → Tendsto (fun d => delta d (rho d (w d)) k) atTop (𝓝 0)) ∧
    (∀ k : ℕ, 0 < k → ∃ m : ℝ, Tendsto (fun d => collisions d (rho d (w d)) k) atTop (𝓝 m)) :=
  HypercubeExchangeable.exists_common_weakLimit_iff_finiteCoefficients
    (continuousShellLaw w hw ht) (discreteShellLaw w hw ht)
    (continuousShellLaw_exchangeable w hw ht) (discreteShellLaw_exchangeable w hw ht)
    (fun d => collisions d (rho d (w d))) (fun d => delta d (rho d (w d)))
    (fun k _ => eventually_collisions w hw ht k) (fun k _ => eventually_gap w hw ht k)

theorem shell_continuous_tests_gap_iff :
    (∀ f : C(↑HypercubeWeakLimit.UnitInterval, ℝ),
      Tendsto (fun d =>
        (∫ x, f x ∂↑(HypercubeExchangeable.radialLaw (continuousShellLaw w hw ht d))) -
          (∫ x, f x ∂↑(HypercubeExchangeable.radialLaw (discreteShellLaw w hw ht d))))
        atTop (𝓝 0)) ↔
    ∀ k : ℕ, 0 < k → Tendsto (fun d => delta d (rho d (w d)) k) atTop (𝓝 0) :=
  HypercubeExchangeable.tendsto_integral_sub_iff_tendsto_finiteGap
    (continuousShellLaw w hw ht) (discreteShellLaw w hw ht)
    (continuousShellLaw_exchangeable w hw ht) (discreteShellLaw_exchangeable w hw ht)
    (fun d => delta d (rho d (w d))) (fun k _ => eventually_gap w hw ht k)

/-- Once either radial law is known to converge to `π`, the same limit holds for
both walks exactly when every fixed positive-weight CT–DT Walsh gap vanishes. -/
theorem common_shell_weakLimit_iff_gap
    (π : ProbabilityMeasure HypercubeWeakLimit.UnitInterval)
    (h : Tendsto (fun d => HypercubeExchangeable.radialLaw (continuousShellLaw w hw ht d))
        atTop (𝓝 π) ∨
      Tendsto (fun d => HypercubeExchangeable.radialLaw (discreteShellLaw w hw ht d))
        atTop (𝓝 π)) :
    (Tendsto (fun d => HypercubeExchangeable.radialLaw (continuousShellLaw w hw ht d))
        atTop (𝓝 π) ∧
      Tendsto (fun d => HypercubeExchangeable.radialLaw (discreteShellLaw w hw ht d))
        atTop (𝓝 π)) ↔
    ∀ k : ℕ, 0 < k → Tendsto (fun d => delta d (rho d (w d)) k) atTop (𝓝 0) :=
  HypercubeExchangeable.common_weakLimit_iff_tendsto_finiteGap
    (continuousShellLaw w hw ht) (discreteShellLaw w hw ht)
    (continuousShellLaw_exchangeable w hw ht) (discreteShellLaw_exchangeable w hw ht)
    (fun d => delta d (rho d (w d))) (fun k _ => eventually_gap w hw ht k) π h

/-- The collision limit at each order is the corresponding shifted moment of the CT limit
and hence of any common limit. -/
theorem tendsto_shell_collisions_to_shiftedMoment
    (π : ProbabilityMeasure HypercubeWeakLimit.UnitInterval)
    (h : Tendsto (fun d => HypercubeExchangeable.radialLaw (continuousShellLaw w hw ht d))
      atTop (𝓝 π)) (k : ℕ) :
    Tendsto (fun d => collisions d (rho d (w d)) k) atTop
      (𝓝 (HypercubeWeakLimit.shiftedMoment π k)) := by
  have herr : Tendsto (fun d => collisions d (rho d (w d)) k -
      HypercubeWeakLimit.shiftedMoment
        (HypercubeExchangeable.radialLaw (continuousShellLaw w hw ht d)) k) atTop (𝓝 0) := by
    apply squeeze_zero_norm'
      _ (tendsto_const_div_atTop_nhds_zero_nat ((k : ℝ) * ((k : ℝ) - 1)))
    filter_upwards [eventually_collisions w hw ht k] with d hd
    obtain ⟨c, hc⟩ := hd
    rw [Real.norm_eq_abs, hc]
    exact HypercubeExchangeable.abs_walshCoefficient_sub_shiftedMoment_le
      (continuousShellLaw w hw ht d) (continuousShellLaw_exchangeable w hw ht d) c
  have hmoment : Tendsto (fun d => HypercubeWeakLimit.shiftedMoment
      (HypercubeExchangeable.radialLaw (continuousShellLaw w hw ht d)) k) atTop
      (𝓝 (HypercubeWeakLimit.shiftedMoment π k)) := by
    exact (HypercubeWeakLimit.continuous_shiftedMoment k).continuousAt.tendsto.comp h
  simpa using herr.add hmoment

end HypercubeWalsh

end
