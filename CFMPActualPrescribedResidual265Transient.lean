import CFMPActualEnergySecond264Transient
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Sqrt

noncomputable section
universe u265 v265
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped BigOperators Topology ContDiff
open D5.S3.Geometry.Hyperideal.FourCycleCurvature
open CFMPGenuineLengthNeighborhood435Transient (genuine)
open CFMPOriginalCovolumeNeighborhood251Transient
open CFMPGlobalGenuineCovolume256Transient
open CFMPActualGlobalEnergy259Transient
open CFMPActualGlobalHessian260Transient
open CFMPActualCompactHessian261Transient

namespace CFMPActualPrescribedResidual265Transient

theorem compact_actual_antimonotonicity_and_residual
    (C : Set Lengths) (hC : IsCompact C) (hsub : C ⊆ {a : Lengths | genuine a}) :
    ∃ mu : ℝ, 0 < mu ∧
      ∀ (T : Type u265) (E : Type v265) [Fintype T] [Fintype E] [DecidableEq E]
        (s : Incidence T E) (a b : E → ℝ),
        (∀ p ∈ Icc a b, ∀ t : T, localRead s t p ∈ C) →
        (∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
          mu * (∑ e : E, (degree s e : ℝ) * (y e - x e)^2) ≤
            -(∑ e : E, (physicalCurvature s y e - physicalCurvature s x e) *
              (y e - x e))) ∧
        (∀ kappa c : E → ℝ, c ∈ Icc a b → physicalCurvature s c = kappa →
          (∀ e : E, kappa e ≠ 2 * Real.pi) →
          (∀ e : E, 0 < (degree s e : ℝ)) ∧
          ∀ l ∈ Icc a b,
            mu * Real.sqrt (∑ e : E, (degree s e : ℝ) * (l e - c e)^2) ≤
              Real.sqrt (∑ e : E, (physicalCurvature s l e - kappa e)^2 /
                (degree s e : ℝ)) ∧
            (physicalCurvature s l = kappa → l = c)) := by
  obtain ⟨mu,bound,hmu,_hbound,hfinite⟩ := compact_actual_global_degree_bounds C hC hsub
  refine ⟨mu,hmu,?_⟩
  intro T E _ _ _ s a b hreads
  classical
  let K : (E → ℝ) → (E → ℝ) := physicalCurvature s
  have hdiff (p : E → ℝ) (hp : p ∈ Icc a b) : DifferentiableAt ℝ K p :=
    (physicalCurvature_hasFDerivAt s p (fun t => hsub (hreads p hp t))).differentiableAt
  have hbound (p : E → ℝ) (hp : p ∈ Icc a b) (v : E → ℝ) :
      mu * (∑ e : E, (degree s e : ℝ) * (v e)^2) ≤
        -(∑ e : E, v e * (fderiv ℝ K p v) e) :=
    (hfinite T E s wholeFamily wholeFamily_realized p (hreads p hp) v).1
  have hanti (x : E → ℝ) (hx : x ∈ Icc a b) (y : E → ℝ) (hy : y ∈ Icc a b) :
      mu * (∑ e, (degree s e : ℝ) * (y e - x e)^2) ≤
        -(∑ e, (K y e - K x e) * (y e - x e)) := by
    let v : E → ℝ := y - x
    let γ : ℝ → (E → ℝ) := fun t => x + t • v
    let g : ℝ → ℝ := fun t => -(∑ e, v e * K (γ t) e)
    have hγmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ Icc a b :=
      (convex_Icc a b).add_smul_sub_mem hx hy ht
    have hγderiv (t : ℝ) : HasDerivAt γ v t := by
      simpa only [γ, one_smul] using! ((hasDerivAt_id t).smul_const v).const_add x
    have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        HasDerivAt g (-(∑ e, v e * (fderiv ℝ K (γ t) v) e)) t := by
      have hk : HasDerivAt (fun u => K (γ u)) (fderiv ℝ K (γ t) v) t :=
        (hdiff (γ t) (hγmem t ht)).hasFDerivAt.comp_hasDerivAt t (hγderiv t)
      have hke (e : E) : HasDerivAt (fun u => K (γ u) e)
          ((fderiv ℝ K (γ t) v) e) t := by
        simpa only [Function.comp_def] using!
          (ContinuousLinearMap.proj e).hasFDerivAt.comp_hasDerivAt t hk
      exact (HasDerivAt.fun_sum fun e _ => (hke e).const_mul (v e)).neg
    have hm := (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
      (f := g)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [(hg t (interior_subset ht)).deriv]
        exact hbound (γ t) (hγmem t (interior_subset ht)) v)
      0 (by constructor <;> norm_num) 1 (by constructor <;> norm_num) (by norm_num)
    have hg0 : g 0 = -(∑ e, v e * K x e) := by simp [g, γ]
    have hγ1 : γ 1 = y := by
      simp [γ, v]
    have hg1 : g 1 = -(∑ e, v e * K y e) := by simp only [g, hγ1]
    have hend : g 1 - g 0 = -(∑ e, (K y e - K x e) * (y e - x e)) := by
      calc
        g 1 - g 0 = -(∑ e, v e * (K y e - K x e)) := by
          rw [hg1, hg0]
          simp only [mul_sub, Finset.sum_sub_distrib]
          ring
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro e _
          change (y e - x e) * (K y e - K x e) = _
          ring
    simpa only [sub_zero, mul_one, hend, v, Pi.sub_apply] using hm
  refine ⟨hanti,?_⟩
  intro kappa lstar hstar hzero hkappa
  have hdegree (e : E) : 0 < (degree s e : ℝ) := by
    have hnat : degree s e ≠ 0 := by
      intro hz
      have he : star s e = ∅ :=
        Finset.card_eq_zero.mp (show (star s e).card = 0 from hz)
      have hk := congrFun hzero e
      change 2 * Real.pi - ∑ o ∈ star s e,
        angle s (fun j => Real.cosh (lstar j)) o = kappa e at hk
      simp only [he,Finset.sum_empty,sub_zero] at hk
      exact hkappa e hk.symm
    exact_mod_cast Nat.pos_of_ne_zero hnat
  refine ⟨hdegree,?_⟩
  intro l hl
  let W : ℝ := ∑ e, (degree s e : ℝ) * (l e - lstar e)^2
  let S : ℝ := ∑ e, (K l e - kappa e)^2 / (degree s e : ℝ)
  have hW : 0 ≤ W :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (hdegree e).le (sq_nonneg _))
  have hstrong : mu * W ≤ -(∑ e, (K l e - kappa e) * (l e - lstar e)) := by
    simpa only [K, hzero] using hanti lstar hstar l hl
  have hcauchy : -(∑ e, (K l e - kappa e) * (l e - lstar e)) ≤ Real.sqrt W * Real.sqrt S := by
    have hroot (e : E) : Real.sqrt (degree s e : ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (hdegree e)).ne'
    have hf (e : E) :
        (Real.sqrt (degree s e : ℝ) * (l e - lstar e))^2 =
          (degree s e : ℝ) * (l e - lstar e)^2 := by
      rw [mul_pow, Real.sq_sqrt (hdegree e).le]
    have hg (e : E) :
        (-(K l e - kappa e) / Real.sqrt (degree s e : ℝ))^2 =
          (K l e - kappa e)^2 / (degree s e : ℝ) := by
      rw [div_pow, neg_sq, Real.sq_sqrt (hdegree e).le]
    have hp (e : E) :
        (Real.sqrt (degree s e : ℝ) * (l e - lstar e)) *
            (-(K l e - kappa e) / Real.sqrt (degree s e : ℝ)) =
          -((K l e - kappa e) * (l e - lstar e)) := by
      field_simp [hroot e]
      <;> ring
    have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun e => Real.sqrt (degree s e : ℝ) * (l e - lstar e))
      (fun e => -(K l e - kappa e) / Real.sqrt (degree s e : ℝ))
    simpa only [hf, hg, hp, Finset.sum_neg_distrib] using hc
  constructor
  · change mu * Real.sqrt W ≤ Real.sqrt S
    by_cases hz : Real.sqrt W = 0
    · simpa only [hz, mul_zero] using Real.sqrt_nonneg S
    · have hr : 0 < Real.sqrt W :=
        lt_of_le_of_ne (Real.sqrt_nonneg W) (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ hr).mp
      calc
        Real.sqrt W * (mu * Real.sqrt W) = mu * (Real.sqrt W)^2 := by ring
        _ = mu * W := by rw [Real.sq_sqrt hW]
        _ ≤ Real.sqrt W * Real.sqrt S := hstrong.trans hcauchy
  · intro hzl
    have hwzero : W = 0 := by
      have hh : mu * W ≤ 0 := by simpa only [K, hzl, sub_self, zero_mul,
        Finset.sum_const_zero, neg_zero] using hstrong
      nlinarith
    funext e
    have hterm : (degree s e : ℝ) * (l e - lstar e)^2 ≤ W := by
      exact Finset.single_le_sum
        (f := fun j => (degree s j : ℝ) * (l j - lstar j)^2)
        (fun j _ => mul_nonneg (hdegree j).le (sq_nonneg _)) (Finset.mem_univ e)
    have htermzero : (degree s e : ℝ) * (l e - lstar e)^2 = 0 :=
      le_antisymm (by simpa only [hwzero] using hterm)
        (mul_nonneg (hdegree e).le (sq_nonneg _))
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp
      ((mul_eq_zero.mp htermzero).resolve_left (hdegree e).ne'))
end CFMPActualPrescribedResidual265Transient

run_cmd do
  let name := ``CFMPActualPrescribedResidual265Transient.compact_actual_antimonotonicity_and_residual
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP265 actual prescribed residual theorem absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP265 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP265 CHECKED {name} axioms={axioms}"
