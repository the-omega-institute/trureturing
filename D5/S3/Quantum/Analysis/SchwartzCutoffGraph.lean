/- GID: D5/S3/Quantum/Analysis/SchwartzCutoffGraph
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/SchwartzCutoffGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Schwartz cutoffs converge in the actual Euclidean L2 differential graph norm. -/

/-
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Modified 2026 by Anthropic PBC.
Adapted from the W21_approximation argument in trureturing
D5/S3/Weil/ZetaPntBase/Sobolev.lean at 43cdec3b5cfa62c75aac586f4edc2066e2cac4ca;
its source chain is anthropics/zeta-23-lean at
3635e74826a4c1fcece7d1cd2b6fa75e43a00510 and
AlexKontorovich/PrimeNumberTheoremAnd at 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01,
PrimeNumberTheoremAnd/Sobolev.lean.
Changes: actual complex Lebesgue L2 in every finite Euclidean dimension,
squared dominated convergence, directional product and scaling rules,
and simultaneous convergence for the full quadratic differential sum.
Full licenses and applicable NOTICE:
docs/reports/oscillator-suppliers/sobolev-zeta-LICENSE.txt,
docs/reports/oscillator-suppliers/sobolev-pnt-LICENSE.txt,
docs/reports/oscillator-suppliers/sobolev-zeta-NOTICE.txt.
The pinned PNT tree has no NOTICE-named file.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

open SchwartzMap MeasureTheory Filter LineDeriv
open scoped Topology LineDeriv ENNReal
noncomputable section
namespace D5.S3.Quantum.Analysis.SchwartzCutoffGraph

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def differential (d : ℕ) (a b : Fin d → ℝ) (f : 𝓢(Space d, ℂ)) : 𝓢(Space d, ℂ) :=
  ∑ j, ((-a j) • (∂_{(EuclideanSpace.basisFun (Fin d) ℝ) j}
    (∂_{(EuclideanSpace.basisFun (Fin d) ℝ) j} f)) +
    b j • SchwartzMap.smulLeftCLM ℂ (fun x : Space d => x j ^ 2) f)

set_option maxHeartbeats 800000 in
theorem scaled_cutoff_graph (d : ℕ) (a b : Fin d → ℝ) (f : 𝓢(Space d, ℂ))
    (χ : 𝓢(Space d, ℝ)) (hχ : HasCompactSupport χ) (hzero : χ 0 = 1)
    (hbound : ∀ x, ‖χ x‖ ≤ 1) :
    ∃ ψ : ℕ → 𝓢(Space d, ℂ),
      (∀ n x, ψ n x = χ (((n : ℝ) + 1)⁻¹ • x) • f x) ∧
      (∀ n, HasCompactSupport (ψ n)) ∧
      Tendsto (fun n => (ψ n).toLp 2 volume) atTop (𝓝 (f.toLp 2 volume)) ∧
      Tendsto (fun n => (differential d a b (ψ n)).toLp 2 volume) atTop
        (𝓝 ((differential d a b f).toLp 2 volume)) := by
  classical
  let E := Space d
  let J := SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure E)
  let r : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hrpos : ∀ n, 0 < r n := fun n => by dsimp [r]; positivity
  have hrle : ∀ n, r n ≤ 1 := fun n => by
    dsimp [r]
    exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hr : Tendsto r atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  let σ : ℕ → E ≃L[ℝ] E := fun n =>
    (LinearEquiv.smulOfNeZero ℝ E (r n) (ne_of_gt (hrpos n))).toContinuousLinearEquiv
  let C : ℕ → 𝓢(E, ℝ) →L[ℝ] 𝓢(E, ℝ) := fun n =>
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (σ n)
  let θ : ℕ → 𝓢(E, ℝ) := fun n => C n χ
  let P : 𝓢(E, ℝ) → 𝓢(E, ℂ) → 𝓢(E, ℂ) := fun u v =>
    SchwartzMap.smulLeftCLM ℂ (u : E → ℝ) v
  have hC (n : ℕ) (u : 𝓢(E, ℝ)) (x : E) : C n u x = u (r n • x) := rfl
  have hP (u : 𝓢(E, ℝ)) (v : 𝓢(E, ℂ)) (x : E) : P u v x = u x • v x := by
    exact SchwartzMap.smulLeftCLM_apply_apply u.hasTemperateGrowth v x
  have hprod (u : 𝓢(E, ℝ)) (v : 𝓢(E, ℂ)) (w : E) :
      ∂_{w} (P u v) = P (∂_{w} u) v + P u (∂_{w} v) := by
    ext x
    simp only [add_apply, hP, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have heq : (P u v : E → ℂ) = fun x => u x • v x := funext (hP u v)
    rw [heq, fderiv_fun_smul u.differentiableAt v.differentiableAt]
    simp [add_comm]
  have hscale (u : 𝓢(E, ℝ)) (w : E) (n : ℕ) :
      ∂_{w} (C n u) = r n • C n (∂_{w} u) := by
    rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv]
    change C n (∂_{r n • w} u) = _
    rw [lineDerivOp_left_smul, map_smul]
  have hscale2 (u : 𝓢(E, ℝ)) (w : E) (n : ℕ) :
      ∂_{w} (∂_{w} (C n u)) = (r n)^2 • C n (∂_{w} (∂_{w} u)) := by
    rw [hscale, lineDerivOp_smul, hscale, smul_smul, pow_two]
  have hsmul_limit (u : 𝓢(E, ℂ)) (q : ℕ → E → ℝ)
      (hq : ∀ n, (q n).HasTemperateGrowth) (B : ℝ)
      (hb : ∀ n x, ‖q n x‖ ≤ B) (ht : ∀ x, Tendsto (fun n => q n x) atTop (𝓝 0)) :
      Tendsto (fun n => J (SchwartzMap.smulLeftCLM ℂ (q n) u)) atTop (𝓝 0) := by
    let F : ℕ → E → ℝ := fun n x => ‖q n x • u x‖ ^ 2
    have hint : Tendsto (fun n => ∫ x, F n x) atTop (𝓝 0) := by
      have hm : ∀ᶠ n in atTop, AEStronglyMeasurable (F n) volume :=
        Eventually.of_forall fun n =>
          (((hq n).1.continuous.smul u.continuous).norm.pow 2).aestronglyMeasurable
      have hdom : ∀ᶠ n in atTop, ∀ᵐ x ∂volume, ‖F n x‖ ≤ B^2 * ‖u x‖^2 := by
        filter_upwards with n
        filter_upwards with x
        change ‖‖q n x • u x‖ ^ 2‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_smul, mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb n x) 2)
          (sq_nonneg _)
      have hi : Integrable (fun x : E => B^2 * ‖u x‖^2) volume :=
        ((u.memLp 2 volume).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul _
      have hl : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (𝓝 0) := by
        filter_upwards with x
        simpa [F] using ((ht x).smul (tendsto_const_nhds (x := u x))).norm.pow 2
      simpa using tendsto_integral_filter_of_dominated_convergence _ hm hdom hi hl
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : ∀ n, ‖J (SchwartzMap.smulLeftCLM ℂ (q n) u)‖ =
        Real.sqrt (∫ x, F n x) := by
      intro n
      change ‖(SchwartzMap.smulLeftCLM ℂ (q n) u).toLp 2 volume‖ = _
      rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
      simp [F, SchwartzMap.smulLeftCLM_apply_apply (hq n), Real.sqrt_eq_rpow]
    simpa only [heq, Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hint
  have hθ_lim (u : 𝓢(E, ℂ)) : Tendsto (fun n => J (P (θ n) u)) atTop (𝓝 (J u)) := by
    let q : ℕ → E → ℝ := fun n x => θ n x - 1
    have hq : ∀ n, (q n).HasTemperateGrowth := fun n =>
      (θ n).hasTemperateGrowth.sub (Function.HasTemperateGrowth.const 1)
    have hb : ∀ n x, ‖q n x‖ ≤ 2 := by
      intro n x
      change ‖θ n x - 1‖ ≤ 2
      calc ‖θ n x - 1‖ ≤ ‖θ n x‖ + 1 := by simpa using norm_sub_le (θ n x) 1
        _ ≤ 1 + 1 := by
          have ht : ‖θ n x‖ ≤ 1 := by
            change ‖χ (r n • x)‖ ≤ 1
            exact hbound (r n • x)
          linarith
        _ = 2 := by norm_num
    have ht : ∀ x, Tendsto (fun n => q n x) atTop (𝓝 0) := by
      intro x
      have hx : Tendsto (fun n => r n • x) atTop (𝓝 0) := by
        simpa using hr.smul (tendsto_const_nhds (x := x))
      simpa [q, θ, hC, hzero] using (χ.continuous.continuousAt.tendsto.comp hx).sub_const 1
    have h := hsmul_limit u q hq 2 hb ht
    rw [← tendsto_sub_nhds_zero_iff]
    convert h using 1
    funext n
    rw [← map_sub]
    congr 1
    ext x
    simp [hP, SchwartzMap.smulLeftCLM_apply_apply (hq n), q, sub_smul]
  have hdecay_lim (u : 𝓢(E, ℂ)) (χ' : 𝓢(E, ℝ)) (k : ℕ) (hk : 0 < k) :
      Tendsto (fun n => J (P ((r n)^k • C n χ') u)) atTop (𝓝 0) := by
    let B := SchwartzMap.seminorm ℝ 0 0 χ'
    apply hsmul_limit u (fun n x => ((r n)^k • C n χ') x)
      (fun n => ((r n)^k • C n χ').hasTemperateGrowth) B ?_ ?_
    · intro n x
      simp only [smul_apply, hC, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (hrpos n).le k)]
      calc (r n)^k * ‖χ' (r n • x)‖ ≤ 1 * ‖χ' (r n • x)‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (hrpos n).le (hrle n)) (norm_nonneg _)
        _ ≤ B := by simpa using χ'.norm_le_seminorm ℝ (r n • x)
    · intro x
      have hx : Tendsto (fun n => r n • x) atTop (𝓝 0) := by
        simpa using hr.smul (tendsto_const_nhds (x := x))
      have hp : Tendsto (fun n => (r n)^k) atTop (𝓝 0) := by simpa [hk.ne'] using hr.pow k
      simpa [smul_apply, hC] using hp.smul (χ'.continuous.continuousAt.tendsto.comp hx)
  let ψ : ℕ → 𝓢(E, ℂ) := fun n => P (θ n) f
  refine ⟨ψ, fun n x => by simpa [ψ, θ, hC, r] using hP (θ n) f x, ?_, hθ_lim f, ?_⟩
  · intro n
    have heq : (ψ n : E → ℂ) = fun x => χ (r n • x) • f x := by
      funext x; simp [ψ, θ, hC, hP]
    rw [heq]
    exact (hχ.comp_smul (ne_of_gt (hrpos n))).smul_right
  · have hd (w : E) : Tendsto (fun n => J (∂_{w} (∂_{w} (ψ n)))) atTop
        (𝓝 (J (∂_{w} (∂_{w} f)))) := by
      have hD (n : ℕ) : ∂_{w} (∂_{w} (ψ n)) =
          P (∂_{w} (∂_{w} (θ n))) f +
          (2 : ℝ) • P (∂_{w} (θ n)) (∂_{w} f) + P (θ n) (∂_{w} (∂_{w} f)) := by
        simp only [ψ, hprod, lineDerivOp_add, two_smul]
        abel
      -- The same bound-and-DCT argument applies to the second directional cutoff derivative.
      have h2 := hdecay_lim (∂_{w} f) (∂_{w} χ) 1 (by norm_num)
      have hsecond : Tendsto (fun n => J (P (∂_{w} (∂_{w} (θ n))) f)) atTop (𝓝 0) := by
        simpa only [θ, hscale2] using hdecay_lim f (∂_{w} (∂_{w} χ)) 2 (by norm_num)
      have hfirst : Tendsto (fun n => J (P (∂_{w} (θ n)) (∂_{w} f))) atTop (𝓝 0) := by
        simpa [θ, hscale, pow_one] using h2
      have h := (hsecond.add (hfirst.const_smul (2 : ℝ))).add (hθ_lim (∂_{w} (∂_{w} f)))
      simpa [hD, map_add, map_smul] using h
    have hv (j : Fin d) : Tendsto (fun n =>
        J (SchwartzMap.smulLeftCLM ℂ (fun x : E => x j ^ 2) (ψ n))) atTop
          (𝓝 (J (SchwartzMap.smulLeftCLM ℂ (fun x : E => x j ^ 2) f))) := by
      have hp : (fun x : E => x j ^ 2).HasTemperateGrowth :=
        (EuclideanSpace.proj j).hasTemperateGrowth.pow 2
      convert hθ_lim (SchwartzMap.smulLeftCLM ℂ (fun x : E => x j ^ 2) f) using 1
      funext n
      congr 1
      ext x
      simp [ψ, hP, SchwartzMap.smulLeftCLM_apply_apply hp]
      ring
    have h := tendsto_finsetSum Finset.univ (fun j _ =>
      ((hd ((EuclideanSpace.basisFun (Fin d) ℝ) j)).const_smul (-a j)).add ((hv j).const_smul (b j)))
    change Tendsto (fun n => J (differential d a b (ψ n))) atTop
      (𝓝 (J (differential d a b f)))
    simpa [differential, map_sum, map_add, map_smul] using h

#print axioms scaled_cutoff_graph
end D5.S3.Quantum.Analysis.SchwartzCutoffGraph
