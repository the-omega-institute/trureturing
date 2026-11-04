/- GID: D5/S3/Analytic/Probability/EfronStein
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/EfronStein
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded finite-product Efron-Stein inequality from the credited CoarseGraining source port. -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0, retained in docs/reports/licenses/coarsegraining-efron-stein/LICENSE.txt.
Source: scottnarmstrong/CoarseGraining revision 310d1a6bab3ba2d398cdaffec32f3c9d4b5a24be,
Homogenization/Probability/EfronStein/{TwoPoint,ProdDecomp,Fin}.lean.
Modified for the receiver's mathlib API and consolidated into one host; the proof structure
and mathematical statement are preserved. Matching-pin mirror LeanPool/lean-pool revision
2c977d55c4bff8cde334058fee22200999d67a8b was acknowledged but is not a dependency.
The source license and attribution chain are retained in the referenced license file.
-/

import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi


/-
Copyright (c) 2026. All rights reserved.
-/


/-!
# Two-point variance identity and a Jensen bound

Building blocks for the Efron–Stein inequality.

* `Homogenization.variance_eq_half_integral_sub_sq`: for a bounded measurable
  real random variable `X` on a probability space,
  `Var[X] = ½ ∫∫ (X a − X b)² dμ dμ`.
* `Homogenization.sq_integral_le_integral_sq`: Jensen's inequality in the
  form `(∫ X)² ≤ ∫ X²` for a bounded measurable `X` on a probability space.

Everything is stated for *bounded* observables, which makes all integrability
side conditions immediate; no `L²`-generality is attempted.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Homogenization

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

section Bounded

variable {X : Ω → ℝ} (hX : Measurable X) {M : ℝ} (hM : ∀ ω, |X ω| ≤ M)

include hX hM

/-- A bounded measurable function is `MemLp 2` on a probability (finite) measure. -/
private theorem memLp_two_of_bound : MemLp X 2 μ :=
  memLp_of_bounded (Eventually.of_forall fun ω => abs_le.mp (hM ω)) hX.aestronglyMeasurable 2

/-- A bounded measurable function is integrable on a probability (finite) measure. -/
private theorem integrable_of_bound : Integrable X μ :=
  (memLp_two_of_bound μ hX hM).integrable one_le_two

/-- The square of a bounded measurable function is integrable. -/
private theorem integrable_sq_of_bound : Integrable (fun ω => (X ω) ^ 2) μ :=
  (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mp (memLp_two_of_bound μ hX hM)

end Bounded

/-- **Two-point variance identity.** For a bounded measurable real random variable
`X` on a probability space, the variance equals one half of the mean squared
difference of two independent samples. -/
private theorem variance_eq_half_integral_sub_sq {X : Ω → ℝ} (hX : Measurable X) {M : ℝ}
    (hM : ∀ ω, |X ω| ≤ M) :
    Var[X; μ] = (1 / 2) * ∫ a, ∫ b, (X a - X b) ^ 2 ∂μ ∂μ := by
  set m : ℝ := ∫ ω, X ω ∂μ with hm
  set s : ℝ := ∫ ω, (X ω) ^ 2 ∂μ with hs
  have hintX : Integrable X μ := integrable_of_bound μ hX hM
  have hintXsq : Integrable (fun ω => (X ω) ^ 2) μ := integrable_sq_of_bound μ hX hM
  -- inner integral, for each fixed `a`
  have hinner : ∀ a, ∫ b, (X a - X b) ^ 2 ∂μ = (X a) ^ 2 - 2 * (X a) * m + s := by
    intro a
    have hcongr : ∀ b, (X a - X b) ^ 2 = (X a) ^ 2 - (2 * X a) * X b + (X b) ^ 2 := by
      intro b; ring
    calc
      ∫ b, (X a - X b) ^ 2 ∂μ
          = ∫ b, ((X a) ^ 2 - (2 * X a) * X b + (X b) ^ 2) ∂μ := by
            simp_rw [hcongr]
      _ = (∫ _b, (X a) ^ 2 ∂μ) - (∫ b, (2 * X a) * X b ∂μ) + ∫ b, (X b) ^ 2 ∂μ := by
            rw [integral_add, integral_sub]
            · exact integrable_const _
            · exact hintX.const_mul _
            · exact (integrable_const _).sub (hintX.const_mul _)
            · exact hintXsq
      _ = (X a) ^ 2 - 2 * (X a) * m + s := by
            rw [integral_const, integral_const_mul]
            simp [hm, hs, mul_assoc]
  -- outer integral
  have houter :
      ∫ a, ∫ b, (X a - X b) ^ 2 ∂μ ∂μ = 2 * s - 2 * m ^ 2 := by
    simp_rw [hinner]
    have hcongr : ∀ a, (X a) ^ 2 - 2 * (X a) * m + s
        = (X a) ^ 2 - (2 * m) * X a + s := by intro a; ring
    calc
      ∫ a, ((X a) ^ 2 - 2 * (X a) * m + s) ∂μ
          = ∫ a, ((X a) ^ 2 - (2 * m) * X a + s) ∂μ := by simp_rw [hcongr]
      _ = (∫ a, (X a) ^ 2 ∂μ) - (∫ a, (2 * m) * X a ∂μ) + ∫ _a, s ∂μ := by
            rw [integral_add, integral_sub]
            · exact hintXsq
            · exact hintX.const_mul _
            · exact hintXsq.sub (hintX.const_mul _)
            · exact integrable_const _
      _ = 2 * s - 2 * m ^ 2 := by
            rw [integral_const, integral_const_mul]
            simp only [hm, hs, probReal_univ, smul_eq_mul]
            ring
  rw [houter, variance_eq_sub (memLp_two_of_bound μ hX hM)]
  simp only [Pi.pow_apply]
  rw [← hs, ← hm]
  ring

/-- **Jensen's inequality**, `(∫ X)² ≤ ∫ X²`, for a bounded measurable function on
a probability space. -/
private theorem sq_integral_le_integral_sq {X : Ω → ℝ} (hX : Measurable X) {M : ℝ}
    (hM : ∀ ω, |X ω| ≤ M) :
    (∫ ω, X ω ∂μ) ^ 2 ≤ ∫ ω, (X ω) ^ 2 ∂μ := by
  have h := variance_nonneg X μ
  rw [variance_eq_sub (memLp_two_of_bound μ hX hM)] at h
  simp only [Pi.pow_apply] at h
  linarith

end Homogenization

/-
Copyright (c) 2026. All rights reserved.
-/


/-!
# Two-factor variance decomposition

The "law of total variance" for a product of two probability measures, proved by
direct Fubini computation for *bounded* observables (no `condExp`).

* `Homogenization.variance_prod_eq`: for a bounded measurable `F : α × β → ℝ`
  and probability measures `P, Q`,
  `Var[F; P ⊗ Q] = ∫ b, Var[F(·,b); P] dQ + Var[b ↦ ∫ F(·,b) dP; Q]`.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Homogenization

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (P : Measure α) (Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- **Two-factor variance decomposition** (law of total variance for a product of
two probability measures), bounded-observable form.  Here the first coordinate is
"integrated out": `g b := ∫ a, F (a, b) ∂P` is the conditional mean. -/
private theorem variance_prod_eq {F : α × β → ℝ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ p, |F p| ≤ M) :
    Var[F; P.prod Q]
      = (∫ b, Var[fun a => F (a, b); P] ∂Q)
        + Var[fun b => ∫ a, F (a, b) ∂P; Q] := by
  classical
  set g : β → ℝ := fun b => ∫ a, F (a, b) ∂P with hg_def
  set m : ℝ := ∫ p, F p ∂(P.prod Q) with hm_def
  -- basic measurability / integrability
  have hFab : ∀ b, Measurable fun a => F (a, b) := fun b =>
    hF.comp (measurable_id.prodMk measurable_const)
  have hFab_int : ∀ b, Integrable (fun a => F (a, b)) P := fun b =>
    integrable_of_bound P (hFab b) (fun a => hM _)
  have hg : Measurable g := hF.stronglyMeasurable.integral_prod_left'.measurable
  have hgb : ∀ b, g b = ∫ a, F (a, b) ∂P := fun b => by simp only [hg_def]
  have hFint : Integrable F (P.prod Q) := integrable_of_bound _ hF hM
  -- `g` is bounded by `M`
  have hMg : ∀ b, |g b| ≤ M := by
    intro b
    rw [hgb b]
    calc |∫ a, F (a, b) ∂P| ≤ ∫ a, |F (a, b)| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _a, M ∂P := integral_mono (hFab_int b).abs (integrable_const M) (fun a => hM _)
      _ = M := by simp
  -- `m = ∫ g` under `Q`
  have hmg : m = ∫ b, g b ∂Q := by
    rw [hm_def, integral_prod_symm F hFint]
  -- pointwise bound on the centred difference
  have hdmeas : ∀ b, Measurable fun a => F (a, b) - g b := fun b =>
    (hFab b).sub measurable_const
  have hdbound : ∀ b a, |F (a, b) - g b| ≤ 2 * M := by
    intro b a
    have h := abs_add_le (F (a, b)) (-(g b))
    rw [← sub_eq_add_neg, abs_neg] at h
    calc |F (a, b) - g b| ≤ |F (a, b)| + |g b| := h
      _ ≤ M + M := add_le_add (hM _) (hMg b)
      _ = 2 * M := by ring
  -- key pointwise-in-`b` identity
  have key : ∀ b, ∫ a, (F (a, b) - m) ^ 2 ∂P
      = (∫ a, (F (a, b) - g b) ^ 2 ∂P) + (g b - m) ^ 2 := by
    intro b
    have hFdiff : Integrable (fun a => F (a, b) - g b) P := (hFab_int b).sub (integrable_const _)
    have hAint : Integrable (fun a => (F (a, b) - g b) ^ 2) P :=
      integrable_sq_of_bound P (hdmeas b) (hdbound b)
    have hBint : Integrable (fun a => (2 * (g b - m)) * (F (a, b) - g b)) P := hFdiff.const_mul _
    have hAB : Integrable
        (fun a => (F (a, b) - g b) ^ 2 + (2 * (g b - m)) * (F (a, b) - g b)) P := hAint.add hBint
    have hcenter : ∫ a, (F (a, b) - g b) ∂P = 0 := by
      rw [integral_sub (hFab_int b) (integrable_const _), integral_const, ← hgb b]; simp
    have hexp : ∀ a, (F (a, b) - m) ^ 2
        = (F (a, b) - g b) ^ 2 + (2 * (g b - m)) * (F (a, b) - g b) + (g b - m) ^ 2 := by
      intro a; ring
    calc
      ∫ a, (F (a, b) - m) ^ 2 ∂P
          = ∫ a, ((F (a, b) - g b) ^ 2 + (2 * (g b - m)) * (F (a, b) - g b)
              + (g b - m) ^ 2) ∂P := by simp_rw [hexp]
      _ = (∫ a, (F (a, b) - g b) ^ 2 ∂P)
            + (2 * (g b - m)) * (∫ a, (F (a, b) - g b) ∂P) + (g b - m) ^ 2 := by
            rw [integral_add hAB (integrable_const _),
              integral_add hAint hBint, integral_const_mul, integral_const]
            simp
      _ = (∫ a, (F (a, b) - g b) ^ 2 ∂P) + (g b - m) ^ 2 := by rw [hcenter]; ring
  -- variance rewrites
  have hVb : ∀ b, Var[fun a => F (a, b); P] = ∫ a, (F (a, b) - g b) ^ 2 ∂P := by
    intro b
    rw [variance_eq_integral (hFab b).aemeasurable]
  have hVg : Var[g; Q] = ∫ b, (g b - m) ^ 2 ∂Q := by
    rw [variance_eq_integral hg.aemeasurable, ← hmg]
  -- LHS via Fubini
  have hFm_bound : ∀ p, |F p - m| ≤ M + |m| := by
    intro p
    have h := abs_add_le (F p) (-m)
    rw [← sub_eq_add_neg, abs_neg] at h
    exact h.trans (add_le_add (hM p) le_rfl)
  have hFm_int : Integrable (fun p => (F p - m) ^ 2) (P.prod Q) :=
    integrable_sq_of_bound _ (hF.sub measurable_const) hFm_bound
  have hLHS : Var[F; P.prod Q] = ∫ b, ∫ a, (F (a, b) - m) ^ 2 ∂P ∂Q := by
    rw [variance_eq_integral hFint.aemeasurable, ← hm_def,
      integral_prod_symm (fun p => (F p - m) ^ 2) hFm_int]
  -- integrability of the two `Q`-integrands in the decomposition
  have hI2 : Integrable (fun b => (g b - m) ^ 2) Q :=
    integrable_sq_of_bound Q (hg.sub measurable_const)
      (fun b => by
        have h := abs_add_le (g b) (-m)
        rw [← sub_eq_add_neg, abs_neg] at h
        exact h.trans (add_le_add (hMg b) le_rfl))
  have hInnerNonneg : ∀ b, 0 ≤ ∫ a, (F (a, b) - g b) ^ 2 ∂P := fun b =>
    integral_nonneg fun a => sq_nonneg _
  have hInnerBdd : ∀ b, |∫ a, (F (a, b) - g b) ^ 2 ∂P| ≤ (2 * M) ^ 2 := by
    intro b
    rw [abs_of_nonneg (hInnerNonneg b)]
    calc ∫ a, (F (a, b) - g b) ^ 2 ∂P ≤ ∫ _a, (2 * M) ^ 2 ∂P :=
          integral_mono (integrable_sq_of_bound P (hdmeas b) (hdbound b)) (integrable_const _)
            (fun a => by
              have := hdbound b a
              nlinarith [abs_nonneg (F (a, b) - g b), sq_abs (F (a, b) - g b)])
      _ = (2 * M) ^ 2 := by simp
  have hI1_sm : StronglyMeasurable (fun b => ∫ a, (F (a, b) - g b) ^ 2 ∂P) := by
    have hH : Measurable (fun p : α × β => (F p - g p.2) ^ 2) :=
      ((hF.sub (hg.comp measurable_snd)).pow_const 2)
    exact hH.stronglyMeasurable.integral_prod_left'
  have hI1 : Integrable (fun b => ∫ a, (F (a, b) - g b) ^ 2 ∂P) Q :=
    (memLp_top_of_bound hI1_sm.aestronglyMeasurable ((2 * M) ^ 2)
      (Eventually.of_forall fun b => by
        rw [Real.norm_eq_abs]; exact hInnerBdd b)).integrable le_top
  -- assemble
  rw [hLHS]
  simp_rw [key]
  rw [integral_add hI1 hI2, hVg]
  simp_rw [hVb]

end Homogenization

/-
Copyright (c) 2026. All rights reserved.
-/


/-!
# Efron–Stein on finite products indexed by `Fin n`

Elementary induction on the number of coordinates, splitting off coordinate `0`
via `MeasurableEquiv.piFinSuccAbove`.
-/

@[expose] public section

open MeasureTheory Filter Fin Function ProbabilityTheory
open scoped ProbabilityTheory ENNReal BigOperators

namespace Homogenization

variable {n : ℕ} {α : Fin (n + 1) → Type*} [∀ i, MeasurableSpace (α i)]

/-- Updating coordinate `0` of `e.symm p` to `y` re-inserts `y` in the first slot. -/
private theorem update_symm_zero (p : α 0 × (∀ j, α ((0 : Fin (n + 1)).succAbove j))) (y : α 0) :
    Function.update ((MeasurableEquiv.piFinSuccAbove α 0).symm p) 0 y
      = (MeasurableEquiv.piFinSuccAbove α 0).symm (y, p.2) := by
  set e := MeasurableEquiv.piFinSuccAbove α 0 with he
  apply e.injective
  rw [e.apply_symm_apply]
  have happ : ∀ z : ∀ i, α i, e z = (z 0, fun j => z ((0 : Fin (n + 1)).succAbove j)) := by
    intro z; rfl
  rw [happ]
  have hp : e ((MeasurableEquiv.piFinSuccAbove α 0).symm p) = p := e.apply_symm_apply p
  rw [happ] at hp
  rw [Prod.mk.injEq]
  refine ⟨Function.update_self 0 y (e.symm p), ?_⟩
  funext j
  have hne : (0 : Fin (n + 1)).succAbove j ≠ 0 := Fin.succAbove_ne 0 j
  rw [Function.update_of_ne hne]
  exact congrFun (congrArg Prod.snd hp) j

/-- Updating coordinate `succAbove 0 j` of `e.symm p` corresponds to updating tail slot `j`. -/
private theorem update_symm_succ (p : α 0 × (∀ j, α ((0 : Fin (n + 1)).succAbove j))) (j : Fin n)
    (y : α ((0 : Fin (n + 1)).succAbove j)) :
    Function.update ((MeasurableEquiv.piFinSuccAbove α 0).symm p) ((0 : Fin (n + 1)).succAbove j) y
      = (MeasurableEquiv.piFinSuccAbove α 0).symm (p.1, Function.update p.2 j y) := by
  classical
  set e := MeasurableEquiv.piFinSuccAbove α 0 with he
  apply e.injective
  rw [e.apply_symm_apply]
  have happ : ∀ z : ∀ i, α i, e z = (z 0, fun k => z ((0 : Fin (n + 1)).succAbove k)) := by
    intro z; rfl
  rw [happ]
  have hp : e ((MeasurableEquiv.piFinSuccAbove α 0).symm p) = p := e.apply_symm_apply p
  rw [happ] at hp
  rw [Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [Function.update_of_ne (Fin.succAbove_ne 0 j).symm]
    exact congrArg Prod.fst hp
  · funext k
    by_cases hkj : k = j
    · subst hkj
      rw [Function.update_self, Function.update_self]
    · have hne : (0 : Fin (n + 1)).succAbove k ≠ (0 : Fin (n + 1)).succAbove j := by
        simpa [Fin.succAbove_right_inj] using hkj
      rw [Function.update_of_ne hne, Function.update_of_ne hkj]
      exact congrFun (congrArg Prod.snd hp) k

/-- The coordinate-`0` conditional-variance integral equals half the coordinate-`0`
resampling energy. -/
private theorem term_zero_eq (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {F : (∀ i, α i) → ℝ} (hF : Measurable F) {M : ℝ} (hM : ∀ x, |F x| ≤ M) :
    (∫ t, Var[fun a => F ((MeasurableEquiv.piFinSuccAbove α 0).symm (a, t)); μ 0]
        ∂(Measure.pi fun j => μ ((0 : Fin (n + 1)).succAbove j)))
      = (1 / 2) * ∫ x, ∫ y, (F (Function.update x 0 y) - F x) ^ 2 ∂(μ 0) ∂(Measure.pi μ) := by
  set e := MeasurableEquiv.piFinSuccAbove α 0 with he
  set ν : ∀ j, Measure (α ((0 : Fin (n + 1)).succAbove j)) :=
    fun j => μ ((0 : Fin (n + 1)).succAbove j) with hν
  have mp : MeasurePreserving e (Measure.pi μ) ((μ 0).prod (Measure.pi ν)) :=
    measurePreserving_piFinSuccAbove μ 0
  set φ0 : (∀ i, α i) → ℝ := fun x => ∫ y, (F (Function.update x 0 y) - F x) ^ 2 ∂(μ 0) with hφ0
  -- LHS as a triple integral via the two-point identity
  have hLHS : (∫ t, Var[fun a => F (e.symm (a, t)); μ 0] ∂(Measure.pi ν))
      = (1 / 2) * ∫ t, (∫ a, ∫ b, (F (e.symm (a, t)) - F (e.symm (b, t))) ^ 2
          ∂(μ 0) ∂(μ 0)) ∂(Measure.pi ν) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    exact variance_eq_half_integral_sub_sq (μ 0)
      (hF.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const)))
      (fun a => hM _)
  -- transport target₀ to the product measure
  have htrans : ∫ x, φ0 x ∂(Measure.pi μ)
      = ∫ p, φ0 (e.symm p) ∂((μ 0).prod (Measure.pi ν)) :=
    (mp.symm.integral_comp' φ0).symm
  have hφe : ∀ p, φ0 (e.symm p)
      = ∫ y, (F (e.symm (y, p.2)) - F (e.symm p)) ^ 2 ∂(μ 0) := by
    intro p
    have hup : ∀ y, Function.update (e.symm p) 0 y = e.symm (y, p.2) := fun y => by
      rw [he]; exact update_symm_zero p y
    simp only [hφ0]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hup y]
  -- integrability of the transported integrand for Fubini
  have hK : Measurable fun q : α 0 × (α 0 × (∀ j, α ((0 : Fin (n + 1)).succAbove j))) =>
      (F (e.symm (q.1, q.2.2)) - F (e.symm q.2)) ^ 2 :=
    ((hF.comp (e.symm.measurable.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))).sub
      (hF.comp (e.symm.measurable.comp measurable_snd))).pow_const 2
  have hdb : ∀ (p : α 0 × (∀ j, α ((0 : Fin (n + 1)).succAbove j))) (y : α 0),
      |F (e.symm (y, p.2)) - F (e.symm p)| ≤ 2 * M := by
    intro p y
    have h := abs_add_le (F (e.symm (y, p.2))) (-(F (e.symm p)))
    rw [← sub_eq_add_neg, abs_neg] at h
    have := h.trans (add_le_add (hM _) (hM _)); linarith
  have hInt : Integrable (fun p => ∫ y, (F (e.symm (y, p.2)) - F (e.symm p)) ^ 2 ∂(μ 0))
      ((μ 0).prod (Measure.pi ν)) := by
    have hsm : StronglyMeasurable
        (fun p => ∫ y, (F (e.symm (y, p.2)) - F (e.symm p)) ^ 2 ∂(μ 0)) :=
      hK.stronglyMeasurable.integral_prod_left'
    refine (memLp_top_of_bound hsm.aestronglyMeasurable ((2 * M) ^ 2)
      (Eventually.of_forall fun p => ?_)).integrable le_top
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => sq_nonneg _)]
    calc ∫ y, (F (e.symm (y, p.2)) - F (e.symm p)) ^ 2 ∂(μ 0)
        ≤ ∫ _y, (2 * M) ^ 2 ∂(μ 0) := by
          refine integral_mono ?_ (integrable_const _) (fun y => ?_)
          · exact integrable_sq_of_bound (μ 0) (M := 2 * M)
              ((hF.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))).sub
                measurable_const) (fun y => hdb p y)
          · nlinarith [sq_abs (F (e.symm (y, p.2)) - F (e.symm p)), hdb p y,
              abs_nonneg (F (e.symm (y, p.2)) - F (e.symm p))]
      _ = (2 * M) ^ 2 := by simp
  -- assemble
  rw [hLHS]
  have hgoal : (1 / 2) * ∫ x, ∫ y, (F (Function.update x 0 y) - F x) ^ 2 ∂(μ 0) ∂(Measure.pi μ)
      = (1 / 2) * ∫ t, (∫ a, ∫ b, (F (e.symm (a, t)) - F (e.symm (b, t))) ^ 2
          ∂(μ 0) ∂(μ 0)) ∂(Measure.pi ν) := by
    congr 1
    show ∫ x, φ0 x ∂(Measure.pi μ) = _
    rw [htrans]
    simp_rw [hφe]
    rw [integral_prod_symm _ hInt]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    ring
  rw [hgoal]

/-- The tail (coordinate `succAbove 0 j`) contribution: the resampling energy of the
conditional mean `g'` is bounded by the full resampling energy of `F`. -/
private theorem term_succ_le (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {F : (∀ i, α i) → ℝ} (hF : Measurable F) {M : ℝ} (hM : ∀ x, |F x| ≤ M) (j : Fin n) :
    (∫ t, ∫ w, ((∫ a, F ((MeasurableEquiv.piFinSuccAbove α 0).symm (a, Function.update t j w)) ∂(μ 0))
          - ∫ a, F ((MeasurableEquiv.piFinSuccAbove α 0).symm (a, t)) ∂(μ 0)) ^ 2
        ∂(μ ((0 : Fin (n + 1)).succAbove j))
        ∂(Measure.pi fun k => μ ((0 : Fin (n + 1)).succAbove k)))
      ≤ ∫ x, ∫ y, (F (Function.update x ((0 : Fin (n + 1)).succAbove j) y) - F x) ^ 2
          ∂(μ ((0 : Fin (n + 1)).succAbove j)) ∂(Measure.pi μ) := by
  classical
  set e := MeasurableEquiv.piFinSuccAbove α 0 with he
  set ν : ∀ k, Measure (α ((0 : Fin (n + 1)).succAbove k)) :=
    fun k => μ ((0 : Fin (n + 1)).succAbove k) with hν
  have mp : MeasurePreserving e (Measure.pi μ) ((μ 0).prod (Measure.pi ν)) :=
    measurePreserving_piFinSuccAbove μ 0
  have hGe : Measurable fun p => F (e.symm p) := hF.comp e.symm.measurable
  have hdiff : ∀ u v, |F (e.symm u) - F (e.symm v)| ≤ 2 * M := by
    intro u v
    have h := abs_add_le (F (e.symm u)) (-(F (e.symm v)))
    rw [← sub_eq_add_neg, abs_neg] at h
    have := h.trans (add_le_add (hM _) (hM _)); linarith
  have hDsq : ∀ u v, (F (e.symm u) - F (e.symm v)) ^ 2 ≤ (2 * M) ^ 2 := by
    intro u v
    nlinarith [hdiff u v, abs_nonneg (F (e.symm u) - F (e.symm v)), sq_abs (F (e.symm u) - F (e.symm v))]
  -- Jensen at fixed `(t, w)`
  have step1 : ∀ (t : ∀ k, α ((0 : Fin (n + 1)).succAbove k)) w,
      ((∫ a, F (e.symm (a, Function.update t j w)) ∂(μ 0)) - ∫ a, F (e.symm (a, t)) ∂(μ 0)) ^ 2
        ≤ ∫ a, (F (e.symm (a, Function.update t j w)) - F (e.symm (a, t))) ^ 2 ∂(μ 0) := by
    intro t w
    have hfm : Measurable fun a => F (e.symm (a, Function.update t j w)) := by fun_prop
    have hgm : Measurable fun a => F (e.symm (a, t)) := by fun_prop
    rw [← integral_sub (integrable_of_bound (μ 0) hfm (fun a => hM _))
      (integrable_of_bound (μ 0) hgm (fun a => hM _))]
    exact sq_integral_le_integral_sq (μ 0) (hfm.sub hgm)
      (fun a => hdiff (a, Function.update t j w) (a, t))
  -- the main product-measure integrand and its integrability
  have hKmeas : Measurable fun q : α ((0 : Fin (n + 1)).succAbove j)
      × (α 0 × (∀ k, α ((0 : Fin (n + 1)).succAbove k))) =>
      (F (e.symm (q.2.1, Function.update q.2.2 j q.1)) - F (e.symm (q.2.1, q.2.2))) ^ 2 := by
    fun_prop
  have hIntTail : Integrable
      (fun p : α 0 × (∀ k, α ((0 : Fin (n + 1)).succAbove k)) =>
        ∫ w, (F (e.symm (p.1, Function.update p.2 j w)) - F (e.symm (p.1, p.2))) ^ 2 ∂(ν j))
      ((μ 0).prod (Measure.pi ν)) := by
    have hsm : StronglyMeasurable
        (fun p : α 0 × (∀ k, α ((0 : Fin (n + 1)).succAbove k)) =>
          ∫ w, (F (e.symm (p.1, Function.update p.2 j w)) - F (e.symm (p.1, p.2))) ^ 2 ∂(ν j)) :=
      hKmeas.stronglyMeasurable.integral_prod_left'
    refine (memLp_top_of_bound hsm.aestronglyMeasurable ((2 * M) ^ 2)
      (Eventually.of_forall fun p => ?_)).integrable le_top
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun w => sq_nonneg _)]
    calc ∫ w, (F (e.symm (p.1, Function.update p.2 j w)) - F (e.symm (p.1, p.2))) ^ 2 ∂(ν j)
        ≤ ∫ _w, (2 * M) ^ 2 ∂(ν j) :=
          integral_mono
            (integrable_sq_of_bound (ν j) (M := 2 * M) (by fun_prop)
              (fun w => hdiff (p.1, Function.update p.2 j w) (p.1, p.2)))
            (integrable_const _) (fun w => hDsq _ _)
      _ = (2 * M) ^ 2 := by
          have hprob : IsProbabilityMeasure (ν j) := by rw [hν]; infer_instance
          rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
  -- per-`t` swap integrability
  have hSwapInt : ∀ t : ∀ k, α ((0 : Fin (n + 1)).succAbove k),
      Integrable (Function.uncurry fun (a : α 0) (w : α ((0 : Fin (n + 1)).succAbove j)) =>
        (F (e.symm (a, Function.update t j w)) - F (e.symm (a, t))) ^ 2) ((μ 0).prod (ν j)) := by
    intro t
    refine integrable_of_bound ((μ 0).prod (ν j)) (M := (2 * M) ^ 2) (by fun_prop) (fun q => ?_)
    rw [Function.uncurry_apply_pair, abs_of_nonneg (sq_nonneg _)]
    exact hDsq _ _
  -- transport the target coordinate onto the product measure
  set ψ : (∀ i, α i) → ℝ :=
    fun x => ∫ y, (F (Function.update x ((0 : Fin (n + 1)).succAbove j) y) - F x) ^ 2 ∂(ν j) with hψ
  have htrans : ∫ x, ψ x ∂(Measure.pi μ) = ∫ p, ψ (e.symm p) ∂((μ 0).prod (Measure.pi ν)) :=
    (mp.symm.integral_comp' ψ).symm
  have hψe : ∀ p, ψ (e.symm p)
      = ∫ w, (F (e.symm (p.1, Function.update p.2 j w)) - F (e.symm (p.1, p.2))) ^ 2 ∂(ν j) := by
    intro p
    have hup : ∀ w, Function.update (e.symm p) ((0 : Fin (n + 1)).succAbove j) w
        = e.symm (p.1, Function.update p.2 j w) := fun w => by rw [he]; exact update_symm_succ p j w
    simp only [hψ]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [hup w]
  have htgt : (∫ x, ∫ y, (F (Function.update x ((0 : Fin (n + 1)).succAbove j) y) - F x) ^ 2
        ∂(ν j) ∂(Measure.pi μ))
      = ∫ t, ∫ a, ∫ w, (F (e.symm (a, Function.update t j w)) - F (e.symm (a, t))) ^ 2
          ∂(ν j) ∂(μ 0) ∂(Measure.pi ν) := by
    show ∫ x, ψ x ∂(Measure.pi μ) = _
    rw [htrans]
    simp_rw [hψe]
    rw [integral_prod_symm _ hIntTail]
  -- assemble
  rw [htgt]
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => integral_nonneg fun w => sq_nonneg _)
    hIntTail.integral_prod_right (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [integral_integral_swap (hSwapInt t)]
  refine integral_mono_of_nonneg (Eventually.of_forall fun w => sq_nonneg _)
    (hSwapInt t).integral_prod_right (Eventually.of_forall fun w => step1 t w)

/-- **Efron–Stein inequality** for bounded measurable observables on a finite
product `Fin m` (proved by induction on `m`). -/
private theorem efronStein_fin : ∀ (m : ℕ) {β : Fin m → Type*} [∀ i, MeasurableSpace (β i)]
    (μ : ∀ i, Measure (β i)) [∀ i, IsProbabilityMeasure (μ i)]
    {F : (∀ i, β i) → ℝ} (_hF : Measurable F) {M : ℝ} (_hM : ∀ x, |F x| ≤ M),
    Var[F; Measure.pi μ]
      ≤ (1 / 2) * ∑ i, ∫ x, ∫ y, (F (Function.update x i y) - F x) ^ 2 ∂(μ i)
          ∂(Measure.pi μ) := by
  intro m
  induction m with
  | zero =>
    intro β _ μ _ F hF M hM
    simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero]
    have hsub : ∀ x y : (∀ i : Fin 0, β i), x = y := fun x y => funext fun i => i.elim0
    have hmean : ∫ z, F z ∂(Measure.pi μ) = F default := by
      rw [show (fun z => F z) = (fun _ => F default) from funext fun z => by rw [hsub z default]]
      simp
    have hzero : Var[F; Measure.pi μ] = 0 := by
      rw [variance_eq_integral hF.aemeasurable, hmean]
      have hz : ∀ x, (F x - F default) ^ 2 = 0 := fun x => by rw [hsub x default]; ring
      simp_rw [hz]; simp
    rw [hzero]
  | succ n ih =>
    intro β _ μ _ F hF M hM
    have mp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove β 0) (Measure.pi μ)
        ((μ 0).prod (Measure.pi fun j => μ ((0 : Fin (n + 1)).succAbove j))) :=
      measurePreserving_piFinSuccAbove μ 0
    have hMG : ∀ t, |∫ a, F ((MeasurableEquiv.piFinSuccAbove β 0).symm (a, t)) ∂(μ 0)| ≤ M := by
      intro t
      calc |∫ a, F ((MeasurableEquiv.piFinSuccAbove β 0).symm (a, t)) ∂(μ 0)|
          ≤ ∫ a, |F ((MeasurableEquiv.piFinSuccAbove β 0).symm (a, t))| ∂(μ 0) :=
            abs_integral_le_integral_abs
        _ ≤ ∫ _a, M ∂(μ 0) :=
            integral_mono (integrable_of_bound (μ 0) (by fun_prop) (fun a => hM _)).abs
              (integrable_const M) (fun a => hM _)
        _ = M := by simp
    have hG : Measurable fun t => ∫ a, F ((MeasurableEquiv.piFinSuccAbove β 0).symm (a, t)) ∂(μ 0) :=
      (hF.comp (MeasurableEquiv.piFinSuccAbove β 0).symm.measurable).stronglyMeasurable.integral_prod_left'.measurable
    have hFsymm : Measurable fun p => F ((MeasurableEquiv.piFinSuccAbove β 0).symm p) :=
      hF.comp (MeasurableEquiv.piFinSuccAbove β 0).symm.measurable
    have hvar : Var[F; Measure.pi μ]
        = Var[fun p => F ((MeasurableEquiv.piFinSuccAbove β 0).symm p);
            (μ 0).prod (Measure.pi fun j => μ ((0 : Fin (n + 1)).succAbove j))] := by
      rw [← mp.variance_fun_comp (f := fun p => F ((MeasurableEquiv.piFinSuccAbove β 0).symm p))
        hFsymm.aemeasurable]
      congr 1
      funext ω
      simp only [MeasurableEquiv.symm_apply_apply]
    rw [hvar, variance_prod_eq (μ 0) (Measure.pi fun j => μ ((0 : Fin (n + 1)).succAbove j))
      hFsymm (fun p => hM _)]
    rw [term_zero_eq μ hF hM,
      Fin.sum_univ_succ (f := fun i => ∫ x, ∫ y, (F (Function.update x i y) - F x) ^ 2 ∂(μ i)
        ∂(Measure.pi μ)), mul_add]
    have hB : Var[fun p => ∫ a, F ((MeasurableEquiv.piFinSuccAbove β 0).symm (a, p)) ∂(μ 0);
          Measure.pi fun j => μ ((0 : Fin (n + 1)).succAbove j)]
        ≤ (1 / 2) * ∑ j : Fin n, ∫ x, ∫ y, (F (Function.update x (Fin.succ j) y) - F x) ^ 2
            ∂(μ (Fin.succ j)) ∂(Measure.pi μ) := by
      refine le_trans (ih (fun j => μ ((0 : Fin (n + 1)).succAbove j)) hG hMG) ?_
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      exact Finset.sum_le_sum (fun j _ => term_succ_le μ hF hM j)
    linarith [hB]

/-- **Efron–Stein inequality** for bounded measurable observables on an arbitrary
finite product probability space. -/
theorem efronStein_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    {F : (∀ i, Ω i) → ℝ} (hF : Measurable F) {M : ℝ} (hM : ∀ x, |F x| ≤ M) :
    Var[F; Measure.pi μ]
      ≤ (1 / 2) * ∑ i, ∫ x, ∫ y, (F (Function.update x i y) - F x) ^ 2 ∂(μ i)
          ∂(Measure.pi μ) := by
  classical
  set f : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with hf
  set Φ := MeasurableEquiv.piCongrLeft Ω f with hΦ
  have mp : MeasurePreserving Φ (Measure.pi fun k => μ (f k)) (Measure.pi μ) :=
    measurePreserving_piCongrLeft μ f
  have hvar : Var[F; Measure.pi μ] = Var[fun z => F (Φ z); Measure.pi fun k => μ (f k)] :=
    (mp.variance_fun_comp hF.aemeasurable).symm
  -- `Φ` intertwines coordinate updates
  have hupd : ∀ (z : ∀ k, Ω (f k)) (k : Fin (Fintype.card ι)) (y : Ω (f k)),
      Φ (Function.update z k y) = Function.update (Φ z) (f k) y := by
    intro z k y
    funext i
    obtain ⟨a, rfl⟩ := f.surjective i
    rw [hΦ, MeasurableEquiv.piCongrLeft_apply_apply]
    by_cases hak : a = k
    · subst hak; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hak,
        Function.update_of_ne (fun h => hak (f.injective h)),
        MeasurableEquiv.piCongrLeft_apply_apply]
  -- apply the `Fin` version to the reindexed family
  have hG : Measurable fun z => F (Φ z) := hF.comp Φ.measurable
  have key := efronStein_fin (Fintype.card ι) (fun k => μ (f k)) hG (M := M) (fun z => hM _)
  rw [hvar]
  refine le_trans key ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  refine le_of_eq ?_
  rw [← Equiv.sum_comp f (fun i => ∫ x, ∫ y, (F (Function.update x i y) - F x) ^ 2 ∂(μ i)
    ∂(Measure.pi μ))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp_rw [hupd]
  exact mp.integral_comp' (fun x => ∫ y, (F (Function.update x (f k) y) - F x) ^ 2 ∂(μ (f k)))

end Homogenization
