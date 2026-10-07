/- GID: D5/S3/Arith/Lattices/Klartag/State/PaddingMap
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/State/PaddingMap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric matrix state invariants and padded driving laws. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Tail.TailTransport
import D5.S3.Arith.Lattices.Klartag.Walk.Increments

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open ProbabilityTheory
open Set
open Real
open scoped ENNReal NNReal RealInnerProductSpace

theorem map_inner_stdGaussian {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (v : F) :
    (stdGaussian F).map (fun x => ⟪x, v⟫) = gaussianReal 0 (Real.toNNReal (‖v‖ ^ 2)) := by
  refine Measure.ext_of_charFun ?_
  funext t
  rw [Increments.charFun_map_of_inner (stdGaussian F) (fun x => ⟪x, v⟫) (by fun_prop)
      (fun s : ℝ => s • v) (fun x s => by
        simp [real_inner_smul_right, real_inner_comm]),
    charFun_stdGaussian, charFun_gaussianReal]
  congr 1
  have hn : ‖t • v‖ = |t| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
  have hreal : (|t| * ‖v‖) ^ 2 = ‖v‖ ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs]; ring
  rw [hn, Real.coe_toNNReal _ (sq_nonneg _), ← Complex.ofReal_pow, hreal]
  push_cast
  ring

/-- **The padding direction is a unit vector.**  `w` is the projected drift direction `π_k v_k`,
`e` a fresh direction orthogonal to it; `√(1 − ‖w‖²)` is Klartag's padding amplitude, and the
Pythagorean identity is exactly the statement that the padded conditional variance is `h`. -/
theorem norm_padUnit {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {w e : F}
    (hw : ‖w‖ ≤ 1) (he : ‖e‖ = 1) (horth : ⟪w, e⟫ = 0) :
    ‖w + Real.sqrt (1 - ‖w‖ ^ 2) • e‖ = 1 := by
  have hnn : (0 : ℝ) ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have horth' : ⟪w, Real.sqrt (1 - ‖w‖ ^ 2) • e⟫ = 0 := by
    rw [real_inner_smul_right, horth, mul_zero]
  have hpy : ‖w + Real.sqrt (1 - ‖w‖ ^ 2) • e‖ ^ 2
      = ‖w‖ ^ 2 + ‖Real.sqrt (1 - ‖w‖ ^ 2) • e‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real horth'
    simpa only [← pow_two] using h
  have hs : ‖Real.sqrt (1 - ‖w‖ ^ 2) • e‖ ^ 2 = 1 - ‖w‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, he, mul_one, sq_abs, Real.sq_sqrt hnn]
  have h1 : ‖w + Real.sqrt (1 - ‖w‖ ^ 2) • e‖ ^ 2 = 1 := by rw [hpy, hs]; ring
  nlinarith [norm_nonneg (w + Real.sqrt (1 - ‖w‖ ^ 2) • e)]

/-- The padded increment's law at a *fixed* unit direction: `N(0, r²)`. -/
theorem map_scaled_inner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {u : F} (hu : ‖u‖ = 1) (r : ℝ) :
    (stdGaussian F).map (fun g => r * ⟪g, u⟫) = gaussianReal 0 (Real.toNNReal (r ^ 2)) := by
  rw [show (fun g : F => r * ⟪g, u⟫) = (fun t : ℝ => r * t) ∘ (fun g : F => ⟪g, u⟫) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), map_inner_stdGaussian, hu,
    show (fun t : ℝ => r * t) = (r * ·) from rfl, gaussianReal_map_const_mul]
  refine gaussianReal_ext_iff.2 ⟨by ring, ?_⟩
  refine NNReal.coe_injective ?_
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg r), Real.coe_toNNReal _ (by norm_num)]
  norm_num

theorem map_prod_frozen {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] (μ : Measure α) [SFinite μ] {ρ : Measure E} [SFinite ρ]
    {ν : Measure β} [SFinite ν]
    (F : α → E → β) (hF : Measurable fun q : α × E => F q.1 q.2)
    (hfib : ∀ a, ρ.map (F a) = ν) :
    (μ.prod ρ).map (fun q => (q.1, F q.1 q.2)) = μ.prod ν := by
  have hmeas : Measurable fun q : α × E => (q.1, F q.1 q.2) := measurable_fst.prodMk hF
  have hFa : ∀ a, Measurable (F a) := fun a => hF.comp (measurable_const.prodMk measurable_id)
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hmeas hs, Measure.prod_apply (hmeas hs), Measure.prod_apply hs]
  refine lintegral_congr fun a => ?_
  have hpre : (Prod.mk a ⁻¹' ((fun q : α × E => (q.1, F q.1 q.2)) ⁻¹' s))
      = (F a) ⁻¹' (Prod.mk a ⁻¹' s) := rfl
  rw [hpre, ← Measure.map_apply (hFa a) (measurable_prodMk_left hs), hfib a]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem map_prod_eq_frozen {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] {Z : Ω → α} {ξ : Ω → E} (hZ : Measurable Z) (hξ : Measurable ξ)
    (hindep : IndepFun Z ξ P) {ρ : Measure E} [SFinite ρ] {ν : Measure β} [SFinite ν]
    (hlaw : P.map ξ = ρ) (F : α → E → β) (hF : Measurable fun q : α × E => F q.1 q.2)
    (hfib : ∀ a, ρ.map (F a) = ν) :
    P.map (fun ω => (Z ω, F (Z ω) (ξ ω))) = (P.map Z).prod ν := by
  have hpair : P.map (fun ω => (Z ω, ξ ω)) = (P.map Z).prod ρ := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hξ.aemeasurable).1 hindep, hlaw]
  have hcomp : (fun ω => (Z ω, F (Z ω) (ξ ω)))
      = (fun q : α × E => (q.1, F q.1 q.2)) ∘ (fun ω => (Z ω, ξ ω)) := rfl
  rw [hcomp, ← Measure.map_map (measurable_fst.prodMk hF) (hZ.prodMk hξ), hpair,
    map_prod_frozen _ F hF hfib]

/-- **The frozen law.**  `Increments.map_frozen_isometry` with the isometry hypothesis weakened to
constancy of the fibre law. -/
theorem map_frozen {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] {Z : Ω → α} {ξ : Ω → E} (hZ : Measurable Z) (hξ : Measurable ξ)
    (hindep : IndepFun Z ξ P) {ρ : Measure E} [SFinite ρ] {ν : Measure β}
    [IsProbabilityMeasure ν] (hlaw : P.map ξ = ρ) (F : α → E → β)
    (hF : Measurable fun q : α × E => F q.1 q.2) (hfib : ∀ a, ρ.map (F a) = ν) :
    P.map (fun ω => F (Z ω) (ξ ω)) = ν := by
  have hmeas : Measurable fun ω => F (Z ω) (ξ ω) := hF.comp (hZ.prodMk hξ)
  have hPZ : IsProbabilityMeasure (P.map Z) :=
    ⟨by rw [Measure.map_apply hZ MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩
  have h := map_prod_eq_frozen hZ hξ hindep hlaw F hF hfib
  have hsnd : P.map (fun ω => F (Z ω) (ξ ω))
      = (P.map (fun ω => (Z ω, F (Z ω) (ξ ω)))).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hZ.prodMk hmeas)]; rfl
  rw [hsnd, h, Measure.map_snd_prod, measure_univ, one_smul]

/-- **The frozen independence.**  The padded increment is independent of the past it was read
against. -/
theorem indepFun_frozen {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] {Z : Ω → α} {ξ : Ω → E} (hZ : Measurable Z) (hξ : Measurable ξ)
    (hindep : IndepFun Z ξ P) {ρ : Measure E} [SFinite ρ] {ν : Measure β}
    [IsProbabilityMeasure ν] (hlaw : P.map ξ = ρ) (F : α → E → β)
    (hF : Measurable fun q : α × E => F q.1 q.2) (hfib : ∀ a, ρ.map (F a) = ν) :
    IndepFun Z (fun ω => F (Z ω) (ξ ω)) P := by
  have hmeas : Measurable fun ω => F (Z ω) (ξ ω) := hF.comp (hZ.prodMk hξ)
  rw [indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hmeas.aemeasurable,
    map_prod_eq_frozen hZ hξ hindep hlaw F hF hfib, map_frozen hZ hξ hindep hlaw F hF hfib]

/-- **`hincl` at every horizon.**  The induction is on the horizon: the pair
`(X k, (X i)_{i<k})` has law `ν ⊗ πν` by independence, and `Fin.insertNthEquiv` at `Fin.last k`
turns `ν ⊗ πν` into `π ν` on `Fin (k+1)`. -/
theorem map_pi_of_stepIndep {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = ν)
    (hind : ∀ k, IndepFun (X k) (fun ω (i : Fin k) => X (i : ℕ) ω) P) (k : ℕ) :
    P.map (fun ω (i : Fin k) => X (i : ℕ) ω) = Measure.pi (fun _ : Fin k => ν) := by
  induction k with
  | zero =>
    refine Measure.ext fun s hs => ?_
    rcases Set.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
    · simp
    · have hsu : s = Set.univ := by
        ext y
        simp only [Set.mem_univ, iff_true]
        have hy : y = x := Subsingleton.elim _ _
        rw [hy]; exact hx
      have h1 : IsProbabilityMeasure (P.map (fun ω (i : Fin 0) => X (i : ℕ) ω)) :=
        ⟨by rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ,
          measure_univ]⟩
      rw [hsu, measure_univ, measure_univ]
  | succ k ih =>
    have hmpast : Measurable (fun ω (i : Fin k) => X (i : ℕ) ω) :=
      measurable_pi_iff.mpr (fun i => hm i)
    have hmall : Measurable (fun ω (j : Fin (k + 1)) => X (j : ℕ) ω) :=
      measurable_pi_iff.mpr (fun j => hm j)
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k) with he
    have hpair : P.map (fun ω => (X k ω, fun i : Fin k => X (i : ℕ) ω))
        = ν.prod (Measure.pi fun _ : Fin k => ν) := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map (hm k).aemeasurable
        hmpast.aemeasurable).1 (hind k), hlaw k, ih]
    have hcomp : (fun ω => (X k ω, fun i : Fin k => X (i : ℕ) ω))
        = (fun f : Fin (k + 1) → ℝ => e f) ∘ (fun ω (j : Fin (k + 1)) => X (j : ℕ) ω) := by
      funext ω
      simp [he, MeasurableEquiv.piFinSuccAbove, Fin.val_last]
      funext i
      rfl
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => ν) (Fin.last k)
    have hsym : (ν.prod (Measure.pi fun _ : Fin k => ν)).map e.symm
        = Measure.pi (fun _ : Fin (k + 1) => ν) := (MeasurePreserving.symm _ hmp).map_eq
    have hA : P.map (fun ω (j : Fin (k + 1)) => X (j : ℕ) ω)
        = ((P.map (fun ω (j : Fin (k + 1)) => X (j : ℕ) ω)).map e).map e.symm := by
      rw [Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self,
        Measure.map_id]
    rw [hcomp, ← Measure.map_map e.measurable hmall] at hpair
    rw [hA, hpair, hsym]

section PaddingMap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

end PaddingMap

omit [IsProbabilityMeasure P] in

theorem contact_zero_of_gap {n : ℕ} (C : ℕ → Ω → Finset (Fin n → ℤ))
    (W : Finset (Fin n → ℤ)) (M : (Fin n → ℤ) → ℕ → Ω → ℝ)
    (hhit : ∀ y ∈ W, {ω | y ∈ C 0 ω} ⊆ {ω | ∃ j ≤ 0, M y j ω ≤ 0})
    (hgap : ∀ y ∈ W, ∀ ω, 0 < M y 0 ω) :
    ∀ y ∈ W, P.real {ω | y ∈ C 0 ω} = 0 := by
  intro y hy
  have hempty : {ω | y ∈ C 0 ω} = (∅ : Set Ω) := by
    refine Set.eq_empty_of_subset_empty (le_trans (hhit y hy) ?_)
    intro ω hω
    obtain ⟨j, hj, hle⟩ := hω
    rw [Nat.le_zero.1 hj] at hle
    exact absurd hle (not_le.2 (hgap y hy ω))
  rw [hempty]
  simp [measureReal_def]

end D5.S3.Arith.Lattices.Klartag
