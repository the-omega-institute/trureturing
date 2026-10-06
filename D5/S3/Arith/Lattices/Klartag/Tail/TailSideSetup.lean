/- GID: D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Tail/TailSideSetup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lattice tail bounds along the matrix walk. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup

open MeasureTheory
open ProbabilityTheory
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.ChainSetup
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetup
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA

noncomputable section

section ProdIndep

variable {X Y α β γ ε : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace ε]

/-- **The middle-four interchange for product measures.**  Not in Mathlib; proved on rectangles by
Fubini twice. -/
theorem prod_map_middle_four (A₁ : Measure α) (B₁ : Measure β) (A₂ : Measure γ) (B₂ : Measure ε)
    [SigmaFinite A₁] [SigmaFinite B₁] [SigmaFinite A₂] [SigmaFinite B₂] :
    ((A₁.prod B₁).prod (A₂.prod B₂)).map
        (fun q : (α × β) × (γ × ε) => ((q.1.1, q.2.1), (q.1.2, q.2.2)))
      = (A₁.prod A₂).prod (B₁.prod B₂) := by
  have hΦ : Measurable (fun q : (α × β) × (γ × ε) => ((q.1.1, q.2.1), (q.1.2, q.2.2))) := by
    fun_prop
  refine (Measure.prod_eq fun S T hS hT => ?_).symm
  rw [Measure.map_apply hΦ (hS.prod hT)]
  have hpre : (fun q : (α × β) × (γ × ε) => ((q.1.1, q.2.1), (q.1.2, q.2.2))) ⁻¹' (S ×ˢ T)
      = {q : (α × β) × (γ × ε) | (q.1.1, q.2.1) ∈ S ∧ (q.1.2, q.2.2) ∈ T} := rfl
  have hmeas : MeasurableSet
      {q : (α × β) × (γ × ε) | (q.1.1, q.2.1) ∈ S ∧ (q.1.2, q.2.2) ∈ T} := by
    rw [← hpre]; exact hΦ (hS.prod hT)
  rw [hpre, Measure.prod_apply hmeas]
  have hsec : ∀ p : α × β,
      (A₂.prod B₂) (Prod.mk p ⁻¹'
          {q : (α × β) × (γ × ε) | (q.1.1, q.2.1) ∈ S ∧ (q.1.2, q.2.2) ∈ T})
        = A₂ (Prod.mk p.1 ⁻¹' S) * B₂ (Prod.mk p.2 ⁻¹' T) := by
    intro p
    have hset : (Prod.mk p ⁻¹'
        {q : (α × β) × (γ × ε) | (q.1.1, q.2.1) ∈ S ∧ (q.1.2, q.2.2) ∈ T})
        = (Prod.mk p.1 ⁻¹' S) ×ˢ (Prod.mk p.2 ⁻¹' T) := rfl
    rw [hset, Measure.prod_prod]
  simp_rw [hsec]
  rw [Measure.prod_apply hS, Measure.prod_apply hT]
  exact lintegral_prod_mul (μ := A₁) (ν := B₁)
    (measurable_measure_prodMk_left hS).aemeasurable
    (measurable_measure_prodMk_left hT).aemeasurable

variable {μ : Measure X} [IsProbabilityMeasure μ] {ν : Measure Y} [IsProbabilityMeasure ν]

/-- **Two independent pairs of blocks, one pair per factor.** -/
theorem indepFun_prodMk_prodMk {f₁ : X → α} {g₁ : X → β} {f₂ : Y → γ} {g₂ : Y → ε}
    (hf₁ : Measurable f₁) (hg₁ : Measurable g₁) (hf₂ : Measurable f₂) (hg₂ : Measurable g₂)
    (h₁ : IndepFun f₁ g₁ μ) (h₂ : IndepFun f₂ g₂ ν) :
    IndepFun (fun p : X × Y => (f₁ p.1, f₂ p.2)) (fun p : X × Y => (g₁ p.1, g₂ p.2))
      (μ.prod ν) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]
  have hF : (μ.prod ν).map (fun p : X × Y => (f₁ p.1, f₂ p.2))
      = (μ.map f₁).prod (ν.map f₂) := by
    rw [show (fun p : X × Y => (f₁ p.1, f₂ p.2)) = Prod.map f₁ f₂ from rfl,
      ← Measure.map_prod_map _ _ hf₁ hf₂]
  have hG : (μ.prod ν).map (fun p : X × Y => (g₁ p.1, g₂ p.2))
      = (μ.map g₁).prod (ν.map g₂) := by
    rw [show (fun p : X × Y => (g₁ p.1, g₂ p.2)) = Prod.map g₁ g₂ from rfl,
      ← Measure.map_prod_map _ _ hg₁ hg₂]
  rw [hF, hG,
    show (fun p : X × Y => ((f₁ p.1, f₂ p.2), (g₁ p.1, g₂ p.2)))
      = (fun q : (α × β) × (γ × ε) => ((q.1.1, q.2.1), (q.1.2, q.2.2)))
        ∘ (Prod.map (fun x => (f₁ x, g₁ x)) (fun y => (f₂ y, g₂ y))) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (hf₁.prodMk hg₁) (hf₂.prodMk hg₂),
    (indepFun_iff_map_prod_eq_prod_map_map hf₁.aemeasurable hg₁.aemeasurable).1 h₁,
    (indepFun_iff_map_prod_eq_prod_map_map hf₂.aemeasurable hg₂.aemeasurable).1 h₂,
    prod_map_middle_four]

/-- **A block on the first factor against a block on the first factor together with all of the
second.** -/
theorem indepFun_fst_prod {f : X → α} {g : X → β}
    (hf : Measurable f) (hg : Measurable g) (h : IndepFun f g μ) :
    IndepFun (fun p : X × Y => f p.1) (fun p : X × Y => (g p.1, p.2)) (μ.prod ν) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)]
  have hF : (μ.prod ν).map (fun p : X × Y => f p.1) = μ.map f := by
    rw [show (fun p : X × Y => f p.1) = f ∘ Prod.fst from rfl,
      ← Measure.map_map hf measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  have hG : (μ.prod ν).map (fun p : X × Y => (g p.1, p.2)) = (μ.map g).prod ν := by
    rw [show (fun p : X × Y => (g p.1, p.2)) = Prod.map g id from rfl,
      ← Measure.map_prod_map _ _ hg measurable_id, Measure.map_id]
  rw [hF, hG,
    show (fun p : X × Y => (f p.1, (g p.1, p.2)))
      = (MeasurableEquiv.prodAssoc : (α × β) × Y ≃ᵐ α × β × Y)
        ∘ (Prod.map (fun x => (f x, g x)) (id : Y → Y)) from rfl,
    ← Measure.map_map MeasurableEquiv.prodAssoc.measurable (by fun_prop),
    ← Measure.map_prod_map _ _ (hf.prodMk hg) measurable_id, Measure.map_id,
    (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).1 h,
    Measure.prodAssoc_prod]

end ProdIndep

section Space

variable {n : ℕ}

/-- `stdGaussian ℝ` is `N(0,1)` — the bridge between the value type's second summand and the
external factor's law. -/
theorem stdGaussian_real : stdGaussian ℝ = gaussianReal 0 1 := by
  have h := map_inner_stdGaussian (F := ℝ) (1 : ℝ)
  rw [show (fun x : ℝ => ⟪x, (1 : ℝ)⟫) = id from by funext x; simp, Measure.map_id] at h
  simpa using h

/-- **The space of the external-padding route**: the chain's path space times the `k` fresh
Gaussians `TailTransport.hit_tail_yOf` asks for. -/
abbrev PadSpace (n k : ℕ) : Type := (ℕ → EuclideanSpace ℝ (UT n)) × (Fin k → ℝ)

def padP (n k : ℕ) (δ : ℝ≥0) : Measure (PadSpace n k) :=
  (gaussPath (EuclideanSpace ℝ (UT n))).prod (Measure.pi fun _ : Fin k => gaussianReal 0 δ)

instance isProbabilityMeasure_padP (n k : ℕ) (δ : ℝ≥0) :
    IsProbabilityMeasure (padP n k δ) := by rw [padP]; infer_instance

/-- The past at step `i`: the first `i` chain coordinates and the first `i` fresh ones. -/
def Zed (n k i : ℕ) (ω : PadSpace n k) :
    (Fin i → EuclideanSpace ℝ (UT n)) × (Fin i → ℝ) :=
  ((fun j => ω.1 j), fun j => if h : (j : ℕ) < k then ω.2 ⟨j, h⟩ else 0)

theorem measurable_Zed (n k i : ℕ) : Measurable (Zed n k i) := by
  refine Measurable.prodMk ?_ ?_
  · exact (measurable_pi_iff.mpr fun _j => measurable_pi_apply _).comp measurable_fst
  · refine measurable_pi_iff.mpr fun j => ?_
    by_cases h : (j : ℕ) < k
    · simp only [dif_pos h]; exact (measurable_pi_apply _).comp measurable_snd
    · simp only [dif_neg h]; exact measurable_const

/-- **The combined increment below the horizon**, rescaled so that it is a *standard* Gaussian on
the two-factor value type: the chain coordinate and the fresh coordinate divided by `r`. -/
def Xi (r : ℝ) (n k i : ℕ) (ω : PadSpace n k) : PadCarrier n :=
  WithLp.toLp 2 (ω.1 i, if h : i < k then r⁻¹ * ω.2 ⟨i, h⟩ else 0)

theorem measurable_Xi (r : ℝ) (n k i : ℕ) : Measurable (Xi r n k i) := by
  refine (WithLp.measurable_toLp _ _).comp (Measurable.prodMk ?_ ?_)
  · exact (measurable_pi_apply i).comp measurable_fst
  · by_cases h : i < k
    · simp only [dif_pos h]
      exact (measurable_const.mul ((measurable_pi_apply _).comp measurable_snd))
    · simp only [dif_neg h]; exact measurable_const

/-- **Its law is standard**: `map_pair_prod`, with the fresh coordinate rescaled. -/
theorem map_Xi {r : ℝ} (hr : 0 < r) {k i : ℕ} (hik : i < k) :
    (padP n k (Real.toNNReal (r ^ 2))).map (Xi r n k i) = stdGaussian (PadCarrier n) := by
  have hne : r ≠ 0 := ne_of_gt hr
  have hfun : (Xi r n k i)
      = (WithLp.toLp 2 : EuclideanSpace ℝ (UT n) × ℝ → PadCarrier n)
        ∘ (Prod.map (fun v : ℕ → EuclideanSpace ℝ (UT n) => v i)
            (fun v : Fin k → ℝ => r⁻¹ * v ⟨i, hik⟩)) := by
    funext ω
    show WithLp.toLp 2 (ω.1 i, if h : i < k then r⁻¹ * ω.2 ⟨i, h⟩ else 0) = _
    rw [dif_pos hik]; rfl
  have h2 : (Measure.pi fun _ : Fin k => gaussianReal 0 (Real.toNNReal (r ^ 2))).map
      (fun v : Fin k → ℝ => r⁻¹ * v ⟨i, hik⟩) = stdGaussian ℝ := by
    have he : (fun v : Fin k → ℝ => r⁻¹ * v ⟨i, hik⟩)
        = (fun t : ℝ => r⁻¹ * t) ∘ (fun v : Fin k → ℝ => v ⟨i, hik⟩) := rfl
    have hcomp : (Measure.pi fun _ : Fin k => gaussianReal 0 (Real.toNNReal (r ^ 2))).map
        ((fun t : ℝ => r⁻¹ * t) ∘ (fun v : Fin k → ℝ => v ⟨i, hik⟩))
        = ((Measure.pi fun _ : Fin k => gaussianReal 0 (Real.toNNReal (r ^ 2))).map
            (fun v : Fin k → ℝ => v ⟨i, hik⟩)).map (fun t : ℝ => r⁻¹ * t) :=
      (Measure.map_map (by fun_prop) (measurable_pi_apply _)).symm
    rw [he, hcomp,
      (measurePreserving_eval (fun _ : Fin k => gaussianReal 0 (Real.toNNReal (r ^ 2)))
        ⟨i, hik⟩).map_eq,
      show (fun t : ℝ => r⁻¹ * t) = (r⁻¹ * ·) from rfl, gaussianReal_map_const_mul,
      stdGaussian_real]
    refine gaussianReal_ext_iff.2 ⟨by ring, ?_⟩
    refine NNReal.coe_injective ?_
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg r)]
    simp only [NNReal.coe_mk, NNReal.coe_one]
    field_simp
  rw [hfun, ← Measure.map_map (WithLp.measurable_toLp _ _) (by fun_prop), padP,
    ← Measure.map_prod_map _ _ (measurable_pi_apply i) (by fun_prop),
    show (gaussPath (EuclideanSpace ℝ (UT n))).map (fun v : ℕ → EuclideanSpace ℝ (UT n) => v i)
      = stdGaussian (EuclideanSpace ℝ (UT n)) from map_coord i, h2, stdGaussian_prodL2]

/-- **The past is independent of the increment** — the four blocks straddle the two factors, which
is what §1 is for. -/
theorem indepFun_Zed_Xi {r : ℝ} {k i : ℕ} (hik : i < k) (δ : ℝ≥0) :
    IndepFun (Zed n k i) (Xi r n k i) (padP n k δ) := by
  classical
  set ν : Measure (Fin k → ℝ) := Measure.pi fun _ : Fin k => gaussianReal 0 δ with hν
  have hbase : iIndepFun (fun (j : Fin k) (v : Fin k → ℝ) => v j) ν :=
    iIndepFun_pi (X := fun _ : Fin k => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
  have hdisj : Disjoint (Finset.univ.filter (fun j : Fin k => (j : ℕ) < i))
      ({⟨i, hik⟩} : Finset (Fin k)) := by
    simp only [Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_irrefl i
  have hfin := hbase.indepFun_finset (Finset.univ.filter (fun j : Fin k => (j : ℕ) < i))
    ({⟨i, hik⟩} : Finset (Fin k)) hdisj (fun j => measurable_pi_apply j)
  have hre : Measurable fun u : (↥(Finset.univ.filter (fun j : Fin k => (j : ℕ) < i)) → ℝ) =>
      (fun j : Fin i => if h : (j : ℕ) < k then
        u ⟨⟨(j : ℕ), h⟩, by simp [Finset.mem_filter, j.isLt]⟩ else 0) := by
    refine measurable_pi_iff.mpr fun j => ?_
    by_cases h : (j : ℕ) < k
    · simp only [dif_pos h]; exact measurable_pi_apply _
    · simp only [dif_neg h]; exact measurable_const
  have hpt : Measurable fun u : (↥({⟨i, hik⟩} : Finset (Fin k)) → ℝ) =>
      u ⟨⟨i, hik⟩, Finset.mem_singleton_self _⟩ := measurable_pi_apply _
  have hext := hfin.comp hre hpt
  have e1 : ((fun u : (↥(Finset.univ.filter (fun j : Fin k => (j : ℕ) < i)) → ℝ) =>
        (fun j : Fin i => if h : (j : ℕ) < k then
          u ⟨⟨(j : ℕ), h⟩, by simp [Finset.mem_filter, j.isLt]⟩ else 0))
      ∘ fun (v : Fin k → ℝ) (j : ↥(Finset.univ.filter (fun j : Fin k => (j : ℕ) < i))) => v j)
      = fun v : Fin k → ℝ => (fun j : Fin i => if h : (j : ℕ) < k then v ⟨j, h⟩ else 0) := rfl
  have e2 : ((fun u : (↥({⟨i, hik⟩} : Finset (Fin k)) → ℝ) =>
        u ⟨⟨i, hik⟩, Finset.mem_singleton_self _⟩)
      ∘ fun (v : Fin k → ℝ) (j : ↥({⟨i, hik⟩} : Finset (Fin k))) => v j)
      = fun v : Fin k → ℝ => v ⟨i, hik⟩ := rfl
  rw [e1, e2] at hext
  have hchain : IndepFun (restr (F := EuclideanSpace ℝ (UT n)) i)
      (coord (F := EuclideanSpace ℝ (UT n)) i) (gaussPath (EuclideanSpace ℝ (UT n))) :=
    (indepFun_coord_restr i).symm
  have h4 := indepFun_prodMk_prodMk (μ := gaussPath (EuclideanSpace ℝ (UT n))) (ν := ν)
    (measurable_restr i) (measurable_coord i)
    (by
      refine measurable_pi_iff.mpr fun j => ?_
      by_cases h : (j : ℕ) < k
      · simp only [dif_pos h]; exact measurable_pi_apply _
      · simp only [dif_neg h]; exact measurable_const)
    (measurable_pi_apply _) hchain hext
  have hZ : (fun p : PadSpace n k => (restr (F := EuclideanSpace ℝ (UT n)) i p.1,
      (fun j : Fin i => if h : (j : ℕ) < k then p.2 ⟨j, h⟩ else 0))) = Zed n k i := rfl
  rw [hZ, hν] at h4
  have hXi : (Xi r n k i)
      = (fun q : EuclideanSpace ℝ (UT n) × ℝ => (WithLp.toLp 2 (q.1, r⁻¹ * q.2) : PadCarrier n))
        ∘ (fun p : PadSpace n k => (coord (F := EuclideanSpace ℝ (UT n)) i p.1, p.2 ⟨i, hik⟩)) := by
    funext ω
    show WithLp.toLp 2 (ω.1 i, if h : i < k then r⁻¹ * ω.2 ⟨i, h⟩ else 0) = _
    rw [dif_pos hik]; rfl
  have hmq : Measurable fun q : EuclideanSpace ℝ (UT n) × ℝ =>
      (WithLp.toLp 2 (q.1, r⁻¹ * q.2) : PadCarrier n) :=
    (WithLp.measurable_toLp _ _).comp
      (Measurable.prodMk measurable_fst (measurable_const.mul measurable_snd))
  have h5 := h4.comp (measurable_id : Measurable (id :
    (Fin i → EuclideanSpace ℝ (UT n)) × (Fin i → ℝ) → _)) hmq
  rw [show (id ∘ Zed n k i) = Zed n k i from rfl, ← hXi] at h5
  exact h5

end Space

section Family

variable {n : ℕ}

/-- The past, truncated further — used to say that the earlier increments are functions of the
past at step `i`. -/
def trunc {i : ℕ} (j : Fin i) (z : (Fin i → EuclideanSpace ℝ (UT n)) × (Fin i → ℝ)) :
    (Fin (j : ℕ) → EuclideanSpace ℝ (UT n)) × (Fin (j : ℕ) → ℝ) :=
  ((fun l => z.1 ⟨l, lt_trans l.isLt j.isLt⟩), fun l => z.2 ⟨l, lt_trans l.isLt j.isLt⟩)

theorem trunc_Zed {k i : ℕ} (j : Fin i) (ω : PadSpace n k) :
    trunc j (Zed n k i ω) = Zed n k (j : ℕ) ω := rfl

/-- **The increment family.**  Below the horizon it is the padded increment — the chain coordinate
and the fresh one read in a past-measurable unit direction.  **At and above the horizon there is no
fresh coordinate, so the increment is an unused chain coordinate read in a fixed unit direction**;
that completion is exactly what `PaddingMap.map_pi_of_stepIndep`'s `∀ i` hypotheses need. -/
def Xfam (r : ℝ) (n k : ℕ)
    (u : ∀ i : ℕ, ((Fin i → EuclideanSpace ℝ (UT n)) × (Fin i → ℝ)) → PadCarrier n)
    (e : EuclideanSpace ℝ (UT n)) (i : ℕ) (ω : PadSpace n k) : ℝ :=
  if i < k then r * ⟪Xi r n k i ω, u i (Zed n k i ω)⟫ else r * ⟪ω.1 i, e⟫

theorem measurable_Xfam {r : ℝ} {k : ℕ}
    {u : ∀ i : ℕ, ((Fin i → EuclideanSpace ℝ (UT n)) × (Fin i → ℝ)) → PadCarrier n}
    (hum : ∀ i, Measurable (u i)) (e : EuclideanSpace ℝ (UT n)) (i : ℕ) :
    Measurable (Xfam r n k u e i) := by
  unfold Xfam
  by_cases h : i < k
  · simp only [if_pos h]
    exact measurable_const.mul (continuous_inner.measurable.comp
      ((measurable_Xi r n k i).prodMk ((hum i).comp (measurable_Zed n k i))))
  · simp only [if_neg h]
    exact measurable_const.mul (continuous_inner.measurable.comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_const))

/-- **Every increment is `N(0, r²)`** — below the horizon by the frozen-direction argument on the
two-factor value type, above it by `map_scaled_inner` at the unused chain coordinate. -/
theorem map_Xfam {r : ℝ} (hr : 0 < r) {k : ℕ}
    {u : ∀ i : ℕ, ((Fin i → EuclideanSpace ℝ (UT n)) × (Fin i → ℝ)) → PadCarrier n}
    (hum : ∀ i, Measurable (u i)) (hu : ∀ i z, ‖u i z‖ = 1)
    {e : EuclideanSpace ℝ (UT n)} (he : ‖e‖ = 1) (i : ℕ) :
    (padP n k (Real.toNNReal (r ^ 2))).map (Xfam r n k u e i)
      = gaussianReal 0 (Real.toNNReal (r ^ 2)) := by
  unfold Xfam
  by_cases h : i < k
  · simp only [if_pos h]
    exact map_frozen (measurable_Zed n k i) (measurable_Xi r n k i)
      (indepFun_Zed_Xi (r := r) h _) (map_Xi hr h)
      (fun z g => r * ⟪g, u i z⟫)
      (measurable_const.mul (continuous_inner.measurable.comp
        (measurable_snd.prodMk ((hum i).comp measurable_fst))))
      (fun z => map_scaled_inner (hu i z) r)
  · simp only [if_neg h]
    have hfst : (padP n k (Real.toNNReal (r ^ 2))).map
        (fun ω : PadSpace n k => ω.1 i) = stdGaussian (EuclideanSpace ℝ (UT n)) := by
      rw [show (fun ω : PadSpace n k => ω.1 i)
          = (fun v : ℕ → EuclideanSpace ℝ (UT n) => v i) ∘ Prod.fst from rfl,
        ← Measure.map_map (measurable_pi_apply i) measurable_fst, padP, Measure.map_fst_prod,
        measure_univ, one_smul]
      exact map_coord i
    rw [show (fun ω : PadSpace n k => r * ⟪ω.1 i, e⟫)
        = (fun g : EuclideanSpace ℝ (UT n) => r * ⟪g, e⟫) ∘ (fun ω : PadSpace n k => ω.1 i)
        from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), hfst, map_scaled_inner he r]

/-- The earlier increments, as a function of the past at step `i`. -/
def Gfam (r : ℝ) (n k : ℕ)
    (u : ∀ i : ℕ, ((Fin i → EuclideanSpace ℝ (UT n)) × (Fin i → ℝ)) → PadCarrier n)
    (e : EuclideanSpace ℝ (UT n)) (i : ℕ)
    (z : (Fin i → EuclideanSpace ℝ (UT n)) × (Fin i → ℝ)) : Fin i → ℝ :=
  fun j => if (j : ℕ) < k then
      r * ⟪(WithLp.toLp 2 (z.1 j, r⁻¹ * z.2 j) : PadCarrier n), u (j : ℕ) (trunc j z)⟫
    else r * ⟪z.1 j, e⟫

theorem measurable_Gfam {r : ℝ} {k : ℕ}
    {u : ∀ i : ℕ, ((Fin i → EuclideanSpace ℝ (UT n)) × (Fin i → ℝ)) → PadCarrier n}
    (hum : ∀ i, Measurable (u i)) (e : EuclideanSpace ℝ (UT n)) (i : ℕ) :
    Measurable (Gfam r n k u e i) := by
  refine measurable_pi_iff.mpr fun j => ?_
  have htr : Measurable (trunc (n := n) j) :=
    ((measurable_pi_iff.mpr fun _l => measurable_pi_apply _).comp measurable_fst).prodMk
      ((measurable_pi_iff.mpr fun _l => measurable_pi_apply _).comp measurable_snd)
  by_cases h : (j : ℕ) < k
  · simp only [Gfam, if_pos h]
    refine measurable_const.mul (continuous_inner.measurable.comp (Measurable.prodMk ?_ ?_))
    · exact (WithLp.measurable_toLp _ _).comp
        (((measurable_pi_apply j).comp measurable_fst).prodMk
          (measurable_const.mul ((measurable_pi_apply j).comp measurable_snd)))
    · exact (hum _).comp htr
  · simp only [Gfam, if_neg h]
    exact measurable_const.mul (continuous_inner.measurable.comp
      (((measurable_pi_apply j).comp measurable_fst).prodMk measurable_const))

theorem Gfam_Zed {r : ℝ} {k : ℕ}
    {u : ∀ i : ℕ, ((Fin i → EuclideanSpace ℝ (UT n)) × (Fin i → ℝ)) → PadCarrier n}
    (e : EuclideanSpace ℝ (UT n)) (i : ℕ) (ω : PadSpace n k) :
    Gfam r n k u e i (Zed n k i ω) = fun j : Fin i => Xfam r n k u e (j : ℕ) ω := by
  funext j
  by_cases h : (j : ℕ) < k
  · show (if (j : ℕ) < k then
        r * ⟪(WithLp.toLp 2 ((Zed n k i ω).1 j, r⁻¹ * (Zed n k i ω).2 j) : PadCarrier n),
          u (j : ℕ) (trunc j (Zed n k i ω))⟫
      else r * ⟪(Zed n k i ω).1 j, e⟫) = _
    rw [if_pos h, trunc_Zed]
    show _ = (if (j : ℕ) < k then
      r * ⟪Xi r n k (j : ℕ) ω, u (j : ℕ) (Zed n k (j : ℕ) ω)⟫ else _)
    rw [if_pos h]
    congr 2
    show (WithLp.toLp 2 (ω.1 (j : ℕ), r⁻¹ * (if hh : (j : ℕ) < k then ω.2 ⟨j, hh⟩ else 0))
      : PadCarrier n) = _
    rw [dif_pos h]
    show _ = WithLp.toLp 2 (ω.1 (j : ℕ), if hh : (j : ℕ) < k then r⁻¹ * ω.2 ⟨j, hh⟩ else 0)
    rw [dif_pos h]
  · show (if (j : ℕ) < k then _ else r * ⟪(Zed n k i ω).1 j, e⟫) = _
    rw [if_neg h]
    show _ = (if (j : ℕ) < k then _ else r * ⟪ω.1 (j : ℕ), e⟫)
    rw [if_neg h]
    rfl

/-- **Each increment is independent of all the earlier ones.** -/
theorem indepFun_Xfam {r : ℝ} {k : ℕ}
    {u : ∀ i : ℕ, ((Fin i → EuclideanSpace ℝ (UT n)) × (Fin i → ℝ)) → PadCarrier n}
    (hum : ∀ i, Measurable (u i)) (hu : ∀ i z, ‖u i z‖ = 1)
    {e : EuclideanSpace ℝ (UT n)} (_he : ‖e‖ = 1) (hr : 0 < r) (i : ℕ) :
    IndepFun (Xfam r n k u e i) (fun ω (j : Fin i) => Xfam r n k u e (j : ℕ) ω)
      (padP n k (Real.toNNReal (r ^ 2))) := by
  by_cases h : i < k
  · have hfro := indepFun_frozen (measurable_Zed n k i) (measurable_Xi r n k i)
      (indepFun_Zed_Xi (r := r) h (Real.toNNReal (r ^ 2))) (map_Xi (n := n) hr h)
      (fun z g => r * ⟪g, u i z⟫)
      (measurable_const.mul (continuous_inner.measurable.comp
        (measurable_snd.prodMk ((hum i).comp measurable_fst))))
      (fun z => map_scaled_inner (hu i z) r)
    have hcomp := hfro.symm.comp (measurable_id : Measurable (id : ℝ → ℝ))
      (measurable_Gfam (r := r) (k := k) hum e i)
    have e1 : (id ∘ fun ω : PadSpace n k => r * ⟪Xi r n k i ω, u i (Zed n k i ω)⟫)
        = Xfam r n k u e i := by
      funext ω; show _ = (if i < k then _ else _); rw [if_pos h]; rfl
    have e2 : (Gfam r n k u e i ∘ Zed n k i)
        = fun ω (j : Fin i) => Xfam r n k u e (j : ℕ) ω :=
      funext fun ω => Gfam_Zed e i ω
    rw [e1, e2] at hcomp
    exact hcomp
  · have hchain : IndepFun (coord (F := EuclideanSpace ℝ (UT n)) i)
        (restr (F := EuclideanSpace ℝ (UT n)) i) (gaussPath (EuclideanSpace ℝ (UT n))) :=
      indepFun_coord_restr i
    have hbase := indepFun_fst_prod (ν := Measure.pi fun _ : Fin k => gaussianReal 0
        (Real.toNNReal (r ^ 2))) (measurable_coord i) (measurable_restr i) hchain
    have hGm : Measurable fun q : (Fin i → EuclideanSpace ℝ (UT n)) × (Fin k → ℝ) =>
        Gfam r n k u e i (q.1, fun j : Fin i =>
          if hh : (j : ℕ) < k then q.2 ⟨j, hh⟩ else 0) := by
      refine (measurable_Gfam (r := r) (k := k) hum e i).comp
        (Measurable.prodMk measurable_fst ?_)
      refine measurable_pi_iff.mpr fun j => ?_
      by_cases hh : (j : ℕ) < k
      · simp only [dif_pos hh]; exact (measurable_pi_apply _).comp measurable_snd
      · simp only [dif_neg hh]; exact measurable_const
    have hme : Measurable fun g : EuclideanSpace ℝ (UT n) => r * ⟪g, e⟫ :=
      measurable_const.mul (continuous_inner.measurable.comp
        (measurable_id.prodMk measurable_const))
    have hcomp := hbase.comp hme hGm
    have e1 : ((fun g : EuclideanSpace ℝ (UT n) => r * ⟪g, e⟫)
        ∘ fun p : PadSpace n k => coord (F := EuclideanSpace ℝ (UT n)) i p.1)
        = Xfam r n k u e i := by
      funext ω; show _ = (if i < k then _ else _); rw [if_neg h]; rfl
    have e2 : ((fun q : (Fin i → EuclideanSpace ℝ (UT n)) × (Fin k → ℝ) =>
          Gfam r n k u e i (q.1, fun j : Fin i =>
            if hh : (j : ℕ) < k then q.2 ⟨j, hh⟩ else 0))
        ∘ fun p : PadSpace n k => (restr (F := EuclideanSpace ℝ (UT n)) i p.1, p.2))
        = fun ω (j : Fin i) => Xfam r n k u e (j : ℕ) ω :=
      funext fun ω => Gfam_Zed e i ω
    rw [e1, e2] at hcomp
    rw [padP]
    exact hcomp

/-- **`hincl` at every horizon on the external-padding route.** -/
theorem hincl_external {r : ℝ} (hr : 0 < r) {k : ℕ}
    {u : ∀ i : ℕ, ((Fin i → EuclideanSpace ℝ (UT n)) × (Fin i → ℝ)) → PadCarrier n}
    (hum : ∀ i, Measurable (u i)) (hu : ∀ i z, ‖u i z‖ = 1)
    {e : EuclideanSpace ℝ (UT n)} (he : ‖e‖ = 1) (m : ℕ) :
    (padP n k (Real.toNNReal (r ^ 2))).map
        (fun ω (j : Fin m) => Xfam r n k u e (j : ℕ) ω)
      = Measure.pi fun _ : Fin m => gaussianReal 0 (Real.toNNReal (r ^ 2)) :=
  map_pi_of_stepIndep _ (measurable_Xfam (r := r) hum e)
    (map_Xfam hr hum hu he) (indepFun_Xfam hum hu he hr) m

end Family

section Increments

variable {n : ℕ}

/-- The completed unit direction, written out at the two-factor carrier. -/
theorem inner_toLp_padUnit (a v : EuclideanSpace ℝ (UT n)) (s : ℝ) :
    ⟪(WithLp.toLp 2 (a, s) : PadCarrier n), padUnit (chainDir v) (freshDir n)⟫
      = ⟪a, v⟫ + s * Real.sqrt (1 - ‖v‖ ^ 2) := by
  rw [padUnit, WithLp.prod_inner_apply]
  simp [chainDir, freshDir]
  ring

theorem norm_neg_padDir {v : EuclideanSpace ℝ (UT n)} (hv : ‖v‖ ≤ 1) :
    ‖-padUnit (chainDir v) (freshDir n)‖ = 1 := by
  rw [norm_neg]
  exact norm_padUnit_eq_one (by rw [norm_chainDir]; exact hv) (norm_freshDir n)
    (inner_chainDir_freshDir v)

/-- **`hincl` for an adapted increment family** — `TailTransport.hit_tail_yOf`'s law, with the
chain entering only through `hM`: its increment at step `i` is `r⟪ω i, w_i(past)⟫`, and the
padding amplitude is the completing `√(1 − ‖w_i‖²)`. -/
theorem hincl_of_increments {r : ℝ} (hr : 0 < r) {k : ℕ} (hn : 0 < n)
    {w : ∀ i : ℕ, (Fin i → EuclideanSpace ℝ (UT n)) → EuclideanSpace ℝ (UT n)}
    (hwm : ∀ i, Measurable (w i)) (hw1 : ∀ i z, ‖w i z‖ ≤ 1)
    {M : ℕ → (ℕ → EuclideanSpace ℝ (UT n)) → ℝ}
    (hM : ∀ i ω₁, M (i + 1) ω₁ - M i ω₁ = r * ⟪ω₁ i, w i (restr i ω₁)⟫) :
    (padP n k (Real.toNNReal (r ^ 2))).map
        (padIncVec M (fun i ω₁ => Real.sqrt (1 - ‖w i (restr i ω₁)‖ ^ 2)) k)
      = Measure.pi fun _ : Fin k => gaussianReal 0 (Real.toNNReal (r ^ 2)) := by
  classical
  set p₀ : UT n := ⟨(⟨0, hn⟩, ⟨0, hn⟩), le_refl _⟩ with hp₀
  set e : EuclideanSpace ℝ (UT n) := EuclideanSpace.single p₀ (1 : ℝ) with he'
  have he : ‖e‖ = 1 := by rw [he']; simp
  set u : ∀ i : ℕ, ((Fin i → EuclideanSpace ℝ (UT n)) × (Fin i → ℝ)) → PadCarrier n :=
    fun i z => -padUnit (chainDir (w i z.1)) (freshDir n) with hu'
  have hum : ∀ i, Measurable (u i) := by
    intro i
    have h1 : Measurable fun z : (Fin i → EuclideanSpace ℝ (UT n)) × (Fin i → ℝ) =>
        chainDir (w i z.1) := measurable_chainDir.comp ((hwm i).comp measurable_fst)
    have h2 : Measurable fun z : (Fin i → EuclideanSpace ℝ (UT n)) × (Fin i → ℝ) =>
        Real.sqrt (1 - ‖chainDir (w i z.1)‖ ^ 2) :=
      Real.continuous_sqrt.measurable.comp (measurable_const.sub (h1.norm.pow_const 2))
    show Measurable fun z : (Fin i → EuclideanSpace ℝ (UT n)) × (Fin i → ℝ) =>
      -(chainDir (w i z.1) + Real.sqrt (1 - ‖chainDir (w i z.1)‖ ^ 2) • freshDir n)
    have hs : Measurable fun c : ℝ => c • freshDir n := by
      change Measurable fun c : ℝ =>
        WithLp.toLp 2 (c • (0 : EuclideanSpace ℝ (UT n)), c • (1 : ℝ))
      simp only [smul_zero, smul_eq_mul, mul_one]
      exact (WithLp.measurable_toLp 2 _).comp (measurable_const.prodMk measurable_id)
    exact (h1.add (hs.comp h2)).neg
  have hu : ∀ i z, ‖u i z‖ = 1 := fun i z => norm_neg_padDir (hw1 i z.1)
  have hkey : (padIncVec M (fun i ω₁ => Real.sqrt (1 - ‖w i (restr i ω₁)‖ ^ 2)) k)
      = fun ω (j : Fin k) => Xfam r n k u e (j : ℕ) ω := by
    funext ω j
    have hjk : (j : ℕ) < k := j.isLt
    show -((M ((j : ℕ) + 1) ω.1 - M (j : ℕ) ω.1)
        + Real.sqrt (1 - ‖w (j : ℕ) (restr (j : ℕ) ω.1)‖ ^ 2) * ω.2 j) = _
    rw [hM (j : ℕ) ω.1]
    show _ = (if (j : ℕ) < k then
      r * ⟪Xi r n k (j : ℕ) ω, u (j : ℕ) (Zed n k (j : ℕ) ω)⟫ else _)
    rw [if_pos hjk, hu']
    show _ = r * ⟪Xi r n k (j : ℕ) ω,
      -padUnit (chainDir (w (j : ℕ) (Zed n k (j : ℕ) ω).1)) (freshDir n)⟫
    rw [inner_neg_right]
    show _ = r * -⟪(WithLp.toLp 2 (ω.1 (j : ℕ),
      if h : (j : ℕ) < k then r⁻¹ * ω.2 ⟨j, h⟩ else 0) : PadCarrier n),
        padUnit (chainDir (w (j : ℕ) (restr (j : ℕ) ω.1))) (freshDir n)⟫
    rw [dif_pos hjk, inner_toLp_padUnit]
    have hrne : r ≠ 0 := ne_of_gt hr
    have hfin : ω.2 ⟨(j : ℕ), hjk⟩ = ω.2 j := by congr 1
    rw [hfin]
    field_simp
  rw [hkey]
  exact hincl_external hr hum hu he k

/-- **The transported per-step tail for an adapted increment family**, on the chain's own path
space, with no probabilistic hypothesis left. -/
theorem tail_of_increments {r : ℝ} (hr : 0 < r) {k : ℕ} (hn : 0 < n)
    {w : ∀ i : ℕ, (Fin i → EuclideanSpace ℝ (UT n)) → EuclideanSpace ℝ (UT n)}
    (hwm : ∀ i, Measurable (w i)) (hw1 : ∀ i z, ‖w i z‖ ≤ 1)
    {M : ℕ → (ℕ → EuclideanSpace ℝ (UT n)) → ℝ} (hMm : ∀ i, Measurable (M i))
    (hM : ∀ i ω₁, M (i + 1) ω₁ - M i ω₁ = r * ⟪ω₁ i, w i (restr i ω₁)⟫)
    {a₀ u t : ℝ} (ht : 0 < t) (hM₀ : 0 < a₀ - (u ^ 2)⁻¹)
    (hzero : ∀ ω₁, M 0 ω₁ = a₀ - (u ^ 2)⁻¹)
    (hv : ((k • Real.toNNReal (r ^ 2) : ℝ≥0) : ℝ) = t * 1 ^ 2) :
    (gaussPath (EuclideanSpace ℝ (UT n))) {ω₁ | ∃ j ≤ k, M j ω₁ ≤ 0}
      ≤ ENNReal.ofReal (4 * Phi (yOf a₀ t u)) := by
  refine hprop_of_hincl (P₁ := gaussPath (EuclideanSpace ℝ (UT n)))
    (c := fun i ω₁ => Real.sqrt (1 - ‖w i (restr i ω₁)‖ ^ 2)) hMm ?_ ht hM₀ hzero hv ?_
  · intro i
    exact (Real.continuous_sqrt.measurable.comp
      (measurable_const.sub ((((hwm i).comp (measurable_restr i)).norm).pow_const 2)))
  · exact hincl_of_increments hr hn hwm hw1 hM

end Increments

end

end D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup
