/- GID: D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/ChainSetup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Tail.TailAtStep
import D5.S3.Arith.Lattices.Klartag.Walk.ChainWalk
import D5.S3.Arith.Lattices.Klartag.State.StateInvariant4
import D5.S3.Arith.Lattices.Klartag.Contact.ContactIntegrated
import D5.S3.Arith.Lattices.Klartag.Walk.WalkTelescope

set_option warn.classDefReducibility false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Walk.ChainSetup

open MeasureTheory
open ProbabilityTheory
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments

noncomputable section

section Space

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **The path space**: one standard Gaussian per step, for infinitely many steps. -/
def gaussPath : Measure (ℕ → F) := Measure.infinitePi fun _ : ℕ => stdGaussian F

instance isProbabilityMeasure_gaussPath : IsProbabilityMeasure (gaussPath F) := by
  rw [gaussPath]; infer_instance

variable {F}

/-- **The `k`-th driving increment.** -/
def coord (k : ℕ) : (ℕ → F) → F := fun ω => ω k

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [BorelSpace F] in
theorem measurable_coord (k : ℕ) : Measurable (coord (F := F) k) := measurable_pi_apply k

/-- **The law of each coordinate is the standard Gaussian.** -/
theorem map_coord (k : ℕ) : (gaussPath F).map (coord k) = stdGaussian F :=
  Measure.infinitePi_map_eval (fun _ : ℕ => stdGaussian F) k

/-- **The coordinates are independent.** -/
theorem iIndepFun_coord : iIndepFun (coord (F := F)) (gaussPath F) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun k => measurable_coord k)]
  have h1 : (fun (ω : ℕ → F) (k : ℕ) => coord k ω) = fun ω => ω := rfl
  rw [h1, Measure.map_id']
  have h2 : (fun k : ℕ => (gaussPath F).map (coord k)) = fun _ : ℕ => stdGaussian F := by
    funext k; exact map_coord k
  rw [h2]
  rfl

end Space

section Filtration

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The first `k` increments. -/
def restr (k : ℕ) : (ℕ → F) → (Fin k → F) := fun ω j => ω j

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [BorelSpace F] in
theorem measurable_restr (k : ℕ) : Measurable (restr (F := F) k) :=
  measurable_pi_iff.mpr fun _j => measurable_pi_apply _

/-- **The natural filtration of the driving sequence.** -/
def natFil (k : ℕ) : MeasurableSpace (ℕ → F) :=
  MeasurableSpace.comap (restr (F := F) k) inferInstance

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [BorelSpace F] in
theorem natFil_le (k : ℕ) : natFil (F := F) k ≤ (inferInstance : MeasurableSpace (ℕ → F)) :=
  (measurable_restr k).comap_le

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [BorelSpace F] in
theorem monotone_natFil : Monotone (natFil (F := F)) := by
  intro k m hkm s hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact ⟨(fun u : Fin m → F => fun j : Fin k => u ⟨j, lt_of_lt_of_le j.isLt hkm⟩) ⁻¹' t,
    (measurable_pi_iff.mpr fun _j => measurable_pi_apply _) ht, rfl⟩

/-- **The filtration, bundled.** -/
def filtration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → F)) where
  seq := natFil
  mono' := monotone_natFil
  le' := natFil_le

instance sigmaFinite_trim_natFil (k : ℕ) :
    SigmaFinite ((gaussPath F).trim (natFil_le (F := F) k)) := by
  have : IsFiniteMeasure ((gaussPath F).trim (natFil_le (F := F) k)) := inferInstance
  infer_instance

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [BorelSpace F] in
/-- **`ξ k` is `ℱ (k+1)`-measurable** — the sequence is adapted. -/
theorem measurable_coord_natFil (k : ℕ) : Measurable[natFil (F := F) (k + 1)] (coord k) := by
  have h : coord (F := F) k
      = (fun u : Fin (k + 1) → F => u ⟨k, Nat.lt_succ_self k⟩) ∘ restr (k + 1) := rfl
  rw [h]
  exact (measurable_pi_apply _).comp (Measurable.of_comap_le le_rfl)

/-- **`ξ k` is independent of the first `k` increments.** -/
theorem indepFun_coord_restr (k : ℕ) :
    IndepFun (coord (F := F) k) (restr k) (gaussPath F) := by
  classical
  have hdisj : Disjoint ({k} : Finset ℕ) (Finset.range k) := by
    simp [Finset.disjoint_singleton_left]
  have hbase := (iIndepFun_coord (F := F)).indepFun_finset {k} (Finset.range k) hdisj
    (fun j => measurable_coord j)
  have hf : Measurable fun u : (↥({k} : Finset ℕ) → F) => u ⟨k, Finset.mem_singleton_self k⟩ :=
    measurable_pi_apply _
  have hg : Measurable fun u : (↥(Finset.range k) → F) =>
      (fun j : Fin k => u ⟨j, Finset.mem_range.2 j.isLt⟩) :=
    measurable_pi_iff.mpr fun _j => measurable_pi_apply _
  have hcomp := hbase.comp hf hg
  have e1 : ((fun u : (↥({k} : Finset ℕ) → F) => u ⟨k, Finset.mem_singleton_self k⟩)
      ∘ fun (ω : ℕ → F) (j : ↥({k} : Finset ℕ)) => coord (j : ℕ) ω) = coord k := rfl
  have e2 : ((fun u : (↥(Finset.range k) → F) =>
        (fun j : Fin k => u ⟨j, Finset.mem_range.2 j.isLt⟩))
      ∘ fun (ω : ℕ → F) (j : ↥(Finset.range k)) => coord (j : ℕ) ω) = restr k := rfl
  rwa [e1, e2] at hcomp

end Filtration

section Moments

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem coord_law (k : ℕ) (p : ι) :
    (gaussPath (EuclideanSpace ℝ ι)).map (fun ω : ℕ → EuclideanSpace ℝ ι => coord k ω p)
      = gaussianReal 0 1 :=
  StepGlue.coord_law (measurable_coord k) (map_coord k) p

omit [DecidableEq ι] in
theorem coord_indep (k : ℕ) :
    iIndepFun (fun (p : ι) (ω : ℕ → EuclideanSpace ℝ ι) => coord k ω p)
      (gaussPath (EuclideanSpace ℝ ι)) :=
  StepGlue.coord_indep (measurable_coord k) (map_coord k)

/-- **All moments of every coordinate are finite**, from `memLp_id_gaussianReal`. -/
theorem memLp_coord_apply (k : ℕ) (p : ι) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun ω : ℕ → EuclideanSpace ℝ ι => coord k ω p) r (gaussPath (EuclideanSpace ℝ ι)) := by
  have hm : Measurable fun ω : ℕ → EuclideanSpace ℝ ι => coord k ω p :=
    StepInputs2.measurable_coord (measurable_coord k) p
  have h : MemLp id r ((gaussPath (EuclideanSpace ℝ ι)).map
      (fun ω : ℕ → EuclideanSpace ℝ ι => coord k ω p)) := by
    rw [coord_law k p]; exact memLp_id_gaussianReal' r hr
  exact (memLp_map_measure_iff aestronglyMeasurable_id hm.aemeasurable).1 h

theorem integrable_coord_mul (k : ℕ) (p q : ι) :
    Integrable (fun ω : ℕ → EuclideanSpace ℝ ι => coord k ω p * coord k ω q)
      (gaussPath (EuclideanSpace ℝ ι)) := by
  have hH : ENNReal.HolderTriple 2 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two]; simp⟩
  exact MemLp.integrable_mul (memLp_coord_apply k p 2 (by simp))
    (memLp_coord_apply k q 2 (by simp))

/-- `‖ξ_k‖²` is integrable — the second moment that dominates `hintquad`, since
`‖π x‖ ≤ ‖x‖`. -/
theorem integrable_norm_sq_coord (k : ℕ) :
    Integrable (fun ω : ℕ → EuclideanSpace ℝ ι => ‖coord k ω‖ ^ 2)
      (gaussPath (EuclideanSpace ℝ ι)) := by
  have hsum : ∀ ω : ℕ → EuclideanSpace ℝ ι,
      ‖coord k ω‖ ^ 2 = ∑ p : ι, coord k ω p * coord k ω p := by
    intro ω
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  simp only [hsum]
  exact integrable_finsetSum _ fun p _ => integrable_coord_mul k p p

end Moments

section Step

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The chain's increment**: the standard coordinate scaled by `c = √h`. -/
def step (c : ℝ) (k : ℕ) (ω : ℕ → EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι := c • coord k ω

omit [DecidableEq ι] in
theorem measurable_step (c : ℝ) (k : ℕ) : Measurable (step (ι := ι) c k) :=
  (measurable_coord k).const_smul c

omit [DecidableEq ι] in
/-- `ξ_k ~ N(0, c²·Id)` — the currency `StateInvariant4`'s half-laws take. -/
theorem map_step (c : ℝ) (k : ℕ) :
    (gaussPath (EuclideanSpace ℝ ι)).map (step c k)
      = StateInvariant.scaled c (EuclideanSpace ℝ ι) := by
  rw [show (step (ι := ι) c k) = (fun x : EuclideanSpace ℝ ι => c • x) ∘ coord k from rfl,
    ← Measure.map_map (by fun_prop) (measurable_coord k), map_coord k]
  rfl

omit [DecidableEq ι] in
theorem iIndepFun_step (c : ℝ) :
    iIndepFun (step (ι := ι) c) (gaussPath (EuclideanSpace ℝ ι)) :=
  (iIndepFun_coord (F := EuclideanSpace ℝ ι)).comp
    (fun _ : ℕ => fun x : EuclideanSpace ℝ ι => c • x) (fun _ => measurable_id.const_smul c)

omit [DecidableEq ι] in
/-- `hlaw` of `driftInputs_step_chain`, at `v = c²`. -/
theorem step_coord_law (c : ℝ) (k : ℕ) (p : ι) :
    (gaussPath (EuclideanSpace ℝ ι)).map (fun ω : ℕ → EuclideanSpace ℝ ι => step c k ω p)
      = gaussianReal 0 (Real.toNNReal (c ^ 2)) :=
  StepGlue.coord_law_smul (measurable_coord k) (map_coord k) c p

omit [DecidableEq ι] in
/-- `hindep` of `driftInputs_step_chain`. -/
theorem step_coord_indep (c : ℝ) (k : ℕ) :
    iIndepFun (fun (p : ι) (ω : ℕ → EuclideanSpace ℝ ι) => step c k ω p)
      (gaussPath (EuclideanSpace ℝ ι)) :=
  StepGlue.coord_indep_smul (measurable_coord k) (map_coord k) c

omit [DecidableEq ι] in
/-- `hind` of `driftInputs_step_chain`: each increment is independent of its own past. -/
theorem indep_step_natFil (c : ℝ) (k : ℕ) :
    Indep (MeasurableSpace.comap (step (ι := ι) c k) inferInstance) (natFil k)
      (gaussPath (EuclideanSpace ℝ ι)) :=
  (indepFun_coord_restr (F := EuclideanSpace ℝ ι) k).comp
    (measurable_id.const_smul c) measurable_id

theorem memLp_step_apply (c : ℝ) (k : ℕ) (p : ι) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun ω : ℕ → EuclideanSpace ℝ ι => step c k ω p) r
      (gaussPath (EuclideanSpace ℝ ι)) := by
  have he : (fun ω : ℕ → EuclideanSpace ℝ ι => step c k ω p)
      = fun ω : ℕ → EuclideanSpace ℝ ι => c * coord k ω p := rfl
  rw [he]
  exact (memLp_coord_apply k p r hr).const_mul c

/-- `hintxi` of `driftInputs_step_chain`. -/
theorem integrable_step_apply (c : ℝ) (k : ℕ) (p : ι) :
    Integrable (fun ω : ℕ → EuclideanSpace ℝ ι => step c k ω p)
      (gaussPath (EuclideanSpace ℝ ι)) :=
  memLp_one_iff_integrable.1 (memLp_step_apply c k p 1 (by simp))

/-- `hintprod` of `driftInputs_step_chain`. -/
theorem integrable_step_mul (c : ℝ) (k : ℕ) (p q : ι) :
    Integrable (fun ω : ℕ → EuclideanSpace ℝ ι => step c k ω p * step c k ω q)
      (gaussPath (EuclideanSpace ℝ ι)) := by
  have hH : ENNReal.HolderTriple 2 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two]; simp⟩
  exact MemLp.integrable_mul (memLp_step_apply c k p 2 (by simp))
    (memLp_step_apply c k q 2 (by simp))

theorem integrable_norm_sq_step (c : ℝ) (k : ℕ) :
    Integrable (fun ω : ℕ → EuclideanSpace ℝ ι => ‖step c k ω‖ ^ 2)
      (gaussPath (EuclideanSpace ℝ ι)) := by
  have he : (fun ω : ℕ → EuclideanSpace ℝ ι => ‖step c k ω‖ ^ 2)
      = fun ω : ℕ → EuclideanSpace ℝ ι => c ^ 2 * ‖coord k ω‖ ^ 2 := by
    funext ω
    rw [step, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [he]
  exact (integrable_norm_sq_coord k).const_mul _

/-- `hintK`: a coefficient bounded by `C` times a product of two coordinates is integrable as soon
as the coefficient is a.e. strongly measurable.  For `driftInputs_step_chain` the coefficient is
`(π_k e_p) q`, bounded by `‖π_k e_p‖ ≤ ‖e_p‖ = 1`. -/
theorem integrable_bddCoeff_mul (c : ℝ) (k : ℕ) (p q : ι)
    {M : (ℕ → EuclideanSpace ℝ ι) → ℝ} {C : ℝ}
    (hm : AEStronglyMeasurable M (gaussPath (EuclideanSpace ℝ ι)))
    (hC : ∀ ω, ‖M ω‖ ≤ C) :
    Integrable (fun ω : ℕ → EuclideanSpace ℝ ι => M ω * (step c k ω p * step c k ω q))
      (gaussPath (EuclideanSpace ℝ ι)) :=
  (integrable_step_mul c k p q).bdd_mul hm (Filter.Eventually.of_forall hC)

/-- A coordinate is bounded by the norm. -/
theorem norm_coord_le (x : EuclideanSpace ℝ ι) (q : ι) : ‖x q‖ ≤ ‖x‖ := by
  have h : x q = ⟪(EuclideanSpace.single q (1 : ℝ)), x⟫ :=
    (StepInputs2.inner_single_left' q x).symm
  have hn : ‖(EuclideanSpace.single q (1 : ℝ) : EuclideanSpace ℝ ι)‖ = 1 := by simp
  rw [Real.norm_eq_abs, h]
  refine le_trans (abs_real_inner_le_norm _ _) ?_
  rw [hn, one_mul]

/-- The bound `integrable_bddCoeff_mul` is applied at: an orthogonal projection's matrix entries
are at most `1` in absolute value. -/
theorem abs_starProjection_single_le_one (K : Submodule ℝ (EuclideanSpace ℝ ι))
    [K.HasOrthogonalProjection] (p q : ι) :
    ‖(K.starProjection (EuclideanSpace.single p (1 : ℝ))) q‖ ≤ 1 := by
  have h1 := norm_coord_le (K.starProjection (EuclideanSpace.single p (1 : ℝ))) q
  have h2 : ‖K.starProjection (EuclideanSpace.single p (1 : ℝ))‖
      ≤ ‖(EuclideanSpace.single p (1 : ℝ) : EuclideanSpace ℝ ι)‖ :=
    Submodule.norm_starProjection_apply_le _ _
  have h3 : ‖(EuclideanSpace.single p (1 : ℝ) : EuclideanSpace ℝ ι)‖ = 1 := by simp
  linarith

end Step

section Drift

variable {n : ℕ}

end Drift

section Setup

end Setup

section Padding

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

def padUnit (w e : F) : F := w + Real.sqrt (1 - ‖w‖ ^ 2) • e

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem norm_padUnit_eq_one {w e : F} (hw : ‖w‖ ≤ 1) (he : ‖e‖ = 1) (horth : ⟪w, e⟫ = 0) :
    ‖padUnit w e‖ = 1 := norm_padUnit hw he horth

end Padding

section TwoFactor

variable {n : ℕ}

abbrev PadCarrier (n : ℕ) : Type := WithLp 2 (EuclideanSpace ℝ (UT n) × ℝ)

/-- The chain direction, in the first summand. -/
def chainDir (v : EuclideanSpace ℝ (UT n)) : PadCarrier n := WithLp.toLp 2 (v, 0)

/-- The fresh direction: the second summand's unit vector. -/
def freshDir (n : ℕ) : PadCarrier n := WithLp.toLp 2 (0, 1)

theorem inner_chainDir_freshDir (v : EuclideanSpace ℝ (UT n)) :
    ⟪chainDir v, freshDir n⟫ = 0 := by
  simp [chainDir, freshDir]

theorem norm_chainDir (v : EuclideanSpace ℝ (UT n)) : ‖chainDir v‖ = ‖v‖ := by
  have h : ‖chainDir v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]; simp [chainDir]
  have h0 : (0 : ℝ) ≤ ‖chainDir v‖ := norm_nonneg _
  nlinarith [norm_nonneg v]

theorem norm_freshDir (n : ℕ) : ‖freshDir n‖ = 1 := by
  have h : ‖freshDir n‖ ^ 2 = 1 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]; simp [freshDir]
  nlinarith [norm_nonneg (freshDir n)]

theorem measurable_chainDir : Measurable (chainDir (n := n)) :=
  (WithLp.measurable_toLp _ _).comp (measurable_id.prodMk measurable_const)

end TwoFactor

end

end D5.S3.Arith.Lattices.Klartag.Walk.ChainSetup
