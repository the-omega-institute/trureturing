/- GID: D5/S3/LatticeGauge/Basic
   generality: G
   mirror-B: none(waiver:covered-by-lattice-reflection-positivity4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Open four-dimensional boxes, their gauge action, and the Wilson measure. -/

import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.Unique
import OmegaBuild.Commands

/-!
Omega original.

Open four-dimensional boxes, their gauge action, and the Wilson measure.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Matrix Filter

namespace Omega.LatticeGauge

section CompactHaar
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Probability Haar measure on a compact group. -/
noncomputable def compactHaar : Measure G := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)

instance : IsProbabilityMeasure (compactHaar G) :=
  ⟨by simpa [compactHaar] using (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts G)))⟩

instance : (compactHaar G).IsMulLeftInvariant := by
  unfold compactHaar
  infer_instance

private instance : (compactHaar G).IsHaarMeasure := by
  unfold compactHaar
  infer_instance

instance : (compactHaar G).IsMulRightInvariant := by
  constructor
  intro g
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

instance : (compactHaar G).IsInvInvariant := by
  constructor
  have : IsProbabilityMeasure (compactHaar G).inv := by
    change IsProbabilityMeasure ((compactHaar G).map Inv.inv)
    infer_instance
  have : (compactHaar G).inv.IsHaarMeasure := { }
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end CompactHaar

/-- Axis zero is time. Both halves use distance from the reflecting seam as time. -/
abbrev Vertex (n : Fin 4 → ℕ) := (i : Fin 4) → Fin (n i + 1)

abbrev Link (n : Fin 4 → ℕ) :=
  {a : Vertex n × Fin 4 // (a.1 a.2).val < n a.2}

abbrev Plaquette (n : Fin 4 → ℕ) :=
  {a : Vertex n × Fin 4 × Fin 4 //
    a.2.1 < a.2.2 ∧ (a.1 a.2.1).val < n a.2.1 ∧ (a.1 a.2.2).val < n a.2.2}

def shift {n : Fin 4 → ℕ} (v : Vertex n) (i : Fin 4) : Vertex n :=
  Function.update v i (v i + 1)

theorem shift_apply_of_ne {n : Fin 4 → ℕ} (v : Vertex n) {i j : Fin 4}
    (h : j ≠ i) : shift v i j = v j :=
  Function.update_of_ne h _ _

theorem shift_comm {n : Fin 4 → ℕ} (v : Vertex n) {i j : Fin 4}
    (h : i ≠ j) : shift (shift v i) j = shift (shift v j) i := by
  simp only [shift, Function.update_of_ne h, Function.update_of_ne h.symm]
  exact Function.update_comm h _ _ _

abbrev BoundarySite (n : Fin 4 → ℕ) := {v : Vertex n // v 0 = 0}

abbrev BoundaryLink (n : Fin 4 → ℕ) :=
  {e : Link n // e.val.1 0 = 0 ∧ e.val.2 ≠ 0}

/-- Product coordinates for all links. Negative temporal links point away from the seam. -/
abbrev Box (n : Fin 4 → ℕ) (G : Type*) :=
  ((Link n → G) × (Link n → G)) × (BoundarySite n → G)

variable {n : Fin 4 → ℕ} {G : Type*} [Group G] {d : ℕ}

/-- A finite dimensional measurable unitary representation. -/
structure GaugeData (G : Type*) [Group G] [MeasurableSpace G] (d : ℕ) where
  rep : G →* Matrix (Fin d) (Fin d) ℂ
  measurable_entry : ∀ i j, Measurable (fun g => rep g i j)
  unitary : ∀ g, (rep g)ᴴ * rep g = 1

def src (e : Link n) : Vertex n := e.val.1
def dst (e : Link n) : Vertex n := shift e.val.1 e.val.2
def bsrc (e : BoundaryLink n) : BoundarySite n := ⟨src e, e.property.1⟩
def bdst (e : BoundaryLink n) : BoundarySite n :=
  ⟨dst e, (shift_apply_of_ne _ (Ne.symm e.property.2)).trans e.property.1⟩

def gauge (g : Vertex n → G) (u : Link n → G) (e : Link n) : G :=
  g (src e) * u e * (g (dst e))⁻¹

def boundaryGauge (g : BoundarySite n → G) (u : BoundaryLink n → G)
    (e : BoundaryLink n) : G := g (bsrc e) * u e * (g (bdst e))⁻¹

def squareHolonomy (u : Link n → G) (p : Plaquette n) : G :=
  let ⟨⟨v, i, j⟩, hij, hi, hj⟩ := p
  u ⟨(v, i), hi⟩ * u ⟨(shift v i, j), by simpa [shift_apply_of_ne v hij.ne.symm] using hj⟩ *
    (u ⟨(shift v j, i), by simpa [shift_apply_of_ne v hij.ne] using hi⟩)⁻¹ * (u ⟨(v, j), hj⟩)⁻¹

def seamHolonomy (x y : BoundaryLink n → G) (h : BoundarySite n → G)
    (e : BoundaryLink n) : G :=
  (x e)⁻¹ * h (bsrc e) * y e * (h (bdst e))⁻¹

/-- Site gauges on the two halves act on seam links from negative to positive. -/
def siteGauge (g k : Vertex n → G) (u : Box n G) : Box n G :=
  ((gauge g u.1.1, gauge k u.1.2), fun v => g v * u.2 v * (k v)⁻¹)

theorem gauge_square (g : Vertex n → G) (u : Link n → G) (p : Plaquette n) :
    squareHolonomy (gauge g u) p = g p.val.1 * squareHolonomy u p * (g p.val.1)⁻¹ := by
  obtain ⟨⟨v, i, j⟩, h, hi, hj⟩ := p
  simp only [squareHolonomy, gauge, src, dst, _root_.mul_inv_rev, inv_inv, shift_comm v h.ne]
  group

variable [MeasurableSpace G]

theorem trace_conjugate (D : GaugeData G d) (a b : G) :
    (D.rep (a * b * a⁻¹)).trace = (D.rep b).trace := by
  rw [map_mul, map_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← map_mul, inv_mul_cancel,
    map_one, one_mul]

def boundary (u : Link n → G) : BoundaryLink n → G := fun e => u e

def halfAction (D : GaugeData G d) (u : Link n → G) : ℝ :=
  ∑ p : Plaquette n, (D.rep (squareHolonomy u p)).trace.re

/-- Sum of the spatial and temporal plaquette weights in the two halves and at the seam. -/
def wilsonAction (D : GaugeData G d) (u : Box n G) : ℝ :=
  halfAction D u.1.1 + halfAction D u.1.2 +
    ∑ e : BoundaryLink n, (D.rep (seamHolonomy (boundary u.1.1) (boundary u.1.2) u.2 e)).trace.re

omit [MeasurableSpace G] in
theorem gauge_seam (g k : Vertex n → G) (u : Box n G) (e : BoundaryLink n) :
    seamHolonomy (boundary (siteGauge g k u).1.1) (boundary (siteGauge g k u).1.2)
        (siteGauge g k u).2 e =
      g (bdst e) * seamHolonomy (boundary u.1.1) (boundary u.1.2) u.2 e * (g (bdst e))⁻¹ := by
  simp only [seamHolonomy, boundary, siteGauge, gauge, _root_.mul_inv_rev, inv_inv]
  simp only [bsrc, bdst]
  group

/-- Reflection swaps the half configurations and reverses the seam links. -/
def reflect (u : Box n G) : Box n G := ((u.1.2, u.1.1), u.2⁻¹)

theorem rep_inv (D : GaugeData G d) (a : G) : D.rep a⁻¹ = (D.rep a)ᴴ := by
  calc
    D.rep a⁻¹ = ((D.rep a)ᴴ * D.rep a) * D.rep a⁻¹ := by rw [D.unitary, one_mul]
    _ = (D.rep a)ᴴ := by rw [Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

private theorem trace_inv_re (D : GaugeData G d) (a : G) :
    (D.rep a⁻¹).trace.re = (D.rep a).trace.re := by
  rw [rep_inv, Matrix.trace_conjTranspose]
  rfl

/-- Reflection preserves the real trace of a seam plaquette. -/
theorem seamWeight_reflect (D : GaugeData G d) (s t : BoundaryLink n → G)
    (h : BoundarySite n → G) (e : BoundaryLink n) :
    (D.rep (seamHolonomy t s h⁻¹ e)).trace.re = (D.rep (seamHolonomy s t h e)).trace.re := by
  have hHolonomy :
      seamHolonomy t s h⁻¹ e =
        (h (bdst e))⁻¹ * (seamHolonomy s t h e)⁻¹ * ((h (bdst e))⁻¹)⁻¹ := by
    simp only [seamHolonomy, Pi.inv_apply]
    group
  rw [hHolonomy, trace_conjugate, trace_inv_re]

def pairing (D : GaugeData G d) (a b : G) : ℝ :=
  ((D.rep a)ᴴ * D.rep b).trace.re

theorem seam_pairing (D : GaugeData G d) (x y : BoundaryLink n → G)
    (h : BoundarySite n → G) (e : BoundaryLink n) :
    (D.rep (seamHolonomy x y h e)).trace.re = pairing D (x e) (boundaryGauge h y e) := by
  simp [seamHolonomy, pairing, boundaryGauge, mul_assoc, rep_inv D (x e)]

theorem pairing_mul (D : GaugeData G d) (a b g k : G) :
    pairing D (g * a * k⁻¹) (g * b * k⁻¹) = pairing D a b := by
  rw [pairing, ← rep_inv, ← map_mul, pairing, ← rep_inv, ← map_mul]
  have heq : (g * a * k⁻¹)⁻¹ * (g * b * k⁻¹) = k * (a⁻¹ * b) * k⁻¹ := by group
  rw [heq, trace_conjugate]

def feature (D : GaugeData G d) (a : G) (i j : Fin d) (k : Bool) : ℝ :=
  if k then (D.rep a i j).im else (D.rep a i j).re

theorem pairing_eq (D : GaugeData G d) (a b : G) :
    pairing D a b = ∑ i : Fin d, ∑ j : Fin d, ∑ k : Bool, feature D a j i k * feature D b j i k := by
  simp [pairing, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, feature,
    Complex.mul_re, Finset.sum_add_distrib, add_comm]

theorem norm_entry_le (D : GaugeData G d) (a : G) (i j : Fin d) :
    ‖D.rep a i j‖ ≤ 1 := by
  have h := congr_fun (congr_fun (D.unitary a) j) j
  have hsum : (∑ k : Fin d, ‖D.rep a k j‖ ^ 2) = 1 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.sq_norm, Complex.mul_re,
      Complex.normSq_apply, sub_eq_add_neg] using congrArg Complex.re h
  have hle : ‖D.rep a i j‖ ^ 2 ≤ 1 :=
    hsum ▸ Finset.single_le_sum (f := fun k => ‖D.rep a k j‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [norm_nonneg (D.rep a i j)]

theorem norm_trace_le (D : GaugeData G d) (a : G) : ‖(D.rep a).trace‖ ≤ d := by
  rw [Matrix.trace]
  calc
    _ ≤ ∑ i : Fin d, ‖D.rep a i i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => norm_entry_le D a i i
    _ = d := by simp

section Haar

variable [MeasurableMul₂ G] [MeasurableInv G]
variable (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ]

/-- The Haar probability on an independent family of links. -/
noncomputable def configMeasure (E : Type*) [Fintype E] : Measure (E → G) :=
  Measure.pi (fun _ => μ)

instance {E : Type*} [Fintype E] :
    IsProbabilityMeasure (configMeasure μ E) := by unfold configMeasure; infer_instance

instance {E : Type*} [Fintype E] :
    Measure.IsMulLeftInvariant (configMeasure μ E) := by unfold configMeasure; infer_instance

/-- Independent link measure, expressed in the two halves and the seam. -/
noncomputable def boxMeasure (n : Fin 4 → ℕ) : Measure (Box n G) :=
  ((configMeasure μ (Link n)).prod (configMeasure μ (Link n))).prod
    (configMeasure μ (BoundarySite n))

private local instance : IsProbabilityMeasure (boxMeasure μ n) := by
  unfold boxMeasure
  infer_instance

theorem measurable_square (p : Plaquette n) :
    Measurable (fun u : Link n → G => squareHolonomy u p) := by
  obtain ⟨⟨v, i, j⟩, h, hi, hj⟩ := p
  simp only [squareHolonomy]
  fun_prop

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem measurable_weight (D : GaugeData G d) :
    Measurable (fun a => (D.rep a).trace.re) := by
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
  exact Finset.measurable_sum _ fun i _ => Complex.measurable_re.comp (D.measurable_entry i i)

theorem measurable_halfAction (D : GaugeData G d) :
    Measurable (halfAction D : (Link n → G) → ℝ) :=
  Finset.measurable_sum _ fun p _ => (measurable_weight D).comp (measurable_square p)

private theorem measurable_cross (e : BoundaryLink n) :
    Measurable (fun u : Box n G =>
      seamHolonomy (boundary u.1.1) (boundary u.1.2) u.2 e) := by
  unfold seamHolonomy boundary
  fun_prop

theorem measurable_action (D : GaugeData G d) :
    Measurable (wilsonAction D : Box n G → ℝ) :=
  (((measurable_halfAction D).comp (measurable_fst.comp measurable_fst)).add
    ((measurable_halfAction D).comp (measurable_snd.comp measurable_fst))).add
    (Finset.measurable_sum _ fun e _ => (measurable_weight D).comp (measurable_cross e))

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem abs_halfAction_le (D : GaugeData G d) (u : Link n → G) :
    |halfAction D u| ≤ Fintype.card (Plaquette n) * d := by
  calc
    _ ≤ ∑ p : Plaquette n, |(D.rep (squareHolonomy u p)).trace.re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Plaquette n, (d : ℝ) := Finset.sum_le_sum fun _ _ =>
      (Complex.abs_re_le_norm _).trans (norm_trace_le _ _)
    _ = _ := by simp [mul_comm]

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem abs_action_le (D : GaugeData G d) (u : Box n G) :
    |wilsonAction D u| ≤ (2 * Fintype.card (Plaquette n) + Fintype.card (BoundaryLink n)) * d := by
  have h : |∑ e : BoundaryLink n,
      (D.rep (seamHolonomy (boundary u.1.1) (boundary u.1.2) u.2 e)).trace.re| ≤
      Fintype.card (BoundaryLink n) * d := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact (Finset.sum_le_sum fun _ _ =>
      (Complex.abs_re_le_norm _).trans (norm_trace_le D _)).trans_eq (by simp [mul_comm])
  unfold wilsonAction
  exact (abs_add_le ..).trans ((add_le_add
    ((abs_add_le ..).trans (add_le_add (abs_halfAction_le D _) (abs_halfAction_le D _))) h).trans_eq
      (by ring))

theorem exp_bound {a b C : ℝ} (h : |a| ≤ C) :
    Real.exp (b * a) ≤ Real.exp (|b| * C) := by
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |b * a| := le_abs_self _
    _ = |b| * |a| := abs_mul ..
    _ ≤ _ := mul_le_mul_of_nonneg_left h (abs_nonneg _)

private theorem exp_integrable {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsFiniteMeasure ν] {f : X → ℝ} (hf : Measurable f)
    (C : ℝ) (hC : ∀ x, |f x| ≤ C) (β : ℝ) :
    Integrable (fun x => Real.exp (β * f x)) ν :=
  Integrable.of_bound ((Real.measurable_exp.comp (hf.const_mul β)).aestronglyMeasurable)
    (Real.exp (|β| * C)) <| Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using exp_bound (b := β) (hC x)

/-- The Wilson partition function using the unnormalized defining trace. -/
noncomputable def partition (D : GaugeData G d) (β : ℝ) : ℝ :=
  ∫ u : Box n G, Real.exp (β * wilsonAction D u) ∂boxMeasure μ n

omit [μ.IsMulLeftInvariant] in
theorem partition_pos (D : GaugeData G d) (β : ℝ) :
    0 < partition (n := n) μ D β :=
  integral_exp_pos (exp_integrable (measurable_action D) _ (abs_action_le D) β)

end Haar

end Omega.LatticeGauge
