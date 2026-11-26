/- GID: D5/S3/Quantum/Gauge/LatticeReflectionPositivity4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/LatticeReflectionPositivity4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Wilson reflection positivity and planar Wilson-loop bounds. -/

module

import OmegaBuild.Commands
public import D5.S3.StatisticalMechanics.ZTwoHighTemperatureExpansion
public import OmegaMath.Topology.CubicalBox
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup

/-! # Finite Wilson reflection positivity and planar Wilson loops

A real Gram expansion gives reflection positivity of the finite Wilson pairing after the
crossing links are fixed to one. The mod-two plaquette expansion gives the two-dimensional
loop expectation and the four-dimensional bound on open cubical boxes.
-/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators ComplexConjugate
noncomputable section

namespace D5.S3.Quantum.Gauge.LatticeReflectionPositivity4D

section Abstract

variable {X ι : Type*} [Fintype X] [Fintype ι]

/-- The pairing for reflection exchanging two copies of the half configuration space. -/
def reflectionPairing (K : X → X → ℝ) (f g : X → ℂ) : ℂ :=
  ∑ x, ∑ y, (K x y : ℂ) * (star (f y) * g x)

/-- The unperturbed pairing is a single squared norm. -/
theorem product_reflection_positivity (w : X → ℝ) (f : X → ℂ) :
    reflectionPairing (fun x y => w x * w y) f f =
      (↑(‖∑ x, (w x : ℂ) * f x‖ ^ 2) : ℂ) := by
  rw [Complex.sq_norm, ← Complex.mul_conj]
  simp only [map_sum, map_mul, Complex.conj_ofReal, reflectionPairing, Complex.ofReal_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Complex.star_def]
  ring

/-- The real part of a Hermitian finite feature kernel. -/
def interaction (A : ι → X → ℂ) (c : ι → ℝ) (x y : X) : ℝ :=
  ∑ i, c i * (A i x * star (A i y)).re

private def realFeature (A : ι → X → ℂ) (c : ι → ℝ) (i : ι × Bool) (x : X) : ℝ :=
  Real.sqrt (c i.1) * if i.2 then (A i.1 x).re else (A i.1 x).im

omit [Fintype X] in
private theorem interaction_gram (A : ι → X → ℂ) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (x y : X) :
    interaction A c x y = ∑ i : ι × Bool, realFeature A c i x * realFeature A c i y := by
  rw [interaction, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fintype.sum_bool, realFeature, Bool.false_eq_true, ite_false, ite_true,
    Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  calc
    _ = c i * ((A i x).im * (A i y).im + (A i x).re * (A i y).re) := by ring
    _ = _ := by
      conv_lhs => rw [← Real.sq_sqrt (hc i)]
      ring

private theorem pairing_gram {J : Type*} [Fintype J] (B : J → X → ℝ)
    (w : X → ℝ) (f : X → ℂ) :
    reflectionPairing (fun x y => w x * w y * ∑ j, B j x * B j y) f f =
      ∑ j, (↑(‖∑ x, ((w x * B j x : ℝ) : ℂ) * f x‖ ^ 2) : ℂ) := by
  let term (x y : X) (j : J) :=
    (((w x * B j x) * (w y * B j y) : ℝ) : ℂ) * (star (f y) * f x)
  calc
    _ = ∑ x, ∑ y, ∑ j, term x y j := by
      unfold reflectionPairing
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [term, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ j, ∑ x, ∑ y, term x y j := by
      have h (x : X) : (∑ y, ∑ j, term x y j) = ∑ j, ∑ y, term x y j := Finset.sum_comm
      simp_rw [h]
      exact Finset.sum_comm
    _ = _ := by simp_rw [← product_reflection_positivity, reflectionPairing, term]

/-- Every nonnegative integer power of the interaction preserves reflection positivity. -/
theorem factorized_interaction_pow_rp (w : X → ℝ) (A : ι → X → ℂ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (n : ℕ) (f : X → ℂ) :
    0 ≤ (reflectionPairing (fun x y => w x * w y * interaction A c x y ^ n) f f).re ∧
      (reflectionPairing (fun x y => w x * w y * interaction A c x y ^ n) f f).im = 0 := by
  have h x y : interaction A c x y ^ n =
      ∑ p : Fin n → ι × Bool, (∏ i, realFeature A c (p i) x) * (∏ i, realFeature A c (p i) y) := by
    rw [interaction_gram A c hc, Fintype.sum_pow]
    simp_rw [Finset.prod_mul_distrib]
  simp_rw [h, pairing_gram, Complex.re_sum, Complex.im_sum, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨Finset.sum_nonneg fun _ _ => sq_nonneg _, by simp⟩

/-- The Wilson-type Boltzmann factor built from two copies of the half action. -/
def boltzmann (S : X → ℝ) (A : ι → X → ℂ) (c : ι → ℝ) (β : ℝ) (x y : X) : ℝ :=
  Real.exp (β * (S x + S y + interaction A c x y))

/-- The exponential of a nonnegatively coupled real feature interaction is reflection positive. -/
theorem exponential_boltzmann_reflection_positivity
    (w : X → ℝ) (S : X → ℝ) (A : ι → X → ℂ) (c : ι → ℝ) (β : ℝ)
    (hc : ∀ i, 0 ≤ c i) (hβ : 0 ≤ β) (f : X → ℂ) :
    0 ≤ (reflectionPairing (fun x y => w x * w y * boltzmann S A c β x y) f f).re ∧
      (reflectionPairing (fun x y => w x * w y * boltzmann S A c β x y) f f).im = 0 := by
  let u x := w x * Real.exp (β * S x)
  have hw x y : w x * w y * boltzmann S A c β x y =
      u x * u y * Real.exp (β * interaction A c x y) := by
    simp only [boltzmann, mul_add, Real.exp_add, u]
    ring
  simp_rw [hw]
  let K (n : ℕ) x y := u x * u y * interaction A c x y ^ n
  let a (n : ℕ) := β ^ n / (n.factorial : ℝ)
  have h x y : HasSum (fun n => a n * K n x y)
      (u x * u y * Real.exp (β * interaction A c x y)) := by
    rw [Real.exp_eq_exp_ℝ]
    convert (NormedSpace.expSeries_div_hasSum_exp (β * interaction A c x y)).mul_left (u x * u y) using 1
    ext n
    dsimp [a, K]
    rw [mul_pow]
    ring
  have hs (part : ℂ → ℝ) (hp : ∀ r : ℝ, ∀ z : ℂ, part ((r : ℂ) * z) = r * part z) :
      HasSum (fun n => ∑ x, ∑ y, a n * part ((K n x y : ℂ) * (star (f y) * f x)))
        (∑ x, ∑ y, u x * u y * Real.exp (β * interaction A c x y) * part (star (f y) * f x)) := by
    simp_rw [hp, ← mul_assoc]
    exact hasSum_sum fun x _ => hasSum_sum fun y _ => (h x y).mul_right _
  have hre : ∀ (r : ℝ) (z : ℂ), ((r : ℂ) * z).re = r * z.re := by
    simp [Complex.mul_re]
  have him : ∀ (r : ℝ) (z : ℂ), ((r : ℂ) * z).im = r * z.im := by
    simp [Complex.mul_im]
  have hr := hs Complex.re hre
  have hi := hs Complex.im him
  simp_rw [← Finset.mul_sum] at hr hi
  simp only [reflectionPairing, Complex.re_sum, Complex.im_sum, hre, him]
  constructor
  · rw [← hr.tsum_eq]
    exact tsum_nonneg fun n => mul_nonneg (div_nonneg (pow_nonneg hβ _) (by positivity))
      (by simpa only [reflectionPairing, Complex.re_sum] using
        (factorized_interaction_pow_rp u A c hc n f).1)
  · rw [← hi.tsum_eq]
    have hn n : (∑ x, ∑ y, ((K n x y : ℂ) * (star (f y) * f x)).im) = 0 := by
      simpa only [reflectionPairing, Complex.im_sum] using
        (factorized_interaction_pow_rp u A c hc n f).2
    simp only [hn, mul_zero, tsum_zero]

/-- On two configurations the sign observable has exactly the indicated negative pairing. -/
theorem negative_coupling_rp_counterexample (β : ℝ) (hβ : β < 0) :
    let f : Bool → ℂ := fun x => if x then 1 else -1
    let z := reflectionPairing (boltzmann (fun _ => 0) (fun _ : Unit => f) (fun _ => 1) β) f f
    z = (↑(4 * Real.sinh β) : ℂ) ∧ (4 * Real.sinh β : ℝ) < 0 := by
  dsimp
  constructor
  · simp [reflectionPairing, boltzmann, interaction, Real.sinh_eq]
    ring
  · rw [Real.sinh_eq]
    have h := Real.exp_lt_exp.mpr (show β < -β by linarith)
    linarith

private theorem reflectionPairing_cauchy_schwarz (K : X → X → ℝ)
    (hs : ∀ x y, K x y = K y x) (hp : ∀ f, 0 ≤ (reflectionPairing K f f).re)
    (f g : X → ℂ) :
    ‖reflectionPairing K f g‖ ^ 2 ≤ (reflectionPairing K f f).re * (reflectionPairing K g g).re := by
  let core : PreInnerProductSpace.Core ℂ (X → ℂ) :=
    { inner := reflectionPairing K
      conj_inner_symm := fun u v => by
        simp only [reflectionPairing, map_sum, map_mul, Complex.conj_ofReal,
          Complex.star_def, Complex.conj_conj]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [hs y x, mul_comm (v x)]
      re_inner_nonneg := hp
      add_left := fun u v z => by
        simp only [reflectionPairing, Pi.add_apply, star_add, add_mul, mul_add, Finset.sum_add_distrib]
      smul_left := fun u v r => by
        simp only [reflectionPairing, Pi.smul_apply, smul_eq_mul, star_mul', Complex.star_def,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        ring }
  let _ : PreInnerProductSpace.Core ℂ (X → ℂ) := core
  have h := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) f g
  rw [InnerProductSpace.Core.norm_inner_symm (𝕜 := ℂ) g f] at h
  rw [pow_two]
  exact h

end Abstract

section WilsonGauge

abbrev Space3 (L : ℕ) := Fin 3 → ZMod L
abbrev HalfTime (T : ℕ) := Fin T
abbrev HalfSite (T L : ℕ) := HalfTime T × Space3 L
abbrev Site (T L : ℕ) := Bool × HalfSite T L

/-- Reflection sends a site to the same coordinates in the opposite half. -/
def reflectSite {T L : ℕ} (s : Site T L) : Site T L :=
  (!s.1, s.2)

abbrev TimeStep (T : ℕ) := {t : Fin T // t.val + 1 < T}
abbrev HalfLink (T L : ℕ) :=
  (Fin T × Space3 L × Fin 3) ⊕ (TimeStep T × Space3 L)

abbrev CrossingLink (L : ℕ) := Space3 L
abbrev HalfConfig (T L : ℕ) (G : Type*) := HalfLink T L → G
abbrev CrossingConfig (L : ℕ) (G : Type*) := CrossingLink L → G
/-- Positive half, negative half, and links directed from negative to positive. -/
abbrev GaugeConfig (T L : ℕ) (G : Type*) :=
  HalfConfig T L G × HalfConfig T L G × CrossingConfig L G

def reflectGaugeConfig {T L : ℕ} {G : Type*} [Group G]
    (U : GaugeConfig T L G) : GaugeConfig T L G :=
  (U.2.1, U.1, U.2.2⁻¹)

abbrev HalfPlaquette (T L : ℕ) :=
  (Fin T × Space3 L × {d : Fin 3 × Fin 3 // d.1 < d.2}) ⊕
    (TimeStep T × Space3 L × Fin 3)
abbrev CrossingPlaquette (L : ℕ) := CrossingLink L × Fin 3
abbrev Plaquette (T L : ℕ) := (Bool × HalfPlaquette T L) ⊕ CrossingPlaquette L

variable {T L N : ℕ} {G : Type*} [Group G]

private def spatialStep (x : Space3 L) (μ : Fin 3) : Space3 L :=
  x + Pi.single μ 1

private def timeNext (t : TimeStep T) : Fin T := ⟨t.1.val + 1, t.2⟩

/-- Endpoints of an oriented link within one half. -/
def halfEndpoints : HalfLink T L → HalfSite T L × HalfSite T L
  | .inl (t, x, μ) => ((t, x), (t, spatialStep x μ))
  | .inr (t, x) => ((t.1, x), (timeNext t, x))

variable [NeZero T]

/-- A crossing link runs between the two boundary sites at the same spatial coordinate. -/
def crossingEndpoints (x : CrossingLink L) : Site T L × Site T L :=
  ((false, 0, x), (true, 0, x))

def halfGauge (k : HalfSite T L → G) (U : HalfConfig T L G) : HalfConfig T L G :=
  fun e => k (halfEndpoints e).1 * U e * (k (halfEndpoints e).2)⁻¹

def gaugeTransform (k : Site T L → G) (U : GaugeConfig T L G) : GaugeConfig T L G :=
  (halfGauge (fun s => k (true, s)) U.1, halfGauge (fun s => k (false, s)) U.2.1,
    fun e => k (crossingEndpoints e).1 * U.2.2 e * (k (crossingEndpoints e).2)⁻¹)

private def square (a b c d : G) : G := a * b * c⁻¹ * d⁻¹

def halfPlaquetteHolonomy (U : HalfConfig T L G) : HalfPlaquette T L → G
  | .inl (t, x, ⟨(μ, ν), _⟩) => square (U (.inl (t, x, μ)))
      (U (.inl (t, spatialStep x μ, ν))) (U (.inl (t, spatialStep x ν, μ)))
      (U (.inl (t, x, ν)))
  | .inr (t, x, μ) => square (U (.inr (t, x))) (U (.inl (timeNext t, x, μ)))
      (U (.inr (t, spatialStep x μ))) (U (.inl (t.1, x, μ)))

def crossingPlaquetteHolonomy (U : GaugeConfig T L G) (p : CrossingPlaquette L) : G :=
  square (U.2.2 p.1) (U.1 (.inl (0, p.1, p.2))) (U.2.2 (spatialStep p.1 p.2))
    (U.2.1 (.inl (0, p.1, p.2)))

def plaquetteHolonomy (U : GaugeConfig T L G) : Plaquette T L → G
  | .inl (true, p) => halfPlaquetteHolonomy U.1 p
  | .inl (false, p) => halfPlaquetteHolonomy U.2.1 p
  | .inr p => crossingPlaquetteHolonomy U p

private theorem square_gauge (a b c d v w x y : G) :
    square (v * a * w⁻¹) (w * b * x⁻¹) (y * c * x⁻¹) (v * d * y⁻¹) =
      v * square a b c d * v⁻¹ := by
  simp only [square, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]

variable (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ)

def holonomyTrace (u : G) : ℂ := Matrix.trace (ρ u).val

private theorem holonomyTrace_conj (v u : G) :
    holonomyTrace ρ (v * u * v⁻¹) = holonomyTrace ρ u := by
  rw [holonomyTrace, holonomyTrace, map_mul, Matrix.UnitaryGroup.mul_val,
    Matrix.trace_mul_comm, ← Matrix.UnitaryGroup.mul_val, ← map_mul]
  simp [← mul_assoc]

omit [NeZero T] in
private theorem half_trace_gauge (k : HalfSite T L → G) (U : HalfConfig T L G)
    (p : HalfPlaquette T L) :
    holonomyTrace ρ (halfPlaquetteHolonomy (halfGauge k U) p) =
      holonomyTrace ρ (halfPlaquetteHolonomy U p) := by
  rcases p with ⟨t, x, ⟨⟨μ, ν⟩, h⟩⟩ | ⟨t, x, μ⟩
  · have hstep : spatialStep (spatialStep x μ) ν = spatialStep (spatialStep x ν) μ := by
      simp only [spatialStep, add_right_comm]
    simp only [halfPlaquetteHolonomy, halfGauge, halfEndpoints, ← hstep, square_gauge,
      holonomyTrace_conj]
  · simp only [halfPlaquetteHolonomy, halfGauge, halfEndpoints, square_gauge, holonomyTrace_conj]

theorem plaquette_trace_gauge_invariant (k : Site T L → G) (U : GaugeConfig T L G)
    (p : Plaquette T L) :
    holonomyTrace ρ (plaquetteHolonomy (gaugeTransform k U) p) =
      holonomyTrace ρ (plaquetteHolonomy U p) := by
  rcases p with ⟨b, p⟩ | ⟨x, μ⟩
  · cases b
    · exact half_trace_gauge ρ (fun s => k (false, s)) U.2.1 p
    · exact half_trace_gauge ρ (fun s => k (true, s)) U.1 p
  · simp only [plaquetteHolonomy, crossingPlaquetteHolonomy, gaugeTransform, halfGauge,
      halfEndpoints, crossingEndpoints, square_gauge, holonomyTrace_conj]

def halfWilsonAction [NeZero L] (U : HalfConfig T L G) : ℝ :=
  ∑ p : HalfPlaquette T L, (holonomyTrace ρ (halfPlaquetteHolonomy U p)).re

def wilsonAction [NeZero L] (U : GaugeConfig T L G) : ℝ :=
  halfWilsonAction ρ U.1 + halfWilsonAction ρ U.2.1 +
    ∑ p : CrossingPlaquette L, (holonomyTrace ρ (crossingPlaquetteHolonomy U p)).re

theorem wilson_action_gauge_invariant [NeZero L] (k : Site T L → G) (U : GaugeConfig T L G) :
    wilsonAction ρ (gaugeTransform k U) = wilsonAction ρ U := by
  have hc (p : CrossingPlaquette L) :
      holonomyTrace ρ (crossingPlaquetteHolonomy (gaugeTransform k U) p) =
        holonomyTrace ρ (crossingPlaquetteHolonomy U p) :=
    plaquette_trace_gauge_invariant ρ k U (.inr p)
  simp only [wilsonAction, halfWilsonAction, hc]
  congr 1
  simp only [gaugeTransform, half_trace_gauge]

/-- The boundary field extended constantly in time on the positive half. -/
def temporalGauge (c : CrossingConfig L G) : Site T L → G
  | (true, _, x) => c x
  | (false, _, _) => 1

/-- Gauge fixing acts by a permutation of half fields for each fixed crossing field. -/
def temporalGaugeFiber (c : CrossingConfig L G) :
    (HalfConfig T L G × HalfConfig T L G) ≃ (HalfConfig T L G × HalfConfig T L G) :=
  Equiv.prodCongr
    (Equiv.piCongrRight fun e =>
      (Equiv.mulLeft (c (halfEndpoints e).1.2)).trans
        (Equiv.mulRight (c (halfEndpoints e).2.2)⁻¹))
    (Equiv.refl _)

/-- The explicit time-constant half gauge fixes all crossing links. -/
theorem temporalGauge_transform (c : CrossingConfig L G) (h : HalfConfig T L G × HalfConfig T L G) :
    gaugeTransform (temporalGauge c) (h.1, h.2, c) =
      ((temporalGaugeFiber c h).1, (temporalGaugeFiber c h).2, 1) := by
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext e
    simp [gaugeTransform, halfGauge, temporalGauge, temporalGaugeFiber]
  · funext e
    simp [gaugeTransform, crossingEndpoints, temporalGauge]

variable [NeZero L] [Fintype G]

local instance : DecidableEq (HalfLink T L) := Classical.decEq _

/-- Full counting sum, with the crossing configuration as the outer index. -/
def wilsonSum {M : Type*} [AddCommMonoid M] (F : GaugeConfig T L G → M) : M :=
  ∑ c : CrossingConfig L G, ∑ h : HalfConfig T L G × HalfConfig T L G, F (h.1, h.2, c)

theorem temporal_gauge_fixing {M : Type*} [AddCommMonoid M] (F : GaugeConfig T L G → M)
    (hF : ∀ k U, F (gaugeTransform k U) = F U) :
    wilsonSum F = Fintype.card G ^ (L ^ 3) •
      ∑ h : HalfConfig T L G × HalfConfig T L G, F (h.1, h.2, 1) := by
  have hfiber (c : CrossingConfig L G) :
      (∑ h : HalfConfig T L G × HalfConfig T L G, F (h.1, h.2, c)) =
        ∑ h : HalfConfig T L G × HalfConfig T L G, F (h.1, h.2, 1) := by
    calc
      _ = ∑ h : HalfConfig T L G × HalfConfig T L G,
          F ((temporalGaugeFiber c h).1, (temporalGaugeFiber c h).2, 1) := by
        apply Finset.sum_congr rfl
        intro h _
        rw [← temporalGauge_transform, hF]
      _ = _ := (temporalGaugeFiber c).sum_comp (fun h => F (h.1, h.2, 1))
  simp only [wilsonSum, hfiber, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    ZMod.card, Fintype.card_fin]

def boundaryEntry (p : CrossingPlaquette L × Fin N × Fin N)
    (U : HalfConfig T L G) : ℂ :=
  ρ (U (.inl (0, p.1.1, p.1.2))) p.2.1 p.2.2

omit [NeZero L] [Fintype G] in
theorem crossing_plaquette_factorization (x y : HalfConfig T L G) (p : CrossingPlaquette L) :
    (holonomyTrace ρ (crossingPlaquetteHolonomy (x, y, 1) p)).re =
      ∑ i : Fin N, ∑ j : Fin N,
        (boundaryEntry ρ (p, i, j) x * star (boundaryEntry ρ (p, i, j) y)).re := by
  simp only [crossingPlaquetteHolonomy, Pi.one_apply, square, one_mul, inv_one, mul_one,
    holonomyTrace, map_mul, map_inv, Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.inv_val,
    Matrix.star_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  rfl

/-- Invariance under every site gauge on the chosen half. -/
def HalfGaugeInvariant (f : HalfConfig T L G → ℂ) : Prop :=
  ∀ k U, f (halfGauge k U) = f U

def wilsonWeight (β : ℝ) (U : GaugeConfig T L G) : ℝ :=
  Real.exp (β * wilsonAction ρ U)

def wilsonPartition (β : ℝ) : ℝ :=
  wilsonSum (wilsonWeight (T := T) (L := L) ρ β)

private theorem wilsonPartition_pos (β : ℝ) : 0 < wilsonPartition (T := T) (L := L) ρ β := by
  unfold wilsonPartition wilsonSum
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro c _
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro h _
  exact Real.exp_pos _

/-- Full counting Wilson pairing divided by the partition function. -/
def wilsonPairing (β : ℝ) (f g : HalfConfig T L G → ℂ) : ℂ :=
  (wilsonSum fun U : GaugeConfig T L G =>
    (wilsonWeight ρ β U : ℂ) * (star (f (reflectGaugeConfig U).1) * g U.1)) /
      (wilsonPartition (T := T) (L := L) ρ β : ℂ)

private def wilsonScale (β : ℝ) : ℝ :=
  ((Fintype.card G : ℕ) ^ (L ^ 3) : ℕ) / wilsonPartition (T := T) (L := L) ρ β

private theorem wilsonScale_nonneg (β : ℝ) : 0 ≤ wilsonScale (T := T) (L := L) ρ β :=
  div_nonneg (Nat.cast_nonneg _) (wilsonPartition_pos (T := T) (L := L) ρ β).le

private theorem wilsonPairing_fixed (β : ℝ) {f g : HalfConfig T L G → ℂ}
    (hf : HalfGaugeInvariant f) (hg : HalfGaugeInvariant g) :
    wilsonPairing ρ β f g = (wilsonScale (T := T) (L := L) ρ β : ℂ) *
      ∑ x : HalfConfig T L G, ∑ y : HalfConfig T L G,
        (wilsonWeight ρ β (x, y, 1) : ℂ) * (star (f y) * g x) := by
  unfold wilsonPairing wilsonScale
  rw [temporal_gauge_fixing _ (fun k U => by
    have hn : f (reflectGaugeConfig (gaugeTransform k U)).1 =
        f (reflectGaugeConfig U).1 := hf (fun s => k (false, s)) U.2.1
    have hp : g (gaugeTransform k U).1 = g U.1 := hg (fun s => k (true, s)) U.1
    simp only [wilsonWeight, wilson_action_gauge_invariant, hn, hp])]
  rw [Fintype.sum_prod_type, nsmul_eq_mul, Complex.ofReal_div, Complex.ofReal_natCast,
    div_mul_eq_mul_div]
  simp only [reflectGaugeConfig]

omit [Fintype G] in
private theorem wilsonWeight_fixed (β : ℝ) (x y : HalfConfig T L G) :
    wilsonWeight ρ β (x, y, 1) =
      boltzmann (halfWilsonAction ρ) (boundaryEntry ρ) (fun _ => 1) β x y := by
  simp only [wilsonWeight, wilsonAction, boltzmann, interaction, Fintype.sum_prod_type,
    one_mul, crossing_plaquette_factorization]

private theorem wilsonPairing_eq_reflectionPairing (β : ℝ) {f g : HalfConfig T L G → ℂ}
    (hf : HalfGaugeInvariant f) (hg : HalfGaugeInvariant g) :
    wilsonPairing ρ β f g = reflectionPairing (fun x y =>
      Real.sqrt (wilsonScale (T := T) (L := L) ρ β) *
      Real.sqrt (wilsonScale (T := T) (L := L) ρ β) *
      boltzmann (halfWilsonAction ρ) (boundaryEntry ρ) (fun _ => 1) β x y) f g := by
  rw [wilsonPairing_fixed ρ β hf hg]
  simp only [reflectionPairing, Real.mul_self_sqrt (wilsonScale_nonneg ρ β),
    Finset.mul_sum, wilsonWeight_fixed, Complex.ofReal_mul, mul_assoc]

/-- Finite-volume link reflection positivity for the normalized Wilson pairing. -/
theorem lattice_ym_4d_reflection_positivity (β : ℝ) (hβ : 0 ≤ β)
    (f : HalfConfig T L G → ℂ) (hf : HalfGaugeInvariant f) :
    0 ≤ (wilsonPairing ρ β f f).re ∧ (wilsonPairing ρ β f f).im = 0 := by
  rw [wilsonPairing_eq_reflectionPairing ρ β hf hf]
  exact exponential_boltzmann_reflection_positivity
    (fun _ => Real.sqrt (wilsonScale (T := T) (L := L) ρ β))
    (halfWilsonAction ρ) (boundaryEntry ρ) (fun _ => 1) β
    (fun _ => zero_le_one) hβ f

/-- Cauchy–Schwarz for the normalized Wilson pairing on the two gauge-invariant observables. -/
theorem lattice_ym_4d_cauchy_schwarz (β : ℝ) (hβ : 0 ≤ β)
    (f g : HalfConfig T L G → ℂ) (hf : HalfGaugeInvariant f) (hg : HalfGaugeInvariant g) :
    ‖wilsonPairing ρ β f g‖ ^ 2 ≤
      (wilsonPairing ρ β f f).re * (wilsonPairing ρ β g g).re := by
  rw [wilsonPairing_eq_reflectionPairing ρ β hf hg,
    wilsonPairing_eq_reflectionPairing ρ β hf hf,
    wilsonPairing_eq_reflectionPairing ρ β hg hg]
  apply reflectionPairing_cauchy_schwarz
  · intro x y
    have hv : interaction (boundaryEntry ρ) (fun _ => 1) x y =
        interaction (boundaryEntry ρ) (fun _ => 1) y x := by
      rw [interaction_gram _ _ (fun _ => zero_le_one) x y,
        interaction_gram _ _ (fun _ => zero_le_one) y x]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    simp only [boltzmann, hv, add_comm (halfWilsonAction ρ x) (halfWilsonAction ρ y)]
  · intro u
    exact (exponential_boltzmann_reflection_positivity
      (fun _ => Real.sqrt (wilsonScale (T := T) (L := L) ρ β))
      (halfWilsonAction ρ) (boundaryEntry ρ) (fun _ => 1) β
      (fun _ => zero_le_one) hβ u).1

end WilsonGauge

section WilsonLoops

open Matrix
open D5.S3.StatisticalMechanics.ZTwoHighTemperatureExpansion

/-- The Boltzmann factor of a single sign. -/
theorem ising_boltzmann_expansion (β s : ℝ) (hs : s = 1 ∨ s = -1) :
    Real.exp (β * s) = Real.cosh β * (1 + Real.tanh β * s) := by
  have h : Real.cosh β * Real.tanh β = Real.sinh β := by
    rw [Real.tanh_eq_sinh_div_cosh, mul_comm, div_mul_cancel₀ _ (Real.cosh_pos β).ne']
  rw [mul_add, mul_one, ← mul_assoc, h]
  rcases hs with rfl | rfl <;> simp [← sub_eq_add_neg]

variable {P E : Type*} [Fintype P] [Fintype E] [DecidableEq P] [DecidableEq E]

/-- The plaquettes where the bit surface is nonzero. -/
def plaquetteSupport (S : P → ZMod 2) : Finset P :=
  Finset.univ.filter (fun p => S p ≠ 0)

/-- Bit surfaces with the prescribed boundary. -/
def fillings (M : Matrix P E (ZMod 2)) (c : E → ZMod 2) : Finset (P → ZMod 2) :=
  Finset.univ.filter (fun S => Mᵀ *ᵥ S = c)

/-- Fillings that contain no filling with strictly smaller support. -/
def minimalFillings (M : Matrix P E (ZMod 2)) (c : E → ZMod 2) : Finset (P → ZMod 2) :=
  (fillings M c).filter fun S =>
    ∀ T ∈ fillings M c, plaquetteSupport T ⊆ plaquetteSupport S →
      plaquetteSupport S ⊆ plaquetteSupport T

def surfaceSum (M : Matrix P E (ZMod 2)) (t : ℝ) (c : E → ZMod 2) : ℝ :=
  ∑ S ∈ fillings M c, t ^ (plaquetteSupport S).card

/-- The normalized finite Wilson expectation with parity insertion `c`. -/
def wilsonExpectation (M : Matrix P E (ZMod 2)) (β : ℝ) (c : E → ZMod 2) : ℝ :=
  (∑ σ : E → ZMod 2, sgn ℝ (c ⬝ᵥ σ) * Real.exp (β * ∑ p, sgn ℝ ((M *ᵥ σ) p))) /
    (∑ σ : E → ZMod 2, Real.exp (β * ∑ p, sgn ℝ ((M *ᵥ σ) p)))

private theorem wilsonSpinSum_eq (M : Matrix P E (ZMod 2)) (β : ℝ) (c : E → ZMod 2) :
    (∑ σ : E → ZMod 2, sgn ℝ (c ⬝ᵥ σ) * Real.exp (β * ∑ p, sgn ℝ ((M *ᵥ σ) p))) =
      (Real.cosh β ^ Fintype.card P * 2 ^ Fintype.card E) * surfaceSum M (Real.tanh β) c := by
  have h (σ : E → ZMod 2) :
      Real.exp (β * ∑ p, sgn ℝ ((M *ᵥ σ) p)) =
        Real.cosh β ^ Fintype.card P * ∏ p, (1 + Real.tanh β * sgn ℝ ((M *ᵥ σ) p)) := by
    rw [Finset.mul_sum, Real.exp_sum, ← Finset.card_univ (α := P), ← Finset.prod_const,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ising_boltzmann_expansion _ _ ?_
    by_cases hp : (M *ᵥ σ) p = 0 <;> simp [sgn, hp]
  simp_rw [h, mul_left_comm (sgn ℝ _) (Real.cosh β ^ Fintype.card P), ← Finset.mul_sum]
  rw [sum_sgn_mul_prod_one_add_eq M (fun _ => Real.tanh β) c, mul_assoc]
  simp only [surfaceSum, fillings, plaquetteSupport, Finset.prod_const]

theorem wilsonExpectation_eq_surfaceRatio (M : Matrix P E (ZMod 2)) (β : ℝ)
    (c : E → ZMod 2) :
    wilsonExpectation M β c = surfaceSum M (Real.tanh β) c / surfaceSum M (Real.tanh β) 0 := by
  have hzero := wilsonSpinSum_eq M β 0
  have hsign : sgn ℝ 0 = 1 := by simp [sgn]
  simp only [zero_dotProduct, hsign, one_mul] at hzero
  rw [wilsonExpectation, wilsonSpinSum_eq, hzero, mul_div_mul_left]
  exact mul_ne_zero (pow_ne_zero _ (Real.cosh_pos β).ne') (pow_ne_zero _ two_ne_zero)

omit [DecidableEq E] in
theorem one_le_closedSurfaceSum (M : Matrix P E (ZMod 2)) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ surfaceSum M t 0 := by
  have hzero : (0 : P → ZMod 2) ∈ fillings M 0 := by simp [fillings]
  simpa [surfaceSum, plaquetteSupport] using
    (Finset.single_le_sum (f := fun S : P → ZMod 2 => t ^ (plaquetteSupport S).card)
      (fun _ _ => pow_nonneg ht _) hzero)

private theorem tanh_nonneg_of_nonneg {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ Real.tanh β := by
  rw [Real.tanh_eq]
  exact div_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_nonpos_of_nonneg hβ |>.trans hβ)))
    (add_pos (Real.exp_pos _) (Real.exp_pos _)).le

private theorem plaquetteSupport_sub {S T : P → ZMod 2}
    (hTS : plaquetteSupport T ⊆ plaquetteSupport S) :
    plaquetteSupport (S - T) = plaquetteSupport S \ plaquetteSupport T := by
  have bit (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide
  ext p
  by_cases hT : T p = 0
  · simp [plaquetteSupport, hT]
  · have hS : S p ≠ 0 := by
      simpa [plaquetteSupport] using hTS (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hT⟩)
    have hp : S p = T p := ((bit _).resolve_left hS).trans ((bit _).resolve_left hT).symm
    simp [plaquetteSupport, hp, hT]

omit [DecidableEq E] in
private theorem exists_minimalFilling_subset (M : Matrix P E (ZMod 2)) (c : E → ZMod 2)
    {S : P → ZMod 2} (hS : S ∈ fillings M c) :
    ∃ T ∈ minimalFillings M c, plaquetteSupport T ⊆ plaquetteSupport S := by
  let candidates := (fillings M c).filter fun T => plaquetteSupport T ⊆ plaquetteSupport S
  obtain ⟨T, hT, hmin⟩ := candidates.exists_min_image (fun T => (plaquetteSupport T).card)
    ⟨S, Finset.mem_filter.mpr ⟨hS, Finset.Subset.rfl⟩⟩
  obtain ⟨hTc, hTS⟩ := Finset.mem_filter.mp hT
  refine ⟨T, Finset.mem_filter.mpr ⟨hTc, ?_⟩, hTS⟩
  intro U hU hUT
  exact (Finset.eq_of_subset_of_card_le hUT
    (hmin U (Finset.mem_filter.mpr ⟨hU, hUT.trans hTS⟩))).ge

omit [DecidableEq E] in
private theorem surfaceSum_le_minimal_mul_closed (M : Matrix P E (ZMod 2))
    (c : E → ZMod 2) {t : ℝ} (ht : 0 ≤ t) :
    surfaceSum M t c ≤ (∑ T ∈ minimalFillings M c, t ^ (plaquetteSupport T).card) *
      surfaceSum M t 0 := by
  classical
  choose T hT hTS using fun S : (fillings M c) => exists_minimalFilling_subset M c S.property
  let split (S : (fillings M c)) := (T S, (S : P → ZMod 2) - T S)
  let weight (s : (P → ZMod 2) × (P → ZMod 2)) :=
    t ^ (plaquetteSupport s.1).card * t ^ (plaquetteSupport s.2).card
  -- Addition recovers the original surface from the chosen pair.
  have hsplit : Function.Injective split := by
    intro S U h
    apply Subtype.ext
    simpa [split, add_comm (T S), add_comm (T U)] using
      congrArg (fun s : (P → ZMod 2) × (P → ZMod 2) => s.1 + s.2) h
  unfold surfaceSum
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product', ← Finset.sum_attach (fillings M c)]
  refine Finset.sum_le_sum_of_injOn (g := weight) split hsplit.injOn ?_ ?_ ?_
  · intro s hs
    obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hs
    refine Finset.mem_product.mpr ⟨hT S, ?_⟩
    have hSc := (Finset.mem_filter.mp S.property).2
    have hTc := (Finset.mem_filter.mp (Finset.mem_filter.mp (hT S)).1).2
    simp [split, fillings, Matrix.mulVec_sub, hSc, hTc]
  · intro S _
    have hdiff := plaquetteSupport_sub (hTS S)
    have hdisjoint : Disjoint (plaquetteSupport (T S)) (plaquetteSupport (↑S - T S)) := by
      rw [hdiff]
      exact Finset.disjoint_sdiff
    have hunion : plaquetteSupport (T S) ∪ plaquetteSupport (↑S - T S) = plaquetteSupport ↑S := by
      rw [hdiff, Finset.union_sdiff_of_subset (hTS S)]
    dsimp [weight, split]
    rw [← pow_add, ← Finset.card_union_of_disjoint hdisjoint, hunion]
  · intro s _ _
    exact mul_nonneg (pow_nonneg ht _) (pow_nonneg ht _)

/-- With injective boundary there is a unique filling and the only closed surface is zero. -/
omit [DecidableEq P] in
private theorem wilsonExpectation_eq_pow_of_injective (M : Matrix P E (ZMod 2))
    (hM : Function.Injective (Mᵀ *ᵥ ·)) (β : ℝ) (S : P → ZMod 2) :
    wilsonExpectation M β (Mᵀ *ᵥ S) = (Real.tanh β) ^ (plaquetteSupport S).card := by
  classical
  have hf : ∀ U, fillings M (Mᵀ *ᵥ U) = {U} := by
    intro U
    ext V
    simp [fillings, hM.eq_iff]
  have hz : fillings M 0 = {0} := by simpa using hf 0
  simp [wilsonExpectation_eq_surfaceRatio, surfaceSum, hf, hz, plaquetteSupport]

open Omega.CubicalBox in
/-- On an open planar box the four sides of a rectangle have a unique filling. -/
theorem wilson_loop_2d_exact_area_law {w : Fin 2 → ℕ} (r : Rectangle w) (β : ℝ) :
    wilsonExpectation (incidence w) β r.perimeter = Real.tanh β ^ (r.width * r.height) ∧
      (0 < β → 0 < -Real.log (Real.tanh β) ∧
        wilsonExpectation (incidence w) β r.perimeter =
          Real.exp (-(-Real.log (Real.tanh β)) * ((r.width * r.height : ℕ) : ℝ))) := by
  rw [← r.loop_eq_perimeter]
  have hpow : wilsonExpectation (incidence w) β r.loop = Real.tanh β ^ (r.width * r.height) := by
    simpa only [Rectangle.loop, plaquetteSupport, r.filling_support_card] using
      wilsonExpectation_eq_pow_of_injective (incidence w) (boundary_injective_2d w) β r.filling
  refine ⟨hpow, fun hβ => ?_⟩
  have ht : 0 < Real.tanh β := by
    rw [Real.tanh_eq]
    exact div_pos (sub_pos.mpr (Real.exp_lt_exp.mpr ((neg_neg_of_pos hβ).trans hβ)))
      (add_pos (Real.exp_pos _) (Real.exp_pos _))
  refine ⟨neg_pos.mpr (Real.log_neg ht (Real.tanh_lt_one _)), ?_⟩
  rw [hpow, neg_neg, mul_comm (Real.log (Real.tanh β)), Real.exp_nat_mul, Real.exp_log ht]

open Omega.CubicalBox in
/-- Each square in the rectangle's footprint requires a distinct plaquette of any filling. -/
theorem hypercubic_4d_minimal_surface_area_bound {w : Fin 4 → ℕ} (r : Rectangle w)
    (S : Omega.CubicalBox.Plaquette w → ZMod 2) (h : (incidence w)ᵀ *ᵥ S = r.perimeter) :
    r.width * r.height ≤ (Finset.univ.filter fun p => S p ≠ 0).card := by
  classical
  have exists_cell (q : Fin r.width × Fin r.height) :
      ∃ p : Omega.CubicalBox.Plaquette w, (p.1.1 = (r.i, r.j) ∧
        (p.1.2 r.i).val = (r.corner r.i).val + q.1.val ∧
        (p.1.2 r.j).val = (r.corner r.j).val + q.2.val) ∧ S p ≠ 0 := by
    have sameBoundary := h.trans r.loop_eq_perimeter.symm
    have parity := (projectedCoefficient_eq_of_boundary_eq r.i r.j r.ordered _ _ sameBoundary).trans
      (r.projected_filling q)
    by_contra! empty
    have zero : projectedCoefficient r.i r.j ((r.corner r.i).val + q.1.val)
        ((r.corner r.j).val + q.2.val) S = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      split
      · exact empty p ‹_›
      · rfl
    rw [zero] at parity
    exact zero_ne_one parity
  choose f hf hn using exists_cell
  have inj : Function.Injective f := by
    intro q q' he
    have hi := (hf q).2.1.symm.trans (he ▸ (hf q').2.1)
    have hj := (hf q).2.2.symm.trans (he ▸ (hf q').2.2)
    exact Prod.ext (Fin.ext (Nat.add_left_cancel hi)) (Fin.ext (Nat.add_left_cancel hj))
  have bound := Finset.card_le_card_of_injOn f
    (s := Finset.univ) (t := Finset.univ.filter fun p => S p ≠ 0)
    (fun q _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn q⟩) inj.injOn
  simpa using bound


set_option maxHeartbeats 600000 in
open Omega.CubicalBox in
/-- The closed surfaces cancel from the upper bound, and each minimal filling has at least the
area of the rectangle. -/
theorem strong_coupling_4d_minimal_surface_expansion_bound {w : Fin 4 → ℕ}
    (r : Rectangle w) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ wilsonExpectation (incidence w) β r.perimeter ∧
      wilsonExpectation (incidence w) β r.perimeter ≤
        ∑ S ∈ minimalFillings (incidence w) r.perimeter, Real.tanh β ^ (plaquetteSupport S).card ∧
      ∀ S ∈ minimalFillings (incidence w) r.perimeter, r.width * r.height ≤ (plaquetteSupport S).card := by
  classical
  have ht := tanh_nonneg_of_nonneg hβ
  have hden : 0 < surfaceSum (incidence w) (Real.tanh β) 0 :=
    zero_lt_one.trans_le (one_le_closedSurfaceSum (incidence w) ht)
  rw [wilsonExpectation_eq_surfaceRatio]
  refine ⟨div_nonneg (Finset.sum_nonneg fun _ _ => pow_nonneg ht _) hden.le,
    (div_le_iff₀ hden).mpr (surfaceSum_le_minimal_mul_closed (incidence w) _ ht), ?_⟩
  intro S hS
  have hs : S ∈ fillings (incidence w) r.perimeter := (Finset.mem_filter.mp hS).1
  exact hypercubic_4d_minimal_surface_area_bound r S (Finset.mem_filter.mp hs).2

end WilsonLoops

end D5.S3.Quantum.Gauge.LatticeReflectionPositivity4D
