/- GID: D5/S3/QuantumBounds/QuaternionicDeutschEquality
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/QuaternionicDeutschEquality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Quaternionic Deutsch lower equality rigidity and simultaneous equality. -/

/- proof_shape: result: content
   escape_witness: none (external open-problem settlement admission)
   admission_basis: open-problem-resolution (#23061; Proved)
   Direct frozen dependencies: none
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27109
   The public claim keeps the preregistered source conventions literally; private
   helpers use the same definitions on the proof path. Private proof helpers are
   classified in the delivery record; the settling theorem is the sole public theorem. -/

import Mathlib.Analysis.Quaternion
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Equality classification for Krishna, arXiv:2610.35881v1, Question 2.12.
The question asks for equality cases, rather than asserting an answer.
The answer below concerns the central lower endpoint and simultaneous
equality in the chain, on the nonzero domain of the source's normalization.
Mathlib's InnerProductSpace has RCLike scalars, so it cannot represent this
right quaternionic inner product. Quaternion, Module, norm, completeness,
measurability, measure, rank, and Lebesgue integral retain their existing owners.
Right multiplication x q is (MulOpposite.op q) • x.
Entropy uses the nonnegative extended integral of -p log p. On source-admissible
1-bounded frames the integrand is nonnegative; infinite entropy is retained.
-/

noncomputable section

namespace D5.S3.QuantumBounds.QuaternionicDeutschEquality

open MeasureTheory
open scoped Quaternion ENNReal

universe u v w

attribute [local instance] borel

/-- Definition 1.9, with the norm-induced completeness supplied by CompleteSpace. -/
structure RightHilbert (Q : Type u) [NormedAddCommGroup Q] [Module ℍᵐᵒᵖ Q] where
  inner : Q → Q → ℍ
  self_real : ∀ x : Q, inner x x = ((inner x x).re : ℍ)
  self_nonneg : ∀ x : Q, 0 ≤ (inner x x).re
  definite : ∀ x : Q, inner x x = 0 → x = 0
  add_left : ∀ x y z : Q, inner (x + y) z = inner x z + inner y z
  right_linear : ∀ (x y : Q) (q : ℍ),
    inner x ((MulOpposite.op q) • y) = inner x y * q
  conjugate_symmetry : ∀ x y : Q, inner x y = star (inner y x)
  norm_eq : ∀ x : Q, ‖x‖ = Real.sqrt (inner x x).re

variable {Q : Type u} [NormedAddCommGroup Q] [Module ℍᵐᵒᵖ Q]
variable {Ω : Type v} {Δ : Type w} [MeasurableSpace Ω] [MeasurableSpace Δ]

/-- Definition 2.7: measurable coefficients and Parseval for every vector.
The nonnegative integral prevents a divergent real integral being assigned zero. -/
def ContinuousParseval (h : RightHilbert Q) (μ : Measure Ω) (τ : Ω → Q) : Prop :=
  (∀ x : Q, Measurable (fun α : Ω => h.inner (τ α) x)) ∧
    ∀ x : Q, (∫⁻ α : Ω, ENNReal.ofReal (‖h.inner (τ α) x‖ ^ 2) ∂μ) =
      ENNReal.ofReal (‖x‖ ^ 2)

/-- Definition 2.8 is pointwise, including null indices. -/
def OneBounded (τ : Ω → Q) : Prop := ∀ α : Ω, ‖τ α‖ ≤ 1

/-- The source's Q_tau: no deletion of zero coefficients on null sets. -/
def EntropyDomain (h : RightHilbert Q) (τ : Ω → Q) : Set Q :=
  {x : Q | ∀ α : Ω, h.inner (τ α) x ≠ 0}

/-- The source's x / norm x is right multiplication by the inverse real norm. -/
def unitVector (x : Q) : Q :=
  (MulOpposite.op ((‖x‖⁻¹ : ℝ) : ℍ)) • x

def density (h : RightHilbert Q) (τ : Ω → Q) (x : Q) (α : Ω) : ℝ :=
  ‖h.inner (τ α) (unitVector x)‖ ^ 2

/-- Continuous Shannon entropy in nats, with its possible infinite value retained. -/
def entropy (h : RightHilbert Q) (μ : Measure Ω) (τ : Ω → Q) (x : Q) : ℝ≥0∞ :=
  ∫⁻ α : Ω, ENNReal.ofReal
    (-(density h τ x α) * Real.log (density h τ x α)) ∂μ

/-- The supremum in (11) is over every pair of indices, not an essential supremum. -/
def overlap (h : RightHilbert Q) (τ : Ω → Q) (ω : Δ → Q) : ℝ :=
  sSup (Set.range (fun z : Ω × Δ => ‖h.inner (τ z.1) (ω z.2)‖))

def deutschEndpoint (h : RightHilbert Q) (τ : Ω → Q) (ω : Δ → Q) : ℝ≥0∞ :=
  ENNReal.ofReal (-2 * Real.log ((1 + overlap h τ ω) / 2))

def lowerEquality (h : RightHilbert Q) (μ : Measure Ω) (ν : Measure Δ)
    (τ : Ω → Q) (ω : Δ → Q) (x : Q) : Prop :=
  entropy h μ τ x + entropy h ν ω x = deutschEndpoint h τ ω

def rigid (μ : Measure Ω) (ν : Measure Δ) (τ : Ω → Q) (ω : Δ → Q) : Prop :=
  Module.rank ℍᵐᵒᵖ Q = 1 ∧ (∀ᵐ α ∂μ, ‖τ α‖ = 1) ∧ (∀ᵐ β ∂ν, ‖ω β‖ = 1)

/-- Every quantity in (11) equals zero, without converting infinite masses to reals. -/
def simultaneousEquality (h : RightHilbert Q) (μ : Measure Ω) (ν : Measure Δ)
    (τ : Ω → Q) (ω : Δ → Q) (x : Q) : Prop :=
  μ Set.univ = 1 ∧ ν Set.univ = 1 ∧ overlap h τ ω = 1 ∧
    entropy h μ τ x = 0 ∧ entropy h ν ω x = 0

/-- Nonvacuity is a conclusion: an actual source frame pair with an equality state exists. -/
def equalityModelExists : Prop :=
  ∃ (Q : Type u) (_ : NormedAddCommGroup Q) (_ : Module ℍᵐᵒᵖ Q)
    (_ : CompleteSpace Q) (h : RightHilbert Q)
    (Ω : Type v) (Δ : Type w) (_ : MeasurableSpace Ω) (_ : MeasurableSpace Δ)
    (μ : Measure Ω) (ν : Measure Δ) (τ : Ω → Q) (ω : Δ → Q) (x : Q),
    ContinuousParseval h μ τ ∧ ContinuousParseval h ν ω ∧
    OneBounded τ ∧ OneBounded ω ∧ x ≠ 0 ∧
    x ∈ EntropyDomain h τ ∧ x ∈ EntropyDomain h ω ∧ lowerEquality h μ ν τ ω x

/-- Proposed answer to Question 2.12, with the state and pair quantifiers explicit.
The classification of equality at the upper link alone is outside this statement. -/
def claim : Prop :=
  equalityModelExists.{u,v,w} ∧
  ∀ (Q : Type u) (_ : NormedAddCommGroup Q) (_ : Module ℍᵐᵒᵖ Q)
    (_ : CompleteSpace Q) (h : RightHilbert Q)
    (Ω : Type v) (Δ : Type w) (_ : MeasurableSpace Ω) (_ : MeasurableSpace Δ)
    (μ : Measure Ω) (ν : Measure Δ) (τ : Ω → Q) (ω : Δ → Q),
    ContinuousParseval h μ τ → ContinuousParseval h ν ω →
    OneBounded τ → OneBounded ω →
    (∀ x : Q, x ≠ 0 → x ∈ EntropyDomain h τ → x ∈ EntropyDomain h ω →
      (lowerEquality h μ ν τ ω x ↔ rigid μ ν τ ω) ∧
      (lowerEquality h μ ν τ ω x → simultaneousEquality h μ ν τ ω x)) ∧
    ((∃ x : Q, x ≠ 0 ∧ x ∈ EntropyDomain h τ ∧ x ∈ EntropyDomain h ω ∧
        lowerEquality h μ ν τ ω x) ↔
      rigid μ ν τ ω ∧ (∀ α : Ω, τ α ≠ 0) ∧ (∀ β : Δ, ω β ≠ 0))

end D5.S3.QuantumBounds.QuaternionicDeutschEquality

namespace D5.S3.QuantumBounds.QuaternionicDeutschEquality
open MeasureTheory
open scoped Quaternion ENNReal
universe u
variable {Q : Type u} [NormedAddCommGroup Q] [Module ℍᵐᵒᵖ Q]

namespace RightHilbert
variable (h : RightHilbert Q)
include h

private theorem self_re (x : Q) : (h.inner x x).re = ‖x‖ ^ 2 := by
  have hx := Real.sq_sqrt (h.self_nonneg x)
  rw [← h.norm_eq x] at hx
  exact hx.symm

private theorem self (x : Q) : h.inner x x = (‖x‖ ^ 2 : ℝ) := by
  rw [h.self_real, h.self_re]

@[simp] private theorem zero_left (x : Q) : h.inner 0 x = 0 := by
  exact map_zero (AddMonoidHom.mk' (fun a : Q => h.inner a x) (fun a b => h.add_left a b x))

@[simp] private theorem smul_left (x y : Q) (q : ℍ) :
    h.inner ((MulOpposite.op q) • x) y = star q * h.inner x y := by
  rw [h.conjugate_symmetry, h.right_linear, star_mul,
    ← h.conjugate_symmetry]

private theorem norm_smul (x : Q) (q : ℍ) : ‖(MulOpposite.op q) • x‖ = ‖x‖ * ‖q‖ := by
  have hs := congrArg norm (h.smul_left x ((MulOpposite.op q) • x) q)
  rw [h.right_linear x x q, h.self, h.self, norm_mul, norm_mul,
    Quaternion.norm_star, Quaternion.norm_coe, Quaternion.norm_coe,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (sq_nonneg _)] at hs
  nlinarith [norm_nonneg ((MulOpposite.op q) • x), norm_nonneg x, norm_nonneg q,
    mul_nonneg (norm_nonneg x) (norm_nonneg q)]

@[simp] private theorem add_right (x y z : Q) :
    h.inner x (y + z) = h.inner x y + h.inner x z := by
  rw [h.conjugate_symmetry, h.add_left, star_add,
    ← h.conjugate_symmetry x y, ← h.conjugate_symmetry x z]

@[simp] private theorem sub_left (x y z : Q) :
    h.inner (x - y) z = h.inner x z - h.inner y z := by
  exact map_sub (AddMonoidHom.mk' (fun a : Q => h.inner a z) (fun a b => h.add_left a b z)) x y

@[simp] private theorem sub_right (x y z : Q) :
    h.inner x (y - z) = h.inner x y - h.inner x z := by
  exact map_sub (AddMonoidHom.mk' (h.inner x) (h.add_right x)) y z

private theorem unit_norm {x : Q} (hx : x ≠ 0) : ‖unitVector x‖ = 1 := by
  rw [unitVector, h.norm_smul, Quaternion.norm_coe, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx)

private theorem inner_norm_symm (x y : Q) : ‖h.inner x y‖ = ‖h.inner y x‖ := by
  rw [h.conjugate_symmetry, Quaternion.norm_star]

private theorem projection_norm_sq (u a : Q) (hu : ‖u‖ = 1) :
    ‖a - (MulOpposite.op (h.inner u a)) • u‖ ^ 2 =
      ‖a‖ ^ 2 - ‖h.inner u a‖ ^ 2 := by
  rw [← h.self_re]
  simp only [h.sub_left, h.sub_right, h.smul_left, h.right_linear]
  rw [h.self u, hu, one_pow, Quaternion.coe_one, one_mul,
    h.conjugate_symmetry a u]
  rw [show h.inner a a - star (h.inner u a) * h.inner u a -
      (star (h.inner u a) * h.inner u a - star (h.inner u a) * h.inner u a) =
        h.inner a a - star (h.inner u a) * h.inner u a by noncomm_ring]
  rw [Quaternion.star_mul_self, Quaternion.re_sub, Quaternion.re_coe,
    h.self_re, Quaternion.normSq_eq_norm_mul_self, ← sq]

private theorem unit_inner_bound (u a : Q) (hu : ‖u‖ = 1) :
    ‖h.inner u a‖ ≤ ‖a‖ := by
  have hp := h.projection_norm_sq u a hu
  nlinarith [sq_nonneg ‖a - (MulOpposite.op (h.inner u a)) • u‖,
    norm_nonneg (h.inner u a), norm_nonneg a]

private theorem cauchy_schwarz (a b : Q) : ‖h.inner a b‖ ≤ ‖a‖ * ‖b‖ := by
  by_cases ha : a = 0
  · simp [ha, h.zero_left]
  have hp := h.unit_inner_bound (unitVector a) b (h.unit_norm ha)
  rw [unitVector, h.smul_left, norm_mul, Quaternion.norm_star, Quaternion.norm_coe,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg a))] at hp
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have he := (mul_le_mul_of_nonneg_left hp hna.le)
  simpa only [← mul_assoc, mul_inv_cancel₀ hna.ne', one_mul] using he

private theorem projection_inner (u a b : Q) (hu : ‖u‖ = 1) :
    h.inner (a - (MulOpposite.op (h.inner u a)) • u)
      (b - (MulOpposite.op (h.inner u b)) • u) =
        h.inner a b - star (h.inner u a) * h.inner u b := by
  simp only [h.sub_left, h.sub_right, h.smul_left, h.right_linear]
  rw [h.self u, hu, one_pow, Quaternion.coe_one, one_mul,
    h.conjugate_symmetry a u]
  noncomm_ring

private theorem buzano (u a b : Q) (hu : ‖u‖ = 1) :
    2 * (‖h.inner u a‖ * ‖h.inner u b‖) ≤ ‖a‖ * ‖b‖ + ‖h.inner a b‖ := by
  let r := ‖h.inner u a‖
  let t := ‖h.inner u b‖
  let A := a - (MulOpposite.op (h.inner u a)) • u
  let B := b - (MulOpposite.op (h.inner u b)) • u
  have hA : ‖A‖ ^ 2 = ‖a‖ ^ 2 - r ^ 2 := h.projection_norm_sq u a hu
  have hB : ‖B‖ ^ 2 = ‖b‖ ^ 2 - t ^ 2 := h.projection_norm_sq u b hu
  have hcross : r * t ≤ ‖h.inner a b‖ + ‖A‖ * ‖B‖ := by
    calc
      r * t = ‖star (h.inner u a) * h.inner u b‖ := by simp [r, t, norm_mul]
      _ = ‖h.inner a b - h.inner A B‖ := by
        rw [h.projection_inner u a b hu]
        congr 1
        noncomm_ring
      _ ≤ ‖h.inner a b‖ + ‖h.inner A B‖ := norm_sub_le _ _
      _ ≤ ‖h.inner a b‖ + ‖A‖ * ‖B‖ := add_le_add le_rfl (h.cauchy_schwarz A B)
  have ha2 : r ^ 2 + ‖A‖ ^ 2 = ‖a‖ ^ 2 := by exact add_eq_of_eq_sub' hA
  have hb2 : t ^ 2 + ‖B‖ ^ 2 = ‖b‖ ^ 2 := by exact add_eq_of_eq_sub' hB
  have hprod : (r ^ 2 + ‖A‖ ^ 2) * (t ^ 2 + ‖B‖ ^ 2) = (‖a‖ * ‖b‖) ^ 2 := by
    rw [ha2, hb2]
    ring
  have hs : (r * t + ‖A‖ * ‖B‖) ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by
    nlinarith only [hprod, sq_nonneg (r * ‖B‖ - t * ‖A‖)]
  have hsum : r * t + ‖A‖ * ‖B‖ ≤ ‖a‖ * ‖b‖ := by
    nlinarith [mul_nonneg (norm_nonneg a) (norm_nonneg b)]
  linarith

end RightHilbert
end D5.S3.QuantumBounds.QuaternionicDeutschEquality

namespace D5.S3.QuantumBounds.QuaternionicDeutschEquality
open MeasureTheory
open scoped Quaternion ENNReal
universe u v w
attribute [local instance] borel
variable {Q : Type u} [NormedAddCommGroup Q] [Module ℍᵐᵒᵖ Q]
variable {Ω : Type v} {Δ : Type w} [MeasurableSpace Ω] [MeasurableSpace Δ]
variable (h : RightHilbert Q)

private theorem density_measurable {μ : Measure Ω} {τ : Ω → Q}
    (hP : ContinuousParseval h μ τ) (x : Q) : Measurable (density h τ x) := by
  borelize ℍ
  exact (hP.1 (unitVector x)).norm.pow_const 2

private theorem density_mass {μ : Measure Ω} {τ : Ω → Q}
    (hP : ContinuousParseval h μ τ) {x : Q} (hx : x ≠ 0) :
    (∫⁻ a, ENNReal.ofReal (density h τ x a) ∂μ) = 1 := by
  simpa only [density, h.unit_norm hx, one_pow, ENNReal.ofReal_one] using hP.2 (unitVector x)

omit [MeasurableSpace Ω] in
private theorem density_bounds {τ : Ω → Q} (hτ : OneBounded τ)
    {x : Q} (hx : x ≠ 0) (hdom : x ∈ EntropyDomain h τ) (a : Ω) :
    0 < density h τ x a ∧ density h τ x a ≤ 1 := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hq : ((‖x‖⁻¹ : ℝ) : ℍ) ≠ 0 := by
    intro hz
    have hzre := congrArg (fun z : ℍ => z.re) hz
    exact (inv_ne_zero hn) (by simpa only [Quaternion.re_coe, Quaternion.re_zero] using hzre)
  have hcoeff : h.inner (τ a) (unitVector x) ≠ 0 := by
    rw [unitVector, h.right_linear]
    exact mul_ne_zero (hdom a) hq
  have hb : ‖h.inner (τ a) (unitVector x)‖ ≤ 1 := by
    have ht := h.cauchy_schwarz (τ a) (unitVector x)
    rw [h.unit_norm hx, mul_one] at ht
    exact ht.trans (hτ a)
  constructor
  · exact pow_pos (norm_pos_iff.mpr hcoeff) 2
  · dsimp [density]
    nlinarith [norm_nonneg (h.inner (τ a) (unitVector x))]

private theorem measure_nonzero {μ : Measure Ω} {τ : Ω → Q}
    (hP : ContinuousParseval h μ τ) {x : Q} (hx : x ≠ 0) : μ ≠ 0 := by
  intro hz
  have hm := density_mass h hP hx
  simp [hz] at hm

private theorem index_nonempty {μ : Measure Ω} {τ : Ω → Q}
    (hP : ContinuousParseval h μ τ) {x : Q} (hx : x ≠ 0) : Nonempty Ω := by
  by_contra he
  have : IsEmpty Ω := not_nonempty_iff.mp he
  have hm := density_mass h hP hx
  simp only [lintegral_of_isEmpty, zero_ne_one] at hm

omit [MeasurableSpace Ω] [MeasurableSpace Δ] in
private theorem overlap_bounds [Nonempty Ω] [Nonempty Δ] {τ : Ω → Q} {ω : Δ → Q}
    (hτ : OneBounded τ) (hω : OneBounded ω) :
    0 ≤ overlap h τ ω ∧ overlap h τ ω ≤ 1 ∧
      ∀ a b, ‖h.inner (τ a) (ω b)‖ ≤ overlap h τ ω := by
  have hb (a : Ω) (b : Δ) : ‖h.inner (τ a) (ω b)‖ ≤ 1 := by
    calc
      _ ≤ ‖τ a‖ * ‖ω b‖ := h.cauchy_schwarz _ _
      _ ≤ 1 * 1 := mul_le_mul (hτ a) (hω b) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hbd : BddAbove (Set.range (fun z : Ω × Δ => ‖h.inner (τ z.1) (ω z.2)‖)) :=
    ⟨1, by rintro _ ⟨⟨a,b⟩, rfl⟩; exact hb a b⟩
  have hle (a : Ω) (b : Δ) : ‖h.inner (τ a) (ω b)‖ ≤ overlap h τ ω :=
    le_csSup hbd (Set.mem_range_self (a,b))
  exact ⟨(norm_nonneg _).trans (hle (Classical.arbitrary Ω) (Classical.arbitrary Δ)),
    csSup_le (Set.range_nonempty _) (by rintro _ ⟨⟨a,b⟩, rfl⟩; exact hb a b), hle⟩

omit [MeasurableSpace Ω] [MeasurableSpace Δ] in
private theorem density_product_bound [Nonempty Ω] [Nonempty Δ]
    {τ : Ω → Q} {ω : Δ → Q} (hτ : OneBounded τ) (hω : OneBounded ω)
    {x : Q} (hx : x ≠ 0) (a : Ω) (b : Δ) :
    density h τ x a * density h ω x b ≤ ((1 + overlap h τ ω) / 2) ^ 2 := by
  have hc := overlap_bounds h hτ hω
  have hb := h.buzano (unitVector x) (τ a) (ω b) (h.unit_norm hx)
  have hp : ‖τ a‖ * ‖ω b‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul (hτ a) (hω b) (norm_nonneg _) zero_le_one
  rw [h.inner_norm_symm (unitVector x) (τ a),
    h.inner_norm_symm (unitVector x) (ω b)] at hb
  have h2 : 2 * (‖h.inner (τ a) (unitVector x)‖ * ‖h.inner (ω b) (unitVector x)‖) ≤
      1 + overlap h τ ω := by linarith [hc.2.2 a b]
  dsimp [density]
  nlinarith [mul_nonneg (norm_nonneg (h.inner (τ a) (unitVector x)))
    (norm_nonneg (h.inner (ω b) (unitVector x)))]

private theorem frame_saturation (u a b : Q) (hu : ‖u‖ = 1)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) {c : ℝ} (hc : 0 ≤ c)
    (hcross : ‖h.inner a b‖ ≤ c)
    (hprod : ‖h.inner u a‖ ^ 2 * ‖h.inner u b‖ ^ 2 = ((1 + c) / 2) ^ 2) :
    ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ ‖h.inner a b‖ = c := by
  have hr : 0 ≤ ‖h.inner u a‖ * ‖h.inner u b‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h2 : 2 * (‖h.inner u a‖ * ‖h.inner u b‖) = 1 + c := by
    nlinarith [sq_nonneg (2 * (‖h.inner u a‖ * ‖h.inner u b‖) - (1+c))]
  have hB := h.buzano u a b hu
  have hp : ‖a‖ * ‖b‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul ha hb (norm_nonneg _) zero_le_one
  have hpa : ‖a‖ * ‖b‖ ≤ ‖a‖ := by simpa using mul_le_mul_of_nonneg_left hb (norm_nonneg a)
  have hpb : ‖a‖ * ‖b‖ ≤ ‖b‖ := by simpa using mul_le_mul_of_nonneg_right ha (norm_nonneg b)
  exact ⟨by linarith, by linarith, by linarith⟩

private theorem rank_one_inner (hrank : Module.rank ℍᵐᵒᵖ Q = 1) (a b : Q) :
    ‖h.inner a b‖ = ‖a‖ * ‖b‖ := by
  by_cases ha : a = 0
  · simp [ha, h.zero_left]
  have hfin : Module.finrank ℍᵐᵒᵖ Q = 1 := (Module.rank_eq_one_iff_finrank_eq_one).mp hrank
  obtain ⟨q,hq⟩ := exists_smul_eq_of_finrank_eq_one hfin ha b
  have hqb : b = (MulOpposite.op (MulOpposite.unop q)) • a := hq.symm
  rw [hqb, h.right_linear, h.self, norm_mul, Quaternion.norm_coe,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), h.norm_smul]
  ring

end D5.S3.QuantumBounds.QuaternionicDeutschEquality

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace D5.S3.QuantumBounds.QuaternionicDeutschEquality.Saturation
universe v w
variable {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω}

private def E (p : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ a, ENNReal.ofReal (-(p a) * Real.log (p a)) ∂μ

private theorem entropy_split {p : Ω → ℝ} (hp : Measurable p)
    (hpos : ∀ a, 0 < p a) (hmass : (∫⁻ a, ENNReal.ofReal (p a) ∂μ) = 1)
    {A : ℝ} (hA : 0 < A) (hA1 : A ≤ 1) (hle : ∀ a, p a ≤ A) :
    E (μ := μ) p = ENNReal.ofReal (-Real.log A) +
      ∫⁻ a, ENNReal.ofReal (p a * (Real.log A - Real.log (p a))) ∂μ := by
  have hc : 0 ≤ -Real.log A := neg_nonneg.mpr (Real.log_nonpos hA.le hA1)
  have hr (a : Ω) : 0 ≤ p a * (Real.log A - Real.log (p a)) :=
    mul_nonneg (hpos a).le (sub_nonneg.mpr (Real.log_le_log (hpos a) (hle a)))
  have heq (a : Ω) : ENNReal.ofReal (-p a * Real.log (p a)) =
      ENNReal.ofReal (-Real.log A) * ENNReal.ofReal (p a) +
        ENNReal.ofReal (p a * (Real.log A - Real.log (p a))) := by
    rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add (mul_nonneg hc (hpos a).le) (hr a)]
    congr 1
    ring
  unfold E
  simp_rw [heq]
  have hmc : Measurable (fun a : Ω => ENNReal.ofReal (-Real.log A) * ENNReal.ofReal (p a)) :=
    measurable_const.mul hp.ennreal_ofReal
  rw [lintegral_add_left hmc, lintegral_const_mul _ hp.ennreal_ofReal, hmass, mul_one]

private theorem entropy_eq_min_iff {p : Ω → ℝ} (hp : Measurable p)
    (hpos : ∀ a, 0 < p a) (hmass : (∫⁻ a, ENNReal.ofReal (p a) ∂μ) = 1)
    {A : ℝ} (hA : 0 < A) (hA1 : A ≤ 1) (hle : ∀ a, p a ≤ A) :
    E (μ := μ) p = ENNReal.ofReal (-Real.log A) ↔ ∀ᵐ a ∂μ, p a = A := by
  rw [entropy_split hp hpos hmass hA hA1 hle]
  have hm : Measurable (fun a => ENNReal.ofReal (p a * (Real.log A - Real.log (p a)))) :=
    (hp.mul (measurable_const.sub hp.log)).ennreal_ofReal
  constructor
  · intro heq
    have hz : (∫⁻ a, ENNReal.ofReal (p a * (Real.log A - Real.log (p a))) ∂μ) = 0 := by
      apply (ENNReal.add_right_inj (a := ENNReal.ofReal (-Real.log A)) ENNReal.ofReal_ne_top).mp
      simpa using heq
    filter_upwards [(lintegral_eq_zero_iff hm).mp hz] with a ha
    have hl := ENNReal.ofReal_eq_zero.mp ha
    have he : Real.log A ≤ Real.log (p a) := by nlinarith [hpos a]
    exact le_antisymm (hle a) ((Real.log_le_log_iff hA (hpos a)).mp he)
  · intro heq
    have hz : (∫⁻ a, ENNReal.ofReal (p a * (Real.log A - Real.log (p a))) ∂μ) = 0 := by
      apply (lintegral_eq_zero_iff hm).mpr
      filter_upwards [heq] with a ha
      simp [ha]
    simp [hz]


variable {Δ : Type w} [MeasurableSpace Δ] {ν : Measure Δ}

private theorem pair_saturation [Nonempty Ω] [Nonempty Δ]
    {p : Ω → ℝ} {q : Δ → ℝ} (hp : Measurable p) (hq : Measurable q)
    (hpos : ∀ a, 0 < p a) (hposq : ∀ b, 0 < q b)
    (hp1 : ∀ a, p a ≤ 1) (hq1 : ∀ b, q b ≤ 1)
    (hpmass : (∫⁻ a, ENNReal.ofReal (p a) ∂μ) = 1)
    (hqmass : (∫⁻ b, ENNReal.ofReal (q b) ∂ν) = 1)
    {M : ℝ} (hM : 0 < M) (hM1 : M ≤ 1)
    (hprod : ∀ a b, p a * q b ≤ M)
    (hsum : E (μ := μ) p + E (μ := ν) q = ENNReal.ofReal (-Real.log M)) :
    ∃ A B : ℝ, 0 < A ∧ A ≤ 1 ∧ 0 < B ∧ B ≤ 1 ∧ A * B = M ∧
      (∀ᵐ a ∂μ, p a = A) ∧ (∀ᵐ b ∂ν, q b = B) := by
  let A := sSup (Set.range p)
  let B := sSup (Set.range q)
  have hpbd : BddAbove (Set.range p) := ⟨1, by rintro _ ⟨a, rfl⟩; exact hp1 a⟩
  have hqbd : BddAbove (Set.range q) := ⟨1, by rintro _ ⟨b, rfl⟩; exact hq1 b⟩
  have hpA (a : Ω) : p a ≤ A := le_csSup hpbd (Set.mem_range_self a)
  have hqB (b : Δ) : q b ≤ B := le_csSup hqbd (Set.mem_range_self b)
  have hA : 0 < A := (hpos (Classical.arbitrary Ω)).trans_le (hpA _)
  have hB : 0 < B := (hposq (Classical.arbitrary Δ)).trans_le (hqB _)
  have hA1 : A ≤ 1 := csSup_le (Set.range_nonempty p) (by rintro _ ⟨a, rfl⟩; exact hp1 a)
  have hB1 : B ≤ 1 := csSup_le (Set.range_nonempty q) (by rintro _ ⟨b, rfl⟩; exact hq1 b)
  have hAB : A * B ≤ M := by
    have hb (b : Δ) : A ≤ M / q b :=
      csSup_le (Set.range_nonempty p) (by
        rintro _ ⟨a, rfl⟩
        exact (le_div_iff₀ (hposq b)).mpr (hprod a b))
    have hBB : B ≤ M / A := csSup_le (Set.range_nonempty q) (by
      rintro _ ⟨b, rfl⟩
      apply (le_div_iff₀ hA).mpr
      simpa [mul_comm] using (le_div_iff₀ (hposq b)).mp (hb b))
    simpa only [mul_comm] using (le_div_iff₀ hA).mp hBB
  let C := ENNReal.ofReal (-Real.log A)
  let D := ENNReal.ofReal (-Real.log B)
  let R := ∫⁻ a, ENNReal.ofReal (p a * (Real.log A - Real.log (p a))) ∂μ
  let S := ∫⁻ b, ENNReal.ofReal (q b * (Real.log B - Real.log (q b))) ∂ν
  have hsplitp : E (μ := μ) p = C + R := entropy_split hp hpos hpmass hA hA1 hpA
  have hsplitq : E (μ := ν) q = D + S := entropy_split hq hposq hqmass hB hB1 hqB
  have hbase : C + D = ENNReal.ofReal (-Real.log (A * B)) := by
    dsimp [C, D]
    rw [Real.log_mul hA.ne' hB.ne', neg_add,
      ENNReal.ofReal_add (neg_nonneg.mpr (Real.log_nonpos hA.le hA1))
        (neg_nonneg.mpr (Real.log_nonpos hB.le hB1))]
  have hCD : ENNReal.ofReal (-Real.log M) ≤ C + D := by
    rw [hbase]
    exact ENNReal.ofReal_le_ofReal (neg_le_neg (Real.log_le_log (mul_pos hA hB) hAB))
  have hLE : C + D ≤ E (μ := μ) p + E (μ := ν) q := by
    rw [hsplitp, hsplitq]
    exact add_le_add (le_add_of_nonneg_right bot_le) (le_add_of_nonneg_right bot_le)
  have hCDexact : C + D = ENNReal.ofReal (-Real.log M) :=
    le_antisymm (hLE.trans_eq hsum) hCD
  have hABexact : A * B = M := by
    have hposAB := mul_pos hA hB
    have hAB1 : A * B ≤ 1 := hAB.trans hM1
    have hh := (ENNReal.ofReal_eq_ofReal_iff
      (neg_nonneg.mpr (Real.log_nonpos hposAB.le hAB1))
      (neg_nonneg.mpr (Real.log_nonpos hM.le hM1))).mp (hbase.symm.trans hCDexact)
    exact Real.log_injOn_pos hposAB hM (neg_injective hh)
  have hRS : R + S = 0 := by
    apply (ENNReal.add_right_inj (show C + D ≠ ∞ by simp [C, D])).mp
    calc
      (C + D) + (R + S) = (C + R) + (D + S) := by ac_rfl
      _ = E (μ := μ) p + E (μ := ν) q := by rw [← hsplitp, ← hsplitq]
      _ = ENNReal.ofReal (-Real.log M) := hsum
      _ = C + D + 0 := by rw [add_zero, hCDexact]
  have hR : R = 0 := (add_eq_zero.mp hRS).1
  have hS : S = 0 := (add_eq_zero.mp hRS).2
  refine ⟨A, B, hA, hA1, hB, hB1, hABexact, ?_, ?_⟩
  · exact (entropy_eq_min_iff hp hpos hpmass hA hA1 hpA).mp (by simpa [hR] using hsplitp)
  · exact (entropy_eq_min_iff hq hposq hqmass hB hB1 hqB).mp (by simpa [hS] using hsplitq)

end D5.S3.QuantumBounds.QuaternionicDeutschEquality.Saturation
namespace D5.S3.QuantumBounds.QuaternionicDeutschEquality
open MeasureTheory
open scoped Quaternion ENNReal
universe u v w
attribute [local instance] borel
variable {Q : Type u} [NormedAddCommGroup Q] [Module ℍᵐᵒᵖ Q]
variable {Ω : Type v} {Δ : Type w} [MeasurableSpace Ω] [MeasurableSpace Δ]
variable (h : RightHilbert Q)

private theorem lower_to_rigid {μ : Measure Ω} {ν : Measure Δ} {τ : Ω → Q} {ω : Δ → Q}
    (hP : ContinuousParseval h μ τ) (hR : ContinuousParseval h ν ω)
    (hτ : OneBounded τ) (hω : OneBounded ω)
    {x : Q} (hx : x ≠ 0) (hdom : x ∈ EntropyDomain h τ) (hdomω : x ∈ EntropyDomain h ω)
    (heq : lowerEquality h μ ν τ ω x) : rigid μ ν τ ω := by
  have : Nonempty Ω := index_nonempty h hP hx
  have : Nonempty Δ := index_nonempty h hR hx
  have : NeZero μ := ⟨measure_nonzero h hP hx⟩
  have : NeZero ν := ⟨measure_nonzero h hR hx⟩
  let p := density h τ x
  let q := density h ω x
  let c := overlap h τ ω
  let u := unitVector x
  have hu : ‖u‖ = 1 := h.unit_norm hx
  have hc := overlap_bounds h hτ hω
  have hp := density_bounds h hτ hx hdom
  have hq := density_bounds h hω hx hdomω
  have hM : 0 < ((1+c)/2)^2 := sq_pos_of_pos (by dsimp [c]; linarith [hc.1])
  have hM1 : ((1+c)/2)^2 ≤ 1 := by dsimp [c]; nlinarith [hc.1,hc.2.1]
  have hsum : Saturation.E (μ := μ) p + Saturation.E (μ := ν) q =
      ENNReal.ofReal (-Real.log (((1+c)/2)^2)) := by
    simpa only [Saturation.E, p, q, c, entropy, lowerEquality, deutschEndpoint,
      Real.log_pow, Nat.cast_ofNat, neg_mul] using heq
  obtain ⟨A,B,hA,hA1,hB,hB1,hAB,hpae,hqae⟩ := Saturation.pair_saturation
    (density_measurable h hP x) (density_measurable h hR x)
    (fun a => (hp a).1) (fun b => (hq b).1) (fun a => (hp a).2) (fun b => (hq b).2)
    (density_mass h hP hx) (density_mass h hR hx) hM hM1
    (density_product_bound h hτ hω hx) hsum
  have sat (a : Ω) (ha : p a = A) (b : Δ) (hb : q b = B) :
      ‖τ a‖ = 1 ∧ ‖ω b‖ = 1 ∧ ‖h.inner (τ a) (ω b)‖ = c := by
    apply frame_saturation h u (τ a) (ω b) hu (hτ a) (hω b) hc.1 (hc.2.2 a b)
    rw [h.inner_norm_symm u (τ a), h.inner_norm_symm u (ω b)]
    change p a * q b = ((1+c)/2)^2
    rw [ha,hb]
    exact hAB
  obtain ⟨a0,ha0⟩ := hpae.exists
  obtain ⟨b0,hb0⟩ := hqae.exists
  have hnorms := sat a0 ha0 b0 hb0
  have hτnorm : ∀ᵐ a ∂μ, ‖τ a‖ = 1 := hpae.mono fun a ha => (sat a ha b0 hb0).1
  have hωnorm : ∀ᵐ b ∂ν, ‖ω b‖ = 1 := hqae.mono fun b hb => (sat a0 ha0 b hb).2.1
  have hμA : ENNReal.ofReal A * μ Set.univ = 1 := by
    calc
      _ = ∫⁻ a : Ω, ENNReal.ofReal A ∂μ := (lintegral_const _).symm
      _ = ∫⁻ a, ENNReal.ofReal (p a) ∂μ :=
        (lintegral_congr_ae (hpae.mono fun a ha => congrArg ENNReal.ofReal ha)).symm
      _ = 1 := density_mass h hP hx
  have hνB : ENNReal.ofReal B * ν Set.univ = 1 := by
    calc
      _ = ∫⁻ b : Δ, ENNReal.ofReal B ∂ν := (lintegral_const _).symm
      _ = ∫⁻ b, ENNReal.ofReal (q b) ∂ν :=
        (lintegral_congr_ae (hqae.mono fun b hb => congrArg ENNReal.ofReal hb)).symm
      _ = 1 := density_mass h hR hx
  have hμc : ENNReal.ofReal (c^2) * μ Set.univ = 1 := by
    calc
      _ = ∫⁻ a : Ω, ENNReal.ofReal (c^2) ∂μ := (lintegral_const _).symm
      _ = ∫⁻ a, ENNReal.ofReal (‖h.inner (τ a) (ω b0)‖^2) ∂μ :=
        (lintegral_congr_ae (hpae.mono fun a ha => by rw [(sat a ha b0 hb0).2.2])).symm
      _ = 1 := by simpa only [hnorms.2.1,one_pow,ENNReal.ofReal_one] using hP.2 (ω b0)
  have hνc : ENNReal.ofReal (c^2) * ν Set.univ = 1 := by
    calc
      _ = ∫⁻ b : Δ, ENNReal.ofReal (c^2) ∂ν := (lintegral_const _).symm
      _ = ∫⁻ b, ENNReal.ofReal (‖h.inner (ω b) (τ a0)‖^2) ∂ν :=
        (lintegral_congr_ae (hqae.mono fun b hb => by
          rw [h.inner_norm_symm (ω b) (τ a0), (sat a0 ha0 b hb).2.2])).symm
      _ = 1 := by simpa only [hnorms.1,one_pow,ENNReal.ofReal_one] using hR.2 (τ a0)
  have hAm : A * (μ Set.univ).toReal = 1 := by
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hA.le,ENNReal.toReal_one] using congrArg ENNReal.toReal hμA
  have hBm : B * (ν Set.univ).toReal = 1 := by
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hB.le,ENNReal.toReal_one] using congrArg ENNReal.toReal hνB
  have hcm : c^2 * (μ Set.univ).toReal = 1 := by
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg c),ENNReal.toReal_one] using congrArg ENNReal.toReal hμc
  have hcn : c^2 * (ν Set.univ).toReal = 1 := by
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg c),ENNReal.toReal_one] using congrArg ENNReal.toReal hνc
  have hAc : A = c^2 := by
    apply mul_right_cancel₀ (b := (μ Set.univ).toReal) (by intro hz; simp [hz] at hAm)
    exact hAm.trans hcm.symm
  have hBc : B = c^2 := by
    apply mul_right_cancel₀ (b := (ν Set.univ).toReal) (by intro hz; simp [hz] at hBm)
    exact hBm.trans hcn.symm
  have hcpos : 0 ≤ c := hc.1
  have hroot : (2*c^2-c-1)*(2*c^2+c+1) = 0 := by rw [hAc,hBc] at hAB; nlinarith [hAB]
  have hroot1 : 2*c^2-c-1 = 0 :=
    (mul_eq_zero.mp hroot).resolve_right (by nlinarith [sq_nonneg c])
  have hfac : (2*c+1)*(c-1) = 0 := by nlinarith [hroot1]
  have hc1 : c = 1 := by
    have ht := (mul_eq_zero.mp hfac).resolve_left (by linarith)
    linarith
  have hAeq : A = 1 := by rw [hAc,hc1,one_pow]
  have hspan : ∀ᵐ a ∂μ, τ a = (MulOpposite.op (h.inner u (τ a))) • u := by
    filter_upwards [hpae,hτnorm] with a ha hn
    have hd : ‖h.inner u (τ a)‖^2 = 1 := by
      rw [h.inner_norm_symm u (τ a)]
      exact ha.trans hAeq
    have hproj := h.projection_norm_sq u (τ a) hu
    rw [hn,one_pow,hd,sub_self] at hproj
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hproj))
  have huspan (y : Q) : ∃ r : ℍᵐᵒᵖ, r • u = y := by
    let v := y - (MulOpposite.op (h.inner u y)) • u
    have huv : h.inner u v = 0 := by
      dsimp [v]
      rw [h.sub_right,h.right_linear,h.self u,hu,one_pow,Quaternion.coe_one,one_mul,sub_self]
    have hvan : ∀ᵐ a ∂μ, h.inner (τ a) v = 0 := by
      filter_upwards [hspan] with a ha
      rw [ha,h.smul_left,huv,mul_zero]
    have hm : ENNReal.ofReal (‖v‖^2) = 0 := by
      rw [← hP.2 v]
      calc
        _ = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂μ := lintegral_congr_ae (hvan.mono fun a ha => by simp [ha])
        _ = 0 := lintegral_zero
    have hv : v = 0 := norm_eq_zero.mp (by nlinarith [ENNReal.ofReal_eq_zero.mp hm, norm_nonneg v])
    exact ⟨MulOpposite.op (h.inner u y), (sub_eq_zero.mp hv).symm⟩
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (hu.trans_ne one_ne_zero)
  exact ⟨rank_eq_one_iff.mpr ⟨u,hu0,huspan⟩,hτnorm,hωnorm⟩


private theorem rigid_to_simultaneous {μ : Measure Ω} {ν : Measure Δ} {τ : Ω → Q} {ω : Δ → Q}
    (hP : ContinuousParseval h μ τ) (hR : ContinuousParseval h ν ω)
    (hτ : OneBounded τ) (hω : OneBounded ω)
    {x : Q} (hx : x ≠ 0) (hr : rigid μ ν τ ω) : simultaneousEquality h μ ν τ ω x := by
  have : Nonempty Ω := index_nonempty h hP hx
  have : Nonempty Δ := index_nonempty h hR hx
  have : NeZero μ := ⟨measure_nonzero h hP hx⟩
  have : NeZero ν := ⟨measure_nonzero h hR hx⟩
  have hp : ∀ᵐ a ∂μ, density h τ x a = 1 := by
    filter_upwards [hr.2.1] with a ha
    simp only [density,rank_one_inner h hr.1,h.unit_norm hx,mul_one,ha,one_pow]
  have hq : ∀ᵐ b ∂ν, density h ω x b = 1 := by
    filter_upwards [hr.2.2] with b hb
    simp only [density,rank_one_inner h hr.1,h.unit_norm hx,mul_one,hb,one_pow]
  have hμ : μ Set.univ = 1 := by
    calc
      _ = ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ := lintegral_one.symm
      _ = ∫⁻ a, ENNReal.ofReal (density h τ x a) ∂μ :=
        (lintegral_congr_ae (hp.mono fun a ha => by simp [ha])).symm
      _ = 1 := density_mass h hP hx
  have hν : ν Set.univ = 1 := by
    calc
      _ = ∫⁻ _ : Δ, (1 : ℝ≥0∞) ∂ν := lintegral_one.symm
      _ = ∫⁻ b, ENNReal.ofReal (density h ω x b) ∂ν :=
        (lintegral_congr_ae (hq.mono fun b hb => by simp [hb])).symm
      _ = 1 := density_mass h hR hx
  have hc : overlap h τ ω = 1 := by
    have hbounds := overlap_bounds h hτ hω
    obtain ⟨a,ha⟩ := hr.2.1.exists
    obtain ⟨b,hb⟩ := hr.2.2.exists
    apply le_antisymm hbounds.2.1
    simpa only [rank_one_inner h hr.1,ha,hb,one_mul] using hbounds.2.2 a b
  have hE : entropy h μ τ x = 0 := by
    unfold entropy
    calc
      _ = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂μ := lintegral_congr_ae (hp.mono fun a ha => by simp [ha])
      _ = 0 := lintegral_zero
  have hF : entropy h ν ω x = 0 := by
    unfold entropy
    calc
      _ = ∫⁻ _ : Δ, (0 : ℝ≥0∞) ∂ν := lintegral_congr_ae (hq.mono fun b hb => by simp [hb])
      _ = 0 := lintegral_zero
  exact ⟨hμ,hν,hc,hE,hF⟩

private theorem lower_of_simultaneous {μ : Measure Ω} {ν : Measure Δ} {τ : Ω → Q} {ω : Δ → Q}
    {x : Q} (hs : simultaneousEquality h μ ν τ ω x) : lowerEquality h μ ν τ ω x := by
  simp only [lowerEquality,deutschEndpoint,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2,zero_add]
  norm_num

omit [MeasurableSpace Ω] in
private theorem rank_one_domain (hrank : Module.rank ℍᵐᵒᵖ Q = 1) {τ : Ω → Q}
    (hτ : ∀ a, τ a ≠ 0) {x : Q} (hx : x ≠ 0) : x ∈ EntropyDomain h τ := by
  intro a
  apply norm_ne_zero_iff.mp
  rw [rank_one_inner h hrank]
  exact mul_ne_zero (norm_ne_zero_iff.mpr (hτ a)) (norm_ne_zero_iff.mpr hx)

omit [MeasurableSpace Ω] in
private theorem frame_nonzero_of_domain {τ : Ω → Q} {x : Q} (hx : x ∈ EntropyDomain h τ) :
    ∀ a, τ a ≠ 0 := by
  intro a ha
  have hd := hx a
  rw [ha,h.zero_left] at hd
  exact hd rfl

end D5.S3.QuantumBounds.QuaternionicDeutschEquality

namespace D5.S3.QuantumBounds.QuaternionicDeutschEquality
open MeasureTheory
open scoped Quaternion ENNReal
universe u v w
attribute [local instance] borel

private noncomputable def quaternionHilbert : RightHilbert (ULift.{u} ℍ) where
  inner x y := star x.down * y.down
  self_real x := Quaternion.star_mul_eq_coe x.down
  self_nonneg x := by
    rw [Quaternion.star_mul_self,Quaternion.re_coe]
    exact Quaternion.normSq_nonneg
  definite x hx := by
    apply ULift.ext
    change x.down = 0
    apply Quaternion.normSq_eq_zero.mp
    apply Quaternion.coe_injective
    simpa only [Quaternion.star_mul_self,Quaternion.coe_zero] using hx
  add_left x y z := by
    change star (x.down + y.down) * z.down = star x.down * z.down + star y.down * z.down
    rw [star_add,add_mul]
  right_linear x y q := by
    change star x.down * (y.down*q) = (star x.down*y.down)*q
    exact (mul_assoc _ _ _).symm
  conjugate_symmetry x y := by
    rw [star_mul,star_star]
  norm_eq x := by
    change ‖x.down‖ = Real.sqrt (star x.down*x.down).re
    simpa only [Quaternion.star_mul_self,Quaternion.re_coe,Quaternion.inner_self] using
      (norm_eq_sqrt_real_inner x.down)

private theorem equality_model : equalityModelExists.{u,v,w} := by
  letI : MeasurableSpace PUnit.{v+1} := ⊤
  letI : MeasurableSpace PUnit.{w+1} := ⊤
  let μ : Measure PUnit.{v+1} := Measure.dirac PUnit.unit
  let ν : Measure PUnit.{w+1} := Measure.dirac PUnit.unit
  let τ : PUnit.{v+1} → ULift.{u} ℍ := fun _ => ULift.up 1
  let ω : PUnit.{w+1} → ULift.{u} ℍ := fun _ => ULift.up 1
  let h := quaternionHilbert.{u}
  have hP : ContinuousParseval h μ τ := by
    constructor
    · intro x
      change Measurable (fun _ : PUnit.{v+1} => star (1 : ℍ) * x.down)
      exact measurable_const
    · intro x
      change (∫⁻ _ : PUnit.{v+1}, ENNReal.ofReal (‖star (1 : ℍ)*x.down‖^2) ∂μ) =
        ENNReal.ofReal (‖x.down‖^2)
      rw [lintegral_const]
      simp [μ]
  have hR : ContinuousParseval h ν ω := by
    constructor
    · intro x
      change Measurable (fun _ : PUnit.{w+1} => star (1 : ℍ) * x.down)
      exact measurable_const
    · intro x
      change (∫⁻ _ : PUnit.{w+1}, ENNReal.ofReal (‖star (1 : ℍ)*x.down‖^2) ∂ν) =
        ENNReal.ofReal (‖x.down‖^2)
      rw [lintegral_const]
      simp [ν]
  refine ⟨ULift.{u} ℍ,inferInstance,inferInstance,inferInstance,h,
    PUnit.{v+1},PUnit.{w+1},inferInstance,inferInstance,μ,ν,τ,ω,ULift.up 1,
    hP,hR,?_,?_,?_,?_,?_,?_⟩
  · intro a
    simp [τ]
  · intro b
    simp [ω]
  · intro hx
    have hd := congrArg ULift.down hx
    exact one_ne_zero hd
  · intro a
    simp [h,quaternionHilbert,τ]
  · intro b
    simp [h,quaternionHilbert,ω]
  · have hdτ : ∀ a, density h τ (ULift.up 1) a = 1 := by
      intro a
      simp [density,unitVector,h,quaternionHilbert,τ]
    have hdω : ∀ b, density h ω (ULift.up 1) b = 1 := by
      intro b
      simp [density,unitVector,h,quaternionHilbert,ω]
    have hov : overlap h τ ω = 1 := by
      simp [overlap,h,quaternionHilbert,τ,ω,Set.range_const]
    simp [lowerEquality,entropy,deutschEndpoint,hdτ,hdω,hov]

end D5.S3.QuantumBounds.QuaternionicDeutschEquality

namespace D5.S3.QuantumBounds.QuaternionicDeutschEquality
open MeasureTheory
open scoped Quaternion ENNReal
universe u v w

theorem result : claim.{u,v,w} := by
  constructor
  · exact equality_model
  · intro Q _ _ _ h Ω Δ _ _ μ ν τ ω hP hR hτ hω
    constructor
    · intro x hx hdom hdomω
      constructor
      · constructor
        · exact lower_to_rigid h hP hR hτ hω hx hdom hdomω
        · intro hr
          exact lower_of_simultaneous h (rigid_to_simultaneous h hP hR hτ hω hx hr)
      · intro hl
        exact rigid_to_simultaneous h hP hR hτ hω hx (lower_to_rigid h hP hR hτ hω hx hdom hdomω hl)
    · constructor
      · rintro ⟨x,hx,hdom,hdomω,hl⟩
        exact ⟨lower_to_rigid h hP hR hτ hω hx hdom hdomω hl,
          frame_nonzero_of_domain h hdom,frame_nonzero_of_domain h hdomω⟩
      · rintro ⟨hr,hnt,hnw⟩
        obtain ⟨x,hx,_⟩ := rank_eq_one_iff.mp hr.1
        exact ⟨x,hx,rank_one_domain h hr.1 hnt hx,rank_one_domain h hr.1 hnw hx,
          lower_of_simultaneous h (rigid_to_simultaneous h hP hR hτ hω hx hr)⟩

end D5.S3.QuantumBounds.QuaternionicDeutschEquality

