/- GID: D5/S3/Quantum/Entanglement/TriangleIndependentSourceNoise
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/TriangleIndependentSourceNoise
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Born distributions and the eight-term expansion of three independently noisy triangle sources. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-
Library search: the canonical DensityState supplies PSD and trace one;
Mathlib supplies tensor positivity and trace identities. No existing owner
combines three bipartite density states with triangle incident-wire routing
and independent source noise. The missing inference is the normalized Born
distribution and its sourcewise multiaffine, rather than global, noise law.
admission_basis: escape-witness
triangle_noise_distribution: proof_shape: content; escape_witness: the routed
six-wire Born contraction is expanded with three independently varied sources.
The private lemmas below are consumed on this theorem's live proof path.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise

open D5.S3.Quantum.Foundation.FiniteStateChannel
open scoped CStarAlgebra ComplexOrder MatrixOrder Kronecker

/-- A local finite POVM on the two incident systems of a triangle node. -/
structure LocalPOVM (h o : Type*) [Fintype h] [DecidableEq h] [Fintype o] where
  effect : o → Matrix h h ℂ
  positive : ∀ a, (effect a).PosSemidef
  complete : ∑ a, effect a = 1

/-- The actual matrix of a canonical finite density state. -/
def stateMatrix {h : Type*} [Fintype h] [DecidableEq h]
    (rho : DensityState h) : Matrix h h ℂ :=
  CStarMatrix.ofMatrix.symm rho.val

/-- One independently depolarized/replaced bipartite source. The background
is an actual density state; it need not be maximally mixed or separable. -/
def sourceNoise {h : Type*} [Fintype h] [DecidableEq h]
    (rho sigma : DensityState h) (w : ℝ) : Matrix h h ℂ :=
  w • stateMatrix rho + (1 - w) • stateMatrix sigma

/-- Source order: AB, BC, CA. Party order: A=(AB,CA), B=(BC,AB), C=(CA,BC).
Every source contributes exactly one wire to each of its incident parties. -/
def incidentWires (a b b' c c' a' : Type*) :
    ((a × b) × ((b' × c) × (c' × a'))) ≃
      ((a × a') × ((b' × b) × (c' × c))) where
  toFun x := ((x.1.1, x.2.2.2), ((x.2.1.1, x.1.2), (x.2.2.1, x.2.1.2)))
  invFun x := ((x.1.1, x.2.1.2), ((x.2.1.1, x.2.2.2), (x.2.2.1, x.1.2)))
  left_inv x := by rcases x with ⟨⟨a, b⟩, ⟨⟨b', c⟩, ⟨c', a'⟩⟩⟩; rfl
  right_inv x := by rcases x with ⟨⟨a, a'⟩, ⟨⟨b, b'⟩, ⟨c, c'⟩⟩⟩; rfl

section Triangle

variable {a b b' c c' a' oa ob oc : Type*}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype b'] [DecidableEq b'] [Fintype c] [DecidableEq c]
variable [Fintype c'] [DecidableEq c'] [Fintype a'] [DecidableEq a']
variable [Fintype oa] [Fintype ob] [Fintype oc]

/-- The tensor product of three independent bipartite source states. -/
def independentSources (ab : Matrix (a × b) (a × b) ℂ)
    (bc : Matrix (b' × c) (b' × c) ℂ) (ca : Matrix (c' × a') (c' × a') ℂ) :=
  ab ⊗ₖ (bc ⊗ₖ ca)

/-- A joint local outcome effect expressed in source wire order. -/
def outcomeEffect (ma : LocalPOVM (a × a') oa) (mb : LocalPOVM (b' × b) ob)
    (mc : LocalPOVM (c' × c) oc) (x : oa) (y : ob) (z : oc) :=
  (ma.effect x ⊗ₖ (mb.effect y ⊗ₖ mc.effect z)).submatrix
    (incidentWires a b b' c c' a') (incidentWires a b b' c c' a')

/-- Actual Born probability for three independent sources and local joint
measurements. Taking real part is justified by the positivity proof below. -/
def triangleBorn (ab : Matrix (a × b) (a × b) ℂ)
    (bc : Matrix (b' × c) (b' × c) ℂ) (ca : Matrix (c' × a') (c' × a') ℂ)
    (ma : LocalPOVM (a × a') oa) (mb : LocalPOVM (b' × b) ob)
    (mc : LocalPOVM (c' × c) oc) (x : oa) (y : ob) (z : oc) : ℝ :=
  (Matrix.trace (independentSources ab bc ca * outcomeEffect ma mb mc x y z)).re

/-- Sourcewise physical noise: each of the three bipartite density matrices
is mixed before taking their tensor product and the Born rule. -/
def noisyTriangle (ab0 ab1 : DensityState (a × b))
    (bc0 bc1 : DensityState (b' × c)) (ca0 ca1 : DensityState (c' × a'))
    (ma : LocalPOVM (a × a') oa) (mb : LocalPOVM (b' × b) ob)
    (mc : LocalPOVM (c' × c) oc) (wa wb wc : ℝ) (x : oa) (y : ob) (z : oc) : ℝ :=
  triangleBorn (sourceNoise ab1 ab0 wa) (sourceNoise bc1 bc0 wb)
    (sourceNoise ca1 ca0 wc) ma mb mc x y z

/-- Weight of selecting signal (`true`) or background (`false`) on one edge. -/
def sourceWeight (w : ℝ) (signal : Bool) : ℝ := if signal then w else 1 - w

private theorem state_positive {h : Type*} [Fintype h] [DecidableEq h]
    (rho : DensityState h) : (stateMatrix rho).PosSemidef := by
  exact Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.nonnegative)

private theorem state_trace {h : Type*} [Fintype h] [DecidableEq h]
    (rho : DensityState h) : Matrix.trace (stateMatrix rho) = 1 := rho.trace_eq_one

private theorem noise_positive {h : Type*} [Fintype h] [DecidableEq h]
    (rho sigma : DensityState h) (w : ℝ) (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    (sourceNoise rho sigma w).PosSemidef :=
  ((state_positive rho).smul hw.1).add
    ((state_positive sigma).smul (sub_nonneg.mpr hw.2))

private theorem noise_trace {h : Type*} [Fintype h] [DecidableEq h]
    (rho sigma : DensityState h) (w : ℝ) : Matrix.trace (sourceNoise rho sigma w) = 1 := by
  simp only [sourceNoise, Matrix.trace_add, Matrix.trace_smul, state_trace]
  simp [Complex.real_smul, Complex.ofReal_sub]

private theorem born_nonnegative {h : Type*} [Fintype h] [DecidableEq h]
    (rho e : Matrix h h ℂ) (hrho : rho.PosSemidef) (he : e.PosSemidef) :
    0 ≤ (Matrix.trace (rho * e)).re := by
  obtain ⟨q, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp he.nonneg
  have hp := (hrho.mul_mul_conjTranspose_same q).trace_nonneg
  have ht : Matrix.trace (q * rho * star q) = Matrix.trace (rho * (star q * q)) := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  have hnonneg : (0 : ℂ) ≤ Matrix.trace (rho * (star q * q)) := by
    rw [← ht]
    simpa only [Matrix.star_eq_conjTranspose] using hp
  exact (Complex.nonneg_iff.mp hnonneg).1

private theorem outcome_positive (ma : LocalPOVM (a × a') oa)
    (mb : LocalPOVM (b' × b) ob) (mc : LocalPOVM (c' × c) oc)
    (x : oa) (y : ob) (z : oc) : (outcomeEffect ma mb mc x y z).PosSemidef :=
  ((ma.positive x).kronecker ((mb.positive y).kronecker (mc.positive z))).submatrix _

set_option backward.isDefEq.respectTransparency false in
private theorem outcome_complete (ma : LocalPOVM (a × a') oa)
    (mb : LocalPOVM (b' × b) ob) (mc : LocalPOVM (c' × c) oc) :
    ∑ x, ∑ y, ∑ z, outcomeEffect ma mb mc x y z = 1 := by
  ext i j
  simp only [Matrix.sum_apply]
  let e := incidentWires a b b' c c' a'
  change (∑ x, ∑ y, ∑ z, ma.effect x (e i).1 (e j).1 *
    (mb.effect y (e i).2.1 (e j).2.1 * mc.effect z (e i).2.2 (e j).2.2)) =
      (1 : Matrix _ _ ℂ) i j
  have ha := congrArg (fun m : Matrix (a × a') (a × a') ℂ => m (e i).1 (e j).1)
    ma.complete
  have hb := congrArg (fun m : Matrix (b' × b) (b' × b) ℂ => m (e i).2.1 (e j).2.1)
    mb.complete
  have hc := congrArg (fun m : Matrix (c' × c) (c' × c) ℂ => m (e i).2.2 (e j).2.2)
    mc.complete
  simp only [Matrix.sum_apply] at ha hb hc
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [ha, hb, hc]
  simp [e, incidentWires, Matrix.one_apply, Prod.ext_iff,
    and_left_comm, and_assoc, and_comm]
  split_ifs <;> simp_all

private theorem born_normalized (ab : Matrix (a × b) (a × b) ℂ)
    (bc : Matrix (b' × c) (b' × c) ℂ) (ca : Matrix (c' × a') (c' × a') ℂ)
    (hab : Matrix.trace ab = 1) (hbc : Matrix.trace bc = 1)
    (hca : Matrix.trace ca = 1) (ma : LocalPOVM (a × a') oa)
    (mb : LocalPOVM (b' × b) ob) (mc : LocalPOVM (c' × c) oc) :
    ∑ x, ∑ y, ∑ z, triangleBorn ab bc ca ma mb mc x y z = 1 := by
  simp only [triangleBorn, ← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum]
  rw [outcome_complete, Matrix.mul_one]
  simp [independentSources, Matrix.trace_kronecker, hab, hbc, hca]

private theorem born_multiaffine (ab0 ab1 : DensityState (a × b))
    (bc0 bc1 : DensityState (b' × c)) (ca0 ca1 : DensityState (c' × a'))
    (ma : LocalPOVM (a × a') oa) (mb : LocalPOVM (b' × b) ob)
    (mc : LocalPOVM (c' × c) oc) (wa wb wc : ℝ) (x : oa) (y : ob) (z : oc) :
    noisyTriangle ab0 ab1 bc0 bc1 ca0 ca1 ma mb mc wa wb wc x y z =
      ∑ i : Bool, ∑ j : Bool, ∑ k : Bool,
        (sourceWeight wa i * sourceWeight wb j * sourceWeight wc k) *
          triangleBorn (stateMatrix (if i then ab1 else ab0))
            (stateMatrix (if j then bc1 else bc0))
            (stateMatrix (if k then ca1 else ca0)) ma mb mc x y z := by
  simp only [noisyTriangle, triangleBorn, independentSources, sourceNoise,
    Matrix.add_kronecker, Matrix.kronecker_add, Matrix.smul_kronecker,
    Matrix.kronecker_smul, smul_smul, Matrix.add_mul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re,
    Fintype.sum_bool, sourceWeight, Bool.false_eq_true, ↓reduceIte, smul_eq_mul]
  ring

/-- Three independently noisy quantum sources produce a normalized positive
Born distribution, with the exact eight endpoint weights. The input consists
of six actual density states and three local POVMs, not eight arbitrary tables. -/
theorem triangle_noise_distribution (ab0 ab1 : DensityState (a × b))
    (bc0 bc1 : DensityState (b' × c)) (ca0 ca1 : DensityState (c' × a'))
    (ma : LocalPOVM (a × a') oa) (mb : LocalPOVM (b' × b) ob)
    (mc : LocalPOVM (c' × c) oc) (wa wb wc : ℝ)
    (ha : wa ∈ Set.Icc (0 : ℝ) 1) (hb : wb ∈ Set.Icc (0 : ℝ) 1)
    (hc : wc ∈ Set.Icc (0 : ℝ) 1) :
    (∀ x y z, 0 ≤ noisyTriangle ab0 ab1 bc0 bc1 ca0 ca1 ma mb mc wa wb wc x y z) ∧
    (∑ x, ∑ y, ∑ z, noisyTriangle ab0 ab1 bc0 bc1 ca0 ca1 ma mb mc wa wb wc x y z = 1) ∧
    (∀ x y z, noisyTriangle ab0 ab1 bc0 bc1 ca0 ca1 ma mb mc wa wb wc x y z =
      ∑ i : Bool, ∑ j : Bool, ∑ k : Bool,
        (sourceWeight wa i * sourceWeight wb j * sourceWeight wc k) *
          triangleBorn (stateMatrix (if i then ab1 else ab0))
            (stateMatrix (if j then bc1 else bc0))
            (stateMatrix (if k then ca1 else ca0)) ma mb mc x y z) := by
  refine ⟨?_, ?_, born_multiaffine ab0 ab1 bc0 bc1 ca0 ca1 ma mb mc wa wb wc⟩
  · intro x y z
    exact born_nonnegative _ _
      ((noise_positive ab1 ab0 wa ha).kronecker
        ((noise_positive bc1 bc0 wb hb).kronecker (noise_positive ca1 ca0 wc hc)))
      (outcome_positive ma mb mc x y z)
  · exact born_normalized _ _ _ (noise_trace ab1 ab0 wa) (noise_trace bc1 bc0 wb)
      (noise_trace ca1 ca0 wc) ma mb mc

end Triangle

end D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise
