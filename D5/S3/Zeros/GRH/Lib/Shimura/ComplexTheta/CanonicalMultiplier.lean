/- GID: D5/S3/Zeros/GRH/Lib/Shimura/ComplexTheta/CanonicalMultiplier
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/ComplexTheta/CanonicalMultiplier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.ComplexTheta.CanonicalMultiplier. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/ComplexTheta/CanonicalMultiplier.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation.LieExponential
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Frobenius' dimension formula and irreducibility of the theta group (known result; see
Lib.Shimura.ComplexTheta.ThetaDimension).

This file: Canonical semicharacter from an endomorphism b with b + b* = 1 for the Riemann form;
normalised translations and their cocycle. -/

noncomputable section


open Complex Finset
variable {V V' ι : Type} [FinComplexSpace V] [FinComplexSpace V'] (B : RealComplexForm V) (b :
  V →L[ℂ] V) {L}

/-- The canonical multiplier x ↦ exp(πi E(bx, x)) attached to a complex-linear endomorphism b of
V, where E is the Riemann form of B. -/
def canonicalMultiplier x := (Real.pi * I * B.riemannForm (b x) x).exp

/-- Normalised translation: the twisted translation by x, divided by the canonical multiplier
exp(πi E(bx, x)). -/
def normalizedShift x := (canonicalMultiplier B b x)⁻¹ • B.thetaShift x

attribute [local simp] sum_div exp_sum funext_iff thetaShift_apply exp_neg fieldEq
  canonicalMultiplier normalizedShift exp_add

/-- If the pull-backs of the forms B_i along linear maps A_i add up to B', the twisted translate
by u of the product of the f_i∘A_i is the product of the pulled-back translates of f_i by
A_i u. -/
lemma thetaShift_prod [Fintype ι] {B : ι → _} {A : ι → V' →L[ℂ] V} {f : ι → _} u : thetaShift (∑ i,
    pullForm (A i) (B i)) u (∏ i, f i ∘ A i) = ∏ i, thetaShift (B i) (A i u) (f i) ∘ A i := by simp

variable {B : LatticeForm L} {b x y f} (adj : ∀ u w, B.riemannForm (b u) w =
  B.riemannForm u w - B.riemannForm u (b w))

/-- The theta functions for L, B and the canonical multiplier of b are the entire functions
fixed by the normalised translations by the elements of L. -/
lemma mem_thetaSpace_iff_normalizedShift : f ∈ B.thetaSpace (canonicalMultiplier B b) ↔
  Differentiable ℂ f ∧ ∀ l ∈ L, normalizedShift B b l f = f := .and .rfl (by simp [mul_right_comm])

include adj

/-- If Re B is symmetric, E(bu, w) + E(u, bw) = E(u, w) for its Riemann form E, and E(bL, L) ⊂
ℤ, then L, B and the canonical multiplier of b are Appell–Humbert data. -/
lemma isAppellHumbert_canonicalMultiplier (re : ∀ u w, (B u w).re = (B w u).re) (h : ∀ᵉ (l ∈ L)
  (m ∈ L), ∃ n : ℤ, B.riemannForm (b l) m = n) : IsAppellHumbert B (canonicalMultiplier B b) := by
  simp [isAppellHumbert_iff, ← exp_add, exp_eq_exp_iff_exists_int]
  norm_cast
  grind [riemannForm_swap]

/-- The Heisenberg law: if b + b* = 1 for the Riemann form E of Appell–Humbert data, the
normalised translations Ũ (`normalizedShift`) satisfy Ũ_x Ũ_y f = exp(2πi E(bx, y))·Ũ_{x+y} f for
every function f. -/
lemma IsAppellHumbert.normalizedShift_normalizedShift {χ} (h : IsAppellHumbert B χ) :
  normalizedShift B b x (normalizedShift B b y f) =
  B.riemannPhase (b x) y • normalizedShift B b (x + y) f := by simp [riemannForm_swap y, adj y x,
  h.thetaShift_thetaShift, mul_add, sub_eq_add_neg, two_mul, add_mul]
