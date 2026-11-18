/- GID: D5/S3/VertexAlgebra/TwistedGround/SignedFinite/TInverse
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/SignedFinite/TInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scaled finite h/h2 stencils invert every actual signed Gaussian denominator. -/
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.Tables

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.VertexAlgebra.TwistedGround.SignedFinite
open OriginalGaussianFiniteCandidateModes

def stencil (c α β δ : ℂ) (a : ℕ → ℕ → ℂ) (p q : ℕ) : ℂ :=
  c*a p q - α*shift 1 0 a p q - β*shift 0 1 a p q + δ*shift 1 1 a p q

theorem stencil_unique {c α β δ : ℂ} (hc : c ≠ 0) {a b : ℕ → ℕ → ℂ}
    (he : stencil c α β δ a = stencil c α β δ b) : a = b := by
  have hpq : ∀ p q, a p q = b p q := by
    intro p
    induction p with
    | zero =>
      intro q
      induction q with
      | zero =>
        have hh := congrFun (congrFun he 0) 0
        simpa [stencil, shift, hc] using hh
      | succ q ih =>
        have hh := congrFun (congrFun he 0) (q+1)
        simp [stencil, shift, ih, hc] at hh
        exact hh
    | succ p ihp =>
      intro q
      induction q with
      | zero =>
        have hh := congrFun (congrFun he (p+1)) 0
        simp [stencil, shift, ihp, hc] at hh
        exact hh
      | succ q ihq =>
        have hh := congrFun (congrFun he (p+1)) (q+1)
        simp only [stencil, shift] at hh
        simp [ihp, ihq] at hh
        exact hh.resolve_right hc
  exact funext (fun p => funext (hpq p))

theorem mulPoly_ePolynomial (e f : Bool) (r : ℂ) (a : ℕ → ℕ → ℂ) :
    mulPoly (ePolynomial e f r) a =
      stencil (tConstant e f r) (tAlpha e f r) (tBeta e f r) (tDelta e f r) a := by
  funext p q
  cases p <;> cases q <;>
    norm_num [mulPoly, ePolynomial, Fin.sum_univ_succ, stencil, shift] <;> ring

private lemma scaled_stencil (F : ℕ → ℕ → ℂ → ℂ) (s c x y δ : ℂ)
    (hc : c ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (p q : ℕ) :
    stencil c (c*x) (c*y) δ (fun i j => s*x^i*y^j*F i j (1-δ/(c*x*y))) p q =
      c*s*x^p*y^q * denominatorStencil F p q (1-δ/(c*x*y)) := by
  cases p <;> cases q <;>
    simp [stencil, shift, denominatorStencil, shiftX, shiftY, shift11, pow_succ] <;>
    field_simp [hc, hx, hy] <;> ring

private lemma signed_constants (e f : Bool) {r : ℂ} (hr : ‖r‖ < 1) :
    tConstant e f r ≠ 0 ∧ tAlpha e f r ≠ 0 ∧ tBeta e f r ≠ 0 := by
  cases e <;> cases f <;> simp [tConstant, tAlpha, tBeta, A_ne_zero hr]

private lemma H_eq_scaled (square e f : Bool) {r : ℂ} (hr : ‖r‖ < 1) :
    H square e f r = fun p q =>
      (tConstant e f r)⁻¹ ^ (if square then 2 else 1) *
        (tAlpha e f r / tConstant e f r)^p * (tBeta e f r / tConstant e f r)^q *
        (if square then h2 p q (1-tDelta e f r /
          (tConstant e f r*(tAlpha e f r/tConstant e f r)*(tBeta e f r/tConstant e f r)))
        else h p q (1-tDelta e f r /
          (tConstant e f r*(tAlpha e f r/tConstant e f r)*(tBeta e f r/tConstant e f r)))) := by
  have hh := signed_constants e f hr
  have ht : (tAlpha e f r*tBeta e f r-tConstant e f r*tDelta e f r)/(tAlpha e f r*tBeta e f r) =
      1-tDelta e f r/(tConstant e f r*(tAlpha e f r/tConstant e f r)*(tBeta e f r/tConstant e f r)) := by
    field_simp [hh.1, hh.2.1, hh.2.2]
    <;> ring
  funext p q
  simp only [H, ht]

theorem H_stencils (e f : Bool) {r : ℂ} (hr : ‖r‖ < 1) :
    mulPoly (ePolynomial e f r) (H false e f r) = atom 0 0 1 ∧
    mulPoly (ePolynomial e f r) (H true e f r) = H false e f r := by
  have hh := signed_constants e f hr
  have hx : tAlpha e f r / tConstant e f r ≠ 0 := div_ne_zero hh.2.1 hh.1
  have hy : tBeta e f r / tConstant e f r ≠ 0 := div_ne_zero hh.2.2 hh.1
  have ha : tConstant e f r * (tAlpha e f r/tConstant e f r) = tAlpha e f r := by
    field_simp [hh.1]
  have hb : tConstant e f r * (tBeta e f r/tConstant e f r) = tBeta e f r := by
    field_simp [hh.1]
  constructor
  · rw [mulPoly_ePolynomial, H_eq_scaled false e f hr]
    simp only [Bool.false_eq_true, ite_false, pow_one]
    funext p q
    have hs := scaled_stencil h (tConstant e f r)⁻¹ (tConstant e f r)
      (tAlpha e f r/tConstant e f r) (tBeta e f r/tConstant e f r) (tDelta e f r)
      hh.1 hx hy p q
    conv at hs => lhs; arg 2; rw [ha]
    conv at hs => lhs; arg 3; rw [hb]
    rw [hs, h_inverse_stencil]
    by_cases hpq : p = 0 ∧ q = 0
    · rcases hpq with ⟨rfl,rfl⟩; simp [atom, hh.1]
    · simp [atom, hpq]
  · rw [mulPoly_ePolynomial, H_eq_scaled true e f hr, H_eq_scaled false e f hr]
    simp only [Bool.false_eq_true, ite_false, ite_true, pow_one]
    funext p q
    have hs := scaled_stencil h2 ((tConstant e f r)⁻¹^2) (tConstant e f r)
      (tAlpha e f r/tConstant e f r) (tBeta e f r/tConstant e f r) (tDelta e f r)
      hh.1 hx hy p q
    conv at hs => lhs; arg 2; rw [ha]
    conv at hs => lhs; arg 3; rw [hb]
    rw [hs, h2_inverse_stencil]
    field_simp
    <;> ring

end D5.S3.VertexAlgebra.TwistedGround.SignedFinite
