/- GID: D5/S3/VertexAlgebra/TwistedGround/SignedFinite/FiniteInverse
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/SignedFinite/FiniteInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite convolution cancels the squared signed polynomial stencil. -/
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.TInverse

noncomputable section
namespace D5.S3.VertexAlgebra.TwistedGround.SignedFinite

theorem conv_sub (a b c : ℕ → ℕ → ℂ) :
    conv (fun p q => a p q-b p q) c = fun p q => conv a c p q-conv b c p q := by
  funext p q
  simp [conv, sub_mul, Finset.sum_sub_distrib]

private def polynomial (c α β δ : ℂ) : ℕ → ℕ → ℂ :=
  fun p q => c*atom 0 0 1 p q - α*atom 1 0 1 p q - β*atom 0 1 1 p q + δ*atom 1 1 1 p q

private theorem polynomial_conv (c α β δ : ℂ) (a : ℕ → ℕ → ℂ) :
    conv (polynomial c α β δ) a = stencil c α β δ a := by
  unfold polynomial
  rw [conv_add, conv_sub, conv_sub, conv_scale, conv_scale, conv_scale, conv_scale]
  simp only [conv_atom]
  funext p q
  simp [stencil, shift]

theorem stencil_conv (c α β δ : ℂ) (a b : ℕ → ℕ → ℂ) :
    stencil c α β δ (conv a b) = conv (stencil c α β δ a) b := by
  rw [← polynomial_conv, ← polynomial_conv, conv_assoc]

theorem mulPoly_e_conv (e f : Bool) (r : ℂ) (a b : ℕ → ℕ → ℂ) :
    mulPoly (ePolynomial e f r) (conv a b) = conv (mulPoly (ePolynomial e f r) a) b := by
  simp only [mulPoly_ePolynomial, stencil_conv]

theorem squared_stencil_inverse (e f : Bool) {r : ℂ} (hr : ‖r‖<1)
    (Y U : ℕ → ℕ → ℂ)
    (he : mulPoly (ePolynomial e f r) (mulPoly (ePolynomial e f r) Y) = U) :
    Y = conv (H true e f r) U := by
  have hc : tConstant e f r ≠ 0 := by
    cases e <;> cases f <;> simp [tConstant, A_ne_zero hr]
  have hH := H_stencils e f hr
  apply stencil_unique (α := tAlpha e f r) (β := tBeta e f r) (δ := tDelta e f r) hc
  apply stencil_unique (α := tAlpha e f r) (β := tBeta e f r) (δ := tDelta e f r) hc
  simp only [← mulPoly_ePolynomial]
  change mulPoly (ePolynomial e f r) (mulPoly (ePolynomial e f r) Y) =
    mulPoly (ePolynomial e f r) (mulPoly (ePolynomial e f r) (conv (H true e f r) U))
  rw [he, mulPoly_e_conv, hH.2, mulPoly_e_conv, hH.1, conv_one]

theorem conv_shift (a b : ℕ → ℕ → ℂ) (i j : ℕ) :
    conv a (shift i j b) = shift i j (conv a b) := by
  have hh (b : ℕ → ℕ → ℂ) : conv (atom i j 1) b = shift i j b := by
    simpa using conv_atom i j 1 b
  rw [← hh b, ← conv_assoc, conv_comm a (atom i j 1), conv_assoc, hh]

end D5.S3.VertexAlgebra.TwistedGround.SignedFinite
