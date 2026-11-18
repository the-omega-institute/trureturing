/- GID: D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteEulerStencil
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteEulerStencil
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full finite Gaussian polynomial candidate satisfies its Euler stencil. -/

import D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Topology

namespace D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes


private lemma denominatorStencil_injective_zero (F : ℕ → ℕ → ℂ → ℂ) (r : ℂ)
    (hF : ∀ p q, denominatorStencil F p q r = 0) : ∀ p q, F p q r = 0 := by
  intro p
  induction p with
  | zero =>
    intro q
    induction q with
    | zero => simpa [denominatorStencil, shiftX, shiftY] using hF 0 0
    | succ q ih => simpa [denominatorStencil, shiftX, shiftY, ih] using hF 0 (q + 1)
  | succ p ih =>
    intro q
    induction q with
    | zero => simpa [denominatorStencil, shiftX, shiftY, ih] using hF (p + 1) 0
    | succ q ihq =>
      simpa [denominatorStencil, shiftX, shiftY, ih, ihq] using hF (p + 1) (q + 1)

private lemma hasDerivAt_denominatorStencil (F FPrime : ℕ → ℕ → ℂ → ℂ)
    (p q : ℕ) (r : ℂ) (hF : ∀ i j, HasDerivAt (F i j) (FPrime i j r) r) :
    HasDerivAt (denominatorStencil F p q)
      (denominatorStencil FPrime p q r - shift11 F p q r) r := by
  have hx : HasDerivAt (shiftX F p q) (shiftX FPrime p q r) r := by
    cases p <;> simp only [shiftX, Nat.succ_ne_zero, ite_true, ite_false,
      Nat.add_sub_cancel]
    · exact hasDerivAt_const r 0
    · exact hF _ _
  have hy : HasDerivAt (shiftY F p q) (shiftY FPrime p q r) r := by
    cases q <;> simp only [shiftY, Nat.succ_ne_zero, ite_true, ite_false,
      Nat.add_sub_cancel]
    · exact hasDerivAt_const r 0
    · exact hF _ _
  have hd := (((hF p q).sub hx).sub hy).add
    (((hasDerivAt_const r (1 : ℂ)).sub (hasDerivAt_id r)).mul
      (hasDerivAt_shift11 F FPrime p q r hF))
  convert! hd using 1 <;> simp only [denominatorStencil, Pi.sub_apply, id_eq] <;> ring

private def doubleDenominator (F : ℕ → ℕ → ℂ → ℂ) :=
  denominatorStencil (denominatorStencil F)

private def certificateW (A : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ) : ℂ :=
  r / 2 * (denominatorStencil A p q r +
    (1-r) * shift11 (denominatorStencil A) p q r) + r^2 * shift11 A p q r

private def certificateWPrime (A AP : ℕ → ℕ → ℂ → ℂ)
    (p q : ℕ) (r : ℂ) : ℂ :=
  (1/2 : ℂ) * (denominatorStencil A p q r +
    (1-r) * shift11 (denominatorStencil A) p q r) +
  r / 2 * (denominatorStencil AP p q r - shift11 A p q r -
    shift11 (denominatorStencil A) p q r +
    (1-r) * shift11 (fun i j u => denominatorStencil AP i j u - shift11 A i j u) p q r) +
  2*r*shift11 A p q r + r^2 * shift11 AP p q r

private lemma hasDerivAt_certificateW (A AP : ℕ → ℕ → ℂ → ℂ)
    (p q : ℕ) (r : ℂ) (hA : ∀ i j, HasDerivAt (A i j) (AP i j r) r) :
    HasDerivAt (certificateW A p q) (certificateWPrime A AP p q r) r := by
  have he := fun i j => hasDerivAt_denominatorStencil A AP i j r hA
  have hz := hasDerivAt_shift11 A AP p q r hA
  have hze := hasDerivAt_shift11 (denominatorStencil A)
    (fun i j u => denominatorStencil AP i j u - shift11 A i j u) p q r he
  have hd := (((hasDerivAt_id r).div_const 2).mul
    ((he p q).add (((hasDerivAt_const r (1 : ℂ)).sub (hasDerivAt_id r)).mul hze))).add
    ((hasDerivAt_pow 2 r).mul hz)
  convert hd using 1
  · rfl
  · dsimp [certificateWPrime]
    ring

private lemma P_double_denominator (p q : ℕ) (r : ℂ) :
    doubleDenominator P p q r = certificateW (fun i j u => a i u * a j u) p q r := by
  have hp : denominatorStencil P = fun i j u =>
      u/2 * (a i u*a j u + (1-u)*shift11 (fun i j u => a i u*a j u) i j u) +
      u^2 * shift11 L_h i j u :=
    funext fun i => funext fun j => funext fun u => P_inverse_stencil i j u
  unfold doubleDenominator
  rw [hp, denominatorStencil_linear]
  have hlin := denominatorStencil_linear (fun i j u => a i u*a j u)
    (shift11 (fun i j u => a i u*a j u)) (fun _ => 1) (fun u => 1-u) p q r
  simp only [one_mul] at hlin
  rw [hlin, denominatorStencil_shift11, denominatorStencil_shift11]
  have hg : denominatorStencil L_h = fun i j u => a i u*a j u :=
    funext fun i => funext fun j => funext fun u => L_h_inverse_stencil i j u
  rw [hg]
  rfl


private def certificateThetaW (A U : ℕ → ℕ → ℂ → ℂ)
    (p q : ℕ) (r : ℂ) : ℂ :=
  r/2 * (denominatorStencil A p q r + (1-r)*shift11 (denominatorStencil A) p q r) +
  r/2 * (denominatorStencil U p q r - r*shift11 A p q r -
    r*shift11 (denominatorStencil A) p q r +
    (1-r)*shift11 (fun i j u => denominatorStencil U i j u - u*shift11 A i j u) p q r) +
  2*r^2*shift11 A p q r + r^2*shift11 U p q r

private def certificateM (F : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ) : ℂ :=
  denominatorStencil F p q r - 2*shiftX (denominatorStencil F) p q r +
  (1-r)*shiftX (shiftX (denominatorStencil F)) p q r +
  2*r*(shiftX F p q r - shiftX (shiftX F) p q r)

private def polynomialResidual (F FP A Q : ℕ → ℕ → ℂ → ℂ)
    (p q : ℕ) (r : ℂ) : ℂ :=
  4*(r*FP p q r - (p+1/2 : ℂ)*(F p q r-shiftX F p q r)) -
    r*A p q r + 2*(1-r)*(Q p q r-shiftX Q p q r)

private lemma thetaW_eq (A AP : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ) :
    r * certificateWPrime A AP p q r =
      certificateThetaW A (fun i j u => u*AP i j u) p q r := by
  rcases p with _ | _ | p <;> rcases q with _ | _ | q <;>
    simp [certificateWPrime, certificateThetaW, denominatorStencil, shiftX, shiftY,
      shift11] <;> ring

private lemma doubleDenominator_commutator (F FP A Q : ℕ → ℕ → ℂ → ℂ)
    (p q : ℕ) (r : ℂ) :
    doubleDenominator (polynomialResidual F FP A Q) p q r =
      4*(r*(doubleDenominator FP p q r -
        2*shift11 (denominatorStencil F) p q r) -
        (p+1/2 : ℂ)*(doubleDenominator F p q r - shiftX (doubleDenominator F) p q r) -
        2*shiftX (doubleDenominator F) p q r) -
      r*doubleDenominator A p q r +
        2*(1-r)*doubleDenominator (fun i j u => Q i j u-shiftX Q i j u) p q r := by
  rcases p with _ | _ | _ | p <;> rcases q with _ | _ | q <;>
    simp [doubleDenominator, polynomialResidual, denominatorStencil, shiftX, shiftY,
      shift11, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] <;> ring

private lemma residual_finite_certificate (A Q : ℕ → ℕ → ℂ → ℂ)
    (p q : ℕ) (r : ℂ) :
    4*(certificateThetaW A (fun i j u =>
        (i : ℂ)*(A i j u-shiftX A i j u)+Q i j u) p q r -
      (p+1/2 : ℂ)*(certificateW A p q r-shiftX (certificateW A) p q r) -
      2*shiftX (certificateW A) p q r) - r*doubleDenominator A p q r +
      2*(1-r)*doubleDenominator (fun i j u => Q i j u-shiftX Q i j u) p q r =
    certificateM (fun i j u => 2*(Q i j u-(1-u)*shiftY Q i j u) +
      u*shiftY A i j u) p q r := by
  rcases p with _ | _ | _ | p <;> rcases q with _ | _ | q <;>
    simp [certificateThetaW, certificateW, certificateM, doubleDenominator,
      denominatorStencil, shiftX, shiftY, shift11, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel] <;> ring


private lemma hasDerivAt_doubleDenominator (F FP : ℕ → ℕ → ℂ → ℂ)
    (p q : ℕ) (r : ℂ) (hF : ∀ i j, HasDerivAt (F i j) (FP i j r) r) :
    HasDerivAt (doubleDenominator F p q)
      (doubleDenominator FP p q r - 2*shift11 (denominatorStencil F) p q r) r := by
  have hd := hasDerivAt_denominatorStencil (denominatorStencil F)
    (fun i j u => denominatorStencil FP i j u-shift11 F i j u) p q r
    (fun i j => hasDerivAt_denominatorStencil F FP i j r hF)
  convert! hd using 1 <;>
    rcases p with _ | _ | p <;> rcases q with _ | _ | q <;>
      simp [doubleDenominator, denominatorStencil, shiftX, shiftY, shift11] <;> ring

private def sourceProduct (p q : ℕ) (r : ℂ) := a p r*a q r
private def sourceThetaProduct (p q : ℕ) (r : ℂ) := a p r*(r*aPrime q r)
private def sourceProductPrime (p q : ℕ) (r : ℂ) :=
  aPrime p r*a q r+a p r*aPrime q r

private lemma sourceProduct_euler (p q : ℕ) (r : ℂ) :
    r*sourceProductPrime p q r =
      (p : ℂ)*(sourceProduct p q r-shiftX sourceProduct p q r)+
        sourceThetaProduct p q r := by
  cases p with
  | zero => simp [sourceProductPrime, sourceProduct, sourceThetaProduct, shiftX, aPrime]; ring
  | succ p =>
    simp only [sourceProductPrime, sourceProduct, sourceThetaProduct, shiftX,
      Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    linear_combination a q r * a_euler_mode_step p r

private lemma sourceThetaProduct_step (p q : ℕ) (r : ℂ) :
    2*(sourceThetaProduct p q r-(1-r)*shiftY sourceThetaProduct p q r) +
      r*shiftY sourceProduct p q r = 0 := by
  cases q with
  | zero => simp [sourceThetaProduct, shiftY, aPrime]
  | succ q =>
    simp only [sourceThetaProduct, sourceProduct, shiftY, Nat.succ_ne_zero,
      ite_false, Nat.add_sub_cancel]
    linear_combination a p r*r * a_derivative_mode_step q r

/-- The full finite polynomial candidate satisfies the asymmetric Euler stencil,
including both zero axes and every complex parameter. The proof uses two
inverse-denominator stencils and triangular cancellation, with no division by r. -/
theorem P_euler_stencil (p q : ℕ) (r : ℂ) :
    r * PPrime p q r - (p + 1/2 : ℂ) * (P p q r - shiftX P p q r) =
      r * a p r * a q r / 4 - (1-r) *
        (a p r - (if p=0 then 0 else a (p-1) r)) * (r * aPrime q r) / 2 := by
  have hp : doubleDenominator P = certificateW sourceProduct :=
    funext fun i => funext fun j => funext fun u => P_double_denominator i j u
  have hd (i j : ℕ) :
      doubleDenominator PPrime i j r - 2*shift11 (denominatorStencil P) i j r =
        certificateWPrime sourceProduct sourceProductPrime i j r := by
    have hh := hasDerivAt_doubleDenominator P PPrime i j r (fun i j => hasDerivAt_P i j r)
    rw [hp] at hh
    exact hh.unique (hasDerivAt_certificateW sourceProduct sourceProductPrime i j r
      (fun i j => (hasDerivAt_a i r).mul (hasDerivAt_a j r)))
  have hu : (fun i j u => u*sourceProductPrime i j u) =
      (fun (i j : ℕ) (u : ℂ) => (i : ℂ)*(sourceProduct i j u-shiftX sourceProduct i j u)+
        sourceThetaProduct i j u) :=
    funext fun i => funext fun j => funext fun u => sourceProduct_euler i j u
  have hz : ∀ i j, doubleDenominator
      (polynomialResidual P PPrime sourceProduct sourceThetaProduct) i j r = 0 := by
    intro i j
    rw [doubleDenominator_commutator, hd, hp, thetaW_eq, hu,
      residual_finite_certificate]
    have hs : (fun i j u => 2*(sourceThetaProduct i j u-
        (1-u)*shiftY sourceThetaProduct i j u) + u*shiftY sourceProduct i j u) =
        (fun _ _ _ => 0) :=
      funext fun i => funext fun j => funext fun u => sourceThetaProduct_step i j u
    rw [hs]
    simp [certificateM, denominatorStencil, shiftX, shiftY, shift11]
  have hE := denominatorStencil_injective_zero
    (denominatorStencil (polynomialResidual P PPrime sourceProduct sourceThetaProduct)) r hz
  have hR := denominatorStencil_injective_zero
    (polynomialResidual P PPrime sourceProduct sourceThetaProduct) r hE p q
  cases p <;> simp only [polynomialResidual, sourceProduct, sourceThetaProduct,
    shiftX, Nat.succ_ne_zero, ite_true, ite_false, Nat.add_sub_cancel] at hR ⊢ <;>
    linear_combination hR/4

end D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes
