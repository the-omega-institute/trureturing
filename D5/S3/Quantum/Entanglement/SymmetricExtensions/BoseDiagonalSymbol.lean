/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseDiagonalSymbol
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/BoseDiagonalSymbol
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complex coherent symbols of actual occupation-diagonal operators. -/

import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseCoherentSymbol

/-! The diagonal symbol bridge is part of the operator/polynomial argument
of Gulati--Nechita--Park, Section 8. It retains the actual tensor entries. -/

open scoped BigOperators ComplexOrder
open Matrix MvPolynomial
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseCoherentSymbol

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDiagonalSymbol

noncomputable section
set_option backward.isDefEq.respectTransparency false

open private occupation_product from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseCoherentSymbol

variable {r n : ℕ}

/-- The occupation polynomial of the original tensor entries, before the
substitution of squared real coordinates. -/
def occupationForm (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ x, ∑ y, if occupation x = occupation y then
    monomial (occupation x).toFinsupp (E x y).re else 0

private lemma expand_occupationForm
    (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) :
    expand 2 (occupationForm E) = realSymbol (occupationTwirl E) := by
  simp only [occupationForm,map_sum,realSymbol]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  by_cases h : occupation x = occupation y
  · simp [h,occupationTwirl_apply,two_smul]
  · simp [h,occupationTwirl_apply]

private lemma phase_pair (z : Fin n → ℂ) (x y : Fin r → Fin n)
    (h : occupation x = occupation y) :
    star (tensorPhase z x) * tensorPhase z y =
      (((occupation x).toFinsupp.prod (fun i k => (Complex.normSq (z i))^k) : ℝ) : ℂ) := by
  rw [← occupation_product,← occupation_product,← h]
  simp only [Finsupp.prod,star_prod,star_pow,← Finset.prod_mul_distrib,← mul_pow]
  simp [Complex.normSq_eq_conj_mul_self]

private lemma eval_occupationForm
    (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) (z : Fin n → ℂ) :
    eval (fun i => Complex.normSq (z i)) (occupationForm E) =
      (star (tensorPhase z) ⬝ᵥ (occupationTwirl E *ᵥ tensorPhase z)).re := by
  simp only [occupationForm,MvPolynomial.eval_sum,dotProduct,Matrix.mulVec,
    Pi.star_apply,Finset.mul_sum,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  by_cases h : occupation x = occupation y
  · rw [if_pos h,eval_monomial,occupationTwirl_apply,if_pos h]
    rw [show star (tensorPhase z x) * (E x y * tensorPhase z y) =
      E x y * (star (tensorPhase z x) * tensorPhase z y) by ring,phase_pair z x y h]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  · simp [h,occupationTwirl_apply]

private lemma eval₂_normSq (p : MvPolynomial (Fin n) ℝ) (z : Fin n → ℂ) :
    eval₂ Complex.ofRealHom (fun i => star (z i) * z i) p =
      (eval (fun i => Complex.normSq (z i)) p : ℂ) := by
  have he := (eval₂_comp_left Complex.ofRealHom (RingHom.id ℝ)
      (fun i => Complex.normSq (z i)) p).symm
  change eval₂ Complex.ofRealHom (fun i => (Complex.normSq (z i) : ℂ)) p = _ at he
  simpa only [Complex.normSq_eq_conj_mul_self,Complex.star_def,Complex.ofRealHom_eq_coe,
    MvPolynomial.eval,MvPolynomial.coe_eval₂Hom] using he

/-- An actual occupation-diagonal Hermitian operator with the even real
symbol `p(X²)` has the complex coherent symbol `p(|z|²)` on every vector. -/
theorem coherent_of_even_realSymbol
    (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) (hE : E.IsHermitian)
    (ht : occupationTwirl E = E) (p : MvPolynomial (Fin n) ℝ)
    (hp : realSymbol E = expand 2 p) (z : Fin n → ℂ) :
    star (tensorPhase z) ⬝ᵥ (E *ᵥ tensorPhase z) =
      eval₂ Complex.ofRealHom (fun i => star (z i) * z i) p := by
  have hf : occupationForm E = p := by
    apply expand_injective (by omega : 0 < 2)
    rw [expand_occupationForm,ht,hp]
  rw [eval₂_normSq]
  apply Complex.ext
  · simpa only [ht,hf,Complex.ofReal_re] using (eval_occupationForm E z).symm
  · simpa only [Complex.ofReal_im,RCLike.im_to_complex] using
      hE.im_star_dotProduct_mulVec_self (tensorPhase z)

#print axioms coherent_of_even_realSymbol

end
end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDiagonalSymbol
