/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseSOSCertificates
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/BoseSOSCertificates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Constructive tensor PSD cut certificates for homogeneous even SOS forms. -/

import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseCoherentSymbol

/-! The constructive certificate argument is prior Gulati--Nechita--Park,
Theorem 8.11. The polynomial hypothesis is the genuine native SOS predicate;
its actual tensor realization is constructed from occupation representatives. -/

open scoped BigOperators ComplexOrder
open MvPolynomial Matrix
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseCoherentSymbol
open D5.S3.QuadraticForms

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseSOSCertificates

noncomputable section
set_option backward.isDefEq.respectTransparency false

open private occupation_product from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseCoherentSymbol
open private homogeneous_eq_form from D5.S3.QuadraticForms.HomogeneousSOSGram

variable {n : ℕ}

private def prefixCut (a b : ℕ) : Finset (Fin (a+b)) :=
  Finset.univ.filter (fun i => i.val < a)

private lemma cutPhase_append {a b : ℕ} (u : Fin a → Fin n) (v : Fin b → Fin n)
    (z : Fin n → ℂ) :
    cutPhase (prefixCut a b) z (Fin.append u v) =
      tensorPhase (fun i => star (z i)) u * tensorPhase z v := by
  rw [cutPhase,Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp [prefixCut,Fin.append_left,Fin.is_lt]
  · apply Finset.prod_congr rfl
    intro i hi
    simp [prefixCut,Fin.append_right,Nat.not_lt.mpr (Nat.le_add_right a i.val)]

private lemma exponent_card (a : Fin n →₀ ℕ) : a.toMultiset.card = a.degree := by
  simpa only [Finsupp.degree_apply,Finsupp.sum,id_eq] using Finsupp.card_toMultiset a

private def exponentWord (a : Fin n →₀ ℕ) {d : ℕ} (ha : a.degree = d) : Fin d → Fin n :=
  representative a.toMultiset ((exponent_card a).trans ha)

private lemma exponentWord_product (a : Fin n →₀ ℕ) {d : ℕ} (ha : a.degree = d)
    (z : Fin n → ℂ) : tensorPhase z (exponentWord a ha) = a.prod (fun i k => z i ^ k) := by
  rw [← occupation_product]
  simp only [exponentWord,occupation_representative,Finsupp.toMultiset_toFinsupp]

private def certificateWord (α : Fin n →₀ ℕ) (j : ℕ)
    (β : HomogeneousSOSGram.Exponent (Fin n) j) : Fin (j+(α.degree+j)) → Fin n :=
  Fin.append (exponentWord β.val β.property)
    (exponentWord (α+β.val) (by rw [map_add,β.property]))

private lemma certificateWord_product (α : Fin n →₀ ℕ) (j : ℕ)
    (β : HomogeneousSOSGram.Exponent (Fin n) j) (z : Fin n → ℂ) :
    cutPhase (prefixCut j (α.degree+j)) z (certificateWord α j β) =
      α.prod (fun i k => z i ^ k) * β.val.prod (fun i k => (star (z i) * z i)^k) := by
  rw [certificateWord,cutPhase_append,exponentWord_product,exponentWord_product,
    Finsupp.prod_add_index' (by simp) (fun i a b => pow_add _ _ _)]
  calc
    _ = α.prod (fun i k => z i ^ k) *
        (β.val.prod (fun i k => star (z i)^k) * β.val.prod (fun i k => z i^k)) := by ring
    _ = _ := by
      simp only [Finsupp.prod,← Finset.prod_mul_distrib,← mul_pow]

private def certificateVector (α : Fin n →₀ ℕ) (j : ℕ)
    (q : MvPolynomial (Fin n) ℝ) : (Fin (j+(α.degree+j)) → Fin n) → ℂ :=
  ∑ β : HomogeneousSOSGram.Exponent (Fin n) j,
    (q.coeff β.val : ℂ) • Pi.single (certificateWord α j β) 1

private lemma certificateVector_amplitude (α : Fin n →₀ ℕ) (j : ℕ)
    (q : MvPolynomial (Fin n) ℝ) (hq : q.IsHomogeneous j) (z : Fin n → ℂ) :
    star (certificateVector α j q) ⬝ᵥ cutPhase (prefixCut j (α.degree+j)) z =
      α.prod (fun i k => z i ^ k) *
        eval₂ Complex.ofRealHom (fun i => star (z i) * z i) q := by
  have hs : star (certificateVector α j q) = certificateVector α j q := by
    simp only [certificateVector,star_sum,star_smul,Complex.star_def,Complex.conj_ofReal]
    congr 1
    ext β x
    simp [Pi.single_apply]
  rw [hs,certificateVector,sum_dotProduct]
  simp only [smul_dotProduct,smul_eq_mul,single_one_dotProduct,
    certificateWord_product]
  conv_rhs => rw [homogeneous_eq_form q j hq]
  simp only [HomogeneousSOSGram.form,eval₂_sum,eval₂_monomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  change (q.coeff β.val : ℂ) *
    (α.prod (fun i k => z i ^ k) * β.val.prod (fun i k => (star (z i) * z i)^k)) =
      α.prod (fun i k => z i ^ k) *
        ((q.coeff β.val : ℂ) * β.val.prod (fun i k => (star (z i) * z i)^k))
  ring

private lemma eval_norm_star (q : MvPolynomial (Fin n) ℝ) (z : Fin n → ℂ) :
    star (eval₂ Complex.ofRealHom (fun i => star (z i) * z i) q) =
      eval₂ Complex.ofRealHom (fun i => star (z i) * z i) q := by
  induction q using MvPolynomial.induction_on with
  | C c =>
    simp only [eval₂_C]
    exact Complex.conj_ofReal c
  | add p q hp hq => simpa only [eval₂_add,star_add] using congrArg₂ (·+·) hp hq
  | mul_X p i hp =>
    simp only [eval₂_mul,eval₂_X,star_mul,star_star,hp]
    ring

private lemma norm_monomial (α : Fin n →₀ ℕ) (z : Fin n → ℂ) :
    star (α.prod (fun i k => z i ^ k)) * α.prod (fun i k => z i ^ k) =
      α.prod (fun i k => (star (z i) * z i)^k) := by
  simp only [Finsupp.prod,star_prod,star_pow,← Finset.prod_mul_distrib,← mul_pow]

/-- Each homogeneous parity SOS term is realized by an actual rank-one PSD
operator at a genuine tensor cut. -/
theorem term_cut_certificate (r : ℕ) (α : Fin n →₀ ℕ) (j : ℕ)
    (hr : α.degree + 2*j = r) (q : MvPolynomial (Fin n) ℝ)
    (hq : q.IsHomogeneous j) :
    ∃ (S : Finset (Fin r)) (Z : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ),
      Z.PosSemidef ∧ ∀ z : Fin n → ℂ,
        star (tensorPhase z) ⬝ᵥ (partialTransposeOn S Z *ᵥ tensorPhase z) =
          eval₂ Complex.ofRealHom (fun i => star (z i) * z i)
            (monomial α 1 * (q*q)) := by
  have he : r = j+(α.degree+j) := by omega
  rw [he]
  let v := certificateVector α j q
  refine ⟨prefixCut j (α.degree+j),vecMulVec v (star v),
    Matrix.posSemidef_vecMulVec_self_star v,?_⟩
  intro z
  rw [rankOne_partialTranspose_coherent,certificateVector_amplitude α j q hq z]
  simp only [star_mul,eval_norm_star,eval₂_mul,eval₂_monomial,map_one,one_mul]
  rw [← norm_monomial]
  ring

#print axioms term_cut_certificate

/-- Every native even homogeneous SOS form has genuine PSD tensor certificates
at actual cuts. No SOS characterization of extendibility is assumed. -/
theorem even_form_cut_certificates (p : MvPolynomial (Fin n) ℝ) (r : ℕ)
    (hp : p.IsHomogeneous r) (hs : IsSumSq (expand 2 p)) :
    ∃ (m : ℕ) (S : Fin m → Finset (Fin r))
      (Z : Fin m → Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ),
      (∀ i, (Z i).PosSemidef) ∧ ∀ z : Fin n → ℂ,
        star (tensorPhase z) ⬝ᵥ ((∑ i, partialTransposeOn (S i) (Z i)) *ᵥ tensorPhase z) =
          eval₂ Complex.ofRealHom (fun i => star (z i) * z i) p := by
  obtain ⟨m,α,d,q,hq,he⟩ := (HomogeneousSOS.even_form_sos_iff p r hp).mp hs
  have hterm (i : Fin m) :
      ∃ (S : Finset (Fin r)) (Z : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ),
        Z.PosSemidef ∧ ∀ z : Fin n → ℂ,
          star (tensorPhase z) ⬝ᵥ (partialTransposeOn S Z *ᵥ tensorPhase z) =
            eval₂ Complex.ofRealHom (fun i => star (z i) * z i)
              (monomial (α i) 1 * (q i * q i)) := by
    rcases (hq i).2.2 with hz | hd
    · refine ⟨∅,0,Matrix.PosSemidef.zero,?_⟩
      intro z
      simp [hz,partialTransposeOn,Matrix.mulVec,dotProduct]
    · exact term_cut_certificate r (α i) (d i) hd (q i) (hq i).2.1
  choose S Z hZ using hterm
  refine ⟨m,S,Z,fun i => (hZ i).1,?_⟩
  intro z
  rw [he,eval₂_sum,Matrix.sum_mulVec,dotProduct_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (hZ i).2 z

#print axioms even_form_cut_certificates

end
end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseSOSCertificates
