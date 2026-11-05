/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coherent polynomial symbols of actual Bose-supported tensor operators. -/

import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDPS
import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad

/-! Coherent symbols use actual computational tensor entries. The separation
argument is the finite polynomial spanning step needed by GNP, Theorem 8.9. -/

open scoped BigOperators
open MvPolynomial Matrix

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseCoherentSymbol

noncomputable section
set_option backward.isDefEq.respectTransparency false

private def cartesian {L : Type*} : L ⊕ L → MvPolynomial (L ⊕ L) ℂ :=
  Sum.elim (fun i => X (Sum.inl i) - C Complex.I * X (Sum.inr i))
    (fun i => X (Sum.inl i) + C Complex.I * X (Sum.inr i))

private def inverseCartesian {L : Type*} : L ⊕ L → MvPolynomial (L ⊕ L) ℂ :=
  Sum.elim (fun i => C (1/2 : ℂ) * (X (Sum.inl i) + X (Sum.inr i)))
    (fun i => C (-Complex.I/2) * (X (Sum.inr i) - X (Sum.inl i)))

private lemma cartesian_inverse {L : Type*} (p : MvPolynomial (L ⊕ L) ℂ) :
    bind₁ inverseCartesian (bind₁ cartesian p) = p := by
  rw [bind₁_bind₁]
  have he : (fun i : L ⊕ L => bind₁ inverseCartesian (cartesian i)) = X := by
    funext i
    cases i with
    | inl i =>
      apply MvPolynomial.funext
      intro z
      simp [cartesian,inverseCartesian]
      ring_nf
      simp [Complex.I_sq] <;> ring
    | inr i =>
      apply MvPolynomial.funext
      intro z
      simp [cartesian,inverseCartesian]
      ring_nf
      simp [Complex.I_sq] <;> ring
  rw [he,bind₁_X_left]
  rfl

/-- A polynomial in independent conjugate and ordinary complex coordinates is
zero if it vanishes on every actual conjugation graph. There is no assumed
coherent-vector spanning hypothesis. -/
private theorem eq_zero_of_eval_conjugate {L : Type*}
    (p : MvPolynomial (L ⊕ L) ℂ)
    (hp : ∀ z : L → ℂ, eval (Sum.elim (fun i => star (z i)) z) p = 0) : p = 0 := by
  have hreal : bind₁ cartesian p = 0 := by
    apply MvPolynomial.funext_set (fun _ => Set.range Complex.ofReal)
      (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
    intro x hx
    have hxreal (i : L ⊕ L) : star (x i) = x i := by
      obtain ⟨a,ha⟩ := hx i (Set.mem_univ i)
      rw [← ha]
      exact Complex.conj_ofReal a
    let z (i : L) := x (Sum.inl i) + Complex.I * x (Sum.inr i)
    have he : (fun i => eval x (cartesian i)) = Sum.elim (fun i => star (z i)) z := by
      funext i
      cases i with
      | inl i => simp [cartesian,z,star_add,star_mul,hxreal]; ring
      | inr i => simp [cartesian,z]
    change eval₂Hom (RingHom.id ℂ) x (bind₁ cartesian p) = _
    rw [eval₂Hom_bind₁]
    change eval (fun i => eval x (cartesian i)) p = _
    rw [he,hp]
    simp
  have h := congrArg (bind₁ inverseCartesian) hreal
  simpa only [cartesian_inverse,map_zero] using h

#print axioms eq_zero_of_eval_conjugate

open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl
open private columns_of_support from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDPS

variable {r n : ℕ}

private def exponent (x y : Fin r → Fin n) : Fin n ⊕ Fin n →₀ ℕ :=
  Finsupp.sumElim (occupation x).toFinsupp (occupation y).toFinsupp

private lemma exponent_eq_iff (x y u v : Fin r → Fin n) :
    exponent x y = exponent u v ↔ occupation x = occupation u ∧ occupation y = occupation v := by
  constructor
  · intro h
    constructor
    · apply Multiset.toFinsupp.injective
      ext i
      exact congrArg (fun a => a (Sum.inl i)) h
    · apply Multiset.toFinsupp.injective
      ext i
      exact congrArg (fun a => a (Sum.inr i)) h
  · rintro ⟨hx,hy⟩
    simp only [exponent,hx,hy]

/-- The bihomogeneous polynomial of the original computational tensor entries. -/
def symbol (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) :
    MvPolynomial (Fin n ⊕ Fin n) ℂ :=
  ∑ x, ∑ y, monomial (exponent x y) (E x y)

private lemma occupation_product (u : Fin n → ℂ) (x : Fin r → Fin n) :
    (occupation x).toFinsupp.prod (fun a k => u a ^ k) = tensorPhase u x := by
  have he := Finsupp.prod_toMultiset ((occupation x).toFinsupp.mapDomain u)
  rw [← Finsupp.toMultiset_map] at he
  rw [Multiset.toFinsupp_toMultiset] at he
  rw [Finsupp.prod_mapDomain_index] at he
  · exact he.symm.trans (by simp [tensorPhase,occupation,List.map_ofFn,List.prod_ofFn])
  · intro a
    exact pow_zero _
  · intro a i j
    exact pow_add _ _ _

/-- Evaluation on (conjugate z,z) is exactly the actual coherent quadratic form. -/
theorem eval_symbol (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) (z : Fin n → ℂ) :
    eval (Sum.elim (fun i => star (z i)) z) (symbol E) =
      star (tensorPhase z) ⬝ᵥ (E *ᵥ tensorPhase z) := by
  simp only [symbol,map_sum,eval_monomial,exponent,Finsupp.prod_sumElim]
  change (∑ x, ∑ y, E x y *
    (((occupation x).toFinsupp.prod fun a k => star (z a) ^ k) *
      ((occupation y).toFinsupp.prod fun a k => z a ^ k))) = _
  simp_rw [occupation_product]
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,Pi.star_apply,tensorPhase,star_prod]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

private lemma entry_occupation_constant
    (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) (hE : E.IsHermitian)
    (hs : P (Fin r) (Fin n) * E * P (Fin r) (Fin n) = E)
    (x y u v : Fin r → Fin n) (hx : occupation x = occupation u)
    (hy : occupation y = occupation v) : E x y = E u v := by
  calc
    E x y = E u y := symmetric_occupation_constant _ (columns_of_support E hs y) _ _ hx
    _ = star (E y u) := (hE.apply u y).symm
    _ = star (E v u) := congrArg star
      (symmetric_occupation_constant _ (columns_of_support E hs u) _ _ hy)
    _ = E u v := hE.apply u v

private lemma symbol_coeff
    (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) (hE : E.IsHermitian)
    (hs : P (Fin r) (Fin n) * E * P (Fin r) (Fin n) = E)
    (x y : Fin r → Fin n) :
    (symbol E).coeff (exponent x y) =
      (multiplicity r (occupation x) : ℂ) * (multiplicity r (occupation y) : ℂ) * E x y := by
  simp only [symbol,coeff_sum,coeff_monomial,exponent_eq_iff]
  have he (u v : Fin r → Fin n) :
      (if occupation u = occupation x ∧ occupation v = occupation y then E u v else 0) =
      if occupation u = occupation x ∧ occupation v = occupation y then E x y else 0 := by
    split_ifs with h
    · exact entry_occupation_constant E hE hs u v x y h.1 h.2
    · rfl
  simp_rw [he,ite_and]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp_rw [← Finset.sum_filter]
  simp [OccupancyWordSectors.multiplicity,sectorWords,nsmul_eq_mul,mul_assoc]

/-- Actual coherent evaluations separate Hermitian operators supported on the
full symmetric tensor subspace. This supplies the spanning step in the GNP
argument without assuming it as a premise. -/
theorem eq_zero_of_coherent
    (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) (hE : E.IsHermitian)
    (hs : P (Fin r) (Fin n) * E * P (Fin r) (Fin n) = E)
    (hz : ∀ z : Fin n → ℂ, star (tensorPhase z) ⬝ᵥ (E *ᵥ tensorPhase z) = 0) : E = 0 := by
  have hp : symbol E = 0 := eq_zero_of_eval_conjugate _ (fun z => by rw [eval_symbol,hz])
  ext x y
  have hc := congrArg (fun p : MvPolynomial (Fin n ⊕ Fin n) ℂ => p.coeff (exponent x y)) hp
  rw [symbol_coeff E hE hs] at hc
  have hx : (multiplicity r (occupation x) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (multiplicity_pos _ (occupation_card x)).ne'
  have hy : (multiplicity r (occupation y) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (multiplicity_pos _ (occupation_card y)).ne'
  exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero hx hy)

#print axioms eval_symbol
#print axioms eq_zero_of_coherent

end
end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseCoherentSymbol
