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
import D5.S3.QuadraticForms.HomogeneousSOSGram

/-! Coherent symbols use actual computational tensor entries. The separation
argument is the finite polynomial spanning step needed by GNP, Theorem 8.9. -/

open scoped BigOperators ComplexOrder MatrixOrder
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


/-- The actual signed occupation eigenvalue, without trace normalization. -/
def occupationCoefficient (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ)
    (a : Sym (Fin n) r) : ℝ :=
  (OccupancyWordSectors.multiplicity r a.val : ℝ) *
    (E (representative a.val a.property) (representative a.val a.property)).re

/-- The explicit twirl of a Hermitian Bose operator is its actual signed
occupation-projector expansion. Positivity is not needed for this equality. -/
theorem occupationTwirl_decomposition
    (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) (hE : E.IsHermitian)
    (hs : P (Fin r) (Fin n) * E * P (Fin r) (Fin n) = E) :
    occupationTwirl E = ∑ a : Sym (Fin n) r,
      occupationCoefficient E a • vecMulVec (sectorVector r a.val) (star (sectorVector r a.val)) := by
  ext x y
  simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,Pi.star_apply]
  rw [occupationTwirl_apply]
  by_cases hxy : occupation x = occupation y
  · rw [if_pos hxy]
    let a : Sym (Fin n) r := ⟨occupation x,occupation_card x⟩
    rw [Finset.sum_eq_single a]
    · have hx : x ∈ sectorWords r a.val := by simp [sectorWords,a]
      have hy : y ∈ sectorWords r a.val := by simp [sectorWords,a,hxy]
      have hm : (OccupancyWordSectors.multiplicity r a.val : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (multiplicity_pos _ a.property).ne'
      have hsqrt : (Real.sqrt (OccupancyWordSectors.multiplicity r a.val : ℝ) : ℂ) *
          (Real.sqrt (OccupancyWordSectors.multiplicity r a.val : ℝ) : ℂ) =
          (OccupancyWordSectors.multiplicity r a.val : ℂ) := by
        norm_cast
        exact Real.mul_self_sqrt (Nat.cast_nonneg _)
      let w := representative a.val a.property
      have hd : ((E w w).re : ℂ) = E w w := by
        exact (RCLike.conj_eq_iff_re (K := ℂ)).mp (hE.apply w w)
      have he : E w w = E x y := entry_occupation_constant E hE hs w w x y
        (occupation_representative _ _) ((occupation_representative _ _).trans hxy)
      simp only [sectorVector,if_pos hx,if_pos hy,star_inv₀,Complex.star_def,
        Complex.conj_ofReal,occupationCoefficient,RCLike.real_smul_eq_coe_mul,Complex.ofReal_mul,
        Complex.ofReal_natCast,← mul_inv,hsqrt]
      push_cast
      change E x y = (OccupancyWordSectors.multiplicity r a.val : ℂ) *
        ((E w w).re : ℂ) * (OccupancyWordSectors.multiplicity r a.val : ℂ)⁻¹
      rw [hd,he]
      field_simp
    · intro b hb hba
      have hxb : x ∉ sectorWords r b.val := by
        simp only [sectorWords,Finset.mem_filter,Finset.mem_univ,true_and]
        intro h
        apply hba
        apply Subtype.ext
        exact h.symm
      have hz : sectorVector r b.val x = 0 := by
        unfold sectorVector
        exact if_neg hxb
      simp only [hz,zero_mul,smul_zero]
    · simp
  · rw [if_neg hxy]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    by_cases hx : x ∈ sectorWords r a.val
    · have hy : y ∉ sectorWords r a.val := by
        intro hy
        exact hxy ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
      have hz : sectorVector r a.val y = 0 := by
        unfold sectorVector
        exact if_neg hy
      simp only [hz,star_zero,mul_zero,smul_zero]
    · have hz : sectorVector r a.val x = 0 := by
        unfold sectorVector
        exact if_neg hx
      simp only [hz,zero_mul,smul_zero]

#print axioms occupationTwirl_decomposition

section Cuts

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

open private transposed_phase from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl

private def cutSwap (S : Finset I) : ((I → L) × (I → L)) ≃ ((I → L) × (I → L)) where
  toFun p := (S.piecewise p.2 p.1,S.piecewise p.1 p.2)
  invFun p := (S.piecewise p.2 p.1,S.piecewise p.1 p.2)
  left_inv := by
    intro p
    ext i <;> by_cases h : i ∈ S <;> simp [Finset.piecewise,h]
  right_inv := by
    intro p
    ext i <;> by_cases h : i ∈ S <;> simp [Finset.piecewise,h]

/-- Actual partial transposition of a tensor operator conjugates precisely the
local coordinates in the transposed tensor factors of its coherent form. -/
theorem partialTranspose_coherent (S : Finset I)
    (E : Matrix (I → L) (I → L) ℂ) (z : L → ℂ) :
    star (tensorPhase z) ⬝ᵥ (partialTransposeOn S E *ᵥ tensorPhase z) =
      star (cutPhase S z) ⬝ᵥ (E *ᵥ cutPhase S z) := by
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,Pi.star_apply,partialTransposeOn]
  change (∑ x, ∑ y, star (tensorPhase z x) *
      (E (S.piecewise y x) (S.piecewise x y) * tensorPhase z y)) =
    ∑ x, ∑ y, star (cutPhase S z x) * (E x y * cutPhase S z y)
  suffices heq :
      (∑ p : (I → L) × (I → L), star (tensorPhase z p.1) *
        (E (S.piecewise p.2 p.1) (S.piecewise p.1 p.2) * tensorPhase z p.2)) =
      ∑ p : (I → L) × (I → L), star (cutPhase S z p.1) *
        (E p.1 p.2 * cutPhase S z p.2) by
    simpa only [Fintype.sum_prod_type] using heq
  apply Fintype.sum_equiv (cutSwap S)
  intro p
  change star (tensorPhase z p.1) *
      (E (S.piecewise p.2 p.1) (S.piecewise p.1 p.2) * tensorPhase z p.2) =
    star (cutPhase S z (S.piecewise p.2 p.1)) *
      (E (S.piecewise p.2 p.1) (S.piecewise p.1 p.2) *
        cutPhase S z (S.piecewise p.1 p.2))
  have he := transposed_phase S z (S.piecewise p.1 p.2) (S.piecewise p.2 p.1)
  have hleft : S.piecewise (S.piecewise p.2 p.1) (S.piecewise p.1 p.2) = p.2 := by
    ext i
    by_cases h : i ∈ S <;> simp [Finset.piecewise,h]
  have hright : S.piecewise (S.piecewise p.1 p.2) (S.piecewise p.2 p.1) = p.1 := by
    ext i
    by_cases h : i ∈ S <;> simp [Finset.piecewise,h]
  rw [hleft,hright] at he
  linear_combination E (S.piecewise p.2 p.1) (S.piecewise p.1 p.2) * he

/-- A genuine rank-one positive certificate contributes an absolute square at
every cut, including empty and full cuts. -/
theorem rankOne_partialTranspose_coherent (S : Finset I)
    (v : (I → L) → ℂ) (z : L → ℂ) :
    star (tensorPhase z) ⬝ᵥ
        (partialTransposeOn S (vecMulVec v (star v)) *ᵥ tensorPhase z) =
      star (star v ⬝ᵥ cutPhase S z) * (star v ⬝ᵥ cutPhase S z) := by
  rw [partialTranspose_coherent]
  simp only [dotProduct,Matrix.mulVec,vecMulVec_apply,Pi.star_apply,star_sum,
    star_mul,star_star,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

#print axioms partialTranspose_coherent
#print axioms rankOne_partialTranspose_coherent

end Cuts


/-- The actual coherent entry polynomial on real local coordinates. -/
def realSymbol (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ x, ∑ y, monomial ((occupation x).toFinsupp + (occupation y).toFinsupp) (E x y).re

private def realAmplitude (v : (Fin r → Fin n) → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ x, monomial (occupation x).toFinsupp (v x)

private lemma realSymbol_sum {J : Type*} [Fintype J]
    (E : J → Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) :
    realSymbol (∑ j, E j) = ∑ j, realSymbol (E j) := by
  simp only [realSymbol,Matrix.sum_apply,Complex.re_sum,map_sum]
  calc
    _ = ∑ x, ∑ j, ∑ y, monomial ((occupation x).toFinsupp +
        (occupation y).toFinsupp) (E j x y).re := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private lemma realSymbol_rankOne (v : (Fin r → Fin n) → ℂ) :
    realSymbol (vecMulVec v (star v)) =
      realAmplitude (fun x => (v x).re) * realAmplitude (fun x => (v x).re) +
      realAmplitude (fun x => (v x).im) * realAmplitude (fun x => (v x).im) := by
  simp only [realSymbol,realAmplitude,vecMulVec_apply,Pi.star_apply,
    Complex.star_def,Complex.mul_re,Complex.conj_re,Complex.conj_im,mul_neg,sub_neg_eq_add,
    map_add,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum,monomial_mul_monomial]
  simp only [add_comm,mul_comm]

/-- Every genuine positive tensor operator has a native real SOS coherent
symbol. No finite list of sample evaluations replaces the polynomial identity. -/
theorem realSymbol_posSemidef_sos
    (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) (hE : E.PosSemidef) :
    IsSumSq (realSymbol E) := by
  obtain ⟨A,hA⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hE.nonneg
  have he : Aᴴ * A = ∑ j, vecMulVec (star (A j)) (A j) := by
    ext x y
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.sum_apply,
      vecMulVec_apply,Pi.star_apply]
  rw [hA,Matrix.star_eq_conjTranspose,he,realSymbol_sum]
  apply IsSumSq.sum
  intro j hj
  have hh := realSymbol_rankOne (star (A j))
  simp only [star_star] at hh
  rw [hh]
  exact (IsSumSq.mul_self _).add (IsSumSq.mul_self _)

private lemma realSymbol_homogeneous
    (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) :
    (realSymbol E).IsHomogeneous (2*r) := by
  apply IsHomogeneous.sum
  intro x hx
  apply IsHomogeneous.sum
  intro y hy
  apply isHomogeneous_monomial
  simp [map_add,Finsupp.degree,occupation_card,two_mul]

#print axioms realSymbol_posSemidef_sos

open D5.S3.QuadraticForms
open private homogeneous_eq_form from D5.S3.QuadraticForms.HomogeneousSOSGram


private lemma occupation_real_product (u : Fin n → ℝ) (x : Fin r → Fin n) :
    (occupation x).toFinsupp.prod (fun a k => u a ^ k) = ∏ i, u (x i) := by
  apply Complex.ofReal_injective
  simpa [Finsupp.prod,tensorPhase] using occupation_product (fun i => (u i : ℂ)) x

/-- Evaluation of the native real polynomial is the actual coherent quadratic
form on real local vectors. -/
theorem eval_realSymbol (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ)
    (u : Fin n → ℝ) :
    eval u (realSymbol E) =
      (star (tensorPhase (fun i => (u i : ℂ))) ⬝ᵥ
        (E *ᵥ tensorPhase (fun i => (u i : ℂ)))).re := by
  have ht (x : Fin r → Fin n) : tensorPhase (fun i => (u i : ℂ)) x =
      ((∏ i, u (x i) : ℝ) : ℂ) := by simp [tensorPhase]
  simp only [realSymbol, MvPolynomial.eval_sum, MvPolynomial.eval_monomial,
    dotProduct,Matrix.mulVec,Finset.mul_sum,Pi.star_apply,Complex.re_sum]
  simp_rw [ht]
  simp only [Complex.star_def,Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finsupp.prod_add_index' (by simp) (fun i a b => pow_add _ _ _)]
  rw [occupation_real_product,occupation_real_product]
  ring

/-- Partial transposition has the identical real coherent polynomial for every
cut. This is a polynomial identity, not an equality on a finite sample. -/
theorem realSymbol_partialTranspose (S : Finset (Fin r))
    (E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) :
    realSymbol (partialTransposeOn S E) = realSymbol E := by
  apply MvPolynomial.funext
  intro u
  rw [eval_realSymbol,eval_realSymbol,partialTranspose_coherent]
  have hc : cutPhase S (fun i => (u i : ℂ)) = tensorPhase (fun i => (u i : ℂ)) := by
    ext x
    simp [cutPhase,tensorPhase,Complex.star_def,Complex.conj_ofReal]
  rw [hc]

/-- The set of actual Hermitian tensor operators with a native real SOS
coherent symbol is closed. This supplies the limit step in the GNP duality
argument while retaining closure in the underlying operator polar sum. -/
theorem realSymbol_sos_closed :
    IsClosed {E : HermitianMat (Fin r → Fin n) ℂ | IsSumSq (realSymbol E.mat)} := by
  let f : HermitianMat (Fin r → Fin n) ℂ →ₗ[ℝ]
      (HomogeneousSOSGram.Exponent (Fin n) (2*r) → ℝ) := {
    toFun := fun E a => (realSymbol E.mat).coeff a.val
    map_add' := by
      intro E F
      ext a
      have he : realSymbol (E+F).mat = realSymbol E.mat + realSymbol F.mat := by
        change realSymbol (E.mat + F.mat) = _
        simp [realSymbol,Matrix.add_apply,Complex.add_re,Finset.sum_add_distrib]
      exact congrArg (fun p : MvPolynomial (Fin n) ℝ => p.coeff a.val) he
    map_smul' := by
      intro c E
      ext a
      have he : realSymbol (c • E).mat = c • realSymbol E.mat := by
        simp [HermitianMat.mat_smul,realSymbol,Matrix.smul_apply,RCLike.real_smul_eq_coe_mul,
          Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
          MvPolynomial.smul_eq_C_mul,Finset.mul_sum,C_mul_monomial]
      exact congrArg (fun p : MvPolynomial (Fin n) ℝ => p.coeff a.val) he }
  have he : {E : HermitianMat (Fin r → Fin n) ℂ | IsSumSq (realSymbol E.mat)} =
      f ⁻¹' HomogeneousSOSGram.sosCoefficients r := by
    ext E
    change IsSumSq (realSymbol E.mat) ↔
      IsSumSq (HomogeneousSOSGram.form (2*r) (fun a => (realSymbol E.mat).coeff a.val))
    rw [← homogeneous_eq_form _ _ (realSymbol_homogeneous E.mat)]
  rw [he]
  exact (HomogeneousSOSGram.sosCoefficients_closed r).preimage
    f.continuous_of_finiteDimensional

#print axioms eval_realSymbol
#print axioms realSymbol_partialTranspose
#print axioms realSymbol_sos_closed

end
end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseCoherentSymbol
