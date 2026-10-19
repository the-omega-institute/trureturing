/- GID: D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/EulerProduct
   generality: G
   mirror-B: none(waiver:upstream-proof-complete-port)
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   utility: none
   digest: Upstream Euler-product identity used by Hasse–Davenport. -/

/-
Attributed source: https://github.com/fukubillueda-web/epsilon_FML/blob/
b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed/LanglandsFirstMainLemma/FiniteField/EulerProduct.lean
License: Apache-2.0; the verbatim upstream LICENSE and original source hashes are in
Library/Fourier/epsilonfml2026hassedavenport.md.
Modifications: repository import paths.
The upstream namespace, theorem statements, normalization, and proof structure are
retained. The pinned upstream distribution contains no NOTICE file.
-/

import D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.FiniteField.PolynomialWeights
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Finite Euler products for monic-polynomial weights

For a multiplicative weight `w` on monic polynomials over a finite field, this file defines

* the degree sums `MonicWeight.degreeSum w n`,
* their generating series `MonicWeight.series w`, and
* the closed-point power sums `MonicWeight.closedPointPowerSum w r`.

Unique factorization of monic polynomials and the formal derivative give the integral identity

`L_w' = L_w * ∑_{r ≥ 1} B_r T^(r - 1)`.

Consequently, if all degree sums from degree two onward vanish, then
`-B_r = (-A_1)^r`.  This is the single Euler-product calculation used by both the
Hasse--Davenport lift and the Hasse-function lift.  In particular, no nonvanishing hypothesis is
placed on the weight: the zero value of a multiplicative character at zero is allowed.
-/

open Polynomial PowerSeries
open scoped BigOperators

namespace LanglandsFirstMainLemma

universe u


noncomputable section

/-- Monic polynomials of exact degree `n`.  The type is finite when the coefficient field is
finite, via Mathlib's coefficient equivalence with `Fin n → k`. -/
abbrev MonicPolynomialOfDegree (k : Type u) [Field k] (n : ℕ) :=
  {p : k[X] // p.Monic ∧ p.natDegree = n}

noncomputable instance monicPolynomialOfDegreeFintype
    (k : Type u) [Field k] [Fintype k] (n : ℕ) :
    Fintype (MonicPolynomialOfDegree k n) :=
  Fintype.ofEquiv (Fin n → k)
    ((Polynomial.degreeLTEquiv k n).toEquiv.symm.trans
      (Polynomial.monicEquivDegreeLT n).symm)

/-- Monic irreducible polynomials of exact degree `n`. -/
abbrev MonicIrreducibleOfDegree (k : Type u) [Field k] (n : ℕ) :=
  {p : MonicPolynomialOfDegree k n // Irreducible (p : k[X])}

noncomputable instance monicIrreducibleOfDegreeFintype
    (k : Type u) [Field k] [Fintype k] (n : ℕ) :
    Fintype (MonicIrreducibleOfDegree k n) :=
  Fintype.ofFinite _

/-- Monic irreducible polynomials, without a degree bound. -/
abbrev MonicIrreducible (k : Type u) [Field k] :=
  {p : k[X] // p.Monic ∧ Irreducible p}

section Factorization

variable (k : Type u) [Field k]

local instance : DecidableEq k := Classical.decEq k

open UniqueFactorizationMonoid

/-- The multiset of normalized monic irreducible factors of a monic polynomial. -/
def monicFactors (p : MonicPolynomial k) : Multiset (MonicIrreducible k) :=
  (normalizedFactors (p : k[X])).pmap
    (fun q hq ↦
      ⟨q, (Polynomial.mem_normalizedFactors_iff p.property.ne_zero).mp hq |>.2.1,
        (Polynomial.mem_normalizedFactors_iff p.property.ne_zero).mp hq |>.1⟩)
    (fun _ hq ↦ hq)

/-- Multiply a multiset of monic irreducible polynomials. -/
def monicFactorsProd (s : Multiset (MonicIrreducible k)) : MonicPolynomial k :=
  ⟨(s.map (fun p : MonicIrreducible k ↦ p.1)).prod, by
    apply Polynomial.monic_multiset_prod_of_monic
    intro p _
    exact p.2.1⟩

theorem map_val_monicFactors (p : MonicPolynomial k) :
    (monicFactors k p).map (·.1) = normalizedFactors (p : k[X]) := by
  simp [monicFactors, Multiset.pmap_eq_map_attach]

@[simp]
theorem monicFactorsProd_monicFactors (p : MonicPolynomial k) :
    monicFactorsProd k (monicFactors k p) = p := by
  classical
  apply Subtype.ext
  simp only [monicFactorsProd]
  rw [map_val_monicFactors]
  simpa [p.property.leadingCoeff] using
    Polynomial.leadingCoeff_mul_prod_normalizedFactors (p : k[X])

@[simp]
theorem monicFactors_monicFactorsProd (s : Multiset (MonicIrreducible k)) :
    monicFactors k (monicFactorsProd k s) = s := by
  classical
  apply Multiset.map_injective Subtype.val_injective
  rw [map_val_monicFactors]
  change normalizedFactors ((s.map (·.1)).prod) = s.map (·.1)
  rw [normalizedFactors_prod_eq]
  · simp only [Multiset.map_map, Function.comp_apply]
    apply Multiset.map_congr rfl
    intro p _
    exact p.2.1.normalize_eq_self
  · intro p hp
    obtain ⟨q, _, rfl⟩ := Multiset.mem_map.mp hp
    exact q.2.2

/-- Unique factorization identifies monic polynomials with finite multisets of monic irreducible
polynomials.  Unlike an associates-level factorization, this equivalence has no unit ambiguity. -/
noncomputable def monicFactorsEquiv :
    MonicPolynomial k ≃ Multiset (MonicIrreducible k) where
  toFun := monicFactors k
  invFun := monicFactorsProd k
  left_inv := monicFactorsProd_monicFactors k
  right_inv := monicFactors_monicFactorsProd k

theorem natDegree_monicFactorsProd (s : Multiset (MonicIrreducible k)) :
    ((monicFactorsProd k s : MonicPolynomial k) : k[X]).natDegree =
      (s.map fun p ↦ p.1.natDegree).sum := by
  change ((s.map fun p : MonicIrreducible k ↦ p.1).prod).natDegree =
    (s.map fun p : MonicIrreducible k ↦ p.1.natDegree).sum
  rw [Polynomial.natDegree_multiset_prod_of_monic]
  · simp only [Multiset.map_map, Function.comp_apply]
  · intro p hp
    obtain ⟨q, _, rfl⟩ := Multiset.mem_map.mp hp
    exact q.2.1

theorem sum_natDegree_monicFactors (p : MonicPolynomial k) :
    ((monicFactors k p).map fun q ↦ q.1.natDegree).sum = (p : k[X]).natDegree := by
  rw [← natDegree_monicFactorsProd k, monicFactorsProd_monicFactors]

end Factorization

/-- A monic weight evaluated on a product of irreducible factors is the product of the factor
weights. -/
theorem weight_monicFactorsProd {k : Type u} [Field k]
    (w : MonicWeight k ℂ) (s : Multiset (MonicIrreducible k)) :
    w (monicFactorsProd k s) =
      (s.map fun q ↦ w ⟨q.1, by change q.1.Monic; exact q.2.1⟩).prod := by
  have heq : monicFactorsProd k s =
      (s.map fun q ↦ (⟨q.1, by change q.1.Monic; exact q.2.1⟩ :
        MonicPolynomial k)).prod := by
    apply Subtype.ext
    rw [Submonoid.coe_multiset_prod]
    change (s.map fun q ↦ q.1).prod = _
    simp only [Multiset.map_map, Function.comp_apply]
  rw [heq, map_multiset_prod, Multiset.map_map]
  simp only [Function.comp_apply]

theorem weight_monicFactors {k : Type u} [Field k]
    (w : MonicWeight k ℂ) (p : MonicPolynomial k) :
    w p = ((monicFactors k p).map fun q ↦
      w ⟨q.1, by change q.1.Monic; exact q.2.1⟩).prod := by
  rw [← weight_monicFactorsProd w (monicFactors k p), monicFactorsProd_monicFactors]

/-- Multisets of monic irreducibles whose degrees add to `n`. -/
def FactorMultisetsOfDegree (k : Type u) [Field k] (n : ℕ) :=
  {s : Multiset (MonicIrreducible k) // (s.map fun q ↦ q.1.natDegree).sum = n}

/-- Exact-degree monic polynomials are equivalent to exact-total-degree multisets of monic
irreducibles. -/
noncomputable def monicPolynomialOfDegreeFactorsEquiv (k : Type u) [Field k] (n : ℕ) :
    MonicPolynomialOfDegree k n ≃ FactorMultisetsOfDegree k n where
  toFun p := ⟨monicFactors k ⟨p.1, by change p.1.Monic; exact p.2.1⟩, by
    simpa [p.2.2] using
      sum_natDegree_monicFactors k ⟨p.1, by change p.1.Monic; exact p.2.1⟩⟩
  invFun s := ⟨monicFactorsProd k s.1, (monicFactorsProd k s.1).property,
    (natDegree_monicFactorsProd k s.1).trans s.2⟩
  left_inv p := by
    apply Subtype.ext
    change ((monicFactorsProd k
      (monicFactors k ⟨p.1, by change p.1.Monic; exact p.2.1⟩) :
        MonicPolynomial k) : k[X]) = p.1
    exact congrArg Subtype.val
      (monicFactorsProd_monicFactors k
        ⟨p.1, by change p.1.Monic; exact p.2.1⟩)
  right_inv s := by
    apply Subtype.ext
    exact monicFactors_monicFactorsProd k s.1

noncomputable instance factorMultisetsOfDegreeFintype
    (k : Type u) [Field k] [Fintype k] (n : ℕ) :
    Fintype (FactorMultisetsOfDegree k n) :=
  Fintype.ofEquiv (MonicPolynomialOfDegree k n)
    (monicPolynomialOfDegreeFactorsEquiv k n)

section GradedMultisetRecurrence

variable {alpha : Type*} [DecidableEq alpha]

/-- Data consisting of a multiset, a distinguished color, and a positive multiplicity. -/
abbrev ExpansionIndex :=
  {x : Multiset alpha × alpha × ℕ // 0 < x.2.2}

/-- Data consisting of a multiset, a color occurring in it, and a chosen occurrence number. -/
abbrev OccurrenceIndex :=
  {x : Multiset alpha × alpha × ℕ // x.2.2 < x.1.count x.2.1}

/-- Adding a positive block of one color is equivalent to choosing an occurrence of that color
in the resulting multiset. -/
def multisetOccurrenceEquiv :
    ExpansionIndex (alpha := alpha) ≃ OccurrenceIndex (alpha := alpha) where
  toFun := fun ⟨⟨t, p, h⟩, hh⟩ ↦
    ⟨⟨t + Multiset.replicate h p, p, h - 1⟩, by
        change 0 < h at hh
        change h - 1 < Multiset.count p (t + Multiset.replicate h p)
        rw [Multiset.count_add, Multiset.count_replicate_self]
        have := hh
        omega⟩
  invFun := fun ⟨⟨s, p, j⟩, _⟩ ↦
    ⟨⟨s - Multiset.replicate (j + 1) p, p, j + 1⟩, by
        change 0 < j + 1
        omega⟩
  left_inv := by
    rintro ⟨⟨t, p, h⟩, hh⟩
    change 0 < h at hh
    have hpred : h - 1 + 1 = h := Nat.sub_add_cancel (by omega)
    apply Subtype.ext
    change
      (t + Multiset.replicate h p - Multiset.replicate (h - 1 + 1) p,
          p, h - 1 + 1) = (t, p, h)
    rw [hpred, Multiset.add_sub_cancel_right]
  right_inv := by
    rintro ⟨⟨s, p, j⟩, hj⟩
    change j < s.count p at hj
    have hj' : j + 1 ≤ s.count p := by omega
    have hle : Multiset.replicate (j + 1) p ≤ s :=
      Multiset.le_count_iff_replicate_le.mp hj'
    apply Subtype.ext
    change
      (s - Multiset.replicate (j + 1) p + Multiset.replicate (j + 1) p,
          p, j + 1 - 1) = (s, p, j)
    rw [Multiset.sub_add_cancel hle]
    simp

/-- Total degree of a multiset with respect to a positive integer degree function. -/
def gradedDegree (d : alpha → ℕ) (s : Multiset alpha) : ℕ :=
  (s.map d).sum

/-- Product of the weights of the entries of a multiset. -/
def gradedWeight {A : Type*} [CommMonoid A] (weight : alpha → A)
    (s : Multiset alpha) : A :=
  (s.map weight).prod

omit [DecidableEq alpha] in
theorem gradedDegree_add_replicate (d : alpha → ℕ) (s : Multiset alpha)
    (p : alpha) (h : ℕ) :
    gradedDegree d (s + Multiset.replicate h p) = gradedDegree d s + h * d p := by
  simp [gradedDegree, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
    Multiset.sum_replicate]

/-- Positive-block expansions having prescribed total degree. -/
abbrev ExpansionOfDegree (d : alpha → ℕ) (N : ℕ) :=
  {x : ExpansionIndex (alpha := alpha) //
    gradedDegree d x.1.1 + x.1.2.2 * d x.1.2.1 = N}

/-- Pointed multisets having prescribed total degree. -/
abbrev OccurrenceOfDegree (d : alpha → ℕ) (N : ℕ) :=
  {x : OccurrenceIndex (alpha := alpha) // gradedDegree d x.1.1 = N}

/-- The block-insertion equivalence preserves total degree. -/
def expansionOccurrenceEquiv (d : alpha → ℕ) (N : ℕ) :
    ExpansionOfDegree d N ≃ OccurrenceOfDegree d N :=
  Equiv.subtypeEquiv multisetOccurrenceEquiv fun x ↦ by
    rcases x with ⟨⟨t, p, h⟩, _⟩
    change
      gradedDegree d t + h * d p = N ↔
        gradedDegree d (t + Multiset.replicate h p) = N
    rw [gradedDegree_add_replicate]

omit [DecidableEq alpha] in
theorem gradedWeight_add_replicate {A : Type*} [CommMonoid A]
    (weight : alpha → A) (s : Multiset alpha) (p : alpha) (h : ℕ) :
    gradedWeight weight (s + Multiset.replicate h p) =
      gradedWeight weight s * weight p ^ h := by
  simp [gradedWeight, Multiset.map_add, Multiset.prod_add, Multiset.map_replicate]

end GradedMultisetRecurrence

namespace GradedEulerProduct

variable {alpha : Type*} [DecidableEq alpha]

/-- Multisets of graded atoms having exact total degree. -/
abbrev GradedExact (d : alpha → ℕ) (N : ℕ) :=
  {s : Multiset alpha // gradedDegree d s = N}

abbrev OccurrenceSigma (d : alpha → ℕ) (N : ℕ) :=
  Σ s : GradedExact d N,
    Σ p : {p : alpha // p ∈ s.1}, Fin (s.1.count p.1)

def occurrenceSigmaEquiv (d : alpha → ℕ) (N : ℕ) :
    OccurrenceOfDegree d N ≃ OccurrenceSigma d N where
  toFun := fun ⟨⟨⟨s, p, j⟩, hj⟩, hdeg⟩ ↦
    ⟨⟨s, hdeg⟩,
      ⟨p, Multiset.count_pos.mp (Nat.zero_lt_of_lt hj)⟩,
      ⟨j, hj⟩⟩
  invFun := fun ⟨⟨s, hdeg⟩, ⟨p, _⟩, ⟨j, hj⟩⟩ ↦
    ⟨⟨⟨s, p, j⟩, hj⟩, hdeg⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    rcases x with ⟨s, p, j⟩
    rfl

@[reducible]
noncomputable def occurrenceFintype (d : alpha → ℕ) (N : ℕ)
    [Fintype (GradedExact d N)] :
    Fintype (OccurrenceOfDegree d N) :=
  Fintype.ofEquiv (OccurrenceSigma d N) (occurrenceSigmaEquiv d N).symm

@[reducible]
noncomputable def expansionFintype (d : alpha → ℕ) (N : ℕ)
    [Fintype (GradedExact d N)] :
    Fintype (ExpansionOfDegree d N) := by
  letI := occurrenceFintype d N
  exact Fintype.ofEquiv _ (expansionOccurrenceEquiv d N).symm

theorem sum_mem_count_nsmul {M : Type*} [AddCommMonoid M]
    (s : Multiset alpha) (f : alpha → M) :
    (∑ p : {p : alpha // p ∈ s}, s.count p.1 • f p.1) = (s.map f).sum := by
  rw [← Finset.sum_subtype s.toFinset (by simp)
    (fun p ↦ s.count p • f p)]
  exact (Finset.sum_multiset_map_count s f).symm

theorem occurrence_sum_eq {d : alpha → ℕ} {N : ℕ}
    [Fintype (GradedExact d N)] {A : Type*} [CommSemiring A]
    (weight : alpha → A) :
    let _ := occurrenceFintype d N
    (∑ x : OccurrenceOfDegree d N,
      d x.1.1.2.1 • gradedWeight weight x.1.1.1) =
    N • ∑ s : GradedExact d N, gradedWeight weight s.1 := by
  dsimp only
  letI := occurrenceFintype d N
  let occurrenceTerm : OccurrenceSigma d N → A
    | ⟨⟨s, _⟩, ⟨p, _⟩, _⟩ => d p • gradedWeight weight s
  calc
    _ = ∑ x : OccurrenceSigma d N, occurrenceTerm x := by
      apply Fintype.sum_equiv (occurrenceSigmaEquiv d N)
      rintro ⟨⟨⟨s, p, j⟩, _⟩, _⟩
      rfl
    _ = _ := by
      dsimp only [occurrenceTerm]
      rw [Fintype.sum_sigma]
      simp only [Fintype.sum_sigma]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro s _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      have hdeg :
          (∑ p : {p : alpha // p ∈ s.1}, s.1.count p.1 * d p.1) = N := by
        have hmap :
            (∑ p : {p : alpha // p ∈ s.1}, s.1.count p.1 * d p.1) =
              gradedDegree d s.1 := by
          simpa [nsmul_eq_mul, gradedDegree] using sum_mem_count_nsmul s.1 d
        exact hmap.trans s.2
      simp only [nsmul_eq_mul]
      simp_rw [← mul_assoc, ← Nat.cast_mul]
      rw [← Finset.sum_mul, ← Nat.cast_sum, hdeg]

theorem global_weighted_recurrence {d : alpha → ℕ} {N : ℕ}
    [Fintype (GradedExact d N)] {A : Type*} [CommSemiring A]
    (weight : alpha → A) :
    let _ := expansionFintype d N
    N • (∑ s : GradedExact d N, gradedWeight weight s.1) =
      ∑ x : ExpansionOfDegree d N,
        gradedWeight weight x.1.1.1 *
          (d x.1.1.2.1 • weight x.1.1.2.1 ^ x.1.1.2.2) := by
  dsimp only
  letI := expansionFintype d N
  letI := occurrenceFintype d N
  rw [← occurrence_sum_eq (d := d) (N := N) weight]
  symm
  apply Fintype.sum_equiv (expansionOccurrenceEquiv d N)
  rintro ⟨⟨⟨s, p, h⟩, _⟩, _⟩
  change gradedWeight weight s * (d p • weight p ^ h) =
    d p • gradedWeight weight (s + Multiset.replicate h p)
  rw [gradedWeight_add_replicate]
  simp only [nsmul_eq_mul]
  ac_rfl

/-- A graded atom together with a positive power whose total degree is `r`. -/
abbrev AtomPowerIndex (d : alpha → ℕ) (r : ℕ) :=
  {x : alpha × ℕ // 0 < x.2 ∧ x.2 * d x.1 = r}

def atomPowerToExpansion (d : alpha → ℕ) (r : ℕ) :
    AtomPowerIndex d r → ExpansionOfDegree d r :=
  fun ⟨⟨p, h⟩, hh, hpow⟩ ↦ ⟨⟨⟨∅, p, h⟩, hh⟩, by
    simpa [gradedDegree] using hpow⟩

omit [DecidableEq alpha] in
theorem atomPowerToExpansion_injective (d : alpha → ℕ) (r : ℕ) :
    Function.Injective (atomPowerToExpansion d r) := by
  rintro ⟨⟨p, h⟩, _, _⟩ ⟨⟨q, j⟩, _, _⟩ heq
  have htuple := congrArg (fun z : ExpansionOfDegree d r ↦ z.1.1) heq
  change ((∅ : Multiset alpha), p, h) = (∅, q, j) at htuple
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z ↦ z.2.1) htuple
  · exact congrArg (fun z ↦ z.2.2) htuple

@[reducible]
noncomputable def atomPowerFintype (d : alpha → ℕ) (r : ℕ)
    [Fintype (GradedExact d r)] : Fintype (AtomPowerIndex d r) := by
  letI := expansionFintype d r
  exact Fintype.ofInjective (atomPowerToExpansion d r)
    (atomPowerToExpansion_injective d r)

noncomputable def powerSum (d : alpha → ℕ) (weight : alpha → ℂ) (r : ℕ)
    [Fintype (GradedExact d r)] : ℂ := by
  letI := atomPowerFintype d r
  exact ∑ x : AtomPowerIndex d r,
    (d x.1.1 : ℂ) * weight x.1.1 ^ x.1.2

noncomputable def gradedSum (d : alpha → ℕ) (weight : alpha → ℂ) (n : ℕ)
    [Fintype (GradedExact d n)] : ℂ :=
  ∑ s : GradedExact d n, gradedWeight weight s.1

abbrev DegreeSplit (N : ℕ) :=
  {z : ℕ × ℕ // z ∈
    (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ))}

instance degreeSplitFintype (N : ℕ) : Fintype (DegreeSplit N) :=
  Finset.fintypeCoeSort _

abbrev ConvolutionIndex (d : alpha → ℕ) (N : ℕ) :=
  Σ z : DegreeSplit N, GradedExact d z.1.1 × AtomPowerIndex d z.1.2

def convolutionExpansionEquiv (d : alpha → ℕ) (N : ℕ) :
    ConvolutionIndex d N ≃ ExpansionOfDegree d N where
  toFun := fun ⟨⟨⟨i, r⟩, hir⟩, ⟨t, htdeg⟩,
      ⟨⟨p, h⟩, hh, hpow⟩⟩ ↦
    ⟨⟨⟨t, p, h⟩, hh⟩, by
      calc
        gradedDegree d t + h * d p = i + r :=
          congrArg₂ Nat.add htdeg hpow
        _ = N := Finset.HasAntidiagonal.mem_antidiagonal.mp hir⟩
  invFun := fun ⟨⟨⟨t, p, h⟩, hh⟩, hdeg⟩ ↦
    ⟨⟨⟨gradedDegree d t, h * d p⟩,
        Finset.HasAntidiagonal.mem_antidiagonal.mpr hdeg⟩,
      ⟨t, rfl⟩,
      ⟨⟨p, h⟩, hh, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨⟨i, r⟩, hir⟩, ⟨t, htdeg⟩,
      ⟨⟨p, h⟩, hh, hpow⟩⟩
    dsimp at htdeg hpow
    subst i
    subst r
    rfl
  right_inv := by
    rintro ⟨⟨⟨t, p, h⟩, hh⟩, hdeg⟩
    rfl

theorem expansion_sum_eq_convolution {d : alpha → ℕ}
    (finite : ∀ n, Fintype (GradedExact d n))
    (weight : alpha → ℂ) (N : ℕ) :
    let _ := expansionFintype d N
    (∑ x : ExpansionOfDegree d N,
      gradedWeight weight x.1.1.1 *
        (d x.1.1.2.1 • weight x.1.1.2.1 ^ x.1.1.2.2)) =
    ∑ z : DegreeSplit N,
      gradedSum d weight z.1.1 * powerSum d weight z.1.2 := by
  dsimp only
  letI (n : ℕ) := finite n
  letI := expansionFintype d N
  letI (r : ℕ) := atomPowerFintype d r
  let convolutionTerm : ConvolutionIndex d N → ℂ
    | ⟨_, ⟨⟨s, _⟩, ⟨⟨p, h⟩, _⟩⟩⟩ =>
        gradedWeight weight s * ((d p : ℂ) * weight p ^ h)
  calc
    _ = ∑ x : ConvolutionIndex d N, convolutionTerm x := by
      apply Fintype.sum_equiv (convolutionExpansionEquiv d N).symm
      rintro ⟨⟨⟨s, p, h⟩, _⟩, _⟩
      simp only [nsmul_eq_mul, convolutionTerm]
      rfl
    _ = _ := by
      dsimp only [convolutionTerm]
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro z _
      rw [Fintype.sum_prod_type]
      simp only [gradedSum, powerSum]
      rw [Finset.sum_mul_sum]

noncomputable def gradedSumFamily (d : alpha → ℕ)
    (finite : ∀ n, Fintype (GradedExact d n))
    (weight : alpha → ℂ) (n : ℕ) : ℂ :=
  @gradedSum alpha d weight n (finite n)

noncomputable def powerSumFamily (d : alpha → ℕ)
    (finite : ∀ n, Fintype (GradedExact d n))
    (weight : alpha → ℂ) (n : ℕ) : ℂ :=
  @powerSum alpha _ d weight n (finite n)

theorem global_convolution_recurrence (d : alpha → ℕ)
    (finite : ∀ n, Fintype (GradedExact d n))
    (weight : alpha → ℂ) (N : ℕ) :
    N • gradedSumFamily d finite weight N =
      ∑ z : DegreeSplit N,
        gradedSumFamily d finite weight z.1.1 *
          powerSumFamily d finite weight z.1.2 := by
  letI (n : ℕ) := finite n
  simp only [gradedSumFamily, powerSumFamily]
  rw [gradedSum]
  rw [global_weighted_recurrence (d := d) (N := N) weight]
  exact expansion_sum_eq_convolution (d := d) finite weight N

@[simp]
theorem powerSumFamily_zero (d : alpha → ℕ) (hd : ∀ p, 0 < d p)
    (finite : ∀ n, Fintype (GradedExact d n)) (weight : alpha → ℂ) :
    powerSumFamily d finite weight 0 = 0 := by
  letI := finite 0
  change powerSum d weight 0 = 0
  unfold powerSum
  letI := atomPowerFintype d 0
  apply Fintype.sum_eq_zero
  intro x
  have hpos : 0 < x.1.2 * d x.1.1 := Nat.mul_pos x.2.1 (hd _)
  rw [x.2.2] at hpos
  omega

theorem sum_degreeSplit_succ (a b : ℕ → ℂ) (hb0 : b 0 = 0) (n : ℕ) :
    (∑ z : DegreeSplit (n + 1), a z.1.1 * b z.1.2) =
      ∑ z ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)),
        a z.1 * b (z.2 + 1) := by
  change (∑ z : {z : ℕ × ℕ //
    z ∈ (Finset.HasAntidiagonal.antidiagonal (n + 1) : Finset (ℕ × ℕ))},
      a z.1.1 * b z.1.2) = _
  rw [show (Finset.univ : Finset {z : ℕ × ℕ //
      z ∈ (Finset.HasAntidiagonal.antidiagonal (n + 1) : Finset (ℕ × ℕ))}) =
      (Finset.HasAntidiagonal.antidiagonal (n + 1) : Finset (ℕ × ℕ)).attach from
    Finset.univ_eq_attach _]
  calc
    (∑ z ∈ (Finset.HasAntidiagonal.antidiagonal (n + 1) :
        Finset (ℕ × ℕ)).attach, a z.1.1 * b z.1.2) =
        ∑ z ∈ (Finset.HasAntidiagonal.antidiagonal (n + 1) : Finset (ℕ × ℕ)),
          a z.1 * b z.2 :=
      Finset.sum_attach
        (Finset.HasAntidiagonal.antidiagonal (n + 1) : Finset (ℕ × ℕ))
        (fun z : ℕ × ℕ ↦ a z.1 * b z.2)
    _ = _ := by
      rw [Finset.Nat.sum_antidiagonal_succ']
      simp [hb0]

/-- Integral logarithmic-derivative identity for arbitrary positive-degree graded atoms. -/
theorem global_weighted_derivative (d : alpha → ℕ) (hd : ∀ p, 0 < d p)
    (finite : ∀ n, Fintype (GradedExact d n)) (weight : alpha → ℂ) :
    PowerSeries.derivative (PowerSeries.mk (gradedSumFamily d finite weight)) =
      PowerSeries.mk (gradedSumFamily d finite weight) *
        PowerSeries.mk (fun n ↦ powerSumFamily d finite weight (n + 1)) := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk,
    PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  rw [← sum_degreeSplit_succ (gradedSumFamily d finite weight)
    (powerSumFamily d finite weight) (powerSumFamily_zero d hd finite weight) n]
  rw [← global_convolution_recurrence d finite weight (n + 1)]
  simp [nsmul_eq_mul, mul_comm]

end GradedEulerProduct

/-- Integral Newton recurrence for a formal Euler product.  If `A(T)` has constant coefficient one,
has no terms from degree two onward, and satisfies `A' = A B`, then the shifted coefficients of
`B` are the signed powers of the linear coefficient of `A`. -/
theorem power_identity_of_derivative {A : Type*} [CommRing A] (a b : ℕ → A)
    (ha0 : a 0 = 1)
    (ha : ∀ n, 2 ≤ n → a n = 0)
    (hderiv :
      PowerSeries.derivative (PowerSeries.mk a) =
        PowerSeries.mk a * PowerSeries.mk (fun n ↦ b (n + 1))) :
    ∀ r, 0 < r → -b r = (-a 1) ^ r := by
  intro r hr
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  induction n with
  | zero =>
      have h := congrArg (PowerSeries.coeff 0) hderiv
      simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_mk,
        PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
        Nat.zero_add] at h
      rw [ha0, one_mul] at h
      simpa using (congrArg Neg.neg h).symm
  | succ n ih =>
      let m := n + 1
      have hm : 1 ≤ m := by omega
      have h := congrArg (PowerSeries.coeff m) hderiv
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk,
        PowerSeries.coeff_mul] at h
      simp only [PowerSeries.coeff_mk] at h
      have hm1 : 2 ≤ m + 1 := by omega
      rw [ha (m + 1) hm1, zero_mul] at h
      have hsum :
          (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal m : Finset (ℕ × ℕ)),
              a x.1 * b (x.2 + 1)) =
            b (m + 1) + a 1 * b m := by
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        rw [Finset.sum_range_succ']
        have hz :
            (∑ x ∈ Finset.range m, a (x + 1) * b (m - (x + 1) + 1)) =
              a 1 * b m := by
          rw [Finset.sum_eq_single 0]
          · simp only [Nat.zero_add]
            rw [Nat.sub_add_cancel hm]
          · intro j hj hne
            have hj2 : 2 ≤ j + 1 := by omega
            rw [ha (j + 1) hj2, zero_mul]
          · intro hnot
            exact (hnot (Finset.mem_range.mpr hm)).elim
        rw [hz]
        rw [ha0, one_mul]
        simp only [Nat.sub_zero]
        exact add_comm _ _
      rw [hsum] at h
      have hrec : -b (m + 1) = a 1 * b m := by
        rw [neg_eq_iff_add_eq_zero]
        exact h.symm
      rw [hrec]
      have ihm := ih (by omega)
      have hbm : b m = -((-a 1) ^ m) := by
        simpa using congrArg Neg.neg ihm
      rw [hbm]
      rw [show (n + 1).succ = m + 1 by simp [m], pow_succ]
      ring

namespace MonicWeight

variable {k : Type u} [Field k] [Fintype k]

/-- The coefficient in degree `n` of the monic-polynomial `L`-series attached to `w`. -/
noncomputable def degreeSum (w : MonicWeight k ℂ) (n : ℕ) : ℂ :=
  ∑ p : MonicPolynomialOfDegree k n,
    w (⟨p.1, by change p.1.Monic; exact p.2.1⟩ : MonicPolynomial k)

theorem degreeSum_eq_factorMultisets (w : MonicWeight k ℂ) (n : ℕ) :
    degreeSum w n =
      ∑ s : FactorMultisetsOfDegree k n,
        (s.1.map fun q ↦
          w ⟨q.1, by change q.1.Monic; exact q.2.1⟩).prod := by
  rw [degreeSum, ← (monicPolynomialOfDegreeFactorsEquiv k n).sum_comp]
  apply Fintype.sum_congr
  intro p
  exact weight_monicFactors w
    ⟨p.1, by change p.1.Monic; exact p.2.1⟩

/-- The formal generating series `L_w(T) = ∑_n A_n(w) T^n`. -/
noncomputable def series (w : MonicWeight k ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk (degreeSum w)

@[simp]
theorem coeff_series (w : MonicWeight k ℂ) (n : ℕ) :
    PowerSeries.coeff n (series w) = degreeSum w n :=
  PowerSeries.coeff_mk _ _

@[simp]
theorem degreeSum_zero (w : MonicWeight k ℂ) : degreeSum w 0 = 1 := by
  classical
  rw [degreeSum]
  let p0 : MonicPolynomialOfDegree k 0 := ⟨1, monic_one, natDegree_one⟩
  rw [Fintype.sum_eq_single p0]
  · change w (1 : MonicPolynomial k) = 1
    exact map_one w
  · intro p hp
    have hp0 : p = p0 := Subtype.ext <|
      Polynomial.eq_one_of_monic_natDegree_zero p.2.1 p.2.2
    exact (hp hp0).elim

/-- The degree-`r` closed-point power sum

`B_r(w) = ∑_{d ∣ r} d ∑_{P monic irreducible, deg P = d} w(P)^(r/d)`.

For `r = 0` Mathlib's `Nat.divisors` is empty, so the value is zero. -/
noncomputable def closedPointPowerSum (w : MonicWeight k ℂ) (r : ℕ) : ℂ :=
  ∑ d ∈ r.divisors,
    (d : ℂ) * ∑ p : MonicIrreducibleOfDegree k d,
      (fun ⟨⟨f, hmonic, _⟩, _⟩ ↦
        w (⟨f, hmonic⟩ : MonicPolynomial k) ^ (r / d)) p

/-- The shifted closed-point series `∑_{n≥0} B_(n+1)(w) T^n`. -/
noncomputable def closedPointSeries (w : MonicWeight k ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n ↦ closedPointPowerSum w (n + 1)

@[simp]
theorem coeff_closedPointSeries (w : MonicWeight k ℂ) (n : ℕ) :
    PowerSeries.coeff n (closedPointSeries w) = closedPointPowerSum w (n + 1) :=
  PowerSeries.coeff_mk _ _

section MonicSpecialization

variable (k : Type u) [Field k] [Fintype k]

local instance : DecidableEq k := Classical.decEq k

abbrev primeDegree : MonicIrreducible k → ℕ := fun p ↦ p.1.natDegree

omit [Fintype k] in
theorem primeDegree_pos (p : MonicIrreducible k) : 0 < primeDegree k p :=
  p.2.2.natDegree_pos

@[reducible]
noncomputable def monicGradedFinite (n : ℕ) :
    Fintype (GradedEulerProduct.GradedExact (primeDegree k) n) := by
  change Fintype (FactorMultisetsOfDegree k n)
  infer_instance

abbrev DivisorPrimeIndex (r : ℕ) :=
  Σ e : {e : ℕ // e ∈ r.divisors}, MonicIrreducibleOfDegree k e.1

def atomPowerDivisorEquiv (r : ℕ) (hr : 0 < r) :
    GradedEulerProduct.AtomPowerIndex (primeDegree k) r ≃ DivisorPrimeIndex k r where
  toFun := fun ⟨⟨p, h⟩, _, hpow⟩ ↦
    ⟨⟨primeDegree k p, Nat.mem_divisors.mpr ⟨⟨h, by
      simpa [mul_comm] using hpow.symm⟩, hr.ne'⟩⟩,
      ⟨⟨p.1, p.2.1, rfl⟩, p.2.2⟩⟩
  invFun := fun ⟨⟨e, he⟩, ⟨⟨p, hpmonic, hpdeg⟩, hpirr⟩⟩ ↦ by
    have hdvd : e ∣ r := (Nat.mem_divisors.mp he).1
    change p.natDegree = e at hpdeg
    have hdeg : 0 < e := by
      rw [← hpdeg]
      exact hpirr.natDegree_pos
    exact ⟨⟨⟨p, hpmonic, hpirr⟩, r / e⟩,
      Nat.div_pos (Nat.le_of_dvd hr hdvd) hdeg,
      by
        change r / e * p.natDegree = r
        rw [hpdeg]
        exact Nat.div_mul_cancel hdvd⟩
  left_inv := by
    rintro ⟨⟨p, h⟩, hh, hpow⟩
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · dsimp
      rw [← hpow]
      exact Nat.mul_div_left h (primeDegree_pos k p)
  right_inv := by
    rintro ⟨⟨e, he⟩, ⟨⟨p, hpmonic, hpdeg⟩, hpirr⟩⟩
    dsimp at hpdeg
    subst e
    rfl

abbrev primeWeight (w : MonicWeight k ℂ) : MonicIrreducible k → ℂ :=
  fun p ↦ w ⟨p.1, by change p.1.Monic; exact p.2.1⟩

abbrev exactPrimeWeight (w : MonicWeight k ℂ) {e : ℕ}
    (p : MonicIrreducibleOfDegree k e) : ℂ :=
  primeWeight k w ⟨p.1.1, p.1.2.1, p.2⟩

theorem powerSumFamily_eq_closedPointPowerSum (w : MonicWeight k ℂ)
    (r : ℕ) (hr : 0 < r) :
    GradedEulerProduct.powerSumFamily (primeDegree k) (monicGradedFinite k)
        (primeWeight k w) r = closedPointPowerSum w r := by
  letI := monicGradedFinite k r
  change GradedEulerProduct.powerSum (primeDegree k) (primeWeight k w) r = _
  unfold GradedEulerProduct.powerSum
  letI := GradedEulerProduct.atomPowerFintype (primeDegree k) r
  calc
    (∑ x : GradedEulerProduct.AtomPowerIndex (primeDegree k) r,
        (primeDegree k x.1.1 : ℂ) * primeWeight k w x.1.1 ^ x.1.2) =
      ∑ x : DivisorPrimeIndex k r,
        (x.1.1 : ℂ) * exactPrimeWeight k w x.2 ^ (r / x.1.1) := by
      apply Fintype.sum_equiv (atomPowerDivisorEquiv k r hr)
      rintro ⟨⟨p, h⟩, _, hpow⟩
      have hexp : h = r / primeDegree k p := by
        calc
          h = (h * primeDegree k p) / primeDegree k p :=
            (Nat.mul_div_left h (primeDegree_pos k p)).symm
          _ = r / primeDegree k p := congrArg
            (fun n ↦ n / primeDegree k p) hpow
      change (primeDegree k p : ℂ) * primeWeight k w p ^ h =
        (primeDegree k p : ℂ) * primeWeight k w p ^ (r / primeDegree k p)
      rw [hexp]
    _ = closedPointPowerSum w r := by
      rw [Fintype.sum_sigma]
      unfold closedPointPowerSum
      rw [show (Finset.univ : Finset {e : ℕ // e ∈ r.divisors}) =
          r.divisors.attach from Finset.univ_eq_attach _]
      calc
        (∑ e ∈ r.divisors.attach,
            ∑ p : MonicIrreducibleOfDegree k e.1,
              (e.1 : ℂ) * exactPrimeWeight k w p ^ (r / e.1)) =
          ∑ e ∈ r.divisors,
            ∑ p : MonicIrreducibleOfDegree k e,
              (e : ℂ) * exactPrimeWeight k w p ^ (r / e) :=
          Finset.sum_attach r.divisors (fun e ↦
            ∑ p : MonicIrreducibleOfDegree k e,
              (e : ℂ) * exactPrimeWeight k w p ^ (r / e))
        _ = _ := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.mul_sum]

theorem gradedSumFamily_eq_degreeSum (w : MonicWeight k ℂ) (n : ℕ) :
    GradedEulerProduct.gradedSumFamily (primeDegree k) (monicGradedFinite k)
        (primeWeight k w) n = degreeSum w n := by
  unfold GradedEulerProduct.gradedSumFamily GradedEulerProduct.gradedSum
  change (∑ s : FactorMultisetsOfDegree k n,
    (s.1.map fun q ↦ w ⟨q.1, by change q.1.Monic; exact q.2.1⟩).prod) = _
  exact (degreeSum_eq_factorMultisets w n).symm

/-- The logarithmic derivative of the monic-weight series is the shifted closed-point series. -/
theorem closedPointSeries_derivative (w : MonicWeight k ℂ) :
    PowerSeries.derivative (series w) = series w * closedPointSeries w := by
  have h := GradedEulerProduct.global_weighted_derivative
    (primeDegree k) (primeDegree_pos k) (monicGradedFinite k) (primeWeight k w)
  have hA :
      GradedEulerProduct.gradedSumFamily (primeDegree k) (monicGradedFinite k)
          (primeWeight k w) = degreeSum w := by
    funext n
    exact gradedSumFamily_eq_degreeSum k w n
  have hB :
      (fun n ↦ GradedEulerProduct.powerSumFamily (primeDegree k)
        (monicGradedFinite k) (primeWeight k w) (n + 1)) =
      (fun n ↦ closedPointPowerSum w (n + 1)) := by
    funext n
    exact powerSumFamily_eq_closedPointPowerSum k w (n + 1) (by omega)
  rw [hA, hB] at h
  simpa [series, closedPointSeries] using h

end MonicSpecialization

end MonicWeight

/-- Reusable closed-point power identity for a multiplicative weight on monic polynomials.
If all exact-degree weight sums in degrees at least two vanish, every positive closed-point
power sum is the corresponding signed power of the degree-one sum. -/
theorem closedPoint_power_identity {k : Type u} [Field k] [Fintype k]
    (w : MonicWeight k ℂ)
    (hvanish : ∀ n, 2 ≤ n → MonicWeight.degreeSum w n = 0) :
    ∀ r, 0 < r →
      -MonicWeight.closedPointPowerSum w r = (-MonicWeight.degreeSum w 1) ^ r := by
  apply LanglandsFirstMainLemma.power_identity_of_derivative
  · exact MonicWeight.degreeSum_zero w
  · exact hvanish
  · simpa [MonicWeight.series, MonicWeight.closedPointSeries] using
      MonicWeight.closedPointSeries_derivative k w

end


end LanglandsFirstMainLemma
