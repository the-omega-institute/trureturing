/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverSixteenPairSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sixteen independent fractional oscillator zero modes, their exact point spectrum and ground line. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverGroundSpectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
The moving oscillator zero mode for the sixteen complementary pairs in the
order-three P48q calculation. Each pair carries the two nonzero residue grids,
at frequencies `(k.val + 1) / 3`. The opposite-frequency Heisenberg pairing
uses Bakalov and Kac, *Twisted Modules over Lattice Vertex Algebras*,
arXiv:math/0402315v1, (4.23), as in `ThirdCoverComplement`.

The oscillator energy comes from the explicit native Fock monomial calculation
in `PolynomialFockLZeroSpectrum.lZero_spectrum`. The ordinary vacuum slice of
the cover splitting gives `ThirdCoverGroundSpectrum.fractionalVirasoro_zero_monomial`,
with the native energy divided by three and the cover shift `1 / 9` per pair.
Here that calculation acts on each independent moving polynomial factor.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverSixteenPairSpectrum

open MvPolynomial Module.End
open ThirdCoverIntegerFactor ThirdCoverComplement ThirdCoverGroundSpectrum

/-- The first coordinate indexes the dual lattice pair. The second indexes
the native oscillator frequencies in the two nonzero residue classes. -/
abbrev MovingVariable := Fin 16 × Complement
abbrev MovingFock := MvPolynomial MovingVariable ℂ
abbrev Occupation := MovingVariable →₀ ℕ

abbrev OtherVariable (i : Fin 16) := {x : MovingVariable // x.1 ≠ i}

/-- Restrict an occupation vector to variables of the given lattice pair. -/
def pairOccupation (i : Fin 16) (d : Occupation) : Complement →₀ ℕ :=
  d.curry i

private def otherOccupation (i : Fin 16) (d : Occupation) : Occupation :=
  d.filter (fun x => x.1 ≠ i)

private theorem pairVar_injective (i : Fin 16) :
    Function.Injective (Prod.mk i : Complement → MovingVariable) :=
  fun _ _ h => congrArg Prod.snd h

private theorem occupation_split (i : Fin 16) (d : Occupation) :
    (pairOccupation i d).mapDomain (Prod.mk i) + otherOccupation i d = d := by
  apply Finsupp.ext
  rintro ⟨j, k⟩
  rw [Finsupp.add_apply]
  by_cases h : j = i
  · subst j
    rw [Finsupp.mapDomain_apply_of_injective (pairVar_injective i)]
    simp [pairOccupation, otherOccupation]
  · have hn : (j, k) ∉ Set.range (Prod.mk i : Complement → MovingVariable) := by
      rintro ⟨l, hl⟩
      exact h (congrArg Prod.fst hl).symm
    rw [Finsupp.mapDomain_of_notMem_range _ _ hn]
    simp [otherOccupation, h]

private theorem pairOccupation_separated (i : Fin 16) (d : Complement →₀ ℕ)
    (e : OtherVariable i →₀ ℕ) :
    pairOccupation i (d.mapDomain (Prod.mk i) + e.mapDomain Subtype.val) = d := by
  apply Finsupp.ext
  intro k
  have hn : (i, k) ∉ Set.range (Subtype.val : OtherVariable i → MovingVariable) := by
    rintro ⟨x, hx⟩
    exact x.property (congrArg Prod.fst hx)
  change (d.mapDomain (Prod.mk i) + e.mapDomain Subtype.val) (i, k) = d k
  rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective (pairVar_injective i),
    Finsupp.mapDomain_of_notMem_range _ _ hn, add_zero]

/-- Split each basis monomial into two factors, apply the actual one-pair
fractional zero mode to the selected factor, and multiply them back together. -/
def pairLZero (i : Fin 16) : Module.End ℂ MovingFock :=
  (basisMonomials MovingVariable ℂ).constr ℂ fun d =>
    rename (Prod.mk i) (fractionalVirasoro 0 (monomial (pairOccupation i d) 1)) *
      monomial (otherOccupation i d) 1

theorem pairLZero_monomial (i : Fin 16) (d : Occupation) (a : ℂ) :
    pairLZero i (monomial d a) =
      ((1 / 9 : ℂ) + (occupationEnergy (pairOccupation i d) : ℂ) / 3) • monomial d a := by
  have hunit : pairLZero i (monomial d 1) =
      ((1 / 9 : ℂ) + (occupationEnergy (pairOccupation i d) : ℂ) / 3) • monomial d 1 := by
    change pairLZero i (basisMonomials MovingVariable ℂ d) = _
    rw [pairLZero, Module.Basis.constr_basis, fractionalVirasoro_zero_monomial, map_smul,
      smul_mul_assoc, rename_monomial, monomial_mul_monomial, mul_one, occupation_split]
  have hm : monomial d a = a • monomial d (1 : ℂ) := by
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, hunit,
    smul_comm a ((1 / 9 : ℂ) + (occupationEnergy (pairOccupation i d) : ℂ) / 3)]

/-- On a product of arbitrary polynomials in the chosen and remaining
variables, the summand acts as the actual fractional zero mode on the
chosen factor and the identity on the remaining factor. -/
theorem pairLZero_separated (i : Fin 16) (Q : ComplementFock)
    (R : MvPolynomial (OtherVariable i) ℂ) :
    pairLZero i (rename (Prod.mk i) Q * rename Subtype.val R) =
      rename (Prod.mk i) (fractionalVirasoro 0 Q) * rename Subtype.val R := by
  induction Q using MvPolynomial.induction_on' with
  | monomial d a =>
    induction R using MvPolynomial.induction_on' with
    | monomial e b =>
      simp only [fractionalVirasoro_zero_monomial, map_smul, smul_mul_assoc,
        rename_monomial, monomial_mul_monomial, pairLZero_monomial, pairOccupation_separated]
    | add R S hR hS =>
      simp only [map_add, mul_add, hR, hS]
  | add P Q hP hQ =>
    simp only [map_add, add_mul, hP, hQ]

/-- The moving part of the oscillator zero mode is the sum of the
sixteen lifted one-pair zero modes. -/
def fractionalLZero : Module.End ℂ MovingFock := ∑ i : Fin 16, pairLZero i

/-- The total frequency before dividing native cover indices by three. -/
def totalOccupationEnergy (d : Occupation) : ℕ :=
  d.sum fun k e => (k.2.val + 1) * e

theorem sum_pairOccupationEnergy (d : Occupation) :
    (∑ i : Fin 16, occupationEnergy (pairOccupation i d)) = totalOccupationEnergy d := by
  calc
    _ = d.curry.sum (fun _ e => occupationEnergy e) :=
      (Finsupp.sum_fintype d.curry (fun _ e => occupationEnergy e)
        (fun _ => by simp [occupationEnergy])).symm
    _ = _ := Finsupp.sum_curry_index d (fun _ k e => (k.val + 1) * e)

@[simp] theorem totalOccupationEnergy_eq_zero_iff (d : Occupation) :
    totalOccupationEnergy d = 0 ↔ d = 0 := by
  constructor
  · intro hd
    apply Finsupp.ext
    intro k
    change d k = 0
    by_contra hk
    have hle : (k.2.val + 1) * d k ≤ totalOccupationEnergy d :=
      Finset.single_le_sum (f := fun j : MovingVariable => (j.2.val + 1) * d j)
        (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hk)
    have hpos := Nat.mul_pos (Nat.succ_pos k.2.val) (Nat.pos_of_ne_zero hk)
    rw [hd] at hle
    exact Nat.not_lt_of_ge hle hpos
  · rintro rfl
    simp [totalOccupationEnergy]

/-- Every occupation monomial has the sum of the sixteen one-pair weights. -/
theorem fractionalLZero_monomial (d : Occupation) (a : ℂ) :
    fractionalLZero (monomial d a) =
      ((16 / 9 : ℂ) + (totalOccupationEnergy d : ℂ) / 3) • monomial d a := by
  have hshift : (∑ _i : Fin 16, (1 / 9 : ℂ)) = 16 / 9 := by
    simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have henergy :
      (∑ i : Fin 16, (occupationEnergy (pairOccupation i d) : ℂ) / 3) =
        (totalOccupationEnergy d : ℂ) / 3 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, sum_pairOccupationEnergy]
  rw [fractionalLZero, LinearMap.sum_apply]
  simp_rw [pairLZero_monomial]
  rw [← Finset.sum_smul, Finset.sum_add_distrib, hshift, henergy]

/-- The monomial calculation determines every coefficient on the full Fock space. -/
theorem fractionalLZero_coeff (P : MovingFock) (d : Occupation) :
    (fractionalLZero P).coeff d =
      ((16 / 9 : ℂ) + (totalOccupationEnergy d : ℂ) / 3) * P.coeff d := by
  classical
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, coeff_sum, fractionalLZero_monomial, coeff_smul, smul_eq_mul,
    coeff_monomial, mul_ite, mul_zero, Finset.sum_ite_eq']
  by_cases hd : d ∈ P.support
  · rw [ite_eq_left hd]
  · rw [ite_eq_right hd, notMem_support_iff.mp hd, mul_zero]

private theorem eigenvalue_of_nonzero_coeff {P : MovingFock} {a : ℂ}
    (hP : fractionalLZero P = a • P) {d : Occupation} (hd : P.coeff d ≠ 0) :
    (16 / 9 : ℂ) + (totalOccupationEnergy d : ℂ) / 3 = a := by
  have h := congrArg (fun Q : MovingFock => Q.coeff d) hP
  change (fractionalLZero P).coeff d = (a • P).coeff d at h
  rw [fractionalLZero_coeff, coeff_smul, smul_eq_mul] at h
  exact mul_right_cancel₀ hd h

theorem fractionalLZero_eigenvalue {P : MovingFock} {a : ℂ} (hP : P ≠ 0)
    (heig : fractionalLZero P = a • P) :
    ∃ n : ℕ, a = (16 / 9 : ℂ) + (n : ℂ) / 3 := by
  classical
  obtain ⟨d, hd⟩ : ∃ d : Occupation, P.coeff d ≠ 0 := by
    by_contra! h
    apply hP
    apply MvPolynomial.ext
    intro d
    simpa using h d
  exact ⟨totalOccupationEnergy d, (eigenvalue_of_nonzero_coeff heig hd).symm⟩

/-- The point spectrum consists exactly of the nonnegative integer shifts by thirds of `16 / 9`. -/
theorem fractionalLZero_eigenvalue_iff (a : ℂ) :
    (∃ P : MovingFock, P ≠ 0 ∧ fractionalLZero P = a • P) ↔
      ∃ n : ℕ, a = (16 / 9 : ℂ) + (n : ℂ) / 3 := by
  constructor
  · rintro ⟨P, hP, heig⟩
    exact fractionalLZero_eigenvalue hP heig
  · rintro ⟨n, rfl⟩
    let d : Occupation := Finsupp.single (0, ⟨0, by decide⟩) n
    refine ⟨monomial d 1, ?_, ?_⟩
    · exact fun h => one_ne_zero (monomial_eq_zero.mp h)
    · have hd : totalOccupationEnergy d = n := by
        simp [d, totalOccupationEnergy, Finsupp.sum_single_index]
      rw [fractionalLZero_monomial, hd]

private theorem fractionalLZero_one : fractionalLZero (1 : MovingFock) = (16 / 9 : ℂ) • 1 := by
  simpa [totalOccupationEnergy] using fractionalLZero_monomial (0 : Occupation) (1 : ℂ)

/-- Only the zero occupation vector can occur at the vacuum weight. -/
theorem fractionalLZero_ground_eigenspace :
    fractionalLZero.eigenspace (16 / 9 : ℂ) =
      Submodule.span ℂ ({(1 : MovingFock)} : Set MovingFock) := by
  apply le_antisymm
  · intro P hP
    have heig := mem_eigenspace_iff.mp hP
    have hm : P = monomial 0 (P.coeff 0) := by
      apply eq_monomial_of_support_subset_singleton
      intro d hd
      have hvalue := eigenvalue_of_nonzero_coeff heig (mem_support_iff.mp hd)
      have hcast : (totalOccupationEnergy d : ℂ) = 0 := by
        linear_combination 3 * hvalue
      have henergy : totalOccupationEnergy d = 0 := by exact_mod_cast hcast
      exact Set.mem_singleton_iff.mpr ((totalOccupationEnergy_eq_zero_iff d).mp henergy)
    refine Submodule.mem_span_singleton.mpr ⟨P.coeff 0, ?_⟩
    simpa only [monomial_zero', C_eq_smul_one] using hm.symm
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr
      (mem_eigenspace_iff.mpr fractionalLZero_one)

theorem fractionalLZero_ground_finrank :
    Module.finrank ℂ (fractionalLZero.eigenspace (16 / 9 : ℂ)) = 1 := by
  rw [fractionalLZero_ground_eigenspace]
  exact finrank_span_singleton (one_ne_zero : (1 : MovingFock) ≠ 0)

theorem fractionalLZero_minimum :
    IsLeast {x : ℝ | ∃ P : MovingFock, P ≠ 0 ∧ fractionalLZero P = (x : ℂ) • P}
      (16 / 9) := by
  refine ⟨⟨1, one_ne_zero, ?_⟩, ?_⟩
  · simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using fractionalLZero_one
  · rintro x ⟨P, hP, heig⟩
    obtain ⟨n, hn⟩ := fractionalLZero_eigenvalue hP heig
    have hx := congrArg Complex.re hn
    simp only [Complex.ofReal_re, Complex.add_re, Complex.div_ofNat_re, Complex.re_ofNat,
      Complex.natCast_re] at hx
    change (16 / 9 : ℝ) ≤ x
    rw [hx]
    exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg n) (by norm_num))

#print axioms pairLZero_monomial
#print axioms pairLZero_separated
#print axioms fractionalLZero_monomial
#print axioms fractionalLZero_coeff
#print axioms fractionalLZero_eigenvalue
#print axioms fractionalLZero_eigenvalue_iff
#print axioms fractionalLZero_minimum
#print axioms fractionalLZero_ground_eigenspace
#print axioms fractionalLZero_ground_finrank

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverSixteenPairSpectrum
