/- GID: D5/S3/Combinatorics/Partitions/SpechtThreeRowVirtual
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtThreeRowVirtual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed ordered-colouring characters equal the three-variable alternant coefficient, with a sufficient actual-trace norm criterion. -/

/-
Source only; native elaboration, accepted axiom closure, proof-term liveness and
admission are not established. Unfinished audit:
https://github.com/the-omega-institute/trureturing/issues/24542.
The finite Cauchy coefficient identity and the same-shape mixed pairing are explicit
undischarged premises of the final theorem, not assertions of the ordinary HSW result.
utility none: arbitrary degrees and shapes, no finite certified instance.
-/
import D5.S3.Combinatorics.Partitions.SpechtThreeRowGram
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators
namespace TauCeti.ThreeRowGram
open _root_.Equiv _root_.Equiv.Perm Finset MvPolynomial

def staircase (i : Fin 3) : ℕ := 2 - (i : ℕ)
private def exponent (μ : Fin 3 → ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => μ i + staircase i
def permutedStaircase (σ : Perm (Fin 3)) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => staircase (σ i)

private theorem fixedColourings_eq_zero_of_negative {n : ℕ} {a : Fin 3 → ℤ}
    (i : Fin 3) (hi : a i < 0) (π : Perm (Fin n)) : fixedColourings a π = 0 := by
  rw [fixedColourings, card_eq_zero, filter_eq_empty_iff]
  intro f _ hf
  have h := hf.2 i
  have hn := Int.natCast_nonneg (#{x | f x = i})
  omega

theorem vandermonde_eq_signed_monomials :
    D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.vandermonde3 =
      ∑ σ : Perm (Fin 3), (sign σ : ℤ) • monomial (permutedStaircase σ) (1 : ℤ) := by
  let A : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℤ) :=
    fun j i => X i ^ staircase j
  have hd : A.det = D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.vandermonde3 := by
    rw [Matrix.det_fin_three]
    simp only [A, staircase, Fin.val_zero]
    norm_num
    rw [D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.vandermonde3]
    ring
  rw [← hd, Matrix.det_apply]
  apply sum_congr rfl
  intro σ _
  simp only [Units.smul_def]
  congr 1
  change (∏ i, (X i : MvPolynomial (Fin 3) ℤ) ^ (permutedStaircase σ) i) =
    monomial (permutedStaircase σ) (1 : ℤ)
  rw [← prod_X_pow_eq_monomial]
  exact (Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by
    rw [Finsupp.notMem_support_iff.mp hi, pow_zero]).symm

/-- The monomial coefficient matches the integer shifted margin, including its negative cases. -/
private theorem coeff_shifted (n : ℕ) (μ : Fin 3 → ℕ) (σ : Perm (Fin 3))
    (π : Perm (Fin n)) :
    (monomial (permutedStaircase σ) (1 : ℤ) * psumPart (Fin 3) ℤ π.partition).coeff
      (exponent μ) = (fixedColourings (shifted μ σ) π : ℤ) := by
  classical
  rw [coeff_monomial_mul']
  by_cases h : permutedStaircase σ ≤ exponent μ
  · rw [if_pos h, one_mul, coeff_psumPart_partition]
    congr 1
    apply congrArg Finset.card
    ext f
    simp only [mem_filter, mem_univ, true_and]
    apply and_congr_right'
    apply forall_congr'
    intro i
    have hi := i.isLt
    have hs := (σ i).isLt
    have hle : staircase (σ i) ≤ μ i + staircase i := h i
    change (#{x | f x = i}) = (μ i + staircase i) - staircase (σ i) ↔
      (#{x | f x = i} : ℤ) = (μ i : ℤ) - (i : ℕ) + (σ i : ℕ)
    unfold staircase at hle ⊢
    omega
  · rw [if_neg h]
    have hx : ∃ i, ¬ staircase (σ i) ≤ μ i + staircase i := by
      change ¬ ∀ i, staircase (σ i) ≤ μ i + staircase i at h
      exact not_forall.mp h
    obtain ⟨i, hi⟩ := hx
    have hneg : shifted μ σ i < 0 := by
      have h₁ := i.isLt
      have h₂ := (σ i).isLt
      unfold shifted staircase at *
      omega
    rw [fixedColourings_eq_zero_of_negative i hneg, Nat.cast_zero]

/-- The signed permutation character has exactly the existing HSW coefficient.
This does not yet identify it with the same-shape ordinary Specht trace. -/
theorem virtualCharacter_eq_frobChar {n : ℕ} (μ : Fin 3 → ℕ)
    (ρ : n.Partition) {π : Perm (Fin n)}
    (hπ : ConjClasses.mk π = partitionEquivConjClasses n ρ) {τ : List ℕ}
    (hτ : (τ : Multiset ℕ) = ρ.parts) :
    virtualCharacter n μ π =
      D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar μ τ := by
  rw [D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar,
    hsw_powerSumProd_eq_psumPart ρ hτ, psumPart_eq_psumPart_partition ℤ hπ,
    vandermonde_eq_signed_monomials, sum_mul, coeff_sum]
  change (∑ σ : Perm (Fin 3), _) = ∑ σ : Perm (Fin 3),
    ((sign σ : ℤ) • monomial (permutedStaircase σ) (1 : ℤ) *
      psumPart (Fin 3) ℤ π.partition).coeff (exponent μ)
  apply sum_congr rfl
  intro σ _
  rw [smul_mul_assoc, coeff_smul, smul_eq_mul, coeff_shifted]

private theorem spechtChar_inv {n : ℕ} (μ : n.Partition) (π : Perm (Fin n)) :
    spechtChar μ π⁻¹ = spechtChar μ π := by
  have h := spechtTrace_inv μ π
  change (spechtModuleℂ μ).character π⁻¹ = (spechtModuleℂ μ).character π at h
  simp only [character_spechtModuleℂ_intCast] at h
  exact_mod_cast h

private theorem sum_spechtChar_sq {n : ℕ} (μ : n.Partition) :
    ∑ π : Perm (Fin n), (spechtChar μ π) ^ 2 = (n.factorial : ℤ) := by
  have h := sum_spechtTrace_mul_spechtTrace_inv μ μ
  change (∑ π : Perm (Fin n),
    (spechtModuleℂ μ).character π * (spechtModuleℂ μ).character π⁻¹) = _ at h
  simp only [character_spechtModuleℂ_intCast, spechtChar_inv, if_pos rfl, ← pow_two] at h
  exact_mod_cast h

/-- Positive definiteness is used over Z through the integral actual character.
The two hypotheses are a finite contingency identity and an actual mixed pairing;
neither is the desired pointwise character identity. -/
private theorem spechtChar_eq_virtualCharacter_of_gram {n : ℕ} (μ : n.Partition)
    (r : Fin 3 → ℕ) (hgram : signedContingencyGram n r r = 1)
    (hmixed : (∑ π : Perm (Fin n), spechtChar μ π * virtualCharacter n r π) =
      (n.factorial : ℤ)) (π : Perm (Fin n)) :
    spechtChar μ π = virtualCharacter n r π := by
  have hs := sum_spechtChar_sq μ
  have ht := sum_virtualCharacter_mul n r r
  rw [hgram, mul_one] at ht
  have hzero : (∑ g : Perm (Fin n), (spechtChar μ g - virtualCharacter n r g) ^ 2) = 0 := by
    calc
      _ = (∑ g : Perm (Fin n), (spechtChar μ g) ^ 2) +
          (∑ g : Perm (Fin n), (virtualCharacter n r g) ^ 2) -
          2 * (∑ g : Perm (Fin n), spechtChar μ g * virtualCharacter n r g) := by
        simp only [sub_sq, sum_add_distrib, sum_sub_distrib, mul_sum]
        ring
      _ = 0 := by
        simp only [pow_two] at hs ⊢
        rw [hs, ht, hmixed]
        ring
  have hle : (spechtChar μ π - virtualCharacter n r π) ^ 2 ≤
      ∑ g : Perm (Fin n), (spechtChar μ g - virtualCharacter n r g) ^ 2 :=
    single_le_sum (fun g _ => sq_nonneg (spechtChar μ g - virtualCharacter n r g)) (mem_univ π)
  rw [hzero] at hle
  nlinarith [sq_nonneg (spechtChar μ π - virtualCharacter n r π)]

/-- A sufficient finite Gram criterion for the actual preserved complex Specht trace
and the exact existing coefficient, with full cycle partitions and no degree bound. -/
theorem ordinaryTrace_eq_frobChar_of_gram {n : ℕ} (μ ρ : n.Partition)
    (r : Fin 3 → ℕ) (hgram : signedContingencyGram n r r = 1)
    (hmixed : (∑ g : Perm (Fin n), spechtChar μ g * virtualCharacter n r g) =
      (n.factorial : ℤ)) {π : Perm (Fin n)}
    (hπ : ConjClasses.mk π = partitionEquivConjClasses n ρ) {τ : List ℕ}
    (hτ : (τ : Multiset ℕ) = ρ.parts) :
    LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) =
      (D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar r τ : ℂ) := by
  change (spechtModuleℂ μ).character π = _
  rw [character_spechtModuleℂ_intCast,
    spechtChar_eq_virtualCharacter_of_gram μ r hgram hmixed π,
    virtualCharacter_eq_frobChar r ρ hπ hτ]

end TauCeti.ThreeRowGram
end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
