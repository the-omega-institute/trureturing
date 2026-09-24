/- GID: D5/S3/Combinatorics/Interpolation/AbrFilteredStraightening
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Interpolation/AbrFilteredStraightening
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coordinate-box filtered ABR descent straightening on actual multivariate polynomials. -/

import D5.S3.Combinatorics.Interpolation.AbrIteratedTriangularity

/-!
This module carries out the finite triangular elimination from ABR Lemma 3.3
and Corollary 3.4.  The filtration is the coordinate box: every exponent is
bounded by `D`.  The coefficient polynomial has ordinary total degree at most
`D - descents pi`; the total degree of the descent monomial is not used as the
filter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Interpolation.AbrFilteredStraightening

open scoped BigOperators
open MvPolynomial
open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S3.Combinatorics.Interpolation.AbrCoordinateBoxStraightening
open D5.S3.Combinatorics.Interpolation.AbrResidualPartition
open D5.S3.Combinatorics.Interpolation.AbrIteratedTriangularity

/-- Every polynomial in the coordinate `D`-box is an exact sum of descent
monomials times elementary-symmetric substitutions.  The coefficient bound is
uniform in the permutation, and permutations outside the descent guard carry
the zero coefficient polynomial. -/
theorem coordinateBox_descent_straightening
    {n : Nat} (hn : 0 < n) (D : Nat) (P : MvPolynomial (Fin n) Rat)
    (hP : ∀ a ∈ P.support, ∀ i, a i ≤ D) :
    ∃ Q : Equiv.Perm (Fin n) → MvPolynomial (Fin n) Rat,
      (∀ pi, descents pi ≤ D → (Q pi).totalDegree ≤ D - descents pi) ∧
      (∀ pi, D < descents pi → Q pi = 0) ∧
      P = ∑ pi, descentMonomial pi * esymmSubstitution (Q pi) := by
  classical
  let Represents (R : MvPolynomial (Fin n) Rat) : Prop :=
    ∃ Q : Equiv.Perm (Fin n) → MvPolynomial (Fin n) Rat,
      (∀ pi, descents pi ≤ D → (Q pi).totalDegree ≤ D - descents pi) ∧
      (∀ pi, D < descents pi → Q pi = 0) ∧
      R = ∑ pi, descentMonomial pi * esymmSubstitution (Q pi)
  have hzero : Represents 0 := by
    refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro pi _
      simp
    · intro pi _
      rfl
    · simp
  have hadd {R S : MvPolynomial (Fin n) Rat}
      (hR : Represents R) (hS : Represents S) : Represents (R + S) := by
    obtain ⟨QR, hQRDegree, hQRZero, hReq⟩ := hR
    obtain ⟨QS, hQSDegree, hQSZero, hSeq⟩ := hS
    refine ⟨fun pi => QR pi + QS pi, ?_, ?_, ?_⟩
    · intro pi hpi
      exact (totalDegree_add _ _).trans (max_le (hQRDegree pi hpi) (hQSDegree pi hpi))
    · intro pi hpi
      simp [hQRZero pi hpi, hQSZero pi hpi]
    · rw [hReq, hSeq, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro pi _
      rw [map_add, mul_add]
  have hsmul (c : Rat) {R : MvPolynomial (Fin n) Rat}
      (hR : Represents R) : Represents (c • R) := by
    obtain ⟨Q, hQDegree, hQZero, hReq⟩ := hR
    refine ⟨fun pi => C c * Q pi, ?_, ?_, ?_⟩
    · intro pi hpi
      exact (totalDegree_mul _ _).trans (by
        rw [totalDegree_C]
        simpa using hQDegree pi hpi)
    · intro pi hpi
      simp [hQZero pi hpi]
    · rw [hReq, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro pi _
      simp [esymmSubstitution, smul_eq_C_mul]
      ring
  let BoxExponent := {a : Fin n →₀ Nat // ∀ i, a i ≤ D}
  let boxCode : BoxExponent → (Fin n → Fin (D + 1)) := fun a i =>
    ⟨a.1 i, by have := a.2 i; omega⟩
  have boxCode_injective : Function.Injective boxCode := by
    intro a b hab
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact congrArg (fun f => (f i).val) hab
  letI : Finite BoxExponent := Finite.of_injective boxCode boxCode_injective
  let lower : BoxExponent → BoxExponent → Prop := fun a b => AbrLower a.1 b.1
  have lower_trans : Transitive lower := by
    intro a b c hab hbc
    exact abrLower_trans hab hbc
  have lower_irrefl : Irreflexive lower := by
    intro a ha
    rcases ha with ha | ha
    · exact ha.2 ha.1
    · exact (lt_irrefl _ ha.2).elim
  letI : IsTrans BoxExponent lower := ⟨lower_trans⟩
  letI : Std.Irrefl lower := ⟨lower_irrefl⟩
  have lower_wf : WellFounded lower :=
    Finite.wellFounded_of_trans_of_irrefl lower
  have hMonomial : ∀ a : BoxExponent, Represents (monomial a.1 (1 : Rat)) := by
    intro a
    induction a using lower_wf.induction with
    | h a ih =>
        have hMax : maxExponent a.1 ≤ D := by
          unfold maxExponent
          apply Finset.sup_le
          intro i _
          exact a.2 i
        have hDesc : descents (indexPerm a.1) ≤ D := by
          apply le_trans _ hMax
          rw [maxExponent_eq_at_zero hn]
          rw [← suffixHeight_zero hn]
          exact suffixHeight_indexPerm_le_exponent a.1 ⟨0, hn⟩
        have hCoeffDegree :
            (abrCoefficientPolynomial a.1).totalDegree ≤
              D - descents (indexPerm a.1) := by
          apply (totalDegree_abrCoefficientPolynomial_le a.1).trans
          rw [residualDepth_eq_maxExponent_sub_descents hn]
          omega
        have hBasisRep : Represents (abrBasis a.1) := by
          let target := indexPerm a.1
          let QA : Equiv.Perm (Fin n) → MvPolynomial (Fin n) Rat := fun pi =>
            if pi = target then abrCoefficientPolynomial a.1 else 0
          refine ⟨QA, ?_, ?_, ?_⟩
          · intro pi hpi
            by_cases hp : pi = target
            · subst pi
              simpa [QA, target] using hCoeffDegree
            · simp [QA, hp]
          · intro pi hpi
            by_cases hp : pi = target
            · subst pi
              exact (not_lt_of_ge hDesc hpi).elim
            · simp [QA, hp]
          · rw [Finset.sum_eq_single target]
            · simp [QA, target, abrBasis_eq_descent_mul_esymmSubstitution]
            · intro pi _ hne
              simp [QA, hne]
            · simp
        let remainder : MvPolynomial (Fin n) Rat :=
          ∑ b ∈ (abrBasis a.1).support.erase a.1,
            monomial b (coeff b (abrBasis a.1))
        have hRemainderRep : Represents remainder := by
          unfold remainder
          apply Finset.sum_induction _ Represents
          · intro R S hR hS
            exact hadd hR hS
          · exact hzero
          · intro b hb
            rw [Finset.mem_erase] at hb
            have hbBox : ∀ i, b i ≤ D := by
              intro i
              exact (abrBasis_support_coordinate_le hn a.1 b hb.2 i).trans hMax
            let bBox : BoxExponent := ⟨b, hbBox⟩
            have hba : lower bBox a := by
              have htri := (abrBasis_triangular a.1 b).2 hb.2
              exact htri.resolve_left hb.1
            have hLowerRep := ih bBox hba
            have hscaled := hsmul (coeff b (abrBasis a.1)) hLowerRep
            simpa [smul_eq_C_mul, C_mul_monomial] using hscaled
        have hdecomp : abrBasis a.1 = monomial a.1 1 + remainder := by
          rw [(abrBasis a.1).as_sum]
          have haSupport : a.1 ∈ (abrBasis a.1).support := by
            rw [MvPolynomial.mem_support_iff, (abrBasis_triangular a.1 a.1).1]
            exact one_ne_zero
          rw [← Finset.add_sum_erase _ _ haSupport]
          rw [(abrBasis_triangular a.1 a.1).1]
        have hnegRemainder := hsmul (-1) hRemainderRep
        have hcombined := hadd hBasisRep hnegRemainder
        have heq : abrBasis a.1 + (-1 : Rat) • remainder = monomial a.1 1 := by
          rw [hdecomp]
          simp
        exact heq ▸ hcombined
  rw [P.as_sum]
  apply Finset.sum_induction _ Represents
  · intro R S hR hS
    exact hadd hR hS
  · exact hzero
  · intro a ha
    let aBox : BoxExponent := ⟨a, hP a ha⟩
    have hrep := hsmul (coeff a P) (hMonomial aBox)
    simpa [smul_eq_C_mul, C_mul_monomial] using hrep

#print axioms coordinateBox_descent_straightening

end D5.S3.Combinatorics.Interpolation.AbrFilteredStraightening
