/- GID: D5/S3/Combinatorics/Interpolation/AbrFullSecretNewtonSpan
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Interpolation/AbrFullSecretNewtonSpan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full permutation-by-colored-transversal consumer of coordinate-box ABR straightening. -/

import D5.S3.Combinatorics.Interpolation.AbrFilteredStraightening
import D5.S3.Combinatorics.Interpolation.ColoredTransversalNewtonSpanning

/-!
This module composes the coordinate-box form of ABR Corollary 3.4 with the
immutable colored-transversal Newton theorem.  Its function-space generators
are indexed by the complete permutation-by-transversal secret family; neither
the permutation coordinate nor unequal and singleton colored blocks are
discarded.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Interpolation.AbrFullSecretNewtonSpan

open scoped BigOperators
open MvPolynomial
open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S3.Combinatorics.Interpolation.AbrCoordinateBoxStraightening
open D5.S3.Combinatorics.Interpolation.AbrFilteredStraightening
open D5.S3.Combinatorics.Interpolation.ColoredTransversalNewtonSpanning

/-- The ordered root tuple of a full secret.  The permutation sends a tuple
position to the colored block supplying its root. -/
def secretRootPoint {n : Nat} (B : OrderedDisjointBlocks n)
    (sigma : Equiv.Perm (Fin n)) (beta : Transversal B) : Fin n -> Rat :=
  fun i => B.value (sigma i) (beta (sigma i))

/-- Permutation-by-transversal indices admitted by the joint descent/Newton
filtration. -/
abbrev FullSecretIndex {n : Nat} (B : OrderedDisjointBlocks n) (D : Nat) :=
  {z : Equiv.Perm (Fin n) × Transversal B //
    descents z.1 + newtonWeight z.2 <= D}

/-- A full-secret evaluation generator: a descent monomial in the permuted
roots times a colored Newton polynomial in the immutable coefficient point. -/
def fullSecretGenerator {n : Nat} (B : OrderedDisjointBlocks n) (D : Nat)
    (j : FullSecretIndex B D) :
    (Equiv.Perm (Fin n) × Transversal B) -> Rat :=
  fun secret =>
    MvPolynomial.eval (secretRootPoint B secret.1 secret.2)
        (descentMonomial j.1.1) *
      MvPolynomial.eval (coefficientPoint B secret.2)
        (newtonPolynomial B j.1.2)

/-- Every polynomial supported in the coordinate `D`-box has its complete
permutation-by-colored-transversal evaluation function in the span of the
jointly filtered descent/Newton generators.  Span scalars are independent of
both secret coordinates. -/
theorem coordinateBox_fullSecret_newton_mem_span
    {n : Nat} (hn : 0 < n) (B : OrderedDisjointBlocks n) (D : Nat)
    (P : MvPolynomial (Fin n) Rat)
    (hP : forall a, a ∈ P.support -> forall i, a i <= D) :
    (fun secret : Equiv.Perm (Fin n) × Transversal B =>
      MvPolynomial.eval (secretRootPoint B secret.1 secret.2) P) ∈
      Submodule.span Rat (Set.range (fullSecretGenerator B D)) := by
  classical
  have hEsymm (sigma : Equiv.Perm (Fin n)) (beta : Transversal B) (k : Fin n) :
      MvPolynomial.eval (secretRootPoint B sigma beta)
          (MvPolynomial.esymm (Fin n) Rat (k.val + 1)) =
        coefficientPoint B beta k := by
    let chosen : Fin n -> Rat := fun j => B.value j (beta j)
    calc
      MvPolynomial.eval (secretRootPoint B sigma beta)
          (MvPolynomial.esymm (Fin n) Rat (k.val + 1)) =
          MvPolynomial.eval (chosen ∘ sigma)
            (MvPolynomial.esymm (Fin n) Rat (k.val + 1)) := by rfl
      _ = MvPolynomial.eval chosen
          (MvPolynomial.rename sigma
            (MvPolynomial.esymm (Fin n) Rat (k.val + 1))) := by
            symm
            exact MvPolynomial.eval_rename sigma chosen _
      _ = MvPolynomial.eval chosen
          (MvPolynomial.esymm (Fin n) Rat (k.val + 1)) := by
            rw [MvPolynomial.esymm_isSymmetric (Fin n) Rat (k.val + 1) sigma]
      _ = coefficientPoint B beta k := by
            change MvPolynomial.aeval chosen
              (MvPolynomial.esymm (Fin n) Rat (k.val + 1)) = _
            rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
            rfl
  have hSubstitution (sigma : Equiv.Perm (Fin n)) (beta : Transversal B)
      (Q : MvPolynomial (Fin n) Rat) :
      MvPolynomial.eval (secretRootPoint B sigma beta) (esymmSubstitution Q) =
        MvPolynomial.eval (coefficientPoint B beta) Q := by
    unfold esymmSubstitution
    change MvPolynomial.aeval (secretRootPoint B sigma beta)
        (MvPolynomial.aeval
          (fun k : Fin n => MvPolynomial.esymm (Fin n) Rat (k.val + 1)) Q) =
      MvPolynomial.aeval (coefficientPoint B beta) Q
    rw [MvPolynomial.comp_aeval_apply]
    apply congrArg (fun x => MvPolynomial.aeval x Q)
    funext k
    exact hEsymm sigma beta k
  obtain ⟨Q, hQDegree, hQZero, hStraight⟩ :=
    coordinateBox_descent_straightening hn D P hP
  rw [hStraight]
  simp only [map_sum, map_mul]
  have hsumfun :
      (fun secret : Equiv.Perm (Fin n) × Transversal B =>
        ∑ pi, MvPolynomial.eval (secretRootPoint B secret.1 secret.2)
            (descentMonomial pi) *
          MvPolynomial.eval (secretRootPoint B secret.1 secret.2)
            (esymmSubstitution (Q pi))) =
      ∑ pi : Equiv.Perm (Fin n),
        fun secret : Equiv.Perm (Fin n) × Transversal B =>
          MvPolynomial.eval (secretRootPoint B secret.1 secret.2)
              (descentMonomial pi) *
            MvPolynomial.eval (secretRootPoint B secret.1 secret.2)
              (esymmSubstitution (Q pi)) := by
    funext secret
    simp
  rw [hsumfun]
  apply Submodule.sum_mem
  intro pi _
  by_cases hpi : descents pi <= D
  · obtain ⟨c, hc⟩ :=
      (colored_transversal_newton_spans hn B (D - descents pi)).2
        (Q pi) (hQDegree pi hpi)
    let index : {alpha : Transversal B // newtonWeight alpha <= D - descents pi} ->
        FullSecretIndex B D := fun alpha =>
      ⟨(pi, alpha.1), by
        change descents pi + newtonWeight alpha.1 <= D
        have hw := Nat.add_le_of_le_sub hpi alpha.2
        simpa [Nat.add_comm] using hw⟩
    have heq :
        (fun secret : Equiv.Perm (Fin n) × Transversal B =>
          MvPolynomial.eval (secretRootPoint B secret.1 secret.2)
            (descentMonomial pi) *
          MvPolynomial.eval (secretRootPoint B secret.1 secret.2)
            (esymmSubstitution (Q pi))) =
        ∑ alpha, c alpha • fullSecretGenerator B D (index alpha) := by
      funext secret
      rw [hSubstitution, hc secret.2]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        fullSecretGenerator, index]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro alpha _
      ring
    rw [heq]
    apply Submodule.sum_mem
    intro alpha _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_range_self (index alpha)
  · have hlt : D < descents pi := by omega
    rw [hQZero pi hlt]
    have hevalZero :
        (fun secret : Equiv.Perm (Fin n) × Transversal B =>
          MvPolynomial.eval (secretRootPoint B secret.1 secret.2)
              (descentMonomial pi) *
            MvPolynomial.eval (secretRootPoint B secret.1 secret.2)
              (esymmSubstitution 0)) = 0 := by
      funext secret
      simp [esymmSubstitution]
    rw [hevalZero]
    exact Submodule.zero_mem _

#print axioms coordinateBox_fullSecret_newton_mem_span

end D5.S3.Combinatorics.Interpolation.AbrFullSecretNewtonSpan
