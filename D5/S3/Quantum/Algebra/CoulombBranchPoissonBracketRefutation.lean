/- GID: D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.claim; result=D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.result; claim=D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.claim
   digest: Jacobi and reducedness obstruct the proposed E6 and truck spinor Poisson brackets. -/

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation

/-- A complex bilinear, antisymmetric biderivation satisfying the Jacobi identity. -/
def IsPoissonBracket {R : Type*} [CommRing R] [Algebra ℂ R] (br : R → R → R) : Prop :=
  (∀ a b c, br (a + b) c = br a c + br b c) ∧
  (∀ (c : ℂ) a b, br (c • a) b = c • br a b) ∧
  (∀ a b c, br a (b + c) = br a b + br a c) ∧
  (∀ (c : ℂ) a b, br a (c • b) = c • br a b) ∧
  (∀ a b, br a b = -br b a) ∧
  (∀ a b c, br a (b * c) = br a b * c + b * br a c) ∧
  (∀ a b c, br a (br b c) + br b (br c a) + br c (br a b) = 0)

/-- Uniform diagonal mixed spinor brackets, weights, and vanishing equal-charge brackets. -/
def SpinorBrackets {R : Type*} [CommRing R] {N : ℕ}
    (br : R → R → R) (h : R) (sUp sDn : Fin N → R) (e : ℕ) : Prop :=
  (∀ α, br h (sUp α) = sUp α) ∧
  (∀ α, br h (sDn α) = -sDn α) ∧
  (∀ α β, br (sUp α) (sDn β) = if α = β then h ^ e else 0) ∧
  (∀ α β, br (sUp α) (sUp β) = 0) ∧
  (∀ α β, br (sDn α) (sDn β) = 0)

/-- The proposed brackets for every admissible member of the second E6 family. -/
def ConjE6 : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∃ (R : Type) (ringR : CommRing R),
    letI := ringR
    ∃ algR : Algebra ℂ R,
      letI := algR
      IsReduced R ∧ ∃ (br : R → R → R) (h : R) (sUp sDn : Fin (2 ^ (2 * n)) → R),
        IsPoissonBracket br ∧ h ≠ 0 ∧ SpinorBrackets br h sUp sDn (n - 1)

/-- The proposed brackets for every admissible truck rank and positive multiplicity. -/
def ConjTruck : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ σ : ℕ, 1 ≤ σ → ∃ (R : Type) (ringR : CommRing R),
    letI := ringR
    ∃ algR : Algebra ℂ R,
      letI := algR
      IsReduced R ∧ ∃ (br : R → R → R) (h : R) (sUp sDn : Fin (2 ^ (2 * n)) → R),
        IsPoissonBracket br ∧ h ≠ 0 ∧ SpinorBrackets br h sUp sDn (n + σ - 1)

/-- At least one of the two proposed families exists in reduced complex algebras. -/
def claim : Prop := ConjE6 ∨ ConjTruck

private def hamiltonian {R : Type*} [CommRing R] [Algebra ℂ R]
    (br : R → R → R) (hp : IsPoissonBracket br) (a : R) : Derivation ℂ R R := by
  sorry

private lemma bracket_pow {R : Type*} [CommRing R] [Algebra ℂ R]
    (br : R → R → R) (hp : IsPoissonBracket br) (a h : R) (k : ℕ) :
    br a (h ^ k) = k • (h ^ (k - 1) * br a h) := by
  sorry

private lemma bracket_mul_left {R : Type*} [CommRing R] [Algebra ℂ R]
    (br : R → R → R) (hp : IsPoissonBracket br) (a b c : R) :
    br (a * b) c = a * br b c + br a c * b := by
  sorry

private lemma bracket_forces_zero {R : Type*} [CommRing R] [Algebra ℂ R] [IsReduced R]
    (br : R → R → R) (hp : IsPoissonBracket br) (e : ℕ) (he : 1 ≤ e)
    (h x y z w : R) (hhx : br h x = x) (hhy : br h y = -y)
    (hxy : br x y = h ^ e) (hzw : br z w = h ^ e)
    (hxw : br x w = 0) (hxz : br x z = 0) : h = 0 := by
  sorry

private lemma spinor_forces_zero {R : Type*} [CommRing R] [Algebra ℂ R] [IsReduced R]
    {N : ℕ} (hN : 2 ≤ N) (br : R → R → R) (hp : IsPoissonBracket br)
    (h : R) (sUp sDn : Fin N → R) (e : ℕ) (he : 1 ≤ e)
    (hs : SpinorBrackets br h sUp sDn e) : h = 0 := by
  sorry

private lemma not_conjE6 : ¬ ConjE6 := by
  sorry

private lemma not_conjTruck : ¬ ConjTruck := by
  sorry

/-- Neither proposed family of spinor brackets exists in reduced complex algebras. -/
theorem result : ¬ claim := by
  intro hc
  rcases hc with hc | hc
  · exact not_conjE6 hc
  · exact not_conjTruck hc

end D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation
