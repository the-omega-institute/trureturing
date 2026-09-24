/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ParityRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.claim; result=D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.result; claim=D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.claim
   digest: The actual independence polynomial of GP(3,1) refutes the literal parity conjecture. -/

import D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation

open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open scoped BigOperators

/-- The two layers are the outer and inner vertices; indices are taken modulo n.
The source domain is imposed in `claim`, not by changing the graph construction. -/
def gp (n k : ℕ) : SimpleGraph (Bool × Fin n) :=
  SimpleGraph.fromRel fun a b =>
    (a.1 = false ∧ b.1 = false ∧ b.2.val = (a.2.val + 1) % n) ∨
    (a.1 = true ∧ b.1 = true ∧ b.2.val = (a.2.val + k) % n) ∨
    (a.1 = false ∧ b.1 = true ∧ a.2 = b.2)

instance gpDecidableAdj (n k : ℕ) : DecidableRel (gp n k).Adj := by
  unfold gp
  infer_instance

/-- Pandey's Parity Conjecture 4.1 on the full domain of Definition 2.1.
For natural parameters, `2*k < n` is exactly `n ≥ 2*k+1` and `k < n/2`
with the latter division interpreted over the rationals, as in the source. -/
def claim : Prop :=
  ∀ n k : ℕ, 3 ≤ n → 1 ≤ k → 2 * k < n →
    ((∀ z : ℂ, Polynomial.eval₂ (Int.castRingHom ℂ) z
        (independencePolynomial (gp n k) Finset.univ) = 0 → z.im = 0) ↔ Even k)

/-- GP(3,1) has real-rooted independence polynomial 1+6X+6X² although 1 is odd. -/
theorem result : ¬ claim := by
  intro h
  have hconfigs : configurations (gp 3 1) Finset.univ =
      ({∅,
        {(false, 0)}, {(false, 1)}, {(false, 2)},
        {(true, 0)}, {(true, 1)}, {(true, 2)},
        {(false, 0), (true, 1)}, {(false, 0), (true, 2)},
        {(false, 1), (true, 0)}, {(false, 1), (true, 2)},
        {(false, 2), (true, 0)}, {(false, 2), (true, 1)}} :
        Finset (Finset (Bool × Fin 3))) := by decide
  have heval (z : ℂ) : Polynomial.eval₂ (Int.castRingHom ℂ) z
      (independencePolynomial (gp 3 1) Finset.univ) = 1 + 6 * z + 6 * z ^ 2 := by
    rw [independencePolynomial_eval, partition, hconfigs]
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton,
      Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty]
    ring
  have hreal : ∀ z : ℂ, Polynomial.eval₂ (Int.castRingHom ℂ) z
      (independencePolynomial (gp 3 1) Finset.univ) = 0 → z.im = 0 := by
    intro z hz
    rw [heval] at hz
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp [Complex.mul_re, Complex.mul_im, pow_two] at hre him
    by_contra hb
    have hfactor : 6 * z.im * (1 + 2 * z.re) = 0 := by nlinarith [him]
    have ha : z.re = -(1 / 2 : ℝ) := by
      have := (mul_eq_zero.mp hfactor).resolve_left (mul_ne_zero (by norm_num) hb)
      linarith
    rw [ha] at hre
    nlinarith [sq_nonneg z.im]
  have heven : Even (1 : ℕ) := (h 3 1 (by decide) (by decide) (by decide)).mp hreal
  norm_num at heven

#print axioms result

end D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation
