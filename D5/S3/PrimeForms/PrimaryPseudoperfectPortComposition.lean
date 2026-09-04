/- GID: D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition
   generality: G
   mirror-B: D5/B/S3/PrimeForms/PrimaryPseudoperfectPortComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Coprime Leibniz, port-composition, and primary-pseudoperfect extension laws. -/

import D5.S3.PrimeForms.PrimaryPseudoperfectPorts

namespace D5.S3.PrimeForms.PrimaryPseudoperfectPortComposition

open D5.S3.PrimeForms.PrimaryPseudoperfectPorts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The natural-number residual transported through a coprime factor. -/
def portDelta (R c B : Nat) : Nat :=
  c * B - R * squarefreeDeriv B

private theorem mul_div_prime_factor_left
    {A B p : Nat} (hpA : p ∣ A) : A * B / p = (A / p) * B := by
  rw [mul_comm A B, Nat.mul_div_assoc B hpA, mul_comm]

private theorem mul_div_prime_factor_right
    {A B p : Nat} (hpB : p ∣ B) : A * B / p = A * (B / p) := by
  exact Nat.mul_div_assoc A hpB

/-- The complementary-prime-divisor sum obeys a Leibniz rule on coprime inputs. -/
theorem squarefreeDeriv_mul {A B : Nat} (hAB : A.Coprime B) :
    squarefreeDeriv (A * B) =
      A * squarefreeDeriv B + B * squarefreeDeriv A := by
  rw [squarefreeDeriv, hAB.primeFactors_mul, Finset.sum_union hAB.disjoint_primeFactors]
  unfold squarefreeDeriv
  have hleft :
      (∑ p ∈ A.primeFactors, A * B / p) = (∑ p ∈ A.primeFactors, A / p) * B := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun p hp ↦
      mul_div_prime_factor_left (Nat.dvd_of_mem_primeFactors hp)
  have hright :
      (∑ p ∈ B.primeFactors, A * B / p) = A * (∑ p ∈ B.primeFactors, B / p) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p hp ↦
      mul_div_prime_factor_right (Nat.dvd_of_mem_primeFactors hp)
  rw [hleft, hright]
  ac_rfl

/-- Port composition substitutes the residual produced by the first coprime factor. -/
theorem portDelta_mul {A B R c : Nat} (hAB : A.Coprime B) :
    portDelta R c (A * B) = portDelta (R * A) (portDelta R c A) B := by
  rw [portDelta, squarefreeDeriv_mul hAB, portDelta, portDelta]
  simp only [mul_add, Nat.sub_mul, Nat.sub_sub, mul_assoc]
  congr 1
  ring

/-- Extending a PPN by a coprime squarefree factor is equivalent to a unit residual. -/
theorem isPPN_mul_iff_port {K C : Nat} (hK : IsPPN K)
    (hC : Squarefree C) (hCgt : 1 < C) (hKC : K.Coprime C) :
    IsPPN (K * C) ↔ C - K * squarefreeDeriv C = 1 := by
  rcases hK with ⟨hKsq, hKgt, hKppn⟩
  constructor
  · rintro ⟨_, _, hKCppn⟩
    rw [squarefreeDeriv_mul hKC] at hKCppn
    have hCeq : C = 1 + K * squarefreeDeriv C := by
      nlinarith
    omega
  · intro hport
    refine ⟨(Nat.squarefree_mul hKC).2 ⟨hKsq, hC⟩, ?_, ?_⟩
    · nlinarith
    · rw [squarefreeDeriv_mul hKC]
      have hCeq : C = 1 + K * squarefreeDeriv C := by
        omega
      nlinarith

-- Fidelity witnesses: the domain is inhabited and all conditional hypotheses are satisfiable.
example : Nat := 2

example : Nat.Coprime 2 3 := by norm_num

example : IsPPN 2 ∧ Squarefree 3 ∧ 1 < 3 ∧ Nat.Coprime 2 3 := by
  exact ⟨primary_pseudoperfect_numerical_chain.1,
    (by norm_num : Nat.Prime 3).squarefree, by norm_num, by norm_num⟩

#print axioms squarefreeDeriv_mul
#print axioms portDelta_mul
#print axioms isPPN_mul_iff_port

end D5.S3.PrimeForms.PrimaryPseudoperfectPortComposition
