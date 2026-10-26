/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/EvolutionSharpBound
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/EvolutionSharpBound
   mirror-E: none(waiver:general-sharp-bound)
   anchors: []
   utility: none
   digest: Full successor partitions and nonempty quotient fibers give the universal sharp automorphism bound. -/

import D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport
import D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight
import D5.S0.Asymptotics.WeightedProbability.PermutationMultiplicity

/-! Full bilinear evolution automorphisms, their sharp bound, and attaining products. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionSharpBound

open D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionAutomorphismControl
open D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport
open D5.S3.FiniteGroups.SuccessorQuotient
open D5.S3.FiniteGroups.SuccessorPowerAssignments
open D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight
open D5.S0.Asymptotics.WeightedProbability.PermutationMultiplicity

private theorem shifted_factorial_mul (a b : ℕ) :
    (a + 1).factorial * (b + 1).factorial ≤ (a + b + 1).factorial := by
  have h := Nat.mul_le_mul_left (a + 1).factorial
    (Nat.ascFactorial_le b (show 2 ≤ a + 2 by omega))
  have htwo : (2 : ℕ).ascFactorial b = (b + 1).factorial := by
    simpa [Nat.add_comm] using Nat.factorial_mul_ascFactorial 1 b
  rw [htwo, show a + 2 = (a + 1) + 1 by omega,
    Nat.factorial_mul_ascFactorial] at h
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem block_factorial_bound {Q : Type*} [Fintype Q] (k : Q → ℕ)
    (hk : ∀ q, 1 ≤ k q) :
    (∏ q, (k q).factorial) ≤ ((∑ q, k q) - Fintype.card Q + 1).factorial := by
  classical
  let f : Multiplicative ℕ → ℕᵒᵈ := fun x => (x.toAdd + 1).factorial
  have hf : f (∏ q, Multiplicative.ofAdd (k q - 1)) ≤
      ∏ q, f (Multiplicative.ofAdd (k q - 1)) :=
    Finset.le_prod_of_submultiplicative f (by rfl)
      (fun x y => shifted_factorial_mul x.toAdd y.toAdd) Finset.univ _
  change (∏ q, (k q - 1 + 1).factorial) ≤
    ((∑ q, (k q - 1)) + 1).factorial at hf
  simpa only [Nat.sub_add_cancel (hk _),
    Finset.sum_tsub_distrib Finset.univ (fun q _ => hk q), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] using hf

/-- The full partition includes every fixed point, including its multiplicity factorial. -/
theorem cycle_weight_centralizer {Q : Type*} [hQ : Fintype Q] [dQ : DecidableEq Q]
    (β : Equiv.Perm Q) :
    cycleWeight β * Nat.card (Subgroup.centralizer ({β} : Set (Equiv.Perm Q))) =
      weight β.partition.parts := by
  classical
  have hroot : cycleWeight β = (β.cycleType.map (fun l => 2 ^ l - 1)).prod := by
    have hft : Fintype.ofFinite Q = hQ := Subsingleton.elim _ _
    have hd : (fun a b : Q => Classical.propDecidable (a = b)) = dQ :=
      Subsingleton.elim _ _
    unfold cycleWeight
    rw [hft, hd]
    simp [Equiv.Perm.cycleType_def, Multiset.map_map]
    exact Finset.prod_attach β.cycleFactorsFinset
      (fun c : Equiv.Perm Q => 2 ^ c.support.card - 1)
  have hfull : (β.partition.parts.map (fun l => 2 ^ l - 1)).prod =
      (β.cycleType.map (fun l => 2 ^ l - 1)).prod := by
    simp [Equiv.Perm.parts_partition]
  have hweight : weight β.partition.parts =
      z β.partition.parts * (β.partition.parts.map (fun l => 2 ^ l - 1)).prod := by
    rw [weight, z, Finset.prod_multiset_map_count, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro l hl
    rw [mul_pow]
    ring
  rw [hweight, hfull, hroot, hz_perm, Equiv.Perm.nat_card_centralizer]
  ring

private theorem quotient_numeric_bound {n : ℕ} (hn : 1 ≤ n)
    (R : Fin n → Fin n → Prop) (β : Equiv.Perm (Blocks R)) :
    letI := Fintype.ofFinite (Blocks R)
    cycleWeight β * Nat.card (Subgroup.centralizer ({β} : Set (Equiv.Perm (Blocks R)))) *
      (∏ q : Blocks R, (Nat.card (Fiber R q)).factorial) ≤ maximumWeight n := by
  classical
  letI := Fintype.ofFinite (Blocks R)
  let k : Blocks R → ℕ := fun q => Nat.card (Fiber R q)
  have hk (q : Blocks R) : 1 ≤ k q := by
    obtain ⟨i, hi⟩ := Quotient.mk_surjective q
    haveI : Nonempty (Fiber R q) := ⟨⟨i, hi⟩⟩
    exact Nat.card_pos
  have hsum : ∑ q, k q = n := by
    simpa only [k, Nat.card_eq_fintype_card, Fintype.card_sigma, Fintype.card_fin] using
      Fintype.card_congr (Equiv.sigmaFiberEquiv (project R))
  have hs : 1 ≤ Fintype.card (Blocks R) := by
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    haveI : Nonempty (Blocks R) := ⟨project R (Classical.arbitrary (Fin n))⟩
    exact Fintype.card_pos
  have hsn : Fintype.card (Blocks R) ≤ n := by
    simpa using Fintype.card_le_of_surjective (project R) Quotient.mk_surjective
  calc
    _ = weight β.partition.parts * ∏ q, (k q).factorial := by
      rw [cycle_weight_centralizer]
    _ ≤ maximumWeight (Fintype.card (Blocks R)) *
        (n - Fintype.card (Blocks R) + 1).factorial :=
      Nat.mul_le_mul (by
        exact Finset.le_sup (f := fun p : Nat.Partition (Fintype.card (Blocks R)) => weight p.parts)
          (Finset.mem_univ β.partition))
        (by simpa [hsum] using block_factorial_bound k hk)
    _ ≤ maximumWeight n := maximum_weight_mul_factorial_le hs hsn

/-- Universal upper bound for the full group on an arbitrary finite-dimensional carrier. -/
theorem finite_and_bound {A : Type*} [AddCommGroup A] [Module ℂ A]
    [FiniteDimensional ℂ A] {ι : Type*} [Fintype ι] {n : ℕ}
    (hn : 1 ≤ n) (hd : Module.finrank ℂ A = n)
    (μ : A →ₗ[ℂ] A →ₗ[ℂ] A) (b : Module.Basis ι ℂ A)
    (hb : ∀ i j : ι, i ≠ j → μ (b i) (b j) = 0)
    (hp : productSpan μ = ⊤) :
    Finite (Aut μ) ∧ Nat.card (Aut μ) ≤ maximumWeight n := by
  classical
  have h := finite_and_joint_bound hd μ b hb hp
  refine ⟨h.1, h.2.trans ?_⟩
  exact quotient_numeric_bound hn _ _

end D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionSharpBound
