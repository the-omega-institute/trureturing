/- GID: D5/S3/Factorization/Galois/FiniteVersusPrimePowerResidual
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/FiniteVersusPrimePowerResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite kernels lie below prime-power kernels; A5 is strict, with audits. -/
/- Library-search audit trail (2026-08-25):
   * The repository search hit the canonical `finiteResidual` and `primePowerResidual`
     definitions, so this module reuses them instead of defining a second residual family.
   * Exact repository hit `alternating_five_residual_separation` supplies the strict A5
     witness; no simplicity, p-group-map, or residual-separation theorem is reproved here.
   * Pinned Mathlib hit `Group.ResiduallyFinite` and the general profinite completion, but
     no pro-p completion. This is therefore honest fallback level 2: comparison of kernels
     cut out by the two finite quotient families, not comparison of completion objects.
   * `IsPGroup.to_quotient`, `IsPGroup.iff_card`, `IsPGroup.of_card`, and
     `nat_card_alternatingGroup` are the exact library inputs used in the audits. -/

import D5.S3.Factorization.PrimePowers.AlternatingFiveResidualSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Galois.FiniteVersusPrimePowerResidual

open D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientJointKernel
open D5.S3.Factorization.PrimePowers.AlternatingFiveResidualSeparation
open D5.S3.Factorization.PrimePowers.FinitePrimePowerQuotientCompleteness

universe u

/- Formalization choice for the undefined source notation:
`R_fin(G)` is the existing `finiteResidual G`, the intersection of every finite-index
normal subgroup. `R_pp(G)` is the existing `primePowerResidual G`, restricted to those
indices whose quotient is a p-group for some prime p. These are indistinguishability
kernels, so enlarging the quotient family makes the intersection smaller. -/

/-- The all-finite residual lies below the residual from only finite p-group quotients. -/
theorem finite_residual_le_prime_power_residual
    {G : Type u} [Group G] : finiteResidual G ≤ primePowerResidual G := by
  rw [primePowerResidual]
  refine le_iInf fun H => ?_
  rw [finiteResidual]
  exact iInf_le_of_le H.1 le_rfl

#print axioms finite_residual_le_prime_power_residual

/-- For A5 the general inclusion is strict. -/
theorem alternating_five_strict_residual_separation :
    finiteResidual (alternatingGroup (Fin 5)) <
      primePowerResidual (alternatingGroup (Fin 5)) :=
  alternating_five_residual_separation.2.2.2.2.2

#print axioms alternating_five_strict_residual_separation

/-- A concrete factored finite order does not force equality of the two residuals.
The equality records `|A5| = 2^2 * 3 * 5`; the second clause refutes the attempted
passage from factorization of an order to decomposition into p-group quotients. -/
theorem order_factorization_does_not_force_residual_equality :
    Nat.card (alternatingGroup (Fin 5)) = (2 ^ 2) * 3 * 5 ∧
      finiteResidual (alternatingGroup (Fin 5)) ≠
        primePowerResidual (alternatingGroup (Fin 5)) := by
  constructor
  · rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · exact ne_of_lt alternating_five_strict_residual_separation

#print axioms order_factorization_does_not_force_residual_equality

/-- On the one-element group both residuals are bottom, so the inclusion is not strict. -/
theorem trivial_group_degenerate_case :
    finiteResidual (⊥ : Subgroup (alternatingGroup (Fin 5))) = ⊥ ∧
      primePowerResidual (⊥ : Subgroup (alternatingGroup (Fin 5))) = ⊥ ∧
      ¬finiteResidual (⊥ : Subgroup (alternatingGroup (Fin 5))) <
        primePowerResidual (⊥ : Subgroup (alternatingGroup (Fin 5))) := by
  have hfinite :
      finiteResidual (⊥ : Subgroup (alternatingGroup (Fin 5))) = ⊥ :=
    Subsingleton.elim _ _
  have hprimePower :
      primePowerResidual (⊥ : Subgroup (alternatingGroup (Fin 5))) = ⊥ :=
    Subsingleton.elim _ _
  refine ⟨hfinite, hprimePower, ?_⟩
  rw [hfinite, hprimePower]
  exact lt_irrefl _

#print axioms trivial_group_degenerate_case

/-- If G is itself a p-group for a prime p, every finite quotient remains a p-group;
hence the two residual families coincide. Primality registers each quotient in the
prime-power index family. Finiteness of G is not needed. -/
theorem p_group_residual_equality
    {p : Nat} {G : Type u} [Group G] (hp : p.Prime) (hG : IsPGroup p G) :
    finiteResidual G = primePowerResidual G := by
  apply le_antisymm
  · exact finite_residual_le_prime_power_residual
  · rw [finiteResidual]
    refine le_iInf fun H => ?_
    rw [primePowerResidual]
    let K : primePowerQuotientIndex G :=
      ⟨H, ⟨p, hp, hG.to_quotient H.toSubgroup⟩⟩
    exact iInf_le_of_le K le_rfl

#print axioms p_group_residual_equality

/-- The finite simple audit is maximally separated: A5 has bottom finite residual,
top prime-power residual, and a trivial joint prime-power observer. -/
theorem alternating_five_simple_group_case :
    IsSimpleGroup (alternatingGroup (Fin 5)) ∧
      finiteResidual (alternatingGroup (Fin 5)) = ⊥ ∧
      primePowerResidual (alternatingGroup (Fin 5)) = ⊤ ∧
      primePowerQuotientObserver (alternatingGroup (Fin 5)) = 1 := by
  refine ⟨alternatingGroup.isSimpleGroup (by norm_num), ?_⟩
  exact ⟨alternating_five_residual_separation.2.2.2.2.1,
    alternating_five_residual_separation.2.1,
    alternating_five_residual_separation.2.2.1⟩

#print axioms alternating_five_simple_group_case

/-- The p-group hypothesis in `p_group_residual_equality` is necessary: A5 is not a
2-group, and its finite and prime-power residuals are unequal. -/
theorem p_group_assumption_is_necessary :
    Nat.Prime 2 ∧
      ¬IsPGroup 2 (alternatingGroup (Fin 5)) ∧
      finiteResidual (alternatingGroup (Fin 5)) ≠
        primePowerResidual (alternatingGroup (Fin 5)) := by
  refine ⟨Nat.prime_two, ?_, ne_of_lt alternating_five_strict_residual_separation⟩
  intro hG
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsPGroup.iff_card.mp hG with ⟨n, hn⟩
  have hthree : 3 ∣ 2 ^ n := by
    rw [← hn, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hthree
  norm_num at this

#print axioms p_group_assumption_is_necessary

/-- Primality is necessary in `p_group_residual_equality`: Mathlib's raw predicate
`IsPGroup p G` is defined for every natural p. A5 satisfies it for composite p = 60,
but its finite and prime-power residuals are unequal. -/
theorem prime_parameter_is_necessary :
    ¬Nat.Prime 60 ∧
      IsPGroup 60 (alternatingGroup (Fin 5)) ∧
      finiteResidual (alternatingGroup (Fin 5)) ≠
        primePowerResidual (alternatingGroup (Fin 5)) := by
  refine ⟨?_, ?_, ne_of_lt alternating_five_strict_residual_separation⟩
  · intro hprime
    rcases hprime.eq_one_or_self_of_dvd 2 (by norm_num) with h | h <;> norm_num at h
  · apply IsPGroup.of_card (n := 1)
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]

#print axioms prime_parameter_is_necessary

-- Empty-source audit: a group type cannot be empty because its identity inhabits it.
example {G : Type*} [Group G] : Nonempty G := ⟨1⟩

-- Exponent-zero audit: on the one-element group, p^0 witnesses `IsPGroup p` for every p.
example (p : Nat) : IsPGroup p (⊥ : Subgroup (alternatingGroup (Fin 5))) := by
  intro g
  refine ⟨0, ?_⟩
  simpa using (Subsingleton.elim g 1)

-- Trivial-map audit: every prime-power quotient observation of A5 is the constant one map.
example : primePowerQuotientObserver (alternatingGroup (Fin 5)) = 1 :=
  alternating_five_residual_separation.2.2.1

-- Identity-channel audit: the all-finite quotient observer does separate A5.
example : Function.Injective (finiteQuotientObserver (alternatingGroup (Fin 5))) :=
  (finite_quotient_joint_kernel (G := alternatingGroup (Fin 5))).2.2.mp
    alternating_five_residual_separation.2.2.2.2.1

end D5.S3.Factorization.Galois.FiniteVersusPrimePowerResidual
