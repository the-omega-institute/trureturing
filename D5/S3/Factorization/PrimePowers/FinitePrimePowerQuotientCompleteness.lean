/- GID: D5/S3/Factorization/PrimePowers/FinitePrimePowerQuotientCompleteness
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/FinitePrimePowerQuotientCompleteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite prime-power quotient completeness is equivalent to nilpotence. -/

import D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientJointKernel
import Mathlib.GroupTheory.Nilpotent

/- Library-search audit trail (2026-08-25):
   * The finite-quotient faithfulness family supplies the canonical quotient
     indexing and observer construction; this module restricts that family to
     quotients that are p-groups rather than redeclaring the all-finite objects.
   * Exact Mathlib hit `Group.isNilpotent_of_finite_tfae` supplies finite
     nilpotence iff the Sylow direct-product equivalence and is applied directly.
   * Exact hits `IsPGroup.isNilpotent`, `Group.isNilpotent_pi`, subgroup
     nilpotence, `MonoidHom.ofInjective`, `IsPGroup.of_injective`, and
     `QuotientGroup.kerLift_injective` supply the remaining implication edges.
   * No current-tree or pinned-library theorem packages all five source clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.FinitePrimePowerQuotientCompleteness

open Group

universe u

/-- Normal finite-index subgroups whose canonical quotient is a p-group for
some prime p. -/
def primePowerQuotientIndex (G : Type u) [Group G] :=
  { H : FiniteIndexNormalSubgroup G //
    ∃ p : Nat, p.Prime ∧ IsPGroup p (G ⧸ H.toSubgroup) }

/-- The intersection of the kernels of all finite p-group quotient maps. -/
def primePowerResidual (G : Type u) [Group G] : Subgroup G :=
  ⨅ H : primePowerQuotientIndex G, H.1.toSubgroup

/-- The canonical joint observation into every finite p-group quotient. -/
def primePowerQuotientObserver (G : Type u) [Group G] :
    G →* ((H : primePowerQuotientIndex G) → (G ⧸ H.1.toSubgroup)) :=
  MonoidHom.pi fun H => QuotientGroup.mk' H.1.toSubgroup

/-- For a finite group, joint faithfulness of all finite p-group quotients,
triviality of their residual, embeddability in a finite product of finite
p-groups, nilpotence, and decomposition as the product of the Sylow subgroups
are equivalent. -/
theorem finite_prime_power_quotient_completeness_tfae
    {G : Type u} [Group G] [Finite G] :
    List.TFAE
      [Function.Injective (primePowerQuotientObserver G),
        primePowerResidual G = ⊥,
        ∃ (ι : Type u) (_ : Finite ι) (P : ι -> Type u)
            (_ : ∀ i, Group (P i)) (_ : ∀ i, Finite (P i))
            (prime : ι -> Nat),
          (∀ i, (prime i).Prime ∧ IsPGroup (prime i) (P i)) ∧
            ∃ embedding : G →* (∀ i, P i), Function.Injective embedding,
        Group.IsNilpotent G,
        Nonempty
          ((∀ p : (Nat.card G).primeFactors,
              ∀ P : Sylow p G, (↑P : Subgroup G)) ≃* G)] := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have kernelIdentity :
      (primePowerQuotientObserver G).ker = primePowerResidual G := by
    ext g
    constructor
    · intro inKernel
      change g ∈ (⨅ H : primePowerQuotientIndex G, H.1.toSubgroup)
      rw [Subgroup.mem_iInf]
      intro H
      apply (QuotientGroup.eq_one_iff g).mp
      simpa [primePowerQuotientObserver] using congrFun inKernel H
    · intro inResidual
      change
        (fun H : primePowerQuotientIndex G =>
          (QuotientGroup.mk' H.1.toSubgroup) g) = 1
      funext H
      have inH : g ∈ H.1.toSubgroup :=
        (Subgroup.mem_iInf.mp (show
          g ∈ (⨅ K : primePowerQuotientIndex G, K.1.toSubgroup) from
            inResidual)) H
      exact (QuotientGroup.eq_one_iff g).mpr inH
  tfae_have 1 → 2 := by
    intro faithful
    rw [← kernelIdentity]
    exact (MonoidHom.ker_eq_bot_iff (primePowerQuotientObserver G)).mpr faithful
  tfae_have 2 → 1 := by
    intro residualTrivial
    rw [← kernelIdentity] at residualTrivial
    exact (MonoidHom.ker_eq_bot_iff (primePowerQuotientObserver G)).mp
      residualTrivial
  tfae_have 1 → 3 := by
    intro faithful
    letI : Finite (FiniteIndexNormalSubgroup G) :=
      Finite.of_injective
        (fun H : FiniteIndexNormalSubgroup G => H.toSubgroup)
        FiniteIndexNormalSubgroup.toSubgroup_injective
    letI : Finite (primePowerQuotientIndex G) :=
      Finite.of_injective
        (fun H : primePowerQuotientIndex G => H.1)
        Subtype.val_injective
    refine ⟨primePowerQuotientIndex G, inferInstance,
      fun H => G ⧸ H.1.toSubgroup, inferInstance, inferInstance,
      fun H => H.2.choose, ?_, primePowerQuotientObserver G, faithful⟩
    intro H
    exact ⟨H.2.choose_spec.1, H.2.choose_spec.2⟩
  tfae_have 3 → 1 := by
    rintro ⟨ι, finiteIndex, P, groupFactors, finiteFactors, prime,
      primeFactors, embedding, embeddingInjective⟩
    letI : Finite ι := finiteIndex
    letI (i : ι) : Group (P i) := groupFactors i
    letI (i : ι) : Finite (P i) := finiteFactors i
    intro x y sameObservations
    apply embeddingInjective
    funext i
    let coordinate : G →* P i :=
      (Pi.evalMonoidHom P i).comp embedding
    have quotientIsPGroup : IsPGroup (prime i) (G ⧸ coordinate.ker) :=
      (primeFactors i).2.of_injective
        (QuotientGroup.kerLift coordinate)
        (QuotientGroup.kerLift_injective coordinate)
    let quotientIndex : primePowerQuotientIndex G :=
      ⟨FiniteIndexNormalSubgroup.ofSubgroup coordinate.ker,
        ⟨prime i, (primeFactors i).1, quotientIsPGroup⟩⟩
    have sameQuotient := congrFun sameObservations quotientIndex
    change
      (QuotientGroup.mk' coordinate.ker) x =
        (QuotientGroup.mk' coordinate.ker) y at sameQuotient
    have inKernel : x / y ∈ coordinate.ker :=
      QuotientGroup.eq_iff_div_mem.mp sameQuotient
    change coordinate (x / y) = 1 at inKernel
    have coordinateDivision : coordinate (x / y) = 1 := inKernel
    rw [map_div, div_eq_one] at coordinateDivision
    exact coordinateDivision
  tfae_have 3 → 4 := by
    rintro ⟨ι, finiteIndex, P, groupFactors, finiteFactors, prime,
      primeFactors, embedding, embeddingInjective⟩
    letI : Finite ι := finiteIndex
    letI (i : ι) : Group (P i) := groupFactors i
    letI (i : ι) : Finite (P i) := finiteFactors i
    letI (i : ι) : Fact (Nat.Prime (prime i)) := ⟨(primeFactors i).1⟩
    letI (i : ι) : Group.IsNilpotent (P i) :=
      (primeFactors i).2.isNilpotent
    letI : Group.IsNilpotent (∀ i, P i) := inferInstance
    letI : Group.IsNilpotent embedding.range := inferInstance
    exact
      (Group.isNilpotent_congr
        (MonoidHom.ofInjective embeddingInjective)).mpr inferInstance
  tfae_have 4 → 5 := by
    exact (Group.isNilpotent_of_finite_tfae (G := G)).out 0 4 rfl rfl |>.mp
  tfae_have 5 → 3 := by
    rintro ⟨sylowProduct⟩
    let Index :=
      Σ p : (Nat.card G).primeFactors, Sylow p G
    let Factor : Index -> Type u := fun i => i.2
    let uncurryHom :
        (∀ p : (Nat.card G).primeFactors, ∀ P : Sylow p G, P) →*
          (∀ i : Index, Factor i) := {
      toFun := Sigma.uncurry
      map_one' := rfl
      map_mul' _ _ := rfl }
    have uncurryInjective : Function.Injective uncurryHom := by
      intro first second same
      funext p P
      exact congrFun same ⟨p, P⟩
    let embedding : G →* (∀ i : Index, Factor i) :=
      uncurryHom.comp sylowProduct.symm.toMonoidHom
    refine ⟨Index, inferInstance, Factor, inferInstance, inferInstance,
      fun i => i.1.1, ?_, embedding, ?_⟩
    · intro i
      have prime : i.1.1.Prime := Nat.prime_of_mem_primeFactors i.1.2
      letI : Fact (Nat.Prime i.1.1) := ⟨prime⟩
      exact ⟨prime, i.2.isPGroup'⟩
    · exact uncurryInjective.comp sylowProduct.symm.injective
  tfae_finish

#print axioms primePowerQuotientIndex
#print axioms primePowerResidual
#print axioms primePowerQuotientObserver
#print axioms finite_prime_power_quotient_completeness_tfae

end D5.S3.Factorization.PrimePowers.FinitePrimePowerQuotientCompleteness
