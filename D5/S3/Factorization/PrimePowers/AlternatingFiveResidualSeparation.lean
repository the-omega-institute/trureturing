/- GID: D5/S3/Factorization/PrimePowers/AlternatingFiveResidualSeparation
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/AlternatingFiveResidualSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime-power quotient observations of A5 are strictly weaker than all finite quotients. -/

import D5.S3.Factorization.PrimePowers.FinitePrimePowerQuotientCompleteness
import D5.S3.Factorization.PrimePowers.SimpleToPGroupTrivial

/- Library-search audit trail (2026-08-25):
   * The current-tree body-shape search for fixed-prime residual intersections
     found no D5 definition. The broader `primePowerResidual` and
     `primePowerQuotientObserver` are imported from the canonical family rather
     than redeclared.
   * The frozen predecessor `alternating_five_hom_to_pgroup_trivial` is the
     exact source-level input for every prime-power quotient channel.
   * The canonical `finiteResidual` is inherited through the imported
     finite-quotient family. Pinned Mathlib contains the A5 simplicity theorem
     and standard quotient kernel APIs, but no theorem packaging this six-clause
     residual separation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.AlternatingFiveResidualSeparation

open D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientJointKernel
open D5.S3.Factorization.PrimePowers.FinitePrimePowerQuotientCompleteness
open D5.S3.Factorization.PrimePowers.SimpleToPGroupTrivial

universe u

/-- The residual left by all canonical finite quotient channels with a fixed
prime p-group target. -/
def pGroupResidual (p : Nat) (G : Type u) [Group G] : Subgroup G :=
  ⨅ H : { H : FiniteIndexNormalSubgroup G //
    IsPGroup p (G ⧸ H.toSubgroup) }, H.1.toSubgroup

/-- Every fixed-prime and all-primes quotient observation of `A₅` is blind,
whereas the identity finite quotient makes the all-finite residual trivial.
Thus the two canonical residuals are strictly separated. -/
theorem alternating_five_residual_separation :
    (∀ p : Nat, p.Prime →
        pGroupResidual p (alternatingGroup (Fin 5)) = ⊤) ∧
      primePowerResidual (alternatingGroup (Fin 5)) = ⊤ ∧
      primePowerQuotientObserver (alternatingGroup (Fin 5)) = 1 ∧
      (∃ H : FiniteIndexNormalSubgroup (alternatingGroup (Fin 5)),
        H.toSubgroup = ⊥) ∧
      finiteResidual (alternatingGroup (Fin 5)) = ⊥ ∧
      finiteResidual (alternatingGroup (Fin 5)) <
        primePowerResidual (alternatingGroup (Fin 5)) := by
  have fixedPrimeResidualTop :
      ∀ p : Nat, p.Prime →
        pGroupResidual p (alternatingGroup (Fin 5)) = ⊤ := by
    intro p hp
    apply top_unique
    refine le_iInf fun H => ?_
    intro g _
    apply (QuotientGroup.eq_one_iff g).mp
    exact alternating_five_hom_to_pgroup_trivial hp H.2
      (QuotientGroup.mk' H.1.toSubgroup) g
  have allPrimeResidualTop :
      primePowerResidual (alternatingGroup (Fin 5)) = ⊤ := by
    apply top_unique
    refine le_iInf fun H => ?_
    rcases H.2 with ⟨p, hp, hP⟩
    intro g _
    apply (QuotientGroup.eq_one_iff g).mp
    exact alternating_five_hom_to_pgroup_trivial hp hP
      (QuotientGroup.mk' H.1.toSubgroup) g
  have allPrimeObserverTrivial :
      primePowerQuotientObserver (alternatingGroup (Fin 5)) = 1 := by
    ext g H
    rcases H.2 with ⟨p, hp, hP⟩
    exact alternating_five_hom_to_pgroup_trivial hp hP
      (QuotientGroup.mk' H.1.toSubgroup) g
  letI : (⊥ : Subgroup (alternatingGroup (Fin 5))).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  let identityIndex :
      FiniteIndexNormalSubgroup (alternatingGroup (Fin 5)) :=
    FiniteIndexNormalSubgroup.ofSubgroup ⊥
  have identityChannel :
      ∃ H : FiniteIndexNormalSubgroup (alternatingGroup (Fin 5)),
        H.toSubgroup = ⊥ :=
    ⟨identityIndex, rfl⟩
  have allFiniteResidualBottom :
      finiteResidual (alternatingGroup (Fin 5)) = ⊥ := by
    apply le_antisymm
    · exact iInf_le_of_le identityIndex le_rfl
    · exact bot_le
  refine ⟨fixedPrimeResidualTop, allPrimeResidualTop,
    allPrimeObserverTrivial, identityChannel, allFiniteResidualBottom, ?_⟩
  rw [allFiniteResidualBottom, allPrimeResidualTop]
  exact bot_lt_top

#print axioms pGroupResidual
#print axioms alternating_five_residual_separation

end D5.S3.Factorization.PrimePowers.AlternatingFiveResidualSeparation
