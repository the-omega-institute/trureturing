/- GID: D5/S3/Factorization/PrimePowers/SimpleToPGroupTrivial
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/SimpleToPGroupTrivial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every homomorphism from A5 to a finite p-group is trivial. -/

import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'alternating_five_hom_to_pgroup_trivial' D5 Golden/Frozen/accepted`
     returned no matches.
   * `rg -n 'alternating|IsPGroup|IsSimpleGroup' D5/ | head -20` hit only unrelated
     uses of "alternating" in probability and recurrence modules. A separate search on
     `origin/dev` found no `IsPGroup` or `IsSimpleGroup` declaration in `D5`.
   * Private hits were `LedgerLimit.lean:114` and `AlternatingGoldenContraction.lean:21`;
     both concern unrelated alternating sequences and do not cover the group statement.
   * Pinned mathlib search found `alternatingGroup.isSimpleGroup`,
     `IsPGroup.isNilpotent`, `Group.IsNilpotent.to_isSolvable`, and
     `IsSimpleGroup.comm_iff_isSolvable`, but no theorem with the full target statement.
   * The proof reuses those structural results and the basic kernel API; it does not
     reprove simplicity, nilpotence, or solvability. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.SimpleToPGroupTrivial

/-- A group homomorphism is trivial when every source element maps to the identity. -/
def IsTrivialHom {G P : Type*} [Group G] [Group P] (phi : G →* P) : Prop :=
  ∀ g, phi g = 1

/-- Every homomorphism from `A₅` to a finite `p`-group is trivial. -/
theorem alternating_five_hom_to_pgroup_trivial
    {P : Type*} [Group P] [Finite P] {p : ℕ} (hp : p.Prime) (hP : IsPGroup p P)
    (phi : alternatingGroup (Fin 5) →* P) :
    IsTrivialHom phi := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal phi.ker inferInstance with hker | hker
  · have hinjective : Function.Injective phi := (MonoidHom.ker_eq_bot_iff phi).mp hker
    have hsourceP : IsPGroup p (alternatingGroup (Fin 5)) :=
      IsPGroup.of_injective hP phi hinjective
    letI : Group.IsNilpotent (alternatingGroup (Fin 5)) :=
      IsPGroup.isNilpotent hsourceP
    have hcomm : ∀ a b : alternatingGroup (Fin 5), a * b = b * a :=
      IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
    have hsmall : Nat.card (Fin 5) ≤ 3 :=
      alternatingGroup.isMulCommutative_iff_card_le_three.mp
        (isMulCommutative_iff.mpr hcomm)
    norm_num at hsmall
  · have hphi : phi = 1 := MonoidHom.ker_eq_top_iff.mp hker
    intro g
    rw [hphi]
    rfl

example :
    IsTrivialHom
      (1 : alternatingGroup (Fin 5) →* (⊥ : Subgroup (alternatingGroup (Fin 5)))) :=
  alternating_five_hom_to_pgroup_trivial Nat.prime_two IsPGroup.of_bot 1

#print axioms alternating_five_hom_to_pgroup_trivial

end D5.S3.Factorization.PrimePowers.SimpleToPGroupTrivial
