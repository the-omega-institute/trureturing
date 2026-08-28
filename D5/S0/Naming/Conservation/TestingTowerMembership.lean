/- GID: D5/S0/Naming/Conservation/TestingTowerMembership
   generality: G
   mirror-B: D5/B/S0/Naming/Conservation/TestingTowerMembership
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Testing names have a code-length filtration with finite sublevels. -/

import Mathlib.Data.Set.Finite.List

/- Library-search audit trail (2026-08-29):
   * Body-shape searches for a sum of finite-support tables and program codes,
     and for an injective Boolean-code length filtration, found no exact D5
     primitive. The nearby frozen `FiniteProgramLevelSet` treats only raw
     binary programs and not the source name carrier.
   * Pinned Mathlib's `List.finite_length_le` is the exact bounded-code lemma.
     Its preimage under the supplied injective self-delimiting code proves the
     main filtration clause without assumptions on the secondary execution cost.
   * The name carrier is introduced directly from the source primitives; no
     naming-system structure is defined to make the conclusion hold by typing. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Naming.Conservation.TestingTowerMembership

/-- Names are either finite functional tables on self-selected supports or
natural-number codes for program-based tests. -/
abbrev TestingName (Output : Type*) :=
  (Sigma fun support : Finset Nat => support -> Output) ⊕ Nat

/-- For the testing-tower name carrier, the length of an injective binary code
is a primary height with finite sublevels. Together with any execution-cost
height, this supplies the required primary coordinate of a two-height naming
system. -/
theorem testing_tower_is_multi_filtration
    {Output : Type*}
    (selfDelimitingCode : TestingName Output -> List Bool)
    (codeInjective : Function.Injective selfDelimitingCode)
    (executionCost : TestingName Output -> Nat) :
    exists primary : Bool, forall Q : Nat,
      Set.Finite {name |
        (if primary then executionCost name else (selfDelimitingCode name).length) <= Q} := by
  refine ⟨false, fun Q => ?_⟩
  simpa using
    (List.finite_length_le Bool Q).preimage codeInjective.injOn

#print axioms testing_tower_is_multi_filtration

end D5.S0.Naming.Conservation.TestingTowerMembership
