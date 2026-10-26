import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Permutation.PackingMaximumRefutation

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Permutation.PackingMaximumRefutation

namespace Reg.D5.S3.Combinatorics.Permutation.PackingMaximumRefutation

namespace Cardinality

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, ℕ
  State q := Fin q.1 → Fin q.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ q p => count p q.2.1 q.2.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {K : ℕ} (m j : ℕ) (p : Fin K → Fin K),
    r.readout () ⟨K, m, j⟩ p = Nat.card
      {w : Fin (K + (j - 1) * (K - m)) → Fin (K + (j - 1) * (K - m)) //
        Function.Injective w ∧ Packs p m j w}

noncomputable def bad : Realization signature :=
  realize signature (fun _ q p => count p q.2.1 q.2.2 + 1) (fun e => nomatch e)

private theorem positive : arena.Law actual := source_cardinality

private theorem bad_not_law : ¬ arena.Law bad := by
  intro h
  have hp := source_cardinality 4 2 competitor
  have hx := h 4 2 competitor
  change count competitor 4 2 + 1 = _ at hx
  rw [← hp] at hx
  omega

noncomputable def family : Registration arena (type_of% (@source_cardinality)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, bad, bad_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_not_law⟩
      intro k hk
      exact (hk (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨8, 4, 2⟩, competitor, prescribed, ?_⟩
    change count competitor 4 2 ≠ count prescribed 4 2
    rw [count_competitor, count_prescribed]
    decide

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@source_cardinality)
    (type_of% (realize signature (fun _ q p => count p q.2.1 q.2.2)
      (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Combinatorics.Permutation.PackingMaximumRefutation.source_cardinality.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.PackingMaximumRefutation.Cardinality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q p => count p q.2.1 q.2.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.PackingMaximumRefutation
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Cardinality

namespace Boundary

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 8 → Fin 8
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 8 → Fin 8
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ p : Fin 8 → Fin 8, Prescribed p 4 → r.readout () () p = prescribed

def bad : Realization signature :=
  realize signature (fun _ _ _ => competitor) (fun e => nomatch e)

private theorem bad_not_law : ¬ arena.Law bad := by
  intro h
  have hh := h prescribed (by unfold Prescribed; decide)
  have he := congrFun hh 2
  change (3 : Fin 8) = 4 at he
  exact (by decide : (3 : Fin 8) ≠ 4) he

def family : Registration arena (type_of% (@prescribed_boundary)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prescribed_boundary, bad, bad_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_not_law⟩
      intro k hk
      exact (hk (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), competitor, prescribed, ?_⟩
    intro he
    have hh := congrFun he 2
    change (3 : Fin 8) = 4 at hh
    exact (by decide : (3 : Fin 8) ≠ 4) hh

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@prescribed_boundary)
    (type_of% (realize signature (fun _ _ p => p) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Combinatorics.Permutation.PackingMaximumRefutation.prescribed_boundary.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.PackingMaximumRefutation.Boundary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.PackingMaximumRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Boundary

namespace Counts

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 8 → Fin 8
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Unit
  finiteAnchor := inferInstance

noncomputable def actual (p : Fin 8 → Fin 8) : Realization signature :=
  realize signature (fun _ _ w => count w 4 2) (fun _ _ => p)

abbrev arena (n : ℕ) : Arena where
  signature := signature
  Law r := r.readout () () (r.anchor () ()) = n

noncomputable def badReadout (p : Fin 8 → Fin 8) (n : ℕ) : Realization signature :=
  realize signature (fun _ _ _ => n + 1) (fun _ _ => p)

private theorem bad_readout_not_law (p : Fin 8 → Fin 8) (n : ℕ) :
    ¬ (arena n).Law (badReadout p n) := by
  change n + 1 ≠ n
  omega

abbrev competitorArena : Arena := arena 9

noncomputable def competitorFamily : Registration competitorArena (type_of% (@count_competitor)) where
  actual := actual competitor
  bridge := Iff.rfl
  variation := ⟨count_competitor, badReadout competitor 9, bad_readout_not_law competitor 9⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨badReadout competitor 9, ?_, rfl, bad_readout_not_law competitor 9⟩
      intro k hk
      exact (hk (Subsingleton.elim _ _)).elim
    · intro i
      refine ⟨actual prescribed, rfl, ?_, ?_⟩
      · intro k hk
        exact (hk (Subsingleton.elim _ _)).elim
      · change count prescribed 4 2 ≠ 9
        rw [count_prescribed]
        decide
  dependence := by
    intro i
    refine ⟨(), competitor, prescribed, ?_⟩
    change count competitor 4 2 ≠ count prescribed 4 2
    rw [count_competitor, count_prescribed]
    decide

noncomputable def competitorAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@count_competitor)
    (type_of% (realize signature (fun _ _ w => count w 4 2) (fun _ _ => competitor))) Type Unit := {
  unitName := `D5.S3.Combinatorics.Permutation.PackingMaximumRefutation.count_competitor.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.PackingMaximumRefutation.Counts.competitorFamily
  realizationSource := none
  generated := false
  arena := .source ⟨competitorArena⟩
  objectArena := .source ⟨competitorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source competitorArena ⟨competitorFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => count w 4 2) (fun _ _ => competitor))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.PackingMaximumRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev prescribedArena : Arena := arena 8

noncomputable def prescribedFamily : Registration prescribedArena (type_of% (@count_prescribed)) where
  actual := actual prescribed
  bridge := Iff.rfl
  variation := ⟨count_prescribed, badReadout prescribed 8, bad_readout_not_law prescribed 8⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨badReadout prescribed 8, ?_, rfl, bad_readout_not_law prescribed 8⟩
      intro k hk
      exact (hk (Subsingleton.elim _ _)).elim
    · intro i
      refine ⟨actual competitor, rfl, ?_, ?_⟩
      · intro k hk
        exact (hk (Subsingleton.elim _ _)).elim
      · change count competitor 4 2 ≠ 8
        rw [count_competitor]
        decide
  dependence := by
    intro i
    refine ⟨(), competitor, prescribed, ?_⟩
    change count competitor 4 2 ≠ count prescribed 4 2
    rw [count_competitor, count_prescribed]
    decide

noncomputable def prescribedAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@count_prescribed)
    (type_of% (realize signature (fun _ _ w => count w 4 2) (fun _ _ => prescribed))) Type Unit := {
  unitName := `D5.S3.Combinatorics.Permutation.PackingMaximumRefutation.count_prescribed.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.PackingMaximumRefutation.Counts.prescribedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨prescribedArena⟩
  objectArena := .source ⟨prescribedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source prescribedArena ⟨prescribedFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => count w 4 2) (fun _ _ => prescribed))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.PackingMaximumRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Counts

end Reg.D5.S3.Combinatorics.Permutation.PackingMaximumRefutation
