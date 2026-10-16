import D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
open D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy (VertexModule)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
noncomputable section

abbrev signature : Signature where
  Params := Nat
  State q := VertexModule Sign q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := VertexModule Sign q
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (ho : Odd q) (v : VertexModule Sign q),
    resetDefect q (r.readout () q v) = 0 ↔
      ∃! k : ℤ, v = k • resetOddVector q

abbrev actual : Realization signature :=
  realize signature (fun _ _ v => v) (fun e => nomatch e)

abbrev bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private def positiveRow : VertexModule Sign 1 :=
  fun _ => MonoidAlgebra.single (1 : Sign) 1

private theorem positive_not_kernel :
    ¬ ∃! k : ℤ, positiveRow = k • resetOddVector 1 := by
  rintro ⟨k, hk, _⟩
  have h1 := congrArg (fun v : VertexModule Sign 1 => (v 0).coeff 1) hk
  have ht := congrArg (fun v : VertexModule Sign 1 =>
    (v 0).coeff (Multiplicative.ofAdd true)) hk
  change (positiveRow 0).coeff 1 = (k • (resetOddVector 1 0)).coeff 1 at h1
  change (positiveRow 0).coeff (Multiplicative.ofAdd true) =
    (k • (resetOddVector 1 0)).coeff (Multiplicative.ofAdd true) at ht
  rw [MonoidAlgebra.coeff_smul_apply] at h1 ht
  simp [positiveRow, resetOddVector, MonoidAlgebra.coeff_sub,
    MonoidAlgebra.coeff_single] at h1 ht
  omega

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hv := (h 1 (by decide) (by decide) positiveRow).mp (map_zero _)
  exact positive_not_kernel hv

private theorem actual_law : arena.Law actual := reset_odd_kernel

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, positiveRow, ?_⟩
  intro h
  change (0 : VertexModule Sign 1) = positiveRow at h
  apply positive_not_kernel
  have hz : resetDefect 1 positiveRow = 0 := by
    rw [← h]
    exact map_zero _
  exact (reset_odd_kernel 1 (by decide) (by decide) positiveRow).mp hz

def kernelRegistration : Registration arena
    (∀ (q : ℕ) (hq : 0 < q) (ho : Odd q) (v : VertexModule Sign q),
      resetDefect q v = 0 ↔ ∃! k : ℤ, v = k • resetOddVector q) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.reset_odd_kernel)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.kernel_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.kernelRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨kernelRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


private theorem positive_ne_zero : positiveRow ≠ 0 := by
  intro h
  have hh := congrArg (fun v : VertexModule Sign 1 => (v 0).coeff 1) h
  simpa [positiveRow, MonoidAlgebra.coeff_single] using hh

private theorem positive_character : resetCharacter 1 positiveRow = 1 := by
  norm_num [resetCharacter, positiveRow, Fin.sum_univ_one,
    MonoidAlgebra.coeff_single]

private def rowRegistration (law : Realization signature → Prop) (Target : Prop)
    (bridge : law actual ↔ Target) (hp : law actual) (hn : ¬ law bad) :
    Registration ⟨signature, law⟩ Target where
  actual := actual
  bridge := bridge.symm
  variation := ⟨hp, bad, hn⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, hn⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

abbrev imageArena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (_hq : 0 < q) (_ho : Odd q) (y : VertexModule Sign q),
    (∃ v, resetDefect q v = r.readout () q y) ↔ resetCharacter q y = 0

private theorem image_bad : ¬ imageArena.Law bad := by
  intro h
  have hz := (h 1 (by decide) (by decide) positiveRow).mp ⟨0, map_zero _⟩
  rw [positive_character] at hz
  omega

def imageRegistration : Registration imageArena
    (∀ (q : ℕ) (hq : 0 < q) (ho : Odd q) (y : VertexModule Sign q),
      (∃ v, resetDefect q v = y) ↔ resetCharacter q y = 0) :=
  rowRegistration _ _ Iff.rfl reset_odd_image image_bad

abbrev evenArena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (he : Even q) (y : VertexModule Sign q),
    resetDefect q (resetPreimage q hq (r.readout () q y)) = y ∧
      ∀ v, resetDefect q v = y ↔ v = resetPreimage q hq y

private theorem even_bad : ¬ evenArena.Law bad := by
  intro h
  let y : VertexModule Sign 2 := fun _ => MonoidAlgebra.single (1 : Sign) 1
  have hz := (h 2 (by decide) (by decide) y).1
  change resetDefect 2 (resetPreimage 2 (by decide) 0) = y at hz
  rw [(reset_even_unique_solution 2 (by decide) (by decide) 0).1] at hz
  have hh := congrArg (fun v : VertexModule Sign 2 => (v 0).coeff 1) hz
  norm_num [y, MonoidAlgebra.coeff_single] at hh

def evenRegistration : Registration evenArena
    (∀ (q : ℕ) (hq : 0 < q) (he : Even q) (y : VertexModule Sign q),
      resetDefect q (resetPreimage q hq y) = y ∧
        ∀ v, resetDefect q v = y ↔ v = resetPreimage q hq y) :=
  rowRegistration _ _ Iff.rfl reset_even_unique_solution even_bad

abbrev solutionsArena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (ho : Odd q) (y : VertexModule Sign q)
      (_hy : resetCharacter q y = 0) (v : VertexModule Sign q),
    resetDefect q (r.readout () q v) = y ↔
      ∃! k : ℤ, v = resetPreimage q hq y + k • resetOddVector q

private theorem solutions_bad : ¬ solutionsArena.Law bad := by
  intro h
  have hs := (h 1 (by decide) (by decide) 0 (map_zero _) positiveRow).mp (map_zero _)
  have hv := (reset_odd_all_solutions 1 (by decide) (by decide) 0
    (map_zero _) positiveRow).mpr hs
  exact positive_not_kernel ((reset_odd_kernel 1 (by decide) (by decide) positiveRow).mp hv)

def solutionsRegistration : Registration solutionsArena
    (∀ (q : ℕ) (hq : 0 < q) (ho : Odd q) (y : VertexModule Sign q)
        (hy : resetCharacter q y = 0) (v : VertexModule Sign q),
      resetDefect q v = y ↔
        ∃! k : ℤ, v = resetPreimage q hq y + k • resetOddVector q) :=
  rowRegistration _ _ Iff.rfl reset_odd_all_solutions solutions_bad

abbrev companionSignature : Signature where
  Params := Nat
  State n := VertexModule Sign (n + 1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := VertexModule Sign (n + 1)
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev companionActual : Realization companionSignature :=
  realize companionSignature (fun _ _ v => v) (fun e => nomatch e)

abbrev companionBad : Realization companionSignature :=
  realize companionSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev companionArena : Arena where
  signature := companionSignature
  Law r := ∀ (n : ℕ) (v : VertexModule Sign (n + 1)),
    resetDefect (n + 1) (r.readout () n v) =
      D5.S1.Recurrence.FiniteCompanionDefect.companion resetFlip n v

private theorem companion_bad : ¬ companionArena.Law companionBad := by
  intro h
  have hz := h 0 positiveRow
  change resetDefect 1 0 =
    D5.S1.Recurrence.FiniteCompanionDefect.companion resetFlip 0 positiveRow at hz
  rw [map_zero, ← reset_defect_companion] at hz
  exact positive_not_kernel ((reset_odd_kernel 1 (by decide) (by decide) positiveRow).mp hz.symm)

def companionRegistration : Registration companionArena
    (∀ (n : ℕ) (v : VertexModule Sign (n + 1)),
      resetDefect (n + 1) v =
        D5.S1.Recurrence.FiniteCompanionDefect.companion resetFlip n v) where
  actual := companionActual
  bridge := Iff.rfl
  variation := ⟨reset_defect_companion, companionBad, companion_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨companionBad, ?_, rfl, companion_bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨0, 0, positiveRow, ?_⟩
    exact fun h => positive_ne_zero h.symm

abbrev characterSignature : Signature where
  Params := Nat
  State q := VertexModule Sign q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev characterArena : Arena where
  signature := characterSignature
  Law r := ∀ (q : ℕ) (_hq : 0 < q), Function.Surjective (r.readout () q)

abbrev characterActual : Realization characterSignature :=
  realize characterSignature (fun _ q v => resetCharacter q v) (fun e => nomatch e)

abbrev characterBad : Realization characterSignature :=
  realize characterSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem character_bad : ¬ characterArena.Law characterBad := by
  intro h
  obtain ⟨v, hv⟩ := h 1 (by decide) 1
  change (0 : ℤ) = 1 at hv
  omega

def characterRegistration : Registration characterArena
    (∀ (q : ℕ) (hq : 0 < q), Function.Surjective (resetCharacter q)) where
  actual := characterActual
  bridge := Iff.rfl
  variation := ⟨reset_character_surjective, characterBad, character_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨characterBad, ?_, rfl, character_bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, positiveRow, ?_⟩
    change resetCharacter 1 0 ≠ resetCharacter 1 positiveRow
    rw [map_zero, positive_character]
    decide

abbrev rangeSignature : Signature where
  Params := Nat
  State q := Module.End ℤ (VertexModule Sign q)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := Submodule ℤ (VertexModule Sign q)
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev rangeArena : Arena where
  signature := rangeSignature
  Law r := ∀ (q : ℕ) (_hq : 0 < q) (_ho : Odd q),
    r.readout () q (resetDefect q) = LinearMap.ker (resetCharacter q)

abbrev rangeActual : Realization rangeSignature :=
  realize rangeSignature (fun _ _ f => LinearMap.range f) (fun e => nomatch e)

abbrev rangeBad : Realization rangeSignature :=
  realize rangeSignature (fun _ _ _ => ⊤) (fun e => nomatch e)

private theorem range_bad : ¬ rangeArena.Law rangeBad := by
  intro h
  have hh := h 1 (by decide) (by decide)
  change (⊤ : Submodule ℤ (VertexModule Sign 1)) = LinearMap.ker (resetCharacter 1) at hh
  have hp : positiveRow ∈ LinearMap.ker (resetCharacter 1) := hh ▸ Submodule.mem_top
  change resetCharacter 1 positiveRow = 0 at hp
  rw [positive_character] at hp
  omega

def rangeRegistration : Registration rangeArena
    (∀ (q : ℕ) (hq : 0 < q) (ho : Odd q),
      LinearMap.range (resetDefect q) = LinearMap.ker (resetCharacter q)) where
  actual := rangeActual
  bridge := Iff.rfl
  variation := ⟨reset_odd_range, rangeBad, range_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rangeBad, ?_, rfl, range_bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, LinearMap.id, ?_⟩
    change LinearMap.range (0 : Module.End ℤ (VertexModule Sign 1)) ≠
      LinearMap.range (LinearMap.id : Module.End ℤ (VertexModule Sign 1))
    intro h
    have hp : positiveRow ∈ LinearMap.range (LinearMap.id : Module.End ℤ (VertexModule Sign 1)) :=
      ⟨positiveRow, rfl⟩
    rw [← h] at hp
    obtain ⟨v, hv⟩ := hp
    exact positive_ne_zero hv.symm

noncomputable def registration_image : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.reset_odd_image)
    (Realization imageArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.image_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.imageRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨imageArena⟩
  objectArena := .source ⟨imageArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source imageArena ⟨imageRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "arg", "body", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_even : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.reset_even_unique_solution)
    (Realization evenArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.even_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.evenRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨evenArena⟩
  objectArena := .source ⟨evenArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source evenArena ⟨evenRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_solutions : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.reset_odd_all_solutions)
    (Realization solutionsArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.solutions_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.solutionsRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨solutionsArena⟩
  objectArena := .source ⟨solutionsArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source solutionsArena ⟨solutionsRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_companion : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.reset_defect_companion)
    (Realization companionArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.companion_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.companionRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨companionArena⟩
  objectArena := .source ⟨companionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source companionArena ⟨companionRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize companionSignature (fun _ _ v => v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "fn", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_character : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.reset_character_surjective)
    (Realization characterArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.character_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.characterRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨characterArena⟩
  objectArena := .source ⟨characterArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source characterArena ⟨characterRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize characterSignature (fun _ q v => resetCharacter q v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_range : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.reset_odd_range)
    (Realization rangeArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.range_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect.rangeRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨rangeArena⟩
  objectArena := .source ⟨rangeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rangeArena ⟨rangeRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rangeSignature (fun _ _ f => LinearMap.range f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
