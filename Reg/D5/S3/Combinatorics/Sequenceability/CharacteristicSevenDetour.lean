import D5.S3.Combinatorics.Sequenceability.CharacteristicSevenDetour
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod

/-! Faithful source-bound registration for the six-column lift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u
namespace Reg.D5.S1.Words.Sequenceability.CharacteristicSevenDetour

open _root_.D5.S1.Words.Sequenceability.CharacteristicSevenDetour
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev LiftParams := Σ K : Type u, Σ f : Field K, @Units K f.toMonoid × K

abbrev liftSignature : Signature where
  Params := LiftParams.{u}
  State p := Fin 6 × p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ZMod 7 × p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def liftActual : Realization liftSignature.{u} :=
  realize liftSignature (fun _ p v => by
    letI := p.2.1
    exact edgeLabel p.2.2.1 p.2.2.2 v) (fun e => nomatch e)

def liftBad : Realization liftSignature.{u} :=
  realize liftSignature (fun _ p _ => by
    letI := p.2.1
    exact (0, 0)) (fun e => nomatch e)

abbrev liftArena : Arena where
  signature := liftSignature.{u}
  Law R := ∀ (K : Type u) [f : Field K] [Finite K] [CharP K 7] (c : K),
    ∃ r : Kˣ, (r : K) + 1 ≠ 0 ∧
      (∀ v w : Fin 6 × K, (lift r c).SameCycle v w ↔
        (initialRow v = c ↔ initialRow w = c)) ∧
      Set.BijOn (R.readout () ⟨K, f, r, c⟩) Set.univ {v | v.1 ≠ 0} ∧
      Set.BijOn (@vertex K) Set.univ {v | v.1 ≠ 0} ∧
      (∀ h : K, (lift r c ^ 6) (0, h) =
        (0, _root_.D5.S1.Words.Sequenceability.RowOrbitLift.rowReturn r c h))

private theorem lift_bad_law : ¬ liftArena.{u}.Law liftBad := by
  intro h
  let K := ULift.{u} (ZMod 7)
  obtain ⟨r, _, _, hlabel, _, _⟩ := h K 0
  exact hlabel.1 (show (0, (0 : K)) ∈ Set.univ from trivial) rfl

def liftFamily : Registration liftArena.{u}
    (type_of% (@exists_characteristic_seven_lift.{u})) where
  actual := liftActual
  bridge := Iff.rfl
  variation := ⟨exists_characteristic_seven_lift, liftBad, lift_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨liftBad, ?_, rfl, lift_bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let K := ULift.{u} (ZMod 7)
    refine ⟨⟨K, inferInstance, 1, 0⟩, (0, 0), (1, 0), ?_⟩
    intro he
    have h := congrArg Prod.fst he
    have h' : (3 : ZMod 7) - 1 = 2 - 3 := by
      simpa [liftActual, realize,
        _root_.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.edgeLabel,
        _root_.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.lift,
        _root_.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.vertex,
        _root_.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.column] using h
    exact (by decide : (3 : ZMod 7) - 1 ≠ 2 - 3) h'

def liftAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_characteristic_seven_lift.{u}) (Realization liftSignature.{u}) Unit Unit where
  unitName :=
    `D5.S1.Words.Sequenceability.CharacteristicSevenDetour.exists_characteristic_seven_lift.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.liftFamily
  realizationSource := none
  generated := false
  arena := .source ⟨liftArena⟩
  objectArena := .source ⟨liftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source liftArena ⟨liftFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize liftSignature liftActual.readout liftActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Sequenceability.CharacteristicSevenDetour
    definition := none
    coordinates := #[0, 1, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev SeamsParams := Σ K : Type u, Σ f : Field K, K

abbrev seamsSignature : Signature where
  Params := SeamsParams.{u}
  State p := carrier (K := p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ZMod 7 × p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def seamsActual : Realization seamsSignature.{u} :=
  realize seamsSignature (fun _ p v => by
    letI := p.2.1
    exact vertexWithEndpoints p.2.2 v) (fun e => nomatch e)

def seamsBad : Realization seamsSignature.{u} :=
  realize seamsSignature (fun _ p _ => by
    letI := p.2.1
    exact (0, 0)) (fun e => nomatch e)

abbrev seamsArena : Arena where
  signature := seamsSignature.{u}
  Law R := ∀ (K : Type u) [f : Field K] [CharP K 7]
    (r : Kˣ) (u : K) (_hu : u ≠ 0) (_hr : (r : K) + 1 ≠ 0),
    (splice r u (predecessorOne r u) = headTwo r u) ∧
    (splice r u (predecessorTwo r u) = target) ∧
    (splice r u source = headOne r u) ∧
    (splice r u target = source) ∧
    (R.readout () ⟨K, f, u⟩ (headTwo r u) -
        R.readout () ⟨K, f, u⟩ (predecessorOne r u) = (0, u)) ∧
    (R.readout () ⟨K, f, u⟩ target -
        R.readout () ⟨K, f, u⟩ (predecessorTwo r u) = (2, 2 * alpha r u)) ∧
    (R.readout () ⟨K, f, u⟩ (headOne r u) -
        R.readout () ⟨K, f, u⟩ source = (3, alpha r u)) ∧
    (R.readout () ⟨K, f, u⟩ source -
        R.readout () ⟨K, f, u⟩ target = (0, -u))

private theorem seams_bad_law : ¬ seamsArena.{u}.Law seamsBad := by
  intro h
  let K := ULift.{u} (ZMod 7)
  have htwo : (2 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 7 2).not.mpr (by decide)
  obtain ⟨_, _, _, _, he, _, _, _⟩ := h K 1 1 (by simp)
    (by simpa only [Units.val_one, one_add_one_eq_two] using htwo)
  have hz : (0 : K) = 1 := by
    simpa [seamsBad, realize] using congrArg Prod.snd he
  exact zero_ne_one hz

def seamsFamily : Registration seamsArena.{u}
    (type_of% (@six_column_splice_seams.{u})) where
  actual := seamsActual
  bridge := Iff.rfl
  variation := ⟨@six_column_splice_seams.{u}, seamsBad, seams_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨seamsBad, ?_, rfl, seams_bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let K := ULift.{u} (ZMod 7)
    refine ⟨⟨K, inferInstance, 1⟩, source, target, ?_⟩
    simp [seamsActual, realize, vertexWithEndpoints, source, target]

def seamsAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@six_column_splice_seams.{u}) (Realization seamsSignature.{u}) Unit Unit where
  unitName :=
    `D5.S1.Words.Sequenceability.CharacteristicSevenDetour.six_column_splice_seams.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.seamsFamily
  realizationSource := none
  generated := false
  arena := .source ⟨seamsArena⟩
  objectArena := .source ⟨seamsArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source seamsArena ⟨seamsFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize seamsSignature seamsActual.readout seamsActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev FieldParams := Σ K : Type u, Field K

abbrev cycleSignature : Signature where
  Params := FieldParams.{u}
  State p := @Units p.1 p.2.toMonoid × p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Equiv.Perm (Fin 6 × p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def cycleActual : Realization cycleSignature.{u} :=
  realize cycleSignature (fun _ p rc => by
    letI := p.2
    exact lift rc.1 rc.2) (fun e => nomatch e)

def cycleBad : Realization cycleSignature.{u} :=
  realize cycleSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev cycleArena : Arena where
  signature := cycleSignature.{u}
  Law R := ∀ (K : Type u) [f : Field K] [Finite K] (r : Kˣ)
    (_hr : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) (c : K) (v w : Fin 6 × K),
    (R.readout () ⟨K, f⟩ (r, c)).SameCycle v w ↔
      (initialRow v = c ↔ initialRow w = c)

private theorem cycle_bad_law : ¬ cycleArena.{u}.Law cycleBad := by
  intro h
  let K := ULift.{u} (ZMod 7)
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hn : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z := fun z =>
    (Submonoid.mem_powers_iff z r).mp (mem_powers_iff_mem_zpowers.mpr (hr z))
  have he := (h K r hn 0 (0, 0) (1, 0)).mpr (by simp [initialRow])
  have hv : (0 : Fin 6) = 1 := congrArg Prod.fst (Equiv.Perm.sameCycle_one.mp he)
  exact (by decide : (0 : Fin 6) ≠ 1) hv

def cycleFamily : Registration cycleArena.{u} (type_of% (@lift_same_cycle.{u})) where
  actual := cycleActual
  bridge := Iff.rfl
  variation := ⟨@lift_same_cycle.{u}, cycleBad, cycle_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨cycleBad, ?_, rfl, cycle_bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let K := ULift.{u} (ZMod 7)
    refine ⟨⟨K, inferInstance⟩, (-1, 0), (-1, 1), ?_⟩
    intro he
    have h := congrArg (fun p : Equiv.Perm (Fin 6 × K) => (p (5, 0)).2) he
    have htwo : (2 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 7 2).not.mpr (by decide)
    apply htwo
    simpa [cycleActual, realize, lift, one_add_one_eq_two,
      _root_.D5.S1.Words.Sequenceability.RowOrbitLift.rowReturn] using h.symm

abbrev generatorSignature : Signature where
  Params := FieldParams.{u}
  State p := @Units p.1 p.2.toMonoid
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def generatorActual : Realization generatorSignature.{u} :=
  realize generatorSignature (fun _ p r => by
    letI := p.2
    exact (r : p.1) + 1) (fun e => nomatch e)

def generatorBad : Realization generatorSignature.{u} :=
  realize generatorSignature (fun _ p _ => by
    letI := p.2
    exact 0) (fun e => nomatch e)

abbrev generatorArena : Arena where
  signature := generatorSignature.{u}
  Law R := ∀ (K : Type u) [f : Field K] [CharP K 7] (r : Kˣ)
    (_hn : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z), R.readout () ⟨K, f⟩ r ≠ 0

private theorem generator_bad_law : ¬ generatorArena.{u}.Law generatorBad := by
  intro h
  let K := ULift.{u} (ZMod 7)
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hn : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z := fun z =>
    (Submonoid.mem_powers_iff z r).mp (mem_powers_iff_mem_zpowers.mpr (hr z))
  exact (h K r hn) rfl

def generatorFamily : Registration generatorArena.{u}
    (type_of% (@generator_add_one_ne_zero.{u})) where
  actual := generatorActual
  bridge := Iff.rfl
  variation := ⟨@generator_add_one_ne_zero.{u}, generatorBad, generator_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨generatorBad, ?_, rfl, generator_bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let K := ULift.{u} (ZMod 7)
    refine ⟨⟨K, inferInstance⟩, 1, -1, ?_⟩
    intro he
    have htwo : (2 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 7 2).not.mpr (by decide)
    exact htwo (by simpa [generatorActual, realize, one_add_one_eq_two] using he)

abbrev inventorySignature : Signature where
  Params := LiftParams.{u}
  State p := carrier (K := p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ZMod 7 × p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def inventoryActual : Realization inventorySignature.{u} :=
  realize inventorySignature (fun _ p x => by
    letI := p.2.1
    exact vertexWithEndpoints p.2.2.2 (splice p.2.2.1 p.2.2.2 x) -
      vertexWithEndpoints p.2.2.2 x) (fun e => nomatch e)

def inventoryBad : Realization inventorySignature.{u} :=
  realize inventorySignature (fun _ p _ => by
    letI := p.2.1
    exact (0, 0)) (fun e => nomatch e)

abbrev inventoryArena : Arena where
  signature := inventorySignature.{u}
  Law R := ∀ (K : Type u) [f : Field K] [Finite K] [CharP K 7] (r : Kˣ) (u : K)
    (_hu : u ≠ 0) (_hr : (r : K) + 1 ≠ 0),
    Set.BijOn (R.readout () ⟨K, f, r, u⟩) {x | x ≠ target}
      {v | v.1 ≠ 0 ∨ v = (0, u)}

private theorem inventory_bad_law : ¬ inventoryArena.{u}.Law inventoryBad := by
  intro h
  let K := ULift.{u} (ZMod 7)
  have htwo : (2 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 7 2).not.mpr (by decide)
  have hb := h K 1 1 (by simp) (by simpa only [Units.val_one, one_add_one_eq_two] using htwo)
  have hz := hb.1 (show source (K := K) ≠ target from by simp [source, target, Fin.ext_iff])
  simp [inventoryBad, realize] at hz

def inventoryFamily : Registration inventoryArena.{u}
    (type_of% (@splice_labels_bijective.{u})) where
  actual := inventoryActual
  bridge := Iff.rfl
  variation := ⟨@splice_labels_bijective.{u}, inventoryBad, inventory_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨inventoryBad, ?_, rfl, inventory_bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let K := ULift.{u} (ZMod 7)
    refine ⟨⟨K, inferInstance, 1, 1⟩, source, predecessorOne 1 1, ?_⟩
    intro he
    have htwo : (2 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 7 2).not.mpr (by decide)
    have hb := splice_labels_bijective (1 : Kˣ) 1 (by simp) (by simpa only [Units.val_one, one_add_one_eq_two] using htwo)
    have heq : source (K := K) = predecessorOne 1 1 := hb.2.1
      (by simp [source, target]) Sum.inl_ne_inr he
    exact Sum.inr_ne_inl heq

def cycleAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lift_same_cycle.{u}) (Realization cycleSignature.{u}) Unit Unit where
  unitName :=
    `D5.S1.Words.Sequenceability.CharacteristicSevenDetour.lift_same_cycle.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.cycleFamily
  realizationSource := none
  generated := false
  arena := .source ⟨cycleArena⟩
  objectArena := .source ⟨cycleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cycleArena ⟨cycleFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cycleSignature cycleActual.readout cycleActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def generatorAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@generator_add_one_ne_zero.{u}) (Realization generatorSignature.{u}) Unit Unit where
  unitName :=
    `D5.S1.Words.Sequenceability.CharacteristicSevenDetour.generator_add_one_ne_zero.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.generatorFamily
  realizationSource := none
  generated := false
  arena := .source ⟨generatorArena⟩
  objectArena := .source ⟨generatorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source generatorArena ⟨generatorFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize generatorSignature generatorActual.readout generatorActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def inventoryAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@splice_labels_bijective.{u}) (Realization inventorySignature.{u}) Unit Unit where
  unitName :=
    `D5.S1.Words.Sequenceability.CharacteristicSevenDetour.splice_labels_bijective.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.CharacteristicSevenDetour.inventoryFamily
  realizationSource := none
  generated := false
  arena := .source ⟨inventoryArena⟩
  objectArena := .source ⟨inventoryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source inventoryArena ⟨inventoryFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize inventorySignature inventoryActual.readout inventoryActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.Sequenceability.CharacteristicSevenDetour
