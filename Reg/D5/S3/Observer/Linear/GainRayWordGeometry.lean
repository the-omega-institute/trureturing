import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.GainRayWordGeometry
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Linear.GainRayWordGeometry
open _root_.D5.S3.Observer.Linear.GainRay
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
open scoped Matrix Classical

abbrev signature : Signature where
  Params := List Bool
  State _ := Mat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ w L => (Finset.univ.filter (fun i : Fin (w.length+1) =>
    ∃ c : ℝ, acquisition (w.take i.val) = c • L)).card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ w _ => w.length+1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (w : List Bool) (m : ℕ) (_hlen : w.length = 2*m) (_hM : false ∈ w)
    (L : Mat), R.readout () w L ≤ m

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h [false,false] 1 rfl (by simp) 0
  norm_num [rejected,realize] at hh

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cumulative_proportionality_card_even,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    classical
    intro i
    refine ⟨[], (0 : Mat), (1 : Mat), ?_⟩
    have he : acquisition [] = (1 : Mat) := by
      simpa using acquisition_pure false 0
    change (Finset.univ.filter (fun j : Fin 1 =>
      ∃ c : ℝ, acquisition ([].take j.val) = c • (0 : Mat))).card ≠
      (Finset.univ.filter (fun j : Fin 1 =>
      ∃ c : ℝ, acquisition ([].take j.val) = c • (1 : Mat))).card
    simp [he, show ∃ c : ℝ, (1 : Mat) = c • (1 : Mat) from ⟨1,by simp⟩]

def entry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@cumulative_proportionality_card_even)
    (type_of% (realize signature (fun _ w L => (Finset.univ.filter
      (fun i : Fin (w.length+1) => ∃ c : ℝ, acquisition (w.take i.val) = c • L)).card)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.evenUnit,
  realizationName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ w L => (Finset.univ.filter
    (fun i : Fin (w.length+1) => ∃ c : ℝ, acquisition (w.take i.val) = c • L)).card)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.GainRayWordGeometry, definition := none, coordinates := #[0], readouts := #[{
      path := #["body","body","body","body","body","fn","arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


abbrev switchSignature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Mat
  Anchor := Empty
  finiteAnchor := inferInstance

def switchActual : Realization switchSignature :=
  realize switchSignature (fun _ _ w => acquisition w) (fun e => nomatch e)

def switchRejected : Realization switchSignature :=
  realize switchSignature (fun _ _ _ => 0) (fun e => nomatch e)

def switchArena : Arena where
  signature := switchSignature
  Law R := ∀ (w : List Bool) (a : Bool) (k : ℕ) (r : List Bool)
    (_hk : 0 < k) (_hw : w = List.replicate k a ++ ((!a) :: r)),
    let K := Submodule.span ℝ
      (Set.range (fun i : Fin (w.length+1) => R.readout () () (w.take i.val)))
    (1 : Mat) ∈ K ∧ action a ∈ K ∧ action (!a) * action a ^ k ∈ K

theorem switchRejected_law : ¬ switchArena.Law switchRejected := by
  intro h
  have hh := (h [false,true] false 1 [] (by omega) rfl).1
  simpa [switchRejected,realize] using hh

def switchRegistration : Registration switchArena (switchArena.Law switchActual) where
  actual := switchActual
  bridge := Iff.rfl
  variation := ⟨first_switch_generators_mem,switchRejected,switchRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨switchRejected, ?_, rfl, switchRejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),[],[false],?_⟩
    intro he
    have h0 : acquisition [] = (1 : Mat) := by
      simpa using acquisition_pure false 0
    have h1 : acquisition [false] = action false := by
      simpa using acquisition_pure false 1
    change acquisition [] = acquisition [false] at he
    rw [h0,h1,action_m_shape] at he
    have hh := congrArg (fun A : Mat => A 0 0) he
    norm_num at hh

def switchEntry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@first_switch_generators_mem)
    (type_of% (realize switchSignature (fun _ _ w => acquisition w)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.switchUnit,
  realizationName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.switchRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨switchArena⟩,
  objectArena := .source ⟨switchArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source switchArena ⟨switchRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize switchSignature (fun _ _ w => acquisition w)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.GainRayWordGeometry, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body","body","body","body","body","body","value","arg","arg","body","fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


abbrev actionSignature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Mat
  Anchor := Empty
  finiteAnchor := inferInstance

def actionActual : Realization actionSignature :=
  realize actionSignature (fun _ _ a => action a) (fun e => nomatch e)

def actionRejected : Realization actionSignature :=
  realize actionSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem actionDependence : ObservationalDependence actionSignature actionActual := by
  intro i
  refine ⟨(),false,true,?_⟩
  intro he
  have hh := congrArg (fun A : Mat => A 1 1) he
  norm_num [actionActual,realize,action_m_shape,action_j_shape] at hh

def mShapeArena : Arena where
  signature := actionSignature
  Law R := R.readout () () false = !![0,1;1,1]

theorem mShapeRejected : ¬ mShapeArena.Law actionRejected := by
  intro he
  have hh := congrArg (fun A : Mat => A 0 1) he
  change (0 : ℝ) = 1 at hh
  exact zero_ne_one hh

def jShapeArena : Arena where
  signature := actionSignature
  Law R := R.readout () () true = !![0,1;1,0]

theorem jShapeRejected : ¬ jShapeArena.Law actionRejected := by
  intro he
  have hh := congrArg (fun A : Mat => A 0 1) he
  change (0 : ℝ) = 1 at hh
  exact zero_ne_one hh

abbrev independenceSignature : Signature where
  Params := Bool × ℕ
  State _ := Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Mat
  Anchor := Empty
  finiteAnchor := inferInstance

def independenceActual : Realization independenceSignature :=
  realize independenceSignature (fun _ p i =>
    ![(1 : Mat), action p.1, action (!p.1) * action p.1 ^ p.2] i)
    (fun e => nomatch e)

def independenceRejected : Realization independenceSignature :=
  realize independenceSignature (fun _ _ _ => 0) (fun e => nomatch e)

def independenceArena : Arena where
  signature := independenceSignature
  Law R := ∀ (a : Bool) (k : ℕ) (_hk : 0 < k),
    LinearIndependent ℝ (R.readout () (a,k))

theorem independenceRejected_law : ¬ independenceArena.Law independenceRejected := by
  intro h
  have hh := (h false 1 zero_lt_one).ne_zero (0 : Fin 3)
  exact hh rfl

theorem independenceDependence :
    ObservationalDependence independenceSignature independenceActual := by
  intro i
  refine ⟨(false,1),0,1,?_⟩
  intro he
  have hh := congrArg (fun A : Mat => A 0 0) he
  change (1 : Mat) 0 0 = action false 0 0 at hh
  rw [action_m_shape] at hh
  norm_num at hh

abbrev powerSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Mat
  Anchor := Empty
  finiteAnchor := inferInstance

def powerActual : Realization powerSignature :=
  realize powerSignature (fun _ _ k => action false ^ k) (fun e => nomatch e)

def powerRejected : Realization powerSignature :=
  realize powerSignature (fun _ _ _ => 0) (fun e => nomatch e)

def powerArena : Arena where
  signature := powerSignature
  Law R := ∀ k : ℕ, ∃ a b : ℝ, 0 ≤ a ∧ 0 < b ∧
    R.readout () () (k+1) = a • (1 : Mat) + b • action false

theorem powerRejected_law : ¬ powerArena.Law powerRejected := by
  intro h
  obtain ⟨a,b,ha,hb,he⟩ := h 0
  have hh := congrArg (fun A : Mat => A 0 1) he
  change (0 : ℝ) = a * (1 : Mat) 0 1 + b * action false 0 1 at hh
  rw [action_m_shape] at hh
  norm_num at hh
  linarith

theorem powerDependence : ObservationalDependence powerSignature powerActual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro he
  have hh := congrArg (fun A : Mat => A 0 0) he
  change (action false ^ 0) 0 0 = (action false ^ 1) 0 0 at hh
  rw [pow_zero,pow_one,action_m_shape] at hh
  norm_num at hh

abbrev decompositionSignature : Signature where
  Params := Unit
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def decompositionActual : Realization decompositionSignature :=
  realize decompositionSignature (fun _ _ w => w) (fun e => nomatch e)

def decompositionRejected : Realization decompositionSignature :=
  realize decompositionSignature (fun _ _ _ => []) (fun e => nomatch e)

def decompositionArena : Arena where
  signature := decompositionSignature
  Law R := ∀ (w : List Bool) (_hM : false ∈ w) (_hJ : true ∈ w),
    ∃ a : Bool, ∃ k : ℕ, ∃ r : List Bool,
      0 < k ∧ R.readout () () w = List.replicate k a ++ ((!a) :: r)

theorem decompositionRejected_law : ¬ decompositionArena.Law decompositionRejected := by
  intro h
  obtain ⟨a,k,r,hk,he⟩ := h [false,true] (by simp) (by simp)
  have hh := congrArg List.length he
  simp [decompositionRejected,realize] at hh

theorem decompositionDependence :
    ObservationalDependence decompositionSignature decompositionActual := by
  intro i
  exact ⟨(),[],[false],by simp [decompositionActual,realize]⟩

def unitArena : Arena where
  signature := switchSignature
  Law R := ∀ v : List Bool, IsUnit (R.readout () () v)

theorem unitRejected_law : ¬ unitArena.Law switchRejected := by
  intro h
  exact (h []).ne_zero rfl

theorem acquisitionDependence : ObservationalDependence switchSignature switchActual :=
  switchRegistration.dependence


def mShapeRegistration : Registration mShapeArena (mShapeArena.Law actionActual) where
  actual := actionActual
  bridge := Iff.rfl
  variation := ⟨action_m_shape,actionRejected,mShapeRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨actionRejected, ?_, rfl, mShapeRejected⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := actionDependence

def mShapeEntry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@action_m_shape) (type_of% (realize actionSignature (fun _ _ a => action a)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.mShapeUnit,
  realizationName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.mShapeRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨mShapeArena⟩, objectArena := .source ⟨mShapeArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source mShapeArena ⟨mShapeRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize actionSignature (fun _ _ a => action a) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.GainRayWordGeometry,
    definition := none, coordinates := #[], readouts := #[{
      path := #["fn","arg","fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


def jShapeRegistration : Registration jShapeArena (jShapeArena.Law actionActual) where
  actual := actionActual
  bridge := Iff.rfl
  variation := ⟨action_j_shape,actionRejected,jShapeRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨actionRejected, ?_, rfl, jShapeRejected⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := actionDependence

def jShapeEntry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@action_j_shape) (type_of% (realize actionSignature (fun _ _ a => action a)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.jShapeUnit,
  realizationName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.jShapeRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨jShapeArena⟩, objectArena := .source ⟨jShapeArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source jShapeArena ⟨jShapeRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize actionSignature (fun _ _ a => action a) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.GainRayWordGeometry,
    definition := none, coordinates := #[], readouts := #[{
      path := #["fn","arg","fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


def independenceRegistration : Registration independenceArena (independenceArena.Law independenceActual) where
  actual := independenceActual
  bridge := Iff.rfl
  variation := ⟨first_switch_independent,independenceRejected,independenceRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨independenceRejected, ?_, rfl, independenceRejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := independenceDependence

def independenceEntry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@first_switch_independent) (type_of% (realize independenceSignature (fun _ p i =>
      ![(1 : Mat), action p.1, action (!p.1) * action p.1 ^ p.2] i)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.independenceUnit,
  realizationName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.independenceRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨independenceArena⟩, objectArena := .source ⟨independenceArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source independenceArena ⟨independenceRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize independenceSignature (fun _ p i =>
      ![(1 : Mat), action p.1, action (!p.1) * action p.1 ^ p.2] i) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.GainRayWordGeometry,
    definition := none, coordinates := #[0,1], readouts := #[{
      path := #["body","body","body","fn","fn","fn","arg"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


def powerRegistration : Registration powerArena (powerArena.Law powerActual) where
  actual := powerActual
  bridge := Iff.rfl
  variation := ⟨m_power_coordinates,powerRejected,powerRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨powerRejected, ?_, rfl, powerRejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := powerDependence

def powerEntry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@m_power_coordinates) (type_of% (realize powerSignature (fun _ _ k => action false ^ k)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.powerUnit,
  realizationName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.powerRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨powerArena⟩, objectArena := .source ⟨powerArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source powerArena ⟨powerRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize powerSignature (fun _ _ k => action false ^ k) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.GainRayWordGeometry,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body","arg","body","arg","body","arg","arg","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


def decompositionRegistration : Registration decompositionArena (decompositionArena.Law decompositionActual) where
  actual := decompositionActual
  bridge := Iff.rfl
  variation := ⟨switch_decomposition,decompositionRejected,decompositionRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨decompositionRejected, ?_, rfl, decompositionRejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := decompositionDependence

def decompositionEntry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@switch_decomposition) (type_of% (realize decompositionSignature (fun _ _ w => w)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.decompositionUnit,
  realizationName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.decompositionRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨decompositionArena⟩, objectArena := .source ⟨decompositionArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source decompositionArena ⟨decompositionRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize decompositionSignature (fun _ _ w => w) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.GainRayWordGeometry,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body","body","body","arg","body","arg","body","arg","body","arg","fn","arg"],
      stateBinder := 0, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }


def unitRegistration : Registration unitArena (unitArena.Law switchActual) where
  actual := switchActual
  bridge := Iff.rfl
  variation := ⟨acquisition_unit,switchRejected,unitRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨switchRejected, ?_, rfl, unitRejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := acquisitionDependence

def unitEntry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@acquisition_unit) (type_of% (realize switchSignature (fun _ _ w => acquisition w)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.unitUnit,
  realizationName := `Reg.D5.S3.Observer.Linear.GainRayWordGeometry.unitRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨unitArena⟩, objectArena := .source ⟨unitArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source unitArena ⟨unitRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize switchSignature (fun _ _ w => acquisition w) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.GainRayWordGeometry,
    definition := none, coordinates := #[], readouts := #[{
      path := #["body","arg","fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.Observer.Linear.GainRayWordGeometry
