import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio
import Reg.Support.DependentFamily

open _root_.D5.S3.Combinatorics.Partitions.PaddedWordPartition
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

@[reducible] def countSignature : Signature where
  Params := Unit
  State _ := Five
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def countActual : Realization countSignature :=
  realize countSignature (fun _ _ g => M g) (fun e => nomatch e)

def countingRejected : Realization countSignature :=
  realize countSignature (fun _ _ g => H g + 1) (fun e => nomatch e)

def zeroRejected : Realization countSignature :=
  realize countSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem countDependence : ObservationalDependence countSignature countActual := by
  intro i
  rcases sharp_geometry_entrance_ratio.2.2.1 with
    ⟨_, _, _, _, hba, _, _, _, _, _, hbab, _⟩
  refine ⟨(), ba, bab, ?_⟩
  change M ba ≠ M bab
  rw [hba, hbab]
  decide

@[reducible] def countingArena : Arena where
  signature := countSignature
  Law R := ∀ g : Five,
    (0 < N g → R.readout () () g = catalan (N g-1) * m g) ∧
    H g = R.readout () () g + H (Linv g) ∧ m (Linv g) ≤ m g ∧ R.readout () () g ≤ H g

theorem countingRejectedLaw : ¬ countingArena.Law countingRejected := by
  intro h
  have hh := (h ba).2.2.2
  change H ba + 1 ≤ H ba at hh
  omega

def countingRegistration : Registration countingArena (countingArena.Law countActual) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨actual_fiber_counting, countingRejected, countingRejectedLaw⟩
  sensitivity := ⟨fun i => ⟨countingRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, countingRejectedLaw⟩,
    fun i => nomatch i⟩
  dependence := countDependence


#print axioms countingRegistration

@[reducible] def estimateArena : Arena where
  signature := countSignature
  Law R := ∀ g : Five,
    R.readout () () g ≤ H g ∧
    (N g = 1 → H g ≤ 2*R.readout () () g) ∧
    (N g = 2 → H g ≤ 3*R.readout () () g) ∧
    (N g = 3 → 2*H g ≤ 5*R.readout () () g) ∧
    (4 ≤ N g → H g ≤ 2*R.readout () () g) ∧ H g ≤ 3*R.readout () () g

theorem estimateRejectedLaw : ¬ estimateArena.Law zeroRejected := by
  intro h
  rcases sharp_geometry_entrance_ratio.2.2.1 with
    ⟨_, _, _, _, _, hba, _, _, _, _, _, _⟩
  have hh := (h ba).2.2.2.2.2
  change H ba ≤ 3 * 0 at hh
  rw [hba] at hh
  omega

def estimateRegistration : Registration estimateArena (estimateArena.Law countActual) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨uniform_actual_entrance_estimate, zeroRejected, estimateRejectedLaw⟩
  sensitivity := ⟨fun i => ⟨zeroRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, estimateRejectedLaw⟩,
    fun i => nomatch i⟩
  dependence := countDependence


#print axioms estimateRegistration

@[reducible] def sharpArena : Arena where
  signature := countSignature
  Law R := (∀ g : Five, Nonempty (TreeFiber g) →
      SourceGuards g ∧ 0 < N g ∧ 0 < R.readout () () g ∧
      1 ≤ (H g : ℝ)/R.readout () () g ∧ (H g : ℝ)/R.readout () () g ≤ B (N g) ∧
      R.readout () () g ≤ H g ∧ H g ≤ 3*R.readout () () g) ∧
    (∀ n : ℕ, 0 < n →
      Nonempty (TreeFiber (pure true n)) ∧ Nonempty (TreeFiber (pure false n)) ∧
      N (pure true n) = n ∧ N (pure false n) = n ∧
      m (pure true n) = 1 ∧ m (pure false n) = 1 ∧
      R.readout () () (pure true n) = catalan (n-1) ∧ H (pure true n) = R.readout () () (pure true n) ∧
      R.readout () () (pure false n) = catalan (n-1) ∧ H (pure false n) = 2*R.readout () () (pure false n) ∧
      (H (pure true n) : ℝ)/R.readout () () (pure true n) = 1 ∧
      (H (pure false n) : ℝ)/R.readout () () (pure false n) = 2 ∧
      Nonempty (TreeFiber (upper n)) ∧ N (upper n) = n ∧
      (H (upper n) : ℝ)/R.readout () () (upper n) = B n) ∧
    (Nonempty (TreeFiber ba) ∧ N ba = 2 ∧
      (∀ w : WordFiber ba, w.val = [false,true]) ∧ m ba = 1 ∧ R.readout () () ba = 1 ∧ H ba = 3 ∧
      Nonempty (TreeFiber bab) ∧ N bab = 3 ∧
      (∀ w : WordFiber bab, w.val = [false,true,false]) ∧ m bab = 1 ∧ R.readout () () bab = 2 ∧ H bab = 5) ∧
    (∀ c : ℝ, (∀ g : Five, Nonempty (TreeFiber g) → (H g : ℝ)/R.readout () () g ≤ c) → 3 ≤ c)

theorem sharpRejectedLaw : ¬ sharpArena.Law zeroRejected := by
  intro h
  rcases h.2.2.1 with ⟨_, _, _, _, hba, _, _, _, _, _, _, _⟩
  change (0 : ℕ) = 1 at hba
  exact Nat.zero_ne_one hba

def sharpRegistration : Registration sharpArena (sharpArena.Law countActual) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨sharp_geometry_entrance_ratio, zeroRejected, sharpRejectedLaw⟩
  sensitivity := ⟨fun i => ⟨zeroRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, sharpRejectedLaw⟩,
    fun i => nomatch i⟩
  dependence := countDependence


#print axioms sharpRegistration

def countingReadoutSelection : LeanInformationAudit.Contract.ReadoutSelection := {
  path := #["body", "fn", "arg", "body", "fn", "arg", "fn"],
  stateBinder := 0,
  functionOperand := true,
  stateOperand := none,
  booleanPredicate := false }

def estimateReadoutSelection : LeanInformationAudit.Contract.ReadoutSelection := {
  path := #["body", "fn", "arg", "fn", "arg", "fn"],
  stateBinder := 0,
  functionOperand := true,
  stateOperand := none,
  booleanPredicate := false }

def sharpReadoutSelection : LeanInformationAudit.Contract.ReadoutSelection := {
  path := #["fn", "arg", "body", "body", "arg", "arg", "fn", "arg", "arg", "fn"],
  stateBinder := 0,
  functionOperand := true,
  stateOperand := none,
  booleanPredicate := false }

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio.actual_fiber_counting)
    (type_of% (realize countSignature countActual.readout countActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio.actual_fiber_counting
    "Reg.D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio/countingArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio.countingRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨countingArena⟩,
  objectArena := .source ⟨countingArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source countingArena ⟨countingRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize countSignature countActual.readout countActual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio,
    definition := none,
    coordinates := #[],
    readouts := #[countingReadoutSelection] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio.uniform_actual_entrance_estimate)
    (type_of% (realize countSignature countActual.readout countActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio.uniform_actual_entrance_estimate
    "Reg.D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio/estimateArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio.estimateRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨estimateArena⟩,
  objectArena := .source ⟨estimateArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source estimateArena ⟨estimateRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize countSignature countActual.readout countActual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio,
    definition := none,
    coordinates := #[],
    readouts := #[estimateReadoutSelection] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio.sharp_geometry_entrance_ratio)
    (type_of% (realize countSignature countActual.readout countActual.anchor)) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio.sharp_geometry_entrance_ratio
    "Reg.D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio/sharpArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio.sharpRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨sharpArena⟩,
  objectArena := .source ⟨sharpArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source sharpArena ⟨sharpRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize countSignature countActual.readout countActual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio,
    definition := none,
    coordinates := #[],
    readouts := #[sharpReadoutSelection] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Combinatorics.Partitions.WordPartitionInverse (wd)

abbrev lengthSignature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def lengthActual : Realization lengthSignature :=
  realize lengthSignature (fun _ _ t => t.length) (fun e => nomatch e)
def lengthRejected : Realization lengthSignature :=
  realize lengthSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev lengthArena : Arena where
  signature := lengthSignature
  Law R := ∀ (g : Five) (t : TreeFiber g), R.readout () () t.val = N g

theorem lengthRejectedLaw : ¬ lengthArena.Law lengthRejected := by
  intro h
  let t : Source := .of true
  have ht : t.length = N (G (wd t)) := tree_length _ ⟨t,rfl⟩
  have hb := h (G (wd t)) ⟨t,rfl⟩
  change (0 : ℕ) = N (G (wd t)) at hb
  have hp := t.length_pos
  omega

theorem lengthDependence : ObservationalDependence lengthSignature lengthActual := by
  intro i
  cases i
  exact ⟨(), .of true, .mul (.of true) (.of true), by decide⟩

def lengthFamily : Registration lengthArena (type_of% (@tree_length)) where
  actual := lengthActual
  bridge := Iff.rfl
  variation := ⟨tree_length,lengthRejected,lengthRejectedLaw⟩
  sensitivity := ⟨fun _i => ⟨lengthRejected,
    fun _j h => (h (Subsingleton.elim _ _)).elim,rfl,lengthRejectedLaw⟩,fun i => nomatch i⟩
  dependence := lengthDependence

abbrev wordSignature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def wordActual : Realization wordSignature :=
  realize wordSignature (fun _ _ t => wd t) (fun e => nomatch e)
def wordRejected : Realization wordSignature :=
  realize wordSignature (fun _ _ _ => [true]) (fun e => nomatch e)
abbrev wordArena : Arena where
  signature := wordSignature
  Law R := ∀ t : Source, R.readout () () (substitution t) = sigma (R.readout () () t)

theorem wordRejectedLaw : ¬ wordArena.Law wordRejected := by
  intro h
  have hb := h (.of true)
  change [true] = [false] at hb
  cases hb

theorem wordDependence : ObservationalDependence wordSignature wordActual := by
  intro i
  cases i
  exact ⟨(), .of true, .of false, by decide⟩

def wordFamily : Registration wordArena (type_of% (@wd_substitution)) where
  actual := wordActual
  bridge := Iff.rfl
  variation := ⟨wd_substitution,wordRejected,wordRejectedLaw⟩
  sensitivity := ⟨fun _i => ⟨wordRejected,
    fun _j h => (h (Subsingleton.elim _ _)).elim,rfl,wordRejectedLaw⟩,fun i => nomatch i⟩
  dependence := wordDependence

def lengthRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tree_length) (type_of% (realize lengthSignature lengthActual.readout lengthActual.anchor))
    Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio.tree_length.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio.lengthFamily
  realizationSource := none
  generated := false
  arena := .source ⟨lengthArena⟩
  objectArena := .source ⟨lengthArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lengthArena ⟨lengthFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize lengthSignature lengthActual.readout lengthActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def wordRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@wd_substitution) (type_of% (realize wordSignature wordActual.readout wordActual.anchor))
    Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio.wd_substitution.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio.wordFamily
  realizationSource := none
  generated := false
  arena := .source ⟨wordArena⟩
  objectArena := .source ⟨wordArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source wordArena ⟨wordFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize wordSignature wordActual.readout wordActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg", "fn"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms tree_length
#print axioms wd_substitution
#print axioms lengthRegistration
#print axioms wordRegistration


end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio
