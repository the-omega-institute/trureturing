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
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.GeometryEntranceRatio
