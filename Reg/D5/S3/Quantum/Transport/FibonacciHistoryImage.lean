import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Transport.FibonacciHistoryImage
import Reg.Support.DependentFamily

/-! Full-family registrations for native history realization and image cardinality. -/

open _root_.D5.S3.Quantum.Transport.FibonacciPrefix
open _root_.D5.S3.Quantum.Transport.FibonacciHistoryImage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

namespace Reg.D5.S3.Quantum.Transport.FibonacciHistoryImage

abbrev signature : Signature where
  Params := Σ _d : ℕ, ℕ
  State p := ZMod p.1 × ZMod p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.2 → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p a => carryPrefix p.1 p.2 a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d N : ℕ) (hd : 2 ≤ d) (a : ZMod d × ZMod d),
    (∀ j : ℕ, (carryHistory d a j : ℤ) =
      ⌊linearLayer (j + 2) (normalizedState d a)⌋ -
        ⌊linearLayer j (normalizedState d a)⌋ -
        ⌊linearLayer (j + 1) (normalizedState d a)⌋) ∧
    R.readout () ⟨d, N⟩ a = layerHistory N (normalizedState d a) ∧
    ∃ w : ℝ × ℝ, (0 < w.1 ∧ w.1 < 1) ∧ (0 < w.2 ∧ w.2 < 1) ∧
      (∀ m < N + 2, ⌊linearLayer m w⌋ = ⌊linearLayer m (normalizedState d a)⌋ ∧
        0 < Int.fract (linearLayer m w)) ∧
      carryPrefix d N a = layerHistory N w

theorem actual_law : arena.Law actual := by
  intro d N hd a
  exact native_history_interior_realization d N hd a

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have heq := congrFun (h 2 1 (by omega) (0, 0)).2.1 (0 : Fin 1)
  norm_num [rejected, realize, layerHistory, linearLayer, normalizedState,
    _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.step] at heq

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 1⟩, (0, 0), (1, 1), ?_⟩
  intro h
  have heq := congrFun h (0 : Fin 1)
  norm_num [actual, realize, carryPrefix, carryHistory, lowTrajectory,
    _root_.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.carry,
    ZMod.val_one_eq_one_mod] at heq

def registration : Registration arena
    (type_of% (@_root_.D5.S3.Quantum.Transport.FibonacciHistoryImage.native_history_interior_realization)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := dependence

def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Transport.FibonacciHistoryImage.native_history_interior_realization)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ p a => carryPrefix p.1 p.2 a) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Transport.FibonacciHistoryImage.native_history_interior_realization.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Transport.FibonacciHistoryImage.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ p a => carryPrefix p.1 p.2 a) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Transport.FibonacciHistoryImage,
    definition := none,
    coordinates := #[0,1],
    readouts := #[{
      path := #["body","body","body","body","arg","fn","arg","fn","arg"],
      stateBinder := 3,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }


namespace ImageCount

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ d N => (Set.range (carryPrefix d N)).ncard) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 5) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d N : ℕ) (_hd : 2 ≤ d),
    (Set.range (carryPrefix d N)).Finite ∧
    R.readout () d N ≤ 4 * (Nat.fib (N+5)-N-4) ∧
    (((4 * (Nat.fib (N+5)-N-4) : ℕ) : ℝ) ≤ 4*((1+Real.sqrt 5)/2)^(N+4)) ∧
    (((Nat.fib (N+5)-N-4 : ℕ) : ℝ) = (Nat.fib (N+5) : ℝ)-N-4)

theorem actual_law : arena.Law actual := by
  intro d N hd
  exact native_history_image_bound d N hd

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := (h 2 0 (by omega)).2.1
  norm_num [rejected,realize] at hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hz : (Set.range (carryPrefix 2 0)).ncard = 1 := by
    have he : Set.range (carryPrefix 2 0) = {carryPrefix 2 0 (0,0)} := by
      ext w
      simp only [Set.mem_range,Set.mem_singleton_iff]
      constructor
      · rintro ⟨a,rfl⟩
        exact Subsingleton.elim _ _
      · intro h
        exact ⟨(0,0),h.symm⟩
    rw [he,Set.ncard_singleton]
  have hp : 1 < (Set.range (carryPrefix 2 1)).ncard := by
    apply (Set.one_lt_ncard (Set.finite_range (carryPrefix 2 1))).mpr
    refine ⟨carryPrefix 2 1 (0,0),⟨(0,0),rfl⟩,carryPrefix 2 1 (1,1),⟨(1,1),rfl⟩,?_⟩
    intro h
    have heq := congrFun h (0 : Fin 1)
    norm_num [carryPrefix,carryHistory,lowTrajectory,
      _root_.D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.carry,
      ZMod.val_one_eq_one_mod] at heq
  refine ⟨2,0,1,?_⟩
  intro h
  change (Set.range (carryPrefix 2 0)).ncard = (Set.range (carryPrefix 2 1)).ncard at h
  omega

def registration : Registration arena
    (type_of% (@_root_.D5.S3.Quantum.Transport.FibonacciHistoryImage.native_history_image_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := dependence

def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Transport.FibonacciHistoryImage.native_history_image_bound)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ d N => (Set.range (carryPrefix d N)).ncard) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Transport.FibonacciHistoryImage.native_history_image_bound.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Transport.FibonacciHistoryImage.ImageCount.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ d N => (Set.range (carryPrefix d N)).ncard) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Transport.FibonacciHistoryImage,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body","body","body","arg","fn","arg","fn","arg"],
      stateBinder := 1,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end ImageCount

end Reg.D5.S3.Quantum.Transport.FibonacciHistoryImage
