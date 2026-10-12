import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics
open Matrix Filter Topology

namespace Reg.D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics
noncomputable section

abbrev extensionSignature : Signature where
  Params := ℕ
  State := fun m => Fin m → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ m => Fin (m + 2) → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def extensionActual : Realization extensionSignature := realize extensionSignature
  (fun _ _ z => zeroExtend z) (fun e => nomatch e)

def extensionRejected : Realization extensionSignature := realize extensionSignature
  (fun _ _ _ _ => 1) (fun e => nomatch e)

theorem extensionZero (m : ℕ) : zeroExtend (0 : Fin m → ℂ) = 0 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · exact extend_last (0 : Fin m → ℂ)
    · simpa using (extend_interior (0 : Fin m → ℂ) k)

theorem extensionDependence : ObservationalDependence extensionSignature extensionActual := by
  intro i
  refine ⟨1, 0, (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h ((0 : Fin 1).castSucc.succ)
  change zeroExtend (0 : Fin 1 → ℂ) ((0 : Fin 1).castSucc.succ) =
    zeroExtend (fun _ : Fin 1 => 1) ((0 : Fin 1).castSucc.succ) at hh
  rw [extend_interior, extend_interior] at hh
  norm_num [Pi.zero_apply] at hh

abbrev interiorArena : Arena where
  signature := extensionSignature
  Law R := ∀ {m : ℕ} (z : Fin m → ℂ) (i : Fin m),
    R.readout () m z i.castSucc.succ = z i

theorem interiorRejectedLaw : ¬ interiorArena.Law extensionRejected := by
  intro h
  have hh := h (m := 1) 0 0
  norm_num [extensionRejected, realize] at hh

def interiorRecord : Registration interiorArena (type_of% (@extend_interior)) where
  actual := extensionActual
  bridge := Iff.rfl
  variation := ⟨extend_interior, extensionRejected, interiorRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨extensionRejected, ?_, rfl, interiorRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := extensionDependence

abbrev lastArena : Arena where
  signature := extensionSignature
  Law R := ∀ {m : ℕ} (z : Fin m → ℂ),
    R.readout () m z (Fin.last (m + 1)) = 0

theorem lastRejectedLaw : ¬ lastArena.Law extensionRejected := by
  intro h
  have hh := h (m := 0) 0
  norm_num [extensionRejected, realize] at hh

def lastRecord : Registration lastArena (type_of% (@extend_last)) where
  actual := extensionActual
  bridge := Iff.rfl
  variation := ⟨extend_last, extensionRejected, lastRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨extensionRejected, ?_, rfl, lastRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := extensionDependence

abbrev vectorSignature : Signature where
  Params := ℕ
  State := fun m => Fin m → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ m => Fin m → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def vectorActual : Realization vectorSignature := realize vectorSignature
  (fun _ _ z => z) (fun e => nomatch e)

def vectorRejected : Realization vectorSignature := realize vectorSignature
  (fun _ _ _ _ => 1) (fun e => nomatch e)

theorem vectorDependence : ObservationalDependence vectorSignature vectorActual := by
  intro i
  refine ⟨1, 0, (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h 0
  change (0 : ℂ) = 1 at hh
  exact zero_ne_one hh

abbrev harmonicArena : Arena where
  signature := vectorSignature
  Law R := ∀ {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : ∀ j, 0 < v j)
    (z : Fin m → ℂ)
    (hfix : ∀ i : Fin m,
      (z i - zeroExtend z i.castSucc.castSucc) / (v i.castSucc : ℂ) =
      (zeroExtend z i.succ.succ - z i) / (v i.succ : ℂ)),
    R.readout () m z = 0

theorem harmonicRejectedLaw : ¬ harmonicArena.Law vectorRejected := by
  intro h
  have hh := h (m := 1) (fun _ => 1) (by intro j; norm_num) 0
    (by intro i; simp [extensionZero, Pi.zero_apply])
  have h0 := congrFun hh 0
  change (1 : ℂ) = 0 at h0
  exact one_ne_zero h0

def harmonicRecord : Registration harmonicArena (type_of% (@harmonic_dirichlet_zero)) where
  actual := vectorActual
  bridge := Iff.rfl
  variation := ⟨harmonic_dirichlet_zero, vectorRejected, harmonicRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨vectorRejected, ?_, rfl, harmonicRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := vectorDependence

abbrev boundaryArena : Arena where
  signature := vectorSignature
  Law R := ∀ {m : ℕ} (hm : 1 ≤ m) (z : Fin m → ℂ)
    (hz : z ⟨0, by omega⟩ = 0)
    (hprop : ∀ i : Fin m, z i = 0 → zeroExtend z i.castSucc.castSucc = 0 →
      zeroExtend z i.succ.succ = 0), R.readout () m z = 0

theorem boundaryRejectedLaw : ¬ boundaryArena.Law vectorRejected := by
  intro h
  have hh := h (m := 1) (by norm_num) 0 (by simp)
    (by intro i hi hl; simp [extensionZero, Pi.zero_apply])
  have h0 := congrFun hh 0
  change (1 : ℂ) = 0 at h0
  exact one_ne_zero h0

def boundaryRecord : Registration boundaryArena (type_of% (@boundary_zero_observability)) where
  actual := vectorActual
  bridge := Iff.rfl
  variation := ⟨boundary_zero_observability, vectorRejected, boundaryRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨vectorRejected, ?_, rfl, boundaryRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := vectorDependence

abbrev powerSignature : Signature where
  Params := Σ m : ℕ, Matrix (Fin m) (Fin m) ℝ
  State := fun p => Fin p.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => ℕ → (Fin p.1 → ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def powerActual : Realization powerSignature := realize powerSignature
  (fun _ p u k => (p.2 ^ k).mulVec u) (fun e => nomatch e)

def powerRejected : Realization powerSignature := realize powerSignature
  (fun _ _ _ _ _ => 1) (fun e => nomatch e)

abbrev powerArena : Arena where
  signature := powerSignature
  Law R := ∀ {m : ℕ} (hm : 1 ≤ m) (N : Matrix (Fin m) (Fin m) ℝ)
    (hN : ∀ c ∈ spectrum ℂ (N.map (algebraMap ℝ ℂ)), ‖c‖ < 1)
    (u : Fin m → ℝ), Tendsto (R.readout () ⟨m, N⟩ u) atTop (nhds 0)

theorem powerRejectedLaw : ¬ powerArena.Law powerRejected := by
  intro h
  have hN : ∀ c ∈ spectrum ℂ
      ((0 : Matrix (Fin 1) (Fin 1) ℝ).map (algebraMap ℝ ℂ)), ‖c‖ < 1 := by
    intro c hc
    have hc0 : c = 0 := by simpa using hc
    simp [hc0]
  have ht := h (m := 1) (by norm_num) 0 hN 0
  have he : (fun _ : Fin 1 => (1 : ℝ)) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds ht
  have hh := congrFun he 0
  norm_num at hh

def powerRecord : Registration powerArena (type_of% (@real_mulVec_powers_tendsto_zero)) where
  actual := powerActual
  bridge := Iff.rfl
  variation := ⟨real_mulVec_powers_tendsto_zero, powerRejected, powerRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨powerRejected, ?_, rfl, powerRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, 0⟩, 0, (fun _ => 1), ?_⟩
    intro h
    have hh := congrFun (congrFun h 0) 0
    norm_num [powerActual, realize] at hh

noncomputable def extend_interior_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.extend_interior)
    (type_of% (realize.{0,0,0,0,0} extensionSignature
      (fun _ _ z => zeroExtend z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.extend_interior.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.interiorRecord,
  realizationSource := none,
  generated := false,
  arena := .source ⟨interiorArena⟩,
  objectArena := .source ⟨interiorArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source interiorArena ⟨interiorRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} extensionSignature
    (fun _ _ z => zeroExtend z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn"],
      stateBinder := 1, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def extend_last_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.extend_last)
    (type_of% (realize.{0,0,0,0,0} extensionSignature
      (fun _ _ z => zeroExtend z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.extend_last.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.lastRecord,
  realizationSource := none,
  generated := false,
  arena := .source ⟨lastArena⟩,
  objectArena := .source ⟨lastArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source lastArena ⟨lastRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} extensionSignature
    (fun _ _ z => zeroExtend z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn"],
      stateBinder := 1, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def harmonic_dirichlet_zero_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.harmonic_dirichlet_zero)
    (type_of% (realize.{0,0,0,0,0} vectorSignature
      (fun _ _ z => z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.harmonic_dirichlet_zero.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.harmonicRecord,
  realizationSource := none,
  generated := false,
  arena := .source ⟨harmonicArena⟩,
  objectArena := .source ⟨harmonicArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source harmonicArena ⟨harmonicRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} vectorSignature
    (fun _ _ z => z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 3, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def boundary_zero_observability_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.boundary_zero_observability)
    (type_of% (realize.{0,0,0,0,0} vectorSignature
      (fun _ _ z => z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.boundary_zero_observability.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.boundaryRecord,
  realizationSource := none,
  generated := false,
  arena := .source ⟨boundaryArena⟩,
  objectArena := .source ⟨boundaryArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source boundaryArena ⟨boundaryRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} vectorSignature
    (fun _ _ z => z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

noncomputable def real_mulVec_powers_tendsto_zero_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.real_mulVec_powers_tendsto_zero)
    (type_of% (realize.{0,0,0,0,0} powerSignature
      (fun _ p u k => (p.2 ^ k).mulVec u) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.real_mulVec_powers_tendsto_zero.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics.powerRecord,
  realizationSource := none,
  generated := false,
  arena := .source ⟨powerArena⟩,
  objectArena := .source ⟨powerArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source powerArena ⟨powerRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} powerSignature
    (fun _ p u k => (p.2 ^ k).mulVec u) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics,
    definition := none,
    coordinates := #[0, 2],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn", "arg"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms interiorRecord
#print axioms lastRecord
#print axioms harmonicRecord
#print axioms boundaryRecord
#print axioms powerRecord
end
end Reg.D5.S3.Quantum.Dynamics.TridiagonalSweeps.FinitePathDynamics
