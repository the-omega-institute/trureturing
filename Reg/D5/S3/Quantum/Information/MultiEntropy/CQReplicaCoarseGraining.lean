import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Information.MultiEntropy.CQReplicaCoarseGraining

noncomputable section

open LeanInformationAudit
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.MultiEntropyPositivityRefutation (E IsUnitState)
open _root_.D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.CQReplica
  (IsBlockDiagonalOnA blocks densityAB E_eq_trace_tensor_sum_pow
    E_coarseGraining_all_mergers renyi_coarseGraining_all_mergers
    mergeAB mergeAC mergeBC)

namespace Reg.D5.S3.Quantum.Information.MultiEntropy.CQReplicaCoarseGraining

universe u

private abbrev observation := signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization observation :=
  realize observation (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization observation :=
  realize observation (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := observation
  Law R := ∀ {L : Fin 3 → Type u} [∀ i, Fintype (L i)]
    (n : ℕ) [NeZero n] (_hn : 2 ≤ n) (ψ : ((i : Fin 3) → L i) → ℂ)
    (_hψ : IsUnitState ψ) (_hρ : IsBlockDiagonalOnA (densityAB ψ)),
    (E n 3 ψ).im = 0 ∧ 0 < (E n 3 ψ).re ∧
      R.readout () () (E n 3 ψ).re ((E n 2 (mergeAB ψ)).re ^ n) ∧
      R.readout () () (E n 3 ψ).re ((E n 2 (mergeBC ψ)).re ^ n) ∧
      R.readout () () (E n 3 ψ).re ((E n 2 (mergeAC ψ)).re ^ n)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let L : Fin 3 → Type u := fun _ => PUnit.{u + 1}
  let ψ : ((i : Fin 3) → L i) → ℂ := fun _ => 1
  have hψ : IsUnitState ψ := by simp [IsUnitState, ψ, L]
  have hρ : IsBlockDiagonalOnA (densityAB ψ) := by
    intro a c _ _ hne
    exact (hne (Subsingleton.elim a c)).elim
  exact (h (L := L) 2 le_rfl ψ hψ hρ).2.2.1

private theorem dependence : ObservationalDependence observation actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hbad := congrFun he 0
  norm_num [actual, realize] at hbad

def family : Registration arena.{u} (type_of% (@E_coarseGraining_all_mergers.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@E_coarseGraining_all_mergers.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity arena.{u}.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@E_coarseGraining_all_mergers.{u}) (Realization observation) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.CQReplica.E_coarseGraining_all_mergers.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Information.MultiEntropy.CQReplicaCoarseGraining.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.MultiEntropy.CQReplicaCoarseGraining
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Renyi

private abbrev renyiArena : Arena where
  signature := observation
  Law R := ∀ {L : Fin 3 → Type u} [∀ i, Fintype (L i)]
    (n : ℕ) [NeZero n] (_hn : 2 ≤ n) (ψ : ((i : Fin 3) → L i) → ℂ)
    (_hψ : IsUnitState ψ) (_hρ : IsBlockDiagonalOnA (densityAB ψ))
    (y : ℝ) (_hy : y ∈ [(E n 2 (mergeAB ψ)).re, (E n 2 (mergeBC ψ)).re,
      (E n 2 (mergeAC ψ)).re]),
    0 < y ∧ R.readout () () (-Real.log y / ((n : ℝ) - 1))
      (-Real.log (E n 3 ψ).re / ((n : ℝ) * ((n : ℝ) - 1)))

private theorem renyi_rejected_law : ¬ renyiArena.{u}.Law rejected := by
  intro h
  let L : Fin 3 → Type u := fun _ => PUnit.{u + 1}
  let ψ : ((i : Fin 3) → L i) → ℂ := fun _ => 1
  have hψ : IsUnitState ψ := by simp [IsUnitState, ψ, L]
  have hρ : IsBlockDiagonalOnA (densityAB ψ) := by
    intro a c _ _ hne
    exact (hne (Subsingleton.elim a c)).elim
  exact (h (L := L) 2 le_rfl ψ hψ hρ (E 2 2 (mergeAB ψ)).re (by simp)).2

def renyiFamily : Registration renyiArena.{u}
    (type_of% (@renyi_coarseGraining_all_mergers.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@renyi_coarseGraining_all_mergers.{u}, rejected, renyi_rejected_law⟩
  sensitivity := sensitivity renyiArena.{u}.Law actual rejected renyi_rejected_law
  dependence := dependence

def renyiRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@renyi_coarseGraining_all_mergers.{u}) (Realization observation) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.CQReplica.renyi_coarseGraining_all_mergers.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Information.MultiEntropy.CQReplicaCoarseGraining.Renyi.renyiFamily
  realizationSource := none
  generated := false
  arena := .source ⟨renyiArena.{u}⟩
  objectArena := .source ⟨renyiArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source renyiArena.{u} ⟨renyiFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.MultiEntropy.CQReplicaCoarseGraining
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Renyi

namespace Contraction

open _root_.CQReplicaRegroupingSupplier (cqTensorSum)

private abbrev traceObservation := signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

private def traceActual : Realization traceObservation :=
  realize traceObservation (fun _ _ x y => x = y) (fun e => nomatch e)

private def traceRejected : Realization traceObservation :=
  realize traceObservation (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev traceArena : Arena where
  signature := traceObservation
  Law R := ∀ {L : Fin 3 → Type u} (n : ℕ) [NeZero n] [∀ i, Fintype (L i)]
    [DecidableEq (L 1)] (ψ : ((i : Fin 3) → L i) → ℂ)
    (_hρ : IsBlockDiagonalOnA (densityAB ψ)),
    R.readout () () (E n 3 ψ) (Matrix.trace ((cqTensorSum (blocks (densityAB ψ)) n) ^ n))

private theorem trace_rejected_law : ¬ traceArena.{u}.Law traceRejected := by
  intro h
  let L : Fin 3 → Type u := fun _ => PUnit.{u + 1}
  let ψ : ((i : Fin 3) → L i) → ℂ := fun _ => 0
  have hρ : IsBlockDiagonalOnA (densityAB ψ) := by
    intro a c _ _ hne
    exact (hne (Subsingleton.elim a c)).elim
  exact h (L := L) 2 ψ hρ

private theorem trace_dependence : ObservationalDependence traceObservation traceActual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hbad : (1 : ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hbad

def traceFamily : Registration traceArena.{u}
    (type_of% (@E_eq_trace_tensor_sum_pow.{u})) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨@E_eq_trace_tensor_sum_pow.{u}, traceRejected, trace_rejected_law⟩
  sensitivity := sensitivity traceArena.{u}.Law traceActual traceRejected trace_rejected_law
  dependence := trace_dependence

def traceRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@E_eq_trace_tensor_sum_pow.{u}) (Realization traceObservation) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.CQReplica.E_eq_trace_tensor_sum_pow.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Information.MultiEntropy.CQReplicaCoarseGraining.Contraction.traceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨traceArena.{u}⟩
  objectArena := .source ⟨traceArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source traceArena.{u} ⟨traceFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceObservation (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.MultiEntropy.CQReplicaCoarseGraining
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Contraction

end Reg.D5.S3.Quantum.Information.MultiEntropy.CQReplicaCoarseGraining
