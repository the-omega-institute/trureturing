import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
import Reg.Support.DependentFamily

/-! Four-slot source-bound registrations for stabilizer multi-entropy collapse lemmas. -/

namespace Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse

open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
open _root_.D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open _root_.D5.S3.QuadraticForms.TernaryTranslationQuadraticNormalForm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

private def psi0 : (Fin 0 → Fin 2) → ℂ := fun _ => 1

private theorem psi0_norm : (∑ x : Fin 0 → Fin 2, ‖psi0 x‖ ^ 2) = 1 := by
  simp [psi0, Finset.sum_const]

private theorem graphAmp0_norm :
    (∑ x : Fin 0 → Fin 2, ‖graphAmp (0 : Matrix (Fin 0) (Fin 0) (ZMod 2)) x‖ ^ 2) = 1 := by
  classical
  simp [graphAmp.eq_1, norm_pow]

namespace ZSmul

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ c => c) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} (n q : ℕ) [NeZero n] (col : Fin N → Fin q)
    (ψ : (Fin N → Fin 2) → ℂ) (c : ℂ),
    Z n q col (c • ψ) = (star c * R.readout () () c) ^ (n ^ (q - 1)) * Z n q col ψ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := @h 0 1 1 inferInstance Fin.elim0 psi0 1
  simp only [rejected, realize, one_smul, Z_one, psi0_norm, Complex.ofReal_one] at hb
  norm_num at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, zero_ne_one⟩

def source_registration : Registration arena (type_of% @Z_smul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Z_smul, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩; exact ⟨rejected, fun ⟨⟩ hj => (hj rfl).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.Z_smul)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.ZSmul.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.ZSmul.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ZSmul

namespace ZOne

abbrev signature : Signature where
  Params := ℕ
  State N := (Fin N → Fin 2) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ N := (Fin N → Fin 2) → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ ψ => ψ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} (q : ℕ) (col : Fin N → Fin q) (ψ : (Fin N → Fin 2) → ℂ),
    Z 1 q col (R.readout () N ψ) = ((∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2 : ℝ) : ℂ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := @h 0 1 Fin.elim0 psi0
  rw [show rejected.readout () 0 psi0 = (fun _ => 0) from rfl, Z_one, psi0_norm] at hb
  simp at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨0, 0, psi0, ?_⟩
  intro he
  have h0 := congrFun he Fin.elim0
  change (0 : ℂ) = 1 at h0
  exact zero_ne_one h0

def source_registration : Registration arena (type_of% @Z_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Z_one, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩; exact ⟨rejected, fun ⟨⟩ hj => (hj rfl).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.Z_one)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.ZOne.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.ZOne.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ ψ => ψ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ZOne

namespace LocalScalar

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ c => c) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} (n q : ℕ) [NeZero n] (col : Fin N → Fin q)
    (ψ : (Fin N → Fin 2) → ℂ) (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ u, U u ∈ Matrix.unitaryGroup (Fin 2) ℂ) → ∀ (c : ℂ),
    Z n q col (c • (tensorOp U *ᵥ ψ)) = Z n q col (R.readout () () c • ψ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := @h 0 1 1 inferInstance Fin.elim0 psi0 Fin.elim0 (fun u => Fin.elim0 u) 1
  rw [Z_local_scalar 1 1 Fin.elim0 psi0 Fin.elim0 (fun u => Fin.elim0 u) 1] at hb
  simp only [rejected, realize, one_smul, zero_smul, Z_one, psi0_norm, Complex.ofReal_one] at hb
  norm_num at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, zero_ne_one⟩

def source_registration : Registration arena (type_of% @Z_local_scalar) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Z_local_scalar, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩; exact ⟨rejected, fun ⟨⟩ hj => (hj rfl).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.Z_local_scalar)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.LocalScalar.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.LocalScalar.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end LocalScalar

namespace ScalarNorm

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ c => c) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} (A : Matrix (Fin N) (Fin N) (ZMod 2))
    (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ u, U u ∈ Matrix.unitaryGroup (Fin 2) ℂ) → ∀ (c : ℂ),
    (∑ x : Fin N → Fin 2, ‖(c • (tensorOp U *ᵥ graphAmp A)) x‖ ^ 2) = 1 →
    star c * R.readout () () c = ((2 : ℂ) ^ N)⁻¹

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn : (∑ x : Fin 0 → Fin 2,
      ‖((1 : ℂ) • (tensorOp Fin.elim0 *ᵥ
        graphAmp (0 : Matrix (Fin 0) (Fin 0) (ZMod 2)))) x‖ ^ 2) = 1 := by
    have hz := Z_local_scalar 1 1 Fin.elim0
      (graphAmp (0 : Matrix (Fin 0) (Fin 0) (ZMod 2))) Fin.elim0 (fun u => Fin.elim0 u) 1
    rw [Z_one, Z_one, one_smul, one_smul, graphAmp0_norm] at hz
    simpa only [one_smul] using Complex.ofReal_injective hz
  have hb := @h 0 0 Fin.elim0 (fun u => Fin.elim0 u) 1 hn
  norm_num [rejected, realize] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, zero_ne_one⟩

def source_registration : Registration arena (type_of% @graph_scalar_norm) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨graph_scalar_norm, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩; exact ⟨rejected, fun ⟨⟩ hj => (hj rfl).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.graph_scalar_norm)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.ScalarNorm.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.ScalarNorm.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ScalarNorm

namespace GraphCount

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ z => z⁻¹) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {N q : ℕ} (A : Matrix (Fin N) (Fin N) (ZMod 2)),
    (∀ u v, A u v = A v u) → ∀ (col : Fin N → Fin q)
    (P : Finset (Fin (q - 1) → ZMod 3)), (0 : Fin (q - 1) → ZMod 3) ∉ P →
    (∀ t : Fin (q - 1) → ZMod 3, t ≠ 0 → (t ∈ P ↔ -t ∉ P)) →
    (((2 : ℂ) ^ N)⁻¹) ^ (3 ^ (q - 1)) * Z 3 q col (graphAmp A) =
      R.readout () () ((2 : ℂ) ^ (∑ t : {t : Fin (q - 1) → ZMod 3 // t ∈ P},
        (C A (delta col) t.val).rank))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let A0 : Matrix (Fin 0) (Fin 0) (ZMod 2) := 0
  have hP : ∀ t : Fin (1 - 1) → ZMod 3, t ≠ 0 →
      (t ∈ (∅ : Finset (Fin (1 - 1) → ZMod 3)) ↔ -t ∉ (∅ : Finset (Fin (1 - 1) → ZMod 3))) :=
    fun t ht => False.elim (ht (funext fun i => Fin.elim0 i))
  have hb := @h 0 1 A0 (fun u => Fin.elim0 u) Fin.elim0 ∅ (Finset.notMem_empty 0) hP
  have ht := graph_count A0 (fun u => Fin.elim0 u) Fin.elim0 ∅ (Finset.notMem_empty 0) hP
  rw [ht] at hb
  norm_num [rejected, realize] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @graph_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨graph_count, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩; exact ⟨rejected, fun ⟨⟩ hj => (hj rfl).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.graph_count)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.GraphCount.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.GraphCount.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z⁻¹) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end GraphCount

namespace RepsExist

abbrev signature : Signature where
  Params := ℕ
  State d := Fin d → ZMod 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Fin d → ZMod 3
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ t => -t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ t => t) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ), ∃ P : Finset (Fin d → ZMod 3), (0 : Fin d → ZMod 3) ∉ P ∧
    ∀ t : Fin d → ZMod 3, t ≠ 0 → (t ∈ P ↔ R.readout () d t ∉ P)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨P, _, hP⟩ := h 1
  have ht : (fun _ : Fin 1 => (1 : ZMod 3)) ≠ 0 := by
    intro he
    have h0 := congrFun he 0
    exact (by decide : (1 : ZMod 3) ≠ 0) h0
  have hc := hP (fun _ => 1) ht
  simp only [rejected, realize] at hc
  exact not_iff_self hc.symm

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨1, 0, (fun _ => 1), ?_⟩
  intro he
  have h0 := congrFun he 0
  change (0 : ZMod 3) = -1 at h0
  exact (by decide : (0 : ZMod 3) ≠ -1) h0

def source_registration : Registration arena (type_of% @representatives_exist) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨representatives_exist, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩; exact ⟨rejected, fun ⟨⟩ hj => (hj rfl).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.representatives_exist)
      (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.RepsExist.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.RepsExist.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => -t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "body", "body", "arg", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end RepsExist

namespace Entropy

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} (ψ : (Fin N → Fin 2) → ℂ),
    (∑ x : Fin N → Fin 2, ‖ψ x‖ ^ 2) = 1 → ∀ (q : ℕ) (col : Fin N → Fin q)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (P : Finset (Fin (q - 1) → ZMod 3)),
    Z 3 q col ψ =
      ((2 : ℂ) ^ (∑ t : {t : Fin (q - 1) → ZMod 3 // t ∈ P},
        (C A (delta col) t.val).rank))⁻¹ →
    S 3 q col ψ = Real.log 2 / (2 * (3 : ℝ) ^ (q - 2)) *
      ∑ t ∈ P, R.readout () () (C A (delta col) t).rank

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let A0 : Matrix (Fin 0) (Fin 0) (ZMod 2) := 0
  let P1 : Finset (Fin (2 - 1) → ZMod 3) := {fun _ => 1}
  have h01 : (0 : Fin (2 - 1) → ZMod 3) ∉ P1 := by decide
  have hP1 : ∀ t : Fin (2 - 1) → ZMod 3, t ≠ 0 → (t ∈ P1 ↔ -t ∉ P1) := by decide
  have hc : Z 3 2 Fin.elim0 (graphAmp A0) =
      ((2 : ℂ) ^ (∑ t : {t : Fin (2 - 1) → ZMod 3 // t ∈ P1},
        (C A0 (delta Fin.elim0) t.val).rank))⁻¹ := by
    simpa using graph_count A0 (fun u => Fin.elim0 u) Fin.elim0 P1 h01 hP1
  have hr0 : ∀ t : Fin (2 - 1) → ZMod 3, (C A0 (delta Fin.elim0) t).rank = 0 := fun t =>
    Nat.eq_zero_of_le_zero ((C A0 (delta Fin.elim0) t).rank_le_card_width.trans (by simp))
  have hb := @h 0 (graphAmp A0) graphAmp0_norm 2 Fin.elim0 A0 P1 hc
  have ht := entropy_formula (graphAmp A0) graphAmp0_norm 2 Fin.elim0 A0 P1 hc
  rw [ht] at hb
  simp only [P1, rejected, realize, hr0, Nat.cast_zero, Finset.sum_singleton, mul_zero,
    mul_one, show (2 : ℕ) - 2 = 0 from rfl, pow_zero] at hb
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @entropy_formula) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨entropy_formula, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩; exact ⟨rejected, fun ⟨⟩ hj => (hj rfl).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.entropy_formula)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.Entropy.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse.Entropy.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Entropy

end
end Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropyCollapse
