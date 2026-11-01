import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity
import Reg.Support.DependentFamily

/-! Source-bound audit of negative-line parity over all linear doilies. -/

namespace Reg.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity

open _root_.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Count negative lines while retaining the ambient number of qubits. -/
abbrev signature : Signature where
  Params := ℕ
  State N := Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ U => (negativeLines U).card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The original dimension, nondegeneracy, and odd-cardinality assertion. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ), 2 ≤ N →
    ∀ U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2),
      IsLinearDoily U → Odd (R.readout () N U)

private theorem two_qubit_doily :
    IsLinearDoily (⊤ : Submodule (ZMod 2) (Fin 2 → ZMod 2 × ZMod 2)) := by
  constructor
  · simp [Module.finrank_pi_fintype]
  · intro u _ hu
    funext j
    apply Prod.ext
    · have h := hu (Pi.single j (0, 1)) (Submodule.mem_top)
      fin_cases j <;> simpa [B, Pi.single_apply] using h
    · have h := hu (Pi.single j (1, 0)) (Submodule.mem_top)
      fin_cases j <;> simpa [B, Pi.single_apply] using h

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 2 (by decide) ⊤ two_qubit_doily
  change Odd (0 : ℕ) at hbad
  simp at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, ⊥, ⊤, ?_⟩
  change (negativeLines (⊥ : Submodule (ZMod 2) (Fin 2 → ZMod 2 × ZMod 2))).card ≠
    (negativeLines (⊤ : Submodule (ZMod 2) (Fin 2 → ZMod 2 × ZMod 2))).card
  have hz : (negativeLines (⊥ : Submodule (ZMod 2) (Fin 2 → ZMod 2 × ZMod 2))).card = 0 := by
    simp [negativeLines, lines, points]
  rw [hz]
  intro h
  have hodd := result 2 (by decide) ⊤ two_qubit_doily
  rw [← h] at hodd
  simp at hodd

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ U => (negativeLines U).card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity
    definition := some {
      owner := `D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity
      name := `D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

namespace Pairing

/-- Fix the first vector and observe its pairing with a variable second vector. -/
abbrev signature : Signature where
  Params := Σ N : ℕ, Fin N → ZMod 2 × ZMod 2
  State p := Fin p.1 → ZMod 2 × ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p v => B p.2 v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, fun _ => (1, 0)⟩, 0, (fun _ => (0, 1)), ?_⟩
  change B (fun _ : Fin 1 => (1, 0)) 0 ≠
    B (fun _ : Fin 1 => (1, 0)) (fun _ => (0, 1))
  norm_num [B, Fin.sum_univ_one]

end Pairing

namespace Comm

abbrev arena : Arena where
  signature := Pairing.signature
  Law R := ∀ {N : ℕ} (u v : Fin N → ZMod 2 × ZMod 2),
    R.readout () ⟨N, u⟩ v = B v u

theorem rejected_law : ¬ arena.Law Pairing.rejected := by
  intro h
  have hbad := h (0 : Fin 1 → ZMod 2 × ZMod 2) 0
  norm_num [Pairing.rejected, realize, B] at hbad

def source_registration : Registration arena
    (∀ {N : ℕ} (u v : Fin N → ZMod 2 × ZMod 2), B u v = B v u) where
  actual := Pairing.actual
  bridge := Iff.rfl
  variation := ⟨B_comm, Pairing.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨Pairing.rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
        rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := Pairing.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@B_comm) (Realization Pairing.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.Comm.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.Comm.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize Pairing.signature (fun _ p v => B p.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Comm

namespace AddRight

abbrev arena : Arena where
  signature := Pairing.signature
  Law R := ∀ {N : ℕ} (u v w : Fin N → ZMod 2 × ZMod 2),
    R.readout () ⟨N, u⟩ (v + w) = B u v + B u w

theorem rejected_law : ¬ arena.Law Pairing.rejected := by
  intro h
  have hbad := h (0 : Fin 1 → ZMod 2 × ZMod 2) 0 0
  norm_num [Pairing.rejected, realize, B] at hbad

def source_registration : Registration arena
    (∀ {N : ℕ} (u v w : Fin N → ZMod 2 × ZMod 2), B u (v + w) = B u v + B u w) where
  actual := Pairing.actual
  bridge := Iff.rfl
  variation := ⟨B_add_right, Pairing.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨Pairing.rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
        rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := Pairing.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@B_add_right) (Realization Pairing.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.AddRight.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.AddRight.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize Pairing.signature (fun _ p v => B p.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end AddRight

namespace Self

abbrev arena : Arena where
  signature := Pairing.signature
  Law R := ∀ {N : ℕ} (u : Fin N → ZMod 2 × ZMod 2), R.readout () ⟨N, u⟩ u = 0

theorem rejected_law : ¬ arena.Law Pairing.rejected := by
  intro h
  have hbad := h (0 : Fin 1 → ZMod 2 × ZMod 2)
  norm_num [Pairing.rejected, realize] at hbad

def source_registration : Registration arena
    (∀ {N : ℕ} (u : Fin N → ZMod 2 × ZMod 2), B u u = 0) where
  actual := Pairing.actual
  bridge := Iff.rfl
  variation := ⟨B_self, Pairing.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨Pairing.rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
        rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := Pairing.dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@B_self) (Realization Pairing.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.Self.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.Self.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize Pairing.signature (fun _ p v => B p.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Self

namespace Triple

/-- Observe the line-product scalar with a fixed first vector and variable second vector. -/
abbrev signature : Signature where
  Params := Σ N : ℕ, Fin N → ZMod 2 × ZMod 2
  State p := Fin p.1 → ZMod 2 × ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p v => phase p.2 v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p v => phase p.2 v + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} (u v : Fin N → ZMod 2 × ZMod 2),
    u ≠ 0 → v ≠ 0 → u ≠ v → B u v = 0 →
    lineProduct {u, v, u + v} = R.readout () ⟨N, u⟩ v • 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let u : Fin 2 → ZMod 2 × ZMod 2 := fun _ => (1, 0)
  let v : Fin 2 → ZMod 2 × ZMod 2 := fun _ => (0, 1)
  have hu : u ≠ 0 := by decide
  have hv : v ≠ 0 := by decide
  have huv : u ≠ v := by decide
  have hB : B u v = 0 := by decide
  have hbad := h u v hu hv huv hB
  rw [lineProduct_triple u v hu hv huv hB] at hbad
  have hdiag := congrFun (congrFun hbad (fun _ => 0)) (fun _ => 0)
  simp only [rejected, realize, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one] at hdiag
  exact one_ne_zero (add_left_cancel (hdiag.symm.trans (add_zero _).symm))

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, fun _ => (1, 0)⟩, 0, (fun _ => (0, 1)), ?_⟩
  change phase (fun _ : Fin 1 => (1, 0)) 0 ≠
    phase (fun _ : Fin 1 => (1, 0)) (fun _ => (0, 1))
  simp only [phase, Fin.prod_univ_one]
  change (Complex.I ^ 0 : ℂ) ≠ Complex.I ^ 3
  norm_num [pow_succ, Complex.I_sq, Complex.ext_iff]

def source_registration : Registration arena
    (∀ {N : ℕ} (u v : Fin N → ZMod 2 × ZMod 2),
      u ≠ 0 → v ≠ 0 → u ≠ v → B u v = 0 →
      lineProduct {u, v, u + v} = phase u v • 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lineProduct_triple, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@lineProduct_triple) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.Triple.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.Triple.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => phase p.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Triple

set_option pp.proofs false in
#print _root_.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.B_comm
set_option pp.proofs false in
#print _root_.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.B_add_right
set_option pp.proofs false in
#print _root_.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.B_self
set_option pp.proofs false in
#print _root_.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity.lineProduct_triple

end
end Reg.D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity
