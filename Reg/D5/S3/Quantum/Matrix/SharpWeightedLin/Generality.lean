import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.SharpWeightedLin.Generality
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Matrix.SharpWeightedLin
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Reg.D5.S3.Quantum.Matrix.SharpWeightedLin.Generality

namespace EigenvaluesRealSmul
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (r : ℝ) (hr : 0 ≤ r)
    (hB : (r • A).IsHermitian) (i : n),
    R.readout () () (hB.eigenvalues i) (r * hA.eigenvalues i)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (n := Fin 1) (A := (1 : Matrix (Fin 1) (Fin 1) ℂ))
    Matrix.PosDef.one.isHermitian 1 (by norm_num) (by simpa only [one_smul] using (Matrix.PosDef.one.isHermitian : (1 : Matrix (Fin 1) (Fin 1) ℂ).IsHermitian)) 0
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.SharpWeightedLin.eigenvalues_real_smul)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.SharpWeightedLin.eigenvalues_real_smul, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i; refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.SharpWeightedLin.eigenvalues_real_smul)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.SharpWeightedLin.eigenvalues_real_smul.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.SharpWeightedLin.Generality.EigenvaluesRealSmul.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.SharpWeightedLin.Generality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body",
        "body",
        "body",
        "body",
        "body",
        "body",
        "body",
        "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end EigenvaluesRealSmul

namespace NonnegIndexRealSmul
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (r : ℝ) (hr : 0 < r)
    (hB : (r • A).IsHermitian), R.readout () () (nonnegIndex hB) (nonnegIndex hA)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (n := Fin 1) (A := (1 : Matrix (Fin 1) (Fin 1) ℂ))
    Matrix.PosDef.one.isHermitian 1 (by norm_num) (by simpa only [one_smul] using (Matrix.PosDef.one.isHermitian : (1 : Matrix (Fin 1) (Fin 1) ℂ).IsHermitian))
private theorem dependence : ObservationalDependence signature actual := by
  intro i; refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.SharpWeightedLin.nonnegIndex_real_smul)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.SharpWeightedLin.nonnegIndex_real_smul, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i; refine ⟨rejected, ?_, rfl, rejected_law⟩; intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.SharpWeightedLin.nonnegIndex_real_smul)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.SharpWeightedLin.nonnegIndex_real_smul.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.SharpWeightedLin.Generality.NonnegIndexRealSmul.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.SharpWeightedLin.Generality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body",
        "body",
        "body",
        "body",
        "body",
        "body",
        "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end NonnegIndexRealSmul

namespace NonnegIndexMono
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A ≤ B),
    R.readout () () (nonnegIndex hA) (nonnegIndex hB)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (n := Fin 1) (A := (1 : Matrix (Fin 1) (Fin 1) ℂ)) (B := 1)
    Matrix.PosDef.one.isHermitian Matrix.PosDef.one.isHermitian (by exact le_rfl)
private theorem dependence : ObservationalDependence signature actual := by
  intro i; refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.SharpWeightedLin.nonnegIndex_mono)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.SharpWeightedLin.nonnegIndex_mono, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i; refine ⟨rejected, ?_, rfl, rejected_law⟩; intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.SharpWeightedLin.nonnegIndex_mono)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.SharpWeightedLin.nonnegIndex_mono.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.SharpWeightedLin.Generality.NonnegIndexMono.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.SharpWeightedLin.Generality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body",
        "body",
        "body",
        "body",
        "body",
        "body",
        "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end NonnegIndexMono

end Reg.D5.S3.Quantum.Matrix.SharpWeightedLin.Generality
