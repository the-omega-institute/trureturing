import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
import Reg.Support.SingleDependentReadout

/-! The full Dicke cone telescope, observed through its actual star-extension predicate. -/

namespace Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

open _root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

structure Parameters where
  n : ℕ
  r : ℕ
  hn : 1 ≤ n
  hr : 2 ≤ r
  Y : Fin n → Fin n → ℝ
  hY : ∀ i j, i ≤ j → 0 ≤ Y i j

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters
    (fun p => Matrix (Fin p.r → Fin p.n) (Fin p.r → Fin p.n) ℂ)
    (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ p E =>
    StarExtension (⟨0,by have := p.hr; omega⟩ : Fin p.r) (dickeOperator p.Y) E)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n r : ℕ) (hn : 1 ≤ n) (hr : 2 ≤ r)
    (Y : Fin n → Fin n → ℝ) (hY : ∀ i j, i ≤ j → 0 ≤ Y i j),
    (∃ E, R.readout () ⟨n,r,hn,hr,Y,hY⟩ E) ↔
      ∃ E : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ,
        CompleteExtension (dickeOperator Y) E

private lemma zero_complete (n r : ℕ) :
    CompleteExtension (dickeOperator (fun _ _ : Fin n => (0 : ℝ)))
      (0 : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) := by
  refine ⟨Matrix.PosSemidef.zero, by simp, ?_, ?_⟩
  · intro a b hab
    ext u v
    simp [edgeMarginal, _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
      dickeOperator]
  · intro S hS hp
    exact Matrix.PosSemidef.zero

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := (h 1 2 (by omega) (by omega) (fun _ _ => 0) (by simp)).mpr
    ⟨0,zero_complete 1 2⟩
  obtain ⟨E,hE⟩ := hz
  exact hE

private def base : Parameters := ⟨1,2,by omega,by omega,fun _ _ => 0,by simp⟩

private lemma zero_star :
    StarExtension (⟨0,by decide⟩ : Fin 2)
      (dickeOperator (fun _ _ : Fin 1 => (0 : ℝ)))
      (0 : Matrix (Fin 2 → Fin 1) (Fin 2 → Fin 1) ℂ) := by
  refine ⟨Matrix.PosSemidef.zero, by simp, ?_, ?_⟩
  · intro i hi
    ext u v
    simp [edgeMarginal, _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
      dickeOperator]
  · intro S hS hp
    exact Matrix.PosSemidef.zero

private lemma not_one_star :
    ¬ StarExtension (⟨0,by decide⟩ : Fin 2)
      (dickeOperator (fun _ _ : Fin 1 => (0 : ℝ)))
      (1 : Matrix (Fin 2 → Fin 1) (Fin 2 → Fin 1) ℂ) := by
  intro h
  have hm := h.2.2.1 (⟨1,by decide⟩ : Fin 2) (by decide)
  have he := congrArg (fun A : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ =>
    A (0,0) (0,0)) hm
  have hone (x y : Fin 2 → Fin 1) :
      (1 : Matrix (Fin 2 → Fin 1) (Fin 2 → Fin 1) ℂ) x y = 1 := by
    simp [Matrix.one_apply, Subsingleton.elim x y]
  norm_num [edgeMarginal,
    _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight,
    Matrix.submatrix_apply, hone, dickeOperator] at he

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨base,0,1,?_⟩
  intro h
  have h0 : actual.readout () base 0 := zero_star
  have h1 : actual.readout () base 1 := Eq.mp h h0
  exact not_one_star h1

def source_registration : Registration arena
    (type_of% @_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.result,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p E =>
    StarExtension (⟨0,by have := p.hr; omega⟩ : Fin p.r) (dickeOperator p.Y) E)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
    definition := none
    coordinates := #[0,1,2,3,4,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg","arg","body"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
