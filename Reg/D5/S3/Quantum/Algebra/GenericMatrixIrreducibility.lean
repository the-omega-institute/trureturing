import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Algebra.GenericMatrixIrreducibility

open Classical
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.GenericMatrixIrreducibility

noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.GenericMatrixIrreducibility

namespace Determinant
abbrev signature : Signature where
  Params := ℕ
  State n := MvPolynomial (Fin n × Fin n) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ p => decide (Irreducible p)) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ), 0 < n → r.readout () n (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ)) = true

private theorem bridge : (type_of% (@det_generic_irreducible)) ↔ arena.Law actual := by
  simp only [arena, actual, realize, decide_eq_true_eq]
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact Bool.false_ne_true (h 1 (by decide))

def family : Registration arena (type_of% (@det_generic_irreducible)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@det_generic_irreducible), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, Matrix.det (Matrix.mvPolynomialX (Fin 1) (Fin 1) ℂ), 1, ?_⟩
    change decide (Irreducible _) ≠ decide (Irreducible (1 : signature.State 1))
    rw [decide_eq_true (det_generic_irreducible 1 (by decide)),
      decide_eq_false not_irreducible_one]
    decide

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@det_generic_irreducible) (Realization signature) (type_of% (@Irreducible.{0})) Unit where
  unitName := `D5.S3.Quantum.Algebra.GenericMatrixIrreducibility.det_generic_irreducible.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.GenericMatrixIrreducibility.Determinant.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@Irreducible.{0})
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.GenericMatrixIrreducibility
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Determinant

namespace Characteristic
abbrev signature : Signature where
  Params := ℕ
  State n := Polynomial (FractionRing (MvPolynomial (Fin n × Fin n) ℂ))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ p => decide (Irreducible p)) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ), 0 < n → r.readout () n ((Matrix.charpoly (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ)).map (algebraMap (MvPolynomial (Fin n × Fin n) ℂ) (FractionRing (MvPolynomial (Fin n × Fin n) ℂ)))) = true

private theorem bridge : (type_of% (@charpoly_generic_irreducible_fractionRing)) ↔ arena.Law actual := by
  simp only [arena, actual, realize, decide_eq_true_eq]
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact Bool.false_ne_true (h 1 (by decide))

def family : Registration arena (type_of% (@charpoly_generic_irreducible_fractionRing)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@charpoly_generic_irreducible_fractionRing), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, (Matrix.charpoly (Matrix.mvPolynomialX (Fin 1) (Fin 1) ℂ)).map
      (algebraMap (MvPolynomial (Fin 1 × Fin 1) ℂ)
        (FractionRing (MvPolynomial (Fin 1 × Fin 1) ℂ))), 1, ?_⟩
    change decide (Irreducible _) ≠ decide (Irreducible (1 : signature.State 1))
    rw [decide_eq_true (charpoly_generic_irreducible_fractionRing 1 (by decide)),
      decide_eq_false not_irreducible_one]
    decide

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@charpoly_generic_irreducible_fractionRing) (Realization signature) (type_of% (@Irreducible.{0})) Unit where
  unitName := `D5.S3.Quantum.Algebra.GenericMatrixIrreducibility.charpoly_generic_irreducible_fractionRing.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.GenericMatrixIrreducibility.Characteristic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@Irreducible.{0})
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.GenericMatrixIrreducibility
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Characteristic

end Reg.D5.S3.Quantum.Algebra.GenericMatrixIrreducibility
