import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeSectorGeneralScalarNumerator

/-! Full-source finite scalar numerator observation for arbitrary lattice data. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open _root_.D5.S3.VertexAlgebra
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open _root_.D5.S3.VertexAlgebra.LatticeSectorScalarNumerator (readout testEnergy wordDegreeBound)
open _root_.D5.S3.VertexAlgebra.LatticeSectorGeneralScalarNumerator
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.FieldNormalProductLocality
open _root_.D5.S3.VertexAlgebra.UniformGradedLocalCorrelator
open _root_.D5.S3.VertexAlgebra.UngradedLocalWordSeries
open scoped VertexOperator BigOperators

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorGeneralScalarNumerator

private def D0 : LatticeData :=
  ⟨0, 0, by intro i; exact Fin.elim0 i, by intro i; exact Fin.elim0 i⟩

namespace WordNumerator
abbrev signature : Signature where
  Params := ℕ
  State n := MvPowerSeries (Fin n) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := MvPowerSeries (Fin n) ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize _ (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  intro h
  have bad : (1 : MvPowerSeries (Fin 0) ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero bad

abbrev arena : Arena where
  signature := signature
  Law obs := ∀
    (D : LatticeData)
    (n : ℕ) (c : Fin n → Charge D) (s : Fin n → Oscillator D),
    let A := fun i => LatticeAllStateField.Y D (inclusion D (c i) (s i))
    let order := List.ofFn (fun i : Fin n => i)
    ∃ k : ℕ,
      (∀ i j : Fin n, i < j → (deltaEnd ^ k) (commutator (A i) (A j)) = 0) ∧
      ∀ (δ : Charge D) (w : Sector D δ), ∃ a : Fin n → ℕ,
        ∃ P : MvPowerSeries (Fin n) (Carrier D),
        (∀ (i : Fin n) (m : ℤ), (a i : ℤ) ≤ m → (A i [[m]]) (inclusion D δ w) = 0) ∧
        (∀ other : List (Fin n), order.Perm other → ∀ e : Fin n → ℤ,
          polynomialAction (clearingPolynomial n k)
            (coefficientDistribution A (inclusion D δ w) 1 other)
            (fun i => e i - (a i : ℤ)) = signedExtend P e) ∧
        ∀ p : Oscillator D,
          let φ := (readout D p).comp (projection D ((∑ i, c i) + δ))
          let S : MvPowerSeries (Fin n) ℂ := fun d => φ (P d)
          (∀ d, S d ≠ 0 → (d.degree : ℤ) ≤ wordDegreeBound D c δ k a p) ∧
          ∃! R : MvPolynomial (Fin n) ℂ,
            obs.readout () n (R : MvPowerSeries (Fin n) ℂ) S ∧
            R.totalDegree ≤ (wordDegreeBound D c δ k a p).toNat ∧
            (wordDegreeBound D c δ k a p < 0 → S = 0 ∧ R = 0) ∧
            ∀ other : List (Fin n), order.Perm other → ∀ e : Fin n → ℤ,
              polynomialAction (clearingPolynomial n k)
                (fun b => φ (coefficientDistribution A (inclusion D δ w) 1 other b))
                (fun i => e i - (a i : ℤ)) = signedExtend (R : MvPowerSeries (Fin n) ℂ) e

private theorem bad : ¬ arena.Law rejected := by
  intro h
  obtain ⟨k, _hk, rest⟩ := h D0 0
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  obtain ⟨a, P, _truncation, _common, tests⟩ := rest 0 0
  obtain ⟨_support, R, hR, _unique⟩ := tests 0
  exact hR.1

def family : Registration arena (type_of% (@ordinary_actual_word_finite_scalar_numerator)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ordinary_actual_word_finite_scalar_numerator, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := dependence
end WordNumerator

def wordNumeratorAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ordinary_actual_word_finite_scalar_numerator) (Realization WordNumerator.signature) Unit Unit where
  unitName :=
    `Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorGeneralScalarNumerator.WordNumeratorUnit
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorGeneralScalarNumerator.WordNumerator.family
  realizationSource := none
  generated := false
  arena := .source ⟨WordNumerator.arena⟩
  objectArena := .source ⟨WordNumerator.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source WordNumerator.arena ⟨WordNumerator.family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize WordNumerator.signature WordNumerator.actual.readout WordNumerator.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Sectors.LatticeSectorGeneralScalarNumerator
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body",
        "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body",
        "arg", "body", "arg", "body", "arg", "arg", "body", "body", "body",
        "arg", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


#print axioms WordNumerator.family

end Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorGeneralScalarNumerator
