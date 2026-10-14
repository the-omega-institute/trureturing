import D5.S3.VertexAlgebra.LatticeChargedFockForms
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped VertexOperator
namespace Reg.D5.S3.VertexAlgebra.LatticeChargedFockForms.hermitian_charged

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeOscillatorFockForm
open _root_.D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeChargedFockForms
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev Parameters := Sigma fun lattice : LatticeData =>
  Sigma fun _charge : Charge lattice => Sigma fun _degree : ℤ => Carrier lattice

abbrev Parameters.lattice (parameter : Parameters) : LatticeData := parameter.1

abbrev Parameters.charge (parameter : Parameters) : Charge parameter.lattice := parameter.2.1

abbrev Parameters.degree (parameter : Parameters) : ℤ := parameter.2.2.1

abbrev Parameters.left (parameter : Parameters) : Carrier parameter.lattice := parameter.2.2.2

def signature : Signature where
  Params := Parameters
  State parameter := Carrier parameter.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ parameter right => hermitianForm parameter.lattice (((actualField parameter.lattice parameter.charge)[[parameter.degree]]) parameter.left) right)
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ parameter right,
    realization.readout () parameter right =
      paritySign (bilinear parameter.lattice parameter.charge parameter.charge / 2) * hermitianForm parameter.lattice parameter.left (((actualField parameter.lattice (-parameter.charge))[[bilinear parameter.lattice parameter.charge parameter.charge - parameter.degree - 2]]) right)

def rejected : Realization signature :=
  realize signature (fun _ parameter right => actual.readout () parameter right + 1)
    (fun empty => nomatch empty)

def testLattice : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intro left right; rfl
  even_diagonal := by intro axis; exact ⟨1, by norm_num⟩

private theorem actual_law : arena.Law actual := by
  intro parameter right
  exact hermitian_charged parameter.lattice parameter.charge
    parameter.degree parameter.left right

private theorem rejected_failure : ¬arena.Law rejected := by
  intro law
  have contradiction := law (⟨testLattice, 0, 0, 0⟩ : Parameters) 0
  have actual_eq := actual_law (⟨testLattice, 0, 0, 0⟩ : Parameters) 0
  change actual.readout () (⟨testLattice, 0, 0, 0⟩ : Parameters) 0 + 1 = _ at contradiction
  rw [← actual_eq] at contradiction
  exact one_ne_zero (add_left_cancel (show
    actual.readout () (⟨testLattice, 0, 0, 0⟩ : Parameters) 0 + 1 =
      actual.readout () (⟨testLattice, 0, 0, 0⟩ : Parameters) 0 + 0 by simpa using contradiction))

def sourceRegistration : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeChargedFockForms.hermitian_charged)) where
  actual := actual
  bridge := by
    constructor
    · intro source parameter right
      exact source parameter.lattice parameter.charge parameter.degree parameter.left right
    · intro law lattice charge degree left right
      exact law ⟨lattice, charge, degree, left⟩ right
  variation := ⟨actual_law, rejected, rejected_failure⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_failure⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨⟨testLattice, 0, -1, Finsupp.single 0 1⟩, 0, Finsupp.single 0 1, ?_⟩
    change hermitianForm testLattice _ 0 ≠ hermitianForm testLattice _ (Finsupp.single 0 1)
    have acting : VertexOperator.ncoeff (actualField testLattice 0)
        (-bilinear testLattice 0 0 - 1) (Finsupp.single 0 1) =
          epsilon testLattice 0 0 • Finsupp.single (0 + 0) 1 := by
      run_tac
        let supplier := (Lean.Name.num
          `_private.D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration 0).append
          `D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration.actual_negative_single
        Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($(Lean.mkIdent supplier))))
    simp [bilinear, epsilon, lowerCocycleExponent, paritySign] at acting
    rw [acting]
    simp [hermitianForm, bpzForm, pct, coefficientConjugation,
      Finsupp.lsum_single, Finsupp.mapRange.linearMap, conjugatePolynomial,
      _root_.D5.S3.VertexAlgebra.LatticeInvolution.theta_single,
      _root_.D5.S3.VertexAlgebra.LatticeInvolution.sigma,
      neutralMode, neutralPolynomialMode, LinearMap.comp_apply,
      fockForm_vacuum_left, testLattice]

def registration : LeanInformationAudit.Contract.Registration
    (@_root_.D5.S3.VertexAlgebra.LatticeChargedFockForms.hermitian_charged)
    (type_of% (realize signature
      (fun _ parameter right => hermitianForm parameter.lattice (((actualField parameter.lattice parameter.charge)[[parameter.degree]]) parameter.left) right)
      (fun empty => nomatch empty))) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeChargedFockForms.hermitian_charged.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeChargedFockForms.hermitian_charged.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ parameter right => hermitianForm parameter.lattice (((actualField parameter.lattice parameter.charge)[[parameter.degree]]) parameter.left) right)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeChargedFockForms
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.VertexAlgebra.LatticeChargedFockForms.hermitian_charged

namespace Reg.D5.S3.VertexAlgebra.LatticeChargedFockForms.bpz_charged

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeOscillatorFockForm
open _root_.D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeChargedFockForms
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev Parameters := Sigma fun lattice : LatticeData =>
  Sigma fun _charge : Charge lattice => Sigma fun _degree : ℤ => Carrier lattice

abbrev Parameters.lattice (parameter : Parameters) : LatticeData := parameter.1

abbrev Parameters.charge (parameter : Parameters) : Charge parameter.lattice := parameter.2.1

abbrev Parameters.degree (parameter : Parameters) : ℤ := parameter.2.2.1

abbrev Parameters.left (parameter : Parameters) : Carrier parameter.lattice := parameter.2.2.2

def signature : Signature where
  Params := Parameters
  State parameter := Carrier parameter.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ parameter right => bpzForm parameter.lattice (((actualField parameter.lattice parameter.charge)[[parameter.degree]]) parameter.left) right)
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ parameter right,
    realization.readout () parameter right =
      paritySign (bilinear parameter.lattice parameter.charge parameter.charge / 2) * bpzForm parameter.lattice parameter.left (((actualField parameter.lattice parameter.charge)[[bilinear parameter.lattice parameter.charge parameter.charge - parameter.degree - 2]]) right)

def rejected : Realization signature :=
  realize signature (fun _ parameter right => actual.readout () parameter right + 1)
    (fun empty => nomatch empty)

def testLattice : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intro left right; rfl
  even_diagonal := by intro axis; exact ⟨1, by norm_num⟩

private theorem actual_law : arena.Law actual := by
  intro parameter right
  exact bpz_charged parameter.lattice parameter.charge
    parameter.degree parameter.left right

private theorem rejected_failure : ¬arena.Law rejected := by
  intro law
  have contradiction := law (⟨testLattice, 0, 0, 0⟩ : Parameters) 0
  have actual_eq := actual_law (⟨testLattice, 0, 0, 0⟩ : Parameters) 0
  change actual.readout () (⟨testLattice, 0, 0, 0⟩ : Parameters) 0 + 1 = _ at contradiction
  rw [← actual_eq] at contradiction
  exact one_ne_zero (add_left_cancel (show
    actual.readout () (⟨testLattice, 0, 0, 0⟩ : Parameters) 0 + 1 =
      actual.readout () (⟨testLattice, 0, 0, 0⟩ : Parameters) 0 + 0 by simpa using contradiction))

def sourceRegistration : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeChargedFockForms.bpz_charged)) where
  actual := actual
  bridge := by
    constructor
    · intro source parameter right
      exact source parameter.lattice parameter.charge parameter.degree parameter.left right
    · intro law lattice charge degree left right
      exact law ⟨lattice, charge, degree, left⟩ right
  variation := ⟨actual_law, rejected, rejected_failure⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_failure⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨⟨testLattice, 0, -1, Finsupp.single 0 1⟩, 0, Finsupp.single 0 1, ?_⟩
    change bpzForm testLattice _ 0 ≠ bpzForm testLattice _ (Finsupp.single 0 1)
    have acting : VertexOperator.ncoeff (actualField testLattice 0)
        (-bilinear testLattice 0 0 - 1) (Finsupp.single 0 1) =
          epsilon testLattice 0 0 • Finsupp.single (0 + 0) 1 := by
      run_tac
        let supplier := (Lean.Name.num
          `_private.D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration 0).append
          `D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration.actual_negative_single
        Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($(Lean.mkIdent supplier))))
    simp [bilinear, epsilon, lowerCocycleExponent, paritySign] at acting
    rw [acting]
    simp [hermitianForm, bpzForm, pct, coefficientConjugation,
      Finsupp.lsum_single, Finsupp.mapRange.linearMap, conjugatePolynomial,
      _root_.D5.S3.VertexAlgebra.LatticeInvolution.theta_single,
      _root_.D5.S3.VertexAlgebra.LatticeInvolution.sigma,
      neutralMode, neutralPolynomialMode, LinearMap.comp_apply,
      fockForm_vacuum_left, testLattice]

def registration : LeanInformationAudit.Contract.Registration
    (@_root_.D5.S3.VertexAlgebra.LatticeChargedFockForms.bpz_charged)
    (type_of% (realize signature
      (fun _ parameter right => bpzForm parameter.lattice (((actualField parameter.lattice parameter.charge)[[parameter.degree]]) parameter.left) right)
      (fun empty => nomatch empty))) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeChargedFockForms.bpz_charged.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeChargedFockForms.bpz_charged.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ parameter right => bpzForm parameter.lattice (((actualField parameter.lattice parameter.charge)[[parameter.degree]]) parameter.left) right)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeChargedFockForms
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.VertexAlgebra.LatticeChargedFockForms.bpz_charged

namespace Reg.D5.S3.VertexAlgebra.LatticeChargedFockForms.hermitian_neutral

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeOscillatorFockForm
open _root_.D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeChargedFockForms
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev Parameters := Sigma fun lattice : LatticeData =>
  Sigma fun _charge : Fin lattice.rank => Sigma fun _degree : ℤ => Carrier lattice

abbrev Parameters.lattice (parameter : Parameters) : LatticeData := parameter.1

abbrev Parameters.charge (parameter : Parameters) : Fin parameter.lattice.rank := parameter.2.1

abbrev Parameters.degree (parameter : Parameters) : ℤ := parameter.2.2.1

abbrev Parameters.left (parameter : Parameters) : Carrier parameter.lattice := parameter.2.2.2

def signature : Signature where
  Params := Parameters
  State parameter := Carrier parameter.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ parameter right => hermitianForm parameter.lattice (neutralMode parameter.lattice parameter.charge parameter.degree parameter.left) right)
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ parameter right,
    realization.readout () parameter right =
      hermitianForm parameter.lattice parameter.left (neutralMode parameter.lattice parameter.charge (-parameter.degree) right)

def rejected : Realization signature :=
  realize signature (fun _ parameter right => actual.readout () parameter right + 1)
    (fun empty => nomatch empty)

def testLattice : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intro left right; rfl
  even_diagonal := by intro axis; exact ⟨1, by norm_num⟩

private theorem actual_law : arena.Law actual := by
  intro parameter right
  exact hermitian_neutral parameter.lattice parameter.charge
    parameter.degree parameter.left right

private theorem rejected_failure : ¬arena.Law rejected := by
  intro law
  have contradiction := law (⟨testLattice, 0, 0, 0⟩ : Parameters) 0
  have actual_eq := actual_law (⟨testLattice, 0, 0, 0⟩ : Parameters) 0
  change actual.readout () (⟨testLattice, 0, 0, 0⟩ : Parameters) 0 + 1 = _ at contradiction
  rw [← actual_eq] at contradiction
  exact one_ne_zero (add_left_cancel (show
    actual.readout () (⟨testLattice, 0, 0, 0⟩ : Parameters) 0 + 1 =
      actual.readout () (⟨testLattice, 0, 0, 0⟩ : Parameters) 0 + 0 by simpa using contradiction))

def sourceRegistration : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeChargedFockForms.hermitian_neutral)) where
  actual := actual
  bridge := by
    constructor
    · intro source parameter right
      exact source parameter.lattice parameter.charge parameter.degree parameter.left right
    · intro law lattice charge degree left right
      exact law ⟨lattice, charge, degree, left⟩ right
  variation := ⟨actual_law, rejected, rejected_failure⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_failure⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨⟨testLattice, 0, -1, Finsupp.single 0 1⟩, 0, Finsupp.single 0 (MvPolynomial.X (0, 0)), ?_⟩
    change hermitianForm testLattice _ 0 ≠ hermitianForm testLattice _ (Finsupp.single 0 (MvPolynomial.X (0, 0)))
    simp [hermitianForm, bpzForm, pct, coefficientConjugation,
      Finsupp.lsum_single, Finsupp.mapRange.linearMap, conjugatePolynomial,
      _root_.D5.S3.VertexAlgebra.LatticeInvolution.theta_single,
      _root_.D5.S3.VertexAlgebra.LatticeInvolution.sigma,
      neutralMode, neutralPolynomialMode, LinearMap.comp_apply,
      fockForm_vacuum_left, testLattice]

def registration : LeanInformationAudit.Contract.Registration
    (@_root_.D5.S3.VertexAlgebra.LatticeChargedFockForms.hermitian_neutral)
    (type_of% (realize signature
      (fun _ parameter right => hermitianForm parameter.lattice (neutralMode parameter.lattice parameter.charge parameter.degree parameter.left) right)
      (fun empty => nomatch empty))) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeChargedFockForms.hermitian_neutral.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeChargedFockForms.hermitian_neutral.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ parameter right => hermitianForm parameter.lattice (neutralMode parameter.lattice parameter.charge parameter.degree parameter.left) right)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeChargedFockForms
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.VertexAlgebra.LatticeChargedFockForms.hermitian_neutral

namespace Reg.D5.S3.VertexAlgebra.LatticeChargedFockForms.bpz_neutral

open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeOscillatorFockForm
open _root_.D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeChargedFockForms
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev Parameters := Sigma fun lattice : LatticeData =>
  Sigma fun _charge : Fin lattice.rank => Sigma fun _degree : ℤ => Carrier lattice

abbrev Parameters.lattice (parameter : Parameters) : LatticeData := parameter.1

abbrev Parameters.charge (parameter : Parameters) : Fin parameter.lattice.rank := parameter.2.1

abbrev Parameters.degree (parameter : Parameters) : ℤ := parameter.2.2.1

abbrev Parameters.left (parameter : Parameters) : Carrier parameter.lattice := parameter.2.2.2

def signature : Signature where
  Params := Parameters
  State parameter := Carrier parameter.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ parameter right => bpzForm parameter.lattice (neutralMode parameter.lattice parameter.charge parameter.degree parameter.left) right)
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law realization := ∀ parameter right,
    realization.readout () parameter right =
      -bpzForm parameter.lattice parameter.left (neutralMode parameter.lattice parameter.charge (-parameter.degree) right)

def rejected : Realization signature :=
  realize signature (fun _ parameter right => actual.readout () parameter right + 1)
    (fun empty => nomatch empty)

def testLattice : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intro left right; rfl
  even_diagonal := by intro axis; exact ⟨1, by norm_num⟩

private theorem actual_law : arena.Law actual := by
  intro parameter right
  exact bpz_neutral parameter.lattice parameter.charge
    parameter.degree parameter.left right

private theorem rejected_failure : ¬arena.Law rejected := by
  intro law
  have contradiction := law (⟨testLattice, 0, 0, 0⟩ : Parameters) 0
  have actual_eq := actual_law (⟨testLattice, 0, 0, 0⟩ : Parameters) 0
  change actual.readout () (⟨testLattice, 0, 0, 0⟩ : Parameters) 0 + 1 = _ at contradiction
  rw [← actual_eq] at contradiction
  exact one_ne_zero (add_left_cancel (show
    actual.readout () (⟨testLattice, 0, 0, 0⟩ : Parameters) 0 + 1 =
      actual.readout () (⟨testLattice, 0, 0, 0⟩ : Parameters) 0 + 0 by simpa using contradiction))

def sourceRegistration : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeChargedFockForms.bpz_neutral)) where
  actual := actual
  bridge := by
    constructor
    · intro source parameter right
      exact source parameter.lattice parameter.charge parameter.degree parameter.left right
    · intro law lattice charge degree left right
      exact law ⟨lattice, charge, degree, left⟩ right
  variation := ⟨actual_law, rejected, rejected_failure⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_failure⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨⟨testLattice, 0, -1, Finsupp.single 0 1⟩, 0, Finsupp.single 0 (MvPolynomial.X (0, 0)), ?_⟩
    change bpzForm testLattice _ 0 ≠ bpzForm testLattice _ (Finsupp.single 0 (MvPolynomial.X (0, 0)))
    simp [hermitianForm, bpzForm, pct, coefficientConjugation,
      Finsupp.lsum_single, Finsupp.mapRange.linearMap, conjugatePolynomial,
      _root_.D5.S3.VertexAlgebra.LatticeInvolution.theta_single,
      _root_.D5.S3.VertexAlgebra.LatticeInvolution.sigma,
      neutralMode, neutralPolynomialMode, LinearMap.comp_apply,
      fockForm_vacuum_left, testLattice]

def registration : LeanInformationAudit.Contract.Registration
    (@_root_.D5.S3.VertexAlgebra.LatticeChargedFockForms.bpz_neutral)
    (type_of% (realize signature
      (fun _ parameter right => bpzForm parameter.lattice (neutralMode parameter.lattice parameter.charge parameter.degree parameter.left) right)
      (fun empty => nomatch empty))) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeChargedFockForms.bpz_neutral.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeChargedFockForms.bpz_neutral.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ parameter right => bpzForm parameter.lattice (neutralMode parameter.lattice parameter.charge parameter.degree parameter.left) right)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeChargedFockForms
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.VertexAlgebra.LatticeChargedFockForms.bpz_neutral
