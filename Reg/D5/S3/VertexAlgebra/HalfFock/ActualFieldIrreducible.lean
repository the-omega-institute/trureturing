import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.HalfFock.ActualFieldIrreducible

/-! The coefficient family retains the entire invariant-submodule telescope.
The source bridge and whole-family intervention proofs are typed; the
escape-from carrier binding is not supplied. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Reg.D5.S3.VertexAlgebra.HalfFock.ActualFieldIrreducible
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open HalfFock.ActualFieldIrreducible LatticeAllStateField
open scoped TensorProduct
open private vacuum_coeff from D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds

structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  source : Carrier D
  e : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun p => ActualTensor p.D p.hu) (fun p => ActualTensor p.D p.hu)

def actual : Realization signature := realize signature
  (fun _ p x => (correctedField p.D p.hu p.source).coeff p.e x)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (S : Submodule ℂ (ActualTensor D hu)),
    (∀ (source : Carrier D) (e : ℤ) (x : ActualTensor D hu),
      x ∈ S → r.readout () ⟨D, hu, source, e⟩ x ∈ S) → S = ⊥ ∨ S = ⊤

theorem source_bridge :
    (type_of% (@correctedField_irreducible)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := correctedField_irreducible

private def hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  even_diagonal := by intro i; fin_cases i <;> exact ⟨0, rfl⟩

private theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
  have hd : hyperbolic.G.det = -1 := by
    change Matrix.det (!![(0 : ℤ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) = -1
    norm_num [Matrix.det_fin_two]
  rw [hd]
  exact isUnit_neg_one

private def probe (p : Oscillator hyperbolic) : ActualTensor hyperbolic hyperbolic_unit :=
  p ⊗ₜ[ℂ] (fun _ => (1 : ℂ))

private def coordinate (m : Index hyperbolic →₀ ℕ) :
    ActualTensor hyperbolic hyperbolic_unit →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map (MvPolynomial.lcoeff ℂ m) (LinearMap.proj 0))

private theorem coordinate_probe (m : Index hyperbolic →₀ ℕ)
    (p : Oscillator hyperbolic) : coordinate m (probe p) = p.coeff m := by
  simp [coordinate, probe]

private theorem probe_one_nonzero : probe 1 ≠ 0 := by
  intro h
  have he := congrArg (coordinate 0) h
  simp only [coordinate_probe, MvPolynomial.coeff_one, ite_true, map_zero] at he
  exact one_ne_zero he

private def probeIndex : Index hyperbolic := (⟨0, by decide⟩, 0)

private theorem proper_kernel :
    LinearMap.ker (coordinate 0) ≠ ⊥ ∧ LinearMap.ker (coordinate 0) ≠ ⊤ := by
  constructor
  · intro h
    have member : probe (MvPolynomial.X probeIndex) ∈ LinearMap.ker (coordinate 0) := by
      rw [LinearMap.mem_ker, coordinate_probe]
      simp
    rw [h, Submodule.mem_bot] at member
    have he := congrArg (coordinate (Finsupp.single probeIndex 1)) member
    simp [coordinate_probe] at he
  · intro h
    have member : probe 1 ∈ LinearMap.ker (coordinate 0) := by rw [h]; trivial
    rw [LinearMap.mem_ker, coordinate_probe] at member
    simpa using member

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun empty => nomatch empty)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := h hyperbolic hyperbolic_unit (LinearMap.ker (coordinate 0))
    (fun _ _ _ _ => (LinearMap.ker (coordinate 0)).zero_mem)
  exact hc.elim proper_kernel.1 proper_kernel.2

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨hyperbolic, hyperbolic_unit, vacuum hyperbolic, 0⟩, probe 1, 0, ?_⟩
  have hi : i = () := Subsingleton.elim _ _
  subst i
  change (correctedField _ _ (vacuum _)).coeff 0 (probe 1) ≠
    (correctedField _ _ (vacuum _)).coeff 0 0
  simpa only [vacuum_coeff, ite_true] using probe_one_nonzero

def family : Registration arena (type_of% (@correctedField_irreducible)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@correctedField_irreducible)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.HalfFock.ActualFieldIrreducible.correctedField_irreducible
    "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.HalfFock.ActualFieldIrreducible.family
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.HalfFock.ActualFieldIrreducible
    definition := none
    coordinates := #[0, 1, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "domain", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.HalfFock.ActualFieldIrreducible
