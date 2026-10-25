import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
import Reg.Support.DependentFamily

/-! Matrix-readout audits for the sparse shared-energy family. -/
set_option autoImplicit false
noncomputable section
open scoped MatrixOrder ComplexOrder BigOperators

namespace Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
open _root_.D5.S3.Quantum.Fibers.RealCopyConjugation

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 3) (Fin 3) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ u => sparseMatrix u) (fun e => nomatch e)
def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, -1, ?_⟩
  intro h
  have he := congrArg (fun X => X 2 0) h
  norm_num [actual, realize, sparseMatrix] at he

namespace Spectrum
abbrev arena : Arena where
  signature := signature
  Law R := ∀ u : ℂ, u * star u = 1 →
    (R.readout () () u).PosDef ∧ Matrix.trace (R.readout () () u) = 1 ∧
    spectrum ℂ (R.readout () () u) =
      {1/3, 1/3 - (Real.sqrt 2 : ℂ)/12, 1/3 + (Real.sqrt 2 : ℂ)/12}

private theorem bridge : (type_of% sparse_density_spectrum) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law zeroReadout := by
  intro h
  have ht := (h 1 (by simp)).2.1
  norm_num [zeroReadout, realize, Matrix.trace] at ht

def family : Registration arena (type_of% sparse_density_spectrum) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp sparse_density_spectrum, zeroReadout, rejected⟩
  sensitivity := ⟨fun i => ⟨zeroReadout,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    sparse_density_spectrum (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Spectrum.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Spectrum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => sparseMatrix u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Spectrum

namespace Pair
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, 2 ≤ m →
    (R.readout () () 1).PosDef ∧ (R.readout () () (phase m)).PosDef ∧
    starMonomial m (R.readout () () 1) = (1/12 : ℂ) ^ (2*m-1) ∧
    starMonomial m (R.readout () () (phase m)) = -(1/12 : ℂ) ^ (2*m-1) ∧
    (∀ k₁ k₂ : ℤ, ((m : ℤ)-1)*k₁ + (m : ℤ)*k₂ = 0 ↔
      ∃ ell : ℤ, k₁ = ell*(m : ℤ) ∧ k₂ = ell*(-((m : ℤ)-1))) ∧
    (∀ ell : ℤ, ell ≠ 0 → (2*(m : ℤ)-1) ≤
      |ell*(m : ℤ)| + |ell*(-((m : ℤ)-1))|)

private theorem bridge : (type_of% sparse_pair_data) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law zeroReadout := by
  intro h
  have ht := (h 2 (by omega)).1.diag_pos (i := (0 : Fin 3))
  exact (lt_irrefl (0 : ℂ)) ht

def family : Registration arena (type_of% sparse_pair_data) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp sparse_pair_data, zeroReadout, rejected⟩
  sensitivity := ⟨fun i => ⟨zeroReadout,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    sparse_pair_data (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Pair.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Pair.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => sparseMatrix u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Pair

namespace Low
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 2 ≤ m → ∀ alpha : Exponent,
    degree alpha < 2*m-1 → weight m alpha = 0 →
    ∀ u : ℂ, u * star u = 1 →
      monomial (R.readout () () 1) alpha = monomial (R.readout () () u) alpha

def rejectedReadout : Realization signature :=
  realize signature (fun _ _ u => if u = 1 then 1 else 0) (fun e => nomatch e)

private theorem bridge : (type_of% sparse_low_monomials) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law rejectedReadout := by
  intro h
  let alpha : Exponent := fun i j => if i = 0 ∧ j = 0 then 1 else 0
  have hd : degree alpha < 2*2-1 := by norm_num [alpha, degree, Fin.sum_univ_succ]
  have hw : weight 2 alpha = 0 := by norm_num [alpha, weight, energy, Fin.sum_univ_succ]
  have he := h 2 (by omega) alpha hd hw (-1) (by norm_num)
  norm_num [rejectedReadout, realize, alpha, monomial, Fin.prod_univ_succ] at he

def family : Registration arena (type_of% sparse_low_monomials) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp sparse_low_monomials, rejectedReadout, rejected⟩
  sensitivity := ⟨fun i => ⟨rejectedReadout,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    sparse_low_monomials (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Low.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Low.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => sparseMatrix u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Low

#print axioms Spectrum.registration
#print axioms Pair.registration
#print axioms Low.registration
end Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
