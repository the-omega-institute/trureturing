import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
import Reg.Support.DependentFamily
import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity

/-! Matrix-readout audits for the sparse shared-energy family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
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
  change Matrix.trace (0 : Matrix (Fin 3) (Fin 3) ℂ) = 1 at ht
  rw [Matrix.trace_zero] at ht
  norm_num at ht

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
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 3) (Fin 3) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => stateMatrix (sigma m)) (fun e => nomatch e)
def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  intro h
  have he := congrArg (fun X => X 2 0) h
  norm_num [actual, realize, stateMatrix, sigma, sparseState, sparseMatrix, phase,
    Circle.coe_exp, Complex.exp_pi_mul_I] at he

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, 2 ≤ m →
    (stateMatrix rho).PosDef ∧ (R.readout () () m).PosDef ∧
    starMonomial m (stateMatrix rho) = (1/12 : ℂ) ^ (2*m-1) ∧
    starMonomial m (R.readout () () m) = -(1/12 : ℂ) ^ (2*m-1) ∧
    (∀ k₁ k₂ : ℤ, ((m : ℤ)-1)*k₁ + (m : ℤ)*k₂ = 0 ↔
      ∃ ell : ℤ, k₁ = ell*(m : ℤ) ∧ k₂ = ell*(-((m : ℤ)-1))) ∧
    (∀ ell : ℤ, ell ≠ 0 → (2*(m : ℤ)-1) ≤
      |ell*(m : ℤ)| + |ell*(-((m : ℤ)-1))|)

private theorem bridge : (type_of% sparse_pair_data) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law zeroReadout := by
  intro h
  have ht := (h 2 (by omega)).2.1.diag_pos (i := (0 : Fin 3))
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
  readout := some (realize signature (fun _ _ m => stateMatrix (sigma m)) (fun e => nomatch e))
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
      stateOperand := some #["arg", "arg"]
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
  have hd : degree alpha < 2*2-1 := by decide
  have hw : weight 2 alpha = 0 := by norm_num [alpha, weight, energy, Fin.sum_univ_succ]
  have he := h 2 (by omega) alpha hd hw (-1) (by norm_num)
  norm_num [rejectedReadout, realize, alpha, monomial, Fin.prod_univ_succ,
    Matrix.one_apply, Matrix.zero_apply] at he
  change (1 : ℂ) = 0 at he
  norm_num at he

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
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Low

namespace Tensor
abbrev signature : Signature where
  Params := ℕ
  State _ := _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState (Fin 3)

  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def readoutFunction : Unit → ∀ n, signature.State n → signature.Output () n :=
  fun _ n r => stateMatrix (copies r n)
def actual : Realization signature := realize signature readoutFunction (fun e => nomatch e)
def zeroReadout : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m n : ℕ) (r : signature.State n) (I J : CopyIndex (Fin 3) n),
    degree (tensorExponent n I J) = n ∧
    weight m (tensorExponent n I J) = totalEnergy m n I - totalEnergy m n J ∧
    R.readout () n r I J = monomial (stateMatrix r) (tensorExponent n I J) ∧
    (pinchedCopies m n r I J = if weight m (tensorExponent n I J) = 0 then
      monomial (stateMatrix r) (tensorExponent n I J) else 0) ∧
    (pinchedCopies m n r).PosSemidef ∧ Matrix.trace (pinchedCopies m n r) = 1
private theorem bridge : (type_of% tensor_monomial_bridge) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law zeroReadout := by
  intro h
  have he := (h 2 0 rho PUnit.unit PUnit.unit).2.2.1
  change (0 : ℂ) = monomial (stateMatrix rho) 0 at he
  norm_num [monomial] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, rho, sigma 2, ?_⟩
  intro h
  cases i
  have he := congrArg (fun X => X (2 : Fin 3) (0 : Fin 3)) h
  change (1/12 : ℂ) * 1 = (1/12 : ℂ) * (phase 2 : ℂ) at he
  norm_num [phase, Circle.coe_exp, Complex.exp_pi_mul_I] at he

def family : Registration arena (type_of% tensor_monomial_bridge) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp tensor_monomial_bridge, zeroReadout, rejected⟩
  sensitivity := ⟨fun i => ⟨zeroReadout,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    tensor_monomial_bridge (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Tensor.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Tensor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature readoutFunction (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Tensor
namespace Pinching
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState (Fin 3)
  Anchor := Empty
  finiteAnchor := inferInstance

def lowestEnergyState :=
  _root_.D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity.pureDensityState
    (Pi.single (0 : Fin 3) (1 : ℂ)) (by
      norm_num [dotProduct, Fin.sum_univ_succ, Pi.single_apply])
def readoutFunction : Unit → Unit → ℕ → signature.Output () () := fun _ _ m => sigma m
def actual : Realization signature := realize signature readoutFunction (fun e => nomatch e)
def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => lowestEnergyState) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m n : ℕ), 2 ≤ m → n < 2*m-1 →
    pinchedCopies m n rho = pinchedCopies m n (R.readout () () m)
private theorem bridge : (type_of% sparse_low_pinching) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law zeroReadout := by
  intro h
  have he := congrArg (fun X => X (0 : Fin 3) (0 : Fin 3)) (h 2 1 (by omega) (by omega))
  change pinchedCopies 2 1 rho (0 : Fin 3) (0 : Fin 3) =
    pinchedCopies 2 1 lowestEnergyState (0 : Fin 3) (0 : Fin 3) at he
  rw [(tensor_monomial_bridge 2 1 rho (0 : Fin 3) (0 : Fin 3)).2.2.2.1,
    (tensor_monomial_bridge 2 1 lowestEnergyState (0 : Fin 3) (0 : Fin 3)).2.2.2.1] at he
  norm_num [tensorExponent, coordinateExponent, weight, energy, monomial,
    Fin.sum_univ_succ, Fin.prod_univ_succ] at he
  change sparseMatrix 1 0 0 =
    _root_.D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity
      (Pi.single (0 : Fin 3) (1 : ℂ)) 0 0 at he
  norm_num [sparseMatrix,
    _root_.D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity,
    Matrix.vecMulVec, Pi.single_apply] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  intro h
  have he := congrArg (fun r => stateMatrix r (2 : Fin 3) (0 : Fin 3)) h
  change (1/12 : ℂ) * (phase 2 : ℂ) = (1/12 : ℂ) * (phase 3 : ℂ) at he
  norm_num [phase, Circle.coe_exp, Complex.exp_pi_mul_I,
    Complex.exp_pi_div_two_mul_I] at he
  have hr := congrArg Complex.re he
  norm_num at hr

def family : Registration arena (type_of% sparse_low_pinching) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp sparse_low_pinching, zeroReadout, rejected⟩
  sensitivity := ⟨fun i => ⟨zeroReadout,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    sparse_low_pinching (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Pinching.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Pinching.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature readoutFunction (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Pinching
namespace Words
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ

  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def readoutFunction : Unit → Unit → ℕ → ℤ :=
  fun _ _ m => totalEnergy m (copyOrder m) (wordI m)
def actual : Realization signature := realize signature readoutFunction (fun e => nomatch e)
def zeroReadout : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, 2 ≤ m →
    copyOrder m = 2*m-1 ∧ wordI m ≠ wordJ m ∧
    R.readout () () m = (m : ℤ)^2 ∧
    totalEnergy m (copyOrder m) (wordJ m) = (m : ℤ)^2 ∧
    ∀ r : _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState (Fin 3),
      stateMatrix (copies r (copyOrder m)) (wordI m) (wordJ m) = starMonomial m (stateMatrix r)
private theorem bridge : (type_of% sparse_joint_words) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law zeroReadout := by
  intro h
  have ht := (h 2 (by omega)).2.2.1
  norm_num [zeroReadout, realize] at ht
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  intro h
  change totalEnergy 2 (copyOrder 2) (wordI 2) = totalEnergy 3 (copyOrder 3) (wordI 3) at h
  rw [(sparse_joint_words 2 (by omega)).2.2.1,
    (sparse_joint_words 3 (by omega)).2.2.1] at h
  norm_num at h

def family : Registration arena (type_of% sparse_joint_words) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp sparse_joint_words, zeroReadout, rejected⟩
  sensitivity := ⟨fun i => ⟨zeroReadout,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    sparse_joint_words (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Words.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Words.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature readoutFunction (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Words
namespace Effect
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ

  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def readoutFunction : Unit → Unit → ℕ → ℂ :=
  fun _ _ m => Matrix.trace (jointEffect m * stateMatrix (copies (sigma m) (copyOrder m)))
def actual : Realization signature := realize signature readoutFunction (fun e => nomatch e)
def zeroReadout : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, 2 ≤ m →
    (jointEffect m).PosSemidef ∧ (1-jointEffect m).PosSemidef ∧
    jointEffect m * totalHamiltonian m (copyOrder m) =
      totalHamiltonian m (copyOrder m) * jointEffect m ∧
    Matrix.trace (jointEffect m * stateMatrix (copies rho (copyOrder m))) =
      (1/3 : ℂ)^(2*m-1) + (1/12 : ℂ)^(2*m-1) ∧
    R.readout () () m = (1/3 : ℂ)^(2*m-1) - (1/12 : ℂ)^(2*m-1) ∧
    (0 : ℝ) < 2*(1/12 : ℝ)^(2*m-1) ∧
    (1/3 : ℝ)^(2*m-1) + (1/12 : ℝ)^(2*m-1) ∈ Set.Icc (0 : ℝ) 1 ∧
    (1/3 : ℝ)^(2*m-1) - (1/12 : ℝ)^(2*m-1) ∈ Set.Icc (0 : ℝ) 1 ∧
    pinchedCopies m (copyOrder m) rho ≠ pinchedCopies m (copyOrder m) (sigma m) ∧
    ∀ n : ℕ, n < 2*m-1 →
      ∀ F : Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ,
        F.PosSemidef → (1-F).PosSemidef →
        F * totalHamiltonian m n = totalHamiltonian m n * F →
        Matrix.trace (F * stateMatrix (copies rho n)) =
          Matrix.trace (F * stateMatrix (copies (sigma m) n))
private theorem bridge : (type_of% sparse_joint_effect) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law zeroReadout := by
  intro h
  have ht := (h 2 (by omega)).2.2.2.2.1
  norm_num [zeroReadout, realize] at ht
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  intro h
  change Matrix.trace (jointEffect 2 * stateMatrix (copies (sigma 2) (copyOrder 2))) =
    Matrix.trace (jointEffect 3 * stateMatrix (copies (sigma 3) (copyOrder 3))) at h
  rw [(sparse_joint_effect 2 (by omega)).2.2.2.2.1,
    (sparse_joint_effect 3 (by omega)).2.2.2.2.1] at h
  norm_num at h

def family : Registration arena (type_of% sparse_joint_effect) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp sparse_joint_effect, zeroReadout, rejected⟩
  sensitivity := ⟨fun i => ⟨zeroReadout,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    sparse_joint_effect (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Effect.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Effect.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature readoutFunction (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Effect

namespace Compatible
abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState (Fin 3)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (CopyIndex (Fin 3) p.2) (CopyIndex (Fin 3) p.2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def readoutFunction : Unit → ∀ p, signature.State p → signature.Output () p :=
  fun _ p r => pinchedCopies p.1 p.2 r
def actual : Realization signature := realize signature readoutFunction (fun e => nomatch e)
def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m n : ℕ) (r s : signature.State ⟨m,n⟩),
    R.readout () ⟨m,n⟩ r = R.readout () ⟨m,n⟩ s ↔
      ∀ F : Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ,
        F.PosSemidef → (1-F).PosSemidef →
        F * totalHamiltonian m n = totalHamiltonian m n * F →
        Matrix.trace (F * stateMatrix (copies r n)) =
          Matrix.trace (F * stateMatrix (copies s n))
private theorem bridge : (type_of% compatible_effects_iff) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law zeroReadout := by
  intro h
  have hp := sparse_joint_effect 2 (by omega)
  have he := (h 2 (copyOrder 2) rho (sigma 2)).mp rfl
    (jointEffect 2) hp.1 hp.2.1 hp.2.2.1
  rw [hp.2.2.2.1, hp.2.2.2.2.1] at he
  norm_num at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨2, copyOrder 2⟩, rho, sigma 2, ?_⟩
  change pinchedCopies 2 (copyOrder 2) rho ≠ pinchedCopies 2 (copyOrder 2) (sigma 2)
  exact (sparse_joint_effect 2 (by omega)).2.2.2.2.2.2.2.2.1

def family : Registration arena (type_of% compatible_effects_iff) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp compatible_effects_iff, zeroReadout, rejected⟩
  sensitivity := ⟨fun i => ⟨zeroReadout,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    compatible_effects_iff (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Compatible.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Compatible.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature readoutFunction (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Compatible
#print axioms Compatible.registration
#print axioms Tensor.registration
#print axioms Pinching.registration
#print axioms Words.registration
#print axioms Effect.registration
#print axioms Spectrum.registration
#print axioms Pair.registration
#print axioms Low.registration

namespace ExponentWords
abbrev signature : Signature where
  Params := _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState (Fin 3)
  State _ := Exponent
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def readoutFunction : Unit → ∀ r, signature.State r → signature.Output () r :=
  fun _ r alpha => monomial (stateMatrix r) alpha
def actual : Realization signature := realize signature readoutFunction (fun e => nomatch e)
def zeroReadout : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (alpha : Exponent),
    ∃ I J : CopyIndex (Fin 3) (degree alpha),
      tensorExponent (degree alpha) I J = alpha ∧
      totalEnergy m (degree alpha) I - totalEnergy m (degree alpha) J = weight m alpha ∧
      ∀ r : signature.Params,
        stateMatrix (copies r (degree alpha)) I J = R.readout () r alpha ∧
        pinchedCopies m (degree alpha) r I J =
          if weight m alpha = 0 then R.readout () r alpha else 0
private theorem bridge : (type_of% exponent_tensor_bridge) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law zeroReadout := by
  intro h
  obtain ⟨I, J, hIJ⟩ := h 2 0
  have he := (hIJ.2.2 rho).1
  change stateMatrix (copies rho (degree 0)) I J = 0 at he
  have ht := (tensor_monomial_bridge 2 (degree 0) rho I J).2.2.1
  rw [hIJ.1] at ht
  have hone : monomial (stateMatrix rho) 0 = 1 := by
    norm_num [monomial, Fin.prod_univ_succ]
  rw [hone] at ht
  exact one_ne_zero (ht.symm.trans he)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨rho, 0, coordinateExponent 0 0, ?_⟩
  intro h
  cases i
  change monomial (sparseMatrix 1) 0 = monomial (sparseMatrix 1) (coordinateExponent 0 0) at h
  norm_num [monomial, coordinateExponent, sparseMatrix, Fin.prod_univ_succ] at h

def family : Registration arena (type_of% exponent_tensor_bridge) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp exponent_tensor_bridge, zeroReadout, rejected⟩
  sensitivity := ⟨fun i => ⟨zeroReadout,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exponent_tensor_bridge (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.ExponentWords.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.ExponentWords.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature readoutFunction (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ExponentWords


namespace Hamiltonian
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (CopyIndex (Fin 3) n) (CopyIndex (Fin 3) n) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def readoutFunction : Unit → ∀ n, ℕ → signature.Output () n := fun _ n m => totalHamiltonian m n
def actual : Realization signature := realize signature readoutFunction (fun e => nomatch e)
def zeroReadout : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m n : ℕ,
    R.readout () n m = Matrix.diagonal (fun I => (totalEnergy m n I : ℂ))
private theorem bridge : (type_of% total_hamiltonian_diagonal) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law zeroReadout := by
  intro h
  have he := congrArg (fun X => X (1 : Fin 3) (1 : Fin 3)) (h 2 1)
  norm_num [zeroReadout, realize, totalEnergy, energy, Matrix.diagonal, CopyIndex] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 2, 3, ?_⟩
  intro h
  have he := congrArg (fun X => X (2 : Fin 3) (2 : Fin 3)) h
  change (2 : ℂ) = 3 at he
  norm_num at he

def family : Registration arena (type_of% total_hamiltonian_diagonal) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp total_hamiltonian_diagonal, zeroReadout, rejected⟩
  sensitivity := ⟨fun i => ⟨zeroReadout,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    total_hamiltonian_diagonal (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Hamiltonian.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold.Hamiltonian.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature readoutFunction (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Hamiltonian

#print axioms ExponentWords.registration
#print axioms Hamiltonian.registration
end Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
