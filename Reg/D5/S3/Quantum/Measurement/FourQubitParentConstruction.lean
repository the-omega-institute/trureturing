import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.FourQubitParentConstruction
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open LeanInformationAudit
set_option maxHeartbeats 1000000
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open scoped Classical
noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction
universe u
abbrev Vec := EuclideanSpace ℝ (Fin 3)
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev Tuple := Fin 4 → Bool → Mat

abbrev vectorSignature : Signature where
  Params := Unit
  State _ := Vec
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Mat
  Anchor := Empty
  finiteAnchor := inferInstance

def vectorActual : Realization vectorSignature :=
  realize vectorSignature (fun _ _ a => B a) (fun e => nomatch e)
def vectorRejected : Realization vectorSignature :=
  realize vectorSignature (fun _ _ _ => 1) (fun e => nomatch e)

theorem vectorDependence : ObservationalDependence vectorSignature vectorActual := by
  intro i
  refine ⟨(), 0, !₂[0,0,1], ?_⟩
  intro h
  have hh := congrArg (fun A : Mat => A 0 0) h
  norm_num [vectorActual, realize, B_formula, Matrix.cons_val_succ, Matrix.cons_val_zero] at hh
  change (0 : ℂ) = 1 at hh
  norm_num at hh

@[reducible] def formulaArena : Arena where
  signature := vectorSignature
  Law R := ∀ a : Vec, R.readout () () a = !![(a 2 : ℂ), (a 0 : ℂ) - Complex.I * (a 1 : ℂ); (a 0 : ℂ) + Complex.I * (a 1 : ℂ), -(a 2 : ℂ)]
theorem formulaPositive : formulaArena.Law vectorActual := by
  intro a; exact B_formula a
theorem formulaNegative : ¬ formulaArena.Law vectorRejected := by
  intro h
  have hh := h 0
  have he := congrArg (fun A : Mat => A 0 0) hh
  norm_num [vectorRejected, realize, B_formula, Matrix.one_apply] at he
  change (1 : ℂ) = 0 at he
  norm_num at he

def formulaEvidence : Registration formulaArena
    (type_of% (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula)) where
  actual := vectorActual
  bridge := Iff.rfl
  variation := ⟨formulaPositive, vectorRejected, formulaNegative⟩
  sensitivity := ⟨fun i => ⟨vectorRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, formulaNegative⟩,
    fun i => nomatch i⟩
  dependence := vectorDependence

@[reducible] def smulArena : Arena where
  signature := vectorSignature
  Law R := ∀ (c : ℝ) (a : Vec), R.readout () () (c • a) = c • B a
theorem smulPositive : smulArena.Law vectorActual := by
  intro c a; exact B_real_smul c a
theorem smulNegative : ¬ smulArena.Law vectorRejected := by
  intro h
  have hh := h 0 0
  have he := congrArg (fun A : Mat => A 0 0) hh
  norm_num [vectorRejected, realize, B_formula, Matrix.one_apply] at he
  change (1 : ℂ) = 0 at he
  norm_num at he

def smulEvidence : Registration smulArena
    (type_of% (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_real_smul)) where
  actual := vectorActual
  bridge := Iff.rfl
  variation := ⟨smulPositive, vectorRejected, smulNegative⟩
  sensitivity := ⟨fun i => ⟨vectorRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, smulNegative⟩,
    fun i => nomatch i⟩
  dependence := vectorDependence

@[reducible] def negArena : Arena where
  signature := vectorSignature
  Law R := ∀ a : Vec, R.readout () () (-a) = -B a
theorem negPositive : negArena.Law vectorActual := by
  intro a; exact B_neg a
theorem negNegative : ¬ negArena.Law vectorRejected := by
  intro h
  have hh := h 0
  have he := congrArg (fun A : Mat => A 0 0) hh
  norm_num [vectorRejected, realize, B_formula, Matrix.one_apply] at he
  change (1 : ℂ) = 0 at he
  norm_num at he

def negEvidence : Registration negArena
    (type_of% (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_neg)) where
  actual := vectorActual
  bridge := Iff.rfl
  variation := ⟨negPositive, vectorRejected, negNegative⟩
  sensitivity := ⟨fun i => ⟨vectorRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negNegative⟩,
    fun i => nomatch i⟩
  dependence := vectorDependence

@[reducible] def sumArena : Arena where
  signature := vectorSignature
  Law R := ∀ {ι : Type u} (s : Finset ι) (a : ι → Vec), R.readout () () (∑ i ∈ s, a i) = ∑ i ∈ s, B (a i)
theorem sumPositive : sumArena.{u}.Law vectorActual := by
  intro ι s a; exact B_sum s a
theorem sumNegative : ¬ sumArena.{u}.Law vectorRejected := by
  intro h
  have hh := h (ι := ULift.{u} Unit) ∅ (fun _ => 0)
  have he := congrArg (fun A : Mat => A 0 0) hh
  norm_num [vectorRejected, realize, B_formula, Matrix.one_apply] at he
  change (1 : ℂ) = 0 at he
  norm_num at he

def sumEvidence : Registration sumArena.{u}
    (type_of% (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_sum.{u})) where
  actual := vectorActual
  bridge := Iff.rfl
  variation := ⟨sumPositive, vectorRejected, sumNegative⟩
  sensitivity := ⟨fun i => ⟨vectorRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, sumNegative⟩,
    fun i => nomatch i⟩
  dependence := vectorDependence

abbrev realVectorSignature : Signature where
  Params := Unit
  State _ := Vec
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def squareActual : Realization realVectorSignature :=
  realize realVectorSignature (fun _ _ a => ‖a‖ ^ 2) (fun e => nomatch e)
def normActual : Realization realVectorSignature :=
  realize realVectorSignature (fun _ _ a => ‖a‖) (fun e => nomatch e)
def normRejected : Realization realVectorSignature :=
  realize realVectorSignature (fun _ _ _ => 1) (fun e => nomatch e)

theorem normDependence : ObservationalDependence realVectorSignature normActual := by
  intro i
  refine ⟨(), 0, !₂[0,0,1], ?_⟩
  intro h
  have hz : ‖(!₂[0,0,1] : Vec)‖ = 0 := by simpa [normActual, realize] using h.symm
  have hv := norm_eq_zero.mp hz
  have hc := congrArg (fun a : Vec => a 2) hv
  change (1 : ℝ) = 0 at hc
  norm_num at hc

@[reducible] def coordsArena : Arena where
  signature := realVectorSignature
  Law R := ∀ a : Vec, R.readout () () a = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2

theorem coordsPositive : coordsArena.Law squareActual := norm_sq_coords
theorem coordsNegative : ¬ coordsArena.Law normRejected := by
  intro h
  have hh := h 0
  norm_num [normRejected, realize] at hh

def coordsEvidence : Registration coordsArena
    (type_of% (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.norm_sq_coords)) where
  actual := squareActual
  bridge := Iff.rfl
  variation := ⟨coordsPositive, normRejected, coordsNegative⟩
  sensitivity := ⟨fun i => ⟨normRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, coordsNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, !₂[0,0,1], ?_⟩
    intro h
    have hz : ‖(!₂[0,0,1] : Vec)‖ ^ 2 = 0 := by
      simpa [squareActual, realize] using h.symm
    have hv := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    have hc := congrArg (fun a : Vec => a 2) hv
    change (1 : ℝ) = 0 at hc
    norm_num at hc

abbrev traceSignature : Signature where
  Params := Unit
  State _ := Mat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def traceActual : Realization traceSignature :=
  realize traceSignature (fun _ _ A => Matrix.trace A) (fun e => nomatch e)
def traceRejected : Realization traceSignature :=
  realize traceSignature (fun _ _ _ => 1) (fun e => nomatch e)
@[reducible] def traceArena : Arena where
  signature := traceSignature
  Law R := ∀ a b : Vec, R.readout () () (B a * B b) = ((2 * inner ℝ a b : ℝ) : ℂ)
theorem tracePositive : traceArena.Law traceActual := trace_B_mul
theorem traceNegative : ¬ traceArena.Law traceRejected := by
  intro h
  have hh := h 0 0
  norm_num [traceRejected, realize] at hh

def traceEvidence : Registration traceArena
    (type_of% (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.trace_B_mul)) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨tracePositive, traceRejected, traceNegative⟩
  sensitivity := ⟨fun i => ⟨traceRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, traceNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [traceActual, realize, Matrix.trace_one]

@[reducible] def scalarArena : Arena where
  signature := realVectorSignature
  Law R := ∀ (t : ℝ) (a : Vec), (scalarB t a).PosSemidef ↔ R.readout () () a ≤ t
theorem scalarPositive : scalarArena.Law normActual := scalarB_posSemidef_iff
theorem scalarNegative : ¬ scalarArena.Law normRejected := by
  intro h
  have hp := (scalarB_posSemidef_iff 0 (0 : Vec)).mpr (by simp)
  have hh := (h 0 0).mp hp
  change (1 : ℝ) ≤ 0 at hh
  norm_num at hh

def scalarEvidence : Registration scalarArena
    (type_of% (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB_posSemidef_iff)) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨scalarPositive, normRejected, scalarNegative⟩
  sensitivity := ⟨fun i => ⟨normRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, scalarNegative⟩,
    fun i => nomatch i⟩
  dependence := normDependence

@[reducible] def halfArena : Arena where
  signature := realVectorSignature
  Law R := ∀ (t : ℝ) (a : Vec), ((1 / 2 : ℂ) • scalarB t a).PosSemidef ↔ R.readout () () a ≤ t
theorem halfPositive : halfArena.Law normActual := half_scalarB_posSemidef_iff
theorem halfNegative : ¬ halfArena.Law normRejected := by
  intro h
  have hp := (half_scalarB_posSemidef_iff 0 (0 : Vec)).mpr (by simp)
  have hh := (h 0 0).mp hp
  change (1 : ℝ) ≤ 0 at hh
  norm_num at hh

def halfEvidence : Registration halfArena
    (type_of% (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.half_scalarB_posSemidef_iff)) where
  actual := normActual
  bridge := Iff.rfl
  variation := ⟨halfPositive, normRejected, halfNegative⟩
  sensitivity := ⟨fun i => ⟨normRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, halfNegative⟩,
    fun i => nomatch i⟩
  dependence := normDependence

abbrev intervalSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def intervalActual : Realization intervalSignature :=
  realize intervalSignature (fun _ _ t => Set.Icc 0 t) (fun e => nomatch e)
def intervalRejected : Realization intervalSignature :=
  realize intervalSignature (fun _ _ _ => ∅) (fun e => nomatch e)
@[reducible] def endpointArena : Arena where
  signature := intervalSignature
  Law R := endpoint ∈ R.readout () () 1
theorem endpointPositive : endpointArena.Law intervalActual := endpoint_mem_Icc
theorem endpointNegative : ¬ endpointArena.Law intervalRejected := by
  simp [endpointArena, intervalRejected, realize]

def endpointEvidence : Registration endpointArena
    (type_of% (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.endpoint_mem_Icc)) where
  actual := intervalActual
  bridge := Iff.rfl
  variation := ⟨endpointPositive, intervalRejected, endpointNegative⟩
  sensitivity := ⟨fun i => ⟨intervalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, endpointNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have hh := Set.ext_iff.mp h 1
    norm_num [intervalActual, realize] at hh

abbrev predicateSignature : Signature where
  Params := Tuple
  State _ := Fin 4
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool → Mat
  Anchor := Empty
  finiteAnchor := inferInstance

def predicateActual : Realization predicateSignature :=
  realize predicateSignature (fun _ E i => E i) (fun e => nomatch e)
def predicateRejected : Realization predicateSignature :=
  realize predicateSignature (fun _ _ i => fun _ => (1 / 2 : ℂ) • 1) (fun e => nomatch e)

/-- A genuine parent gives a realizable fiber for the rejection and dependence tests. -/
def uniformParent : (Fin 4 → Bool) → Mat := fun _ => (1 / 16 : ℂ) • 1

theorem uniformParentPOVM : IsPOVM uniformParent := by
  constructor
  · intro ε
    exact Matrix.PosSemidef.one.smul (by norm_num [Complex.le_def])
  · simp [uniformParent, Finset.sum_const, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]

def uniformMarginal : Tuple := fun i b => ∑ ε with ε i = b, uniformParent ε

theorem uniformCompatible : Compatible4 uniformMarginal :=
  compatible_of_parent uniformParent uniformParentPOVM (fun _ _ => rfl)

theorem zeroIncompatible : ¬ Compatible4 (0 : Tuple) := by
  intro h
  have hh := (h.1 0).2
  have he := congrArg (fun A : Mat => A 0 0) hh
  norm_num [Matrix.one_apply] at he

@[reducible] def parentArena : Arena where
  signature := predicateSignature
  Law R := ∀ {E : Tuple} (J : (Fin 4 → Bool) → Mat) (_hJ : IsPOVM J)
    (_hm : ∀ i b, R.readout () E i b = ∑ ε with ε i = b, J ε), Compatible4 E

theorem parentPositive : parentArena.Law predicateActual := by
  intro E J hJ hm
  exact compatible_of_parent J hJ hm

theorem parentNegative : ¬ parentArena.Law predicateRejected := by
  intro h
  apply zeroIncompatible
  apply h (E := 0) uniformParent uniformParentPOVM
  intro i b
  have hm : uniformMarginal i b = (1 / 2 : ℂ) • (1 : Mat) := by
    simp only [uniformMarginal, uniformParent, Finset.sum_const]
    have hc : (Finset.univ.filter (fun ε : Fin 4 → Bool => ε i = b)).card = 8 := by
      rw [Finset.card_filter]
      fin_cases i <;> cases b <;> decide
    rw [hc, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    norm_num
  exact hm.symm

def parentEvidence : Registration parentArena
    (type_of% (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.compatible_of_parent)) where
  actual := predicateActual
  bridge := Iff.rfl
  variation := ⟨parentPositive, predicateRejected, parentNegative⟩
  sensitivity := ⟨fun i => ⟨predicateRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, parentNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(fun j _ => if j = 0 then (1 : Mat) else 0), 0, 1, ?_⟩
    intro h
    have hh := congrArg (fun f : Bool → Mat => f false 0 0) h
    norm_num [predicateActual, realize, Matrix.one_apply] at hh

abbrev tupleSignature : Signature where
  Params := Unit
  State _ := Tuple
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Tuple
  Anchor := Empty
  finiteAnchor := inferInstance

def noisyActual : Realization tupleSignature :=
  realize tupleSignature (fun _ _ E => noisy endpoint E) (fun e => nomatch e)
def noisyRejected : Realization tupleSignature :=
  realize tupleSignature (fun _ _ _ => 0) (fun e => nomatch e)
@[reducible] def allArena : Arena where
  signature := tupleSignature
  Law R := ∀ (E : Tuple) (_hE : ∀ i, IsPOVM (E i)), Compatible4 (R.readout () () E)
theorem allPositive : allArena.Law noisyActual := all_povms_compatible
theorem allNegative : ¬ allArena.Law noisyRejected := by
  intro h
  exact zeroIncompatible (h uniformMarginal uniformCompatible.1)

def allEvidence : Registration allArena
    (type_of% (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.all_povms_compatible)) where
  actual := noisyActual
  bridge := Iff.rfl
  variation := ⟨allPositive, noisyRejected, allNegative⟩
  sensitivity := ⟨fun i => ⟨noisyRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, allNegative⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, (fun _ _ => (1 : Mat)), ?_⟩
    intro h
    have hh := congrArg (fun E : Tuple => (E 0 true 0 0).re) h
    have hs : Real.sqrt 13 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    simp [noisyActual, realize, noisy, Matrix.one_apply, Pi.zero_apply, Matrix.zero_apply, Complex.real_smul,
      endpoint, Complex.mul_re, Complex.mul_im] at hh
    change (0 : ℝ) = 1 at hh
    norm_num at hh

noncomputable def formulaRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula)
    (type_of% (realize vectorSignature (fun _ _ a => B a) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula
    "Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction/Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.formulaArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.formulaEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨formulaArena⟩,
  objectArena := .source ⟨formulaArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source formulaArena ⟨formulaEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize vectorSignature (fun _ _ a => B a) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.FourQubitParentConstruction, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms formulaRegistration

noncomputable def smulRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_real_smul)
    (type_of% (realize vectorSignature (fun _ _ a => B a) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_real_smul
    "Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction/Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.smulArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.smulEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨smulArena⟩,
  objectArena := .source ⟨smulArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source smulArena ⟨smulEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize vectorSignature (fun _ _ a => B a) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.FourQubitParentConstruction, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms smulRegistration

noncomputable def negRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_neg)
    (type_of% (realize vectorSignature (fun _ _ a => B a) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_neg
    "Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction/Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.negArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.negEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨negArena⟩,
  objectArena := .source ⟨negArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source negArena ⟨negEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize vectorSignature (fun _ _ a => B a) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.FourQubitParentConstruction, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms negRegistration

noncomputable def sumRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_sum.{u})
    (type_of% (realize vectorSignature (fun _ _ a => B a) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_sum
    "Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction/Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.sumArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.sumEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨sumArena.{u}⟩,
  objectArena := .source ⟨sumArena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source sumArena.{u} ⟨sumEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize vectorSignature (fun _ _ a => B a) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.FourQubitParentConstruction, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms sumRegistration

noncomputable def coordsRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.norm_sq_coords)
    (type_of% (realize realVectorSignature (fun _ _ a => ‖a‖ ^ 2) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.Measurement.FourQubitParentConstruction.norm_sq_coords
    "Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction/Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.coordsArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.coordsEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨coordsArena⟩,
  objectArena := .source ⟨coordsArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source coordsArena ⟨coordsEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize realVectorSignature (fun _ _ a => ‖a‖ ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.FourQubitParentConstruction, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms coordsRegistration

noncomputable def traceRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.trace_B_mul)
    (type_of% (realize traceSignature (fun _ _ A => Matrix.trace A) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.Measurement.FourQubitParentConstruction.trace_B_mul
    "Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction/Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.traceArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.traceEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨traceArena⟩,
  objectArena := .source ⟨traceArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source traceArena ⟨traceEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize traceSignature (fun _ _ A => Matrix.trace A) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.FourQubitParentConstruction, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms traceRegistration

noncomputable def scalarRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB_posSemidef_iff)
    (type_of% (realize realVectorSignature (fun _ _ a => ‖a‖) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB_posSemidef_iff
    "Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction/Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨scalarArena⟩,
  objectArena := .source ⟨scalarArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source scalarArena ⟨scalarEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize realVectorSignature (fun _ _ a => ‖a‖) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.FourQubitParentConstruction, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "arg", "fn", "arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms scalarRegistration

noncomputable def halfRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.half_scalarB_posSemidef_iff)
    (type_of% (realize realVectorSignature (fun _ _ a => ‖a‖) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.Measurement.FourQubitParentConstruction.half_scalarB_posSemidef_iff
    "Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction/Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.halfArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.halfEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨halfArena⟩,
  objectArena := .source ⟨halfArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source halfArena ⟨halfEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize realVectorSignature (fun _ _ a => ‖a‖) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.FourQubitParentConstruction, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "arg", "fn", "arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms halfRegistration

noncomputable def endpointRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.endpoint_mem_Icc)
    (type_of% (realize intervalSignature (fun _ _ t => Set.Icc 0 t) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.Measurement.FourQubitParentConstruction.endpoint_mem_Icc
    "Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction/Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.endpointArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.endpointEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨endpointArena⟩,
  objectArena := .source ⟨endpointArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source endpointArena ⟨endpointEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize intervalSignature (fun _ _ t => Set.Icc 0 t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.FourQubitParentConstruction, definition := none,
    coordinates := #[], readouts := #[{
      path := #["fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms endpointRegistration

noncomputable def parentRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.compatible_of_parent)
    (type_of% (realize predicateSignature (fun _ E i => E i) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.Measurement.FourQubitParentConstruction.compatible_of_parent
    "Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction/Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.parentArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.parentEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨parentArena⟩,
  objectArena := .source ⟨parentArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source parentArena ⟨parentEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize predicateSignature (fun _ E i => E i) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.FourQubitParentConstruction, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "domain", "body", "body", "fn", "arg", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms parentRegistration

noncomputable def allRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurement.FourQubitParentConstruction.all_povms_compatible)
    (type_of% (realize tupleSignature (fun _ _ E => noisy endpoint E) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.Measurement.FourQubitParentConstruction.all_povms_compatible
    "Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction/Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.allArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction.allEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨allArena⟩,
  objectArena := .source ⟨allArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source allArena ⟨allEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize tupleSignature (fun _ _ E => noisy endpoint E) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.FourQubitParentConstruction, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms allRegistration

end Reg.D5.S3.Quantum.Measurement.FourQubitParentConstruction
