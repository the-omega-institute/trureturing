import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.TraceClass.Compact
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder InnerProductSpace Classical lp
open Filter Topology HilbertSchmidt
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.TraceClass.Compact
abbrev scalarSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def sqrtActual := realize scalarSignature.{u} (fun _ _ x => Real.sqrt x) (fun a => nomatch a)
def scalarActual := realize scalarSignature.{u} (fun _ _ x => x) (fun a => nomatch a)
def scalarRejected := realize scalarSignature.{u} (fun _ _ _ => -1) (fun a => nomatch a)

theorem sqrtDependence : ObservationalDependence scalarSignature.{u} sqrtActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  simp [sqrtActual, realize]

theorem scalarDependence : ObservationalDependence scalarSignature.{u} scalarActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  simp [scalarActual, realize]

def normLaw (R : Realization scalarSignature.{u}) : Prop :=
    ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {w : Set H} (b : HilbertBasis w ℂ H) (T : H →L[ℂ] H) (hT : Summable (fun i : w => ‖T (b i)‖ ^ 2)),
    ‖T‖ ≤ R.readout ⟨()⟩ () (∑' i : w, ‖T (b i)‖ ^ 2)
abbrev normArena : Arena where
  signature := scalarSignature.{u}
  Law := normLaw

theorem normActual : normArena.{u}.Law sqrtActual := by
  intro H _ _ _ w b T hT
  exact opNorm_le_sqrt_column_square_sum b T hT

theorem normRejected : ¬ normArena.{u}.Law scalarRejected := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ K
  have hh := h (H := K) b (0 : K →L[ℂ] K) (by simp)
  have : (0 : ℝ) ≤ -1 := by simpa [scalarRejected, realize, finiteColumnApprox] using hh
  norm_num at this

def normFamily : Registration normArena (normArena.Law sqrtActual) where
  actual := realize scalarSignature.{u} (fun _ _ x => Real.sqrt x) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨normActual, scalarRejected, normRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨scalarRejected, ?_, rfl, normRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := sqrtDependence

def normRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@HilbertSchmidt.opNorm_le_sqrt_column_square_sum.{u}) (type_of% (realize scalarSignature.{u} (fun _ _ x => Real.sqrt x) (fun a => nomatch a))) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.normUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.normFamily
  realizationSource := none
  generated := false
  arena := .source ⟨normArena⟩
  objectArena := .source ⟨normArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source normArena ⟨normFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature.{u} (fun _ _ x => Real.sqrt x) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TraceClass.Compact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def tailLaw (R : Realization scalarSignature.{u}) : Prop :=
    ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {w : Set H} (b : HilbertBasis w ℂ H) (S : H →L[ℂ] H) (hS : Summable (fun i : w => ‖S (b i)‖ ^ 2)) (F : Finset w),
    ‖S - finiteColumnApprox b S F‖ ≤ R.readout ⟨()⟩ () (tailColumnSquareSum b S F)
abbrev tailArena : Arena where
  signature := scalarSignature.{u}
  Law := tailLaw

theorem tailActual : tailArena.{u}.Law sqrtActual := by
  intro H _ _ _ w b S hS F
  exact norm_sub_finiteColumnApprox_le b S hS F

theorem tailRejected : ¬ tailArena.{u}.Law scalarRejected := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ K
  have hh := h (H := K) b (0 : K →L[ℂ] K) (by simp) ∅
  have : (0 : ℝ) ≤ -1 := by simpa [scalarRejected, realize, finiteColumnApprox] using hh
  norm_num at this

def tailFamily : Registration tailArena (tailArena.Law sqrtActual) where
  actual := realize scalarSignature.{u} (fun _ _ x => Real.sqrt x) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨tailActual, scalarRejected, tailRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨scalarRejected, ?_, rfl, tailRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := sqrtDependence

def tailRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@HilbertSchmidt.norm_sub_finiteColumnApprox_le.{u}) (type_of% (realize scalarSignature.{u} (fun _ _ x => Real.sqrt x) (fun a => nomatch a))) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.tailUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.tailFamily
  realizationSource := none
  generated := false
  arena := .source ⟨tailArena⟩
  objectArena := .source ⟨tailArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tailArena ⟨tailFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature.{u} (fun _ _ x => Real.sqrt x) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TraceClass.Compact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def squareTailLaw (R : Realization scalarSignature.{u}) : Prop :=
    ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {w : Set H} (b : HilbertBasis w ℂ H) (S : H →L[ℂ] H) (hS : Summable (fun i : w => ‖S (b i)‖ ^ 2)) (F : Finset w),
    ‖S - finiteColumnApprox b S F‖ ^ 2 ≤ R.readout ⟨()⟩ () (tailColumnSquareSum b S F)
abbrev squareTailArena : Arena where
  signature := scalarSignature.{u}
  Law := squareTailLaw

theorem squareTailActual : squareTailArena.{u}.Law scalarActual := by
  intro H _ _ _ w b S hS F
  exact norm_sub_finiteColumnApprox_sq_le b S hS F

theorem squareTailRejected : ¬ squareTailArena.{u}.Law scalarRejected := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ K
  have hh := h (H := K) b (0 : K →L[ℂ] K) (by simp) ∅
  have : (0 : ℝ) ≤ -1 := by simpa [scalarRejected, realize, finiteColumnApprox] using hh
  norm_num at this

def squareTailFamily : Registration squareTailArena (squareTailArena.Law scalarActual) where
  actual := realize scalarSignature.{u} (fun _ _ x => x) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨squareTailActual, scalarRejected, squareTailRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨scalarRejected, ?_, rfl, squareTailRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := scalarDependence

def squareTailRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@HilbertSchmidt.norm_sub_finiteColumnApprox_sq_le.{u}) (type_of% (realize scalarSignature.{u} (fun _ _ x => x) (fun a => nomatch a))) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.squareTailUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.squareTailFamily
  realizationSource := none
  generated := false
  arena := .source ⟨squareTailArena⟩
  objectArena := .source ⟨squareTailArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source squareTailArena ⟨squareTailFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature.{u} (fun _ _ x => x) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TraceClass.Compact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

structure Carrier where
  H : Type u
  [normed : NormedAddCommGroup H]
  [inner : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
attribute [instance] Carrier.normed Carrier.inner Carrier.complete

abbrev compactSignature : Signature where
  Params := Carrier.{u}
  State p := p.H →L[ℂ] p.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def compactActual := realize compactSignature.{u} (fun _ _ T => IsCompactOperator T) (fun a => nomatch a)
def compactRejected := realize compactSignature.{u} (fun _ _ _ => False) (fun a => nomatch a)

theorem compactDependence : ObservationalDependence compactSignature.{u} compactActual := by
  intro i
  let K := ℓ²(ULift.{u} ℕ, ℂ)
  let p : Carrier.{u} := ⟨K⟩
  refine ⟨p, 0, ContinuousLinearMap.id ℂ K, ?_⟩
  change IsCompactOperator (0 : K →L[ℂ] K) ≠ IsCompactOperator (ContinuousLinearMap.id ℂ K)
  intro h
  have hcompact : IsCompactOperator (ContinuousLinearMap.id ℂ K) := h ▸ isCompactOperator_zero
  letI : FiniteDimensional ℂ K := FiniteDimensional.of_isCompactOperator_id hcompact
  let b : HilbertBasis (ULift.{u} ℕ) ℂ K := default
  haveI : Finite (ULift.{u} ℕ) := b.orthonormal.linearIndependent.finite
  exact not_finite (ULift.{u} ℕ)

def finiteCompactLaw (R : Realization compactSignature.{u}) : Prop :=
    ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {w : Set H} (b : HilbertBasis w ℂ H) (S : H →L[ℂ] H) (F : Finset w),
    R.readout () (⟨H⟩ : Carrier) (finiteColumnApprox b S F)
abbrev finiteCompactArena : Arena where
  signature := compactSignature.{u}
  Law := finiteCompactLaw

theorem finiteCompactActual : finiteCompactArena.{u}.Law compactActual := by
  intro H _ _ _ w b S F
  exact isCompactOperator_finiteColumnApprox b S F

theorem finiteCompactRejected : ¬ finiteCompactArena.{u}.Law compactRejected := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ K
  exact h (H := K) b (0 : K →L[ℂ] K) ∅

def finiteCompactFamily : Registration finiteCompactArena (finiteCompactArena.Law compactActual) where
  actual := realize compactSignature.{u} (fun _ _ T => IsCompactOperator T) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨finiteCompactActual, compactRejected, finiteCompactRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨compactRejected, ?_, rfl, finiteCompactRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := compactDependence

def finiteCompactRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@HilbertSchmidt.isCompactOperator_finiteColumnApprox.{u}) (type_of% (realize compactSignature.{u} (fun _ _ T => IsCompactOperator T) (fun a => nomatch a))) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.finiteCompactUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.finiteCompactFamily
  realizationSource := none
  generated := false
  arena := .source ⟨finiteCompactArena⟩
  objectArena := .source ⟨finiteCompactArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source finiteCompactArena ⟨finiteCompactFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize compactSignature.{u} (fun _ _ T => IsCompactOperator T) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TraceClass.Compact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def hsCompactLaw (R : Realization compactSignature.{u}) : Prop :=
    ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S : H →L[ℂ] H} (hS : IsHilbertSchmidt S), R.readout () (⟨H⟩ : Carrier) S
abbrev hsCompactArena : Arena where
  signature := compactSignature.{u}
  Law := hsCompactLaw

theorem hsCompactActual : hsCompactArena.{u}.Law compactActual := by
  intro H _ _ _ S hS
  exact isCompactOperator_of_isHilbertSchmidt hS

theorem hsCompactRejected : ¬ hsCompactArena.{u}.Law compactRejected := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  exact h (isHilbertSchmidt_zero (H := K))

def hsCompactFamily : Registration hsCompactArena (hsCompactArena.Law compactActual) where
  actual := realize compactSignature.{u} (fun _ _ T => IsCompactOperator T) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨hsCompactActual, compactRejected, hsCompactRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨compactRejected, ?_, rfl, hsCompactRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := compactDependence

def hsCompactRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@HilbertSchmidt.isCompactOperator_of_isHilbertSchmidt.{u}) (type_of% (realize compactSignature.{u} (fun _ _ T => IsCompactOperator T) (fun a => nomatch a))) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.hsCompactUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.hsCompactFamily
  realizationSource := none
  generated := false
  arena := .source ⟨hsCompactArena⟩
  objectArena := .source ⟨hsCompactArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source hsCompactArena ⟨hsCompactFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize compactSignature.{u} (fun _ _ T => IsCompactOperator T) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TraceClass.Compact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def positiveCompactLaw (R : Realization compactSignature.{u}) : Prop :=
    ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hT : IsTraceClass T) (hpos : 0 ≤ T), R.readout () (⟨H⟩ : Carrier) T
abbrev positiveCompactArena : Arena where
  signature := compactSignature.{u}
  Law := positiveCompactLaw

theorem positiveCompactActual : positiveCompactArena.{u}.Law compactActual := by
  intro H _ _ _ T hT hpos
  exact isCompactOperator_of_nonneg_isTraceClass hT hpos

theorem positiveCompactRejected : ¬ positiveCompactArena.{u}.Law compactRejected := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  exact h (isTraceClass_of_finiteDimensional (0 : K →L[ℂ] K)) (by simp)

def positiveCompactFamily : Registration positiveCompactArena (positiveCompactArena.Law compactActual) where
  actual := realize compactSignature.{u} (fun _ _ T => IsCompactOperator T) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨positiveCompactActual, compactRejected, positiveCompactRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨compactRejected, ?_, rfl, positiveCompactRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := compactDependence

def positiveCompactRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@isCompactOperator_of_nonneg_isTraceClass.{u}) (type_of% (realize compactSignature.{u} (fun _ _ T => IsCompactOperator T) (fun a => nomatch a))) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.positiveCompactUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.positiveCompactFamily
  realizationSource := none
  generated := false
  arena := .source ⟨positiveCompactArena⟩
  objectArena := .source ⟨positiveCompactArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source positiveCompactArena ⟨positiveCompactFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize compactSignature.{u} (fun _ _ T => IsCompactOperator T) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TraceClass.Compact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def traceCompactLaw (R : Realization compactSignature.{u}) : Prop :=
    ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hT : IsTraceClass T), R.readout () (⟨H⟩ : Carrier) T
abbrev traceCompactArena : Arena where
  signature := compactSignature.{u}
  Law := traceCompactLaw

theorem traceCompactActual : traceCompactArena.{u}.Law compactActual := by
  intro H _ _ _ T hT
  exact isCompactOperator_of_isTraceClass hT

theorem traceCompactRejected : ¬ traceCompactArena.{u}.Law compactRejected := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  exact h (isTraceClass_of_finiteDimensional (0 : K →L[ℂ] K))

def traceCompactFamily : Registration traceCompactArena (traceCompactArena.Law compactActual) where
  actual := realize compactSignature.{u} (fun _ _ T => IsCompactOperator T) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨traceCompactActual, compactRejected, traceCompactRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨compactRejected, ?_, rfl, traceCompactRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := compactDependence

def traceCompactRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@isCompactOperator_of_isTraceClass.{u}) (type_of% (realize compactSignature.{u} (fun _ _ T => IsCompactOperator T) (fun a => nomatch a))) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.traceCompactUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.traceCompactFamily
  realizationSource := none
  generated := false
  arena := .source ⟨traceCompactArena⟩
  objectArena := .source ⟨traceCompactArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source traceCompactArena ⟨traceCompactFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize compactSignature.{u} (fun _ _ T => IsCompactOperator T) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TraceClass.Compact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev vectorSignature : Signature where
  Params := Carrier.{u}
  State p := p.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.H
  Anchor := Empty
  finiteAnchor := inferInstance

def vectorActual := realize vectorSignature.{u} (fun _ _ x => x) (fun a => nomatch a)
def vectorRejected := realize vectorSignature.{u} (fun _ _ _ => 0) (fun a => nomatch a)

def columnsLaw (R : Realization vectorSignature.{u}) : Prop :=
    ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {w : Set H} (b : HilbertBasis w ℂ H) (S : H →L[ℂ] H) (F : Finset w) (i : w),
    finiteColumnApprox b S F (b i) = if i ∈ F then R.readout () (⟨H⟩ : Carrier) (S (b i)) else 0
abbrev columnsArena : Arena where
  signature := vectorSignature.{u}
  Law := columnsLaw

theorem columnsActual : columnsArena.{u}.Law vectorActual := by
  intro H _ _ _ w b S F i
  exact finiteColumnApprox_apply_basis b S F i

theorem columnsRejected : ¬ columnsArena.{u}.Law vectorRejected := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ K
  have hz (i : w) : b i = 0 := by
    have hh := h (H := K) b (1 : K →L[ℂ] K) {i} i
    simpa [finiteColumnApprox_apply_basis, vectorRejected, realize] using hh
  have : (1 : K →L[ℂ] K) = 0 := ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span) (by
      rintro _ ⟨i, rfl⟩
      simp [hz])
  exact one_ne_zero this

theorem vectorDependence : ObservationalDependence vectorSignature.{u} vectorActual := by
  intro i
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  refine ⟨⟨K⟩, 0, WithLp.toLp 2 (fun _ : ULift.{u} Unit => (1 : ℂ)), ?_⟩
  change (0 : K) ≠ WithLp.toLp 2 (fun _ : ULift.{u} Unit => (1 : ℂ))
  intro h
  have hh := congrArg (fun v : K => v (⟨()⟩ : ULift.{u} Unit)) h
  norm_num at hh

def columnsFamily : Registration columnsArena (columnsArena.Law vectorActual) where
  actual := realize vectorSignature.{u} (fun _ _ x => x) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨columnsActual, vectorRejected, columnsRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨vectorRejected, ?_, rfl, columnsRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := vectorDependence

def columnsRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@HilbertSchmidt.finiteColumnApprox_apply_basis.{u}) (type_of% (realize vectorSignature.{u} (fun _ _ x => x) (fun a => nomatch a))) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.columnsUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.columnsFamily
  realizationSource := none
  generated := false
  arena := .source ⟨columnsArena⟩
  objectArena := .source ⟨columnsArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source columnsArena ⟨columnsFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize vectorSignature.{u} (fun _ _ x => x) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TraceClass.Compact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev netSignature : Signature where
  Params := Carrier.{u}
  State p := p.H →L[ℂ] p.H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.H →L[ℂ] p.H
  Anchor := Empty
  finiteAnchor := inferInstance

def netActual := realize netSignature.{u} (fun _ _ T => T) (fun a => nomatch a)
def netRejected := realize netSignature.{u} (fun _ _ T => T + 1) (fun a => nomatch a)

def netLaw (R : Realization netSignature.{u}) : Prop :=
    ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {w : Set H} (b : HilbertBasis w ℂ H) (S : H →L[ℂ] H) (hS : Summable (fun i : w => ‖S (b i)‖ ^ 2)),
    Tendsto (finiteColumnApprox b S) (atTop : Filter (Finset w))
      (𝓝 (R.readout () (⟨H⟩ : Carrier) S))
abbrev netArena : Arena where
  signature := netSignature.{u}
  Law := netLaw

theorem netActualLaw : netArena.{u}.Law netActual := by
  intro H _ _ _ w b S hS
  exact tendsto_finiteColumnApprox b S hS

theorem netRejectedLaw : ¬ netArena.{u}.Law netRejected := by
  intro h
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ K
  have hh := h (H := K) b (0 : K →L[ℂ] K) (by simp)
  have hz := tendsto_finiteColumnApprox b (0 : K →L[ℂ] K) (by simp)
  have hh' : Tendsto (finiteColumnApprox b (0 : K →L[ℂ] K)) atTop (𝓝 1) := by
    simpa only [netRejected, realize, zero_add] using hh
  have heq : (0 : K →L[ℂ] K) = 1 := tendsto_nhds_unique hz hh'
  exact zero_ne_one heq

theorem netDependence : ObservationalDependence netSignature.{u} netActual := by
  intro i
  let K := EuclideanSpace ℂ (ULift.{u} Unit)
  refine ⟨⟨K⟩, 0, 1, ?_⟩
  exact zero_ne_one


def netFamily : Registration netArena (netArena.Law netActual) where
  actual := realize netSignature.{u} (fun _ _ T => T) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨netActualLaw, netRejected, netRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨netRejected, ?_, rfl, netRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := netDependence

def netRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@HilbertSchmidt.tendsto_finiteColumnApprox.{u}) (type_of% (realize netSignature.{u} (fun _ _ T => T) (fun a => nomatch a))) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.netUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.Compact.netFamily
  realizationSource := none
  generated := false
  arena := .source ⟨netArena⟩
  objectArena := .source ⟨netArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source netArena ⟨netFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize netSignature.{u} (fun _ _ T => T) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.TraceClass.Compact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms compactDependence
#print axioms hsCompactRegistration
end Reg.D5.S3.Quantum.Analysis.TraceClass.Compact
