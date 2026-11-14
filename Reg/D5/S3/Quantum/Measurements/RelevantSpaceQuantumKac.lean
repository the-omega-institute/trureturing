import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.PositiveBranchReachableResponse
open _root_.D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac
open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace

noncomputable section
namespace Reg.D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac
universe u

@[reducible] def signature : Signature where
  Params := Type u
  State n := Matrix n n ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix n n ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ S => S) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} {α : Type} [Fintype n] [DecidableEq n]
    (K : α → Matrix n n ℂ) (P : Matrix n n ℂ), P.IsHermitian →
    reachableSpace (fun a => (1 - P) * K a) P = reachableSpace K (R.readout () n P)

private theorem actual_law : arena.{u}.Law actual := by
  exact @monitored_reachable_space_eq.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let K : Unit → Matrix n n ℂ := fun _ => 0
  have heq := h K (1 : Matrix n n ℂ) Matrix.isHermitian_one
  change reachableSpace (fun a => (1 - (1 : Matrix n n ℂ)) * K a) 1 =
    reachableSpace K 0 at heq
  have hzero : reachableSpace K 0 = ⊥ := by
    apply le_antisymm _ bot_le
    apply iSup_le
    intro l
    apply Submodule.span_le.mpr
    rintro y ⟨w, _hw, v, hv, rfl⟩
    have hv0 : v = 0 := by simpa [matrixSupport] using hv
    simp [hv0]
  rw [hzero] at heq
  let v : EuclideanSpace ℂ n := WithLp.toLp 2 (fun _ => (1 : ℂ))
  have hv : v ∈ matrixSupport (1 : Matrix n n ℂ) := by
    simp [matrixSupport, Matrix.toEuclideanLin, Matrix.toLpLin_one]
  have hmem : v ∈ reachableSpace (fun a => (1 - (1 : Matrix n n ℂ)) * K a) 1 := by
    apply (le_iSup (wordSpan (fun a => (1 - (1 : Matrix n n ℂ)) * K a) 1) 0)
    exact Submodule.subset_span ⟨[], by simp, v, hv,
      by simp [krausWord, Matrix.toEuclideanLin, Matrix.toLpLin_one]⟩
  rw [heq, Submodule.mem_bot] at hmem
  have hz := congrArg (fun x : EuclideanSpace ℂ n => WithLp.ofLp x ⟨0⟩) hmem
  simpa [v] using hz

private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨ULift.{u} (Fin 1), 0, 1, ?_⟩
  change (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ) ≠ 1
  exact zero_ne_one

def reconstruction : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac.monitored_reachable_space_eq.{u})
    (Realization signature.{u}) Unit Unit := {
  unitName := `quantumKacMonitoredReachableSpace,
  realizationName := `Reg.D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac.reconstruction,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨reconstruction⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ S => S) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"],
      stateBinder := 5,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms reconstruction
#print axioms registration

namespace OperatorSeries

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} {α : Type} [Fintype n] [DecidableEq n]
    (K : α → Matrix n n ℂ) [Fintype α] (P PiC : Matrix n n ℂ),
    P.PosSemidef → P * P = P →
    PiC.toEuclideanLin = (reachableSpace K P).starProjection.toLinearMap →
    weightedCP K (fun _ => 1) PiC = PiC →
    HasSum (fun k => (weightedCP (fun a => (1 - P) * K a) (fun _ => 1))^[k] P)
      (R.readout () n PiC)

private theorem actual_law : arena.{u}.Law actual := by
  exact @relevant_projection_hasSum.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let K : Unit → Matrix n n ℂ := fun _ => 1
  have hC : reachableSpace K (1 : Matrix n n ℂ) = ⊤ := by
    apply le_antisymm le_top
    intro x _
    apply (le_iSup (wordSpan K (1 : Matrix n n ℂ)) 0)
    apply Submodule.subset_span
    refine ⟨[], by simp, x, ?_, ?_⟩
    · simp [matrixSupport, Matrix.toEuclideanLin, Matrix.toLpLin_one]
    · simp [krausWord, Matrix.toEuclideanLin, Matrix.toLpLin_one]
  have hPiC : (1 : Matrix n n ℂ).toEuclideanLin =
      (reachableSpace K 1).starProjection.toLinearMap := by
    rw [hC, Submodule.starProjection_top]
    ext x
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_one]
  have hu : weightedCP K (fun _ => 1) (1 : Matrix n n ℂ) = 1 := by
    simp [K, weightedCP]
  have hgood := relevant_projection_hasSum K 1 1 Matrix.PosSemidef.one
    (by simp) hPiC hu
  have hbad := h K 1 1 Matrix.PosSemidef.one (by simp) hPiC hu
  change HasSum _ (0 : Matrix n n ℂ) at hbad
  exact one_ne_zero (hgood.unique hbad)

private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

def reconstruction : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := Reg.D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac.dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac.relevant_projection_hasSum.{u})
    (Realization signature.{u}) Unit Unit := {
  unitName := `quantumKacRelevantProjectionSeries,
  realizationName := `Reg.D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac.OperatorSeries.reconstruction,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨reconstruction⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ S => S) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg"],
      stateBinder := 7,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms reconstruction
#print axioms registration

end OperatorSeries

namespace ReturnMoments

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} {α : Type} [Fintype n] [DecidableEq n]
    (K : α → Matrix n n ℂ) [Fintype α] (P PiC : Matrix n n ℂ),
    P.PosSemidef → P * P = P → P.trace = 1 →
    (∑ a, (K a)ᴴ * K a) = 1 →
    PiC.toEuclideanLin = (reachableSpace K P).starProjection.toLinearMap →
    weightedCP K (fun _ => 1) PiC = PiC →
    let E := weightedCP K (fun _ => 1)
    let F := weightedCP (fun a => (1 - P) * K a) (fun _ => 1)
    let p := fun k => (P * E (F^[k] P)).trace.re
    HasSum (fun k => F^[k] P) (R.readout () n PiC) ∧ (∀ k, 0 ≤ p k) ∧
      HasSum p 1 ∧ HasSum (fun k : ℕ => (k + 1 : ℝ) * p k)
        (Module.finrank ℂ (reachableSpace K P) : ℝ)

private theorem actual_law : arena.{u}.Law actual := by
  exact @relevant_space_quantum_kac.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} (Fin 1)
  let K : Unit → Matrix n n ℂ := fun _ => 1
  have hC : reachableSpace K (1 : Matrix n n ℂ) = ⊤ := by
    apply le_antisymm le_top
    intro x _
    apply (le_iSup (wordSpan K (1 : Matrix n n ℂ)) 0)
    apply Submodule.subset_span
    refine ⟨[], by simp, x, ?_, ?_⟩
    · simp [matrixSupport, Matrix.toEuclideanLin, Matrix.toLpLin_one]
    · simp [krausWord, Matrix.toEuclideanLin, Matrix.toLpLin_one]
  have hPiC : (1 : Matrix n n ℂ).toEuclideanLin =
      (reachableSpace K 1).starProjection.toLinearMap := by
    rw [hC, Submodule.starProjection_top]
    ext x
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_one]
  have hu : weightedCP K (fun _ => 1) (1 : Matrix n n ℂ) = 1 := by
    simp [K, weightedCP]
  have htrace : (1 : Matrix n n ℂ).trace = 1 := by simp [n]
  have htp : ∑ a, (K a)ᴴ * K a = 1 := by simp [K]
  have hgood := relevant_space_quantum_kac K 1 1 Matrix.PosSemidef.one
    (by simp) htrace htp hPiC hu
  have hbad := h K 1 1 Matrix.PosSemidef.one (by simp) htrace htp hPiC hu
  have hz : HasSum (fun k =>
      (weightedCP (fun a => (1 - (1 : Matrix n n ℂ)) * K a) (fun _ => 1))^[k] 1) 0 :=
    hbad.1
  exact one_ne_zero (hgood.1.unique hz)

private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

def reconstruction : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := Reg.D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac.dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac.relevant_space_quantum_kac.{u})
    (Realization signature.{u}) Unit Unit := {
  unitName := `quantumKacActualReturnMoments,
  realizationName := `Reg.D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac.ReturnMoments.reconstruction,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨reconstruction⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ S => S) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg"],
      stateBinder := 7,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms reconstruction
#print axioms registration

end ReturnMoments

namespace OriginalCarrier
structure Carrier where
  Space : Type u
  [group : NormedAddCommGroup Space]
  [inner : InnerProductSpace ℂ Space]
  [finite : FiniteDimensional ℂ Space]
attribute [instance] Carrier.group Carrier.inner Carrier.finite
@[reducible] def sig : Signature where
  Params := Carrier.{u}
  State c := c.Space
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ c := c.Space
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization sig.{u} := realize sig (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization sig.{u} := realize sig (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := sig.{u}
  Law R := ∀ {H : Type u} [g : NormedAddCommGroup H] [i : InnerProductSpace ℂ H]
    [d : FiniteDimensional ℂ H] {α : Type} [Fintype α]
    (L : α → H →L[ℂ] H) (v : H) (_hv : ‖v‖ = 1)
    (_hTP : ∑ a, (L a).adjoint * L a = 1)
    (_hunital :
      let C := Submodule.span ℂ (Set.range (fun w : List α => w.foldr (fun a x => L a x) v))
      (∑ a, L a * C.starProjection * (L a).adjoint) = C.starProjection),
    let y := R.readout () ({ Space := H, group := g, inner := i, finite := d } : Carrier.{u}) v
    let P := InnerProductSpace.rankOne ℂ y y
    let C := Submodule.span ℂ (Set.range (fun w : List α => w.foldr (fun a x => L a x) v))
    let E := fun X : H →L[ℂ] H => ∑ a, L a * X * (L a).adjoint
    let F := fun X : H →L[ℂ] H => (1 - P) * E X * (1 - P)
    let p := fun k => (LinearMap.trace ℂ H (P * E (F^[k] P)).toLinearMap).re
    HasSum (fun k => F^[k] P) C.starProjection ∧ (∀ k, 0 ≤ p k) ∧
      HasSum p 1 ∧ HasSum (fun k : ℕ => (k + 1 : ℝ) * p k)
        (Module.finrank ℂ C : ℝ)
private theorem actual_law : arena.{u}.Law actual := by
  exact @pure_vector_quantum_kac.{u}
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let H := EuclideanSpace ℂ (ULift.{u} (Fin 1))
  let b := EuclideanSpace.basisFun (ULift.{u} (Fin 1)) ℂ
  let v : H := b ⟨0⟩
  let L : Unit → H →L[ℂ] H := fun _ => 1
  let C := Submodule.span ℂ (Set.range
    (fun w : List Unit => w.foldr (fun a x => L a x) v))
  have hv : ‖v‖ = 1 := b.norm_eq_one _
  have htp : ∑ a, (L a).adjoint * L a = 1 := by simp [L, ← ContinuousLinearMap.star_eq_adjoint]
  have hu : (∑ a, L a * C.starProjection * (L a).adjoint) = C.starProjection := by
    simp [L, ← ContinuousLinearMap.star_eq_adjoint]
  have hh := h L v hv htp hu
  have hs : HasSum (fun _ : ℕ => (0 : H →L[ℂ] H)) C.starProjection := by
    simpa [C, L, rejected, actual, realize, sig, ← ContinuousLinearMap.star_eq_adjoint,
      show (fun X : H →L[ℂ] H => X) = id from rfl] using hh.1
  have hz : C.starProjection = 0 := hs.unique hasSum_zero
  have hvC : v ∈ C := Submodule.subset_span ⟨[], rfl⟩
  have hp := C.starProjection_eq_self_iff.mpr hvC
  rw [hz] at hp
  have hnorm := congrArg norm hp
  simp [hv] at hnorm
private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i
private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro i
  cases i
  let H := EuclideanSpace ℂ (ULift.{u} (Fin 1))
  let b := EuclideanSpace.basisFun (ULift.{u} (Fin 1)) ℂ
  let v : H := b ⟨0⟩
  refine ⟨({ Space := H, group := inferInstance, inner := inferInstance, finite := inferInstance } : Carrier.{u}), 0, v, ?_⟩
  change (0 : H) ≠ v
  intro h
  have hv : ‖v‖ = 1 := b.norm_eq_one ⟨0⟩
  rw [← h] at hv
  simp at hv
def reconstruction : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence
noncomputable def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac.pure_vector_quantum_kac.{u})
    (Realization sig.{u}) Unit Unit := {
  unitName := `quantumKacOriginalCarrier,
  realizationName := `Reg.D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac.OriginalCarrier.reconstruction,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨reconstruction⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize sig (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac,
    definition := none,
    coordinates := #[0, 1, 2, 3],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "value", "fn", "arg"],
      stateBinder := 7, functionOperand := false, stateOperand := none,
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "value", "arg"],
      stateBinder := 7, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms registration
end OriginalCarrier

end Reg.D5.S3.Quantum.Measurements.RelevantSpaceQuantumKac
