import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Lattices.CyclotomicTraceCovolume
import Reg.Support.UniverseSingleReadout
import Mathlib.Algebra.Field.ULift

/-! The discriminant square root in the trace covolume of fractional ideals. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open _root_.D5.S3.Combinatorics.Lattices
open CyclotomicTraceCovolume
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open LeanInformationAudit
open scoped Classical nonZeroDivisors

universe u

namespace Reg.D5.S3.Combinatorics.Lattices.CyclotomicTraceCovolume

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (K : Type u) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ),
    (∀ x : mixedSpace K, ‖traceVector K x‖ ^ 2 =
      (∑ w : {w : InfinitePlace K // IsReal w}, (x.1 w) ^ 2) +
      2 * ∑ w : {w : InfinitePlace K // IsComplex w}, ‖x.2 w‖ ^ 2) ∧
    ZLattice.covolume (traceIdealLattice K I) =
      V.readout () () |(discr K : ℝ)| * (FractionalIdeal.absNorm I.val : ℝ) ∧
    -Real.log (ZLattice.covolume (traceIdealLattice K I)) / finrank ℚ K =
      idealDegree K I / finrank ℚ K - discriminantShift K ∧
    EuclideanHarderNarasimhan.covolume (traceIdealLattice K I) =
      Real.sqrt |(discr K : ℝ)| * (FractionalIdeal.absNorm I.val : ℝ)

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  classical
  intro law
  let K := ULift.{u} ℚ
  letI : NumberField K := NumberField.of_ringEquiv ℚ K (ULift.ringEquiv.symm : ℚ ≃+* K)
  have h := (law K 1).2.1
  have hp := ZLattice.covolume_pos (traceIdealLattice K 1)
  change ZLattice.covolume (traceIdealLattice K 1) =
    0 * (FractionalIdeal.absNorm (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ).val : ℝ) at h
  rw [zero_mul] at h
  exact (ne_of_gt hp) h

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, by change Real.sqrt 0 ≠ Real.sqrt 1; norm_num⟩

def family : Registration arena.{u} (type_of% @trace_ideal_formula.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@trace_ideal_formula.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@trace_ideal_formula.{u}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.CyclotomicTraceCovolume.trace_ideal_formula
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.CyclotomicTraceCovolume.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.CyclotomicTraceCovolume
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg",
        "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.CyclotomicTraceCovolume

namespace Reg.D5.S3.Combinatorics.Lattices.CyclotomicTraceCovolume.Ideal

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => Real.log x + 1) (fun e => nomatch e)

def law (V : Realization signature) : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] {n : ℕ} [NeZero n]
    [IsCyclotomicExtension {n} ℚ K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ),
    let L := traceIdealLattice K I
    (EuclideanHarderNarasimhan.slopeData L).Semistable ⊥ ⊤ ∧
      (∀ l : List (EuclideanSublattices.Sublattice L),
        (EuclideanHarderNarasimhan.slopeData L).Filtration ⊥ ⊤ l ↔ l = [⊤]) ∧
      -V.readout () () (EuclideanHarderNarasimhan.covolume L) / finrank ℤ L =
        idealDegree K I / finrank ℚ K - discriminantShift K

abbrev arena : Arena where
  signature := signature
  Law := law.{u}

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro law
  let K := ULift.{u} ℚ
  letI : NumberField K := NumberField.of_ringEquiv ℚ K (ULift.ringEquiv.symm : ℚ ≃+* K)
  letI : IsCyclotomicExtension {1} ℚ K :=
    IsCyclotomicExtension.singleton_one_of_algebraMap_bijective
      (by rintro ⟨x⟩; exact ⟨x, rfl⟩)
  have hd : finrank ℚ K = 1 := by
    simpa using IsCyclotomicExtension.Rat.finrank 1 K
  have h := (law K (n := 1) 1).2.2
  have hg := (cyclotomic_ideal_hn K (n := 1) 1).2.2
  change -(Real.log (EuclideanHarderNarasimhan.covolume (traceIdealLattice K 1)) + 1) /
    finrank ℤ (traceIdealLattice K 1) =
      idealDegree K 1 / finrank ℚ K - discriminantShift K at h
  rw [ZLattice.rank ℝ, euclidean.finrank, hd, Nat.cast_one, div_one] at h hg
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 1, Real.exp 1, ?_⟩
  change Real.log 1 ≠ Real.log (Real.exp 1)
  simp

def family : Registration arena.{u} (type_of% @cyclotomic_ideal_hn.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclotomic_ideal_hn.{u}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cyclotomic_ideal_hn.{u}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.CyclotomicTraceCovolume.cyclotomic_ideal_hn
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.CyclotomicTraceCovolume.Ideal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.CyclotomicTraceCovolume
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "arg", "fn", "arg", "fn", "arg",
        "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.CyclotomicTraceCovolume.Ideal
