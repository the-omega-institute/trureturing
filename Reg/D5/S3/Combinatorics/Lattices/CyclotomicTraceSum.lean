import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Lattices.CyclotomicTraceSum
import Reg.Support.UniverseSingleReadout
import Mathlib.Algebra.Field.ULift

/-! The exponential of degree in covolumes of actual orthogonal sums. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open _root_.D5.S3.Combinatorics.Lattices
open CyclotomicTraceCovolume CyclotomicTraceSum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open NumberField NumberField.mixedEmbedding Module
open LeanInformationAudit
open scoped Classical nonZeroDivisors

universe u v

namespace Reg.D5.S3.Combinatorics.Lattices.CyclotomicTraceSum

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (K : Type u) [Field K] [NumberField K]
    {ι : Type v} [Fintype ι] (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ),
    EuclideanHarderNarasimhan.covolume (sumLattice K I) =
      ∏ i, EuclideanHarderNarasimhan.covolume (traceIdealLattice K (I i)) ∧
    EuclideanHarderNarasimhan.covolume (sumLattice K I) =
      (Real.sqrt |(discr K : ℝ)|) ^ Fintype.card ι *
        V.readout () () (-(∑ i, idealDegree K (I i))) ∧
    Module.finrank ℤ (sumLattice K I) = finrank ℚ K * Fintype.card ι ∧
    (Fintype.card ι ≠ 0 →
      -Real.log (EuclideanHarderNarasimhan.covolume (sumLattice K I)) /
          (finrank ℚ K * Fintype.card ι : ℕ) =
        (∑ i, idealDegree K (I i)) / (finrank ℚ K * Fintype.card ι : ℕ) -
          discriminantShift K)

private theorem rejected_fails : ¬ arena.{u,v}.Law rejected := by
  classical
  intro law
  let K := ULift.{u} ℚ
  letI : NumberField K := NumberField.of_ringEquiv ℚ K (ULift.ringEquiv.symm : ℚ ≃+* K)
  let I : ULift.{v} Empty → (FractionalIdeal (𝓞 K)⁰ K)ˣ := fun x => nomatch x.down
  have h := (law K I).2.1
  have hp := EuclideanHarderNarasimhan.covolume_pos (sumLattice K I)
  change EuclideanHarderNarasimhan.covolume (sumLattice K I) =
    (Real.sqrt |(discr K : ℝ)|) ^ Fintype.card (ULift.{v} Empty) * 0 at h
  rw [mul_zero] at h
  exact (ne_of_gt hp) h

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, by change Real.exp 0 ≠ Real.exp 1; exact Real.exp_injective.ne zero_ne_one⟩

def family : Registration arena.{u,v} (type_of% @trace_sum_formula.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@trace_sum_formula.{u,v}, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.{u,v}.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@trace_sum_formula.{u,v}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.CyclotomicTraceSum.trace_sum_formula
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.CyclotomicTraceSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.exp x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.CyclotomicTraceSum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn",
        "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.CyclotomicTraceSum

namespace Reg.D5.S3.Combinatorics.Lattices.CyclotomicTraceSum.EqualDegree

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit
    (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (_ : Unit) (x : ℝ) => Real.log x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (_ : Unit) (x : ℝ) => Real.log x + 1) (fun e => nomatch e)

def law (V : Realization signature) : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] {ι : Type v} [Fintype ι]
    {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} ℚ K]
    (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hcard : Fintype.card ι ≠ 0) (a : ℝ) (hdegree : ∀ i, idealDegree K (I i) = a),
    let N := sumLattice K I
    (EuclideanHarderNarasimhan.slopeData N).Semistable ⊥ ⊤ ∧
      (∀ l : List (EuclideanSublattices.Sublattice N),
        (EuclideanHarderNarasimhan.slopeData N).Filtration ⊥ ⊤ l ↔ l = [⊤]) ∧
      -V.readout () () (EuclideanHarderNarasimhan.covolume N) / finrank ℤ N =
        a / finrank ℚ K - discriminantShift K

abbrev arena : Arena where
  signature := signature
  Law := law.{u,v}

private theorem rejected_fails : ¬ arena.{u,v}.Law rejected := by
  intro law
  let K := ULift.{u} ℚ
  letI : NumberField K := NumberField.of_ringEquiv ℚ K (ULift.ringEquiv.symm : ℚ ≃+* K)
  letI : IsCyclotomicExtension {1} ℚ K :=
    IsCyclotomicExtension.singleton_one_of_algebraMap_bijective
      (by rintro ⟨x⟩; exact ⟨x, rfl⟩)
  let I : ULift.{v} Unit → (FractionalIdeal (𝓞 K)⁰ K)ˣ := fun _ => 1
  have hd : finrank ℚ K = 1 := by
    simpa using IsCyclotomicExtension.Rat.finrank 1 K
  have hcard : Fintype.card (ULift.{v} Unit) ≠ 0 := by simp
  have hdegree : ∀ i, idealDegree K (I i) = idealDegree K 1 := fun _ => rfl
  have h := (law K (n := 1) I
    hcard (idealDegree K 1) hdegree).2.2
  have hg := (equal_degree_sum_hn K (n := 1) I
    hcard (idealDegree K 1) hdegree).2.2
  change -(Real.log (EuclideanHarderNarasimhan.covolume (sumLattice K I)) + 1) /
    finrank ℤ (sumLattice K I) =
      idealDegree K 1 / finrank ℚ K - discriminantShift K at h
  rw [(trace_sum_formula K I).2.2.1, hd] at h hg
  simp only [Fintype.card_ulift, Fintype.card_unit, Nat.mul_one, Nat.cast_one,
    div_one] at h hg
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 1, Real.exp 1, ?_⟩
  change Real.log 1 ≠ Real.log (Real.exp 1)
  simp

private theorem positive : law.{u,v} actual := @equal_degree_sum_hn.{u,v}

def family : Registration arena.{u,v} (type_of% @equal_degree_sum_hn.{u,v}) :=
  @Registration.mk arena.{u,v} (law.{u,v} actual) actual Iff.rfl
    ⟨positive, rejected, rejected_fails⟩
    (_root_.Reg.Support.UniverseSingleReadout.sensitivity
      arena.{u,v}.Law actual rejected rejected_fails) dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@equal_degree_sum_hn.{u,v}) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Combinatorics.Lattices.CyclotomicTraceSum.equal_degree_sum_hn
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Lattices.CyclotomicTraceSum.EqualDegree.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun (_ : Unit) (_ : Unit) (x : ℝ) => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Lattices.CyclotomicTraceSum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg",
        "arg", "fn", "arg", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Lattices.CyclotomicTraceSum.EqualDegree
