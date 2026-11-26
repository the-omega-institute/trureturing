import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurements.WeightedLabelRecordDilation
import Reg.Support.DependentFamily

/-! The perfect-readout endpoint observes the pure environment dimension. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurements.FiniteLabelRecordDilation
open _root_.D5.S3.Quantum.Measurements.WeightedLabelRecordDilation
open LeanInformationAudit Matrix
open scoped Classical ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurements.WeightedLabelRecordDilation

universe u v

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ e => e) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun a => nomatch a)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {B : Type u} {J : Type v} [Fintype B] [DecidableEq B] [Fintype J]
    {d e : ℕ} [Nonempty J] (c : B → J) (p : B → ℝ),
    (∀ b, 0 ≤ p b) → (∑ b, p b = 1) → 0 < e →
    ∀ hN : Fintype.card B ≤ d * e,
    (∀ (V : Matrix (Fin d × Fin e) B ℂ) (E : J → Matrix (Fin d) (Fin d) ℂ),
      Vᴴ * V = 1 → (∀ j, (E j).PosSemidef) → (∑ j, E j) = 1 →
        averageSuccess c p V E ≤ optimalSuccess c p hN) ∧
    (∃ (g : B ↪ Fin d × Fin e) (r : Fin d → J),
      let V : Matrix (Fin d × Fin e) B ℂ := fun k b => if k = g b then 1 else 0
      let E (j : J) : Matrix (Fin d) (Fin d) ℂ := diagonal fun m => if r m = j then 1 else 0
      Vᴴ * V = 1 ∧ (∀ j, (E j).PosSemidef) ∧ (∑ j, E j) = 1 ∧
        (∀ i j, E i * E j = if i = j then E i else 0) ∧
        averageSuccess c p V E = optimalSuccess c p hN) ∧
    (optimalSuccess c p hN = 1 ↔
      memorySlots (fun b : {b : B | 0 < p b} => c b.1) (R.readout () () e) ≤ d)

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let B := ULift.{u} (Fin 2)
  let J := ULift.{v} Unit
  let c : B → J := fun _ => ⟨()⟩
  let p : B → ℝ := fun _ => 1 / 2
  have hp : ∀ b, 0 ≤ p b := fun _ => by norm_num [p]
  have hpSum : ∑ b, p b = 1 := by norm_num [p, B]
  let P := {b : B | 0 < p b}
  let label : P → J := fun b => c b.1
  have hFiber : Nat.card {b : P // label b = (⟨()⟩ : J)} = 2 := by
    let e : {b : P // label b = (⟨()⟩ : J)} ≃ B :=
      ⟨fun b => b.1.1, fun b => ⟨⟨b, by norm_num [P, p]⟩, rfl⟩,
        fun _ => rfl, fun _ => rfl⟩
    rw [Nat.card_congr e, Nat.card_eq_fintype_card]
    simp [B]
  have hSlots (e : ℕ) : memorySlots label e = 2 ⌈/⌉ e := by
    unfold memorySlots
    rw [Fintype.sum_unique]
    exact congrArg (· ⌈/⌉ e) hFiber
  have hDim : Fintype.card B ≤ 1 * 2 := by simp [B]
  have hOpt : optimalSuccess c p (d := 1) (e := 2) hDim = 1 :=
    (weightedLabelRecord_optimum c p hp hpSum (by decide) hDim).2.2.mpr
      (by change memorySlots label 2 ≤ 1; rw [hSlots]; decide)
  have hFalse := (h c p hp hpSum (by decide) hDim).2.2.mp hOpt
  change memorySlots label 1 ≤ 1 at hFalse
  rw [hSlots] at hFalse
  exact (by decide : ¬ 2 ⌈/⌉ 1 ≤ 1) hFalse

def family : Registration arena.{u, v} (type_of% @weightedLabelRecord_optimum.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weightedLabelRecord_optimum.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change (1 : ℕ) ≠ 2
    decide

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weightedLabelRecord_optimum.{u, v}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurements.WeightedLabelRecordDilation.audit
  realizationName := `Reg.D5.S3.Quantum.Measurements.WeightedLabelRecordDilation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ e => e) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.WeightedLabelRecordDilation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration


namespace Uniform

private abbrev SampleBasis := ULift.{u} (Fin 2)
private abbrev SampleLabel := ULift.{v} Unit
private abbrev sampleClass : SampleBasis → SampleLabel := fun _ => ⟨()⟩

private theorem sample_card : Fintype.card SampleBasis.{u} = 2 := by simp [SampleBasis]

private theorem sample_classSize (j : SampleLabel.{v}) : classSize sampleClass.{u, v} j = 2 := by
  have hj : (⟨()⟩ : SampleLabel.{v}) = j := Subsingleton.elim _ _
  simp [classSize, hj]

private theorem sample_fullBlockCount : fullBlockCount sampleClass.{u, v} 2 = 1 := by
  simp [fullBlockCount, sample_classSize.{u, v}]

private theorem sample_feasible : Fintype.card SampleBasis.{u} ≤ 1 * 2 := by simp [sample_card.{u}]

private theorem sample_optimum :
    (Fintype.card SampleBasis.{u} : ℝ) *
      optimalSuccess (d := 1) (e := 2) sampleClass.{u, v} (uniformPrior SampleBasis.{u}) sample_feasible.{u} = 2 := by
  rw [uniform_optimalSuccess_eq (d := 1) (e := 2) sampleClass.{u, v} (by decide) sample_feasible.{u},
    sample_fullBlockCount.{u, v}]
  norm_num [largestRemainderSum, sample_classSize.{u, v}]

@[reducible] def exactArena : Arena where
  signature := signature
  Law R := ∀ {B : Type u} {J : Type v} [Fintype B] [DecidableEq B] [Fintype J] {d e : ℕ} [Nonempty B]
    (c : B → J), 0 < e → ∀ hN : Fintype.card B ≤ d * e,
    (Fintype.card B : ℝ) * optimalSuccess c (uniformPrior B) hN =
      (R.readout () () e : ℝ) * fullBlockCount c e +
        largestRemainderSum c e (d - fullBlockCount c e)

private theorem rejected_exact : ¬ exactArena.{u, v}.Law rejected := by
  intro h
  have hBad := h sampleClass.{u, v} (by decide) sample_feasible.{u}
  rw [sample_optimum.{u, v}, sample_fullBlockCount.{u, v}] at hBad
  rw [show rejected.readout () () 2 = 1 from rfl] at hBad
  norm_num [largestRemainderSum, sample_classSize.{u, v}] at hBad

def exactFamily : Registration exactArena.{u, v} (type_of% @uniform_optimalSuccess_eq.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@uniform_optimalSuccess_eq.{u, v}, rejected, rejected_exact⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_exact⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change (1 : ℕ) ≠ 2
    decide

def exactRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@uniform_optimalSuccess_eq.{u, v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurements.WeightedLabelRecordDilation.uniform_optimalSuccess_eq.audit
  realizationName := `Reg.D5.S3.Quantum.Measurements.WeightedLabelRecordDilation.Uniform.exactFamily
  realizationSource := none
  generated := false
  arena := .source ⟨exactArena.{u, v}⟩
  objectArena := .source ⟨exactArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exactArena.{u, v} ⟨exactFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ e => e) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.WeightedLabelRecordDilation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms exactRegistration


@[reducible] def memoryArena : Arena where
  signature := signature
  Law R := ∀ {B : Type u} {J : Type v} [Fintype B] [DecidableEq B] [Fintype J] {d e : ℕ}
    [Nonempty B] (c : B → J), 0 < e →
    ∀ hN : Fintype.card B ≤ d * e, ∀ (α : ℝ) (M : ℕ),
    (∃ S : Finset J, S.card = M ∧ α ≤ classMass c S ∧
      ∀ T : Finset J, α ≤ classMass c T → M ≤ T.card) →
    let Reaches := ∃ (V : Matrix (Fin d × Fin e) B ℂ) (E : J → Matrix (Fin d) (Fin d) ℂ),
      Vᴴ * V = 1 ∧ (∀ j, (E j).PosSemidef) ∧ (∑ j, E j) = 1 ∧
        α ≤ averageSuccess c (uniformPrior B) V E
    (Reaches → max (Fintype.card B ⌈/⌉ R.readout () () e)
      (fullBlockCount c e + M - fullLabelCount c e) ≤ d) ∧
    (max (Fintype.card B ⌈/⌉ e) (fullBlockCount c e + M) ≤ d → Reaches)

set_option maxHeartbeats 800000 in
private theorem rejected_memory : ¬ memoryArena.{u, v}.Law rejected := by
  intro h
  let j : SampleLabel.{v} := ⟨()⟩
  have hCover : ∃ S : Finset SampleLabel.{v}, S.card = 1 ∧ (1 / 2 : ℝ) ≤ classMass sampleClass.{u, v} S ∧
      ∀ T : Finset SampleLabel.{v}, (1 / 2 : ℝ) ≤ classMass sampleClass.{u, v} T → 1 ≤ T.card := by
    refine ⟨{j}, by simp, by norm_num [classMass, sample_classSize.{u, v}, sample_card.{u}], ?_⟩
    intro T hT
    by_contra! hEmpty
    have he : T = ∅ := Finset.card_eq_zero.mp (by omega)
    norm_num [he, classMass] at hT
  have hPrior : ∑ b, uniformPrior SampleBasis.{u} b = 1 := by
    simp [uniformPrior, nsmul_eq_mul]
  have hNonneg : ∀ b, 0 ≤ uniformPrior SampleBasis.{u} b := by
    intro b
    norm_num [uniformPrior, sample_card.{u}]
  obtain ⟨g, r, hV, hE, hSum, _, hScore⟩ :=
    (weightedLabelRecord_optimum (d := 1) (e := 2) sampleClass.{u, v} (uniformPrior SampleBasis.{u})
      hNonneg hPrior (by decide) sample_feasible.{u}).2.1
  have hOpt : (1 / 2 : ℝ) ≤ optimalSuccess (d := 1) (e := 2) sampleClass.{u, v} (uniformPrior SampleBasis.{u}) sample_feasible.{u} := by
    have hs := sample_optimum.{u, v}
    rw [sample_card.{u}, Nat.cast_ofNat] at hs
    linarith only [hs]
  have hBad := (h (d := 1) (e := 2) sampleClass.{u, v} (by decide) sample_feasible.{u} (1 / 2) 1 hCover).1
    ⟨_, _, hV, hE, hSum, hScore ▸ hOpt⟩
  have hFloor : Fintype.card SampleBasis.{u} ⌈/⌉ rejected.readout () () 2 ≤ 1 :=
    (le_max_left _ _).trans hBad
  rw [sample_card.{u}, show rejected.readout () () 2 = 1 from rfl] at hFloor
  exact (by decide : ¬ ((2 : ℕ) ⌈/⌉ 1 ≤ 1)) hFloor

def memoryFamily : Registration memoryArena.{u, v} (type_of% @uniform_record_memory_bounds.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@uniform_record_memory_bounds.{u, v}, rejected, rejected_memory⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_memory⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change (1 : ℕ) ≠ 2
    decide

def memoryRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@uniform_record_memory_bounds.{u, v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurements.WeightedLabelRecordDilation.uniform_record_memory_bounds.audit
  realizationName := `Reg.D5.S3.Quantum.Measurements.WeightedLabelRecordDilation.Uniform.memoryFamily
  realizationSource := none
  generated := false
  arena := .source ⟨memoryArena.{u, v}⟩
  objectArena := .source ⟨memoryArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source memoryArena.{u, v} ⟨memoryFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ e => e) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.WeightedLabelRecordDilation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms memoryRegistration


end Uniform


end Reg.D5.S3.Quantum.Measurements.WeightedLabelRecordDilation
