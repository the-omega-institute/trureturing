import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
import Reg.Support.SingleDependentReadout


namespace Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Scalar

open _root_.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature := realize signature (fun _ _ x y => x < y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hh : (0 : ℝ) < 1 := by norm_num
  have hf : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) hh
  exact (lt_irrefl _ hf)

abbrev arena_separableThreshold_gt_uniform : Arena where
  signature := signature
  Law R := ∀ {m n : ℕ}, 2 ≤ m → 2 ≤ n →
    R.readout () () (1 / ((m : ℝ)^2)) (separableThreshold m n)

private theorem rejected_separableThreshold_gt_uniform : ¬ arena_separableThreshold_gt_uniform.Law rejected := by
  intro h
  exact @h 2 2 (by decide) (by decide)

def source_separableThreshold_gt_uniform : Registration arena_separableThreshold_gt_uniform (type_of% @separableThreshold_gt_uniform) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@separableThreshold_gt_uniform, rejected, rejected_separableThreshold_gt_uniform⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_separableThreshold_gt_uniform.Law actual rejected rejected_separableThreshold_gt_uniform
  dependence := dependence

def registration_separableThreshold_gt_uniform :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.separableThreshold_gt_uniform)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Scalar.unit_separableThreshold_gt_uniform
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Scalar.source_separableThreshold_gt_uniform
  realizationSource := none
  generated := false
  arena := .source ⟨arena_separableThreshold_gt_uniform⟩
  objectArena := .source ⟨arena_separableThreshold_gt_uniform⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_separableThreshold_gt_uniform ⟨source_separableThreshold_gt_uniform⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_separableThreshold_lt_one : Arena where
  signature := signature
  Law R := ∀ {m n : ℕ}, 2 ≤ m → 2 ≤ n →
    R.readout () () (separableThreshold m n) 1

private theorem rejected_separableThreshold_lt_one : ¬ arena_separableThreshold_lt_one.Law rejected := by
  intro h
  exact @h 2 2 (by decide) (by decide)

def source_separableThreshold_lt_one : Registration arena_separableThreshold_lt_one (type_of% @separableThreshold_lt_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@separableThreshold_lt_one, rejected, rejected_separableThreshold_lt_one⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_separableThreshold_lt_one.Law actual rejected rejected_separableThreshold_lt_one
  dependence := dependence

def registration_separableThreshold_lt_one :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.separableThreshold_lt_one)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Scalar.unit_separableThreshold_lt_one
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Scalar.source_separableThreshold_lt_one
  realizationSource := none
  generated := false
  arena := .source ⟨arena_separableThreshold_lt_one⟩
  objectArena := .source ⟨arena_separableThreshold_lt_one⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_separableThreshold_lt_one ⟨source_separableThreshold_lt_one⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_main_profile_gap : Arena where
  signature := signature
  Law R := ∀ {m n ℓ : ℕ}, 2 ≤ m → m < n → n ≤ m^3 → 2 ≤ ℓ → ℓ ≤ m^2 →
    R.readout () () (schurProfile (m^2) ℓ (separableThreshold m n))
      (schurProfile (m^2) ℓ (1 / Real.sqrt ((m : ℝ) * n)))

private theorem rejected_main_profile_gap : ¬ arena_main_profile_gap.Law rejected := by
  intro h
  exact @h 2 3 2 (by decide) (by decide) (by decide) (by decide) (by decide)

def source_main_profile_gap : Registration arena_main_profile_gap (type_of% @main_profile_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@main_profile_gap, rejected, rejected_main_profile_gap⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_main_profile_gap.Law actual rejected rejected_main_profile_gap
  dependence := dependence

def registration_main_profile_gap :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.main_profile_gap)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Scalar.unit_main_profile_gap
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Scalar.source_main_profile_gap
  realizationSource := none
  generated := false
  arena := .source ⟨arena_main_profile_gap⟩
  objectArena := .source ⟨arena_main_profile_gap⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_main_profile_gap ⟨source_main_profile_gap⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_uniform_profile_gap : Arena where
  signature := signature
  Law R := ∀ {m n ℓ : ℕ}, 2 ≤ m → 2 ≤ n → 2 ≤ ℓ → ℓ ≤ m^2 →
    R.readout () () (schurProfile (m^2) ℓ (separableThreshold m n))
      (schurProfile (m^2) ℓ (1 / ((m : ℝ)^2)))

private theorem rejected_uniform_profile_gap : ¬ arena_uniform_profile_gap.Law rejected := by
  intro h
  exact @h 2 2 2 (by decide) (by decide) (by decide) (by decide)

def source_uniform_profile_gap : Registration arena_uniform_profile_gap (type_of% @uniform_profile_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@uniform_profile_gap, rejected, rejected_uniform_profile_gap⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_uniform_profile_gap.Law actual rejected rejected_uniform_profile_gap
  dependence := dependence

def registration_uniform_profile_gap :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.uniform_profile_gap)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Scalar.unit_uniform_profile_gap
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Scalar.source_uniform_profile_gap
  realizationSource := none
  generated := false
  arena := .source ⟨arena_uniform_profile_gap⟩
  objectArena := .source ⟨arena_uniform_profile_gap⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_uniform_profile_gap ⟨source_uniform_profile_gap⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_exceptional_profile_gap : Arena where
  signature := signature
  Law R := ∀ {m n ℓ : ℕ}, 2 ≤ m → 2 ≤ n → 2 ≤ ℓ → ℓ ≤ m^2 →
    R.readout () () (schurProfile (m^2) ℓ (separableThreshold m n))
      (schurProfile (m^2) ℓ (1 / ((m : ℝ) * Real.sqrt ((m : ℝ)^2 - 1))))

private theorem rejected_exceptional_profile_gap : ¬ arena_exceptional_profile_gap.Law rejected := by
  intro h
  exact @h 2 2 2 (by decide) (by decide) (by decide) (by decide)

def source_exceptional_profile_gap : Registration arena_exceptional_profile_gap (type_of% @exceptional_profile_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exceptional_profile_gap, rejected, rejected_exceptional_profile_gap⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_exceptional_profile_gap.Law actual rejected rejected_exceptional_profile_gap
  dependence := dependence

def registration_exceptional_profile_gap :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.exceptional_profile_gap)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Scalar.unit_exceptional_profile_gap
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Scalar.source_exceptional_profile_gap
  realizationSource := none
  generated := false
  arena := .source ⟨arena_exceptional_profile_gap⟩
  objectArena := .source ⟨arena_exceptional_profile_gap⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_exceptional_profile_gap ⟨source_exceptional_profile_gap⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Scalar

namespace Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.TailBudget

open _root_.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  norm_num at hbad

def actualEq : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private theorem dependenceEq : ObservationalDependence signature actualEq := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hbad : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hbad

abbrev arena_replicate : Arena where
  signature := signature
  Law R := ∀ (N j : ℕ) (a b : ℝ),
    R.readout () () ((a ::ₘ Multiset.replicate N b).esymm (j+1))
      ((N.choose (j+1) : ℝ) * b^(j+1) + (N.choose j : ℝ) * a * b^j)

private theorem rejected_replicate : ¬ arena_replicate.Law rejected := by
  intro h
  exact h 0 0 0 0

def source_replicate : Registration arena_replicate (type_of% @esymm_cons_replicate) where
  actual := actualEq
  bridge := Iff.rfl
  variation := ⟨@esymm_cons_replicate, rejected, rejected_replicate⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_replicate.Law actualEq rejected rejected_replicate
  dependence := dependenceEq

def registration_replicate :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.esymm_cons_replicate)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.TailBudget.unit_replicate
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.TailBudget.source_replicate
  realizationSource := none
  generated := false
  arena := .source ⟨arena_replicate⟩
  objectArena := .source ⟨arena_replicate⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_replicate ⟨source_replicate⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev arena_fin : Arena where
  signature := signature
  Law R := ∀ {k ℓ : ℕ} (hk : 2 ≤ k), 2 ≤ ℓ → ℓ ≤ k →
    ∀ s : Fin k → ℝ, (∀ i, 0 ≤ s i) → (∑ i, s i ≤ 1) →
      ∀ δ : ℝ, 1/(k : ℝ) ≤ δ → δ ≤ 1 →
        (∑ i, s i) - s ⟨0, by omega⟩ ≤ 1-δ →
          R.readout () () (esymmVec ℓ s) (schurProfile k ℓ δ)

private theorem rejected_fin : ¬ arena_fin.Law rejected := by
  intro h
  exact @h 2 2 (by decide) (by decide) (by decide) (fun _ => 0)
    (by intro i; norm_num) (by norm_num [Fin.sum_univ_two]) (1/2)
    (by norm_num) (by norm_num) (by norm_num [Fin.sum_univ_two])

private theorem bridge_fin :
    (type_of% @esymmVec_le_schurProfile_fin) ↔ arena_fin.Law actual := by
  have htail_eq (k : ℕ) (hk : 2 ≤ k) (s : Fin k → ℝ) :
      (∑ i ∈ Finset.univ.filter (fun i : Fin k => 0 < i.val), s i) =
        (∑ i, s i) - s ⟨0, by omega⟩ := by
    let z : Fin k := ⟨0, by omega⟩
    change _ = (∑ i, s i) - s z
    have hset : Finset.univ.filter (fun i : Fin k => 0 < i.val) =
        Finset.univ.erase z := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, and_true]
      constructor
      · intro hi hiz
        have he := congrArg Fin.val hiz
        dsimp [z] at he
        omega
      · intro hi
        by_contra h
        apply hi
        apply Fin.ext
        dsimp [z]
        omega
    rw [hset]
    have he := Finset.sum_erase_add Finset.univ s (Finset.mem_univ z)
    linarith
  constructor
  · intro h k ℓ hk hℓ hℓk s hs0 hs δ hδ hδ1 htail
    apply h hk hℓ hℓk s hs0 hs δ hδ hδ1
    simpa only [htail_eq k hk s] using htail
  · intro h k ℓ hk hℓ hℓk s hs0 hs δ hδ hδ1 htail
    apply h hk hℓ hℓk s hs0 hs δ hδ hδ1
    simpa only [htail_eq k hk s] using htail

def source_fin : Registration arena_fin (type_of% @esymmVec_le_schurProfile_fin) where
  actual := actual
  bridge := bridge_fin
  variation := ⟨bridge_fin.mp @esymmVec_le_schurProfile_fin, rejected, rejected_fin⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena_fin.Law actual rejected rejected_fin
  dependence := dependence

def registration_fin :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.esymmVec_le_schurProfile_fin)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.TailBudget.unit_fin
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.TailBudget.source_fin
  realizationSource := none
  generated := false
  arena := .source ⟨arena_fin⟩
  objectArena := .source ⟨arena_fin⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_fin ⟨source_fin⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.TailBudget

namespace Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Spectrum
noncomputable section
open Matrix
open scoped BigOperators Kronecker MatrixOrder ComplexOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
open _root_.D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)
universe u v
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℂ) (i : Fin (Fintype.card ι)),
    R.readout () () (singularVector A i)
      (Real.sqrt (A.posSemidef_self_mul_conjTranspose.isHermitian.eigenvalues₀ i))
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact @h (ULift.{u} Unit) (ULift.{v} Unit) inferInstance inferInstance
    inferInstance inferInstance 0 ⟨0, by simp⟩
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have ht := congrFun he 0
  norm_num [actual, realize] at ht
def family : Registration arena.{u,v} (type_of% @singularVector_eq_sqrt_rowGram.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@singularVector_eq_sqrt_rowGram, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@singularVector_eq_sqrt_rowGram.{u,v}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Spectrum.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Spectrum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Spectrum

namespace Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Separable
noncomputable section
open Matrix
open scoped BigOperators Kronecker MatrixOrder ComplexOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
open _root_.D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m n ℓ : ℕ}, 2 ≤ m → m < n → 2 ≤ ℓ → ℓ ≤ m ^ 2 →
    ∀ (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ), IsSeparable ρ →
      R.readout () () (esymmSV ℓ (realign ρ))
        (schurProfile (m ^ 2) ℓ (separableThreshold m n))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let σ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun i => if i = 0 then 1 else 0)
  let τ : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i => if i = 0 then 1 else 0)
  have hσ : σ.PosSemidef ∧ σ.trace = 1 := by
    constructor
    · apply Matrix.posSemidef_diagonal_iff.mpr
      intro i
      split_ifs <;> simp
    · simp [σ, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  have hτ : τ.PosSemidef ∧ τ.trace = 1 := by
    constructor
    · apply Matrix.posSemidef_diagonal_iff.mpr
      intro i
      split_ifs <;> simp
    · simp [τ, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  have hsep : IsSeparable (σ ⊗ₖ τ) := by
    refine ⟨1, fun _ => 1, fun _ => σ, fun _ => τ, ?_, ?_, ?_, ?_⟩
    · intro t; norm_num
    · simp
    · intro t; exact ⟨hσ, hτ⟩
    · simp
  exact @h 2 3 2 (by decide) (by decide) (by decide) (by decide) (σ ⊗ₖ τ) hsep
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have ht := congrFun he 0
  norm_num [actual, realize] at ht
def family : Registration arena (type_of% @separable_esymm_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@separable_esymm_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@separable_esymm_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Separable.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Separable.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Quantum.Entanglement.Witness.RealignmentSchurBound.Separable
