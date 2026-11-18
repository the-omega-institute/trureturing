import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real Finset LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy

namespace LogChooseGeBinEntropy

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m a : ℕ), a ≤ m →
    R.readout () () ((m : ℝ) * binEntropy ((a : ℝ) / m) - log ((m : ℝ) + 1))
      (log (m.choose a : ℝ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 le_rfl

def family : Registration arena (type_of% @log_choose_ge_binEntropy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@log_choose_ge_binEntropy, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@log_choose_ge_binEntropy) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.log_choose_ge_binEntropy.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.LogChooseGeBinEntropy.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LogChooseGeBinEntropy

namespace EntropyLowerScaled

universe u

abbrev signature : Signature where
  Params := Type u
  State α := α → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ α := Filter α → Filter ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} {l : Filter α} (W : α → ℝ) (n k : α → ℕ)
    {d q : ℝ}, Tendsto W l atTop → 0 < d →
    Tendsto (fun x => (n x : ℝ) / W x) l (𝓝 d) →
    Tendsto (fun x => (k x : ℝ) / W x) l (𝓝 (d * q)) →
    R.readout () α (fun x => entropyLower (n x) (k x) / W x) l
      (𝓝 (d * binEntropy q))

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact h (α := PUnit.{u+1}) (l := ⊥) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (d := 1) (q := 1/2) tendsto_bot (by norm_num) tendsto_bot tendsto_bot

def family : Registration arena.{u} (type_of% @entropy_lower_scaled.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@entropy_lower_scaled, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨PUnit.{u+1}, (fun _ => (0 : ℝ)), (fun _ => (1 : ℝ)), ?_⟩
    intro he
    have hh : Tendsto (fun _ : PUnit.{u+1} => (1 : ℝ)) (pure PUnit.unit) (𝓝 0) :=
      Eq.mp (congrFun (congrFun he (pure PUnit.unit)) (𝓝 (0 : ℝ))) tendsto_const_nhds
    have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hh
    norm_num at this

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@entropy_lower_scaled.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.entropy_lower_scaled.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.EntropyLowerScaled.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end EntropyLowerScaled

namespace FloorScaled

universe u

abbrev signature : Signature where
  Params := Type u
  State α := α → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ α := Filter α → Filter ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} {l : Filter α} (W : α → ℝ) (M : α → ℕ)
    {d q : ℝ}, Tendsto W l atTop → 0 < d → 0 ≤ q →
    Tendsto (fun x => (M x : ℝ) / W x) l (𝓝 d) →
    R.readout () α (fun x => (⌊q * (M x : ℝ)⌋₊ : ℝ) / W x) l (𝓝 (q * d))

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact h (α := PUnit.{u+1}) (l := ⊥) (fun _ => 0) (fun _ => 0)
    (d := 1) (q := 1/2) tendsto_bot (by norm_num) (by norm_num) tendsto_bot

def family : Registration arena.{u} (type_of% @floor_scaled.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@floor_scaled, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨PUnit.{u+1}, (fun _ => (0 : ℝ)), (fun _ => (1 : ℝ)), ?_⟩
    intro he
    have hh : Tendsto (fun _ : PUnit.{u+1} => (1 : ℝ)) (pure PUnit.unit) (𝓝 0) :=
      Eq.mp (congrFun (congrFun he (pure PUnit.unit)) (𝓝 (0 : ℝ))) tendsto_const_nhds
    have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hh
    norm_num at this

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@floor_scaled.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.floor_scaled.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.FloorScaled.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end FloorScaled

namespace MinScaled

universe u

abbrev signature : Signature where
  Params := Type u
  State α := α → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ α := Filter α → Filter ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} {l : Filter α} (W : α → ℝ) (M N : α → ℕ)
    {d : ℝ}, Tendsto W l atTop →
    Tendsto (fun x => (M x : ℝ) / W x) l (𝓝 d) →
    Tendsto (fun x => (N x : ℝ) / W x) l (𝓝 d) →
    R.readout () α (fun x => (min (M x) (N x) : ℝ) / W x) l (𝓝 d)

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact h (α := PUnit.{u+1}) (l := ⊥) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (d := 1) tendsto_bot tendsto_bot tendsto_bot

def family : Registration arena.{u} (type_of% @min_scaled.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@min_scaled, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨PUnit.{u+1}, (fun _ => (0 : ℝ)), (fun _ => (1 : ℝ)), ?_⟩
    intro he
    have hh : Tendsto (fun _ : PUnit.{u+1} => (1 : ℝ)) (pure PUnit.unit) (𝓝 0) :=
      Eq.mp (congrFun (congrFun he (pure PUnit.unit)) (𝓝 (0 : ℝ))) tendsto_const_nhds
    have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hh
    norm_num at this

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@min_scaled.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.min_scaled.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.MinScaled.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end MinScaled

end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy

open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit

namespace CorrectionUpper

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℝ}, π ≤ s →
    0 ≤ s * (π / sin (π / s) - s) ∧
      R.readout () () (s * (π / sin (π / s) - s)) (correctionMajorant s)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (s := π) le_rfl).2

def family : Registration arena (type_of% @kernel_correction_upper) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kernel_correction_upper, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kernel_correction_upper) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit.kernel_correction_upper.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit.CorrectionUpper.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CorrectionUpper

namespace MajorantLimit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () correctionMajorant atTop (𝓝 (π ^ 2 / 6))

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena (type_of% @correction_majorant_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@correction_majorant_limit, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun x : ℝ => x), (fun _ : ℝ => (0 : ℝ)), ?_⟩
    intro he
    have hEq := congrFun (congrFun he atTop) atTop
    change Tendsto (fun x : ℝ => x) atTop atTop =
      Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop at hEq
    have hId : Tendsto (fun x : ℝ => x) atTop atTop := tendsto_id
    have hh : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop := Eq.mp hEq hId
    exact not_tendsto_const_atTop (0 : ℝ) atTop hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@correction_majorant_limit) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit.correction_majorant_limit.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit.MajorantLimit.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MajorantLimit

end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit

open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail

namespace FinitePower

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℝ}, 1 < s → ∀ {N : ℕ}, 0 < N →
    ∀ S : Finset ℕ, (∀ n ∈ S, N < n) →
    R.readout () () (∑ n ∈ S, (n : ℝ) ^ (-s)) ((N : ℝ) ^ (1 - s) / (s - 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (s := 2) (by norm_num) (N := 1) (by norm_num) ∅ (by simp)

def family : Registration arena (type_of% @finite_power_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_power_tail, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_power_tail) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail.finite_power_tail.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail.FinitePower.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FinitePower

namespace SmallWeight

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P s : ℝ}, 2 ≤ P → 0 ≤ s →
    ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ P / 2) →
    R.readout () () (∑ n ∈ S, log (1 + exp (-s * |log ((n : ℝ) / P)|)))
      (P * (1 / 2 : ℝ) ^ s)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 2) (s := 0) le_rfl le_rfl ∅ (by simp)

def family : Registration arena (type_of% @small_weight_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@small_weight_tail, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@small_weight_tail) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail.small_weight_tail.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail.SmallWeight.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SmallWeight

namespace LargeWeight

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P s : ℝ}, 2 ≤ P → 2 ≤ s →
    ∀ S : Finset ℕ, (∀ n ∈ S, 2 * P < (n : ℝ)) →
    R.readout () () (∑ n ∈ S, log (1 + exp (-s * |log ((n : ℝ) / P)|)))
      (2 * P * (2 / 3 : ℝ) ^ s)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 2) (s := 2) le_rfl le_rfl ∅ (by simp)

def family : Registration arena (type_of% @large_weight_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@large_weight_tail, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ))
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@large_weight_tail) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail.large_weight_tail.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail.LargeWeight.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LargeWeight

namespace GeometricDecay

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Filter ℝ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {c q : ℝ}, 0 < c → 0 < q → q < 1 →
    R.readout () () (fun t : ℝ => t * sqrt t * q ^ (c * sqrt t)) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (c := 1) (q := 1 / 2) (by norm_num) (by norm_num) (by norm_num)

def family : Registration arena (type_of% @geometric_sqrt_decay) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@geometric_sqrt_decay, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun x : ℝ => x), (fun _ : ℝ => (0 : ℝ)), ?_⟩
    intro he
    have hEq := congrFun (congrFun he atTop) atTop
    change Tendsto (fun x : ℝ => x) atTop atTop =
      Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop at hEq
    have hId : Tendsto (fun x : ℝ => x) atTop atTop := tendsto_id
    have hh : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop := Eq.mp hEq hId
    exact not_tendsto_const_atTop (0 : ℝ) atTop hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@geometric_sqrt_decay) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail.geometric_sqrt_decay.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail.GeometricDecay.family
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
    owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GeometricDecay

end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail
