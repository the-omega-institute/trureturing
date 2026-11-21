import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Divergence.CoinfiniteExhaustion

open Filter LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Divergence.CoinfiniteExhaustion
open _root_.D5.S3.Entropy.MaxEntropy (shannonEntropy)

noncomputable section

namespace Reg.D5.S3.Divergence.CoinfiniteExhaustion

namespace Limit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℝ)
    (fun _ => Filter ℕ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

def indiscriminate : Realization signature :=
  realize signature (fun _ _ _ _ _ => True) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have hwrong : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) :=
    Eq.mp (congrFun (congrFun he atTop) (𝓝 (0 : ℝ))) hz
  have h : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hwrong
  norm_num at h

end Limit

namespace ExactLoss

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a n : ℕ}, n ≤ a →
    R.readout () () (loss a n)
      (Real.log 2 * ((harmonic a : ℝ) - (harmonic n : ℝ)) -
        (shannonEntropy (pCut a) - shannonEntropy (pCut n)))

private theorem rejected_law : ¬ arena.Law rejected := fun h => @h 0 0 le_rfl

def family : Registration arena (type_of% @loss_exact) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@loss_exact, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro he
    have hh := congrFun he 0
    norm_num [actual, realize] at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@loss_exact) (Realization signature) Unit Unit where
  unitName := `D5.S3.Divergence.CoinfiniteExhaustion.loss_exact.__information_unit
  realizationName := `Reg.D5.S3.Divergence.CoinfiniteExhaustion.ExactLoss.family
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
    owner := `D5.S3.Divergence.CoinfiniteExhaustion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExactLoss

namespace ShannonLimit

open Limit

abbrev arena : Arena where
  signature := signature
  Law R :=
    R.readout () () (fun m => shannonEntropy (pCut m)) atTop
      (𝓝 (∑' i : ℕ, Real.negMulLog (pAtom i)))

private theorem rejected_law : ¬ arena.Law rejected := fun h => h

def family : Registration arena (type_of% @tendsto_cut_shannon) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tendsto_cut_shannon, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tendsto_cut_shannon) (Realization signature) Unit Unit where
  unitName := `D5.S3.Divergence.CoinfiniteExhaustion.tendsto_cut_shannon.__information_unit
  realizationName := `Reg.D5.S3.Divergence.CoinfiniteExhaustion.ShannonLimit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Divergence.CoinfiniteExhaustion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ShannonLimit

namespace ResidualLimit

open Limit

abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ (a : ℕ → ℕ) (_ : ∀ n, n ≤ a n),
      R.readout () () (fun n => loss (a n) n - Real.log 2 * Real.log ((a n : ℝ) / (n : ℝ)))
        atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := fun h => h id (fun _ => le_rfl)

def family : Registration arena (type_of% @tendsto_loss_sub_log_ratio) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tendsto_loss_sub_log_ratio, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tendsto_loss_sub_log_ratio) (Realization signature) Unit Unit where
  unitName := `D5.S3.Divergence.CoinfiniteExhaustion.tendsto_loss_sub_log_ratio.__information_unit
  realizationName := `Reg.D5.S3.Divergence.CoinfiniteExhaustion.ResidualLimit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Divergence.CoinfiniteExhaustion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ResidualLimit

namespace RatioLimit

open Limit

abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ (a : ℕ → ℕ) (_ : ∀ n, n ≤ a n) {R₀ : ℝ},
      Tendsto (fun n => (a n : ℝ) / (n : ℝ)) atTop (𝓝 R₀) →
      R.readout () () (fun n => loss (a n) n) atTop (𝓝 (Real.log 2 * Real.log R₀))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hratio : Tendsto (fun n : ℕ => (id n : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    apply (tendsto_const_nhds (x := (1 : ℝ))).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    exact (div_self hn').symm
  exact h id (fun _ => le_rfl) hratio

def family : Registration arena (type_of% @tendsto_loss_of_ratio) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tendsto_loss_of_ratio, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tendsto_loss_of_ratio) (Realization signature) Unit Unit where
  unitName := `D5.S3.Divergence.CoinfiniteExhaustion.tendsto_loss_of_ratio.__information_unit
  realizationName := `Reg.D5.S3.Divergence.CoinfiniteExhaustion.RatioLimit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Divergence.CoinfiniteExhaustion
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
  options := #[]

end RatioLimit

namespace TwoLimits

open Limit

abbrev arena : Arena where
  signature := signature
  Law R :=
    R.readout () () (fun n => loss n n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => loss (2 * n) n) atTop (𝓝 (Real.log 2 * Real.log 2)) ∧
      0 < Real.log 2 * Real.log 2

private theorem rejected_law : ¬ arena.Law rejected := fun h => h.1

def family : Registration arena (type_of% @nonunique_exhaustion_loss) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nonunique_exhaustion_loss, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nonunique_exhaustion_loss) (Realization signature) Unit Unit where
  unitName := `D5.S3.Divergence.CoinfiniteExhaustion.nonunique_exhaustion_loss.__information_unit
  realizationName := `Reg.D5.S3.Divergence.CoinfiniteExhaustion.TwoLimits.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Divergence.CoinfiniteExhaustion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TwoLimits

namespace NoCommonLimit

open Limit

abbrev arena : Arena where
  signature := signature
  Law R :=
    ¬ ∃ L : ℝ, ∀ a : ℕ → ℕ, Monotone a → (∀ n, n ≤ a n) →
      (∀ n m k, n ≤ m → m ≤ k → ∀ x : Cut (a k),
        partitionMap (n := a n) (partitionMap (n := a m) x) =
          partitionMap (n := a n) x) →
      (∀ n, (∀ x y, 0 ≤ partitionChannel (a n) n x y) ∧
        ∀ x, ∑ y, partitionChannel (a n) n x y = 1) →
      R.readout () () (fun n => loss (a n) n) atTop (𝓝 L)

private theorem rejected_law : ¬ arena.Law indiscriminate := fun h => h ⟨0, fun _ _ _ _ _ => True.intro⟩

def family : Registration arena (type_of% @no_common_exhaustion_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@no_common_exhaustion_limit, indiscriminate, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual indiscriminate rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@no_common_exhaustion_limit) (Realization signature) Unit Unit where
  unitName := `D5.S3.Divergence.CoinfiniteExhaustion.no_common_exhaustion_limit.__information_unit
  realizationName := `Reg.D5.S3.Divergence.CoinfiniteExhaustion.NoCommonLimit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Divergence.CoinfiniteExhaustion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NoCommonLimit

end Reg.D5.S3.Divergence.CoinfiniteExhaustion
