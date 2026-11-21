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

private theorem different_sequences :
    (fun n : ℕ => loss n n) ≠ (fun n : ℕ => loss (2 * n) n) := by
  intro h
  obtain ⟨hsame, hdouble, hpos⟩ := nonunique_exhaustion_loss
  rw [h] at hsame
  have heq := tendsto_nhds_unique hsame hdouble
  linarith

namespace RatioLimit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℕ) (fun _ => ℕ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ a n => loss (a n) n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : ℕ → ℕ) (_ : ∀ n, n ≤ a n) {L : ℝ},
    Tendsto (fun n => (a n : ℝ) / (n : ℝ)) atTop (𝓝 L) →
    Tendsto (R.readout () () a) atTop (𝓝 (Real.log 2 * Real.log L))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hratio : Tendsto (fun n : ℕ => ((2 * n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 2) := by
    apply (tendsto_const_nhds (x := (2 : ℝ))).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    change (2 : ℝ) = ((2 * n : ℕ) : ℝ) / (n : ℝ)
    apply (eq_div_iff hn').2
    norm_num [Nat.cast_mul]
  have hwrong := h (fun n => 2 * n) (fun n => by omega) hratio
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have heq := tendsto_nhds_unique hz hwrong
  linarith [nonunique_exhaustion_loss.2.2]

def family : Registration arena (type_of% @tendsto_loss_of_ratio) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tendsto_loss_of_ratio, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), id, (fun n => 2 * n), different_sequences⟩

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
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Divergence.CoinfiniteExhaustion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RatioLimit

namespace TwoLimits

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ n => loss (2 * n) n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    Tendsto (fun n : ℕ => loss n n) atTop (𝓝 0) ∧
      Tendsto (R.readout () ()) atTop (𝓝 (Real.log 2 * Real.log 2)) ∧
      0 < Real.log 2 * Real.log 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have heq := tendsto_nhds_unique hz h.2.1
  linarith [h.2.2]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hzero : loss (2 * 0) 0 = 0 := by simp [loss_exact (le_refl 0)]
  by_contra! h
  have hz : Tendsto (fun n : ℕ => loss (2 * n) n) atTop (𝓝 0) := by
    apply (tendsto_const_nhds (x := (0 : ℝ))).congr'
    exact Filter.Eventually.of_forall fun n => hzero.symm.trans (h () 0 n)
  have heq := tendsto_nhds_unique hz nonunique_exhaustion_loss.2.1
  linarith [nonunique_exhaustion_loss.2.2]

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
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Divergence.CoinfiniteExhaustion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TwoLimits

namespace NoCommonLimit

open RatioLimit (signature actual rejected)

abbrev arena : Arena where
  signature := signature
  Law R :=
    ¬ ∃ L : ℝ, ∀ a : ℕ → ℕ, Monotone a → (∀ n, n ≤ a n) →
      (∀ n m k, n ≤ m → m ≤ k → ∀ x : Cut (a k),
        partitionMap (n := a n) (partitionMap (n := a m) x) =
          partitionMap (n := a n) x) →
      (∀ n, (∀ x y, 0 ≤ partitionChannel (a n) n x y) ∧
        ∀ x, ∑ y, partitionChannel (a n) n x y = 1) →
      Tendsto (R.readout () () a) atTop (𝓝 L)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h ⟨0, fun _ _ _ _ _ => tendsto_const_nhds⟩

def family : Registration arena (type_of% @no_common_exhaustion_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@no_common_exhaustion_limit, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), id, (fun n => 2 * n), different_sequences⟩

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
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Divergence.CoinfiniteExhaustion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "body", "body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NoCommonLimit

end Reg.D5.S3.Divergence.CoinfiniteExhaustion
