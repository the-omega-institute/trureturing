import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.LogPowerExchange
import Reg.Support.SingleDependentReadout

/-! The entropy inequality of the constructed signed-prime family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.LogPowerExchange

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.LogPowerExchange

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def lowerBound : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev entropyArena : Arena where
  signature := signature
  Law O := ∀ {m : ℕ} (t : Fin (m + 1) → ℝ) (_ht : StrictMono t)
    (_ht0 : t 0 = 0) (q : Fin m → ℝ) (_hq0 : ∀ i, 0 < q i) (_hq1 : ∀ i, q i < 1)
    (C a : ℝ) (_hC : 0 < C) (_ha : 0 < a)
    (base : ℝ → Finset ℕ) (reserve : ℝ → ℝ) (B zeta : ℝ) (_hzeta : 0 < zeta),
    let s := fun P : ℝ => C * log P ^ a
    let W := fun P : ℝ => (P / log P) / s P
    let delta := fun i : Fin m => t i.succ - t i.castSucc
    (2 * ∑ i, t i.succ * (delta i * q i) < B) →
    (∀ i, Tendsto (fun P => ((donorBin t P (s P) i).card : ℝ) / W P) atTop (𝓝 (delta i))) →
    (∀ i, Tendsto (fun P => ((recipientBin t P (s P) i).card : ℝ) / W P) atTop (𝓝 (delta i))) →
    Tendsto (fun P => reserve P / (W P / s P)) atTop (𝓝 B) →
    (∀ᶠ P in atTop, base P ⊆ Nat.primesLE ⌊P⌋₊ ∧
      (∀ i, donorBin t P (s P) i ⊆ base P) ∧
      (∑ p ∈ base P, log (p : ℝ)) ≤ P - reserve P) →
    ∀ᶠ P in atTop,
      let h := fun i => ⌊q i * (min (donorBin t P (s P) i).card
        (recipientBin t P (s P) i).card : ℕ)⌋₊
      let outputs := pairedOutputs (base P) (donorBin t P (s P)) (recipientBin t P (s P)) h
      outputs.card = (∏ i, (donorBin t P (s P) i).card.choose (h i) *
        (recipientBin t P (s P) i).card.choose (h i)) ∧
      0 < outputs.card ∧
      (∀ n ∈ outputs, 0 < n ∧ Squarefree n ∧ ArithmeticFunction.cardDistinctFactors n =
        (base P).card ∧ (n : ℝ) < exp P) ∧
      O.readout () () ((2 * ∑ i, delta i * binEntropy (q i) - zeta) * W P)
        (log (outputs.card : ℝ))

private theorem entropy_rejected : ¬ entropyArena.Law rejected := by
  intro h
  let reserve (P : ℝ) := (P / log P) / log P / log P
  have hreserve : Tendsto (fun P : ℝ =>
      reserve P / (((P / log P) / (1 * log P ^ (1 : ℝ))) / (1 * log P ^ (1 : ℝ))))
      atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    have hl := log_pos hP
    have hpos := div_pos (div_pos (div_pos (zero_lt_one.trans hP) hl) hl) hl
    simpa only [rpow_one, one_mul, reserve] using (div_self hpos.ne').symm
  have hbase : ∀ᶠ P : ℝ in atTop, (∅ : Finset ℕ) ⊆ Nat.primesLE ⌊P⌋₊ ∧
      (∀ i : Fin 0, donorBin (fun _ => 0) P (1 * log P ^ (1 : ℝ)) i ⊆ ∅) ∧
      (∑ p ∈ (∅ : Finset ℕ), log (p : ℝ)) ≤ P - reserve P := by
    filter_upwards [eventually_ge_atTop (exp 1)] with P hP
    have hpos := (exp_pos 1).trans_le hP
    have hlog : 1 ≤ log P := (le_log_iff_exp_le hpos).mpr hP
    have hl := zero_le_one.trans hlog
    have hdiv := div_le_self hpos.le hlog
    have hdiv' := div_le_self (div_nonneg hpos.le hl) hlog
    have hdiv'' := div_le_self (div_nonneg (div_nonneg hpos.le hl) hl) hlog
    exact ⟨empty_subset _, fun i => i.elim0,
      by simpa [sum_empty, sub_nonneg, reserve] using hdiv''.trans (hdiv'.trans hdiv)⟩
  have he := h (m := 0) (fun _ => 0) (fun i j hij => by omega) rfl Fin.elim0
    (fun i => i.elim0) (fun i => i.elim0) 1 1 (by norm_num) (by norm_num)
    (fun _ => ∅) reserve 1 1 (by norm_num) (by norm_num)
    (fun i => i.elim0) (fun i => i.elim0) hreserve hbase
  obtain ⟨_, _, _, _, hfalse⟩ := he.exists
  exact hfalse

def entropyFamily : Registration entropyArena (type_of% @log_power_grid_lower) where
  actual := lowerBound
  bridge := Iff.rfl
  variation := ⟨@log_power_grid_lower, rejected, entropy_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    entropyArena.Law lowerBound rejected entropy_rejected
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

def entropyAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@log_power_grid_lower) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.LogPowerExchange.log_power_grid_lower.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.LogPowerExchange.entropyFamily
  realizationSource := none
  generated := false
  arena := .source ⟨entropyArena⟩
  objectArena := .source ⟨entropyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source entropyArena ⟨entropyFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature lowerBound.readout lowerBound.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.LogPowerExchange
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "body", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.LogPowerExchange
