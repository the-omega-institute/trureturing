import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange
import Reg.Support.SingleDependentReadout

/-! Readouts of the exact exchange cardinality and the finite grid lower count. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange
universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def exactCardinality : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def lowerCount : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev exchangeArena : Arena where
  signature := signature
  Law O := ∀ {J : Type u} [Fintype J]
    (base : Finset ℕ) (D R : J → Finset ℕ) (h : J → ℕ)
    (lo hi : J → ℝ) (x : ℝ)
    (hbase : ∀ p ∈ base, Nat.Prime p)
    (hD : ∀ j, D j ⊆ base) (hR : ∀ j, Disjoint (R j) base)
    (hDdisj : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hRdisj : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hprime : ∀ j, ∀ p ∈ R j, Nat.Prime p)
    (hlo : ∀ j, ∀ p ∈ D j, lo j ≤ log (p : ℝ))
    (hhi : ∀ j, ∀ p ∈ R j, log (p : ℝ) ≤ hi j)
    (hx : 0 < x)
    (hslack : (∑ p ∈ base, log (p : ℝ)) + ∑ j, (h j : ℝ) * (hi j - lo j) < log x),
    ∃ outputs : Finset ℕ,
      O.readout () () outputs.card (∏ j, (D j).card.choose (h j) * (R j).card.choose (h j)) ∧
      ∀ n ∈ outputs, 0 < n ∧ Squarefree n ∧ ArithmeticFunction.cardDistinctFactors n =
        base.card ∧ (n : ℝ) < x

private theorem exchange_rejected : ¬ exchangeArena.{u}.Law rejected := by
  intro h
  obtain ⟨_, hfalse, _⟩ := h (J := PEmpty.{u+1}) ∅ (fun j => j.elim) (fun j => j.elim)
    (fun j => j.elim) (fun j => j.elim) (fun j => j.elim) 2 (by simp)
    (fun j => j.elim) (fun j => j.elim) (fun i => i.elim) (fun i => i.elim)
    (fun j => j.elim) (fun j => j.elim) (fun j => j.elim) (by norm_num)
    (by simpa using log_pos (show (1 : ℝ) < 2 by norm_num))
  exact hfalse

def exchangeFamily : Registration exchangeArena.{u} (type_of% @paired_exchange.{u}) where
  actual := exactCardinality
  bridge := Iff.rfl
  variation := ⟨@paired_exchange, rejected, exchange_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    exchangeArena.{u}.Law exactCardinality rejected exchange_rejected
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), 1, ?_⟩
    intro he
    have hh : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
    exact Nat.one_ne_zero hh

abbrev gridArena : Arena where
  signature := signature
  Law O := ∀ {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : StrictMono t)
    (ht0 : t 0 = 0) (P s reserve : ℝ) (hP : 0 < P) (hs : 0 < s)
    (base : Finset ℕ) (h : Fin m → ℕ)
    (hbase : base ⊆ Nat.primesLE ⌊P⌋₊)
    (hdonor : ∀ i, donorBin t P s i ⊆ base)
    (lambda : ℝ) (hsize : threshold lambda (exp P) < (base.card : ℝ))
    (hreserve : (∑ p ∈ base, log (p : ℝ)) ≤ P - reserve)
    (hcost : (2 / s) * (∑ i, t i.succ * (h i : ℝ)) < reserve),
    O.readout () () (∏ i, (donorBin t P s i).card.choose (h i) *
      (recipientBin t P s i).card.choose (h i)) (tailCount lambda (exp P))

private theorem grid_rejected : ¬ gridArena.Law rejected := by
  intro h
  have hlog : log (1 / 2 : ℝ) < 0 := log_neg (by norm_num) (by norm_num)
  have hthreshold : threshold 0 (exp (1 / 2 : ℝ)) < (0 : ℝ) := by
    simpa [threshold, scale, log_exp] using div_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 1 / 2) hlog
  exact h (m := 0) (fun _ => 0) (fun i j hij => by omega)
    rfl (1 / 2) 1 (1 / 4) (by norm_num) (by norm_num) ∅ Fin.elim0 (empty_subset _)
    (fun i => i.elim0) 0 (by simpa using hthreshold) (by norm_num) (by norm_num)

def gridFamily : Registration gridArena (type_of% @fixed_grid_bound) where
  actual := lowerCount
  bridge := Iff.rfl
  variation := ⟨@fixed_grid_bound, rejected, grid_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    gridArena.Law lowerCount rejected grid_rejected
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), 1, ?_⟩
    intro he
    have hh : (1 : ℕ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    exact Nat.not_succ_le_zero _ hh

def exchangeAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@paired_exchange.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange.paired_exchange.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange.exchangeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨exchangeArena⟩
  objectArena := .source ⟨exchangeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exchangeArena ⟨exchangeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature exactCardinality.readout exactCardinality.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "fn", "arg", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def gridAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fixed_grid_bound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange.fixed_grid_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange.gridFamily
  realizationSource := none
  generated := false
  arena := .source ⟨gridArena⟩
  objectArena := .source ⟨gridArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gridArena ⟨gridFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature lowerCount.readout lowerCount.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Exchange
