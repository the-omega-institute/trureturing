import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
import Reg.Support.SingleDependentReadout
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
section
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
universe u
private def emptySystem (J : Type u) : ExchangeSystem J := { base := ∅, neg := fun _ => ∅, pos := fun _ => ∅, base_prime := by simp, neg_subset := by simp, pos_prime := by simp, pos_base := by simp, neg_disjoint := by intro i j hij; simp, pos_disjoint := by intro i j hij; simp }
private def emptyChoices (J : Type u) [Fintype J] [DecidableEq J] : Choices (emptySystem J) (fun _ => 0) := ⟨fun _ => ⟨∅, by simp [emptySystem]⟩, fun _ => ⟨∅, by simp [emptySystem]⟩⟩
namespace Injection
abbrev signature : Signature where
  Params := Σ J : Type u, Σ _ : Fintype J, Σ _ : ExchangeSystem J, J → ℕ
  State p := Choices p.2.2.1 p.2.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ p z => @value p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J] (E : ExchangeSystem J) (h : J → ℕ), Function.Injective (R.readout () ⟨J, ⟨inferInstance, ⟨E, h⟩⟩⟩)
private def witnessSystem : ExchangeSystem PUnit.{u+1} where
  base := {2, 3}
  neg := fun _ => {2, 3}
  pos := fun _ => {5}
  base_prime := by { intro p hp; simp only [mem_insert, mem_singleton] at hp; rcases hp with rfl | rfl <;> norm_num }
  neg_subset := fun _ _ h => h
  pos_prime := by { intro i p hp; simp only [mem_singleton] at hp; subst p; norm_num }
  pos_base := by { intro i; norm_num [Finset.disjoint_left] }
  neg_disjoint := by { intro i j h; exact (h (Subsingleton.elim _ _)).elim }
  pos_disjoint := by { intro i j h; exact (h (Subsingleton.elim _ _)).elim }
private def witnessFirst : Choices witnessSystem.{u} (fun _ => 1) := ⟨fun _ => ⟨{2}, by { apply mem_powersetCard.mpr; constructor <;> simp [witnessSystem] }⟩, fun _ => ⟨{5}, by { apply mem_powersetCard.mpr; constructor <;> simp [witnessSystem] }⟩⟩
private def witnessSecond : Choices witnessSystem.{u} (fun _ => 1) := ⟨fun _ => ⟨{3}, by { apply mem_powersetCard.mpr; constructor <;> simp [witnessSystem] }⟩, fun _ => ⟨{5}, by { apply mem_powersetCard.mpr; constructor <;> simp [witnessSystem] }⟩⟩
private theorem witness_ne : witnessFirst.{u} ≠ witnessSecond.{u} := by
  intro h
  have hh := congrArg (fun z : Choices witnessSystem.{u} (fun _ => 1) => (z.1 PUnit.unit).val) h
  change ({2} : Finset ℕ) = {3} at hh
  have hh' : (2 : ℕ) = 3 := Finset.singleton_inj.mp hh
  norm_num at hh'
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact witness_ne.{u} (h witnessSystem.{u} (fun _ => 1) (a₁ := witnessFirst.{u}) (a₂ := witnessSecond.{u}) rfl)
def family : Registration arena (type_of% @exchange_value_injective.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exchange_value_injective, rejected, rejected_law⟩
  sensitivity := by { constructor; { intro i; refine ⟨rejected, ?_, rfl, rejected_law⟩; intro j hj; exact (hj (Subsingleton.elim _ _)).elim }; { intro e; exact nomatch e } }
  dependence := by
    intro i
    refine ⟨⟨PUnit.{u+1}, ⟨inferInstance, ⟨witnessSystem.{u}, fun _ => 1⟩⟩⟩, witnessFirst.{u}, witnessSecond.{u}, ?_⟩
    intro he
    exact witness_ne.{u} (exchange_value_injective witnessSystem.{u} (fun _ => 1) he)
def audit : Contract.Registration.{_,_,_,0,0,0,u+1,u,0,0,0,0} (@exchange_value_injective.{u}) (Realization signature.{u}) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.exchange_value_injective.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.Injection.family, realizationSource := none, generated := false, arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena.{u} ⟨family.{u}⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature.{u} actual.{u}.readout actual.{u}.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[0, 3, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end Injection
namespace Omega
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J] (E : ExchangeSystem J) (h : J → ℕ) (z : Choices E h), R.readout () () (ArithmeticFunction.cardDistinctFactors (value E h z)) E.base.card }
private theorem rejected_law : ¬ arena.Law rejected := by intro h; exact h (J := PUnit) (emptySystem PUnit) (fun _ => 0) (emptyChoices PUnit)
def family : Registration arena (type_of% @omega_exchange_value.{u}) := { actual := actual, bridge := Iff.rfl, variation := ⟨@omega_exchange_value, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℕ), 1, ?_⟩; intro he; have hh : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl; norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@omega_exchange_value.{u}) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.omega_exchange_value.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.Omega.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end Omega
namespace Card
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J] (E : ExchangeSystem J) (h : J → ℕ), R.readout () () (Fintype.card (Choices E h)) (∏ i, (E.neg i).card.choose (h i) * (E.pos i).card.choose (h i)) }
private theorem rejected_law : ¬ arena.Law rejected := by intro h; exact h (J := PUnit) (emptySystem PUnit) (fun _ => 0)
def family : Registration arena (type_of% @card_exchange_choices.{u}) := { actual := actual, bridge := Iff.rfl, variation := ⟨@card_exchange_choices, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℕ), 1, ?_⟩; intro he; have hh : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl; norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@card_exchange_choices.{u}) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.card_exchange_choices.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.Card.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end Card
namespace LogCost
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J] (E : ExchangeSystem J) (h : J → ℕ) (P D s : ℝ) (t : J → ℝ) (hbase : ∑ p ∈ E.base, log (p : ℝ) ≤ P - D) (hneg : ∀ i p, p ∈ E.neg i → log P - t i / s ≤ log (p : ℝ)) (hpos : ∀ i p, p ∈ E.pos i → log (p : ℝ) ≤ log P + t i / s) (z : Choices E h), R.readout () () (log (value E h z : ℝ)) (P - D + (2 / s) * ∑ i, t i * (h i : ℝ)) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (J := PUnit) (emptySystem PUnit) (fun _ => 0) 0 0 1 (fun _ => 0)
    (by simp [emptySystem]) (by simp [emptySystem]) (by simp [emptySystem])
    (emptyChoices PUnit)
def family : Registration arena (type_of% @log_exchange_value_le.{u}) := { actual := actual, bridge := Iff.rfl, variation := ⟨@log_exchange_value_le, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), 1, ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@log_exchange_value_le.{u}) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.log_exchange_value_le.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.LogCost.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end LogCost
namespace TailBound
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {J : Type u} [Fintype J] [DecidableEq J] (E : ExchangeSystem J) (h : J → ℕ) (P D s : ℝ) (t : J → ℝ) (lambda x : ℝ) (hbase : ∑ p ∈ E.base, log (p : ℝ) ≤ P - D) (hneg : ∀ i p, p ∈ E.neg i → log P - t i / s ≤ log (p : ℝ)) (hpos : ∀ i p, p ∈ E.pos i → log (p : ℝ) ≤ log P + t i / s) (hbudget : (2 / s) * ∑ i, t i * (h i : ℝ) ≤ D) (hthreshold : threshold lambda x < (E.base.card : ℝ)) (hP : P ≤ log x) (hx : 0 < x), R.readout () () (∏ i, (E.neg i).card.choose (h i) * (E.pos i).card.choose (h i)) (tailCount lambda x) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (J := PUnit) (emptySystem PUnit) (fun _ => 0) 0 0 1 (fun _ => 0)
    (-2) (exp (exp 1)) (by simp [emptySystem]) (by simp [emptySystem])
    (by simp [emptySystem]) (by simp)
    (by simp only [emptySystem, card_empty, Nat.cast_zero, threshold, scale, log_exp, div_one]
        have := exp_pos (1 : ℝ)
        linarith)
    (by simpa only [log_exp] using (exp_pos (1 : ℝ)).le) (exp_pos _)
def family : Registration arena (type_of% @balanced_exchange_bound.{u}) := { actual := actual, bridge := Iff.rfl, variation := ⟨@balanced_exchange_bound, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℕ), 1, ?_⟩; intro he; have hh : (1 : ℕ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@balanced_exchange_bound.{u}) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.balanced_exchange_bound.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.TailBound.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end TailBound
namespace LogarithmicBound
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ (n : ℕ) (P s : ℝ) (node : ℕ → ℝ) (Rset : Finset ℕ) (hP : 0 < P) (hs : 0 < s) (hmono : Monotone node) (hzero : node 0 = 0) (hfar : 3 * P / 4 ≤ P * exp (-node n / s)) (hR : Rset ⊆ primeInterval (P / 2) (3 * P / 4)) (h : Fin n → ℕ) (D lambda x : ℝ) (hbase : ∑ p ∈ Nat.primesLE ⌊P⌋₊ \ Rset, log (p : ℝ) ≤ P - D) (hbudget : (2 / s) * ∑ i : Fin n, node (i.val + 1) * (h i : ℝ) ≤ D) (hthreshold : threshold lambda x < ((Nat.primesLE ⌊P⌋₊ \ Rset).card : ℝ)) (hPx : P ≤ log x) (hx : 0 < x), R.readout () () (∏ i : Fin n, (primeInterval (P * exp (-node (i.val + 1) / s)) (P * exp (-node i.val / s))).card.choose (h i) * (primeInterval (P * exp (node i.val / s)) (P * exp (node (i.val + 1) / s))).card.choose (h i)) (tailCount lambda x) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 1 1 (fun _ => 0) ∅ (by norm_num) (by norm_num)
    (fun _ _ _ => le_rfl) rfl (by norm_num) (by simp) (fun _ => 0)
    0 (-2) (exp (exp 1)) (by norm_num) (by simp)
    (by simp only [Nat.floor_one, sdiff_empty, Nat.primesLE_one, card_empty,
          Nat.cast_zero, threshold, scale, log_exp, div_one]
        have := exp_pos (1 : ℝ)
        linarith)
    (by simpa only [log_exp] using (one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)))
    (exp_pos _)
def family : Registration arena (type_of% @logarithmic_exchange_bound) := { actual := actual, bridge := Iff.rfl, variation := ⟨@logarithmic_exchange_bound, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℕ), 1, ?_⟩; intro he; have hh : (1 : ℕ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@logarithmic_exchange_bound) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.logarithmic_exchange_bound.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.LogarithmicBound.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end LogarithmicBound
end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
end
section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.PrimeExpansion
namespace ThreeTerms
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => Filter ℝ → Filter ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := R.readout () () (fun P : ℝ => (primeCount P - countingThreeTerms P) / (P / log P ^ 4)) atTop (𝓝 6) }
private theorem rejected_law : ¬ arena.Law rejected := by exact id
def family : Registration arena (type_of% @prime_counting_three_terms) := { actual := actual, bridge := Iff.rfl, variation := ⟨@prime_counting_three_terms, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (fun x : ℝ => x), (fun _ : ℝ => (0 : ℝ)), ?_⟩; intro he; have hEq := congrFun (congrFun he atTop) atTop; change Tendsto (fun x : ℝ => x) atTop atTop = Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop at hEq; have hId : Tendsto (fun x : ℝ => x) atTop atTop := tendsto_id; have hh : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop := Eq.mp hEq hId; exact not_tendsto_const_atTop (0 : ℝ) atTop hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@prime_counting_three_terms) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.prime_counting_three_terms.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.PrimeExpansion.ThreeTerms.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end ThreeTerms
namespace CountingError
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ᶠ t : ℝ in atTop, R.readout () () (|primeCount t - t / log t|) (3 * (t / log t ^ 2)) }
private theorem rejected_law : ¬ arena.Law rejected := by intro h; obtain ⟨t, ht⟩ := h.exists; exact ht
def family : Registration arena (type_of% @prime_counting_error_bound) := { actual := actual, bridge := Iff.rfl, variation := ⟨@prime_counting_error_bound, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@prime_counting_error_bound) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.prime_counting_error_bound.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.PrimeExpansion.CountingError.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end CountingError
namespace BudgetLimit
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => Filter ℝ → Filter ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := R.readout () () (fun P : ℝ => budget P / (P / log P ^ 2)) atTop (𝓝 2) }
private theorem rejected_law : ¬ arena.Law rejected := by exact id
def family : Registration arena (type_of% @budget_limit) := { actual := actual, bridge := Iff.rfl, variation := ⟨@budget_limit, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (fun x : ℝ => x), (fun _ : ℝ => (0 : ℝ)), ?_⟩; intro he; have hEq := congrFun (congrFun he atTop) atTop; change Tendsto (fun x : ℝ => x) atTop atTop = Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop at hEq; have hId : Tendsto (fun x : ℝ => x) atTop atTop := tendsto_id; have hh : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop := Eq.mp hEq hId; exact not_tendsto_const_atTop (0 : ℝ) atTop hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@budget_limit) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.budget_limit.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.PrimeExpansion.BudgetLimit.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end BudgetLimit
namespace CentralBound
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ᶠ P : ℝ in atTop, ∀ t ∈ Set.Icc (P / 2) (2 * P), R.readout () () (|primeCount t - t / log P|) (28 * (P / log P ^ 2)) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨P, hP, ht⟩ := ((eventually_gt_atTop (0 : ℝ)).and h).exists
  exact ht P ⟨by linarith, by linarith⟩
def family : Registration arena (type_of% @central_prime_counting_bound) := { actual := actual, bridge := Iff.rfl, variation := ⟨@central_prime_counting_bound, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@central_prime_counting_bound) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.central_prime_counting_bound.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.PrimeExpansion.CentralBound.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end CentralBound
end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.PrimeExpansion
end
section
open Filter Real Set Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.MovingWeight
namespace WeightNonneg
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ P s t : ℝ, R.readout () () 0 (weight P s t) }
private theorem rejected_law : ¬ arena.Law rejected := by intro h; exact h 0 0 0
def family : Registration arena (type_of% @weight_nonneg) := { actual := actual, bridge := Iff.rfl, variation := ⟨@weight_nonneg, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@weight_nonneg) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.weight_nonneg.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.MovingWeight.WeightNonneg.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end WeightNonneg
namespace WeightContinuity
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => Set ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ f => ContinuousOn f) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {P s a b : ℝ}, 0 < P → 0 < a → R.readout () () (weight P s) (Set.Icc a b) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 0) (a := 1) (b := 2) (by norm_num) (by norm_num)
def family : Registration arena (type_of% @weight_continuousOn) := { actual := actual, bridge := Iff.rfl, variation := ⟨@weight_continuousOn, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (fun _ : ℝ => 0), Real.log, ?_⟩; intro he; have hc : ContinuousOn Real.log Set.univ := Eq.mp (congrFun he Set.univ) continuousOn_const; have hc0 : ContinuousAt Real.log (0 : ℝ) := (continuousOn_univ.mp hc).continuousAt; exact (Real.continuousAt_log_iff.mp hc0) rfl } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@weight_continuousOn) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.weight_continuousOn.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.MovingWeight.WeightContinuity.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end WeightContinuity
namespace LeftEquals
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {P s t : ℝ}, 0 < P → 0 < t → 0 ≤ s → t ≤ P → R.readout () () (leftWeight P s t) (weight P s t) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 0) (t := 1) (by norm_num) (by norm_num) le_rfl le_rfl
def family : Registration arena (type_of% @leftWeight_eq_weight) := { actual := actual, bridge := Iff.rfl, variation := ⟨@leftWeight_eq_weight, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he (0 : ℝ)) (rfl : (0 : ℝ) = 0); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@leftWeight_eq_weight) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.leftWeight_eq_weight.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.MovingWeight.LeftEquals.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end LeftEquals
namespace RightEquals
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {P s t : ℝ}, 0 < P → 0 < t → 0 ≤ s → P ≤ t → R.readout () () (logWeight s (P ^ s) t) (weight P s t) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 0) (t := 1) (by norm_num) (by norm_num) le_rfl le_rfl
def family : Registration arena (type_of% @rightWeight_eq_weight) := { actual := actual, bridge := Iff.rfl, variation := ⟨@rightWeight_eq_weight, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he (0 : ℝ)) (rfl : (0 : ℝ) = 0); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@rightWeight_eq_weight) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.rightWeight_eq_weight.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.MovingWeight.RightEquals.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end RightEquals
namespace LeftWeightDerivative
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ f => HasDerivAt f) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {P s t : ℝ}, 0 < P → 0 < t → R.readout () () (leftWeight P s) (s / t - abelKernel s (P ^ s) t) t }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 0) (t := 1) (by norm_num) (by norm_num)
def family : Registration arena (type_of% @leftWeight_deriv) := { actual := actual, bridge := Iff.rfl, variation := ⟨@leftWeight_deriv, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (fun _ : ℝ => 0), (fun x : ℝ => x), ?_⟩; intro he; have hh : HasDerivAt (fun x : ℝ => x) 0 0 := Eq.mp (congrFun (congrFun he 0) 0) (hasDerivAt_const 0 (0 : ℝ)); have hzero : (1 : ℝ) = 0 := (hasDerivAt_id 0).unique hh; norm_num at hzero } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@leftWeight_deriv) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.leftWeight_deriv.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.MovingWeight.LeftWeightDerivative.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end LeftWeightDerivative
namespace LeftCutoff
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {P s : ℝ}, 0 < P → R.readout () () (leftWeight P s P) (log 2) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 0) (by norm_num)
def family : Registration arena (type_of% @leftWeight_at_cutoff) := { actual := actual, bridge := Iff.rfl, variation := ⟨@leftWeight_at_cutoff, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he (0 : ℝ)) (rfl : (0 : ℝ) = 0); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@leftWeight_at_cutoff) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.leftWeight_at_cutoff.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.MovingWeight.LeftCutoff.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end LeftCutoff
namespace RightCutoff
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {P s : ℝ}, 0 < P → R.readout () () (logWeight s (P ^ s) P) (log 2) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 0) (by norm_num)
def family : Registration arena (type_of% @rightWeight_at_cutoff) := { actual := actual, bridge := Iff.rfl, variation := ⟨@rightWeight_at_cutoff, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he (0 : ℝ)) (rfl : (0 : ℝ) = 0); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@rightWeight_at_cutoff) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.rightWeight_at_cutoff.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.MovingWeight.RightCutoff.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end RightCutoff
namespace LeftDerivativeNonneg
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {P s t : ℝ}, 0 < P → 0 < t → 0 ≤ s → R.readout () () 0 (s / t - abelKernel s (P ^ s) t) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 0) (t := 1) (by norm_num) (by norm_num) le_rfl
def family : Registration arena (type_of% @leftWeight_deriv_nonneg) := { actual := actual, bridge := Iff.rfl, variation := ⟨@leftWeight_deriv_nonneg, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@leftWeight_deriv_nonneg) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.leftWeight_deriv_nonneg.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.MovingWeight.LeftDerivativeNonneg.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end LeftDerivativeNonneg
namespace PrimeWeightSplit
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {P s x : ℝ}, 0 < P → P ≤ x → 0 ≤ s → R.readout () () (∑ p ∈ Nat.primesLE ⌊x⌋₊, log (1 + P ^ s * (p : ℝ) ^ (-s))) (s * ((Nat.primeCounting ⌊P⌋₊ : ℝ) * log P - Chebyshev.theta P) + remainder P s x) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 0) (x := 1) (by norm_num) le_rfl le_rfl
def family : Registration arena (type_of% @prime_weight_split) := { actual := actual, bridge := Iff.rfl, variation := ⟨@prime_weight_split, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he (0 : ℝ)) (rfl : (0 : ℝ) = 0); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@prime_weight_split) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.prime_weight_split.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.MovingWeight.PrimeWeightSplit.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end PrimeWeightSplit
end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.MovingWeight
end
section
open Filter Real MeasureTheory Set LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.CentralWeight
namespace QuadratureUpper
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {a b C E : ℝ} {f d : ℝ → ℝ}, 0 ≤ a → a ≤ b → 0 ≤ E → ContinuousOn d (Set.Icc a b) → (∀ t ∈ Set.Icc a b, HasDerivAt f (d t) t) → (∀ t ∈ Set.Icc a b, |primeCount t - C * t| ≤ E) → R.readout () () (∑ p ∈ primeInterval a b, f p) (C * (∫ t in a..b, f t) + E * (|f a| + |f b| + ∫ t in a..b, |d t|)) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (a := 0) (b := 0) (C := 0) (E := 0)
    (f := fun _ => 0) (d := fun _ => 0) le_rfl le_rfl le_rfl continuousOn_const
    (fun t _ => by simpa using hasDerivAt_const t (0 : ℝ))
    (by
      intro t ht
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      subst t
      simp [primeCount])
def family : Registration arena (type_of% @prime_quadrature_upper) := { actual := actual, bridge := Iff.rfl, variation := ⟨@prime_quadrature_upper, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@prime_quadrature_upper) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.prime_quadrature_upper.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.CentralWeight.QuadratureUpper.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end QuadratureUpper
namespace CentralPrimeWeight
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ᶠ P : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → R.readout () () (∑ p ∈ primeInterval (P / 2) (2 * P), _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.weight P s p) ((∫ t in (P / 2)..(2 * P), _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.weight P s t) / log P + 112 * log 2 * (P / log P ^ 2)) }
private theorem rejected_law : ¬ arena.Law rejected := by intro h; obtain ⟨P, hP⟩ := h.exists; exact hP 0 le_rfl
def family : Registration arena (type_of% @central_prime_weight_upper) := { actual := actual, bridge := Iff.rfl, variation := ⟨@central_prime_weight_upper, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@central_prime_weight_upper) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.central_prime_weight_upper.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.CentralWeight.CentralPrimeWeight.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end CentralPrimeWeight
end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.CentralWeight
end
section
open Filter Real MeasureTheory Set LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.ContinuumWeight
namespace CentralIntegral
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {P s : ℝ}, 0 < P → 1 < s → R.readout () () (∫ t in (P / 2)..(2 * P), _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.weight P s t) (P * (π / sin (π / s) - s) + (s / 2 + 2) * P * (2 : ℝ) ^ (-s)) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 1) (s := 2) (by norm_num) (by norm_num)
def family : Registration arena (type_of% @central_integral_upper) := { actual := actual, bridge := Iff.rfl, variation := ⟨@central_integral_upper, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@central_integral_upper) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.central_integral_upper.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.ContinuumWeight.CentralIntegral.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end CentralIntegral
end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.ContinuumWeight
end
section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.Grid
namespace Bounds
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ G : Mesh, R.readout () () G.cost (π ^ 2 / 6 + 2 * G.step * log 2) ∧ π ^ 2 / 3 - 2 * (G.U + 2) * exp (-G.U) - 2 * G.step * log 2 ≤ G.mass }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h ⟨1, 1, by norm_num, by norm_num⟩).1
def family : Registration arena (type_of% @grid_bounds) := { actual := actual, bridge := Iff.rfl, variation := ⟨@grid_bounds, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@grid_bounds) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.grid_bounds.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.Grid.Bounds.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "arg", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end Bounds
namespace ExistsGrid
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {η ρ : ℝ}, 0 < η → 0 < ρ → ∃ G : Mesh, R.readout () () G.cost ((π ^ 2 / 6) * (1 + η / 2)) ∧ π ^ 2 / 3 - ρ ≤ G.mass }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨G, hG, _⟩ := h (η := 1) (ρ := 1) (by norm_num) (by norm_num)
  exact hG
def family : Registration arena (type_of% @exists_good_grid) := { actual := actual, bridge := Iff.rfl, variation := ⟨@exists_good_grid, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@exists_good_grid) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.exists_good_grid.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.Grid.ExistsGrid.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end ExistsGrid
namespace StepPositive
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x < y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ G : Mesh, R.readout () () 0 G.step }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h ⟨1,1,by norm_num,by norm_num⟩
def family : Registration arena (type_of% @step_pos) := { actual := actual, bridge := Iff.rfl, variation := ⟨@step_pos, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) < 1 := Eq.mp (congrFun he (1 : ℝ)) (by norm_num : (0 : ℝ) < 1); exact lt_irrefl _ hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@step_pos) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.step_pos.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.Grid.StepPositive.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end StepPositive
namespace NodeStep
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ (G : Mesh) (i : ℕ), R.readout () () (G.node (i+1) - G.node i) G.step }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h ⟨1,1,by norm_num,by norm_num⟩ 0
def family : Registration arena (type_of% @node_step) := { actual := actual, bridge := Iff.rfl, variation := ⟨@node_step, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he (0 : ℝ)) (rfl : (0 : ℝ) = 0); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@node_step) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.node_step.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.Grid.NodeStep.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end NodeStep
namespace NodeEnd
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ G : Mesh, R.readout () () (G.node G.n) G.U }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h ⟨1,1,by norm_num,by norm_num⟩
def family : Registration arena (type_of% @node_end) := { actual := actual, bridge := Iff.rfl, variation := ⟨@node_end, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he (0 : ℝ)) (rfl : (0 : ℝ) = 0); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@node_end) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.node_end.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.Grid.NodeEnd.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end NodeEnd
namespace NodeZero
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ G : Mesh, R.readout () () (G.node 0) 0 }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h ⟨1,1,by norm_num,by norm_num⟩
def family : Registration arena (type_of% @node_zero) := { actual := actual, bridge := Iff.rfl, variation := ⟨@node_zero, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) = 0 := Eq.mp (congrFun he (0 : ℝ)) (rfl : (0 : ℝ) = 0); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@node_zero) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.node_zero.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.Grid.NodeZero.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end NodeZero
end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.Grid
end
section
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
namespace LogChooseGeBinEntropy
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ (m a : ℕ), a ≤ m → R.readout () () ((m : ℝ) * binEntropy ((a : ℝ) / m) - log ((m : ℝ) + 1)) (log (m.choose a : ℝ)) }
private theorem rejected_law : ¬ arena.Law rejected := by intro h; exact h 0 0 le_rfl
def family : Registration arena (type_of% @log_choose_ge_binEntropy) := { actual := actual, bridge := Iff.rfl, variation := ⟨@log_choose_ge_binEntropy, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@log_choose_ge_binEntropy) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.log_choose_ge_binEntropy.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.LogChooseGeBinEntropy.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end LogChooseGeBinEntropy
namespace EntropyLowerScaled
universe u
abbrev signature : Signature := { Params := Type u, State α := α → ℝ, Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance, Output _ α := Filter α → Filter ℝ → Prop, Anchor := Empty, finiteAnchor := inferInstance }
def actual : Realization signature.{u} := realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature.{u}, Law R := ∀ {α : Type u} {l : Filter α} (W : α → ℝ) (n k : α → ℕ) {d q : ℝ}, Tendsto W l atTop → 0 < d → Tendsto (fun x => (n x : ℝ) / W x) l (𝓝 d) → Tendsto (fun x => (k x : ℝ) / W x) l (𝓝 (d * q)) → R.readout () α (fun x => entropyLower (n x) (k x) / W x) l (𝓝 (d * binEntropy q)) }
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact h (α := PUnit.{u+1}) (l := ⊥) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (d := 1) (q := 1/2) tendsto_bot (by norm_num) tendsto_bot tendsto_bot
def family : Registration arena.{u} (type_of% @entropy_lower_scaled.{u}) := { actual := actual, bridge := Iff.rfl, variation := ⟨@entropy_lower_scaled, rejected, rejected_law⟩, sensitivity := by { constructor; { intro i; refine ⟨rejected, ?_, ?_, rejected_law⟩; { intro j h; exact (h (Subsingleton.elim _ _)).elim }; { funext e; exact nomatch e } }; { intro e; exact nomatch e } }, dependence := by { intro i; refine ⟨PUnit.{u+1}, (fun _ => (0 : ℝ)), (fun _ => (1 : ℝ)), ?_⟩; intro he; have hh : Tendsto (fun _ : PUnit.{u+1} => (1 : ℝ)) (pure PUnit.unit) (𝓝 0) := Eq.mp (congrFun (congrFun he (pure PUnit.unit)) (𝓝 (0 : ℝ))) tendsto_const_nhds; have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hh; norm_num at this } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@entropy_lower_scaled.{u}) (Realization signature.{u}) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.entropy_lower_scaled.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.EntropyLowerScaled.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end EntropyLowerScaled
namespace FloorScaled
universe u
abbrev signature : Signature := { Params := Type u, State α := α → ℝ, Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance, Output _ α := Filter α → Filter ℝ → Prop, Anchor := Empty, finiteAnchor := inferInstance }
def actual : Realization signature.{u} := realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature.{u}, Law R := ∀ {α : Type u} {l : Filter α} (W : α → ℝ) (M : α → ℕ) {d q : ℝ}, Tendsto W l atTop → 0 < d → 0 ≤ q → Tendsto (fun x => (M x : ℝ) / W x) l (𝓝 d) → R.readout () α (fun x => (⌊q * (M x : ℝ)⌋₊ : ℝ) / W x) l (𝓝 (q * d)) }
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  exact h (α := PUnit.{u+1}) (l := ⊥) (fun _ => 0) (fun _ => 0)
    (d := 1) (q := 1/2) tendsto_bot (by norm_num) (by norm_num) tendsto_bot
def family : Registration arena.{u} (type_of% @floor_scaled.{u}) := { actual := actual, bridge := Iff.rfl, variation := ⟨@floor_scaled, rejected, rejected_law⟩, sensitivity := by { constructor; { intro i; refine ⟨rejected, ?_, ?_, rejected_law⟩; { intro j h; exact (h (Subsingleton.elim _ _)).elim }; { funext e; exact nomatch e } }; { intro e; exact nomatch e } }, dependence := by { intro i; refine ⟨PUnit.{u+1}, (fun _ => (0 : ℝ)), (fun _ => (1 : ℝ)), ?_⟩; intro he; have hh : Tendsto (fun _ : PUnit.{u+1} => (1 : ℝ)) (pure PUnit.unit) (𝓝 0) := Eq.mp (congrFun (congrFun he (pure PUnit.unit)) (𝓝 (0 : ℝ))) tendsto_const_nhds; have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hh; norm_num at this } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@floor_scaled.{u}) (Realization signature.{u}) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.floor_scaled.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.FloorScaled.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end FloorScaled
namespace MinScaled
universe u
abbrev signature : Signature := { Params := Type u, State α := α → ℝ, Role := Unit, finiteRole := inferInstance, nonemptyRole := inferInstance, Output _ α := Filter α → Filter ℝ → Prop, Anchor := Empty, finiteAnchor := inferInstance }
def actual : Realization signature.{u} := realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature.{u}, Law R := ∀ {α : Type u} {l : Filter α} (W : α → ℝ) (M N : α → ℕ) {d : ℝ}, Tendsto W l atTop → Tendsto (fun x => (M x : ℝ) / W x) l (𝓝 d) → Tendsto (fun x => (N x : ℝ) / W x) l (𝓝 d) → R.readout () α (fun x => ((min (M x) (N x) : ℕ) : ℝ) / W x) l (𝓝 d) }
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by intro h; exact h (α := PUnit.{u+1}) (l := ⊥) (fun _ => 0) (fun _ => 0) (fun _ => 0) (d := 1) tendsto_bot tendsto_bot tendsto_bot
def family : Registration arena.{u} (type_of% @min_scaled.{u}) := { actual := actual, bridge := Iff.rfl, variation := ⟨@min_scaled, rejected, rejected_law⟩, sensitivity := by { constructor; { intro i; refine ⟨rejected, ?_, ?_, rejected_law⟩; { intro j h; exact (h (Subsingleton.elim _ _)).elim }; { funext e; exact nomatch e } }; { intro e; exact nomatch e } }, dependence := by { intro i; refine ⟨PUnit.{u+1}, (fun _ => (0 : ℝ)), (fun _ => (1 : ℝ)), ?_⟩; intro he; have hh : Tendsto (fun _ : PUnit.{u+1} => (1 : ℝ)) (pure PUnit.unit) (𝓝 0) := Eq.mp (congrFun (congrFun he (pure PUnit.unit)) (𝓝 (0 : ℝ))) tendsto_const_nhds; have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hh; norm_num at this } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@min_scaled.{u}) (Realization signature.{u}) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.min_scaled.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.MinScaled.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end MinScaled
end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit
namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit
namespace CorrectionUpper
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {s : ℝ}, π ≤ s → 0 ≤ s * (π / sin (π / s) - s) ∧ R.readout () () (s * (π / sin (π / s) - s)) (correctionMajorant s) }
private theorem rejected_law : ¬ arena.Law rejected := by intro h; exact (h (s := π) le_rfl).2
def family : Registration arena (type_of% @kernel_correction_upper) := { actual := actual, bridge := Iff.rfl, variation := ⟨@kernel_correction_upper, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@kernel_correction_upper) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit.kernel_correction_upper.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit.CorrectionUpper.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "arg", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end CorrectionUpper
namespace MajorantLimit
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => Filter ℝ → Filter ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := R.readout () () correctionMajorant atTop (𝓝 (π ^ 2 / 6)) }
private theorem rejected_law : ¬ arena.Law rejected := by exact id
def family : Registration arena (type_of% @correction_majorant_limit) := { actual := actual, bridge := Iff.rfl, variation := ⟨@correction_majorant_limit, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (fun x : ℝ => x), (fun _ : ℝ => (0 : ℝ)), ?_⟩; intro he; have hEq := congrFun (congrFun he atTop) atTop; change Tendsto (fun x : ℝ => x) atTop atTop = Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop at hEq; have hId : Tendsto (fun x : ℝ => x) atTop atTop := tendsto_id; have hh : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop := Eq.mp hEq hId; exact not_tendsto_const_atTop (0 : ℝ) atTop hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@correction_majorant_limit) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit.correction_majorant_limit.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit.MajorantLimit.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end MajorantLimit
end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail
namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail
namespace FinitePower
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {s : ℝ}, 1 < s → ∀ {N : ℕ}, 0 < N → ∀ S : Finset ℕ, (∀ n ∈ S, N < n) → R.readout () () (∑ n ∈ S, (n : ℝ) ^ (-s)) ((N : ℝ) ^ (1 - s) / (s - 1)) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (s := 2) (by norm_num) (N := 1) (by norm_num) ∅ (by simp)
def family : Registration arena (type_of% @finite_power_tail) := { actual := actual, bridge := Iff.rfl, variation := ⟨@finite_power_tail, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@finite_power_tail) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail.finite_power_tail.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail.FinitePower.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end FinitePower
namespace SmallWeight
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {P s : ℝ}, 2 ≤ P → 0 ≤ s → ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ P / 2) → R.readout () () (∑ n ∈ S, log (1 + exp (-s * |log ((n : ℝ) / P)|))) (P * (1 / 2 : ℝ) ^ s) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 2) (s := 0) le_rfl le_rfl ∅ (by simp)
def family : Registration arena (type_of% @small_weight_tail) := { actual := actual, bridge := Iff.rfl, variation := ⟨@small_weight_tail, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@small_weight_tail) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail.small_weight_tail.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail.SmallWeight.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end SmallWeight
namespace LargeWeight
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {P s : ℝ}, 2 ≤ P → 2 ≤ s → ∀ S : Finset ℕ, (∀ n ∈ S, 2 * P < (n : ℝ)) → R.readout () () (∑ n ∈ S, log (1 + exp (-s * |log ((n : ℝ) / P)|))) (2 * P * (2 / 3 : ℝ) ^ s) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (P := 2) (s := 2) le_rfl le_rfl ∅ (by simp)
def family : Registration arena (type_of% @large_weight_tail) := { actual := actual, bridge := Iff.rfl, variation := ⟨@large_weight_tail, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@large_weight_tail) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail.large_weight_tail.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail.LargeWeight.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end LargeWeight
namespace GeometricDecay
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => Filter ℝ → Filter ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {c q : ℝ}, 0 < c → 0 < q → q < 1 → R.readout () () (fun t : ℝ => t * sqrt t * q ^ (c * sqrt t)) atTop (𝓝 0) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (c := 1) (q := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
def family : Registration arena (type_of% @geometric_sqrt_decay) := { actual := actual, bridge := Iff.rfl, variation := ⟨@geometric_sqrt_decay, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (fun x : ℝ => x), (fun _ : ℝ => (0 : ℝ)), ?_⟩; intro he; have hEq := congrFun (congrFun he atTop) atTop; change Tendsto (fun x : ℝ => x) atTop atTop = Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop at hEq; have hId : Tendsto (fun x : ℝ => x) atTop atTop := tendsto_id; have hh : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop := Eq.mp hEq hId; exact not_tendsto_const_atTop (0 : ℝ) atTop hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@geometric_sqrt_decay) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail.geometric_sqrt_decay.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail.GeometricDecay.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end GeometricDecay
end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail
end
section
open Filter Real LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.MovingEstimate
namespace RemainderMajorant
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ᶠ P : ℝ in atTop, ∀ s : ℝ, π ≤ s → 2 ≤ s → ∀ x : ℝ, R.readout () () (remainder P s x) (majorant P s) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨P, hP⟩ := h.exists
  exact hP (π + 2) (by linarith) (by linarith [pi_pos]) 0
def family : Registration arena (type_of% @remainder_le_majorant) := { actual := actual, bridge := Iff.rfl, variation := ⟨@remainder_le_majorant, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@remainder_le_majorant) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.remainder_le_majorant.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.MovingEstimate.RemainderMajorant.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end RemainderMajorant
namespace MajorantLimit
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => Filter ℝ → Filter ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {c : ℝ}, 0 < c → R.readout () () (fun P : ℝ => majorant P (c * sqrt (log P)) / (P / (log P * sqrt (log P)))) atTop (𝓝 (π ^ 2 / (6 * c))) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (c := 1) (by norm_num)
def family : Registration arena (type_of% @majorant_limit) := { actual := actual, bridge := Iff.rfl, variation := ⟨@majorant_limit, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (fun x : ℝ => x), (fun _ : ℝ => (0 : ℝ)), ?_⟩; intro he; have hEq := congrFun (congrFun he atTop) atTop; change Tendsto (fun x : ℝ => x) atTop atTop = Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop at hEq; have hId : Tendsto (fun x : ℝ => x) atTop atTop := tendsto_id; have hh : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop := Eq.mp hEq hId; exact not_tendsto_const_atTop (0 : ℝ) atTop hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@majorant_limit) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.majorant_limit.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.MovingEstimate.MajorantLimit.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end MajorantLimit
namespace MovingUpper
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {c ε : ℝ}, 0 < c → 0 < ε → ∀ᶠ P : ℝ in atTop, ∀ x : ℝ, R.readout () () (remainder P (c * sqrt (log P)) x) ((π ^ 2 / (6 * c) + ε) * (P / (log P * sqrt (log P)))) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨P, hP⟩ := (h (c := 1) (ε := 1) (by norm_num) (by norm_num)).exists
  exact hP 0
def family : Registration arena (type_of% @moving_weight_upper) := { actual := actual, bridge := Iff.rfl, variation := ⟨@moving_weight_upper, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@moving_weight_upper) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.moving_weight_upper.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.MovingEstimate.MovingUpper.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end MovingUpper
end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.MovingEstimate
end
section
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
open _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Upper
namespace RankinReduction
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ {x s : ℝ}, exp 1 < x → 2 ≤ s → R.readout () () (tailCount 1 x : ℝ) (exp (s * budget (log x) + remainder (log x) s x + eulerCost)) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (x := exp 2) (s := 2) (exp_lt_exp.mpr (by norm_num)) le_rfl
def family : Registration arena (type_of% @rankin_reduction) := { actual := actual, bridge := Iff.rfl, variation := ⟨@rankin_reduction, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@rankin_reduction) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.rankin_reduction.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Upper.RankinReduction.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end RankinReduction
namespace SecondScaleTop
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => Filter ℝ → Filter ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := R.readout () () secondScale atTop atTop }
private theorem rejected_law : ¬ arena.Law rejected := by exact id
def family : Registration arena (type_of% @secondScale_top) := { actual := actual, bridge := Iff.rfl, variation := ⟨@secondScale_top, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (fun x : ℝ => x), (fun _ : ℝ => (0 : ℝ)), ?_⟩; intro he; have hEq := congrFun (congrFun he atTop) atTop; change Tendsto (fun x : ℝ => x) atTop atTop = Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop at hEq; have hId : Tendsto (fun x : ℝ => x) atTop atTop := tendsto_id; have hh : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop := Eq.mp hEq hId; exact not_tendsto_const_atTop (0 : ℝ) atTop hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@secondScale_top) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.secondScale_top.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Upper.SecondScaleTop.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end SecondScaleTop
namespace SaddleBudgetLimit
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => Filter ℝ → Filter ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := R.readout () () (fun P : ℝ => saddle P * budget P / (P / (log P * sqrt (log P)))) atTop (𝓝 (π / sqrt 3)) }
private theorem rejected_law : ¬ arena.Law rejected := by exact id
def family : Registration arena (type_of% @saddle_budget_limit) := { actual := actual, bridge := Iff.rfl, variation := ⟨@saddle_budget_limit, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (fun x : ℝ => x), (fun _ : ℝ => (0 : ℝ)), ?_⟩; intro he; have hEq := congrFun (congrFun he atTop) atTop; change Tendsto (fun x : ℝ => x) atTop atTop = Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop at hEq; have hId : Tendsto (fun x : ℝ => x) atTop atTop := tendsto_id; have hh : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop atTop := Eq.mp hEq hId; exact not_tendsto_const_atTop (0 : ℝ) atTop hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@saddle_budget_limit) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.saddle_budget_limit.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Upper.SaddleBudgetLimit.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end SaddleBudgetLimit
namespace Result
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, R.readout () () (tailCount 1 x : ℝ) (exp ((2 * π / sqrt 3 + ε) * log x / (log (log x)) ^ (3 / 2 : ℝ))) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x, hx⟩ := (h 1 (by norm_num)).exists
  exact hx
def family : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.upper) := { actual := actual, bridge := Iff.rfl, variation := ⟨@_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.upper, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he (0 : ℝ)) (le_refl (0 : ℝ)); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.upper) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.upper.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Upper.Result.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end Result
namespace EnoughPrimes
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ᶠ P : ℝ in atTop, R.readout () () (thresholdK P) (Nat.primeCounting ⌊P⌋₊) }
private theorem rejected_law : ¬ arena.Law rejected := by intro h; obtain ⟨P, hP⟩ := h.exists; exact hP
def family : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.thresholdK_le_primeCount) := { actual := actual, bridge := Iff.rfl, variation := ⟨@_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.thresholdK_le_primeCount, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℕ), 1, ?_⟩; intro he; have hh : (1 : ℕ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.thresholdK_le_primeCount) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.thresholdK_le_primeCount.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Upper.EnoughPrimes.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end EnoughPrimes
namespace Excess
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => Filter ℝ → Filter ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := R.readout () () (fun P : ℝ => (excess P : ℝ) / (P / log P ^ 3)) atTop (𝓝 (2 : ℝ)) }
private theorem rejected_law : ¬ arena.Law rejected := by exact id
def family : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.excess_limit) := { actual := actual, bridge := Iff.rfl, variation := ⟨@_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.excess_limit, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (fun _ : ℝ => 0), (fun _ : ℝ => 1), ?_⟩; intro he; have hh : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) := Eq.mp (congrFun (congrFun he atTop) (𝓝 (0 : ℝ))) tendsto_const_nhds; have hzero : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hh; norm_num at hzero } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.excess_limit) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.excess_limit.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Upper.Excess.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end Excess
namespace CoreBudget
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => Filter ℝ → Filter ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := R.readout () () (fun P : ℝ => coreBudget P / (P / log P ^ 2)) atTop (𝓝 (2 : ℝ)) }
private theorem rejected_law : ¬ arena.Law rejected := by exact id
def family : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.coreBudget_limit) := { actual := actual, bridge := Iff.rfl, variation := ⟨@_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.coreBudget_limit, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (fun _ : ℝ => 0), (fun _ : ℝ => 1), ?_⟩; intro he; have hh : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) := Eq.mp (congrFun (congrFun he atTop) (𝓝 (0 : ℝ))) tendsto_const_nhds; have hzero : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hh; norm_num at hzero } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.coreBudget_limit) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.coreBudget_limit.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Upper.CoreBudget.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end CoreBudget
namespace ExactLimit
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => Filter ℝ → Filter ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := R.readout () () (fun x : ℝ => log (tailCount 1 x : ℝ) / (log x / (log (log x)) ^ (3 / 2 : ℝ))) atTop (𝓝 (2 * π / sqrt 3)) }
private theorem rejected_law : ¬ arena.Law rejected := by exact id
def family : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.result) := { actual := actual, bridge := Iff.rfl, variation := ⟨@_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.result, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (fun _ : ℝ => 0), (fun _ : ℝ => 1), ?_⟩; intro he; have hh : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) := Eq.mp (congrFun (congrFun he atTop) (𝓝 (0 : ℝ))) tendsto_const_nhds; have hzero : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hh; norm_num at hzero } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.result) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.result.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Upper.ExactLimit.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end ExactLimit
namespace FixedGrid
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ (ε : ℝ) (hε : 0 < ε), ∃ c : ℝ, 0 < c ∧ ∃ G : _root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange.Mesh, ∀ᶠ P : ℝ in atTop, exchangeCost G c P ≤ coreBudget P ∧ R.readout () () ((2 * π / sqrt 3 - ε) * (P / (log P * sqrt (log P)))) (log (∏ i : Fin G.n, ((capacity G c P i).choose (occupancy G c P i)) ^ 2 : ℕ)) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c, hc, G, hG⟩ := h 1 (by norm_num)
  obtain ⟨P, hP⟩ := hG.exists
  exact hP.2
def family : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.fixed_grid_exists) := { actual := actual, bridge := Iff.rfl, variation := ⟨@_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.fixed_grid_exists, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), 1, ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.fixed_grid_exists) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.fixed_grid_exists.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Upper.FixedGrid.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "arg", "body", "arg", "arg", "body", "fn", "arg", "body", "arg", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end FixedGrid
namespace Lower
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena := { signature := signature, Law R := ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, R.readout () () ((2 * π / sqrt 3 - ε) * log x / (log (log x)) ^ (3 / 2 : ℝ)) (log (tailCount 1 x : ℝ)) }
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x, hx⟩ := (h 1 (by norm_num)).exists
  exact hx
def family : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.lower) := { actual := actual, bridge := Iff.rfl, variation := ⟨@_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.lower, rejected, rejected_law⟩, sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law, dependence := by { intro i; refine ⟨(), (0 : ℝ), 1, ?_⟩; intro he; have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0); norm_num at hh } }
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.lower) (Realization signature) Type Unit := { unitName := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.lower.audit, realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Upper.Lower.family, realizationSource := none, generated := false, arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩, catalog := Lean.Name.anonymous, localNames := false, realization := .source arena ⟨family⟩, correspondence := { stage := .evidence, objectStage := .evidence }, bundleNonempty := .absent, readout := some (realize signature actual.readout actual.anchor), variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none, sourceSelection := some { owner := `D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg", "body", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }, continuation := .unknown, familyRecord := none, options := #[] }
end Lower
end Reg.D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Upper
end
