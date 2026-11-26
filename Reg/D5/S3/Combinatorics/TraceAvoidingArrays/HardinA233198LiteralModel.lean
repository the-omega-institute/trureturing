import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Whole-family readouts of the literal complementary-pair fibre counts. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

attribute [local irreducible] a fibreCount

private def alternating (v : Cell 1) : Fin 4 := if v.2.val % 2 = 0 then 0 else 1

private theorem alternating_legal : PairLegal alternating := by
  refine ⟨⟨by decide, rfl⟩, ?_, ?_⟩
  · unfold PairNormal alternating rank
    decide
  · unfold Edge alternating
    decide

private theorem constant_fibre_zero : fibreCount (fun _ : Cell 1 => 0) = 0 := by
  haveI : IsEmpty {f : Cell 1 → Fin 8 //
      Legal f ∧ (fun v => pair (f v)) = (fun _ => 0)} := ⟨by
    rintro ⟨f, hf, hp⟩
    have he := hf.2.2 (0, 0) (0, 1) (Or.inl ⟨rfl, rfl⟩)
    have hx : pair (f (0, 0)) = 0 := congrFun hp (0, 0)
    have hy : pair (f (0, 1)) = 0 := congrFun hp (0, 1)
    have hbad : ∀ x y : Fin 8, pair x = 0 → pair y = 0 → ¬ Bond x y := by
      unfold pair Bond
      decide
    exact hbad _ _ hx hy he⟩
  unfold fibreCount
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

abbrev fibreSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Cell n → Fin 4) (fun _ => ℕ)

def fibreActual : Realization fibreSignature :=
  realize fibreSignature (fun _ _ p => fibreCount p) (fun e => nomatch e)

def fibreRejected : Realization fibreSignature :=
  realize fibreSignature (fun _ _ p => fibreCount p + 1) (fun e => nomatch e)

private theorem fibreDependence : ObservationalDependence fibreSignature fibreActual := by
  intro i
  refine ⟨1, alternating, (fun _ => 0), ?_⟩
  change fibreCount alternating ≠ fibreCount (fun _ : Cell 1 => 0)
  rw [literal_fibre_card alternating_legal, constant_fibre_zero]
  exact (pow_pos (by decide : 0 < (2 : ℕ)) _).ne'

namespace FibreCard

abbrev arena : Arena where
  signature := fibreSignature
  Law R := ∀ {n} {p : Cell n → Fin 4}, PairLegal p →
    R.readout () n p = 2 ^ Nat.card (Free p)

private theorem rejected_law : ¬ arena.Law fibreRejected := by
  intro h
  have hb := h alternating_legal
  have ha := literal_fibre_card alternating_legal
  change fibreCount alternating + 1 = 2 ^ Nat.card (Free alternating) at hb
  omega

def family : Registration arena (type_of% @literal_fibre_card) where
  actual := fibreActual
  bridge := Iff.rfl
  variation := ⟨@literal_fibre_card, fibreRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law fibreActual fibreRejected rejected_law
  dependence := fibreDependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@literal_fibre_card) (Realization fibreSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.FibreCard.unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.FibreCard.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fibreSignature (fun _ _ p => fibreCount p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198LiteralModel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FibreCard

namespace FibrePower

abbrev arena : Arena where
  signature := fibreSignature
  Law R := ∀ {n} {p : Cell n → Fin 4}, PairLegal p →
    R.readout () n p = 2 ^ (4 * n - Nat.card (Set.range p))

private theorem rejected_law : ¬ arena.Law fibreRejected := by
  intro h
  have hb := h alternating_legal
  have ha := literal_fibre_power alternating_legal
  change fibreCount alternating = 2 ^ (4 - Nat.card (Set.range alternating)) at ha
  change fibreCount alternating + 1 = 2 ^ (4 - Nat.card (Set.range alternating)) at hb
  omega

def family : Registration arena (type_of% @literal_fibre_power) where
  actual := fibreActual
  bridge := Iff.rfl
  variation := ⟨@literal_fibre_power, fibreRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law fibreActual fibreRejected rejected_law
  dependence := fibreDependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@literal_fibre_power) (Realization fibreSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.FibrePower.unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.FibrePower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fibreSignature (fun _ _ p => fibreCount p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198LiteralModel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FibrePower

namespace LiteralCount

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

attribute [local instance] Classical.propDecidable

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n, R.readout () () n = ∑ p : {p : Cell n → Fin 4 // PairLegal p},
    2 ^ (4 * n - Nat.card (Set.range p.1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  have ha := literal_count_by_pairs 0
  change a 0 + 1 = _ at hb
  omega

private theorem zero_count : a 0 = 0 := by
  unfold a
  apply Nat.card_eq_zero.mpr
  left
  exact ⟨fun f => by obtain ⟨h, _⟩ := f.2.1; omega⟩

theorem positive_one : 0 < a 1 := by
  let f : Cell 1 → Fin 8 := fun v => if v.2.val % 2 = 0 then 0 else 1
  have hf : Legal f := by
    refine ⟨⟨by omega, rfl⟩, ?_, ?_⟩
    · intro v
      have hb : (f v).val = 0 ∨ (f v).val = 1 := by
        dsimp [f]
        split_ifs <;> simp
      refine ⟨?_, ?_, ?_⟩
      · intro h; omega
      · intro h; rcases h with h | h | h <;> have := congrArg Fin.val h <;> omega
      · intro h; have := congrArg Fin.val h; omega
    · rintro ⟨i, j⟩ ⟨k, l⟩ he
      fin_cases i
      fin_cases k
      fin_cases j <;> fin_cases l <;> simp_all [Edge, Bond, f]
  haveI : Nonempty {g : Cell 1 → Fin 8 // Legal g} := ⟨⟨f, hf⟩⟩
  unfold a
  exact Nat.card_pos

def family : Registration arena (type_of% @literal_count_by_pairs) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨literal_count_by_pairs, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    rw [zero_count]
    exact positive_one.ne

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@literal_count_by_pairs) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.LiteralCount.unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.LiteralCount.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198LiteralModel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LiteralCount

attribute [local irreducible] ordinaryCount

namespace OrdinaryPairs

attribute [local instance] Classical.propDecidable

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ q n => ordinaryCount q n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ q n => ordinaryCount q n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ q n, q ≤ 4 → 0 < n → R.readout () q n =
    ∑ p : {p : Cell n → Fin 4 // PairLegal p},
      q.descFactorial (Nat.card (Set.range p.1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 2 1 (by decide) (by decide)
  have ha := ordinary_count_by_pairs 2 1 (by decide) (by decide)
  change ordinaryCount 2 1 + 1 = _ at hb
  omega

def family : Registration arena (type_of% @ordinary_count_by_pairs) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ordinary_count_by_pairs, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨2, 1, 2, ?_⟩
    change ordinaryCount 2 1 ≠ ordinaryCount 2 2
    rw [ordinary_two_count 1 (by decide), ordinary_two_count 2 (by decide)]
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@ordinary_count_by_pairs) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.OrdinaryPairs.unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.OrdinaryPairs.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q n => ordinaryCount q n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198LiteralModel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end OrdinaryPairs

namespace LiteralOrdinary

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ n => (a n : ℚ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => (a n : ℚ) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n, 0 < n → R.readout () () n = 16 ^ (n - 1) *
    ((ordinaryCount 4 n : ℚ) / 24 + (ordinaryCount 3 n : ℚ) / 6 +
      5 * (ordinaryCount 2 n : ℚ) / 4)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 (by decide)
  have ha := literal_ordinary_count 1 (by decide)
  change (a 1 : ℚ) + 1 = _ at hb
  linarith

def family : Registration arena (type_of% @literal_ordinary_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨literal_ordinary_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (a 0 : ℚ) ≠ (a 1 : ℚ)
    rw [LiteralCount.zero_count]
    exact_mod_cast LiteralCount.positive_one.ne

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@literal_ordinary_count) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.LiteralOrdinary.unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.LiteralOrdinary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (a n : ℚ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198LiteralModel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LiteralOrdinary

end

end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres
