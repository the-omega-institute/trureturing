/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FourLabelPaidFeedback
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FourLabelPaidFeedback
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Full original four-label phase families have exact paid-feedback prices two and three. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FourLabelPaidFeedback

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S0.Tower.DBonacci.Names
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge WindowChargeInverse
open OriginalAcquiredTrace PhysicalWindowDecoder GlobalPresetObstruction DonorCorrection
open scoped BigOperators

/-- The indices zero, one, two and three name A, B, C and D, respectively. -/
def phaseClass (m : ℕ) (j : ZMod (2 * m - 2 + 1)) : Fin 4 :=
  if j.val = m - 2 ∨ j.val = m - 1 ∨ j.val = m then 1
  else if j.val = 0 ∨ j.val = m + 1 then 2
  else if j.val = 1 then 3 else 0

/-- A fixed free-value fibre retains all original histories and inherited tails. -/
def OriginalFiberPresetFeasible {Y : Type u} (k m : ℕ) (hk : 0 < k)
    (alphabet : Bool) (f : Option (LiveRecord k) → Y) (v : ZMod 2) (d : ℕ) : Prop :=
  ∃ (stream : ℕ → Fin m → Bool)
    (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y),
    FullPositiveWindowPrice.SelectorLegal k alphabet (presetSelector stream stop) ∧
    stop none [] = some (f none) ∧
    ∀ history : List (AllowedBlock k m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      NarrowWindowCost.output k hk w = some v →
      ∃ c ≤ d, NarrowWindowCost.execute k hk (presetSelector stream stop) d w
        (some v) [] = some (f (OriginalRecord k hk w), c)

def FiberPresetPrice {Y : Type u} (k m : ℕ) (hk : 0 < k)
    (alphabet : Bool) (f : Option (LiveRecord k) → Y) (v : ZMod 2) : ℕ∞ :=
  FullPositiveWindowPrice.BudgetPrice (OriginalFiberPresetFeasible k m hk alphabet f v)

/-- The saved free value selects the stream once. Paid replies only select stops. -/
def selectedSelector {m : ℕ} {Y : Type u} (streams : ZMod 2 → ℕ → Fin m → Bool)
    (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y) :
    NarrowWindowCost.Selector m Y := fun free archive =>
  presetSelector (streams (free.getD 0)) stop free archive

def OriginalSelectedPresetFeasible {Y : Type u} (k m : ℕ) (hk : 0 < k)
    (alphabet : Bool) (f : Option (LiveRecord k) → Y) (d : ℕ) : Prop :=
  ∃ (streams : ZMod 2 → ℕ → Fin m → Bool)
    (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y),
    FullPositiveWindowPrice.SelectorLegal k alphabet (selectedSelector streams stop) ∧
    stop none [] = some (f none) ∧
    ∀ history : List (AllowedBlock k m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      ∃ c ≤ d, NarrowWindowCost.execute k hk (selectedSelector streams stop) d w
        (NarrowWindowCost.output k hk w) [] = some (f (OriginalRecord k hk w), c)

def SelectedPresetPrice {Y : Type u} (k m : ℕ) (hk : 0 < k)
    (alphabet : Bool) (f : Option (LiveRecord k) → Y) : ℕ∞ :=
  FullPositiveWindowPrice.BudgetPrice (OriginalSelectedPresetFeasible k m hk alphabet f)

private theorem coprime (m : ℕ) (hm : 5 ≤ m) : Nat.gcd m (2 * m - 2 + 1) = 1 := by
  have h : Nat.Coprime m (m - 1) := by
    apply (Nat.coprime_self_sub_right (m := 1) (n := m) (by omega)).2
    exact Nat.coprime_one_right m
  have h' : Nat.Coprime m (2 * m - 1) := by
    apply (Nat.coprime_sub_self_right (m := m) (n := 2 * m - 1) (by omega)).1
    simpa only [show 2 * m - 1 - m = m - 1 by omega] using h
  simpa only [show 2 * m - 2 + 1 = 2 * m - 1 by omega] using h'

private def representative (m : ℕ) (c : Fin 4) : ZMod (2 * m - 2 + 1) :=
  if c = 0 then 2 else if c = 1 then (m - 2 : ℕ) else if c = 2 then 0 else 1

private theorem class_representative (m : ℕ) (hm : 5 ≤ m) (c : Fin 4) :
    phaseClass m (representative m c) = c := by
  have v1 : (1 : ZMod (2 * m - 2 + 1)).val = 1 := ZMod.val_natCast_of_lt (a := 1) (by omega)
  have v2 : (2 : ZMod (2 * m - 2 + 1)).val = 2 := ZMod.val_natCast_of_lt (a := 2) (by omega)
  have vb : ((m - 2 : ℕ) : ZMod (2 * m - 2 + 1)).val = m - 2 :=
    ZMod.val_natCast_of_lt (by omega)
  fin_cases c <;> simp only [representative, Fin.reduceFinMk, ite_true, ite_false,
    show (1 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide,
    show (2 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 0 by decide,
    show (3 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 2 by decide]
  all_goals simp only [phaseClass, v1, v2, vb, ZMod.val_zero]
  all_goals split_ifs
  all_goals (try simp only [true_or, false_or, or_true, or_false, not_true_eq_false] at *)
  all_goals first | omega | rfl

/-- Four distinct labels fill the four two-bit codes; consequently the code is
constant on each label class, even on sources that stop before a scheduled word. -/
private theorem saturation (m : ℕ) (hm : 5 ≤ m)
    (code : ZMod (2 * m - 2 + 1) → ZMod 2 × ZMod 2)
    (refines : ∀ p q, code p = code q → phaseClass m p = phaseClass m q) :
    ∀ p q, phaseClass m p = phaseClass m q → code p = code q := by
  let four := fun c : Fin 4 => code (representative m c)
  have injective : Function.Injective four := by
    intro c d equal
    simpa only [class_representative m hm] using
      refines (representative m c) (representative m d) equal
  have onto : Function.Surjective four :=
    ((Fintype.bijective_iff_injective_and_card four).mpr
      ⟨injective, by simp [ZMod.card]⟩).2
  have unique (p) : code p = four (phaseClass m p) := by
    obtain ⟨c, hc⟩ := onto (code p)
    have same := refines (representative m c) p hc
    rw [class_representative m hm] at same
    simpa only [← same] using hc.symm
  intro p q same
  rw [unique p, unique q, same]

private theorem first_blind (m : ℕ) (hm : 5 ≤ m) (word : Fin m → Bool)
    (j : ZMod (2 * m - 2 + 1)) (outside : m < j.val) :
    wordIncrement (2 * m - 2) (-j) word = 0 := by
  rw [increment_derivative _ (by omega) m (by omega)]
  simp [extendedBit, show ¬ j.val < m by omega,
    show j.val ≠ 0 by omega, show ¬ j.val - 1 < m by omega]

set_option maxHeartbeats 2000000 in
-- Saturation and full-support parity are checked over the symbolic phase modulus.
private theorem fixed_preset_obstruction {Y : Type u} (m : ℕ) (hm : 5 ≤ m)
    (alphabet : Bool) (labels : Fin 4 → Y) (distinct : Function.Injective labels)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ v j s, s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = labels (phaseClass m j)) (v : ZMod 2) :
    ¬ OriginalFiberPresetFeasible (2 * m - 2) m (by omega) alphabet f v 2 := by
  classical
  rintro ⟨stream, stop, _, _, correct⟩
  let a := fun j : ZMod (2 * m - 2 + 1) => wordIncrement (2 * m - 2) (-j) (stream 0)
  let b := fun j : ZMod (2 * m - 2 + 1) =>
    wordIncrement (2 * m - 2) (-j + (m : ℕ)) (stream 1)
  let code := fun j => (a j, b j)
  have refines (p q) (same : code p = code q) : phaseClass m p = phaseClass m q := by
    obtain ⟨c, _, hp⟩ := OwnPathCharges.native_fiber _ m (by omega) (by omega)
      alphabet f v 2 (presetSelector stream stop) correct (-p) 0 (by omega)
      (by rw [coprime m hm]; exact one_dvd _)
    obtain ⟨d, _, hq⟩ := OwnPathCharges.native_fiber _ m (by omega) (by omega)
      alphabet f v 2 (presetSelector stream stop) correct (-q) 0 (by omega)
      (by rw [coprime m hm]; exact one_dvd _)
    have sameRun := native_two_same _ m (by omega) stream stop v (-p) (-q) 0
      (by omega) (congrArg Prod.fst same) (congrArg Prod.snd same)
    rw [hp, hq] at sameRun
    have eq := (Prod.mk.inj (Option.some.inj sameRun)).1
    rw [target v p 0 (by omega), target v q 0 (by omega)] at eq
    exact distinct eq
  have const := saturation m hm code refines
  have cast_val (n : ℕ) (hn : n < 2 * m - 2 + 1) :
      (((n : ℕ) : ZMod (2 * m - 2 + 1))).val = n := ZMod.val_natCast_of_lt hn
  have Aclass : phaseClass m (m + 2 : ℕ) = 0 := by
    simp only [phaseClass, cast_val (m + 2) (by omega)]
    split_ifs
    all_goals (try simp only [true_or, false_or, or_true, or_false, not_true_eq_false] at *)
    all_goals first | omega | rfl
  have Cclass : phaseClass m (m + 1 : ℕ) = 2 := by
    rw [phaseClass, cast_val (m + 1) (by omega)]
    split_ifs <;> simp only [true_or, false_or, or_true, or_false, not_true_eq_false] at *
    all_goals first | omega | rfl
  have aA : a (representative m 0) = 0 := by
    have same := const (representative m 0) (m + 2 : ℕ)
      ((class_representative m hm 0).trans Aclass.symm)
    exact (congrArg Prod.fst same).trans
      (first_blind m hm _ _ (by rw [cast_val (m + 2) (by omega)]; omega))
  have aC : a (representative m 2) = 0 := by
    have same := const (representative m 2) (m + 1 : ℕ)
      ((class_representative m hm 2).trans Cclass.symm)
    exact (congrArg Prod.fst same).trans
      (first_blind m hm _ _ (by rw [cast_val (m + 1) (by omega)]; omega))
  have bA : b (representative m 0) = 0 := by
    exact second_charge_blind m hm _ _
      (by norm_num [representative, ZMod.val_ofNat,
        Nat.mod_eq_of_lt (show 2 < 2 * m - 2 + 1 by omega)])
      (by norm_num [representative, ZMod.val_ofNat,
        Nat.mod_eq_of_lt (show 2 < 2 * m - 2 + 1 by omega)]; omega)
  have bB : b (representative m 1) = 0 := by
    exact second_charge_blind m hm _ _
      (by simp [representative, cast_val (m - 2) (by omega)]; omega)
      (by simp [representative, cast_val (m - 2) (by omega)]; omega)
  have inj : Function.Injective (fun c : Fin 4 => code (representative m c)) := by
    intro c d h
    simpa only [class_representative m hm] using refines _ _ h
  have bC : b (representative m 2) = 1 := by
    have ne : b (representative m 2) ≠ 0 := by
      intro h
      have impossible := inj (show code (representative m 2) = code (representative m 0) from
        Prod.ext (aC.trans aA.symm) (h.trans bA.symm))
      have impossible' := congrArg Fin.val impossible
      norm_num at impossible'
    generalize b (representative m 2) = x at *
    fin_cases x
    · exact False.elim (ne rfl)
    · rfl
  have aB : a (representative m 1) = 1 := by
    have ne : a (representative m 1) ≠ 0 := by
      intro h
      have impossible := inj (show code (representative m 1) = code (representative m 0) from
        Prod.ext (h.trans aA.symm) (bB.trans bA.symm))
      have impossible' := congrArg Fin.val impossible
      norm_num at impossible'
    generalize a (representative m 1) = x at *
    fin_cases x
    · exact False.elim (ne rfl)
    · rfl
  have bD : b (representative m 3) = 1 := by
    have ne : b (representative m 3) ≠ 0 := by
      intro h
      generalize ha : a (representative m 3) = x
      fin_cases x
      · have impossible := inj (show code (representative m 3) = code (representative m 0) from
          Prod.ext (ha.trans aA.symm) (h.trans bA.symm))
        have impossible' := congrArg Fin.val impossible
        norm_num at impossible'
      · have impossible := inj (show code (representative m 3) = code (representative m 1) from
          Prod.ext (ha.trans aB.symm) (h.trans bB.symm))
        have impossible' := congrArg Fin.val impossible
        norm_num at impossible'
    generalize b (representative m 3) = x at *
    fin_cases x
    · exact False.elim (ne rfl)
    · rfl
  have forced (j) : b j = if j.val = 0 ∨ j.val = 1 ∨ j.val = m + 1 then 1 else 0 := by
    have same := const j (representative m (phaseClass m j))
      (class_representative m hm _).symm
    have scalar := congrArg Prod.snd same
    change b j = b (representative m (phaseClass m j)) at scalar
    rw [scalar]
    unfold phaseClass
    split_ifs <;> simp only [bA, bB, bC, bD] <;> omega
  have even := charge_even (2 * m - 2) m (by omega) (m : ℕ) (stream 1)
  change (∑ j, b j) = 0 at even
  simp_rw [forced] at even
  have eq (j : ZMod (2 * m - 2 + 1)) :
      (if j.val = 0 ∨ j.val = 1 ∨ j.val = m + 1 then (1 : ZMod 2) else 0) =
        (if j = 0 then 1 else 0) + (if j = 1 then 1 else 0) +
        (if j = (m + 1 : ℕ) then 1 else 0) := by
    have value1 : (1 : ZMod (2 * m - 2 + 1)).val = 1 :=
      ZMod.val_natCast_of_lt (a := 1) (by omega)
    have zero : j = 0 ↔ j.val = 0 := by
      constructor
      · intro h; simp [h]
      · intro h; apply ZMod.val_injective; simpa using h
    have one : j = 1 ↔ j.val = 1 := by
      constructor
      · intro h; rw [h]; exact value1
      · intro h; apply ZMod.val_injective; exact h.trans value1.symm
    have plus : j = (m + 1 : ℕ) ↔ j.val = m + 1 := by
      constructor
      · intro h; rw [h]; exact cast_val (m + 1) (by omega)
      · intro h; apply ZMod.val_injective; exact h.trans (cast_val (m + 1) (by omega)).symm
    simp only [zero, one, plus]
    split_ifs <;> norm_num <;> omega
  simp_rw [eq] at even
  simp only [Finset.sum_add_distrib] at even
  have impossible : (1 + 1 + 1 : ZMod 2) = 0 := by simpa using even
  exact (show (1 + 1 + 1 : ZMod 2) ≠ 0 from by decide) impossible

/-- R = 0 1^(m-3) 0 1. -/
def rootWord (m : ℕ) : Fin m → Bool := fun i => decide (i.val ≠ 0 ∧ i.val ≠ m - 2)
/-- X = 0 1^(m-2) 0. -/
def leftWord (m : ℕ) : Fin m → Bool := fun i => decide (0 < i.val ∧ i.val < m - 1)
/-- Y = 0^(m-1) 1. -/
def rightWord (m : ℕ) : Fin m → Bool := fun i => decide (i.val = m - 1)
/-- Z = 1^m. -/
def lastWord (m : ℕ) : Fin m → Bool := fun _ => true

private theorem val_eq (m : ℕ) (hm : 5 ≤ m) (j : ZMod (2 * m - 2 + 1))
    (n : ℕ) (hn : n < 2 * m - 2 + 1) : j.val = n ↔ j = (n : ℕ) := by
  have value := ZMod.val_natCast_of_lt hn
  constructor
  · intro h; exact ZMod.val_injective _ (h.trans value.symm)
  · intro h; rw [h]; exact value

private theorem twice (m : ℕ) (hm : 5 ≤ m) :
    (m : ZMod (2 * m - 2 + 1)) + (m : ℕ) = 1 := by
  have h : 2 * m = (2 * m - 2 + 1) + 1 := by omega
  have cast := congrArg (fun n : ℕ => (n : ZMod (2 * m - 2 + 1))) h
  rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add] at cast
  have two : ((2 * m : ℕ) : ZMod (2 * m - 2 + 1)) =
      (m : ℕ) + (m : ℕ) := by push_cast; ring
  exact two.symm.trans cast

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
-- The four symbolic literal derivatives require arithmetic splits at their transitions.
private theorem derivatives (m : ℕ) (hm : 5 ≤ m) (j : ZMod (2 * m - 2 + 1)) :
    wordIncrement (2 * m - 2) (-j) (rootWord m) =
      (if j.val = 1 ∨ j.val = m - 2 ∨ j.val = m - 1 ∨ j.val = m then 1 else 0) ∧
    wordIncrement (2 * m - 2) (-j) (leftWord m) =
      (if j.val = 1 ∨ j.val = m - 1 then 1 else 0) ∧
    wordIncrement (2 * m - 2) (-j) (rightWord m) =
      (if j.val = m - 1 ∨ j.val = m then 1 else 0) ∧
    wordIncrement (2 * m - 2) (-j) (lastWord m) =
      (if j.val = 0 ∨ j.val = m then 1 else 0) := by
  have bound := ZMod.val_lt j
  repeat' apply And.intro
  all_goals rw [increment_derivative _ (by omega) m (by omega)]
  all_goals simp only [extendedBit, rootWord, leftWord, rightWord, lastWord,
    bitScalar, Bool.decide_coe, decide_eq_true_eq]
  all_goals split_ifs <;> simp only [CharTwo.add_self_eq_zero, add_zero, zero_add,
    ite_true, ite_false,
    Bool.true_eq_false, Bool.false_eq_true, not_false_eq_true, not_true_eq_false,
    decide_true, decide_false] at * <;> first | omega | rfl

/-- Full physical charges at chronological indices zero, one, one and two. -/
private theorem literal_charges (m : ℕ) (hm : 5 ≤ m) (j : ZMod (2 * m - 2 + 1)) :
    wordIncrement (2 * m - 2) (-j) (rootWord m) =
      (if j.val = 1 ∨ j.val = m - 2 ∨ j.val = m - 1 ∨ j.val = m then 1 else 0) ∧
    wordIncrement (2 * m - 2) (-j + (m : ℕ)) (leftWord m) =
      (if j.val = 0 ∨ j.val = m + 1 then 1 else 0) ∧
    wordIncrement (2 * m - 2) (-j + (m : ℕ)) (rightWord m) =
      (if j.val = 0 ∨ j.val = 1 then 1 else 0) ∧
    wordIncrement (2 * m - 2) (-j + (m : ℕ) + (m : ℕ)) (lastWord m) =
      (if j.val = 1 ∨ j.val = m + 1 then 1 else 0) := by
  have val0 := val_eq m hm j 0 (by omega)
  have val1 := val_eq m hm j 1 (by omega)
  have valp := val_eq m hm j (m + 1) (by omega)
  have mid : ((m - 1 : ℕ) : ZMod (2 * m - 2 + 1)) + (m : ℕ) = 0 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    linear_combination twice m hm
  have h1 : j - (m : ℕ) = 1 ↔ j = (m + 1 : ℕ) := by
    rw [sub_eq_iff_eq_add]
    have eq : (m + 1 : ℕ) = (m : ZMod (2 * m - 2 + 1)) + 1 := by push_cast; rfl
    rw [eq, add_comm (1 : ZMod (2 * m - 2 + 1))]
  have h2 : j - (m : ℕ) = (m - 1 : ℕ) ↔ j = 0 := by
    rw [sub_eq_iff_eq_add, mid]
  have h3 : j - (m : ℕ) = (m : ℕ) ↔ j = 1 := by
    rw [sub_eq_iff_eq_add, twice m hm]
  have phase : -j + (m : ℕ) = -(j - (m : ℕ)) := by ring
  refine ⟨(derivatives m hm j).1, ?_, ?_, ?_⟩
  · rw [phase, (derivatives m hm (j - (m : ℕ))).2.1]
    simp only [
      val_eq m hm (j - (m : ℕ)) 1 (by omega), val_eq m hm (j - (m : ℕ)) (m - 1) (by omega), h1, h2]
    simp only [Nat.cast_zero, Nat.cast_one, h1, val0, valp, or_comm]
  · rw [phase, (derivatives m hm (j - (m : ℕ))).2.2.1]
    simp only [
      val_eq m hm (j - (m : ℕ)) (m - 1) (by omega), val_eq m hm (j - (m : ℕ)) m (by omega), h2, h3]
    simp only [Nat.cast_zero, Nat.cast_one, val0, val1]
  · have phase2 : -j + (m : ℕ) + (m : ℕ) = -(j - 1) := by
      linear_combination twice m hm
    rw [phase2, (derivatives m hm (j - 1)).2.2.2]
    simp only [
      val_eq m hm (j - 1) 0 (by omega), val_eq m hm (j - 1) m (by omega)]
    have plus : (m : ZMod (2 * m - 2 + 1)) + 1 = (m + 1 : ℕ) := by push_cast; rfl
    simp only [sub_eq_zero, sub_eq_iff_eq_add, plus, Nat.cast_zero, Nat.cast_one,
      zero_add, ← val1, ← valp]
    simp only [val1, Nat.cast_one]

/-- The adaptive controller uses the first paid difference to select X or Y. -/
def adaptiveSelector {Y : Type u} (m : ℕ) (labels : Fin 4 → Y) (bottom : Y) :
    NarrowWindowCost.Selector m Y := fun free archive =>
  match free, archive with
  | none, _ => .inl bottom
  | some _, [] => .inr (rootWord m)
  | some v, [(_, some z)] => .inr (if z = v then leftWord m else rightWord m)
  | some v, [(_, some z), (_, some z')] =>
      .inl (if z = v then (if z' = z then labels 0 else labels 2)
        else (if z' = z then labels 1 else labels 3))
  | _, _ => .inl bottom

/-- The same chronological stream serves every value and every running archive. -/
def commonStream (m : ℕ) : ℕ → Fin m → Bool
  | 0 => rootWord m
  | 1 => leftWord m
  | 2 => lastWord m
  | _ => fun _ => false

def commonStop {m : ℕ} {Y : Type u} (labels : Fin 4 → Y) (bottom : Y) :
    Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y := fun free archive =>
  match free, archive with
  | none, _ => some bottom
  | some _, [] => none
  | some _, [_] => none
  | some v, [(_, some z), (_, some z')] =>
      if z = v then some (if z' = z then labels 0 else labels 2) else none
  | some _, [(_, some _), (_, some z'), (_, some z'')] =>
      some (if z'' = z' then labels 1 else labels 3)
  | _, _ => some bottom

/-- Initial bottom pays zero. Live A,C sources pay two and B,D sources pay three. -/
def presetFee (m : ℕ) (q : Option (LiveRecord (2 * m - 2))) : ℕ :=
  match q with
  | none => 0
  | some q => if phaseClass m (-q.phase) = 0 ∨ phaseClass m (-q.phase) = 2 then 2 else 3

set_option maxHeartbeats 3000000 in
-- Both controllers are reduced on the symbolic record in each of the four phase classes.
private theorem live_attainment {Y : Type u} (m : ℕ) (hm : 5 ≤ m)
    (labels : Fin 4 → Y) (bottom : Y) (v : ZMod 2)
    (j : ZMod (2 * m - 2 + 1)) (s : ℕ) (hs : s < 2 * m - 2) :
    NativeExecute (adaptiveSelector m labels bottom) 2 (some ⟨v, -j, s⟩) (some v) [] =
      some (labels (phaseClass m j), 2) ∧
    NativeExecute (presetSelector (commonStream m) (commonStop labels bottom)) 3
      (some ⟨v, -j, s⟩) (some v) [] =
      some (labels (phaseClass m j), presetFee m (some ⟨v, -j, s⟩)) := by
  have root := short_safe_execution (2 * m - 2) (by omega) m (by omega) (by omega)
    (rootWord m) v (-j) s hs (Or.inr (by simp [rootWord]))
  have left := short_safe_execution (2 * m - 2) (by omega) m (by omega) (by omega)
    (leftWord m) (v + wordIncrement (2 * m - 2) (-j) (rootWord m)) (-j + (m : ℕ))
    (tailAfter 0 (rootWord m)) root.2 (Or.inr (by simp [leftWord]))
  have right := short_safe_execution (2 * m - 2) (by omega) m (by omega) (by omega)
    (rightWord m) (v + wordIncrement (2 * m - 2) (-j) (rootWord m)) (-j + (m : ℕ))
    (tailAfter 0 (rootWord m)) root.2 (Or.inr (by simp [rightWord]; omega))
  have endTail : tailAfter 0 (leftWord m) = 0 := by
    obtain ⟨n, eq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    subst m
    apply last_false_tail
    simp [leftWord]
  have last := short_safe_execution (2 * m - 2) (by omega) m (by omega) (by omega)
    (lastWord m) ((v + wordIncrement (2 * m - 2) (-j) (rootWord m)) +
      wordIncrement (2 * m - 2) (-j + (m : ℕ)) (leftWord m))
    (-j + (m : ℕ) + (m : ℕ)) (tailAfter 0 (leftWord m)) left.2 (Or.inl endTail)
  have charge := literal_charges m hm j
  have plusNe (w : ZMod 2) : w + 1 ≠ w := by
    intro h
    have eq : (1 : ZMod 2) = 0 := add_left_cancel (h.trans (add_zero w).symm)
    exact one_ne_zero eq
  have nb1 : ¬ (1 = m - 2 ∨ 1 = m - 1 ∨ 1 = m) := by omega
  have nc1 : ¬ (1 = 0 ∨ 1 = m + 1) := by omega
  have vne : v + 1 ≠ v := by
    intro h
    have eq : (1 : ZMod 2) = 0 := add_left_cancel (h.trans (add_zero v).symm)
    exact one_ne_zero eq
  have hr : wordIncrement (2 * m - 2) (-j) (rootWord m) =
      (if (j.val = m - 2 ∨ j.val = m - 1 ∨ j.val = m) ∨ j.val = 1 then 1 else 0) := by
    rw [charge.1]
    congr 1
    apply propext
    tauto
  by_cases hB : j.val = m - 2 ∨ j.val = m - 1 ∨ j.val = m
  all_goals by_cases hC : j.val = 0 ∨ j.val = m + 1
  all_goals by_cases hD : j.val = 1
  all_goals try omega
  all_goals
    have hx := charge.2.1
    have hy := charge.2.2.1
    have hz := charge.2.2.2
    simp only [hB, hC, hD, true_or, false_or, or_true, or_false,
      ite_true, ite_false] at hr hx hy hz
    have r := root.1
    have x := left.1
    have y := right.1
    have z := last.1
    have hp0 : (j.val = 0) ↔ (j = 0) := ZMod.val_eq_zero j
    have hc' : (j = 0 ∨ j.val = m + 1) ↔ (j.val = 0 ∨ j.val = m + 1) := by
      rw [← hp0]
    have hzero : ¬(j.val = 0 ∨ j.val = m + 1) → j.val ≠ 0 := by tauto
    have hplus : ¬(j.val = 0 ∨ j.val = m + 1) → j.val ≠ m + 1 := by tauto
    try simp only [hzero hC, hplus hC, ite_false] at hy hz
    simp only [hr, hx, hy, hz, nc1, nb1, ite_false, add_zero, zero_add] at r x y z
    simp only [native_succ, native_zero, adaptiveSelector, presetSelector,
      commonStream, commonStop, r, x, y, z, endpointReading, presetFee,
      phaseClass, neg_neg, hB, hC, hD, vne, plusNe, nb1, nc1,
      show (1 + 1 : ZMod 2) = 0 by decide, add_zero, zero_add, ite_true, ite_false,
      List.length_nil, List.length_cons, List.nil_append, List.cons_append,
      List.append_nil, Option.map_some, Option.some.injEq, Prod.mk.injEq,
      true_or, or_true, false_or, or_false, not_true_eq_false,
      show (1 : Fin 4) ≠ 0 by decide, show (1 : Fin 4) ≠ 2 by decide,
      show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 2 by decide,
      and_self, hc', and_true, true_and]
    try simp only [hC, hD, hB, ite_true, ite_false, add_zero,
      Option.map_some, Option.some.injEq, Prod.mk.injEq, and_self, and_true, true_and]


private theorem histories_attain {Y : Type u} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (labels : Fin 4 → Y) (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ v j s, s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = labels (phaseClass m j))
    (history : List (AllowedBlock (2 * m - 2) m alphabet)) :
    let w := history.flatMap (fun a => List.ofFn a.val)
    let q := OriginalRecord (2 * m - 2) (by omega) w
    NarrowWindowCost.execute (2 * m - 2) (by omega) (adaptiveSelector m labels (f none)) 2
      w (NarrowWindowCost.output (2 * m - 2) (by omega) w) [] =
        some (f q, if q.isSome then 2 else 0) ∧
    NarrowWindowCost.execute (2 * m - 2) (by omega)
      (presetSelector (commonStream m) (commonStop labels (f none))) 3
      w (NarrowWindowCost.output (2 * m - 2) (by omega) w) [] =
        some (f q, presetFee m q) := by
  intro w q
  have actual : SourceRecord (2 * m - 2) m q := by
    apply ((whole_first_zero_acquisition (2 * m - 2) m (by omega) (by omega)
      alphabet (fun _ => ())).1 q).mpr
    exact ⟨history, (record_history _ m (by omega) alphabet history).symm⟩
  rw [OriginalExecutionBridge.execute_same _ m (by omega),
    OriginalExecutionBridge.execute_same _ m (by omega), OriginalExecutionBridge.output_record]
  change NativeExecute _ 2 q (endpointReading q) [] = _ ∧
    NativeExecute _ 3 q (endpointReading q) [] = _
  cases hq : q with
  | none =>
    simp [native_succ, adaptiveSelector, presetSelector, commonStop, presetFee, endpointReading]
  | some r =>
    have hs : r.tail < 2 * m - 2 := by
      rw [hq] at actual
      exact actual.1
    have h := live_attainment m hm labels (f none) r.value (-r.phase) r.tail hs
    have targetEq := target r.value (-r.phase) r.tail hs
    simp only [neg_neg] at targetEq h
    simpa only [Option.isSome_some, if_true, endpointReading, ← targetEq] using h

private theorem attainable {Y : Type u} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (labels : Fin 4 → Y) (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ v j s, s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = labels (phaseClass m j)) :
    OriginalAdaptiveFeasible (2 * m - 2) m (by omega) alphabet f 2 ∧
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 3 := by
  have legal (π : NarrowWindowCost.Selector m Y) :
      FullPositiveWindowPrice.SelectorLegal (2 * m - 2) alphabet π := by
    intro free archive B _ _
    exact short_legal _ m (by omega) (by omega) B
  constructor
  · refine ⟨adaptiveSelector m labels (f none), legal _, rfl, ?_⟩
    intro history
    refine ⟨_, ?_, (histories_attain m hm alphabet labels f target history).1⟩
    split_ifs <;> omega
  · refine ⟨commonStream m, commonStop labels (f none), legal _, rfl, ?_⟩
    intro history
    refine ⟨_, ?_, (histories_attain m hm alphabet labels f target history).2⟩
    unfold presetFee
    split <;> first | omega | (split_ifs <;> omega)

private theorem adaptive_lower {Y : Type u} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (labels : Fin 4 → Y) (distinct : Function.Injective labels)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ v j s, s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = labels (phaseClass m j))
    (v : ZMod 2) : 2 ≤ OriginalFiberCost (2 * m - 2) m (by omega) alphabet f v := by
  classical
  let sample (i : Fin m) := f (some ⟨v, -((i.val : ℕ) : ZMod (2 * m - 2 + 1)), 0⟩)
  have range : Set.range sample = Set.range labels := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨phaseClass m (i.val : ℕ), (target v (i.val : ℕ) 0 (by omega)).symm⟩
    · rintro ⟨c, rfl⟩
      let n := if c = 0 then 2 else if c = 1 then m - 2 else if c = 2 then 0 else 1
      have hn : n < m := by dsimp [n]; split_ifs <;> omega
      refine ⟨⟨n, hn⟩, ?_⟩
      dsimp [sample]
      rw [target v (n : ℕ) 0 (by omega)]
      have same : (n : ZMod (2 * m - 2 + 1)) = representative m c := by
        dsimp [n, representative]; split_ifs <;> rfl
      rw [same, class_representative m hm]
  have card : Nat.card (Set.range sample) = 4 := by
    rw [range, Nat.card_range_of_injective distinct, Nat.card_fin]
  let g := Nat.gcd m (2 * m - 2 + 1)
  have g1 : g = 1 := coprime m hm
  let originalSample (j : Fin (m / g)) :=
    f (some ⟨v, -((j.val * g : ℕ) : ZMod (2 * m - 2 + 1)), 0⟩)
  have count : Nat.card (Set.range originalSample) = 4 := by
    dsimp only [originalSample]
    conv_lhs => rw [g1, Nat.div_one]
    simpa only [sample, Nat.mul_one] using card
  have lower := original_cost_lower (2 * m - 2) m (by omega) (by omega) (by omega)
    f v alphabet (show 3 ≤ Nat.card (Set.range originalSample) by rw [count]; omega)
  have wait : (2 * m - 2 + 1) / m = 1 := by
    apply Nat.div_eq_of_lt_le <;> omega
  change (((((2 * m - 2 + 1) / g) / (m / g)) +
    Nat.clog 2 (Nat.card (Set.range originalSample)) - 1 : ℕ) : ℕ∞) ≤ _ at lower
  rw [count, g1] at lower
  simpa [wait, show Nat.clog 2 4 = 2 from by decide] using lower


private theorem fiber_le_budget {Y : Type u} (k m : ℕ) (hk : 0 < k)
    (alphabet : Bool) (f : Option (LiveRecord k) → Y) (v : ZMod 2) (d : ℕ)
    (feasible : OriginalFiberFeasible k m hk alphabet f v d) :
    OriginalFiberCost k m hk alphabet f v ≤ (d : ℕ∞) :=
  iInf_le_of_le ⟨d, feasible⟩ le_rfl

private theorem fiber_preset_least {Y : Type u} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (labels : Fin 4 → Y) (distinct : Function.Injective labels)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ v j s, s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = labels (phaseClass m j))
    (v : ZMod 2) (d : ℕ)
    (feasible : OriginalFiberPresetFeasible (2 * m - 2) m (by omega) alphabet f v d) : 3 ≤ d := by
  by_contra small
  apply fixed_preset_obstruction m hm alphabet labels distinct f target v
  obtain ⟨stream, stop, legal, bottom, correct⟩ := feasible
  refine ⟨stream, stop, legal, bottom, ?_⟩
  intro history
  dsimp only
  intro observed
  obtain ⟨c, hc, success⟩ := correct history observed
  refine ⟨c, by omega, ?_⟩
  rw [execute_paid_trace _ m (by omega)] at success ⊢
  obtain ⟨issued, traced, count, _⟩ := success
  exact ⟨issued, traced, count, by omega⟩

private theorem global_to_fiber {Y : Type u} (k m : ℕ) (hk : 0 < k) (alphabet : Bool)
    (f : Option (LiveRecord k) → Y) (d : ℕ)
    (feasible : OriginalPresetFeasible k m hk alphabet f d) (v : ZMod 2) :
    OriginalFiberPresetFeasible k m hk alphabet f v d := by
  obtain ⟨stream, stop, legal, bottom, correct⟩ := feasible
  refine ⟨stream, stop, legal, bottom, ?_⟩
  intro history
  dsimp only
  intro observed
  simpa only [observed] using correct history

private theorem selected_to_fiber {Y : Type u} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (d : ℕ)
    (feasible : OriginalSelectedPresetFeasible (2 * m - 2) m (by omega) alphabet f d)
    (v : ZMod 2) : OriginalFiberPresetFeasible (2 * m - 2) m (by omega) alphabet f v d := by
  obtain ⟨streams, stop, _, bottom, correct⟩ := feasible
  refine ⟨streams v, stop, ?_, bottom, ?_⟩
  · intro free archive B _ _
    exact short_legal _ m (by omega) (by omega) B
  · intro history
    dsimp only
    intro observed
    obtain ⟨c, hc, success⟩ := correct history
    rw [observed, execute_paid_trace _ m (by omega)] at success
    obtain ⟨issued, traced, count, bound⟩ := success
    refine ⟨c, hc, ?_⟩
    rw [execute_paid_trace _ m (by omega)]
    refine ⟨issued, ?_, count, bound⟩
    exact (FullPositiveWindowPrice.trace_congr (selectedSelector streams stop)
      (presetSelector (streams v) stop) (some v)
      (by intro archive; rfl) _ _ [] _).mp traced

private theorem adaptive_to_fiber {Y : Type u} (k m : ℕ) (hk : 0 < k) (alphabet : Bool)
    (f : Option (LiveRecord k) → Y) (d : ℕ)
    (feasible : OriginalAdaptiveFeasible k m hk alphabet f d) (v : ZMod 2) :
    OriginalFiberFeasible k m hk alphabet f v d := by
  obtain ⟨π, legal, bottom, correct⟩ := feasible
  refine ⟨π, legal, bottom, ?_⟩
  intro history
  dsimp only
  intro observed
  simpa only [observed] using correct history

private theorem history_traces {Y : Type u} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (labels : Fin 4 → Y) (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ v j s, s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = labels (phaseClass m j))
    (history : List (AllowedBlock (2 * m - 2) m alphabet)) :
    let w := history.flatMap (fun a => List.ofFn a.val)
    let q := OriginalRecord (2 * m - 2) (by omega) w
    let free := NarrowWindowCost.output (2 * m - 2) (by omega) w
    (∃ issued, PaidTrace (adaptiveSelector m labels (f none)) free q [] issued (f q) ∧
      issued.length = (if q.isSome then 2 else 0) ∧
      (archiveWords issued).length = (if q.isSome then 2 * m else 0)) ∧
    (∃ issued, PaidTrace (presetSelector (commonStream m) (commonStop labels (f none)))
      free q [] issued (f q) ∧ issued.length = presetFee m q ∧
      (archiveWords issued).length = presetFee m q * m) := by
  intro w q free
  have successes := histories_attain m hm alphabet labels f target history
  constructor
  · obtain ⟨issued, traced, count, _⟩ :=
      (execute_paid_trace _ m (by omega) _ 2 w free [] (f q) _).mp successes.1
    refine ⟨issued, traced, count, ?_⟩
    rw [archive_length, count]
    split_ifs <;> simp
  · obtain ⟨issued, traced, count, _⟩ :=
      (execute_paid_trace _ m (by omega) _ 3 w free [] (f q) _).mp successes.2
    exact ⟨issued, traced, count, by rw [archive_length, count]⟩

/-- Exact minima on each full free-value fibre and on the joint original prior.
The explicit selectors retain own stopped archives and exact complete-word fees. -/
theorem original_four_label_paid_feedback {Y : Type u} (m : ℕ) (hm : 5 ≤ m)
    (alphabet : Bool) (labels : Fin 4 → Y) (distinct : Function.Injective labels)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = labels (phaseClass m j)) :
    (∀ v, OriginalFiberCost (2 * m - 2) m (by omega) alphabet f v = 2 ∧
      FiberPresetPrice (2 * m - 2) m (by omega) alphabet f v = 3) ∧
    GlobalAdaptivePrice (2 * m - 2) m (by omega) alphabet f = 2 ∧
    SelectedPresetPrice (2 * m - 2) m (by omega) alphabet f = 3 ∧
    GlobalPresetPrice (2 * m - 2) m (by omega) alphabet f = 3 ∧
    OriginalAdaptiveFeasible (2 * m - 2) m (by omega) alphabet f 2 ∧
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 3 ∧
    (∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      let q := OriginalRecord (2 * m - 2) (by omega) w
      let free := NarrowWindowCost.output (2 * m - 2) (by omega) w
      (∃ issued, PaidTrace (adaptiveSelector m labels (f none)) free q [] issued (f q) ∧
        issued.length = (if q.isSome then 2 else 0) ∧
        (archiveWords issued).length = (if q.isSome then 2 * m else 0)) ∧
      (∃ issued, PaidTrace (presetSelector (commonStream m) (commonStop labels (f none)))
        free q [] issued (f q) ∧ issued.length = presetFee m q ∧
        (archiveWords issued).length = presetFee m q * m)) ∧
    ∀ v : ZMod 2, ∃ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      let q := OriginalRecord (2 * m - 2) (by omega) w
      let free := NarrowWindowCost.output (2 * m - 2) (by omega) w
      q = some ⟨v, -1, 0⟩ ∧ ∃ ad pre,
        PaidTrace (adaptiveSelector m labels (f none)) free q [] ad (f q) ∧
        (archiveWords ad).length = 2 * m ∧
        PaidTrace (presetSelector (commonStream m) (commonStop labels (f none)))
          free q [] pre (f q) ∧ (archiveWords pre).length = 3 * m := by
  have attains := attainable m hm alphabet labels f target
  have leastAd (v : ZMod 2) (d : ℕ)
      (feasible : OriginalFiberFeasible (2 * m - 2) m (by omega) alphabet f v d) : 2 ≤ d := by
    exact_mod_cast (adaptive_lower m hm alphabet labels distinct f target v).trans
      (fiber_le_budget _ m (by omega) alphabet f v d feasible)
  have leastPre := fiber_preset_least m hm alphabet labels distinct f target
  refine ⟨?_, ?_, ?_, ?_, attains.1, attains.2, ?_, ?_⟩
  · intro v
    refine ⟨le_antisymm ?_ (adaptive_lower m hm alphabet labels distinct f target v), ?_⟩
    · exact fiber_le_budget _ m (by omega) alphabet f v 2
        (adaptive_to_fiber _ m (by omega) alphabet f 2 attains.1 v)
    · exact FullPositiveWindowPrice.price_exact _ 3
        (global_to_fiber _ m (by omega) alphabet f 3 attains.2 v) (leastPre v)
  · apply FullPositiveWindowPrice.price_exact _ 2 attains.1
    intro d feasible
    exact leastAd 0 d (adaptive_to_fiber _ m (by omega) alphabet f d feasible 0)
  · apply FullPositiveWindowPrice.price_exact _ 3
    · obtain ⟨stream, stop, legal, bottom, correct⟩ := attains.2
      exact ⟨fun _ => stream, stop, legal, bottom, correct⟩
    · intro d feasible
      exact leastPre 0 d (selected_to_fiber m hm alphabet f d feasible 0)
  · apply FullPositiveWindowPrice.price_exact _ 3 attains.2
    intro d feasible
    exact leastPre 0 d (global_to_fiber _ m (by omega) alphabet f d feasible 0)
  · exact history_traces m hm alphabet labels f target
  · intro v
    let initial : Option (LiveRecord (2 * m - 2)) := some ⟨v, -1, 0⟩
    have source : SourceRecord (2 * m - 2) m initial := by
      change 0 < 2 * m - 2 ∧ _
      refine ⟨by omega, ?_⟩
      rw [coprime m hm]
      exact one_dvd _
    obtain ⟨history, realized⟩ :=
      ((whole_first_zero_acquisition (2 * m - 2) m (by omega) (by omega)
        alphabet (fun _ => ())).1 initial).mp source
    let w := history.flatMap (fun a => List.ofFn a.val)
    have record : OriginalRecord (2 * m - 2) (by omega) w = initial :=
      (record_history _ m (by omega) alphabet history).trans realized
    have fee : presetFee m initial = 3 := by
      have cls := class_representative m hm 3
      change phaseClass m 1 = 3 at cls
      simp [presetFee, initial, cls]
    have traces := history_traces m hm alphabet labels f target history
    change (∃ issued, PaidTrace _ _ _ [] issued _ ∧
      issued.length = (if (OriginalRecord _ _ w).isSome then 2 else 0) ∧ _) ∧ _ at traces
    rw [record] at traces
    obtain ⟨ad, adTrace, _, adBits⟩ := traces.1
    obtain ⟨pre, preTrace, _, preBits⟩ := traces.2
    refine ⟨history, record, ?_⟩
    rw [record]
    refine ⟨ad, pre, adTrace, ?_, preTrace, ?_⟩
    · simpa only [initial, Option.isSome_some, if_true] using adBits
    · simpa only [fee] using preBits

#print axioms original_four_label_paid_feedback

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FourLabelPaidFeedback
