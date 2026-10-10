/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/DonorCorrection
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Full-family original paid-feedback excess is at most four complete blocks. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FullPositiveWindowPrice
import Mathlib.Data.List.ChainOfFn

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection
open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse InternalZeroSafety
open OriginalNarrowCost OwnPathCharges PhysicalWindowDecoder
open GlobalPresetObstruction OriginalExecutionBridge OriginalAcquiredTrace
open scoped BigOperators

/-- Preserve every non-donor entry of the ordered window. -/
def outside (a : ℕ → ZMod 2) (r i : ℕ) : ZMod 2 :=
  if i = r ∨ i = r + 1 ∨ i = r + 2 then 0 else a i
/-- The first donor cancels the preceding prefix; the middle donor is zero;
the third absorbs the full remaining parity. -/
def correctedRow (m : ℕ) (a : ℕ → ZMod 2) (r i : ℕ) : ZMod 2 :=
  outside a r i + (if i = r then ∑ h ∈ Finset.range r, a h else 0) +
    (if i = r + 2 then (∑ h ∈ Finset.range r, a h) + (∑ h ∈ Finset.range (m + 1), outside a r h) else 0)

private theorem row_even (m : ℕ) (a : ℕ → ZMod 2) (r : ℕ) (bound : r + 2 ≤ m) :
    (∑ h ∈ Finset.range (m + 1), correctedRow m a r h) = 0 := by
  classical
  simp only [correctedRow, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_range, show r < m + 1 by omega, show r + 2 < m + 1 by omega, if_true]
  rw [show (∑ h ∈ Finset.range (m + 1), outside a r h) + (∑ h ∈ Finset.range r, a h) + ((∑ h ∈ Finset.range r, a h) + (∑ h ∈ Finset.range (m + 1), outside a r h)) =
      ((∑ h ∈ Finset.range (m + 1), outside a r h) + (∑ h ∈ Finset.range (m + 1), outside a r h)) +
      ((∑ h ∈ Finset.range r, a h) + (∑ h ∈ Finset.range r, a h)) by abel]
  rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add]

private theorem row_zero (m : ℕ) (a : ℕ → ZMod 2) (r : Fin m) :
    prefixWord m (correctedRow m a r.val) r = false := by
  classical
  have before : (∑ h ∈ Finset.range r.val, outside a r.val h) =
      ∑ h ∈ Finset.range r.val, a h := by
    apply Finset.sum_congr rfl
    intro h hh
    have less := Finset.mem_range.mp hh
    simp only [outside, if_neg (by omega : ¬ (h = r.val ∨ h = r.val + 1 ∨ h = r.val + 2))]
  have all : (∑ h ∈ Finset.range (r.val + 1), outside a r.val h) =
      ∑ h ∈ Finset.range r.val, a h := by
    rw [Finset.sum_range_succ, before]
    simp only [outside, true_or, if_true, add_zero]
  have prefixSum : (∑ h ∈ Finset.range (r.val + 1), correctedRow m a r.val h) = 0 := by
    simp only [correctedRow, Finset.sum_add_distrib]
    rw [all, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_range, Nat.lt_succ_self, if_true, show ¬ r.val + 2 < r.val + 1 by omega, if_false, add_zero]
    exact CharTwo.add_self_eq_zero _
  simp only [prefixWord, prefixSum, ne_eq, not_true_eq_false, decide_false]

/-- Correcting three consecutive entries gives a literal common archive. The
unchanged entries, root condition, every seam and original joint source witness
are retained. Calendar placement and label decoding are separate obligations. -/
private theorem actual_donor_corrected_suffix (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (hm : 1 ≤ m) (short : m < k) (alphabet : Bool)
    (marked : List ((ℕ → ZMod 2) × Fin m)) (donors : ∀ entry ∈ marked, entry.2.val + 2 ≤ m)
    (seams : marked.IsChain (fun a b => m + b.2.val ≤ k + a.2.val)) (v : ZMod 2) (j : ZMod (k + 1)) (s : ℕ) (hs : s < k)
    (incoming : ∀ entry ∈ marked.head?, s + entry.2.val < k ∨ correctedRow m entry.1 entry.2.val 0 = 0) (actualPhase : Nat.gcd m (k + 1) ∣ (-j).val) :
    let rows := marked.map (fun e => correctedRow m e.1 e.2.val)
    let actions := chargeBlocks k m (by omega) short alphabet rows
    (∀ entry ∈ marked, ∀ i, i ≠ entry.2.val → i ≠ entry.2.val + 1 → i ≠ entry.2.val + 2 → correctedRow m entry.1 entry.2.val i = entry.1 i) ∧
    actions.length = marked.length ∧
    fixedBlockArchive actions (some ⟨v, -j, s⟩) = chargeArchive k m rows v j ∧ (fixedBlockArchive actions (some ⟨v, -j, s⟩)).length = marked.length ∧
    none ∉ fixedBlockArchive actions (some ⟨v, -j, s⟩) ∧
    ∃ (N : ℕ) (source : Fin N → Bool),
      m ∣ N ∧ DBonacciAdmissible k N source ∧
      runBits k source (some ⟨0, 0, 0⟩) = some ⟨v, -j, s⟩ ∧
      originalWordValue k source = v ∧ tailAfter 0 source = s ∧ (∀ (b : ℕ) (hb : (b + 1) * m ≤ N), DBonacciAdmissible k m (fun i : Fin m =>
          source ⟨b * m + i.val, by nlinarith [i.isLt]⟩)) ∧
      fixedBlockArchive actions (runBits k source (some ⟨0, 0, 0⟩)) =
        chargeArchive k m rows v j := by
  dsimp only
  let transformed : List ((ℕ → ZMod 2) × Fin m) :=
    marked.map (fun e => (correctedRow m e.1 e.2.val, e.2))
  have even : ∀ entry ∈ transformed, ∑ h ∈ Finset.range (m + 1), entry.1 h = 0 := by
    rintro entry he
    change entry ∈ marked.map _ at he
    obtain ⟨e, emem, eeq⟩ := List.mem_map.mp he
    subst entry
    exact row_even m e.1 e.2.val (donors e emem)
  have zero : ∀ entry ∈ transformed, prefixWord m entry.1 entry.2 = false := by
    rintro entry he
    change entry ∈ marked.map _ at he
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp he
    exact row_zero m e.1 e.2
  have nextSeams : transformed.IsChain (fun a b => m + b.2.val ≤ k + a.2.val) := by
    simpa only [transformed, List.isChain_map] using seams
  have nextIncoming : ∀ entry ∈ transformed.head?, s + entry.2.val < k ∨ entry.1 0 = 0 := by
    intro entry he
    have mapped : transformed.head? = marked.head?.map (fun e => (correctedRow m e.1 e.2.val, e.2)) := List.head?_map
    rw [mapped] at he
    cases original : marked.head? with
    | none => simp only [original, Option.map_none, Option.not_mem_none] at he
    | some e =>
      simp only [original, Option.map_some, Option.mem_some_iff] at he
      subst entry
      exact incoming e (by simp only [original, Option.mem_some_iff])
  have native := actual_internal_zero_charge_suffix k hk m hm short alphabet transformed
    even zero nextSeams v j s hs nextIncoming actualPhase
  dsimp only at native
  have rows : transformed.map Prod.fst =
      marked.map (fun e => correctedRow m e.1 e.2.val) := by
    simp only [transformed, List.map_map, Function.comp_def]
  rw [rows, show transformed.length = marked.length from List.length_map _] at native
  refine ⟨?_, native⟩
  intro entry _ i first second third
  simp only [correctedRow, outside, first, second, third, or_self, if_false, add_zero]

/-- The six ordinary INITIAL phase donors. -/
def Donor (m : ℕ) (j : ZMod (2 * m - 2 + 1)) : Prop :=
  ∃ (e : ℕ) (δ : ℕ), e < 2 ∧ δ < 3 ∧
    j = ((m - 4 + e * m + δ : ℕ) : ZMod (2 * m - 2 + 1))
/-- The exact ordered moving-window input extracted from the own phase paths. -/
def codingRow {Y : Type*} {m : ℕ} (table : ZMod (2 * m - 2 + 1) → Y) (π : NarrowWindowCost.Selector m Y) (d t h : ℕ) : ZMod 2 :=
  correctedRow m (fun i => phaseCharges table π d t ((t * m + i : ℕ) : ZMod (2 * m - 2 + 1))) (m - 4 - t / 2) h

private theorem donor_calendar (m : ℕ) (hm : 5 ≤ m) (t : ℕ) (quotient : t / 2 ≤ m - 4) (δ : ℕ) :
    (((t * m + (m - 4 - t / 2) + δ : ℕ)) : ZMod (2 * m - 2 + 1)) = ((m - 4 + (t % 2) * m + δ : ℕ) : ZMod (2 * m - 2 + 1)) := by
  have period : (2 : ZMod (2 * m - 2 + 1)) * (m : ℕ) = 1 := by
    have sum : 2 * m = (2 * m - 2 + 1) + 1 := by omega
    have cast := congrArg (fun n : ℕ => (n : ZMod (2 * m - 2 + 1))) sum
    rw [Nat.cast_add, ZMod.natCast_self, zero_add] at cast
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using cast
  nth_rw 1 [show t = t % 2 + 2 * (t / 2) from (Nat.mod_add_div _ _).symm]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [Nat.cast_sub quotient]
  linear_combination ((t / 2 : ℕ) : ZMod (2 * m - 2 + 1)) * period

/-- Two consecutive charge vertices, whose inverse is one literal occupied bit. -/
def pairRow (r h : ℕ) : ZMod 2 := if h = r ∨ h = r + 1 then 1 else 0
private theorem pair_prefix (m r : ℕ) (i : Fin m) :
    prefixWord m (pairRow r) i = decide (i.val = r) := by
  classical
  have distinct : ∀ h : ℕ, pairRow r h = (if h = r then (1 : ZMod 2) else 0) + (if h = r + 1 then 1 else 0) := by
    intro h
    simp only [pairRow]
    split_ifs <;> simp_all <;> omega
  simp only [prefixWord]
  simp_rw [distinct]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_range]
  by_cases before : i.val < r
  · simp [show ¬ r < i.val + 1 by omega, show ¬ r + 1 < i.val + 1 by omega, show i.val ≠ r by omega]
  · by_cases equal : i.val = r
    · simp [equal]
    · simp [show r < i.val + 1 by omega, show r + 1 < i.val + 1 by omega, equal, CharTwo.add_self_eq_zero]

private theorem pair_even (m r : ℕ) (fit : r + 1 ≤ m) :
    ∑ h ∈ Finset.range (m + 1), pairRow r h = 0 := by
  classical
  have distinct : ∀ h : ℕ, pairRow r h = (if h = r then (1 : ZMod 2) else 0) + (if h = r + 1 then 1 else 0) := by
    intro h
    simp only [pairRow]
    split_ifs <;> simp_all <;> omega
  simp_rw [distinct]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [show r < m + 1 by omega, show r + 1 < m + 1 by omega, CharTwo.add_self_eq_zero]

/-- The two occurrences of each actual parity use consecutive donor edges.
The argument t is the offset within the four paid suffix blocks. -/
def suffixRow (m d t : ℕ) : ℕ → ZMod 2 :=
  pairRow (m - 4 - (d + t) / 2 + t / 2)
/-- All coding rows followed by the four donor-identifying rows. -/
def conversionRows {Y : Type*} {m : ℕ} (table : ZMod (2 * m - 2 + 1) → Y) (π : NarrowWindowCost.Selector m Y) (d : ℕ) : List (ℕ → ZMod 2) :=
  List.ofFn (fun t : Fin (d + 4) => if t.val < d then codingRow table π d t.val else suffixRow m d (t.val - d))

private theorem pair_charge (k m r : ℕ) (fit : r + 1 ≤ m) (short : m < k + 1) (j : ZMod (k + 1)) :
    windowCharge k m (pairRow r) j =
      if j = (r : ℕ) ∨ j = ((r + 1 : ℕ) : ZMod (k + 1)) then 1 else 0 := by
  have eqCast (a : ℕ) (ha : a < k + 1) : j = (a : ℕ) ↔ j.val = a := by
    constructor
    · intro eq
      rw [eq, ZMod.val_natCast, Nat.mod_eq_of_lt ha]
    · intro eq
      rw [← eq, ZMod.natCast_zmod_val]
  simp only [eqCast r (by omega), eqCast (r + 1) (by omega)]
  unfold windowCharge pairRow
  split_ifs <;> simp_all <;> omega

private theorem suffix_charge (m : ℕ) (hm : 5 ≤ m) (d : ℕ) (bound : d ≤ 2 * m - 10) (t : Fin 4) (j : ZMod (2 * m - 2 + 1)) :
    windowCharge (2 * m - 2) m (suffixRow m d t.val) (j - (((d + t.val) * m : ℕ) : ZMod (2 * m - 2 + 1))) =
    if j = ((m - 4 + ((d + t.val) % 2) * m + t.val / 2 : ℕ) : ZMod (2 * m - 2 + 1)) ∨
      j = ((m - 4 + ((d + t.val) % 2) * m + t.val / 2 + 1 : ℕ) : ZMod (2 * m - 2 + 1)) then 1 else 0 := by
  have range := t.isLt
  have quotient : (d + t.val) / 2 ≤ m - 4 := by omega
  rw [suffixRow, pair_charge _ _ _ (by omega) (by omega)]
  have first := donor_calendar m hm (d + t.val) quotient (t.val / 2)
  have second := donor_calendar m hm (d + t.val) quotient (t.val / 2 + 1)
  have first' : (((d + t.val) * m : ℕ) : ZMod (2 * m - 2 + 1)) + ((m - 4 - (d + t.val) / 2 + t.val / 2 : ℕ) : ZMod (2 * m - 2 + 1)) =
      ((m - 4 + ((d + t.val) % 2) * m + t.val / 2 : ℕ) : ZMod (2 * m - 2 + 1)) := by
    rw [← Nat.cast_add]
    simpa only [Nat.add_assoc] using first
  have second' : (((d + t.val) * m : ℕ) : ZMod (2 * m - 2 + 1)) + ((m - 4 - (d + t.val) / 2 + t.val / 2 + 1 : ℕ) : ZMod (2 * m - 2 + 1)) =
      ((m - 4 + ((d + t.val) % 2) * m + t.val / 2 + 1 : ℕ) : ZMod (2 * m - 2 + 1)) := by
    rw [← Nat.cast_add]
    simpa only [Nat.add_assoc] using second
  simp only [sub_eq_iff_eq_add, first', second', add_comm ((m - 4 - (d + t.val) / 2 + t.val / 2 : ℕ) : ZMod (2 * m - 2 + 1)) (((d + t.val) * m : ℕ) : ZMod (2 * m - 2 + 1)), add_comm ((m - 4 - (d + t.val) / 2 + t.val / 2 + 1 : ℕ) : ZMod (2 * m - 2 + 1)) (((d + t.val) * m : ℕ) : ZMod (2 * m - 2 + 1))]
private theorem suffix_charge_val (m : ℕ) (hm : 5 ≤ m) (d : ℕ) (bound : d ≤ 2 * m - 10) (t : Fin 4) (j : ZMod (2 * m - 2 + 1)) :
    windowCharge (2 * m - 2) m (suffixRow m d t.val) (j - (((d + t.val) * m : ℕ) : ZMod (2 * m - 2 + 1))) =
    if j.val = m - 4 + ((d + t.val) % 2) * m + t.val / 2 ∨
      j.val = m - 4 + ((d + t.val) % 2) * m + t.val / 2 + 1 then 1 else 0 := by
  rw [suffix_charge m hm d bound t j]
  have range := t.isLt
  have parity := Nat.mod_lt (d + t.val) (by decide : 0 < 2)
  have eqCast (a : ℕ) (ha : a < 2 * m - 2 + 1) :
      j = (a : ℕ) ↔ j.val = a := by
    constructor
    · intro eq
      rw [eq, ZMod.val_natCast, Nat.mod_eq_of_lt ha]
    · intro eq
      rw [← eq, ZMod.natCast_zmod_val]
  have high : m - 4 + ((d + t.val) % 2) * m + t.val / 2 + 1 < 2 * m - 2 + 1 := by
    rcases (by omega : (d + t.val) % 2 = 0 ∨ (d + t.val) % 2 = 1) with h | h <;>
      simp only [h, Nat.zero_mul, Nat.one_mul] <;> omega
  simp only [eqCast _ (by omega : m - 4 + ((d + t.val) % 2) * m + t.val / 2 < 2 * m - 2 + 1), eqCast _ high]
private theorem suffix_identifies_donors (m : ℕ) (hm : 5 ≤ m) (d : ℕ) (bound : d ≤ 2 * m - 10) (j j' : ZMod (2 * m - 2 + 1))
    (same : ∀ t : Fin 4, windowCharge (2 * m - 2) m (suffixRow m d t.val) (j - (((d + t.val) * m : ℕ) : ZMod (2 * m - 2 + 1))) =
      windowCharge (2 * m - 2) m (suffixRow m d t.val) (j' - (((d + t.val) * m : ℕ) : ZMod (2 * m - 2 + 1))))
    (donor : Donor m j) : j = j' := by
  have tests (t : Fin 4) : (j.val = m - 4 + ((d + t.val) % 2) * m + t.val / 2 ∨ j.val = m - 4 + ((d + t.val) % 2) * m + t.val / 2 + 1) ↔ (j'.val = m - 4 + ((d + t.val) % 2) * m + t.val / 2 ∨
       j'.val = m - 4 + ((d + t.val) % 2) * m + t.val / 2 + 1) := by
    have equal := same t
    rw [suffix_charge_val m hm d bound, suffix_charge_val m hm d bound] at equal
    split_ifs at equal <;> simp_all only [true_iff, iff_true, false_iff, iff_false, not_true_eq_false, not_false_eq_true, one_ne_zero, zero_ne_one]
  have zero := tests 0
  have one := tests 1
  have two := tests 2
  have three := tests 3
  obtain ⟨e, δ, he, hδ, phase⟩ := donor
  have low : m - 4 + e * m + δ < 2 * m - 2 + 1 := by
    interval_cases e <;> simp_all <;> omega
  have jvalue : j.val = m - 4 + e * m + δ := by
    rw [phase, ZMod.val_natCast, Nat.mod_eq_of_lt low]
  apply ZMod.val_injective
  have parity := Nat.mod_lt d (by decide : 0 < 2)
  have modone : (d + 1) % 2 = 1 - d % 2 := by omega
  have modtwo : (d + 2) % 2 = d % 2 := by omega
  have modthree : (d + 3) % 2 = 1 - d % 2 := by omega
  interval_cases e <;> interval_cases d % 2 <;>
    simp only [Fin.val_zero, Fin.val_one, Fin.val_ofNat, modone, modtwo, modthree, Nat.reduceMod, Nat.reduceDiv, Nat.zero_add,
      Nat.zero_mul, Nat.one_mul, Nat.add_zero] at zero one two three jvalue <;>
    simp_all <;> omega

/-- The coding portion of the donor conversion, with its root and seam safety
discharged from the original controller. Outside the six ordinary donors every
chronological phase charge is unchanged. All live sources acquire their own
complete common archive; this is not yet a label-decoding preset controller. -/
theorem original_donor_coding_archive {Y : Type*} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (table : ZMod (2 * m - 2 + 1) → Y)
    (target : ∀ (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ), s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = table j) (π : NarrowWindowCost.Selector m Y) (d : ℕ) (positive : 1 ≤ d)
    (bound : d ≤ 2 * m - 10) (correct : ∀ history : List (AllowedBlock (2 * m - 2) m alphabet), let w := history.flatMap (fun a => List.ofFn a.val)
      NarrowWindowCost.output (2 * m - 2) (by omega) w = some 0 →
      ∃ c ≤ d, NarrowWindowCost.execute (2 * m - 2) (by omega) π d w (some 0) [] =
        some (f (OriginalRecord (2 * m - 2) (by omega) w), c)) (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ) (hs : s < 2 * m - 2) :
    let rows := List.ofFn (fun t : Fin d => codingRow table π d t.val)
    let actions := chargeBlocks (2 * m - 2) m (by omega) (by omega) alphabet rows
    (∀ (t : Fin d) (phase : ZMod (2 * m - 2 + 1)), ¬ Donor m phase → windowCharge (2 * m - 2) m (codingRow table π d t.val) (phase - ((t.val * m : ℕ) : ZMod (2 * m - 2 + 1))) =
        phaseCharges table π d t.val phase) ∧
    actions.length = d ∧
    fixedBlockArchive actions (some ⟨v, -j, s⟩) =
      chargeArchive (2 * m - 2) m rows v j ∧ (fixedBlockArchive actions (some ⟨v, -j, s⟩)).length = d ∧
    none ∉ fixedBlockArchive actions (some ⟨v, -j, s⟩) := by
  classical
  dsimp only
  obtain ⟨support, root, separation⟩ := original_adaptive_charge_array
    m hm alphabet f table target π d correct
  let mark (t : Fin d) : Fin m := ⟨m - 4 - t.val / 2, by omega⟩
  let raw (t : Fin d) (h : ℕ) : ZMod 2 :=
    phaseCharges table π d t.val ((t.val * m + h : ℕ) : ZMod (2 * m - 2 + 1))
  let marked := List.ofFn (fun t : Fin d => (raw t, mark t))
  have donors : ∀ entry ∈ marked, entry.2.val + 2 ≤ m := by
    intro entry he
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp he
    dsimp [mark]
    omega
  have seams : marked.IsChain (fun a b => m + b.2.val ≤ (2 * m - 2) + a.2.val) := by
    apply List.isChain_ofFn.mpr
    intro t ht
    dsimp [mark]
    have mono : t / 2 ≤ (t + 1) / 2 := Nat.div_le_div_right (by omega)
    omega
  have incoming : ∀ entry ∈ marked.head?, s + entry.2.val < 2 * m - 2 ∨
      correctedRow m entry.1 entry.2.val 0 = 0 := by
    intro entry he
    have first : marked.head? = some (raw ⟨0, by omega⟩, mark ⟨0, by omega⟩) := by
      obtain ⟨n, eq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
      subst d
      simp only [marked, List.ofFn_succ, List.head?_cons]
      rfl
    rw [first] at he
    have equal := Option.mem_some_iff.mp he
    subst entry
    right
    dsimp [raw, mark, correctedRow, outside]
    simp only [Nat.zero_div, Nat.sub_zero, Nat.zero_mul, Nat.zero_add, Nat.cast_zero, if_neg (by omega : ¬ (0 = m - 4 ∨ 0 = m - 4 + 1 ∨ 0 = m - 4 + 2)),
      if_neg (by omega : ¬ 0 = m - 4), if_neg (by omega : ¬ 0 = m - 4 + 2), add_zero]
    exact root
  have gcdOne : Nat.gcd m (2 * m - 2 + 1) = 1 := by
    have twice : Nat.gcd m (2 * m - 2 + 1) ∣ 2 * m :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_left m _) 2
    have one := Nat.dvd_sub twice (Nat.gcd_dvd_right m _)
    rw [show 2 * m - (2 * m - 2 + 1) = 1 by omega] at one
    exact Nat.dvd_one.mp one
  have native := actual_donor_corrected_suffix (2 * m - 2) (by omega) m (by omega) (by omega) alphabet marked donors seams v j s hs incoming (by rw [gcdOne]; exact one_dvd _)
  dsimp only at native
  have rows : marked.map (fun e => correctedRow m e.1 e.2.val) =
      List.ofFn (fun t : Fin d => codingRow table π d t.val) := by
    simp only [marked, List.map_ofFn]
    rfl
  rw [rows, show marked.length = d from List.length_ofFn] at native
  refine ⟨?_, native.2.1, native.2.2.1, native.2.2.2.1, native.2.2.2.2.1⟩
  intro t phase notDonor
  let q := phase - ((t.val * m : ℕ) : ZMod (2 * m - 2 + 1))
  have original : ((t.val * m + q.val : ℕ) : ZMod (2 * m - 2 + 1)) = phase := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
    dsimp [q]
    abel
  have avoided (δ : ℕ) (hδ : δ < 3) : q.val ≠ m - 4 - t.val / 2 + δ := by
    intro equal
    apply notDonor
    refine ⟨t.val % 2, δ, Nat.mod_lt _ (by decide), hδ, ?_⟩
    rw [← original, equal]
    rw [← Nat.add_assoc, donor_calendar m hm t.val (by have := t.isLt; omega) δ]
  unfold windowCharge
  change (if q.val ≤ m then codingRow table π d t.val q.val else 0) = _
  split_ifs with inside
  · have preserved := native.1 (raw t, mark t) (List.mem_ofFn.mpr ⟨t, rfl⟩) q.val (by simpa only [Nat.add_zero] using avoided 0 (by decide))
      (avoided 1 (by decide)) (avoided 2 (by decide))
    change codingRow table π d t.val q.val = raw t q.val at preserved
    rw [preserved]
    exact congrArg (phaseCharges table π d t.val) original
  · exact (support t.val phase (by change m < q.val; omega)).symm
#print axioms original_donor_coding_archive

private theorem conversion_archive {Y : Type*} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (table : ZMod (2 * m - 2 + 1) → Y)
    (target : ∀ (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ), s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = table j) (π : NarrowWindowCost.Selector m Y) (d : ℕ) (positive : 1 ≤ d)
    (bound : d ≤ 2 * m - 10) (correct : ∀ history : List (AllowedBlock (2 * m - 2) m alphabet), let w := history.flatMap (fun a => List.ofFn a.val)
      NarrowWindowCost.output (2 * m - 2) (by omega) w = some 0 →
      ∃ c ≤ d, NarrowWindowCost.execute (2 * m - 2) (by omega) π d w (some 0) [] =
        some (f (OriginalRecord (2 * m - 2) (by omega) w), c)) (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ) (hs : s < 2 * m - 2) :
    fixedBlockArchive (chargeBlocks (2 * m - 2) m (by omega) (by omega) alphabet (conversionRows table π d)) (some ⟨v, -j, s⟩) =
      chargeArchive (2 * m - 2) m (conversionRows table π d) v j := by
  classical
  obtain ⟨_, root, _⟩ := original_adaptive_charge_array
    m hm alphabet f table target π d correct
  let row (t : ℕ) := if t < d then codingRow table π d t else suffixRow m d (t - d)
  let mark (t : ℕ) : Fin m := ⟨if t < d then m - 4 - t / 2 else m - 1, by split_ifs <;> omega⟩
  let marked := List.ofFn (fun t : Fin (d + 4) => (row t.val, mark t.val))
  have even : ∀ entry ∈ marked, ∑ h ∈ Finset.range (m + 1), entry.1 h = 0 := by
    intro entry he
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp he
    dsimp [row]
    split_ifs with inCoding
    · exact row_even m _ _ (by omega)
    · apply pair_even
      have := t.isLt
      have range : t.val - d < 4 := by omega
      change m - 4 - (d + (t.val - d)) / 2 + (t.val - d) / 2 + 1 ≤ m
      omega
  have zero : ∀ entry ∈ marked, prefixWord m entry.1 entry.2 = false := by
    intro entry he
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp he
    dsimp [row, mark]
    split_ifs with inCoding
    · exact row_zero m _ _
    · rw [suffixRow, pair_prefix]
      have := t.isLt
      simp only [Fin.val_mk, decide_eq_false_iff_not]
      omega
  have seams : marked.IsChain (fun a b => m + b.2.val ≤ (2 * m - 2) + a.2.val) := by
    apply List.isChain_ofFn.mpr
    intro t ht
    dsimp [mark]
    split_ifs <;> omega
  have incoming : ∀ entry ∈ marked.head?, s + entry.2.val < 2 * m - 2 ∨ entry.1 0 = 0 := by
    intro entry he
    have first : marked.head? = some (row 0, mark 0) := by
      change (List.ofFn (fun t : Fin ((d + 3) + 1) => (row t.val, mark t.val))).head? = _
      rw [List.ofFn_succ, List.head?_cons]
      rfl
    rw [first] at he
    have equal := Option.mem_some_iff.mp he
    subst entry
    right
    dsimp [row]
    rw [if_pos (by omega : 0 < d)]
    dsimp [codingRow, correctedRow, outside]
    simp only [Nat.zero_div, Nat.sub_zero, Nat.zero_mul, Nat.zero_add, Nat.cast_zero, if_neg (by omega : ¬ (0 = m - 4 ∨ 0 = m - 4 + 1 ∨ 0 = m - 4 + 2)),
      if_neg (by omega : ¬ 0 = m - 4), if_neg (by omega : ¬ 0 = m - 4 + 2), add_zero]
    exact root
  have gcdOne : Nat.gcd m (2 * m - 2 + 1) = 1 := by
    have twice := dvd_mul_of_dvd_right (Nat.gcd_dvd_left m (2 * m - 2 + 1)) 2
    have one := Nat.dvd_sub twice (Nat.gcd_dvd_right m _)
    rw [show 2 * m - (2 * m - 2 + 1) = 1 by omega] at one
    exact Nat.dvd_one.mp one
  have native := actual_internal_zero_charge_suffix (2 * m - 2) (by omega) m (by omega) (by omega) alphabet marked even zero seams v j s hs incoming
    (by rw [gcdOne]; exact one_dvd _)
  dsimp only at native
  have rows : marked.map Prod.fst = conversionRows table π d := by
    simp only [marked, List.map_ofFn, conversionRows]
    rfl
  rw [rows] at native
  exact native.2.1

private theorem row_readings_index (k m : ℕ) (rows : List (ℕ → ZMod 2)) (j : ZMod (k + 1)) (t : ℕ) :
    (rowReadings k m rows j)[t]? = (rows[t]?).map (fun row => some (windowCharge k m row (j - ((t * m : ℕ) : ZMod (k + 1))))) := by
  induction rows generalizing j t with
  | nil => simp [rowReadings]
  | cons row rest ih =>
    cases t with
    | zero => simp [rowReadings]
    | succ t =>
      simp only [rowReadings, List.getElem?_cons_succ, ih]
      congr 2
      funext r
      congr 2
      push_cast
      ring

private theorem conversion_separates {Y : Type*} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (table : ZMod (2 * m - 2 + 1) → Y)
    (target : ∀ (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ), s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = table j) (π : NarrowWindowCost.Selector m Y) (d : ℕ) (positive : 1 ≤ d)
    (bound : d ≤ 2 * m - 10) (correct : ∀ history : List (AllowedBlock (2 * m - 2) m alphabet), let w := history.flatMap (fun a => List.ofFn a.val)
      NarrowWindowCost.output (2 * m - 2) (by omega) w = some 0 →
      ∃ c ≤ d, NarrowWindowCost.execute (2 * m - 2) (by omega) π d w (some 0) [] =
        some (f (OriginalRecord (2 * m - 2) (by omega) w), c)) (j j' : ZMod (2 * m - 2 + 1))
    (same : rowReadings (2 * m - 2) m (conversionRows table π d) j = rowReadings (2 * m - 2) m (conversionRows table π d) j') : table j = table j' := by
  have coords (t : Fin (d + 4)) :
      windowCharge (2 * m - 2) m (if t.val < d then codingRow table π d t.val else suffixRow m d (t.val - d))
        (j - ((t.val * m : ℕ) : ZMod (2 * m - 2 + 1))) =
      windowCharge (2 * m - 2) m (if t.val < d then codingRow table π d t.val else suffixRow m d (t.val - d))
        (j' - ((t.val * m : ℕ) : ZMod (2 * m - 2 + 1))) := by
    have eq := congrArg (fun xs => xs[t.val]?) same
    simp only [row_readings_index, conversionRows, List.getElem?_ofFn, dif_pos t.isLt, Option.map_some] at eq
    exact Option.some.inj (Option.some.inj eq)
  have suffixSame (t : Fin 4) := coords ⟨d + t.val, by have := t.isLt; omega⟩
  simp only [Fin.val_mk, show ∀ t : ℕ, ¬ d + t < d by omega, if_false, Nat.add_sub_cancel_left] at suffixSame
  by_cases donor : Donor m j
  · exact congrArg table (suffix_identifies_donors m hm d bound j j' suffixSame donor)
  by_cases donor' : Donor m j'
  · exact congrArg table (suffix_identifies_donors m hm d bound j' j (fun t => (suffixSame t).symm) donor').symm
  have kept := (original_donor_coding_archive m hm alphabet f table target π d positive bound correct 0 0 0 (by omega)).1
  apply (original_adaptive_charge_array m hm alphabet f table target π d correct).2.2
  intro t ht
  have eq := coords ⟨t, by omega⟩
  simp only [Fin.val_mk, if_pos ht] at eq
  rw [kept ⟨t, ht⟩ j donor, kept ⟨t, ht⟩ j' donor'] at eq
  exact eq

private theorem script_global_preset {Y : Type*} (k m : ℕ) (hk : 2 ≤ k) (short : m < k) (alphabet : Bool) (f : Option (LiveRecord k) → Y)
    (words : List (Fin m → Bool)) (decode : ZMod 2 → NarrowWindowCost.Archive m → Y) (decoded : ∀ (v : ZMod 2) (phase : ZMod (k + 1)) (s : ℕ), s < k → decode v (scriptArchive words (some ⟨v, phase, s⟩)) = f (some ⟨v, phase, s⟩)) :
    OriginalPresetFeasible k m (by omega) alphabet f words.length := by
  classical
  let stream : ℕ → Fin m → Bool := fun t => words[t]?.getD (fun _ => false)
  let stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y := fun free ar =>
    match free with
    | none => some (f none)
    | some v => match words[ar.length]? with
      | some _ => none
      | none => some (decode v ar)
  refine ⟨stream, stop, ?_, rfl, ?_⟩
  · intro free ar B _ _
    exact short_legal k m hk short B
  · intro history
    dsimp only
    let w := history.flatMap (fun action => List.ofFn action.val)
    rw [output_record]
    cases initial : OriginalRecord k (by omega) w with
    | none =>
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [execute_same k m hk]
      change NativeExecute (presetSelector stream stop) words.length (OriginalRecord k (by omega) w) (endpointReading (OriginalRecord k (by omega) w)) [] = _
      rw [initial]
      cases words.length <;> rfl
    | some q =>
      have tail : q.tail < k := by
        unfold OriginalRecord at initial
        cases scan : (NarrowWindowCost.scanner k (by omega)).eval w with
        | none => simp [scan] at initial
        | some s =>
          simp only [scan, Option.map_some, Option.some.injEq] at initial
          have eq := congrArg LiveRecord.tail initial
          simpa only [← eq] using s.isLt
      have same (ar : NarrowWindowCost.Archive m) :
          presetSelector stream stop (some q.value) ar =
          finalSelector 0 words (decode q.value) (some q.value) ar := by
        simp only [presetSelector, stop]
        cases chosen : words[ar.length]? <;> simp [chosen, stream, finalSelector]
      have exactScript := original_final_script k m hk words (decode q.value)
        w (some q.value) []
      dsimp only at exactScript
      rw [initial] at exactScript
      have traced := (FullPositiveWindowPrice.trace_congr (presetSelector stream stop) (finalSelector 0 words (decode q.value)) (some q.value) same _ _ [] _).mpr exactScript.1
      have correctDecode := decoded q.value q.phase q.tail tail
      have qrecord : (⟨q.value, q.phase, q.tail⟩ : LiveRecord k) = q := by cases q; rfl
      rw [qrecord] at correctDecode
      rw [correctDecode] at traced
      refine ⟨words.length, le_rfl, ?_⟩
      rw [execute_same k m hk]
      change NativeExecute (presetSelector stream stop) words.length (OriginalRecord k (by omega) w) (endpointReading (OriginalRecord k (by omega) w)) [] = _
      rw [initial]
      rw [native_execute_paid_trace k m]
      exact ⟨scriptArchive words (some q), traced, exactScript.2.2.1, le_rfl⟩

/-- A correct original adaptive controller on the zero-value fibre supplies
one global preset stream costing at most four additional full blocks. The
stream, its safe suffix, and its decoder are constructed; both free values,
every original history and legal tail, and free initial bottom are included. -/
theorem original_donor_preset_feasible {Y : Type*} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (table : ZMod (2 * m - 2 + 1) → Y)
    (target : ∀ (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ),
      s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = table j) (π : NarrowWindowCost.Selector m Y) (d : ℕ) (positive : 1 ≤ d)
    (bound : d ≤ 2 * m - 10) (correct : ∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      NarrowWindowCost.output (2 * m - 2) (by omega) w = some 0 →
      ∃ c ≤ d, NarrowWindowCost.execute (2 * m - 2) (by omega) π d w (some 0) [] =
        some (f (OriginalRecord (2 * m - 2) (by omega) w), c)) :
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (d + 4) := by
  classical
  let rows := conversionRows table π d
  let words := rows.map (prefixWord m)
  let decode (v : ZMod 2) (archive : NarrowWindowCost.Archive m) : Y :=
    if h : ∃ j, rowReadings (2 * m - 2) m rows j =
        endpointDifferences (some v) (archive.map Prod.snd)
      then table (Classical.choose h) else f none
  have count : words.length = d + 4 := by simp [words, rows, conversionRows]
  rw [← count]
  apply script_global_preset (2 * m - 2) m (by omega) (by omega) alphabet f words decode
  intro v phase s hs
  let actions := chargeBlocks (2 * m - 2) m (by omega) (by omega) alphabet rows
  have wordEq : actions.map Subtype.val = words := by
    unfold actions chargeBlocks
    unfold AllowedBlock
    rw [List.map_map]
    rfl
  have readings : endpointDifferences (some v) ((scriptArchive words (some ⟨v, phase, s⟩)).map Prod.snd) =
      rowReadings (2 * m - 2) m rows (-phase) := by
    rw [← wordEq, script_readings]
    have native := conversion_archive m hm alphabet f table target π d positive bound
      correct v (-phase) s hs
    simp only [neg_neg] at native
    change fixedBlockArchive actions (some ⟨v, phase, s⟩) = _ at native
    rw [native, charge_differences]
  have existsPhase : ∃ j, rowReadings (2 * m - 2) m rows j =
      endpointDifferences (some v) ((scriptArchive words (some ⟨v, phase, s⟩)).map Prod.snd) :=
    ⟨-phase, readings.symm⟩
  change (if h : ∃ j, rowReadings (2 * m - 2) m rows j =
      endpointDifferences (some v) ((scriptArchive words (some ⟨v, phase, s⟩)).map Prod.snd)
    then table (Classical.choose h) else f none) = _
  rw [dif_pos existsPhase]
  have same := (Classical.choose_spec existsPhase).trans readings
  have separated := conversion_separates m hm alphabet f table target π d
    positive bound correct _ (-phase) same
  exact separated.trans (by simpa only [neg_neg] using (target v (-phase) s hs).symm)

#print axioms original_donor_preset_feasible
def uniformHorizon (m : ℕ) := 2 * m - 4 - min 2 (m - 5)
def uniformOccupied (m t : ℕ) := if 4 ≤ t ∧ t < 4 + min 2 (m - 5) then
  m - 2 - min 2 (m - 5) else 1
private def selected (m t : ℕ) : ZMod (2 * m - 2 + 1) := ((t * m + uniformOccupied m t : ℕ) : _)
private def absent (m e : ℕ) := e = 0 ∨ e = 3 ∨ e = m - 1 ∨ e = m ∨ e = m + 3
private theorem calendar (m : ℕ) (hm : 5 ≤ m) (h eps i : ℕ) : (((2 * h + eps) * m + i : ℕ) : ZMod (2 * m - 2 + 1)) =
      ((h + eps * m + i : ℕ) : ZMod (2 * m - 2 + 1)) := by
  have period : (2 : ZMod (2 * m - 2 + 1)) * (m : ℕ) = 1 := by
    have equality : 2 * m = (2 * m - 2 + 1) + 1 := by omega
    have cast := congrArg (fun n : ℕ => (n : ZMod (2 * m - 2 + 1))) equality
    rw [Nat.cast_add, ZMod.natCast_self, zero_add] at cast
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using cast
  push_cast
  linear_combination (h : ZMod (2 * m - 2 + 1)) * period
private theorem selected_surjects (m : ℕ) (hm : 7 ≤ m) (e : ℕ) (he : e < 2 * m - 2 + 1) (present : ¬ absent m e) :
    ∃ t : Fin (uniformHorizon m), selected m t.val = (e : ℕ) := by
  have q : min 2 (m - 5) = 2 := Nat.min_eq_left (by omega)
  have H : uniformHorizon m = 2 * m - 6 := by simp only [uniformHorizon, q]; omega
  have nonzero : e ≠ 0 := fun h => present (Or.inl h)
  have notThree : e ≠ 3 := fun h => present (Or.inr (Or.inl h))
  have notMone : e ≠ m - 1 := fun h => present (Or.inr (Or.inr (Or.inl h)))
  have notM : e ≠ m := fun h => present (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have notMthree : e ≠ m + 3 := fun h => present (Or.inr (Or.inr (Or.inr (Or.inr h))))
  by_cases special : e = m - 2
  · refine ⟨⟨4, by rw [H]; omega⟩, ?_⟩
    change (((4 * m + uniformOccupied m 4 : ℕ)) : ZMod (2 * m - 2 + 1)) = _
    have oi : uniformOccupied m 4 = m - 4 := by simp [uniformOccupied, q]; omega
    rw [oi]
    have cal := calendar m (by omega) 2 0 (m - 4)
    simpa only [Nat.zero_mul, Nat.add_zero, Nat.zero_add,
      show 2 + (m - 4) = e by omega] using cal
  by_cases terminal : e = 2 * m - 2
  · refine ⟨⟨5, by rw [H]; omega⟩, ?_⟩
    change (((5 * m + uniformOccupied m 5 : ℕ)) : ZMod (2 * m - 2 + 1)) = _
    have oi : uniformOccupied m 5 = m - 4 := by simp [uniformOccupied, q]; omega
    rw [oi]
    have cal := calendar m (by omega) 2 1 (m - 4)
    simpa only [Nat.one_mul, show 2 + m + (m - 4) = e by omega] using cal
  by_cases low : e ≤ m - 3
  · refine ⟨⟨2 * (e - 1), by rw [H]; omega⟩, ?_⟩
    have oi : uniformOccupied m (2 * (e - 1)) = 1 := by
      rw [uniformOccupied, q, if_neg (by omega : ¬ (4 ≤ 2 * (e - 1) ∧ 2 * (e - 1) < 6))]
    change (((2 * (e - 1) * m + uniformOccupied m (2 * (e - 1)) : ℕ)) : ZMod (2 * m - 2 + 1)) = _
    rw [oi]
    have cal := calendar m (by omega) (e - 1) 0 1
    simpa only [Nat.zero_mul, Nat.add_zero, Nat.zero_add,
      show e - 1 + 1 = e by omega] using cal
  · have high : m + 1 ≤ e ∧ e ≤ 2 * m - 3 := by omega
    refine ⟨⟨2 * (e - m - 1) + 1, by rw [H]; omega⟩, ?_⟩
    have oi : uniformOccupied m (2 * (e - m - 1) + 1) = 1 := by
      rw [uniformOccupied, q, if_neg (by omega : ¬ (4 ≤ 2 * (e - m - 1) + 1 ∧
        2 * (e - m - 1) + 1 < 6))]
    change ((((2 * (e - m - 1) + 1) * m + uniformOccupied m (2 * (e - m - 1) + 1) : ℕ)) : ZMod (2 * m - 2 + 1)) = _
    rw [oi]
    have cal := calendar m (by omega) (e - m - 1) 1 1
    simpa only [Nat.one_mul, show e - m - 1 + m + 1 = e by omega] using cal

private theorem profiles_separate (m : ℕ) (hm : 7 ≤ m) (x y : ℕ) (hx : x < 2 * m - 2 + 1) (hy : y < 2 * m - 2 + 1)
    (tests : ∀ e < 2 * m - 2 + 1, ¬ absent m e → ((x = e ∨ x = (if e + 1 = 2 * m - 2 + 1 then 0 else e + 1)) ↔
      (y = e ∨ y = (if e + 1 = 2 * m - 2 + 1 then 0 else e + 1)))) : x = y := by
  let previous (a : ℕ) := if a = 0 then 2 * m - 2 else a - 1
  have prevBound (a : ℕ) (ha : a < 2 * m - 2 + 1) : previous a < 2 * m - 2 + 1 := by
    dsimp [previous]; split_ifs <;> omega
  have prevNext (a : ℕ) (ha : a < 2 * m - 2 + 1) : (if previous a + 1 = 2 * m - 2 + 1 then 0 else previous a + 1) = a := by
    dsimp [previous]; split_ifs <;> omega
  have ax : absent m x ∨ y = x ∨ y = (if x + 1 = 2 * m - 2 + 1 then 0 else x + 1) := by
    by_cases missing : absent m x
    · exact Or.inl missing
    · exact Or.inr ((tests x hx missing).mp (Or.inl rfl))
  have ay : absent m y ∨ x = y ∨ x = (if y + 1 = 2 * m - 2 + 1 then 0 else y + 1) := by
    by_cases missing : absent m y
    · exact Or.inl missing
    · exact Or.inr ((tests y hy missing).mpr (Or.inl rfl))
  have bx : absent m (previous x) ∨ y = previous x ∨ y = x := by
    by_cases missing : absent m (previous x)
    · exact Or.inl missing
    · right
      have row := tests (previous x) (prevBound x hx) missing
      rw [prevNext x hx] at row
      exact row.mp (Or.inr rfl)
  have byy : absent m (previous y) ∨ x = previous y ∨ x = y := by
    by_cases missing : absent m (previous y)
    · exact Or.inl missing
    · right
      have row := tests (previous y) (prevBound y hy) missing
      rw [prevNext y hy] at row
      exact row.mpr (Or.inr rfl)
  dsimp [previous, absent] at ax ay bx byy
  split_ifs at ax ay bx byy <;> omega
private def column (m : ℕ) (j : ZMod (2 * m - 2 + 1)) (t : Fin (uniformHorizon m)) : ZMod 2 :=
  if j = selected m t.val ∨ j = selected m t.val + 1 then 1 else 0

private theorem columns_injective (m : ℕ) (hm : 5 ≤ m) :
    Function.Injective (fun j : ZMod (2 * m - 2 + 1) => column m j) := by
  intro j j' same
  by_cases five : m = 5
  · subst m
    have exact : Function.Injective (fun j : ZMod 9 => column 5 j) := by decide +kernel
    exact exact same
  by_cases six : m = 6
  · subst m
    have exact : Function.Injective (fun j : ZMod 11 => column 6 j) := by decide +kernel
    exact exact same
  have large : 7 ≤ m := by omega
  apply ZMod.val_injective
  apply profiles_separate m large j.val j'.val (ZMod.val_lt j) (ZMod.val_lt j')
  intro e he present
  obtain ⟨t, selectedEq⟩ := selected_surjects m large e he present
  have equal := congrFun same t
  simp only [column, selectedEq] at equal
  rw [show (e : ZMod (2 * m - 2 + 1)) + 1 = ((e + 1 : ℕ) : ZMod _) by
    push_cast; rfl] at equal
  have castEq (z : ZMod (2 * m - 2 + 1)) (a : ℕ) :
      z = (a : ℕ) ↔ z.val = a % (2 * m - 2 + 1) := by
    constructor
    · intro h
      rw [h, ZMod.val_natCast]
    · intro h
      apply ZMod.val_injective
      simpa only [ZMod.val_natCast] using h
  have next : (e + 1) % (2 * m - 2 + 1) =
      if e + 1 = 2 * m - 2 + 1 then 0 else e + 1 := by
    split_ifs with last
    · rw [last, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  simp only [castEq, Nat.mod_eq_of_lt he, next] at equal
  split_ifs at equal <;> simp_all only [true_iff, iff_true, false_iff, iff_false,
    not_true_eq_false, not_false_eq_true, one_ne_zero, zero_ne_one, ite_true, ite_false]
private def rows (m : ℕ) : List (ℕ → ZMod 2) :=
  List.ofFn (fun t : Fin (uniformHorizon m) => pairRow (uniformOccupied m t.val))
private theorem positions_internal (m : ℕ) (hm : 5 ≤ m) (t : ℕ) :
    1 ≤ uniformOccupied m t ∧ uniformOccupied m t + 1 < m := by
  have small : min 2 (m - 5) ≤ 2 := Nat.min_le_left _ _
  have width : min 2 (m - 5) ≤ m - 5 := Nat.min_le_right _ _
  unfold uniformOccupied
  split_ifs <;> omega
private theorem row_column (m : ℕ) (hm : 5 ≤ m) (j : ZMod (2 * m - 2 + 1)) (t : Fin (uniformHorizon m)) :
    windowCharge (2 * m - 2) m (pairRow (uniformOccupied m t.val)) (j - ((t.val * m : ℕ) : ZMod (2 * m - 2 + 1))) = column m j t := by
  rw [pair_charge _ _ _ (by have := positions_internal m hm t.val; omega) (by omega)]
  have first : (j - ((t.val * m : ℕ) : ZMod (2 * m - 2 + 1)) = ((uniformOccupied m t.val : ℕ) : ZMod (2 * m - 2 + 1))) ↔ j = selected m t.val := by
    rw [sub_eq_iff_eq_add]
    simp only [selected, Nat.cast_add, add_comm]
  have second : (j - ((t.val * m : ℕ) : ZMod (2 * m - 2 + 1)) = ((uniformOccupied m t.val + 1 : ℕ) : ZMod (2 * m - 2 + 1))) ↔
      j = selected m t.val + 1 := by
    rw [sub_eq_iff_eq_add]
    simp only [selected, Nat.cast_add, Nat.cast_one]
    congr 1
    abel
  simp only [first, second, column]
private theorem readings_injective (m : ℕ) (hm : 5 ≤ m) :
    Function.Injective (rowReadings (2 * m - 2) m (rows m)) := by
  intro j j' same
  apply columns_injective m hm
  funext t
  have equal := congrArg (fun xs => xs[t.val]?) same
  simp only [row_readings_index, rows, List.getElem?_ofFn,
    dif_pos t.isLt, Option.map_some] at equal
  have values := Option.some.inj (Option.some.inj equal)
  simpa only [row_column m hm] using values
private theorem native_archive (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool) (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ) (hs : s < 2 * m - 2) :
    fixedBlockArchive (chargeBlocks (2 * m - 2) m (by omega) (by omega) alphabet (rows m)) (some ⟨v, -j, s⟩) = chargeArchive (2 * m - 2) m (rows m) v j := by
  let marked := List.ofFn (fun t : Fin (uniformHorizon m) => (pairRow (uniformOccupied m t.val), (⟨0, by omega⟩ : Fin m)))
  have even : ∀ entry ∈ marked, ∑ h ∈ Finset.range (m + 1), entry.1 h = 0 := by
    intro entry he
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp he
    exact pair_even m _ (by have := positions_internal m hm t.val; omega)
  have zero : ∀ entry ∈ marked, prefixWord m entry.1 entry.2 = false := by
    intro entry he
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp he
    rw [pair_prefix]
    have positive := (positions_internal m hm t.val).1
    simp only [Fin.val_mk, decide_eq_false_iff_not]
    omega
  have seams : marked.IsChain (fun a b => m + b.2.val ≤ (2 * m - 2) + a.2.val) := by
    apply List.isChain_ofFn.mpr
    intros
    dsimp
    omega
  have incoming : ∀ entry ∈ marked.head?, s + entry.2.val < 2 * m - 2 ∨ entry.1 0 = 0 := by
    intro entry he
    have mem := List.mem_of_mem_head? he
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp mem
    left
    exact hs
  have gcdOne : Nat.gcd m (2 * m - 2 + 1) = 1 := by
    have twice := dvd_mul_of_dvd_right (Nat.gcd_dvd_left m (2 * m - 2 + 1)) 2
    have one := Nat.dvd_sub twice (Nat.gcd_dvd_right m _)
    rw [show 2 * m - (2 * m - 2 + 1) = 1 by omega] at one
    exact Nat.dvd_one.mp one
  have native := actual_internal_zero_charge_suffix (2 * m - 2) (by omega) m (by omega) (by omega) alphabet marked even zero seams v j s hs incoming
    (by rw [gcdOne]; exact one_dvd _)
  have rowEq : marked.map Prod.fst = rows m := by
    simp only [marked, rows, List.map_ofFn]
    congr 1
  dsimp only at native
  rw [rowEq] at native
  exact native.2.1

/-- A strictly internal single-one schedule separates every original phase
and yields one global preset protocol, including widths five and six. -/
theorem original_uniform_phase_preset {Y : Type*} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (table : ZMod (2 * m - 2 + 1) → Y)
    (target : ∀ (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ),
      s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = table j) :
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (uniformHorizon m) := by
  classical
  let words := (rows m).map (prefixWord m)
  let decode (v : ZMod 2) (ar : NarrowWindowCost.Archive m) : Y :=
    if h : ∃ j, rowReadings (2 * m - 2) m (rows m) j =
        endpointDifferences (some v) (ar.map Prod.snd)
      then table (Classical.choose h) else f none
  have count : words.length = uniformHorizon m := by simp [words, rows]
  rw [← count]
  apply script_global_preset (2 * m - 2) m (by omega) (by omega) alphabet f words decode
  intro v phase s hs
  let actions := chargeBlocks (2 * m - 2) m (by omega) (by omega) alphabet (rows m)
  have wordEq : actions.map Subtype.val = words := by
    unfold actions chargeBlocks AllowedBlock
    rw [List.map_map]
    rfl
  have readings : endpointDifferences (some v) ((scriptArchive words (some ⟨v, phase, s⟩)).map Prod.snd) =
      rowReadings (2 * m - 2) m (rows m) (-phase) := by
    rw [← wordEq, script_readings]
    have native := native_archive m hm alphabet v (-phase) s hs
    simp only [neg_neg] at native
    change fixedBlockArchive actions (some ⟨v, phase, s⟩) = _ at native
    rw [native, charge_differences]
  have existsPhase : ∃ j, rowReadings (2 * m - 2) m (rows m) j =
      endpointDifferences (some v) ((scriptArchive words (some ⟨v, phase, s⟩)).map Prod.snd) := ⟨-phase, readings.symm⟩
  change (if h : ∃ j, rowReadings (2 * m - 2) m (rows m) j =
      endpointDifferences (some v) ((scriptArchive words (some ⟨v, phase, s⟩)).map Prod.snd)
    then table (Classical.choose h) else f none) = _
  rw [dif_pos existsPhase]
  have identified := readings_injective m hm ((Classical.choose_spec existsPhase).trans readings)
  rw [identified]
  simpa only [neg_neg] using (target v (-phase) s hs).symm

#print axioms original_uniform_phase_preset

/-- One legal original controller serves both free values and every actual
complete-word history. Issued complete words, including rejection, are paid. -/
def OriginalAdaptiveFeasible {Y : Type*} (k m : ℕ) (hk : 0 < k) (alphabet : Bool) (f : Option (LiveRecord k) → Y) (d : ℕ) : Prop :=
  ∃ π : NarrowWindowCost.Selector m Y,
    FullPositiveWindowPrice.SelectorLegal k alphabet π ∧
    π none [] = .inl (f none) ∧
    ∀ history : List (AllowedBlock k m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      ∃ c ≤ d, NarrowWindowCost.execute k hk π d w (NarrowWindowCost.output k hk w) [] = some (f (OriginalRecord k hk w), c)

/-- The true global adaptive minimum, with infinity for infeasibility. -/
def GlobalAdaptivePrice {Y : Type*} (k m : ℕ) (hk : 0 < k) (alphabet : Bool) (f : Option (LiveRecord k) → Y) : ℕ∞ :=
  FullPositiveWindowPrice.BudgetPrice (OriginalAdaptiveFeasible k m hk alphabet f)

/-- The true original global preset minimum, using the existing whole-history
preset interface and a single literal stream shared by all free values. -/
def GlobalPresetPrice {Y : Type*} (k m : ℕ) (hk : 0 < k) (alphabet : Bool) (f : Option (LiveRecord k) → Y) : ℕ∞ :=
  FullPositiveWindowPrice.BudgetPrice (OriginalPresetFeasible k m hk alphabet f)

private theorem preset_inclusion {Y : Type*} (k m : ℕ) (hk : 0 < k) (alphabet : Bool) (f : Option (LiveRecord k) → Y) (d : ℕ)
    (feasible : OriginalPresetFeasible k m hk alphabet f d) :
    OriginalAdaptiveFeasible k m hk alphabet f d := by
  obtain ⟨stream, stop, legal, bottom, correct⟩ := feasible
  refine ⟨presetSelector stream stop, legal, ?_, correct⟩
  simp only [presetSelector, bottom]
private theorem preset_monotone {Y : Type*} (k m : ℕ) (hk : 2 ≤ k) (alphabet : Bool) (f : Option (LiveRecord k) → Y) (a b : ℕ) (le : a ≤ b)
    (feasible : OriginalPresetFeasible k m (by omega) alphabet f a) :
    OriginalPresetFeasible k m (by omega) alphabet f b := by
  obtain ⟨stream, stop, legal, bottom, correct⟩ := feasible
  refine ⟨stream, stop, legal, bottom, ?_⟩
  intro history
  obtain ⟨c, bound, success⟩ := correct history
  refine ⟨c, bound.trans le, ?_⟩
  rw [execute_paid_trace k m hk] at success ⊢
  obtain ⟨issued, trace, count, _⟩ := success
  exact ⟨issued, trace, count, bound.trans le⟩
private theorem constant_preset {Y : Type*} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool) (f : Option (LiveRecord (2 * m - 2)) → Y)
    (table : ZMod (2 * m - 2 + 1) → Y) (target : ∀ v j s, s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = table j)
    (constant : ∃ y, ∀ j, table j = y) :
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 0 := by
  obtain ⟨y, labels⟩ := constant
  have constructed := script_global_preset (2 * m - 2) m (by omega) (by omega)
    alphabet f [] (fun _ _ => y) (by
      intro v phase s hs
      exact (labels (-phase)).symm.trans (by
        simpa only [neg_neg] using (target v (-phase) s hs).symm))
  exact constructed
private theorem one_block_preset {Y : Type*} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool) (f : Option (LiveRecord (2 * m - 2)) → Y)
    (table : ZMod (2 * m - 2 + 1) → Y) (target : ∀ v j s, s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = table j)
    (π : NarrowWindowCost.Selector m Y) (correct : ∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      NarrowWindowCost.output (2 * m - 2) (by omega) w = some 0 →
      ∃ c ≤ 1, NarrowWindowCost.execute (2 * m - 2) (by omega) π 1 w (some 0) [] =
        some (f (OriginalRecord (2 * m - 2) (by omega) w), c)) :
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 1 := by
  classical
  by_cases constant : ∃ y, ∀ j, table j = y
  · exact preset_monotone _ _ (by omega) alphabet f 0 1 (by omega) (constant_preset m hm alphabet f table target constant)
  have array := original_adaptive_charge_array m hm alphabet f table target π 1 correct
  cases chosen : π (some 0) [] with
  | inl label =>
    have zero (j : ZMod (2 * m - 2 + 1)) : phaseCharges table π 1 0 j = 0 := by
      simp only [phaseCharges, if_neg constant, ownCharge, chosen]
    apply False.elim
    apply constant
    exact ⟨table 0, fun j => array.2.2 j 0 (by
      intro t ht
      have : t = 0 := by omega
      subst t
      rw [zero j, zero 0])⟩
  | inr B =>
    have safe : runAdmissible (2 * m - 2 - 1) (2 * m - 2 - 1 - 0) m B = true := by
      apply runAdmissible_eq_true_of_length_le <;> omega
    have charge (j : ZMod (2 * m - 2 + 1)) :
        phaseCharges table π 1 0 j = wordIncrement (2 * m - 2) (-j) B := by
      simp only [phaseCharges, if_neg constant, ownCharge, chosen, if_pos safe]
    have root := array.2.1
    rw [charge 0, neg_zero, show (0 : ZMod (2 * m - 2 + 1)) = -0 by simp,
      increment_derivative (2 * m - 2) (by omega) m (by omega)] at root
    have head : B ⟨0, by omega⟩ = false := by
      simpa [extendedBit, bitScalar, show 0 < m by omega] using root
    let decode (_v : ZMod 2) (ar : NarrowWindowCost.Archive m) : Y :=
      if h : ∃ j, [some (wordIncrement (2 * m - 2) (-j) B)] =
          endpointDifferences (some _v) (ar.map Prod.snd)
        then table (Classical.choose h) else f none
    have constructed := script_global_preset (2 * m - 2) m (by omega) (by omega)
      alphabet f [B] decode
    apply constructed
    intro v phase s hs
    have step := (short_safe_execution (2 * m - 2) (by omega) m (by omega) (by omega)
      B v phase s hs (Or.inr head)).1
    have readings : endpointDifferences (some v) ((scriptArchive [B] (some ⟨v, phase, s⟩)).map Prod.snd) =
        [some (wordIncrement (2 * m - 2) phase B)] := by
      simp [scriptArchive, step, endpointReading, endpointDifferences]
    have existsPhase : ∃ j, [some (wordIncrement (2 * m - 2) (-j) B)] =
        endpointDifferences (some v) ((scriptArchive [B] (some ⟨v, phase, s⟩)).map Prod.snd) := by
      refine ⟨-phase, ?_⟩
      simpa only [neg_neg] using readings.symm
    change (if h : ∃ j, [some (wordIncrement (2 * m - 2) (-j) B)] =
        endpointDifferences (some v) ((scriptArchive [B] (some ⟨v, phase, s⟩)).map Prod.snd)
      then table (Classical.choose h) else f none) = _
    rw [dif_pos existsPhase]
    have code := (Classical.choose_spec existsPhase).trans readings
    have separated := array.2.2 (Classical.choose existsPhase) (-phase) (by
      intro t ht
      have : t = 0 := by omega
      subst t
      rw [charge, charge, neg_neg]
      exact Option.some.inj (List.cons.inj code).1)
    exact separated.trans (by simpa only [neg_neg] using (target v (-phase) s hs).symm)
private theorem adaptive_conversion {Y : Type*} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool) (f : Option (LiveRecord (2 * m - 2)) → Y)
    (table : ZMod (2 * m - 2 + 1) → Y) (target : ∀ v j s, s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = table j)
    (d : ℕ) (adaptive : OriginalAdaptiveFeasible (2 * m - 2) m (by omega) alphabet f d) :
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (d + 4) := by
  obtain ⟨π, _, _, all⟩ := adaptive
  have correct : ∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      NarrowWindowCost.output (2 * m - 2) (by omega) w = some 0 →
      ∃ c ≤ d, NarrowWindowCost.execute (2 * m - 2) (by omega) π d w (some 0) [] =
        some (f (OriginalRecord (2 * m - 2) (by omega) w), c) := by
    intro history
    dsimp only
    intro free
    simpa only [free] using all history
  by_cases zero : d = 0
  · subst d
    have array := original_adaptive_charge_array m hm alphabet f table target π 0 correct
    have constant : ∃ y, ∀ j, table j = y := ⟨table 0, fun j => array.2.2 j 0 (by intros; omega)⟩
    exact preset_monotone _ _ (by omega) alphabet f 0 4 (by omega) (constant_preset m hm alphabet f table target constant)
  by_cases one : d = 1
  · subst d
    exact preset_monotone _ _ (by omega) alphabet f 1 5 (by omega) (one_block_preset m hm alphabet f table target π correct)
  by_cases small : d ≤ 2 * m - 10
  · exact original_donor_preset_feasible m hm alphabet f table target π d (by omega) small correct
  have fallback := original_uniform_phase_preset m hm alphabet f table target
  apply preset_monotone _ _ (by omega) alphabet f (uniformHorizon m) (d + 4) _ fallback
  unfold uniformHorizon
  by_cases five : m = 5
  · subst m; norm_num; omega
  by_cases six : m = 6
  · subst m; norm_num; omega
  have large : 7 ≤ m := by omega
  rw [Nat.min_eq_left (by omega : 2 ≤ m - 5)]
  omega
private theorem minimum_price (feasible : ℕ → Prop) (existsBudget : ∃ d, feasible d) :
    FullPositiveWindowPrice.BudgetPrice feasible = (@Nat.find feasible (Classical.decPred _) existsBudget : ℕ∞) := by
  classical
  exact FullPositiveWindowPrice.price_exact feasible (Nat.find existsBudget) (Nat.find_spec existsBudget) (fun _ proof => Nat.find_min' existsBudget proof)

/-- Full-family native paid feedback costs at most four complete blocks.
Both minima are finite and attained; all original histories, both free values,
both original alphabets, and every legal inherited tail remain in scope. -/
theorem original_uniform_paid_feedback_bound {Y : Type*} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (table : ZMod (2 * m - 2 + 1) → Y)
    (target : ∀ (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ),
      s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = table j) :
    GlobalAdaptivePrice (2 * m - 2) m (by omega) alphabet f ≤
      GlobalPresetPrice (2 * m - 2) m (by omega) alphabet f ∧
    GlobalPresetPrice (2 * m - 2) m (by omega) alphabet f ≤
      GlobalAdaptivePrice (2 * m - 2) m (by omega) alphabet f + 4 ∧
    GlobalAdaptivePrice (2 * m - 2) m (by omega) alphabet f + 4 < ⊤ := by
  classical
  have existsPreset : ∃ d, OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f d := ⟨uniformHorizon m,
      original_uniform_phase_preset m hm alphabet f table target⟩
  have existsAdaptive : ∃ d, OriginalAdaptiveFeasible (2 * m - 2) m (by omega) alphabet f d := ⟨Nat.find existsPreset, preset_inclusion _ _ (by omega) alphabet f _
      (Nat.find_spec existsPreset)⟩
  have lower : Nat.find existsAdaptive ≤ Nat.find existsPreset :=
    Nat.find_min' existsAdaptive (preset_inclusion _ _ (by omega) alphabet f _ (Nat.find_spec existsPreset))
  have upper : Nat.find existsPreset ≤ Nat.find existsAdaptive + 4 :=
    Nat.find_min' existsPreset (adaptive_conversion m hm alphabet f table target _ (Nat.find_spec existsAdaptive))
  unfold GlobalAdaptivePrice GlobalPresetPrice
  rw [minimum_price _ existsAdaptive, minimum_price _ existsPreset]
  constructor
  · exact_mod_cast lower
  constructor
  · exact_mod_cast upper
  · exact ENat.add_lt_top.mpr ⟨ENat.natCast_lt_top _, ENat.natCast_lt_top 4⟩

#print axioms original_uniform_paid_feedback_bound
end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection
