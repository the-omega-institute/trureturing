/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAttainment
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAttainment
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: A common pulse decodes first-window pairs on every original source. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.DonorCorrection
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FourLabelPaidFeedback

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment
open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse PhysicalWindowDecoder
open OriginalNarrowCost OriginalAcquiredTrace DonorCorrection GlobalPresetObstruction
open scoped BigOperators

abbrev Pair := ZMod 2 × ZMod 2
abbrev Phase (m : ℕ) := ZMod (2 * m - 2 + 1)

/-- A basis whose first coordinate annihilates the given parity vector. -/
def basis (p z : Pair) : Pair :=
  if p.1 = 0 then z else if p.2 = 0 then (z.2, z.1) else (z.1 + z.2, z.2)

/-- Each phase appears once in the parity, independently of tails and histories. -/
def parity (m : ℕ) (table : Phase m → Pair) : Pair :=
  ∑ h ∈ Finset.range (m + 1), table (h : ℕ)

def rootRow (m : ℕ) (table : Phase m → Pair) (h : ℕ) : ZMod 2 :=
  (basis (parity m table) (table (h : ℕ))).1

/-- The final path starts at actual phase one; its terminal donor is phase m+1. -/
def finalRow (m : ℕ) (table : Phase m → Pair) (h : ℕ) : ZMod 2 :=
  if h < m then (basis (parity m table) (table ((h + 1 : ℕ) : Phase m))).2
  else (basis (parity m table) (parity m table)).2

/-- The middle literal word is exactly 010^(m-2). -/
def pulse (m : ℕ) (i : Fin m) : Bool := decide (i.val = 1)

def words (m : ℕ) (table : Phase m → Pair) : List (Fin m → Bool) :=
  [prefixWord m (rootRow m table), pulse m, prefixWord m (finalRow m table)]

/-- Actual chronological differences, including both base-labelled pulse phases. -/
def code (m : ℕ) (table : Phase m → Pair) (j : Phase m) : List (Option (ZMod 2)) :=
  [some (basis (parity m table) (table j)).1,
   some (if j.val = m + 1 ∨ j.val = m + 2 then 1 else 0),
   some (if 1 ≤ j.val ∧ j.val ≤ m then (basis (parity m table) (table j)).2
     else if j.val = m + 1 then (basis (parity m table) (parity m table)).2 else 0)]

private theorem basis_zero (p : Pair) : basis p 0 = 0 := by
  unfold basis
  split_ifs <;> rfl

private theorem basis_injective (p : Pair) : Function.Injective (basis p) := by
  intro z w same
  unfold basis at same
  split_ifs at same with first second
  · exact same
  · exact Prod.ext (congrArg Prod.snd same) (congrArg Prod.fst same)
  · have right := congrArg Prod.snd same
    have left := congrArg Prod.fst same
    change z.2 = w.2 at right
    change z.1 + z.2 = w.1 + w.2 at left
    rw [← right] at left
    exact Prod.ext (add_right_cancel left) right

private theorem basis_annihilates (p : Pair) : (basis p p).1 = 0 := by
  unfold basis
  split_ifs with first second
  · exact first
  · exact second
  · have va : p.1.val = 1 := by
      have bound := ZMod.val_lt p.1
      have nonzero := (ZMod.val_ne_zero p.1).mpr first
      omega
    have vb : p.2.val = 1 := by
      have bound := ZMod.val_lt p.2
      have nonzero := (ZMod.val_ne_zero p.2).mpr second
      omega
    have equal : p.1 = p.2 := ZMod.val_injective 2 (va.trans vb.symm)
    change p.1 + p.2 = 0
    rw [equal, CharTwo.add_self_eq_zero]

private theorem basis_sum (p : Pair) (s : Finset ℕ) (f : ℕ → Pair) :
    (∑ h ∈ s, basis p (f h)) = basis p (∑ h ∈ s, f h) := by
  unfold basis
  split_ifs
  · rfl
  · apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  · apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_add_distrib]

private theorem rows_even (m : ℕ) (table : Phase m → Pair) (zero : table 0 = 0) :
    (∑ h ∈ Finset.range (m + 1), rootRow m table h) = 0 ∧
    (∑ h ∈ Finset.range (m + 1), finalRow m table h) = 0 := by
  have sumBasis := basis_sum (parity m table) (Finset.range (m + 1))
    (fun h => table (h : ℕ))
  have first : (∑ h ∈ Finset.range (m + 1), rootRow m table h) = 0 := by
    have eq := congrArg Prod.fst sumBasis
    have final := eq.trans (basis_annihilates _)
    simpa only [Prod.fst_sum, rootRow, parity] using final
  refine ⟨first, ?_⟩
  rw [Finset.sum_range_succ]
  have shifted : (∑ h ∈ Finset.range m, (basis (parity m table)
      (table ((h + 1 : ℕ) : Phase m))).2) = (basis (parity m table) (parity m table)).2 := by
    have eq := congrArg Prod.snd sumBasis
    rw [Finset.sum_range_succ'] at eq
    simp only [Nat.cast_zero, zero, basis_zero, add_zero, Prod.snd_sum] at eq
    exact eq
  have kept : (∑ h ∈ Finset.range m, finalRow m table h) =
      ∑ h ∈ Finset.range m, (basis (parity m table) (table ((h + 1 : ℕ) : Phase m))).2 := by
    apply Finset.sum_congr rfl
    intro h hh
    exact if_pos (Finset.mem_range.mp hh)
  rw [kept, shifted]
  simp only [finalRow, lt_self_iff_false, if_false, CharTwo.add_self_eq_zero]

theorem shift_value (m a : ℕ) (_hm : 5 ≤ m) (ha : a < 2 * m - 2 + 1)
    (j : Phase m) :
    (j - (a : ℕ)).val = if a ≤ j.val then j.val - a else j.val + (2 * m - 2 + 1) - a := by
  have bound := ZMod.val_lt j
  have : NeZero (2 * m - 2 + 1) := ⟨by omega⟩
  by_cases le : a ≤ j.val
  · rw [if_pos le, ZMod.val_sub (by simpa only [ZMod.val_natCast_of_lt ha] using le),
      ZMod.val_natCast_of_lt ha]
  · rw [if_neg le]
    have eq : j - (a : ℕ) = ((j.val + (2 * m - 2 + 1) - a : ℕ) : Phase m) := by
      rw [Nat.cast_sub (by omega : a ≤ j.val + (2 * m - 2 + 1)), Nat.cast_add,
        ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
    rw [eq, ZMod.val_natCast_of_lt (by omega)]

private theorem pulse_charge (m : ℕ) (hm : 5 ≤ m) (j : Phase m) :
    wordIncrement (2 * m - 2) (-(j - (m : ℕ))) (pulse m) =
      if j.val = m + 1 ∨ j.val = m + 2 then 1 else 0 := by
  rw [increment_derivative (2 * m - 2) (by omega) m (by omega)]
  have shift := shift_value m m hm (by omega) j
  rw [shift]
  unfold extendedBit bitScalar pulse
  by_cases hi : m ≤ j.val
  · rw [if_pos hi]
    split_ifs <;> simp_all <;> omega
  · rw [if_neg hi]
    have large : 2 ≤ j.val + (2 * m - 2 + 1) - m := by omega
    split_ifs <;> simp_all <;> omega

private theorem root_charge (m : ℕ) (_hm : 5 ≤ m) (table : Phase m → Pair)
    (outside : ∀ j, ¬ (1 ≤ j.val ∧ j.val ≤ m) → table j = 0) (j : Phase m) :
    windowCharge (2 * m - 2) m (rootRow m table) j =
      (basis (parity m table) (table j)).1 := by
  unfold windowCharge rootRow
  split_ifs with inside
  · rw [ZMod.natCast_zmod_val]
  · rw [outside j (by omega), basis_zero]
    rfl

private theorem final_charge (m : ℕ) (hm : 5 ≤ m) (table : Phase m → Pair) (j : Phase m) :
    windowCharge (2 * m - 2) m (finalRow m table) (j - ((2 * m : ℕ) : Phase m)) =
      if 1 ≤ j.val ∧ j.val ≤ m then (basis (parity m table) (table j)).2
      else if j.val = m + 1 then (basis (parity m table) (parity m table)).2 else 0 := by
  have cal := calendar m hm 1 0 0
  simp only [Nat.mul_one, Nat.add_zero, Nat.zero_mul] at cal
  rw [cal]
  have shift := shift_value m 1 hm (by omega) j
  unfold windowCharge finalRow
  rw [shift]
  have bound := ZMod.val_lt j
  by_cases positive : 1 ≤ j.val
  · rw [if_pos positive]
    have undo : (((j.val - 1 + 1 : ℕ)) : Phase m) = j := by
      rw [Nat.sub_add_cancel positive, ZMod.natCast_zmod_val]
    split_ifs <;> simp_all <;> omega
  · rw [if_neg positive]
    have jzero : j.val = 0 := by omega
    rw [if_neg (by omega : ¬ (j.val + (2 * m - 2 + 1) - 1 ≤ m))]
    simp [jzero]

theorem code_separates (m : ℕ) (table : Phase m → Pair)
    (outside : ∀ j, ¬ (1 ≤ j.val ∧ j.val ≤ m) → table j = 0)
    (j l : Phase m) (same : code m table j = code m table l) : table j = table l := by
  have first := congrArg (fun xs => xs[0]?) same
  have middle := congrArg (fun xs => xs[1]?) same
  have last := congrArg (fun xs => xs[2]?) same
  simp only [code, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq] at first middle last
  have forward (a b : Phase m) (inside : 1 ≤ a.val ∧ a.val ≤ m)
      (other : ¬ (1 ≤ b.val ∧ b.val ≤ m)) (eq : code m table a = code m table b) :
      table a = table b := by
    have first := congrArg (fun xs => xs[0]?) eq
    have middle := congrArg (fun xs => xs[1]?) eq
    have last := congrArg (fun xs => xs[2]?) eq
    simp only [code, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at first middle last
    have base := outside b other
    have donor : ¬ (b.val = m + 1 ∨ b.val = m + 2) := by
      have clear : ¬ (a.val = m + 1 ∨ a.val = m + 2) := by omega
      rw [if_neg clear] at middle
      split_ifs at middle <;> simp_all
    rw [if_pos inside, if_neg other, if_neg (by tauto : b.val ≠ m + 1)] at last
    rw [base, basis_zero] at first
    have equal : basis (parity m table) (table a) = 0 := Prod.ext first last
    exact (basis_injective _ (equal.trans (basis_zero _).symm)).trans base.symm
  by_cases inside : 1 ≤ j.val ∧ j.val ≤ m
  · by_cases other : 1 ≤ l.val ∧ l.val ≤ m
    · rw [if_pos inside, if_pos other] at last
      exact basis_injective _ (Prod.ext first last)
    · exact forward j l inside other same
  · by_cases other : 1 ≤ l.val ∧ l.val ≤ m
    · exact (forward l j other inside same.symm).symm
    · rw [outside j inside, outside l other]

private theorem script_code (m : ℕ) (hm : 5 ≤ m) (table : Phase m → Pair)
    (outside : ∀ j, ¬ (1 ≤ j.val ∧ j.val ≤ m) → table j = 0)
    (v : ZMod 2) (j : Phase m) (s : ℕ) (hs : s < 2 * m - 2) :
    endpointDifferences (some v)
      ((scriptArchive (words m table) (some ⟨v, -j, s⟩)).map Prod.snd) = code m table j := by
  have zero : table 0 = 0 := outside 0 (by simp)
  obtain ⟨evenRoot, evenFinal⟩ := rows_even m table zero
  obtain ⟨rootInv, rootHead, _, _⟩ := short_window_charge_inverse
    (2 * m - 2) (by omega) m (by omega) (by omega) (rootRow m table) evenRoot
  obtain ⟨finalInv, _, _, _⟩ := short_window_charge_inverse
    (2 * m - 2) (by omega) m (by omega) (by omega) (finalRow m table) evenFinal
  have head : prefixWord m (rootRow m table) ⟨0, by omega⟩ = false := by
    apply rootHead.mpr
    simp [rootRow, zero, basis_zero]
  obtain ⟨stepRoot, safeRoot⟩ := short_safe_execution (2 * m - 2) (by omega)
    m (by omega) (by omega) (prefixWord m (rootRow m table)) v (-j) s hs (Or.inr head)
  have pulseHead : pulse m ⟨0, by omega⟩ = false := by simp [pulse]
  obtain ⟨stepPulse, safePulse⟩ := short_safe_execution (2 * m - 2) (by omega)
    m (by omega) (by omega) (pulse m)
    (v + wordIncrement (2 * m - 2) (-j) (prefixWord m (rootRow m table)))
    (-j + (m : ℕ)) _ safeRoot (Or.inr pulseHead)
  have pulseTail : tailAfter 0 (pulse m) = 0 := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    cases hn
    apply last_false_tail
    simp [pulse, show n ≠ 1 by omega]
  rw [pulseTail] at stepPulse safePulse
  obtain ⟨stepFinal, _⟩ := short_safe_execution (2 * m - 2) (by omega)
    m (by omega) (by omega) (prefixWord m (finalRow m table))
    (v + wordIncrement (2 * m - 2) (-j) (prefixWord m (rootRow m table)) +
      (if j.val = m + 1 ∨ j.val = m + 2 then 1 else 0))
    (-j + (m : ℕ) + (m : ℕ)) 0 (by omega) (Or.inl rfl)
  have phaseOne : -j + (m : ℕ) = -(j - (m : ℕ)) := by ring
  have phaseTwo : -j + (m : ℕ) + (m : ℕ) = -(j - ((2 * m : ℕ) : Phase m)) := by push_cast; ring
  rw [phaseOne, pulse_charge m hm] at stepPulse
  rw [phaseTwo, finalInv, final_charge m hm] at stepFinal
  rw [rootInv, root_charge m hm table outside] at stepRoot stepPulse stepFinal
  rw [← phaseOne] at stepPulse
  rw [← phaseTwo] at stepFinal
  simp [words, scriptArchive, stepRoot, stepPulse, stepFinal, endpointReading,
    endpointDifferences, code]

/-- One literal stream, on every original history and both free-value fibres.
The two pulse donors are decoded as base rather than removed from the source. -/
theorem original_first_window_three_block_stream {Y : Type*}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (table : Phase m → Pair)
    (outside : ∀ j, ¬ (1 ≤ j.val ∧ j.val ≤ m) → table j = 0)
    (label : ZMod 2 → Pair → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = label v (table j)) :
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 3 ∧
    (words m table)[1]? = some (pulse m) ∧
    ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      endpointDifferences (some v)
        ((scriptArchive (words m table) (some ⟨v, -j, s⟩)).map Prod.snd) = code m table j ∧
      (scriptArchive (words m table) (some ⟨v, -j, s⟩)).length = 3 ∧
      ((scriptArchive (words m table) (some ⟨v, -j, s⟩)).flatMap
        (fun a => List.ofFn a.1)).length = 3 * m := by
  classical
  let decode (v : ZMod 2) (ar : NarrowWindowCost.Archive m) : Y :=
    if h : ∃ j, code m table j = endpointDifferences (some v) (ar.map Prod.snd)
    then label v (table (Classical.choose h)) else f none
  have feasible : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f 3 := by
    have count : (words m table).length = 3 := rfl
    rw [← count]
    apply script_global_preset (2 * m - 2) m (by omega) (by omega) alphabet f (words m table) decode
    intro v phase s hs
    have readings := script_code m hm table outside v (-phase) s hs
    simp only [neg_neg] at readings
    have existsPhase : ∃ j, code m table j = endpointDifferences (some v)
        ((scriptArchive (words m table) (some ⟨v, phase, s⟩)).map Prod.snd) :=
      ⟨-phase, readings.symm⟩
    dsimp only [decode]
    rw [dif_pos existsPhase]
    have separated := code_separates m table outside _ (-phase)
      ((Classical.choose_spec existsPhase).trans readings)
    rw [separated]
    simpa only [neg_neg] using (target v (-phase) s hs).symm
  refine ⟨feasible, rfl, ?_⟩
  intro v j s hs
  refine ⟨script_code m hm table outside v j s hs, ?_, ?_⟩
  · simp [words, scriptArchive]
  · change (archiveWords (scriptArchive (words m table) (some ⟨v, -j, s⟩))).length = _
    rw [archive_length]
    simp [words, scriptArchive]

/-- Scalar membership, on the actual integer representatives of the phase group. -/
def supportRow (H : Finset ℕ) (h : ℕ) : ZMod 2 := if h ∈ H then 1 else 0

/-- The boundary compensation in the three odd-support cases. -/
def oddRoot (m : ℕ) (H : Finset ℕ) : Finset ℕ :=
  if m ∉ H then insert m H else if 1 ∉ H then insert 1 H else H.erase m

def oddSecond (m : ℕ) (H : Finset ℕ) : Finset ℕ :=
  if m ∉ H then {0, 1} else if 1 ∉ H then {1, m} else {0, m}

/-- Second charge in the original phase frame, including the actual donor. -/
def oddSecondCharge (m : ℕ) (H : Finset ℕ) (h : ℕ) : ZMod 2 :=
  if m ∉ H then (if h = m ∨ h = m + 1 then 1 else 0)
  else if 1 ∉ H then (if h = 1 ∨ h = m + 1 then 1 else 0)
  else if h = 1 ∨ h = m then 1 else 0

def binaryCost (H : Finset ℕ) : ℕ :=
  if H = ∅ then 0 else if Even H.card then 1 else 2

def binaryWords (m : ℕ) (H : Finset ℕ) : List (Fin m → Bool) :=
  if H = ∅ then [] else if Even H.card then [prefixWord m (supportRow H)]
  else [prefixWord m (supportRow (oddRoot m H)), prefixWord m (supportRow (oddSecond m H))]

def binaryCode (m : ℕ) (H : Finset ℕ) (j : Phase m) : List (Option (ZMod 2)) :=
  if H = ∅ then [] else if Even H.card then [some (supportRow H j.val)]
  else [some (supportRow (oddRoot m H) j.val), some (oddSecondCharge m H j.val)]

theorem support_sum (m : ℕ) (H : Finset ℕ)
    (inside : ∀ h ∈ H, h ≤ m) :
    (∑ h ∈ Finset.range (m + 1), supportRow H h) = (H.card : ZMod 2) := by
  have subset : H ⊆ Finset.range (m + 1) := by
    intro h hh; exact Finset.mem_range.mpr (by have := inside h hh; omega)
  have eq := Finset.sum_subset subset (f := supportRow H) (by
    intro h _ hh; exact if_neg hh)
  rw [← eq]
  simp [supportRow]

private theorem odd_rows (m : ℕ) (hm : 5 ≤ m) (H : Finset ℕ)
    (inside : ∀ h ∈ H, 1 ≤ h ∧ h ≤ m) (odd : ¬ Even H.card) :
    (∑ h ∈ Finset.range (m + 1), supportRow (oddRoot m H) h) = 0 ∧
    (∑ h ∈ Finset.range (m + 1), supportRow (oddSecond m H) h) = 0 ∧
    supportRow (oddRoot m H) 0 = 0 := by
  have zero : 0 ∉ H := by intro h; have := inside 0 h; omega
  have castOdd : (H.card : ZMod 2) = 1 := by
    exact (Odd.natCast_zmod_two (Nat.not_even_iff_odd.mp odd))
  by_cases last : m ∉ H
  · simp only [oddRoot, oddSecond, if_pos last]
    rw [support_sum m (insert m H) (by
      intro h hh; rcases Finset.mem_insert.mp hh with rfl | hh
      · omega
      · exact (inside h hh).2), Finset.card_insert_of_notMem last,
      Nat.cast_add, Nat.cast_one, castOdd]
    have two : ({0, 1} : Finset ℕ).card = 2 := by decide
    rw [support_sum m {0, 1} (by intro h hh; simp at hh; rcases hh with rfl | rfl <;> omega), two]
    simp [supportRow, zero, show (0 : ℕ) ≠ m by omega,
      show (2 : ZMod 2) = 0 by decide, CharTwo.add_self_eq_zero]
  · by_cases first : 1 ∉ H
    · simp only [oddRoot, oddSecond, if_neg last, if_pos first]
      rw [support_sum m (insert 1 H) (by
        intro h hh; rcases Finset.mem_insert.mp hh with rfl | hh
        · omega
        · exact (inside h hh).2), Finset.card_insert_of_notMem first,
        Nat.cast_add, Nat.cast_one, castOdd]
      have two : ({1, m} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
      rw [support_sum m {1, m} (by intro h hh; simp at hh; rcases hh with rfl | rfl <;> omega), two]
      simp [supportRow, zero, show (2 : ZMod 2) = 0 by decide, CharTwo.add_self_eq_zero]
    · simp only [oddRoot, oddSecond, if_neg last, if_neg first]
      rw [support_sum m (H.erase m) (by intro h hh; exact (inside h (Finset.mem_of_mem_erase hh)).2)]
      have card : (H.erase m).card + 1 = H.card := Finset.card_erase_add_one (by tauto)
      have cast := congrArg (fun n : ℕ => (n : ZMod 2)) card
      push_cast at cast
      rw [castOdd] at cast
      have even : ((H.erase m).card : ZMod 2) = 0 := by linear_combination cast
      rw [even]
      have two : ({0, m} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
      rw [support_sum m {0, m} (by intro h hh; simp at hh; rcases hh with rfl | rfl <;> omega), two]
      simp [supportRow, zero, show (2 : ZMod 2) = 0 by decide, CharTwo.add_self_eq_zero]

private theorem odd_second_charge (m : ℕ) (hm : 5 ≤ m) (H : Finset ℕ) (j : Phase m) :
    windowCharge (2 * m - 2) m (supportRow (oddSecond m H)) (j - (m : ℕ)) =
      oddSecondCharge m H j.val := by
  have shift := shift_value m m hm (by omega) j
  have bound := ZMod.val_lt j
  unfold windowCharge
  rw [shift]
  unfold supportRow oddSecond oddSecondCharge
  by_cases last : m ∉ H <;> by_cases first : 1 ∉ H <;>
    by_cases large : m ≤ j.val <;> simp only [last, first, large, if_true, if_false,
      Finset.mem_insert, Finset.mem_singleton] <;>
    split_ifs <;> simp_all <;> omega

theorem binary_separates (m : ℕ) (hm : 5 ≤ m) (H : Finset ℕ)
    (inside : ∀ h ∈ H, 1 ≤ h ∧ h ≤ m)
    (j l : Phase m) (same : binaryCode m H j = binaryCode m H l) :
    supportRow H j.val = supportRow H l.val := by
  classical
  by_cases empty : H = ∅
  · simp [supportRow, empty]
  · by_cases even : Even H.card
    · simpa [binaryCode, empty, even] using same
    · simp only [binaryCode, if_neg empty, if_neg even, List.cons.injEq,
        Option.some.injEq] at same
      rcases same with ⟨left, right, _⟩
      unfold supportRow at left ⊢
      unfold oddRoot at left
      unfold oddSecondCharge at right
      by_cases last : m ∉ H <;> by_cases first : 1 ∉ H <;>
        by_cases jmem : j.val ∈ H <;> by_cases lmem : l.val ∈ H <;>
        simp_all only [if_pos, if_neg, Finset.mem_insert, Finset.mem_erase] <;>
        split_ifs at left right <;> simp_all <;> grind

private theorem support_charge (m : ℕ) (H : Finset ℕ)
    (inside : ∀ h ∈ H, h ≤ m) (j : Phase m) :
    windowCharge (2 * m - 2) m (supportRow H) j = supportRow H j.val := by
  unfold windowCharge
  split_ifs with small
  · rfl
  · have absent : j.val ∉ H := by intro mem; have := inside j.val mem; omega
    simp [supportRow, absent]

private theorem binary_script_code (m : ℕ) (hm : 5 ≤ m) (H : Finset ℕ)
    (inside : ∀ h ∈ H, 1 ≤ h ∧ h ≤ m)
    (v : ZMod 2) (j : Phase m) (s : ℕ) (hs : s < 2 * m - 2) :
    endpointDifferences (some v)
      ((scriptArchive (binaryWords m H) (some ⟨v, -j, s⟩)).map Prod.snd) = binaryCode m H j := by
  classical
  have zero : 0 ∉ H := by intro mem; have := inside 0 mem; omega
  by_cases empty : H = ∅
  · simp [binaryWords, binaryCode, empty, scriptArchive, endpointDifferences]
  · by_cases even : Even H.card
    · have sum : (∑ h ∈ Finset.range (m + 1), supportRow H h) = 0 :=
        (support_sum m H (fun h hh => (inside h hh).2)).trans (Even.natCast_zmod_two even)
      obtain ⟨inverse, head, _, _⟩ := short_window_charge_inverse (2 * m - 2)
        (by omega) m (by omega) (by omega) (supportRow H) sum
      have headZero : prefixWord m (supportRow H) ⟨0, by omega⟩ = false :=
        head.mpr (by simp [supportRow, zero])
      have step := (short_safe_execution (2 * m - 2) (by omega) m (by omega)
        (by omega) (prefixWord m (supportRow H)) v (-j) s hs (Or.inr headZero)).1
      rw [inverse, support_charge m H (fun h hh => (inside h hh).2)] at step
      simp [binaryWords, binaryCode, empty, even, scriptArchive, step,
        endpointReading, endpointDifferences]
    · obtain ⟨rootSum, secondSum, rootZero⟩ := odd_rows m hm H inside even
      obtain ⟨rootInv, rootHead, rootLast, _⟩ := short_window_charge_inverse
        (2 * m - 2) (by omega) m (by omega) (by omega) (supportRow (oddRoot m H)) rootSum
      obtain ⟨secondInv, secondHead, _, _⟩ := short_window_charge_inverse
        (2 * m - 2) (by omega) m (by omega) (by omega) (supportRow (oddSecond m H)) secondSum
      have headZero := rootHead.mpr rootZero
      obtain ⟨rootStep, rootTail⟩ := InternalZeroSafety.internal_zero_execution
        (2 * m - 2) (by omega) m (by omega) (prefixWord m (supportRow (oddRoot m H)))
        ⟨0, by omega⟩ headZero v (-j) s hs (Or.inr headZero)
      have rootInside : ∀ h ∈ oddRoot m H, h ≤ m := by
        intro h hh
        unfold oddRoot at hh
        by_cases last : m ∉ H
        · rw [if_pos last] at hh
          rcases Finset.mem_insert.mp hh with rfl | hh
          · omega
          · exact (inside h hh).2
        · rw [if_neg last] at hh
          by_cases first : 1 ∉ H
          · rw [if_pos first] at hh
            rcases Finset.mem_insert.mp hh with rfl | hh
            · omega
            · exact (inside h hh).2
          · rw [if_neg first] at hh
            exact (inside h (Finset.mem_of_mem_erase hh)).2
      rw [rootInv, support_charge m _ rootInside] at rootStep
      have secondStep : runBits (2 * m - 2) (prefixWord m (supportRow (oddSecond m H)))
          (some ⟨v + supportRow (oddRoot m H) j.val, -j + (m : ℕ),
            tailAfter 0 (prefixWord m (supportRow (oddRoot m H)))⟩) =
          some ⟨v + supportRow (oddRoot m H) j.val + oddSecondCharge m H j.val,
            -j + (m : ℕ) + (m : ℕ), tailAfter 0 (prefixWord m (supportRow (oddSecond m H)))⟩ := by
        have tailBound : tailAfter 0 (prefixWord m (supportRow (oddRoot m H))) < 2 * m - 2 := by
          change tailAfter 0 (prefixWord m (supportRow (oddRoot m H))) ≤ m - 1 at rootTail
          omega
        have step : runBits (2 * m - 2) (prefixWord m (supportRow (oddSecond m H)))
            (some ⟨v + supportRow (oddRoot m H) j.val, -j + (m : ℕ),
              tailAfter 0 (prefixWord m (supportRow (oddRoot m H)))⟩) =
            some ⟨v + supportRow (oddRoot m H) j.val +
              wordIncrement (2 * m - 2) (-j + (m : ℕ)) (prefixWord m (supportRow (oddSecond m H))),
              -j + (m : ℕ) + (m : ℕ), tailAfter 0 (prefixWord m (supportRow (oddSecond m H)))⟩ := by
          by_cases last : m ∉ H
          · have marked : prefixWord m (supportRow (oddSecond m H)) ⟨1, by omega⟩ = false := by
              simp only [oddSecond, if_pos last, prefixWord, Fin.val_mk, Finset.sum_range_succ,
                Finset.range_zero, Finset.sum_empty]
              simp [supportRow, CharTwo.add_self_eq_zero]
            exact (InternalZeroSafety.internal_zero_execution (2 * m - 2) (by omega)
              m (by omega) _ ⟨1, by omega⟩ marked _ _ _ tailBound
              (Or.inl (by change tailAfter 0 (prefixWord m (supportRow (oddRoot m H))) + 1 < 2 * m - 2; omega))).1
          · by_cases first : 1 ∉ H
            · have clear : prefixWord m (supportRow (oddSecond m H)) ⟨0, by omega⟩ = false :=
                secondHead.mpr (by simp [oddSecond, last, first, supportRow, show (0 : ℕ) ≠ m by omega])
              exact (short_safe_execution (2 * m - 2) (by omega) m (by omega)
                (by omega) _ _ _ _ tailBound (Or.inr clear)).1
            · have tailZero : tailAfter 0 (prefixWord m (supportRow (oddRoot m H))) = 0 := by
                have lastZero := rootLast.mpr (by simp [supportRow, oddRoot, last, first])
                obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
                cases hn
                exact last_false_tail n _ 0 lastZero
              exact (short_safe_execution (2 * m - 2) (by omega) m (by omega)
                (by omega) _ _ _ _ tailBound (Or.inl tailZero)).1
        have phase : -j + (m : ℕ) = -(j - (m : ℕ)) := by ring
        rw [phase, secondInv, odd_second_charge m hm] at step
        simpa only [← phase] using step
      simp [binaryWords, binaryCode, empty, even, scriptArchive, rootStep,
        secondStep, endpointReading, endpointDifferences]

/-- Correctness on every actual history with the specified saved INITIAL value. -/
def FiberCorrect {Y : Type*} (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (v : ZMod 2) (d : ℕ)
    (π : NarrowWindowCost.Selector m Y) : Prop :=
  ∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
    let w := history.flatMap (fun a => List.ofFn a.val)
    NarrowWindowCost.output (2 * m - 2) (by omega) w = some v →
    ∃ c ≤ d, NarrowWindowCost.execute (2 * m - 2) (by omega) π d w (some v) [] =
      some (f (OriginalRecord (2 * m - 2) (by omega) w), c)

private theorem binary_one_block_necessary {Y : Type*}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : Finset ℕ) (inside : ∀ h ∈ H, 1 ≤ h ∧ h ≤ m)
    (nonempty : H.Nonempty) (f : Option (LiveRecord (2 * m - 2)) → Y)
    (label : ZMod 2 → ZMod 2 → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = label v (supportRow H j.val))
    (v : ZMod 2) (distinct : label v 0 ≠ label v 1)
    (π : NarrowWindowCost.Selector m Y) (correct : FiberCorrect m hm alphabet f v 1 π) :
    ∃ W : Fin m → Bool, π (some v) [] = .inr W ∧
      W ⟨0, by omega⟩ = false ∧
      (∀ j : Phase m, wordIncrement (2 * m - 2) (-j) W = supportRow H j.val) ∧
      Even H.card := by
  classical
  let k := 2 * m - 2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have gcdOne := FourLabelPaidFeedback.coprime m hm
  have native (j : Phase m) : ∃ c, OriginalExecutionBridge.NativeExecute π 1
      (some ⟨v, -j, 0⟩) (some v) [] = some (label v (supportRow H j.val), c) := by
    obtain ⟨c, _, ex⟩ := OwnPathCharges.native_fiber k m hk (by omega) alphabet f v 1 π
      correct (-j) 0 (by dsimp [k]; omega) (by rw [gcdOne]; exact one_dvd _)
    rw [target v j 0 (by omega)] at ex
    exact ⟨c, ex⟩
  obtain ⟨h, hmem⟩ := nonempty
  have hb := inside h hmem
  have value : ((h : ℕ) : Phase m).val = h := ZMod.val_natCast_of_lt (by omega)
  let outside : Phase m := ((m + 1 : ℕ) : Phase m)
  have outsideVal : outside.val = m + 1 := ZMod.val_natCast_of_lt (by omega)
  have outsideMem : m + 1 ∉ H := by intro mem; have := inside _ mem; omega
  have outsideRow : supportRow H outside.val = 0 := by simp [outsideVal, supportRow, outsideMem]
  have memberRow : supportRow H ((h : ℕ) : Phase m).val = 1 := by simp [value, supportRow, hmem]
  cases chosen : π (some v) [] with
  | inl y =>
    obtain ⟨c, ex⟩ := native outside
    obtain ⟨c', ey⟩ := native (h : ℕ)
    simp only [GlobalPresetObstruction.native_succ, chosen, outsideRow, memberRow,
      Option.some.injEq, Prod.mk.injEq] at ex ey
    exact False.elim (distinct (ex.1.symm.trans ey.1))
  | inr W =>
    have safe : runAdmissible (k - 1) (k - 1 - 0) m W = true := by
      apply runAdmissible_eq_true_of_length_le <;> dsimp [k] <;> omega
    have separates (j l : Phase m)
        (same : wordIncrement k (-j) W = wordIncrement k (-l) W) :
        label v (supportRow H j.val) = label v (supportRow H l.val) := by
      obtain ⟨c, ex⟩ := native j
      obtain ⟨c', ey⟩ := native l
      exact OwnPathCharges.charge_separates k m hk π 1 v (-j) (-l) 0
        (by dsimp [k]; omega) (some v) [] _ _ c c' ex ey (by
          intro t ht
          have : t = 0 := by omega
          subst t
          simpa only [OwnPathCharges.ownCharge, chosen, if_pos safe] using same)
    have outsideCharge : wordIncrement k (-outside) W = 0 := by
      rw [increment_derivative k (by dsimp [k]; omega) m (by dsimp [k]; omega), outsideVal]
      simp [extendedBit, show ¬ m + 1 < m by omega, show ¬ m + 1 - 1 < m by omega]
    have memberCharge : wordIncrement k (-((h : ℕ) : Phase m)) W = 1 := by
      have notZero : wordIncrement k (-((h : ℕ) : Phase m)) W ≠ 0 := by
        intro eq
        have bad := separates outside (h : ℕ) (outsideCharge.trans eq.symm)
        rw [outsideRow, memberRow] at bad
        exact distinct bad
      have bound := ZMod.val_lt (wordIncrement k (-((h : ℕ) : Phase m)) W)
      have nonzero := (ZMod.val_ne_zero _).mpr notZero
      exact ZMod.val_injective 2 (by change _ = 1; omega)
    have charges (j : Phase m) : wordIncrement k (-j) W = supportRow H j.val := by
      by_cases mem : j.val ∈ H
      · have notZero : wordIncrement k (-j) W ≠ 0 := by
          intro eq
          have bad := separates outside j (outsideCharge.trans eq.symm)
          rw [outsideRow, show supportRow H j.val = 1 from if_pos mem] at bad
          exact distinct bad
        have bound := ZMod.val_lt (wordIncrement k (-j) W)
        have nonzero := (ZMod.val_ne_zero _).mpr notZero
        rw [supportRow, if_pos mem]
        exact ZMod.val_injective 2 (by change _ = 1; omega)
      · have notOne : wordIncrement k (-j) W ≠ 1 := by
          intro eq
          have bad := separates j (h : ℕ) (eq.trans memberCharge.symm)
          rw [memberRow, show supportRow H j.val = 0 from if_neg mem] at bad
          exact distinct bad
        rw [supportRow, if_neg mem]
        have bound := ZMod.val_lt (wordIncrement k (-j) W)
        have notVal : (wordIncrement k (-j) W).val ≠ 1 := by
          intro eq
          exact notOne (ZMod.val_injective 2 (by change _ = 1; exact eq))
        exact ZMod.val_injective 2 (by change _ = 0; omega)
    have zero : 0 ∉ H := by intro mem; have := inside 0 mem; omega
    have headZero : W ⟨0, by omega⟩ = false := by
      have eq := charges 0
      rw [increment_derivative k (by dsimp [k]; omega) m (by dsimp [k]; omega)] at eq
      simpa [extendedBit, bitScalar, supportRow, zero, show 0 < m by omega] using eq
    have : NeZero (k + 1) := ⟨by omega⟩
    have total : (∑ j : Phase m, supportRow H j.val) = (H.card : ZMod 2) := by
      let e : Fin (k + 1) ≃ Phase m := (ZMod.finEquiv (k + 1)).toEquiv
      rw [← e.sum_comp]
      have val (j : Fin (k + 1)) : (e j).val = j.val := rfl
      simp only [val]
      rw [Fin.sum_univ_eq_sum_range]
      exact support_sum k H (by intro n hn; have := inside n hn; dsimp [k]; omega)
    have parity := GlobalPresetObstruction.charge_even k m hk 0 W
    simp only [add_zero] at parity
    simp_rw [charges] at parity
    rw [total] at parity
    exact ⟨W, rfl, headZero, charges, (ZMod.natCast_eq_zero_iff_even.mp parity)⟩

private theorem binary_zero_block_necessary {Y : Type*}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : Finset ℕ) (inside : ∀ h ∈ H, 1 ≤ h ∧ h ≤ m)
    (f : Option (LiveRecord (2 * m - 2)) → Y) (label : ZMod 2 → ZMod 2 → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = label v (supportRow H j.val))
    (v : ZMod 2) (distinct : label v 0 ≠ label v 1)
    (π : NarrowWindowCost.Selector m Y) (correct : FiberCorrect m hm alphabet f v 0 π) : H = ∅ := by
  classical
  by_contra notEmpty
  obtain ⟨h, hmem⟩ := Finset.nonempty_iff_ne_empty.mpr notEmpty
  have hb := inside h hmem
  have value : ((h : ℕ) : Phase m).val = h := ZMod.val_natCast_of_lt (by omega)
  have gcdOne := FourLabelPaidFeedback.coprime m hm
  have native (j : Phase m) : ∃ c, OriginalExecutionBridge.NativeExecute π 0
      (some ⟨v, -j, 0⟩) (some v) [] = some (label v (supportRow H j.val), c) := by
    obtain ⟨c, _, ex⟩ := OwnPathCharges.native_fiber (2 * m - 2) m (by omega)
      (by omega) alphabet f v 0 π correct (-j) 0 (by omega)
      (by rw [gcdOne]; exact one_dvd _)
    rw [target v j 0 (by omega)] at ex
    exact ⟨c, ex⟩
  obtain ⟨c, ex⟩ := native 0
  obtain ⟨c', ey⟩ := native (h : ℕ)
  have same : OriginalExecutionBridge.NativeExecute (k := 2 * m - 2) π 0 (some ⟨v, -0, 0⟩) (some v) [] =
      OriginalExecutionBridge.NativeExecute π 0 (some ⟨v, -((h : ℕ) : Phase m), 0⟩) (some v) [] := rfl
  rw [ex, ey] at same
  have zero : 0 ∉ H := by intro mem; have := inside 0 mem; omega
  exact distinct (by simpa [supportRow, zero, value, hmem] using
    (Prod.mk.inj (Option.some.inj same)).1)

/-- The complete binary-support scripts, including all boundary and donor phases.
The same words work for both free values; the label map may depend on that value. -/
theorem original_first_window_binary_stream {Y : Type*}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (H : Finset ℕ) (inside : ∀ h ∈ H, 1 ≤ h ∧ h ≤ m)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (label : ZMod 2 → ZMod 2 → Y)
    (target : ∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = label v (supportRow H j.val)) :
    OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (binaryCost H) ∧
    (binaryWords m H).length = binaryCost H ∧
    (∀ (v : ZMod 2) (j : Phase m) (s : ℕ), s < 2 * m - 2 →
      endpointDifferences (some v)
        ((scriptArchive (binaryWords m H) (some ⟨v, -j, s⟩)).map Prod.snd) = binaryCode m H j ∧
      (scriptArchive (binaryWords m H) (some ⟨v, -j, s⟩)).length = binaryCost H ∧
      ((scriptArchive (binaryWords m H) (some ⟨v, -j, s⟩)).flatMap
        (fun a => List.ofFn a.1)).length = binaryCost H * m) ∧
    (∀ (v : ZMod 2), label v 0 ≠ label v 1 →
      ∀ (π : NarrowWindowCost.Selector m Y), FiberCorrect m hm alphabet f v 0 π → H = ∅) ∧
    (H.Nonempty → ∀ (v : ZMod 2), label v 0 ≠ label v 1 →
      ∀ (π : NarrowWindowCost.Selector m Y), FiberCorrect m hm alphabet f v 1 π →
      ∃ W : Fin m → Bool, π (some v) [] = .inr W ∧
        W ⟨0, by omega⟩ = false ∧
        (∀ j : Phase m, wordIncrement (2 * m - 2) (-j) W = supportRow H j.val) ∧
        Even H.card) := by
  classical
  have count : (binaryWords m H).length = binaryCost H := by
    unfold binaryWords binaryCost
    split_ifs <;> rfl
  let decode (v : ZMod 2) (ar : NarrowWindowCost.Archive m) : Y :=
    if h : ∃ j, binaryCode m H j = endpointDifferences (some v) (ar.map Prod.snd)
    then label v (supportRow H (Classical.choose h).val) else f none
  have feasible : OriginalPresetFeasible (2 * m - 2) m (by omega) alphabet f (binaryCost H) := by
    rw [← count]
    apply script_global_preset (2 * m - 2) m (by omega) (by omega) alphabet f (binaryWords m H) decode
    intro v phase s hs
    have readings := binary_script_code m hm H inside v (-phase) s hs
    simp only [neg_neg] at readings
    have existsPhase : ∃ j, binaryCode m H j = endpointDifferences (some v)
        ((scriptArchive (binaryWords m H) (some ⟨v, phase, s⟩)).map Prod.snd) :=
      ⟨-phase, readings.symm⟩
    dsimp only [decode]
    rw [dif_pos existsPhase]
    have separated := binary_separates m hm H inside _ (-phase)
      ((Classical.choose_spec existsPhase).trans readings)
    rw [separated]
    simpa only [neg_neg] using (target v (-phase) s hs).symm
  refine ⟨feasible, count, ?_, ?_, ?_⟩
  · intro v j s hs
    refine ⟨binary_script_code m hm H inside v j s hs, ?_, ?_⟩
    · exact (script_length (binaryWords m H) (some ⟨v, -j, s⟩)).trans count
    · change (archiveWords (scriptArchive (binaryWords m H) (some ⟨v, -j, s⟩))).length = _
      rw [archive_length]
      have blocks : (scriptArchive (binaryWords m H) (some ⟨v, -j, s⟩)).length = binaryCost H := by
        unfold binaryWords
        split_ifs <;> simp [scriptArchive, binaryCost, *]
      rw [blocks, Nat.mul_comm]
  · intro v distinct π correct
    exact binary_zero_block_necessary m hm alphabet H inside f label target v distinct π correct
  · intro nonempty v distinct π correct
    exact binary_one_block_necessary m hm alphabet H inside nonempty f label target v distinct π correct

#print axioms original_first_window_binary_stream

#print axioms original_first_window_three_block_stream
end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FirstWindowBoundaryAttainment
