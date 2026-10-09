/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Prefix-parity inverses realize short-window charges by actual shared endpoint words. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.CoprimeSingletonLower

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse

open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells
open scoped BigOperators

/-- The literal bit is one exactly when the prefix charge is nonzero. -/
def prefixWord (m : ℕ) (q : ℕ → ZMod 2) : Fin m → Bool :=
  fun i => decide ((∑ h ∈ Finset.range (i.val + 1), q h) ≠ 0)

/-- The ordered row occupies offsets zero through `m`; all other phases have
zero charge. Translating the argument rotates the same physical window. -/
def windowCharge (k m : ℕ) (q : ℕ → ZMod 2) (j : ZMod (k + 1)) : ZMod 2 :=
  if j.val ≤ m then q j.val else 0

def bitScalar (b : Bool) : ZMod 2 := if b then 1 else 0

def extendedBit {m : ℕ} (w : Fin m → Bool) (i : ℕ) : ZMod 2 :=
  if h : i < m then bitScalar (w ⟨i, h⟩) else 0

private theorem scalar_decide (x : ZMod 2) : bitScalar (decide (x ≠ 0)) = x := by
  fin_cases x
  · rfl
  · rfl

private theorem sum_pick {m : ℕ} (w : Fin m → Bool) (r : ℕ) :
    (∑ i : Fin m, if i.val = r then bitScalar (w i) else 0) = extendedBit w r := by
  classical
  by_cases hr : r < m
  · rw [Finset.sum_eq_single (⟨r, hr⟩ : Fin m)]
    · simp [extendedBit, hr]
    · intro i _ hi
      have hv : i.val ≠ r := fun h => hi (Fin.ext h)
      simp [hv]
    · simp
  · have hz : ∀ i : Fin m, i.val ≠ r := by intro i h; have := i.isLt; omega
    simp [hz, extendedBit, hr]

theorem increment_derivative (k : ℕ) (hk : 3 ≤ k) (m : ℕ)
    (hshort : m < k) (w : Fin m → Bool) (j : ZMod (k + 1)) :
    wordIncrement k (-j) w = extendedBit w j.val +
      (if j.val = 0 then 0 else extendedBit w (j.val - 1)) := by
  classical
  obtain ⟨edge, indexed, _, _⟩ :=
    CoprimeSingletonLower.singleton_tree_obstruction k 2 1 (by omega) (by omega)
      (by omega) (by omega) (by omega) false true (by decide) 0 false
  dsimp only at edge indexed
  have jbound : j.val ≤ k := by have := ZMod.val_lt j; omega
  have atom (i : Fin m) :
      (if w i then coefficient k (-j + (i.val : ℕ)) else 0) =
        (if i.val = j.val then bitScalar (w i) else 0) +
        (if i.val + 1 = j.val then bitScalar (w i) else 0) := by
    rw [← ZMod.natCast_zmod_val j, edge]
    have shift : -(j.val : ZMod (k + 1)) + (i.val : ℕ) + 1 =
        -(j.val : ZMod (k + 1)) + ((i.val + 1 : ℕ) : ZMod (k + 1)) := by
      push_cast; abel
    rw [shift, indexed j.val i.val jbound (by omega),
      indexed j.val (i.val + 1) jbound (by omega)]
    cases w i <;> simp [bitScalar]
  unfold wordIncrement
  simp_rw [atom]
  rw [Finset.sum_add_distrib, sum_pick]
  congr 1
  by_cases zero : j.val = 0
  · simp [zero]
  · have next : ∀ i : Fin m, i.val + 1 = j.val ↔ i.val = j.val - 1 := by
      intro i; omega
    simp_rw [next]
    rw [sum_pick, if_neg zero]

private theorem increment_injective (k : ℕ) (hk : 3 ≤ k) (m : ℕ)
    (hshort : m < k) (w z : Fin m → Bool)
    (same : ∀ j : ZMod (k + 1), wordIncrement k (-j) w = wordIncrement k (-j) z) :
    w = z := by
  have equalScalar : ∀ r (hr : r < m), bitScalar (w ⟨r, hr⟩) = bitScalar (z ⟨r, hr⟩) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
        intro hr
        have castVal : ((r : ℕ) : ZMod (k + 1)).val = r := by
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : r < k + 1)]
        have recurrence := same (r : ZMod (k + 1))
        rw [increment_derivative k hk m hshort, increment_derivative k hk m hshort,
          castVal] at recurrence
        have atR (a : Fin m → Bool) : extendedBit a r = bitScalar (a ⟨r, hr⟩) := by
          simp only [extendedBit, dif_pos hr]
        rw [atR w, atR z] at recurrence
        by_cases zero : r = 0
        · rw [if_pos zero, if_pos zero, add_zero, add_zero] at recurrence
          exact recurrence
        · have hp : r - 1 < m := by omega
          have atPrev (a : Fin m → Bool) :
              extendedBit a (r - 1) = bitScalar (a ⟨r - 1, hp⟩) := by
            simp only [extendedBit, dif_pos hp]
          rw [if_neg zero, if_neg zero, atPrev w, atPrev z,
            ih (r - 1) (by omega) hp] at recurrence
          exact add_right_cancel recurrence
  funext i
  have h := equalScalar i.val i.isLt
  cases hw : w i <;> cases hz : z i <;> simp [hw, hz, bitScalar] at h ⊢

/-- Every even short-window charge has its literal prefix-parity inverse.
The first and last bits are the two endpoint charges of that same row. -/
theorem short_window_charge_inverse (k : ℕ) (hk : 3 ≤ k) (m : ℕ)
    (hm : 1 ≤ m) (hshort : m < k) (q : ℕ → ZMod 2)
    (evenCharge : ∑ h ∈ Finset.range (m + 1), q h = 0) :
    (∀ j : ZMod (k + 1), wordIncrement k (-j) (prefixWord m q) =
      windowCharge k m q j) ∧
    (prefixWord m q ⟨0, by omega⟩ = false ↔ q 0 = 0) ∧
    (prefixWord m q ⟨m - 1, by omega⟩ = false ↔ q m = 0) ∧
    (∀ w : Fin m → Bool,
      (∀ j : ZMod (k + 1), wordIncrement k (-j) w = windowCharge k m q j) →
      w = prefixWord m q) := by
  have prefixEval (i : ℕ) (hi : i < m) :
      extendedBit (prefixWord m q) i = ∑ h ∈ Finset.range (i + 1), q h := by
    simp only [extendedBit, dif_pos hi, prefixWord]
    exact scalar_decide _
  have terminal : (∑ h ∈ Finset.range m, q h) = q m := by
    rw [Finset.sum_range_succ] at evenCharge
    exact (eq_neg_of_add_eq_zero_left evenCharge).trans (ZMod.neg_eq_self_mod_two _)
  have inverse : ∀ j : ZMod (k + 1), wordIncrement k (-j) (prefixWord m q) =
      windowCharge k m q j := by
    intro j
    rw [increment_derivative k hk m hshort]
    by_cases zero : j.val = 0
    · simp [windowCharge, zero, prefixEval 0 (by omega)]
    · rw [if_neg zero]
      by_cases inside : j.val < m
      · rw [prefixEval j.val inside, prefixEval (j.val - 1) (by omega)]
        have prev : j.val - 1 + 1 = j.val := by omega
        rw [prev, Finset.sum_range_succ]
        simp only [windowCharge, if_pos (by omega : j.val ≤ m)]
        linear_combination CharTwo.add_self_eq_zero (∑ h ∈ Finset.range j.val, q h)
      · by_cases last : j.val = m
        · rw [last, extendedBit, dif_neg (by omega : ¬ m < m),
            prefixEval (m - 1) (by omega)]
          have prev : m - 1 + 1 = m := by omega
          simp only [prev, zero_add, terminal, windowCharge, last, le_refl, if_true]
        · have outside : m < j.val := by omega
          simp [extendedBit, show ¬ j.val < m by omega,
            show ¬ j.val - 1 < m by omega, windowCharge, show ¬ j.val ≤ m by omega]
  refine ⟨inverse, ?_, ?_, ?_⟩
  · simp [prefixWord]
  · have prev : m - 1 + 1 = m := by omega
    simp [prefixWord, prev, terminal]
  · intro w hw
    exact increment_injective k hk m hshort w (prefixWord m q)
      (fun j => (hw j).trans (inverse j).symm)

#print axioms increment_derivative
#print axioms short_window_charge_inverse

theorem short_legal (k m : ℕ) (hk : 2 ≤ k) (hshort : m < k)
    (w : Fin m → Bool) : DBonacciAdmissible k m w := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact runAdmissible_eq_true_of_length_le a a m w (by omega) le_rfl

private theorem last_false_tail : ∀ (n : ℕ) (w : Fin (n + 1) → Bool) (s : ℕ),
    w (Fin.last n) = false → tailAfter s w = 0 := by
  intro n
  induction n with
  | zero => intro w s h; simpa [tailAfter, h] using h
  | succ n ih =>
      intro w s h
      simp only [tailAfter]
      apply ih
      exact h

theorem short_safe_execution (k : ℕ) (hk : 2 ≤ k) (m : ℕ)
    (hm : 1 ≤ m) (hshort : m < k) (w : Fin m → Bool)
    (v : ZMod 2) (phase : ZMod (k + 1)) (s : ℕ) (hs : s < k)
    (incoming : s = 0 ∨ w ⟨0, by omega⟩ = false) :
    runBits k w (some ⟨v, phase, s⟩) =
      some ⟨v + wordIncrement k phase w, phase + (m : ℕ), tailAfter 0 w⟩ ∧
    tailAfter 0 w < k := by
  have localSafe := short_legal k m hk hshort w
  have localScanner : runAdmissible (k - 1) (k - 1) m w = true := by
    obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simpa [ha, DBonacciAdmissible] using localSafe
  have scanner : runAdmissible (k - 1) (k - 1 - s) m w = true := by
    rcases incoming with rfl | headZero
    · simpa only [Nat.sub_zero] using localScanner
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      have headZero' : w 0 = false := headZero
      have tailSafe := runAdmissible_eq_true_of_length_le (k - 1) (k - 1) n
        (Fin.tail w) (by omega) le_rfl
      cases fuel : k - 1 - s <;> simpa [runAdmissible, headZero'] using tailSafe
  have sameTail : tailAfter s w = tailAfter 0 w := by
    rcases incoming with rfl | headZero
    · rfl
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      have headZero' : w 0 = false := headZero
      simp [tailAfter, headZero']
  have model := literal_block_execution k hk m w v phase s hs
  refine ⟨?_, ?_⟩
  · simpa only [scanner, if_true, sameTail] using model.1
  · rw [← sameTail]
    exact model.2 scanner

/-- Every row of the suffix is even. At a later seam at least one of the two
adjacent literal bits is zero; the head row's incoming seam is separate. -/
def safeRows (m : ℕ) : List (ℕ → ZMod 2) → Prop
  | [] => True
  | q :: rest => (∑ h ∈ Finset.range (m + 1), q h = 0) ∧
      (∀ r ∈ rest.head?, q m = 0 ∨ r 0 = 0) ∧ safeRows m rest

/-- One fixed list of complete literal actions, independent of value, phase,
tail and reply. Both original alphabets contain all these short words. -/
def chargeBlocks (k m : ℕ) (hk : 2 ≤ k) (hshort : m < k) (localAlphabet : Bool)
    (rows : List (ℕ → ZMod 2)) : List (AllowedBlock k m localAlphabet) :=
  rows.map (fun q => ⟨prefixWord m q, fun _ => short_legal k m hk hshort _⟩)

/-- The successive scalar endpoints predicted by the ordered charge rows.
After each paid block the relative INITIAL phase decreases by `m`. -/
def chargeArchive (k m : ℕ) : List (ℕ → ZMod 2) → ZMod 2 →
    ZMod (k + 1) → List (Option (ZMod 2))
  | [], _, _ => []
  | q :: rest, v, j =>
      let next := v + windowCharge k m q j
      some next :: chargeArchive k m rest next (j - (m : ℕ))

private theorem charge_archive_live (k m : ℕ) (rows : List (ℕ → ZMod 2))
    (v : ZMod 2) (j : ZMod (k + 1)) :
    (chargeArchive k m rows v j).length = rows.length ∧
    none ∉ chargeArchive k m rows v j := by
  induction rows generalizing v j with
  | nil => simp [chargeArchive]
  | cons q rows ih =>
      simpa [chargeArchive] using ih (v + windowCharge k m q j) (j - (m : ℕ))

/-- The prefix-parity words physically realize all prescribed endpoint rows
on one common suffix. Every actual issued block is counted, including an
all-one row when its incoming seam is cleared by the preceding terminal zero. -/
theorem actual_shared_charge_suffix (k : ℕ) (hk : 3 ≤ k) (m : ℕ)
    (hm : 1 ≤ m) (hshort : m < k) (localAlphabet : Bool)
    (rows : List (ℕ → ZMod 2)) (safe : safeRows m rows)
    (v : ZMod 2) (j : ZMod (k + 1)) (s : ℕ) (hs : s < k)
    (incoming : ∀ q ∈ rows.head?, s = 0 ∨ q 0 = 0)
    (actualPhase : Nat.gcd m (k + 1) ∣ (-j).val) :
    let actions := chargeBlocks k m (by omega) hshort localAlphabet rows
    actions.length = rows.length ∧
    fixedBlockArchive actions (some ⟨v, -j, s⟩) = chargeArchive k m rows v j ∧
    (fixedBlockArchive actions (some ⟨v, -j, s⟩)).length = rows.length ∧
    none ∉ fixedBlockArchive actions (some ⟨v, -j, s⟩) ∧
    ∃ (N : ℕ) (source : Fin N → Bool),
      m ∣ N ∧ DBonacciAdmissible k N source ∧
      runBits k source (some ⟨0, 0, 0⟩) = some ⟨v, -j, s⟩ ∧
      originalWordValue k source = v ∧ tailAfter 0 source = s ∧
      (∀ (b : ℕ) (hb : (b + 1) * m ≤ N),
        DBonacciAdmissible k m (fun i : Fin m =>
          source ⟨b * m + i.val, by nlinarith [i.isLt]⟩)) ∧
      fixedBlockArchive actions (runBits k source (some ⟨0, 0, 0⟩)) =
        chargeArchive k m rows v j := by
  dsimp only
  have exactArchive : fixedBlockArchive
      (chargeBlocks k m (by omega) hshort localAlphabet rows) (some ⟨v, -j, s⟩) =
      chargeArchive k m rows v j := by
    clear actualPhase
    induction rows generalizing v j s with
    | nil => rfl
    | cons q rows ih =>
        obtain ⟨evenCharge, seam, restSafe⟩ := safe
        obtain ⟨inverse, firstBit, lastBit, _⟩ :=
          short_window_charge_inverse k hk m hm hshort q evenCharge
        have incomingBit : s = 0 ∨ prefixWord m q ⟨0, by omega⟩ = false := by
          rcases incoming q (by simp) with cleared | chargeZero
          · exact Or.inl cleared
          · exact Or.inr (firstBit.mpr chargeZero)
        obtain ⟨step, tailSafe⟩ := short_safe_execution k (by omega) m hm hshort
          (prefixWord m q) v (-j) s hs incomingBit
        rw [inverse] at step
        have nextIncoming : ∀ r ∈ rows.head?, tailAfter 0 (prefixWord m q) = 0 ∨ r 0 = 0 := by
          intro r hr
          rcases seam r hr with terminalZero | firstZero
          · left
            have bitZero := lastBit.mpr terminalZero
            obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
            cases hn
            exact last_false_tail n (prefixWord (n + 1) q) 0 bitZero
          · exact Or.inr firstZero
        have next := ih restSafe (v + windowCharge k m q j) (j - (m : ℕ))
          (tailAfter 0 (prefixWord m q)) tailSafe nextIncoming
        have phase : -j + (m : ℕ) = -(j - (m : ℕ)) := by abel
        change endpointReading (runBits k (prefixWord m q) (some ⟨v, -j, s⟩)) ::
          fixedBlockArchive (chargeBlocks k m (by omega) hshort localAlphabet rows)
            (runBits k (prefixWord m q) (some ⟨v, -j, s⟩)) = _
        rw [step, phase]
        change some (v + windowCharge k m q j) :: _ =
          some (v + windowCharge k m q j) :: _
        exact congrArg (List.cons _) next
  obtain ⟨count, noBottom⟩ := charge_archive_live k m rows v j
  obtain ⟨N, source, divisible, legal, actual, value, tail, localBlocks⟩ :=
    joint_history_realization k m (by omega) hm v (-j) s hs actualPhase
  refine ⟨by unfold chargeBlocks; exact List.length_map _, exactArchive,
    exactArchive.symm ▸ count, exactArchive.symm ▸ noBottom,
    N, source, divisible, legal, actual, value, tail, localBlocks, ?_⟩
  rw [actual]
  exact exactArchive

#print axioms actual_shared_charge_suffix

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse
