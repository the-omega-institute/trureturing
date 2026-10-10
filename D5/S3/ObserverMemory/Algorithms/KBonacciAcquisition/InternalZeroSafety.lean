/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InternalZeroSafety
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InternalZeroSafety
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Internal zeros bound inherited runs and realize common charge archives across seams. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowChargeInverse
import Mathlib.Data.List.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety

open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells WindowChargeInverse
open scoped BigOperators

private theorem tail_growth : ∀ (n s : ℕ) (w : Fin n → Bool),
    tailAfter s w ≤ s + n := by
  intro n
  induction n with
  | zero => intro s w; simp [tailAfter]
  | succ n ih =>
      intro s w
      simp only [tailAfter]
      cases w 0 <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · have := ih 0 (Fin.tail w); omega
      · have := ih (s + 1) (Fin.tail w); omega

private theorem internal_zero_tail : ∀ (n : ℕ) (w : Fin n → Bool) (i : Fin n),
    w i = false → ∀ s : ℕ,
    tailAfter s w = tailAfter 0 w ∧ tailAfter 0 w ≤ n - 1 - i.val := by
  intro n
  induction n with
  | zero => intro w i; exact Fin.elim0 i
  | succ n ih =>
      intro w i hz s
      by_cases atHead : i.val = 0
      · have hi : i = 0 := Fin.ext atHead
        have headZero : w 0 = false := hi ▸ hz
        simp only [tailAfter, headZero, Bool.false_eq_true, ↓reduceIte]
        refine ⟨trivial, ?_⟩
        have bound := tail_growth n 0 (Fin.tail w)
        simpa only [Nat.zero_add, Nat.add_sub_cancel, atHead, Nat.sub_zero] using bound
      · let j : Fin n := ⟨i.val - 1, by have := i.isLt; omega⟩
        have ij : j.succ = i := Fin.ext (by simp [j]; omega)
        have zero : Fin.tail w j = false := by simpa only [Fin.tail, ij] using hz
        have h := ih (Fin.tail w) j zero
        simp only [tailAfter]
        refine ⟨(h _).1.trans (h _).1.symm, ?_⟩
        have bound := (h 0).2
        rw [(h _).1]
        dsimp [j] at bound
        omega

private theorem internal_zero_scanner : ∀ (n : ℕ) (w : Fin n → Bool)
    (i : Fin n) (k s : ℕ), 2 ≤ k → n < k → w i = false → s + i.val < k →
    runAdmissible (k - 1) (k - 1 - s) n w = true := by
  intro n
  induction n with
  | zero => intro w i; exact Fin.elim0 i
  | succ n ih =>
      intro w i k s hk hn hz incoming
      by_cases atHead : i.val = 0
      · have hi : i = 0 := Fin.ext atHead
        have headZero : w 0 = false := hi ▸ hz
        have rest := runAdmissible_eq_true_of_length_le (k - 1) (k - 1) n
          (Fin.tail w) (by omega) le_rfl
        cases fuel : k - 1 - s <;> simpa only [runAdmissible, headZero,
          Bool.false_eq_true, ↓reduceIte] using rest
      · let j : Fin n := ⟨i.val - 1, by have := i.isLt; omega⟩
        have ij : j.succ = i := Fin.ext (by simp [j]; omega)
        have zero : Fin.tail w j = false := by simpa only [Fin.tail, ij] using hz
        cases head : w 0 with
        | false =>
            have rest := ih (Fin.tail w) j k 0 hk (by omega) zero (by dsimp [j]; omega)
            cases fuel : k - 1 - s <;> simpa only [runAdmissible, head,
              Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] using rest
        | true =>
            have rest := ih (Fin.tail w) j k (s + 1) hk (by omega) zero
              (by dsimp [j]; omega)
            have fuel : k - 1 - s = (k - 1 - (s + 1)) + 1 := by omega
            rw [fuel]
            simpa only [runAdmissible, head, ↓reduceIte] using rest

/-- A marked zero inside a short literal block clears the inherited tail. The
incoming run need only reach that zero safely; a zero at the head instead
admits every legal inherited tail. No interior endpoint is observed. -/
theorem internal_zero_execution (k : ℕ) (hk : 2 ≤ k) (m : ℕ) (hshort : m < k)
    (w : Fin m → Bool) (i : Fin m) (zero : w i = false)
    (v : ZMod 2) (phase : ZMod (k + 1)) (s : ℕ) (hs : s < k)
    (incoming : s + i.val < k ∨ w ⟨0, by have := i.isLt; omega⟩ = false) :
    runBits k w (some ⟨v, phase, s⟩) =
      some ⟨v + wordIncrement k phase w, phase + (m : ℕ), tailAfter 0 w⟩ ∧
    tailAfter 0 w ≤ m - 1 - i.val := by
  have tail := internal_zero_tail m w i zero s
  refine ⟨?_, tail.2⟩
  rcases incoming with reaches | headZero
  · have scanner := internal_zero_scanner m w i k s hk hshort zero reaches
    simpa only [scanner, if_true, tail.1] using
      (literal_block_execution k hk m w v phase s hs).1
  · exact (short_safe_execution k hk m (by have := i.isLt; omega) hshort
      w v phase s hs (Or.inr headZero)).1

#print axioms internal_zero_execution

/-- One common list of literal words realizes even charge rows when marked
internal zeros are separated by at most `k` chronological positions. Every
complete block remains in the archive, including zero rows and the initial
clearing bit. Both alphabets and all jointly realizable live records occur. -/
theorem actual_internal_zero_charge_suffix (k : ℕ) (hk : 3 ≤ k) (m : ℕ)
    (hm : 1 ≤ m) (hshort : m < k) (localAlphabet : Bool)
    (marked : List ((ℕ → ZMod 2) × Fin m))
    (even : ∀ entry ∈ marked, ∑ h ∈ Finset.range (m + 1), entry.1 h = 0)
    (zero : ∀ entry ∈ marked, prefixWord m entry.1 entry.2 = false)
    (seams : marked.IsChain (fun a b => m + b.2.val ≤ k + a.2.val))
    (v : ZMod 2) (j : ZMod (k + 1)) (s : ℕ) (hs : s < k)
    (incoming : ∀ entry ∈ marked.head?, s + entry.2.val < k ∨ entry.1 0 = 0)
    (actualPhase : Nat.gcd m (k + 1) ∣ (-j).val) :
    let rows := marked.map Prod.fst
    let actions := chargeBlocks k m (by omega) hshort localAlphabet rows
    actions.length = marked.length ∧
    fixedBlockArchive actions (some ⟨v, -j, s⟩) = chargeArchive k m rows v j ∧
    (fixedBlockArchive actions (some ⟨v, -j, s⟩)).length = marked.length ∧
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
      (chargeBlocks k m (by omega) hshort localAlphabet (marked.map Prod.fst))
        (some ⟨v, -j, s⟩) = chargeArchive k m (marked.map Prod.fst) v j := by
    clear actualPhase
    induction marked generalizing v j s with
    | nil => rfl
    | cons entry rest ih =>
        have rowEven := even entry (by simp)
        have rowZero := zero entry (by simp)
        obtain ⟨inverse, firstBit, _, _⟩ :=
          short_window_charge_inverse k hk m hm hshort entry.1 rowEven
        have arrives : s + entry.2.val < k ∨
            prefixWord m entry.1 ⟨0, by omega⟩ = false := by
          rcases incoming entry (by simp) with reaches | headZero
          · exact Or.inl reaches
          · exact Or.inr (firstBit.mpr headZero)
        obtain ⟨step, tailBound⟩ := internal_zero_execution k (by omega) m hshort
          (prefixWord m entry.1) entry.2 rowZero v (-j) s hs arrives
        rw [inverse] at step
        obtain ⟨seam, restSeams⟩ := List.isChain_cons.mp seams
        have nextIncoming : ∀ next ∈ rest.head?,
            tailAfter 0 (prefixWord m entry.1) + next.2.val < k ∨ next.1 0 = 0 := by
          intro next hnext
          left
          have gap := seam next hnext
          have markBound := entry.2.isLt
          omega
        have next := ih (fun e he => even e (by simp [he]))
          (fun e he => zero e (by simp [he])) restSeams
          (v + windowCharge k m entry.1 j) (j - (m : ℕ))
          (tailAfter 0 (prefixWord m entry.1)) (by have := entry.2.isLt; omega)
          nextIncoming
        have phase : -j + (m : ℕ) = -(j - (m : ℕ)) := by abel
        change endpointReading (runBits k (prefixWord m entry.1) (some ⟨v, -j, s⟩)) ::
          fixedBlockArchive (chargeBlocks k m (by omega) hshort localAlphabet
            (rest.map Prod.fst)) (runBits k (prefixWord m entry.1) (some ⟨v, -j, s⟩)) = _
        rw [step, phase]
        exact congrArg (List.cons (some (v + windowCharge k m entry.1 j))) next
  obtain ⟨count, noBottom⟩ := charge_archive_live k m (marked.map Prod.fst) v j
  obtain ⟨N, source, divisible, legal, actual, value, tail, localBlocks⟩ :=
    joint_history_realization k m (by omega) hm v (-j) s hs actualPhase
  refine ⟨?_, exactArchive, ?_,
    exactArchive.symm ▸ noBottom, N, source, divisible, legal, actual, value,
    tail, localBlocks, ?_⟩
  · unfold chargeBlocks
    exact (List.length_map _).trans (List.length_map _)
  · rw [exactArchive, count, List.length_map]
  · rw [actual]
    exact exactArchive

#print axioms actual_internal_zero_charge_suffix

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety
