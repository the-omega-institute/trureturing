/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Own successful endpoint differences retain chronological support and distinguish initial labels. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.InternalZeroSafety
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalNarrowCost

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S0.Tower.DBonacci.Names
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge WindowChargeInverse

/-- Follow only this source's successfully issued endpoints. A stop or a
common rejecting action retires the source and pads every remaining coordinate
with zero. No endpoint on another branch is used. -/
def ownCharge {Y : Type u} {k m : ℕ} (π : NarrowWindowCost.Selector m Y) :
    ℕ → ZMod 2 → ZMod (k + 1) → ℕ → Option (ZMod 2) →
      NarrowWindowCost.Archive m → ℕ → ZMod 2
  | 0, _, _, _, _, _, _ => 0
  | b + 1, z, phase, s, free, archive, t =>
    match π free archive with
    | .inl _ => 0
    | .inr B =>
      if runAdmissible (k - 1) (k - 1 - s) m B then
        match t with
        | 0 => wordIncrement k phase B
        | t + 1 => ownCharge π b (z + wordIncrement k phase B)
            (phase + (m : ZMod (k + 1))) (tailAfter s B) free
            (archive ++ [(B, some (z + wordIncrement k phase B))]) t
      else 0

private theorem charge_support {Y : Type u} (k m : ℕ) (hk : 3 ≤ k)
    (short : m < k) (π : NarrowWindowCost.Selector m Y) (b t : ℕ)
    (z : ZMod 2) (phase : ZMod (k + 1)) (s : ℕ)
    (free : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m)
    (outside : (-phase - ((t * m : ℕ) : ZMod (k + 1))).val > m) :
    ownCharge π b z phase s free archive t = 0 := by
  induction b generalizing t z phase s archive with
  | zero => rfl
  | succ b ih =>
    cases chosen : π free archive with
    | inl y => simp only [ownCharge, chosen]
    | inr B =>
      simp only [ownCharge, chosen]
      split_ifs with safe
      · cases t with
        | zero =>
          simp only [Nat.zero_mul, Nat.cast_zero, sub_zero] at outside
          rw [show phase = -(-phase) by simp, increment_derivative k hk m short]
          simp only [extendedBit, dif_neg (by omega : ¬ (-phase).val < m),
            if_neg (by omega : ¬ (-phase).val = 0),
            dif_neg (by omega : ¬ (-phase).val - 1 < m), add_zero]
        | succ t =>
          apply ih
          convert outside using 1
          congr 1
          push_cast
          ring
      · rfl

theorem charge_separates {Y : Type u} (k m : ℕ) (hk : 2 ≤ k)
    (π : NarrowWindowCost.Selector m Y) (b : ℕ) :
    ∀ (z : ZMod 2) (p q : ZMod (k + 1)) (s : ℕ), s < k →
    ∀ (free : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m)
      (x y : Y) (cx cy : ℕ),
    NativeExecute π b (some ⟨z, p, s⟩) free archive = some (x, cx) →
    NativeExecute π b (some ⟨z, q, s⟩) free archive = some (y, cy) →
    (∀ t < b, ownCharge π b z p s free archive t =
      ownCharge π b z q s free archive t) → x = y := by
  induction b with
  | zero =>
    intro z p q s hs free archive x y cx cy ex ey codes
    have same : NativeExecute π 0 (some ⟨z, p, s⟩) free archive =
      NativeExecute π 0 (some ⟨z, q, s⟩) free archive := rfl
    rw [ex, ey] at same
    exact (Prod.mk.inj (Option.some.inj same)).1
  | succ b ih =>
    intro z p q s hs free archive x y cx cy ex ey codes
    cases chosen : π free archive with
    | inl label =>
      simp only [NativeExecute, chosen] at ex ey
      exact (Prod.mk.inj (Option.some.inj ex)).1.symm.trans
        (Prod.mk.inj (Option.some.inj ey)).1
    | inr B =>
      have left := literal_block_execution k hk m B z p s hs
      have right := literal_block_execution k hk m B z q s hs
      simp only [NativeExecute, chosen] at ex ey
      by_cases safe : runAdmissible (k - 1) (k - 1 - s) m B = true
      · rw [left.1, if_pos safe] at ex
        rw [right.1, if_pos safe] at ey
        have first := codes 0 (by omega)
        simp only [ownCharge, chosen, if_pos safe] at first
        have zsame : z + wordIncrement k p B = z + wordIncrement k q B := by rw [first]
        simp only [endpointReading] at ex ey
        rw [← zsame] at ey
        obtain ⟨rx, erx, hrx⟩ := Option.map_eq_some_iff.mp ex
        obtain ⟨ry, ery, hry⟩ := Option.map_eq_some_iff.mp ey
        have tailBound := left.2 safe
        have labels := ih (z + wordIncrement k p B) (p + (m : ℕ)) (q + (m : ℕ))
          (tailAfter s B) tailBound free
          (archive ++ [(B, some (z + wordIncrement k p B))]) rx.1 ry.1 rx.2 ry.2 erx ery
          (by
            intro t ht
            have e := codes (t + 1) (by omega)
            simpa only [ownCharge, chosen, if_pos safe, ← zsame] using e)
        exact (Prod.mk.inj hrx).1.symm.trans (labels.trans (Prod.mk.inj hry).1)
      · rw [left.1, if_neg safe] at ex
        rw [right.1, if_neg safe] at ey
        have same := ex.symm.trans ey
        exact (Prod.mk.inj (Option.some.inj same)).1

theorem native_fiber {Y : Type u} (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (alphabet : Bool) (f : Option (LiveRecord k) → Y) (v : ZMod 2) (d : ℕ)
    (π : NarrowWindowCost.Selector m Y)
    (correct : ∀ history : List (AllowedBlock k m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      NarrowWindowCost.output k (by omega) w = some v →
      ∃ c ≤ d, NarrowWindowCost.execute k (by omega) π d w (some v) [] =
        some (f (OriginalRecord k (by omega) w), c))
    (phase : ZMod (k + 1)) (s : ℕ) (hs : s < k)
    (actual : Nat.gcd m (k + 1) ∣ phase.val) :
    ∃ c ≤ d, NativeExecute π d (some ⟨v, phase, s⟩) (some v) [] =
      some (f (some ⟨v, phase, s⟩), c) := by
  obtain ⟨history, eq⟩ :=
    ((whole_first_zero_acquisition k m hk hm alphabet (fun _ => ())).1
      (some ⟨v, phase, s⟩)).mp ⟨hs, actual⟩
  have record : OriginalRecord k (by omega)
      (history.flatMap (fun a => List.ofFn a.val)) = some ⟨v, phase, s⟩ :=
    (record_history k m hk alphabet history).trans eq
  have readout : NarrowWindowCost.output k (by omega)
      (history.flatMap (fun a => List.ofFn a.val)) = some v := by
    rw [output_record]
    change endpointReading (OriginalRecord k (by omega) _) = some v
    rw [record]
    rfl
  obtain ⟨c, bound, success⟩ := correct history readout
  rw [execute_same k m hk] at success
  change NativeExecute π d (OriginalRecord k (by omega) _) (some v) [] =
    some (f (OriginalRecord k (by omega) _), c) at success
  rw [record] at success
  exact ⟨c, bound, success⟩

/-- The constant-label root is retired immediately. Otherwise each coordinate
is the own-path difference defined above, padded after retirement. -/
def phaseCharges {Y : Type u} {m : ℕ} (table : ZMod (2 * m - 2 + 1) → Y)
    (π : NarrowWindowCost.Selector m Y) (d t : ℕ)
    (j : ZMod (2 * m - 2 + 1)) : ZMod 2 := by
  classical
  exact if ∃ y, ∀ j, table j = y then 0 else ownCharge π d 0 (-j) 0 (some 0) [] t

private theorem root_zero {Y : Type u} (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (table : ZMod (k + 1) → Y) (π : NarrowWindowCost.Selector m Y) (d : ℕ)
    (native : ∀ j s, s < k → ∃ c,
      NativeExecute π d (some ⟨0, -j, s⟩) (some 0) [] = some (table j, c))
    (nonconstant : ¬ ∃ y, ∀ j, table j = y) (B : Fin m → Bool)
    (chosen : π (some 0) [] = .inr B) : B ⟨0, by omega⟩ = false := by
  cases head : B ⟨0, by omega⟩ with
  | false => rfl
  | true =>
    have rejected : runAdmissible (k - 1) (k - 1 - (k - 1)) m B = false := by
      obtain ⟨n, eq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      subst m
      have headEq : B 0 = true := head
      simp only [Nat.sub_self, runAdmissible, headEq, if_true]
    have merge (p q : ZMod (k + 1)) :
        NativeExecute π d (some ⟨0, -p, k - 1⟩) (some 0) [] =
        NativeExecute π d (some ⟨0, -q, k - 1⟩) (some 0) [] := by
      cases d with
      | zero => rfl
      | succ b =>
        simp only [NativeExecute, chosen]
        rw [(literal_block_execution k hk m B 0 (-p) (k - 1) (by omega)).1,
          (literal_block_execution k hk m B 0 (-q) (k - 1) (by omega)).1,
          rejected]
        rfl
    apply False.elim
    apply nonconstant
    refine ⟨table 0, ?_⟩
    intro j
    obtain ⟨c, ex⟩ := native j (k - 1) (by omega)
    obtain ⟨c', ey⟩ := native 0 (k - 1) (by omega)
    have same := merge j 0
    rw [ex, ey] at same
    exact (Prod.mk.inj (Option.some.inj same)).1

/-- A correct arbitrary original controller supplies a chronological supported
array on the whole near-critical phase family. Both original alphabets and
all inherited tails are present in the history premise. Equal padded columns
force equal INITIAL labels, including early stops and common rejection. -/
theorem original_adaptive_charge_array {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (alphabet : Bool)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (table : ZMod (2 * m - 2 + 1) → Y)
    (target : ∀ (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ),
      s < 2 * m - 2 → f (some ⟨v, -j, s⟩) = table j)
    (π : NarrowWindowCost.Selector m Y) (d : ℕ)
    (correct : ∀ history : List (AllowedBlock (2 * m - 2) m alphabet),
      let w := history.flatMap (fun a => List.ofFn a.val)
      NarrowWindowCost.output (2 * m - 2) (by omega) w = some 0 →
      ∃ c ≤ d, NarrowWindowCost.execute (2 * m - 2) (by omega) π d w (some 0) [] =
        some (f (OriginalRecord (2 * m - 2) (by omega) w), c)) :
    (∀ t j, m < (j - ((t * m : ℕ) : ZMod (2 * m - 2 + 1))).val →
      phaseCharges table π d t j = 0) ∧
    phaseCharges table π d 0 0 = 0 ∧
    (∀ j j', (∀ t < d, phaseCharges table π d t j = phaseCharges table π d t j') →
      table j = table j') := by
  classical
  let k := 2 * m - 2
  have hk : 3 ≤ k := by dsimp [k]; omega
  have short : m < k := by dsimp [k]; omega
  have gcdOne : Nat.gcd m (k + 1) = 1 := by
    have twice : Nat.gcd m (k + 1) ∣ 2 * m :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_left m (k + 1)) 2
    have one := Nat.dvd_sub twice (Nat.gcd_dvd_right m (k + 1))
    have difference : 2 * m - (k + 1) = 1 := by dsimp [k]; omega
    rw [difference] at one
    exact Nat.dvd_one.mp one
  have native (j : ZMod (k + 1)) (s : ℕ) (hs : s < k) :
      ∃ c, NativeExecute π d (some ⟨0, -j, s⟩) (some 0) [] = some (table j, c) := by
    obtain ⟨c, _, ex⟩ := native_fiber k m (by omega) (by omega) alphabet f 0 d π
      correct (-j) s hs (by rw [gcdOne]; exact one_dvd _)
    rw [target 0 j s hs] at ex
    exact ⟨c, ex⟩
  by_cases constant : ∃ y, ∀ j, table j = y
  · have isConstant := constant
    obtain ⟨y, labels⟩ := constant
    refine ⟨?_, ?_, ?_⟩
    · intro t j _; simp only [phaseCharges, if_pos isConstant]
    · simp only [phaseCharges, if_pos isConstant]
    · intro j j' _; exact (labels j).trans (labels j').symm
  · refine ⟨?_, ?_, ?_⟩
    · intro t j outside
      simp only [phaseCharges, if_neg constant]
      apply charge_support k m hk short π d t 0 (-j) 0 (some 0) []
      simpa only [neg_neg] using outside
    · simp only [phaseCharges, if_neg constant]
      cases d with
      | zero => rfl
      | succ b =>
        cases chosen : π (some 0) [] with
        | inl label => simp only [ownCharge, chosen]
        | inr B =>
          have headZero := root_zero k m (by omega) (by omega) table π (b + 1)
            native constant B chosen
          simp only [ownCharge, chosen]
          split_ifs
          · rw [neg_zero, show (0 : ZMod (k + 1)) = -0 by simp,
              increment_derivative k hk m short]
            simp only [ZMod.val_zero, extendedBit, dif_pos (by omega : 0 < m),
              bitScalar, headZero, Bool.false_eq_true, if_false, if_true, add_zero]
          · rfl
    · intro j j' codes
      obtain ⟨c, ex⟩ := native j 0 (by omega)
      obtain ⟨c', ey⟩ := native j' 0 (by omega)
      exact charge_separates k m (by omega) π d 0 (-j) (-j') 0 (by omega)
        (some 0) [] (table j) (table j') c c' ex ey (by
          intro t ht
          simpa only [phaseCharges, if_neg constant] using codes t ht)

#print axioms original_adaptive_charge_array
#print axioms charge_separates
end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OwnPathCharges
