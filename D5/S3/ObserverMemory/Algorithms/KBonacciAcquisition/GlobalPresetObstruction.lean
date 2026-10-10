/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Original preset streams cannot acquire unequal even interior masks in two blocks. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhysicalWindowDecoder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S0.Tower.DBonacci.Names
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge WindowChargeInverse
open scoped BigOperators

/-- A single literal stream, with stopping determined only by the free output
and this execution's chronological archive. -/
def presetSelector {m : ℕ} {Y : Type u} (stream : ℕ → Fin m → Bool)
    (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y) :
    NarrowWindowCost.Selector m Y := fun free archive =>
  match stop free archive with
  | some label => .inl label
  | none => .inr (stream archive.length)

/-- Correct bounded original execution on every actual source history. Every
issued word is paid, including rejection; the target uses the INITIAL record.
The same stream serves both free-value fibres and all stopping archives. -/
def OriginalPresetFeasible {Y : Type u} (k m : ℕ) (hk : 0 < k)
    (localAlphabet : Bool) (f : Option (LiveRecord k) → Y) (d : ℕ) : Prop :=
  ∃ (stream : ℕ → Fin m → Bool)
    (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y),
    (∀ free archive B, presetSelector stream stop free archive = .inr B →
      localAlphabet = true → DBonacciAdmissible k m B) ∧
    stop none [] = some (f none) ∧
    ∀ history : List (AllowedBlock k m localAlphabet),
      let w := history.flatMap (fun action => List.ofFn action.val)
      ∃ c ≤ d, NarrowWindowCost.execute k hk (presetSelector stream stop) d w
        (NarrowWindowCost.output k hk w) [] = some (f (OriginalRecord k hk w), c)

private theorem bit_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem even_mask_normal_form {P : Type*} [Fintype P]
    (a b h : P → ZMod 2)
    (odd : (Fintype.card P : ZMod 2) = 1)
    (evenB : ∑ p, b p = 0) (evenH : ∑ p, h p = 0)
    (blind : ∀ p, h p ≠ 0 → b p = 0)
    (refines : ∀ p q, a p = a q → b p = b q → h p = h q) :
    h = 0 ∨ h = fun p => a p * (1 + b p) +
      (∑ q, a q * (1 + b q)) * (1 + b p) := by
  classical
  let coeff (x : ZMod 2) : ZMod 2 :=
    if e : ∃ p, a p = x ∧ b p = 0 then h (Classical.choose e) else 0
  have value (p : P) (hb : b p = 0) : h p = coeff (a p) := by
    have e : ∃ q, a q = a p ∧ b q = 0 := ⟨p, rfl, hb⟩
    simp only [coeff, dif_pos e]
    exact refines p (Classical.choose e) (Classical.choose_spec e).1.symm
      (hb.trans (Classical.choose_spec e).2.symm)
  have outside (p : P) (hb : b p = 1) : h p = 0 := by
    by_contra ne
    have := blind p ne
    rw [hb] at this
    exact one_ne_zero this
  have form (p : P) : h p = coeff 0 * (1 + b p) +
      (coeff 1 + coeff 0) * (a p * (1 + b p)) := by
    rcases bit_cases (b p) with hb | hb
    · rw [value p hb, hb]
      rcases bit_cases (a p) with ha | ha <;> rw [ha]
      · simp
      · ring_nf
        simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, zero_add]
    · rw [outside p hb, hb]
      simp [CharTwo.add_self_eq_zero]
  have sumU : (∑ p, (1 + b p)) = (1 : ZMod 2) := by
    rw [Finset.sum_add_distrib, evenB]
    simpa using odd
  let sigma : ZMod 2 := ∑ p, a p * (1 + b p)
  have coefficientEq : coeff 0 = (coeff 1 + coeff 0) * sigma := by
    have sumForm := congrArg (fun g : P → ZMod 2 => ∑ p, g p) (funext form)
    rw [evenH, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sumU, mul_one] at sumForm
    have sumForm' : coeff 0 + (coeff 1 + coeff 0) * sigma = 0 := by
      exact sumForm.symm
    exact CharTwo.add_eq_zero.mp sumForm'
  rcases bit_cases (coeff 1 + coeff 0) with zero | one
  · left
    funext p
    have c0 : coeff 0 = 0 := by simpa only [zero, zero_mul] using coefficientEq
    rw [form, zero, c0]
    simp only [zero_mul, add_zero, Pi.zero_apply]
  · right
    funext p
    have c0 : coeff 0 = sigma := by simpa only [one, one_mul] using coefficientEq
    rw [form, one, c0, one_mul, add_comm]

theorem native_zero {Y : Type u} {k m : ℕ}
    (π : NarrowWindowCost.Selector m Y) (q : Option (LiveRecord k))
    (y : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m) :
    NativeExecute π 0 q y archive = match π y archive with
      | .inl z => some (z, 0)
      | .inr _ => none := by rfl

theorem native_succ {Y : Type u} {k m d : ℕ}
    (π : NarrowWindowCost.Selector m Y) (q : Option (LiveRecord k))
    (y : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m) :
    NativeExecute π (d + 1) q y archive = match π y archive with
      | .inl z => some (z, 0)
      | .inr B => Option.map (fun r => (r.1, r.2 + 1))
          (NativeExecute π d (runBits k B q) y
            (archive ++ [(B, endpointReading (runBits k B q))])) := by rfl

private theorem two_even_masks {P : Type*} [Fintype P]
    (a b h₀ h₁ : P → ZMod 2)
    (odd : (Fintype.card P : ZMod 2) = 1)
    (evenB : ∑ p, b p = 0) (even₀ : ∑ p, h₀ p = 0) (even₁ : ∑ p, h₁ p = 0)
    (blind₀ : ∀ p, h₀ p ≠ 0 → b p = 0) (blind₁ : ∀ p, h₁ p ≠ 0 → b p = 0)
    (refines₀ : ∀ p q, a p = a q → b p = b q → h₀ p = h₀ q)
    (refines₁ : ∀ p q, a p = a q → b p = b q → h₁ p = h₁ q) :
    h₀ = 0 ∨ h₁ = 0 ∨ h₀ = h₁ := by
  rcases even_mask_normal_form a b h₀ odd evenB even₀ blind₀ refines₀ with zero | form₀
  · exact Or.inl zero
  rcases even_mask_normal_form a b h₁ odd evenB even₁ blind₁ refines₁ with zero | form₁
  · exact Or.inr (Or.inl zero)
  exact Or.inr (Or.inr (form₀.trans form₁.symm))

theorem native_two_same {Y : Type u} (k m : ℕ) (hk : 2 ≤ k)
    (stream : ℕ → Fin m → Bool)
    (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y)
    (v : ZMod 2) (p q : ZMod (k + 1)) (s : ℕ) (hs : s < k)
    (first : wordIncrement k p (stream 0) = wordIncrement k q (stream 0))
    (second : wordIncrement k (p + (m : ℕ)) (stream 1) =
      wordIncrement k (q + (m : ℕ)) (stream 1)) :
    NativeExecute (presetSelector stream stop) 2 (some ⟨v, p, s⟩) (some v) [] =
      NativeExecute (presetSelector stream stop) 2 (some ⟨v, q, s⟩) (some v) [] := by
  have left := literal_block_execution k hk m (stream 0) v p s hs
  have right := literal_block_execution k hk m (stream 0) v q s hs
  cases root : stop (some v) [] with
  | some label =>
      simp only [native_succ (d := 1), presetSelector, root]
  | none =>
    simp only [native_succ (d := 1), presetSelector, root, List.length_nil, List.nil_append]
    rw [left.1, right.1]
    split_ifs with safe
    · have tailBound := left.2 safe
      simp only [endpointReading, first]
      cases next : stop (some v) [(stream 0, some (v + wordIncrement k q (stream 0)))] with
      | some label => simp only [native_succ (d := 0), presetSelector, next]
      | none =>
        simp only [native_succ (d := 0), presetSelector, next, List.length_cons, List.length_nil]
        have left₂ := literal_block_execution k hk m (stream 1)
          (v + wordIncrement k q (stream 0)) (p + (m : ℕ))
          (tailAfter s (stream 0)) tailBound
        have right₂ := literal_block_execution k hk m (stream 1)
          (v + wordIncrement k q (stream 0)) (q + (m : ℕ))
          (tailAfter s (stream 0)) tailBound
        rw [left₂.1, right₂.1]
        split_ifs <;> simp only [native_zero, endpointReading, second]
    · rfl

private theorem native_correct {Y : Type u} (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (localAlphabet : Bool) (f : Option (LiveRecord k) → Y) (d : ℕ)
    (stream : ℕ → Fin m → Bool)
    (stop : Option (ZMod 2) → NarrowWindowCost.Archive m → Option Y)
    (correct : ∀ history : List (AllowedBlock k m localAlphabet),
      let w := history.flatMap (fun action => List.ofFn action.val)
      ∃ c ≤ d, NarrowWindowCost.execute k (by omega) (presetSelector stream stop) d w
        (NarrowWindowCost.output k (by omega) w) [] =
        some (f (OriginalRecord k (by omega) w), c))
    (q : Option (LiveRecord k)) (hq : SourceRecord k m q) :
    ∃ c ≤ d, NativeExecute (presetSelector stream stop) d q (endpointReading q) [] =
      some (f q, c) := by
  obtain ⟨history, eq⟩ :=
    ((whole_first_zero_acquisition k m hk hm localAlphabet (fun _ => ())).1 q).mp hq
  obtain ⟨c, bound, success⟩ := correct history
  refine ⟨c, bound, ?_⟩
  rw [execute_same k m hk, output_record] at success
  have record := (record_history k m hk localAlphabet history).trans eq
  change OriginalRecord k (by omega) _ = q at record
  change NativeExecute _ _ (OriginalRecord k (by omega) _)
    (endpointReading (OriginalRecord k (by omega) _)) [] = _ at success
  simpa only [record] using success

theorem charge_even (k m : ℕ) (hk : 2 ≤ k)
    (shift : ZMod (k + 1)) (word : Fin m → Bool) :
    (∑ j : ZMod (k + 1), wordIncrement k (-j + shift) word) = 0 := by
  classical
  have : Fact (1 < k + 1) := ⟨by omega⟩
  have distinct : (0 : ZMod (k + 1)) ≠ -1 := by simp
  have coefficientSplit (p : ZMod (k + 1)) :
      coefficient k p = (if p = 0 then 1 else 0) + (if p = -1 then 1 else 0) := by
    by_cases zero : p = 0
    · subst p; simp [coefficient, distinct]
    · by_cases last : p = -1 <;> simp [coefficient, zero, last]
  have total : (∑ p : ZMod (k + 1), coefficient k p) = 0 := by
    simp_rw [coefficientSplit]
    rw [Finset.sum_add_distrib]
    simp [CharTwo.add_self_eq_zero]
  simp only [wordIncrement]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  by_cases selected : word i = true
  · simp only [selected, if_true]
    let e : ZMod (k + 1) ≃ ZMod (k + 1) :=
      { toFun := fun j => -j + shift + (i.val : ℕ)
        invFun := fun p => -p + shift + (i.val : ℕ)
        left_inv := by intro p; ring
        right_inv := by intro p; ring }
    exact (e.sum_comp (coefficient k)).trans total
  · simp [selected]

theorem second_charge_blind (m : ℕ) (hm : 5 ≤ m)
    (word : Fin m → Bool) (j : ZMod (2 * m - 2 + 1))
    (lo : 2 ≤ j.val) (hi : j.val < m) :
    wordIncrement (2 * m - 2) (-j + (m : ℕ)) word = 0 := by
  let T := 2 * m - 2 + 1
  have hT : T = 2 * m - 1 := by dsimp [T]; omega
  have repBound : j.val + m - 1 < T := by omega
  have castT : ((T : ℕ) : ZMod T) = 0 := by simp
  have castRel : (2 : ZMod T) * (m : ℕ) - 1 = 0 := by
    have two : 2 * m = T + 1 := by omega
    have cast := congrArg (fun n : ℕ => (n : ZMod T)) two
    push_cast at cast
    rw [castT, zero_add] at cast
    exact sub_eq_zero.mpr cast
  have representative : j - (m : ℕ) = ((j.val + m - 1 : ℕ) : ZMod T) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one]
    linear_combination -castRel
  have repVal : (j - (m : ℕ)).val = j.val + m - 1 := by
    rw [representative, ZMod.val_natCast_of_lt repBound]
  have phase : -j + (m : ℕ) = -(j - (m : ℕ)) := by ring
  rw [phase, increment_derivative (2 * m - 2) (by omega) m (by omega), repVal]
  simp only [extendedBit, dif_neg (by omega : ¬ j.val + m - 1 < m),
    if_neg (by omega : ¬ j.val + m - 1 = 0),
    dif_neg (by omega : ¬ j.val + m - 1 - 1 < m), add_zero]

/-- Unequal nonempty even interior supports in the two free-value fibres
cannot be acquired by one original GLOBAL stream within two paid blocks.
All actual INITIAL histories, both alphabets, rejection and own-archive early
stopping are quantified by OriginalPresetFeasible. -/
theorem original_global_two_block_obstruction {Y : Type u}
    (m : ℕ) (hm : 5 ≤ m) (localAlphabet : Bool)
    (H : ZMod 2 → Finset (ZMod (2 * m - 2 + 1)))
    (inside : ∀ v j, j ∈ H v → 2 ≤ j.val ∧ j.val < m)
    (even : ∀ v, Even (H v).card)
    (nonempty : ∀ v, (H v).Nonempty) (unequal : H 0 ≠ H 1)
    (A B : ZMod 2 → Y) (distinct : ∀ v, A v ≠ B v)
    (f : Option (LiveRecord (2 * m - 2)) → Y)
    (target : ∀ (v : ZMod 2) (j : ZMod (2 * m - 2 + 1)) (s : ℕ), s < 2 * m - 2 →
      f (some ⟨v, -j, s⟩) = if j ∈ H v then B v else A v) :
    ¬ OriginalPresetFeasible (2 * m - 2) m (by omega) localAlphabet f 2 := by
  classical
  intro feasible
  obtain ⟨stream, stop, _, _, correct⟩ := feasible
  let k := 2 * m - 2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have gcdOne : Nat.gcd m (k + 1) = 1 := by
    have hcop1 : Nat.Coprime m (m - 1) := by
      apply (Nat.coprime_self_sub_right (m := 1) (n := m) (by omega)).2
      exact Nat.coprime_one_right m
    have hcop : Nat.Coprime m (2 * m - 1) := by
      apply (Nat.coprime_sub_self_right (m := m) (n := 2 * m - 1) (by omega)).1
      simpa only [show 2 * m - 1 - m = m - 1 by omega] using hcop1
    have eq : k + 1 = 2 * m - 1 := by dsimp [k]; omega
    rw [eq]
    exact hcop
  let a : ZMod (k + 1) → ZMod 2 := fun j => wordIncrement k (-j) (stream 0)
  let b : ZMod (k + 1) → ZMod 2 := fun j => wordIncrement k (-j + (m : ℕ)) (stream 1)
  let mask (v : ZMod 2) (j : ZMod (k + 1)) : ZMod 2 := if j ∈ H v then 1 else 0
  have refineMask (v : ZMod 2) (p q : ZMod (k + 1))
      (ha : a p = a q) (hb : b p = b q) : mask v p = mask v q := by
    have legal (j : ZMod (k + 1)) : SourceRecord k m (some ⟨v, -j, 0⟩) := by
      simp only [SourceRecord, gcdOne, one_dvd, and_true]
      omega
    obtain ⟨c, _, left⟩ := native_correct k m hk (by omega) localAlphabet f 2
      stream stop correct (some ⟨v, -p, 0⟩) (legal p)
    obtain ⟨c', _, right⟩ := native_correct k m hk (by omega) localAlphabet f 2
      stream stop correct (some ⟨v, -q, 0⟩) (legal q)
    have execution := native_two_same k m hk stream stop v (-p) (-q) 0 (by omega) ha hb
    change NativeExecute _ _ _ (some v) [] = _ at left right
    rw [left, right] at execution
    have labels := congrArg (fun result : Option (Y × ℕ) => result.map Prod.fst) execution
    simp only [Option.map_some, Option.some.injEq] at labels
    rw [target v p 0 (by omega), target v q 0 (by omega)] at labels
    by_cases hp : p ∈ H v <;> by_cases hq : q ∈ H v
    · simp only [mask, if_pos hp, if_pos hq]
    · simp only [if_pos hp, if_neg hq] at labels
      exact False.elim (distinct v labels.symm)
    · simp only [if_neg hp, if_pos hq] at labels
      exact False.elim (distinct v labels)
    · simp only [mask, if_neg hp, if_neg hq]
  have odd : (Fintype.card (ZMod (k + 1)) : ZMod 2) = 1 := by
    rw [ZMod.card]
    apply Odd.natCast_zmod_two
    refine ⟨m - 1, ?_⟩
    dsimp [k]
    omega
  have evenMask (v : ZMod 2) : (∑ j, mask v j) = 0 := by
    simpa [mask] using (even v).natCast_zmod_two
  have blindMask (v : ZMod 2) (j : ZMod (k + 1)) (ne : mask v j ≠ 0) : b j = 0 := by
    have mem : j ∈ H v := by
      by_contra no
      exact ne (if_neg no)
    exact second_charge_blind m hm (stream 1) j (inside v j mem).1 (inside v j mem).2
  have notZero (v : ZMod 2) : mask v ≠ 0 := by
    obtain ⟨j, hj⟩ := nonempty v
    intro zero
    have impossible := congrFun zero j
    have bad : (1 : ZMod 2) = 0 := by
      simpa only [mask, if_pos hj, Pi.zero_apply] using impossible
    exact one_ne_zero bad
  have notEqual : mask 0 ≠ mask 1 := by
    intro eq
    apply unequal
    ext j
    have e := congrFun eq j
    by_cases h₀ : j ∈ H 0 <;> by_cases h₁ : j ∈ H 1 <;>
      simp_all [mask]
  rcases two_even_masks a b (mask 0) (mask 1) odd
      (charge_even k m hk (m : ℕ) (stream 1)) (evenMask 0) (evenMask 1)
      (blindMask 0) (blindMask 1) (refineMask 0) (refineMask 1) with zero | zero | equal
  · exact notZero 0 zero
  · exact notZero 1 zero
  · exact notEqual equal

#print axioms original_global_two_block_obstruction

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.GlobalPresetObstruction
