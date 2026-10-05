/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhaseRecovery
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/PhaseRecovery
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Safe literal KBonacci phase probes for block and single-bit alphabets. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.LiteralModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhaseRecovery

open D5.S0.Tower.DBonacci.Names
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open scoped BigOperators
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.LiteralModel

/- This model uses the original KBonacci recurrence, its fixed mod-two scalar,
legal-run language and endpoint alphabet. Its all-order results do not provide
a theorem for an arbitrary recurrence, scalar readout or controlled machine. -/

/-- A length-`m` probe containing exactly one true bit at the known offset `j`. -/
def isolatedProbe (m j : ℕ) : Fin m → Bool := fun i => decide (i.val = j)

/-- Repeated literal probes beginning with a zero are safe for every old legal
tail. Their endpoint increments are precisely the translated coefficient
samples used by the source phase protocol. The number of actions is `r`. -/
theorem isolated_probe_orbit_exact (k m : ℕ) (hk : 2 ≤ k) (j : ℕ)
    (hj : 1 ≤ j) (hjm : j < m) (r : ℕ)
    (v : ZMod 2) (phase : ZMod (k + 1)) (s : ℕ) (hs : s < k) :
    DBonacciAdmissible k m (isolatedProbe m j) ∧
    ∃ tail₀, tail₀ < k ∧
      (runBits k (isolatedProbe m j))^[r] (some ⟨v, phase, s⟩) =
        some ⟨v + ∑ i ∈ Finset.range r,
          coefficient k (phase + ((i * m + j : ℕ) : ZMod (k + 1))),
          phase + ((r * m : ℕ) : ZMod (k + 1)), tail₀⟩ := by
  have scanProbe : ∀ (n offset fuel maxTrue : ℕ),
      offset < n → 1 ≤ maxTrue → (offset = 0 → 1 ≤ fuel) →
      runAdmissible maxTrue fuel n (isolatedProbe n offset) = true := by
    intro n
    induction n with
    | zero => intro offset fuel maxTrue h; omega
    | succ n ih =>
        intro offset fuel maxTrue hoff hmax hhead
        cases offset with
        | zero =>
            obtain ⟨fuel₀, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
              (by have := hhead rfl; omega : fuel ≠ 0)
            have noMore : Fin.tail (isolatedProbe (n + 1) 0) = (fun _ : Fin n => false) := by
              funext i
              simp [Fin.tail, isolatedProbe]
            have head : isolatedProbe (n + 1) 0 0 = true := by simp [isolatedProbe]
            simp only [runAdmissible, head, ↓reduceIte]
            rw [noMore]
            exact D5.S0.Tower.DBonacci.Values.runAdmissible_all_false maxTrue fuel₀ n
        | succ offset =>
            have shifted : Fin.tail (isolatedProbe (n + 1) (offset + 1)) =
                isolatedProbe n offset := by
              funext i
              simp [Fin.tail, isolatedProbe]
            have tailSafe := ih offset maxTrue maxTrue (by omega) hmax (fun _ => hmax)
            have head : isolatedProbe (n + 1) (offset + 1) 0 = false := by simp [isolatedProbe]
            cases fuel <;>
              simp only [runAdmissible, head, Bool.false_eq_true, ↓reduceIte]
            all_goals
              change runAdmissible maxTrue maxTrue n
                (Fin.tail (isolatedProbe (n + 1) (offset + 1))) = true
              rw [shifted]
              exact tailSafe
  have scanned : ∀ fuel, runAdmissible (k - 1) fuel m (isolatedProbe m j) = true :=
    fun fuel => scanProbe m j fuel (k - 1) hjm (by omega) (by omega)
  have legal : DBonacciAdmissible k m (isolatedProbe m j) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simpa [hd, DBonacciAdmissible] using scanned (k - 1)
  have increment : ∀ phi : ZMod (k + 1),
      wordIncrement k phi (isolatedProbe m j) = coefficient k (phi + (j : ℕ)) := by
    intro phi
    unfold wordIncrement
    rw [Finset.sum_eq_single (⟨j, hjm⟩ : Fin m)]
    · simp [isolatedProbe]
    · intro i _ different
      have hval : i.val ≠ j := by
        intro h
        apply different
        exact Fin.ext h
      simp [isolatedProbe, hval]
    · simp
  have oneStep : ∀ value phi tail₀, tail₀ < k →
      runBits k (isolatedProbe m j) (some ⟨value, phi, tail₀⟩) =
        some ⟨value + coefficient k (phi + (j : ℕ)), phi + (m : ℕ),
          tailAfter tail₀ (isolatedProbe m j)⟩ ∧
      tailAfter tail₀ (isolatedProbe m j) < k := by
    intro value phi tail₀ htail
    have model := literal_block_execution k hk m (isolatedProbe m j) value phi tail₀ htail
    constructor
    · simpa only [scanned, ↓reduceIte, increment] using model.1
    · exact model.2 (scanned (k - 1 - tail₀))
  refine ⟨legal, ?_⟩
  induction r with
  | zero => exact ⟨s, hs, by simp⟩
  | succ r ih =>
      obtain ⟨tail₀, htail, actual⟩ := ih
      rw [Function.iterate_succ_apply', actual]
      obtain ⟨next, safe⟩ := oneStep
        (v + ∑ i ∈ Finset.range r,
          coefficient k (phase + ((i * m + j : ℕ) : ZMod (k + 1))))
        (phase + ((r * m : ℕ) : ZMod (k + 1))) tail₀ htail
      refine ⟨tailAfter tail₀ (isolatedProbe m j), safe, ?_⟩
      rw [next, Finset.sum_range_succ]
      have phaseArithmetic :
          phase + ((r * m : ℕ) : ZMod (k + 1)) + (m : ℕ) =
          phase + (((r + 1) * m : ℕ) : ZMod (k + 1)) := by push_cast; ring
      simp only [Nat.cast_add, add_assoc, phaseArithmetic]

#print axioms isolated_probe_orbit_exact

/-- The single-bit protocol literally issues a zero block and then a one block
in each pair. Each bit is a complete action when the block width is one. -/
def alternatingBitOrbit (k r : ℕ) (q : Option (LiveRecord k)) : Option (LiveRecord k) :=
  (fun current => runBits k (fun _ : Fin 1 => true)
    (runBits k (fun _ : Fin 1 => false) current))^[r] q

/-- For odd `T=k+1`, the actual `(01)^T` single-bit protocol is safe and its
acquired endpoints distinguish the initial ambient phase. Equal pair endpoints
are already sufficient, so the extra observed zero endpoints need no assumption. -/
theorem odd_single_bit_phase_recovery (k : ℕ) (hk : 2 ≤ k) (oddT : Odd (k + 1))
    (v₁ v₂ : ZMod 2) (phase₁ phase₂ : ZMod (k + 1))
    (s₁ s₂ : ℕ) (hs₁ : s₁ < k) (hs₂ : s₂ < k) :
    (∀ r, ∃ tail₀, tail₀ < k ∧
      alternatingBitOrbit k r (some ⟨v₁, phase₁, s₁⟩) =
        some ⟨v₁ + ∑ i ∈ Finset.range r,
          coefficient k (phase₁ + ((i * 2 + 1 : ℕ) : ZMod (k + 1))),
          phase₁ + ((r * 2 : ℕ) : ZMod (k + 1)), tail₀⟩) ∧
    ((∀ r, r ≤ k + 1 →
      endpointReading (alternatingBitOrbit k r (some ⟨v₁, phase₁, s₁⟩)) =
        endpointReading (alternatingBitOrbit k r (some ⟨v₂, phase₂, s₂⟩))) →
      phase₁ = phase₂) := by
  have literalPair : (fun current => runBits k (fun _ : Fin 1 => true)
      (runBits k (fun _ : Fin 1 => false) current)) = runBits k (isolatedProbe 2 1) := by
    funext current
    simp +unfoldPartialApp [runBits, List.ofFn_succ, isolatedProbe, Fin.tail, runWord]
  have actual : ∀ (v : ZMod 2) (phi : ZMod (k + 1)) (tail₀ : ℕ), tail₀ < k →
      ∀ r, ∃ tail₁, tail₁ < k ∧
        alternatingBitOrbit k r (some ⟨v, phi, tail₀⟩) =
          some ⟨v + ∑ i ∈ Finset.range r,
            coefficient k (phi + ((i * 2 + 1 : ℕ) : ZMod (k + 1))),
            phi + ((r * 2 : ℕ) : ZMod (k + 1)), tail₁⟩ := by
    intro v phi tail₀ htail r
    rw [alternatingBitOrbit, literalPair]
    exact (isolated_probe_orbit_exact k 2 hk 1 le_rfl (by omega) r v phi tail₀ htail).2
  have readings : ∀ (v : ZMod 2) (phi : ZMod (k + 1)) (tail₀ : ℕ), tail₀ < k →
      ∀ r, endpointReading (alternatingBitOrbit k r (some ⟨v, phi, tail₀⟩)) =
        some (v + ∑ i ∈ Finset.range r,
          coefficient k (phi + ((i * 2 + 1 : ℕ) : ZMod (k + 1)))) := by
    intro v phi tail₀ htail r
    obtain ⟨tail₁, _, run⟩ := actual v phi tail₀ htail r
    rw [run]
    rfl
  refine ⟨actual v₁ phase₁ s₁ hs₁, ?_⟩
  intro sameArchive
  have samples : ∀ i, i < k + 1 →
      coefficient k (phase₁ + ((i * 2 + 1 : ℕ) : ZMod (k + 1))) =
        coefficient k (phase₂ + ((i * 2 + 1 : ℕ) : ZMod (k + 1))) := by
    intro i hi
    have before := sameArchive i (by omega)
    have after := sameArchive (i + 1) (by omega)
    rw [readings v₁ phase₁ s₁ hs₁, readings v₂ phase₂ s₂ hs₂] at before after
    simp only [Option.some.injEq] at before after
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at after
    linear_combination after - before
  have unit : IsUnit (2 : ZMod (k + 1)) :=
    (ZMod.isUnit_iff_coprime 2 (k + 1)).mpr oddT.coprime_two_left
  have allSamples : ∀ offset : ZMod (k + 1),
      coefficient k (phase₁ + offset) = coefficient k (phase₂ + offset) := by
    intro offset
    let x : ZMod (k + 1) := (2 : ZMod (k + 1))⁻¹ * (offset - 1)
    have offsetEq : ((x.val * 2 + 1 : ℕ) : ZMod (k + 1)) = offset := by
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_two, Nat.cast_one]
      dsimp [x]
      calc
        _ = ((2 : ZMod (k + 1)) * (2 : ZMod (k + 1))⁻¹) * (offset - 1) + 1 := by ring
        _ = offset := by rw [ZMod.mul_inv_of_unit _ unit]; ring
    simpa only [offsetEq] using samples x.val (ZMod.val_lt x)
  letI : Fact (2 < k + 1) := ⟨by omega⟩
  have support : ∀ x : ZMod (k + 1), coefficient k x = 1 ↔ x = 0 ∨ x = -1 := by
    intro x
    unfold coefficient
    split_ifs with h
    · exact iff_of_true rfl h
    · exact iff_of_false (by decide : ¬ (0 : ZMod 2) = 1) h
  have firstHit := allSamples (-phase₁)
  have firstMarked : phase₂ - phase₁ = 0 ∨ phase₂ - phase₁ = -1 := by
    apply (support _).mp
    simpa [sub_eq_add_neg, coefficient] using firstHit.symm
  rcases firstMarked with equal | shifted
  · exact (sub_eq_zero.mp equal).symm
  · have secondHit := allSamples (-phase₁ - 1)
    have nextMarked : phase₂ - phase₁ - 1 = 0 ∨ phase₂ - phase₁ - 1 = -1 := by
      apply (support _).mp
      have h : phase₁ + (-phase₁ - 1) = (-1 : ZMod (k + 1)) := by abel
      rw [h] at secondHit
      simpa [sub_eq_add_neg, add_assoc, coefficient] using secondHit.symm
    rw [shifted] at nextMarked
    rcases nextMarked with zero | one
    · exact False.elim (ZMod.neg_one_ne_one (sub_eq_zero.mp zero))
    · have bad : (1 : ZMod (k + 1)) = 0 := by linear_combination -one
      have divisor := (ZMod.natCast_eq_zero_iff 1 (k + 1)).mp bad
      have bound := Nat.le_of_dvd (by omega : 0 < 1) divisor
      omega

#print axioms odd_single_bit_phase_recovery

/-- The second half of the even-period single-bit protocol, after the actual
first half and the separating zero. Each `01` consists of two complete blocks. -/
def evenSingleBitOrbit (k r : ℕ) (q : Option (LiveRecord k)) : Option (LiveRecord k) :=
  alternatingBitOrbit k r
    (runBits k (fun _ : Fin 1 => false) (alternatingBitOrbit k ((k + 1) / 2) q))

/-- The literal `(01)^(T/2) 0 (01)^(T/2)` protocol is safe and its actual
endpoint archive recovers the INITIAL ambient phase when `T` is even. -/
theorem even_single_bit_phase_recovery (k : ℕ) (hk : 2 ≤ k) (evenT : Even (k + 1))
    (v₁ v₂ : ZMod 2) (phase₁ phase₂ : ZMod (k + 1))
    (s₁ s₂ : ℕ) (hs₁ : s₁ < k) (hs₂ : s₂ < k) :
    (∀ r, ∃ value tail₀, tail₀ < k ∧
      evenSingleBitOrbit k r (some ⟨v₁, phase₁, s₁⟩) =
        some ⟨value, phase₁ + 1 + ((r * 2 : ℕ) : ZMod (k + 1)), tail₀⟩) ∧
    ((∀ r, r ≤ (k + 1) / 2 →
      endpointReading (alternatingBitOrbit k r (some ⟨v₁, phase₁, s₁⟩)) =
        endpointReading (alternatingBitOrbit k r (some ⟨v₂, phase₂, s₂⟩))) →
      (∀ r, r ≤ (k + 1) / 2 →
        endpointReading (evenSingleBitOrbit k r (some ⟨v₁, phase₁, s₁⟩)) =
          endpointReading (evenSingleBitOrbit k r (some ⟨v₂, phase₂, s₂⟩))) →
      phase₁ = phase₂) := by
  have pairLiteral : (fun current => runBits k (fun _ : Fin 1 => true)
      (runBits k (fun _ : Fin 1 => false) current)) = runBits k (isolatedProbe 2 1) := by
    funext current
    simp +unfoldPartialApp [runBits, List.ofFn_succ, isolatedProbe, runWord]
  have pairActual : ∀ v phi s, s < k → ∀ r, ∃ tail₀, tail₀ < k ∧
      alternatingBitOrbit k r (some ⟨v, phi, s⟩) =
        some ⟨v + ∑ i ∈ Finset.range r,
          coefficient k (phi + ((i * 2 + 1 : ℕ) : ZMod (k + 1))),
          phi + ((r * 2 : ℕ) : ZMod (k + 1)), tail₀⟩ := by
    intro v phi s hs r
    rw [alternatingBitOrbit, pairLiteral]
    exact (isolated_probe_orbit_exact k 2 hk 1 le_rfl (by omega) r v phi s hs).2
  have half : (k + 1) / 2 * 2 = k + 1 := by
    exact Nat.div_mul_cancel evenT.two_dvd
  have halfPositive : 0 < (k + 1) / 2 := by omega
  have castHalf : (((k + 1) / 2 * 2 : ℕ) : ZMod (k + 1)) = 0 := by
    rw [half, ZMod.natCast_self]
  have secondActual : ∀ v phi s, s < k → ∀ r, ∃ tail₀, tail₀ < k ∧
      evenSingleBitOrbit k r (some ⟨v, phi, s⟩) =
        some ⟨v + (∑ i ∈ Finset.range ((k + 1) / 2),
          coefficient k (phi + ((i * 2 + 1 : ℕ) : ZMod (k + 1)))) +
          ∑ i ∈ Finset.range r,
            coefficient k (phi + 1 + ((i * 2 + 1 : ℕ) : ZMod (k + 1))),
          phi + 1 + ((r * 2 : ℕ) : ZMod (k + 1)), tail₀⟩ := by
    intro v phi s hs r
    obtain ⟨tail₁, _, first⟩ := pairActual v phi s hs ((k + 1) / 2)
    simp only [castHalf, add_zero] at first
    unfold evenSingleBitOrbit
    rw [first]
    have zeroLiteral : runBits k (fun _ : Fin 1 => false)
        (some ⟨v + ∑ i ∈ Finset.range ((k + 1) / 2),
          coefficient k (phi + ((i * 2 + 1 : ℕ) : ZMod (k + 1))), phi, tail₁⟩) =
        some ⟨v + ∑ i ∈ Finset.range ((k + 1) / 2),
          coefficient k (phi + ((i * 2 + 1 : ℕ) : ZMod (k + 1))), phi + 1, 0⟩ := by
      simp [runBits, List.ofFn_const, runWord, bitUpdate]
    rw [zeroLiteral]
    exact pairActual _ _ _ (by omega) r
  have firstReading : ∀ v phi s, s < k → ∀ r,
      endpointReading (alternatingBitOrbit k r (some ⟨v, phi, s⟩)) =
        some (v + ∑ i ∈ Finset.range r,
          coefficient k (phi + ((i * 2 + 1 : ℕ) : ZMod (k + 1)))) := by
    intro v phi s hs r
    obtain ⟨tail₀, _, actual⟩ := pairActual v phi s hs r
    rw [actual]; rfl
  have secondReading : ∀ v phi s, s < k → ∀ r,
      endpointReading (evenSingleBitOrbit k r (some ⟨v, phi, s⟩)) =
        some (v + (∑ i ∈ Finset.range ((k + 1) / 2),
          coefficient k (phi + ((i * 2 + 1 : ℕ) : ZMod (k + 1)))) +
          ∑ i ∈ Finset.range r,
            coefficient k (phi + 1 + ((i * 2 + 1 : ℕ) : ZMod (k + 1)))) := by
    intro v phi s hs r
    obtain ⟨tail₀, _, actual⟩ := secondActual v phi s hs r
    rw [actual]; rfl
  refine ⟨?_, ?_⟩
  · intro r
    obtain ⟨tail₀, legal, actual⟩ := secondActual v₁ phase₁ s₁ hs₁ r
    exact ⟨_, tail₀, legal, actual⟩
  · intro firstArchive secondArchive
    have oddSamples : ∀ i, i < (k + 1) / 2 →
        coefficient k (phase₁ + ((i * 2 + 1 : ℕ) : ZMod (k + 1))) =
          coefficient k (phase₂ + ((i * 2 + 1 : ℕ) : ZMod (k + 1))) := by
      intro i hi
      have before := firstArchive i (by omega)
      have after := firstArchive (i + 1) (by omega)
      rw [firstReading _ _ _ hs₁, firstReading _ _ _ hs₂] at before after
      simp only [Option.some.injEq] at before after
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at after
      linear_combination after - before
    have evenSamples : ∀ i, i < (k + 1) / 2 →
        coefficient k (phase₁ + ((i * 2 + 2 : ℕ) : ZMod (k + 1))) =
          coefficient k (phase₂ + ((i * 2 + 2 : ℕ) : ZMod (k + 1))) := by
      intro i hi
      have before := secondArchive i (by omega)
      have after := secondArchive (i + 1) (by omega)
      rw [secondReading _ _ _ hs₁, secondReading _ _ _ hs₂] at before after
      simp only [Option.some.injEq] at before after
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at after
      have adjust : ∀ phi : ZMod (k + 1),
          phi + 1 + ((i * 2 + 1 : ℕ) : ZMod (k + 1)) =
            phi + ((i * 2 + 2 : ℕ) : ZMod (k + 1)) := by intro phi; push_cast; ring
      rw [adjust, adjust] at after
      linear_combination after - before
    have allSamples : ∀ offset : ZMod (k + 1),
        coefficient k (phase₁ + offset) = coefficient k (phase₂ + offset) := by
      intro offset
      have bound := ZMod.val_lt offset
      have decomposition := Nat.mod_add_div offset.val 2
      by_cases odd : offset.val % 2 = 1
      · have eq : offset.val / 2 * 2 + 1 = offset.val := by omega
        simpa only [eq, ZMod.natCast_zmod_val] using
          oddSamples (offset.val / 2) (by omega)
      · have even : offset.val % 2 = 0 := by have := Nat.mod_lt offset.val (by omega : 0 < 2); omega
        by_cases zero : offset.val = 0
        · have eq : ((k + 1) / 2 - 1) * 2 + 2 = k + 1 := by omega
          have offsetZero : offset = 0 := by
            rw [← ZMod.natCast_zmod_val offset, zero, Nat.cast_zero]
          simpa only [eq, ZMod.natCast_self, offsetZero] using
            evenSamples ((k + 1) / 2 - 1) (by omega)
        · have eq : (offset.val / 2 - 1) * 2 + 2 = offset.val := by omega
          simpa only [eq, ZMod.natCast_zmod_val] using
            evenSamples (offset.val / 2 - 1) (by omega)
    letI : Fact (2 < k + 1) := ⟨by omega⟩
    have marked : ∀ x : ZMod (k + 1), coefficient k x = 1 ↔ x = 0 ∨ x = -1 := by
      intro x
      unfold coefficient
      split_ifs with member
      · exact iff_of_true rfl member
      · exact iff_of_false (by decide : ¬ (0 : ZMod 2) = 1) member
    have atZero := allSamples (-phase₁)
    have difference : phase₂ - phase₁ = 0 ∨ phase₂ - phase₁ = -1 := by
      apply (marked _).mp
      simpa [sub_eq_add_neg, coefficient] using atZero.symm
    rcases difference with equal | shifted
    · exact (sub_eq_zero.mp equal).symm
    · have atLast := allSamples (-phase₁ - 1)
      have next : phase₂ - phase₁ - 1 = 0 ∨ phase₂ - phase₁ - 1 = -1 := by
        apply (marked _).mp
        have hit : phase₁ + (-phase₁ - 1) = (-1 : ZMod (k + 1)) := by abel
        rw [hit] at atLast
        simpa [sub_eq_add_neg, add_assoc, coefficient] using atLast.symm
      rw [shifted] at next
      rcases next with zero | one
      · exact False.elim (ZMod.neg_one_ne_one (sub_eq_zero.mp zero))
      · have impossible : (1 : ZMod (k + 1)) = 0 := by linear_combination -one
        have divisor := (ZMod.natCast_eq_zero_iff 1 (k + 1)).mp impossible
        have size := Nat.le_of_dvd (by omega : 0 < 1) divisor
        omega

#print axioms even_single_bit_phase_recovery

/-- The source's gcd-dependent isolated-one offset. -/
def phaseProbeOffset (k m : ℕ) : ℕ :=
  if Nat.gcd m (k + 1) = 1 then 1 else Nat.gcd m (k + 1) - 1

/-- The actual `p-1` safe block archive identifies every phase in the SAME
endpoint subgroup. Cycle-sum invariance recovers the single omitted sample;
the proof never treats the two support positions as mod-two nonzero mass. -/
theorem safe_block_phase_recovery (k m : ℕ) (hk : 2 ≤ k) (hm : 2 ≤ m)
    (v₁ v₂ : ZMod 2) (phase₁ phase₂ : ZMod (k + 1))
    (s₁ s₂ : ℕ) (hs₁ : s₁ < k) (hs₂ : s₂ < k)
    (hp₁ : Nat.gcd m (k + 1) ∣ phase₁.val)
    (hp₂ : Nat.gcd m (k + 1) ∣ phase₂.val) :
    DBonacciAdmissible k m (isolatedProbe m (phaseProbeOffset k m)) ∧
    (∀ r, ∃ value phase tail₀, tail₀ < k ∧
      (runBits k (isolatedProbe m (phaseProbeOffset k m)))^[r] (some ⟨v₁, phase₁, s₁⟩) =
        some ⟨value, phase, tail₀⟩) ∧
    ((∀ r, r ≤ (k + 1) / Nat.gcd m (k + 1) - 1 →
      endpointReading ((runBits k (isolatedProbe m (phaseProbeOffset k m)))^[r]
        (some ⟨v₁, phase₁, s₁⟩)) =
      endpointReading ((runBits k (isolatedProbe m (phaseProbeOffset k m)))^[r]
        (some ⟨v₂, phase₂, s₂⟩))) → phase₁ = phase₂) := by
  classical
  let g := Nat.gcd m (k + 1)
  let p := (k + 1) / g
  let j := phaseProbeOffset k m
  change g ∣ phase₁.val at hp₁
  change g ∣ phase₂.val at hp₂
  have gPositive : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have gDivM : g ∣ m := Nat.gcd_dvd_left _ _
  have gDivT : g ∣ k + 1 := Nat.gcd_dvd_right _ _
  have gSmall : g ≤ m := Nat.le_of_dvd (by omega) gDivM
  have pPositive : 0 < p := Nat.div_gcd_pos_of_pos_right _ (by omega)
  have pg : p * g = k + 1 := Nat.div_mul_cancel gDivT
  have jPositive : 1 ≤ j := by
    unfold j phaseProbeOffset
    split_ifs with one
    · omega
    · change g ≠ 1 at one
      omega
  have jSmall : j < m := by
    unfold j phaseProbeOffset
    split_ifs with one
    · omega
    · change g ≠ 1 at one
      omega
  have actual : ∀ v phi s, s < k → ∀ r, ∃ tail₀, tail₀ < k ∧
      (runBits k (isolatedProbe m j))^[r] (some ⟨v, phi, s⟩) =
        some ⟨v + ∑ i ∈ Finset.range r,
          coefficient k (phi + ((i * m + j : ℕ) : ZMod (k + 1))),
          phi + ((r * m : ℕ) : ZMod (k + 1)), tail₀⟩ := by
    intro v phi s hs r
    exact (isolated_probe_orbit_exact k m hk j jPositive jSmall r v phi s hs).2
  refine ⟨(isolated_probe_orbit_exact k m hk j jPositive jSmall 0 v₁ phase₁ s₁ hs₁).1,
    ?_, ?_⟩
  · intro r
    obtain ⟨tail₀, safe, executed⟩ := actual v₁ phase₁ s₁ hs₁ r
    exact ⟨_, _, tail₀, safe, executed⟩
  · intro archive
    change ∀ r, r ≤ p - 1 →
      endpointReading ((runBits k (isolatedProbe m j))^[r] (some ⟨v₁, phase₁, s₁⟩)) =
      endpointReading ((runBits k (isolatedProbe m j))^[r] (some ⟨v₂, phase₂, s₂⟩)) at archive
    by_cases onePhase : p = 1
    · have gEq : g = k + 1 := by rw [onePhase, one_mul] at pg; exact pg
      have zero₁ : phase₁.val = 0 := Nat.eq_zero_of_dvd_of_lt hp₁
        (by rw [gEq]; exact ZMod.val_lt phase₁)
      have zero₂ : phase₂.val = 0 := Nat.eq_zero_of_dvd_of_lt hp₂
        (by rw [gEq]; exact ZMod.val_lt phase₂)
      rw [← ZMod.natCast_zmod_val phase₁, ← ZMod.natCast_zmod_val phase₂, zero₁, zero₂]
    have pTwo : 2 ≤ p := by omega
    obtain ⟨q₁, phase₁Nat⟩ := hp₁
    obtain ⟨q₂, phase₂Nat⟩ := hp₂
    have phase₁Eq : phase₁ = (g : ZMod (k + 1)) * (q₁ : ℕ) := by
      rw [← ZMod.natCast_zmod_val phase₁, phase₁Nat, Nat.cast_mul]
    have phase₂Eq : phase₂ = (g : ZMod (k + 1)) * (q₂ : ℕ) := by
      rw [← ZMod.natCast_zmod_val phase₂, phase₂Nat, Nat.cast_mul]
    have inverseG : (m : ZMod (k + 1)) * (m : ZMod (k + 1))⁻¹ = (g : ℕ) := by
      rw [ZMod.mul_inv_eq_gcd, ZMod.val_natCast, ← Nat.gcd_rec (k + 1) m,
        Nat.gcd_comm]
    have periodZero : (p : ZMod (k + 1)) * (m : ℕ) = 0 := by
      rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      obtain ⟨r, mEq⟩ := gDivM
      exact ⟨r, by rw [mEq]; nlinarith [pg]⟩
    let sample := fun phi i => coefficient k (phi + ((i * m + j : ℕ) : ZMod (k + 1)))
    have periodic : ∀ phi i, sample phi (i + p) = sample phi i := by
      intro phi i
      dsimp [sample]
      congr 1
      push_cast
      linear_combination periodZero
    have sampleMod : ∀ phi i, sample phi (i % p) = sample phi i := by
      intro phi i
      have decompose : i = i % p + p * (i / p) := (Nat.mod_add_div i p).symm
      have samePosition : ((i * m + j : ℕ) : ZMod (k + 1)) =
          ((i % p * m + j : ℕ) : ZMod (k + 1)) := by
        calc
          _ = (((i % p + p * (i / p)) * m + j : ℕ) : ZMod (k + 1)) :=
            congrArg (fun x : ℕ => ((x * m + j : ℕ) : ZMod (k + 1))) decompose
          _ = _ := by push_cast; linear_combination (i / p : ZMod (k + 1)) * periodZero
      dsimp [sample]
      rw [samePosition]
    have reading : ∀ v phi s, s < k → ∀ r,
        endpointReading ((runBits k (isolatedProbe m j))^[r] (some ⟨v, phi, s⟩)) =
          some (v + ∑ i ∈ Finset.range r, sample phi i) := by
      intro v phi s hs r
      obtain ⟨tail₀, _, execution⟩ := actual v phi s hs r
      rw [execution]; rfl
    have shortSamples : ∀ i, i < p - 1 → sample phase₁ i = sample phase₂ i := by
      intro i hi
      have before := archive i (by omega)
      have after := archive (i + 1) (by omega)
      rw [reading _ _ _ hs₁, reading _ _ _ hs₂] at before after
      simp only [Option.some.injEq] at before after
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at after
      linear_combination after - before
    let shift : ZMod (k + 1) := (m : ZMod (k + 1))⁻¹ * ((q₂ : ℕ) - (q₁ : ℕ))
    have shiftEq : ((shift.val * m : ℕ) : ZMod (k + 1)) = phase₂ - phase₁ := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      dsimp [shift]
      rw [phase₁Eq, phase₂Eq]
      linear_combination ((q₂ : ZMod (k + 1)) - (q₁ : ℕ)) * inverseG
    have phaseShift : phase₂ = phase₁ + ((shift.val * m : ℕ) : ZMod (k + 1)) := by
      rw [shiftEq]; ring
    have rotateSum : ∀ r,
        (∑ i ∈ Finset.range p, sample phase₁ (i + r)) =
          ∑ i ∈ Finset.range p, sample phase₁ i := by
      intro r
      induction r with
      | zero => simp
      | succ r inductionHypothesis =>
          have left := Finset.sum_range_succ (fun i => sample phase₁ (i + r)) p
          have right := Finset.sum_range_succ' (fun i => sample phase₁ (i + r)) p
          have endSame : sample phase₁ (p + r) = sample phase₁ r := by
            simpa only [Nat.add_comm] using periodic phase₁ r
          rw [endSame] at left
          have adjust : (∑ i ∈ Finset.range p, sample phase₁ (i + 1 + r)) =
              ∑ i ∈ Finset.range p, sample phase₁ (i + (r + 1)) := by
            apply Finset.sum_congr rfl
            intro i _; congr 1; omega
          rw [adjust] at right
          simp only [Nat.zero_add] at right
          linear_combination left - right + inductionHypothesis
    have totalSame : (∑ i ∈ Finset.range p, sample phase₂ i) =
        ∑ i ∈ Finset.range p, sample phase₁ i := by
      calc
        _ = ∑ i ∈ Finset.range p, sample phase₁ (i + shift.val) := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp [sample]
          congr 1
          rw [phaseShift]
          push_cast
          ring
        _ = _ := rotateSum shift.val
    have shortSame : (∑ i ∈ Finset.range (p - 1), sample phase₁ i) =
        ∑ i ∈ Finset.range (p - 1), sample phase₂ i :=
      Finset.sum_congr rfl (fun i hi => shortSamples i (Finset.mem_range.mp hi))
    have expand : ∀ phi, (∑ i ∈ Finset.range p, sample phi i) =
        (∑ i ∈ Finset.range (p - 1), sample phi i) + sample phi (p - 1) := by
      intro phi
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p)] using
        Finset.sum_range_succ (sample phi) (p - 1)
    rw [expand, expand] at totalSame
    have lastSame : sample phase₁ (p - 1) = sample phase₂ (p - 1) := by
      linear_combination -totalSame - shortSame
    have fullSamples : ∀ i, i < p → sample phase₁ i = sample phase₂ i := by
      intro i hi
      by_cases short : i < p - 1
      · exact shortSamples i short
      · have last : i = p - 1 := by omega
        simpa only [last] using lastSame
    have allNatural : ∀ i, sample phase₁ i = sample phase₂ i := by
      intro i
      rw [← sampleMod phase₁ i, ← sampleMod phase₂ i]
      exact fullSamples (i % p) (Nat.mod_lt _ pPositive)
    have marked : ∀ x : ZMod (k + 1), coefficient k x = 1 ↔ x = 0 ∨ x = -1 := by
      intro x
      unfold coefficient
      split_ifs with member
      · exact iff_of_true rfl member
      · exact iff_of_false (by decide : ¬ (0 : ZMod 2) = 1) member
    by_cases gOne : g = 1
    · have jOne : j = 1 := by
        change (if g = 1 then 1 else g - 1) = 1
        rw [if_pos gOne]
      have allOffsets : ∀ offset : ZMod (k + 1),
          coefficient k (phase₁ + offset) = coefficient k (phase₂ + offset) := by
        intro offset
        let x : ZMod (k + 1) := (m : ZMod (k + 1))⁻¹ * (offset - 1)
        have position : ((x.val * m + j : ℕ) : ZMod (k + 1)) = offset := by
          rw [jOne, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
          dsimp [x]
          rw [gOne, Nat.cast_one] at inverseG
          linear_combination (offset - 1) * inverseG
        simpa only [sample, position] using allNatural x.val
      letI : Fact (2 < k + 1) := ⟨by omega⟩
      have atZero := allOffsets (-phase₁)
      have difference : phase₂ - phase₁ = 0 ∨ phase₂ - phase₁ = -1 := by
        apply (marked _).mp
        simpa [sub_eq_add_neg, coefficient] using atZero.symm
      rcases difference with equal | shifted
      · exact (sub_eq_zero.mp equal).symm
      · have atLast := allOffsets (-phase₁ - 1)
        have next : phase₂ - phase₁ - 1 = 0 ∨ phase₂ - phase₁ - 1 = -1 := by
          apply (marked _).mp
          have hit : phase₁ + (-phase₁ - 1) = (-1 : ZMod (k + 1)) := by abel
          rw [hit] at atLast
          simpa [sub_eq_add_neg, add_assoc, coefficient] using atLast.symm
        rw [shifted] at next
        rcases next with zero | one
        · exact False.elim (ZMod.neg_one_ne_one (sub_eq_zero.mp zero))
        · have impossible : (1 : ZMod (k + 1)) = 0 := by linear_combination -one
          have divisor := (ZMod.natCast_eq_zero_iff 1 (k + 1)).mp impossible
          have size := Nat.le_of_dvd (by omega : 0 < 1) divisor
          omega
    · have gTwo : 2 ≤ g := by omega
      have jCast : (j : ZMod (k + 1)) = (g : ℕ) - 1 := by
        change ((if g = 1 then 1 else g - 1 : ℕ) : ZMod (k + 1)) = (g : ℕ) - 1
        rw [if_neg gOne]
        rw [Nat.cast_sub (by omega : 1 ≤ g), Nat.cast_one]
      let x : ZMod (k + 1) := (m : ZMod (k + 1))⁻¹ * (-1 - (q₁ : ℕ))
      have hit : phase₁ + ((x.val * m + j : ℕ) : ZMod (k + 1)) = -1 := by
        rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, jCast, phase₁Eq]
        dsimp [x]
        linear_combination (-1 - (q₁ : ZMod (k + 1))) * inverseG
      have observed := allNatural x.val
      dsimp [sample] at observed
      rw [hit] at observed
      have other : phase₂ + ((x.val * m + j : ℕ) : ZMod (k + 1)) =
          phase₂ - phase₁ - 1 := by linear_combination hit
      rw [other] at observed
      have difference : phase₂ - phase₁ - 1 = 0 ∨ phase₂ - phase₁ - 1 = -1 := by
        apply (marked _).mp
        simpa [coefficient] using observed.symm
      rcases difference with neighbor | same
      · let hom := ZMod.castHom gDivT (ZMod g)
        have zero₁ : hom phase₁ = 0 := by
          rw [phase₁Eq, map_mul, map_natCast, map_natCast, ZMod.natCast_self, zero_mul]
        have zero₂ : hom phase₂ = 0 := by
          rw [phase₂Eq, map_mul, map_natCast, map_natCast, ZMod.natCast_self, zero_mul]
        have equalOne : phase₂ - phase₁ = (1 : ZMod (k + 1)) := by
          linear_combination neighbor
        have impossible := congrArg hom equalOne
        have bad : (1 : ZMod g) = 0 := by simpa [map_sub, zero₁, zero₂] using impossible.symm
        have divisor := (ZMod.natCast_eq_zero_iff 1 g).mp (by simpa only [Nat.cast_one] using bad)
        have size := Nat.le_of_dvd (by omega : 0 < 1) divisor
        omega
      · have equal : phase₂ - phase₁ = 0 := by linear_combination same
        exact (sub_eq_zero.mp equal).symm

#print axioms safe_block_phase_recovery


end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PhaseRecovery
