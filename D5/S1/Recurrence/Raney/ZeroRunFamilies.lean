/- GID: D5/S1/Recurrence/Raney/ZeroRunFamilies
   generality: G
   mirror-B: D5/B/S1/Recurrence/Raney/ZeroRunFamilies
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Raney quotients have unbounded support and finite zero-run families. -/

import D5.S1.Recurrence.Raney.FinitePathDisplacements
import Mathlib.Data.Nat.Choose.Lucas

namespace TrureTuring
namespace Raney

/-- The literal integral Raney number from Conjecture 7.1. -/
def raneyNumber (k r n : Nat) : Nat :=
  r * Nat.choose (k * n + r) n / (k * n + r)

/-- For positive `k,r` and a prime not dividing `k*r`, the Raney sequence has
unbounded nonzero support modulo the prime, and the lengths of all its actual
maximal zero runs belong to one finite family of affine prime-power forms. -/
theorem raney_zero_run_coefficient_families
    (k r p : Nat) (hk : 0 < k) (hr : 0 < r) (hp : p.Prime)
    (hcoprime : ¬ p ∣ k * r) :
    (∀ cutoff : Nat, ∃ n : Nat, cutoff ≤ n ∧
      (raneyNumber k r n : ZMod p) ≠ 0) ∧
    ∃ coefficients : Finset (Int × Int × Nat),
      (∀ abc ∈ coefficients, 0 < abc.2.2) ∧
      ∀ first last : Nat,
        IsMaximalDeltaInterval {0}
            (fun n => (raneyNumber k r n : ZMod p)) first last ->
        ∃ abc ∈ coefficients, ∃ m : Nat,
          (abc.2.2 : Int) * ((last + 1 - first : Nat) : Int) =
            abc.1 * (p : Int) ^ m + abc.2.1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hpOne : 1 < p := hp.one_lt
  have hpPos : 0 < p := hp.pos
  have hpk : ¬ p ∣ k := by
    intro h
    exact hcoprime (dvd_mul_of_dvd_left h r)
  let A := max (k - 1) (r - 1)
  have hkA : k ≤ A + 1 := by
    dsimp [A]
    omega
  have hrA : r - 1 < A + 1 := by
    dsimp [A]
    omega
  let State := Fin (A + 1) × Bool
  let Alphabet := State -> ZMod p
  let normal : Nat -> Nat -> ZMod p := fun a n => (Nat.choose (k * n + a) n : ZMod p)
  let pred : Nat -> Nat -> ZMod p := fun a n =>
    if n = 0 then 0 else (Nat.choose (k * n + a) (n - 1) : ZMod p)
  let word : Nat -> Alphabet := fun n s =>
    if s.2 then pred s.1 n else normal s.1 n
  have sourceBridge (n : Nat) :
      (if n = 0 then 0 else
        (k - 1) * Nat.choose (k * n + r - 1) (n - 1)) ≤
          Nat.choose (k * n + r - 1) n ∧
        raneyNumber k r n =
          Nat.choose (k * n + r - 1) n -
            (if n = 0 then 0 else
              (k - 1) * Nat.choose (k * n + r - 1) (n - 1)) := by
    cases n with
    | zero =>
        simp [raneyNumber, Nat.div_self hr]
    | succ n =>
        let N := k * (n + 1) + r
        let M := N - 1
        have hN : 0 < N := by
          dsimp [N]
          omega
        have hM : M + 1 = N := by
          dsimp [M]
          omega
        have hMN : k * (n + 1) + r - 1 = M := by
          rfl
        have hPred := Nat.add_one_mul_choose_eq M n
        have hNormal := Nat.choose_mul_succ_eq M (n + 1)
        rw [hM] at hPred hNormal
        have hNsub : N - (n + 1) = (k - 1) * (n + 1) + r := by
          have hkMul : k * (n + 1) = (k - 1) * (n + 1) + (n + 1) := by
            calc
              k * (n + 1) = ((k - 1) + 1) * (n + 1) := by
                rw [Nat.sub_add_cancel hk]
              _ = (k - 1) * (n + 1) + (n + 1) := by ring
          have hnle : n + 1 ≤ N := by
            dsimp [N]
            rw [hkMul]
            omega
          apply (Nat.sub_eq_iff_eq_add hnle).2
          dsimp [N]
          rw [hkMul]
          omega
        rw [hNsub] at hNormal
        let C := Nat.choose N (n + 1)
        let B := Nat.choose M n
        let D := Nat.choose M (n + 1)
        have hPred' : N * B = C * (n + 1) := by
          simpa [B, C, Nat.mul_comm] using hPred
        have hNormal' : D * N = C * ((k - 1) * (n + 1) + r) := by
          simpa [D, C] using hNormal
        have hDecomp : D * N = ((k - 1) * B) * N + r * C := by
          calc
            D * N = C * ((k - 1) * (n + 1) + r) := hNormal'
            _ = (k - 1) * (C * (n + 1)) + r * C := by ring
            _ = (k - 1) * (N * B) + r * C := by rw [hPred']
            _ = ((k - 1) * B) * N + r * C := by ring
        have hLeMul : ((k - 1) * B) * N ≤ D * N := by
          rw [hDecomp]
          exact Nat.le_add_right _ _
        have hLe : (k - 1) * B ≤ D := by
          exact Nat.le_of_mul_le_mul_right hLeMul hN
        have hCross : N * (D - (k - 1) * B) = r * C := by
          rw [Nat.mul_sub_left_distrib, Nat.mul_comm N D,
            Nat.mul_comm N ((k - 1) * B)]
          omega
        refine ⟨?_, ?_⟩
        · simpa [B, D, M, N] using hLe
        · have hQuot : r * C / N = D - (k - 1) * B := by
            rw [← hCross, Nat.mul_div_right _ hN]
          simpa [raneyNumber, C, D, B, M, N] using hQuot
  have sourceReadout (n : Nat) :
      (raneyNumber k r n : ZMod p) =
        word n (⟨r - 1, hrA⟩, false) -
          (k - 1 : Nat) * word n (⟨r - 1, hrA⟩, true) := by
    have bridge := sourceBridge n
    rw [bridge.2, Nat.cast_sub bridge.1]
    have hrSub : k * n + r - 1 = k * n + (r - 1) := by omega
    rw [hrSub]
    simp [word, normal, pred]
  have nextIndexBound (a : Fin (A + 1)) (d : Fin p) :
      (k * (d : Nat) + (a : Nat)) / p < A + 1 := by
    apply (Nat.div_lt_iff_lt_mul hpPos).2
    have hd : (d : Nat) ≤ p - 1 := by omega
    have ha : (a : Nat) ≤ A := by omega
    have hkd := Nat.mul_le_mul hkA hd
    calc
      k * (d : Nat) + (a : Nat) ≤ (A + 1) * (p - 1) + A :=
        Nat.add_le_add hkd ha
      _ < (A + 1) * (p - 1) + A + 1 := Nat.lt_succ_self _
      _ = (A + 1) * p := by
        rw [show (A + 1) * (p - 1) + A + 1 =
          (A + 1) * ((p - 1) + 1) by ring, Nat.sub_add_cancel hpPos]
  let nextIndex : Fin (A + 1) -> Fin p -> Fin (A + 1) := fun a d =>
    ⟨(k * (d : Nat) + (a : Nat)) / p, nextIndexBound a d⟩
  let nextState : State -> Fin p -> State := fun s d =>
    (nextIndex s.1 d, s.2 && decide ((d : Nat) = 0))
  let weight : State -> Fin p -> ZMod p := fun s d =>
    if s.2 then
      if (d : Nat) = 0 then Nat.choose ((k * (d : Nat) + (s.1 : Nat)) % p) (p - 1)
      else Nat.choose ((k * (d : Nat) + (s.1 : Nat)) % p) ((d : Nat) - 1)
    else Nat.choose ((k * (d : Nat) + (s.1 : Nat)) % p) d
  let digitTransform : Fin p -> Alphabet -> Alphabet := fun d x s =>
    weight s d * x (nextState s d)
  let morphism : Alphabet -> List Alphabet := fun x =>
    List.ofFn fun d : Fin p => digitTransform d x
  have uniform (x : Alphabet) : (morphism x).length = p := by
    simp [morphism]
  have lucas (N K : Nat) :
      (Nat.choose N K : ZMod p) =
        (Nat.choose (N % p) (K % p) : ZMod p) *
          (Nat.choose (N / p) (K / p) : ZMod p) := by
    have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := N) (k := K) (p := p)
    rw [← ZMod.intCast_eq_intCast_iff] at h
    exact_mod_cast h
  have fixed (i : Nat) (d : Fin p) :
      word (p * i + d) =
        uniformLetter morphism uniform (word i) d := by
    funext s
    rcases s with ⟨a, b⟩
    cases b with
    | false =>
        rw [show word (p * i + d) (a, false) = normal a (p * i + d) by simp [word]]
        dsimp [normal]
        rw [lucas]
        have hUpper : k * (p * i + (d : Nat)) + (a : Nat) =
            (k * (d : Nat) + (a : Nat)) + p * (k * i) := by ring
        have hUpperDiv :
            ((k * (d : Nat) + (a : Nat)) + p * (k * i)) / p =
              (k * (d : Nat) + (a : Nat)) / p + k * i :=
          Nat.add_mul_div_left _ _ hpPos
        have hLowerDiv : (p * i + (d : Nat)) / p = i := by
          rw [Nat.add_comm]
          simpa [Nat.div_eq_of_lt d.isLt] using
            (Nat.add_mul_div_left (d : Nat) i hpPos)
        rw [hUpper]
        rw [hUpperDiv, hLowerDiv]
        simp [uniformLetter, morphism, digitTransform, weight, nextState,
          nextIndex, word, normal, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt d.isLt, Nat.add_comm]
    | true =>
        by_cases hd : (d : Nat) = 0
        · have hdFin : d = ⟨0, hpPos⟩ := Fin.ext hd
          subst d
          simp only [Nat.add_zero]
          by_cases hi : i = 0
          · subst i
            simp [uniformLetter, morphism, digitTransform, weight, nextState,
              nextIndex, word, pred]
          · have hiPos : 0 < i := Nat.pos_of_ne_zero hi
            change pred a (p * i) = _
            rw [show pred a (p * i) =
                (Nat.choose (k * (p * i) + a) (p * i - 1) : ZMod p) by
              simp [pred, Nat.mul_ne_zero hp.ne_zero hi]]
            rw [lucas]
            have hUpper : k * (p * i) + (a : Nat) =
                (a : Nat) + p * (k * i) := by ring
            have hLower : p * i - 1 = (p - 1) + p * (i - 1) := by
              rw [show p * i = p * (i - 1) + p by
                calc
                  p * i = p * ((i - 1) + 1) := by rw [Nat.sub_add_cancel hiPos]
                  _ = p * (i - 1) + p := by ring]
              rw [Nat.add_sub_assoc (by omega : 1 ≤ p)]
              omega
            have hUpperDiv : ((a : Nat) + p * (k * i)) / p =
                (a : Nat) / p + k * i := Nat.add_mul_div_left _ _ hpPos
            have hLowerDiv : ((p - 1) + p * (i - 1)) / p = i - 1 := by
              simpa [Nat.div_eq_of_lt (by omega : p - 1 < p)] using
                (Nat.add_mul_div_left (p - 1) (i - 1) hpPos)
            rw [hUpper, hLower]
            rw [hUpperDiv, hLowerDiv]
            simp [uniformLetter, morphism, digitTransform, weight, nextState,
              nextIndex, word, pred, hi, Nat.add_mul_mod_self_left, Nat.add_comm]
        · have hdi : 0 < (d : Nat) := Nat.pos_of_ne_zero hd
          have hIndex : p * i + (d : Nat) ≠ 0 := by omega
          change pred a (p * i + d) = _
          dsimp [pred]
          rw [if_neg hIndex]
          rw [lucas]
          have hUpper : k * (p * i + (d : Nat)) + (a : Nat) =
              (k * (d : Nat) + (a : Nat)) + p * (k * i) := by ring
          have hLower : p * i + (d : Nat) - 1 =
              ((d : Nat) - 1) + p * i := by omega
          have hUpperDiv :
              ((k * (d : Nat) + (a : Nat)) + p * (k * i)) / p =
                (k * (d : Nat) + (a : Nat)) / p + k * i :=
            Nat.add_mul_div_left _ _ hpPos
          have hLowerDiv : (((d : Nat) - 1) + p * i) / p = i := by
            simpa [Nat.div_eq_of_lt (by omega : (d : Nat) - 1 < p)] using
              (Nat.add_mul_div_left ((d : Nat) - 1) i hpPos)
          rw [hUpper, hLower]
          rw [hUpperDiv, hLowerDiv]
          rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]
          rw [Nat.mod_eq_of_lt (by omega : (d : Nat) - 1 < p)]
          have hHigh :
              (Nat.choose ((k * (d : Nat) + (a : Nat)) / p + k * i) i : ZMod p) =
                normal ((k * (d : Nat) + (a : Nat)) / p) i := by
            simp [normal, Nat.add_comm]
          rw [hHigh]
          simp [uniformLetter, morphism, digitTransform, weight, nextState,
            nextIndex, word, pred, hd, Nat.add_comm]
  let Delta : Finset Alphabet := {x | x (⟨r - 1, hrA⟩, false) -
    (k - 1 : Nat) * x (⟨r - 1, hrA⟩, true) = 0}
  have deltaIff (n : Nat) :
      word n ∈ Delta ↔ (raneyNumber k r n : ZMod p) = 0 := by
    simp [Delta, ← sourceReadout]
  have normalPower (j a : Nat) (ha : a < p ^ j) :
      (Nat.choose (k * p ^ j + a) (p ^ j) : ZMod p) = k := by
    induction j generalizing a with
    | zero =>
        have : a = 0 := by simpa using ha
        subst a
        simp
    | succ j ih =>
        have hpow : p ^ (j + 1) = p * p ^ j := by
          rw [pow_succ]
          ring
        have haDiv : a / p < p ^ j := by
          apply (Nat.div_lt_iff_lt_mul hpPos).2
          simpa [hpow, Nat.mul_comm] using ha
        have hUpper : k * (p * p ^ j) + a = a + p * (k * p ^ j) := by ring
        rw [hpow, lucas, hUpper]
        rw [Nat.add_mul_div_left _ _ hpPos]
        rw [Nat.add_mul_mod_self_left, Nat.mul_mod_right,
          Nat.mul_div_right _ hpPos]
        have high := ih (a / p) haDiv
        rw [show a / p + k * p ^ j = k * p ^ j + a / p by omega, high]
        simp
  have predPower (j a : Nat) (ha : a < p ^ j) :
      (Nat.choose (k * p ^ (j + 1) + a) (p ^ (j + 1) - 1) : ZMod p) = 0 := by
    induction j generalizing a with
    | zero =>
        have : a = 0 := by simpa using ha
        subst a
        rw [show 0 + 1 = 1 by omega, pow_one, lucas]
        have hz : Nat.choose 0 (p - 1) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        simp [hz, hp.ne_zero]
    | succ j ih =>
        have hpow : p ^ (Nat.succ j + 1) = p * p ^ (j + 1) := by
          rw [show Nat.succ j + 1 = (j + 1) + 1 by omega, pow_succ]
          ring
        have haDiv : a / p < p ^ j := by
          apply (Nat.div_lt_iff_lt_mul hpPos).2
          simpa [pow_succ, Nat.mul_comm] using ha
        have hUpper : k * (p * p ^ (j + 1)) + a =
            a + p * (k * p ^ (j + 1)) := by ring
        have hMulPred (q : Nat) (hq : 0 < q) :
            p * q - 1 = (p - 1) + p * (q - 1) := by
          rw [show p * q = p * (q - 1) + p by
            calc
              p * q = p * ((q - 1) + 1) := by rw [Nat.sub_add_cancel hq]
              _ = p * (q - 1) + p := by ring]
          rw [Nat.add_sub_assoc (by omega : 1 ≤ p)]
          omega
        have hLower : p * p ^ (j + 1) - 1 =
            (p - 1) + p * (p ^ (j + 1) - 1) :=
          hMulPred _ (pow_pos hpPos _)
        rw [hpow, lucas, hUpper, hLower]
        rw [Nat.add_mul_div_left _ _ hpPos, Nat.add_mul_div_left _ _ hpPos]
        rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]
        have high := ih (a / p) haDiv
        rw [show a / p + k * p ^ (j + 1) =
          k * p ^ (j + 1) + a / p by omega]
        rw [show (p - 1) / p + (p ^ (j + 1) - 1) =
          p ^ (j + 1) - 1 by simp [Nat.div_eq_of_lt (by omega : p - 1 < p)]]
        rw [high]
        simp
  have unbounded : ∀ cutoff : Nat, ∃ n : Nat, cutoff ≤ n ∧
      (raneyNumber k r n : ZMod p) ≠ 0 := by
    intro cutoff
    let j := max cutoff (r - 1) + 1
    have hj : max cutoff (r - 1) + 1 < p ^ j := by
      dsimp [j]
      exact Nat.lt_pow_self hpOne
    let n := p ^ (j + 1)
    have hcut : cutoff ≤ n := by
      dsimp [n]
      have hpPow : p ^ j ≤ p ^ (j + 1) := by
        rw [pow_succ]
        exact Nat.le_mul_of_pos_right _ hpPos
      omega
    have hra : r - 1 < p ^ j := by omega
    have hnormal := normalPower (j + 1) (r - 1) (by
      exact hra.trans_le (by
        rw [pow_succ]
        exact Nat.le_mul_of_pos_right _ hpPos))
    have hpred := predPower j (r - 1) hra
    refine ⟨n, hcut, ?_⟩
    rw [sourceReadout]
    change normal (r - 1) n - (k - 1 : Nat) * pred (r - 1) n ≠ 0
    have hnormal' : normal (r - 1) n = (k : ZMod p) := by
      simpa [normal, n] using hnormal
    have hpred' : pred (r - 1) n = 0 := by
      simp [pred, n, hpred]
    rw [hnormal', hpred', mul_zero, sub_zero]
    intro hz
    exact hpk ((ZMod.natCast_eq_zero_iff k p).mp hz)
  refine ⟨unbounded, ?_⟩
  obtain ⟨coefficients, positive, families⟩ :=
    exists_finite_actual_maximal_block_coefficient_families
      p hpOne morphism uniform word fixed Delta
  refine ⟨coefficients, positive, ?_⟩
  intro first last block
  apply families first last
  simp only [IsMaximalDeltaInterval, Finset.mem_singleton] at block ⊢
  simpa only [deltaIff] using block

#print axioms raney_zero_run_coefficient_families

end Raney
end TrureTuring
