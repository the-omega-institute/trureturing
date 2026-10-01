/- GID: D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe
   mirror-E: none(waiver:uniform-short-canonical-probes)
   anchors: [D5/S3/Analytic/GoldenEulerBetaZeckendorf, D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd]
   utility: none
   digest: Short canonical words realize every coefficient pair on all rows and legal prefixes. -/

import D5.S3.Analytic.GoldenEulerBetaZeckendorf
import D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Round
import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe

open D5.S3.Analytic.GoldenEulerBetaZeckendorf
open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
open D5.S3.Arith.ZeckendorfFutureKernel (legal value)
open scoped BigOperators

local instance : IsTrans Nat (fun a b => b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

noncomputable section

/-- First Fibonacci number strictly larger than twice the modulus. -/
def firstIndex (H : Nat) : Nat := Nat.find (show ∃ j, 2 * H < Nat.fib j from by
  refine ⟨2 * H + 5, ?_⟩
  have h := Nat.le_fib_self (n := 2 * H + 5) (by omega)
  omega)

/-- The first Fibonacci index whose value bounds the integer construction. -/
def lengthIndex (H : Nat) : Nat := Nat.find (show
    ∃ m, H * (Nat.fib (firstIndex H) + 1) ≤ Nat.fib m from by
  refine ⟨H * (Nat.fib (firstIndex H) + 1) + 5, ?_⟩
  exact (by omega : H * (Nat.fib (firstIndex H) + 1) ≤
    H * (Nat.fib (firstIndex H) + 1) + 5).trans (Nat.le_fib_self (by omega)))

/-- Ceiling of one third of the first index bounding the construction. -/
def lengthBound (H : Nat) : Nat := (lengthIndex H + 2) / 3

def windowCoefficients (H : Nat) (w : List Window) : ZMod H × ZMod H :=
  (value 1 0 (flatten w), value 0 1 (flatten w))

def firstTwoZero (w : List Window) : Prop :=
  List.take 2 (flatten w) = [false, false]

def Covers (H L : Nat) : Prop :=
  ∀ A B : ZMod H, ∃ w : List Window,
    w.length ≤ L ∧ w ≠ [] ∧ Success w ∧
      windowCoefficients H w = (A, B)

def Covers00 (H L : Nat) : Prop :=
  ∀ A B : ZMod H, ∃ w : List Window,
    w.length ≤ L ∧ w ≠ [] ∧ firstTwoZero w ∧ Success w ∧
      windowCoefficients H w = (A, B)

noncomputable def D (H : Nat) : WithTop Nat :=
  sInf ((fun L : Nat => (L : WithTop Nat)) '' {L : Nat | 1 ≤ L ∧ Covers H L})

noncomputable def D00 (H : Nat) : WithTop Nat :=
  sInf ((fun L : Nat => (L : WithTop Nat)) '' {L : Nat | 1 ≤ L ∧ Covers00 H L})

private def supportBits (n t : Nat) : List Bool :=
  false :: false :: List.ofFn (fun i : Fin (3 * t - 2) =>
    decide (i.val + 2 ∈ Nat.zeckendorf n))

private def supportWord (n t : Nat) : List Window :=
  pack (supportBits n t)

set_option maxHeartbeats 2000000 in
-- The bounded real grid and the recursive literal-word constructions share one proof.
/-- A common bounded nonempty word realizes every coefficient pair and ends
canonically after every actual legal prefix. -/
theorem result (H : Nat) (hH : 2 ≤ H) :
    5 ≤ firstIndex H ∧
    2 * H < Nat.fib (firstIndex H) ∧ Nat.fib (firstIndex H) < 4 * H ∧
    (∀ A B : ZMod H, ∃ w : List Window,
      w.length ≤ lengthBound H ∧ w ≠ [] ∧ firstTwoZero w ∧ Success w ∧
      windowCoefficients H w = (A, B) ∧
      (∀ u v : ZMod H, value u v (flatten w) = A * u + B * v) ∧
      (∀ (epsilon : Bool) (p : List Window), legal epsilon (flatten p) →
        ∃ N : Nat, 0 < N ∧ initialized epsilon (p ++ w) = some N)) ∧
    D H ≤ D00 H ∧ D00 H ≤ (lengthBound H : WithTop Nat) ∧
    lengthBound H ≤ 2 * Nat.log 2 H + 5 ∧
    (lengthBound H : Real) ≤ (7 / Real.log 2) * Real.log (H : Real) := by
  classical
  have bounded_coefficient_pair (H : Nat) (hH : 2 ≤ H) :
      let j := firstIndex H
      let q := Nat.fib j
      5 ≤ j ∧ 2 * H < q ∧ q < 4 * H ∧
        ∀ A B : ZMod H, ∃ n : Nat,
          H ≤ n ∧ n < H * (q + 1) ∧
          (n : ZMod H) = B ∧ (shiftedFibSum n : ZMod H) = A := by
    classical
    let j := firstIndex H
    let q := Nat.fib j
    have hjq : 2 * H < q := by
      change 2 * H < Nat.fib (firstIndex H)
      unfold firstIndex
      exact Nat.find_spec (p := fun k : Nat => 2 * H < Nat.fib k) _
    have hmin : ∀ k < j, Nat.fib k ≤ 2 * H := by
      intro k hk
      exact Nat.le_of_not_gt (Nat.find_min (p := fun k : Nat => 2 * H < Nat.fib k) _ hk)
    have hj5 : 5 ≤ j := by
      by_contra hn
      have hj4 : j ≤ 4 := by omega
      have hf := Nat.fib_mono hj4
      norm_num at hf
      omega
    have hjprev : Nat.fib (j - 1) ≤ 2 * H := hmin _ (by omega)
    have hstrict : Nat.fib (j - 2) < Nat.fib (j - 1) :=
      (Nat.fib_lt_fib (by omega)).2 (by omega)
    have hrec : q = Nat.fib (j - 1) + Nat.fib (j - 2) := by
      dsimp [q]
      calc
        Nat.fib j = Nat.fib ((j - 2) + 2) := congrArg Nat.fib (by omega)
        _ = Nat.fib (j - 1) + Nat.fib (j - 2) := by
          rw [Nat.fib_add_two, show j - 2 + 1 = j - 1 by omega]
          exact Nat.add_comm _ _
    have hq4 : q < 4 * H := by omega
    refine ⟨hj5, hjq, hq4, ?_⟩
    let φ := Real.goldenRatio
    let α := φ⁻¹
    have hφ : 0 < φ := Real.goldenRatio_pos
    have hφ1 : 1 < φ := Real.one_lt_goldenRatio
    have hφsq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
    have hφhalf : (3 / 2 : Real) < φ := by nlinarith
    have hupper : ∀ k : Nat, (Nat.fib (k + 2) : Real) < φ ^ (k + 2) / 2 := by
      intro k
      induction k using Nat.twoStepInduction with
      | zero => norm_num [Nat.fib]; nlinarith
      | one =>
        norm_num [Nat.fib]
        rw [pow_succ, hφsq]
        nlinarith
      | more k ih₀ ih₁ =>
        have hp : φ ^ (k + 4) = φ ^ (k + 3) + φ ^ (k + 2) := by
          have hx := Real.goldenRatio_pow_sub_goldenRatio_pow (k + 2)
          rw [show k + 2 + 2 = k + 4 by omega,
            show k + 2 + 1 = k + 3 by omega] at hx
          linarith only [hx]
        rw [show k + 2 + 2 = (k + 2) + 2 by omega, Nat.fib_add_two, Nat.cast_add]
        rw [show k + 2 + 2 = k + 4 by omega, hp]
        have h₁ : (Nat.fib (k + 2 + 1) : Real) < φ ^ (k + 3) / 2 := by
          simpa [Nat.add_assoc] using ih₁
        linarith
    have hqR : 0 < (q : Real) := by exact_mod_cast (show 0 < q by omega)
    have hsmall : (q : Real) * α ^ j < 1 / 2 := by
      have hu := hupper (j - 2)
      rw [show j - 2 + 2 = j by omega] at hu
      have hm := mul_lt_mul_of_pos_right hu (inv_pos.mpr (pow_pos hφ j))
      have heq : φ ^ j / 2 * (φ ^ j)⁻¹ = (1 / 2 : Real) := by
        field_simp
      rw [heq] at hm
      simpa [q, α, inv_pow] using hm
    let p := Nat.fib (j - 1)
    have hcop : IsCoprime (p : Int) (q : Int) := by
      apply Nat.Coprime.isCoprime
      simpa [p, q, show j - 1 + 1 = j by omega] using Nat.fib_coprime_fib_succ (j - 1)
    have herr : |(q : Real) * α - p| = α ^ j := by
      have hg := Real.goldenConj_mul_fib_succ_add_fib (j - 1)
      rw [show j - 1 + 1 = j by omega] at hg
      have heq : (q : Real) * α - p = -Real.goldenConj ^ j := by
        dsimp [q, p, α, φ]
        rw [Real.inv_goldenRatio]
        linarith
      rw [heq, abs_neg, abs_pow]
      congr 1
      dsimp [α, φ]
      rw [abs_of_neg Real.goldenConj_neg, Real.inv_goldenRatio]
    have happ : |α - (p : Real) / q| < 1 / (2 * (q : Real) ^ 2) := by
      have heq : α - (p : Real) / q = ((q : Real) * α - p) / q := by
        field_simp
      rw [heq, abs_div, abs_of_pos hqR, herr]
      apply (div_lt_iff₀ hqR).2
      rw [show 1 / (2 * (q : Real) ^ 2) * q = 1 / (2 * (q : Real)) by field_simp]
      apply (lt_div_iff₀ (by positivity : 0 < 2 * (q : Real))).2
      nlinarith only [hsmall]
    intro A B
    let : NeZero H := ⟨by omega⟩
    let a := A.val
    let b := B.val
    have ha : a < H := ZMod.val_lt A
    have hb : b < H := ZMod.val_lt B
    let θ : Real := ((b : Real) + 1) * α / H
    let x : Real := ((a : Real) + 1 / 2) / H
    let k : Int := round ((q : Real) * (x - θ))
    obtain ⟨r, s, hrs⟩ := hcop
    let d : Int := (k * r - 1) / q
    let t : Int := (k * r - 1) % q + 1
    have hqI : 0 < (q : Int) := by exact_mod_cast hqR
    have ht0 : 0 < t := by
      dsimp [t]
      have he := Int.emod_nonneg (k * r - 1) hqI.ne'
      omega
    have htq : t ≤ q := by
      dsimp [t]
      have he := Int.emod_lt_of_pos (k * r - 1) hqI
      omega
    have ht : t = k * r - (q : Int) * d := by
      have hd := Int.emod_add_mul_ediv (k * r - 1) (q : Int)
      dsimp [t, d]
      nlinarith
    let z : Int := -(k * s) - (p : Int) * d
    have htz : t * (p : Int) = k + (q : Int) * z := by
      dsimp [z]
      rw [ht]
      nlinarith [congrArg (fun v : Int => k * v) hrs]
    have htzR : (t : Real) * p = (k : Real) + (q : Real) * z := by
      exact_mod_cast htz
    have hgrid : |x - (θ + (t : Real) * p / q - z)| ≤ 1 / (2 * (q : Real)) := by
      have hrnd := abs_sub_round ((q : Real) * (x - θ))
      have heq : x - (θ + (t : Real) * p / q - z) =
          ((q : Real) * (x - θ) - k) / q := by
        apply (eq_div_iff hqR.ne').2
        field_simp at *
        nlinarith [htzR]
      rw [heq, abs_div, abs_of_pos hqR]
      apply (div_le_iff₀ hqR).2
      dsimp [k] at *
      convert hrnd using 1
      field_simp
    have htR : 0 < (t : Real) := by exact_mod_cast ht0
    have htqR : (t : Real) ≤ q := by exact_mod_cast htq
    have hpert : |(t : Real) * (α - (p : Real) / q)| < 1 / (2 * (q : Real)) := by
      rw [abs_mul, abs_of_pos htR]
      calc
        (t : Real) * |α - (p : Real) / q| <
            (t : Real) * (1 / (2 * (q : Real) ^ 2)) := mul_lt_mul_of_pos_left happ htR
        _ ≤ (q : Real) * (1 / (2 * (q : Real) ^ 2)) :=
          mul_le_mul_of_nonneg_right htqR (by positivity)
        _ = 1 / (2 * (q : Real)) := by field_simp
    have hdist : |x - (θ + (t : Real) * α - z)| < 1 / (q : Real) := by
      have htriangle := abs_add_le
        (x - (θ + (t : Real) * p / q - z))
        (-((t : Real) * (α - (p : Real) / q)))
      have heq : x - (θ + (t : Real) * α - z) =
          (x - (θ + (t : Real) * p / q - z)) -
          (t : Real) * (α - (p : Real) / q) := by ring
      rw [heq]
      rw [abs_neg] at htriangle
      calc
        |(x - (θ + (t : Real) * p / q - z)) - (t : Real) * (α - (p : Real) / q)|
            ≤ |x - (θ + (t : Real) * p / q - z)| +
              |(t : Real) * (α - (p : Real) / q)| := by
                simpa only [sub_eq_add_neg] using htriangle
        _ < 1 / (2 * (q : Real)) + 1 / (2 * (q : Real)) :=
          add_lt_add_of_le_of_lt hgrid hpert
        _ = 1 / (q : Real) := by ring
    have hHR : 0 < (H : Real) := by exact_mod_cast (show 0 < H by omega)
    have hqHR : 2 * (H : Real) < q := by exact_mod_cast hjq
    have hradius : 1 / (q : Real) < 1 / (2 * (H : Real)) :=
      one_div_lt_one_div_of_lt (by positivity) hqHR
    have hball := abs_lt.mp (hdist.trans hradius)
    let n := b + H * t.toNat
    have hnlo : H ≤ n := by
      have htNat : 1 ≤ t.toNat := by omega
      dsimp [n]
      nlinarith
    have hnhi : n < H * (q + 1) := by
      have htNat : t.toNat ≤ q := by omega
      dsimp [n]
      nlinarith
    have hnR : (n : Real) = (b : Real) + (H : Real) * t := by
      dsimp [n]
      have htcast : (t.toNat : Real) = (t : Real) := by
        exact_mod_cast Int.toNat_of_nonneg ht0.le
      rw [Nat.cast_add, Nat.cast_mul, htcast]
    have hfloor : ⌊((n + 1 : Nat) : Real) / φ⌋ = (a : Int) + (H : Int) * z := by
      apply Int.floor_eq_iff.mpr
      have hx : (H : Real) * x = (a : Real) + 1 / 2 := by
        dsimp [x]
        field_simp
      have hθ : (H : Real) * θ = ((b : Real) + 1) * α := by
        dsimp [θ]
        field_simp
      have hnval : ((n + 1 : Nat) : Real) / φ =
          (H : Real) * (θ + (t : Real) * α - z) + (H : Real) * z := by
        rw [Nat.cast_add, Nat.cast_one, hnR]
        dsimp [α] at hθ ⊢
        rw [div_eq_mul_inv]
        linear_combination -hθ
      rw [hnval]
      push_cast
      have hleft := mul_lt_mul_of_pos_left hball.1 hHR
      have hright := mul_lt_mul_of_pos_left hball.2 hHR
      have hh : (H : Real) * (1 / (2 * (H : Real))) = 1 / 2 := by field_simp
      constructor <;> nlinarith only [hleft, hright, hx, hh]
    refine ⟨n, hnlo, hnhi, ?_, ?_⟩
    · dsimp [n]
      simp [b]
    · have hs := floor_succ_div_golden_eq_shifted (n := n) (by omega)
      change ⌊((n + 1 : Nat) : Real) / φ⌋ = _ at hs
      have hi : (shiftedFibSum n : Int) = (a : Int) + (H : Int) * z := hs.symm.trans hfloor
      have hc := congrArg (fun v : Int => (v : ZMod H)) hi
      simpa [a, Int.cast_add, Int.cast_mul] using hc

  have legal_of_no_adj (N : Nat) (f : Fin N → Bool) :
      ∀ s : Bool,
        (s = true → ∀ h : 0 < N, f ⟨0, h⟩ = false) →
        (∀ (i : Nat) (hi : i + 1 < N),
          f ⟨i, Nat.lt_of_succ_lt hi⟩ = true →
          f ⟨i + 1, hi⟩ = false) →
        legal s (List.ofFn f) := by
    induction N with
    | zero => intro s _ _; simp [legal]
    | succ N ih =>
        intro s hs hsep
        rw [List.ofFn_succ]
        have htail : legal (f ⟨0, by omega⟩)
            (List.ofFn (Fin.tail f)) := by
          apply ih (Fin.tail f) (f ⟨0, by omega⟩)
          · intro hf hpos
            have hfalse : f ⟨1, by omega⟩ = false := by
              exact hsep 0 (by omega) hf
            simpa [Fin.tail] using hfalse
          · intro i hi htrue
            have hs := hsep (i + 1) (by omega)
              (by simpa [Fin.tail] using htrue)
            simpa [Fin.tail] using hs
        change (¬(s = true ∧ f ⟨0, by omega⟩ = true) ∧
          legal (f ⟨0, by omega⟩) (List.ofFn (Fin.tail f)))
        refine ⟨?_, htail⟩
        intro hbad
        rcases hbad with ⟨hs', hbit⟩
        have hfalse := hs hs' (by omega)
        exact Bool.noConfusion (hfalse.symm.trans hbit)

  have no_consecutive_of_pairwise {l : List Nat}
      (hp : l.Pairwise (fun a b => b + 2 ≤ a)) :
      ∀ i, i ∈ l → i + 1 ∉ l := by
    induction l with
    | nil => simp
    | cons a l ih =>
        rw [List.pairwise_cons] at hp
        intro i hi hj
        simp only [List.mem_cons] at hi hj
        rcases hi with hia | hi
        · rcases hj with rfl | hj
          · omega
          · have h := hp.1 _ hj
            rw [← hia] at h
            omega
        · rcases hj with rfl | hj
          · have h := hp.1 _ hi
            omega
          · exact ih hp.2 i hi hj

  have zeckendorf_no_adj (n : Nat) (_hn : 0 < n) :
      ∀ i : Nat,
        (decide (i ∈ Nat.zeckendorf n) : Bool) = true →
        (decide (i + 1 ∈ Nat.zeckendorf n) : Bool) = false := by
    intro i hi
    have hi' : i ∈ Nat.zeckendorf n := by simpa using hi
    have hpair := (Nat.isZeckendorfRep_zeckendorf n)
    rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at hpair
    have hno := no_consecutive_of_pairwise
      (List.pairwise_append.mp hpair).1 i hi'
    by_cases hnext : i + 1 ∈ Nat.zeckendorf n
    · exact False.elim (hno hnext)
    · simp [hnext]

  have pack_legal (t : Nat) (bs : List Bool) (hl : bs.length = 3 * t)
      (s : Bool) (hs : legal s bs) :
      (pack bs).length = t ∧ flatten (pack bs) = bs := by
    induction t generalizing bs s with
    | zero =>
        have hnil : bs = [] := List.length_eq_zero_iff.1 (by omega)
        subst bs
        exact ⟨rfl, rfl⟩
    | succ t ih =>
        rcases bs with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩
        · simp at hl
        · simp at hl; omega
        · simp at hl; omega
        · have htail : tail.length = 3 * t := by
            simp only [List.length_cons] at hl
            omega
          have hlegal : legal c tail := by
            simpa only [legal] using hs |>.2 |>.2 |>.2
          obtain ⟨hlen, hflat⟩ := ih tail htail c hlegal
          cases a <;> cases b <;> cases c <;>
            simp_all [legal, pack, triple, bits, flatten]

  have pack_support (n t : Nat) (ht : 1 ≤ t)
      (hlegal : legal true (supportBits n t)) :
      (supportWord n t).length = t ∧
        flatten (supportWord n t) = supportBits n t := by
    unfold supportWord
    apply pack_legal t (supportBits n t) ?_ true hlegal
    simp only [supportBits, List.length_cons, List.length_ofFn]
    omega

  have supportBits_legal (n t : Nat) (hn : 0 < n) :
      legal true (supportBits n t) := by
    change ¬ (true = true ∧ false = true) ∧
      ¬ (false = true ∧ false = true) ∧ _
    refine ⟨by simp, by simp, ?_⟩
    apply legal_of_no_adj (3 * t - 2) (fun i =>
      decide (i.val + 2 ∈ Nat.zeckendorf n)) false
    · simp
    · intro i hi htrue
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        zeckendorf_no_adj n hn (i + 2) htrue

  have fib_value {R : Type} [CommSemiring R] (n k : Nat) (u v : R)
      (f : Fin n → Bool) :
      value ((Nat.fib k : R) * u + (Nat.fib (k + 1) : R) * v)
          ((Nat.fib (k + 1) : R) * u + (Nat.fib (k + 2) : R) * v)
          (List.ofFn f) =
        ∑ i, if f i then
          (Nat.fib (k + i.val) : R) * u +
            (Nat.fib (k + i.val + 1) : R) * v else 0 := by
    induction n generalizing k with
    | zero => simp [value]
    | succ n ih =>
        rw [List.ofFn_succ, value, Fin.sum_univ_succ]
        have hnext :
            ((Nat.fib k : R) * u + (Nat.fib (k + 1) : R) * v) +
                ((Nat.fib (k + 1) : R) * u +
                  (Nat.fib (k + 2) : R) * v) =
              (Nat.fib (k + 2) : R) * u +
                (Nat.fib (k + 3) : R) * v := by
          have hF := Nat.fib_add_two (n := k)
          have hG : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
            simpa only [Nat.add_assoc] using Nat.fib_add_two (n := k + 1)
          simp only [hF, hG, Nat.cast_add]
          ring
        have hi := ih (k + 1) (Fin.tail f)
        have hi' :
            value ((Nat.fib (k + 1) : R) * u +
                (Nat.fib (k + 2) : R) * v)
                ((Nat.fib (k + 2) : R) * u +
                  (Nat.fib (k + 3) : R) * v)
                (List.ofFn (fun i => f i.succ)) =
              ∑ i : Fin n, if f i.succ = true then
                (Nat.fib (k + 1 + i.val) : R) * u +
                  (Nat.fib (k + 1 + i.val + 1) : R) * v else 0 := by
          convert hi using 1 <;>
            simp [Fin.tail_def, show k + 1 + 1 = k + 2 by omega,
              show k + 1 + 2 = k + 3 by omega] <;>
            rfl
        rw [hnext]
        simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
        rw [hi']
        simp only [Nat.add_comm, Nat.add_left_comm]

  have sum_toFinset_fib (l : List Nat) (f : Nat → Nat)
      (hnodup : l.Nodup) :
      (∑ j ∈ l.toFinset, f j) = (l.map f).sum := by
    induction l with
    | nil => simp
    | cons a l ih =>
        obtain ⟨ha, hl⟩ := List.nodup_cons.mp hnodup
        simp [ha, ih hl]

  have gap_nodup (l : List Nat) :
      l.Pairwise (fun a b => b + 2 ≤ a) → l.Nodup := by
    induction l with
    | nil => simp
    | cons a l ih =>
        intro h
        obtain ⟨ha, hl⟩ := List.pairwise_cons.mp h
        apply List.nodup_cons.mpr
        refine ⟨?_, ih hl⟩
        intro hm
        have hh := ha a hm
        omega

  have trim_value {R : Type} [AddMonoid R]
      (u v : R) (w : List Window) :
      value u v (flatten (trim w)) = value u v (flatten w) := by
    have trim_decomp (w : List Window) :
        ∃ k : Nat, w = trim w ++ List.replicate k .zero := by
      induction w with
      | nil => exact ⟨0, rfl⟩
      | cons b w ih =>
        obtain ⟨k, hk⟩ := ih
        by_cases h : b = .zero ∧ trim w = []
        · refine ⟨k + 1, ?_⟩
          change b :: w = (if b = .zero ∧ trim w = [] then [] else b :: trim w) ++ _
          rw [if_pos h, List.nil_append, List.replicate_succ, h.1]
          congr 1
          simpa only [h.2, List.nil_append] using hk
        · refine ⟨k, ?_⟩
          change b :: w = (if b = .zero ∧ trim w = [] then [] else b :: trim w) ++ _
          rw [if_neg h, List.cons_append, ← hk]
    have value_zeros (w : List Window) (k : Nat) (u v : R) :
        value u v (flatten (w ++ List.replicate k .zero)) = value u v (flatten w) := by
      induction w generalizing u v with
      | nil =>
        simp only [List.nil_append, flatten, List.flatMap_nil, value]
        induction k generalizing u v with
        | zero => rfl
        | succ k ih =>
          simpa [List.replicate_succ, flatten, bits, value] using
            (ih (v + (u + v)) ((u + v) + (v + (u + v))))
      | cons b w ih =>
        simp only [flatten, List.flatMap_append] at ih
        cases b <;> simp [flatten, bits, value, ih]
    obtain ⟨k, hk⟩ := trim_decomp w
    calc
      value u v (flatten (trim w)) = value u v (flatten (trim w ++ List.replicate k .zero)) :=
        (value_zeros (trim w) k u v).symm
      _ = value u v (flatten w) := by rw [← hk]

  have trim_legal (w : List Window) (hw : legal true (flatten w)) :
      legal true (flatten (trim w)) := by
    have trim_decomp (w : List Window) :
        ∃ k : Nat, w = trim w ++ List.replicate k .zero := by
      induction w with
      | nil => exact ⟨0, rfl⟩
      | cons b w ih =>
        obtain ⟨k, hk⟩ := ih
        by_cases h : b = .zero ∧ trim w = []
        · refine ⟨k + 1, ?_⟩
          change b :: w = (if b = .zero ∧ trim w = [] then [] else b :: trim w) ++ _
          rw [if_pos h, List.nil_append, List.replicate_succ, h.1]
          congr 1
          simpa only [h.2, List.nil_append] using hk
        · refine ⟨k, ?_⟩
          change b :: w = (if b = .zero ∧ trim w = [] then [] else b :: trim w) ++ _
          rw [if_neg h, List.cons_append, ← hk]
    have legal_zeros (xs : List Window) (k : Nat) (s : Bool) :
        legal s (flatten (xs ++ List.replicate k .zero)) ↔
          legal s (flatten xs) := by
      induction xs generalizing s with
      | nil =>
        simp only [List.nil_append, flatten, List.flatMap_nil, legal, iff_true]
        induction k generalizing s with
        | zero => trivial
        | succ k ih => simpa [List.replicate_succ, flatten, bits, legal] using ih false
      | cons c xs ih =>
        simp only [flatten, List.flatMap_append] at ih
        cases s <;> cases c <;> simp [flatten, bits, legal, ih]
    obtain ⟨k, hk⟩ := trim_decomp w
    apply (legal_zeros (trim w) k true).1
    rw [hk] at hw
    exact hw

  have trim_length (w : List Window) : (trim w).length ≤ w.length := by
    have trim_decomp (w : List Window) :
        ∃ k : Nat, w = trim w ++ List.replicate k .zero := by
      induction w with
      | nil => exact ⟨0, rfl⟩
      | cons b w ih =>
        obtain ⟨k, hk⟩ := ih
        by_cases h : b = .zero ∧ trim w = []
        · refine ⟨k + 1, ?_⟩
          change b :: w = (if b = .zero ∧ trim w = [] then [] else b :: trim w) ++ _
          rw [if_pos h, List.nil_append, List.replicate_succ, h.1]
          congr 1
          simpa only [h.2, List.nil_append] using hk
        · refine ⟨k, ?_⟩
          change b :: w = (if b = .zero ∧ trim w = [] then [] else b :: trim w) ++ _
          rw [if_neg h, List.cons_append, ← hk]
    obtain ⟨k, hk⟩ := trim_decomp w
    have hl := congrArg List.length hk
    simp only [List.length_append, List.length_replicate] at hl
    omega

  have trim_success (w : List Window) (hw : legal true (flatten w)) :
      Success (trim w) := by
    have trim_decomp (w : List Window) :
        ∃ k : Nat, w = trim w ++ List.replicate k .zero := by
      induction w with
      | nil => exact ⟨0, rfl⟩
      | cons b w ih =>
        obtain ⟨k, hk⟩ := ih
        by_cases h : b = .zero ∧ trim w = []
        · refine ⟨k + 1, ?_⟩
          change b :: w = (if b = .zero ∧ trim w = [] then [] else b :: trim w) ++ _
          rw [if_pos h, List.nil_append, List.replicate_succ, h.1]
          congr 1
          simpa only [h.2, List.nil_append] using hk
        · refine ⟨k, ?_⟩
          change b :: w = (if b = .zero ∧ trim w = [] then [] else b :: trim w) ++ _
          rw [if_neg h, List.cons_append, ← hk]
    have legal_zeros (xs : List Window) (k : Nat) (s : Bool) :
        legal s (flatten (xs ++ List.replicate k .zero)) ↔
          legal s (flatten xs) := by
      induction xs generalizing s with
      | nil =>
        simp only [List.nil_append, flatten, List.flatMap_nil, legal, iff_true]
        induction k generalizing s with
        | zero => trivial
        | succ k ih => simpa [List.replicate_succ, flatten, bits, legal] using ih false
      | cons c xs ih =>
        simp only [flatten, List.flatMap_append] at ih
        cases s <;> cases c <;> simp [flatten, bits, legal, ih]
    have trim_terminal (w : List Window) (E : Bool) :
        (trim w).foldl (fun _ b => nonzero b) E =
          if trim w = [] then E else true := by
      induction w generalizing E with
      | nil => rfl
      | cons b w ih =>
        by_cases h : b = .zero ∧ trim w = []
        · simp [trim, h]
        · simp only [trim, if_neg h, List.foldl_cons, List.cons_ne_nil, ↓reduceIte]
          rw [ih]
          by_cases ht : trim w = []
          · have hb : b ≠ .zero := by intro hb; exact h ⟨hb, ht⟩
            simp [ht, nonzero, hb]
          · simp [ht]
    obtain ⟨k, hk⟩ := trim_decomp w
    unfold Success
    rw [(execution true true (trim w)).1.2 (trim_legal w hw)]
    simp only [endable, Option.any_some]
    rw [trim_terminal w true]
    by_cases hnil : trim w = [] <;> simp [hnil]

  have support_value {R : Type} [CommSemiring R]
      (n t : Nat) (hbound : ∀ k ∈ Nat.zeckendorf n, k < 3 * t)
      (u v : R) :
      value u v (supportBits n t) =
        (shiftedFibSum n : R) * u + (n : R) * v := by
    classical
    have hp := Nat.isZeckendorfRep_zeckendorf n
    rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at hp
    have hlo : ∀ k ∈ Nat.zeckendorf n, 2 ≤ k := by
      intro k hk
      have hh := (List.pairwise_append.mp hp).2.2 k hk 0 (by simp)
      simpa using hh
    have hnd := gap_nodup _ (List.pairwise_append.mp hp).1
    have hs (f : Nat → R) :
        (∑ i : Fin (3 * t - 2), if i.val + 2 ∈ Nat.zeckendorf n
          then f (i.val + 2) else 0) =
        ∑ k ∈ (Nat.zeckendorf n).toFinset, f k := by
      rw [← Finset.sum_filter]
      apply Finset.sum_bij (fun i _ => i.val + 2)
      · intro i hi
        exact List.mem_toFinset.mpr (Finset.mem_filter.mp hi).2
      · intro i hi j hj hij
        apply Fin.ext
        omega
      · intro k hk
        have hk' := List.mem_toFinset.mp hk
        have hl := hlo k hk'
        have hu := hbound k hk'
        refine ⟨⟨k - 2, by omega⟩, ?_, by simp; omega⟩
        apply Finset.mem_filter.mpr
        simp only [Finset.mem_univ, true_and]
        simpa only [Nat.sub_add_cancel hl] using hk'
      · intro i hi
        rfl
    have hfv := fib_value (R := R) (3 * t - 2) 1 u v
      (fun i => decide (i.val + 2 ∈ Nat.zeckendorf n))
    have hstart : value u v (supportBits n t) =
        ∑ i : Fin (3 * t - 2), if i.val + 2 ∈ Nat.zeckendorf n then
          (Nat.fib (i.val + 1) : R) * u + (Nat.fib (i.val + 2) : R) * v else 0 := by
      simpa [supportBits, value, Nat.fib_add_two, add_comm, add_left_comm, add_assoc,
        two_mul] using hfv
    rw [hstart]
    have hrewrite :
        (∑ i : Fin (3 * t - 2), if i.val + 2 ∈ Nat.zeckendorf n then
          (Nat.fib (i.val + 1) : R) * u + (Nat.fib (i.val + 2) : R) * v else 0) =
        ∑ k ∈ (Nat.zeckendorf n).toFinset,
          ((Nat.fib (k - 1) : R) * u + (Nat.fib k : R) * v) := by
      simpa using hs (fun k => (Nat.fib (k - 1) : R) * u + (Nat.fib k : R) * v)
    rw [hrewrite, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    have hA : (∑ k ∈ (Nat.zeckendorf n).toFinset, (Nat.fib (k - 1) : R)) =
        (shiftedFibSum n : R) := by
      rw [← Nat.cast_sum]
      congr 1
      exact sum_toFinset_fib _ _ hnd
    have hB : (∑ k ∈ (Nat.zeckendorf n).toFinset, (Nat.fib k : R)) = (n : R) := by
      rw [← Nat.cast_sum, sum_toFinset_fib _ _ hnd, Nat.sum_zeckendorf_fib]
    rw [hA, hB]
  obtain ⟨hj, hq, hq4, hpair⟩ := bounded_coefficient_pair H hH
  have hwords : ∀ A B : ZMod H, ∃ w : List Window,
      w.length ≤ lengthBound H ∧ w ≠ [] ∧ firstTwoZero w ∧ Success w ∧
      windowCoefficients H w = (A, B) ∧
      (∀ u v : ZMod H, value u v (flatten w) = A * u + B * v) ∧
      (∀ (epsilon : Bool) (p : List Window), legal epsilon (flatten p) →
        ∃ N : Nat, 0 < N ∧ initialized epsilon (p ++ w) = some N) := by
    intro A B
    obtain ⟨n, hnlo, hnhi, hnB, hnA⟩ := hpair A B
    have hn : 0 < n := by omega
    let t := lengthBound H
    have hm : H * (Nat.fib (firstIndex H) + 1) ≤ Nat.fib (lengthIndex H) := by
      unfold lengthIndex
      exact Nat.find_spec (p := fun k => H * (Nat.fib (firstIndex H) + 1) ≤ Nat.fib k) _
    have ht : lengthIndex H ≤ 3 * t := by dsimp [t, lengthBound]; omega
    have htpos : 1 ≤ t := by
      by_contra hh
      have heq : lengthIndex H = 0 := by dsimp [t, lengthBound] at *; omega
      rw [heq, Nat.fib_zero] at hm
      omega
    have hbnd : ∀ k ∈ Nat.zeckendorf n, k < 3 * t := by
      intro k hk
      have hkn : Nat.fib k ≤ n := by
        rw [← Nat.sum_zeckendorf_fib n]
        exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨k, hk, rfl⟩)
      have hkm : k < lengthIndex H := by
        by_contra hh
        have hf := Nat.fib_mono (by omega : lengthIndex H ≤ k)
        omega
      omega
    have hlegal := supportBits_legal n t hn
    obtain ⟨hpacklen, hpackflat⟩ := pack_support n t htpos hlegal
    let w := trim (supportWord n t)
    have hval {R : Type} [CommSemiring R] (u v : R) :
        value u v (flatten w) = (shiftedFibSum n : R) * u + (n : R) * v := by
      dsimp [w]
      rw [trim_value, hpackflat]
      exact support_value n t hbnd u v
    have hnonempty : w ≠ [] := by
      intro he
      have hz : 0 = n := by simpa [he, flatten, value] using hval (R := Nat) 0 1
      omega
    have hfirst : firstTwoZero (supportWord n t) := by
      rw [firstTwoZero, hpackflat]
      simp [supportBits]
    have hfirsttrim : firstTwoZero w := by
      cases he : supportWord n t with
      | nil => simp [w, he, trim] at hnonempty
      | cons b tail =>
        have hkeep : trim (b :: tail) = b :: trim tail := by
          change (if b = .zero ∧ trim tail = [] then [] else b :: trim tail) = _
          split
          · simp [w, trim, *] at hnonempty
          · rfl
        dsimp [w]
        rw [he, hkeep]
        rw [he] at hfirst
        cases b <;> simp [firstTwoZero, flatten, bits] at hfirst ⊢
    have hsuccess : Success w := trim_success (supportWord n t) (by rw [hpackflat]; exact hlegal)
    have hwlegal : legal true (flatten w) :=
      trim_legal (supportWord n t) (by rw [hpackflat]; exact hlegal)
    have halllegal (s : Bool) : legal s (flatten w) := by
      cases s
      · cases he : flatten w with
        | nil => trivial
        | cons b bs =>
          rw [he] at hwlegal
          exact ⟨by simp, hwlegal.2⟩
      · exact hwlegal
    have hterminal (E : Bool) : w.foldl (fun _ b => nonzero b) E = true := by
      have hh := hsuccess
      rw [Success, (execution true true w).1.2 hwlegal] at hh
      simp only [endable, Option.any_some] at hh
      cases he : w with
      | nil => exact False.elim (hnonempty he)
      | cons b bs => simpa only [he, List.foldl_cons] using hh
    have hend (s E : Bool) : endable (run (some (s, E)) w) = true := by
      rw [(execution s E w).1.2 (halllegal s)]
      simpa only [endable, Option.any_some] using hterminal E
    refine ⟨w, (trim_length _).trans (hpacklen.le), hnonempty, hfirsttrim, hsuccess, ?_, ?_, ?_⟩
    · apply Prod.ext <;> simp [windowCoefficients, hval, hnA, hnB]
    · intro u v
      rw [hval, hnA, hnB]
    · intro epsilon p hp
      have run_append (q : Option (Bool × Bool)) (a b : List Window) :
          run q (a ++ b) = run (run q a) b := by
        induction a generalizing q with
        | nil => rfl
        | cons a as ih => exact ih (step q a)
      have hout : initialized epsilon (p ++ w) =
          some ((if epsilon then 1 else 0) + value 2 3 (flatten (p ++ w))) := by
        unfold initialized observe
        rw [run_append, (execution epsilon epsilon p).1.2 hp, hend]
        rfl
      refine ⟨_, ?_, hout⟩
      exact (LiteralWindowEnd.result 0).2.2.2.2.2.2.2 epsilon (p ++ w) _ hout
  have hcover00 : Covers00 H (lengthBound H) := by
    intro A B
    obtain ⟨w, hl, hn, h00, hs, hc, _⟩ := hwords A B
    exact ⟨w, hl, hn, h00, hs, hc⟩
  have hLpos : 1 ≤ lengthBound H := by
    obtain ⟨w, hl, hn, _⟩ := hcover00 0 0
    have hw : 0 < w.length := by
      cases w with
      | nil => exact False.elim (hn rfl)
      | cons _ _ => simp
    omega
  have hcover (K : Nat) (hk : Covers00 H K) : Covers H K := by
    intro A B
    obtain ⟨w, hl, hn, _, hs, hc⟩ := hk A B
    exact ⟨w, hl, hn, hs, hc⟩
  have hdepth : D H ≤ D00 H := by
    unfold D D00
    apply sInf_le_sInf
    rintro _ ⟨K, hk, rfl⟩
    exact ⟨K, ⟨hk.1, hcover K hk.2⟩, rfl⟩
  have hdepth00 : D00 H ≤ (lengthBound H : WithTop Nat) := by
    unfold D00
    exact sInf_le ⟨lengthBound H, ⟨hLpos, hcover00⟩, rfl⟩
  have hpow : ∀ r : Nat, 2 ^ r ≤ Nat.fib (2 * r + 2) := by
    intro r
    induction r with
    | zero => norm_num
    | succ r ih =>
      have hrec := Nat.fib_add_two (n := 2 * r + 2)
      have hmono := Nat.fib_mono (show 2 * r + 2 ≤ 2 * r + 3 by omega)
      rw [pow_succ]
      have he : 2 * (r + 1) + 2 = (2 * r + 2) + 2 := by omega
      rw [he, hrec]
      nlinarith
  let k := Nat.log 2 H
  have hp : H < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide) H
  have hsq : H ^ 2 < (2 ^ (k + 1)) ^ 2 := Nat.pow_lt_pow_left hp (by decide)
  have hN : H * (Nat.fib (firstIndex H) + 1) ≤ 4 * H ^ 2 + H := by nlinarith
  have hP : 4 * H ^ 2 + H < 8 * (2 ^ (k + 1)) ^ 2 := by nlinarith
  have heq : 2 ^ (2 * k + 5) = 8 * (2 ^ (k + 1)) ^ 2 := by
    rw [show 2 * k + 5 = (k + 1) * 2 + 3 by omega, pow_add, pow_mul]
    norm_num
    ring
  have hf : H * (Nat.fib (firstIndex H) + 1) ≤ Nat.fib (4 * k + 12) := by
    calc
      H * (Nat.fib (firstIndex H) + 1) ≤ 4 * H ^ 2 + H := hN
      _ ≤ 2 ^ (2 * k + 5) := by rw [heq]; exact hP.le
      _ ≤ Nat.fib (4 * k + 12) := by
        simpa only [show 2 * (2 * k + 5) + 2 = 4 * k + 12 by omega] using
          hpow (2 * k + 5)
  have hm : lengthIndex H ≤ 4 * k + 12 := by
    unfold lengthIndex
    exact Nat.find_min' _ hf
  have hlog : lengthBound H ≤ 2 * Nat.log 2 H + 5 := by
    unfold lengthBound
    dsimp [k] at hm
    omega
  have hkpos : 1 ≤ Nat.log 2 H :=
    Nat.le_log_of_pow_le (by decide) (by simpa using hH)
  have hlog7 : lengthBound H ≤ 7 * Nat.log 2 H := by omega
  have hreal : (lengthBound H : Real) ≤ (7 / Real.log 2) * Real.log (H : Real) := by
    calc
      (lengthBound H : Real) ≤ 7 * (Nat.log 2 H : Real) := by exact_mod_cast hlog7
      _ ≤ 7 * Real.logb 2 (H : Real) :=
        mul_le_mul_of_nonneg_left (Real.natLog_le_logb H 2) (by norm_num)
      _ = (7 / Real.log 2) * Real.log (H : Real) := by unfold Real.logb; ring
  exact ⟨hj, hq, hq4, hwords, hdepth, hdepth00, hlog, hreal⟩

#print axioms result



end
end D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe
