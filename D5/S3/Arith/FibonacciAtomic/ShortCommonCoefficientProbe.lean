/- GID: D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe
   mirror-E: none(waiver:uniform-short-canonical-probes)
   anchors: [D5/S3/Analytic/GoldenEulerBetaZeckendorf, D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd]
   utility: none
   digest: Short canonical words realize every coefficient pair on all rows and legal prefixes. -/

import D5.S3.Analytic.GoldenEulerBetaZeckendorf
import D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
import D5.S1.Digit.GoldenZeckendorfLanguage
import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
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

attribute [local instance]
  D5.S3.Analytic.GoldenEulerBetaZeckendorf.instIsTransNatLeHAddOfNat_d5

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

set_option maxHeartbeats 2000000 in
-- The bounded real grid is connected to the public successful-word equivalence.
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
    have hupper : ∀ k : Nat, (Nat.fib (k + 2) : Real) < φ ^ (k + 2) / 2 := by
      intro k
      have hrec := Real.goldenRatio_mul_fib_succ_add_fib (k + 1)
      have hf := Nat.fib_add_two (n := k)
      have hm := Nat.fib_le_fib_succ (n := k)
      have hR : (Nat.fib (k + 2) : Real) = (Nat.fib k : Real) + Nat.fib (k + 1) := by
        exact_mod_cast hf
      have hmR : (Nat.fib k : Real) ≤ Nat.fib (k + 1) := by exact_mod_cast hm
      norm_num only [Nat.add_assoc] at hrec
      nlinarith [hφ, hφ1, hφsq]
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
      have heq : (q : Real) * α - p = -Real.goldenConj ^ j := by
        have h := fib_mul_inv_golden (k := j) (by omega)
        dsimp [q, p, α, φ]
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
  have support_offset (n r : Nat)
      (hbound : ∀ k ∈ Nat.zeckendorf n, k < 3 * (r + 1))
      (x : IndependentWord (r + 1))
      (hx : x.val = fun i => decide (i.val + 1 ∈ Nat.zeckendorf n))
      (u v : Nat) :
      independentOffset (r + 1) u v x = shiftedFibSum n * u + n * v := by
    have hlo := canonical_two_le n
    have hnd : (Nat.zeckendorf n).Nodup :=
      (canonical_pairwise n).imp (fun {a b} hab => (show a ≠ b by omega))
    have hs (f : Nat → Nat) :
        (∑ i : Fin (3 * (r + 1) - 1), if i.val + 1 ∈ Nat.zeckendorf n
          then f (i.val + 1) else 0) =
        ∑ k ∈ (Nat.zeckendorf n).toFinset, f k := by
      rw [← Finset.sum_filter]
      apply Finset.sum_bij (fun i _ => i.val + 1)
      · intro i hi
        exact List.mem_toFinset.mpr (Finset.mem_filter.mp hi).2
      · intro i hi j hj hij
        apply Fin.ext
        omega
      · intro k hk
        have hk' := List.mem_toFinset.mp hk
        have hl := hlo k hk'
        have hu := hbound k hk'
        refine ⟨⟨k - 1, by omega⟩, ?_, by simp; omega⟩
        apply Finset.mem_filter.mpr
        simp only [Finset.mem_univ, true_and]
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hk'
      · intro i hi
        rfl
    change (∑ i, if x.val i then Nat.fib i.val * u + Nat.fib (i.val + 1) * v
      else 0) = _
    rw [hx]
    simp only [decide_eq_true_eq]
    have hrewrite := hs (fun k => Nat.fib (k - 1) * u + Nat.fib k * v)
    simp only [Nat.add_sub_cancel] at hrewrite
    rw [hrewrite, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      List.sum_toFinset (fun k => Nat.fib (k - 1)) hnd,
      List.sum_toFinset Nat.fib hnd, Nat.sum_zeckendorf_fib]
    rfl
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
    obtain ⟨r, hr⟩ : ∃ r, t = r + 1 := ⟨t - 1, by omega⟩
    rw [hr] at hbnd
    let x : IndependentWord (r + 1) := ⟨
      fun i => decide (i.val + 1 ∈ Nat.zeckendorf n), by
        apply (D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant.adm_iff_no_adjacent_true
          _ _).mpr
        intro i j hij
        by_cases hmem : i.val + 1 ∈ Nat.zeckendorf n
        · right
          simp only [decide_eq_false_iff_not]
          intro hnext
          exact D5.S1.Digit.GoldenZeckendorfLanguage.canonical_indices_not_adjacent
            _ (Nat.isZeckendorfRep_zeckendorf n) (i.val + 1)
            ⟨hmem, by simpa only [← hij, Nat.add_assoc] using hnext⟩
        · left
          simp [hmem]⟩
    obtain ⟨e, hencode, hbits, hquery, hreadout⟩ := (LiteralWindowEnd.result (r + 1)).1
    let sw := e.symm x
    let w := sw.val
    have he : e sw = x := e.apply_symm_apply x
    have hoff (u v : Nat) : independentOffset (r + 1) u v (e sw) =
        shiftedFibSum n * u + n * v := by
      rw [he]
      exact support_offset n r hbnd x rfl u v
    have hsuccess : Success w := sw.property.2
    have hvalNat : value 0 1 (flatten w) = n := by
      have h := hquery sw 0 0 1
      rw [hoff] at h
      simpa [query, observe, show endable (run (some (true, true)) w) = true
        from hsuccess, w] using h
    have hnonempty : w ≠ [] := by
      intro he
      have hz : 0 = n := by simpa [he, flatten, value] using hvalNat
      omega
    have hfirsttrim : firstTwoZero w := by
      have hx0 : x.val ⟨0, by omega⟩ = false := by
        change decide (1 ∈ Nat.zeckendorf n) = false
        simp only [decide_eq_false_iff_not]
        intro hmem
        have := canonical_two_le n 1 hmem
        omega
      have htake : List.take 2 (independentBits (r + 1) x) = [false, false] := by
        have hlen : 3 * (r + 1) - 1 = (3 * r + 1) + 1 := by omega
        simp only [independentBits, List.take_succ_cons]
        rw [List.ofFn_congr hlen]
        simpa [List.ofFn_succ] using hx0
      have hpad := hbits sw
      rw [he] at hpad
      have hwlen : 2 ≤ (flatten w).length := by
        cases hw : w with
        | nil => exact False.elim (hnonempty hw)
        | cons b bs => cases b <;> simp [flatten, bits] <;> omega
      rw [hpad, pad, flatten, List.flatMap_append] at htake
      change List.take 2 (flatten w ++ _) = [false, false] at htake
      rw [List.take_append_of_le_length hwlen] at htake
      exact htake
    have hwlegal : legal true (flatten w) := by
      by_contra h
      have hnone := (execution true true w).2.2 h
      have hs := hsuccess
      rw [Success, hnone] at hs
      simp [endable] at hs
    have hcoeff : windowCoefficients H w = (A, B) := by
      apply Prod.ext
      · have h := hreadout H 1 0 sw
        rw [hoff] at h
        simpa [windowCoefficients, hnA] using h
      · have h := hreadout H 0 1 sw
        rw [hoff] at h
        simpa [windowCoefficients, hnB] using h
    have hval (u v : ZMod H) : value u v (flatten w) = A * u + B * v := by
      let : NeZero H := ⟨by omega⟩
      have h := hreadout H u.val v.val sw
      rw [hoff] at h
      simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, hnA, hnB] using h
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
    refine ⟨w, by simpa only [← hr] using sw.property.1, hnonempty, hfirsttrim, hsuccess, hcoeff, hval, ?_⟩
    intro epsilon p hp
    have hout : initialized epsilon (p ++ w) =
        some ((if epsilon then 1 else 0) + value 2 3 (flatten (p ++ w))) := by
      unfold initialized observe
      have hpw : legal epsilon (flatten (p ++ w)) := by
        rw [flatten, List.flatMap_append]
        exact (D5.S3.Arith.ZeckendorfFutureKernel.legal_append _ _ _).mpr
          ⟨hp, halllegal _⟩
      rw [(execution epsilon epsilon (p ++ w)).1.2 hpw]
      simp only [List.foldl_append, hterminal, endable, Option.any_some]
      rfl
    refine ⟨_, ?_, hout⟩
    exact (LiteralWindowEnd.result 0).2.2.2.2.2.2.2 epsilon (p ++ w) _ hout
  have hcover00 : Covers00 H (lengthBound H) := by
    intro A B
    obtain ⟨w, hl, hn, h00, hs, hc, _⟩ := hwords A B
    exact ⟨w, hl, hn, h00, hs, hc⟩
  have hLpos : 1 ≤ lengthBound H := by
    obtain ⟨w, hl, hn, _⟩ := hcover00 0 0
    have hw : 0 < w.length := List.length_pos_iff.mpr hn
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

end
end D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe
