/- GID: D5/S1/Digit/ZeckendorfResidueTransducer
   generality: I
   mirror-B: D5/B/S1/Digit/ZeckendorfResidueTransducer
   mirror-E: none(waiver:exact-finite-state-arithmetic)
   anchors: []
   digest: A least-significant-first Fibonacci residue transducer computes canonical Zeckendorf values modulo every prime. -/

import D5.S0.Conventions.WDigits
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.ZeckendorfResidueTransducer

open D5.S0.Conventions

private local instance : IsTrans Nat (fun a b => b + 2 <= a) where
  trans _a _b _c hba hcb := hcb.trans <| le_self_add.trans hba

private local instance primeNeZero (p : Nat.Primes) : NeZero p.1 :=
  ⟨p.2.ne_zero⟩

/-- The accumulated residue and two consecutive Fibonacci weights modulo `p`. -/
structure ZeckendorfResidueState (p : Nat.Primes) where
  residue : ZMod p.1
  u : ZMod p.1
  v : ZMod p.1

/-- Consume one least-significant-first Zeckendorf bit. -/
def residueStep (p : Nat.Primes) (state : ZeckendorfResidueState p)
    (bit : Fin 2) : ZeckendorfResidueState p where
  residue := state.residue + (bit.1 : ZMod p.1) * state.u
  u := state.v
  v := state.u + state.v

/-- Run the arithmetic component from an arbitrary state. -/
def runResidueStateFrom (p : Nat.Primes) (start : ZeckendorfResidueState p)
    (bits : List (Fin 2)) : ZeckendorfResidueState p :=
  bits.foldl (residueStep p) start

/-- The Fibonacci-weighted value of a bit word whose first position has index `k`. -/
def fibonacciWeightedSumFrom : Nat -> List (Fin 2) -> Nat
  | _, [] => 0
  | k, bit :: bits =>
      bit.1 * Nat.fib k + fibonacciWeightedSumFrom (k + 1) bits

/-- Dense bits for consecutive Fibonacci indices, emitted least-significant first. -/
def denseBitsFrom (digits : List Nat) (index : Nat) :
    Nat -> List (Fin 2)
  | 0 => []
  | count + 1 =>
      (if index ∈ digits then 1 else 0) ::
        denseBitsFrom digits (index + 1) count

/-- The least-significant-first dense word induced by sparse descending indices. -/
def zeckendorfLSDWord (digits : List Nat) : List (Fin 2) :=
  match digits with
  | [] => denseBitsFrom [] 2 1
  | largest :: _ => denseBitsFrom digits 2 (largest - 1)

private theorem fibonacciWeightedSumFrom_denseBitsFrom
    (digits : List Nat) (index count : Nat) :
    fibonacciWeightedSumFrom index (denseBitsFrom digits index count) =
      (((List.range' index count).filter fun k => k ∈ digits).map Nat.fib).sum := by
  induction count generalizing index with
  | zero => simp [denseBitsFrom, fibonacciWeightedSumFrom]
  | succ count ih =>
      by_cases h : index ∈ digits
      · simp [denseBitsFrom, fibonacciWeightedSumFrom, List.range', h, ih]
      · simp [denseBitsFrom, fibonacciWeightedSumFrom, List.range', h, ih]

private theorem canonical_pairwise {digits : List Nat}
    (canonical : digits.IsZeckendorfRep) :
    digits.Pairwise fun x y => y + 2 <= x := by
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at canonical
  exact (List.pairwise_append.mp canonical).1

private theorem canonical_two_le {digits : List Nat}
    (canonical : digits.IsZeckendorfRep) :
    ∀ k ∈ digits, 2 <= k := by
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at canonical
  intro k hk
  exact (List.pairwise_append.mp canonical).2.2 k hk 0 (by simp)

private theorem fibonacciWeightedSum_zeckendorfLSDWord (n : Nat) :
    fibonacciWeightedSumFrom 2 (zeckendorfLSDWord (wdigits n)) =
      ((wdigits n).map Nat.fib).sum := by
  cases hdigits : wdigits n with
  | nil =>
      simp [zeckendorfLSDWord, denseBitsFrom, fibonacciWeightedSumFrom]
  | cons largest rest =>
      rw [zeckendorfLSDWord]
      rw [fibonacciWeightedSumFrom_denseBitsFrom]
      have canonical : (largest :: rest).IsZeckendorfRep := by
        simpa [hdigits] using wdigits_isCanonical n
      have pairwise :
          (largest :: rest).Pairwise fun x y => y + 2 <= x :=
        canonical_pairwise canonical
      have low : ∀ k ∈ largest :: rest, 2 <= k :=
        canonical_two_le canonical
      have high : ∀ k ∈ largest :: rest, k <= largest := by
        intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact le_rfl
        · have := (List.pairwise_cons.mp pairwise).1 k hk
          omega
      have nodup : (largest :: rest).Nodup := by
        have pairwiseNe : (largest :: rest).Pairwise (fun x y => x ≠ y) :=
          pairwise.imp (fun {_ _} h => by omega)
        exact pairwiseNe
      have selectedNodup :
          ((List.range' 2 (largest - 1)).filter
            fun k => k ∈ largest :: rest).Nodup :=
        (List.nodup_range' (s := 2) (n := largest - 1)).filter _
      have selectedPerm :
          List.Perm
            ((List.range' 2 (largest - 1)).filter
              (fun k => k ∈ largest :: rest))
            (largest :: rest) := by
        apply (List.perm_ext_iff_of_nodup selectedNodup nodup).2
        intro k
        simp only [List.mem_filter]
        constructor
        · exact fun h => of_decide_eq_true h.2
        · intro hk
          refine ⟨List.mem_range'.2 ⟨k - 2, ?_, ?_⟩, decide_eq_true hk⟩
          · have hlo := low k hk
            have hhi := high k hk
            omega
          · have hlo := low k hk
            omega
      exact (selectedPerm.map Nat.fib).sum_eq

private def weightedSumFrom (p : Nat.Primes) :
    ZMod p.1 -> ZMod p.1 -> List (Fin 2) -> ZMod p.1
  | _, _, [] => 0
  | u, v, bit :: bits =>
      (bit.1 : ZMod p.1) * u + weightedSumFrom p v (u + v) bits

private theorem runResidueStateFrom_residue
    (p : Nat.Primes) (bits : List (Fin 2))
    (start : ZeckendorfResidueState p) :
    (runResidueStateFrom p start bits).residue =
      start.residue + weightedSumFrom p start.u start.v bits := by
  induction bits generalizing start with
  | nil => simp [runResidueStateFrom, weightedSumFrom]
  | cons bit bits ih =>
      rw [runResidueStateFrom, List.foldl_cons]
      change
        (runResidueStateFrom p (residueStep p start bit) bits).residue =
          start.residue + weightedSumFrom p start.u start.v (bit :: bits)
      rw [ih]
      simp [residueStep, weightedSumFrom, add_assoc]

private theorem weightedSumFrom_fib
    (p : Nat.Primes) (bits : List (Fin 2)) (k : Nat) :
    weightedSumFrom p (Nat.fib k) (Nat.fib (k + 1)) bits =
      (fibonacciWeightedSumFrom k bits : ZMod p.1) := by
  induction bits generalizing k with
  | nil => simp [weightedSumFrom, fibonacciWeightedSumFrom]
  | cons bit bits ih =>
      simp only [weightedSumFrom, fibonacciWeightedSumFrom, Nat.cast_add,
        Nat.cast_mul]
      rw [show (Nat.fib k : ZMod p.1) + Nat.fib (k + 1) =
          Nat.fib (k + 2) by
        simpa only [Nat.cast_add] using
          congrArg (fun n : Nat => (n : ZMod p.1))
            (Nat.fib_add_two (n := k)).symm]
      rw [ih (k + 1)]

/-- The residue after a finite prefix is its Fibonacci-weighted value plus the start. -/
theorem residue_step_invariant
    (p : Nat.Primes) (bits : List (Fin 2)) (k : Nat) (r : ZMod p.1) :
    (runResidueStateFrom p
      ⟨r, Nat.fib k, Nat.fib (k + 1)⟩ bits).residue =
        r + (fibonacciWeightedSumFrom k bits : ZMod p.1) := by
  rw [runResidueStateFrom_residue, weightedSumFrom_fib]

/-- Initial arithmetic state at Fibonacci indices two and three. -/
def initialResidueState (p : Nat.Primes) : ZeckendorfResidueState p :=
  ⟨0, Nat.fib 2, Nat.fib 3⟩

/-- Run an arbitrary least-significant-first bit word and return its natural residue. -/
def runResidueBits (p : Nat.Primes) (bits : List (Fin 2)) : Nat :=
  (runResidueStateFrom p (initialResidueState p) bits).residue.val

/-- Every finite least-significant-first word is evaluated modulo `p`. -/
theorem run_residue_eq_sum_fib_mod
    (p : Nat.Primes) (bits : List (Fin 2)) :
    runResidueBits p bits = fibonacciWeightedSumFrom 2 bits % p.1 := by
  have invariant := residue_step_invariant p bits 2 (0 : ZMod p.1)
  have values := congrArg (fun x : ZMod p.1 => x.val) invariant
  simpa [runResidueBits, initialResidueState, ZMod.val_natCast, Nat.fib] using values

/-- Run the residue machine on the dense word induced by sparse Fibonacci indices. -/
def runZeckendorfResidueTransducer
    (p : Nat.Primes) (digits : List Nat) : Nat :=
  runResidueBits p (zeckendorfLSDWord digits)

/-- The transducer computes reduction modulo `p` on canonical Zeckendorf digits. -/
theorem zeckendorfResidueTransducer_correct
    (p : Nat.Primes) (n : ℕ) :
    runZeckendorfResidueTransducer p (wdigits n) = n % p := by
  rw [runZeckendorfResidueTransducer, run_residue_eq_sum_fib_mod,
    fibonacciWeightedSum_zeckendorfLSDWord, decode_wdigits]

example : Nat.Primes := ⟨2, by decide⟩

example : List (Fin 2) := [0, 1]

example : ZeckendorfResidueState ⟨5, by decide⟩ :=
  initialResidueState ⟨5, by decide⟩

example :
    runZeckendorfResidueTransducer ⟨5, by decide⟩ (wdigits 10) = 0 := by
  native_decide

#print axioms residue_step_invariant
#print axioms run_residue_eq_sum_fib_mod
#print axioms zeckendorfResidueTransducer_correct

end D5.S1.Digit.ZeckendorfResidueTransducer
