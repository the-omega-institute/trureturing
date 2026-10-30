/- GID: D5/S3/Arith/PisanoMatrixBridge
   generality: I
   mirror-B: D5/B/S3/Arith/PisanoMatrixBridge
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Fibonacci scalar periods equal companion-matrix orders. -/

import D5.S3.Arith.GoelPisanoRatioRefutation
import D5.S3.Arith.GoldenFibonacciModulusPeriod
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.PisanoMatrixBridge

open scoped Matrix
open D5.S0.Carrier D5.S1.Scale
open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step)
open D5.S3.Arith.GoelPisanoRatioRefutation
open D5.S3.Arith.GoldenApparition
open D5.S3.Arith.GoldenFibonacciModulusPeriod

private theorem iterate_fib (n k : ℕ) :
    (step (A := ZMod n))^[k] (0, 1) =
      ((Nat.fib k : ZMod n), (Nat.fib (k + 1) : ZMod n)) := by
  cases k with
  | zero => simp
  | succ k =>
    apply Prod.ext
    · simpa using
        D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling.iterate_first
          (k + 1) (Nat.succ_pos k) ((0, 1) : ZMod n × ZMod n)
    · simpa using
        D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling.iterate_second
          (k + 1) ((0, 1) : ZMod n × ZMod n)

theorem period_iff_return (n k : ℕ) :
    (∀ m, Nat.fib (m + k) % n = Nat.fib m % n) ↔
      Function.IsPeriodicPt (step (A := ZMod n)) k (0, 1) := by
  constructor
  · intro h
    change (step (A := ZMod n))^[k] (0, 1) = (0, 1)
    rw [iterate_fib]
    apply Prod.ext
    · have h0 := h 0
      simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr h0
    · have h1 := h 1
      simpa [Nat.add_comm] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
  · intro h m
    have hm : (step (A := ZMod n))^[m + k] (0, 1) =
        (step (A := ZMod n))^[m] (0, 1) := by
      rw [Function.iterate_add_apply, h.eq]
    have hh := congrArg Prod.fst hm
    rw [iterate_fib, iterate_fib] at hh
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hh

private theorem pi_eq_minimalPeriod (n : ℕ) :
    pisanoPeriod n = Function.minimalPeriod (step (A := ZMod n)) (0, 1) := by
  rw [Function.minimalPeriod_eq_sInf_n_pos_IsPeriodicPt]
  unfold pisanoPeriod
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq, period_iff_return]

/-- The scalar Fibonacci period is exactly the order of its companion matrix.

The proof passes through the GoldenMod encoding of consecutive Fibonacci values:
`phi^(k+1) = (F_k,F_(k+1))`.  The matrix homomorphism is injective and maps
`phi` to `!![1,1;1,0]`, so a return of the pair is equivalent to a return of
the matrix. -/
theorem pisanoPeriod_eq_matrix_order {n : ℕ} (hn : 1 < n) :
    pisanoPeriod n =
      orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod n)) := by
  have _hn0 : 0 < n := by omega
  let q : Matrix (Fin 2) (Fin 2) (ZMod n) := !![1, 1; 1, 0]
  have hMatrixOrder (m : ℕ) :
      orderOf (GoldenMod.phi : GoldenMod m) =
        orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m)) := by
    have hinj : Function.Injective (goldenMatrixHom m) := by
      intro x y h
      apply GoldenMod.ext
      · have h11 := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 1 1) h
        simpa [goldenMatrixHom, multiplicationMatrix] using h11
      · have h01 := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 0 1) h
        simpa [goldenMatrixHom, multiplicationMatrix] using h01
    have hphi : goldenMatrixHom m (GoldenMod.phi : GoldenMod m) =
        !![1, 1; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [goldenMatrixHom, multiplicationMatrix, GoldenMod.phi]
    have horder := orderOf_injective (goldenMatrixHom m).toMonoidHom
      hinj (GoldenMod.phi : GoldenMod m)
    change orderOf (goldenMatrixHom m (GoldenMod.phi : GoldenMod m)) = _ at horder
    rw [hphi] at horder
    exact horder.symm
  have hpair (k : ℕ) :
      (GoldenMod.phi : GoldenMod n) ^ (k + 1) =
        ⟨(Nat.fib k : ZMod n), (Nat.fib (k + 1) : ZMod n)⟩ := by
    have h := congrArg (GoldenMod.reduce n) (golden_phi_pow_eq_fib_pair k)
    have hreduce : GoldenMod.reduce n D5.S0.Carrier.phi = GoldenMod.phi := by
      apply GoldenMod.ext <;>
        norm_num [GoldenMod.reduce, D5.S0.Carrier.phi, GoldenMod.phi]
    simpa [map_pow, hreduce, GoldenMod.reduce, GoldenMod.phi] using h
  have hinv : (GoldenMod.phi : GoldenMod n) *
      (GoldenMod.phi - 1) = 1 := by
    apply GoldenMod.ext <;>
      simp [GoldenMod.phi, sub_eq_add_neg]
  have hstep_phi (k : ℕ) :
      Function.IsPeriodicPt (step (A := ZMod n)) k (0, 1) ↔
        (GoldenMod.phi : GoldenMod n) ^ (k + 1) = GoldenMod.phi := by
    change (step (A := ZMod n))^[k] (0, 1) = (0, 1) ↔ _
    rw [iterate_fib]
    constructor
    · intro hp
      apply GoldenMod.ext
      · have h := congrArg GoldenMod.a (hpair k)
        simpa [GoldenMod.phi] using (h.trans (congrArg Prod.fst hp))
      · have h := congrArg GoldenMod.b (hpair k)
        simpa [GoldenMod.phi] using (h.trans (congrArg Prod.snd hp))
    · intro hp
      have h := hpair k
      have ha := congrArg GoldenMod.a hp
      have hb := congrArg GoldenMod.b hp
      have ha' : (Nat.fib k : ZMod n) = 0 := by
        calc
          (Nat.fib k : ZMod n) = ((GoldenMod.phi : GoldenMod n) ^ (k + 1)).a :=
            (congrArg GoldenMod.a h).symm
          _ = (GoldenMod.phi : GoldenMod n).a := ha
          _ = 0 := by simp [GoldenMod.phi]
      have hb' : (Nat.fib (k + 1) : ZMod n) = 1 := by
        calc
          (Nat.fib (k + 1) : ZMod n) =
              ((GoldenMod.phi : GoldenMod n) ^ (k + 1)).b :=
            (congrArg GoldenMod.b h).symm
          _ = (GoldenMod.phi : GoldenMod n).b := hb
          _ = 1 := by simp [GoldenMod.phi]
      apply Prod.ext
      · exact ha'
      · exact hb'
  have hstep_matrix (k : ℕ) :
      Function.IsPeriodicPt (step (A := ZMod n)) k (0, 1) ↔ q ^ k = 1 := by
    have hinj : Function.Injective (goldenMatrixHom n) := by
      intro x y h
      apply GoldenMod.ext
      · have h11 := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) (ZMod n) => M 1 1) h
        simpa [goldenMatrixHom, multiplicationMatrix] using h11
      · have h01 := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) (ZMod n) => M 0 1) h
        simpa [goldenMatrixHom, multiplicationMatrix] using h01
    have hphi : goldenMatrixHom n (GoldenMod.phi : GoldenMod n) = q := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [q, goldenMatrixHom, multiplicationMatrix, GoldenMod.phi]
    constructor
    · intro hs
      have hp : (GoldenMod.phi : GoldenMod n) ^ (k + 1) = GoldenMod.phi :=
        (hstep_phi k).mp hs
      have hpk : (GoldenMod.phi : GoldenMod n) ^ k = 1 := by
        have hmul := congrArg (fun z : GoldenMod n => z * (GoldenMod.phi - 1)) hp
        simpa [pow_succ, mul_assoc, hinv] using hmul
      have hm : goldenMatrixHom n ((GoldenMod.phi : GoldenMod n) ^ k) =
          goldenMatrixHom n (1 : GoldenMod n) := by
        rw [hpk]
      have hq : q ^ k = 1 := by
        simpa only [map_pow, hphi, map_one] using hm
      exact hq
    · intro hq
      apply (hstep_phi k).mpr
      have hm : goldenMatrixHom n ((GoldenMod.phi : GoldenMod n) ^ k) =
          goldenMatrixHom n (1 : GoldenMod n) := by
        simpa only [map_pow, hphi, map_one] using hq
      have hpk : (GoldenMod.phi : GoldenMod n) ^ k = 1 := hinj hm
      rw [pow_succ, hpk, one_mul]
  have hmin : Function.minimalPeriod (step (A := ZMod n)) (0, 1) = orderOf q := by
    apply Nat.dvd_antisymm
    · apply (Function.isPeriodicPt_iff_minimalPeriod_dvd).mp
      apply (hstep_matrix (orderOf q)).mpr
      exact pow_orderOf_eq_one q
    · apply orderOf_dvd_of_pow_eq_one
      apply (hstep_matrix (Function.minimalPeriod (step (A := ZMod n)) (0, 1))).mp
      exact (Function.isPeriodicPt_iff_minimalPeriod_dvd).mpr (dvd_refl _)
  rw [pi_eq_minimalPeriod, hmin]

#print axioms pisanoPeriod_eq_matrix_order

end D5.S3.Arith.PisanoMatrixBridge
