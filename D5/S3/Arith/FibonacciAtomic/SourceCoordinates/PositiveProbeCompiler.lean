/- GID: D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SourceCoordinates/PositiveProbeCompiler
   mirror-E: none(waiver:unbounded-symbolic-construction)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Effective positive words realize all terminal shifts in two short directions. -/

import D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost
import D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling
import D5.S3.Analytic.GoldenEulerBetaZeckendorf
import D5.S1.Digit.GoldenZeckendorfLanguage
import Mathlib.Data.Nat.ModEq

/-! # Short positive terminal probes on the original natural-pair source -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PositiveProbeCompiler

open D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost
  (replace graft runWord quantity terminalGcd)
open D5.S3.Analytic.GoldenEulerBetaZeckendorf
  (canonical_pairwise canonical_two_le)

/-- The least positive direction whose next unavailable weight bounds the modulus. -/
def direction (H : ℕ) : ℕ := Nat.find (show ∃ k, 1 ≤ k ∧ H ≤ Nat.fib (k + 4) from by
  refine ⟨H + 1, by omega, ?_⟩
  exact (by omega : H ≤ H + 1 + 4).trans (Nat.le_fib_self (by omega)))

/-- One reserve graft and the ceiling of half the available positions. -/
def graftBound (H : ℕ) : ℕ := 1 + (direction H + 2) / 2

/-- A nonnegative shift representative that never asks for an unavailable weight one. -/
def positiveLift (H c : ℕ) : ℕ :=
  if c % H = 0 then 0 else if c % H = 1 then H + 1 else c % H

/-- Descending actual Fibonacci weights; the auxiliary index two is removed. -/
def weights (H c : ℕ) : List ℕ :=
  if c % H = 0 then [] else
    let z := Nat.zeckendorf (positiveLift H c - 2)
    z.filter (fun i => i ≠ 2) ++ [if 2 ∈ z then 4 else 3]

/-- Emit in chronological order. True is one original R, false one original G.
The parameter k is the number of R calls still to emit. -/
def emit : ℕ → List ℕ → List Bool
  | k, [] => List.replicate k true
  | k, i :: l => List.replicate (k - (i - 3)) true ++ false :: emit (i - 3) l

/-- Public compilation depends only on the modulus, direction and requested shift. -/
def compile (H k c : ℕ) : List Bool := emit k (weights H c)

private theorem gap_length (l : List ℕ) (a b : ℕ) (hab : a ≤ b + 2)
    (hp : l.Pairwise (fun x y => y + 2 ≤ x))
    (hb : ∀ i ∈ l, a ≤ i ∧ i ≤ b) : 2 * l.length + a ≤ b + 2 := by
  induction l generalizing b with
  | nil => simpa using hab
  | cons i l ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
    have hi := hb i (by simp)
    by_cases hl : l = []
    · subst l; simp only [List.length_cons, List.length_nil]; omega
    · obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil l hl
      have hj' := hb j (by simp [hj])
      have hij := hhead j hj
      have hrec := ih (i - 2) (by omega) htail (by
        intro t ht
        have ht' := hb t (by simp [ht])
        have hit := hhead t ht
        exact ⟨ht'.1, by omega⟩)
      simp only [List.length_cons]
      omega

private theorem remove_auxiliary (l : List ℕ) (hn : l.Nodup) :
    ((l.filter (fun i => i ≠ 2)).map Nat.fib).sum +
        (if 2 ∈ l then 1 else 0) = (l.map Nat.fib).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hnot : i ∉ l := (List.nodup_cons.mp hn).1
    have htail : l.Nodup := (List.nodup_cons.mp hn).2
    have hrec := ih htail
    by_cases hi : i = 2
    · subst i
      simp [hnot] at hrec ⊢
      omega
    · by_cases htwo : 2 ∈ l
      all_goals simp [hi, Ne.symm hi, htwo] at hrec ⊢; omega

private theorem representation (H c : ℕ) (hH : 1 < H) :
    (weights H c).Pairwise (fun x y => y ≤ x) ∧
    (∀ i ∈ weights H c, 3 ≤ i ∧ i ≤ direction H + 3) ∧
    (weights H c).length ≤ graftBound H ∧
    ((weights H c).map Nat.fib).sum = positiveLift H c ∧
    positiveLift H c ≡ c [MOD H] := by
  have hK := Nat.find_spec (show ∃ k, 1 ≤ k ∧ H ≤ Nat.fib (k + 4) from by
    refine ⟨H + 1, by omega, ?_⟩
    exact (by omega : H ≤ H + 1 + 4).trans (Nat.le_fib_self (by omega)))
  change 1 ≤ direction H ∧ H ≤ Nat.fib (direction H + 4) at hK
  have hmod : c % H < H := Nat.mod_lt c (by omega)
  by_cases hz : c % H = 0
  · refine ⟨by simp [weights, hz], by simp [weights, hz],
      by simp [weights, hz], by simp [weights, positiveLift, hz], ?_⟩
    change positiveLift H c % H = c % H
    simp only [positiveLift, hz, ↓reduceIte, Nat.zero_mod]
  have ht : 2 ≤ positiveLift H c ∧ positiveLift H c ≤ H + 1 := by
    simp only [positiveLift, hz, ↓reduceIte]
    split_ifs <;> omega
  let z := Nat.zeckendorf (positiveLift H c - 2)
  let core := z.filter (fun i => i ≠ 2)
  have hp := canonical_pairwise (positiveLift H c - 2)
  change z.Pairwise (fun x y => y + 2 ≤ x) at hp
  have hn : z.Nodup := hp.imp (by intro x y h; omega)
  have hcore : core.Pairwise (fun x y => y + 2 ≤ x) := hp.filter _
  have hsum := Nat.sum_zeckendorf_fib (positiveLift H c - 2)
  change (z.map Nat.fib).sum = positiveLift H c - 2 at hsum
  have hi (i : ℕ) (him : i ∈ z) : 2 ≤ i ∧ i ≤ direction H + 3 := by
    have hlo := canonical_two_le (positiveLift H c - 2) i him
    have hfi : Nat.fib i ≤ positiveLift H c - 2 := by
      rw [← hsum]
      exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨i, him, rfl⟩)
    have hupper : i < direction H + 4 := by
      by_contra hh
      have hf := Nat.fib_mono (by omega : direction H + 4 ≤ i)
      omega
    exact ⟨hlo, by omega⟩
  have hc (i : ℕ) (him : i ∈ core) : 3 ≤ i ∧ i ≤ direction H + 3 := by
    obtain ⟨him, hne⟩ := List.mem_filter.mp him
    have := hi i him
    simp only [ne_eq, decide_eq_true_eq] at hne
    omega
  have hlen : core.length ≤ (direction H + 2) / 2 := by
    have h := gap_length core 3 (direction H + 3) (by omega) hcore hc
    omega
  have haux := remove_auxiliary z hn
  have hlast : ∀ i ∈ core, (if 2 ∈ z then 4 else 3) ≤ i := by
    intro i him
    by_cases htwo : 2 ∈ z
    · have hno := D5.S1.Digit.GoldenZeckendorfLanguage.canonical_indices_not_adjacent
        z (Nat.isZeckendorfRep_zeckendorf _) 2
      have hm := (List.mem_filter.mp him).1
      have hil := (hc i him).1
      simp only [htwo, ↓reduceIte]
      by_contra hh
      have : i = 3 := by omega
      exact hno ⟨htwo, by simpa [this] using hm⟩
    · simpa [htwo] using (hc i him).1
  have hw : weights H c = core ++ [if 2 ∈ z then 4 else 3] := by
    simp only [weights, hz, ↓reduceIte]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hw, List.pairwise_append]
    exact ⟨hcore.imp (by intro x y h; omega), by simp, by simpa using hlast⟩
  · intro i him
    rw [hw, List.mem_append, List.mem_singleton] at him
    rcases him with him | rfl
    · exact hc i him
    · split_ifs <;> omega
  · simp only [hw, List.length_append, List.length_singleton, graftBound]
    omega
  · rw [hw, List.map_append, List.sum_append]
    simp only [List.map_singleton, List.sum_singleton]
    change (core.map Nat.fib).sum + _ = _ at haux
    rw [hsum] at haux
    by_cases htwo : 2 ∈ z
    all_goals simp only [htwo, ↓reduceIte] at haux ⊢; norm_num at *; omega
  · change positiveLift H c % H = c % H
    simp only [positiveLift, hz, ↓reduceIte]
    split_ifs with h1
    · simp [Nat.mod_eq_of_lt (by omega : 1 < H), h1]
    · exact Nat.mod_mod c H

theorem run_append (l m : List Bool) (v : ℕ × ℕ) :
    runWord (l ++ m) v = runWord m (runWord l v) := by
  induction l generalizing v with
  | nil => rfl
  | cons b l ih => exact ih (TerminalGcdAcquisitionCost.step b v)

theorem run_replacements (k : ℕ) (v : ℕ × ℕ) :
    runWord (List.replicate k true) v = replace^[k] v := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ, runWord,
      TerminalGcdAcquisitionCost.step, Function.iterate_succ_apply] using ih (replace v)

private theorem quantity_graft (k : ℕ) (v : ℕ × ℕ) :
    quantity (replace^[k] (graft v)) = quantity (replace^[k] v) + Nat.fib (k + 3) := by
  change GraftAffineClosure.quantity (GraftAffineClosure.step^[k] (graft v)) =
    GraftAffineClosure.quantity (GraftAffineClosure.step^[k] v) + Nat.fib (k + 3)
  rw [GlobalGcdSampling.actual_source_value, GlobalGcdSampling.actual_source_value]
  simp only [graft]
  ring

private theorem emit_spec (l : List ℕ) (k : ℕ)
    (hp : l.Pairwise (fun x y => y ≤ x))
    (hb : ∀ i ∈ l, 3 ≤ i ∧ i ≤ k + 3) :
    (emit k l).count true = k ∧ (emit k l).count false = l.length ∧
    ∀ v : ℕ × ℕ, quantity (runWord (emit k l) v) =
      quantity (replace^[k] v) + (l.map Nat.fib).sum := by
  induction l generalizing k with
  | nil => simp [emit, run_replacements, List.count_replicate]
  | cons i l ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
    have hi := hb i (by simp)
    have hrec := ih (i - 3) htail (by
      intro j hj
      have hj' := hb j (by simp [hj])
      have hji := hhead j hj
      exact ⟨hj'.1, by omega⟩)
    have hidx : i - 3 + (k - (i - 3)) = k := by omega
    refine ⟨?_, ?_, ?_⟩
    · simp [emit, hrec.1]
      omega
    · simp [emit, List.count_replicate, hrec.2.1]
    · intro v
      rw [emit, run_append, run_replacements]
      change quantity (runWord (emit (i - 3) l)
        (graft (replace^[k - (i - 3)] v))) = _
      rw [hrec.2.2, quantity_graft, ← Function.iterate_add_apply, hidx]
      simp only [List.map_cons, List.sum_cons, Nat.sub_add_cancel hi.1]
      omega

/-- One effective public compiler covers both original short directions, all
requested shifts and every actual natural pair, including zero. -/
theorem effective_short_compiler (H : ℕ) (hH : 1 < H) :
    1 ≤ direction H ∧ H ≤ Nat.fib (direction H + 4) ∧
    (∀ j, 1 ≤ j → H ≤ Nat.fib (j + 4) → direction H ≤ j) ∧
    ∀ (k c : ℕ), (k = direction H ∨ k = direction H + 1) →
      (weights H c).Pairwise (fun x y => y ≤ x) ∧
      (∀ i ∈ weights H c, 3 ≤ i ∧ i ≤ direction H + 3) ∧
      ((weights H c).map Nat.fib).sum = positiveLift H c ∧
      (compile H k c).count true = k ∧
      (compile H k c).count false = (weights H c).length ∧
      (compile H k c).count false ≤ graftBound H ∧
      ∀ v : ℕ × ℕ,
        quantity (runWord (compile H k c) v) =
          quantity (replace^[k] v) + positiveLift H c ∧
        terminalGcd H (compile H k c) v =
          Nat.gcd (quantity (replace^[k] v) + c) H := by
  have hspec : 1 ≤ direction H ∧ H ≤ Nat.fib (direction H + 4) := by
    unfold direction
    exact Nat.find_spec (p := fun k : ℕ => 1 ≤ k ∧ H ≤ Nat.fib (k + 4)) _
  refine ⟨hspec.1, hspec.2, ?_, ?_⟩
  · intro j hj hb
    unfold direction
    exact Nat.find_min' (p := fun k : ℕ => 1 ≤ k ∧ H ≤ Nat.fib (k + 4)) _ ⟨hj, hb⟩
  · intro k c hk
    obtain ⟨hp, hb, hlen, hsum, hmod⟩ := representation H c hH
    have hk' : direction H ≤ k := by rcases hk with rfl | rfl <;> omega
    obtain ⟨hr, hg, hq⟩ := emit_spec (weights H c) k hp (by
      intro i hi; obtain ⟨hlo, hhi⟩ := hb i hi; exact ⟨hlo, by omega⟩)
    refine ⟨hp, hb, hsum, hr, hg, hg ▸ hlen, ?_⟩
    intro v
    have heq : quantity (runWord (compile H k c) v) =
        quantity (replace^[k] v) + positiveLift H c := by
      simpa only [compile, hsum] using hq v
    refine ⟨heq, ?_⟩
    unfold terminalGcd
    rw [heq]
    exact ((Nat.ModEq.refl (quantity (replace^[k] v))).add hmod).gcd_eq

#print axioms effective_short_compiler

end D5.S3.Arith.FibonacciAtomic.SourceCoordinates.PositiveProbeCompiler
