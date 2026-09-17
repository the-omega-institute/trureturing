/- GID: D5/S1/Digit/Infinite/NoContinuousAdditionExtension
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/NoContinuousAdditionExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: No separately continuous binary operation on legal infinite digit streams extends natural number addition. -/

import D5.S1.Digit.Infinite.SuccessorContinuity
import D5.S1.Digit.Infinite.MultiplierObstruction

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.NoContinuousAdditionExtension

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.MultiplierObstruction
open scoped Topology
open Filter
open D5.S1.Digit
open D5.S1.Digit.GoldenBase4AutomataOracle

/-- A binary operation agrees with addition on every pair of natural number digit rows. -/
def ExtendsFiniteAddition (A : LegalDigits → LegalDigits → LegalDigits) : Prop :=
  ∀ n m : ℕ, A (zRow n) (zRow m) = zRow (n + m)

/-- No separately continuous binary operation on legal digit streams extends finite addition. -/
theorem result :
    ¬ ∃ A : LegalDigits → LegalDigits → LegalDigits,
      (∀ x, Continuous (A x)) ∧
      (∀ y, Continuous (fun x => A x y)) ∧ ExtendsFiniteAddition A := by
  classical
  have row_mem (n i : ℕ) :
      (zRow n).val i = true ↔ i ∈ (rawOfZeckendorf (Nat.zeckendorf n)).support := by
    have raw_mem : i ∈ (rawOfZeckendorf (Nat.zeckendorf n)).support ↔
        i + 2 ∈ Nat.zeckendorf n := by
      conv_rhs => rw [← rawToZeckendorf_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n)]
      simp [rawToZeckendorf, Finsupp.mem_toMultiset]
    rw [raw_mem]
    change decide (zeckendorfBit n i = 1) = true ↔ _
    simp only [decide_eq_true_eq]
    by_cases h : i + 2 ∈ Nat.zeckendorf n <;>
      simp [zeckendorfBit, D5.S0.Conventions.wdigits, h]
  let weight (s : Finset ℕ) : ℕ := ∑ i ∈ s, Nat.fib (i + 2)
  have finite_row (s : Finset ℕ) (hs : ∀ i ∈ s, i + 1 ∉ s) (i : ℕ) :
      (zRow (weight s)).val i = decide (i ∈ s) := by
    let r : RawDigits := Finsupp.onFinset s (fun j => if j ∈ s then 1 else 0)
      (by intro j hj; by_contra h; simp [h] at hj)
    have hc : CanonicalRaw r := by
      constructor
      · intro j
        change (if j ∈ s then 1 else 0) ≤ 1
        split <;> omega
      · intro j hj
        change (if j ∈ s then 1 else 0) = 1 at hj
        have hj' : j ∈ s := by split at hj <;> simp_all
        change (if j + 1 ∈ s then 1 else 0) = 0
        simp [hs j hj']
    have hw : rawValue r = weight s := by
      unfold rawValue
      dsimp only [r]
      rw [Finsupp.sum_onFinset _ _ _ _ (by intros; simp)]
      apply Finset.sum_congr rfl
      intro j hj
      simp [hj, D5.S0.Conventions.wValue]
    have hr : rawOfZeckendorf (Nat.zeckendorf (weight s)) = r := by
      rw [← hw, ← rawToZeckendorf_eq_zeckendorf hc, rawOfZeckendorf_rawToZeckendorf]
    have hm := row_mem (weight s) i
    rw [hr, Finsupp.mem_support_iff] at hm
    change ((zRow (weight s)).val i = true ↔ (if i ∈ s then 1 else 0) ≠ 0) at hm
    by_cases hi : i ∈ s <;> cases hb : (zRow (weight s)).val i <;> simp_all
  let positions (p n : ℕ) : Finset ℕ := (Finset.range n).image (fun j => 2 * j + p)
  have mem_positions (p n i : ℕ) :
      i ∈ positions p n ↔ ∃ j < n, i = 2 * j + p := by
    simp [positions, eq_comm]
  have positions_legal (p n : ℕ) : ∀ i ∈ positions p n, i + 1 ∉ positions p n := by
    intro i hi hi'
    obtain ⟨j, hj, he⟩ := (mem_positions p n i).mp hi
    obtain ⟨j', hj', he'⟩ := (mem_positions p n (i + 1)).mp hi'
    omega
  have weight_positions (p n : ℕ) :
      weight (positions p n) = ∑ j ∈ Finset.range n, Nat.fib (2 * j + p + 2) := by
    dsimp [weight, positions]
    rw [Finset.sum_image]
    intro a ha b hb h
    dsimp at h
    omega
  have even_sum (n : ℕ) : weight (positions 0 n) + 1 = Nat.fib (2 * n + 1) := by
    rw [weight_positions]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      conv_rhs => rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, Nat.fib_add_two]
      simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] at *
      omega
  have odd_sum (n : ℕ) : weight (positions 1 n) + 1 = Nat.fib (2 * n + 2) := by
    rw [weight_positions]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      conv_rhs => rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 2 by omega, Nat.fib_add_two]
      simp only [Nat.add_assoc, Nat.reduceAdd] at *
      omega
  have parity_positions (p n i : ℕ) (hp : p < 2) :
      i ∈ positions p n ↔ i % 2 = p ∧ i < 2 * n + p := by
    rw [mem_positions]
    constructor
    · rintro ⟨j, hj, rfl⟩
      omega
    · rintro ⟨hi, hn⟩
      exact ⟨i / 2, by omega, by omega⟩
  let u : LegalDigits := ⟨fun i => decide (i % 2 = 0), by
    intro i h
    simp only [decide_eq_true_eq] at h
    omega⟩
  let v : LegalDigits := ⟨fun i => decide (i % 2 = 1), by
    intro i h
    simp only [decide_eq_true_eq] at h
    omega⟩
  have uv : u ≠ v := by
    intro h
    have hh := congrArg (fun x : LegalDigits => x.val 0) h
    norm_num [u, v] at hh
  have even_limit : Tendsto (fun n => zRow (weight (positions 0 n))) atTop (𝓝 u) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    rw [finite_row _ (positions_legal 0 n)]
    simp only [parity_positions 0 n i (by omega)]
    have hi : i < 2 * n := by omega
    simp [hi, u]
  have odd_limit : Tendsto (fun n => zRow (weight (positions 1 n))) atTop (𝓝 v) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    rw [finite_row _ (positions_legal 1 n)]
    simp only [parity_positions 1 n i (by omega)]
    have hi : i < 2 * n + 1 := by omega
    simp [hi, v]
  have unit_bits (j i : ℕ) :
      (zRow (Nat.fib (j + 2))).val i = decide (i = j) := by
    have hs : ∀ a ∈ ({j} : Finset ℕ), a + 1 ∉ ({j} : Finset ℕ) := by
      simp
    simpa [weight] using finite_row {j} hs i
  have zero_bits (i : ℕ) : (zRow 0).val i = false := by
    simp [zRow, zeckendorfBit, D5.S0.Conventions.wdigits]
  have unit_limit : Tendsto (fun l => zRow (Nat.fib (2 * l + 3))) atTop (𝓝 (zRow 0)) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop (i + 1)] with l hl
    rw [show 2 * l + 3 = (2 * l + 1) + 2 by omega, unit_bits, zero_bits]
    simp [show i ≠ 2 * l + 1 by omega]
  have sum_bits (k l : ℕ) (hkl : l < k) (i : ℕ) :
      (zRow (weight (positions 1 k) + Nat.fib (2 * l + 3))).val i =
        decide (i = 2 * k ∨ i ∈ positions 0 (l + 1)) := by
    have fresh : 2 * k ∉ positions 0 (l + 1) := by
      rw [mem_positions]
      rintro ⟨j, hj, he⟩
      omega
    have hs : ∀ a ∈ insert (2 * k) (positions 0 (l + 1)),
        a + 1 ∉ insert (2 * k) (positions 0 (l + 1)) := by
      intro a ha hb
      simp only [Finset.mem_insert, mem_positions] at ha hb
      rcases ha with ha | ⟨j, hj, ha⟩ <;>
        rcases hb with hb | ⟨j', hj', hb⟩ <;> omega
    have hw : weight (insert (2 * k) (positions 0 (l + 1))) =
        weight (positions 1 k) + Nat.fib (2 * l + 3) := by
      have h1 := odd_sum k
      have h0 := even_sum (l + 1)
      rw [show 2 * (l + 1) + 1 = 2 * l + 3 by omega] at h0
      simp only [weight, Finset.sum_insert fresh]
      change Nat.fib (2 * k + 2) + weight (positions 0 (l + 1)) =
        weight (positions 1 k) + Nat.fib (2 * l + 3)
      omega
    rw [← hw, finite_row _ hs]
    simp
  have sum_limit (l : ℕ) :
      Tendsto (fun k => zRow (weight (positions 1 k) + Nat.fib (2 * l + 3)))
        atTop (𝓝 (zRow (weight (positions 0 (l + 1))))) := by
    apply tendsto_subtype_rng.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop (max (l + 1) (i + 1))] with k hk
    rw [sum_bits k l (by omega), finite_row _ (positions_legal 0 (l + 1))]
    simp [show i ≠ 2 * k by omega]
  rintro ⟨A, hright, hleft, hadd⟩
  have zero_slice : A (zRow 0) v = v := by
    have hh := ((hright (zRow 0)).tendsto v).comp odd_limit
    have he : (fun k => A (zRow 0) (zRow (weight (positions 1 k)))) =
        (fun k => zRow (weight (positions 1 k))) := by
      funext k
      simpa using hadd 0 (weight (positions 1 k))
    rw [Function.comp_def, he] at hh
    exact tendsto_nhds_unique hh odd_limit
  have natural_slice (l : ℕ) :
      A (zRow (Nat.fib (2 * l + 3))) v = zRow (weight (positions 0 (l + 1))) := by
    have hh := ((hright (zRow (Nat.fib (2 * l + 3)))).tendsto v).comp odd_limit
    have he : (fun k => A (zRow (Nat.fib (2 * l + 3)))
        (zRow (weight (positions 1 k)))) =
        (fun k => zRow (weight (positions 1 k) + Nat.fib (2 * l + 3))) := by
      funext k
      simpa [Nat.add_comm] using hadd (Nat.fib (2 * l + 3)) (weight (positions 1 k))
    rw [Function.comp_def, he] at hh
    exact tendsto_nhds_unique hh (sum_limit l)
  have positive_limit : Tendsto (fun l => A (zRow (Nat.fib (2 * l + 3))) v)
      atTop (𝓝 u) := by
    have hshift : Tendsto (fun l : ℕ => l + 1) atTop atTop := tendsto_add_atTop_nat 1
    have hh := even_limit.comp hshift
    simpa only [Function.comp_def, natural_slice] using hh
  have negative_limit : Tendsto (fun l => A (zRow (Nat.fib (2 * l + 3))) v)
      atTop (𝓝 v) := by
    simpa only [Function.comp_def, zero_slice] using ((hleft v).tendsto (zRow 0)).comp unit_limit
  exact uv (tendsto_nhds_unique positive_limit negative_limit)

end D5.S1.Digit.Infinite.NoContinuousAdditionExtension
