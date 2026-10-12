/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/FloorSelectorCycles
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: FloorSelectorCycles for width-three bridge flow. -/

/-
proof_shape: jump_zero_or_one: bind-only; consumer: FloorSelectorCycles.jump_one_iff_floor
escape_witness: jump_zero_or_one: none
proof_shape: opposite_direction_excess: bind-only; consumer: CyclicResolvent.forward_supported_zero
escape_witness: opposite_direction_excess: none
proof_shape: jump_one_iff_fin_selector: bind-only; consumer: FloorSelectorCycles.jump_one_iff_index_zero
escape_witness: jump_one_iff_fin_selector: none
proof_shape: monodromy_forces_zero: bind-only; consumer: FloorSelectorCycles.balanced_cycle_zero
escape_witness: monodromy_forces_zero: none
proof_shape: half_pow_lt_one: bind-only; consumer: FloorSelectorCycles.tensor_edge_product_lt_one
escape_witness: half_pow_lt_one: none
proof_shape: recurrence_product_bounded: bind-only; consumer: FloorSelectorCycles.balanced_cycle_zero
escape_witness: recurrence_product_bounded: none
proof_shape: balanced_cycle_zero: content
escape_witness: balanced_cycle_zero: FloorSelectorCycles.balanced_cycle_zero
proof_shape: common_node_product_bound: bind-only; consumer: CyclicResolvent.shifted_recurrence_zero
escape_witness: common_node_product_bound: none
proof_shape: backward_apply: bind-only; consumer: FloorSelectorCycles.tensor_mulVec_orbit
escape_witness: backward_apply: none
proof_shape: forwardHalf_apply: bind-only; consumer: FloorSelectorCycles.tensor_mulVec_orbit
escape_witness: forwardHalf_apply: none
proof_shape: index_val_int: bind-only; consumer: FloorSelectorCycles.index_nat
escape_witness: index_val_int: none
proof_shape: index_nat: bind-only; consumer: CyclicResolvent.reservoir_isUnit
escape_witness: index_nat: none
proof_shape: index_add_multiple: bind-only; consumer: FloorSelectorCycles.orbit_period
escape_witness: index_add_multiple: none
proof_shape: index_add_one: bind-only; consumer: FloorSelectorCycles.tensor_mulVec_orbit
escape_witness: index_add_one: none
proof_shape: index_sub_one: bind-only; consumer: FloorSelectorCycles.tensor_mulVec_orbit
escape_witness: index_sub_one: none
proof_shape: orbit_period: bind-only; consumer: CyclicResolvent.reservoir_isUnit
escape_witness: orbit_period: none
proof_shape: edge_pos: bind-only; consumer: CyclicResolvent.forward_supported_zero
escape_witness: edge_pos: none
proof_shape: tensor_mulVec_orbit: bind-only; consumer: CyclicResolvent.reservoir_mulVec_orbit
escape_witness: tensor_mulVec_orbit: none
proof_shape: whole_tensor_excess: bind-only; consumer: CyclicResolvent.forward_supported_zero
escape_witness: whole_tensor_excess: none
proof_shape: jump_index: bind-only; consumer: FloorSelectorCycles.jump_one_iff_index_zero
escape_witness: jump_index: none
proof_shape: edge_product: bind-only; consumer: FloorSelectorCycles.tensor_edge_product_lt_one
escape_witness: edge_product: none
proof_shape: tensor_edge_product_lt_one: bind-only; consumer: CyclicResolvent.reservoir_isUnit
escape_witness: tensor_edge_product_lt_one: none
admission_basis: escape-witness (balanced_cycle_zero)
Module content mechanism: nonzero_start_propagates: balanced-interval obstruction and cyclic propagation.
Direct frozen dependencies: none on the implementation baseline.
Utility: none; symbolic constructions and proofs for arbitrary dimensions,
not bounded enumeration, a checker, numeric reduction, or a certified instance.
Information-escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14762
-/

import Mathlib.Data.Rat.Floor
import Mathlib.LinearAlgebra.Matrix.Rank

set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
open Matrix Module

open Matrix Module
section

open Finset

def jump (ρ : ℚ) (n : ℤ) : ℤ := ⌈((n + 1 : ℤ) : ℚ) * ρ⌉ - ⌈(n : ℚ) * ρ⌉

private def intervalCount (ρ : ℚ) (phase : ℤ) (len : ℕ) : ℤ :=
  ∑ t ∈ range len, jump ρ (phase + t)

private theorem ceil_increment_bounds (x y : ℚ) :
    ⌊y⌋ ≤ ⌈x + y⌉ - ⌈x⌉ ∧ ⌈x + y⌉ - ⌈x⌉ ≤ ⌈y⌉ := by
  constructor
  · have h₁ := Int.ceil_lt_add_one x
    have h₂ := Int.le_ceil (x + y)
    have h₃ := Int.floor_le y
    have h : (⌊y⌋ : ℚ) - 1 < (⌈x + y⌉ : ℚ) - ⌈x⌉ := by linarith
    have hi : ⌊y⌋ - 1 < ⌈x + y⌉ - ⌈x⌉ := by exact_mod_cast h
    omega
  · have := Int.ceil_add_le x y
    omega

theorem jump_zero_or_one {ρ : ℚ} (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (n : ℤ) :
    jump ρ n = 0 ∨ jump ρ n = 1 := by
  have hmono : ⌈(n : ℚ) * ρ⌉ ≤ ⌈((n + 1 : ℤ) : ℚ) * ρ⌉ := by
    apply Int.ceil_mono
    push_cast
    nlinarith
  have hupper : ⌈((n + 1 : ℤ) : ℚ) * ρ⌉ ≤ ⌈(n : ℚ) * ρ⌉ + 1 := by
    rw [← Int.ceil_add_one]
    apply Int.ceil_mono
    push_cast
    nlinarith
  unfold jump
  omega

private theorem intervalCount_eq (ρ : ℚ) (phase : ℤ) (len : ℕ) :
    intervalCount ρ phase len =
      ⌈((phase + len : ℤ) : ℚ) * ρ⌉ - ⌈(phase : ℚ) * ρ⌉ := by
  unfold intervalCount jump
  induction len with
  | zero => simp
  | succ len ih =>
    rw [sum_range_succ, ih]
    have he : (phase + (len + 1 : ℕ) : ℤ) = phase + len + 1 := by omega
    rw [he]
    omega

private theorem balanced_interval_bound (ρ : ℚ) (phase : ℤ) (len : ℕ) :
    ⌊(len : ℚ) * ρ⌋ ≤ intervalCount ρ phase len ∧
    intervalCount ρ phase len ≤ ⌈(len : ℚ) * ρ⌉ := by
  rw [intervalCount_eq]
  have := ceil_increment_bounds ((phase : ℚ) * ρ) ((len : ℚ) * ρ)
  convert this using 2 <;> congr 1 <;> push_cast <;> ring

private theorem paired_interval_excess {ρI ρO : ℚ} (hρ : ρI ≤ ρO)
    (phaseI phaseO : ℤ) (len : ℕ) :
    intervalCount ρI phaseI len - intervalCount ρO phaseO len ≤ 1 := by
  have hI := (balanced_interval_bound ρI phaseI len).2
  have hO := (balanced_interval_bound ρO phaseO len).1
  have hmono : ⌈(len : ℚ) * ρI⌉ ≤ ⌈(len : ℚ) * ρO⌉ :=
    Int.ceil_mono (mul_le_mul_of_nonneg_left hρ (Nat.cast_nonneg _))
  have hceil := Int.ceil_le_floor_add_one ((len : ℚ) * ρO)
  omega

private theorem reverse_interval_eq (ρ : ℚ) (phase : ℤ) (len : ℕ) :
    (∑ t ∈ range len, jump ρ (phase - t)) = intervalCount ρ (phase - len + 1) len := by
  unfold intervalCount
  rw [← sum_range_reflect]
  apply sum_congr rfl
  intro t ht
  congr 1
  have ht' := mem_range.mp ht
  have hcast : ((len - 1 - t : ℕ) : ℤ) = (len : ℤ) - 1 - t := by omega
  rw [hcast]
  ring

theorem opposite_direction_excess {ρI ρO : ℚ} (hρ : ρI ≤ ρO)
    (phaseI phaseO : ℤ) (len : ℕ) :
    (∑ t ∈ range len, (jump ρI (phaseI + t) - jump ρO (phaseO - t))) ≤ 1 := by
  rw [sum_sub_distrib, reverse_interval_eq]
  exact paired_interval_excess hρ phaseI (phaseO - len + 1) len

end
section

private theorem jump_one_iff_floor {ρ : ℚ} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (n : ℤ) :
    jump ρ n = 1 ↔ ∃ k : ℤ, ⌊(k : ℚ) / ρ⌋ = n := by
  constructor
  · intro hj
    let k := ⌈(n : ℚ) * ρ⌉
    have hlow : (n : ℚ) * ρ ≤ k := Int.le_ceil _
    have hupp : (k : ℚ) < ((n + 1 : ℤ) : ℚ) * ρ := by
      apply Int.lt_ceil.mp
      unfold k
      unfold jump at hj
      omega
    refine ⟨k, Int.floor_eq_iff.mpr ⟨?_, ?_⟩⟩
    · exact (le_div_iff₀ hρ).mpr hlow
    · apply (div_lt_iff₀ hρ).mpr
      simpa using hupp
  · rintro ⟨k, hk⟩
    have hf := Int.floor_eq_iff.mp hk
    have hlow : (n : ℚ) * ρ ≤ k := (le_div_iff₀ hρ).mp hf.1
    have hupp : (k : ℚ) < ((n + 1 : ℤ) : ℚ) * ρ := by
      simpa using (div_lt_iff₀ hρ).mp hf.2
    have hceilLow : ⌈(n : ℚ) * ρ⌉ ≤ k := Int.ceil_le.mpr hlow
    have hceilHigh : k < ⌈((n + 1 : ℤ) : ℚ) * ρ⌉ := Int.lt_ceil.mpr hupp
    have hb := jump_zero_or_one hρ.le hρ₁ n
    unfold jump at *
    omega

theorem jump_one_iff_fin_selector (A B : ℕ) (hB : 0 < B) (hBA : B ≤ A) (n : Fin A) :
    jump ((B : ℚ) / A) n.val = 1 ↔ ∃ k : Fin B, n.val = k.val * A / B := by
  have hA : 0 < A := lt_of_lt_of_le hB hBA
  have hAQ : (0 : ℚ) < A := by exact_mod_cast hA
  have hBQ : (0 : ℚ) < B := by exact_mod_cast hB
  have hρ : (0 : ℚ) < (B : ℚ) / A := div_pos hBQ hAQ
  have hρ₁ : (B : ℚ) / A ≤ 1 := by
    rw [div_le_one hAQ]
    exact_mod_cast hBA
  rw [jump_one_iff_floor hρ hρ₁]
  constructor
  · rintro ⟨k, hk⟩
    have hf := Int.floor_eq_iff.mp hk
    have hk0 : 0 ≤ k := by
      have h : (0 : ℚ) ≤ k := le_trans (by positivity) ((le_div_iff₀ hρ).mp hf.1)
      exact_mod_cast h
    have hkB : k < B := by
      have hu := (div_lt_iff₀ hρ).mp hf.2
      have hn : (n.val : ℚ) + 1 ≤ A := by exact_mod_cast n.isLt
      have ht : (n.val + 1 : ℚ) * ((B : ℚ) / A) ≤ B := by
        calc
          _ ≤ (A : ℚ) * ((B : ℚ) / A) := mul_le_mul_of_nonneg_right hn hρ.le
          _ = B := by field_simp
      have h : (k : ℚ) < B := lt_of_lt_of_le hu ht
      exact_mod_cast h
    refine ⟨⟨k.toNat, by omega⟩, ?_⟩
    have hc : (k : ℚ) / ((B : ℚ) / A) = ((k.toNat * A : ℕ) : ℚ) / B := by
      have hkcast : (k.toNat : ℚ) = k := by exact_mod_cast Int.toNat_of_nonneg hk0
      rw [Nat.cast_mul, hkcast]
      field_simp
    rw [hc, Rat.floor_natCast_div_natCast] at hk
    exact_mod_cast hk.symm
  · rintro ⟨k, hk⟩
    refine ⟨k.val, ?_⟩
    have hc : ((k.val : ℤ) : ℚ) / ((B : ℚ) / A) = ((k.val * A : ℕ) : ℚ) / B := by
      push_cast
      field_simp
    rw [hc, Rat.floor_natCast_div_natCast]
    exact_mod_cast hk.symm

end
section

open Finset

theorem monodromy_forces_zero (μ z : ℚ) (hμ : μ < 1) (hfix : z = μ * z) : z = 0 := by
  have hn : 1 - μ ≠ 0 := by linarith
  have hz : (1 - μ) * z = 0 := by nlinarith
  exact (mul_eq_zero.mp hz).resolve_left hn

theorem half_pow_lt_one {n : ℕ} (hn : 0 < n) : (1 / 2 : ℚ) ^ n < 1 := by
  exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

private theorem nonzero_start_is_exclusive
    (i o : ℤ → ℤ) (z c : ℤ → ℚ)
    (hi : ∀ n, i n = 0 ∨ i n = 1) (ho : ∀ n, o n = 0 ∨ o n = 1)
    (hp : ∀ n, i n = o n → z n = c n * z (n - 1))
    (hk : ∀ n, i n = 0 → o n = 1 → z n = 0 ∧ z (n - 1) = 0)
    (a : ℤ) (hprev : z (a - 1) = 0) (hnz : z a ≠ 0) :
    i a = 1 ∧ o a = 0 := by
  rcases hi a with hi | hi <;> rcases ho a with ho | ho
  · have := hp a (hi.trans ho.symm)
    simp [hprev] at this
    exact (hnz this).elim
  · exact (hnz (hk a hi ho).1).elim
  · exact ⟨hi, ho⟩
  · have := hp a (hi.trans ho.symm)
    simp [hprev] at this
    exact (hnz this).elim

private theorem nonzero_start_propagates
    (i o : ℤ → ℤ) (z c : ℤ → ℚ)
    (hi : ∀ n, i n = 0 ∨ i n = 1) (ho : ∀ n, o n = 0 ∨ o n = 1)
    (hp : ∀ n, i n = o n → z n = c n * z (n - 1))
    (hc : ∀ n, c n ≠ 0)
    (hk : ∀ n, i n = 0 → o n = 1 → z n = 0 ∧ z (n - 1) = 0)
    (hbal : ∀ a : ℤ, ∀ len : ℕ,
      (∑ t ∈ range len, (i (a + t) - o (a + t))) ≤ 1)
    (a : ℤ) (hprev : z a = 0) (hnz : z (a + 1) ≠ 0) :
    ∀ t : ℕ, z (a + t + 1) ≠ 0 ∧
      (∑ s ∈ range (t + 1), (i (a + s + 1) - o (a + s + 1))) = 1 := by
  intro t
  induction t with
  | zero =>
    have he := nonzero_start_is_exclusive i o z c hi ho hp hk (a + 1)
      (by simpa using hprev) hnz
    refine ⟨by simpa using hnz, ?_⟩
    simp [he.1, he.2]
  | succ t ih =>
    let n : ℤ := a + (t + 1 : ℕ) + 1
    have hn : n - 1 = a + t + 1 := by dsimp [n]; omega
    have hpred : z (n - 1) ≠ 0 := hn ▸ ih.1
    have hb := hbal (a + 1) (t + 2)
    have hs : (∑ s ∈ range (t + 2), (i (a + s + 1) - o (a + s + 1))) =
        1 + (i n - o n) := by
      rw [show t + 2 = (t + 1) + 1 by omega, sum_range_succ, ih.2]
    have hb' : 1 + (i n - o n) ≤ 1 := by
      have hb'' : (∑ s ∈ range (t + 2), (i (a + s + 1) - o (a + s + 1))) ≤ 1 := by
        simpa only [add_assoc, add_comm, add_left_comm] using hb
      rwa [hs] at hb''
    have he : i n = o n := by
      rcases hi n with hI | hI <;> rcases ho n with hO | hO
      · omega
      · exact (hpred (hk n hI hO).2).elim
      · omega
      · omega
    have hnz' : z n ≠ 0 := by
      rw [hp n he]
      exact mul_ne_zero (hc n) hpred
    refine ⟨by simpa [n] using hnz', ?_⟩
    rw [hs, he]
    omega

private theorem periodic_zero_step
    (i o : ℤ → ℤ) (z c : ℤ → ℚ)
    (hi : ∀ n, i n = 0 ∨ i n = 1) (ho : ∀ n, o n = 0 ∨ o n = 1)
    (hp : ∀ n, i n = o n → z n = c n * z (n - 1))
    (hc : ∀ n, c n ≠ 0)
    (hk : ∀ n, i n = 0 → o n = 1 → z n = 0 ∧ z (n - 1) = 0)
    (hbal : ∀ a : ℤ, ∀ len : ℕ,
      (∑ t ∈ range len, (i (a + t) - o (a + t))) ≤ 1)
    (L : ℕ) (hL : 0 < L) (hperiod : ∀ n, z (n + L) = z n) :
    ∀ a, z a = 0 → z (a + 1) = 0 := by
  intro a hz
  by_contra hnz
  have h := (nonzero_start_propagates i o z c hi ho hp hc hk hbal a hz hnz (L - 1)).1
  have he : (a + (L - 1 : ℕ) + 1 : ℤ) = a + L := by omega
  rw [he, hperiod, hz] at h
  exact h rfl

end
section

open Finset

theorem recurrence_product_bounded (z f : ℕ → ℚ) (L : ℕ)
    (h : ∀ n < L, z (n + 1) = f n * z n) :
    z L = (∏ t ∈ range L, f t) * z 0 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [h L (by omega), ih (fun n hn => h n (by omega)), prod_range_succ]
    ring

theorem balanced_cycle_zero
    (i o : ℤ → ℤ) (z c : ℤ → ℚ)
    (hi : ∀ n, i n = 0 ∨ i n = 1) (ho : ∀ n, o n = 0 ∨ o n = 1)
    (hp : ∀ n, i n = o n → z n = c n * z (n - 1))
    (hc : ∀ n, c n ≠ 0)
    (hk : ∀ n, i n = 0 → o n = 1 → z n = 0 ∧ z (n - 1) = 0)
    (hbal : ∀ a : ℤ, ∀ len : ℕ,
      (∑ t ∈ range len, (i (a + t) - o (a + t))) ≤ 1)
    (L : ℕ) (hL : 0 < L) (hperiod : ∀ n, z (n + L) = z n)
    (hwhole : ∀ a : ℤ, (∑ t ∈ range L, (i (a + t) - o (a + t))) ≤ 0)
    (hproduct : ∀ a : ℤ, (∏ t ∈ range L, c (a + t + 1)) < 1) :
    ∀ a, z a = 0 := by
  have hs := periodic_zero_step i o z c hi ho hp hc hk hbal L hL hperiod
  have hiter : ∀ a : ℤ, ∀ t : ℕ, z a = 0 → z (a + t) = 0 := by
    intro a t hz
    induction t with
    | zero => simpa using hz
    | succ t ih => simpa [Nat.cast_add, add_assoc] using hs (a + t) ih
  intro a
  by_contra ha
  have hnz : ∀ t : ℕ, t ≤ L → z (a + t) ≠ 0 := by
    intro t ht hz
    have h := hiter (a + t) (L - t) hz
    have he : (a + t + (L - t : ℕ) : ℤ) = a + L := by omega
    rw [he, hperiod] at h
    exact ha h
  have hnneg : ∀ t ∈ range L, 0 ≤ i (a + t + 1) - o (a + t + 1) := by
    intro t ht
    let n : ℤ := a + t + 1
    have hprev : z (n - 1) ≠ 0 := by
      have he : n - 1 = a + t := by dsimp [n]; ring
      rw [he]
      exact hnz t (mem_range.mp ht).le
    rcases hi n with hI | hI <;> rcases ho n with hO | hO
    · simpa [n, hI, hO]
    · exact (hprev (hk n hI hO).2).elim
    · simpa [n, hI, hO]
    · simpa [n, hI, hO]
  have hsum : (∑ t ∈ range L, (i (a + t + 1) - o (a + t + 1))) = 0 := by
    apply le_antisymm
    · simpa [add_assoc, add_comm, add_left_comm] using hwhole (a + 1)
    · exact sum_nonneg hnneg
  have heq : ∀ t ∈ range L, i (a + t + 1) = o (a + t + 1) := by
    have h := (sum_eq_zero_iff_of_nonneg hnneg).mp hsum
    intro t ht
    exact sub_eq_zero.mp (h t ht)
  have hrec : ∀ t < L, z (a + (t + 1 : ℕ)) = c (a + t + 1) * z (a + t) := by
    intro t ht
    have h := hp (a + t + 1) (heq t (mem_range.mpr ht))
    have he : (a + t + 1 - 1 : ℤ) = a + t := by ring
    rw [he] at h
    simpa [Nat.cast_add, add_assoc] using h
  have hprod := recurrence_product_bounded (fun t => z (a + t))
    (fun t => c (a + t + 1)) L hrec
  simp only [Nat.cast_zero, add_zero, hperiod] at hprod
  exact ha (monodromy_forces_zero _ _ (hproduct a) hprod)

theorem common_node_product_bound (κ : ℚ) (hκ : 0 < κ)
    (o : ℤ → ℤ) (w : ℤ → ℚ) (hw : ∀ n, 0 < w n)
    (a : ℤ) (L : ℕ) :
    (∏ t ∈ range L, (if o (a + t + 1) = 1 then κ / (κ + 1) else 1) *
      w (a + t + 1)) ≤ ∏ t ∈ range L, w (a + t + 1) := by
  have hq0 : 0 < κ / (κ + 1) := div_pos hκ (by linarith)
  have hq1 : κ / (κ + 1) ≤ 1 := by
    apply (div_le_one (by linarith : (0 : ℚ) < κ + 1)).mpr
    linarith
  apply prod_le_prod
  · intro t ht
    split_ifs
    · exact (mul_pos hq0 (hw _)).le
    · simpa using (hw _).le
  · intro t ht
    split_ifs
    · exact mul_le_of_le_one_left (hw _).le hq1
    · simp

end
section

open Matrix

def backward (A : ℕ) : Matrix (Fin A) (Fin A) ℚ :=
  (1 : Matrix (Fin A) (Fin A) ℚ).submatrix (finRotate A) id

theorem backward_apply (A : ℕ) (i j : Fin A) :
    backward A i j = if j.val = (i.val + 1) % A then 1 else 0 := by
  unfold backward
  letI := i.neZero
  simp only [Matrix.submatrix_apply, Matrix.one_apply, id_eq, Fin.ext_iff,
    finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  simp only [eq_comm]

def forwardHalf (G : ℕ) : Matrix (Fin G) (Fin G) ℚ :=
  (Matrix.diagonal (fun k : Fin G => if k.val = 0 then (1 / 2 : ℚ) else 1)).submatrix
    id (finRotate G)

theorem forwardHalf_apply (G : ℕ) (i j : Fin G) :
    forwardHalf G i j = if j.val = (i.val + G - 1) % G then
      (if i.val = 0 then 1 / 2 else 1) else 0 := by
  unfold forwardHalf
  letI := i.neZero
  have h : i = finRotate G j ↔ j = (finRotate G).symm i :=
    eq_comm.trans (finRotate G).eq_symm_apply.symm
  have hv : ((finRotate G).symm i).val = (i.val + G - 1) % G := by
    rw [finRotate_symm_apply, Fin.val_sub, Fin.val_one']
    by_cases hG : G = 1
    · subst G
      simp
    · have hmod : 1 % G = 1 := Nat.mod_eq_of_lt (by have hi := i.isLt; omega)
      rw [hmod]
      congr 1
      omega
  simp only [Matrix.submatrix_apply, id_eq, Matrix.diagonal_apply, h, Fin.ext_iff, hv]

def rowSelector (A B : ℕ) : Matrix (Fin B) (Fin A) ℚ :=
  ((1 : Matrix ℕ ℕ ℚ).submatrix Fin.val (fun k : Fin B => k.val * A / B)).transpose

def reservoir (A G : ℕ) : Matrix (Fin A × Fin G) (Fin A × Fin G) ℚ :=
  1 + kronecker (-backward A) (forwardHalf G)

noncomputable def schurMap (A B G D : ℕ) (κ : ℚ) :
    Matrix (Fin B × Fin G) (Fin A × Fin D) ℚ :=
  κ • kronecker (rowSelector A B) ((rowSelector G D).transpose) +
  (kronecker (rowSelector A B) (1 : Matrix (Fin G) (Fin G) ℚ)) *
    (reservoir A G)⁻¹ *
    (kronecker (1 : Matrix (Fin A) (Fin A) ℚ) ((rowSelector G D).transpose))

def CyclicResolventLemma : Prop :=
  ∀ A B G D : ℕ, 0 < B → B ≤ A → 0 < D → D ≤ G →
  ∀ κ : ℚ, 0 < κ →
    IsUnit (reservoir A G) ∧
    (A * D ≤ B * G → Function.Injective (schurMap A B G D κ).mulVec) ∧
    (B * G ≤ A * D → Function.Surjective (schurMap A B G D κ).mulVec)

end
section

open Finset Matrix

def index (N : ℕ) (hN : 0 < N) (s : ℤ) : Fin N :=
  ⟨Int.natMod s N, Int.natMod_lt hN.ne'⟩

@[simp]
theorem index_val_int (N : ℕ) (hN : 0 < N) (s : ℤ) :
    ((index N hN s).val : ℤ) = s % N := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

@[simp]
theorem index_nat (N : ℕ) (hN : 0 < N) (i : Fin N) :
    index N hN (i.val : ℤ) = i := by
  apply Fin.ext
  apply Int.natCast_inj.mp
  rw [index_val_int, Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)]

theorem index_add_multiple (N : ℕ) (hN : 0 < N) (s k : ℤ) :
    index N hN (s + k * N) = index N hN s := by
  apply Fin.ext
  apply Int.natCast_inj.mp
  simp [index_val_int, Int.add_emod, Int.mul_emod]

theorem index_add_one (N : ℕ) (hN : 0 < N) (s : ℤ) :
    (index N hN (s + 1)).val = ((index N hN s).val + 1) % N := by
  apply Int.natCast_inj.mp
  rw [index_val_int]
  push_cast
  rw [index_val_int]
  simp [Int.add_emod]

theorem index_sub_one (N : ℕ) (hN : 0 < N) (s : ℤ) :
    (index N hN (s - 1)).val = ((index N hN s).val + N - 1) % N := by
  apply Int.natCast_inj.mp
  rw [index_val_int, Int.natCast_emod]
  have hc : (((index N hN s).val + N - 1 : ℕ) : ℤ) =
      ((index N hN s).val : ℤ) + N - 1 := by omega
  rw [hc, index_val_int]
  have he : (s % (N : ℤ) + N - 1) = (s % N - 1) + N := by ring
  rw [he, Int.add_emod_right]
  exact (Int.emod_sub_emod s N 1).symm

def orbit (A G : ℕ) (hA : 0 < A) (hG : 0 < G) (a b s : ℤ) : Fin A × Fin G :=
  (index A hA (a - s), index G hG (b + s))

def edge (G : ℕ) (hG : 0 < G) (s : ℤ) : ℚ :=
  if (index G hG s).val = 0 then 1 / 2 else 1

theorem orbit_period (A G : ℕ) (hA : 0 < A) (hG : 0 < G) (a b s : ℤ) :
    orbit A G hA hG a b (s + A * G) = orbit A G hA hG a b s := by
  apply Prod.ext
  · change index A hA (a - (s + A * G)) = index A hA (a - s)
    have he : (a - (s + A * G) : ℤ) = a - s + (-G) * A := by ring
    rw [he, index_add_multiple]
  · change index G hG (b + (s + A * G)) = index G hG (b + s)
    have he : (b + (s + A * G) : ℤ) = b + s + A * G := by ring
    rw [he, index_add_multiple]

theorem edge_pos (G : ℕ) (hG : 0 < G) (s : ℤ) : 0 < edge G hG s := by
  unfold edge
  split_ifs <;> norm_num

theorem tensor_mulVec_orbit (A G : ℕ) (hA : 0 < A) (hG : 0 < G)
    (z : Fin A × Fin G → ℚ) (a b s : ℤ) :
    (kronecker (backward A) (forwardHalf G)).mulVec z (orbit A G hA hG a b s) =
      edge G hG (b + s) * z (orbit A G hA hG a b (s - 1)) := by
  let x := orbit A G hA hG a b s
  let y := orbit A G hA hG a b (s - 1)
  have hi : y.1.val = (x.1.val + 1) % A := by
    dsimp [x, y, orbit]
    have he : a - (s - 1) = (a - s) + 1 := by ring
    rw [he, index_add_one]
  have hj : y.2.val = (x.2.val + G - 1) % G := by
    dsimp [x, y, orbit]
    have he : b + (s - 1) = (b + s) - 1 := by ring
    rw [he, index_sub_one]
  change (∑ t : Fin A × Fin G, (backward A x.1 t.1 * forwardHalf G x.2 t.2) * z t) =
    edge G hG (b + s) * z y
  rw [sum_eq_single y]
  · simp only [backward_apply, forwardHalf_apply, ← hi, ← hj, ↓reduceIte, one_mul]
    rfl
  · intro t ht hty
    have hcoords : t.1.val ≠ y.1.val ∨ t.2.val ≠ y.2.val := by
      by_contra h
      push_neg at h
      apply hty
      exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
    rcases hcoords with h | h
    · have h' : t.1.val ≠ (x.1.val + 1) % A := by rwa [← hi]
      simp [backward_apply, h']
    · have h' : t.2.val ≠ (x.2.val + G - 1) % G := by rwa [← hj]
      simp [forwardHalf_apply, h']
  · simp

end
section

open Finset

private theorem jump_period (A B : ℕ) (hA : 0 < A) (n : ℤ) :
    jump ((B : ℚ) / A) (n + A) = jump ((B : ℚ) / A) n := by
  have hAQ : (A : ℚ) ≠ 0 := by exact_mod_cast hA.ne'
  have he₁ : (((n + A + 1 : ℤ) : ℚ) * ((B : ℚ) / A)) =
      (((n + 1 : ℤ) : ℚ) * ((B : ℚ) / A)) + (B : ℤ) := by
    push_cast
    field_simp <;> ring
  have he₀ : (((n + A : ℤ) : ℚ) * ((B : ℚ) / A)) =
      (n : ℚ) * ((B : ℚ) / A) + (B : ℤ) := by
    push_cast
    field_simp <;> ring
  unfold jump
  rw [he₁, he₀, Int.ceil_add_intCast, Int.ceil_add_intCast]
  omega

private theorem jump_emod (A B : ℕ) (hA : 0 < A) (n : ℤ) :
    jump ((B : ℚ) / A) n = jump ((B : ℚ) / A) (n % A) := by
  have hp : Function.Periodic (jump ((B : ℚ) / A)) (A : ℤ) := jump_period A B hA
  have h := hp.int_mul (n / A) (n % A)
  have he : (n % A + (n / A) * A : ℤ) = n := by
    simpa [mul_comm] using Int.emod_add_mul_ediv n A
  simpa only [Int.cast_id, he] using h

private theorem whole_period_count (N C M : ℕ) (hN : 0 < N) (phase : ℤ) :
    intervalCount ((C : ℚ) / N) phase (M * N) = (M * C : ℕ) := by
  rw [intervalCount_eq]
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (((phase + (M * N : ℕ) : ℤ) : ℚ) * ((C : ℚ) / N)) =
      (phase : ℚ) * ((C : ℚ) / N) + ((M * C : ℕ) : ℤ) := by
    push_cast
    field_simp <;> ring
  rw [he, Int.ceil_add_intCast]
  omega

theorem whole_tensor_excess (A B G D : ℕ) (hA : 0 < A) (hG : 0 < G)
    (phaseI phaseO : ℤ) :
    (∑ t ∈ range (A * G), (jump ((D : ℚ) / G) (phaseI + t) -
      jump ((B : ℚ) / A) (phaseO - t))) = (A * D : ℕ) - (G * B : ℕ) := by
  rw [sum_sub_distrib, reverse_interval_eq]
  change intervalCount _ _ _ - intervalCount _ _ _ = _
  rw [whole_period_count G D A hG, show A * G = G * A by ring,
    whole_period_count A B G hA]

end
section

open Finset

theorem jump_index (A B : ℕ) (hA : 0 < A) (s : ℤ) :
    jump ((B : ℚ) / A) (index A hA s).val = jump ((B : ℚ) / A) s := by
  rw [index_val_int]
  exact (jump_emod A B hA s).symm

private theorem jump_one_iff_index_zero (G : ℕ) (hG : 0 < G) (s : ℤ) :
    jump (1 / (G : ℚ)) s = 1 ↔ (index G hG s).val = 0 := by
  have hjidx := jump_index G 1 hG s
  norm_num only [Nat.cast_one] at hjidx
  rw [← hjidx]
  have hs := jump_one_iff_fin_selector G 1 (by omega) (by omega) (index G hG s)
  norm_num only [Nat.cast_one] at hs
  rw [hs]
  constructor
  · rintro ⟨k, hk⟩
    have hz : k.val = 0 := by omega
    simpa [hz] using hk
  · intro h
    exact ⟨⟨0, by omega⟩, by simpa using h⟩

private theorem edge_eq_half_pow_jump (G : ℕ) (hG : 0 < G) (s : ℤ) :
    edge G hG s = (1 / 2 : ℚ) ^ (jump (1 / (G : ℚ)) s).toNat := by
  have hGQ : (0 : ℚ) < G := by exact_mod_cast hG
  have hρ0 : (0 : ℚ) ≤ 1 / (G : ℚ) := by positivity
  have hρ1 : 1 / (G : ℚ) ≤ 1 := by
    rw [div_le_one hGQ]
    exact_mod_cast hG
  rcases jump_zero_or_one hρ0 hρ1 s with hj | hj
  · have hn : (index G hG s).val ≠ 0 := by
      intro h
      have := (jump_one_iff_index_zero G hG s).mpr h
      omega
    simp only [edge, if_neg hn, hj, Int.toNat_zero, pow_zero]
  · have hz := (jump_one_iff_index_zero G hG s).mp hj
    simp only [edge, if_pos hz, hj, Int.toNat_one, pow_one]

theorem edge_product (G M : ℕ) (hG : 0 < G) (phase : ℤ) :
    (∏ t ∈ range (M * G), edge G hG (phase + t)) = (1 / 2 : ℚ) ^ M := by
  have hGQ : (0 : ℚ) < G := by exact_mod_cast hG
  have hρ0 : (0 : ℚ) ≤ 1 / (G : ℚ) := by positivity
  have hρ1 : 1 / (G : ℚ) ≤ 1 := by
    rw [div_le_one hGQ]
    exact_mod_cast hG
  have hnonneg : ∀ s, 0 ≤ jump (1 / (G : ℚ)) s := by
    intro s
    rcases jump_zero_or_one hρ0 hρ1 s with h | h <;> omega
  have hsum : (∑ t ∈ range (M * G), (jump (1 / (G : ℚ)) (phase + t)).toNat) = M := by
    apply Int.natCast_inj.mp
    push_cast
    simp only [Int.toNat_of_nonneg (hnonneg _)]
    simpa [intervalCount] using whole_period_count G 1 M hG phase
  simp_rw [edge_eq_half_pow_jump]
  rw [Finset.prod_pow_eq_pow_sum, hsum]

theorem tensor_edge_product_lt_one (A G : ℕ) (hA : 0 < A) (hG : 0 < G) (phase : ℤ) :
    (∏ t ∈ range (A * G), edge G hG (phase + t + 1)) < 1 := by
  have he : (∏ t ∈ range (A * G), edge G hG (phase + t + 1)) = (1 / 2 : ℚ) ^ A := by
    simpa [add_assoc, add_comm, add_left_comm] using edge_product G A hG (phase + 1)
  rw [he]
  exact half_pow_lt_one hA

end

end D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
