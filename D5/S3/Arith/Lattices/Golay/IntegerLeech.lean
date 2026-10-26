/- GID: D5/S3/Arith/Lattices/Golay/IntegerLeech
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Golay/IntegerLeech
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral Golay congruences give an even integral additive lattice of exact scaled minimum four. -/

import D5.S3.Arith.Lattices.Golay.GolayEncoder
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators
open D5.S3.Arith.Lattices.Golay.GolayEncoder
namespace D5.S3.Arith.Lattices.Golay.IntegerLeech

abbrev IntVector := Fin 24 → ℤ

def red (a : IntVector) : Word := fun i => (a i : F2)
def squareSum (x : IntVector) : ℤ := ∑ i, x i ^ 2

/-- Literal common parity, quotient residue word, and coordinate-sum congruence.
The parity witness is a bit, never an unrestricted integer. -/
def Admissible (C : Submodule F2 Word) (x : IntVector) : Prop :=
  ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ (∀ i, x i % 2 = m) ∧
    red (fun i => (x i - m) / 2) ∈ C ∧ (∑ i, x i) % 8 = 4 * m

theorem representation (C : Submodule F2 Word) (x : IntVector) :
    Admissible C x ↔ ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ ∃ a : IntVector,
      (∀ i, x i = m + 2 * a i) ∧ red a ∈ C ∧ (∑ i, x i) % 8 = 4 * m := by
  constructor
  · rintro ⟨m, hm, hx, hc, hs⟩
    refine ⟨m, hm, (fun i => (x i - m) / 2), ?_, hc, hs⟩
    intro i
    change x i = m + 2 * ((x i - m) / 2)
    have := hx i
    omega
  · rintro ⟨m, hm, a, hx, hc, hs⟩
    refine ⟨m, hm, ?_, ?_, hs⟩
    · intro i; rw [hx i]; rcases hm with rfl | rfl <;> omega
    · have he : (fun i => (x i - m) / 2) = a := by
        funext i; rw [hx i]; omega
      rwa [he]

private theorem admissible_zero (C : Submodule F2 Word) : Admissible C 0 := by
  apply (representation C 0).2
  refine ⟨0, Or.inl rfl, 0, by simp, ?_, by simp⟩
  have hz : red (0 : IntVector) = (0 : Word) := by ext i; simp [red]
  rw [hz]
  exact C.zero_mem

private theorem admissible_add (C : Submodule F2 Word)
    (h1 : (fun _ : Fin 24 => (1 : F2)) ∈ C)
    {x y : IntVector} (hx : Admissible C x) (hy : Admissible C y) :
    Admissible C (x+y) := by
  obtain ⟨m, hm, a, ha, hca, hsa⟩ := (representation C x).1 hx
  obtain ⟨n, hn, b, hb, hcb, hsb⟩ := (representation C y).1 hy
  let k := m + n - 2*m*n
  let d : IntVector := fun i => a i + b i + m*n
  apply (representation C (x+y)).2
  refine ⟨k, ?_, d, ?_, ?_, ?_⟩
  · dsimp [k]; rcases hm with rfl | rfl <;> rcases hn with rfl | rfl <;> norm_num
  · intro i; change x i + y i = _; rw [ha i, hb i]; dsimp [k,d]; ring
  · have hd : red d = red a + red b + (m*n : F2) • (fun _ : Fin 24 => (1 : F2)) := by
      ext i; simp [d,red]
    rw [hd]
    exact C.add_mem (C.add_mem hca hcb) (C.smul_mem _ h1)
  · simp only [Pi.add_apply, Finset.sum_add_distrib]
    dsimp [k]
    rcases hm with rfl | rfl <;> rcases hn with rfl | rfl <;> norm_num at hsa hsb ⊢ <;> omega

private theorem admissible_neg (C : Submodule F2 Word)
    (h1 : (fun _ : Fin 24 => (1 : F2)) ∈ C)
    {x : IntVector} (hx : Admissible C x) : Admissible C (-x) := by
  obtain ⟨m, hm, a, ha, hc, hs⟩ := (representation C x).1 hx
  let d : IntVector := fun i => -a i - m
  apply (representation C (-x)).2
  refine ⟨m, hm, d, ?_, ?_, ?_⟩
  · intro i; change -x i = _; rw [ha i]; dsimp [d]; ring
  · have hd : red d = -red a - (m : F2) • (fun _ : Fin 24 => (1 : F2)) := by
      ext i; simp [d,red]
    rw [hd]; exact C.sub_mem (C.neg_mem hc) (C.smul_mem _ h1)
  · simp only [Pi.neg_apply, Finset.sum_neg_distrib]
    rcases hm with rfl | rfl <;> norm_num at hs ⊢ <;> omega

/-- The subgroup is proved from the coordinate congruences. -/
def integerLattice (C : Submodule F2 Word)
    (h1 : (fun _ : Fin 24 => (1 : F2)) ∈ C) : AddSubgroup IntVector where
  carrier := Admissible C
  zero_mem' := admissible_zero C
  add_mem' := admissible_add C h1
  neg_mem' := admissible_neg C h1

private theorem weight_red (a : IntVector) :
    (weight (red a) : ℤ) = ∑ i, a i % 2 := by
  simp only [weight, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hz : red a i = 0 ↔ a i % 2 = 0 := by
    rw [red, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
    norm_num
  split_ifs with h
  · simp [hz.mp h]
  · have hp := Int.emod_nonneg (a i) (by norm_num : (2:ℤ) ≠ 0)
    have hp' := Int.emod_lt_of_pos (a i) (by norm_num : (0:ℤ) < 2)
    have hn := mt hz.mpr h
    norm_num; omega

private theorem square_mod_four (z : ℤ) : z^2 % 4 = z % 2 := by
  have hp := Int.emod_nonneg z (by norm_num : (4:ℤ) ≠ 0)
  have hp' := Int.emod_lt_of_pos z (by norm_num : (0:ℤ) < 4)
  have he : z^2 % 4 = (z%4)^2 % 4 := by
    simpa only [pow_two] using Int.mul_emod z z 4
  interval_cases h : z % 4 <;> norm_num [h] at he <;> omega

private theorem squares_div_four (C : Submodule F2 Word)
    (h4 : ∀ v ∈ C, 4 ∣ weight v) (a : IntVector) (ha : red a ∈ C) :
    4 ∣ squareSum a := by
  have h : squareSum a ≡ (weight (red a) : ℤ) [ZMOD 4] := by
    rw [weight_red]
    apply Int.ModEq.sum
    intro i _
    change (a i)^2 % 4 = (a i % 2) % 4
    have := square_mod_four (a i)
    omega
  have hw : (4 : ℤ) ∣ (weight (red a) : ℤ) := by exact_mod_cast h4 _ ha
  exact Int.modEq_zero_iff_dvd.mp (h.trans (Int.modEq_zero_iff_dvd.mpr hw))

private theorem sum_rep {x a : IntVector} {m : ℤ}
    (h : ∀ i, x i = m + 2*a i) : ∑ i, x i = 24*m + 2*∑ i, a i := by
  simp_rw [h]
  simp [Finset.sum_add_distrib, Finset.mul_sum]

private theorem square_rep {x a : IntVector} {m : ℤ}
    (h : ∀ i, x i = m + 2*a i) :
    squareSum x = 24*m^2 + 4*m*∑ i, a i + 4*squareSum a := by
  unfold squareSum
  calc
    _ = ∑ i, (m^2 + (4*m)*a i + 4*(a i)^2) := by
      apply Finset.sum_congr rfl; intro i _; rw [h i]; ring
    _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]

/-- Double evenness and the literal sum congruence imply a multiple of sixteen. -/
theorem squareSum_div_sixteen (C : Submodule F2 Word)
    (h4 : ∀ v ∈ C, 4 ∣ weight v) {x : IntVector} (hx : Admissible C x) :
    16 ∣ squareSum x := by
  obtain ⟨m, hm, a, ha, hc, hs⟩ := (representation C x).1 hx
  obtain ⟨t, ht⟩ := squares_div_four C h4 a hc
  have hsum := sum_rep ha
  have hsq := square_rep ha
  have hdiv := Int.emod_add_mul_ediv (∑ i, x i) 8
  refine ⟨-m^2 + m*((∑ i, x i)/8) + t, ?_⟩
  rw [hs] at hdiv
  have ham : (∑ i, a i) = 4*((∑ i, x i)/8) - 10*m := by omega
  rw [hsq, ht, ham]
  ring

private theorem squareSum_pos {x : IntVector} (hx : x ≠ 0) : 0 < squareSum x := by
  have hi : ∃ i, x i ≠ 0 := by
    classical
    by_contra h
    apply hx
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hi
  have hle : (x i)^2 ≤ squareSum x := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hi) hle

theorem weight_le_squares (a : IntVector) : (weight (red a) : ℤ) ≤ squareSum a := by
  rw [weight_red]
  apply Finset.sum_le_sum
  intro i _
  have h0 := Int.emod_nonneg (a i) (by norm_num : (2:ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos (a i) (by norm_num : (0:ℤ) < 2)
  have h2 := sq_nonneg (a i)
  by_cases h : a i = 0
  · simp [h]
  · have := sq_pos_of_ne_zero h; omega

/-- Every actual nonzero integer vector is covered, for any binary code with the
proved Golay divisibility and minimum-weight properties. -/
theorem construction_lower_bound (C : Submodule F2 Word)
    (h4 : ∀ v ∈ C, 4 ∣ weight v)
    (hmin : ∀ v ∈ C, v ≠ 0 → 8 ≤ weight v)
    {x : IntVector} (hx : Admissible C x) (hn : x ≠ 0) : 32 ≤ squareSum x := by
  have hd := squareSum_div_sixteen C h4 hx
  obtain ⟨m, hm, a, ha, hc, hs⟩ := (representation C x).1 hx
  rcases hm with rfl | rfl
  · by_cases hz : red a = 0
    · let b : IntVector := fun i => a i / 2
      have hab : ∀ i, a i = 2*b i := by
        intro i
        have hh : (a i : F2) = 0 := congrFun hz i
        have hh' := (ZMod.intCast_zmod_eq_zero_iff_dvd (a i) 2).mp hh
        dsimp [b]; omega
      have hxb : ∀ i, x i = 0 + 4*b i := by intro i; rw [ha i, hab i]; ring
      have hxsum : ∑ i, x i = 4*∑ i, b i := by
        simp_rw [hxb]; simp [Finset.mul_sum]
      have hb : (∑ i, b i) % 2 = 0 := by norm_num at hs; omega
      have hsq : squareSum b ≡ ∑ i, b i [ZMOD 2] := by
        apply Int.ModEq.sum
        intro i _
        change (b i)^2 % 2 = b i % 2
        rw [pow_two, Int.mul_emod]
        have h0 := Int.emod_nonneg (b i) (by norm_num : (2 : ℤ) ≠ 0)
        have h1 := Int.emod_lt_of_pos (b i) (by norm_num : (0 : ℤ) < 2)
        have h : b i % 2 = 0 ∨ b i % 2 = 1 := by omega
        rcases h with h | h <;> simp [h]
      have hsq0 : squareSum b % 2 = 0 := by
        have he := hsq.eq
        omega
      have hxnorm : squareSum x = 16*squareSum b := by
        unfold squareSum
        simp_rw [hxb]
        simp only [zero_add, mul_pow]
        norm_num
        rw [Finset.mul_sum]
      have hpos := squareSum_pos hn
      have hbpos : 0 < squareSum b := by nlinarith
      have hbtwo : 2 ≤ squareSum b := by omega
      nlinarith
    · have hw := hmin _ hc hz
      have hwl := weight_le_squares a
      have hsq := square_rep ha
      norm_num at hsq
      omega
  · have hbound : 24 ≤ squareSum x := by
      calc
        (24:ℤ) = ∑ _i : Fin 24, (1:ℤ) := by simp
        _ ≤ squareSum x := by
          apply Finset.sum_le_sum
          intro i _
          have h := ha i
          have hne : x i ≠ 0 := by omega
          have hp := sq_pos_of_ne_zero hne
          omega
    obtain ⟨k,hk⟩ := hd
    omega

/-- Integrality follows by polarization using the proved additive closure. -/
theorem pairing_integral (C : Submodule F2 Word)
    (h1 : (fun _ : Fin 24 => (1 : F2)) ∈ C)
    (h4 : ∀ v ∈ C, 4 ∣ weight v)
    {x y : IntVector} (hx : Admissible C x) (hy : Admissible C y) :
    8 ∣ ∑ i, x i * y i := by
  obtain ⟨a, ha⟩ := squareSum_div_sixteen C h4 hx
  obtain ⟨b, hb⟩ := squareSum_div_sixteen C h4 hy
  obtain ⟨c, hc⟩ := squareSum_div_sixteen C h4 (admissible_add C h1 hx hy)
  have hid : squareSum (x+y) = squareSum x + squareSum y + 2*(∑ i, x i*y i) := by
    unfold squareSum
    simp only [Pi.add_apply]
    simp_rw [add_sq]
    simp [Finset.sum_add_distrib, Finset.mul_sum, mul_assoc] <;> ring
  refine ⟨c-a-b, ?_⟩
  omega

/-- This consumes the explicitly encoded weight-eight word. -/
def shortestVector : IntVector := fun i => 2 * (if octad i = 0 then 0 else 1)

private theorem shortest_mem : Admissible code shortestVector := by
  apply (representation code shortestVector).2
  let a : IntVector := fun i => if octad i = 0 then 0 else 1
  refine ⟨0, Or.inl rfl, a, by intro i; simp [shortestVector,a], ?_, ?_⟩
  · have h : red a = octad := by
      ext i
      have hi : octad i = 0 ∨ octad i = 1 := by
        have hz := ZMod.val_lt (octad i)
        have hv : (octad i).val = 0 ∨ (octad i).val = 1 := by omega
        rcases hv with h | h
        · left; apply ZMod.val_injective 2; simpa using h
        · right; apply ZMod.val_injective 2; change (octad i).val = 1; exact h
      rcases hi with h | h <;> simp [red,a,h]
    rw [h]; exact octad_mem
  · have h : ∑ i, shortestVector i = 2*(weight octad : ℤ) := by
      simp [shortestVector, weight, Finset.mul_sum]
    rw [h, octad_weight]; norm_num

private theorem shortest_squareSum : squareSum shortestVector = 32 := by
  have h : squareSum shortestVector = 4 * (weight octad : ℤ) := by
    unfold squareSum shortestVector weight
    simp only [Nat.cast_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> norm_num
  rw [h, octad_weight]; norm_num

def scaledSquare (x : IntVector) : ℚ := (squareSum x : ℚ) / 8

/-- Exact shortest squared norm four for the actual integral-coordinate construction. -/
theorem minimum_norm :
    (∀ x : IntVector, Admissible code x → x ≠ 0 → 4 ≤ scaledSquare x) ∧
    (Admissible code shortestVector ∧ shortestVector ≠ 0 ∧ scaledSquare shortestVector = 4) := by
  constructor
  · intro x hx hn
    have h := construction_lower_bound code doubly_even minimum_weight hx hn
    unfold scaledSquare
    exact (le_div_iff₀ (by norm_num : (0:ℚ) < 8)).2 (by exact_mod_cast h)
  · refine ⟨shortest_mem, ?_, ?_⟩
    · intro h
      have := shortest_squareSum
      rw [h] at this
      norm_num [squareSum] at this
    · norm_num [scaledSquare, shortest_squareSum]

#print axioms minimum_norm
#print axioms pairing_integral
end D5.S3.Arith.Lattices.Golay.IntegerLeech
