/- GID: D5/S3/Arith/FibonacciAtomic/DyadicSupportLines
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/DyadicSupportLines
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Dyadic-cost support lines for three- and five-outcome real probability laws. -/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.DyadicSupportLines

open scoped BigOperators

/-- Unassigned dyadic mass, in units of depth-d cylinders. -/
noncomputable def residual {ι : Type*} [Fintype ι] (p : ι → ℝ) (d : ℕ) : ℝ :=
  (2 : ℝ) ^ d - ∑ i, (⌊(2 : ℝ) ^ d * p i⌋ : ℤ)

/-- The classical DDG tail cost on probability vectors. The real `tsum` is zero
when the series is not summable; other vectors have no sampling-cost interpretation. -/
noncomputable def cost {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑' d : ℕ, residual p d / (2 : ℝ) ^ d

/-- Both supporting lines hold on the full real simplex, and the defining
nonnegative tail series converges, including zero and dyadic atoms. -/
theorem result (p : Fin 5 → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    let t := Finset.univ.inf' (by simp) p
    Summable (fun d : ℕ => residual p d / (2 : ℝ) ^ d) ∧
      0 ≤ t ∧ t ≤ 1 / 5 ∧ 16 * t ≤ cost p ∧ 48 * t - 6 ≤ cost p := by
  classical
  have data (P : Fin 5 → ℝ) (hP : ∀ i, 0 ≤ P i) (hS : ∑ i, P i = 1) :
      (∀ d, 0 ≤ residual P d ∧ residual P d ≤ 4) ∧
        Summable (fun d : ℕ => residual P d / (2 : ℝ) ^ d) ∧ 0 ≤ cost P := by
    have bounds (d : ℕ) : 0 ≤ residual P d ∧ residual P d ≤ 4 := by
      have hsum : ∑ i, (2 : ℝ) ^ d * P i = (2 : ℝ) ^ d := by
        rw [← Finset.mul_sum, hS, mul_one]
      have hlo : (∑ i, (⌊(2 : ℝ) ^ d * P i⌋ : ℝ)) ≤ (2 : ℝ) ^ d := by
        calc
          _ ≤ ∑ i, (2 : ℝ) ^ d * P i := Finset.sum_le_sum fun i _ => Int.floor_le _
          _ = _ := hsum
      have hhi : (2 : ℝ) ^ d < (∑ i, (⌊(2 : ℝ) ^ d * P i⌋ : ℝ)) + 5 := by
        have H := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
          (by simp : (Finset.univ : Finset (Fin 5)).Nonempty)
          (fun i _ => Int.lt_floor_add_one ((2 : ℝ) ^ d * P i))
        simpa [hsum, Finset.sum_add_distrib] using H
      have hi : (2 : ℤ) ^ d - ∑ i, ⌊(2 : ℝ) ^ d * P i⌋ < 5 := by
        have H : ((2 : ℤ) ^ d - ∑ i, ⌊(2 : ℝ) ^ d * P i⌋ : ℝ) < 5 := by
          push_cast
          linarith only [hhi]
        exact_mod_cast H
      constructor
      · simp only [residual, Int.cast_sum]
        linarith only [hlo]
      · have H : (2 : ℤ) ^ d - ∑ i, ⌊(2 : ℝ) ^ d * P i⌋ ≤ 4 := by omega
        have H' : ((2 : ℤ) ^ d - ∑ i, ⌊(2 : ℝ) ^ d * P i⌋ : ℝ) ≤ 4 := by exact_mod_cast H
        simpa [residual] using H'
    have nonneg (d : ℕ) : 0 ≤ residual P d / (2 : ℝ) ^ d :=
      div_nonneg (bounds d).1 (by positivity)
    have summable : Summable (fun d : ℕ => residual P d / (2 : ℝ) ^ d) := by
      apply Summable.of_nonneg_of_le nonneg
        (fun d => div_le_div_of_nonneg_right (bounds d).2 (by positivity))
      simpa [div_pow, div_eq_mul_inv] using
        (summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_left 4
    exact ⟨bounds, summable, tsum_nonneg nonneg⟩
  have minimum_data (P : Fin 5 → ℝ) (hP : ∀ i, 0 ≤ P i) (hS : ∑ i, P i = 1) :
      0 ≤ Finset.univ.inf' (by simp) P ∧
        Finset.univ.inf' (by simp) P ≤ 1 / 5 := by
    have lower (i : Fin 5) : Finset.univ.inf' (by simp) P ≤ P i :=
      Finset.inf'_le _ (Finset.mem_univ i)
    have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ => lower i)
    norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at H
    rw [hS] at H
    exact ⟨Finset.le_inf' (by simp) P (fun i _ => hP i), by linarith only [H]⟩
  have bucket_data (P : Fin 5 → ℝ) (hS : ∑ i, P i = 1)
      (M : ℕ) (k : ℤ) (hmin : ∀ i, (k : ℝ) < (M : ℝ) * P i) :
      let b := fun i => ⌊(M : ℝ) * P i⌋
      (∀ i, k ≤ b i) ∧ (∑ i, b i) ≤ M ∧
        ((∑ i, b i) = M → ∀ i, k + 1 ≤ b i) := by
    dsimp only
    have hf (i : Fin 5) : (⌊(M : ℝ) * P i⌋ : ℝ) ≤ (M : ℝ) * P i :=
      Int.floor_le _
    have hsum : ∑ i, (M : ℝ) * P i = M := by
      rw [← Finset.mul_sum, hS, mul_one]
    have hle : (∑ i, (⌊(M : ℝ) * P i⌋ : ℤ) : ℝ) ≤ M := by
      simpa [hsum] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hf i)
    refine ⟨fun i => Int.le_floor.mpr (hmin i).le, by exact_mod_cast hle, ?_⟩
    intro heq i
    have equal : ∑ j, (⌊(M : ℝ) * P j⌋ : ℝ) = ∑ j, (M : ℝ) * P j := by
      rw [hsum, ← Int.cast_sum, heq]
      norm_cast
    have hi := (Finset.sum_eq_sum_iff_of_le (fun j _ => hf j)).mp equal i
      (Finset.mem_univ i)
    have hlt : k < ⌊(M : ℝ) * P i⌋ := by
      have H : (k : ℝ) < (⌊(M : ℝ) * P i⌋ : ℝ) := by rw [hi]; exact hmin i
      exact_mod_cast H
    omega
  have trunc (P : Fin 5 → ℝ) (hP : ∀ i, 0 ≤ P i) (hS : ∑ i, P i = 1) (n : ℕ) :
      ∑ d ∈ Finset.range n, residual P d / (2 : ℝ) ^ d ≤ cost P := by
    exact (data P hP hS).2.1.sum_le_tsum _
      (fun d _ => div_nonneg ((data P hP hS).1 d).1 (by positivity))
  have bucket_upper (b : Fin 5 → ℤ) (k M : ℤ) (hb : ∀ i, k ≤ b i)
      (hS : ∑ i, b i ≤ M) (i : Fin 5) : b i ≤ M - 4 * k := by
    have H := Finset.single_le_sum (f := fun j => b j - k)
      (fun j _ => sub_nonneg.mpr (hb j)) (Finset.mem_univ i)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at H
    norm_num at H
    linarith only [H, hS]
  have atom_upper (P : Fin 5 → ℝ) (hS : ∑ i, P i = 1) (t : ℝ)
      (ht : ∀ i, t ≤ P i) (i : Fin 5) : P i ≤ 1 - 4 * t := by
    have H := Finset.single_le_sum (f := fun j => P j - t)
      (fun j _ => sub_nonneg.mpr (ht j)) (Finset.mem_univ i)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hS] at H
    norm_num at H
    linarith only [H]
  have low (P : Fin 5 → ℝ) (hP : ∀ i, 0 ≤ P i) (hS : ∑ i, P i = 1)
      (t : ℝ) (ht0 : 0 ≤ t) (ht : ∀ i, t ≤ P i) (htlow : t ≤ 3 / 16) :
      16 * t ≤ cost P := by
    by_cases htpos : t = 0
    · simpa [htpos] using (data P hP hS).2.2
    have hpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htpos)
    have hf0 (i : Fin 5) : ⌊P i⌋ = 0 := by
      apply Int.floor_eq_iff.mpr
      constructor
      · simpa using hP i
      · have H := atom_upper P hS t ht i
        norm_num
        linarith only [H, hpos]
    by_cases htone : t ≤ 1 / 16
    · have H := trunc P hP hS 1
      norm_num [Finset.sum_range_succ, residual, hf0] at H
      linarith only [H, htone]
    have htone' : 1 / 16 < t := lt_of_not_ge htone
    by_cases httwo : t ≤ 1 / 8
    · let b : Fin 5 → ℤ := fun i => ⌊16 * P i⌋
      obtain ⟨hb, hbs, hbeq⟩ := bucket_data P hS 16 1 (fun i => by
        have H := ht i
        norm_num
        linarith only [H, htone'])
      change (∀ i, 1 ≤ b i) at hb
      change ∑ i, b i ≤ 16 at hbs
      change (∑ i, b i) = 16 → ∀ i, 2 ≤ b i at hbeq
      have hbig : ∑ i, b i / 8 ≤ 1 := by
        have h0 := hb 0; have h1 := hb 1; have h2 := hb 2
        have h3 := hb 3; have h4 := hb 4
        simp [Fin.sum_univ_succ] at hbs ⊢
        omega
      have hw : ∑ i, (4 * (b i / 8) + 2 * (b i / 4) + b i / 2) ≤ 16 := by
        by_cases heq : ∑ i, b i = 16
        · have hb' := hbeq heq
          have scalar (i : Fin 5) :
              2 * (4 * (b i / 8) + 2 * (b i / 4) + b i / 2) ≤
                3 * b i - 4 + 4 * (b i / 8) := by
            have H := bucket_upper b 2 16 hb' hbs i
            have H' := hb' i
            generalize hx : b i = x at H H' ⊢
            interval_cases x <;> norm_num
          have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ => scalar i)
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul] at H ⊢
          norm_num at H
          linarith only [H, heq, hbig]
        · have hbs' : ∑ i, b i ≤ 15 := by omega
          have scalar (i : Fin 5) :
              3 * (4 * (b i / 8) + 2 * (b i / 4) + b i / 2) ≤
                4 * b i - 4 + 8 * (b i / 8) := by
            have H := bucket_upper b 1 16 hb hbs i
            have H' := hb i
            generalize hx : b i = x at H H' ⊢
            interval_cases x <;> norm_num
          have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ => scalar i)
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul] at H ⊢
          norm_num at H
          linarith only [H, hbs', hbig]
      have f2 (i : Fin 5) : ⌊2 * P i⌋ = b i / 8 := by
        dsimp only [b]
        convert Int.floor_div_natCast ((16 : ℝ) * P i) 8 using 1 <;>
          norm_num <;> congr 1 <;> ring
      have f4 (i : Fin 5) : ⌊4 * P i⌋ = b i / 4 := by
        dsimp only [b]
        convert Int.floor_div_natCast ((16 : ℝ) * P i) 4 using 1 <;>
          norm_num <;> congr 1 <;> ring
      have f8 (i : Fin 5) : ⌊8 * P i⌋ = b i / 2 := by
        dsimp only [b]
        convert Int.floor_div_natCast ((16 : ℝ) * P i) 2 using 1 <;>
          norm_num <;> congr 1 <;> ring
      have H := trunc P hP hS 4
      have W : ((∑ i, (4 * (b i / 8) + 2 * (b i / 4) + b i / 2) : ℤ) : ℝ) ≤ 16 := by
        exact_mod_cast hw
      norm_num [residual, Finset.sum_range_succ, hf0, f2, f4, f8,
        Fin.sum_univ_succ] at H W
      linarith only [H, W, httwo]
    have httwo' : 1 / 8 < t := lt_of_not_ge httwo
    by_cases htthree : t ≤ 5 / 32
    · let b : Fin 5 → ℤ := fun i => ⌊8 * P i⌋
      obtain ⟨hb, hbs, hbeq⟩ := bucket_data P hS 8 1 (fun i => by
        have H := ht i
        norm_num
        linarith only [H, httwo'])
      change (∀ i, 1 ≤ b i) at hb
      change ∑ i, b i ≤ 8 at hbs
      change (∑ i, b i) = 8 → ∀ i, 2 ≤ b i at hbeq
      have hbs' : ∑ i, b i ≤ 7 := by
        by_contra H
        have heq : ∑ i, b i = 8 := by omega
        have HH := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbeq heq i)
        norm_num at HH
        omega
      have hw : ∑ i, b i / 2 ≤ 2 := by
        have h0 := hb 0; have h1 := hb 1; have h2 := hb 2
        have h3 := hb 3; have h4 := hb 4
        simp [Fin.sum_univ_succ] at hbs' ⊢
        omega
      have f2 (i : Fin 5) : ⌊2 * P i⌋ = 0 := by
        have H := bucket_upper b 1 7 hb hbs' i
        have H' := hb i
        have eqn : ⌊2 * P i⌋ = b i / 4 := by
          dsimp only [b]
          convert Int.floor_div_natCast ((8 : ℝ) * P i) 4 using 1 <;>
            norm_num <;> congr 1 <;> ring
        rw [eqn]
        omega
      have f4 (i : Fin 5) : ⌊4 * P i⌋ = b i / 2 := by
        dsimp only [b]
        convert Int.floor_div_natCast ((8 : ℝ) * P i) 2 using 1 <;>
          norm_num <;> congr 1 <;> ring
      have H := trunc P hP hS 3
      have W : ((∑ i, b i / 2 : ℤ) : ℝ) ≤ 2 := by exact_mod_cast hw
      norm_num [residual, Finset.sum_range_succ, hf0, f2, f4,
        Fin.sum_univ_succ] at H W
      linarith only [H, W, htthree]
    have htthree' : 5 / 32 < t := lt_of_not_ge htthree
    by_cases htfour : t ≤ 1 / 6
    · let b : Fin 5 → ℤ := fun i => ⌊32 * P i⌋
      obtain ⟨hb, hbs, hbeq⟩ := bucket_data P hS 32 5 (fun i => by
        have H := ht i
        norm_num
        linarith only [H, htthree'])
      change (∀ i, 5 ≤ b i) at hb
      change ∑ i, b i ≤ 32 at hbs
      change (∑ i, b i) = 32 → ∀ i, 6 ≤ b i at hbeq
      have hbig : ∑ i, b i / 8 ≤ 2 := by
        have h0 := hb 0; have h1 := hb 1; have h2 := hb 2
        have h3 := hb 3; have h4 := hb 4
        simp [Fin.sum_univ_succ] at hbs ⊢
        omega
      have scalar (i : Fin 5) :
          3 * (8 * (b i / 16) + 4 * (b i / 8) + 2 * (b i / 4) + b i / 2) ≤
            4 * b i - 8 + 12 * (b i / 8) := by
        have H := bucket_upper b 5 32 hb hbs i
        have H' := hb i
        generalize hx : b i = x at H H' ⊢
        interval_cases x <;> norm_num
      have hw : ∑ i, (8 * (b i / 16) + 4 * (b i / 8) +
          2 * (b i / 4) + b i / 2) ≤ 36 := by
        have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ => scalar i)
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul] at H ⊢
        norm_num at H
        by_cases heq : ∑ i, b i = 32
        · have hb' := hbeq heq
          have hbig' : ∑ i, b i / 8 ≤ 1 := by
            have h0 := hb' 0; have h1 := hb' 1; have h2 := hb' 2
            have h3 := hb' 3; have h4 := hb' 4
            simp [Fin.sum_univ_succ] at hbs ⊢
            omega
          linarith only [H, heq, hbig']
        · have hbs' : ∑ i, b i ≤ 31 := by omega
          linarith only [H, hbs', hbig]
      have f2 (i : Fin 5) : ⌊2 * P i⌋ = b i / 16 := by
        dsimp only [b]
        convert Int.floor_div_natCast ((32 : ℝ) * P i) 16 using 1 <;>
          norm_num <;> congr 1 <;> ring
      have f4 (i : Fin 5) : ⌊4 * P i⌋ = b i / 8 := by
        dsimp only [b]
        convert Int.floor_div_natCast ((32 : ℝ) * P i) 8 using 1 <;>
          norm_num <;> congr 1 <;> ring
      have f8 (i : Fin 5) : ⌊8 * P i⌋ = b i / 4 := by
        dsimp only [b]
        convert Int.floor_div_natCast ((32 : ℝ) * P i) 4 using 1 <;>
          norm_num <;> congr 1 <;> ring
      have f16 (i : Fin 5) : ⌊16 * P i⌋ = b i / 2 := by
        dsimp only [b]
        convert Int.floor_div_natCast ((32 : ℝ) * P i) 2 using 1 <;>
          norm_num <;> congr 1 <;> ring
      have H := trunc P hP hS 5
      have W : ((∑ i, (8 * (b i / 16) + 4 * (b i / 8) +
          2 * (b i / 4) + b i / 2) : ℤ) : ℝ) ≤ 36 := by exact_mod_cast hw
      norm_num [residual, Finset.sum_range_succ, hf0, f2, f4, f8, f16,
        Fin.sum_univ_succ] at H W
      linarith only [H, W, htfour]
    have htfour' : 1 / 6 < t := lt_of_not_ge htfour
    let b : Fin 5 → ℤ := fun i => ⌊48 * P i⌋
    obtain ⟨hb, hbs, hbeq⟩ := bucket_data P hS 48 8 (fun i => by
      have H := ht i
      norm_num
      linarith only [H, htfour'])
    change (∀ i, 8 ≤ b i) at hb
    change ∑ i, b i ≤ 48 at hbs
    change (∑ i, b i) = 48 → ∀ i, 9 ≤ b i at hbeq
    have hbig : ∑ i, b i / 12 ≤ 1 := by
      by_cases heq : ∑ i, b i = 48
      · have hb' := hbeq heq
        have h0 := hb' 0; have h1 := hb' 1; have h2 := hb' 2
        have h3 := hb' 3; have h4 := hb' 4
        simp [Fin.sum_univ_succ] at hbs ⊢
        omega
      · have h0 := hb 0; have h1 := hb 1; have h2 := hb 2
        have h3 := hb 3; have h4 := hb 4
        have hbs' : ∑ i, b i ≤ 47 := by omega
        simp [Fin.sum_univ_succ] at hbs' ⊢
        omega
    have scalar (i : Fin 5) :
        4 * (b i / 24) + 2 * (b i / 12) + b i / 6 = 1 + 3 * (b i / 12) := by
      have H' := hb i
      have H : b i ≤ 15 := by
        by_cases heq : ∑ i, b i = 48
        · have HH := bucket_upper b 9 48 (hbeq heq) hbs i
          omega
        · have hbs' : ∑ i, b i ≤ 47 := by omega
          have HH := bucket_upper b 8 47 hb hbs' i
          omega
      omega
    have hw : ∑ i, (4 * (b i / 24) + 2 * (b i / 12) + b i / 6) ≤ 8 := by
      simp_rw [scalar]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      norm_num
      linarith only [hbig]
    have f2 (i : Fin 5) : ⌊2 * P i⌋ = b i / 24 := by
      dsimp only [b]
      convert Int.floor_div_natCast ((48 : ℝ) * P i) 24 using 1 <;>
        norm_num <;> congr 1 <;> ring
    have f4 (i : Fin 5) : ⌊4 * P i⌋ = b i / 12 := by
      dsimp only [b]
      convert Int.floor_div_natCast ((48 : ℝ) * P i) 12 using 1 <;>
        norm_num <;> congr 1 <;> ring
    have f8 (i : Fin 5) : ⌊8 * P i⌋ = b i / 6 := by
      dsimp only [b]
      convert Int.floor_div_natCast ((48 : ℝ) * P i) 6 using 1 <;>
        norm_num <;> congr 1 <;> ring
    have H := trunc P hP hS 4
    have W : ((∑ i, (4 * (b i / 24) + 2 * (b i / 12) + b i / 6) : ℤ) : ℝ) ≤ 8 := by
      exact_mod_cast hw
    norm_num [residual, Finset.sum_range_succ, hf0, f2, f4, f8,
      Fin.sum_univ_succ] at H W
    linarith only [H, W, htlow]
  have high (P : Fin 5 → ℝ) (hP : ∀ i, 0 ≤ P i) (hS : ∑ i, P i = 1)
      (t : ℝ) (ht : ∀ i, t ≤ P i) (hthi : 3 / 16 < t) :
      let Q := fun i => 16 * P i - 3
      (∀ i, 0 ≤ Q i) ∧ (∑ i, Q i = 1) ∧ cost P = 27 / 8 + cost Q / 16 := by
    let Q : Fin 5 → ℝ := fun i => 16 * P i - 3
    change (∀ i, 0 ≤ Q i) ∧ (∑ i, Q i = 1) ∧ cost P = 27 / 8 + cost Q / 16
    have hQ (i : Fin 5) : 0 ≤ Q i := by
      dsimp only [Q]
      have H := ht i
      linarith only [H, hthi]
    have hSQ : ∑ i, Q i = 1 := by
      simp only [Q, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hS]
      norm_num
    have hinterval (i : Fin 5) : 3 / 16 < P i ∧ P i < 1 / 4 := by
      have H := atom_upper P hS t ht i
      have H' := ht i
      constructor <;> linarith only [H, H', hthi]
    have f0 (i : Fin 5) : ⌊P i⌋ = 0 := by
      apply Int.floor_eq_iff.mpr
      have H := hinterval i
      norm_num
      constructor <;> linarith only [H.1, H.2]
    have f2 (i : Fin 5) : ⌊2 * P i⌋ = 0 := by
      apply Int.floor_eq_iff.mpr
      have H := hinterval i
      norm_num
      constructor <;> linarith only [H.1, H.2]
    have f4 (i : Fin 5) : ⌊4 * P i⌋ = 0 := by
      apply Int.floor_eq_iff.mpr
      have H := hinterval i
      norm_num
      constructor <;> linarith only [H.1, H.2]
    have f8 (i : Fin 5) : ⌊8 * P i⌋ = 1 := by
      apply Int.floor_eq_iff.mpr
      have H := hinterval i
      norm_num
      constructor <;> linarith only [H.1, H.2]
    have floor_tail (i : Fin 5) (d : ℕ) :
        ⌊(2 : ℝ) ^ (d + 4) * P i⌋ = ⌊(2 : ℝ) ^ d * Q i⌋ + 3 * (2 : ℤ) ^ d := by
      have scale : (2 : ℝ) ^ (d + 4) * P i =
          (2 : ℝ) ^ d * Q i + ((3 * (2 : ℕ) ^ d : ℕ) : ℝ) := by
        simp only [Q, pow_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        ring
      rw [scale, Int.floor_add_natCast]
      norm_cast
    have tail (d : ℕ) :
        residual P (d + 4) / (2 : ℝ) ^ (d + 4) =
          (residual Q d / (2 : ℝ) ^ d) / 16 := by
      have hR : residual P (d + 4) = residual Q d := by
        unfold residual
        simp_rw [floor_tail]
        simp only [Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_add]
        push_cast
        ring
      rw [hR, pow_add]
      norm_num
      ring
    have head : ∑ d ∈ Finset.range 4, residual P d / (2 : ℝ) ^ d = 27 / 8 := by
      norm_num [residual, Finset.sum_range_succ, f0, f2, f4, f8]
    have tails : (∑' d, residual P (d + 4) / (2 : ℝ) ^ (d + 4)) = cost Q / 16 := by
      simp_rw [tail]
      exact tsum_div_const
    have split := Summable.sum_add_tsum_nat_add 4 (data P hP hS).2.1
    rw [head, tails] at split
    exact ⟨hQ, hSQ, split.symm⟩
  have approximate (n : ℕ) : ∀ (P : Fin 5 → ℝ), (∀ i, 0 ≤ P i) →
      (∑ i, P i = 1) → ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 5 →
      (∀ i, t ≤ P i) → 48 * t - 6 - 4 * (1 / 16 : ℝ) ^ n ≤ cost P := by
    induction n with
    | zero =>
      intro P hP hS t ht0 htmax ht
      have H := (data P hP hS).2.2
      norm_num
      linarith only [H, htmax]
    | succ n ih =>
      intro P hP hS t ht0 htmax ht
      by_cases hlow : t ≤ 3 / 16
      · have H := low P hP hS t ht0 ht hlow
        have H' : 0 ≤ 4 * (1 / 16 : ℝ) ^ (n + 1) := by positivity
        linarith only [H, H', hlow]
      · have hhigh : 3 / 16 < t := lt_of_not_ge hlow
        let Q : Fin 5 → ℝ := fun i => 16 * P i - 3
        obtain ⟨hQ, hSQ, heq⟩ := high P hP hS t ht hhigh
        change (∀ i, 0 ≤ Q i) at hQ
        change (∑ i, Q i) = 1 at hSQ
        change cost P = 27 / 8 + cost Q / 16 at heq
        have H := ih Q hQ hSQ (16 * t - 3) (by linarith) (by linarith)
          (fun i => by dsimp only [Q]; have HH := ht i; linarith)
        rw [pow_succ]
        linarith only [H, heq]
  have second (P : Fin 5 → ℝ) (hP : ∀ i, 0 ≤ P i) (hS : ∑ i, P i = 1)
      (t : ℝ) (ht0 : 0 ≤ t) (htmax : t ≤ 1 / 5) (ht : ∀ i, t ≤ P i) :
      48 * t - 6 ≤ cost P := by
    have limit := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num : (1 / 16 : ℝ) < 1)
    have limit' : Filter.Tendsto (fun n : ℕ => 48 * t - 6 - 4 * (1 / 16 : ℝ) ^ n)
        Filter.atTop (nhds (48 * t - 6)) := by
      simpa only [mul_zero, sub_zero] using
        tendsto_const_nhds.sub (limit.const_mul 4)
    exact le_of_tendsto limit'
      (Filter.Eventually.of_forall (fun n => approximate n P hP hS t ht0 htmax ht))
  have datum := data p hp hs
  have min_datum := minimum_data p hp hs
  have lower (i : Fin 5) : Finset.univ.inf' (by simp) p ≤ p i :=
    Finset.inf'_le _ (Finset.mem_univ i)
  have line2 := second p hp hs (Finset.univ.inf' (by simp) p)
    min_datum.1 min_datum.2 lower
  refine ⟨datum.2.1, min_datum.1, min_datum.2, ?_, line2⟩
  by_cases hlow : Finset.univ.inf' (by simp) p ≤ 3 / 16
  · exact low p hp hs _ min_datum.1 lower hlow
  · linarith only [line2, hlow]

/-- The three-outcome real simplex satisfies both affine dyadic support lines. -/
theorem three_outcome (p : Fin 3 → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    let t := Finset.univ.inf' (by simp) p
    Summable (fun d : ℕ => residual p d / (2 : ℝ) ^ d) ∧
      0 ≤ t ∧ t ≤ 1 / 3 ∧ 6 * t ≤ cost p ∧ 14 * t - 2 ≤ cost p := by
  classical
  have data (P : Fin 3 → ℝ) (hS : ∑ i, P i = 1) :
      (∀ d, 0 ≤ residual P d ∧ residual P d ≤ 2) ∧
        Summable (fun d : ℕ => residual P d / (2 : ℝ) ^ d) ∧ 0 ≤ cost P := by
    have bounds (d : ℕ) : 0 ≤ residual P d ∧ residual P d ≤ 2 := by
      have hsum : ∑ i, (2 : ℝ) ^ d * P i = (2 : ℝ) ^ d := by
        rw [← Finset.mul_sum, hS, mul_one]
      have hlo : (∑ i, (⌊(2 : ℝ) ^ d * P i⌋ : ℝ)) ≤ (2 : ℝ) ^ d := by
        calc
          _ ≤ ∑ i, (2 : ℝ) ^ d * P i := Finset.sum_le_sum fun i _ => Int.floor_le _
          _ = _ := hsum
      have hhi : (2 : ℝ) ^ d < (∑ i, (⌊(2 : ℝ) ^ d * P i⌋ : ℝ)) + 3 := by
        have H := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
          (by simp : (Finset.univ : Finset (Fin 3)).Nonempty)
          (fun i _ => Int.lt_floor_add_one ((2 : ℝ) ^ d * P i))
        simpa [hsum, Finset.sum_add_distrib] using H
      have hi : (2 : ℤ) ^ d - ∑ i, ⌊(2 : ℝ) ^ d * P i⌋ < 3 := by
        have H : ((2 : ℤ) ^ d - ∑ i, ⌊(2 : ℝ) ^ d * P i⌋ : ℝ) < 3 := by
          push_cast
          linarith only [hhi]
        exact_mod_cast H
      constructor
      · simp only [residual, Int.cast_sum]
        linarith only [hlo]
      · have H : (2 : ℤ) ^ d - ∑ i, ⌊(2 : ℝ) ^ d * P i⌋ ≤ 2 := by omega
        have H' : ((2 : ℤ) ^ d - ∑ i, ⌊(2 : ℝ) ^ d * P i⌋ : ℝ) ≤ 2 := by exact_mod_cast H
        simpa [residual] using H'
    have nonneg (d : ℕ) : 0 ≤ residual P d / (2 : ℝ) ^ d :=
      div_nonneg (bounds d).1 (by positivity)
    have summable : Summable (fun d : ℕ => residual P d / (2 : ℝ) ^ d) := by
      apply Summable.of_nonneg_of_le nonneg
        (fun d => div_le_div_of_nonneg_right (bounds d).2 (by positivity))
      simpa [div_pow, div_eq_mul_inv] using
        (summable_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_left 2
    exact ⟨bounds, summable, tsum_nonneg nonneg⟩
  have lower (i : Fin 3) : Finset.univ.inf' (by simp) p ≤ p i :=
    Finset.inf'_le _ (Finset.mem_univ i)
  have minimum_data : 0 ≤ Finset.univ.inf' (by simp) p ∧
      Finset.univ.inf' (by simp) p ≤ 1 / 3 := by
    have H := Finset.sum_le_sum (s := Finset.univ) (fun i _ => lower i)
    norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at H
    rw [hs] at H
    exact ⟨Finset.le_inf' (by simp) p (fun i _ => hp i), by linarith only [H]⟩
  have atom_upper (P : Fin 3 → ℝ) (hS : ∑ i, P i = 1) (t : ℝ)
      (ht : ∀ i, t ≤ P i) (i : Fin 3) : P i ≤ 1 - 2 * t := by
    have H := Finset.single_le_sum (f := fun j => P j - t)
      (fun j _ => sub_nonneg.mpr (ht j)) (Finset.mem_univ i)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hS] at H
    norm_num at H
    linarith only [H]
  have trunc (P : Fin 3 → ℝ) (hS : ∑ i, P i = 1) :
      ∑ d ∈ Finset.range 2, residual P d / (2 : ℝ) ^ d ≤ cost P :=
    (data P hS).2.1.sum_le_tsum _
      (fun d _ => div_nonneg ((data P hS).1 d).1 (by positivity))
  have low (P : Fin 3 → ℝ) (hS : ∑ i, P i = 1)
      (t : ℝ) (ht0 : 0 ≤ t) (ht : ∀ i, t ≤ P i) (htlow : t ≤ 1 / 4) :
      6 * t ≤ cost P ∧ 14 * t - 2 ≤ cost P := by
    by_cases htzero : t = 0
    · have H := (data P hS).2.2
      constructor <;> simp only [htzero, mul_zero] <;> linarith only [H]
    have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
    have f0 (i : Fin 3) : ⌊P i⌋ = 0 := by
      apply Int.floor_eq_iff.mpr
      have H := atom_upper P hS t ht i
      have H' := ht i
      norm_num
      constructor <;> linarith only [H, H', htpos]
    have first_bucket : (∑ i, ⌊2 * P i⌋ : ℤ) ≤ 1 := by
      have hf (i : Fin 3) : (⌊2 * P i⌋ : ℝ) ≤ 2 * P i := Int.floor_le _
      have hsum : ∑ i, 2 * P i = 2 := by rw [← Finset.mul_sum, hS]; norm_num
      have H : ((∑ i, ⌊2 * P i⌋ : ℤ) : ℝ) ≤ 2 := by
        simpa [hsum, Int.cast_sum] using
          Finset.sum_le_sum (s := Finset.univ) (fun i _ => hf i)
      have Hint : (∑ i, ⌊2 * P i⌋ : ℤ) ≤ 2 := by exact_mod_cast H
      by_contra hnot
      have heq : (∑ i, ⌊2 * P i⌋ : ℤ) = 2 := by omega
      have equal : ∑ i, (⌊2 * P i⌋ : ℝ) = ∑ i, 2 * P i := by
        rw [hsum, ← Int.cast_sum, heq]; norm_num
      have hi (i : Fin 3) : 1 ≤ ⌊2 * P i⌋ := by
        have he := (Finset.sum_eq_sum_iff_of_le (fun j _ => hf j)).mp equal i
          (Finset.mem_univ i)
        have hp' := ht i
        have hh : (0 : ℝ) < (⌊2 * P i⌋ : ℝ) := by rw [he]; linarith only [htpos, hp']
        have hh' : 0 < ⌊2 * P i⌋ := by exact_mod_cast hh
        omega
      have H' := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
      norm_num [heq] at H'
    have H := trunc P hS
    have W : ((∑ i, ⌊2 * P i⌋ : ℤ) : ℝ) ≤ 1 := by exact_mod_cast first_bucket
    norm_num [Finset.sum_range_succ, residual, f0, Fin.sum_univ_succ] at H W
    constructor <;> linarith only [H, W, htlow]
  have high (P : Fin 3 → ℝ) (hS : ∑ i, P i = 1)
      (t : ℝ) (ht : ∀ i, t ≤ P i) (hthi : 1 / 4 < t) :
      let Q := fun i => 4 * P i - 1
      (∀ i, 0 ≤ Q i) ∧ (∑ i, Q i = 1) ∧ cost P = 2 + cost Q / 4 := by
    let Q : Fin 3 → ℝ := fun i => 4 * P i - 1
    change (∀ i, 0 ≤ Q i) ∧ (∑ i, Q i = 1) ∧ cost P = 2 + cost Q / 4
    have hQ (i : Fin 3) : 0 ≤ Q i := by
      dsimp only [Q]
      have H := ht i
      linarith only [H, hthi]
    have hSQ : ∑ i, Q i = 1 := by
      simp only [Q, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hS]
      norm_num
    have hinterval (i : Fin 3) : 1 / 4 < P i ∧ P i < 1 / 2 := by
      have H := atom_upper P hS t ht i
      have H' := ht i
      constructor <;> linarith only [H, H', hthi]
    have f0 (i : Fin 3) : ⌊P i⌋ = 0 := by
      apply Int.floor_eq_iff.mpr
      have H := hinterval i
      norm_num
      constructor <;> linarith only [H.1, H.2]
    have f2 (i : Fin 3) : ⌊2 * P i⌋ = 0 := by
      apply Int.floor_eq_iff.mpr
      have H := hinterval i
      norm_num
      constructor <;> linarith only [H.1, H.2]
    have floor_tail (i : Fin 3) (d : ℕ) :
        ⌊(2 : ℝ) ^ (d + 2) * P i⌋ = ⌊(2 : ℝ) ^ d * Q i⌋ + (2 : ℤ) ^ d := by
      have scale : (2 : ℝ) ^ (d + 2) * P i =
          (2 : ℝ) ^ d * Q i + (((2 : ℕ) ^ d : ℕ) : ℝ) := by
        simp only [Q, pow_add, Nat.cast_pow, Nat.cast_ofNat]
        ring
      rw [scale, Int.floor_add_natCast]
      norm_cast
    have tail (d : ℕ) :
        residual P (d + 2) / (2 : ℝ) ^ (d + 2) =
          (residual Q d / (2 : ℝ) ^ d) / 4 := by
      have hR : residual P (d + 2) = residual Q d := by
        unfold residual
        simp_rw [floor_tail]
        simp only [Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_add]
        push_cast
        ring
      rw [hR, pow_add]
      norm_num
      ring
    have head : ∑ d ∈ Finset.range 2, residual P d / (2 : ℝ) ^ d = 2 := by
      norm_num [residual, Finset.sum_range_succ, f0, f2]
    have tails : (∑' d, residual P (d + 2) / (2 : ℝ) ^ (d + 2)) = cost Q / 4 := by
      simp_rw [tail]
      exact tsum_div_const
    have split := Summable.sum_add_tsum_nat_add 2 (data P hS).2.1
    rw [head, tails] at split
    exact ⟨hQ, hSQ, split.symm⟩
  have approximate (n : ℕ) : ∀ (P : Fin 3 → ℝ), (∑ i, P i = 1) →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 3 → (∀ i, t ≤ P i) →
        14 * t - 2 - 3 * (1 / 4 : ℝ) ^ n ≤ cost P := by
    induction n with
    | zero =>
      intro P hS t ht0 htmax ht
      have H := (data P hS).2.2
      norm_num
      linarith only [H, htmax]
    | succ n ih =>
      intro P hS t ht0 htmax ht
      by_cases hlow : t ≤ 1 / 4
      · have H := (low P hS t ht0 ht hlow).2
        have H' : 0 ≤ 3 * (1 / 4 : ℝ) ^ (n + 1) := by positivity
        linarith only [H, H']
      · have hhigh : 1 / 4 < t := lt_of_not_ge hlow
        let Q : Fin 3 → ℝ := fun i => 4 * P i - 1
        obtain ⟨hQ, hSQ, heq⟩ := high P hS t ht hhigh
        change (∑ i, Q i) = 1 at hSQ
        change cost P = 2 + cost Q / 4 at heq
        have H := ih Q hSQ (4 * t - 1) (by linarith) (by linarith)
          (fun i => by dsimp only [Q]; have HH := ht i; linarith)
        rw [pow_succ]
        linarith only [H, heq]
  have second : 14 * Finset.univ.inf' (by simp) p - 2 ≤ cost p := by
    have limit := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    have limit' : Filter.Tendsto
        (fun n : ℕ => 14 * Finset.univ.inf' (by simp) p - 2 - 3 * (1 / 4 : ℝ) ^ n)
        Filter.atTop (nhds (14 * Finset.univ.inf' (by simp) p - 2)) := by
      simpa only [mul_zero, sub_zero] using
        tendsto_const_nhds.sub (limit.const_mul 3)
    exact le_of_tendsto limit' (Filter.Eventually.of_forall
      (fun n => approximate n p hs _ minimum_data.1 minimum_data.2 lower))
  refine ⟨(data p hs).2.1, minimum_data.1, minimum_data.2, ?_, second⟩
  by_cases hlow : Finset.univ.inf' (by simp) p ≤ 1 / 4
  · exact (low p hs _ minimum_data.1 lower hlow).1
  · obtain ⟨_, hSQ, H⟩ := high p hs _ lower (lt_of_not_ge hlow)
    have H' := (data (fun i => 4 * p i - 1) hSQ).2.2
    linarith only [H, H', minimum_data.2]

end D5.S3.Arith.FibonacciAtomic.DyadicSupportLines
