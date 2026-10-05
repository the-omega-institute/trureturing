/- GID: D5/S3/Arith/GrahamObryantInverseSineRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/GrahamObryantInverseSineRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/GrahamObryantInverseSineRefutation.claim; result=D5/S3/Arith/GrahamObryantInverseSineRefutation.result; claim=D5/S3/Arith/GrahamObryantInverseSineRefutation.claim
   digest: Refutes Graham–O'Bryant Conjecture 5.2 through an internal all-n signed-dyadic family. -/

/- Source: Graham and O'Bryant, A Discrete Fourier Kernel and Fraenkel's Tiling
   Conjecture, Acta Arithmetica 118 (2005), 283–304, Conjecture 5.2, p. 302.
   Library: D5/L/Fourier/grahamobryant2005fourier.
   Preregistration: https://github.com/the-omega-institute/trureturing/issues/13152.
   proof_shape: bind-only; escape_witness: none;
   admission_basis: open-problem-resolution.
   The public refutation specializes the independently constructed universal family
   to n=3. Known trigonometric and modular identities are proof-local steps. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

open scoped BigOperators
namespace D5.S3.Arith.GrahamObryantInverseSineRefutation

/-- Complete inverse-sine row, including the diagonal, using reduced product residues. -/
noncomputable def row {n : ℕ} (q : ℕ) (p : Fin n → ℕ) (k : Fin n) : ℝ :=
  ∑ i : Fin n, 1 / |Real.sin (Real.pi *
    (((p k : ZMod q) * (p i : ZMod q)⁻¹).val : ℝ) / (q : ℝ))|

/-- Graham–O'Bryant Conjecture 5.2 with ordinary, unsigned residue-set equality. -/
noncomputable def claim : Prop :=
  ∀ (n q : ℕ) (p : Fin n → ℕ), 0 < n → 0 < q →
    (∀ i, 0 < p i) → Function.Injective p →
    (∀ i, (p i).Coprime q) →
    (7 / 4 : ℝ) ^ n < (q : ℝ) → (∑ i, p i) ≤ q →
    (∀ k, 2 / Real.sin (Real.pi / (q : ℝ)) ≤ row q p k) →
    q = 2 ^ n - 1 ∧
      Finset.univ.image (fun i => (p i : ZMod q)) =
      Finset.univ.image (fun i : Fin n => ((2 : ZMod q) ^ i.val))

/-- The literal conjecture fails; the proof first constructs the complete family for every n ≥ 3. -/
theorem result : ¬ claim := by
  classical
  have family : ∀ (n : ℕ), 3 ≤ n →
      let q := 2 ^ n - 1
      let p : Fin n → ℕ := fun i => if i.val = n - 1 then 2 ^ i.val - 1 else 2 ^ i.val
      0 < q ∧ (∀ i, 0 < p i ∧ p i < q) ∧ Function.Injective p ∧
      (∀ i, (p i).Coprime q) ∧
      (Finset.univ.image p).card = n ∧
      (∑ i, p i) = q - 1 ∧
      (7 / 4 : ℝ) ^ n < (q : ℝ) ∧
      (∀ k, row q p k = 2 / Real.sin (Real.pi / (q : ℝ))) ∧
      (∀ k i, Real.sin (Real.pi *
        (((p k : ZMod q) * (p i : ZMod q)⁻¹).val : ℝ) / (q : ℝ)) ≠ 0) ∧
      Finset.univ.image (fun i => (p i : ZMod q)) ≠
        Finset.univ.image (fun i : Fin n => (2 : ZMod q) ^ i.val) := by
    intro n hn
    dsimp only
    let q := 2 ^ n - 1
    let p : Fin n → ℕ := fun i => if i.val = n - 1 then 2 ^ i.val - 1 else 2 ^ i.val
    change 0 < q ∧ (∀ i, 0 < p i ∧ p i < q) ∧ Function.Injective p ∧ _
    have hnpos : 0 < n := by omega
    have hpow : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
           _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    have hqpos : 0 < q := by dsimp [q]; omega
    have hqgt : 1 < q := by dsimp [q]; omega
    have hqcast : (q : ℝ) = (2 : ℝ) ^ n - 1 := by
      dsimp [q]
      rw [Nat.cast_sub (by omega : 1 ≤ 2 ^ n)]
      norm_cast
    have hthreshold : (7 / 4 : ℝ) ^ n < (q : ℝ) := by
      rw [hqcast]
      have ht : ∀ m : ℕ, 3 ≤ m → (7 / 4 : ℝ) ^ m < (2 : ℝ) ^ m - 1 := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base => norm_num
        | succ k hk ih =>
          rw [pow_succ, pow_succ]
          have hz := pow_pos (by norm_num : (0 : ℝ) < 7 / 4) k
          nlinarith
      exact ht n hn
    let x : ℝ := Real.pi / (q : ℝ)
    have hxpos : 0 < x := div_pos Real.pi_pos (by exact_mod_cast hqpos)
    have hxpi : x < Real.pi := by
      dsimp [x]
      exact (div_lt_self Real.pi_pos (by exact_mod_cast hqgt))
    have hxn : (2 : ℝ) ^ n * x = Real.pi + x := by
      dsimp [x]
      have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
      field_simp
      nlinarith [hqcast]
    have hangle : ∀ j : ℕ, j < n → 0 < (2 : ℝ) ^ j * x ∧ (2 : ℝ) ^ j * x < Real.pi := by
      intro j hj
      constructor
      · positivity
      · have hjle : j ≤ n - 1 := by omega
        have hp : 2 ^ j ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) hjle
        have hn1 : n - 1 + 1 = n := by omega
        have hp2 : 2 * 2 ^ (n - 1) = 2 ^ n := by
          calc 2 * 2 ^ (n - 1) = 2 ^ (n - 1 + 1) := by rw [pow_succ]; omega
               _ = 2 ^ n := by rw [hn1]
        have hplt : 2 ^ j < q := by dsimp [q]; omega
        have hpr : (2 : ℝ) ^ j < (q : ℝ) := by exact_mod_cast hplt
        dsimp [x]
        rw [← mul_div_assoc]
        apply (div_lt_iff₀ (by exact_mod_cast hqpos : (0 : ℝ) < q)).2
        nlinarith [Real.pi_pos]
    have hsinpos : ∀ j : ℕ, j < n → 0 < Real.sin ((2 : ℝ) ^ j * x) := by
      intro j hj
      exact Real.sin_pos_of_pos_of_lt_pi (hangle j hj).1 (hangle j hj).2
    have hsinlast : Real.sin ((2 : ℝ) ^ n * x) = -Real.sin x := by
      rw [hxn, add_comm, Real.sin_add_pi]
    have hsinnonzero : ∀ j : ℕ, j ≤ n → Real.sin ((2 : ℝ) ^ j * x) ≠ 0 := by
      intro j hj
      rcases lt_or_eq_of_le hj with hj | rfl
      · exact (hsinpos j hj).ne'
      · rw [hsinlast]
        exact neg_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hxpos hxpi).ne'
    have double : ∀ j : ℕ, j < n →
        1 / Real.sin ((2 : ℝ) ^ (j + 1) * x) =
          Real.cot ((2 : ℝ) ^ j * x) - Real.cot ((2 : ℝ) ^ (j + 1) * x) := by
      intro j hj
      have ha := hsinnonzero j (by omega)
      have hb := hsinnonzero (j + 1) (by omega)
      have hd : (2 : ℝ) ^ (j + 1) * x = 2 * ((2 : ℝ) ^ j * x) := by rw [pow_succ]; ring
      rw [hd] at hb ⊢
      rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
        Real.sin_two_mul, Real.cos_two_mul']
      have hc : Real.cos ((2 : ℝ) ^ j * x) ≠ 0 := by
        intro hc
        simp [Real.sin_two_mul, hc] at hb
      field_simp
      nlinarith [Real.sin_sq_add_cos_sq ((2 : ℝ) ^ j * x)]
    have hcotlast : Real.cot ((2 : ℝ) ^ n * x) = Real.cot x := by
      rw [hxn, add_comm, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
        Real.cos_add_pi, Real.sin_add_pi]
      simp
    have htel : (∑ j ∈ Finset.range n, 1 / Real.sin ((2 : ℝ) ^ (j + 1) * x)) = 0 := by
      calc
        _ = ∑ j ∈ Finset.range n,
            (Real.cot ((2 : ℝ) ^ j * x) - Real.cot ((2 : ℝ) ^ (j + 1) * x)) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact double j (Finset.mem_range.mp hj)
        _ = Real.cot ((2 : ℝ) ^ 0 * x) - Real.cot ((2 : ℝ) ^ n * x) :=
          Finset.sum_range_sub' (fun j => Real.cot ((2 : ℝ) ^ j * x)) n
        _ = 0 := by simp [hcotlast]
    have hsaturation : (∑ j : Fin n, 1 / Real.sin ((2 : ℝ) ^ j.val * x)) = 2 / Real.sin x := by
      rw [show (∑ j : Fin n, 1 / Real.sin ((2 : ℝ) ^ j.val * x)) =
          ∑ j ∈ Finset.range n, 1 / Real.sin ((2 : ℝ) ^ j * x) from
        Fin.sum_univ_eq_sum_range (fun j => 1 / Real.sin ((2 : ℝ) ^ j * x)) n]
      have hshift := Finset.sum_range_succ' (fun j => 1 / Real.sin ((2 : ℝ) ^ j * x)) n
      have hstandard := Finset.sum_range_succ (fun j => 1 / Real.sin ((2 : ℝ) ^ j * x)) n
      rw [htel] at hshift
      simp only [pow_zero, one_mul, hsinlast, div_neg] at hshift hstandard
      rw [show 2 / Real.sin x = 2 * (1 / Real.sin x) by ring]
      linarith
    have hn1 : n - 1 + 1 = n := by omega
    have hn2 : n - 2 + 1 = n - 1 := by omega
    have ha4 : 4 ≤ 2 ^ (n - 1) := by
      calc 4 = 2 ^ 2 := by norm_num
           _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hb2 : 2 ≤ 2 ^ (n - 2) := by
      calc 2 = 2 ^ 1 := by norm_num
           _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by omega) (by omega)
    have hab : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
      rw [← hn2, pow_succ]; omega
    have hqa : 2 ^ n = 2 * 2 ^ (n - 1) := by
      calc 2 ^ n = 2 ^ (n - 1 + 1) := by rw [hn1]
           _ = 2 * 2 ^ (n - 1) := by rw [pow_succ]; omega
    have hp : ∀ i : Fin n, 0 < p i ∧ p i < q := by
      intro i
      have hpi : 1 ≤ 2 ^ i.val := Nat.one_le_pow i.val 2 (by omega)
      have hle : 2 ^ i.val ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      dsimp [p, q]
      split_ifs with hi
      · rw [hi]; omega
      · omega
    have hmono : StrictMono p := by
      intro i j hij
      have hijv : i.val < j.val := hij
      have hi : i.val ≠ n - 1 := by omega
      dsimp [p]
      rw [if_neg hi]
      split_ifs with hj
      · have hil : i.val ≤ n - 2 := by omega
        have hle := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hil
        rw [hj]
        omega
      · exact Nat.pow_lt_pow_right (by omega) hijv
    have hinj : Function.Injective p := hmono.injective
    have hcard : (Finset.univ.image p).card = n := by
      rw [Finset.card_image_of_injective _ hinj]
      simp
    let last : Fin n := ⟨n - 1, by omega⟩
    have hlast : p last = 2 ^ (n - 1) - 1 := by simp [p, last]
    have hsum_pow : ∀ m : ℕ, (∑ j ∈ Finset.range m, (2 : ℕ) ^ j) + 1 = 2 ^ m := by
      intro m
      simpa using geom_sum_mul_add (1 : ℕ) m
    have hsum : (∑ i : Fin n, p i) = q - 1 := by
      have hdelta : (∑ i : Fin n, if i.val = n - 1 then 1 else 0 : ℕ) = 1 := by
        have hh : ∀ i : Fin n, (i.val = n - 1) ↔ i = last := by
          intro i
          simpa only [last] using (Fin.ext_iff (a := i) (b := last)).symm
        simp_rw [hh]
        simp
      have hterm : (∑ i : Fin n, p i) +
          (∑ i : Fin n, if i.val = n - 1 then 1 else 0 : ℕ) =
          ∑ i : Fin n, 2 ^ i.val := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [p]
        split_ifs with he
        · have hp2 : 1 ≤ 2 ^ i.val := Nat.one_le_pow i.val 2 (by omega)
          omega
        · omega
      rw [hdelta, Fin.sum_univ_eq_sum_range (fun i => (2 : ℕ) ^ i) n] at hterm
      have hh := hsum_pow n
      dsimp [q]
      omega
    have hnotpower : ∀ i : Fin n, p last ≠ 2 ^ i.val := by
      intro i
      rw [hlast]
      by_cases hi : i.val = n - 1
      · rw [hi]; omega
      · have hile : i.val ≤ n - 2 := by omega
        have hle := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) hile
        omega
    let : NeZero q := ⟨hqpos.ne'⟩
    let : NeZero n := ⟨hnpos.ne'⟩
    have hnotcanonical : Finset.univ.image (fun i : Fin n => (p i : ZMod q)) ≠
        Finset.univ.image (fun i : Fin n => (2 : ZMod q) ^ i.val) := by
      intro he
      have hm : (p last : ZMod q) ∈ Finset.univ.image (fun i : Fin n => (p i : ZMod q)) :=
        Finset.mem_image.mpr ⟨last, Finset.mem_univ _, rfl⟩
      rw [he] at hm
      obtain ⟨i, hi, hpi⟩ := Finset.mem_image.mp hm
      have hplt : 2 ^ i.val < q := by
        have hle := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) (show i.val ≤ n - 1 by omega)
        dsimp [q]; omega
      have hcast : ((2 ^ i.val : ℕ) : ZMod q) = (2 : ZMod q) ^ i.val := by norm_cast
      rw [← hcast] at hpi
      have hv := congrArg ZMod.val hpi
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hplt,
        Nat.mod_eq_of_lt (hp last).2] at hv
      exact hnotpower i hv.symm
    have hu : (2 : ZMod q) ^ n = 1 := by
      have hN : 2 ^ n = q + 1 := by dsimp [q]; omega
      have hcast : ((2 ^ n : ℕ) : ZMod q) = (2 : ZMod q) ^ n := by norm_cast
      rw [← hcast, hN, Nat.cast_add, ZMod.natCast_self]
      norm_num
    have hrep : ∀ i : Fin n, (p i : ZMod q) =
        if i.val = n - 1 then -(2 : ZMod q) ^ i.val else (2 : ZMod q) ^ i.val := by
      intro i
      dsimp [p]
      split_ifs with hi
      · have hpi : 1 ≤ 2 ^ i.val := Nat.one_le_pow i.val 2 (by omega)
        rw [Nat.cast_sub hpi, Nat.cast_pow, Nat.cast_one]
        have he : (2 : ZMod q) * (2 : ZMod q) ^ i.val = 1 := by
          rw [hi, ← pow_succ', hn1]
          exact hu
        linear_combination he
      · norm_cast
    have hinv : ∀ i : Fin n, (p i : ZMod q)⁻¹ =
        if i.val = n - 1 then -(2 : ZMod q) ^ (n - i.val) else (2 : ZMod q) ^ (n - i.val) := by
      intro i
      apply ZMod.inv_eq_of_mul_eq_one
      rw [hrep]
      have hm : i.val + (n - i.val) = n := by omega
      split_ifs <;> simp only [neg_mul_neg, ← pow_add, hm, hu]
    have hunit : ∀ i : Fin n, IsUnit (p i : ZMod q) := by
      intro i
      refine isUnit_iff_exists_inv.mpr ⟨(p i : ZMod q)⁻¹, ?_⟩
      rw [hinv, hrep]
      have hm : i.val + (n - i.val) = n := by omega
      split_ifs <;> simp only [neg_mul_neg, ← pow_add, hm, hu]
    have hcoprime : ∀ i : Fin n, (p i).Coprime q := by
      intro i
      exact (ZMod.isUnit_iff_coprime _ _).mp (hunit i)
    let F : ZMod q → ℝ := fun z => |Real.sin (Real.pi * (z.val : ℝ) / (q : ℝ))|
    have hAbsCast : ∀ (Q : ℕ), 0 < Q → ∀ a : ℤ,
        |Real.sin (Real.pi * ((a : ZMod Q).val : ℝ) / (Q : ℝ))| =
        |Real.sin (Real.pi * (a : ℝ) / (Q : ℝ))| := by
      intro Q hQ a
      let : NeZero Q := ⟨hQ.ne'⟩
      have hQne : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
      have hc : (((a : ZMod Q).val : ℤ) : ZMod Q) = (a : ZMod Q) := by simp
      have hm := (ZMod.intCast_eq_intCast_iff _ _ Q).mp hc
      obtain ⟨d, hd⟩ := Int.modEq_iff_dvd.mp hm
      have hdr : (a : ℝ) - (((a : ZMod Q).val : ℤ) : ℝ) = (Q : ℝ) * (d : ℝ) := by
        exact_mod_cast hd
      have he : Real.pi * (a : ℝ) / (Q : ℝ) =
          Real.pi * ((a : ZMod Q).val : ℝ) / (Q : ℝ) + (d : ℝ) * Real.pi := by
        apply (div_eq_iff hQne).mpr
        rw [add_mul, div_mul_cancel₀ _ hQne]
        linear_combination Real.pi * hdr
      rw [he, Real.sin_add_int_mul_pi, abs_mul]
      simp
    have hFcast : ∀ a : ℤ, F (a : ZMod q) =
        |Real.sin (Real.pi * (a : ℝ) / (q : ℝ))| := hAbsCast q hqpos
    have hFneg : ∀ z : ZMod q, F (-z) = F z := by
      intro z
      have hc : (((z.val : ℤ) : ZMod q)) = z := by simp
      have hplus := hFcast (z.val : ℤ)
      have hminus := hFcast (-(z.val : ℤ))
      simp only [Int.cast_neg, hc, mul_neg, neg_div, Real.sin_neg, abs_neg] at hminus
      rw [hc] at hplus
      exact hminus.trans hplus.symm
    have hFpow : ∀ j : Fin n, F ((2 : ZMod q) ^ j.val) = Real.sin ((2 : ℝ) ^ j.val * x) := by
      intro j
      have hplt : 2 ^ j.val < q := by
        have hle := Nat.pow_le_pow_right (n := 2) (by omega : 0 < 2) (show j.val ≤ n - 1 by omega)
        dsimp [q]; omega
      dsimp [F, x]
      have hcast : ((2 ^ j.val : ℕ) : ZMod q) = (2 : ZMod q) ^ j.val := by norm_cast
      rw [← hcast, ZMod.val_natCast, Nat.mod_eq_of_lt hplt, Nat.cast_pow, Nat.cast_two]
      rw [show Real.pi * (2 : ℝ) ^ j.val / (q : ℝ) =
          (2 : ℝ) ^ j.val * (Real.pi / (q : ℝ)) by ring]
      exact abs_of_pos (hsinpos j.val j.isLt)
    have hexponent : ∀ k i : Fin n,
        (2 : ZMod q) ^ (k.val + (n - i.val)) = (2 : ZMod q) ^ (k - i).val := by
      intro k i
      rw [pow_eq_pow_mod _ hu]
      congr 1
      rw [Fin.val_sub]
      congr 1
      omega
    have hrowterm : ∀ k i : Fin n,
        F ((p k : ZMod q) * (p i : ZMod q)⁻¹) = Real.sin ((2 : ℝ) ^ (k - i).val * x) := by
      intro k i
      rw [hrep, hinv]
      split_ifs <;>
        simp only [neg_mul, mul_neg, ← pow_add, hexponent, hFneg, hFpow]
    have hrow : ∀ k : Fin n, row q p k = 2 / Real.sin x := by
      intro k
      change (∑ i : Fin n, 1 / F ((p k : ZMod q) * (p i : ZMod q)⁻¹)) = _
      simp_rw [hrowterm]
      rw [show (∑ i : Fin n, 1 / Real.sin ((2 : ℝ) ^ (k - i).val * x)) =
          ∑ j : Fin n, 1 / Real.sin ((2 : ℝ) ^ j.val * x) from
        (Equiv.subLeft k).sum_comp (fun j : Fin n => 1 / Real.sin ((2 : ℝ) ^ j.val * x))]
      exact hsaturation
    have hdenom : ∀ k i : Fin n, Real.sin (Real.pi *
        (((p k : ZMod q) * (p i : ZMod q)⁻¹).val : ℝ) / (q : ℝ)) ≠ 0 := by
      intro k i
      have ht := hrowterm k i
      have hs := hsinpos (k - i).val (k - i).isLt
      intro he
      dsimp [F] at ht
      rw [he, abs_zero] at ht
      linarith
    exact ⟨hqpos, hp, hinj, hcoprime, hcard, hsum, hthreshold, hrow, hdenom, hnotcanonical⟩
  intro hc
  have hf := family 3 (by omega)
  dsimp only at hf
  have hh := hc 3 7 (fun i : Fin 3 => if i.val = 2 then 2 ^ i.val - 1 else 2 ^ i.val)
    (by omega) (by omega) (fun i => (hf.2.1 i).1) hf.2.2.1 hf.2.2.2.1
    hf.2.2.2.2.2.2.1 (by have hh := hf.2.2.2.2.2.1; norm_num at hh ⊢; omega)
    (fun k => le_of_eq (hf.2.2.2.2.2.2.2.1 k).symm)
  exact hf.2.2.2.2.2.2.2.2.2 hh.2


end D5.S3.Arith.GrahamObryantInverseSineRefutation
