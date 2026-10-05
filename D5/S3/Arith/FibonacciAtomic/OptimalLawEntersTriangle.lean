/- GID: D5/S3/Arith/FibonacciAtomic/OptimalLawEntersTriangle
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/OptimalLawEntersTriangle
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Every attaining positive real law has a canonical reduced triangular root path. -/

import D5.S3.Arith.FibonacciAtomic.OptimalLawNearestStrictCeiling
import D5.S3.Arith.FibonacciAtomic.TriangularPathNormalization
import D5.S3.Arith.FibonacciAtomic.CarryGraphEmbedding
import Mathlib.Data.Fin.Tuple.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.OptimalLawEntersTriangle

open scoped BigOperators
open CarryGraphCriticalAttainment (alpha)
open DyadicSupportLines (cost residual)

open TriangularPathNormalization (RootPath anchorMass pathCost probability)

/-- Every strictly positive normalized law attaining the least cost-to-minimum ratio
is the output of a reduced triangular root path after one fixed label permutation.
The path preserves the minimum probability and the exact dyadic sampling cost. -/
theorem result (m : ℕ) (hm : 2 ≤ m) (p : Fin m → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (hopt : cost p = alpha m * sInf (Set.range p)) :
    ∃ (σ : Equiv.Perm (Fin m)) (γ : RootPath m),
      (∀ i, probability γ i = p (σ i)) ∧
      anchorMass γ = sInf (Set.range p) ∧ pathCost γ = cost p := by
  classical
  have departure : ∀ i : Fin m, sInf (Set.range p) < p i → ∃ D : ℕ,
      (∀ d < D, ⌊(2 : ℝ) ^ d * p i⌋ = ⌊(2 : ℝ) ^ d * sInf (Set.range p)⌋) ∧
      (∀ d, D ≤ d → Int.fract ((2 : ℝ) ^ d * p i) = 0) := by
    intro i hi
    let t := sInf (Set.range p)
    have tpos : 0 < t := by
      have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
      obtain ⟨k, hk⟩ := (Set.range_nonempty p).csInf_mem (Set.finite_range p)
      change 0 < sInf (Set.range p)
      rw [← hk]
      exact hp k
    have term := OptimalLawLargerAtomsTerminate.result m hm p hp hs hopt i hi
    let D := Nat.find term
    obtain ⟨N, hN⟩ := Nat.find_spec term
    change p i = (N : ℝ) / (2 : ℝ) ^ D at hN
    have ceiling : p i = ((⌊(2 : ℝ) ^ D * t⌋ : ℝ) + 1) / (2 : ℝ) ^ D :=
      OptimalLawNearestStrictCeiling.result m hm p hp hs hopt i hi
    have grid (d : ℕ) (hd : D ≤ d) : ∃ A : ℕ, p i = (A : ℝ) / (2 : ℝ) ^ d := by
      refine ⟨N * 2 ^ (d - D), ?_⟩
      rw [hN, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [show (2 : ℝ) ^ d = (2 : ℝ) ^ D * (2 : ℝ) ^ (d - D) by
        rw [← pow_add, Nat.add_sub_of_le hd]]
      field_simp
    have shallow (d : ℕ) (hd : d < D) :
        ⌊(2 : ℝ) ^ d * p i⌋ = ⌊(2 : ℝ) ^ d * t⌋ := by
      let B := ⌊(2 : ℝ) ^ d * t⌋ + 1
      have Bpos : 0 ≤ B := by
        have H := Int.floor_nonneg.mpr
          (mul_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ d) tpos.le)
        dsimp [B]
        omega
      let Q : ℝ := (B : ℝ) / (2 : ℝ) ^ d
      have Qt : t < Q := by
        apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ d)).mpr
        dsimp [B]
        push_cast
        simpa only [mul_comm] using Int.lt_floor_add_one ((2 : ℝ) ^ d * t)
      have Qgrid : (2 : ℝ) ^ D * Q = (B * 2 ^ (D - d) : ℤ) := by
        dsimp [Q]
        rw [show (2 : ℝ) ^ D = (2 : ℝ) ^ d * (2 : ℝ) ^ (D - d) by
          rw [← pow_add, Nat.add_sub_of_le hd.le]]
        push_cast
        field_simp
      have bound : p i ≤ Q := by
        rw [ceiling]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ D)).mpr
        have H := mul_lt_mul_of_pos_left Qt (by positivity : (0 : ℝ) < (2 : ℝ) ^ D)
        rw [Qgrid] at H
        have H' : ⌊(2 : ℝ) ^ D * t⌋ < B * 2 ^ (D - d) := Int.floor_lt.mpr H
        have H'' : ⌊(2 : ℝ) ^ D * t⌋ + 1 ≤ B * 2 ^ (D - d) := by omega
        have castH : (⌊(2 : ℝ) ^ D * t⌋ : ℝ) + 1 ≤ (B * 2 ^ (D - d) : ℤ) := by
          exact_mod_cast H''
        rw [mul_comm Q, Qgrid]
        exact castH
      have lower : ⌊(2 : ℝ) ^ d * t⌋ ≤ ⌊(2 : ℝ) ^ d * p i⌋ :=
        Int.floor_mono (mul_le_mul_of_nonneg_left hi.le (by positivity))
      by_contra ne
      have bigger : B ≤ ⌊(2 : ℝ) ^ d * p i⌋ := by dsimp [B]; omega
      have above : Q ≤ p i := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ d)).mpr
        exact (by exact_mod_cast bigger : (B : ℝ) ≤ (⌊(2 : ℝ) ^ d * p i⌋ : ℝ)).trans
          (by simpa only [mul_comm] using Int.floor_le ((2 : ℝ) ^ d * p i))
      have eq : p i = Q := le_antisymm bound above
      apply Nat.find_min term hd
      refine ⟨B.toNat, ?_⟩
      rw [eq]
      dsimp [Q]
      congr 1
      exact_mod_cast (Int.toNat_of_nonneg Bpos).symm
    refine ⟨D, shallow, ?_⟩
    intro d hd
    obtain ⟨A, hA⟩ := grid d hd
    have eq : (2 : ℝ) ^ d * p i = A := by rw [hA]; field_simp
    rw [eq]
    exact Int.fract_natCast A
  let σ := Tuple.sort p
  let q : Fin m → ℝ := p ∘ σ
  let k : Fin m := ⟨0, by omega⟩
  have hpq (i : Fin m) : 0 < q i := hp (σ i)
  have hsq : ∑ i, q i = 1 := (Equiv.sum_comp σ p).trans hs
  have sorted : Monotone q := Tuple.monotone_sort p
  have min_eq : q k = sInf (Set.range p) := by
    have : Nonempty (Fin m) := ⟨k⟩
    obtain ⟨j, hj⟩ := (Set.range_nonempty p).csInf_mem (Set.finite_range p)
    apply le_antisymm
    · have H := sorted (show k ≤ σ.symm j by change 0 ≤ (σ.symm j).val; omega)
      simpa only [q, Function.comp_apply, Equiv.apply_symm_apply, hj] using H
    · exact csInf_le (Set.finite_range p).bddBelow ⟨σ k, rfl⟩
  have off : ∀ (d : ℕ) (i : Fin m),
      ⌊(2 : ℝ) ^ d * q i⌋ ≠ ⌊(2 : ℝ) ^ d * q k⌋ →
      Int.fract ((2 : ℝ) ^ d * q i) = 0 := by
    intro d i hi
    have low : q k ≤ q i := sorted (by change 0 ≤ i.val; omega)
    have bigger : sInf (Set.range p) < q i := by
      rw [min_eq] at low
      apply lt_of_le_of_ne low
      intro eq
      apply hi
      rw [← eq, min_eq]
    obtain ⟨D, shallow, tail⟩ := departure (σ i) bigger
    by_cases hd : d < D
    · exfalso
      apply hi
      exact (shallow d hd).trans (congrArg (fun x : ℝ => ⌊(2 : ℝ) ^ d * x⌋) min_eq).symm
    · exact tail d (by omega)
  have construction : ∃ γ : RootPath m, (∀ i, probability γ i = q i) ∧
      anchorMass γ = q k ∧ pathCost γ = cost q := by
    classical
    let k : Fin m := ⟨0, by omega⟩
    have low (i : Fin m) : q k ≤ q i := sorted (by change 0 ≤ i.val; omega)
    obtain ⟨g, hg, gr, ge, gb, ga, gc⟩ :=
      (CarryGraphEmbedding.result m hm).2.2.2 q hpq hsq k low
    let n (d : ℕ) (i : Fin m) : ℤ := ⌊(2 : ℝ) ^ d * q i⌋
    let z (d : ℕ) (i : Fin m) : ℤ :=
      D5.S1.Digit.RadixFloorDigit.digitInt 2 ((2 : ℝ) ^ d * q i)
    let F (d : ℕ) (i : Fin m) : ℝ := Int.fract ((2 : ℝ) ^ d * q i)
    let e (d : ℕ) : ℕ := (Finset.univ.filter (fun i => n d i = n d k)).card
    let r (d : ℕ) : ℕ := (g.state d).r.toNat
    have zeq (d : ℕ) (i : Fin m) : z d i = n (d + 1) i - 2 * n d i := by
      simp only [z, n, D5.S1.Digit.RadixFloorDigit.digitInt,
        pow_succ', mul_assoc, Nat.cast_ofNat]
    have zb (d : ℕ) (i : Fin m) : 0 ≤ z d i ∧ z d i ≤ 1 := by
      have lo := D5.S1.Digit.RadixFloorDigit.digitInt_nonneg 2 ((2 : ℝ) ^ d * q i)
      have hi := D5.S1.Digit.RadixFloorDigit.digitInt_lt 2 (by norm_num)
        ((2 : ℝ) ^ d * q i)
      exact ⟨lo, by change z d i < 2 at hi; omega⟩
    have nb (d : ℕ) (i : Fin m) : n d k ≤ n d i :=
      Int.floor_mono (mul_le_mul_of_nonneg_left (low i) (by positivity))
    have same (d : ℕ) (i : Fin m) :
        n (d + 1) i = n (d + 1) k ↔ n d i = n d k ∧ z d i = z d k := by
      have H := zb d i
      have K := zb d k
      have L := nb d i
      simp only [zeq] at *
      omega
    have Fb (d : ℕ) (i : Fin m) : 0 ≤ F d i ∧ F d i < 1 :=
      ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    have Fstep (d : ℕ) (i : Fin m) :
        2 * F d i = (z d i : ℝ) + F (d + 1) i := by
      simp only [zeq]
      dsimp only [F, Int.fract, n]
      push_cast
      rw [pow_succ']
      ring
    have offF (d : ℕ) (i : Fin m) (hi : n d i ≠ n d k) : F d i = 0 :=
      off d i hi
    have offz (d : ℕ) (i : Fin m) (hi : n d i ≠ n d k) : z d i = 0 := by
      have H := Fstep d i
      rw [offF d i hi] at H
      have B := (Fb (d + 1) i).1
      have Z : (0 : ℝ) ≤ z d i := by exact_mod_cast (zb d i).1
      have eq : (z d i : ℝ) = 0 := by linarith only [H, B, Z]
      exact_mod_cast eq
    have index (d : ℕ) (i : Fin m) : i.val < e d ↔ n d i = n d k := by
      have mono : Monotone (n d) := fun a b hab =>
        Int.floor_mono (mul_le_mul_of_nonneg_left (sorted hab) (by positivity))
      have P (j : Fin m) : n d j ≤ n d k ↔ n d j = n d k := by
        have H := nb d j
        omega
      simpa only [P, e] using
        (Tuple.lt_card_le_iff_apply_le_of_monotone (j := i) (a := n d k) mono)
    have ecast (d : ℕ) : (e d : ℤ) = (g.state d).e := (ge d).symm
    have eb (d : ℕ) : 0 < e d ∧ e d ≤ m := by
      have H := (hg.2 d).1.1.2.2
      rw [← ecast d] at H
      exact_mod_cast H
    have rcast (d : ℕ) : (r d : ℝ) = residual q d := by
      have H : (r d : ℤ) = (g.state d).r :=
        Int.toNat_of_nonneg (hg.2 d).1.1.1
      have H' : (r d : ℝ) = ((g.state d).r : ℝ) := by exact_mod_cast H
      exact H'.trans (gr d)
    have Fsum (d : ℕ) : ∑ i, F d i = (r d : ℝ) := by
      rw [rcast]
      simp only [F, Int.fract, DyadicSupportLines.residual, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hsq, mul_one, Int.cast_sum]
    have count (d : ℕ) : (∑ i : Fin m, if n d i = n d k then (1 : ℝ) else 0) = e d := by
      simp [e, Finset.sum_boole]
    have rb (d : ℕ) : r d < e d := by
      have H : (∑ i, F d i) < ∑ i : Fin m, if n d i = n d k then (1 : ℝ) else 0 := by
        apply Finset.sum_lt_sum
        · intro i _
          by_cases hi : n d i = n d k
          · simp only [hi, ite_true]
            exact (Fb d i).2.le
          · simp only [hi, ite_false, offF d i hi]
            rfl
        · refine ⟨k, Finset.mem_univ k, ?_⟩
          simp only [ite_true]
          exact (Fb d k).2
      rw [Fsum, count] at H
      exact_mod_cast H
    have shrink (d : ℕ) : e (d + 1) ≤ e d := by
      apply Finset.card_le_card
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        ((same d i).mp (Finset.mem_filter.mp hi).2).1⟩
    have one_same (d : ℕ) (hb : z d k = 1) (i : Fin m) (hi : n d i = n d k) :
        z d i = 1 := by
      have H := nb (d + 1) i
      have Z := zb d i
      simp only [zeq] at *
      omega
    have one_e (d : ℕ) (hb : z d k = 1) : e (d + 1) = e d := by
      apply congrArg Finset.card
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, same]
      exact ⟨And.left, fun hi => ⟨hi, (one_same d hb i hi).trans hb.symm⟩⟩
    have column (d : ℕ) :
        (∑ i, z d i) = if z d k = 1 then (e d : ℤ) else (e d : ℤ) - e (d + 1) := by
      by_cases hb : z d k = 1
      · rw [if_pos hb]
        have H (i : Fin m) : z d i = if n d i = n d k then 1 else 0 := by
          by_cases hi : n d i = n d k
          · simp only [hi, ite_true]
            exact one_same d hb i hi
          · simp only [hi, ite_false]
            exact offz d i hi
        simp_rw [H]
        simp [e, Finset.sum_boole]
      · rw [if_neg hb]
        have hb0 : z d k = 0 := by have H := zb d k; omega
        have H (i : Fin m) : z d i =
            (if n d i = n d k then 1 else 0) -
            (if n (d + 1) i = n (d + 1) k then 1 else 0) := by
          have S := same d i
          have Z := zb d i
          by_cases hi : n d i = n d k
          · by_cases hn : n (d + 1) i = n (d + 1) k
            · have zeq := (S.mp hn).2
              simp [hi, hn, zeq, hb0]
            · have zne : z d i ≠ 0 := by intro eq; exact hn (S.mpr ⟨hi, eq.trans hb0.symm⟩)
              simp only [hi, hn, ite_true, ite_false]
              omega
          · have hn : n (d + 1) i ≠ n (d + 1) k := fun h => hi (S.mp h).1
            simp only [hi, hn, ite_false, sub_zero]
            exact offz d i hi
        simp_rw [H]
        rw [Finset.sum_sub_distrib]
        simp [e, Finset.sum_boole]
    have recurrence (d : ℕ) : (r (d + 1) : ℤ) = 2 * r d - ∑ i, z d i := by
      have H : (r (d + 1) : ℝ) = 2 * (r d : ℝ) - ∑ i, (z d i : ℝ) := by
        rw [← Fsum (d + 1), ← Fsum d, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        linarith only [Fstep d i]
      exact_mod_cast H
    have threshold (d : ℕ) :
        (z d k = 1 → e d ≤ 2 * r d) ∧ (z d k = 0 → 2 * r d < e d) := by
      constructor
      · intro hb
        have H := recurrence d
        rw [column d, if_pos hb] at H
        omega
      · intro hb
        have upper (i : Fin m) : 2 * F d i ≤ if n d i = n d k then 1 else 0 := by
          by_cases hi : n d i = n d k
          · simp only [hi, ite_true]
            by_cases hn : n (d + 1) i = n (d + 1) k
            · have H := (same d i).mp hn
              have S := Fstep d i
              rw [H.2, hb] at S
              norm_num only [Int.cast_zero, zero_add] at S
              linarith only [S, (Fb (d + 1) i).2]
            · have S := Fstep d i
              rw [offF (d + 1) i hn] at S
              have Z : (z d i : ℝ) ≤ 1 := by exact_mod_cast (zb d i).2
              linarith only [S, Z]
          · simp only [hi, ite_false, offF d i hi]
            norm_num
        have strict : 2 * F d k < (if n d k = n d k then (1 : ℝ) else 0) := by
          simp only [ite_true]
          have S := Fstep d k
          rw [hb] at S
          norm_num only [Int.cast_zero, zero_add] at S
          linarith only [S, (Fb (d + 1) k).2]
        have H := Finset.sum_lt_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => upper i)
          ⟨k, Finset.mem_univ k, strict⟩
        rw [← Finset.mul_sum, Fsum, count] at H
        exact_mod_cast H
    let act (d : ℕ) : TriangularPathNormalization.Action :=
      if z d k = 1 then .one else .zero (e d - e (d + 1))
    let γ : RootPath m := {
      state := fun d => ⟨r d, e d⟩
      action := act
      root := by
        have R : r 0 = 1 := by simp [r, hg.1, CarryGraphEmbedding.root]
        have E : e 0 = m := by
          have H := ecast 0
          rw [hg.1] at H
          change (e 0 : ℤ) = (m : ℤ) at H
          exact_mod_cast H
        simp [R, E]
      legal := by
        intro d
        refine ⟨(eb d).1, rb d, (eb d).2, ?_⟩
        dsimp only [act]
        by_cases hb : z d k = 1
        · rw [if_pos hb]
          exact (threshold d).1 hb
        · rw [if_neg hb]
          have H := recurrence d
          rw [column d, if_neg hb] at H
          have S := shrink d
          have hb0 : z d k = 0 := by have B := zb d k; omega
          exact ⟨(threshold d).2 hb0, by omega⟩
      step := by
        intro d
        dsimp only [act]
        have H := recurrence d
        rw [column d] at H
        by_cases hb : z d k = 1
        · rw [if_pos hb]
          rw [if_pos hb] at H
          simp only [TriangularPathNormalization.successor]
          congr 1
          · omega
          · exact one_e d hb
        · rw [if_neg hb]
          rw [if_neg hb] at H
          have S := shrink d
          simp only [TriangularPathNormalization.successor]
          congr 1 <;> omega }
    have digit_z (d : ℕ) (i : Fin m) :
        ((TriangularPathNormalization.digit γ i d).val : ℤ) = z d i := by
      by_cases hi : i.val < e d
      · have he := (index d i).mp hi
        by_cases hb : z d k = 1
        · simp only [TriangularPathNormalization.digit, γ, act, hi, ite_true, hb,
            Fin.val_one, Nat.cast_one]
          exact (one_same d hb i he).symm
        · have B := zb d k
          have hb0 : z d k = 0 := by omega
          have S := shrink d
          have bound : e d - (e d - e (d + 1)) = e (d + 1) := by omega
          simp only [TriangularPathNormalization.digit, γ, act, hi, ite_true,
            hb, ite_false, bound]
          by_cases hn : i.val < e (d + 1)
          · have H := (same d i).mp ((index (d + 1) i).mp hn)
            have notle : ¬ e (d + 1) ≤ i.val := by omega
            simp only [notle, ite_false, Fin.val_zero, Nat.cast_zero]
            exact (H.2.trans hb0).symm
          · have notsame : n (d + 1) i ≠ n (d + 1) k := fun h => hn ((index (d + 1) i).mpr h)
            have Z := zb d i
            have notzero : z d i ≠ 0 := by
              intro eq
              exact notsame ((same d i).mpr ⟨he, eq.trans hb0.symm⟩)
            have le : e (d + 1) ≤ i.val := by omega
            simp only [le, ite_true, Fin.val_one, Nat.cast_one]
            omega
      · have he : n d i ≠ n d k := fun h => hi ((index d i).mpr h)
        simp only [TriangularPathNormalization.digit, γ, hi, ite_false, Fin.val_zero, Nat.cast_zero]
        exact (offz d i he).symm
    have anchor_z (d : ℕ) :
        ((TriangularPathNormalization.anchorDigit (γ.action d)).val : ℤ) = z d k := by
      have B := zb d k
      dsimp only [γ, act]
      by_cases hb : z d k = 1
      · simp [hb, TriangularPathNormalization.anchorDigit]
      · have hz : z d k = 0 := by omega
        simp [hz, TriangularPathNormalization.anchorDigit]
    refine ⟨γ, ?_, ?_, ?_⟩
    · intro i
      have plt : q i < 1 := by
        let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
        obtain ⟨j, hj⟩ := exists_ne i
        have H := Finset.single_lt_sum (s := Finset.univ) (f := q)
          hj (Finset.mem_univ i) (Finset.mem_univ j) (hpq j) (fun l _ _ => (hpq l).le)
        rwa [hsq] at H
      have dz (d : ℕ) : (Real.digits (q i) 2 d).val =
          (TriangularPathNormalization.digit γ i d).val := by
        have div : n (d + 1) i / 2 = n d i := by
          dsimp only [n]
          rw [pow_succ', mul_assoc]
          exact Int.natCast_mul_floor_div_cancel (n := 2) (by norm_num) _
        have rem : n (d + 1) i % 2 = z d i := by rw [zeq]; omega
        have eq : ((Real.digits (q i) 2 d).val : ℤ) = z d i := by
          simp only [Real.digits, Fin.val_ofNat, Int.natCast_mod, Nat.cast_ofNat]
          rw [Int.natCast_floor_eq_floor (mul_nonneg (hpq i).le (by positivity)), mul_comm]
          exact rem
        exact_mod_cast eq.trans (digit_z d i).symm
      have deq : TriangularPathNormalization.digit γ i = Real.digits (q i) 2 := by
        funext d
        exact Fin.ext (dz d).symm
      unfold probability
      simp_rw [deq, div_eq_mul_inv]
      exact Real.ofDigits_digits (by norm_num : 1 < 2) ⟨(hpq i).le, plt⟩
    · rw [← ga]
      unfold anchorMass CarryGraphEmbedding.anchorValue
      apply tsum_congr
      intro d
      have H := anchor_z d
      have G := gb d
      rw [← zeq] at G
      rw [G]
      congr 1
      exact_mod_cast H
    · unfold pathCost cost
      apply tsum_congr
      intro d
      exact congrArg (fun x : ℝ => x / (2 : ℝ) ^ d) (rcast d)
  obtain ⟨γ, law, anchor, bill⟩ := construction
  refine ⟨σ, γ, law, anchor.trans min_eq, bill.trans ?_⟩
  unfold cost
  apply tsum_congr
  intro d
  congr 1
  unfold DyadicSupportLines.residual
  rw [show (∑ i, ⌊(2 : ℝ) ^ d * q i⌋) =
      ∑ i, ⌊(2 : ℝ) ^ d * p i⌋ from
    Equiv.sum_comp σ (fun i => ⌊(2 : ℝ) ^ d * p i⌋)]

end D5.S3.Arith.FibonacciAtomic.OptimalLawEntersTriangle
