/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSpectralBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/UniformSpectralBound
   mirror-E: none(waiver:kernel-checked-uniform-estimate)
   anchors: []
   utility: none
   digest: The first qutrit LMI bounds spectral purity in dimensions at least 33. -/

/-
proof_shape: uniform_spectral_bound: content
escape_witness: The gap reconstruction, thirty-three ray estimates and convex
  mixture transfer yield a uniform Euclidean norm estimate from boundary mass constraints.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib and same-delivery supporting modules)
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.Entanglement.AbsolutePPT.BoundaryConeDecomposition
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction

set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 8192
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSpectralBound
open Finset Matrix BoundaryConeDecomposition QutritSpectralReduction

theorem uniform_spectral_bound (k : ℕ) (hk : 8 ≤ k)
    (l : Fin (3*(3+k)) → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i)
    (ht : ∑ i, l i = 1) (h1 : (K1 (boundaryValues k l)).PosSemidef) :
    ∑ i, (l i)^2 ≤ 3/(8*((3+k : ℕ) : ℝ)) := by
  have uniform_scalar_bound (d : ℕ) (hd : 33 ≤ d) (l : Fin d → ℝ)
      (ho : Antitone l) (hn : ∀ i, 0 ≤ l i) (ht : ∑ i, l i = 1)
      (hL : l ⟨0, by omega⟩ + l ⟨1, by omega⟩ + l ⟨2, by omega⟩ ≤
        l ⟨d-6, by omega⟩ + l ⟨d-5, by omega⟩ + l ⟨d-4, by omega⟩ +
        l ⟨d-3, by omega⟩ + l ⟨d-2, by omega⟩ + l ⟨d-1, by omega⟩)
      (hC : l ⟨0, by omega⟩ ≤
        l ⟨d-3, by omega⟩ + l ⟨d-2, by omega⟩ + l ⟨d-1, by omega⟩) :
      ∑ i, (l i)^2 ≤ 9/(8*(d : ℝ)) := by
    let spectralGood {d : ℕ} (c : ℝ) (x : Fin d → ℝ) : Prop :=
      ‖WithLp.toLp 2 x‖ ≤ c * ∑ i, x i

    have spectralGood_zero (d : ℕ) (c : ℝ) : spectralGood c (0 : Fin d → ℝ) := by
      simp [spectralGood]

    have spectralGood_add {d : ℕ} (c : ℝ) (x y : Fin d → ℝ)
        (hx : spectralGood c x) (hy : spectralGood c y) : spectralGood c (x+y) := by
      unfold spectralGood at *
      have he : WithLp.toLp 2 (x+y) = WithLp.toLp 2 x + WithLp.toLp 2 y := rfl
      rw [he]
      calc
        _ ≤ ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 y‖ := norm_add_le _ _
        _ ≤ c*(∑ i,x i) + c*(∑ i,y i) := add_le_add hx hy
        _ = c*(∑ i,(x+y) i) := by simp [Finset.sum_add_distrib,mul_add]

    have spectralGood_smul {d : ℕ} (c t : ℝ) (x : Fin d → ℝ)
        (ht : 0≤t) (hx : spectralGood c x) : spectralGood c (t • x) := by
      unfold spectralGood at *
      have he : WithLp.toLp 2 (t • x) = t • WithLp.toLp 2 x := rfl
      rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
      calc
        _ ≤ t*(c*∑ i,x i) := mul_le_mul_of_nonneg_left hx ht
        _ = c*∑ i,(t • x) i := by simp [Finset.mul_sum,mul_assoc,mul_comm,mul_left_comm]

    have spectralGood_of_square {d : ℕ} (c : ℝ) (x : Fin d → ℝ) (hc : 0≤c)
        (hs : 0≤∑ i,x i) (hb : ∑ i,(x i)^2 ≤ c^2*(∑ i,x i)^2) : spectralGood c x := by
      unfold spectralGood
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc hs)).mp
      rw [EuclideanSpace.real_norm_sq_eq]
      simpa [mul_pow] using hb

    have spectralGood_square {d : ℕ} (c : ℝ) (x : Fin d → ℝ) (hc : 0≤c)
        (hs : 0≤∑ i,x i) (hb : spectralGood c x) : ∑ i,(x i)^2 ≤ c^2*(∑ i,x i)^2 := by
      unfold spectralGood at hb
      have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc hs)).mpr hb
      rw [EuclideanSpace.real_norm_sq_eq] at h
      simpa [mul_pow] using h

    let step (d j : ℕ) : Fin d → ℝ := fun k => if k.val<j then 1 else 0

    have sum_step (d j : ℕ) (hj : j≤d) : ∑ k, step d j k = (j : ℝ) := by
      simp only [step]
      rw [Fin.sum_univ_eq_sum_range (f := fun k : ℕ => if k<j then (1 : ℝ) else 0)]
      rw [sum_ite]
      simp only [sum_const_zero,add_zero,sum_const,mul_one]
      have he : (Finset.range d).filter (fun k => k<j) = Finset.range j := by
        ext k
        simp only [mem_filter,mem_range]
        omega
      rw [he,card_range]
      simp

    have sum_step_mul (d i j : ℕ) (hi : i≤d) (hj : j≤d) :
        ∑ k, step d i k * step d j k = (min i j : ℕ) := by
      have he : ∀ k, step d i k*step d j k = step d (min i j) k := by
        intro k
        simp only [step,lt_min_iff]
        split_ifs <;> simp_all
      simp_rw [he]
      exact sum_step _ _ (le_trans (min_le_left _ _) hi)

    let synth {d : ℕ} (p : Fin 9 → ℕ) : (Fin 9 → ℝ) →ₗ[ℝ] (Fin d → ℝ) := {
      toFun x := ∑ j, x j • step d (p j)
      map_add' x y := by simp [add_smul,Finset.sum_add_distrib]
      map_smul' t x := by simp [Finset.smul_sum,smul_smul] }

    have mass_synth {d : ℕ} (p : Fin 9 → ℕ) (hp : ∀ j,p j≤d) (x : Fin 9 → ℝ) :
        ∑ k : Fin d, synth p x k = ∑ j,x j*(p j : ℝ) := by
      simp only [synth,LinearMap.coe_mk,AddHom.coe_mk,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      rw [← mul_sum,sum_step _ _ (hp j)]

    have square_synth {d : ℕ} (p : Fin 9 → ℕ) (hp : ∀ j,p j≤d) (x : Fin 9 → ℝ) :
        ∑ k : Fin d, (synth p x k)^2 = ∑ i,∑ j, x i*x j*(min (p i) (p j) : ℕ) := by
      simp only [synth,LinearMap.coe_mk,AddHom.coe_mk,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,pow_two]
      simp_rw [sum_mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      simp_rw [show ∀ k, (x i * step d (p i) k)*(x j*step d (p j) k) = (x i*x j)*(step d (p i) k*step d (p j) k) from fun k => by ring]
      rw [← mul_sum,sum_step_mul _ _ _ (hp i) (hp j)]

    let extend {d : ℕ} (l : Fin d → ℝ) (j : ℕ) : ℝ := if h:j<d then l ⟨j,h⟩ else 0

    let spectralGap {d : ℕ} (l : Fin d → ℝ) (j : Fin d) : ℝ := extend l j.val-extend l (j.val+1)

    have spectralGap_nonneg {d : ℕ} (l : Fin d → ℝ) (ho : Antitone l) (hn : ∀ j,0≤l j) :
        ∀ j, 0 ≤ spectralGap l j := by
      intro j
      unfold spectralGap extend
      simp only [dif_pos j.isLt]
      split_ifs with h
      · exact sub_nonneg.mpr (ho (by change j.val ≤ j.val+1;omega))
      · simpa using hn j

    have gap_telescope {d : ℕ} (l : Fin d → ℝ) (a b : ℕ) (hab : a≤b) :
        ∑ j ∈ Ico a b, (extend l j-extend l (j+1)) = extend l a-extend l b := by
      have h := Finset.sum_Ico_sub (f := extend l) hab
      calc
        _ = -(∑ j ∈ Ico a b, (extend l (j+1)-extend l j)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [h];ring

    have gap_reconstruct {d : ℕ} (l : Fin d → ℝ) :
        (∑ j, spectralGap l j • step d (j.val+1)) = l := by
      ext k
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,step]
      have he : ∀ j : Fin d, spectralGap l j*(if k.val<j.val+1 then 1 else 0) =
          (fun j : ℕ => if k.val≤j then extend l j-extend l (j+1) else 0) j.val := by
        intro j
        simp only [spectralGap]
        by_cases h : k.val≤j.val
        · simp [h,show k.val<j.val+1 from by omega]
        · simp [h,show ¬k.val<j.val+1 from by omega]
      simp_rw [he]
      rw [Fin.sum_univ_eq_sum_range (f := fun j : ℕ => if k.val≤j then extend l j-extend l (j+1) else 0)]
      rw [sum_ite]
      simp only [sum_const_zero,add_zero]
      have hf : (range d).filter (fun j => k.val≤j) = Ico k.val d := by
        ext j
        simp only [mem_filter,mem_range,mem_Ico]
        omega
      rw [hf,gap_telescope l _ _ (le_of_lt k.isLt)]
      simp [extend,k.isLt]

    let compressed {d : ℕ} (l : Fin d → ℝ) : Fin 9 → ℝ :=
     ![extend l 0-extend l 1,extend l 1-extend l 2,extend l 2-extend l (d-6),
       extend l (d-6)-extend l (d-5),extend l (d-5)-extend l (d-4),
       extend l (d-4)-extend l (d-3),extend l (d-3)-extend l (d-2),
       extend l (d-2)-extend l (d-1),extend l (d-1)]

    let base {d : ℕ} (l : Fin d → ℝ) : Fin d → ℝ :=
      (extend l 0-extend l 1) • step d 1 + (extend l 1-extend l 2) • step d 2 +
      (extend l (d-6)-extend l (d-5)) • step d (d-5) +
      (extend l (d-5)-extend l (d-4)) • step d (d-4) +
      (extend l (d-4)-extend l (d-3)) • step d (d-3) +
      (extend l (d-3)-extend l (d-2)) • step d (d-2) +
      (extend l (d-2)-extend l (d-1)) • step d (d-1) +
      extend l (d-1) • step d d

    have compressed_nonnegative {d : ℕ} (l : Fin d → ℝ) (hd : 33≤d)
        (ho : Antitone l) (hn : ∀ i,0≤l i) : ∀ j,0≤compressed l j := by
      have he : ∀ a b, a≤b → b<d → extend l b≤extend l a := by
        intro a b hab hb
        simp only [extend,dif_pos hb,dif_pos (lt_of_le_of_lt hab hb)]
        exact ho hab
      intro j
      fin_cases j <;> simp only [compressed,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one]
      all_goals first
        | apply sub_nonneg.mpr;apply he <;> omega
        | simp only [extend,dif_pos (show d-1<d from by omega)];exact hn _

    have middle_mass {d : ℕ} (l : Fin d → ℝ) (hd : 33≤d) :
        (∑ j ∈ Ico 2 (d-6), (extend l j-extend l (j+1))) = compressed l 2 := by
      rw [gap_telescope l _ _ (by omega)]
      simp [compressed]

    have spectrum_split {d : ℕ} (l : Fin d → ℝ) (hd : 33≤d) :
        l = base l + ∑ j ∈ Ico 2 (d-6), (extend l j-extend l (j+1)) • step d (j+1) := by
      let f : ℕ → (Fin d → ℝ) := fun j => (extend l j-extend l (j+1)) • step d (j+1)
      have he : (∑ j : Fin d, spectralGap l j • step d (j.val+1)) = ∑ j ∈ range d,f j := by
        exact Fin.sum_univ_eq_sum_range f d
      conv_lhs => rw [← gap_reconstruct l,he]
      rw [← Nat.Ico_zero_eq_range]
      rw [← sum_Ico_consecutive f (show 0≤2 from by omega) (show 2≤d from by omega)]
      rw [← sum_Ico_consecutive f (show 2≤d-6 from by omega) (show d-6≤d from by omega)]
      rw [sum_Ico_eq_sum_range f 0 2,sum_Ico_eq_sum_range f (d-6) d]
      rw [show d-(d-6)=6 from by omega]
      simp only [sum_range_succ,sum_range_zero,zero_add,Nat.zero_add,f]
      have hd1 : d-6+1=d-5 := by omega
      have hd2 : d-6+2=d-4 := by omega
      have hd3 : d-6+3=d-3 := by omega
      have hd4 : d-6+4=d-2 := by omega
      have hd5 : d-6+5=d-1 := by omega
      have hd6 : d-6+6=d := by omega
      have ht1 : d-5+1=d-4 := by omega
      have ht2 : d-4+1=d-3 := by omega
      have ht3 : d-3+1=d-2 := by omega
      have ht4 : d-2+1=d-1 := by omega
      have ht5 : d-1+1=d := by omega
      simp only [hd1,hd2,hd3,hd4,hd5,hd6,ht1,ht2,ht3,ht4,ht5,show extend l d=0 from by simp [extend],sub_zero]
      dsimp only [base]
      ext k
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring

    have ray_00_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ ((-18 + d) * (-2 + d)) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_01_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ ((-1 + d) * (-9 + d)) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_02_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (d ^ 2) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_03_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (d * (-16 + d)) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_04_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (36 + (d ^ 2) + (-28 * d)) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_05_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (36 + (-88 * d) + (4 * (d ^ 2))) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_06_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (9 + (d ^ 2) + (-22 * d)) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_07_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ ((-108 + (4 * d)) * (-3 + d)) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_08_nonnegative (d : ℝ) (i : ℝ) (hd : 33 ≤ d) :
        0 ≤ (81 + (-108 * i) + (-90 * d) + (9 * (d ^ 2)) + (36 * (i ^ 2)) + (-20 * d * i)) := by
      have ht : 0 ≤ d - 33 := by linarith
      have hres : 0 ≤ ((8 / 9) * d * (-135 + (7 * d))) := by nlinarith [sq_nonneg (d - 33)]
      have hid : (81 + (-108 * i) + (-90 * d) + (9 * (d ^ 2)) + (36 * (i ^ 2)) + (-20 * d * i)) = 36 * (i - ((3 / 2) + ((5 / 18) * d)))^2 + ((8 / 9) * d * (-135 + (7 * d))) := by ring
      rw [hid]
      positivity

    have ray_09_nonnegative (d : ℝ) (i : ℝ) (hd : 33 ≤ d) :
        0 ≤ (9 * ((d + (-3 * i)) ^ 2)) := by
      have ht : 0 ≤ d - 33 := by linarith
      have hres : 0 ≤ 0 := by nlinarith [sq_nonneg (d - 33)]
      have hid : (9 * ((d + (-3 * i)) ^ 2)) = 81 * (i - ((1 / 3) * d))^2 + 0 := by ring
      rw [hid]
      positivity

    have ray_10_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (1296 + (-352 * d) + (16 * (d ^ 2))) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_11_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (324 + (-88 * d) + (4 * (d ^ 2))) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_12_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ ((-75 + (5 * d)) * (-27 + (5 * d))) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_13_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (225 + (-76 * d) + (4 * (d ^ 2))) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_14_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (576 + (-176 * d) + (9 * (d ^ 2))) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_15_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (144 + (-64 * d) + (4 * (d ^ 2))) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_16_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (324 + (-132 * d) + (9 * (d ^ 2))) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_17_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (81 + (d ^ 2) + (-34 * d)) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_18_nonnegative (d : ℝ) (i : ℝ) (hd : 33 ≤ d) :
        0 ≤ (9 + (-60 * d) + (-18 * i) + (4 * (d ^ 2)) + (9 * (i ^ 2)) + (-4 * d * i)) := by
      have ht : 0 ≤ d - 33 := by linarith
      have hres : 0 ≤ ((32 / 9) * d * (-18 + d)) := by nlinarith [sq_nonneg (d - 33)]
      have hid : (9 + (-60 * d) + (-18 * i) + (4 * (d ^ 2)) + (9 * (i ^ 2)) + (-4 * d * i)) = 9 * (i - (1 + ((2 / 9) * d)))^2 + ((32 / 9) * d * (-18 + d)) := by ring
      rw [hid]
      positivity

    have ray_19_nonnegative (d : ℝ) (i : ℝ) (hd : 33 ≤ d) :
        0 ≤ (81 + (-108 * d) + (4 * (d ^ 2)) + (9 * (i ^ 2)) + (54 * i) + (-4 * d * i)) := by
      have ht : 0 ≤ d - 33 := by linarith
      have hres : 0 ≤ ((32 / 9) * d * (-27 + d)) := by nlinarith [sq_nonneg (d - 33)]
      have hid : (81 + (-108 * d) + (4 * (d ^ 2)) + (9 * (i ^ 2)) + (54 * i) + (-4 * d * i)) = 9 * (i - (-3 + ((2 / 9) * d)))^2 + ((32 / 9) * d * (-27 + d)) := by ring
      rw [hid]
      positivity

    have ray_20_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (144 + (-64 * d) + (4 * (d ^ 2))) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_21_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (36 + (-56 * d) + (4 * (d ^ 2))) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_22_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (81 + (-150 * d) + (9 * (d ^ 2))) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_23_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (36 + (-72 * d) + (4 * (d ^ 2))) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_24_nonnegative (d : ℝ) (i : ℝ) (hd : 33 ≤ d) :
        0 ≤ (324 + (-132 * d) + (-108 * i) + (9 * (d ^ 2)) + (9 * (i ^ 2)) + (-2 * d * i)) := by
      have ht : 0 ≤ d - 33 := by linarith
      have hres : 0 ≤ ((16 / 9) * d * (-81 + (5 * d))) := by nlinarith [sq_nonneg (d - 33)]
      have hid : (324 + (-132 * d) + (-108 * i) + (9 * (d ^ 2)) + (9 * (i ^ 2)) + (-2 * d * i)) = 9 * (i - (6 + ((1 / 9) * d)))^2 + ((16 / 9) * d * (-81 + (5 * d))) := by ring
      rw [hid]
      positivity

    have ray_25_nonnegative (d : ℝ) (i : ℝ) (hd : 33 ≤ d) :
        0 ≤ (1296 + (-408 * d) + (-216 * i) + (9 * (i ^ 2)) + (25 * (d ^ 2)) + (2 * d * i)) := by
      have ht : 0 ≤ d - 33 := by linarith
      have hres : 0 ≤ ((32 / 9) * d * (-108 + (7 * d))) := by nlinarith [sq_nonneg (d - 33)]
      have hid : (1296 + (-408 * d) + (-216 * i) + (9 * (i ^ 2)) + (25 * (d ^ 2)) + (2 * d * i)) = 9 * (i - (12 + ((-1 / 9) * d)))^2 + ((32 / 9) * d * (-108 + (7 * d))) := by ring
      rw [hid]
      positivity

    have ray_26_nonnegative (d : ℝ) (i : ℝ) (hd : 33 ≤ d) :
        0 ≤ (324 + (-216 * i) + (-192 * d) + (16 * (d ^ 2)) + (36 * (i ^ 2)) + (-16 * d * i)) := by
      have ht : 0 ≤ d - 33 := by linarith
      have hres : 0 ≤ ((16 / 9) * d * (-135 + (8 * d))) := by nlinarith [sq_nonneg (d - 33)]
      have hid : (324 + (-216 * i) + (-192 * d) + (16 * (d ^ 2)) + (36 * (i ^ 2)) + (-16 * d * i)) = 36 * (i - (3 + ((2 / 9) * d)))^2 + ((16 / 9) * d * (-135 + (8 * d))) := by ring
      rw [hid]
      positivity

    have ray_27_nonnegative (d : ℝ) (i : ℝ) (hd : 33 ≤ d) :
        0 ≤ (729 + (-486 * i) + (-324 * d) + (36 * (d ^ 2)) + (81 * (i ^ 2)) + (-36 * d * i)) := by
      have ht : 0 ≤ d - 33 := by linarith
      have hres : 0 ≤ (16 * d * (-27 + (2 * d))) := by nlinarith [sq_nonneg (d - 33)]
      have hid : (729 + (-486 * i) + (-324 * d) + (36 * (d ^ 2)) + (81 * (i ^ 2)) + (-36 * d * i)) = 81 * (i - (3 + ((2 / 9) * d)))^2 + (16 * d * (-27 + (2 * d))) := by ring
      rw [hid]
      positivity

    have ray_28_nonnegative (d : ℝ) (i : ℝ) (hd : 33 ≤ d) :
        0 ≤ (81 + (-54 * i) + (-52 * d) + (4 * (d ^ 2)) + (9 * (i ^ 2)) + (-4 * d * i)) := by
      have ht : 0 ≤ d - 33 := by linarith
      have hres : 0 ≤ ((32 / 9) * d * (-18 + d)) := by nlinarith [sq_nonneg (d - 33)]
      have hid : (81 + (-54 * i) + (-52 * d) + (4 * (d ^ 2)) + (9 * (i ^ 2)) + (-4 * d * i)) = 9 * (i - (3 + ((2 / 9) * d)))^2 + ((32 / 9) * d * (-18 + d)) := by ring
      rw [hid]
      positivity

    have ray_29_nonnegative (d : ℝ) (i : ℝ) (hd : 33 ≤ d) :
        0 ≤ (324 + (-216 * i) + (-192 * d) + (16 * (d ^ 2)) + (36 * (i ^ 2)) + (-16 * d * i)) := by
      have ht : 0 ≤ d - 33 := by linarith
      have hres : 0 ≤ ((16 / 9) * d * (-135 + (8 * d))) := by nlinarith [sq_nonneg (d - 33)]
      have hid : (324 + (-216 * i) + (-192 * d) + (16 * (d ^ 2)) + (36 * (i ^ 2)) + (-16 * d * i)) = 36 * (i - (3 + ((2 / 9) * d)))^2 + ((16 / 9) * d * (-135 + (8 * d))) := by ring
      rw [hid]
      positivity

    have ray_30_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (729 + (-190 * d) + (9 * (d ^ 2))) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_31_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (2916 + (-744 * d) + (36 * (d ^ 2))) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    have ray_32_nonnegative (d : ℝ) (hd : 33 ≤ d) :
        0 ≤ (1296 + (-336 * d) + (16 * (d ^ 2))) := by
      have ht : 0 ≤ d - 33 := by linarith
      nlinarith [sq_nonneg (d - 33)]

    let positions (d i : ℕ) : Fin 9 → ℕ := ![1,2,i,d-5,d-4,d-3,d-2,d-1,d]

    have positions_le (d i : ℕ) (hd : 33 ≤ d) (hi : 3 ≤ i) (hi' : i ≤ d-6) : ∀ j, positions d i j ≤ d := by
      intro j; fin_cases j <;> simp [positions] <;> omega

    have positions_monotone (d i : ℕ) (hd : 33 ≤ d) (hi : 3 ≤ i) (hi' : i ≤ d-6) : Monotone (positions d i) := by
      intro j k hjk
      fin_cases j <;> fin_cases k
      all_goals norm_num [Fin.le_def] at hjk
      all_goals norm_num [positions, Fin.reduceEq, Fin.reduceFinMk]
      all_goals omega

    have ray_spectral_good (d i : ℕ) (hd : 33 ≤ d) (hi : 3 ≤ i) (hi' : i ≤ d-6) :
        ∀ r, spectralGood (Real.sqrt (9/(8*(d : ℝ)))) (synth (d := d) (positions d i) (rays r)) := by
      intro r
      have hp := positions_le d i hd hi hi'
      have hmono := positions_monotone d i hd hi hi'
      have hdR : (33 : ℝ)  ≤  d := by exact_mod_cast hd
      have hdpos : (0 : ℝ) < d := by linarith
      refine spectralGood_of_square _ _ (Real.sqrt_nonneg _) ?_ ?_
      · rw [mass_synth _ hp]
        apply Finset.sum_nonneg
        intro j _
        apply mul_nonneg
        · fin_cases r <;> fin_cases j <;> norm_num [rays]
        · positivity
      · rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 9/(8*(d : ℝ)))]
        rw [mass_synth _ hp,square_synth _ hp]
        simp_rw [← hmono.map_min]
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8*(d : ℝ))).mpr
        have hcast : ∀ j, ((positions d i j : ℕ) : ℝ) =
            (![1,2,(i : ℝ),(d : ℝ)-5,(d : ℝ)-4,(d : ℝ)-3,(d : ℝ)-2,(d : ℝ)-1,(d : ℝ)] : Fin 9 → ℝ) j := by
          intro j
          fin_cases j <;> simp only [positions,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one]
          all_goals push_cast [show 5 ≤ d from by omega,show 4 ≤ d from by omega,show 3 ≤ d from by omega,show 2 ≤ d from by omega,show 1 ≤ d from by omega]
          all_goals norm_num
        fin_cases r

        · have h := ray_00_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_01_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_02_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_03_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_04_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_05_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_06_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_07_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_08_nonnegative (d : ℝ) (i : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_09_nonnegative (d : ℝ) (i : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_10_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_11_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_12_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_13_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_14_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_15_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_16_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_17_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_18_nonnegative (d : ℝ) (i : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_19_nonnegative (d : ℝ) (i : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_20_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_21_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_22_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_23_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_24_nonnegative (d : ℝ) (i : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_25_nonnegative (d : ℝ) (i : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_26_nonnegative (d : ℝ) (i : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_27_nonnegative (d : ℝ) (i : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_28_nonnegative (d : ℝ) (i : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_29_nonnegative (d : ℝ) (i : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_30_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_31_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]
        · have h := ray_32_nonnegative (d : ℝ) hdR
          simp [rays,Fin.sum_univ_succ,hcast,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,min_def,-Fin.val_fin_le]
          norm_num
          nlinarith [h]

    have sum_mem_of_closed {I E : Type} [AddCommMonoid E]
        (Good : E → Prop) (hzero : Good 0) (hadd : ∀ u v, Good u → Good v → Good (u+v))
        (s : Finset I) (f : I → E) (hf : ∀ i ∈ s, Good (f i)) : Good (∑ i ∈ s, f i) := by
      classical
      induction s using Finset.induction_on with
      | empty => simpa using hzero
      | @insert i s hi ih =>
        rw [sum_insert hi]
        exact hadd _ _ (hf i (mem_insert_self _ _)) (ih (fun j hj => hf j (mem_insert_of_mem hj)))

    have mixture_transfer {I E : Type} [AddCommGroup E] [Module ℝ E]
        (Good : E → Prop) (hzero : Good 0)
        (hadd : ∀ u v, Good u → Good v → Good (u+v))
        (hsmul : ∀ (t : ℝ) u, 0≤t → Good u → Good (t • u))
        (s : Finset I) (hs : s.Nonempty) (x : I → ℝ) (v : I → E) (b : E)
        (hx : ∀ i ∈ s,0≤x i) (hb : ∀ i ∈ s, Good (b+(∑ j ∈ s,x j) • v i)) :
        Good (b+∑ i ∈ s,x i • v i) := by
      classical
      let m := ∑ j ∈ s,x j
      have hm : 0 ≤ m := sum_nonneg hx
      by_cases hz : m=0
      · obtain ⟨i,hi⟩ := hs
        have hxi : ∀ i ∈ s,x i=0 := (sum_eq_zero_iff_of_nonneg hx).mp hz
        have he : (∑ i ∈ s,x i • v i)=0 := sum_eq_zero (fun i hi => by rw [hxi i hi,zero_smul])
        have h := hb i hi
        change Good (b+m • v i) at h
        simpa only [he,hz,zero_smul,add_zero] using h
      · have hmp : 0 < m := lt_of_le_of_ne hm (Ne.symm hz)
        have hmem : Good (∑ i ∈ s,(x i/m) • (b+m • v i)) := by
          apply sum_mem_of_closed Good hzero hadd s
          intro i hi
          exact hsmul _ _ (div_nonneg (hx i hi) hm) (hb i hi)
        have he : (∑ i ∈ s,(x i/m) • (b+m • v i)) = b+∑ i ∈ s,x i • v i := by
          simp only [smul_add,smul_smul,sum_add_distrib]
          rw [← sum_smul,← sum_div]
          change (m/m) • b + (∑ i ∈ s,(x i/m*m) • v i) = b+∑ i ∈ s,x i • v i
          simp only [div_self hz,one_smul,div_mul_cancel₀ _ hz]
        rwa [he] at hmem

    have compressed_good (d i : ℕ) (hd : 33 ≤ d) (hi : 3 ≤ i) (hi' : i ≤ d-6)
        (y : Fin 9 → ℝ) (hy : ∀ j,0 ≤ y j)
        (hL : 0 ≤ ∑ j,y j*firstRow j) (hC : 0 ≤ ∑ j,y j*secondRow j) :
        spectralGood (Real.sqrt (9/(8*(d : ℝ)))) (synth (d := d) (positions d i) y) := by
      apply finite_cone_transfer (fun y => spectralGood (Real.sqrt (9/(8*(d : ℝ)))) (synth (d := d) (positions d i) y))
        ?_ ?_ ?_ (ray_spectral_good d i hd hi hi') y hy hL hC
      · simpa only [map_zero] using spectralGood_zero d (Real.sqrt (9/(8*(d : ℝ))))
      · intro u v hu hv
        rw [map_add]
        exact spectralGood_add _ _ _ hu hv
      · intro t u ht hu
        rw [map_smul]
        exact spectralGood_smul _ _ _ ht hu

    have synth_split {d : ℕ} (l : Fin d → ℝ) (i : ℕ) :
        synth (positions d i) (compressed l) = base l + compressed l 2 • step d i := by
      ext k
      simp [synth,positions,compressed,base,Fin.sum_univ_succ]
      ring
    have hL : extend l 0 + extend l 1 + extend l 2 ≤
        extend l (d-6) + extend l (d-5) + extend l (d-4) +
        extend l (d-3) + extend l (d-2) + extend l (d-1) := by
      simpa only [extend, dif_pos (show 0<d by omega), dif_pos (show 1<d by omega),
        dif_pos (show 2<d by omega), dif_pos (show d-6<d by omega),
        dif_pos (show d-5<d by omega), dif_pos (show d-4<d by omega),
        dif_pos (show d-3<d by omega), dif_pos (show d-2<d by omega),
        dif_pos (show d-1<d by omega)] using hL
    have hC : extend l 0 ≤ extend l (d-3) + extend l (d-2) + extend l (d-1) := by
      simpa only [extend, dif_pos (show 0<d by omega), dif_pos (show d-3<d by omega),
        dif_pos (show d-2<d by omega), dif_pos (show d-1<d by omega)] using hC

    have hy := compressed_nonnegative l hd ho hn
    have hL' : 0 ≤ ∑ j,compressed l j*firstRow j := by
      simp [compressed,firstRow,Fin.sum_univ_succ]
      linarith
    have hC' : 0 ≤ ∑ j,compressed l j*secondRow j := by
      simp [compressed,secondRow,Fin.sum_univ_succ]
      linarith
    let c := Real.sqrt (9/(8*(d : ℝ)))
    have hg : spectralGood c l := by
      have hm : spectralGood c (base l + ∑ j ∈ Ico 2 (d-6), (extend l j-extend l (j+1)) • step d (j+1)) := by
        apply mixture_transfer (spectralGood c) (spectralGood_zero d c)
          (fun x y hx hy => spectralGood_add c x y hx hy)
          (fun t x ht hx => spectralGood_smul c t x ht hx)
          (Ico 2 (d-6)) (by exact ⟨2,by simp only [mem_Ico];omega⟩)
          (fun j => extend l j-extend l (j+1)) (fun j => step d (j+1)) (base l)
        · intro j hj
          have hjd : j < d := by simp only [mem_Ico] at hj;omega
          exact spectralGap_nonneg l ho hn ⟨j,hjd⟩
        · intro j hj
          have hj0 : 3 ≤ j+1 := by simp only [mem_Ico] at hj;omega
          have hj1 : j+1 ≤ d-6 := by simp only [mem_Ico] at hj;omega
          rw [middle_mass l hd,← synth_split l (j+1)]
          exact compressed_good d (j+1) hd hj0 hj1 (compressed l) hy hL' hC'
      rwa [← spectrum_split l hd] at hm
    have hb := spectralGood_square c l (Real.sqrt_nonneg _) (by rw [ht];norm_num) hg
    dsimp only [c] at hb
    rw [ht,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 9/(8*(d : ℝ)))] at hb
    simpa using hb

  let d := 3*(3+k)
  have hd : 33 ≤ d := by dsimp [d]; omega
  have hzero : (0 : Fin (3*(3+k))) = ⟨0, by omega⟩ := by apply Fin.ext; simp
  have hL : l ⟨0, by omega⟩ + l ⟨1, by omega⟩ + l ⟨2, by omega⟩ ≤
      l ⟨d-6, by omega⟩ + l ⟨d-5, by omega⟩ + l ⟨d-4, by omega⟩ +
      l ⟨d-3, by omega⟩ + l ⟨d-2, by omega⟩ + l ⟨d-1, by omega⟩ := by
    have h := h1.dotProduct_mulVec_nonneg (![1,1,1] : Fin 3 → ℝ)
    norm_num [K1, boundaryValues, dotProduct, mulVec, Fin.sum_univ_succ] at h
    rw [hzero] at h
    have he6 : d-6=3*k+3 := by dsimp [d]; omega
    have he5 : d-5=3*k+4 := by dsimp [d]; omega
    have he4 : d-4=3*k+5 := by dsimp [d]; omega
    have he3 : d-3=3*k+6 := by dsimp [d]; omega
    have he2 : d-2=3*k+7 := by dsimp [d]; omega
    have he1 : d-1=3*k+8 := by dsimp [d]; omega
    simp only [he6,he5,he4,he3,he2,he1]
    linarith
  have hC : l ⟨0, by omega⟩ ≤
      l ⟨d-3, by omega⟩ + l ⟨d-2, by omega⟩ + l ⟨d-1, by omega⟩ := by
    have h := h1.dotProduct_mulVec_nonneg (![1,1,0] : Fin 3 → ℝ)
    norm_num [K1, boundaryValues, dotProduct, mulVec, Fin.sum_univ_succ] at h
    rw [hzero] at h
    have he3 : d-3=3*k+6 := by dsimp [d]; omega
    have he2 : d-2=3*k+7 := by dsimp [d]; omega
    have he1 : d-1=3*k+8 := by dsimp [d]; omega
    simp only [he3,he2,he1]
    linarith
  have h := uniform_scalar_bound d hd l ho hn ht hL hC
  convert h using 1 <;> dsimp [d] <;> push_cast <;> field_simp <;> ring

#print axioms uniform_spectral_bound
end D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSpectralBound
