/- GID: D5/S3/Combinatorics/Hankel/SunA006077Positivity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hankel/SunA006077Positivity
   mirror-E: none(waiver:beta-moment-positive-semidefiniteness)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: none
   digest: Shifted beta moment matrices and their Schur product realize the multinomial moments. -/

import D5.S3.Combinatorics.Hankel.SunA006077
import D5.S3.Analytic.KummerRatio.BetaIntegral
import Mathlib.Analysis.Matrix.Order

/-! Beta moments at shapes one third and two thirds give positive semidefinite Hankel matrices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Hankel.SunA006077

open Matrix Finset Set MeasureTheory
open D5.S3.Analytic.KummerRatio.BetaIntegral

private def mu (a : ℝ) (n : ℕ) : ℝ := (ascPochhammer ℝ n).eval a / (n.factorial : ℝ)

private theorem mu_succ (a : ℝ) (n : ℕ) :
    mu a (n+1)=mu a n*(a+n)/(n+1) := by
  unfold mu
  rw [ascPochhammer_succ_eval,Nat.factorial_succ]
  push_cast
  field_simp

private theorem c_factorial (n : ℕ) :
    (c n : ℝ)*(n.factorial : ℝ)^3=((3*n).factorial : ℝ) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (by omega : n ≤ 2*n)
  have h2 := Nat.choose_mul_factorial_mul_factorial (by omega : n ≤ 3*n)
  rw [show 2*n-n=n by omega] at h1
  rw [show 3*n-n=2*n by omega] at h2
  have hr1 : ((2*n).choose n : ℝ)*(n.factorial : ℝ)*(n.factorial : ℝ)=
      ((2*n).factorial : ℝ) := by exact_mod_cast h1
  have hr2 : ((3*n).choose n : ℝ)*(n.factorial : ℝ)*((2*n).factorial : ℝ)=
      ((3*n).factorial : ℝ) := by exact_mod_cast h2
  calc
    _ = ((3*n).choose n : ℝ)*(n.factorial : ℝ)*
      (((2*n).choose n : ℝ)*(n.factorial : ℝ)*(n.factorial : ℝ)) := by
        simp only [c,Int.cast_mul,Int.cast_natCast]
        ring
    _ = _ := by rw [hr1,hr2]

private theorem c_recurrence (n : ℕ) :
    ((n : ℝ)+1)^2*(c (n+1) : ℝ)=3*(3*n+1)*(3*n+2)*(c n : ℝ) := by
  have cf (k : ℕ) : (c k : ℝ)=((3*k).factorial : ℝ)/(k.factorial : ℝ)^3 :=
    (eq_div_iff (by positivity)).mpr (c_factorial k)
  have fac : ((3*(n+1)).factorial : ℝ)=
      (3*(n : ℝ)+3)*(3*n+2)*(3*n+1)*((3*n).factorial : ℝ) := by
    rw [show 3*(n+1)=(3*n+2)+1 by omega,Nat.factorial_succ,
      show 3*n+2=(3*n+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
    push_cast
    ring
  rw [cf (n+1),cf n,fac,Nat.factorial_succ]
  push_cast
  field_simp

private theorem c_moments (n : ℕ) :
    (c n : ℝ)=27^n*mu (1/3) n*mu (2/3) n := by
  induction n with
  | zero => norm_num [c,mu]
  | succ n ih =>
    have h := c_recurrence n
    have hn : (n : ℝ)+1 ≠ 0 := by positivity
    rw [mu_succ,mu_succ,pow_succ]
    calc
      (c (n+1) : ℝ) = 3*(3*(n : ℝ)+1)*(3*n+2)*(c n : ℝ)/((n : ℝ)+1)^2 := by
        apply (eq_div_iff (pow_ne_zero 2 hn)).mpr
        simpa [mul_comm] using h
      _ = _ := by rw [ih]; field_simp; ring

private theorem beta_hankel_psd (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (s N : ℕ) :
    (Matrix.of fun i j : Fin N => mu a (i.val+j.val+s)).PosSemidef := by
  let B := Real.Gamma a*Real.Gamma (1-a)
  have hB : 0 < B := mul_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos (by linarith))
  have moments (r : ℕ) :
      (∫ t in (0 : ℝ)..1, t^(a+(r : ℝ)-1)*(1-t)^(-a))=B*mu a r := by
    have he : a+(r : ℝ)+(1-a)=(r : ℝ)+1 := by ring
    have h := integral_beta (p := a+(r : ℝ)) (q := 1-a) (by positivity) (by linarith)
    rw [show (1-a)-1=-a by ring,he,Real.Gamma_nat_eq_factorial,
      gamma_pochhammer ha] at h
    rw [h]
    dsimp [B,mu]
    ring
  have integrable (r : ℕ) :
      IntervalIntegrable (fun t : ℝ => t^(a+(r : ℝ)-1)*(1-t)^(-a)) volume 0 1 := by
    simpa only [show (1-a)-1=-a by ring] using
      intervalIntegrable_beta (p := a+(r : ℝ)) (q := 1-a) (by positivity) (by linarith)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp [Matrix.conjTranspose_apply,Nat.add_comm]
  · intro v
    let F : Fin N → Fin N → ℝ → ℝ := fun i j t =>
      (v i*v j)*(t^(a+((i.val+j.val+s : ℕ) : ℝ)-1)*(1-t)^(-a))
    have hint (i j : Fin N) : IntervalIntegrable (F i j) volume 0 1 :=
      (integrable (i.val+j.val+s)).const_mul (v i*v j)
    have hf : (∫ t in (0 : ℝ)..1, ∑ i : Fin N, ∑ j : Fin N, F i j t)=
        B*(star v ⬝ᵥ ((Matrix.of fun i j : Fin N => mu a (i.val+j.val+s))*ᵥv)) := by
      have hi := intervalIntegral.integral_finsetSum (μ := volume) (a := (0 : ℝ)) (b := 1)
        (s := univ) (fun i _ => IntervalIntegrable.sum univ (fun j _ => hint i j))
      simp only [Finset.sum_apply] at hi
      rw [hi]
      have hj (i : Fin N) := intervalIntegral.integral_finsetSum
        (μ := volume) (a := (0 : ℝ)) (b := 1) (s := univ) (fun j _ => hint i j)
      simp_rw [hj]
      simp only [F,intervalIntegral.integral_const_mul,moments,dotProduct,mulVec,
        Matrix.of_apply,Pi.star_apply,star_trivial]
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..1, ∑ i : Fin N, ∑ j : Fin N, F i j t := by
      have he : (∫ t in (0 : ℝ)..1, ∑ i : Fin N, ∑ j : Fin N, F i j t)=
          ∫ t in (0 : ℝ)..1, t^(a-1)*(1-t)^(-a)*t^s*
            (∑ i : Fin N, v i*t^i.val)^2 := by
        apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
        intro t ht
        dsimp only [F]
        rw [pow_two,sum_mul]
        simp only [mul_sum]
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        rw [show a+((i.val+j.val+s : ℕ) : ℝ)-1=
          (a-1)+(i.val : ℝ)+(j.val : ℝ)+(s : ℝ) by push_cast; ring]
        rw [Real.rpow_add ht.1,Real.rpow_add ht.1,Real.rpow_add ht.1]
        simp only [Real.rpow_natCast]
        ring
      rw [he]
      apply intervalIntegral.integral_nonneg zero_le_one
      intro t ht
      exact mul_nonneg (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _))
        (pow_nonneg ht.1 _)) (sq_nonneg _)
    rw [hf] at hnonneg
    nlinarith

/-- Every nonnegative shift of the multinomial moment matrix is positive semidefinite. -/
theorem multinomial_posSemidef (s N : ℕ) :
    (Matrix.of fun i j : Fin N => (c (i.val+j.val+s) : ℝ)).PosSemidef := by
  let U : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j => mu (1/3) (i.val+j.val+s)
  let V : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j => mu (2/3) (i.val+j.val+s)
  have hU : U.PosSemidef := beta_hankel_psd (1/3) (by norm_num) (by norm_num) s N
  have hV : V.PosSemidef := beta_hankel_psd (2/3) (by norm_num) (by norm_num) s N
  let L : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal (fun i => 27^i.val)
  have hp := ((hU.hadamard hV).conjTranspose_mul_mul_same L).smul
    (by positivity : (0 : ℝ) ≤ 27^s)
  have hL : L.conjTranspose = L := by
    ext i j
    by_cases h : i=j
    · subst j
      simp [L,Matrix.conjTranspose_apply,Matrix.diagonal_apply]
    · simp [L,Matrix.conjTranspose_apply,Matrix.diagonal_apply,h,Ne.symm h]
  rw [hL] at hp
  convert hp using 1
  ext i j
  simp only [Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,L,
    Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.hadamard_apply,U,V]
  rw [c_moments,pow_add,pow_add]
  ring

end D5.S3.Combinatorics.Hankel.SunA006077
