/- GID: D5/S3/Combinatorics/Hankel/SunA006077Result
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hankel/SunA006077Result
   mirror-E: none(waiver:all-index-symbolic-determinant)
   anchors: []
   utility: none
   digest: The complete signed integral oddness assertion for Sun's Hankel determinants. -/

import D5.S3.Combinatorics.Hankel.SunA006077Arithmetic
import D5.S3.Combinatorics.Hankel.SunA006077Positivity

/-! Positivity and exact integral normalization complete all three residue classes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Hankel.SunA006077

/-- The exact all-index assertion in Sun's Conjecture 3.16. -/
def claim : Prop := ∀ n : ℕ,
  (n % 3 = 1 → W n = 0) ∧
  (n % 3 ≠ 1 → ∃ z : ℤ, 0 < z ∧ Odd z ∧
    (-1 : ℤ)^((n+1)/3) * W n = 6^n * z)


private theorem quotients_positive (m : ℕ) : 0 < d m ∧ 0 < e m := by
  have hd : d m ≠ 0 := by
    intro h
    have ho := (normalized_odd m).1
    rw [h] at ho
    norm_num at ho
  have he : e m ≠ 0 := by
    intro h
    have ho := (normalized_odd m).2
    rw [h] at ho
    norm_num at ho
  have hD : D (m+1) ≠ 0 := by rw [D_normalization]; exact mul_ne_zero (by positivity) hd
  have hE : E m ≠ 0 := by rw [E_normalization]; exact mul_ne_zero (by positivity) he
  have castD : (Matrix.of fun i j : Fin (m+1) => (c (i.val+j.val+0) : ℝ)).det =
      (D (m+1) : ℝ) := by
        simp only [D,Int.cast_det,Nat.add_zero]
        congr 1
  have castE : (Matrix.of fun i j : Fin m => (c (i.val+j.val+1) : ℝ)).det =
      (E m : ℝ) := by
        simp only [E,Int.cast_det]
        congr 1
  have hDr : (0 : ℝ) < (D (m+1) : ℝ) := by
    rw [← castD]
    exact ((multinomial_posSemidef 0 (m+1)).posDef_iff_det_ne_zero.mpr
      (by rw [castD]; exact_mod_cast hD)).det_pos
  have hEr : (0 : ℝ) < (E m : ℝ) := by
    rw [← castE]
    exact ((multinomial_posSemidef 1 m).posDef_iff_det_ne_zero.mpr
      (by rw [castE]; exact_mod_cast hE)).det_pos
  have hDp : (0 : ℤ) < D (m+1) := by exact_mod_cast hDr
  have hEp : (0 : ℤ) < E m := by exact_mod_cast hEr
  rw [D_normalization] at hDp
  rw [E_normalization] at hEp
  constructor
  · exact (mul_pos_iff_of_pos_left (by positivity : (0 : ℤ) < 6^m)).mp hDp
  · exact (mul_pos_iff_of_pos_left (by positivity : (0 : ℤ) < 6^m)).mp hEp

private theorem normalized_zero (m : ℕ) :
    (-1 : ℤ)^m*W (3*m)=6^(3*m)*(d m*(e m)^2) := by
  rw [block_zero,D_normalization,E_normalization]
  have hs : (-1 : ℤ)^m*(-1)^m=1 := by rw [← mul_pow]; norm_num
  have hp : (6 : ℤ)^(3*m)=6^m*(6^m)^2 := by
    rw [← pow_mul,← pow_add]
    congr 1
    omega
  rw [hp]
  calc
    _ = ((-1 : ℤ)^m*(-1)^m)*(6^m*(6^m)^2)*(d m*(e m)^2) := by ring
    _ = _ := by rw [hs,one_mul]

private theorem normalized_two (m : ℕ) :
    (-1 : ℤ)^(m+1)*W (3*m+2)=6^(3*m+2)*(d m*(e (m+1))^2) := by
  rw [block_two,D_normalization,E_normalization]
  have hs : (-1 : ℤ)^(m+1)*(-1)^(m+1)=1 := by rw [← mul_pow]; norm_num
  have hp : (6 : ℤ)^(3*m+2)=6^m*(6^(m+1))^2 := by
    rw [← pow_mul,← pow_add]
    congr 1
    omega
  rw [hp]
  calc
    _ = ((-1 : ℤ)^(m+1)*(-1)^(m+1))*(6^m*(6^(m+1))^2)*(d m*(e (m+1))^2) := by ring
    _ = _ := by rw [hs,one_mul]

/-- Sun's complete Conjecture 3.16 for the literal integer finite sum, at every natural index. -/
theorem result : claim := by
  intro n
  have hn := Nat.mod_lt n (by omega : 0 < 3)
  have hdiv := Nat.mod_add_div n 3
  constructor
  · intro h
    have heq : n=3*(n/3)+1 := by omega
    rw [heq]
    exact zero_branch _
  · intro h
    have hcases : n%3=0 ∨ n%3=2 := by omega
    rcases hcases with hz | hz
    · have heq : n=3*(n/3) := by omega
      let m := n/3
      have hexp : (n+1)/3=m := by dsimp [m]; omega
      refine ⟨d m*(e m)^2,mul_pos (quotients_positive m).1
        (sq_pos_of_pos (quotients_positive m).2),
        (normalized_odd m).1.mul ((normalized_odd m).2.pow),?_⟩
      rw [hexp,show n=3*m from heq]
      exact normalized_zero m
    · have heq : n=3*(n/3)+2 := by omega
      let m := n/3
      have hexp : (n+1)/3=m+1 := by dsimp [m]; omega
      refine ⟨d m*(e (m+1))^2,mul_pos (quotients_positive m).1
        (sq_pos_of_pos (quotients_positive (m+1)).2),
        (normalized_odd m).1.mul ((normalized_odd (m+1)).2.pow),?_⟩
      rw [hexp,show n=3*m+2 from heq]
      exact normalized_two m

end D5.S3.Combinatorics.Hankel.SunA006077
