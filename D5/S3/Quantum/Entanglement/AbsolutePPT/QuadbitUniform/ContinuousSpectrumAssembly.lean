/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ContinuousSpectrumAssembly
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ContinuousSpectrumAssembly
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Continuous actual-K1 concentration and unconditional natural-rounded purity for every dimension at least 56. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ActualPSDMoment
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FieldSimp

/-! UNCOMPILED source composition of the terminal continuous assembly and
the paid nonflat transport. The terminal telescope has only the original
spectral hypotheses. No kernel or official acceptance is asserted. -/

set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators Matrix
open Finset Matrix
open UniformSpectralBound.SharedSpectral
noncomputable section

private def defectK (u v : ℝ) (h : Fin 5 → ℝ) (d : Fin 9 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![2*(u-d 8), -(v+h 0+d 7), -(v+h 1+d 5);
     -(v+h 0+d 7), 2*(u-d 6), -(v+h 2+d 4);
     -(v+h 1+d 5), -(v+h 2+d 4), 2*(u-d 3)]

private def spectrumK (N : ℕ) (hN : 56 ≤ N) :
    (Fin N → ℝ) →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ where
  toFun l := !![
    2*l ⟨N-1, by omega⟩, l ⟨N-2, by omega⟩-l ⟨0, by omega⟩,
      l ⟨N-4, by omega⟩-l ⟨1, by omega⟩;
    l ⟨N-2, by omega⟩-l ⟨0, by omega⟩, 2*l ⟨N-3, by omega⟩,
      l ⟨N-5, by omega⟩-l ⟨2, by omega⟩;
    l ⟨N-4, by omega⟩-l ⟨1, by omega⟩,
      l ⟨N-5, by omega⟩-l ⟨2, by omega⟩, 2*l ⟨N-6, by omega⟩]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' a x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem common_pos_56 (n : ℝ) (hn : 56 ≤ n) : 0 < commonEnvelope n := by
  unfold commonEnvelope
  exact div_pos (by linarith) (sq_pos_of_pos (by linarith))

private theorem common_target_56 (N : ℕ) (hN : 56 ≤ N) :
    commonEnvelope (N : ℝ) ≤ target N := by
  simpa only [target, bulkValue, bulkIndex] using common_le_integer_bulk N hN

private def threshold (n w : ℝ) : ℝ :=
  (1+w)*n-(2+w)^2/(4*commonEnvelope n)

private theorem threshold_formula (n w : ℝ) (hn : 56 ≤ n) :
    threshold n w = n*(4+4*w-15*w^2)/64-(2+w)^2/(4*(15*n-8)) := by
  have h0 : 15*n-8 ≠ 0 := by linarith
  have hden : 4*commonEnvelope n = (64*(15*n-8))/(15*n-4)^2 := by
    unfold commonEnvelope
    ring
  have h64 : (64 : ℝ) ≠ 0 := by norm_num
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  have h64den : 64*(15*n-8) ≠ 0 := mul_ne_zero h64 h0
  have h4den : 4*(15*n-8) ≠ 0 := mul_ne_zero h4 h0
  have hscale64 (a : ℝ) : a/64*(64*(15*n-8)) = a*(15*n-8) := by
    rw [← mul_assoc, div_mul_cancel₀ _ h64]
  have hscale4 (a : ℝ) : a/(4*(15*n-8))*(64*(15*n-8)) = 16*a := by
    rw [show 64*(15*n-8) = (4*(15*n-8))*16 by ring,
      ← mul_assoc, div_mul_cancel₀ _ h4den, mul_comm]
  unfold threshold
  rw [hden, div_div_eq_mul_div]
  apply mul_right_cancel₀ h64den
  rw [sub_mul, div_mul_cancel₀ _ h64den, sub_mul, hscale64, hscale4]
  ring

private theorem threshold_mono (n w : ℝ) (hn : 56 ≤ n)
    (hw : 1/4 ≤ w) (hw1 : w ≤ 1/2) : threshold 56 w ≤ threshold n w := by
  have hA : 0 ≤ 4+4*w-15*w^2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ w) (by linarith : 0 ≤ 1/2-w)]
  have hm := mul_le_mul_of_nonneg_right hn (div_nonneg hA (by norm_num : (0:ℝ) ≤ 64))
  have hf : (2+w)^2/(4*(15*n-8)) ≤ (2+w)^2/(4*(15*56-8)) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith)
  rw [threshold_formula 56 w (by norm_num), threshold_formula n w hn]
  nlinarith only [hm, hf]

private theorem rho_bounds :
    (7/16:ℝ) ≤ (5-Real.sqrt 17)/2 ∧ (5-Real.sqrt 17)/2 ≤ 4/9 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 17 by norm_num)
  have hn := Real.sqrt_nonneg (17:ℝ)
  have hu : Real.sqrt 17 ≤ 33/8 := by
    by_contra h
    have hp := mul_pos (by linarith : 0 < Real.sqrt 17-33/8)
      (by linarith : 0 < Real.sqrt 17+33/8)
    nlinarith only [hs, hp]
  have hl : (37/9:ℝ) ≤ Real.sqrt 17 := by
    by_contra h
    have hp := mul_pos (by linarith : 0 < 37/9-Real.sqrt 17)
      (by linarith : 0 < 37/9+Real.sqrt 17)
    nlinarith only [hs, hp]
  constructor <;> linarith

private theorem curve_threshold (n w : ℝ) (hn : 56 ≤ n)
    (hw : 1/4 ≤ w) (hw1 : w ≤ (5-Real.sqrt 17)/2) :
    4-2*w-4*w^2+w^3+w^4 ≤ threshold n w := by
  have hw4 : w ≤ 4/9 := hw1.trans rho_bounds.2
  let p : ℝ → ℝ := fun y => -1668+18300*y-30369*y^2-3328*y^3-3328*y^4
  have hleft : 0 ≤ p (1/4) := by norm_num [p]
  have hright : 0 ≤ p (4/9) := by norm_num [p]
  have hchord : 0 ≤ (4/9-w)*p (1/4)+(w-1/4)*p (4/9) :=
    add_nonneg (mul_nonneg (by linarith) hleft) (mul_nonneg (by linarith) hright)
  have hf : 0 ≤ (4/9-1/4)*(w-1/4)*(4/9-w)*
      (30369+3328*(w+1/4+4/9)+
        3328*(w^2+(1/4+4/9)*w+(1/4)^2+(1/4)*(4/9)+(4/9)^2)) := by
    have hw0 : 0 ≤ w := by linarith
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
    · positivity
  have hi : (4/9-1/4)*p w = (4/9-w)*p (1/4)+(w-1/4)*p (4/9)+
      (4/9-1/4)*(w-1/4)*(4/9-w)*
      (30369+3328*(w+1/4+4/9)+
        3328*(w^2+(1/4+4/9)*w+(1/4)^2+(1/4)*(4/9)+(4/9)^2)) := by
    dsimp [p]
    ring
  have hp : 0 ≤ p w := by nlinarith only [hi, hchord, hf]
  have hpoly : 3328*(threshold 56 w-(4-2*w-4*w^2+w^3+w^4)) = p w := by
    rw [threshold_formula 56 w (by norm_num)]
    dsimp [p]
    norm_num
    <;> ring
  have hb : 4-2*w-4*w^2+w^3+w^4 ≤ threshold 56 w := by
    nlinarith only [hp, hpoly]
  exact hb.trans (threshold_mono n w hn hw (by linarith))

private theorem total_threshold (n w : ℝ) (hn : 56 ≤ n)
    (hw : (5-Real.sqrt 17)/2 ≤ w) (hw1 : w ≤ 1/2) :
    (4-6*w)*(4-5*w) ≤ threshold n w := by
  have hw0 : 7/16 ≤ w := rho_bounds.1.trans hw
  have hp := quadratic_interval_nonneg
    (fun y : ℝ => -41604+158076*y-143521*y^2)
    (-143521) 158076 (-41604) (7/16) (1/2) w
    (by intro y; ring) (by norm_num) hw0 hw1 (by norm_num) (by norm_num)
  have hi : 3328*(threshold 56 w-(4-6*w)*(4-5*w)) =
      -41604+158076*w-143521*w^2 := by
    rw [threshold_formula 56 w (by norm_num)]
    norm_num
    <;> ring
  have hb : (4-6*w)*(4-5*w) ≤ threshold 56 w := by nlinarith only [hp, hi]
  exact hb.trans (threshold_mono n w hn (by linarith) hw1)

private theorem middle_quadratic (n j w : ℝ)
    (hn : 56 ≤ n) (hw : 1/4 ≤ w) (hw1 : w ≤ 1/2)
    (h : Fin 5 → ℝ) (d : Fin 9 → ℝ) (hd : DefectData 1 w h d)
    (hK : (defectK 1 w h d).PosSemidef) :
    (2+w)*(n+w*j+H h-D d)-(1+w)*n+E w h d ≤
      commonEnvelope n*(n+w*j+H h-D d)^2 := by
  have he := actual_psd_nonflat_middle_energy w h d hd.ho hd.hn hd.do_
    (fun i => ⟨hd.dn i, hd.du i⟩) (by simpa only [H, D, mul_one] using hd.row1)
    hw hw1 (by simpa only [defectK, one_mul] using hK)
  change E w h d ≤ (if w ≤ (5-Real.sqrt 17)/2 then
    4-2*w-4*w^2+w^3+w^4 else (4-6*w)*(4-5*w)) at he
  have henergy : E w h d ≤ threshold n w := by
    split_ifs at he with hrho
    · exact he.trans (curve_threshold n w hn hw hrho)
    · exact he.trans (total_threshold n w hn (by linarith) hw1)
  have hpos := common_pos_56 n hn
  have hdsc : (2+w)^2 ≤ 4*commonEnvelope n*((1+w)*n-E w h d) := by
    have hh : (2+w)^2/(4*commonEnvelope n) ≤ (1+w)*n-E w h d := by
      dsimp [threshold] at henergy
      linarith only [henergy]
    calc
      (2+w)^2 ≤ ((1+w)*n-E w h d)*(4*commonEnvelope n) :=
        (div_le_iff₀ (by positivity : 0 < 4*commonEnvelope n)).mp hh
      _ = 4*commonEnvelope n*((1+w)*n-E w h d) := mul_comm _ _
  have hb := square_completion (commonEnvelope n) (2+w) ((1+w)*n-E w h d)
    (n+w*j+H h-D d) hpos hdsc
  linarith only [hb]

private theorem synth_value (N j : ℕ) (x : Fin 16 → ℝ) (k : Fin N) :
    synth (positions N j) x k =
      ∑ q : Fin 16, x q * (if k.val < positions N j q then 1 else 0) := by
  change (∑ q : Fin 16, x q • step N (positions N j q)) k = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, step]

private theorem synth_head_value (N j : ℕ) (hN : 56 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (x : Fin 16 → ℝ) (i : Fin 5) :
    synth (d := N) (positions N j) x (⟨i.val, by omega⟩ : Fin N) =
      low x+x 5+head x i := by
  have hi := i.isLt
  have hm : i.val < j := by omega
  have ht (r : ℕ) (hr : r ≤ 9) : i.val < N-r := by omega
  rw [synth_value, positions_literal N j hN]
  simp only [Fin.sum_univ_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.reduceSucc,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    if_pos hm, if_pos (ht 9 (by omega)), if_pos (ht 8 (by omega)),
    if_pos (ht 7 (by omega)), if_pos (ht 6 (by omega)), if_pos (ht 5 (by omega)),
    if_pos (ht 4 (by omega)), if_pos (ht 3 (by omega)), if_pos (ht 2 (by omega)),
    if_pos (ht 1 (by omega)), if_pos (ht 0 (by omega)), mul_one]
  fin_cases i
  · norm_num [head, low]
    simp only [(show 0 < j by omega),
        (show 0 < N - 9 by omega),
        (show 0 < N - 8 by omega),
        (show 0 < N - 7 by omega),
        (show 0 < N - 6 by omega),
        (show 0 < N - 5 by omega),
        (show 0 < N - 4 by omega),
        (show 0 < N - 3 by omega),
        (show 0 < N - 2 by omega),
        (show 0 < N - 1 by omega),
        (show 0 < N by omega),
        (show 9 < N by omega),
        (show 8 < N by omega),
        (show 7 < N by omega),
        (show 6 < N by omega),
        (show 5 < N by omega),
        (show 4 < N by omega),
        (show 3 < N by omega),
        (show 2 < N by omega),
        (show 1 < N by omega),
      ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add] <;> ring
  · norm_num [head, low]
    simp only [(show 1 < j by omega),
        (show 1 < N - 9 by omega),
        (show 1 < N - 8 by omega),
        (show 1 < N - 7 by omega),
        (show 1 < N - 6 by omega),
        (show 1 < N - 5 by omega),
        (show 1 < N - 4 by omega),
        (show 1 < N - 3 by omega),
        (show 1 < N - 2 by omega),
        (show 1 < N - 1 by omega),
        (show 1 < N by omega),
      ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add] <;> ring
  · norm_num [head, low]
    simp only [(show 2 < j by omega),
        (show 2 < N - 9 by omega),
        (show 2 < N - 8 by omega),
        (show 2 < N - 7 by omega),
        (show 2 < N - 6 by omega),
        (show 2 < N - 5 by omega),
        (show 2 < N - 4 by omega),
        (show 2 < N - 3 by omega),
        (show 2 < N - 2 by omega),
        (show 2 < N - 1 by omega),
        (show 2 < N by omega),
      ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add] <;> ring
  · norm_num [head, low]
    simp only [(show 3 < j by omega),
        (show 3 < N - 9 by omega),
        (show 3 < N - 8 by omega),
        (show 3 < N - 7 by omega),
        (show 3 < N - 6 by omega),
        (show 3 < N - 5 by omega),
        (show 3 < N - 4 by omega),
        (show 3 < N - 3 by omega),
        (show 3 < N - 2 by omega),
        (show 3 < N - 1 by omega),
        (show 3 < N by omega),
      ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add] <;> ring
  · norm_num [head, low]
    simp only [(show 4 < j by omega),
        (show 4 < N - 9 by omega),
        (show 4 < N - 8 by omega),
        (show 4 < N - 7 by omega),
        (show 4 < N - 6 by omega),
        (show 4 < N - 5 by omega),
        (show 4 < N - 4 by omega),
        (show 4 < N - 3 by omega),
        (show 4 < N - 2 by omega),
        (show 4 < N - 1 by omega),
        (show 4 < N by omega),
      ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add] <;> ring

private theorem synth_tail_value (N j : ℕ) (hN : 56 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (x : Fin 16 → ℝ) (i : Fin 9) :
    synth (d := N) (positions N j) x (⟨N-(9-i.val), by omega⟩ : Fin N) =
      low x-tail x i := by
  have hi := i.isLt
  have hm : ¬ N-(9-i.val) < j := by omega
  have hh (r : ℕ) (hr : r ≤ 5) : ¬ N-(9-i.val) < r := by omega
  have ht (r : ℕ) (hr : r ≤ 9) :
      N-(9-i.val) < N-r ↔ i.val+r < 9 := by omega
  rw [synth_value, positions_literal N j hN]
  simp only [Fin.sum_univ_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.reduceSucc,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    if_neg hm, if_neg (hh 1 (by omega)), if_neg (hh 2 (by omega)),
    if_neg (hh 3 (by omega)), if_neg (hh 4 (by omega)), if_neg (hh 5 (by omega)),
    ht 9 (by omega), ht 8 (by omega), ht 7 (by omega), ht 6 (by omega),
    ht 5 (by omega), ht 4 (by omega), ht 3 (by omega), ht 2 (by omega),
    ht 1 (by omega), ht 0 (by omega), mul_zero, zero_add]
  fin_cases i
  · norm_num [tail, low]
    simp only [(show ¬ N - 9 < 1 by omega),
        (show ¬ N - 9 < 2 by omega),
        (show ¬ N - 9 < 3 by omega),
        (show ¬ N - 9 < 4 by omega),
        (show ¬ N - 9 < 5 by omega),
        (show ¬ N - 9 < j by omega),
        (show N - 9 ≠ 0 by omega),
        (show ¬ N ≤ 10 by omega),
        (show 0 < N by omega),
      ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add] <;> ring
  · norm_num [tail, low]
    simp only [(show ¬ N - 8 < 1 by omega),
        (show ¬ N - 8 < 2 by omega),
        (show ¬ N - 8 < 3 by omega),
        (show ¬ N - 8 < 4 by omega),
        (show ¬ N - 8 < 5 by omega),
        (show ¬ N - 8 < j by omega),
        (show N - 8 ≠ 0 by omega),
        (show ¬ N ≤ 9 by omega),
        (show 0 < N by omega),
      ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add] <;> ring
  · norm_num [tail, low]
    simp only [(show ¬ N - 7 < 1 by omega),
        (show ¬ N - 7 < 2 by omega),
        (show ¬ N - 7 < 3 by omega),
        (show ¬ N - 7 < 4 by omega),
        (show ¬ N - 7 < 5 by omega),
        (show ¬ N - 7 < j by omega),
        (show N - 7 ≠ 0 by omega),
        (show ¬ N ≤ 8 by omega),
        (show 0 < N by omega),
      ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add] <;> ring
  · norm_num [tail, low]
    simp only [(show ¬ N - 6 < 1 by omega),
        (show ¬ N - 6 < 2 by omega),
        (show ¬ N - 6 < 3 by omega),
        (show ¬ N - 6 < 4 by omega),
        (show ¬ N - 6 < 5 by omega),
        (show ¬ N - 6 < j by omega),
        (show N - 6 ≠ 0 by omega),
        (show ¬ N ≤ 7 by omega),
        (show 0 < N by omega),
      ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add] <;> ring
  · norm_num [tail, low]
    simp only [(show ¬ N - 5 < 1 by omega),
        (show ¬ N - 5 < 2 by omega),
        (show ¬ N - 5 < 3 by omega),
        (show ¬ N - 5 < 4 by omega),
        (show ¬ N - 5 < 5 by omega),
        (show ¬ N - 5 < j by omega),
        (show N - 5 ≠ 0 by omega),
        (show ¬ N ≤ 6 by omega),
        (show 0 < N by omega),
      ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add] <;> ring
  · norm_num [tail, low]
    simp only [(show ¬ N - 4 < 1 by omega),
        (show ¬ N - 4 < 2 by omega),
        (show ¬ N - 4 < 3 by omega),
        (show ¬ N - 4 < 4 by omega),
        (show ¬ N - 4 < 5 by omega),
        (show ¬ N - 4 < j by omega),
        (show N - 4 ≠ 0 by omega),
        (show ¬ N ≤ 5 by omega),
        (show 0 < N by omega),
      ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add] <;> ring
  · norm_num [tail, low]
    simp only [(show ¬ N - 3 < 1 by omega),
        (show ¬ N - 3 < 2 by omega),
        (show ¬ N - 3 < 3 by omega),
        (show ¬ N - 3 < 4 by omega),
        (show ¬ N - 3 < 5 by omega),
        (show ¬ N - 3 < j by omega),
        (show N - 3 ≠ 0 by omega),
        (show ¬ N ≤ 4 by omega),
        (show 0 < N by omega),
      ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add] <;> ring
  · norm_num [tail, low]
    simp only [(show ¬ N - 2 < 1 by omega),
        (show ¬ N - 2 < 2 by omega),
        (show ¬ N - 2 < 3 by omega),
        (show ¬ N - 2 < 4 by omega),
        (show ¬ N - 2 < 5 by omega),
        (show ¬ N - 2 < j by omega),
        (show N - 2 ≠ 0 by omega),
        (show ¬ N ≤ 3 by omega),
        (show 0 < N by omega),
      ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add] <;> ring
  · norm_num [tail, low]
    simp only [(show ¬ N - 1 < 1 by omega),
        (show ¬ N - 1 < 2 by omega),
        (show ¬ N - 1 < 3 by omega),
        (show ¬ N - 1 < 4 by omega),
        (show ¬ N - 1 < 5 by omega),
        (show ¬ N - 1 < j by omega),
        (show N - 1 ≠ 0 by omega),
        (show ¬ N ≤ 2 by omega),
        (show 0 < N by omega),
      ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add] <;> ring

private theorem spectrumK_synth (N j : ℕ) (hN : 56 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (x : Fin 16 → ℝ) :
    spectrumK N hN (synth (positions N j) x) = defectK (low x) (x 5) (head x) (tail x) := by
  have hh0 : synth (d := N) (positions N j) x ⟨0, by omega⟩ =
      low x+x 5+head x 0 :=
    synth_head_value N j hN hj hj' x (0 : Fin 5)
  have hh1 : synth (d := N) (positions N j) x ⟨1, by omega⟩ =
      low x+x 5+head x 1 :=
    synth_head_value N j hN hj hj' x (1 : Fin 5)
  have hh2 : synth (d := N) (positions N j) x ⟨2, by omega⟩ =
      low x+x 5+head x 2 :=
    synth_head_value N j hN hj hj' x (2 : Fin 5)
  have ht8 : synth (d := N) (positions N j) x ⟨N-1, by omega⟩ =
      low x-tail x 8 :=
    synth_tail_value N j hN hj hj' x (8 : Fin 9)
  have ht7 : synth (d := N) (positions N j) x ⟨N-2, by omega⟩ =
      low x-tail x 7 :=
    synth_tail_value N j hN hj hj' x (7 : Fin 9)
  have ht6 : synth (d := N) (positions N j) x ⟨N-3, by omega⟩ =
      low x-tail x 6 :=
    synth_tail_value N j hN hj hj' x (6 : Fin 9)
  have ht5 : synth (d := N) (positions N j) x ⟨N-4, by omega⟩ =
      low x-tail x 5 :=
    synth_tail_value N j hN hj hj' x (5 : Fin 9)
  have ht4 : synth (d := N) (positions N j) x ⟨N-5, by omega⟩ =
      low x-tail x 4 :=
    synth_tail_value N j hN hj hj' x (4 : Fin 9)
  have ht3 : synth (d := N) (positions N j) x ⟨N-6, by omega⟩ =
      low x-tail x 3 :=
    synth_tail_value N j hN hj hj' x (3 : Fin 9)
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [spectrumK, LinearMap.coe_mk, AddHom.coe_mk, defectK,
      Matrix.of_apply, Matrix.cons_val, Fin.reduceFinMk, Fin.reduceSucc] <;>
    simp only [hh0, hh1, hh2, ht8, ht7, ht6, ht5, ht4, ht3] <;> ring

private theorem normalized_small_good (N j : ℕ) (hN : 56 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (x : Fin 16 → ℝ)
    (hx : ∀ q, 0 ≤ x q) (hAx : ∀ r, 0 ≤ (A *ᵥ x) r)
    (hu : low x = 1) (hv : x 5 ≤ 1/2)
    (hK : (spectrumK N hN (synth (positions N j) x)).PosSemidef) :
    spectralGood (Real.sqrt (target N)) (synth (d := N) (positions N j) x) := by
  have hd : DefectData 1 (x 5) (head x) (tail x) := by
    simpa only [hu] using actual_defects x hx hAx
  rw [spectrumK_synth N j hN hj hj', hu] at hK
  have hb : (2+x 5)*((N:ℝ)+x 5*(j:ℝ)+H (head x)-D (tail x))-
      (1+x 5)*(N:ℝ)+E (x 5) (head x) (tail x) ≤
      target N*((N:ℝ)+x 5*(j:ℝ)+H (head x)-D (tail x))^2 := by
    by_cases hw : x 5 ≤ 1/4
    · have hs := actual_psd_small_jump_defect_bound N hN (j:ℝ) (x 5)
        (by exact_mod_cast hj) (hx 5) hw (head x) (tail x) hd.ho hd.hn hd.do_
        (fun i => ⟨hd.dn i, hd.du i⟩) (by simpa only [H, D, mul_one] using hd.row1)
        (by simpa only [defectK, one_mul] using hK)
      simpa only [E, H, D, H2, D2, add_assoc] using hs
    · exact (middle_quadratic (N:ℝ) (j:ℝ) (x 5) (by exact_mod_cast hN)
        (by linarith) hv (head x) (tail x) hd hK).trans
        (mul_le_mul_of_nonneg_right (common_target_56 N hN)
          (sq_nonneg ((N:ℝ)+x 5*(j:ℝ)+H (head x)-D (tail x))))
  have hm := actual_mass N j hN hj hj' x
  have hq := actual_square N j hN hj hj' x
  simp only [hu, one_mul, mul_one] at hm hq
  apply spectralGood_of_square _ _ (Real.sqrt_nonneg _)
  · exact sum_nonneg (fun k _ => synth_nonneg N j x hx k)
  · rw [Real.sq_sqrt (target_nonneg N), hm, hq]
    exact hb

private theorem actual_small_good (N j : ℕ) (hN : 56 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (x : Fin 16 → ℝ)
    (hx : ∀ q, 0 ≤ x q) (hAx : ∀ r, 0 ≤ (A *ᵥ x) r)
    (hv : 2*x 5 ≤ low x)
    (hK : (spectrumK N hN (synth (positions N j) x)).PosSemidef) :
    spectralGood (Real.sqrt (target N)) (synth (d := N) (positions N j) x) := by
  have hu0 := low_nonneg x hx
  by_cases hu : low x = 0
  · rw [zero_low x hx hAx hu, map_zero]
    exact spectralGood_zero N _
  · let z : Fin 16 → ℝ := (low x)⁻¹ • x
    have hi : 0 ≤ (low x)⁻¹ := inv_nonneg.mpr hu0
    have hz : ∀ q, 0 ≤ z q := fun q => mul_nonneg hi (hx q)
    have hAz : ∀ r, 0 ≤ (A *ᵥ z) r := by
      intro r
      dsimp [z]
      rw [Matrix.mulVec_smul]
      exact mul_nonneg hi (hAx r)
    have huz : low z = 1 := by
      dsimp [z]
      rw [low_smul, inv_mul_cancel₀ hu]
    have hvz : z 5 ≤ 1/2 := by
      have hh := mul_le_mul_of_nonneg_left hv hi
      rw [inv_mul_cancel₀ hu] at hh
      change (low x)⁻¹*x 5 ≤ 1/2
      nlinarith only [hh]
    have hKz : (spectrumK N hN (synth (positions N j) z)).PosSemidef := by
      dsimp [z]
      rw [map_smul, map_smul]
      exact hK.smul hi
    have hg := normalized_small_good N j hN hj hj' z hz hAz huz hvz hKz
    have hr : (low x) • z = x := by
      ext q
      dsimp [z]
      simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
    rw [← hr, map_smul]
    exact spectralGood_smul _ _ _ hu0 hg

private theorem half_jump_good (N j : ℕ) (hN : 56 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10)
    (x : Fin 16 → ℝ) (hx : ∀ q, 0 ≤ x q) (hAx : ∀ r, 0 ≤ (A *ᵥ x) r)
    (hv : 2*x 5 = low x) :
    spectralGood (Real.sqrt (target N)) (synth (d := N) (positions N j) x) := by
  let u := low x
  have hd := actual_defects x hx hAx
  have he := total_energy_estimate hd (hx 5)
  have hv' : x 5 = u/2 := by dsimp [u]; linarith only [hv]
  have he' : E (x 5) (head x) (tail x) ≤ (3/2)*u^2 := by
    change E (x 5) (head x) (tail x) ≤ (4*u-6*x 5)*(4*u-5*x 5) at he
    calc
      E (x 5) (head x) (tail x) ≤ (4*u-6*x 5)*(4*u-5*x 5) := he
      _ = (3/2)*u^2 := by rw [hv']; ring
  have hn : (56:ℝ) ≤ N := by exact_mod_cast hN
  have hhalf := middle_envelope₁_le_common (N:ℝ) hn
  have hh : 25 ≤ commonEnvelope (N:ℝ)*(24*((N:ℝ)-1)) := by
    apply (div_le_iff₀ (by linarith : 0 < 24*((N:ℝ)-1))).mp
    simpa only [middleEnvelope₁] using hhalf
  have hmul := mul_le_mul_of_nonneg_right hh (sq_nonneg u)
  have hdisc : ((5/2)*u)^2 ≤
      4*commonEnvelope (N:ℝ)*((3/2)*u^2*((N:ℝ)-1)) := by nlinarith only [hmul]
  let S := u*(N:ℝ)+x 5*(j:ℝ)+H (head x)-D (tail x)
  have hb := square_completion (commonEnvelope (N:ℝ)) ((5/2)*u)
    ((3/2)*u^2*((N:ℝ)-1)) S (common_pos_56 _ hn) hdisc
  have hm := actual_mass N j hN hj hj' x
  have hq := actual_square N j hN hj hj' x
  have hbound : (∑ k : Fin N, (synth (positions N j) x k)^2) ≤ commonEnvelope (N:ℝ)*S^2 := by
    rw [hq]
    change (2*u+x 5)*S-u*(u+x 5)*(N:ℝ)+E (x 5) (head x) (tail x) ≤ _
    calc
      (2*u+x 5)*S-u*(u+x 5)*(N:ℝ)+E (x 5) (head x) (tail x) ≤
          (2*u+x 5)*S-u*(u+x 5)*(N:ℝ)+(3/2)*u^2 := add_le_add le_rfl he'
      _ = (5/2)*u*S-(3/2)*u^2*((N:ℝ)-1) := by rw [hv']; ring
      _ ≤ commonEnvelope (N:ℝ)*S^2 := hb
  have hmono := mul_le_mul_of_nonneg_right (common_target_56 N hN) (sq_nonneg S)
  apply spectralGood_of_square _ _ (Real.sqrt_nonneg _)
  · exact sum_nonneg (fun k _ => synth_nonneg N j x hx k)
  · rw [Real.sq_sqrt (target_nonneg N), hm]
    exact hbound.trans hmono

private theorem actual_fixed_good (N j : ℕ) (hN : 56 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (x : Fin 16 → ℝ)
    (hx : ∀ q, 0 ≤ x q) (hAx : ∀ r, 0 ≤ (A *ᵥ x) r)
    (hK : (spectrumK N hN (synth (positions N j) x)).PosSemidef) :
    spectralGood (Real.sqrt (target N)) (synth (d := N) (positions N j) x) := by
  by_cases hv : 2*x 5 ≤ low x
  · exact actual_small_good N j hN hj hj' x hx hAx hv hK
  · let a := 2*x 5-low x
    let y := x-a • bulk
    have ha : 0 ≤ a := by dsimp [a]; linarith only [hv]
    have hd := actual_defects x hx hAx
    obtain ⟨hH, hD⟩ := defect_totals_nonneg hd
    obtain ⟨_, _, hsub0, hsub2, hlast⟩ := defect_subtotals hd
    have hr := hd.row1
    have hlastid := last_defect_identity x
    have hy : ∀ q, 0 ≤ y q := by
      intro q
      fin_cases q <;> simp only [y, a, bulk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val, Fin.reduceFinMk, Fin.reduceSucc] <;> norm_num <;>
        linarith [hx 0, hx 1, hx 2, hx 3, hx 4, hx 5, hx 6, hx 7,
          hx 8, hx 9, hx 10, hx 11, hx 12, hx 13, hx 14, hx 15]
    obtain ⟨hr0, hr1, hr2⟩ := actual_row_identities x
    obtain ⟨hy0, hy1, hy2⟩ := subtraction_rows a x
    have hAy : ∀ r, 0 ≤ (A *ᵥ y) r := by
      intro r
      fin_cases r
      · change 0 ≤ (A *ᵥ (x-a • bulk)) 0
        rw [hy0, hr0]
        dsimp [a]
        linarith only [hr, hH, hD, hsub0]
      · change 0 ≤ (A *ᵥ (x-a • bulk)) 1
        rw [hy1]
        exact hAx 1
      · change 0 ≤ (A *ᵥ (x-a • bulk)) 2
        rw [hy2, hr2]
        dsimp [a]
        linarith only [hr, hH, hD, hsub2]
    -- y is row-feasible only. Its low level is m=4u-6v and y5=m/2.
    -- No PSD assertion about y is used by half_jump_good.
    have hlow_y : low y = 4*low x-6*x 5 := by
      simp only [y, a, bulk, low, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val, Fin.reduceFinMk, Fin.reduceSucc]
      ring
    have hhalf : 2*y 5 = low y := by
      rw [hlow_y]
      simp only [y, a, bulk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val, Fin.reduceFinMk, Fin.reduceSucc]
      ring
    have hres := half_jump_good N j hN hj hj' y hy hAy hhalf
    have hbulk := bulk_good N j hN hj hj'
    have hrec : x = y+a • bulk := (sub_add_cancel x (a • bulk)).symm
    rw [hrec, map_add, map_smul]
    exact spectralGood_add _ _ _ hres (spectralGood_smul _ _ _ ha hbulk)

private def middleK : Matrix (Fin 3) (Fin 3) ℝ := !![0,-1,-1; -1,0,-1; -1,-1,0]

private theorem spectrumK_middle_step (N j : ℕ) (hN : 56 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) : spectrumK N hN (step N j) = middleK := by
  have hh0 : 0 < j := by omega
  have hh1 : 1 < j := by omega
  have hh2 : 2 < j := by omega
  have ht (r : ℕ) (hr : r ≤ 6) : ¬ N-r < j := by omega
  ext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [spectrumK, middleK, step, hh0, hh1, hh2,
      ht 1 (by omega), ht 2 (by omega), ht 3 (by omega),
      ht 4 (by omega), ht 5 (by omega), ht 6 (by omega)]

private theorem fixed_K (N : ℕ) (hN : 56 ≤ N) (g : Fin N → ℝ)
    (k : Fin N) (hk : k ∈ middle N) :
    spectrumK N hN (fullSynth N (fixedGaps g k)) = spectrumK N hN (fullSynth N g) := by
  let L := (spectrumK N hN).comp (fullSynth N)
  have hi (i : Fin N) (hi : i ∈ middle N) : L (unitGap i) = middleK := by
    change spectrumK N hN (fullSynth N (unitGap i)) = _
    rw [fullSynth_unit]
    exact spectrumK_middle_step N (i.val+1) hN
      (by have := (mem_middle i).mp hi; omega)
      (by have := (mem_middle i).mp hi; omega)
  have hs : middleMass g • middleK = ∑ i ∈ middle N, g i • L (unitGap i) := by
    rw [middleMass, sum_smul]
    exact sum_congr rfl (fun i hi' => by rw [hi i hi'])
  change L (fixedGaps g k) = L g
  calc
    _ = L (boundaryGaps g)+middleMass g • middleK := by
      rw [fixedGaps, map_add, map_smul, hi k hk]
    _ = L (boundaryGaps g+∑ i ∈ middle N, g i • unitGap i) := by
      rw [map_add, map_sum, hs]
      congr 1
      exact sum_congr rfl (fun i _ => (map_smul L _ _).symm)
    _ = L g := by rw [gaps_split g]

private theorem continuous_concentration_good (N : ℕ) (hN : 56 ≤ N)
    (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i)
    (hrows : ∀ r, 0 ≤ slackMap N hN l r) (hK : (spectrumK N hN l).PosSemidef) :
    spectralGood (Real.sqrt (target N)) l := by
  let g := spectralGap l
  have hg : ∀ i, 0 ≤ g i := spectralGap_nonneg l ho hn
  have hr : fullSynth N g = l := gap_reconstruct l
  have hs : (middle N).Nonempty := by
    refine ⟨⟨5, by omega⟩, ?_⟩
    rw [mem_middle]
    simp
    omega
  have hfixed (k : Fin N) (hk : k ∈ middle N) :
      spectralGood (Real.sqrt (target N)) (fullSynth N (fixedGaps g k)) := by
    have hj : 6 ≤ k.val+1 := by have := (mem_middle k).mp hk; omega
    have hj' : k.val+1 ≤ N-10 := by have := (mem_middle k).mp hk; omega
    have hKf : (spectrumK N hN (fullSynth N (fixedGaps g k))).PosSemidef := by
      rw [fixed_K N hN g k hk, hr]
      exact hK
    rw [← lift_packed N hN g k hk, synth_lift N (k.val+1) hN hj hj'] at hKf ⊢
    apply actual_fixed_good N (k.val+1) hN hj hj' (packed hN g)
      (packed_nonneg hN g hg) _ hKf
    intro r
    rw [packed_image N hN g k hk]
    change 0 ≤ slackMap N hN (fullSynth N g) r
    rw [hr]
    exact hrows r
  have hm := mixture_transfer (spectralGood (Real.sqrt (target N)))
    (spectralGood_zero N _) (fun x y hx hy => spectralGood_add _ x y hx hy)
    (fun t x ht hx => spectralGood_smul _ t x ht hx)
    (middle N) hs g (fun i => fullSynth N (unitGap i)) (fullSynth N (boundaryGaps g))
    (fun i _ => hg i) (by
      intro k hk
      have hh := hfixed k hk
      simpa only [fixedGaps, map_add, map_smul, middleMass] using hh)
  have he : fullSynth N (boundaryGaps g)+
      (∑ i ∈ middle N, g i • fullSynth N (unitGap i)) = l := by
    simp_rw [← map_smul]
    rw [← map_sum, ← map_add, gaps_split g, hr]
  rwa [he] at hm

/-- Exact original all-spectrum purity bound. Natural rounding, zeros,
repetitions and singular PSD matrices are retained. The two literal PSD
tests supply the rows, and N ≥ 67 consumes the existing three-row solver.
UNCOMPILED source candidate; this comment is not validation evidence. -/
theorem actual_k1_l4_purity_bound
    (N : ℕ) (hN : 56 ≤ N) (l : Fin N → ℝ)
    (ho : Antitone l) (hn : ∀ i, 0 ≤ l i) (hmass : ∑ i, l i = 1)
    (hL4 : (∑ i : Fin 6, l ⟨i.val, by omega⟩) ≤
      ∑ i : Fin 10, l ⟨N-10+i.val, by omega⟩)
    (hK : (!![
      2*l ⟨N-1, by omega⟩, l ⟨N-2, by omega⟩-l ⟨0, by omega⟩,
        l ⟨N-4, by omega⟩-l ⟨1, by omega⟩;
      l ⟨N-2, by omega⟩-l ⟨0, by omega⟩, 2*l ⟨N-3, by omega⟩,
        l ⟨N-5, by omega⟩-l ⟨2, by omega⟩;
      l ⟨N-4, by omega⟩-l ⟨1, by omega⟩,
        l ⟨N-5, by omega⟩-l ⟨2, by omega⟩,
        2*l ⟨N-6, by omega⟩] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef) :
    ∑ i, (l i)^2 ≤ target N := by
  classical
  have h111 := hK.dotProduct_mulVec_nonneg (![1,1,1] : Fin 3 → ℝ)
  have h110 := hK.dotProduct_mulVec_nonneg (![1,1,0] : Fin 3 → ℝ)
  norm_num [dotProduct, mulVec, Fin.sum_univ_succ] at h111 h110
  have hL3 : (∑ i : Fin 3, l ⟨i.val, by omega⟩) ≤
      ∑ i : Fin 6, l ⟨N-6+i.val, by omega⟩ := by
    simp [Fin.sum_univ_succ,
      show N-6+1 = N-5 from by omega,
      show N-6+2 = N-4 from by omega,
      show N-6+3 = N-3 from by omega,
      show N-6+4 = N-2 from by omega,
      show N-6+5 = N-1 from by omega]
    linarith only [h111]
  have hC3 : l ⟨0, by omega⟩ ≤ ∑ i : Fin 3, l ⟨N-3+i.val, by omega⟩ := by
    simp [Fin.sum_univ_succ,
      show N-3+1 = N-2 from by omega,
      show N-3+2 = N-1 from by omega]
    linarith only [h110]
  by_cases h67 : 67 ≤ N
  · simpa only [target] using three_row_scalar_bound N h67 l ho hn hmass hL3 hL4 hC3
  · have hrows : ∀ r, 0 ≤ slackMap N hN l r := by
      intro r
      fin_cases r
      · exact sub_nonneg.mpr hL3
      · exact sub_nonneg.mpr hL4
      · exact sub_nonneg.mpr hC3
    have hg := continuous_concentration_good N hN l ho hn hrows
      (by simpa [spectrumK] using hK)
    have hb := spectralGood_square (Real.sqrt (target N)) l (Real.sqrt_nonneg _)
      (by rw [hmass]; norm_num) hg
    rw [hmass, Real.sq_sqrt (target_nonneg N)] at hb
    simpa only [one_pow, mul_one] using hb

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
