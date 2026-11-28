/- GID: D5/S3/Combinatorics/Graph/HilbertTetrahedronBounds
   generality: G
   mirror-B: none(waiver:covered-by-hilbert-clique-phase-reversal-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Inequalities for the coupled tetrahedron and triangle invariants -/

import OmegaBuild.Commands
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

compile_only_with_mathlib

/-! Omega original.

# Inequalities for the coupled tetrahedron and triangle invariants

The squared diameter bound is (25/4). The triangle and tetrahedron
energies are bounded by (329/50) and (621/50), respectively.
-/

namespace HilbertTetrahedronBounds

/-- The combined gradient and cycle energy estimate yields the strict radius bound. -/
theorem radius_of_energy {q S : ℝ}
    (h : q ≤ 25 / 12 ∨ (25 / 4) * (32 * q - 225 / 4) ≤ S * (4 * q - 25 / 4))
    (hS : S < 357 / 10) : q < 10275 / 4576 := by
  rcases h with h | h
  · linarith
  · by_contra! hq
    have hp : 0 < 4 * q - 25 / 4 := by linarith
    have hm := mul_lt_mul_of_pos_right hS hp
    linarith

/-- The gradient energies of a tetrahedral residual and its correction
sum to a radius estimate after their common cycle part is removed. -/
theorem corrected_energy {G C D : ℝ}
    (hG₀ : 0 ≤ G) (hC₀ : 0 ≤ C) (hD₀ : 0 ≤ D)
    (hG : G ≤ 621 / 50 + C) (hD : D ≤ 6 - C) :
    (Real.sqrt G + Real.sqrt D) ^ 2 < 357 / 10 := by
  have hP : G * D ≤ (621 / 50 + C) * (6 - C) :=
    mul_le_mul hG hD hD₀ (by linarith)
  have hP' : G * D ≤ 6 * (621 / 50) := by
    nlinarith [sq_nonneg C]
  have hsq : (Real.sqrt G * Real.sqrt D) ^ 2 = G * D := by
    rw [mul_pow, Real.sq_sqrt hG₀, Real.sq_sqrt hD₀]
  have hcross : Real.sqrt G * Real.sqrt D < 216 / 25 := by
    by_contra! hn
    have hm := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 216 / 25) hn
    nlinarith only [hm, hsq, hP']
  nlinarith only [hG, hD, hcross, Real.sq_sqrt hG₀, Real.sq_sqrt hD₀]

/-- The lower bound on the squared distance of every candidate edge controls
the correction when the squared radius exceeds (25/12). -/
theorem child_triangle {q a t : ℝ}
    (ha : 0 ≤ a) (ht' : a ≤ 3 / 2 + t)
    (h : q ≤ 25 / 12 ∨ 25 * (3 * q - 25 / 4) ≤ a ^ 2 * (4 * q - 25 / 4))
    (hamax : a ^ 2 ≤ 50 / 11) :
    9 / 4 + 2 * q - (2 / 3) * t ^ 2 ≤ 329 / 50 := by
  rcases h with h | h
  · nlinarith only [h, sq_nonneg t]
  by_cases hsmall : a ≤ 3 / 2
  · by_cases hq' : q ≤ 25 / 12
    · nlinarith only [hq', sq_nonneg t]
    have hmul := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ ha hsmall 2) (show 0 ≤ 4 * q - 25 / 4 by linarith)
    have hh : q ≤ 2275 / 1056 := by nlinarith only [h, hmul]
    nlinarith only [hh, sq_nonneg t]
  have hlarge : 3 / 2 < a := lt_of_not_ge hsmall
  have ha' : a ≤ 43 / 20 := by
    by_contra! hh
    nlinarith only [hamax, pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 43 / 20) hh.le 2]
  let x := a - 17 / 10
  have hx₀ : -1 / 5 ≤ x := by dsimp [x]; linarith
  have hx₁ : x ≤ 9 / 20 := by dsimp [x]; linarith
  have hxsq : x ^ 2 ≤ (9 / 20 : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ 9 / 20 - x by linarith)
      (show 0 ≤ 9 / 20 + x by linarith)]
  have hco : 0 ≤ 10122 - 3040 * x - 800 * x ^ 2 - 8500 := by
    nlinarith only [hx₁, hxsq]
  have heq : -800 * a ^ 4 + 2400 * a ^ 3 + 11754 * a ^ 2 - 45000 * a + 37425 =
      x ^ 2 * (10122 - 3040 * x - 800 * x ^ 2 - 8500) +
        8500 * (x + 1 / 340) ^ 2 + 5961 / 1700 := by
    dsimp [x]
    ring
  have hpos : 0 < -800 * a ^ 4 + 2400 * a ^ 3 + 11754 * a ^ 2 - 45000 * a + 37425 := by
    rw [heq]
    nlinarith only [mul_nonneg (sq_nonneg x) hco, sq_nonneg (x + 1 / 340)]
  have hden : 0 < 75 - 4 * a ^ 2 := by linarith
  have hq' : q * (75 - 4 * a ^ 2) ≤ (25 / 4) * (25 - a ^ 2) := by
    nlinarith only [h]
  have hgoal : 9 / 4 + 2 * q - (2 / 3) * (a - 3 / 2) ^ 2 ≤ 329 / 50 := by
    apply le_of_mul_le_mul_right _ hden
    nlinarith only [hq', hpos]
  have ht2 := pow_le_pow_left₀ (show 0 ≤ a - 3 / 2 by linarith) (show a - 3 / 2 ≤ t by linarith) 2
  linarith

noncomputable def faceThreshold : ℝ := 1037 / 150

noncomputable def faceAllowance (S : ℝ) : ℝ :=
  if S ≤ faceThreshold then faceThreshold / 2
  else Real.sqrt (faceThreshold * S) - S / 2

theorem faceAllowance_antitone : Antitone faceAllowance := by
  intro S T hST
  by_cases hS : S ≤ faceThreshold
  · simp only [faceAllowance, hS, ite_true]
    by_cases hT : T ≤ faceThreshold
    · simp only [hT, ite_true, le_refl]
    · simp only [hT, ite_false]
      have hA₀ : 0 ≤ faceThreshold := by norm_num [faceThreshold]
      have hT₀ : 0 ≤ T := hA₀.trans (le_of_not_ge hT)
      have hr : Real.sqrt (faceThreshold * T) ≤ (faceThreshold + T) / 2 := by
        apply (Real.sqrt_le_iff).2
        exact ⟨by positivity, by nlinarith only [sq_nonneg (faceThreshold - T)]⟩
      linarith only [hr]
  · have hT : ¬ T ≤ faceThreshold := fun hT => hS (hST.trans hT)
    simp only [faceAllowance, hS, hT, ite_false]
    have hA₀ : 0 ≤ faceThreshold := by norm_num [faceThreshold]
    have hS₀ : 0 ≤ S := hA₀.trans (le_of_not_ge hS)
    have hT₀ : 0 ≤ T := hS₀.trans hST
    have hroot : faceThreshold ≤ Real.sqrt (faceThreshold * S) := by
      have h := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (le_of_not_ge hS) hA₀)
      simpa [← pow_two, Real.sqrt_sq hA₀] using h
    have hr := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hST hA₀)
    have hdiff : (Real.sqrt (faceThreshold * T) - Real.sqrt (faceThreshold * S)) *
        (Real.sqrt (faceThreshold * T) + Real.sqrt (faceThreshold * S)) =
        faceThreshold * (T - S) := by
      nlinarith only [Real.sq_sqrt (mul_nonneg hA₀ hS₀), Real.sq_sqrt (mul_nonneg hA₀ hT₀)]
    have hm := mul_le_mul_of_nonneg_left
      (show 2 * faceThreshold ≤ Real.sqrt (faceThreshold * T) + Real.sqrt (faceThreshold * S) by linarith)
      (sub_nonneg.mpr hr)
    have hA : 0 < faceThreshold := by norm_num [faceThreshold]
    apply le_of_mul_le_mul_right _ hA
    nlinarith only [hm, hdiff]

/-- At low radius, the face energy lower bound depends only on the sum of
the three squared distances from the center. -/
theorem low_radius_face_allowance {T : ℝ} (hT : 0 < T) (hTB : T ≤ 25 / 4) :
    T + faceAllowance (50 - (1875 / 8) / T) ≤ Real.sqrt (1037 / 12) := by
  let B : ℝ := 25 / 4
  let A := faceThreshold
  let k := Real.sqrt (2 * A / B)
  have hB : 0 < B := by norm_num [B]
  have hA : 0 < A := by norm_num [A, faceThreshold]
  have hk : (4 / 3 : ℝ) ≤ k := by
    have h := Real.sqrt_le_sqrt (show (4 / 3 : ℝ) ^ 2 ≤ 2 * A / B by
      norm_num [A, B, faceThreshold])
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4 / 3)] at h
  have hBk : B * k = Real.sqrt (1037 / 12) := by
    calc
      B * k = Real.sqrt (B ^ 2) * Real.sqrt (2 * A / B) := by
        rw [Real.sqrt_sq hB.le]
      _ = Real.sqrt (B ^ 2 * (2 * A / B)) := (Real.sqrt_mul (sq_nonneg B) _).symm
      _ = Real.sqrt (1037 / 12) := by congr 1; norm_num [A, B, faceThreshold]
  have above (U : ℝ) (hU : 0 < U) (hUB : U ≤ B)
      (hL : A ≤ 8 * B - 6 * B ^ 2 / U) :
      U + (Real.sqrt (A * (8 * B - 6 * B ^ 2 / U)) -
        (8 * B - 6 * B ^ 2 / U) / 2) ≤ B * k := by
    let L := 8 * B - 6 * B ^ 2 / U
    have hL₀ : 0 ≤ L := hA.le.trans hL
    have hLU : L ≤ 2 * B := by
      dsimp [L]
      have h := (div_le_div_of_nonneg_left (by positivity : 0 ≤ 6 * B ^ 2) hU hUB)
      have he : 6 * B ^ 2 / B = 6 * B := by field_simp
      rw [he] at h
      linarith
    let t := Real.sqrt (L / (2 * B))
    have ht₀ : 0 ≤ t := Real.sqrt_nonneg _
    have ht₁ : t ≤ 1 := by
      change Real.sqrt (L / (2 * B)) ≤ 1
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt ((div_le_one (show 0 < 2 * B by positivity)).2 hLU)
    have ht2 : t ^ 2 = L / (2 * B) := Real.sq_sqrt (by positivity)
    have hL' : L = 2 * B * t ^ 2 := by
      rw [ht2]
      field_simp
    have hroot : Real.sqrt (A * L) = B * (k * t) := by
      rw [show A * L = (B * (k * t)) ^ 2 by
        rw [hL', mul_pow, mul_pow, show k ^ 2 = 2 * A / B from Real.sq_sqrt (by positivity)]
        field_simp, Real.sqrt_sq (by positivity)]
    have hden : 0 < 4 - t ^ 2 := by nlinarith only [pow_le_pow_left₀ ht₀ ht₁ 2]
    have hu : U * (4 - t ^ 2) = 3 * B := by
      have hLdef : L * U = 8 * B * U - 6 * B ^ 2 := by dsimp [L]; field_simp
      rw [hL'] at hLdef
      apply (mul_right_inj' (ne_of_gt (show 0 < 2 * B by positivity))).mp
      nlinarith only [hLdef]
    have hpoly : (1 + t) * (3 - t ^ 2) ≤ (4 / 3) * (4 - t ^ 2) := by
      have he : (4 / 3) * (4 - t ^ 2) - (1 + t) * (3 - t ^ 2) =
          (1 - t) * (7 - 2 * t - 3 * t ^ 2) / 3 := by ring
      have hh : 0 ≤ 7 - 2 * t - 3 * t ^ 2 := by
        nlinarith only [ht₁, pow_le_pow_left₀ ht₀ ht₁ 2]
      linarith only [he, div_nonneg (mul_nonneg (sub_nonneg.mpr ht₁) hh) (by norm_num : (0 : ℝ) ≤ 3)]
    have hstep : U - B * t ^ 2 ≤ B * ((4 / 3) * (1 - t)) := by
      apply le_of_mul_le_mul_right _ hden
      have hh := mul_le_mul_of_nonneg_left hpoly
        (show 0 ≤ B * (1 - t) by positivity)
      calc
        (U - B * t ^ 2) * (4 - t ^ 2) =
            B * (1 - t) * ((1 + t) * (3 - t ^ 2)) := by
          calc
            _ = U * (4 - t ^ 2) - B * t ^ 2 * (4 - t ^ 2) := by ring
            _ = _ := by rw [hu]; ring
        _ ≤ B * (1 - t) * ((4 / 3) * (4 - t ^ 2)) := hh
        _ = _ := by ring
    have hlast := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr ht₁)
    have hh := mul_le_mul_of_nonneg_left hlast hB.le
    change U + (Real.sqrt (A * L) - L / 2) ≤ B * k
    rw [hroot, hL']
    linarith only [hstep, hh]
  have hrewrite : 50 - (1875 / 8) / T = 8 * B - 6 * B ^ 2 / T := by norm_num [B]
  rw [hrewrite, ← hBk]
  unfold faceAllowance
  change T + (if 8 * B - 6 * B ^ 2 / T ≤ A then A / 2
    else Real.sqrt (A * (8 * B - 6 * B ^ 2 / T)) -
      (8 * B - 6 * B ^ 2 / T) / 2) ≤ B * k
  split_ifs with hcase
  · let U := 6 * B ^ 2 / (8 * B - A)
    have hden : 0 < 8 * B - A := by norm_num [B, A, faceThreshold]
    have hU : 0 < U := by positivity
    have hUB : U ≤ B := by
      apply (div_le_iff₀ hden).2
      norm_num [B, A, faceThreshold]
    have hTU : T ≤ U := by
      apply (le_div_iff₀ hden).2
      have hh := (le_div_iff₀ hT).1 (show 8 * B - A ≤ 6 * B ^ 2 / T by linarith)
      linarith only [hh]
    have hEq : 8 * B - 6 * B ^ 2 / U = A := by
      dsimp [U]
      field_simp
      ring
    have hbound := above U hU hUB hEq.ge
    rw [hEq, ← pow_two, Real.sqrt_sq hA.le] at hbound
    linarith only [hbound, hTU]
  · exact above T hT hTB (le_of_not_ge hcase)

end HilbertTetrahedronBounds

namespace HilbertTetrahedronBounds

/-- A face in a tetrahedron with four contact points has enough edge energy to
close the tetrahedral invariant in the high-radius range. -/
theorem high_radius_face_allowance {q S : ℝ}
    (hq₀ : 25 / 12 ≤ q) (hq₁ : q ≤ 75 / 32)
    (hS : (125 / 4 - S) * (4 * q - 25 / 4) ≤ 625 / 16) :
    3 * q + faceAllowance S ≤ Real.sqrt (1037 / 12) := by
  let A := faceThreshold
  let L : ℝ := 125 / 4 - (625 / 16) / (4 * q - 25 / 4)
  let Z := Real.sqrt (1037 / 12)
  have hden : 0 < 4 * q - 25 / 4 := by linarith
  have hL : L ≤ S := by
    dsimp [L]
    have h := (le_div_iff₀ hden).2 hS
    linarith
  have hL₀ : 25 / 2 ≤ L := by
    dsimp [L]
    have h := (div_le_iff₀ hden).2 (show (625 / 16 : ℝ) ≤ (75 / 4) * (4 * q - 25 / 4) by
      linarith)
    linarith
  have hL₁ : L ≤ 75 / 4 := by
    dsimp [L]
    have h := (le_div_iff₀ hden).2 (show (25 / 2 : ℝ) * (4 * q - 25 / 4) ≤ 625 / 16 by
      linarith)
    linarith
  have hL' : A < L := by
    have h : A < 25 / 2 := by norm_num [A, faceThreshold]
    exact h.trans_le hL₀
  refine (add_le_add_right (faceAllowance_antitone hL) _).trans ?_
  change 3 * q + faceAllowance L ≤ Z
  rw [show faceAllowance L = Real.sqrt (A * L) - L / 2 by
    simp only [faceAllowance, hL'.not_ge, ite_false, A]]
  have hA : 0 < A := by norm_num [A, faceThreshold]
  have hZ₂ : Z ^ 2 = 1037 / 12 := Real.sq_sqrt (by norm_num)
  have hZ₀ : 0 ≤ Z := Real.sqrt_nonneg _
  have hslope : A ≤ (3 / 4) * Z := by
    have h := Real.sqrt_le_sqrt (show ((4 / 3) * A) ^ 2 ≤ 1037 / 12 by norm_num [A, faceThreshold])
    rw [Real.sqrt_sq (by positivity)] at h
    change (4 / 3) * A ≤ Z at h
    linarith only [h]
  have hroot : Real.sqrt (A * L) ≤ Z + (3 / 8) * (L - 25 / 2) := by
    have hd : 0 ≤ L - 25 / 2 := sub_nonneg.mpr hL₀
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    have hAZ : A * (25 / 2) = Z ^ 2 := by rw [hZ₂]; norm_num [A, faceThreshold]
    have hs := mul_le_mul_of_nonneg_right hslope hd
    nlinarith only [hAZ, hs, sq_nonneg (L - 25 / 2)]
  have hfactor : L - 25 / 2 = 75 * (q - 25 / 12) / (4 * q - 25 / 4) := by
    apply (eq_div_iff hden.ne').2
    dsimp [L]
    rw [sub_mul, sub_mul, div_mul_cancel₀ _ hden.ne']
    ring
  have hqsum : 3 * q - 25 / 4 ≤ (L - 25 / 2) / 8 := by
    rw [hfactor]
    have hd : 4 * q - 25 / 4 ≤ 25 / 8 := by linarith
    apply le_of_mul_le_mul_right _ hden
    have hh := mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hq₀)
    have he : (75 * (q - 25 / 12) / (4 * q - 25 / 4) / 8) *
        (4 * q - 25 / 4) = 75 * (q - 25 / 12) / 8 := by
      rw [div_eq_mul_inv _ 8, mul_right_comm, div_mul_cancel₀ _ hden.ne']
      ring
    rw [he]
    nlinarith only [hh]
  linarith only [hroot, hqsum]

end HilbertTetrahedronBounds

namespace HilbertTetrahedronBounds

/-- Centering a child face leaves a monotone allowance in its old edge energy. -/
theorem face_energy_allowance {S T I u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1)
    (heasy : I ≤ 329 / 50 + T)
    (hsharp : I ≤ (329 / 100) - u / 6 + Real.sqrt (S * (329 / 50 + u / 3)) + T - S / 2) :
    I ≤ 937 / 300 + T + faceAllowance S := by
  let M : ℝ := 329 / 50
  let A := faceThreshold
  have hA : A = M + 1 / 3 := by norm_num [A, M, faceThreshold]
  have hA₀ : 0 < A := by norm_num [A, faceThreshold]
  by_cases hS : S ≤ A
  · simp only [faceAllowance, show S ≤ faceThreshold from hS, ite_true]
    change I ≤ 937 / 300 + T + A / 2
    linarith only [heasy, show A = 1037 / 150 by rfl]
  · have hSA : A ≤ S := (lt_of_not_ge hS).le
    have hS₀ := hA₀.le.trans hSA
    let x := Real.sqrt (S * (M + u / 3))
    let y := Real.sqrt (S * A)
    have hx₀ : 0 ≤ x := Real.sqrt_nonneg _
    have hy₀ : 0 ≤ y := Real.sqrt_nonneg _
    have hx₂ : x ^ 2 = S * (M + u / 3) := Real.sq_sqrt (mul_nonneg hS₀ (by positivity))
    have hy₂ : y ^ 2 = S * A := Real.sq_sqrt (mul_nonneg hS₀ hA₀.le)
    have hxy : x ≤ y := Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left (by linarith only [hA, hu₁]) hS₀)
    have hyS : y ≤ S := by
      have h := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hSA hS₀)
      simpa [← pow_two, Real.sqrt_sq hS₀, y] using h
    have hd : (y - x) * (y + x) = S * (1 - u) / 3 := by
      have h := congrArg (S * ·) hA
      nlinarith only [hx₂, hy₂, h]
    have hm := mul_le_mul_of_nonneg_left (show y + x ≤ 2 * S by linarith only [hxy, hyS])
      (sub_nonneg.mpr hxy)
    have hinc : (1 - u) / 6 ≤ y - x := by
      apply le_of_mul_le_mul_right _ (hA₀.trans_le hSA)
      nlinarith only [hd, hm]
    simp only [faceAllowance, show ¬ S ≤ faceThreshold from hS, ite_false]
    rw [mul_comm faceThreshold S]
    change I ≤ 937 / 300 + T + (y - S / 2)
    change I ≤ 329 / 100 - u / 6 + x + T - S / 2 at hsharp
    linarith only [hsharp, hinc]

theorem upper_face_cutoff {I T S : ℝ} (hI : I ≤ 937 / 300 + T + faceAllowance S)
    (h : T + faceAllowance S ≤ Real.sqrt (1037 / 12)) : I ≤ 621 / 50 := by
  have hs : Real.sqrt (1037 / 12) ≤ (2789 / 300 : ℝ) := by
    apply (Real.sqrt_le_iff).2
    norm_num
  linarith only [hI, h, hs]

end HilbertTetrahedronBounds
