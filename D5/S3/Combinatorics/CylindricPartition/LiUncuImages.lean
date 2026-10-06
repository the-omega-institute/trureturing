/- GID: D5/S3/Combinatorics/CylindricPartition/LiUncuImages
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CylindricPartition/LiUncuImages
   mirror-E: none(waiver:weighted-image-cancellation)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Finprod]
   utility: none
   digest: Weighted Gaussian images cancel at the two strip boundaries. -/

import D5.S3.Combinatorics.CylindricPartition.LiUncuPaths
import Mathlib.Algebra.BigOperators.Finprod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace D5.S3.Combinatorics.CylindricPartition.LiUncu

open Polynomial LiUncuDefs

/-- The parity-restricted Gaussian displacement kernel. -/
noncomputable def imageKernel (L : ℕ) (d : ℤ) : ℤ[X] :=
  if ((L : ℤ) + d) % 2 = 0 then gaussInt L (((L : ℤ) + d) / 2) else 0

/-- The four weighted image families for the floor-reflected strip. -/
noncomputable def imagePolynomial (H L : ℕ) (a b : ℤ) : ℤ[X] :=
  let p : ℤ := 2 * H + 3
  let i : ℤ := H + 1 - a
  (∑ᶠ t : ℤ, X ^ (2 * p * t ^ 2 + (2 * a + 1) * t).toNat *
      imageKernel L (b - a - 2 * p * t)) +
    (∑ᶠ t : ℤ, X ^ (2 * p * t ^ 2 + (2 * a + 1) * t).toNat *
      imageKernel L (b + a + 1 + 2 * p * t)) -
    (∑ᶠ t : ℤ, X ^ ((2 * t + 1) * (p * t + i)).toNat *
      imageKernel L (b - p + 1 + a - 2 * p * t)) -
    (∑ᶠ t : ℤ, X ^ ((2 * t + 1) * (p * t + i)).toNat *
      imageKernel L (b + p - a + 2 * p * t))

/-- Initial images and the two boundary recurrences uniquely count all bounded paths. -/
theorem path_image_formula (H : ℕ) (hH : 1 ≤ H) (a b : ℤ)
    (ha : 0 ≤ a) (haH : a ≤ H) (hb : 0 ≤ b) (hbH : b ≤ H) (L : ℕ) :
    imagePolynomial H L a b = pathPolynomial H L a b := by
  classical
  have support (m : ℕ) (d : ℤ) (hd : d < -(m : ℤ) ∨ (m : ℤ) < d) :
      imageKernel m d = 0 := by
    unfold imageKernel
    split_ifs with he
    · unfold gaussInt
      rcases hd with hd | hd
      · rw [if_pos (by omega)]
      · rw [if_neg (by omega)]
        apply gauss_zero_of_lt
        omega
    · rfl
  have symmetry (m : ℕ) (d : ℤ) : imageKernel m (-d) = imageKernel m d := by
    by_cases hd : d < -(m : ℤ) ∨ (m : ℤ) < d
    · rw [support m d hd, support m (-d) (by omega)]
    · by_cases he : ((m : ℤ) + d) % 2 = 0
      · have he' : ((m : ℤ) + -d) % 2 = 0 := by omega
        have hb : 0 ≤ ((m : ℤ) + d) / 2 := by omega
        have hb' : 0 ≤ ((m : ℤ) + -d) / 2 := by omega
        simp only [imageKernel, he, he', ite_true]
        simp only [gaussInt, not_lt.mpr (Int.natCast_nonneg m), not_lt.mpr hb,
          not_lt.mpr hb', or_self, ite_false, Int.toNat_natCast]
        rw [gauss_symmetry m (((m : ℤ) + -d) / 2).toNat (by omega)]
        congr 1 <;> omega
      · have he' : ((m : ℤ) + -d) % 2 ≠ 0 := by omega
        simp only [imageKernel, he, he', ite_false]
  have ceiling (L : ℕ) : imagePolynomial H (L + 1) a (H + 1) =
      (1 - X ^ (L + 1)) * imagePolynomial H L a H := by
    have hook (d : ℤ) :
        imageKernel (L + 1) d - (1 - X ^ (L + 1)) * imageKernel L (d - 1) =
          X ^ (((L + 1 : ℕ) + d) / 2).toNat * imageKernel (L + 1) d := by
      by_cases he : ((L + 1 : ℕ) + d : ℤ) % 2 = 0
      · by_cases hd : d < -(L + 1 : ℕ) ∨ (L + 1 : ℕ) < d
        · rw [support (L + 1) d hd, support L (d - 1) (by omega)]
          simp
        · have hb : 0 ≤ ((L + 1 : ℕ) + d : ℤ) / 2 := by omega
          have hba : (((L + 1 : ℕ) + d : ℤ) / 2).toNat ≤ L + 1 := by omega
          have he' : ((L : ℤ) + (d - 1)) % 2 = 0 := by omega
          simp only [imageKernel, he, he', ite_true]
          let B : ℕ := (((L + 1 : ℕ) + d : ℤ) / 2).toNat
          have hbval : (B : ℤ) = ((L + 1 : ℕ) + d : ℤ) / 2 := by
            exact Int.toNat_of_nonneg hb
          have hmain : gaussInt (L + 1 : ℕ) (((L + 1 : ℕ) + d : ℤ) / 2) =
              gauss (L + 1) B := by
            simp only [gaussInt, not_lt.mpr (by omega : (0 : ℤ) ≤ L + 1),
              not_lt.mpr hb, or_self, ite_false]
            congr 1 <;> omega
          have hprev : gaussInt L (((L : ℤ) + (d - 1)) / 2) =
              gauss L (L + 1 - B) := by
            by_cases hz : B = 0
            · have hn : ((L : ℤ) + (d - 1)) / 2 < 0 := by omega
              rw [gaussInt, if_pos (Or.inr hn), gauss_zero_of_lt L (L + 1 - B) (by omega)]
            · have hnn : 0 ≤ ((L : ℤ) + (d - 1)) / 2 := by omega
              simp only [gaussInt, not_lt.mpr (Int.natCast_nonneg L), not_lt.mpr hnn,
                or_self, ite_false, Int.toNat_natCast]
              rw [gauss_symmetry L (((L : ℤ) + (d - 1)) / 2).toNat (by omega)]
              congr 1
              omega
          rw [hmain, hprev]
          have hh := gauss_hook (L + 1) (L + 1 - B) (by omega)
          rw [show L + 1 - (L + 1 - B) = B by omega,
            show L + 1 - 1 = L by omega,
            ← gauss_symmetry (L + 1) B hba] at hh
          change gauss (L + 1) B - (1 - X ^ (L + 1)) * gauss L (L + 1 - B) =
            X ^ B * gauss (L + 1) B
          rw [← hh]
          ring
      · have he' : ((L : ℤ) + (d - 1)) % 2 ≠ 0 := by omega
        simp only [imageKernel, he, he', ite_false, mul_zero, sub_zero]
    let p : ℤ := 2 * H + 3
    let i : ℤ := H + 1 - a
    let C (t : ℤ) := 2 * p * t ^ 2 + (2 * a + 1) * t
    let D (t : ℤ) := (2 * t + 1) * (p * t + i)
    have hp : 0 < p := by dsimp [p]; omega
    have hi : 1 ≤ i ∧ i < p := by dsimp [i, p]; omega
    have hc (t : ℤ) : 0 ≤ C t := by
      have hc' : C t = t * (2 * p * t + 2 * a + 1) := by dsimp [C]; ring
      rw [hc']
      by_cases ht : 0 ≤ t
      · exact mul_nonneg ht (by nlinarith)
      · apply mul_nonneg_of_nonpos_of_nonpos (by omega)
        dsimp [p] at *
        nlinarith
    have hd (t : ℤ) : 0 ≤ D t := by
      dsimp [D]
      by_cases ht : 0 ≤ t
      · exact mul_nonneg (by omega) (by nlinarith [hi.1])
      · apply mul_nonneg_of_nonpos_of_nonpos (by omega)
        nlinarith [hi.2]
    have finite (m : ℕ) (c v : ℤ) (hv : v ≠ 0) (e : ℤ → ℕ) :
        Function.HasFiniteSupport (fun t : ℤ => X ^ e t * imageKernel m (c + v * t)) := by
      apply (Set.finite_Icc (-(m : ℤ) - |c|) ((m : ℤ) + |c|)).subset
      intro t ht
      have ht' : imageKernel m (c + v * t) ≠ 0 := by
        intro hz
        exact ht (by simp [hz])
      have hbound : -(m : ℤ) ≤ c + v * t ∧ c + v * t ≤ m := by
        by_contra hn
        exact ht' (support m (c + v * t) (by omega))
      have habs : -|c| ≤ c ∧ c ≤ |c| := ⟨neg_abs_le c, le_abs_self c⟩
      have hv' : 1 ≤ v ∨ v ≤ -1 := by omega
      rcases hv' with hv' | hv'
      · constructor <;> nlinarith
      · constructor <;> nlinarith
    let A (m : ℕ) (t : ℤ) := X ^ (C t).toNat * imageKernel m (i - 2 * p * t)
    let B (m : ℕ) (t : ℤ) := X ^ (C t).toNat * imageKernel m (p - i + 2 * p * t)
    let E (m : ℕ) (t : ℤ) := X ^ (D t).toNat * imageKernel m (-i - 2 * p * t)
    let F (m : ℕ) (t : ℤ) := X ^ (D t).toNat * imageKernel m (p + i + 2 * p * t)
    let A' (m : ℕ) (t : ℤ) := X ^ (C t).toNat * imageKernel m (i - 2 * p * t - 1)
    let B' (m : ℕ) (t : ℤ) := X ^ (C t).toNat * imageKernel m (p - i + 2 * p * t - 1)
    let E' (m : ℕ) (t : ℤ) := X ^ (D t).toNat * imageKernel m (-i - 2 * p * t - 1)
    let F' (m : ℕ) (t : ℤ) := X ^ (D t).toNat * imageKernel m (p + i + 2 * p * t - 1)
    have fA (m : ℕ) : Function.HasFiniteSupport (A m) := by
      simpa [A, sub_eq_add_neg, neg_mul] using finite m i (-2 * p) (by omega) (fun t => (C t).toNat)
    have fB (m : ℕ) : Function.HasFiniteSupport (B m) := finite m (p - i) (2 * p)
      (by omega) (fun t => (C t).toNat)
    have fE (m : ℕ) : Function.HasFiniteSupport (E m) := by
      simpa [E, sub_eq_add_neg, neg_mul] using finite m (-i) (-2 * p) (by omega)
        (fun t => (D t).toNat)
    have fF (m : ℕ) : Function.HasFiniteSupport (F m) := finite m (p + i) (2 * p)
      (by omega) (fun t => (D t).toNat)
    have fA' : Function.HasFiniteSupport (A' L) := by
      have heq : A' L = fun t => X ^ (C t).toNat *
          imageKernel L ((i - 1) + (-2 * p) * t) := by
        funext t
        dsimp only [A']
        rw [show i - 2 * p * t - 1 = (i - 1) + (-2 * p) * t by ring]
      rw [heq]
      exact finite L (i - 1) (-2 * p) (by omega) (fun t => (C t).toNat)
    have fB' : Function.HasFiniteSupport (B' L) := by
      have heq : B' L = fun t => X ^ (C t).toNat *
          imageKernel L ((p - i - 1) + (2 * p) * t) := by
        funext t
        dsimp only [B']
        rw [show p - i + 2 * p * t - 1 = (p - i - 1) + (2 * p) * t by ring]
      rw [heq]
      exact finite L (p - i - 1) (2 * p) (by omega) (fun t => (C t).toNat)
    have fE' : Function.HasFiniteSupport (E' L) := by
      have heq : E' L = fun t => X ^ (D t).toNat *
          imageKernel L ((-i - 1) + (-2 * p) * t) := by
        funext t
        dsimp only [E']
        rw [show -i - 2 * p * t - 1 = (-i - 1) + (-2 * p) * t by ring]
      rw [heq]
      exact finite L (-i - 1) (-2 * p) (by omega) (fun t => (D t).toNat)
    have fF' : Function.HasFiniteSupport (F' L) := by
      have heq : F' L = fun t => X ^ (D t).toNat *
          imageKernel L ((p + i - 1) + (2 * p) * t) := by
        funext t
        dsimp only [F']
        rw [show p + i + 2 * p * t - 1 = (p + i - 1) + (2 * p) * t by ring]
      rw [heq]
      exact finite L (p + i - 1) (2 * p) (by omega) (fun t => (D t).toNat)
    let q : ℤ[X] := 1 - X ^ (L + 1)
    have pair (c d s : ℤ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hds : d = c + s) :
        X ^ c.toNat * (imageKernel (L + 1) s - q * imageKernel L (s - 1)) =
          X ^ d.toNat * (imageKernel (L + 1) (-s) - q * imageKernel L (-s - 1)) := by
      dsimp [q]
      rw [hook, hook]
      by_cases hs : s < -(L + 1 : ℕ) ∨ (L + 1 : ℕ) < s
      · rw [support (L + 1) s hs, support (L + 1) (-s) (by omega)]
        simp
      · by_cases he : ((L + 1 : ℕ) + s : ℤ) % 2 = 0
        · have hn : 0 ≤ ((L + 1 : ℕ) + s : ℤ) / 2 := by omega
          have hn' : 0 ≤ ((L + 1 : ℕ) + -s : ℤ) / 2 := by omega
          rw [symmetry, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
          have hexp : c.toNat + (((L + 1 : ℕ) + s : ℤ) / 2).toNat =
              d.toNat + (((L + 1 : ℕ) + -s : ℤ) / 2).toNat := by omega
          rw [hexp]
        · have he' : ((L + 1 : ℕ) + -s : ℤ) % 2 ≠ 0 := by omega
          simp only [imageKernel, he, he', ite_false, mul_zero, sub_zero]
    have cancelA (t : ℤ) :
        A (L + 1) t - q * A' L t = E (L + 1) (-t) - q * E' L (-t) := by
      have harg : -i - 2 * p * -t = -(i - 2 * p * t) := by ring
      have hexp : D (-t) = C t + (i - 2 * p * t) := by
        dsimp [D, C, i, p]
        ring
      dsimp [A, A', E, E']
      rw [harg]
      have h := pair (C t) (D (-t)) (i - 2 * p * t) (hc t) (hd (-t)) hexp
      linear_combination h
    have cancelB (t : ℤ) :
        B (L + 1) t - q * B' L t = F (L + 1) (-t - 1) - q * F' L (-t - 1) := by
      have harg : p + i + 2 * p * (-t - 1) = -(p - i + 2 * p * t) := by ring
      have hexp : D (-t - 1) = C t + (p - i + 2 * p * t) := by
        dsimp [D, C, i, p]
        ring
      dsimp [B, B', F, F']
      rw [harg]
      have h := pair (C t) (D (-t - 1)) (p - i + 2 * p * t) (hc t) (hd (-t - 1)) hexp
      linear_combination h
    have sumA : (∑ᶠ t, A (L + 1) t) - q * (∑ᶠ t, A' L t) =
        (∑ᶠ t, E (L + 1) t) - q * (∑ᶠ t, E' L t) := by
      rw [mul_finsum, mul_finsum, ← finsum_sub_distrib (fA (L + 1)),
        ← finsum_sub_distrib (fE (L + 1))]
      · exact finsum_eq_of_bijective (fun t : ℤ => -t)
          ⟨fun x y h => by dsimp at h; omega, fun y => ⟨-y, by dsimp; omega⟩⟩ cancelA
      · exact fE'.mul_right (fun _ => q)
      · exact fA'.mul_right (fun _ => q)
    have sumB : (∑ᶠ t, B (L + 1) t) - q * (∑ᶠ t, B' L t) =
        (∑ᶠ t, F (L + 1) t) - q * (∑ᶠ t, F' L t) := by
      rw [mul_finsum, mul_finsum, ← finsum_sub_distrib (fB (L + 1)),
        ← finsum_sub_distrib (fF (L + 1))]
      · exact finsum_eq_of_bijective (fun t : ℤ => -t - 1)
          ⟨fun x y h => by dsimp at h; omega, fun y => ⟨-y - 1, by dsimp; omega⟩⟩ cancelB
      · exact fF'.mul_right (fun _ => q)
      · exact fB'.mul_right (fun _ => q)
    have top : imagePolynomial H (L + 1) a (H + 1) =
        (∑ᶠ t, A (L + 1) t) + (∑ᶠ t, B (L + 1) t) -
          (∑ᶠ t, E (L + 1) t) - (∑ᶠ t, F (L + 1) t) := by
      unfold imagePolynomial
      dsimp only [A, B, E, F, C, D, i, p]
      refine congrArg₂ (· - ·)
        (congrArg₂ (· - ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
      all_goals
        apply finsum_congr
        intro t
        congr 1 <;> (apply congrArg (imageKernel (L + 1)); push_cast; ring)
    have prev : imagePolynomial H L a H =
        (∑ᶠ t, A' L t) + (∑ᶠ t, B' L t) -
          (∑ᶠ t, E' L t) - (∑ᶠ t, F' L t) := by
      unfold imagePolynomial
      dsimp only [A', B', E', F', C, D, i, p]
      refine congrArg₂ (· - ·)
        (congrArg₂ (· - ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
      all_goals
        apply finsum_congr
        intro t
        congr 1 <;> (apply congrArg (imageKernel L); push_cast; ring)
    rw [top, prev]
    change _ = q * _
    linear_combination sumA + sumB
  have gaussian_rec (m : ℕ) (v : ℤ) :
      gaussInt (m + 2 : ℕ) v = gaussInt (m + 1 : ℕ) v +
        gaussInt (m + 1 : ℕ) (v - 1) +
        (X ^ (m + 1) - 1) * gaussInt m (v - 1) := by
    by_cases hv : v < 0
    · simp only [gaussInt, if_pos (Or.inr hv), if_pos (Or.inr (by omega : v - 1 < 0)),
        zero_add, mul_zero]
    · by_cases hz : v = 0
      · subst v
        simp [gaussInt, gauss, show ¬((m : ℤ) + 2 < 0) by omega,
          show ¬((m : ℤ) + 1 < 0) by omega]
      · obtain ⟨j, hj⟩ : ∃ j : ℕ, v = j + 1 := ⟨(v - 1).toNat, by omega⟩
        subst v
        simp only [gaussInt, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
          show ¬((m : ℤ) + 2 < 0) by omega, show ¬((m : ℤ) + 1 < 0) by omega,
          not_lt.mpr (Int.natCast_nonneg m), show ¬((j : ℤ) + 1 < 0) by omega,
          show (j : ℤ) + 1 - 1 = j by omega, not_lt.mpr (Int.natCast_nonneg j),
          or_self, ite_false, Int.toNat_natCast]
        change gauss (m + 2) (j + 1) = gauss (m + 1) (j + 1) +
          gauss (m + 1) j + (X ^ (m + 1) - 1) * gauss m j
        by_cases hjm : j ≤ m + 1
        · have hh := gauss_hook (m + 1) j hjm
          rw [show m + 1 - 1 = m by omega] at hh
          rw [gauss]
          linear_combination -hh
        · rw [gauss_zero_of_lt (m + 2) (j + 1) (by omega),
            gauss_zero_of_lt (m + 1) (j + 1) (by omega),
            gauss_zero_of_lt (m + 1) j (by omega), gauss_zero_of_lt m j (by omega)]
          simp
  have kernel_rec (m : ℕ) (d : ℤ) :
      imageKernel (m + 2) d = imageKernel (m + 1) (d - 1) +
        imageKernel (m + 1) (d + 1) + (X ^ (m + 1) - 1) * imageKernel m d := by
    by_cases he : ((m + 2 : ℕ) + d : ℤ) % 2 = 0
    · have h1 : ((m + 1 : ℕ) + (d - 1) : ℤ) % 2 = 0 := by omega
      have h2 : ((m + 1 : ℕ) + (d + 1) : ℤ) % 2 = 0 := by omega
      have h0 : ((m : ℤ) + d) % 2 = 0 := by omega
      simp only [imageKernel, he, h1, h2, h0, ite_true]
      have e1 : ((m + 1 : ℕ) + (d - 1) : ℤ) / 2 =
          ((m + 2 : ℕ) + d : ℤ) / 2 - 1 := by omega
      have e2 : ((m + 1 : ℕ) + (d + 1) : ℤ) / 2 =
          ((m + 2 : ℕ) + d : ℤ) / 2 := by omega
      have e0 : ((m : ℤ) + d) / 2 = ((m + 2 : ℕ) + d : ℤ) / 2 - 1 := by omega
      rw [e1, e2, e0, gaussian_rec]
      ring
    · have h1 : ((m + 1 : ℕ) + (d - 1) : ℤ) % 2 ≠ 0 := by omega
      have h2 : ((m + 1 : ℕ) + (d + 1) : ℤ) % 2 ≠ 0 := by omega
      have h0 : ((m : ℤ) + d) % 2 ≠ 0 := by omega
      simp only [imageKernel, he, h1, h2, h0, ite_false, zero_add, mul_zero]
  have finite (m : ℕ) (c v : ℤ) (hv : v ≠ 0) (e : ℤ → ℕ) :
      Function.HasFiniteSupport (fun t : ℤ => X ^ e t * imageKernel m (c + v * t)) := by
    apply (Set.finite_Icc (-(m : ℤ) - |c|) ((m : ℤ) + |c|)).subset
    intro t ht
    have ht' : imageKernel m (c + v * t) ≠ 0 := by
      intro hz
      exact ht (by simp [hz])
    have hbound : -(m : ℤ) ≤ c + v * t ∧ c + v * t ≤ m := by
      by_contra hn
      exact ht' (support m (c + v * t) (by omega))
    have habs : -|c| ≤ c ∧ c ≤ |c| := ⟨neg_abs_le c, le_abs_self c⟩
    have hv' : 1 ≤ v ∨ v ≤ -1 := by omega
    rcases hv' with hv' | hv'
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  let p : ℤ := 2 * H + 3
  let i : ℤ := H + 1 - a
  let C (t : ℤ) := (2 * p * t ^ 2 + (2 * a + 1) * t).toNat
  let D (t : ℤ) := ((2 * t + 1) * (p * t + i)).toNat
  have hp : 5 ≤ p := by dsimp [p]; omega
  let family (e : ℤ → ℕ) (c v : ℤ) (m : ℕ) (b : ℤ) : ℤ[X] :=
    ∑ᶠ t, X ^ e t * imageKernel m (b + c + v * t)
  have fam_rec (e : ℤ → ℕ) (c v : ℤ) (hv : v ≠ 0) (m : ℕ) (b : ℤ) :
      family e c v (m + 2) b = family e c v (m + 1) (b - 1) +
        family e c v (m + 1) (b + 1) + (X ^ (m + 1) - 1) * family e c v m b := by
    have fin1 := finite (m + 1) (b - 1 + c) v hv e
    have fin2 := finite (m + 1) (b + 1 + c) v hv e
    have fin12 : Function.HasFiniteSupport (fun t =>
        X ^ e t * imageKernel (m + 1) (b - 1 + c + v * t) +
          X ^ e t * imageKernel (m + 1) (b + 1 + c + v * t)) := fin1.add fin2
    have fin0 : Function.HasFiniteSupport (fun t => (X ^ (m + 1) - 1) *
        (X ^ e t * imageKernel m (b + c + v * t))) := by
      apply (finite m (b + c) v hv e).subset
      intro t ht
      change X ^ e t * imageKernel m (b + c + v * t) ≠ 0
      intro hz
      exact ht (by dsimp only; rw [hz, mul_zero])
    dsimp only [family]
    rw [mul_finsum, ← finsum_add_distrib fin1 fin2,
      ← finsum_add_distrib fin12 fin0]
    apply finsum_congr
    intro t
    rw [kernel_rec]
    have e1 : b + c + v * t - 1 = b - 1 + c + v * t := by ring
    have e2 : b + c + v * t + 1 = b + 1 + c + v * t := by ring
    rw [e1, e2]
    ring
  have as_family (m : ℕ) (b : ℤ) : imagePolynomial H m a b =
      family C (-a) (-2 * p) m b + family C (a + 1) (2 * p) m b -
        family D (-p + 1 + a) (-2 * p) m b - family D (p - a) (2 * p) m b := by
    dsimp only [imagePolynomial, family, C, D, p, i]
    refine congrArg₂ (· - ·)
      (congrArg₂ (· - ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
    all_goals
      apply finsum_congr
      intro t
      congr 1 <;> (apply congrArg (imageKernel m); push_cast; ring)
  have image_rec (m : ℕ) (b : ℤ) : imagePolynomial H (m + 2) a b =
      imagePolynomial H (m + 1) a (b - 1) + imagePolynomial H (m + 1) a (b + 1) +
        (X ^ (m + 1) - 1) * imagePolynomial H m a b := by
    simp only [as_family, fam_rec C (-a) (-2 * p) (by omega),
      fam_rec C (a + 1) (2 * p) (by omega),
      fam_rec D (-p + 1 + a) (-2 * p) (by omega),
      fam_rec D (p - a) (2 * p) (by omega)]
    ring
  have floor (m : ℕ) : imagePolynomial H m a (-1) = imagePolynomial H m a 0 := by
    have pair (z t : ℤ) (e : ℕ) :
        X ^ e * imageKernel m (-1 - z - 2 * p * t) +
            X ^ e * imageKernel m (-1 + z + 1 + 2 * p * t) =
          X ^ e * imageKernel m (0 - z - 2 * p * t) +
            X ^ e * imageKernel m (0 + z + 1 + 2 * p * t) := by
      have h1 : -1 - z - 2 * p * t = -(0 + z + 1 + 2 * p * t) := by ring
      have h2 : -1 + z + 1 + 2 * p * t = -(0 - z - 2 * p * t) := by ring
      rw [h1, h2, symmetry, symmetry]
      ring
    rw [as_family, as_family]
    have pos : family C (-a) (-2 * p) m (-1) + family C (a + 1) (2 * p) m (-1) =
        family C (-a) (-2 * p) m 0 + family C (a + 1) (2 * p) m 0 := by
      dsimp only [family]
      rw [← finsum_add_distrib (finite m (-1 + -a) (-2 * p) (by omega) C)
        (finite m (-1 + (a + 1)) (2 * p) (by omega) C),
        ← finsum_add_distrib (finite m (0 + -a) (-2 * p) (by omega) C)
          (finite m (0 + (a + 1)) (2 * p) (by omega) C)]
      apply finsum_congr
      intro t
      rw [show -1 + -a + (-2 * p) * t = -1 - a - 2 * p * t by ring,
        show -1 + (a + 1) + 2 * p * t = -1 + a + 1 + 2 * p * t by ring,
        show 0 + -a + (-2 * p) * t = 0 - a - 2 * p * t by ring,
        show 0 + (a + 1) + 2 * p * t = 0 + a + 1 + 2 * p * t by ring]
      exact pair a t (C t)
    have neg : family D (-p + 1 + a) (-2 * p) m (-1) +
        family D (p - a) (2 * p) m (-1) =
        family D (-p + 1 + a) (-2 * p) m 0 + family D (p - a) (2 * p) m 0 := by
      dsimp only [family]
      rw [← finsum_add_distrib (finite m (-1 + (-p + 1 + a)) (-2 * p) (by omega) D)
        (finite m (-1 + (p - a)) (2 * p) (by omega) D),
        ← finsum_add_distrib (finite m (0 + (-p + 1 + a)) (-2 * p) (by omega) D)
          (finite m (0 + (p - a)) (2 * p) (by omega) D)]
      apply finsum_congr
      intro t
      rw [show -1 + (-p + 1 + a) + (-2 * p) * t =
          -1 - (p - 1 - a) - 2 * p * t by ring,
        show -1 + (p - a) + 2 * p * t = -1 + (p - 1 - a) + 1 + 2 * p * t by ring,
        show 0 + (-p + 1 + a) + (-2 * p) * t = 0 - (p - 1 - a) - 2 * p * t by ring,
        show 0 + (p - a) + 2 * p * t = 0 + (p - 1 - a) + 1 + 2 * p * t by ring]
      exact pair (p - 1 - a) t (D t)
    linear_combination pos - neg
  have small (m : ℕ) (hm : m ≤ 1) (b : ℤ) (hb : 0 ≤ b) (hbH : b ≤ H) :
      imagePolynomial H m a b = imageKernel m (b - a) + imageKernel m (b + a + 1) := by
    have offA (t : ℤ) (ht : t ≠ 0) : imageKernel m (b - a - 2 * p * t) = 0 := by
      apply support
      dsimp [p] at hp ⊢
      rcases (show t ≤ -1 ∨ 1 ≤ t by omega) with ht | ht
      · right; nlinarith
      · left; nlinarith
    have offB (t : ℤ) (ht : t ≠ 0) : imageKernel m (b + a + 1 + 2 * p * t) = 0 := by
      apply support
      dsimp [p] at hp ⊢
      rcases (show t ≤ -1 ∨ 1 ≤ t by omega) with ht | ht
      · left; nlinarith
      · right; nlinarith
    have offE (t : ℤ) : imageKernel m (b - p + 1 + a - 2 * p * t) = 0 := by
      apply support
      dsimp [p] at hp ⊢
      rcases (show t ≤ -1 ∨ 0 ≤ t by omega) with ht | ht
      · right; nlinarith
      · left; nlinarith
    have offF (t : ℤ) : imageKernel m (b + p - a + 2 * p * t) = 0 := by
      apply support
      dsimp [p] at hp ⊢
      rcases (show t ≤ -1 ∨ 0 ≤ t by omega) with ht | ht
      · left; nlinarith
      · right; nlinarith
    unfold imagePolynomial
    change (∑ᶠ t, X ^ C t * imageKernel m (b - a - 2 * p * t)) +
      (∑ᶠ t, X ^ C t * imageKernel m (b + a + 1 + 2 * p * t)) -
      (∑ᶠ t, X ^ D t * imageKernel m (b - p + 1 + a - 2 * p * t)) -
      (∑ᶠ t, X ^ D t * imageKernel m (b + p - a + 2 * p * t)) = _
    have hA : Function.support (fun t => X ^ C t *
        imageKernel m (b - a - 2 * p * t)) ⊆ ({0} : Finset ℤ) := by
      intro t ht
      by_contra hn
      have ht0 : t ≠ 0 := by simpa using hn
      exact ht (by dsimp only; rw [offA t ht0, mul_zero])
    have hB : Function.support (fun t => X ^ C t *
        imageKernel m (b + a + 1 + 2 * p * t)) ⊆ ({0} : Finset ℤ) := by
      intro t ht
      by_contra hn
      have ht0 : t ≠ 0 := by simpa using hn
      exact ht (by dsimp only; rw [offB t ht0, mul_zero])
    rw [finsum_eq_sum_of_support_subset _ hA, finsum_eq_sum_of_support_subset _ hB]
    simp only [offE, offF, mul_zero, finsum_zero, sub_zero, Finset.sum_singleton]
    simp [C]
  have zero (d : ℤ) : imageKernel 0 d = if d = 0 then 1 else 0 := by
    by_cases hd : d = 0
    · subst d
      simp [imageKernel, gaussInt, gauss]
    · rw [support 0 d (by omega), if_neg hd]
  have one (d : ℤ) : imageKernel 1 d = if d = -1 ∨ d = 1 then 1 else 0 := by
    by_cases hneg : d = -1
    · subst d
      simp [imageKernel, gaussInt, gauss]
    · by_cases hpos : d = 1
      · subst d
        simp [imageKernel, gaussInt, gauss]
      · by_cases hz : d = 0
        · subst d
          simp [imageKernel]
        · rw [support 1 d (by omega), if_neg (by tauto)]
  have initial0 (b : ℤ) (hb : 0 ≤ b) (hbH : b ≤ H) :
      imagePolynomial H 0 a b = pathPolynomial H 0 a b := by
    rw [small 0 (by omega) b hb hbH, zero, zero]
    have hsum : b + a + 1 ≠ 0 := by omega
    have heq : b - a = 0 ↔ a = b := by omega
    simp [pathPolynomial, pathWords, ValidPath, peakWeight, ha, haH, hsum, heq]
  have initial1 (b : ℤ) (hb : 0 ≤ b) (hbH : b ≤ H) :
      imagePolynomial H 1 a b = pathPolynomial H 1 a b := by
    rw [small 1 (by omega) b hb hbH, one, one]
    simp [pathPolynomial, pathWords, ValidPath, peakWeight]
    split_ifs <;> first | rfl | omega | norm_num
  have all (m : ℕ) : ∀ b : ℤ, 0 ≤ b → b ≤ H →
      imagePolynomial H m a b = pathPolynomial H m a b := by
    induction m using Nat.twoStepInduction with
    | zero => exact initial0
    | one => exact initial1
    | more m ih0 ih1 =>
        intro b hb hbH
        rw [image_rec, path_last_edge_recurrence H hH m a b hb hbH]
        by_cases htop : b = H
        · rw [if_pos htop]
          subst b
          rw [ceiling m,
            ih1 (H - 1) (by omega) (by omega), ih0 H (by omega) (by omega)]
          ring
        · rw [if_neg htop]
          have hlt : b < H := by omega
          rw [ih1 (b + 1) (by omega) (by omega), ih0 b hb hbH]
          by_cases hz : b = 0
          · subst b
            simp only [zero_sub, neg_zero]
            rw [floor, ih1 0 (by omega) (by omega)]
            simp only [ite_true]
          · rw [if_neg hz, ih1 (b - 1) (by omega) (by omega)]
  exact all L b hb hbH

end D5.S3.Combinatorics.CylindricPartition.LiUncu
