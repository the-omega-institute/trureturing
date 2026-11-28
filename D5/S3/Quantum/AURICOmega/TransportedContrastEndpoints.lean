/- GID: D5/S3/Quantum/AURICOmega/TransportedContrastEndpoints
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/TransportedContrastEndpoints
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: []
   utility: none
   digest: Bound the reading contrast at overlap three fifths by two translated Gram probes. -/

import OmegaBuild.Commands
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

compile_only_with_mathlib

namespace D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints

open scoped Matrix

private theorem one_sided_bound {M : Type*} (k : M → M → ℚ) (tri : M → M → M → M)
    (hdiag : ∀ a, k a a = 1) (hsymm : ∀ a b, k a b = k b a)
    (hnonneg : ∀ a b, 0 ≤ k a b)
    (hcancelLeft : ∀ a b, tri a a b = b) (hcancelRight : ∀ a b, tri a b b = a)
    (hassoc : ∀ a b c d e, tri (tri a b c) d e = tri a b (tri c d e))
    (hinvLeft : ∀ a b c d, k (tri a b c) (tri a b d) = k c d)
    (hinvRight : ∀ a b c d, k (tri a c d) (tri b c d) = k a b)
    (hgram : ∀ (p : Fin 5 → M) (c : Fin 5 → ℚ),
      0 ≤ ∑ i, ∑ j, c i * c j * k (p i) (p j))
    (x y z : M) (ht : k x y = 3 / 5) : k x z - k y z ≤ 406 / 625 := by
  let w := tri x y z
  have hxw : k x w = k y z := by
    simpa only [w, hcancelRight] using hinvLeft x y y z
  have hzw : k z w = 3 / 5 := by
    rw [hsymm z w]
    simpa only [w, hcancelLeft, ht] using hinvRight x y y z
  let offset := k y z - 1 / 10
  let gap := 13 / 20 - (k x z - k y z)
  let B := 3 / 5 - k y z
  let E := 2 * (1 - k x z - B ^ 2 - k y w * B ^ 2)
  let R := fun p => k x p - B * k y p - k z p + B * k w p
  have hquadratic (p : M) (s : ℚ) : 0 ≤ E + 2 * s * R p + s ^ 2 := by
    have htest := hgram ![x, y, z, w, p] ![1, -B, -1, B, s]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, hdiag, hsymm y x, hsymm z x, hsymm z y, hsymm w x,
      hsymm w y, hsymm w z, hsymm p x, hsymm p y, hsymm p z, hsymm p w,
      ht, hxw, hzw] at htest
    dsimp [E, R, B] at htest ⊢
    nlinarith only [htest]
  have henergy : 0 ≤ E := by simpa using hquadratic x 0
  have hresidual (p : M) : R p ^ 2 ≤ E := by
    have htest := hquadratic p (-R p)
    nlinarith only [htest]
  have hdecomp : E = 2 * (gap - offset ^ 2 - k y w * B ^ 2) := by
    dsimp [E, gap, offset, B]
    ring
  have hslack : 0 ≤ k y w * B ^ 2 := mul_nonneg (hnonneg y w) (sq_nonneg B)
  have hgap0 : 0 ≤ gap := by
    linarith only [hdecomp, henergy, hslack, sq_nonneg offset]
  by_contra! hbound
  have hgap : gap ≤ 1 / 2500 := by dsimp [gap]; linarith only [hbound]
  have hoffsetSq : offset ^ 2 ≤ (1 / 50 : ℚ) ^ 2 := by
    linarith only [hdecomp, henergy, hslack, hgap]
  obtain ⟨hoffsetLo, hoffsetHi⟩ := abs_le_of_sq_le_sq' hoffsetSq (by norm_num)
  have hB : B = 1 / 2 - offset := by dsimp [B, offset]; ring
  have hBLo : 12 / 25 ≤ B := by linarith only [hB, hoffsetHi]
  have hBHi : B ≤ 13 / 25 := by linarith only [hB, hoffsetLo]
  have hB0 : 0 ≤ B := by linarith only [hBLo]
  have hclose (p : M) : -(3 / 100 : ℚ) ≤ R p := by
    have hsq : R p ^ 2 ≤ (3 / 100 : ℚ) ^ 2 := by
      linarith only [hresidual p, hdecomp, hgap, hslack, sq_nonneg offset]
    exact (abs_le_of_sq_le_sq' hsq (by norm_num)).1
  let U := tri y x
  let T := fun a => tri a z x
  let p := T y
  let q := T (U y)
  have hUx : U x = y := hcancelRight y x
  have hUw : U w = z := by
    dsimp [U, w]
    rw [← hassoc, hcancelRight, hcancelLeft]
  have hUp : U p = q := (hassoc y x y z x).symm
  have hUTx : U (T x) = p := by
    change tri y x (tri x z x) = tri y z x
    rw [← hassoc, hcancelRight]
  have hpX : k x p = k y z := by
    simpa only [p, hcancelLeft, hsymm z y] using hinvRight z y z x
  have hpY : k y p = k x z := by
    calc
      k y p = k (U x) (U (T x)) := by rw [hUx, hUTx]
      _ = k x (T x) := hinvLeft y x x (T x)
      _ = k z x := by simpa only [hcancelLeft] using hinvRight z x z x
      _ = k x z := hsymm z x
  have hqX : k x q = k y w := by
    calc
      k x q = k z (U y) := by simpa only [hcancelLeft] using hinvRight z (U y) z x
      _ = k w y := by
        rw [← hUw]
        exact hinvLeft y x w y
      _ = k y w := hsymm w y
  have hqY : k y q = k y z := by
    calc
      k y q = k (U x) (U p) := by rw [hUx, hUp]
      _ = k x p := hinvLeft y x x p
      _ = k y z := hpX
  have hpW : k w p = k z q := by
    rw [← hUp, ← hUw]
    exact (hinvLeft y x w p).symm
  have hwq : k w q ≤ 1 := by
    have htwo := hgram ![w, q, w, w, w] ![1, -1, 0, 0, 0]
    simp [Fin.sum_univ_succ, hdiag, hsymm q w] at htwo
    linarith only [htwo]
  have hlower : -(57 / 1250 : ℚ) ≤ R p + B * R q := by
    have hq := mul_le_mul_of_nonneg_left (hclose q) hB0
    linarith only [hclose p, hq, hBHi]
  have hprobe :
      R p + B * R q = k y z - B * k x z + B * k y w -
        k z p + B ^ 2 * (k w q - k y z) := by
    dsimp [R]
    rw [hpX, hpY, hpW, hqX, hqY]
    ring
  have hupper : R p + B * R q ≤
      k y z - B * k x z + B ^ 2 * (1 - k y z) + B * k y w := by
    have hbq := mul_le_mul_of_nonneg_left (sub_le_sub_right hwq (k y z)) (sq_nonneg B)
    linarith only [hprobe, hbq, hnonneg z p]
  have hcost : B * k y w ≤ (25 / 12 : ℚ) * (1 / 2500) := by
    have hmul := mul_le_mul_of_nonneg_right hBLo (mul_nonneg hB0 (hnonneg y w))
    nlinarith only [hmul, hdecomp, henergy, hgap, sq_nonneg offset]
  have hgapTerm : B * gap ≤ (13 / 25 : ℚ) * (1 / 2500) :=
    mul_le_mul hBHi hgap hgap0 (by norm_num)
  have hcubic : -offset ^ 3 ≤ (1 / 50 : ℚ) * offset ^ 2 := by
    have hmul := mul_nonneg (show 0 ≤ offset + 1 / 50 by linarith only [hoffsetLo])
      (sq_nonneg offset)
    nlinarith only [hmul]
  have hpoly : k y z - B * k x z + B ^ 2 * (1 - k y z) =
      -1 / 20 + offset / 10 + 29 / 10 * offset ^ 2 - offset ^ 3 + B * gap := by
    dsimp [B, gap, offset]
    ring
  linarith only [hlower, hupper, hcost, hgapTerm, hoffsetHi, hoffsetSq, hcubic, hpoly]

/-- At overlap three fifths, bilateral heap transport gives a uniform gap of one
two-thousand-five-hundredth below the five-point contrast endpoint. Repeated
sample points are allowed in the five-point Gram hypothesis. -/
theorem abs_contrast_le {M : Type*} (k : M → M → ℚ) (tri : M → M → M → M)
    (hdiag : ∀ a, k a a = 1) (hsymm : ∀ a b, k a b = k b a)
    (hnonneg : ∀ a b, 0 ≤ k a b)
    (hcancelLeft : ∀ a b, tri a a b = b) (hcancelRight : ∀ a b, tri a b b = a)
    (hassoc : ∀ a b c d e, tri (tri a b c) d e = tri a b (tri c d e))
    (hinvLeft : ∀ a b c d, k (tri a b c) (tri a b d) = k c d)
    (hinvRight : ∀ a b c d, k (tri a c d) (tri b c d) = k a b)
    (hgram : ∀ (p : Fin 5 → M) (c : Fin 5 → ℚ),
      0 ≤ ∑ i, ∑ j, c i * c j * k (p i) (p j))
    (x y z : M) (ht : k x y = 3 / 5) : |k x z - k y z| ≤ 406 / 625 := by
  have bound := one_sided_bound k tri hdiag hsymm hnonneg hcancelLeft hcancelRight
    hassoc hinvLeft hinvRight hgram
  exact abs_le.mpr ⟨by linarith only [bound y x z ((hsymm y x).trans ht)], bound x y z ht⟩

end D5.S3.Quantum.AURICOmega.TransportedContrastEndpoints
