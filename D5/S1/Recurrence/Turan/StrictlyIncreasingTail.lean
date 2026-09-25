/- GID: D5/S1/Recurrence/Turan/StrictlyIncreasingTail
   generality: G
   mirror-B: D5/B/S1/Recurrence/Turan/StrictlyIncreasingTail
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Strictly increasing Jacobi coefficients force the weighted Turan inequality
     on the right tail. -/

import Mathlib.Tactic

namespace D5.S1.Recurrence.Turan.StrictlyIncreasingTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The orthonormal three-term recurrence with off-diagonal coefficients `a` and
diagonal coefficients `b`, normalized by `q 0 = 1`. -/
noncomputable def orthonormal (a b : ℕ → ℝ) (t : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => (t - b 0) / a 1
  | n + 2 =>
      ((t - b (n + 1)) * orthonormal a b t (n + 1) -
        a (n + 1) * orthonormal a b t n) / a (n + 2)

/-- Krasikov's weighted Turan inequality on the complete closed right tail, in
the strictly increasing off-diagonal case and the canonical `c = 1` normalization. -/
theorem weighted_turan_nonneg_of_strict_mono
    (a b : ℕ → ℝ) (t : ℝ) (ha0 : a 0 = 0) (ha : StrictMono a)
    (hb : Monotone b) (n : ℕ) (hn : 1 ≤ n) (ht : b n - 2 * a n ≤ t) :
    0 ≤ orthonormal a b t n ^ 2 -
      (a (n + 1) / a n) * orthonormal a b t (n - 1) * orthonormal a b t (n + 1) := by
  let q := orthonormal a b t
  let S := fun m : ℕ =>
    q m ^ 2 - (a (m + 1) / a m) * q (m - 1) * q (m + 1)
  change 0 ≤ S n
  have ha_pos (m : ℕ) (hm : 1 ≤ m) : 0 < a m := by
    have h := ha (Nat.zero_lt_of_lt hm)
    rwa [ha0] at h
  have hrec (m : ℕ) :
      q (m + 2) =
        ((t - b (m + 1)) * q (m + 1) - a (m + 1) * q m) / a (m + 2) := by
    rfl
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => omega
      | succ j =>
          cases j with
          | zero =>
              have ha1 : 0 < a 1 := ha_pos 1 (by omega)
              have ha2 : 0 < a 2 := ha_pos 2 (by omega)
              have hb01 : b 0 ≤ b 1 := hb (by omega)
              have hbase :
                  a 1 ^ 2 * S 1 =
                    (b 1 - b 0) * t + a 1 ^ 2 + b 0 ^ 2 - b 0 * b 1 := by
                dsimp [S, q]
                norm_num [orthonormal]
                field_simp [ha1.ne', ha2.ne']
                ring
              have hlower :
                  (a 1 - (b 1 - b 0)) ^ 2 ≤
                    (b 1 - b 0) * t + a 1 ^ 2 + b 0 ^ 2 - b 0 * b 1 := by
                nlinarith [sq_nonneg (b 1 - b 0)]
              have hscaled : 0 ≤ a 1 ^ 2 * S 1 := by
                rw [hbase]
                exact (sq_nonneg _).trans hlower
              nlinarith [sq_pos_of_pos ha1]
          | succ k =>
              let j := k + 1
              let N := k + 2
              have hj : 1 ≤ j := by simp [j]
              have hN : 1 ≤ N := by simp [N]
              have hjN : j < N := by simp [j, N]
              have hA : 0 < a j := ha_pos j hj
              have hB : 0 < a N := ha_pos N hN
              have hAB : a j < a N := ha hjN
              have hbjN : b j ≤ b N := hb hjN.le
              by_cases hcentral : t ≤ b N + 2 * a N
              · have hcoef : 0 ≤ 4 * a N ^ 2 - (t - b N) ^ 2 := by
                  nlinarith [sq_nonneg (t - b N)]
                have hcentral_id :
                    4 * a N ^ 2 * S N =
                      (2 * a N * q N - (t - b N) * q (N - 1)) ^ 2 +
                        (4 * a N ^ 2 - (t - b N) ^ 2) * q (N - 1) ^ 2 := by
                  dsimp [S]
                  have hnext : 0 < a (N + 1) := ha_pos (N + 1) (by omega)
                  rw [show q (N + 1) =
                      ((t - b N) * q N - a N * q (N - 1)) / a (N + 1) by
                    simpa [N, j] using hrec (k + 1)]
                  field_simp [hB.ne', hnext.ne']
                  ring
                have hrhs :
                    0 ≤ (2 * a N * q N - (t - b N) * q (N - 1)) ^ 2 +
                      (4 * a N ^ 2 - (t - b N) ^ 2) * q (N - 1) ^ 2 :=
                  add_nonneg (sq_nonneg _) (mul_nonneg hcoef (sq_nonneg _))
                have hfactor : 0 < 4 * a N ^ 2 := by positivity
                nlinarith [hcentral_id]
              · have htail : b N + 2 * a N < t := lt_of_not_ge hcentral
                let A := a j
                let B := a N
                let d := b N - b j
                let r := t - b N - 2 * B
                let den := (t - b j + 2 * A) * (t - b j - 2 * A)
                let C := t ^ 2 - (b j + b N) * t - 2 * A ^ 2 - 2 * B ^ 2 + b j * b N
                let lam := (A ^ 2 / B ^ 2) * (C / den)
                let V := B ^ 2 * d ^ 2 + (2 * B + r) * (2 * B ^ 2 - A ^ 2) * d +
                  (B ^ 2 - A ^ 2) * (r ^ 2 + 4 * B * r + 4 * B ^ 2 - 2 * A ^ 2)
                let U := 2 * B * ((B ^ 2 + A ^ 2) * d + (2 * B + r) * (B ^ 2 - A ^ 2))
                let W := B ^ 2 * (d ^ 2 + (2 * B + r) * d + 2 * B ^ 2 - 2 * A ^ 2)
                have hd : 0 ≤ d := by dsimp [d]; linarith
                have hr : 0 < r := by dsimp [r, B]; linarith
                have hBA : 0 < B - A := by dsimp [A, B]; linarith
                have hBA2 : 0 < B ^ 2 - A ^ 2 := by
                  dsimp [A, B]
                  nlinarith
                have hleft : b j + 2 * A < t := by
                  dsimp [A]
                  nlinarith
                have hden : 0 < den := by
                  dsimp [den]
                  apply mul_pos <;> linarith
                have hC_id :
                    C = r ^ 2 + (4 * B + d) * r + 2 * (B ^ 2 - A ^ 2 + d * B) := by
                  dsimp [C, r, d, A, B]
                  ring
                have hC : 0 < C := by
                  rw [hC_id]
                  nlinarith [sq_nonneg r, mul_nonneg hd hB.le]
                have hlam : 0 < lam := by
                  dsimp [lam]
                  positivity
                have htj : b j - 2 * a j ≤ t := by
                  dsimp [A] at hleft
                  linarith
                have hSj_nonneg : 0 ≤ S j := ih j (by omega) hj htj
                have hA' : 0 < A := by simpa [A] using hA
                have hB' : 0 < B := by simpa [B] using hB
                have hW : 0 < W := by
                  dsimp [W]
                  have : 0 < d ^ 2 + (2 * B + r) * d + 2 * B ^ 2 - 2 * A ^ 2 := by
                    nlinarith [sq_nonneg d, mul_nonneg (by linarith : 0 ≤ 2 * B + r) hd]
                  positivity
                let F := B ^ 2 * d ^ 2 + (2 * B + r) * (B ^ 2 - A ^ 2) * d +
                  (B ^ 2 - A ^ 2) ^ 2
                have hF : 0 < F := by
                  dsimp [F]
                  have hmiddle : 0 ≤ (2 * B + r) * (B ^ 2 - A ^ 2) * d := by
                    positivity
                  nlinarith [sq_pos_of_pos hBA2, sq_nonneg d]
                have hf1 : 0 < 2 * B + 2 * A + d + r := by
                  dsimp [A, B] at *
                  nlinarith
                have hf2 : 0 < 2 * B - 2 * A + d + r := by nlinarith
                have hdisc_id :
                    U ^ 2 - 4 * V * W =
                      -4 * B ^ 2 * (2 * B + 2 * A + d + r) *
                        (2 * B - 2 * A + d + r) * F := by
                  dsimp [U, V, W, F]
                  ring
                have hdisc : 0 < 4 * V * W - U ^ 2 := by
                  have hneg :
                      U ^ 2 - 4 * V * W < 0 := by
                    rw [hdisc_id]
                    have hprod :
                        0 < 4 * B ^ 2 * (2 * B + 2 * A + d + r) *
                          (2 * B - 2 * A + d + r) * F := by
                      positivity
                    rw [show
                      -4 * B ^ 2 * (2 * B + 2 * A + d + r) *
                          (2 * B - 2 * A + d + r) * F =
                        -(4 * B ^ 2 * (2 * B + 2 * A + d + r) *
                          (2 * B - 2 * A + d + r) * F) by ring]
                    exact neg_lt_zero.mpr hprod
                  rw [show 4 * V * W - U ^ 2 = -(U ^ 2 - 4 * V * W) by ring]
                  exact neg_pos.mpr hneg
                have hquad : 0 ≤ V * q j ^ 2 - U * q j * q N + W * q N ^ 2 := by
                  have hquad_id :
                      4 * W * (V * q j ^ 2 - U * q j * q N + W * q N ^ 2) =
                        (2 * W * q N - U * q j) ^ 2 +
                          (4 * V * W - U ^ 2) * q j ^ 2 := by ring
                  have hquad_rhs :
                      0 ≤ (2 * W * q N - U * q j) ^ 2 +
                        (4 * V * W - U ^ 2) * q j ^ 2 := by positivity
                  have hscaled :
                      0 ≤ 4 * W * (V * q j ^ 2 - U * q j * q N + W * q N ^ 2) := by
                    rw [hquad_id]
                    exact hquad_rhs
                  have hfourW : 0 < 4 * W := mul_pos (by norm_num) hW
                  exact nonneg_of_mul_nonneg_right hscaled hfourW
                have hnext : 0 < a (N + 1) := ha_pos (N + 1) (by omega)
                have hSN :
                    S N = q N ^ 2 + q j ^ 2 - ((t - b N) / B) * q j * q N := by
                  dsimp [S]
                  rw [show N - 1 = j by simp [N, j]]
                  rw [show q (N + 1) =
                      ((t - b N) * q N - a N * q j) / a (N + 1) by
                    simpa [N, j] using hrec (k + 1)]
                  dsimp [B]
                  field_simp [hB.ne', hnext.ne']
                  ring
                have hSj_eq : S j = q j ^ 2 - (B / A) * q k * q N := by
                  simp [S, j, N, A, B]
                have hlink : B * q N = (t - b j) * q j - A * q k := by
                  rw [show q N = ((t - b j) * q j - A * q k) / B by
                    simpa [N, j, A, B] using hrec k]
                  field_simp [hB'.ne']
                have hqk : q k = ((t - b j) * q j - B * q N) / A := by
                  apply (eq_div_iff hA'.ne').2
                  linarith [hlink]
                have hD :
                    B ^ 2 * den * (S N - lam * S j) =
                      V * q j ^ 2 - U * q j * q N + W * q N ^ 2 := by
                  rw [hSN, hSj_eq, hqk]
                  dsimp [lam, C, V, U, W, r, d]
                  field_simp [hA'.ne', hB'.ne', hden.ne']
                  ring
                have hdiff : 0 ≤ S N - lam * S j := by
                  have hscale : 0 < B ^ 2 * den := by positivity
                  have hscaled : 0 ≤ B ^ 2 * den * (S N - lam * S j) := by
                    rw [hD]
                    exact hquad
                  exact nonneg_of_mul_nonneg_right hscaled hscale
                linarith [mul_nonneg hlam.le hSj_nonneg]

#print axioms orthonormal
#print axioms weighted_turan_nonneg_of_strict_mono

end D5.S1.Recurrence.Turan.StrictlyIncreasingTail
