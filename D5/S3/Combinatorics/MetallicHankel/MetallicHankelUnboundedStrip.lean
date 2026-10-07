/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedStrip
   mirror-E: none(waiver:finite-rational-strip-comparison)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.AbsoluteValue]
   utility: none
   digest: Exponential coefficient growth and bounded endpoint rows bound every Hankel strip row. -/

import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedJacobi

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedStrip

open MetallicHankelDefs

set_option maxHeartbeats 1000000 in
/-- All rows between two uniformly bounded rows of an exponentially bounded moment sequence
are bounded. The dyadic estimate uses only finite maxima and rational inequalities. -/
theorem bounded_strip (Φ : PowerSeries ℤ) (a b B M : ℕ) (hab : a ≤ b) (hM : 1 ≤ M)
    (hcoeff : ∀ m, (PowerSeries.coeff m Φ).natAbs ≤ B ^ m)
    (hleft : ∀ j, (shiftedHankel Φ a j).natAbs ≤ M)
    (hright : ∀ j, (shiftedHankel Φ b j).natAbs ≤ M) :
    ∀ ℓ j, a ≤ ℓ → ℓ ≤ b → (shiftedHankel Φ ℓ j).natAbs <
      2 ^ (Nat.log2 M + 2 * (ℓ - a) * (b - ℓ) + 1) := by
  classical
  have hdet : ∀ ℓ j, ℓ ≤ b → (shiftedHankel Φ ℓ j).natAbs ≤
      2 ^ (((B + 1) * (b + 3)) * (j + 1) ^ 2) := by
    classical
    intro ℓ j hℓ
    let K : ℕ := 2 ^ (B * (b + 2 * j))
    have hentry : ∀ i k : Fin j,
        |PowerSeries.coeff (ℓ + i + k) Φ| ≤ (K : ℤ) := by
      intro i k
      have hi := i.isLt
      have hk := k.isLt
      have ht : ℓ + (i : ℕ) + k ≤ b + 2 * j := by omega
      have habs : (PowerSeries.coeff (ℓ + i + k) Φ).natAbs ≤ K := by
        calc
          (PowerSeries.coeff (ℓ + i + k) Φ).natAbs ≤ B ^ (ℓ + i + k) := hcoeff _
          _ ≤ (2 ^ B) ^ (ℓ + i + k) := Nat.pow_le_pow_left (le_of_lt Nat.lt_two_pow_self) _
          _ = 2 ^ (B * (ℓ + i + k)) := (pow_mul _ _ _).symm
          _ ≤ K := by dsimp [K]; gcongr <;> omega
      rw [← Int.natCast_natAbs]
      exact_mod_cast habs
    have hd := Matrix.det_le (A := Matrix.of fun i k : Fin j =>
      PowerSeries.coeff (ℓ + i + k) Φ) (abv := AbsoluteValue.abs) hentry
    have hdnat : (shiftedHankel Φ ℓ j).natAbs ≤ j.factorial * K ^ j := by
      simp only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul,
        ← Int.natCast_natAbs, ← Nat.cast_pow, ← Nat.cast_mul] at hd
      exact_mod_cast hd
    have hjpow : j.factorial ≤ 2 ^ (j * j) := by
      calc
        j.factorial ≤ j ^ j := Nat.factorial_le_pow j
        _ ≤ (2 ^ j) ^ j := Nat.pow_le_pow_left (le_of_lt Nat.lt_two_pow_self) j
        _ = 2 ^ (j * j) := (pow_mul _ _ _).symm
    calc
      (shiftedHankel Φ ℓ j).natAbs ≤ j.factorial * K ^ j := hdnat
      _ ≤ 2 ^ (j * j) * K ^ j := Nat.mul_le_mul_right _ hjpow
      _ = 2 ^ (j * j + B * (b + 2 * j) * j) := by dsimp [K]; rw [← pow_mul, ← pow_add]
      _ ≤ 2 ^ (((B + 1) * (b + 3)) * (j + 1) ^ 2) := by
        apply Nat.pow_le_pow_right (by decide : 0 < 2)
        have hj₁ : j ≤ (j + 1) ^ 2 := by nlinarith
        have hj₂ : j ^ 2 ≤ (j + 1) ^ 2 := by nlinarith
        have hb := Nat.mul_le_mul_left b hj₁
        have h₂ := Nat.mul_le_mul_left 2 hj₂
        have hbj : (b + 2 * j) * j ≤ (b + 2) * (j + 1) ^ 2 := by
          nlinarith only [hb, h₂]
        have hB := Nat.mul_le_mul_left B hbj
        have htotal : j * j + B * (b + 2 * j) * j ≤
            (1 + B * (b + 2)) * (j + 1) ^ 2 := by nlinarith only [hj₂, hB]
        have hC : 1 + B * (b + 2) ≤ (B + 1) * (b + 3) := by nlinarith
        exact htotal.trans (Nat.mul_le_mul_right _ hC)
  let d : ℕ → ℕ → ℕ := fun r j => (shiftedHankel Φ (a + r) j).natAbs
  have hzero : ∀ r, r ≤ b - a → d r 0 ≤ 1 := by
    intro r _
    simp [d, shiftedHankel]
  have hdleft : ∀ j, d 0 j ≤ M := by simpa [d] using hleft
  have hdright : ∀ j, d (b - a) j ≤ M := by
    have hn : a + (b - a) = b := Nat.add_sub_of_le hab
    simpa [d, hn] using hright
  have hdstep : ∀ r j, 0 < r → r < b - a → 0 < j →
      d r j ^ 2 ≤ d (r - 1) j * d (r + 1) j +
        d (r - 1) (j + 1) * d (r + 1) (j - 1) := by
    intro r j hr hrL hj
    have hidx₁ : a + (r - 1) + 1 = a + r := by omega
    have hidx₂ : a + (r - 1) + 2 = a + (r + 1) := by omega
    have hj₁ : j - 1 + 1 = j := by omega
    have hj₂ : j - 1 + 2 = j + 1 := by omega
    have heq := MetallicHankelUnboundedJacobi.hankel_jacobi Φ (a + (r - 1)) (j - 1)
    rw [hidx₁, hidx₂, hj₁, hj₂] at heq
    have hbound := Int.natAbs_sub_le
      (shiftedHankel Φ (a + (r - 1)) j * shiftedHankel Φ (a + (r + 1)) j)
      (shiftedHankel Φ (a + (r - 1)) (j + 1) *
        shiftedHankel Φ (a + (r + 1)) (j - 1))
    rw [← heq, Int.natAbs_pow] at hbound
    simpa only [Int.natAbs_mul, d] using hbound
  have hdgrowth : ∀ r j, r ≤ b - a →
      d r j ≤ 2 ^ (((B + 1) * (b + 3)) * (j + 1) ^ 2) := by
    intro r j hr
    exact hdet (a + r) j (by omega)
  have hstrip : ∀ (L M C : ℕ) (d : ℕ → ℕ → ℕ), 1 ≤ M →
      (∀ r, r ≤ L → d r 0 ≤ 1) →
      (∀ j, d 0 j ≤ M) → (∀ j, d L j ≤ M) →
      (∀ r j, 0 < r → r < L → 0 < j →
        d r j ^ 2 ≤ d (r - 1) j * d (r + 1) j +
          d (r - 1) (j + 1) * d (r + 1) (j - 1)) →
      (∀ r j, r ≤ L → d r j ≤ 2 ^ (C * (j + 1) ^ 2)) →
      ∀ r j, r ≤ L → d r j < 2 ^ (Nat.log2 M + 2 * r * (L - r) + 1) := by
    intro L M C d hM hzero hleft hright hstep hgrowth
    classical
    let U : ℕ → ℕ → ℕ := fun r N =>
      max ((Finset.range (N + 1)).sup (d r)) 1
    have hUpos : ∀ r N, 1 ≤ U r N := by
      intro r N
      exact le_max_right _ _
    have hU : ∀ r N j, j ≤ N → d r j ≤ U r N := by
      intro r N j hj
      exact (Finset.le_sup (Finset.mem_range.mpr (by omega))).trans (le_max_left _ _)
    have hUbound : ∀ r N K, 1 ≤ K → (∀ j, j ≤ N → d r j ≤ K) → U r N ≤ K := by
      intro r N K hK h
      exact max_le (Finset.sup_le (fun j hj => h j (by simpa using hj))) hK
    have hUleft : ∀ N, U 0 N ≤ M := fun N => hUbound 0 N M hM (fun j _ => hleft j)
    have hUright : ∀ N, U L N ≤ M := fun N => hUbound L N M hM (fun j _ => hright j)
    have hUstep : ∀ r N, 0 < r → r < L →
        U r N ^ 2 ≤ 2 * U (r - 1) (N + 1) * U (r + 1) (N + 1) := by
      intro r N hr hrL
      by_cases hs : (Finset.range (N + 1)).sup (d r) ≤ 1
      · have heq : U r N = 1 := max_eq_right hs
        rw [heq]
        have h₁ := hUpos (r - 1) (N + 1)
        have h₂ := hUpos (r + 1) (N + 1)
        nlinarith
      · obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup (Finset.range (N + 1))
          (by simp) (d r)
        have hjN : j ≤ N := by simpa using hj
        have hmax : U r N = d r j := by
          dsimp [U]
          rw [max_eq_left (by omega), heq]
        have hjpos : 0 < j := by
          by_contra h
          have hj0 : j = 0 := by omega
          have hz := hzero r (by omega)
          rw [hj0] at heq
          omega
        have h₁ := Nat.mul_le_mul (hU (r - 1) (N + 1) j (by omega))
          (hU (r + 1) (N + 1) j (by omega))
        have h₂ := Nat.mul_le_mul (hU (r - 1) (N + 1) (j + 1) (by omega))
          (hU (r + 1) (N + 1) (j - 1) (by omega))
        have ht := hstep r j hr hrL hjpos
        rw [hmax]
        nlinarith
    have hUgrowth : ∀ r N, r ≤ L → U r N ≤ 2 ^ (C * (N + 1) ^ 2) := by
      intro r N hr
      apply hUbound r N _ (by
        have hp : 0 < 2 ^ (C * (N + 1) ^ 2) := Nat.pow_pos (by decide)
        omega)
      intro j hj
      calc
        d r j ≤ 2 ^ (C * (j + 1) ^ 2) := hgrowth r j hr
        _ ≤ 2 ^ (C * (N + 1) ^ 2) := by gcongr; omega
    have hlogs : ∀ r N, 0 < r → r < L →
        2 * Nat.log2 (U r N) ≤
          Nat.log2 (U (r - 1) (N + 1)) + Nat.log2 (U (r + 1) (N + 1)) + 3 := by
      intro r N hr hrL
      have h₀ := (Nat.log2_eq_iff (n := U r N) (by have := hUpos r N; omega)).1 rfl
      have h₁ := (Nat.log2_eq_iff (n := U (r - 1) (N + 1))
        (by have := hUpos (r - 1) (N + 1); omega)).1 rfl
      have h₂ := (Nat.log2_eq_iff (n := U (r + 1) (N + 1))
        (by have := hUpos (r + 1) (N + 1); omega)).1 rfl
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1
      calc
        2 ^ (2 * Nat.log2 (U r N)) = (2 ^ Nat.log2 (U r N)) ^ 2 := by
          rw [Nat.mul_comm, pow_mul]
        _ ≤ U r N ^ 2 := Nat.pow_le_pow_left h₀.1 2
        _ ≤ 2 * U (r - 1) (N + 1) * U (r + 1) (N + 1) := hUstep r N hr hrL
        _ ≤ 2 * 2 ^ (Nat.log2 (U (r - 1) (N + 1)) + 1) *
            2 ^ (Nat.log2 (U (r + 1) (N + 1)) + 1) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 2 h₁.2.le) h₂.2.le
        _ = 2 ^ (Nat.log2 (U (r - 1) (N + 1)) +
            Nat.log2 (U (r + 1) (N + 1)) + 3) := by
          simp only [pow_add, pow_one]
          ring
    let u : ℕ → ℕ → ℚ := fun r N =>
      (Nat.log2 (U r N) : ℚ) - (Nat.log2 M : ℚ) - 2 * (r : ℚ) * ((L : ℚ) - r)
    have huleft : ∀ N, u 0 N ≤ 0 := by
      intro N
      have hlog : Nat.log2 (U 0 N) ≤ Nat.log2 M := by
        apply (Nat.le_log2 (by omega : M ≠ 0)).2
        exact ((Nat.le_log2 (by have := hUpos 0 N; omega)).1 le_rfl).trans (hUleft N)
      have hlogq : (Nat.log2 (U 0 N) : ℚ) ≤ Nat.log2 M := by exact_mod_cast hlog
      simpa [u] using sub_nonpos.mpr hlogq
    have huright : ∀ N, u L N ≤ 0 := by
      intro N
      have hlog : Nat.log2 (U L N) ≤ Nat.log2 M := by
        apply (Nat.le_log2 (by omega : M ≠ 0)).2
        exact ((Nat.le_log2 (by have := hUpos L N; omega)).1 le_rfl).trans (hUright N)
      simpa [u] using (show (Nat.log2 (U L N) : ℚ) ≤ Nat.log2 M by exact_mod_cast hlog)
    have hustep : ∀ r N, 0 < r → r < L →
        2 * u r N ≤ u (r - 1) (N + 1) + u (r + 1) (N + 1) := by
      intro r N hr hrL
      have hlog : (2 : ℚ) * Nat.log2 (U r N) ≤
          Nat.log2 (U (r - 1) (N + 1)) + Nat.log2 (U (r + 1) (N + 1)) + 3 := by
        exact_mod_cast hlogs r N hr hrL
      have hcast : ((r - 1 : ℕ) : ℚ) = (r : ℚ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ r)]; norm_num
      dsimp [u]
      rw [hcast, Nat.cast_add, Nat.cast_one]
      nlinarith
    have hugrowth : ∀ r N, r ≤ L → u r N ≤ (C : ℚ) * (N + 1 : ℕ) ^ 2 := by
      intro r N hr
      have hlog : Nat.log2 (U r N) ≤ C * (N + 1) ^ 2 := by
        apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1
        exact ((Nat.le_log2 (by have := hUpos r N; omega)).1 le_rfl).trans
          (hUgrowth r N hr)
      have hlogq : (Nat.log2 (U r N) : ℚ) ≤ (C : ℚ) * (N + 1 : ℕ) ^ 2 := by
        exact_mod_cast hlog
      have hrq : (r : ℚ) ≤ L := by exact_mod_cast hr
      have h0 : 0 ≤ (r : ℚ) * ((L : ℚ) - r) := by positivity
      dsimp [u]
      have hM0 : (0 : ℚ) ≤ Nat.log2 M := by positivity
      linarith
    have hmaximum : ∀ (L : ℕ) (u : ℕ → ℕ → ℚ) (C : ℚ), 0 ≤ C →
        (∀ N, u 0 N ≤ 0) → (∀ N, u L N ≤ 0) →
        (∀ r N, 0 < r → r < L →
          2 * u r N ≤ u (r - 1) (N + 1) + u (r + 1) (N + 1)) →
        (∀ r N, r ≤ L → u r N ≤ C * (N + 1 : ℕ) ^ 2) →
        ∀ r N, r ≤ L → u r N ≤ 0 := by
      intro L u C hC hleft hright hstep hgrowth r N hr
      by_cases hr0 : r = 0
      · subst r
        exact hleft N
      by_cases hrL : r = L
      · subst r
        exact hright N
      have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      have hrlt : r < L := lt_of_le_of_ne hr hrL
      have hL : 2 ≤ L := by omega
      have hLq : (2 : ℚ) ≤ L := by exact_mod_cast hL
      let D : ℚ := (L : ℚ) ^ 2 + 1
      let c : ℚ := 1 / D
      let ρ : ℚ := 1 - c
      let w : ℕ → ℚ := fun s => (s : ℚ) * ((L : ℚ) - s)
      have hD : 1 < D := by dsimp [D]; nlinarith
      have hDpos : 0 < D := by linarith
      have hc : 0 < c := by dsimp [c]; exact div_pos (by norm_num) hDpos
      have hc1 : c < 1 := by dsimp [c]; exact (div_lt_iff₀ hDpos).2 (by simpa using hD)
      have hρ : 0 < ρ := by dsimp [ρ]; linarith
      have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
      have hw : ∀ s, s ≤ L → 0 ≤ w s := by
        intro s hs
        dsimp [w]
        have hs' : (s : ℚ) ≤ L := by exact_mod_cast hs
        positivity
      have hw1 : ∀ s, 0 < s → s < L → 1 ≤ w s := by
        intro s hs hsL
        have hs1 : (1 : ℚ) ≤ s := by exact_mod_cast hs
        have hsL1 : (s : ℚ) + 1 ≤ L := by exact_mod_cast hsL
        dsimp [w]
        nlinarith
      have hwD : ∀ s, s ≤ L → w s ≤ D := by
        intro s hs
        have hs0 : (0 : ℚ) ≤ s := by positivity
        have hsL : (s : ℚ) ≤ L := by exact_mod_cast hs
        dsimp [w, D]
        nlinarith [sq_nonneg ((L : ℚ) - s), sq_nonneg (s : ℚ)]
      have hweight : ∀ s, 0 < s → s < L →
          w (s - 1) + w (s + 1) ≤ 2 * ρ * w s := by
        intro s hs hsL
        have hs0 : s ≠ 0 := by omega
        have hcast : ((s - 1 : ℕ) : ℚ) = (s : ℚ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ s)]; norm_num
        have heq : w (s - 1) + w (s + 1) = 2 * w s - 2 := by
          dsimp [w]
          rw [hcast, Nat.cast_add, Nat.cast_one]
          ring
        have hcw : c * w s ≤ 1 := by
          dsimp [c]
          calc
            1 / D * w s = w s / D := by ring
            _ ≤ 1 := (div_le_iff₀ hDpos).2 (by simpa using hwD s (by omega))
        rw [heq]
        dsimp [ρ]
        nlinarith
      have hiter : ∀ t s T, s ≤ L →
          u s T ≤ C * (T + t + 1 : ℕ) ^ 2 * ρ ^ t * w s := by
        intro t
        induction t with
        | zero =>
          intro s T hs
          by_cases hs0 : s = 0
          · subst s
            simpa [w] using hleft T
          by_cases hsL : s = L
          · subst s
            simpa [w] using hright T
          have hws : 1 ≤ w s := hw1 s (by omega) (by omega)
          have hbound := hgrowth s T hs
          simp only [Nat.add_zero, pow_zero, mul_one]
          calc
            u s T ≤ C * (T + 1 : ℕ) ^ 2 := hbound
            _ ≤ C * (T + 1 : ℕ) ^ 2 * w s := by
              exact le_mul_of_one_le_right (by positivity) hws
        | succ t ih =>
          intro s T hs
          by_cases hs0 : s = 0
          · subst s
            simpa [w] using hleft T
          by_cases hsL : s = L
          · subst s
            simpa [w] using hright T
          have hspos : 0 < s := by omega
          have hslt : s < L := by omega
          have h₁ := ih (s - 1) (T + 1) (by omega)
          have h₂ := ih (s + 1) (T + 1) (by omega)
          have htw := hweight s hspos hslt
          have hfactor : 0 ≤ C * (T + t + 2 : ℕ) ^ 2 * ρ ^ t := by positivity
          have hn : T + 1 + t + 1 = T + t + 2 := by omega
          rw [hn] at h₁ h₂
          have hsum := mul_le_mul_of_nonneg_left htw hfactor
          have hrec := hstep s T hspos hslt
          have hn' : T + (t + 1) + 1 = T + t + 2 := by omega
          rw [hn', show ρ ^ (t + 1) = ρ ^ t * ρ from pow_succ ρ t]
          nlinarith
      by_contra hnot
      have hu : 0 < u r N := lt_of_not_ge hnot
      have hwr : 0 < w r := lt_of_lt_of_le (by norm_num) (hw1 r hrpos hrlt)
      have harch : ∀ x : ℚ, ∃ m : ℕ, x < m := by
        intro x
        refine ⟨x.num.natAbs + 1, ?_⟩
        have hn : (x.num : ℚ) ≤ x.num.natAbs := by
          have h : (x.num : ℚ) ≤ ((x.num.natAbs : ℤ) : ℚ) :=
            (Int.cast_le (R := ℚ)).2 (Int.le_natAbs (a := x.num))
          simpa only [Int.cast_natCast] using h
        have hd : (1 : ℚ) ≤ x.den := by exact_mod_cast x.den_pos
        conv_lhs => rw [← Rat.num_div_den x]
        apply (div_lt_iff₀ (by exact_mod_cast x.den_pos : (0 : ℚ) < x.den)).2
        push_cast
        have habs : (0 : ℚ) ≤ x.num.natAbs := by positivity
        nlinarith
      obtain ⟨m₀, hm₀⟩ := harch
        (C * (N + 4 : ℕ) ^ 2 * w r / (u r N * c ^ 3))
      let m : ℕ := m₀ + 1
      have hm : 1 ≤ m := by dsimp [m]; omega
      have hmq : (1 : ℚ) ≤ m := by exact_mod_cast hm
      have hmpos : (0 : ℚ) < m := by linarith
      have hlarge : C * (N + 4 : ℕ) ^ 2 * w r < u r N * (m : ℚ) * c ^ 3 := by
        have hden : 0 < u r N * c ^ 3 := by positivity
        have hlt : C * (N + 4 : ℕ) ^ 2 * w r / (u r N * c ^ 3) < (m : ℚ) := by
          have hm₀m : (m₀ : ℚ) < m := by dsimp [m]; simp
          exact hm₀.trans hm₀m
        have hmul := (div_lt_iff₀ hden).1 hlt
        nlinarith
      have hbern : (m : ℚ) * c ≤ (1 + c) ^ m := by
        have h := Finset.single_le_sum (s := Finset.range (m + 1)) (a := 1)
          (f := fun i => c ^ i * (1 : ℚ) ^ (m - i) * (m.choose i : ℚ))
          (fun i _ => by positivity) (Finset.mem_range.mpr (by omega))
        rw [← add_pow c 1] at h
        simpa [Nat.choose_one_right, add_comm, mul_comm] using h
      have hdecay : ρ ^ (3 * m) * ((m : ℚ) ^ 3 * c ^ 3) ≤ 1 := by
        have hbasic : ρ * (1 + c) ≤ 1 := by dsimp [ρ]; nlinarith [sq_nonneg c]
        have hp := pow_le_pow_left₀ (by positivity : 0 ≤ ρ * (1 + c)) hbasic (3 * m)
        have hb := pow_le_pow_left₀ (by positivity : 0 ≤ (m : ℚ) * c) hbern 3
        have hb' : (m : ℚ) ^ 3 * c ^ 3 ≤ (1 + c) ^ (3 * m) := by
          rw [mul_pow] at hb
          simpa [pow_mul, Nat.mul_comm] using hb
        calc
          ρ ^ (3 * m) * ((m : ℚ) ^ 3 * c ^ 3)
            ≤ ρ ^ (3 * m) * (1 + c) ^ (3 * m) := by gcongr
          _ = (ρ * (1 + c)) ^ (3 * m) := (mul_pow _ _ _).symm
          _ ≤ 1 := by simpa using hp
      have hN : ((N + 3 * m + 1 : ℕ) : ℚ) ≤ (m : ℚ) * (N + 4 : ℕ) := by
        push_cast
        have hN0 : (0 : ℚ) ≤ N := by positivity
        nlinarith
      have hNsq := pow_le_pow_left₀ (by positivity) hN 2
      have hterminal := hiter (3 * m) r N hr
      have hterminal' :
          u r N ≤ C * (m : ℚ) ^ 2 * (N + 4 : ℕ) ^ 2 * ρ ^ (3 * m) * w r := by
        calc
          u r N ≤ C * (N + 3 * m + 1 : ℕ) ^ 2 * ρ ^ (3 * m) * w r := hterminal
          _ ≤ C * (m : ℚ) ^ 2 * (N + 4 : ℕ) ^ 2 * ρ ^ (3 * m) * w r := by
            rw [mul_pow] at hNsq
            have hmul := mul_le_mul_of_nonneg_left hNsq hC
            have hmul' := mul_le_mul_of_nonneg_right hmul
              (show 0 ≤ ρ ^ (3 * m) * w r by positivity)
            simpa [mul_assoc] using hmul'
      have hscale : 0 < (m : ℚ) ^ 3 * c ^ 3 := by positivity
      have hscaled := mul_le_mul_of_nonneg_right hterminal' (le_of_lt hscale)
      have hlast := mul_le_mul_of_nonneg_left hdecay
        (show 0 ≤ C * (m : ℚ) ^ 2 * (N + 4 : ℕ) ^ 2 * w r by positivity)
      have hstrict := mul_lt_mul_of_pos_left hlarge (show 0 < (m : ℚ) ^ 2 by positivity)
      nlinarith
    intro r j hr
    have hu := hmaximum L u C (by positivity) huleft huright hustep hugrowth r j hr
    have hlog : Nat.log2 (U r j) ≤ Nat.log2 M + 2 * r * (L - r) := by
      have hcast : ((L - r : ℕ) : ℚ) = (L : ℚ) - r := Nat.cast_sub hr
      dsimp [u] at hu
      have hq : (Nat.log2 (U r j) : ℚ) ≤
          Nat.log2 M + 2 * (r : ℚ) * (L - r : ℕ) := by rw [hcast]; linarith
      exact_mod_cast hq
    have hup : U r j < 2 ^ (Nat.log2 M + 2 * r * (L - r) + 1) := by
      apply (Nat.log2_lt (by have := hUpos r j; omega)).1
      omega
    exact lt_of_le_of_lt (hU r j j le_rfl) hup
  intro ℓ j ha hb
  have hr : ℓ - a ≤ b - a := by omega
  have hn : a + (ℓ - a) = ℓ := Nat.add_sub_of_le ha
  have hn' : b - a - (ℓ - a) = b - ℓ := by omega
  have hbound := hstrip (b - a) M ((B + 1) * (b + 3)) d hM
    hzero hdleft hdright hdstep hdgrowth (ℓ - a) j hr
  simpa only [d, hn, hn'] using hbound

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelUnboundedStrip
