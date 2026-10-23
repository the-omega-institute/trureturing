/- GID: D5/S3/Combinatorics/Circle/GeometricSourceRelocation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/GeometricSourceRelocation
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Exact attained width for geometric centered sources by physical-label relocation. -/
import D5.S3.Combinatorics.Circle.SourceWidth

/-! # Geometric source envelopes and low-label relocation -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.GeometricSourceRelocation

open D5.S3.Combinatorics.Circle.SourceWidth

private theorem geometric_quotient (r m : ℕ) (hm : 1 ≤ m) :
    let B : ℕ := 2 ^ m
    (B ^ r - 1) / (B - 1) = ∑ j ∈ Finset.range r, B ^ j := by
  dsimp only
  have hB : 1 < 2 ^ m := by
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hm
    norm_num at this ⊢
    omega
  have he := geom_sum_mul_of_one_le (le_of_lt hB) r
  rw [← he, Nat.mul_div_cancel _ (by omega : 0 < 2 ^ m - 1)]

set_option maxHeartbeats 1200000 in
-- Source range certificates and the indexed block decomposition share one proof.
/-- The geometric source forces the entire physical unsigned-potential envelope. -/
private theorem geometric_source_envelope
    (r m d : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    let B : ℕ := 2 ^ m
    let k : ℕ := r * m + d
    let t : ℕ := (B ^ r - 1) / (B - 1)
    let a : ℕ := d - 1
    let A : ℤ := 2 ^ a
    let N : ℤ := modulus k
    let v : ℕ → ℤ := fun i => centered N ((2 : ℤ) ^ i * (t : ℤ))
    let U : ℕ → ℤ := fun i => v i + if v i < 0 then N else 0
    U a = A * (t : ℤ) ∧
      (∀ i : ℕ, i < a → v i = (2 : ℤ) ^ i * (t : ℤ)) ∧
      (∀ i : ℕ, a ≤ i → i ≤ k - 1 →
        A * (t : ℤ) ≤ U i ∧ U i ≤ A * (B : ℤ) * (t : ℤ)) ∧
      U (a + m) = A * (B : ℤ) * (t : ℤ) ∧
      U (k - 1) = (N + (t : ℤ)) / 2 ∧
      v (k - 1) = ((t : ℤ) - N) / 2 := by
  classical
  dsimp only
  let b : ℤ := 2 ^ m
  let k := r * m + d
  let t : ℕ := ((2 ^ m) ^ r - 1) / (2 ^ m - 1)
  let T : ℤ := t
  let a := d - 1
  let A : ℤ := 2 ^ a
  let N := modulus k
  let S : ℕ → ℤ := fun j => ∑ e ∈ Finset.range j, b ^ e
  let u : ℕ → ℤ := fun j => 2 * A * T - (2 * A - 1) * S j
  let v : ℕ → ℤ := fun i => centered N ((2 : ℤ) ^ i * T)
  let U : ℕ → ℤ := fun i => v i + if v i < 0 then N else 0
  change U a = A * T ∧ (∀ i < a, v i = 2 ^ i * T) ∧
    (∀ i, a ≤ i → i ≤ k - 1 → A * T ≤ U i ∧ U i ≤ A * (2 ^ m : ℕ) * T) ∧
    U (a + m) = A * (2 ^ m : ℕ) * T ∧ U (k - 1) = (N + T) / 2 ∧
    v (k - 1) = (T - N) / 2
  have hb : 2 ≤ b := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hm
    norm_num at this
    exact this
  have hA : 1 ≤ A := one_le_pow₀ (by norm_num)
  have hS (j : ℕ) : S j * (b - 1) = b ^ j - 1 := geom_sum_mul b j
  have hSr : S r = T := by
    have hg : t = ∑ j ∈ Finset.range r, (2 ^ m : ℕ) ^ j := geometric_quotient r m hm
    have hc := congrArg (fun x : ℕ => (x : ℤ)) hg
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] at hc
    exact hc.symm
  have hS0 (j : ℕ) : 0 ≤ S j := Finset.sum_nonneg (fun _ _ => pow_nonneg (by omega) _)
  have hmono {i j : ℕ} (hij : i ≤ j) : S i ≤ S j := by
    have hp := pow_le_pow_right₀ (by omega : 1 ≤ b) hij
    have hi := hS i
    have hj := hS j
    nlinarith
  have hS1 : S 1 = 1 := by simp [S]
  have hT : 1 ≤ T := by have := hmono hr; rw [hS1, hSr] at this; exact this
  have hT0 : 0 ≤ T := by omega
  have hA0 : 0 ≤ A := by omega
  have hAT0 : 0 ≤ A * T := mul_nonneg hA0 hT0
  have hAT1 : 1 ≤ A * T := by nlinarith
  have ht : T * (b - 1) = b ^ r - 1 := by rw [← hSr]; exact hS r
  have hshort (j : ℕ) (hj : j < r) : 2 * S j ≤ T - 1 := by
    have hrec : S (j + 1) = b * S j + 1 := by
      dsimp [S]
      rw [Finset.sum_range_succ]
      have := hS j
      dsimp [S] at this
      nlinarith
    have hle := hmono (show j + 1 ≤ r by omega)
    rw [hrec, hSr] at hle
    have := mul_nonneg (show 0 ≤ b - 2 by omega) (hS0 j)
    nlinarith
  have hp : (2 : ℤ) ^ (r * m) = b ^ r := by simp [b, ← pow_mul, Nat.mul_comm]
  have hN : N = 2 * A * b ^ r - 1 := by
    dsimp [N, modulus, k]
    rw [show r * m + d = (a + r * m) + 1 by dsimp [a]; omega,
      pow_succ, pow_add, hp]
    dsimp [A]
    ring
  have hNpos : 0 < N := by have := pow_pos (by omega : 0 < b) r; nlinarith
  have hN2 : N = 2 * (A * b ^ r) - 1 := by rw [hN]; ring
  have hodd : N % 2 = 1 := by omega
  have htop : A * b * T < N := by
    have hn := mul_nonneg hAT0 (show 0 ≤ b - 2 by omega)
    nlinarith [ht]
  have hAt : A * T ≤ N / 2 := by
    have htmax : T ≤ b ^ r - 1 := by nlinarith [mul_nonneg hT0 (show 0 ≤ b - 2 by omega)]
    have hh := mul_le_mul_of_nonneg_left htmax hA0
    nlinarith [Int.emod_add_mul_ediv N 2,
      Int.emod_nonneg N (by decide : (2 : ℤ) ≠ 0),
      Int.emod_lt_of_pos N (by decide : (0 : ℤ) < 2)]
  have hU (i : ℕ) : U i = ((2 : ℤ) ^ i * T) % N := by
    have hv := centered_bounds hNpos hodd ((2 : ℤ) ^ i * T)
    change -(N / 2) ≤ v i ∧ v i ≤ N / 2 at hv
    have hn := Int.emod_add_mul_ediv N 2
    have hmod := centered_mod N ((2 : ℤ) ^ i * T)
    change v i % N = _ at hmod
    have hu0 : 0 ≤ U i := by dsimp only [U]; split_ifs <;> omega
    have huN : U i < N := by dsimp only [U]; split_ifs <;> omega
    have he : U i % N = ((2 : ℤ) ^ i * T) % N := by
      dsimp only [U]
      split_ifs <;> simpa only [add_zero, Int.add_emod_right] using hmod
    rwa [Int.emod_eq_of_lt hu0 huN] at he
  have hrep (i : ℕ) (R : ℤ) (hR0 : 0 ≤ R) (hRN : R < N)
      (he : ((2 : ℤ) ^ i * T) % N = R % N) : U i = R := by
    rw [hU i, he, Int.emod_eq_of_lt hR0 hRN]
  have hlow (i : ℕ) (hi : i ≤ a) : v i = (2 : ℤ) ^ i * T := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hi
    have hx : 0 ≤ (2 : ℤ) ^ i * T := by positivity
    have hxhi : (2 : ℤ) ^ i * T ≤ N / 2 := by nlinarith [mul_le_mul_of_nonneg_right hp hT0]
    exact centered_unique hNpos hodd (centered_bounds hNpos hodd _)
      ⟨by omega, hxhi⟩ (centered_mod N _)
  have hstart : U a = A * T := by
    dsimp only [U]
    rw [hlow a le_rfl]
    simp only [show ¬ (2 : ℤ) ^ a * T < 0 by change ¬ A * T < 0; omega, ite_false, add_zero]
    rfl
  have hu (j : ℕ) (hj : j < r) : A * T ≤ u j ∧ u j ≤ 2 * A * T := by
    have hq := hshort j hj
    have hL := hS0 j
    have hmul := mul_nonneg hA0 (show 0 ≤ T - 1 - 2 * S j by omega)
    have hmul' := mul_nonneg (show 0 ≤ 2 * A - 1 by omega) hL
    dsimp [u]
    constructor <;> nlinarith
  have hpower (j : ℕ) :
      (2 : ℤ) ^ (a + j * m + 1) * T = N * S j + u j := by
    have hjpow : (2 : ℤ) ^ (j * m) = b ^ j := by simp [b, ← pow_mul, Nat.mul_comm]
    rw [pow_succ, pow_add, hjpow]
    have hj := hS j
    dsimp [u]
    have he : b ^ j * T = b ^ r * S j + T - S j := by
      nlinarith only [congrArg (fun x : ℤ => x * T) hj,
        congrArg (fun x : ℤ => x * S j) ht]
    rw [hN]
    dsimp [A] at *
    linear_combination 2 * 2 ^ a * he
  have hblock (j ell : ℕ) (hj : 1 ≤ j) (hjr : j < r)
      (he1 : 1 ≤ ell) (hem : ell ≤ m) :
      U (a + j * m + ell) = (2 : ℤ) ^ (ell - 1) * u j := by
    have huj := hu j hjr
    have hpell : (2 : ℤ) ^ ell ≤ b := pow_le_pow_right₀ (by norm_num) hem
    have htwo : (2 : ℤ) ^ ell = 2 * 2 ^ (ell - 1) := by
      calc (2 : ℤ) ^ ell = 2 ^ ((ell - 1) + 1) := by congr 1 <;> omega
           _ = 2 * 2 ^ (ell - 1) := by rw [pow_succ]; ring
    have hpow1 : (1 : ℤ) ≤ 2 ^ (ell - 1) := one_le_pow₀ (by norm_num)
    have huj0 : 0 ≤ u j := le_trans hAT0 huj.1
    have hR0 : 0 ≤ (2 : ℤ) ^ (ell - 1) * u j := mul_nonneg (by positivity) huj0
    have hRhi : (2 : ℤ) ^ (ell - 1) * u j ≤ A * b * T := by
      have h1 := mul_le_mul_of_nonneg_right hpell (by omega : 0 ≤ u j)
      have h2 := mul_le_mul_of_nonneg_left huj.2 (by omega : 0 ≤ b)
      rw [htwo] at h1
      nlinarith
    apply hrep _ _ hR0 (lt_of_le_of_lt hRhi htop)
    have hexp : a + j * m + ell = (a + j * m + 1) + (ell - 1) := by omega
    rw [hexp, pow_add, mul_right_comm, hpower j]
    have he : (N * S j + u j) * (2 : ℤ) ^ (ell - 1) =
        (2 : ℤ) ^ (ell - 1) * u j + (S j * 2 ^ (ell - 1)) * N := by ring
    rw [he, Int.add_mul_emod_self_right]
  have hfirst (ell : ℕ) (he : ell ≤ m) : U (a + ell) = A * 2 ^ ell * T := by
    have hpell : (2 : ℤ) ^ ell ≤ b := pow_le_pow_right₀ (by norm_num) he
    have hlo : 0 ≤ A * (2 : ℤ) ^ ell * T := by positivity
    have hhi : A * (2 : ℤ) ^ ell * T ≤ A * b * T := by
      nlinarith [mul_le_mul_of_nonneg_left hpell hAT0]
    apply hrep _ _ hlo (lt_of_le_of_lt hhi htop)
    simp [pow_add, A]
  have henvelope (i : ℕ) (hai : a ≤ i) (hik : i ≤ k - 1) :
      A * T ≤ U i ∧ U i ≤ A * b * T := by
    by_cases hi : i ≤ a + m
    · have he : i = a + (i - a) := by omega
      rw [he, hfirst _ (by omega)]
      have hp1 : (1 : ℤ) ≤ 2 ^ (i - a) := one_le_pow₀ (by norm_num)
      have hp2 : (2 : ℤ) ^ (i - a) ≤ b := pow_le_pow_right₀ (by norm_num) (by omega)
      constructor <;> nlinarith [mul_le_mul_of_nonneg_left hp1 (show 0 ≤ A * T by positivity),
        mul_le_mul_of_nonneg_left hp2 (show 0 ≤ A * T by positivity)]
    · let j := (i - a - 1) / m
      let ell := (i - a - 1) % m + 1
      have hdiv := Nat.mod_add_div (i - a - 1) m
      rw [Nat.mul_comm m] at hdiv
      have hmod := Nat.mod_lt (i - a - 1) (by omega : 0 < m)
      have hj : 1 ≤ j := by
        dsimp only [j]
        apply (Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr
        omega
      have hjr : j < r := by
        dsimp [j]
        apply (Nat.div_lt_iff_lt_mul (by omega : 0 < m)).mpr
        dsimp [k, a] at *
        omega
      have he1 : 1 ≤ ell := by dsimp [ell]; omega
      have hem : ell ≤ m := by dsimp [ell]; omega
      have he : i = a + j * m + ell := by dsimp [j, ell]; omega
      rw [he, hblock j ell hj hjr he1 hem]
      have huj := hu j hjr
      have hp1 : (1 : ℤ) ≤ 2 ^ (ell - 1) := one_le_pow₀ (by norm_num)
      have hp2 : (2 : ℤ) ^ ell ≤ b := pow_le_pow_right₀ (by norm_num) hem
      have htwo : (2 : ℤ) ^ ell = 2 * 2 ^ (ell - 1) := by
        calc (2 : ℤ) ^ ell = 2 ^ ((ell - 1) + 1) := by congr 1 <;> omega
           _ = 2 * 2 ^ (ell - 1) := by rw [pow_succ]; ring
      have h1 := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ u j by omega)
      have h2 := mul_le_mul_of_nonneg_right hp2 (show 0 ≤ u j by omega)
      have h3 := mul_le_mul_of_nonneg_left huj.2 (show 0 ≤ b by omega)
      rw [htwo] at h2
      constructor <;> nlinarith
  have hpeak : U (a + m) = A * b * T := by simpa [b] using hfirst m le_rfl
  have hreturn (j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r) :
      2 * U (a + j * m) = N + u j := by
    have hrec : S j = b * S (j - 1) + 1 := by
      have hs := hS (j - 1)
      have he : S j = S (j - 1) + b ^ (j - 1) := by
        conv_lhs => rw [show j = (j - 1) + 1 by omega]
        exact Finset.sum_range_succ _ _
      nlinarith only [hs, he]
    by_cases hj1 : j = 1
    · rw [hj1, one_mul, hpeak]
      dsimp only [u]
      rw [hS1, hN]
      linear_combination 2 * A * ht
    · have hjprev : 1 ≤ j - 1 := by omega
      have hjrprev : j - 1 < r := by omega
      have he : a + j * m = a + (j - 1) * m + m := by
        have hh : (j - 1) + 1 = j := by omega
        nlinarith
      rw [he, hblock (j - 1) m hjprev hjrprev hm le_rfl]
      have htwo : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
        calc (2 : ℤ) ^ m = 2 ^ ((m - 1) + 1) := by congr 1 <;> omega
             _ = 2 * 2 ^ (m - 1) := by rw [pow_succ]; ring
      have hrecU : b * u (j - 1) = N + u j := by
        dsimp only [u]
        rw [hrec, hN]
        linear_combination 2 * A * ht
      calc 2 * (2 ^ (m - 1) * u (j - 1)) = b * u (j - 1) := by
             rw [← mul_assoc, ← htwo]
           _ = N + u j := hrecU
  have hnegative (j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r) :
      v (a + j * m) = (u j - N) / 2 := by
    have hSj := hmono hjr
    rw [hSr] at hSj
    have huj : T ≤ u j := by
      have hh := mul_nonneg (show 0 ≤ 2 * A - 1 by omega) (show 0 ≤ T - S j by omega)
      dsimp only [u]
      nlinarith only [hh]
    have he := hreturn j hj hjr
    have hv := centered_bounds hNpos hodd ((2 : ℤ) ^ (a + j * m) * T)
    change -(N / 2) ≤ v (a + j * m) ∧ v (a + j * m) ≤ N / 2 at hv
    have hn : v (a + j * m) < 0 := by
      dsimp only [U] at he
      split_ifs at he <;> omega
    dsimp only [U] at he
    rw [if_pos hn] at he
    omega
  have hkidx : k - 1 = a + r * m := by dsimp [k, a]; omega
  have hur : u r = T := by dsimp only [u]; rw [hSr]; ring
  have hend : 2 * U (k - 1) = N + T := by
    rw [hkidx]
    simpa only [hur] using hreturn r hr le_rfl
  have hlast : v (k - 1) = (T - N) / 2 := by
    rw [hkidx]
    simpa only [hur] using hnegative r hr le_rfl

  refine ⟨hstart, fun i hi => hlow i (by omega), ?_, ?_, by omega, hlast⟩
  · intro i hi hk
    simpa only [Nat.cast_pow, Nat.cast_ofNat, b] using henvelope i hi hk
  · simpa only [Nat.cast_pow, Nat.cast_ofNat, b] using hpeak

set_option maxHeartbeats 1600000 in
-- The literal word, integer potential and both attained peaks are checked together.
/-- Relocating the low physical labels gives this geometric source an exact attained width. -/
theorem geometric_source_relocation
    (r m d : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    let B : ℕ := 2 ^ m
    let k : ℕ := r * m + d
    let t : ℕ := (B ^ r - 1) / (B - 1)
    let A : ℤ := 2 ^ (d - 1)
    let C : ℤ := (2 : ℤ) ^ (k - 1) - 1
    let W : ℤ := C - min (A - 1) (((t : ℤ) - 1) / 2)
    let f : Fin k → ℤ := actualSource k t
    let word : List (Fin k) :=
      (((List.finRange k).take (k - 1)).rotate (d - 1)) ++
        (List.finRange k).drop (k - 1)
    word.Perm (List.finRange k) ∧
      W ≤ C ∧
      (∀ n : ℕ, ((word.take n).map f).sum ∈ Set.Icc (0 : ℤ) W) ∧
      (word.map f).sum = 0 ∧
      (∃ n : ℕ, n ≤ k ∧ ((word.take n).map f).sum = W) := by
  classical
  dsimp only
  let B : ℕ := 2 ^ m
  let k := r * m + d
  let t : ℕ := (B ^ r - 1) / (B - 1)
  let a := d - 1
  let A : ℤ := 2 ^ a
  let C : ℤ := (2 : ℤ) ^ (k - 1) - 1
  let T : ℤ := t
  let N := modulus k
  let W := C - min (A - 1) ((T - 1) / 2)
  let f := actualSource k t
  let word := (((List.finRange k).take (k - 1)).rotate a) ++
    (List.finRange k).drop (k - 1)
  let v : ℕ → ℤ := fun i => centered N ((2 : ℤ) ^ i * T)
  let U : ℕ → ℤ := fun i => v i + if v i < 0 then N else 0
  let q := k - 1
  let len := r * m
  let main := List.range' a len
  let low := List.range a
  let order := main ++ low ++ [q]
  change word.Perm (List.finRange k) ∧ W ≤ C ∧
    (∀ n : ℕ, ((word.take n).map f).sum ∈ Set.Icc (0 : ℤ) W) ∧
    (word.map f).sum = 0 ∧ ∃ n : ℕ, n ≤ k ∧ ((word.take n).map f).sum = W
  have hlen : 1 ≤ len := by dsimp [len]; nlinarith
  have hk : 2 ≤ k := by dsimp [k, len] at *; omega
  have hq : a + len = q := by dsimp [a, len, q, k]; omega
  have ham : a + m ≤ q := by dsimp [len] at hlen hq; nlinarith
  have hA : 1 ≤ A := one_le_pow₀ (by norm_num)
  have hB : (2 : ℤ) ≤ B := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hm
    simpa [B] using this
  have hT0 : 0 ≤ T := Int.natCast_nonneg t
  have hTsum : T = ∑ j ∈ Finset.range r, (B : ℤ) ^ j := by
    have hg : t = ∑ j ∈ Finset.range r, B ^ j := geometric_quotient r m hm
    have hc := congrArg (fun x : ℕ => (x : ℤ)) hg
    simpa only [Nat.cast_sum, Nat.cast_pow] using hc
  have ht : T * ((B : ℤ) - 1) = (B : ℤ) ^ r - 1 := by
    rw [hTsum]
    exact geom_sum_mul _ _
  have hT : 1 ≤ T := by
    have hp := pow_le_pow_right₀ (by omega : (1 : ℤ) ≤ B) hr
    rw [pow_one] at hp
    by_contra h
    have hz : T = 0 := by omega
    rw [hz] at ht
    nlinarith
  have hN : N = 2 * C + 1 := by
    dsimp [N, modulus, C]
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    ring
  have hC : 1 ≤ C := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 1 ≤ k - 1 by omega)
    norm_num at hp
    dsimp [C]
    omega
  have hNpos : 0 < N := by omega
  have hodd : N % 2 = 1 := by omega
  have hQ : (2 : ℤ) ^ (k - 1) = A * (B : ℤ) ^ r := by
    rw [show k - 1 = a + r * m by dsimp [k, a]; omega, pow_add]
    congr 1
    simp [B, ← pow_mul, Nat.mul_comm]
  have hM : A * (B : ℤ) * T - A * T = C - (A - 1) := by
    dsimp only [C]
    rw [hQ]
    linear_combination A * ht
  let M := C - (A - 1)
  let L := C - (T - 1) / 2
  have hMW : M ≤ W := by dsimp [M, W]; omega
  have hLW : L ≤ W := by dsimp [L, W]; omega
  have hmax : W = M ∨ W = L := by dsimp [M, L, W]; omega
  have hWC : W ≤ C := by dsimp [W]; omega
  obtain ⟨hstart, hlow, henv, hpeak, hend, hlast⟩ := geometric_source_envelope r m d hr hm hd
  change U a = A * T at hstart
  change (∀ i < a, v i = (2 : ℤ) ^ i * T) at hlow
  change (∀ i, a ≤ i → i ≤ q → A * T ≤ U i ∧ U i ≤ A * (B : ℤ) * T) at henv
  change U (a + m) = A * (B : ℤ) * T at hpeak
  change U q = (N + T) / 2 at hend
  change v q = (T - N) / 2 at hlast
  have hstep (i : ℕ) : v (i + 1) = doubleStep N (v i) := by
    dsimp only [v]
    rw [show (2 : ℤ) ^ (i + 1) * T = 2 * (2 ^ i * T) by rw [pow_succ]; ring]
    exact centered_double hNpos hodd _
  have hpot (i : ℕ) : U (i + 1) - U i = v i := by
    dsimp only [U]
    rw [hstep i]
    exact unsigned_step hNpos hodd (centered_bounds hNpos hodd _)
  have hsum (s n : ℕ) : ((List.range' s n).map v).sum = U (s + n) - U s := by
    have heq : (fun i => v (s + i)) = fun i => U (s + (i + 1)) - U (s + i) := by
      funext i
      simpa only [Nat.add_assoc] using (hpot (s + i)).symm
    rw [List.range'_eq_map_range, List.map_map]
    change ((List.range n).map (fun i => v (s + i))).sum = _
    rw [heq]
    simpa only [Nat.add_zero] using List.sum_range_sub n (fun i => U (s + i))
  have hperm : word.Perm (List.finRange k) := by
    dsimp only [word]
    exact ((List.rotate_perm _ _).append_right _).trans (by rw [List.take_append_drop])
  have horiginal : (List.finRange k).map f = (List.range k).map v := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
      rfl
  have hvalues : word.map f = order.map v := by
    dsimp only [word, order, main, low, q]
    rw [List.map_append, List.map_rotate, List.map_take, List.map_drop, horiginal,
      List.rotate_eq_drop_append_take (by simp; omega)]
    simp only [← List.map_take, ← List.map_drop, ← List.map_append]
    congr 1
    simp only [List.take_range, Nat.min_eq_left (by omega : k - 1 ≤ k),
      Nat.min_eq_left (show a ≤ k - 1 by omega)]
    simp only [List.range_eq_range', List.drop_range', Nat.mul_one, Nat.zero_add]
    rw [show k - 1 - a = len by omega, show k - (k - 1) = 1 by omega]
    simp [List.range'_succ, List.append_assoc]
  have hperiod : U k = U 0 := by
    have he : v k = v 0 := by simpa only [v, N, T, pow_zero, one_mul] using centered_full_period k t
    simp only [U, he]
  have htotal : (word.map f).sum = 0 := by
    rw [hperm.map f |>.sum_eq, horiginal, List.range_eq_range', hsum]
    simp only [Nat.zero_add, hperiod, sub_self]
  have htotalOrder : ((main.map v).sum + (low.map v).sum) + v q = 0 := by
    rw [hvalues] at htotal
    simpa [order, List.map_append, List.sum_append, add_assoc] using htotal
  have hmainSum : (main.map v).sum = U q - A * T := by rw [hsum, hq, hstart]
  have hmain0 : 0 ≤ (main.map v).sum := by
    rw [hmainSum]
    have := henv q (by omega) le_rfl
    omega
  have hlowpos (i : ℕ) (hi : i ∈ low) : 0 ≤ v i := by
    have hi' : i < a := List.mem_range.mp hi
    rw [hlow i hi']
    positivity
  have hlow0 : 0 ≤ (low.map v).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hlowpos i hi
  have hEnd : (main.map v).sum + (low.map v).sum = L := by
    dsimp only [L]
    rw [hlast, hN] at htotalOrder
    omega
  have hEnd0 : 0 ≤ L := by omega
  have hW0 : 0 ≤ W := by omega
  have hsegment : ∀ n s : ℕ, a ≤ s → s + n ≤ q →
      InStrip v W (U s - A * T) (List.range' s n) := by
    intro n
    induction n with
    | zero =>
      intro s has hsq
      have hh := henv s has (by omega)
      simp only [List.range'_zero, InStrip]
      constructor <;> omega
    | succ n ih =>
      intro s has hsq
      have hh := henv s has (by omega)
      rw [List.range'_succ]
      refine ⟨by omega, by omega, ?_⟩
      have hn := ih (s + 1) (by omega) (by omega)
      have hp := hpot s
      convert hn using 1 <;> omega
  have hmain : InStrip v W 0 main := by
    have hh := hsegment len a le_rfl (by omega)
    simpa only [hstart, sub_self] using hh
  have hlowstrip : InStrip v W (main.map v).sum low := by
    apply inStrip_reflect
    apply inStrip_nonpos
    · intro i hi
      have := hlowpos i hi
      omega
    · omega
    · rw [sum_neg_map]
      omega
  have hfinal : InStrip v W ((main.map v).sum + (low.map v).sum) [q] := by
    simp only [InStrip]
    exact ⟨by omega, by omega, by omega, by omega⟩
  have hstrip : InStrip v W 0 order := by
    dsimp only [order]
    rw [List.append_assoc]
    apply inStrip_append hmain
    simpa only [zero_add] using inStrip_append hlowstrip hfinal
  have hprefix (n : ℕ) : ((word.take n).map f).sum = ((order.take n).map v).sum := by
    simp only [List.map_take, hvalues]
  refine ⟨hperm, hWC, ?_, htotal, ?_⟩
  · intro n
    rw [hprefix]
    simpa only [zero_add, Set.mem_Icc] using inStrip_prefix hstrip n
  · rcases hmax with hmax | hmax
    · refine ⟨m, by omega, ?_⟩
      rw [hprefix]
      have ht : order.take m = List.range' a m := by
        dsimp only [order]
        rw [List.append_assoc, List.take_append_of_le_length (by simpa [main] using (show m ≤ len by dsimp [len]; nlinarith))]
        exact List.take_range'_of_length_ge (show m ≤ len by dsimp [len]; nlinarith)
      rw [ht, hsum, hpeak, hstart, hM]
      exact hmax.symm
    · refine ⟨q, by dsimp [q]; omega, ?_⟩
      rw [hprefix]
      have hlength : (main ++ low).length = q := by simp [main, low]; omega
      have ht : order.take q = main ++ low := by
        dsimp only [order]
        conv_lhs => rw [← hlength]
        exact List.take_append_length
      rw [ht, List.map_append, List.sum_append, hEnd, ← hmax]

#print axioms geometric_source_relocation

end D5.S3.Combinatorics.Circle.GeometricSourceRelocation
