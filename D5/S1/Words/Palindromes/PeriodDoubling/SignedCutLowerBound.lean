/- GID: D5/S1/Words/Palindromes/PeriodDoubling/SignedCutLowerBound
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/SignedCutLowerBound
   mirror-E: none(waiver:dyadic-cut-potential-estimate)
   anchors: []
   utility: none
   digest: Signed binary weight bounds every actual period-doubling prefix palindromic length. -/

/-
proof_shape: content (palindromic_suffix_signed_bound)
escape_witness: The dyadic estimate across short and long palindrome centers, including radius two.
admission_basis: escape-witness
Direct frozen dependencies: none; the imported period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.DyadicSignedWeight
import D5.S1.Words.Palindromes.PeriodDoubling.OddPalindromeRadius
import D5.S1.Words.Palindromes.PeriodDoubling.EvenPalindrome
import D5.S1.Words.Palindromes.PeriodDoubling.PalindromicLength

set_option autoImplicit false

namespace D5.S1.Words.Palindromes.PeriodDoubling

set_option maxHeartbeats 2000000 in
-- The estimate handles all dyadic scales and both odd-palindrome radius regimes.
/-- Every palindromic suffix cut is Lipschitz for the signed-weight potential. -/
theorem palindromic_suffix_signed_bound :
    (∀ n j : ℕ, j < n →
      List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i))) →
      signedWeight (((n+1)/2 : ℕ) : ℤ) ≤ signedWeight (((j+1)/2 : ℕ) : ℤ)+1) ∧
    (∀ n : ℕ, signedWeight (((n+1)/2 : ℕ) : ℤ) ≤
      PL (List.ofFn (fun i : Fin n => u_pd i))) := by
  have center (r U R : ℕ) (ho : U % 2 = 1) (hR : R < 2 ^ r * U)
    (hbound : R < if U = 1 then 2 ^ r else
      if max (padicValNat 2 (U - 1)) (padicValNat 2 (U + 1)) % 2 = 0 then
        2 ^ r else 3 * 2 ^ r) :
    signedWeight (((2 ^ r * U + R + 1) / 2 : ℕ) : ℤ) ≤
      signedWeight (((2 ^ r * U - R - 1 + 1) / 2 : ℕ) : ℤ) + 1 := by
    have geometry :
        (∀ (h V u : ℕ), V % 2 = 1 → u ≤ 2 ^ h →
          signedWeight ((V : ℤ) * 2 ^ h + u) ≤
            signedWeight ((V : ℤ) * 2 ^ h - u) + 1) ∧
        (∀ (h b u v : ℕ) (V : ℤ), b + 2 ≤ h →
          u ≤ 2 * 2 ^ b → v ≤ 2 * 2 ^ b →
          (u + 2 ^ b = v ∨ v + 2 ^ b = u) →
          signedWeight (V * 2 ^ h + u) ≤ signedWeight (V * 2 ^ h - v) + 1) := by
      obtain ⟨hzero, hone, hneg, htri, heven, hodd⟩ := signed_weight_arithmetic
      have power (h : ℕ) : signedWeight ((2 : ℤ) ^ h) = 1 := by
        induction h with
        | zero => simpa using hone
        | succ h ih =>
          rw [pow_succ, mul_comm, heven, ih]
      have adjacent (x : ℤ) :
          signedWeight x ≤ signedWeight (x + 1) + 1 ∧
            signedWeight (x + 1) ≤ signedWeight x + 1 := by
        have ha := htri x 1
        have hb := htri (x + 1) (-1)
        have hn := hneg 1
        simp only [hone] at ha hn
        have he : x + 1 + -1 = x := by omega
        rw [he, hn] at hb
        exact ⟨hb, ha⟩
      have complement (h u : ℕ) (hu : u ≤ 2 ^ h) :
          signedWeight (u : ℤ) ≤ 1 + signedWeight ((2 ^ h - u : ℕ) : ℤ) := by
        have hc : (u : ℤ) = (2 : ℤ) ^ h + -((2 ^ h - u : ℕ) : ℤ) := by
          norm_cast
          omega
        have ht := htri ((2 : ℤ) ^ h) (-((2 ^ h - u : ℕ) : ℤ))
        rw [← hc, power, hneg] at ht
        exact ht
      have reflect_succ (h u : ℕ) (hu : u ≤ 2 ^ h) :
          signedWeight ((2 ^ (h + 1) - u : ℕ) : ℤ) =
            1 + min (signedWeight ((2 ^ h - u : ℕ) : ℤ)) (signedWeight (u : ℤ)) := by
        have hs := signed_weight_dyadic_split h 1 (2 ^ h - u) (by omega)
        have hp2 : signedWeight (2 : ℤ) = 1 := by
          simpa using power 1
        have he : (((2 ^ (h + 1) - u : ℕ) : ℤ)) =
            (2 : ℤ) ^ h + ((2 ^ h - u : ℕ) : ℤ) := by
          have hn : 2 ^ (h + 1) - u = 2 ^ h + (2 ^ h - u) := by
            rw [pow_succ]
            omega
          rw [hn, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
        simp only [one_mul, hone, Int.reduceAdd, hp2] at hs
        have hc : 2 ^ h - (2 ^ h - u) = u := by omega
        rw [hc] at hs
        rw [he, hs]
        omega
      have half (h u : ℕ) (hu : 2 * u ≤ 2 ^ h) :
          signedWeight (u : ℤ) ≤ signedWeight ((2 ^ h - u : ℕ) : ℤ) := by
        cases h with
        | zero =>
          have he : u = 0 := by norm_num at hu; omega
          subst u
          simp [hzero, hone]
        | succ h =>
          have hu' : u ≤ 2 ^ h := by rw [pow_succ] at hu; omega
          have hc := complement h u hu'
          rw [reflect_succ h u hu']
          omega
      have quarter (h u : ℕ) (hu : 4 * u ≤ 2 ^ h) :
          signedWeight ((2 ^ h - u : ℕ) : ℤ) = 1 + signedWeight (u : ℤ) := by
        cases h with
        | zero =>
          have he : u = 0 := by norm_num at hu; omega
          subst u
          simp [hzero, hone]
        | succ h =>
          have hu' : 2 * u ≤ 2 ^ h := by rw [pow_succ] at hu; omega
          have hc := half h u hu'
          rw [reflect_succ h u (by omega)]
          omega
      have quarter_split (h u : ℕ) (M : ℤ) (hu : 4 * u ≤ 2 ^ h) :
          signedWeight (M * 2 ^ h + u) = signedWeight M + signedWeight (u : ℤ) ∧
          signedWeight (M * 2 ^ h - u) = signedWeight M + signedWeight (u : ℤ) := by
        have hu' : u ≤ 2 ^ h := by omega
        have hq := quarter h u hu
        constructor
        · rw [signed_weight_dyadic_split h M u hu', hq]
          have ha := adjacent M
          omega
        · have hs := signed_weight_dyadic_split h (M - 1) (2 ^ h - u) (by omega)
          have he : (M - 1) * 2 ^ h + ((2 ^ h - u : ℕ) : ℤ) = M * 2 ^ h - u := by
            rw [Nat.cast_sub hu', Nat.cast_pow, Nat.cast_ofNat]
            ring
          have hc : 2 ^ h - (2 ^ h - u) = u := by omega
          have hm : M - 1 + 1 = M := by ring
          rw [he, hc, hm, hq] at hs
          have ha := adjacent (M - 1)
          rw [hm] at ha
          rw [hs]
          omega
      have half_minus (h u : ℕ) (M : ℤ) (hu : 2 * u ≤ 2 ^ h) :
          signedWeight M + signedWeight (u : ℤ) ≤ signedWeight (M * 2 ^ h - u) + 1 := by
        have hu' : u ≤ 2 ^ h := by omega
        have hc := half h u hu
        have hs := signed_weight_dyadic_split h (M - 1) (2 ^ h - u) (by omega)
        have he : (M - 1) * 2 ^ h + ((2 ^ h - u : ℕ) : ℤ) = M * 2 ^ h - u := by
          rw [Nat.cast_sub hu', Nat.cast_pow, Nat.cast_ofNat]
          ring
        have hcomp : 2 ^ h - (2 ^ h - u) = u := by omega
        have hm : M - 1 + 1 = M := by ring
        rw [he, hcomp, hm] at hs
        have ha := adjacent (M - 1)
        rw [hm] at ha
        rw [hs]
        omega
      have add_power (h u : ℕ) (hu : u ≤ 2 ^ h) :
          signedWeight (u : ℤ) ≤ signedWeight ((2 : ℤ) ^ h + u) := by
        have hc := complement h u hu
        have hs := signed_weight_dyadic_split h 1 u hu
        have hp2 : signedWeight (2 : ℤ) = 1 := by simpa using power 1
        simp only [one_mul, hone, Int.reduceAdd, hp2] at hs
        rw [hs]
        omega
      constructor
      · intro h V u ho hu
        have hp := signed_weight_dyadic_split h (V : ℤ) u hu
        have hm := signed_weight_dyadic_split h ((V : ℤ) - 1) (2 ^ h - u) (by omega)
        have hcast : ((V : ℤ) - 1) * 2 ^ h + ((2 ^ h - u : ℕ) : ℤ) =
            (V : ℤ) * 2 ^ h - u := by
          rw [Nat.cast_sub hu, Nat.cast_pow, Nat.cast_ofNat]
          ring
        have hc : 2 ^ h - (2 ^ h - u) = u := by omega
        have hv : (V : ℤ) - 1 + 1 = V := by omega
        rw [hcast, hc, hv] at hm
        have hV : V = 2 * (V / 2) + 1 := by omega
        have hplus : (V : ℤ) + 1 = 2 * ((V / 2 : ℕ) + 1) := by
          exact_mod_cast (by omega : V + 1 = 2 * (V / 2 + 1))
        have hminus : (V : ℤ) - 1 = 2 * (V / 2 : ℕ) := by
          have hc : (V : ℤ) = 2 * (V / 2 : ℕ) + 1 := by exact_mod_cast hV
          omega
        have ha := (adjacent (V / 2 : ℕ)).2
        rw [hplus, heven] at hp
        rw [hminus, heven] at hm
        rw [hp, hm]
        omega
      · intro h b u v V hgap hu hv huv
        have ht : 4 * 2 ^ b ≤ 2 ^ h := by
          have he : 4 * 2 ^ b = 2 ^ (b + 2) := by ring
          rw [he]
          exact Nat.pow_le_pow_right (by decide) hgap
        have hdiff : signedWeight (u : ℤ) ≤ signedWeight (v : ℤ) + 1 := by
          rcases huv with he | he
          · have hx : (u : ℤ) = (v : ℤ) + -((2 : ℤ) ^ b) := by
              have hh : (u : ℤ) + (2 : ℤ) ^ b = v := by exact_mod_cast he
              omega
            have hh := htri (v : ℤ) (-((2 : ℤ) ^ b))
            rw [← hx, hneg, power] at hh
            exact hh
          · have hx : (u : ℤ) = (v : ℤ) + (2 : ℤ) ^ b := by exact_mod_cast he.symm
            have hh := htri (v : ℤ) ((2 : ℤ) ^ b)
            rw [← hx, power] at hh
            exact hh
        by_cases he : h = b + 2
        · have ht' : 2 ^ h = 4 * 2 ^ b := by rw [he]; ring
          by_cases huv' : v ≤ u
          · have hv' : v ≤ 2 ^ b := by rcases huv with hh | hh <;> omega
            have hm := (quarter_split h v V (by omega)).2
            have hp := htri (V * 2 ^ h) (u : ℤ)
            have scale (k : ℕ) : signedWeight (V * 2 ^ k) = signedWeight V := by
              induction k with
              | zero => simp
              | succ k ih =>
                have he' : V * 2 ^ (k + 1) = 2 * (V * 2 ^ k) := by ring
                rw [he', heven, ih]
            rw [scale] at hp
            rw [hm]
            omega
          · have hu' : u ≤ 2 ^ b := by rcases huv with hh | hh <;> omega
            have he' : v = 2 ^ b + u := by rcases huv with hh | hh <;> omega
            have hm := half_minus h v V (by omega)
            have hp := (quarter_split h u V (by omega)).1
            have hh := add_power b u hu'
            have hcast : (v : ℤ) = (2 : ℤ) ^ b + u := by exact_mod_cast he'
            rw [← hcast] at hh
            rw [hp]
            omega
        · have ht' : 8 * 2 ^ b ≤ 2 ^ h := by
            have hgap' : b + 3 ≤ h := by omega
            have he' : 8 * 2 ^ b = 2 ^ (b + 3) := by ring
            rw [he']
            exact Nat.pow_le_pow_right (by decide) hgap'
          have hp := (quarter_split h u V (by omega)).1
          have hm := (quarter_split h v V (by omega)).2
          rw [hp, hm]
          omega
    obtain ⟨hzero, hone, hneg, htri, heven, hodd⟩ := signed_weight_arithmetic
    have adjacent (x : ℤ) : signedWeight (x + 1) ≤ signedWeight x + 1 ∧
        signedWeight x ≤ signedWeight (x + 1) + 1 := by
      have h1 := htri x 1
      have h2 := htri (x + 1) (-1)
      rw [hone] at h1
      have hn : signedWeight (-1) = 1 := by rw [hneg, hone]
      have he : x + 1 + -1 = x := by ring
      rw [he, hn] at h2
      exact ⟨h1, h2⟩
    have hu0 : 0 < U := by omega
    have long_form (hshort : 2 ^ r ≤ R) :
        ∃ s V : ℕ, 3 ≤ s ∧ (U = V * 2 ^ s + 1 ∨ U + 1 = V * 2 ^ s) := by
      have hu1 : U ≠ 1 := by intro he; simp [he] at hbound; omega
      let s := max (padicValNat 2 (U - 1)) (padicValNat 2 (U + 1))
      have hsodd : s % 2 = 1 := by
        change R < if U = 1 then 2 ^ r else if s % 2 = 0 then 2 ^ r else 3 * 2 ^ r at hbound
        by_cases he : s % 2 = 0
        · simp [hu1, he] at hbound
          omega
        · omega
      have hs2 : 2 ≤ s := by
        by_cases he : U % 4 = 1
        · have hd : 2 ^ 2 ∣ U - 1 := by norm_num; omega
          have hv := (padicValNat_dvd_iff_le (by omega : U - 1 ≠ 0)).mp hd
          dsimp [s]
          omega
        · have hd : 2 ^ 2 ∣ U + 1 := by norm_num; omega
          have hv := (padicValNat_dvd_iff_le (by omega : U + 1 ≠ 0)).mp hd
          dsimp [s]
          omega
      have hs3 : 3 ≤ s := by omega
      by_cases he : padicValNat 2 (U + 1) ≤ padicValNat 2 (U - 1)
      · have hs : s = padicValNat 2 (U - 1) := max_eq_left he
        have hd : 2 ^ s ∣ U - 1 :=
          (padicValNat_dvd_iff_le (by omega : U - 1 ≠ 0)).mpr (by omega)
        obtain ⟨V, hV⟩ := hd
        refine ⟨s, V, hs3, Or.inl ?_⟩
        rw [mul_comm] at hV
        omega
      · have hs : s = padicValNat 2 (U + 1) := max_eq_right (by omega)
        have hd : 2 ^ s ∣ U + 1 :=
          (padicValNat_dvd_iff_le (by omega : U + 1 ≠ 0)).mpr (by omega)
        obtain ⟨V, hV⟩ := hd
        refine ⟨s, V, hs3, Or.inr ?_⟩
        simpa [mul_comm] using hV
    have hmax : R < 3 * 2 ^ r := by
      split_ifs at hbound <;> omega
    cases r with
    | zero =>
      simp only [pow_zero, one_mul] at hR hbound ⊢
      norm_num only [pow_zero, mul_one] at hmax
      by_cases hsmall : R ≤ 1
      · have hn : (U + R + 1) / 2 = U / 2 + 1 := by omega
        have hj : (U - R - 1 + 1) / 2 = U / 2 := by omega
        rw [hn, hj, Nat.cast_add, Nat.cast_one]
        exact (adjacent (U / 2 : ℕ)).1
      · have hR2 : R = 2 := by omega
        subst R
        obtain ⟨s, V, hs, hV⟩ := long_form (by norm_num)
        have hd : 8 ∣ 2 ^ s := by
          change 2 ^ 3 ∣ 2 ^ s
          exact Nat.pow_dvd_pow 2 hs
        obtain ⟨l, hl⟩ := hd
        have hmod : U % 8 = 1 ∨ U % 8 = 7 := by
          rcases hV with hV | hV
          · left
            rw [hl] at hV
            have he : V * (8 * l) = 8 * (V * l) := by ring
            rw [he] at hV
            omega
          · right
            rw [hl] at hV
            have he : V * (8 * l) = 8 * (V * l) := by ring
            rw [he] at hV
            omega
        have odd_lower (x : ℤ) :
            signedWeight x ≤ signedWeight (2*x+1) ∧
            signedWeight (x+1) ≤ signedWeight (2*x+1) := by
          have hh := adjacent x
          rw [hodd]
          omega
        rcases hmod with hmod | hmod
        · let k := U / 8
          have hk : 1 ≤ k := by dsimp [k]; omega
          have hn : (U + 2 + 1) / 2 = 4*k+2 := by dsimp [k]; omega
          have hj : (U - 2 - 1 + 1) / 2 = 4*k-1 := by dsimp [k]; omega
          rw [hn, hj]
          have hnc : ((4*k+2 : ℕ) : ℤ) = 2*(2*(k:ℤ)+1) := by push_cast; ring
          have hjc : ((4*k-1 : ℕ) : ℤ) = 2*(2*(k:ℤ)-1)+1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 4*k)]; push_cast; ring
          rw [hnc, hjc, heven]
          have hh := (odd_lower (2*(k:ℤ)-1)).2
          have he : 2*(k:ℤ)-1+1 = 2*k := by ring
          rw [he, heven] at hh
          have hn' : signedWeight (2*(k:ℤ)+1) ≤ signedWeight (k:ℤ)+1 := by
            rw [hodd]; omega
          omega
        · let k := U / 8
          have hn : (U + 2 + 1) / 2 = 4*k+5 := by dsimp [k]; omega
          have hj : (U - 2 - 1 + 1) / 2 = 4*k+2 := by dsimp [k]; omega
          rw [hn, hj]
          have hnc : ((4*k+5 : ℕ) : ℤ) = 2*(2*(k:ℤ)+2)+1 := by push_cast; ring
          have hjc : ((4*k+2 : ℕ) : ℤ) = 2*(2*(k:ℤ)+1) := by push_cast; ring
          rw [hnc, hjc, heven, hodd]
          have hh := (odd_lower (k:ℤ)).2
          have he : 2*(k:ℤ)+2 = 2*((k:ℤ)+1) := by ring
          rw [he, heven]
          omega
    | succ k =>
      let T := 2 ^ k
      let t := (R + 1) / 2
      have hT : 0 < T := by dsimp [T]; positivity
      have he : 2 ^ (k + 1) * U = 2 * (U * T) := by dsimp [T]; ring
      have ht : t ≤ U * T := by dsimp [t]; rw [he] at hR; omega
      have hn : (2 ^ (k + 1) * U + R + 1) / 2 = U * T + t := by
        rw [he]; dsimp [t]; omega
      have hj : (2 ^ (k + 1) * U - R - 1 + 1) / 2 = U * T - t := by
        rw [he] at *; dsimp [t]; omega
      rw [hn, hj, Nat.cast_add, Nat.cast_sub ht]
      change signedWeight ((U : ℤ) * (T : ℤ) + t) ≤
        signedWeight ((U : ℤ) * (T : ℤ) - t) + 1
      by_cases hshort : R < 2 ^ (k + 1)
      · have ht' : t ≤ 2 ^ k := by rw [pow_succ] at hshort; dsimp [t]; omega
        simpa [T] using geometry.1 k U t ho ht'
      · have hshort' : 2 ^ (k + 1) ≤ R := by omega
        obtain ⟨s, V, hs, hV⟩ := long_form hshort'
        have htlo : T ≤ t := by rw [pow_succ] at hshort'; dsimp [T, t]; omega
        have hthi : t ≤ 3 * T := by rw [pow_succ] at hmax; dsimp [T, t]; omega
        rcases hV with hV | hV
        · have hcast : (U : ℤ) = (V : ℤ) * 2 ^ s + 1 := by exact_mod_cast hV
          have h1 : (U : ℤ) * T + t = (V : ℤ) * 2 ^ (k + s) + (T + t : ℕ) := by
            rw [hcast, Nat.cast_add]; simp only [T, Nat.cast_pow, Nat.cast_ofNat, pow_add]; ring
          have h2 : (U : ℤ) * T - t = (V : ℤ) * 2 ^ (k + s) - ((t - T : ℕ) : ℤ) := by
            rw [hcast, Nat.cast_sub htlo]; simp only [T, Nat.cast_pow, Nat.cast_ofNat, pow_add]; ring
          rw [h1, h2]
          apply geometry.2 (k + s) (k + 1) (T + t) (t - T) (V : ℤ)
          · omega
          · rw [pow_succ]; dsimp [T] at *; omega
          · rw [pow_succ]; dsimp [T] at *; omega
          · right; rw [pow_succ]; dsimp [T] at *; omega
        · have hcast : (U : ℤ) = (V : ℤ) * 2 ^ s - 1 := by
            have hh : (U : ℤ) + 1 = (V : ℤ) * 2 ^ s := by exact_mod_cast hV
            omega
          have h1 : (U : ℤ) * T + t = (V : ℤ) * 2 ^ (k + s) + ((t - T : ℕ) : ℤ) := by
            rw [hcast, Nat.cast_sub htlo]; simp only [T, Nat.cast_pow, Nat.cast_ofNat, pow_add]; ring
          have h2 : (U : ℤ) * T - t = (V : ℤ) * 2 ^ (k + s) - (t + T : ℕ) := by
            rw [hcast, Nat.cast_add]; simp only [T, Nat.cast_pow, Nat.cast_ofNat, pow_add]; ring
          rw [h1, h2]
          apply geometry.2 (k + s) (k + 1) (t - T) (t + T) (V : ℤ)
          · omega
          · rw [pow_succ]; dsimp [T] at *; omega
          · rw [pow_succ]; dsimp [T] at *; omega
          · left; rw [pow_succ]; dsimp [T] at *; omega
  have cut (n j : ℕ) (hj : j < n)
      (hpal : List.Palindrome (List.ofFn (fun i : Fin (n-j) => u_pd (j+i)))) :
      signedWeight (((n+1)/2 : ℕ) : ℤ) ≤ signedWeight (((j+1)/2 : ℕ) : ℤ)+1 := by
    by_cases heven : (n-j) % 2 = 0
    · let k := (n-j)/2
      have hL : 2*k = n-j := by dsimp [k]; omega
      rw [← hL] at hpal
      have hk := even_palindrome_length j k hpal
      have hL2 : n = j + 2 := by omega
      rw [hL2]
      have he : (j+2+1)/2 = (j+1)/2 + 1 := by omega
      rw [he, Nat.cast_add, Nat.cast_one]
      obtain ⟨_, hone, _, htri, _, _⟩ := signed_weight_arithmetic
      simpa [hone] using htri (((j+1)/2 : ℕ) : ℤ) 1
    · let R := (n-j)/2
      let m := j+R+1
      have hL : 2*R+1 = n-j := by dsimp [R]; omega
      have hm : m ≠ 0 := by dsimp [m]; omega
      obtain ⟨r, U, hU, hdecomp⟩ := Nat.exists_eq_two_pow_mul_odd hm
      have ho : U % 2 = 1 := by obtain ⟨k,hk⟩ := hU; omega
      have hR : R < 2 ^ r * U := by rw [← hdecomp]; dsimp [m]; omega
      have hstart : 2 ^ r * U - R - 1 = j := by rw [← hdecomp]; dsimp [m]; omega
      have hn : 2 ^ r * U + R = n := by rw [← hdecomp]; dsimp [m]; omega
      rw [← hL] at hpal
      have hp : List.Palindrome (List.ofFn (fun i : Fin (2*R+1) =>
          u_pd (2 ^ r * U - R - 1 + i))) := by simpa [hstart] using hpal
      have hb := (odd_palindrome_radius r U R ho hR).mp hp
      have hc := center r U R ho hR hb
      simpa [hn, hstart] using hc
  refine ⟨cut, ?_⟩
  intro n
  let w := List.ofFn (fun i : Fin n => u_pd i)
  let B : ℕ → ℕ := fun k => signedWeight (((k+1)/2 : ℕ) : ℤ)
  have hzero : B 0 = 0 := by
    dsimp [B]
    exact signed_weight_arithmetic.1
  have hstep (k : ℕ) (hk : k ≤ w.length) (j : ℕ) (hj : j < k)
      (hpal : List.Palindrome ((w.take k).drop j)) : B k ≤ B j+1 := by
    have hlen : w.length = n := by simp [w]
    have heq : (w.take k).drop j = List.ofFn (fun i : Fin (k-j) => u_pd (j+i)) := by
      apply List.ext_getElem
      · simp only [List.length_drop, List.length_take, List.length_ofFn]
        omega
      · intro i hi hi'
        simp only [List.getElem_drop, List.getElem_take, List.getElem_ofFn, w]
    rw [heq] at hpal
    exact cut k j hj hpal
  have hbound := suffix_cut_lower_bound w B hzero hstep n (by simp [w])
  rw [List.take_of_length_le (by simp [w])] at hbound
  exact hbound

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.palindromic_suffix_signed_bound
