/- GID: D5/S3/Combinatorics/Circle/Lattice/FourNegativeLatticePrecedence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/Lattice/FourNegativeLatticePrecedence
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Necessary delta precedence for every actual four-gap source with t=4n+2. -/
import D5.S3.Combinatorics.Circle.Lattice.LatticeChargePrecedence

/-! The unrestricted joint-permutation existence problem remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.Lattice.FourNegativeLatticePrecedence
open SourceWidth PeriodicShorteningArithmetic PeriodicShortening RunFirstEarTransport
open LatticeChargePrecedence
open scoped BigOperators

private abbrev t (n : ℕ) := 4 * n + 2
private abbrev k (n : ℕ) := 2 * t n + 4
private def seed (n : ℕ) := 1 + 2 ^ t n + 2 ^ (t n + 2) + 2 ^ (2 * t n + 2)
private def x (n : ℕ) : ℤ := 2 ^ t n
private def B (n : ℕ) : ℤ := 20 * x n + 5
private def H (n : ℕ) : ℤ := 8 * x n ^ 2 - 10 * x n - 3

private theorem arithmetic (n : ℕ) (hn : 1 ≤ n) :
    64 ≤ x n ∧ (seed n : ℤ) = 4 * x n ^ 2 + 5 * x n + 1 ∧
    modulus (k n) = 16 * x n ^ 2 - 1 ∧
    modulus (k n) / 2 = 8 * x n ^ 2 - 1 ∧
    seed n ≤ 2 ^ (k n - 1) - 1 ∧
    B n ∣ (seed n : ℤ) ∧ B n ∣ modulus (k n) ∧ B n ∣ H n ∧
    0 < H n ∧ H n ≤ modulus (k n) / 2 ∧ modulus (k n) / 2 < H n + B n ∧
    modulus (k n) - 2 * H n = B n ∧ 2 * B n < (seed n : ℤ) + 1 := by
  have hx : 64 ≤ x n := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 6 ≤ t n by dsimp [t]; omega)
    norm_num at hp
    exact hp
  have h2t : (2 : ℤ) ^ (2 * t n) = x n ^ 2 := by
    rw [show 2 * t n = t n * 2 by omega, pow_mul]
    rfl
  have ha : (seed n : ℤ) = 4 * x n ^ 2 + 5 * x n + 1 := by
    simp only [seed, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
    rw [pow_add (2 : ℤ) (t n) 2, pow_add (2 : ℤ) (2 * t n) 2, h2t]
    change 1 + x n + x n * (2 : ℤ) ^ 2 + x n ^ 2 * (2 : ℤ) ^ 2 = _
    ring
  have hN : modulus (k n) = 16 * x n ^ 2 - 1 := by
    change (2 : ℤ) ^ (2 * t n + 4) - 1 = _
    rw [pow_add, h2t]
    ring
  have hC : modulus (k n) / 2 = 8 * x n ^ 2 - 1 := by rw [hN]; omega
  have hpow : (2 : ℤ) ^ (k n - 1) = 8 * x n ^ 2 := by
    rw [show k n - 1 = 2 * t n + 3 by dsimp [k] <;> omega, pow_add (2 : ℤ) (2 * t n) 3, h2t]
    ring
  have hbound : seed n ≤ 2 ^ (k n - 1) - 1 := by
    have hh : (seed n : ℤ) + 1 ≤ (2 : ℤ) ^ (k n - 1) := by rw [ha, hpow]; nlinarith
    have hh' : seed n + 1 ≤ 2 ^ (k n - 1) := by exact_mod_cast hh
    omega
  have hmod : x n % 5 = 4 := by
    have hm : (16 : ℤ) ≡ 1 [ZMOD 5] := by decide
    have hp := hm.pow n
    change (16 : ℤ) ^ n % 5 = 1 ^ n % 5 at hp
    norm_num at hp
    dsimp [x, t]
    rw [pow_add, pow_mul, Int.mul_emod]
    norm_num [hp]
  let r := (x n + 1) / 5
  have hr : x n = 5 * r - 1 := by dsimp [r]; omega
  have hdA : B n ∣ (seed n : ℤ) := by
    refine ⟨r, ?_⟩
    rw [ha]; dsimp [B]; rw [hr]; ring
  have hdN : B n ∣ modulus (k n) := by
    refine ⟨4 * r - 1, ?_⟩
    rw [hN]; dsimp [B]; rw [hr]; ring
  have hdH : B n ∣ H n := by
    refine ⟨2 * r - 1, ?_⟩
    dsimp [H, B]; rw [hr]; ring
  refine ⟨hx, ha, hN, hC, hbound, hdA, hdN, hdH, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try rw [hC]
  all_goals simp only [hN, ha, B, H]
  all_goals nlinarith

private theorem short_period (n i : ℕ) (hn : 1 ≤ n) :
    centered (modulus (k n)) ((2 : ℤ) ^ (i + (t n + 2)) * seed n) =
      centered (modulus (k n)) ((2 : ℤ) ^ i * seed n) := by
  obtain ⟨_, ha, hN, _⟩ := arithmetic n hn
  have hfactor : (2 : ℤ) ^ (t n + 2) * seed n =
      (seed n : ℤ) + modulus (k n) * (x n + 1) := by
    rw [pow_add]
    change (x n * (2 : ℤ) ^ 2) * seed n = _
    rw [ha, hN]
    ring
  apply centered_congr
  rw [pow_add, mul_assoc, hfactor, mul_add]
  have he : (2 : ℤ) ^ i * (modulus (k n) * (x n + 1)) =
      modulus (k n) * ((2 : ℤ) ^ i * (x n + 1)) := by ring
  rw [he, Int.add_mul_emod_self_left]

private theorem first_values (n : ℕ) (hn : 1 ≤ n) :
    actualSource (k n) (seed n) ⟨1, by dsimp [k, t]; omega⟩ = -H n ∧
    actualSource (k n) (seed n) ⟨t n + 3, by dsimp [k, t]; omega⟩ = -H n ∧
    ∀ i : Fin (k n), actualSource (k n) (seed n) i < 0 →
      i.val = 1 ∨ i.val = t n + 1 ∨ i.val = t n + 3 ∨ i.val = k n - 1 := by
  obtain ⟨hx, ha, hN, hC, hbound, _⟩ := arithmetic n hn
  obtain ⟨hpos, hodd⟩ := TwoRunSource.modulus_positive_odd (k n) (by dsimp [k]; omega)
  have hraw (s : ℕ) : (2 : ℤ) ^ (s + 2) * seed n =
      (2 : ℤ) ^ s * B n + modulus (k n) * (2 : ℤ) ^ s := by
    rw [pow_add, ha, hN]; dsimp [B]; ring
  have htwo : (2 : ℤ) * seed n = -H n + modulus (k n) := by
    rw [ha, hN]; dsimp [H]; ring
  have halpha : actualSource (k n) (seed n) ⟨1, by dsimp [k,t]; omega⟩ = -H n := by
    apply centered_unique hpos hodd (centered_bounds hpos hodd _) ?_ ?_
    · rw [hC]; dsimp [H]; constructor <;> nlinarith
    · rw [centered_mod]
      change ((2 : ℤ) * seed n) % _ = _
      rw [htwo, Int.add_emod_right]
  have hgamma : actualSource (k n) (seed n) ⟨t n + 3, by dsimp [k,t]; omega⟩ = -H n := by
    change centered _ ((2 : ℤ) ^ (t n + 3) * _) = _
    rw [show t n + 3 = 1 + (t n + 2) by omega, short_period n 1 hn]
    exact halpha
  have hnonnegative (i : ℕ) (hi : i < t n + 2) (h1 : i ≠ 1) (hlast : i ≠ t n + 1) :
      0 ≤ centered (modulus (k n)) ((2 : ℤ) ^ i * seed n) := by
    by_cases hi0 : i = 0
    · subst i
      have hv : centered (modulus (k n)) (seed n : ℤ) = (seed n : ℤ) := by
        apply centered_unique hpos hodd (centered_bounds hpos hodd _) ?_ (centered_mod _ _)
        rw [hC, ha]; constructor <;> nlinarith
      simp only [pow_zero, one_mul, hv]
      exact Int.natCast_nonneg _
    · have hi2 : 2 ≤ i := by omega
      let s := i - 2
      have hs : i = s + 2 := by dsimp [s]; omega
      have hsp : 4 * (2 : ℤ) ^ s ≤ x n := by
        have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show s + 2 ≤ t n by dsimp [s]; omega)
        simpa [pow_add, x, mul_comm] using hp
      have hBpos : 0 < B n := by dsimp [B]; omega
      have hval0 : 0 ≤ (2 : ℤ) ^ s * B n := by positivity
      have hval : (2 : ℤ) ^ s * B n ≤ modulus (k n) / 2 := by
        have hh := mul_le_mul_of_nonneg_right hsp hBpos.le
        rw [hC]; dsimp [B] at hh
        nlinarith
      have hv : centered (modulus (k n)) ((2 : ℤ) ^ i * seed n) = (2 : ℤ) ^ s * B n := by
        apply centered_unique hpos hodd (centered_bounds hpos hodd _) ⟨by rw [hC]; nlinarith, hval⟩
        rw [centered_mod, hs, hraw, Int.add_mul_emod_self_left]
      rw [hv]; exact hval0
  refine ⟨halpha, hgamma, ?_⟩
  intro i hi
  by_contra hall
  push Not at hall
  by_cases hilow : i.val < t n + 2
  · have hh := hnonnegative i.val hilow hall.1 hall.2.1
    exact (not_lt_of_ge hh) hi
  · have hrem : i.val - (t n + 2) < t n + 2 := by have := i.isLt; dsimp [k] at *; omega
    have hh := hnonnegative (i.val - (t n + 2)) hrem (by omega) (by dsimp [k] at *; omega)
    have he : i.val = (i.val - (t n + 2)) + (t n + 2) := by omega
    unfold actualSource at hi
    rw [he, short_period n _ hn] at hi
    exact (not_lt_of_ge hh) hi

private theorem complete_inventory (n : ℕ) (hn : 1 ≤ n) :
    ∀ i : Fin (k n), actualSource (k n) (seed n) i < 0 ↔
      i.val = 1 ∨ i.val = t n + 1 ∨ i.val = t n + 3 ∨ i.val = k n - 1 := by
  obtain ⟨hx, ha, hN, hC, hb, _⟩ := arithmetic n hn
  obtain ⟨hpos, hodd⟩ := TwoRunSource.modulus_positive_odd (k n) (by dsimp [k]; omega)
  obtain ⟨halpha, hgamma, hclass⟩ := first_values n hn
  have heven : 2 * (x n / 2) = x n := by
    have he : x n = 2 * (2 : ℤ) ^ (t n - 1) := by
      dsimp only [x]
      conv_lhs => rw [show t n = (t n - 1) + 1 by dsimp [t] <;> omega, pow_succ]
      ring
    omega
  let K := (modulus (k n) - (seed n : ℤ)) / 2
  have hK : 2 * K = modulus (k n) - (seed n : ℤ) := by
    dsimp [K]
    rw [hN, ha]
    omega
  have hKpos : 0 < K := by rw [hN,ha] at hK; nlinarith
  have hKbound : K ≤ modulus (k n) / 2 := by rw [hC,hN,ha] at *; nlinarith
  have hbeta : actualSource (k n) (seed n) ⟨t n + 1, by dsimp [k,t]; omega⟩ = -K := by
    apply centered_unique hpos hodd (centered_bounds hpos hodd _)
      ⟨by omega, by rw [hC]; nlinarith⟩ ?_
    rw [centered_mod]
    have he : (2 : ℤ) ^ (t n + 1) * seed n = -K + modulus (k n) * (1 + x n / 2) := by
      rw [pow_succ]
      change x n * 2 * seed n = _
      rw [hN,ha] at hK ⊢
      nlinarith [congrArg (fun z : ℤ => z * (16 * x n ^ 2 - 1)) heven]
    change ((2 : ℤ) ^ (t n + 1) * seed n) % _ = _
    rw [he, Int.add_mul_emod_self_left]
  have hdelta : actualSource (k n) (seed n) ⟨k n - 1, by dsimp [k]; omega⟩ = -K := by
    change centered _ ((2 : ℤ) ^ (k n - 1) * _) = _
    rw [show k n - 1 = (t n + 1) + (t n + 2) by dsimp [k] <;> omega, short_period n _ hn]
    exact hbeta
  intro i
  refine ⟨hclass i, ?_⟩
  intro hi
  rcases hi with hi | hi | hi | hi
  · have he : i = ⟨1, by dsimp [k,t]; omega⟩ := Fin.ext hi
    rw [he,halpha]
    dsimp [H]; nlinarith
  · have he : i = ⟨t n + 1, by dsimp [k,t]; omega⟩ := Fin.ext hi
    rw [he,hbeta]; omega
  · have he : i = ⟨t n + 3, by dsimp [k,t]; omega⟩ := Fin.ext hi
    rw [he,hgamma]
    dsimp [H]; nlinarith
  · have he : i = ⟨k n - 1, by dsimp [k]; omega⟩ := Fin.ext hi
    rw [he,hdelta]; omega

private theorem native_data (n : ℕ) (hn : 1 ≤ n) :
    (∀ i : Fin (k n), B n ∣ actualSource (k n) (seed n) i) ∧
    (∀ i : Fin (k n), 0 ≤ charge (k n) (seed n) i) ∧
    (∀ i : Fin (k n), actualSource (k n + 1) (2 * seed n) i.castSucc =
      2 * actualSource (k n) (seed n) i - charge (k n) (seed n) i) ∧
    actualSource (k n + 1) (2 * seed n) (Fin.last (k n)) = (seed n : ℤ) ∧
    B n < charge (k n) (seed n) ⟨k n - 1, by dsimp [k]; omega⟩ := by
  obtain ⟨hx, ha, hN, hC, hb, hdA, hdN, hdH, hH, hHC, hsat, hbudget, hheavy⟩ := arithmetic n hn
  have hd : 2 ≤ k n := by dsimp [k]; omega
  have data := digit_data (k n) (seed n) hd hb
  refine ⟨?_, fun i => (data i).1, ?_, ?_, ?_⟩
  · intro i
    rw [(data i).2.1]
    exact dvd_sub (dvd_mul_of_dvd_right hdA _) (dvd_mul_of_dvd_left hdN _)
  · intro i
    convert (data i).2.2 using 1
    unfold actualSource
    congr 1
    simp only [Fin.val_castSucc, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
    ring
  · unfold actualSource
    have he : (2 : ℤ) ^ (Fin.last (k n)).val * (2 * seed n : ℕ) = (2 : ℤ) ^ (k n + 1) * seed n := by
      simp only [Fin.val_last, Nat.cast_mul, Nat.cast_ofNat, pow_succ]; ring
    rw [he, centered_full_period]
    obtain ⟨hpos, hodd⟩ := TwoRunSource.modulus_positive_odd (k n + 1) (by omega)
    apply centered_unique hpos hodd (centered_bounds hpos hodd _) ?_ (centered_mod _ _)
    have hcnew : modulus (k n + 1) / 2 = modulus (k n) := by unfold modulus; rw [pow_succ]; omega
    rw [hcnew, hN, ha]; constructor <;> nlinarith
  · simp only [charge, Fin.val_mk, Nat.sub_self, pow_zero, Int.ediv_one]
    have hparity : (seed n : ℤ) % 2 = 1 := by
      rw [ha]
      have heven : x n % 2 = 0 := by
        dsimp [x]
        rw [show t n = (t n - 1) + 1 by dsimp [t] <;> omega, pow_succ]
        omega
      omega
    omega

/-- In the entire actual family with gaps `(4n+2,2,4n+2,2)`, delta precedes
both alpha and gamma, and the ear precedes each of them. Every negative
strictly before delta is beta, so delta is the first or second negative.
No grid, charge table, or existence hypothesis is added to the two literal orders. -/
theorem actualSource_four_gap_lattice_precedence
    (n : ℕ) (hn : 1 ≤ n)
    (sigma : List (Fin (2 * (4 * n + 2) + 4))) (j : ℕ)
    (hj : j ≤ 2 * (4 * n + 2) + 4)
    (hold : OriginalOrder (2 * (4 * n + 2) + 4)
      (1 + 2 ^ (4 * n + 2) + 2 ^ (4 * n + 2 + 2) + 2 ^ (2 * (4 * n + 2) + 2)) sigma)
    (hnew : OriginalOrder (2 * (4 * n + 2) + 4 + 1)
      (2 * (1 + 2 ^ (4 * n + 2) + 2 ^ (4 * n + 2 + 2) + 2 ^ (2 * (4 * n + 2) + 2)))
      (earWord (2 * (4 * n + 2) + 4) sigma j)) :
    let t := 4 * n + 2
    let k := 2 * t + 4
    let A := 1 + 2 ^ t + 2 ^ (t + 2) + 2 ^ (2 * t + 2)
    let alpha : Fin k := ⟨1, by omega⟩
    let gamma : Fin k := ⟨t + 3, by omega⟩
    let delta : Fin k := ⟨k - 1, by omega⟩
    sigma.idxOf delta < sigma.idxOf alpha ∧ sigma.idxOf delta < sigma.idxOf gamma ∧
    j ≤ sigma.idxOf alpha ∧ j ≤ sigma.idxOf gamma ∧
    (∀ i : Fin k, actualSource k A i < 0 → sigma.idxOf i < sigma.idxOf delta → i.val = t + 1) ∧
    Set.Subsingleton {i : Fin k | actualSource k A i < 0 ∧
      sigma.idxOf i < sigma.idxOf delta} ∧
    (∀ i : Fin k, actualSource k A i < 0 ↔
      i.val = 1 ∨ i.val = t + 1 ∨ i.val = t + 3 ∨ i.val = k - 1) := by
  classical
  dsimp only
  obtain ⟨hx, ha, hN, hC, hb, hdA, hdN, hdH, hH, hHC, hsat, hbudget, hheavy⟩ := arithmetic n hn
  obtain ⟨hgrid, hq, hpair, hfresh, hdelta⟩ := native_data n hn
  obtain ⟨halpha, hgamma, hnegative⟩ := first_values n hn
  let alpha : Fin (k n) := ⟨1, by dsimp [k,t]; omega⟩
  let gamma : Fin (k n) := ⟨t n + 3, by dsimp [k,t]; omega⟩
  let delta : Fin (k n) := ⟨k n - 1, by dsimp [k]; omega⟩
  have htotal : (sigma.map (charge (k n) (seed n))).sum = (seed n : ℤ) := by
    rw [(hold.1.map _).sum_eq, ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    exact charge_sum (k n) (seed n) (by dsimp [k]; omega) hb
  have hsumOld : (sigma.map (actualSource (k n) (seed n))).sum = 0 := by
    rw [(hold.1.map _).sum_eq, ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    exact (ZeroSumSubsets.source_cycle (by dsimp [k]; omega : 0 < k n) (seed n)).2.1
  have hsumNew : ((earWord (k n) sigma j).map (actualSource (k n + 1) (2 * seed n))).sum = 0 := by
    rw [(hnew.1.map _).sum_eq, ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    exact (ZeroSumSubsets.source_cycle (by dsimp [k]; omega : 0 < k n + 1) (2 * seed n)).2.1
  have apply_at (nu : Fin (k n)) (hval : actualSource (k n) (seed n) nu = -H n)
      (hne : delta ≠ nu) : sigma.idxOf delta < sigma.idxOf nu ∧ j ≤ sigma.idxOf nu := by
    have hpositive : 0 < charge (k n) (seed n) nu := by
      have hh := (digit_data (k n) (seed n) (by dsimp [k]; omega) hb nu).2.1
      have hp : 0 ≤ (2 : ℤ) ^ nu.val * seed n := by positivity
      have hq0 := hq nu
      rw [hval] at hh
      by_contra hnq
      have : charge (k n) (seed n) nu = 0 := by omega
      rw [this, mul_zero, sub_zero] at hh
      linarith
    have hh := lattice_saturation_suffix_precedence (k n) sigma j hold.1 hj
      (actualSource (k n) (seed n)) (charge (k n) (seed n))
      (actualSource (k n + 1) (2 * seed n)) (B n) (modulus (k n) / 2)
      (modulus (k n + 1) / 2) (seed n) (H n)
      (by dsimp [B]; omega) (by rw [ha]; nlinarith) hgrid hq htotal hpair hfresh
      hsumOld hsumNew hold.2.2 hnew.2.2 nu hval hH hdH hHC hsat hpositive
    have hcnew : modulus (k n + 1) / 2 = modulus (k n) := by unfold modulus; rw [pow_succ]; omega
    exact ⟨hh.2.2.2.2 delta hne (by rw [hcnew, hbudget]; linarith), hh.2.2.1⟩
  have hda := apply_at alpha halpha (by
    intro he
    have hh : k n - 1 = 1 := congrArg (fun i : Fin (k n) => i.val) he
    dsimp only [k] at hh
    omega)
  have hdg := apply_at gamma hgamma (by
    intro he
    have hh : k n - 1 = t n + 3 := congrArg Fin.val he
    have ht : 6 ≤ t n := by dsimp [t]; omega
    change 2 * t n + 4 - 1 = t n + 3 at hh
    omega)
  have honly (i : Fin (k n)) (hi : actualSource (k n) (seed n) i < 0)
      (hbefore : sigma.idxOf i < sigma.idxOf delta) : i.val = t n + 1 := by
    rcases hnegative i hi with he | he | he | he
    · have : i = alpha := Fin.ext he
      subst i; omega
    · exact he
    · have : i = gamma := Fin.ext he
      subst i; omega
    · have : i = delta := Fin.ext he
      subst i; omega
  refine ⟨hda.1, hdg.1, hda.2, hdg.2, honly, ?_, complete_inventory n hn⟩
  intro i hi l hl
  exact Fin.ext ((honly i hi.1 hi.2).trans (honly l hl.1 hl.2).symm)

#print axioms actualSource_four_gap_lattice_precedence
end D5.S3.Combinatorics.Circle.Lattice.FourNegativeLatticePrecedence
