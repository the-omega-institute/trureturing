/- GID: D5/S3/Combinatorics/Circle/FourNegative/ResonantUniversalInsertionPrefix
   generality: I
   mirror-B: none(waiver:universal-resonant-source)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Generic canonical states, endpoint arithmetic, and prefix inventory. -/
import D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertionPhysical

/-! # Canonical states, endpoint estimates, and prefix inventories -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion

open SourceWidth PeriodicShortening PeriodicShorteningArithmetic
open RunFirstEarTransport
open scoped BigOperators

/-- The target modulus is written with the old modulus and the resonant scale. -/
def resonantTargetH (k ell : ℕ) : ℤ := modulus (k + ell) / 2

def resonantTargetN (k ell : ℕ) : ℤ := modulus (k + ell)

def resonantFirstState (k ell seed m : ℕ) (l : List (Fin (k + 1))) : ℤ :=
  (m : ℤ) * (l.map (resonantFirst k seed)).sum -
    (m - 1 : ℕ) * (l.map (resonantCharge k seed)).sum +
    (seed : ℤ) * (l.map (resonantLowWeight (ell := ell))).sum

def resonantSecondState (k ell seed m : ℕ) (l : List (Fin (k + 1))) : ℤ :=
  (m : ℤ) * (l.map (actualSource (k + 1) (2 * seed))).sum -
    (m - 1 : ℕ) * (l.map (resonantCharge k seed)).sum -
    (seed : ℤ) * (m - 1 : ℕ) * (l.map (resonantEar k)).sum +
    (2 * seed : ℤ) * (l.map (resonantLowWeight (ell := ell))).sum

def ResonantInStrip {α : Type*} (f : α → ℤ) (B h : ℤ) : List α → Prop
  | [] => 0 ≤ h ∧ h ≤ B
  | x :: xs => 0 ≤ h ∧ h ≤ B ∧ ResonantInStrip f B (h + f x) xs

def resonantFirstBlockState (k ell seed m : ℕ) (l : List (Fin (k + 1))) : ℤ :=
  resonantFirstState k ell seed m l

def resonantSecondBlockState (k ell seed m : ℕ) (l : List (Fin (k + 1))) : ℤ :=
  resonantSecondState k ell seed m l

/-- Divisibility forces the canonical quotient to be integral and bounded. -/
theorem resonant_quotient_bound
    (m w q B S F C u T Q r : ℤ)
    (hmq : m = 1 + w * q) (hB : B = m * S)
    (hq : 0 < q) (hm : 0 < m)
    (hF : 0 ≤ F ∧ F ≤ B - 1) (hC : 0 ≤ C ∧ C ≤ w)
    (hu : 0 ≤ u ∧ u < m) (hT : T = u + m * Q)
    (hbase : F = w * T - (2 * B - 1) * C)
    (hr : m * r = u + q * (F - C)) :
    0 ≤ r ∧ r ≤ q * S := by
  have hqw : w * q = m - 1 := by omega
  have hlow : -(m - 1) ≤ u + q * (F - C) := by
    have hFC : -w ≤ F - C := by omega
    have hmul := mul_le_mul_of_nonneg_left hFC (le_of_lt hq)
    nlinarith [hmq, hmul]
  have hr0 : 0 ≤ r := by
    by_contra hn
    have hrneg : r ≤ -1 := by omega
    have hmr := mul_le_mul_of_nonneg_left hrneg (le_of_lt hm)
    omega
  have hrupper : r ≤ q * S := by
    by_contra hn
    have hrlow : q * S + 1 ≤ r := by omega
    have hmr := mul_le_mul_of_nonneg_left hrlow (le_of_lt hm)
    have hqF : q * (F - C) ≥ q * (m * S) + 1 := by
      nlinarith [hr, hmr]
    by_contra hfc
    have hfc' : F - C ≤ m * S := by omega
    have hmul := mul_le_mul_of_nonneg_left hfc' (le_of_lt hq)
    nlinarith [hqF, hmul]
  exact ⟨hr0, hrupper⟩

/-- Canonical states are legal whenever the quotient is in its natural interval. -/
theorem resonant_canonical_endpoint
    (w ell k m q B S F Y C u b r X Z : ℤ)
    (hmq : m = 1 + w * q) (hB : B = m * S)
    (hm : 0 < m) (hw : 0 < w) (hq : 0 < q)
    (hF : 0 ≤ F ∧ F ≤ B - 1) (hY : 0 ≤ Y ∧ Y ≤ 2 * B - 1)
    (hC : 0 ≤ C ∧ C ≤ w) (hu : 0 ≤ u ∧ u < m)
    (hb : b = 0 ∨ b = 1) (hrel : Y = 2 * F - C + w * b)
    (hr : 0 ≤ r ∧ r ≤ q * S) (hquot : m * r = u + q * (F - C))
    (hstate : X = m * F - (m - 1) * C + w * u)
    (zstate : Z = m * Y - (m - 1) * C - w * (m - 1) * b + 2 * w * u) :
    0 ≤ X ∧ X ≤ m * B - 1 ∧ 0 ≤ Z ∧ Z ≤ 2 * m * B - 1 := by
  have hformx : X = F + w * m * r := by
    rw [hstate]
    have hm' : m - 1 = w * q := by omega
    rw [hm']
    have hmr : m * r = u + q * (F - C) := hquot
    calc
      m * F - w * q * C + w * u = F + w * (u + q * (F - C)) := by
        rw [hmq]
        ring
      _ = F + w * m * r := by rw [← hmr]; ring
  have hformz : Z = Y + 2 * w * m * r := by
    calc
      Z = 2 * (m * F - (m - 1) * C + w * u) - C + w * b := by
        rw [zstate, canonical_second_relation m w F Y C u b hrel]
      _ = 2 * X - C + w * b := by rw [hstate]
      _ = Y + 2 * w * m * r := by rw [hformx, hrel]; ring
  rw [hformx, hformz]
  have hwmr0 : 0 ≤ w * m * r :=
    mul_nonneg (mul_nonneg (le_of_lt hw) (le_of_lt hm)) hr.1
  constructor
  · nlinarith [hF.1, hwmr0]
  constructor
  · have hwmr : w * m * r ≤ w * m * (q * S) := by
      exact mul_le_mul_of_nonneg_left hr.2 (by positivity)
    have hmq' : w * q = m - 1 := by omega
    rw [hB]
    nlinarith [hmq']
  constructor
  · nlinarith [hY.1, hwmr0]
  · have hwmr : w * m * r ≤ w * m * (q * S) := by
      exact mul_le_mul_of_nonneg_left hr.2 (by positivity)
    have hmq' : w * q = m - 1 := by omega
    rw [hB]
    nlinarith [hmq']

/-- The boundary case `k = ell` has a separate, exact endpoint estimate. -/
theorem resonant_boundary_endpoint
    (w ell m q B F Y C u T b : ℤ)
    (hmq : m = 1 + w * q) (hmB : m = 2 * B) (hqodd : Odd q) (hq3 : 3 ≤ q)
    (hw : 0 < w) (hF : 0 ≤ F ∧ F ≤ (m - 2) / 2)
    (hY : 0 ≤ Y ∧ Y ≤ m - 1) (hC : 0 ≤ C ∧ C ≤ w)
    (hb : b = 0 ∨ b = 1) (hTu : u = T) (hbase : F = w * T - (m - 1) * C)
    (hrel : Y = 2 * F - C + w * b) :
    0 ≤ (m + 1) * F ∧ (m + 1) * F ≤ m * B - 1 ∧
    0 ≤ Y + 2 * m * F ∧ Y + 2 * m * F ≤ 2 * m * B - 1 := by
  have hqpos : 0 < q := by omega
  have hqodd' : q % 2 = 1 := by
    rcases hqodd with ⟨t, ht⟩
    omega
  have hmul : w * q = m - 1 := by omega
  have hdivF : w ∣ F := by
    rw [hbase, ← hmul]
    apply dvd_sub
    · exact ⟨T, by ring⟩
    · exact ⟨q * C, by ring⟩
  have hmult : F % w = 0 := Int.emod_eq_zero_of_dvd hdivF
  obtain ⟨R, hR⟩ : ∃ R : ℤ, F = w * R := by
    have hdvd : w ∣ F := Int.dvd_iff_emod_eq_zero.mpr hmult
    rcases hdvd with ⟨R, hR⟩
    exact ⟨R, hR⟩
  have hR0 : 0 ≤ R := by nlinarith [hF.1, hw]
  have hRbound : 2 * R ≤ q - 1 := by
    have htwice : 2 * F ≤ m - 2 := by omega
    rw [hR] at htwice
    nlinarith [htwice, hmul, hw]
  have hFmax : 2 * F ≤ m - 1 - w := by
    rw [hR]
    nlinarith [hRbound, hw]
  have hmge : 4 ≤ m := by nlinarith [hq3, hw, hqodd']
  have hX : (m + 1) * F ≤ m * B - 1 := by
    have hmulF0 := mul_le_mul_of_nonneg_left hFmax (by omega : 0 ≤ m + 1)
    have hmulF : 2 * (m + 1) * F ≤ (m + 1) * (m - 1 - w) := by
      nlinarith [hmulF0]
    nlinarith [hmul, hmB, hw, hqpos, hmulF]
  have hZ : Y + 2 * m * F ≤ 2 * m * B - 1 := by
    have hY2 : Y ≤ m - 1 := hY.2
    nlinarith [hFmax, hmul, hmB, hw, hqpos, hY2]
  exact ⟨by nlinarith [hF.1, hw], hX, by nlinarith [hY.1, hF.1], hZ⟩

theorem resonant_low_weight_total {k ell m : ℕ}
    (hm : m = 2 ^ ell) (hkl : ell ≤ k) :
    ((List.finRange (k + 1)).map (resonantLowWeight (ell := ell))).sum = m - 1 := by
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  change (∑ i : Fin (k + 1), if i.val < ell then (2 : ℤ) ^ i.val else 0) = m - 1
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < ell then (2 : ℤ) ^ i else 0)]
  have he : (∑ i ∈ Finset.range (k + 1), if i < ell then (2 : ℤ) ^ i else 0) =
      ∑ i ∈ Finset.range ell, (2 : ℤ) ^ i := by
    rw [← Finset.sum_subset (show Finset.range ell ⊆ Finset.range (k + 1) by
      intro i hi; simp only [Finset.mem_range] at *; omega)
      (by intro i hi hn; simp only [Finset.mem_range] at hn; simp [hn])]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  rw [he]
  rw [show (∑ i ∈ Finset.range ell, (2 : ℤ) ^ i) = (2 : ℤ) ^ ell - 1 by
    simpa using (geom_sum_mul (2 : ℤ) ell)]
  norm_num [hm]

private theorem prefix_nonnegative_lowWeight {ell k : ℕ}
    (word : List (Fin (k + 1))) (n : ℕ)
    (hperm : word.Perm (List.finRange (k + 1))) :
    0 ≤ ((word.take n).map (resonantLowWeight (ell := ell))).sum ∧
      ((word.take n).map (resonantLowWeight (ell := ell))).sum ≤
        ((List.finRange (k + 1)).map (resonantLowWeight (ell := ell))).sum := by
  have h0 (l : List (Fin (k + 1))) : 0 ≤
      (l.map (resonantLowWeight (ell := ell))).sum := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
    by_cases h : j.val < ell <;> simp [resonantLowWeight, h]
  have he := congrArg (fun l => (l.map (resonantLowWeight (ell := ell))).sum)
    (List.take_append_drop n word)
  simp only [List.map_append, List.sum_append] at he
  have hsum := (hperm.map (resonantLowWeight (ell := ell))).sum_eq
  rw [hsum] at he
  constructor
  · exact h0 _
  · linarith [h0 (word.drop n)]

/-- A prefix has the source-row normal form and the low inventory needed by the lift. -/
theorem resonant_prefix_normal_form {w ell k m : ℕ}
    (hell : 1 ≤ ell) (hm : m = 2 ^ ell) (hw : 1 ≤ w)
    (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m)
    (hroom : w ≤ 2 ^ (k - 1) - 1) (hk : 2 ≤ k)
    (word : List (Fin (k + 1))) (hperm : word.Perm (List.finRange (k + 1))) (n : ℕ)
    (hkl : ell ≤ k) :
    let l := word.take n
    let F := (l.map (resonantFirst k w)).sum
    let Y := (l.map (actualSource (k + 1) (2 * w))).sum
    let C := (l.map (resonantCharge k w)).sum
    let T := (l.map (resonantWeight k)).sum
    let u := (l.map (resonantLowWeight (ell := ell))).sum
    let b := (l.map (resonantEar k)).sum
    F = (w : ℤ) * T - modulus k * C ∧
      Y = 2 * F - C + w * b ∧
      0 ≤ C ∧ C ≤ w ∧ 0 ≤ b ∧ b ≤ 1 ∧ 0 ≤ u ∧ u ≤ m - 1 := by
  dsimp
  have hrows := resonant_prefix_rows (k := k) (seed := w) hk hroom (word.take n)
  have hinv := resonant_prefix_inventory (k := k) (seed := w) hk hroom word n hperm
  have hlow := prefix_nonnegative_lowWeight (ell := ell) word n hperm
  have htotal := resonant_low_weight_total hm hkl
  rw [htotal] at hlow
  exact ⟨hrows.1, hrows.2, hinv.1.1, hinv.1.2, hinv.2.1, hinv.2.2, hlow.1, hlow.2⟩

end D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion
