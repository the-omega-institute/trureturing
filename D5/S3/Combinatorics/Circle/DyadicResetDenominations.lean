/- GID: D5/S3/Combinatorics/Circle/DyadicResetDenominations
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/DyadicResetDenominations
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Exact physical low-denomination budgets in repeated dyadic reset sources. -/
module
public import D5.S3.Combinatorics.Circle.DyadicResetSource

/-! All denomination counts retain the r distinct labels of each type. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.DyadicResetDenominations
open SourceWidth ExpandingSourcePath MixedSuffixEnergy DyadicResetSource
open scoped BigOperators

def exponent (m r : ℕ) (i : Fin (m * r)) : ℕ := i.val % m

def low (m r q : ℕ) : Finset (Fin (m * r)) :=
  Finset.univ.filter (fun i => exponent m r i < q)

/-- Complete low-denomination mass, with multiplicity r at every denomination. -/
theorem low_mass (m r q : ℕ) (hm : 0 < m) (hq : q ≤ m) :
    (∑ i ∈ low m r q, 2 ^ exponent m r i) = r * (2 ^ q - 1) := by
  classical
  have hf := Finset.sum_fiberwise_eq_sum_filter'
    (Finset.univ : Finset (Fin (m * r))) (Finset.range q)
    (exponent m r) (fun a => (2 : ℕ) ^ a)
  have he : (∑ a ∈ Finset.range q,
      ∑ i ∈ Finset.univ.filter (fun i : Fin (m * r) => exponent m r i = a),
        (2 : ℕ) ^ a) = ∑ a ∈ Finset.range q, r * 2 ^ a := by
    apply Finset.sum_congr rfl
    intro a ha
    have hc := residue_card m r a hm (by have := Finset.mem_range.mp ha; omega)
    have hset : Finset.univ.filter (fun i : Fin (m * r) => exponent m r i = a) =
        Finset.univ.filter (fun i : Fin (m * r) => i.val % m = a) := by
      ext i; rfl
    rw [hset]
    simp [Finset.sum_const, hc]
  have hsum : (∑ a ∈ Finset.range q, (2 : ℕ) ^ a) = 2 ^ q - 1 :=
    by simpa using Nat.geomSum_eq (by decide : 2 ≤ (2 : ℕ)) q
  calc
    (∑ i ∈ low m r q, 2 ^ exponent m r i) =
        ∑ a ∈ Finset.range q,
          ∑ i ∈ Finset.univ.filter (fun i : Fin (m * r) => exponent m r i = a),
            (2 : ℕ) ^ a := by simpa [low] using hf.symm
    _ = ∑ a ∈ Finset.range q, r * 2 ^ a := he
    _ = r * (2 ^ q - 1) := by rw [← Finset.mul_sum, hsum]

theorem scaled_positive_iff (m r : ℕ) (hm : 3 ≤ m) (i : Fin (m * r)) :
    0 < scaled m r i ↔ exponent m r i < m - 1 := by
  have ha : exponent m r i < m := Nat.mod_lt _ (by omega)
  have hM : (0 : ℤ) ≤ height m := by positivity
  change (0 < if exponent m r i = m - 1 then -(height m : ℤ)
    else (2 : ℤ) ^ exponent m r i) ↔ exponent m r i < m - 1
  by_cases hz : exponent m r i = m - 1
  · rw [if_pos hz]; omega
  · rw [if_neg hz]
    have hp : (0 : ℤ) < 2 ^ exponent m r i := by positivity
    omega

theorem scaled_top_iff (m r : ℕ) (hm : 3 ≤ m) (i : Fin (m * r)) :
    scaled m r i = top m ↔ exponent m r i = m - 2 := by
  have ha : exponent m r i < m := Nat.mod_lt _ (by omega)
  have hB : (0 : ℤ) < top m := by dsimp [top]; positivity
  change (if exponent m r i = m - 1 then -(height m : ℤ)
    else (2 : ℤ) ^ exponent m r i) = top m ↔ exponent m r i = m - 2
  by_cases hz : exponent m r i = m - 1
  · have hM : (0 : ℤ) ≤ height m := by positivity
    rw [if_pos hz]; omega
  · rw [if_neg hz]
    have ht : (top m : ℤ) = (2 : ℤ) ^ (m - 2) := by simp [top]
    rw [ht, pow_right_inj₀ (by norm_num : (0 : ℤ) < 2) (by norm_num : (2 : ℤ) ≠ 1)]

theorem scaled_reset_iff (m r : ℕ) (hm : 3 ≤ m) (i : Fin (m * r)) :
    scaled m r i = -(height m : ℤ) ↔ exponent m r i = m - 1 := by
  have hM : (0 : ℤ) ≤ height m := by positivity
  change (if exponent m r i = m - 1 then -(height m : ℤ)
    else (2 : ℤ) ^ exponent m r i) = -(height m : ℤ) ↔ exponent m r i = m - 1
  by_cases hz : exponent m r i = m - 1
  · rw [if_pos hz]; exact ⟨fun _ => hz, fun _ => rfl⟩
  · rw [if_neg hz]
    have hp : (0 : ℤ) < 2 ^ exponent m r i := by positivity
    omega

/-- The two physical LARGE classes each have r occurrences. -/
theorem large_total (m r : ℕ) (hm : 3 ≤ m) (hr : 1 ≤ r) :
    (∑ i : Fin (m * r), largeWeight (m * r) (unit m r) i) = 2 * r := by
  classical
  have hw (i : Fin (m * r)) : largeWeight (m * r) (unit m r) i =
      (if exponent m r i = m - 2 then 1 else 0) +
      (if exponent m r i = m - 1 then 1 else 0) := by
    have hi : exponent m r i < m := Nat.mod_lt _ (by omega)
    unfold largeWeight
    simp only [large_iff m r hm hr]
    change (if m - 2 ≤ exponent m r i then 1 else 0) = _
    split_ifs <;> omega
  have hc (a : ℕ) (ha : a < m) :
      (∑ i : Fin (m * r), if exponent m r i = a then 1 else 0) = r := by
    rw [← Finset.sum_filter]
    have hset : Finset.univ.filter (fun i : Fin (m * r) => exponent m r i = a) =
        Finset.univ.filter (fun i : Fin (m * r) => i.val % m = a) := by
      ext i; rfl
    rw [hset]
    simpa using
      residue_card m r a (by omega) ha
  simp_rw [hw]
  rw [Finset.sum_add_distrib, hc (m - 2) (by omega), hc (m - 1) (by omega)]
  omega

/-- Used LARGE count, without quotienting equal-valued occurrences. -/
theorem large_used_counts (m r : ℕ) (hm : 3 ≤ m) (hr : 1 ≤ r)
    (W : List (Fin (m * r))) :
    largeUsed (m * r) (unit m r) W =
      W.countP (fun i => exponent m r i = m - 2) +
      W.countP (fun i => exponent m r i = m - 1) := by
  induction W with
  | nil => simp [largeUsed, mass]
  | cons a W ih =>
    have hi : exponent m r a < m := Nat.mod_lt _ (by omega)
    have hw : Large (m * r) (unit m r) a ↔ m - 2 ≤ exponent m r a :=
      large_iff m r hm hr a
    simp only [largeUsed, mass, List.map_cons, List.sum_cons] at ih ⊢
    simp only [List.countP_cons]
    have hwa : largeWeight (m * r) (unit m r) a =
        (if exponent m r a = m - 2 then 1 else 0) +
        (if exponent m r a = m - 1 then 1 else 0) := by
      unfold largeWeight
      simp only [hw]
      split_ifs <;> omega
    rw [hwa]
    split_ifs <;> simp_all <;> omega

end D5.S3.Combinatorics.Circle.DyadicResetDenominations
