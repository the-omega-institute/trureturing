/- GID: D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/RankAssembly
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/RankAssembly
   mirror-E: none(waiver:capacity-split-support)
   anchors: []
   utility: none
   digest: Cyclic overlap constraints, mask boundary, rank bound, and final assembly. -/

import D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace.Prelude
import D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace.Trace
import D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace.BooleanCoefficients

/-! Cyclic overlap constraints, mask boundary, rank bound, and final assembly. -/

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace

open D5.S3.QuantumBounds.MerminMeasurementDependence (bit_cases)

private theorem prefix_no_adjacent (m : ℕ) (i j : ZMod (2 * m + 1))
    (hj : j ∈ prefixVariables i m) : j + 1 ∉ prefixVariables i m := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
  intro h
  obtain ⟨b, hb, he⟩ := Finset.mem_image.mp h
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  have hx : ((2 * b + 1 : ℕ) : ZMod (2 * m + 1)) = (2 * a + 2 : ℕ) := by
    apply add_left_cancel (a := i)
    convert he using 1 <;> push_cast <;> ring
  have hx' := (ZMod.natCast_eq_natCast_iff' (2 * b + 1) (2 * a + 2)
    (2 * m + 1)).mp hx
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hx'
  omega

private theorem top_adjacent_pair (m : ℕ) (hm : 0 < m)
    (i j : ZMod (2 * m + 1))
    (hj : j ∈ topVariables m i) (hj' : j + 1 ∈ topVariables m i) :
    j = i + (2 * m - 1 : ℕ) := by
  classical
  have hstep : i + (2 * m : ℕ) + 1 = i := by
    have hz := ZMod.natCast_self (2 * m + 1)
    push_cast at hz ⊢
    linear_combination hz
  have hnot : i ∉ topVariables m i := by
    simp only [topVariables, Finset.mem_insert]
    rintro (he | he)
    · have hx : ((0 : ℕ) : ZMod (2 * m + 1)) = (2 * m : ℕ) := by
        simpa using (add_left_cancel (a := i) (show i + 0 = i + (2 * m : ℕ) by simpa using he))
      have hx' := (ZMod.natCast_eq_natCast_iff' 0 (2 * m) (2 * m + 1)).mp hx
      rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at hx'
      omega
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp he
      have ha' := Finset.mem_range.mp ha
      have hx : ((2 * a + 1 : ℕ) : ZMod (2 * m + 1)) = 0 := by
        exact add_left_cancel (he.trans (add_zero i).symm)
      have hx' := (ZMod.natCast_eq_natCast_iff' (2 * a + 1) 0 (2 * m + 1)).mp hx
      rw [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at hx'
      omega
  rcases Finset.mem_insert.mp hj with he | hp
  · exact (hnot (by simpa only [he, hstep] using hj')).elim
  · rcases Finset.mem_insert.mp hj' with he | hp'
    · have he' : j + 1 = i + (2 * m - 1 : ℕ) + 1 := by
        have hnat : 2 * m - 1 + 1 = 2 * m := by omega
        have hx := congrArg (fun r : ℕ => i + (r : ZMod (2 * m + 1))) hnat
        exact he.trans (by simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hx.symm)
      exact add_right_cancel he'
    · exact (prefix_no_adjacent m i j hp hp').elim

private theorem interior_deletion_unique (m : ℕ) (hm : 0 < m)
    (i a k : ZMod (2 * m + 1))
    (ha : a ≠ i + (2 * m - 1 : ℕ)) (ha' : a ≠ i + (2 * m : ℕ))
    (hsub : (topVariables m i).erase a ⊆ topVariables m k) : k = i := by
  classical
  let j : ZMod (2 * m + 1) := i + (2 * m - 1 : ℕ)
  have hlast : j ∈ prefixVariables i m := by
    refine Finset.mem_image.mpr ⟨m - 1, Finset.mem_range.mpr (by omega), ?_⟩
    dsimp [j]
    have hn : 2 * (m - 1) + 1 = 2 * m - 1 := by omega
    rw [hn]
  have hj : j ∈ (topVariables m i).erase a := by
    exact Finset.mem_erase.mpr ⟨Ne.symm ha, Finset.mem_insert_of_mem hlast⟩
  have hje : j + 1 = i + (2 * m : ℕ) := by
    dsimp [j]
    have hnat : 2 * m - 1 + 1 = 2 * m := by omega
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      congrArg (fun r : ℕ => i + (r : ZMod (2 * m + 1))) hnat
  have hj' : j + 1 ∈ (topVariables m i).erase a := by
    rw [hje]
    exact Finset.mem_erase.mpr ⟨Ne.symm ha', Finset.mem_insert_self _ _⟩
  have he := top_adjacent_pair m hm k j (hsub hj) (hsub hj')
  change i + (2 * m - 1 : ℕ) = k + (2 * m - 1 : ℕ) at he
  exact (add_right_cancel he).symm

private theorem inverse_component_interior_constraint (m : ℕ) (hm : 0 < m)
    (b u : Word (2 * m + 1))
    (hu : u ∈ constantDerivativeSubmodule (inverseComponent m b))
    (i a : ZMod (2 * m + 1)) (ha : a ∈ topVariables m i)
    (ha₁ : a ≠ i + (2 * m - 1 : ℕ)) (ha₂ : a ≠ i + (2 * m : ℕ)) :
    b i * u a = 0 := by
  classical
  let s := (topVariables m i).erase a
  have hs : s.card = m := by
    dsimp [s]
    rw [Finset.card_erase_of_mem ha, top_card]
    omega
  have hcoeff := inverse_component_top_derivative m hm b u hu s hs
  have hterm (k : ZMod (2 * m + 1)) :
      (if s ⊆ topVariables m k then
        booleanMonomial (topVariables m k \ s) u else 0) =
      if k = i then u a else 0 := by
    by_cases hk : k = i
    · subst k
      have hsub : s ⊆ topVariables m i := Finset.erase_subset _ _
      rw [if_pos hsub, if_pos rfl]
      have hdiff : topVariables m i \ s = {a} := by
        ext j
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton, s]
        constructor
        · rintro ⟨hj, hn⟩
          by_contra hja
          exact hn ⟨hja, hj⟩
        · rintro rfl
          simp [ha]
      simp [hdiff, booleanMonomial]
    · have hsub : ¬s ⊆ topVariables m k :=
        fun h => hk (interior_deletion_unique m hm i a k ha₁ ha₂ h)
      simp [hsub, hk]
  simp_rw [hterm] at hcoeff
  simpa [mul_ite] using hcoeff

private theorem prefix_injective (m : ℕ) :
    Function.Injective (fun i : ZMod (2 * m + 1) => prefixVariables i m) := by
  intro i k hik
  have hsum (j : ZMod (2 * m + 1)) :
      (∑ a ∈ prefixVariables j m, a) = (m : ZMod (2 * m + 1)) * j +
        ∑ r ∈ Finset.range m, ((2 * r + 1 : ℕ) : ZMod (2 * m + 1)) := by
    classical
    unfold prefixVariables
    rw [Finset.sum_image (prefix_index_injective m m le_rfl j)]
    simp [Finset.sum_add_distrib, nsmul_eq_mul]
  have he := congrArg (fun s : Finset (ZMod (2 * m + 1)) => ∑ a ∈ s, a) hik
  rw [hsum, hsum] at he
  have he' := congrArg (fun z : ZMod (2 * m + 1) => 2 * z) (add_right_cancel he)
  have hz := ZMod.natCast_self (2 * m + 1)
  push_cast at hz
  linear_combination (i - k) * hz - he'

private theorem top_shift (m : ℕ) (hm : 0 < m) (i : ZMod (2 * m + 1)) :
    topVariables m (i + 2) = insert i (prefixVariables i m) := by
  classical
  have hz := ZMod.natCast_self (2 * m + 1)
  have he : i + 2 + (2 * m : ℕ) = i + 1 := by
    push_cast at hz ⊢
    linear_combination hz
  have hw : i + 2 + (2 * (m - 1) + 1 : ℕ) = i := by
    have hn : 2 * (m - 1) + 1 + 2 = 2 * m + 1 := by omega
    have hx := congrArg (fun r : ℕ => i + (r : ZMod (2 * m + 1))) hn
    push_cast at hx hz ⊢
    linear_combination hx + hz
  ext a
  simp only [topVariables, Finset.mem_insert, prefixVariables, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro (rfl | ⟨r, hr, rfl⟩)
    · exact Or.inr ⟨0, hm, by simpa using he.symm⟩
    · by_cases hlast : r = m - 1
      · left
        simpa [hlast] using hw
      · right
        refine ⟨r + 1, by omega, ?_⟩
        push_cast
        ring
  · rintro (rfl | ⟨r, hr, rfl⟩)
    · right
      exact ⟨m - 1, by omega, hw⟩
    · by_cases hr0 : r = 0
      · left
        simpa [hr0] using he.symm
      · right
        refine ⟨r - 1, by omega, ?_⟩
        have hn : 2 * (r - 1) + 1 + 2 = 2 * r + 1 := by omega
        have hx := congrArg (fun t : ℕ => i + (t : ZMod (2 * m + 1))) hn
        push_cast at hx ⊢
        linear_combination hx

private theorem endpoint_deletion_overlap (m : ℕ) (hm : 0 < m)
    (i k : ZMod (2 * m + 1)) :
    prefixVariables i m ⊆ topVariables m k ↔ k = i ∨ k = i + 2 := by
  classical
  constructor
  · intro hsub
    by_cases he : k + (2 * m : ℕ) ∈ prefixVariables i m
    · have hn : k - 2 + 1 = k + (2 * m : ℕ) := by
        have hz := ZMod.natCast_self (2 * m + 1)
        push_cast at hz ⊢
        linear_combination -hz
      have hnot : k - 2 ∉ prefixVariables i m := by
        intro h
        exact prefix_no_adjacent m i (k - 2) h (hn.symm ▸ he)
      have ht : topVariables m k = insert (k - 2) (prefixVariables (k - 2) m) := by
        simpa using top_shift m hm (k - 2)
      have hs : prefixVariables i m ⊆ prefixVariables (k - 2) m := by
        intro a ha
        have ha' := hsub ha
        rw [ht] at ha'
        rcases Finset.mem_insert.mp ha' with rfl | ha'
        · exact (hnot ha).elim
        · exact ha'
      have heq := Finset.eq_of_subset_of_card_le hs
        (by rw [prefix_card m m le_rfl, prefix_card m m le_rfl])
      have hi := prefix_injective m heq
      right
      linear_combination -hi
    · have hs : prefixVariables i m ⊆ prefixVariables k m := by
        intro a ha
        rcases Finset.mem_insert.mp (hsub ha) with rfl | ha'
        · exact (he ha).elim
        · exact ha'
      have heq := Finset.eq_of_subset_of_card_le hs
        (by rw [prefix_card m m le_rfl, prefix_card m m le_rfl])
      exact Or.inl (prefix_injective m heq).symm
  · rintro (rfl | rfl)
    · exact Finset.subset_insert _ _
    · rw [top_shift m hm]
      exact Finset.subset_insert _ _

private theorem inverse_component_endpoint_constraint (m : ℕ) (hm : 0 < m)
    (b u : Word (2 * m + 1))
    (hu : u ∈ constantDerivativeSubmodule (inverseComponent m b))
    (i : ZMod (2 * m + 1)) :
    b i * u (i + (2 * m : ℕ)) = b (i + 2) * u i := by
  classical
  let s := prefixVariables i m
  have hs : s.card = m := prefix_card m m le_rfl i
  have hc := inverse_component_top_derivative m hm b u hu s hs
  have hi : i ∉ prefixVariables i m := by
    intro h
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp h
    have hr' := Finset.mem_range.mp hr
    have he' : ((2 * r + 1 : ℕ) : ZMod (2 * m + 1)) = 0 := by
      exact add_left_cancel (he.trans (add_zero i).symm)
    have hn := (ZMod.natCast_eq_natCast_iff' (2 * r + 1) 0 (2 * m + 1)).mp he'
    rw [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at hn
    omega
  have hterm (k : ZMod (2 * m + 1)) :
      (if s ⊆ topVariables m k then booleanMonomial (topVariables m k \ s) u else 0) =
      (if k = i then u (i + (2 * m : ℕ)) else 0) +
        (if k = i + 2 then u i else 0) := by
    have hne : i + 2 ≠ i := by
      intro h
      have he : (2 : ZMod (2 * m + 1)) = 0 := by linear_combination h
      have hn := (ZMod.natCast_eq_zero_iff 2 (2 * m + 1)).mp he
      have := Nat.le_of_dvd (by omega : 0 < 2) hn
      omega
    by_cases hk : k = i
    · subst k
      have hd : topVariables m i \ s = {i + (2 * m : ℕ)} := by
        dsimp [topVariables, s]
        ext a
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        have he := endpoint_not_prefix m m le_rfl i
        aesop
      have hsub : s ⊆ topVariables m i := Finset.subset_insert _ _
      simp [hsub, Ne.symm hne, hd, booleanMonomial]
    · by_cases hk' : k = i + 2
      · subst k
        have hd : topVariables m (i + 2) \ s = {i} := by
          rw [top_shift m hm]
          dsimp [s]
          simp [hi]
        have hsub : s ⊆ topVariables m (i + 2) :=
          (endpoint_deletion_overlap m hm i (i + 2)).mpr (Or.inr rfl)
        simp [hsub, hk, hd, booleanMonomial]
      · have hsub : ¬s ⊆ topVariables m k := by
          simpa only [s, endpoint_deletion_overlap m hm i k, not_or] using ⟨hk, hk'⟩
        simp [hsub, hk, hk']
  simp_rw [hterm, mul_add, mul_ite, mul_zero] at hc
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hc
  exact eq_of_sub_eq_zero (by simpa only [ZModModule.sub_eq_add] using hc)

private theorem prefix_start_injective (m r : ℕ) (hr : 0 < r) (hrm : r ≤ m) :
    Function.Injective (fun i : ZMod (2 * m + 1) => prefixVariables i r) := by
  intro i k hik
  change prefixVariables i r = prefixVariables k r at hik
  have hfirst : i + 1 ∈ prefixVariables k r := by
    rw [← hik]
    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hr, by simp⟩
  obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hfirst
  have ht' := Finset.mem_range.mp ht
  have hprev : i - 1 ∉ prefixVariables i r := by
    intro h
    obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp h
    have ha' := Finset.mem_range.mp ha
    have hx : ((2 * a + 2 : ℕ) : ZMod (2 * m + 1)) = 0 := by
      push_cast at hea ⊢
      linear_combination hea
    have hx' := (ZMod.natCast_eq_zero_iff (2 * a + 2) (2 * m + 1)).mp hx
    have hle := Nat.le_of_dvd (by omega : 0 < 2 * a + 2) hx'
    omega
  have ht0 : t = 0 := by
    by_contra h
    apply hprev
    rw [hik]
    refine Finset.mem_image.mpr ⟨t - 1, Finset.mem_range.mpr (by omega), ?_⟩
    have hn : 2 * (t - 1) + 1 + 2 = 2 * t + 1 := by omega
    have hx := congrArg (fun a : ℕ => k + (a : ZMod (2 * m + 1))) hn
    push_cast at he hx ⊢
    linear_combination he + hx
  simpa [ht0] using he.symm

private theorem inverse_component_prefix_fixed (m : ℕ) (hm : 0 < m)
    (b u : Word (2 * m + 1))
    (hu : u ∈ constantDerivativeSubmodule (inverseComponent m b))
    (i : ZMod (2 * m + 1)) (hb : b i ≠ 0)
    (r : ℕ) (hr : r < m) (z : Word (2 * m + 1)) :
    booleanMonomial (prefixVariables i r) (z + u) =
      booleanMonomial (prefixVariables i r) z := by
  classical
  apply Finset.prod_congr rfl
  intro a ha
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
  have ht' := Finset.mem_range.mp ht
  have hmem : i + (2 * t + 1 : ℕ) ∈ topVariables m i :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨t, Finset.mem_range.mpr (by omega), rfl⟩)
  have hne : i + (2 * t + 1 : ℕ) ≠ i + (2 * m - 1 : ℕ) := by
    intro h
    have he := (ZMod.natCast_eq_natCast_iff' (2 * t + 1) (2 * m - 1)
      (2 * m + 1)).mp (add_left_cancel h)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
    omega
  have hne' : i + (2 * t + 1 : ℕ) ≠ i + (2 * m : ℕ) := by
    intro h
    have he := (ZMod.natCast_eq_natCast_iff' (2 * t + 1) (2 * m)
      (2 * m + 1)).mp (add_left_cancel h)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
    omega
  have hz := inverse_component_interior_constraint m hm b u hu i _ hmem hne hne'
  have hzero := (mul_eq_zero.mp hz).resolve_left hb
  change z (i + (2 * t + 1 : ℕ)) + u (i + (2 * t + 1 : ℕ)) = _
  rw [hzero, add_zero]

private theorem monomial_prefix_succ {n : ℕ} (i : ZMod n) (r : ℕ) (z : Word n) :
    booleanMonomial (prefixVariables i (r + 1)) z =
      z (i + (2 * r + 1 : ℕ)) * booleanMonomial (prefixVariables i r) z := by
  classical
  have hs : prefixVariables i (r + 1) =
      insert (i + (2 * r + 1 : ℕ)) (prefixVariables i r) := by
    simp only [prefixVariables, Finset.range_add_one, Finset.image_insert]
  rw [hs, monomial_insert]

private theorem monomial_prefix_cons {n : ℕ} (i : ZMod n) (r : ℕ) (z : Word n) :
    booleanMonomial (prefixVariables (i - 2) (r + 1)) z =
      z (i - 1) * booleanMonomial (prefixVariables i r) z := by
  classical
  have hs : prefixVariables (i - 2) (r + 1) =
      insert (i - 1) (prefixVariables i r) := by
    ext a
    simp only [prefixVariables, Finset.mem_image, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨t, ht, rfl⟩
      by_cases ht0 : t = 0
      · left
        simp only [ht0, Nat.mul_zero, Nat.zero_add, Nat.cast_one]
        ring
      · right
        refine ⟨t - 1, by omega, ?_⟩
        have hn : 2 * (t - 1) + 1 + 2 = 2 * t + 1 := by omega
        have hx := congrArg (fun a : ℕ => (a : ZMod n)) hn
        push_cast at hx ⊢
        linear_combination hx
    · rintro (rfl | ⟨t, ht, rfl⟩)
      · exact ⟨0, by omega, by push_cast; ring⟩
      · refine ⟨t + 1, by omega, ?_⟩
        push_cast
        ring
  rw [hs, monomial_insert]

set_option maxHeartbeats 1000000 in
private theorem shifted_inverse_derivative_expansion (m : ℕ) (hm : 0 < m)
    (b u : Word (2 * m + 1))
    (hu : u ∈ constantDerivativeSubmodule (inverseComponent m b))
    (z : Word (2 * m + 1)) :
    inverseComponent m b (1 + (z + u)) + inverseComponent m b (1 + z) =
      (∑ i, ∑ r ∈ Finset.range m,
        b i * u (i + (2 * r : ℕ)) * booleanMonomial (prefixVariables i r) z) +
      ∑ i, b i * (u (i + (2 * m - 1 : ℕ)) *
          (1 + u (i + (2 * m : ℕ)))) *
        booleanMonomial (prefixVariables i (m - 1)) z := by
  classical
  have hlast : ∀ i : ZMod (2 * m + 1),
      i + (2 * m - 1 : ℕ) = i - 2 := by
    intro i
    have hn : 2 * m - 1 + 2 = 2 * m + 1 := by omega
    have hx := congrArg (fun a : ℕ => (a : ZMod (2 * m + 1))) hn
    have hz := ZMod.natCast_self (2 * m + 1)
    push_cast at hx hz
    linear_combination hx + hz
  have hend : ∀ i : ZMod (2 * m + 1), i + (2 * m : ℕ) = i - 1 := by
    intro i
    have hz := ZMod.natCast_self (2 * m + 1)
    push_cast at hz ⊢
    linear_combination hz
  have hlocal (i : ZMod (2 * m + 1)) :
      (∑ r ∈ Finset.range (m + 1), b i *
        (booleanMonomial (prefixVariables i r) (z + u) +
          booleanMonomial (insert (i + (2 * r : ℕ)) (prefixVariables i r)) (z + u))) +
      (∑ r ∈ Finset.range (m + 1), b i *
        (booleanMonomial (prefixVariables i r) z +
          booleanMonomial (insert (i + (2 * r : ℕ)) (prefixVariables i r)) z)) =
      (∑ r ∈ Finset.range m,
        b i * u (i + (2 * r : ℕ)) * booleanMonomial (prefixVariables i r) z) +
      b i * (u (i - 2) * (1 + u (i - 1))) *
        booleanMonomial (prefixVariables i (m - 1)) z +
      b i * u (i - 1) * booleanMonomial (prefixVariables i m) z +
      b i * u (i - 2) * booleanMonomial (prefixVariables (i - 2) m) z := by
    by_cases hb : b i = 0
    · simp [hb]
    · have hfixed := inverse_component_prefix_fixed m hm b u hu i hb
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hsmall :
          (∑ r ∈ Finset.range m, b i *
            (booleanMonomial (prefixVariables i r) (z + u) +
              booleanMonomial (insert (i + (2 * r : ℕ)) (prefixVariables i r)) (z + u))) +
          (∑ r ∈ Finset.range m, b i *
            (booleanMonomial (prefixVariables i r) z +
              booleanMonomial (insert (i + (2 * r : ℕ)) (prefixVariables i r)) z)) =
          ∑ r ∈ Finset.range m,
            b i * u (i + (2 * r : ℕ)) * booleanMonomial (prefixVariables i r) z := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        rw [monomial_insert, monomial_insert,
          hfixed r (Finset.mem_range.mp hr) z]
        simp only [Pi.add_apply]
        ring_nf
        simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, add_zero, zero_add]
      have hmp : m - 1 + 1 = m := by omega
      have hpz := monomial_prefix_succ i (m - 1) z
      have hpu := monomial_prefix_succ i (m - 1) (z + u)
      have hpc := monomial_prefix_cons i (m - 1) z
      have hn : 2 * (m - 1) + 1 = 2 * m - 1 := by omega
      rw [hmp, hn, hlast] at hpz hpu
      rw [hmp] at hpc
      rw [monomial_insert, monomial_insert, hpz, hpu,
        hfixed (m - 1) (by omega) z]
      simp only [Pi.add_apply, hend, hlast]
      rw [hpc]
      have htwo : (2 : ZMod 2) = 0 := by decide
      linear_combination (norm := (ring_nf; simp only [htwo, mul_zero, add_zero, zero_add]))
        hsmall
  rw [shifted_inverse_expansion, shifted_inverse_expansion, ← Finset.sum_add_distrib]
  simp_rw [hlocal]
  simp only [Finset.sum_add_distrib, hlast, hend]
  have hcancel :
      (∑ i, b i * u (i - 1) * booleanMonomial (prefixVariables i m) z) +
      (∑ i, b i * u (i - 2) * booleanMonomial (prefixVariables (i - 2) m) z) = 0 := by
    have hreindex := Equiv.sum_comp (Equiv.addRight (2 : ZMod (2 * m + 1)))
      (fun i => b i * u (i - 2) * booleanMonomial (prefixVariables (i - 2) m) z)
    change (∑ i, _) = _ at hreindex
    conv_lhs => rhs; rw [← hreindex]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    have hb := inverse_component_endpoint_constraint m hm b u hu i
    rw [hend] at hb
    simp only [Equiv.coe_addRight]
    change b i * u (i - 1) * booleanMonomial (prefixVariables i m) z +
      b (i + 2) * u (i + 2 - 2) *
        booleanMonomial (prefixVariables (i + 2 - 2) m) z = 0
    have hi : i + 2 - 2 = i := by ring
    rw [hi, ← hb]
    exact CharTwo.add_self_eq_zero _
  linear_combination hcancel

private theorem inverse_component_lower_constraint (m : ℕ) (hm : 2 ≤ m)
    (b u : Word (2 * m + 1))
    (hu : u ∈ constantDerivativeSubmodule (inverseComponent m b))
    (i : ZMod (2 * m + 1)) (r : ℕ) (hr : 0 < r) (hrm : r < m) :
    b i * (u (i + (2 * r : ℕ)) +
      if r = m - 1 then u (i + (2 * m - 1 : ℕ)) *
        (1 + u (i + (2 * m : ℕ))) else 0) = 0 := by
  classical
  let s := prefixVariables i r
  have hs : s.Nonempty := Finset.card_pos.mp (by
    change 0 < (prefixVariables i r).card
    rw [prefix_card m r (by omega)]
    exact hr)
  have hiff (k : ZMod (2 * m + 1)) (q : ℕ) (hq : q ≤ m) :
      s = prefixVariables k q ↔ q = r ∧ k = i := by
    constructor
    · intro h
      have hc := congrArg Finset.card h
      dsimp [s] at hc
      rw [prefix_card m r (by omega), prefix_card m q hq] at hc
      subst q
      exact ⟨rfl, (prefix_start_injective m r hr (by omega) h).symm⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have hc : booleanCoeff (fun z =>
      (∑ k, ∑ q ∈ Finset.range m,
        b k * u (k + (2 * q : ℕ)) * booleanMonomial (prefixVariables k q) z) +
      ∑ k, b k * (u (k + (2 * m - 1 : ℕ)) *
        (1 + u (k + (2 * m : ℕ)))) *
        booleanMonomial (prefixVariables k (m - 1)) z) s = 0 := by
    have he := funext (shifted_inverse_derivative_expansion m (by omega) b u hu)
    rw [← he]
    obtain ⟨c, hc⟩ := (constantDerivative_affineSpan_duality (inverseComponent m b)).1 u |>.mp hu
    have hconst : (fun z => inverseComponent m b (1 + (z + u)) +
        inverseComponent m b (1 + z)) = fun _ => c := by
      funext z
      simpa only [add_assoc] using hc (1 + z)
    rw [hconst]
    exact coeff_constant c s hs
  rw [coeff_add, coeff_sum, coeff_sum] at hc
  simp_rw [coeff_sum, coeff_mul, coeff_monomial] at hc
  have hinner (k : ZMod (2 * m + 1)) :
      (∑ q ∈ Finset.range m, b k * u (k + (2 * q : ℕ)) *
        (if s = prefixVariables k q then 1 else 0)) =
      if k = i then b k * u (k + (2 * r : ℕ)) else 0 := by
    rw [Finset.sum_eq_single r]
    · simp only [hiff k r (by omega)]
      by_cases hk : k = i <;> simp [hk]
    · intro q hq hqr
      have hq' := Finset.mem_range.mp hq
      simp only [hiff k q (by omega), hqr, false_and, ite_false, mul_zero]
    · simp [Finset.mem_range.mpr hrm]
  simp_rw [hinner, hiff _ (m - 1) (by omega)] at hc
  by_cases hr' : r = m - 1
  · simp only [hr', eq_self_iff_true, true_and, ite_true, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hc
    simp only [hr', ite_true]
    convert hc using 1 <;> push_cast <;> ring
  · have hr'' : m - 1 ≠ r := Ne.symm hr'
    simp only [hr'', false_and, ite_false, mul_zero, Finset.sum_const_zero, add_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hc
    simp only [if_neg hr', add_zero]
    simpa only [Nat.cast_mul] using hc

private theorem inverse_component_annihilation (m : ℕ) (hm : 2 ≤ m)
    (b u : Word (2 * m + 1))
    (hu : u ∈ constantDerivativeSubmodule (inverseComponent m b))
    (i : ZMod (2 * m + 1)) (r : ℕ) (hr : 0 < r) (hrm : r ≤ 2 * m - 3) :
    b i * u (i + (r : ℕ)) = 0 := by
  have hmod : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases hmod with he | ho
  · have hr' : r = 2 * (r / 2) := by omega
    have hc := inverse_component_lower_constraint m hm b u hu i (r / 2)
      (by omega) (by omega)
    have hne : r / 2 ≠ m - 1 := by omega
    simpa only [if_neg hne, add_zero, ← hr'] using hc
  · have hr' : r = 2 * (r / 2) + 1 := by omega
    have hmem : i + (r : ℕ) ∈ topVariables m i := by
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨r / 2, Finset.mem_range.mpr (by omega), by rw [← hr']⟩
    apply inverse_component_interior_constraint m (by omega) b u hu i _ hmem
    · intro h
      have he := (ZMod.natCast_eq_natCast_iff' r (2 * m - 1) (2 * m + 1)).mp
        (add_left_cancel h)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
      omega
    · intro h
      have he := (ZMod.natCast_eq_natCast_iff' r (2 * m) (2 * m + 1)).mp
        (add_left_cancel h)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
      omega

private theorem inverse_component_last_constraint (m : ℕ) (hm : 2 ≤ m)
    (b u : Word (2 * m + 1))
    (hu : u ∈ constantDerivativeSubmodule (inverseComponent m b))
    (i : ZMod (2 * m + 1)) :
    b i * (u (i - 3) + u (i - 2) * (1 + u (i - 1))) = 0 := by
  have hc := inverse_component_lower_constraint m hm b u hu i (m - 1)
    (by omega) (by omega)
  have hz := ZMod.natCast_self (2 * m + 1)
  have h₁ : i + (2 * (m - 1) : ℕ) = i - 3 := by
    have hn : 2 * (m - 1) + 3 = 2 * m + 1 := by omega
    have hx := congrArg (fun a : ℕ => (a : ZMod (2 * m + 1))) hn
    push_cast at hx hz ⊢
    linear_combination hx + hz
  have h₂ : i + (2 * m - 1 : ℕ) = i - 2 := by
    have hn : 2 * m - 1 + 2 = 2 * m + 1 := by omega
    have hx := congrArg (fun a : ℕ => (a : ZMod (2 * m + 1))) hn
    push_cast at hx hz ⊢
    linear_combination hx + hz
  have h₃ : i + (2 * m : ℕ) = i - 1 := by
    push_cast at hz ⊢
    linear_combination hz
  simpa only [ite_true, h₁, h₂, h₃] using hc

private theorem mask_boundary (m : ℕ) (b : Word (2 * m + 1)) (hb : b ≠ 0) :
    b = 1 ∨ ∃ i, b i = 1 ∧ b (i - 2) = 0 := by
  classical
  by_cases hone : b = 1
  · exact Or.inl hone
  right
  by_contra h
  have hstep (i : ZMod (2 * m + 1)) (hi : b i = 1) : b (i - 2) = 1 := by
    rcases bit_cases (b (i - 2)) with he | he
    · exact (h ⟨i, hi, he⟩).elim
    · exact he
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra hzero
    apply hb
    funext i
    exact not_ne_iff.mp (not_exists.mp hzero i)
  have hi' : b i = 1 := (bit_cases (b i)).resolve_left hi
  have hp (r : ℕ) : b (i - (2 * r : ℕ)) = 1 := by
    induction r with
    | zero => simpa using hi'
    | succ r ih =>
      have hs := hstep (i - (2 * r : ℕ)) ih
      convert hs using 1 <;> congr 1 <;> push_cast <;> ring
  apply hone
  funext k
  obtain ⟨r, hr⟩ := step_two_reaches m k i
  have hk : i - (2 * r : ℕ) = k := by linear_combination -hr
  simpa only [hk, Pi.one_apply] using hp r

private theorem coordinate_rank_bound {n : ℕ} [NeZero n]
    (D : Subspace (ZMod 2) (Word n)) (i : ZMod n)
    (hzero : ∀ u ∈ D, u i = 0 → u = 0) : Module.finrank (ZMod 2) D ≤ 1 := by
  let e : D →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun u => u.1 i
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hi : Function.Injective e := by
    intro u v huv
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hzero (u.1 - v.1) (D.sub_mem u.2 v.2)
    change u.1 i - v.1 i = 0
    exact sub_eq_zero.mpr huv
  simpa using (LinearMap.finrank_le_finrank_of_injective hi)

private theorem inverse_component_three_rank (b : Word 3) (hb : b ≠ 0) :
    Module.finrank (ZMod 2) (constantDerivativeSubmodule (inverseComponent 1 b)) ≤ 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra hzero
    apply hb
    funext i
    exact not_ne_iff.mp (not_exists.mp hzero i)
  have hbi : b i = 1 := (bit_cases (b i)).resolve_left hi
  apply coordinate_rank_bound _ i
  intro u hu hzero
  have h₂ : u (i + 2) = 0 := by
    have hc := inverse_component_endpoint_constraint 1 (by decide) b u hu i
    simpa [hbi, hzero] using hc
  have h₁ : u (i + 1) = 0 := by
    have hc := inverse_component_endpoint_constraint 1 (by decide) b u hu (i + 1)
    change b (i + 1) * u (i + 1 + 2) = b (i + 1 + 2) * u (i + 1) at hc
    have he : i + 1 + 2 = i := by
      have hz : (3 : ZMod 3) = 0 := by decide
      linear_combination hz
    rw [he, hbi, hzero, mul_zero, one_mul] at hc
    exact hc.symm
  funext k
  change u k = 0
  have hval := ZMod.val_lt (k - i)
  have hcast : (((k - i).val : ℕ) : ZMod 3) = k - i := ZMod.natCast_zmod_val _
  have hcases : k = i ∨ k = i + 1 ∨ k = i + 2 := by
    rcases (show (k - i).val = 0 ∨ (k - i).val = 1 ∨ (k - i).val = 2 by omega)
      with h | h | h
    · left
      rw [h] at hcast
      linear_combination -hcast
    · right; left
      rw [h] at hcast
      linear_combination -hcast
    · right; right
      rw [h] at hcast
      linear_combination -hcast
  rcases hcases with rfl | rfl | rfl
  · exact hzero
  · exact h₁
  · exact h₂

private theorem inverse_component_large_rank (m : ℕ) (hm : 2 ≤ m)
    (b : Word (2 * m + 1)) (hb : b ≠ 0) :
    Module.finrank (ZMod 2) (constantDerivativeSubmodule (inverseComponent m b)) ≤ 1 := by
  classical
  rcases mask_boundary m b hb with hone | ⟨i, hbi, hbprev⟩
  · apply coordinate_rank_bound _ 0
    intro u hu _
    funext k
    have hc := inverse_component_annihilation m hm b u hu (k - 1) 1 (by decide) (by omega)
    have hk : k - 1 + (1 : ℕ) = k := by ring
    simpa [hone, hk] using hc
  · apply coordinate_rank_bound _ i
    intro u hu hzero
    have hwrap (a : ℕ) (ha : a ≤ 2 * m + 1) :
        i + (2 * m + 1 - a : ℕ) = i - (a : ZMod (2 * m + 1)) := by
      rw [Nat.cast_sub ha, ZMod.natCast_self]
      ring
    have hend : i + (2 * m : ℕ) = i - 1 := by
      convert hwrap 1 (by omega) using 1 <;> congr 1 <;> omega
    have h₁ : u (i - 1) = 0 := by
      have hc := inverse_component_endpoint_constraint m (by omega) b u hu i
      simpa only [hend, hbi, hzero, one_mul, mul_zero] using hc
    have h₂ : u (i - 2) = 0 := by
      have hc := inverse_component_endpoint_constraint m (by omega) b u hu (i - 2)
      have hi : i - 2 + 2 = i := by ring
      rw [hi, hbprev, hbi, zero_mul, one_mul] at hc
      exact hc.symm
    have h₃ : u (i - 3) = 0 := by
      have hc := inverse_component_last_constraint m hm b u hu i
      simpa only [hbi, h₂, one_mul, zero_mul, add_zero] using hc
    funext k
    change u k = 0
    let r := (k - i).val
    have hr : r < 2 * m + 1 := ZMod.val_lt _
    have hk : i + (r : ZMod (2 * m + 1)) = k := by
      dsimp [r]
      rw [ZMod.natCast_zmod_val]
      ring
    by_cases hr0 : r = 0
    · have he : k = i := by simpa only [hr0, Nat.cast_zero, add_zero] using hk.symm
      simpa only [he] using hzero
    by_cases hr₁ : r = 2 * m
    · rw [hr₁, hend] at hk
      simpa only [← hk] using h₁
    by_cases hr₂ : r = 2 * m - 1
    · have he : r = 2 * m + 1 - 2 := by omega
      rw [he, hwrap 2 (by omega)] at hk
      simpa only [← hk, Nat.cast_ofNat] using h₂
    by_cases hr₃ : r = 2 * m - 2
    · have he : r = 2 * m + 1 - 3 := by omega
      rw [he, hwrap 3 (by omega)] at hk
      simpa only [← hk, Nat.cast_ofNat] using h₃
    have hc := inverse_component_annihilation m hm b u hu i r (by omega) (by omega)
    simpa only [hbi, hk, one_mul] using hc

/-- The literal ordered integer trace has affine support of codimension at most
one for every nonzero mask at every positive odd length. -/
theorem affine_trace_support_dimension (m : ℕ) (b : Word (2 * m + 1)) (hb : b ≠ 0) :
    2 * m ≤ Module.finrank (ZMod 2)
      (affineSpan (ZMod 2) (traceSupport b)).direction := by
  classical
  by_cases hm0 : m = 0
  · subst m
    exact Nat.zero_le _
  have hrank : Module.finrank (ZMod 2)
      (constantDerivativeSubmodule (inverseComponent m b)) ≤ 1 := by
    by_cases hm1 : m = 1
    · subst m
      exact inverse_component_three_rank b hb
    · exact inverse_component_large_rank m (by omega) b hb
  have hdual := (constantDerivative_affineSpan_duality (inverseComponent m b)).2
  have hfull : Module.finrank (ZMod 2) (Word (2 * m + 1)) = 2 * m + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, ZMod.card]
  rw [hfull] at hdual
  have hs : traceSupport b = {a | walsh (inverseComponent m b) a ≠ 0} := by
    ext a
    simp only [traceSupport, Set.mem_setOf_eq, sourceTrace_eq_phase_sum, inverse_phase_sum]
  have hdir : (affineSpan (ZMod 2) (traceSupport b)).direction =
      walshSupportDirection (inverseComponent m b) := by
    rw [hs]
    rfl
  have hdim : Module.finrank (ZMod 2) (affineSpan (ZMod 2) (traceSupport b)).direction =
      Module.finrank (ZMod 2) (walshSupportDirection (inverseComponent m b)) :=
    congrArg (fun D : Subspace (ZMod 2) (Word (2 * m + 1)) =>
      Module.finrank (ZMod 2) D) hdir
  rw [hdim]
  omega


end D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace
