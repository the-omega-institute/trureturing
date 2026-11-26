/- GID: D5/S3/Quantum/Fermionic/SlaterFixedFillingPhase
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/SlaterFixedFillingPhase
   mirror-E: none(waiver:uniform-fixed-filling-sign)
   anchors: []
   utility: none
   digest: Particle-hole cut phases and the alternating rectangle at fixed filling. -/

import D5.S3.Quantum.Fermionic.SlaterCutPhase
import Mathlib.Data.Finset.Card

/-! # Slater shuffle signs at fixed filling -/

namespace D5.S3.Quantum.Fermionic.SlaterFixedFillingPhase

open SlaterCutPhase Finset
open scoped BigOperators

variable {ι : Type*} [LinearOrder ι]

/-- Decompose the occupied shuffle exponent into a local term on each side and
the shuffle exponent of the holes. -/
theorem crossCount_particle_hole {I J a b : Finset ι} (ha : a ⊆ I) (hb : b ⊆ J) :
    crossCount a b + crossCount I J =
      crossCount a J + crossCount I b + crossCount (I \ a) (J \ b) := by
  have hleft (B : Finset ι) : crossCount (I \ a) B + crossCount a B = crossCount I B := by
    unfold crossCount
    exact Finset.sum_sdiff ha
  have hright (A : Finset ι) : crossCount A (J \ b) + crossCount A b = crossCount A J := by
    unfold crossCount
    rw [Finset.sum_comm (s := A), Finset.sum_comm (s := A), Finset.sum_comm (s := A)]
    exact Finset.sum_sdiff hb
  have h1 := hleft J
  have h2 := hleft b
  have h3 := hright (I \ a)
  omega

/-- On the supported occupation pairs, one sign depends only on the retained
occupation and a second sign depends only on the discarded occupation. -/
def Factors (I J : Finset ι) (k : ℕ) : Prop :=
  ∃ left right : Finset ι → ℤ,
    ∀ a b, a ⊆ I → b ⊆ J → a.card + b.card = k →
      (-1 : ℤ) ^ crossCount a b = left a * right b

/-- Every spatial cut has separated shuffle signs with at most one particle
or at most one hole. -/
theorem factors_of_extreme_filling (I J : Finset ι) (k : ℕ)
    (h : k ≤ 1 ∨ I.card + J.card ≤ k + 1) : Factors I J k := by
  rcases h with hk | hk
  · refine ⟨fun _ => 1, fun _ => 1, ?_⟩
    intro a b _ _ ht
    have he : a = ∅ ∨ b = ∅ := by
      rw [← Finset.card_eq_zero, ← Finset.card_eq_zero]
      omega
    rcases he with rfl | rfl <;> simp [crossCount]
  · refine ⟨fun a => (-1) ^ crossCount a J, fun b => (-1) ^ (crossCount I b + crossCount I J), ?_⟩
    intro a b ha hb ht
    have hA := Finset.card_le_card ha
    have hB := Finset.card_le_card hb
    have he : I \ a = ∅ ∨ J \ b = ∅ := by
      rw [← Finset.card_eq_zero, ← Finset.card_eq_zero, Finset.card_sdiff_of_subset ha,
        Finset.card_sdiff_of_subset hb]
      omega
    have hzero : crossCount (I \ a) (J \ b) = 0 := by
      rcases he with he | he <;> simp [he, crossCount]
    have hphase := crossCount_particle_hole ha hb
    rw [hzero, add_zero] at hphase
    rw [← pow_add, ← add_assoc, ← hphase, add_assoc, pow_add]
    simp [← two_mul, pow_mul]

private theorem crossCount_insert_insert {A B : Finset ι} {x y : ι}
    (hx : x ∉ A) (hy : y ∉ B) :
    crossCount (insert x A) (insert y B) =
      crossCount A B + crossCount {x} B + crossCount A {y} + (if y < x then 1 else 0) := by
  simp only [crossCount, Finset.sum_insert hx, Finset.sum_insert hy, Finset.sum_singleton,
    Finset.sum_add_distrib]
  omega

private theorem alternating_rectangle {A B : Finset ι} {x x' y y' : ι}
    (hx : x ∉ A) (hx' : x' ∉ A) (hy : y ∉ B) (hy' : y' ∉ B)
    (horder : (x < y ∧ y < x' ∧ x' < y') ∨ (y < x ∧ x < y' ∧ y' < x')) :
    let diagonal := crossCount (insert x A) (insert y B) +
      crossCount (insert x' A) (insert y' B)
    let offDiagonal := crossCount (insert x A) (insert y' B) +
      crossCount (insert x' A) (insert y B)
    diagonal + 1 = offDiagonal ∨ offDiagonal + 1 = diagonal := by
  dsimp
  rw [crossCount_insert_insert hx hy, crossCount_insert_insert hx' hy',
    crossCount_insert_insert hx hy', crossCount_insert_insert hx' hy]
  rcases horder with ⟨hxy, hyx', hx'y'⟩ | ⟨hyx, hxy', hy'x'⟩
  · simp only [not_lt_of_ge hxy.le, not_lt_of_ge hx'y'.le,
      not_lt_of_ge (hxy.trans (hyx'.trans hx'y')).le, hyx', ite_false, ite_true]
    omega
  · simp only [hyx, hy'x', not_lt_of_ge hxy'.le, hyx.trans (hxy'.trans hy'x'), ite_true, ite_false]
    omega

/-- The four alternating sites and an arbitrary admissible fixed filling
give a rectangle whose diagonal and off-diagonal signs disagree. -/
theorem not_factors_of_alternating {I J : Finset ι} (hdisj : Disjoint I J)
    {x x' y y' : ι} (hx : x ∈ I) (hx' : x' ∈ I) (hy : y ∈ J) (hy' : y' ∈ J)
    (horder : (x < y ∧ y < x' ∧ x' < y') ∨ (y < x ∧ x < y' ∧ y' < x'))
    {k : ℕ} (hk : 2 ≤ k) (hspace : k + 2 ≤ I.card + J.card) : ¬ Factors I J k := by
  classical
  intro hf
  obtain ⟨left, right, hfactor⟩ := hf
  have hxx' : x ≠ x' := by
    rcases horder with ⟨h1, h2, _⟩ | ⟨_, h2, h3⟩
    · exact (h1.trans h2).ne
    · exact (h2.trans h3).ne
  have hyy' : y ≠ y' := by
    rcases horder with ⟨_, h2, h3⟩ | ⟨h1, h2, _⟩
    · exact (h2.trans h3).ne
    · exact (h1.trans h2).ne
  have hne {i j : ι} (hi : i ∈ I) (hj : j ∈ J) : i ≠ j :=
    fun e => Finset.disjoint_left.mp hdisj (e ▸ hi) hj
  let Q : Finset ι := {x, x', y, y'}
  have hQ : Q ⊆ I ∪ J := by
    intro z hz
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp [hx, hx', hy, hy']
  have hQcard : Q.card = 4 := by
    simp [Q, hxx', hyy', hne hx hy, hne hx hy', hne hx' hy, hne hx' hy']
  have hroom : k - 2 ≤ ((I ∪ J) \ Q).card := by
    rw [Finset.card_sdiff_of_subset hQ, Finset.card_union_of_disjoint hdisj, hQcard]
    omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hroom
  let A := T.filter (· ∈ I)
  let B := T.filter (· ∉ I)
  have hA : A ⊆ I := fun _ hi => (Finset.mem_filter.mp hi).2
  have hB : B ⊆ J := by
    intro z hz
    have hm := Finset.mem_filter.mp hz
    exact (Finset.mem_union.mp ((Finset.mem_sdiff.mp (hT hm.1)).1)).resolve_left hm.2
  have houtside {z : ι} (hz : z ∈ Q) : z ∉ T := fun ht => (Finset.mem_sdiff.mp (hT ht)).2 hz
  have hxA : x ∉ A := fun h => houtside (by simp [Q]) (Finset.mem_filter.mp h).1
  have hx'A : x' ∉ A := fun h => houtside (by simp [Q]) (Finset.mem_filter.mp h).1
  have hyB : y ∉ B := fun h => houtside (by simp [Q]) (Finset.mem_filter.mp h).1
  have hy'B : y' ∉ B := fun h => houtside (by simp [Q]) (Finset.mem_filter.mp h).1
  have hsum : A.card + B.card = k - 2 := by
    rw [← hTcard]
    exact Finset.card_filter_add_card_filter_not (s := T) (· ∈ I)
  have localFactor {u v : ι} (hu : u ∈ I) (hv : v ∈ J) (huA : u ∉ A) (hvB : v ∉ B) :
      (-1 : ℤ) ^ crossCount (insert u A) (insert v B) =
        left (insert u A) * right (insert v B) := by
    apply hfactor _ _ (Finset.insert_subset_iff.mpr ⟨hu, hA⟩)
      (Finset.insert_subset_iff.mpr ⟨hv, hB⟩)
    rw [Finset.card_insert_of_notMem huA, Finset.card_insert_of_notMem hvB]
    omega
  have hsign :
      (-1 : ℤ) ^ (crossCount (insert x A) (insert y B) +
        crossCount (insert x' A) (insert y' B)) =
      (-1 : ℤ) ^ (crossCount (insert x A) (insert y' B) +
        crossCount (insert x' A) (insert y B)) := by
    rw [pow_add, pow_add, localFactor hx hy hxA hyB, localFactor hx' hy' hx'A hy'B,
      localFactor hx hy' hxA hy'B, localFactor hx' hy hx'A hyB]
    ring
  rcases alternating_rectangle hxA hx'A hyB hy'B horder with he | he
  · rw [← he, pow_succ] at hsign
    have hn := pow_ne_zero (crossCount (insert x A) (insert y B) +
      crossCount (insert x' A) (insert y' B)) (show (-1 : ℤ) ≠ 0 by norm_num)
    omega
  · rw [← he, pow_succ] at hsign
    have hn := pow_ne_zero (crossCount (insert x A) (insert y' B) +
      crossCount (insert x' A) (insert y B)) (show (-1 : ℤ) ≠ 0 by norm_num)
    omega

end D5.S3.Quantum.Fermionic.SlaterFixedFillingPhase
