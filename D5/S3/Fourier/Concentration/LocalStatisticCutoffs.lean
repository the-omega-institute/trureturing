/- GID: D5/S3/Fourier/Concentration/LocalStatisticCutoffs
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/LocalStatisticCutoffs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Marked indices control how a local tuple statistic changes with its cutoff. -/

import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-! Stability of normalized local tuple sums under a change of index set. -/

open Finset

set_option autoImplicit false

namespace D5.S3.Fourier.Concentration.LocalStatisticCutoffs

private theorem marked_slot_count {J : Type*} [DecidableEq J]
    {k : ℕ} (S : Finset (Fin (k + 1) ↪ J)) (V : Finset J) (l : Fin (k + 1)) (j : J)
    (hslot : ∀ e ∈ S, e l = j)
    (hlocal : ∀ e ∈ S, ∀ i : Fin k, e (l.succAbove i) ∈ V) :
    S.card ≤ (V.erase j).card.descFactorial k := by
  classical
  let f (e : S) : Fin k ↪ (V.erase j) := ⟨fun i => ⟨(e : Fin (k + 1) ↪ J) (l.succAbove i),
    mem_erase.mpr ⟨fun he =>
      l.succAbove_ne i (e.val.injective (he.trans (hslot e e.property).symm)),
      hlocal e e.property i⟩⟩,
    fun _ _ he => Fin.succAbove_right_injective (e.val.injective (congrArg Subtype.val he))⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Function.Embedding.ext
    rw [Fin.forall_iff_succAbove l]
    refine ⟨(hslot x x.property).trans (hslot y y.property).symm, ?_⟩
    intro i
    exact congrArg Subtype.val (DFunLike.congr_fun he i)
  simpa only [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]
    using Fintype.card_le_of_injective f hf

private theorem trace_through_marked_indices {J : Type*} [DecidableEq J]
    {k D : ℕ} (S : Finset (Fin (k + 1) ↪ J)) (U : Finset J) (V : J → Finset J)
    (slots : Finset (Fin (k + 1)))
    (hV : ∀ j ∈ U, ((V j).erase j).card ≤ D)
    (hmark : ∀ e ∈ S, ∃ l ∈ slots, e l ∈ U ∧ ∀ i : Fin k, e (l.succAbove i) ∈ V (e l)) :
    S.card ≤ slots.card * U.card * D.descFactorial k := by
  classical
  let C (jl : J × Fin (k + 1)) := S.filter fun e =>
    e jl.2 = jl.1 ∧ ∀ i : Fin k, e (jl.2.succAbove i) ∈ V jl.1
  let labels := U ×ˢ slots
  have hsub : S ⊆ labels.biUnion C := by
    intro e he
    obtain ⟨l, hl, hu, hv⟩ := hmark e he
    exact mem_biUnion.mpr ⟨(e l,l), mem_product.mpr ⟨hu, hl⟩,
      mem_filter.mpr ⟨he, rfl, hv⟩⟩
  have hcount (jl : J × Fin (k + 1)) (hjl : jl ∈ labels) :
      (C jl).card ≤ D.descFactorial k := by
    refine (marked_slot_count (C jl) (V jl.1) jl.2 jl.1
      (fun e he => (mem_filter.mp he).2.1) (fun e he => (mem_filter.mp he).2.2)).trans ?_
    rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
    exact prod_le_prod fun i _ => Nat.sub_le_sub_right (hV jl.1 (mem_product.mp hjl).1) i
  calc
    _ ≤ (labels.biUnion C).card := card_le_card hsub
    _ ≤ labels.card * D.descFactorial k := card_biUnion_le_card_mul _ _ _ hcount
    _ = _ := by simp [labels, mul_comm]

private theorem normalized_sums_change {a b n m L e : ℝ} (hn : 0 < n) (hm : 0 < m)
    (ha : |a| ≤ n * L) (hb : |b| ≤ m * L) (hab : |a - b| ≤ e) :
    |a / n-b / m| ≤ (e + |n - m| * L)/max n m := by
  suffices aux : ∀ {a b n m : ℝ}, 0 < n → 0 < m → m ≤ n →
      |b| ≤ m * L → |a - b| ≤ e → |a / n-b / m| ≤ (e + |n - m| * L)/n by
    rcases le_total m n with h | h
    · rw [max_eq_left h]
      exact aux hn hm h hb hab
    · rw [max_eq_right h, abs_sub_comm (a / n) (b / m), abs_sub_comm n m]
      exact aux hm hn h ha (by rwa [abs_sub_comm])
  intro a b n m hn hm h hb hab
  have hnm : 0 ≤ n - m := sub_nonneg.mpr h
  have hrew : a / n-b / m = ((a - b)-(b / m)*(n - m))/n := by
    field_simp
    ring
  rw [hrew, abs_div, abs_of_pos hn]
  apply div_le_div_of_nonneg_right _ hn.le
  have hb' : |b / m| ≤ L := by
    rw [abs_div, abs_of_pos hm]
    exact (div_le_iff₀ hm).mpr (by simpa [mul_comm] using hb)
  calc
    _ ≤ |a - b| + |(b / m)*(n - m)| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg hnm, mul_comm (n - m)]
      exact add_le_add hab (mul_le_mul_of_nonneg_right hb' hnm)

/-- For a bounded statistic supported on tuples local to their first coordinate, a change in
the finite index set is controlled by the number of changed indices and the neighborhood size. -/
theorem local_statistic_cutoff {J : Type*} [Fintype J] [DecidableEq J]
    {k D : ℕ} (s t : Finset J) (hs : s.Nonempty) (ht : t.Nonempty)
    (g : J → ℝ) (F : (Fin (k + 1) ↪ J) → ℝ) {R M : ℝ} (hM : 0 ≤ M)
    (hbounded : ∀ e, |F e| ≤ M)
    (hsupport : ∀ e, F e ≠ 0 → ∀ i, |g (e i) - g (e 0)| ≤ R)
    (hlocal : ∀ j ∈ s ∪ t, ((s ∪ t).filter fun x => |g x - g j| ≤ 2 * R).card ≤ D) :
    let A (u : Finset J) := ∑ e : Fin (k + 1) ↪ J, if ∀ i, e i ∈ u then F e else 0
    let b := ((s \ t) ∪ (t \ s)).card
    let L := M * ((D - 1).descFactorial k : ℝ)
    |A s / s.card - A t / t.card| ≤
      min (L * (((k + 1 : ℕ) : ℝ) * b + |(s.card : ℝ) - t.card|) / max (s.card : ℝ) t.card)
        (2 * L) := by
  classical
  let ways := (D - 1).descFactorial k
  by_cases hR : 0 ≤ R
  swap
  · have hzero (e : Fin (k + 1) ↪ J) : F e = 0 := by
      by_contra he
      exact hR (by simpa using hsupport e he 0)
    simp only [hzero, ite_self, sum_const_zero, zero_div, sub_self, abs_zero]
    exact le_min (by positivity) (by positivity)
  let C (u : Finset J) : Finset (Fin (k + 1) ↪ J) :=
    univ.filter fun e => (∀ i, e i ∈ u) ∧ F e ≠ 0
  let A (u : Finset J) := ∑ e ∈ C u, F e
  let V (j : J) := (s ∪ t).filter fun x => |g x - g j| ≤ 2 * R
  let U := (s \ t) ∪ (t \ s)
  let L := M * (ways : ℝ)
  have hV (j : J) (hj : j ∈ s ∪ t) : ((V j).erase j).card ≤ D - 1 := by
    have hjV : j ∈ V j :=
      mem_filter.mpr ⟨hj, by simpa using mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hR⟩
    rw [card_erase_of_mem hjV]
    exact Nat.sub_le_sub_right (hlocal j hj) 1
  have hrewrite (u : Finset J) :
      (∑ e : Fin (k + 1) ↪ J, if ∀ i, e i ∈ u then F e else 0) = A u := by
    unfold A C
    rw [sum_filter]
    refine sum_congr rfl fun e _ => ?_
    by_cases H : ∀ i, e i ∈ u
    · by_cases hzero : F e = 0 <;> simp [H,hzero]
    · simp [H]
  dsimp only
  rw [hrewrite s, hrewrite t]
  have hmem {u : Finset J} {e : Fin (k + 1) ↪ J} (he : e ∈ C u) :
      (∀ i, e i ∈ u) ∧ F e ≠ 0 := (mem_filter.mp he).2
  have hv {u : Finset J} {e : Fin (k + 1) ↪ J} (hu : u ⊆ s ∪ t) (he : e ∈ C u)
      (i j : Fin (k + 1)) : e i ∈ V (e j) := by
    refine mem_filter.mpr ⟨hu ((hmem he).1 i), ?_⟩
    have H := hsupport e (hmem he).2
    calc
      _ = |(g (e i) - g (e 0)) - (g (e j) - g (e 0))| := by ring_nf
      _ ≤ |g (e i) - g (e 0)| + |g (e j) - g (e 0)| := abs_sub _ _
      _ ≤ _ := by linarith [H i, H j]
  have habs (u : Finset J) (hu : u ⊆ s ∪ t) : |A u| ≤ (u.card : ℝ) * L := by
    have hc := trace_through_marked_indices (C u) u V ({0} : Finset (Fin (k + 1)))
      (fun j hj => hV j (hu hj))
      (fun e he => ⟨0, mem_singleton_self 0, (hmem he).1 0, fun i => hv hu he _ _⟩)
    have hc' : ((C u).card : ℝ) ≤ (u.card : ℝ) * (ways : ℝ) := by
      simp only [card_singleton, one_mul] at hc
      exact_mod_cast hc
    calc
      _ ≤ ∑ e ∈ C u, |F e| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ C u, M := sum_le_sum fun e _ => hbounded e
      _ = ((C u).card : ℝ) * M := by simp
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hc' hM
        simpa [L, mul_assoc, mul_left_comm, mul_comm] using h
  let H := (C s \ C t) ∪ (C t \ C s)
  have hmark {u v : Finset J} {e : Fin (k + 1) ↪ J}
      (he : e ∈ C u) (hne : e ∉ C v) : ∃ i, e i ∈ u \ v := by
    have hh := (hmem he)
    have hn : ¬ ∀ i, e i ∈ v := fun h => hne (mem_filter.mpr ⟨mem_univ _, h, hh.2⟩)
    push Not at hn
    obtain ⟨i, hi⟩ := hn
    exact ⟨i, mem_sdiff.mpr ⟨hh.1 i, hi⟩⟩
  have hu : U ⊆ s ∪ t := by
    intro j hj
    rcases mem_union.mp hj with hj | hj
    · exact mem_union_left _ (mem_sdiff.mp hj).1
    · exact mem_union_right _ (mem_sdiff.mp hj).1
  have hH := trace_through_marked_indices H U V (univ : Finset (Fin (k + 1)))
    (fun j hj => hV j (hu hj)) (by
      intro e he
      rcases mem_union.mp he with he | he
      · obtain ⟨i, hi⟩ := hmark (mem_sdiff.mp he).1 (mem_sdiff.mp he).2
        exact ⟨i, mem_univ _, mem_union_left _ hi,
          fun l => hv subset_union_left (mem_sdiff.mp he).1 _ _⟩
      · obtain ⟨i, hi⟩ := hmark (mem_sdiff.mp he).1 (mem_sdiff.mp he).2
        exact ⟨i, mem_univ _, mem_union_right _ hi,
          fun l => hv subset_union_right (mem_sdiff.mp he).1 _ _⟩)
  have hH' : (H.card : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * (U.card : ℝ) * (ways : ℝ) := by
    norm_num at hH ⊢
    exact_mod_cast hH
  have univ_sum (u : Finset J) : A u =
      ∑ e : Fin (k + 1) ↪ J, if e ∈ C u then F e else 0 := by
    unfold A
    rw [← sum_filter, filter_mem_eq_inter, univ_inter]
  have hgap : |A s - A t| ≤ (((k + 1 : ℕ) : ℝ) * U.card) * L := by
    rw [univ_sum s, univ_sum t, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ e : Fin (k + 1) ↪ J, if e ∈ H then M else 0 := by
        refine sum_le_sum fun e _ => ?_
        by_cases hx : e ∈ C s <;> by_cases hy : e ∈ C t <;>
          simp [H, hx, hy, hbounded e, abs_neg]
      _ = (H.card : ℝ) * M := by rw [← sum_filter, filter_mem_eq_inter, univ_inter]; simp
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hH' hM
        simpa [L, mul_assoc, mul_left_comm, mul_comm] using h
  have hsR : (0 : ℝ) < s.card := by exact_mod_cast card_pos.mpr hs
  have htR : (0 : ℝ) < t.card := by exact_mod_cast card_pos.mpr ht
  have hS := habs s subset_union_left
  have hT := habs t subset_union_right
  apply le_min
  · have h := normalized_sums_change hsR htR hS hT hgap
    convert h using 1
    dsimp [L, U]
    ring
  · have hnorm (a n : ℝ) (hn : 0 < n) (ha : |a| ≤ n * L) : |a / n| ≤ L := by
      rw [abs_div, abs_of_pos hn]
      exact (div_le_iff₀ hn).mpr (by simpa [mul_comm] using ha)
    exact (abs_sub _ _).trans (by linarith only [hnorm _ _ hsR hS, hnorm _ _ htR hT])

#print axioms local_statistic_cutoff

end D5.S3.Fourier.Concentration.LocalStatisticCutoffs
