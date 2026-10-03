/- GID: D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence
   mirror-E: none(waiver:universal-symbolic-sequence-identification)
   anchors: []
   utility: none
   digest: The L n-omino instance minimum satisfies the skipped-number recursion. -/

/-
claim: proof_shape: definition (proposition-valued); escape_witness: none.
result
proof_shape: content
escape_witness: The layer injection and cumulative-deficit chain bound in geometric_bound;
  the jump-set/missing-set identity in arithmetic_identification via hermite_prefix.
admission_basis: open-problem-resolution (#12562; Proved)
Direct frozen dependencies: none.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2000

open Finset
namespace D5.S3.Combinatorics.Polyomino.LPolyominoSkippedSequence
open scoped Classical

abbrev Cell := ℤ × ℤ

def L (n : ℕ) : Finset Cell :=
  ((range (n - 1)).image fun i : ℕ => ((i : ℤ), (0 : ℤ))) ∪ {(0, 1)}

noncomputable def instances (P p : Finset Cell) : Finset Cell := by
  classical
  exact (P.biUnion fun u => p.image fun c => u - c).filter fun v => ∀ c ∈ p, c + v ∈ P

def Adj (c c' : Cell) : Prop :=
  (c.1 = c'.1 ∧ (c.2 + 1 = c'.2 ∨ c'.2 + 1 = c.2)) ∨
  (c.2 = c'.2 ∧ (c.1 + 1 = c'.1 ∨ c'.1 + 1 = c.1))

def IsPolyomino (P : Finset Cell) : Prop :=
  P.Nonempty ∧ ∀ c ∈ P, ∀ c' ∈ P,
    Relation.ReflTransGen (fun a b => a ∈ P ∧ b ∈ P ∧ Adj a b) c c'

noncomputable def a (p : Finset Cell) (N : ℕ) : ℕ :=
  sInf {S : ℕ | ∃ P : Finset Cell, IsPolyomino P ∧ N ≤ (instances P p).card ∧ P.card = S}

noncomputable def skip (x k : ℕ) : ℕ :=
  if h : k ≤ 1 then x else
    skip x (k - 1) + if ∃ (i : ℕ) (_h : 1 ≤ i ∧ i < k), skip x i = k then 1 else 2
termination_by k
decreasing_by all_goals omega

def claim : Prop := ∀ n N : ℕ, 3 ≤ n → 1 ≤ N → a (L n) N = skip n N

/-- The finite-layer bound is sharp on trimmed down-sets, and its minimum
has precisely the jump positions excluded from its own earlier range. -/
theorem result : claim := by
  classical
  let H (d K : ℕ) : ℕ := ∑ i ∈ range K, i / d
  have H_zero (d : ℕ) : H d 0 = 0 := by simp only [range_zero, sum_empty, H]
  have H_succ (d K : ℕ) : H d (K + 1) = H d K + K / d := by
    exact sum_range_succ _ _
  have H_mono (d : ℕ) : Monotone (H d) := by
    apply monotone_nat_of_le_succ
    intro K
    rw [H_succ]
    exact Nat.le_add_right _ _
  have H_lt_d (d K : ℕ) (hK : K ≤ d) : H d K = 0 := by
    apply sum_eq_zero
    intro i hi
    exact Nat.div_eq_of_lt (lt_of_lt_of_le (mem_range.mp hi) hK)
  have hermite_prefix (d K : ℕ) (hd : 1 ≤ d) :
      H d (K + d) = H d K + K := by
    induction K with
    | zero => simp only [zero_add, H_lt_d d d (le_refl d), H_zero, add_zero]
    | succ K ih =>
      have heq : K + 1 + d = (K + d) + 1 := by omega
      rw [heq, H_succ, ih, H_succ]
      have hdiv : (K + d) / d = K / d + 1 := by
        exact Nat.add_div_right K hd
      rw [hdiv]
      omega
  have H_unbounded (d : ℕ) (hd : 0 < d) (N : ℕ) :
      ∃ K, N ≤ H d (K + 1) := by
    refine ⟨d * N, ?_⟩
    rw [H_succ, Nat.mul_div_right N hd]
    omega
  let cutoff (d N : ℕ) : ℕ :=
    if hd : 0 < d then Nat.find (H_unbounded d hd N) else 0
  have cutoff_spec (d N : ℕ) (hd : 0 < d) :
      N ≤ H d (cutoff d N + 1) := by
    unfold cutoff
    rw [dif_pos hd]
    exact Nat.find_spec (H_unbounded d hd N)
  have cutoff_min (d N K : ℕ) (hd : 0 < d) (hK : N ≤ H d (K + 1)) :
      cutoff d N ≤ K := by
    unfold cutoff
    rw [dif_pos hd]
    exact Nat.find_min' (H_unbounded d hd N) hK
  have cutoff_lower (d N : ℕ) (hd : 0 < d) (hN : 1 ≤ N) :
      d ≤ cutoff d N ∧ H d (cutoff d N) < N := by
    have hs := cutoff_spec d N hd
    have hbase : d ≤ cutoff d N := by
      by_contra hn
      have hz := H_lt_d d (cutoff d N + 1) (by omega)
      omega
    refine ⟨hbase, ?_⟩
    by_contra hn
    have hmin := cutoff_min d N (cutoff d N - 1) hd (by
      have heq : cutoff d N - 1 + 1 = cutoff d N := by omega
      rw [heq]
      omega)
    omega
  have cutoff_of_interval (d N K : ℕ) (hd : 0 < d)
      (hl : H d K < N) (hu : N ≤ H d (K + 1)) : cutoff d N = K := by
    have hh := cutoff_min d N K hd hu
    have hs := cutoff_spec d N hd
    by_contra hn
    have hk : cutoff d N + 1 ≤ K := by omega
    have hm := H_mono d hk
    omega
  let f (d N : ℕ) : ℕ := N + 1 + cutoff d N
  have f_interval (d N : ℕ) (hd : 0 < d) (hN : 1 ≤ N) :
      H d (cutoff d N + d) + 1 < f d N ∧
        f d N ≤ H d (cutoff d N + d + 1) := by
    have hl := (cutoff_lower d N hd hN).2
    have hu := cutoff_spec d N hd
    have heq : cutoff d N + d + 1 = (cutoff d N + 1) + d := by omega
    rw [hermite_prefix d (cutoff d N) hd, heq, hermite_prefix d (cutoff d N + 1) hd]
    unfold f
    omega
  have f_not_jump (d N K : ℕ) (hd : 0 < d) (hN : 1 ≤ N) :
      f d N ≠ H d (K + 1) + 1 := by
    have hf := f_interval d N hd hN
    by_cases hK : K + 1 ≤ cutoff d N + d
    · have hm := H_mono d hK
      omega
    · have hm := H_mono d (show cutoff d N + d + 1 ≤ K + 1 by omega)
      omega
  have range_of_not_jump (d k : ℕ) (hd : 0 < d) (hk : 2 ≤ k)
      (hnot : ¬ ∃ K, d ≤ K ∧ H d (K + 1) + 1 = k) :
      ∃ i, 1 ≤ i ∧ i < k ∧ f d i = k := by
    let K := cutoff d (k - 1)
    have hbase : d ≤ K := (cutoff_lower d (k - 1) hd (by omega)).1
    have hl : H d K < k - 1 := (cutoff_lower d (k - 1) hd (by omega)).2
    have hu : k - 1 ≤ H d (K + 1) := cutoff_spec d (k - 1) hd
    have hstrict : k - 1 < H d (K + 1) := by
      by_contra hh
      apply hnot
      refine ⟨K, hbase, ?_⟩
      omega
    have hq : 2 ≤ K / d := by
      have hrec := H_succ d K
      omega
    have h2d : d + d ≤ K := by
      have ht := (Nat.le_div_iff_mul_le hd).mp hq
      omega
    let J := K - d
    have hJ : d ≤ J := by dsimp [J]; omega
    have hK : K = J + d := by dsimp [J]; omega
    have hK' : K + 1 = (J + 1) + d := by omega
    have hlow : H d K = H d J + J := by rw [hK, hermite_prefix d J hd]
    have hupp : H d (K + 1) = H d (J + 1) + J + 1 := by
      rw [hK', hermite_prefix d (J + 1) hd]
      omega
    let i := k - J - 1
    have hi : H d J < i := by dsimp [i]; omega
    have hi' : i ≤ H d (J + 1) := by dsimp [i]; omega
    have hc := cutoff_of_interval d i J hd hi hi'
    refine ⟨i, by omega, ?_, ?_⟩
    · dsimp [i]
      omega
    · unfold f
      rw [hc]
      dsimp [i]
      omega
  have cutoff_step (d N : ℕ) (hd : 0 < d) (hN : 1 ≤ N) :
      cutoff d (N + 1) = cutoff d N +
        if N = H d (cutoff d N + 1) then 1 else 0 := by
    have hb := cutoff_lower d N hd hN
    have hs := cutoff_spec d N hd
    by_cases heq : N = H d (cutoff d N + 1)
    · rw [if_pos heq]
      apply cutoff_of_interval d (N + 1) (cutoff d N + 1) hd
      · omega
      · have hq : 1 ≤ (cutoff d N + 1) / d := Nat.div_pos (by omega) hd
        rw [H_succ]
        omega
    · rw [if_neg heq, Nat.add_zero]
      exact cutoff_of_interval d (N + 1) (cutoff d N) hd (by omega) (by omega)
  have jump_boundary (d N : ℕ) (hd : 0 < d) (hN : 1 ≤ N) :
      (∃ K, d ≤ K ∧ H d (K + 1) + 1 = N + 1) ↔
        N = H d (cutoff d N + 1) := by
    constructor
    · rintro ⟨K, hK, heq⟩
      have hpos : 1 ≤ K / d := Nat.div_pos hK hd
      have hlo : H d K < N := by have ht := H_succ d K; omega
      have hup : N ≤ H d (K + 1) := by omega
      have hc := cutoff_of_interval d N K hd hlo hup
      rw [hc]
      omega
    · intro heq
      exact ⟨cutoff d N, (cutoff_lower d N hd hN).1, by omega⟩
  have f_rec (d N : ℕ) (hd : 0 < d) (hN : 1 ≤ N) :
      f d (N + 1) = f d N +
        if ∃ i, 1 ≤ i ∧ i < N + 1 ∧ f d i = N + 1 then 1 else 2 := by
    classical
    have hequiv : (∃ i, 1 ≤ i ∧ i < N + 1 ∧ f d i = N + 1) ↔
        N ≠ H d (cutoff d N + 1) := by
      constructor
      · rintro ⟨i, hi, _, heq⟩ hbound
        have hne := f_not_jump d i (cutoff d N) hd hi
        apply hne
        omega
      · intro hne
        apply range_of_not_jump d (N + 1) hd (by omega)
        rw [jump_boundary d N hd hN]
        exact hne
    have hc := cutoff_step d N hd hN
    change N + 1 + 1 + cutoff d (N + 1) = N + 1 + cutoff d N +
      if ∃ i, 1 ≤ i ∧ i < N + 1 ∧ f d i = N + 1 then 1 else 2
    rw [hc]
    by_cases hh : N = H d (cutoff d N + 1)
    · have hfalse : ¬ ∃ i, 1 ≤ i ∧ i < N + 1 ∧ f d i = N + 1 := by
        rw [hequiv]
        exact not_not.mpr hh
      rw [if_pos hh, if_neg hfalse]
      omega
    · rw [if_neg hh, if_pos (hequiv.mpr hh)]
      omega
  have f_one (d : ℕ) (hd : 0 < d) : f d 1 = d + 2 := by
    have hc : cutoff d 1 = d := by
      apply cutoff_of_interval d 1 d hd
      · rw [H_lt_d d d (le_refl d)]; omega
      · rw [H_succ, H_lt_d d d (le_refl d), Nat.div_self (by omega)]
    unfold f
    rw [hc]
    omega
  have skip_one (x : ℕ) : skip x 1 = x := by
    rw [skip]
    simp only [Std.le_refl, dif_pos]
  have skip_rec (x k : ℕ) (hk : 2 ≤ k) :
      skip x k = skip x (k - 1) +
        if ∃ i, 1 ≤ i ∧ i < k ∧ skip x i = k then 1 else 2 := by
    classical
    rw [skip, dif_neg (by omega)]
    congr 1
    simp only [exists_prop, and_assoc]
  have arithmetic_identification (d N : ℕ) (hd : 0 < d) (hN : 1 ≤ N) :
      f d N = skip (d + 2) N := by
    induction N using Nat.strong_induction_on with
    | h N ih =>
      by_cases h1 : N = 1
      · subst N
        rw [f_one d hd, skip_one]
      · have h2 : 2 ≤ N := by omega
        have hprev : N - 1 + 1 = N := by omega
        rw [← hprev, f_rec d (N - 1) hd (by omega), hprev,
          skip_rec (d + 2) N h2, ih (N - 1) (by omega) (by omega)]
        congr 1
        apply if_congr
        · constructor
          · rintro ⟨i, hi, hiN, hval⟩
            exact ⟨i, hi, hiN, by rw [← ih i hiN hi]; exact hval⟩
          · rintro ⟨i, hi, hiN, hval⟩
            exact ⟨i, hi, hiN, by rw [ih i hiN hi]; exact hval⟩
        · rfl
        · rfl
  have profile_charge (d : ℕ) (hd : 0 < d) (s e : ℕ → ℕ)
      (hle : ∀ k, e k ≤ s k)
      (hzero : ∀ k, k < d → e k = 0)
      (hchain : ∀ k j, 1 ≤ j → j ≤ d → j ≤ k → e k ≤ s (k - j))
      (k : ℕ) : d * e k ≤ ∑ l ∈ range k, (s l - e l) := by
    by_cases hk : k < d
    · rw [hzero k hk, Nat.mul_zero]
      exact Nat.zero_le _
    have hdk : d ≤ k := by omega
    have he : (∑ l ∈ range k, e l) ≤ ∑ l ∈ range (k - d), s l := by
      have heq : k = d + (k - d) := by omega
      conv_lhs => rw [heq, sum_range_add]
      have hfirst : (∑ l ∈ range d, e l) = 0 := by
        apply sum_eq_zero
        exact fun l hl => hzero l (mem_range.mp hl)
      rw [hfirst, Nat.zero_add]
      apply sum_le_sum
      intro l hl
      have hh := hchain (d + l) d hd (le_refl d) (by omega)
      have heq' : d + l - d = l := by omega
      rw [heq'] at hh
      exact hh
    have hw : d * e k ≤ ∑ i ∈ range d, s (k - d + i) := by
      calc
        d * e k = ∑ i ∈ range d, e k := by
          simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_id]
        _ ≤ ∑ i ∈ range d, s (k - d + i) := by
          apply sum_le_sum
          intro i hi
          have hid := mem_range.mp hi
          have hh := hchain k (d - i) (by omega) (by omega) (by omega)
          have heq : k - (d - i) = k - d + i := by omega
          rw [heq] at hh
          exact hh
    have hs : (∑ l ∈ range k, s l) =
        (∑ l ∈ range (k - d), s l) + ∑ i ∈ range d, s (k - d + i) := by
      conv_lhs => rw [show k = (k - d) + d by omega]
      exact sum_range_add _ _ _
    rw [sum_tsub_distrib _ (fun l _ => hle l)]
    omega
  have profile_bound (d M : ℕ) (hd : 0 < d) (s e : ℕ → ℕ)
      (hle : ∀ k, e k ≤ s k)
      (hstrict : ∀ k, 0 < s k → e k < s k)
      (hzero : ∀ k, k < d → e k = 0)
      (hchain : ∀ k j, 1 ≤ j → j ≤ d → j ≤ k → e k ≤ s (k - j)) :
      (∑ k ∈ range M, e k) ≤ H d ((∑ k ∈ range M, s k) - ∑ k ∈ range M, e k) := by
    classical
    let delta : ℕ → ℕ := fun k => s k - e k
    let pref : ℕ → ℕ := fun k => ∑ l ∈ range k, delta l
    let Q := (range M).filter fun k => 0 < s k
    have hpmono : Monotone pref := by
      apply monotone_nat_of_le_succ
      intro k
      change (∑ l ∈ range k, delta l) ≤ ∑ l ∈ range (k + 1), delta l
      rw [sum_range_succ]
      exact Nat.le_add_right _ _
    have hpstep : ∀ k, pref (k + 1) = pref k + delta k := by
      intro k
      exact sum_range_succ _ _
    have hpos : ∀ k ∈ Q, 1 ≤ delta k := by
      intro k hk
      have hh := hstrict k (mem_filter.mp hk).2
      dsimp [delta]
      omega
    have hinj : Set.InjOn pref (Q : Set ℕ) := by
      intro k hk l hl heq
      by_contra hne
      rcases lt_or_gt_of_ne hne with hkl | hlk
      · have hmono := hpmono (show k + 1 ≤ l by omega)
        have hst := hpstep k
        have hpo := hpos k hk
        omega
      · have hmono := hpmono (show l + 1 ≤ k by omega)
        have hst := hpstep l
        have hpo := hpos l hl
        omega
    have hsub : Q.image pref ⊆ range (pref M) := by
      intro z hz
      rcases mem_image.mp hz with ⟨k, hk, rfl⟩
      have hM := mem_range.mp (mem_filter.mp hk).1
      have hmono := hpmono (show k + 1 ≤ M by omega)
      have hst := hpstep k
      have hpo := hpos k hk
      rw [mem_range]
      omega
    have heq : (∑ k ∈ range M, e k) = ∑ k ∈ Q, e k := by
      apply (sum_subset (filter_subset _ _) ?_).symm
      intro k hk hnot
      have hz : s k = 0 := by
        simp only [mem_filter, hk, true_and] at hnot
        omega
      have hh := hle k
      omega
    have hcharge : ∀ k, e k ≤ pref k / d := by
      intro k
      apply (Nat.le_div_iff_mul_le hd).mpr
      have hh := profile_charge d hd s e hle hzero hchain k
      dsimp [pref, delta]
      simpa only [Nat.mul_comm, ge_iff_le] using hh
    calc
      (∑ k ∈ range M, e k) = ∑ k ∈ Q, e k := heq
      _ ≤ ∑ k ∈ Q, pref k / d := sum_le_sum fun k _ => hcharge k
      _ = ∑ z ∈ Q.image pref, z / d := (sum_image (f := fun z => z / d) hinj).symm
      _ ≤ ∑ z ∈ range (pref M), z / d := sum_le_sum_of_subset hsub
      _ = H d ((∑ k ∈ range M, s k) - ∑ k ∈ range M, e k) := by
        have hp : pref M = (∑ k ∈ range M, s k) - ∑ k ∈ range M, e k :=
          sum_tsub_distrib _ (fun k _ => hle k)
        rw [hp]
  have zero_mem_L (n : ℕ) (hn : 3 ≤ n) : (0, 0) ∈ L n := by
    apply mem_union_left
    apply mem_image.mpr
    refine ⟨0, by simp only [mem_range, tsub_pos_iff_lt]; omega, ?_⟩
    rfl
  have top_mem_L (n : ℕ) : (0, 1) ∈ L n := by
    exact mem_union_right _ (mem_singleton_self _)
  have bottom_mem_L (n i : ℕ) (hi : i ≤ n - 2) (hn : 3 ≤ n) :
      ((i : ℤ), 0) ∈ L n := by
    apply mem_union_left
    exact mem_image.mpr ⟨i, mem_range.mpr (by omega), rfl⟩
  have mem_instances (P p : Finset Cell) (hp : (0, 0) ∈ p) (v : Cell) :
      v ∈ instances P p ↔ ∀ c ∈ p, c + v ∈ P := by
    classical
    constructor
    · exact fun h => (mem_filter.mp h).2
    · intro h
      apply mem_filter.mpr
      refine ⟨?_, h⟩
      have hv : v ∈ P := by
        have hh := h (0, 0) hp
        change (0 : Cell) + v ∈ P at hh
        simpa only [zero_add] using hh
      apply mem_biUnion.mpr
      refine ⟨v, hv, mem_image.mpr ⟨(0, 0), hp, ?_⟩⟩
      simp only [sub_eq_self, Prod.mk_eq_zero, and_self]
  have anchor_mem (P : Finset Cell) (n : ℕ) (hn : 3 ≤ n)
      (v : Cell) (hv : v ∈ instances P (L n)) : v ∈ P := by
    have hi := (mem_instances P (L n) (zero_mem_L n hn) v).mp hv
    have hh := hi (0, 0) (zero_mem_L n hn)
    change (0 : Cell) + v ∈ P at hh
    simpa only [zero_add] using hh
  have translate_injective (c : Cell) : Function.Injective (fun v : Cell => c + v) := by
    intro v w hvw
    exact add_left_cancel hvw
  let weight (d : ℕ) (c : Cell) : ℤ := c.1 + (d : ℤ) * c.2
  let level (d : ℕ) (b : ℤ) (c : Cell) : ℕ := (weight d c - b).toNat
  have weight_add (d : ℕ) (c v : Cell) :
      weight d (c + v) = weight d c + weight d v := by
    simp only [weight, Prod.fst_add, Prod.snd_add]
    ring
  have level_cast (d : ℕ) (b : ℤ) (c : Cell) (hc : b ≤ weight d c) :
      (level d b c : ℤ) = weight d c - b := by
    exact Int.toNat_of_nonneg (by omega)
  have geometric_bound (P : Finset Cell) (n : ℕ) (hn : 3 ≤ n) :
      (instances P (L n)).card ≤ H (n - 2) (P.card - (instances P (L n)).card) := by
    classical
    by_cases hP : P.Nonempty
    · let d := n - 2
      have hd : 0 < d := by dsimp [d]; omega
      obtain ⟨z, hz, hmin⟩ := P.exists_min_image (weight d) hP
      let b := weight d z
      let lev := level d b
      let layers := fun k => P.filter fun c => lev c = k
      let anchors := fun k => (instances P (L n)).filter fun v => lev ((0, 1) + v) = k
      let s := fun k => (layers k).card
      let e := fun k => (anchors k).card
      have hcast : ∀ c ∈ P, (lev c : ℤ) = weight d c - b := by
        intro c hc
        exact level_cast d b c (hmin c hc)
      have hcells : ∀ v ∈ instances P (L n), ∀ c ∈ L n, c + v ∈ P := by
        intro v hv
        exact (mem_instances P (L n) (zero_mem_L n hn) v).mp hv
      have htop : ∀ v ∈ instances P (L n), (0, 1) + v ∈ P := by
        intro v hv
        exact hcells v hv (0, 1) (top_mem_L n)
      have hbot : ∀ v ∈ instances P (L n), ∀ i ≤ d, ((i : ℤ), 0) + v ∈ P := by
        intro v hv i hi
        exact hcells v hv ((i : ℤ), 0) (bottom_mem_L n i hi hn)
      have hmem : ∀ k v, v ∈ anchors k ↔ v ∈ instances P (L n) ∧ lev ((0, 1) + v) = k := by
        intro k v
        exact mem_filter
      have hlevel : ∀ v ∈ instances P (L n),
          lev ((0, 1) + v) = lev v + d := by
        intro v hv
        have hvP := anchor_mem P n hn v hv
        have h1 := hcast v hvP
        have h2 := hcast ((0, 1) + v) (htop v hv)
        rw [weight_add] at h2
        simp only [weight, zero_add, mul_one] at h1 h2
        omega
      have hle : ∀ k, e k ≤ s k := by
        intro k
        apply card_le_card_of_injOn (fun v => (0, 1) + v)
        · intro v hv
          have hh := (hmem k v).mp hv
          exact mem_filter.mpr ⟨htop v hh.1, hh.2⟩
        · exact (translate_injective (0, 1)).injOn
      have hstrict : ∀ k, 0 < s k → e k < s k := by
        intro k hk
        obtain ⟨c, hc, hmax⟩ := (layers k).exists_max_image Prod.fst (card_pos.mp hk)
        have hinj : e k ≤ ((layers k).erase c).card := by
          apply card_le_card_of_injOn (fun v => (0, 1) + v)
          · intro v hv
            have hh := (hmem k v).mp hv
            apply mem_erase.mpr
            refine ⟨?_, mem_filter.mpr ⟨htop v hh.1, hh.2⟩⟩
            intro heq
            have hr := hbot v hh.1 d (le_refl d)
            have htcast := hcast ((0, 1) + v) (htop v hh.1)
            have hrcast := hcast (((d : ℤ), 0) + v) hr
            have hweight : weight d (((d : ℤ), 0) + v) = weight d ((0, 1) + v) := by
              rw [weight_add, weight_add]
              simp only [mul_zero, add_zero, mul_one, zero_add, weight]
            have hlev : lev (((d : ℤ), 0) + v) = k := by
              rw [hweight] at hrcast
              omega
            have hm := hmax (((d : ℤ), 0) + v) (mem_filter.mpr ⟨hr, hlev⟩)
            have hx := congrArg Prod.fst heq
            simp only [Prod.fst_add] at hm hx
            omega
          · exact (translate_injective (0, 1)).injOn
        have he := card_erase_of_mem hc
        dsimp [s] at hk ⊢
        omega
      have hzero : ∀ k, k < d → e k = 0 := by
        intro k hk
        apply card_eq_zero.mpr
        apply eq_empty_iff_forall_notMem.mpr
        intro v hv
        have hh := (hmem k v).mp hv
        have hl := hlevel v hh.1
        omega
      have hchain : ∀ k j, 1 ≤ j → j ≤ d → j ≤ k → e k ≤ s (k - j) := by
        intro k j hj hjd hjk
        apply card_le_card_of_injOn (fun v => (((d - j : ℕ) : ℤ), 0) + v)
        · intro v hv
          have hh := (hmem k v).mp hv
          have hr := hbot v hh.1 (d - j) (by omega)
          apply mem_filter.mpr
          refine ⟨hr, ?_⟩
          have htcast := hcast ((0, 1) + v) (htop v hh.1)
          have hrcast := hcast ((((d - j : ℕ) : ℤ), 0) + v) hr
          rw [weight_add] at htcast hrcast
          simp only [weight, zero_add, mul_one, mul_zero, add_zero] at htcast hrcast
          rw [Nat.cast_sub hjd] at hrcast
          change lev ((((d - j : ℕ) : ℤ), 0) + v) = k - j
          rw [Nat.cast_sub hjd]
          omega
        · exact (translate_injective ((((d - j : ℕ) : ℤ), 0))).injOn
      let M := (P.image lev).max' (hP.image lev) + 1
      have hM : ∀ c ∈ P, lev c < M := by
        intro c hc
        have hh := le_max' (P.image lev) (lev c) (mem_image_of_mem lev hc)
        dsimp [M]
        omega
      have hS : P.card = ∑ k ∈ range M, s k := by
        exact card_eq_sum_card_fiberwise (fun c hc => mem_range.mpr (hM c hc))
      have hE : (instances P (L n)).card = ∑ k ∈ range M, e k := by
        exact card_eq_sum_card_fiberwise (fun v hv => mem_range.mpr (hM _ (htop v hv)))
      rw [hS, hE]
      exact profile_bound d M hd s e hle hstrict hzero hchain
    · have hPe : P = ∅ := not_nonempty_iff_eq_empty.mp hP
      subst P
      simp only [instances, notMem_empty, imp_false, Prod.forall, filter_const,
        biUnion_empty, ite_self, card_empty, tsub_self, range_zero, sum_empty, Std.le_refl, H]
  let Label := Σ _ : ℕ, ℕ
  let coord (d : ℕ) (u : Label) : Cell :=
    ((u.fst : ℤ) - (d : ℤ) * (u.snd : ℤ), (u.snd : ℤ))
  let boardLabels (d K q : ℕ) : Finset Label :=
    (range (K + 1)).sigma fun k => range (if k = K then q + 1 else k / d + 1)
  let board (d K q : ℕ) : Finset Cell := (boardLabels d K q).image (coord d)
  have coord_weight (d : ℕ) (u : Label) : weight d (coord d u) = (u.fst : ℤ) := by
    simp only [coord, weight]
    ring
  have coord_injective (d : ℕ) : Function.Injective (coord d) := by
    intro u v huv
    have hy := congrArg Prod.snd huv
    have hx := congrArg (weight d) huv
    simp only [coord_weight] at hx
    change (u.snd : ℤ) = (v.snd : ℤ) at hy
    have hx' : u.fst = v.fst := Int.ofNat_inj.mp hx
    have hy' : u.snd = v.snd := Int.ofNat_inj.mp hy
    cases u
    cases v
    simp_all
  have mem_board (d K q : ℕ) (hd : 0 < d) (hq : q ≤ K / d) (c : Cell) :
      c ∈ board d K q ↔ 0 ≤ c.1 ∧ 0 ≤ c.2 ∧ weight d c ≤ K ∧
        (weight d c = K → c.2 ≤ q) := by
    classical
    constructor
    · intro hc
      rcases mem_image.mp hc with ⟨u, hu, rfl⟩
      have hh := mem_sigma.mp hu
      have hk := mem_range.mp hh.1
      have hy := mem_range.mp hh.2
      have hyq : u.snd ≤ u.fst / d := by
        by_cases heq : u.fst = K
        · rw [if_pos heq] at hy
          rw [heq]
          omega
        · rw [if_neg heq] at hy
          omega
      have hprod := (Nat.le_div_iff_mul_le hd).mp hyq
      have hprodz : (u.snd : ℤ) * (d : ℤ) ≤ (u.fst : ℤ) := by exact_mod_cast hprod
      rw [coord_weight]
      refine ⟨?_, by simp only [Nat.cast_nonneg, coord], by omega, ?_⟩
      · dsimp [coord]
        nlinarith only [hprodz]
      · intro heq
        have hk' : u.fst = K := Int.ofNat_inj.mp heq
        rw [if_pos hk'] at hy
        dsimp [coord]
        omega
    · rintro ⟨hx, hy, hw, htop⟩
      let k := (weight d c).toNat
      let y := c.2.toNat
      have hw0 : 0 ≤ weight d c := by
        unfold weight
        have hp : 0 ≤ (d : ℤ) * c.2 := mul_nonneg (by omega) hy
        omega
      have hkc : (k : ℤ) = weight d c := Int.toNat_of_nonneg hw0
      have hyc : (y : ℤ) = c.2 := Int.toNat_of_nonneg hy
      have hk : k ≤ K := by omega
      have hprod : y * d ≤ k := by
        have hz : (y : ℤ) * (d : ℤ) ≤ (k : ℤ) := by
          rw [hkc, hyc]
          unfold weight
          nlinarith only [hx]
        exact_mod_cast hz
      have hyd : y ≤ k / d := (Nat.le_div_iff_mul_le hd).mpr hprod
      apply mem_image.mpr
      refine ⟨⟨k, y⟩, mem_sigma.mpr ⟨mem_range.mpr (show k < K + 1 by omega), ?_⟩, ?_⟩
      · rw [mem_range]
        change y < if k = K then q + 1 else k / d + 1
        by_cases heq : k = K
        · rw [if_pos heq]
          have hty := htop (by omega)
          omega
        · rw [if_neg heq]
          omega
      · apply Prod.ext
        · change (k : ℤ) - (d : ℤ) * (y : ℤ) = c.1
          rw [hkc, hyc]
          unfold weight
          ring
        · exact hyc
  have board_card (d K q : ℕ) :
      (board d K q).card = H d K + K + q + 1 := by
    classical
    unfold board
    rw [card_image_of_injOn (coord_injective d).injOn]
    unfold boardLabels
    rw [card_sigma, sum_range_succ]
    simp only [card_range]
    have heq : (∑ k ∈ range K, if k = K then q + 1 else k / d + 1) =
        ∑ k ∈ range K, (k / d + 1) := by
      apply sum_congr rfl
      intro k hk
      rw [if_neg (by have hh := mem_range.mp hk; omega)]
    rw [heq]
    simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, Nat.cast_id,
      mul_one, ite_true, Nat.add_assoc, H]
  have Adj_symm (c c' : Cell) (h : Adj c c') : Adj c' c := by
    unfold Adj at h ⊢
    rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · exact Or.inl ⟨hx.symm, hy.symm⟩
    · exact Or.inr ⟨hy.symm, hx.symm⟩
  have downset_polyomino (P : Finset Cell) (h0 : (0, 0) ∈ P)
      (hpos : ∀ c ∈ P, 0 ≤ c.1 ∧ 0 ≤ c.2)
      (hlower : ∀ c ∈ P, ∀ c' : Cell,
        0 ≤ c'.1 → 0 ≤ c'.2 → c'.1 ≤ c.1 → c'.2 ≤ c.2 → c' ∈ P) :
      IsPolyomino P := by
    let r := fun a b : Cell => a ∈ P ∧ b ∈ P ∧ Adj a b
    have hxpath : ∀ x y : ℕ, ((x : ℤ), (y : ℤ)) ∈ P →
        Relation.ReflTransGen r ((0 : ℤ), (y : ℤ)) ((x : ℤ), (y : ℤ)) := by
      intro x
      induction x with
      | zero => intro y hy; exact .refl
      | succ x ih =>
        intro y hy
        have hx : ((x : ℤ), (y : ℤ)) ∈ P :=
          hlower _ hy _ (by omega) (by omega) (by omega) (le_refl _)
        exact (ih y hx).tail
          ⟨hx, hy, Or.inr ⟨rfl, Or.inl (by simp only [Nat.cast_add, Nat.cast_one])⟩⟩
    have hypath : ∀ y x : ℕ, ((x : ℤ), (y : ℤ)) ∈ P →
        Relation.ReflTransGen r ((x : ℤ), (0 : ℤ)) ((x : ℤ), (y : ℤ)) := by
      intro y
      induction y with
      | zero => intro x hx; exact .refl
      | succ y ih =>
        intro x hx
        have hy : ((x : ℤ), (y : ℤ)) ∈ P :=
          hlower _ hx _ (by omega) (by omega) (le_refl _) (by omega)
        exact (ih x hy).tail
          ⟨hy, hx, Or.inl ⟨rfl, Or.inl (by simp only [Nat.cast_add, Nat.cast_one])⟩⟩
    have hpath : ∀ c ∈ P, Relation.ReflTransGen r (0, 0) c := by
      intro c hc
      have hx := (hpos c hc).1
      have hy := (hpos c hc).2
      have hc' : ((c.1.toNat : ℤ), (c.2.toNat : ℤ)) ∈ P := by
        simpa only [Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy, Prod.eta] using hc
      have hb : ((c.1.toNat : ℤ), (0 : ℤ)) ∈ P :=
        hlower _ hc' _ (by omega) (le_refl _) (le_refl _) (by omega)
      have hh := (hxpath c.1.toNat 0 hb).trans (hypath c.2.toNat c.1.toNat hc')
      simpa only [Nat.cast_zero, Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy, Prod.eta] using hh
    have hrev : ∀ c c' : Cell, Relation.ReflTransGen r c c' → Relation.ReflTransGen r c' c := by
      intro c c' h
      induction h with
      | refl => exact .refl
      | @tail c' c'' h hh ih =>
        exact (Relation.ReflTransGen.single ⟨hh.2.1, hh.1, Adj_symm _ _ hh.2.2⟩).trans ih
    refine ⟨⟨(0, 0), h0⟩, ?_⟩
    intro c hc c' hc'
    exact (hrev _ _ (hpath c hc)).trans (hpath c' hc')
  have board_polyomino (d K q : ℕ) (hd : 0 < d) (hq : q ≤ K / d) :
      IsPolyomino (board d K q) := by
    have hmem := mem_board d K q hd hq
    apply downset_polyomino
    · rw [hmem]
      simp only [Std.le_refl, mul_zero, add_zero, Nat.cast_nonneg, implies_true, and_self, weight]
    · intro c hc
      exact ⟨((hmem c).mp hc).1, ((hmem c).mp hc).2.1⟩
    · intro c hc c' hx hy hxc hyc
      have hh := (hmem c).mp hc
      have hmul : (d : ℤ) * c'.2 ≤ (d : ℤ) * c.2 := mul_le_mul_of_nonneg_left hyc (by omega)
      have hw : weight d c' ≤ weight d c := by unfold weight; omega
      apply (hmem c').mpr
      refine ⟨hx, hy, le_trans hw hh.2.2.1, ?_⟩
      intro heq
      have hcK : weight d c = K := by omega
      exact le_trans hyc (hh.2.2.2 hcK)
  have board_top_card (d K q : ℕ) :
      ((board d K q).filter fun c => 0 < c.2).card = H d K + q := by
    classical
    let F := (range (K + 1)).sigma fun k =>
      Ico 1 (if k = K then q + 1 else k / d + 1)
    have hset : (board d K q).filter (fun c => 0 < c.2) = F.image (coord d) := by
      ext c
      constructor
      · intro hc
        rcases mem_filter.mp hc with ⟨hcb, hcy⟩
        rcases mem_image.mp hcb with ⟨u, hu, rfl⟩
        have hh := mem_sigma.mp hu
        apply mem_image.mpr
        refine ⟨u, mem_sigma.mpr ⟨hh.1, mem_Ico.mpr ⟨?_, mem_range.mp hh.2⟩⟩, rfl⟩
        change 0 < (u.snd : ℤ) at hcy
        omega
      · intro hc
        rcases mem_image.mp hc with ⟨u, hu, rfl⟩
        have hh := mem_sigma.mp hu
        have hy := mem_Ico.mp hh.2
        apply mem_filter.mpr
        refine ⟨mem_image.mpr ⟨u, mem_sigma.mpr ⟨hh.1, mem_range.mpr hy.2⟩, rfl⟩, ?_⟩
        change 0 < (u.snd : ℤ)
        omega
    rw [hset, card_image_of_injOn (coord_injective d).injOn]
    dsimp [F]
    rw [card_sigma, sum_range_succ]
    simp only [Nat.card_Ico]
    have heq : (∑ k ∈ range K, ((if k = K then q + 1 else k / d + 1) - 1)) = H d K := by
      apply sum_congr rfl
      intro k hk
      rw [if_neg (by have hh := mem_range.mp hk; omega)]
      exact Nat.add_sub_cancel _ _
    rw [heq]
    simp only [ite_true, add_tsub_cancel_right]
  have board_instances (n K q : ℕ) (hn : 3 ≤ n) (hq : q ≤ K / (n - 2)) :
      (instances (board (n - 2) K q) (L n)).card = H (n - 2) K + q := by
    classical
    let d := n - 2
    have hd : 0 < d := by dsimp [d]; omega
    let P := board d K q
    have hmem := mem_board d K q hd hq
    have hcard : (instances P (L n)).card = (P.filter fun c => 0 < c.2).card := by
      apply card_bij (fun v _ => (0, 1) + v)
      · intro v hv
        have hh := (mem_instances P (L n) (zero_mem_L n hn) v).mp hv
        have hvP := anchor_mem P n hn v hv
        have hy := ((hmem v).mp hvP).2.1
        apply mem_filter.mpr
        refine ⟨hh (0, 1) (top_mem_L n), ?_⟩
        change 0 < 1 + v.2
        omega
      · intro v hv v' hv' heq
        exact translate_injective (0, 1) heq
      · intro c hc
        have hh := mem_filter.mp hc
        have hb := (hmem c).mp hh.1
        let v := c - (0, 1)
        have hv : v ∈ instances P (L n) := by
          apply (mem_instances P (L n) (zero_mem_L n hn) v).mpr
          intro u hu
          rcases mem_union.mp hu with hbottom | htop
          · rcases mem_image.mp hbottom with ⟨i, hi, rfl⟩
            have hid : i ≤ d := by have hr := mem_range.mp hi; dsimp [d]; omega
            apply (hmem _).mpr
            have hx : 0 ≤ (((i : ℤ), 0) + v).1 := by
              change 0 ≤ (i : ℤ) + (c.1 - 0)
              omega
            have hy : 0 ≤ (((i : ℤ), 0) + v).2 := by
              change 0 ≤ 0 + (c.2 - 1)
              omega
            have hw : weight d (((i : ℤ), 0) + v) = weight d c + (i : ℤ) - d := by
              dsimp [v]
              simp only [weight, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
              ring
            refine ⟨hx, hy, ?_, ?_⟩
            · rw [hw]
              omega
            · intro heq
              rw [hw] at heq
              have hcK : weight d c = K := by omega
              have hcy := hb.2.2.2 hcK
              change 0 + (c.2 - 1) ≤ (q : ℤ)
              omega
          · have hu0 : u = (0, 1) := mem_singleton.mp htop
            subst u
            have heq : (0, 1) + v = c := by
              dsimp [v]
              simp only [add_sub_cancel]
            rw [heq]
            exact hh.1
        refine ⟨v, hv, ?_⟩
        dsimp [v]
        simp only [add_sub_cancel]
    rw [hcard]
    exact board_top_card d K q
  have upper_board (n N : ℕ) (hn : 3 ≤ n) (hN : 1 ≤ N) :
      ∃ P : Finset Cell, IsPolyomino P ∧ (instances P (L n)).card = N ∧
        P.card = f (n - 2) N := by
    let d := n - 2
    have hd : 0 < d := by dsimp [d]; omega
    let K := cutoff d N
    let q := N - H d K
    have hlo : H d K < N := (cutoff_lower d N hd hN).2
    have hup : N ≤ H d (K + 1) := cutoff_spec d N hd
    have hq : q ≤ K / d := by have hh := H_succ d K; dsimp [q]; omega
    refine ⟨board d K q, board_polyomino d K q hd hq, ?_, ?_⟩
    · rw [board_instances n K q hn hq]
      change H d K + q = N
      dsimp [q]
      omega
    · rw [board_card]
      change H d K + K + q + 1 = N + 1 + K
      dsimp [q]
      omega
  have minimum_formula (n N : ℕ) (hn : 3 ≤ n) (hN : 1 ≤ N) :
      a (L n) N = f (n - 2) N := by
    classical
    let d := n - 2
    have hd : 0 < d := by dsimp [d]; omega
    obtain ⟨P, hP, hI, hcard⟩ := upper_board n N hn hN
    have hmem : f d N ∈ {S : ℕ | ∃ P : Finset Cell,
        IsPolyomino P ∧ N ≤ (instances P (L n)).card ∧ P.card = S} :=
      ⟨P, hP, by omega, hcard⟩
    have hu : a (L n) N ≤ f d N := Nat.sInf_le hmem
    have hmin := Nat.sInf_mem (show ({S : ℕ | ∃ P : Finset Cell,
      IsPolyomino P ∧ N ≤ (instances P (L n)).card ∧ P.card = S} : Set ℕ).Nonempty
      from ⟨f d N, hmem⟩)
    rcases hmin with ⟨Q, hQ, hQI, hQa⟩
    have hbound := geometric_bound Q n hn
    let I := (instances Q (L n)).card
    let D := Q.card - I
    have hND : N ≤ H d D := by dsimp [I, D, d]; omega
    have hD : 1 ≤ D := by
      by_contra hh
      have hDz : D = 0 := by omega
      rw [hDz, H_zero] at hND
      omega
    have hcut := cutoff_min d N (D - 1) hd (by
      rw [show D - 1 + 1 = D by omega]
      exact hND)
    have hsize : f d N ≤ Q.card := by dsimp [f, D, I] at *; omega
    change Q.card = a (L n) N at hQa
    rw [hQa] at hsize
    exact le_antisymm hu hsize
  intro n N hn hN
  rw [minimum_formula n N hn hN, arithmetic_identification (n - 2) N (by omega) hN]
  have heq : n - 2 + 2 = n := by omega
  rw [heq]

#print axioms result
end D5.S3.Combinatorics.Polyomino.LPolyominoSkippedSequence
