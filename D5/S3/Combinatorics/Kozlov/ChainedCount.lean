/- GID: D5/S3/Combinatorics/Kozlov/ChainedCount
   generality: G
   mirror-B: none(waiver:probe-support)
   mirror-E: none(waiver:literal-equal-shift-counting)
   anchors: []
   utility: none
   digest: Chained sums are injective and their counts are transfer matrix entries. -/

import D5.S3.Combinatorics.Kozlov.ProperSumset
import D5.S3.Combinatorics.Kozlov.TransferCount
import Mathlib.Data.Set.Card

set_option autoImplicit false

open Finset Matrix
open scoped BigOperators

namespace D5.S3.Combinatorics.Kozlov

variable {n : ℕ}

abbrev cap (j : Fin (n + 1)) : ℕ := n.choose j.val

theorem cap_pos (j : Fin (n + 1)) : 0 < cap j := Nat.choose_pos (by omega)

def firstDegree (hn : 1 ≤ n) : Fin (n + 1) := ⟨1, by omega⟩

def Bounded (f : FVector n) : Prop := ∀ j, f j ≤ cap j

def Fixed (hn : 1 ≤ n) (f : FVector n) : Prop :=
  f 0 = 1 ∧ f (firstDegree hn) = n

def skeleton (n k : ℕ) : FVector n := fun j => if j.val ≤ k then cap j else 0

theorem skeleton_mem_SnF {k : ℕ} (hk : 1 ≤ k) : skeleton n k ∈ SnF n := by
  let D : Family n := univ.filter (fun s => #s ≤ k)
  have hD : IsComplex D := {
    down := by
      intro s t hs hst
      simp only [D, mem_filter, mem_univ, true_and] at hs ⊢
      exact (card_le_card hst).trans hs
    empty_mem := by simp [D]
    singleton_mem := by simp [D, hk] }
  refine ⟨D, hD, ?_⟩
  funext j
  have h : D.filter (fun s => #s = j.val) = if j.val ≤ k then layer n j.val else ∅ := by
    ext s
    by_cases hj : j.val ≤ k
    · simp only [D, mem_filter, mem_univ, true_and, ite_eq_left hj, mem_layer]
      exact ⟨And.right, fun h => ⟨h ▸ hj, h⟩⟩
    · simp only [D, mem_filter, mem_univ, true_and, ite_eq_right hj, notMem_empty, iff_false]
      exact fun h => hj (h.2 ▸ h.1)
  simp only [fVector, fEntry, h, skeleton]
  split_ifs <;> simp

theorem SnF_bounded {f : FVector n} (hf : f ∈ SnF n) : Bounded f := by
  obtain ⟨D, _, rfl⟩ := hf
  intro j
  have := fEntry_add_card_missing D j.val
  exact Nat.le.intro this

theorem SnF_fixed (hn : 1 ≤ n) {f : FVector n} (hf : f ∈ SnF n) : Fixed hn f := by
  obtain ⟨D, hD, rfl⟩ := hf
  constructor
  · simpa [fVector, missing_zero hD] using fEntry_add_card_missing D 0
  · simpa [fVector, firstDegree, missing_one hD] using fEntry_add_card_missing D 1

theorem le_top_of_pos {f : FVector n} {j : Fin (n + 1)} (h : 0 < f j) :
    (j.val : ℤ) ≤ top f := by
  have hj : j ∈ univ.filter (fun k : Fin (n + 1) => 0 < f k) := mem_filter.mpr ⟨mem_univ _, h⟩
  have hne : (univ.filter fun k : Fin (n + 1) => 0 < f k).Nonempty := ⟨j, hj⟩
  unfold top
  rw [dite_eq_left hne]
  exact_mod_cast Finset.le_max' _ j hj

theorem vanish_of_top_lt {f : FVector n} {j : Fin (n + 1)} (h : top f < (j.val : ℤ)) :
    f j = 0 := by
  by_contra hpos
  exact (not_le.mpr h) (le_top_of_pos (Nat.pos_of_ne_zero hpos))

theorem indeg_le_of_lt_cap {f : FVector n} {j : Fin (n + 1)} (h : f j < cap j) :
    indeg f ≤ j.val := by
  have hj : j ∈ univ.filter (fun k : Fin (n + 1) => f k < cap k) := mem_filter.mpr ⟨mem_univ _, h⟩
  have hne : (univ.filter fun k : Fin (n + 1) => f k < cap k).Nonempty := ⟨j, hj⟩
  unfold indeg
  rw [dite_eq_left hne]
  exact Finset.min'_le _ j hj

theorem full_below_indeg {f : FVector n} (hb : Bounded f) {j : Fin (n + 1)}
    (hj : j.val < indeg f) : f j = cap j :=
  (hb j).antisymm (not_lt.mp fun h => (not_le.mpr hj) (indeg_le_of_lt_cap h))

theorem lt_indeg_iff (k : Fin (n + 1)) {f : FVector n} (hf : Bounded f) :
    k.val < indeg f ↔ ∀ j : Fin (n + 1), j ≤ k → f j = cap j := by
  constructor
  · intro h j hj
    exact full_below_indeg hf (lt_of_le_of_lt hj h)
  · intro h
    rcases indeg_eq_sentinel_or_missing f with hs | ⟨j, hj, hmiss⟩
    · rw [hs]
      exact k.isLt
    · by_contra! hle
      exact (ne_of_lt hmiss) (h j (by omega))

theorem top_skeleton (k : Fin (n + 1)) : top (skeleton n k.val) = (k.val : ℤ) := by
  apply le_antisymm
  · have h : top (skeleton n k.val) < ((k.val + 1 : ℕ) : ℤ) := by
      apply top_lt_of_vanish
      intro j hj
      simp [skeleton, show ¬j.val ≤ k.val by omega]
    omega
  · apply le_top_of_pos
    simpa [skeleton] using cap_pos k

/-- The last summand at any coordinate is determined by the total and the capacity. -/
private theorem last_eq_min {r : ℕ} {s : Fin (r + 1) → FVector n}
    (h : Chained s) (hs : ∀ i, Bounded (s i)) (j : Fin (n + 1)) :
    s (Fin.last r) j = min (cap j) (sumTuple s j) := by
  by_cases heq : s (Fin.last r) j = cap j
  · rw [heq, min_eq_left]
    rw [← heq]
    exact Finset.single_le_sum (f := fun i : Fin (r + 1) => s i j)
      (fun _ _ => Nat.zero_le _) (mem_univ (Fin.last r))
  · have hlt := lt_of_le_of_ne (hs (Fin.last r) j) heq
    have step (i : Fin r) (hnext : s i.succ j < cap j) : s i.castSucc j = 0 := by
      have htop := h (i := i.castSucc) (j := i.succ) rfl
      have hindeg := indeg_le_of_lt_cap hnext
      exact vanish_of_top_lt (by omega)
    have hzero : ∀ i : Fin (r + 1), i.val < r → s i j = 0 := by
      intro i
      induction i using Fin.reverseInduction with
      | last => simp
      | cast i ih =>
        intro _
        by_cases hi : i.succ.val < r
        · apply step i
          rw [ih hi]
          exact cap_pos j
        · have hi' : i.succ = Fin.last r := Fin.ext (by simp only [Fin.val_last]; have := i.succ.isLt; omega)
          exact step i (hi' ▸ hlt)
    have hsum : sumTuple s j = s (Fin.last r) j := by
      apply Finset.sum_eq_single (Fin.last r)
      · intro i _ hi
        exact hzero i (by
          have hi' : i.val ≠ r := fun e => hi (Fin.ext e)
          omega)
      · simp
    rw [hsum, min_eq_right hlt.le]

theorem chained_sum_injective {r : ℕ} {s t : Fin r → FVector n}
    (hs : Chained s) (ht : Chained t) (hbs : ∀ i, Bounded (s i))
    (hbt : ∀ i, Bounded (t i)) (e : sumTuple s = sumTuple t) : s = t := by
  induction r with
  | zero => funext i; exact i.elim0
  | succ r ih =>
    have hl : s (Fin.last r) = t (Fin.last r) := by
      funext j
      rw [last_eq_min hs hbs, last_eq_min ht hbt, e]
    have hp : Fin.init s = Fin.init t := by
      apply ih
      · intro i j hij
        exact hs (i := i.castSucc) (j := j.castSucc) hij
      · intro i j hij
        exact ht (i := i.castSucc) (j := j.castSucc) hij
      · exact fun i => hbs i.castSucc
      · exact fun i => hbt i.castSucc
      · funext j
        have he := congrFun e j
        simp only [sumTuple, Fin.sum_univ_castSucc] at he
        rw [hl] at he
        exact Nat.add_right_cancel he
    rw [← Fin.snoc_init_self s, ← Fin.snoc_init_self t, hp, hl]

def topState (hn : 1 ≤ n) (f : FVector n) : Fin n :=
  ⟨(top f).toNat - 1, by have := top_le f; omega⟩

theorem topState_val (hn : 1 ≤ n) {f : FVector n} (hf : Fixed hn f) :
    ((topState hn f).val : ℤ) + 1 = top f := by
  have hp : 0 < f (firstDegree hn) := by rw [hf.2]; omega
  have h := le_top_of_pos hp
  change (1 : ℤ) ≤ top f at h
  dsimp [topState]
  omega

def cond (_hn : 1 ≤ n) (i : Fin n) (f : FVector n) : Prop :=
  i.val + 1 < indeg f

instance (hn : 1 ≤ n) (i : Fin n) (f : FVector n) : Decidable (cond hn i f) := by
  unfold cond
  infer_instance

theorem chainG_iff (hn : 1 ≤ n) {r : ℕ} {s : Fin (r + 1) → FVector n}
    (h : ∀ i, Fixed hn (s i)) : ChainG (topState hn) (cond hn) s ↔ Chained s := by
  constructor
  · intro hc i j hij
    have hi : i.val < r := by have := j.isLt; omega
    let p : Fin r := ⟨i.val, hi⟩
    have ha : p.castSucc = i := Fin.ext rfl
    have hb : p.succ = j := Fin.ext hij
    have hp := hc p
    change (topState hn (s p.castSucc)).val + 1 < indeg (s p.succ) at hp
    rw [ha, hb] at hp
    have := topState_val hn (h i)
    omega
  · intro hc i
    have hi := hc (i := i.castSucc) (j := i.succ) rfl
    have := topState_val hn (h i.castSucc)
    change (topState hn (s i.castSucc)).val + 1 < indeg (s i.succ)
    omega

noncomputable def properVectors (n : ℕ) : Finset (FVector n) := by
  classical
  exact ((univ : Finset (Family n)).filter IsComplex).image fVector

@[simp] theorem mem_properVectors {f : FVector n} : f ∈ properVectors n ↔ f ∈ SnF n := by
  classical
  simp [properVectors, SnF]

def standard {m : ℕ} (i : Fin m) : Fin m → ℕ := fun j => if j = i then 1 else 0

noncomputable def transfer (hn : 1 ≤ n) (S : Finset (FVector n)) : Matrix (Fin n) (Fin n) ℕ :=
  TG S (topState hn) (cond hn)

theorem card_of_chained_image (hn : 1 ≤ n) (S : Finset (FVector n))
    (hb : ∀ f ∈ S, Bounded f) (hf : ∀ f ∈ S, Fixed hn f) {r : ℕ} {target : Set (FVector n)}
    (himage : sumTuple '' {s : Fin (r + 1) → FVector n | (∀ i, s i ∈ S) ∧ Chained s} = target) :
    target.ncard = uG S (topState hn) ᵥ* transfer hn S ^ r ⬝ᵥ (fun _ => 1) := by
  classical
  let T := chainG S (topState hn) (cond hn) r
  have hT {s : Fin (r + 1) → FVector n} :
      s ∈ T ↔ (∀ i, s i ∈ S) ∧ Chained s := by
    simp only [T, chainG, mem_filter, Fintype.mem_piFinset]
    exact and_congr_right (fun hs => chainG_iff hn (fun i => hf _ (hs i)))
  have hEq : (T : Set (Fin (r + 1) → FVector n)) =
      {s | (∀ i, s i ∈ S) ∧ Chained s} := Set.ext fun _ => hT
  have hinj : Set.InjOn sumTuple (T : Set (Fin (r + 1) → FVector n)) := by
    intro s hs t ht he
    obtain ⟨hs', hcs⟩ := hT.mp hs
    obtain ⟨ht', hct⟩ := hT.mp ht
    exact chained_sum_injective hcs hct (fun i => hb _ (hs' i)) (fun i => hb _ (ht' i)) he
  rw [← himage, ← hEq, Set.InjOn.ncard_image hinj, Set.ncard_coe_finset]
  exact card_chainG (X := S) (σ := topState hn) (cond := cond hn) r

theorem proper_count_transfer (hn : 1 ≤ n) (r : ℕ) :
    (properSumset n (r + 1)).ncard =
      uG (properVectors n) (topState hn) ᵥ* transfer hn (properVectors n) ^ r ⬝ᵥ (fun _ => 1) := by
  apply card_of_chained_image hn (properVectors n)
  · exact fun _ h => SnF_bounded (mem_properVectors.mp h)
  · exact fun _ h => SnF_fixed hn (mem_properVectors.mp h)
  ext x
  simp only [mem_properVectors]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs.1, rfl⟩
  · exact fun hx => proper_sumset_surjOn n (r + 1) hx

theorem SnF_terminal {f : FVector n} (hf : f ∈ SnF n)
    (h : top f = (n : ℤ)) : f = skeleton n n := by
  obtain ⟨D, hD, rfl⟩ := hf
  have hpos : 0 < fVector D (Fin.last n) := by
    unfold top at h
    split at h
    · rename_i hne
      let j := (univ.filter fun j : Fin (n + 1) => 0 < fVector D j).max' hne
      have hj : j = Fin.last n := Fin.ext (by change (j.val : ℤ) = (n : ℤ) at h; simp only [Fin.val_last]; omega)
      rw [← hj]
      exact (mem_filter.mp (max'_mem _ hne)).2
    · omega
  obtain ⟨t, ht⟩ := card_pos.mp hpos
  obtain ⟨htD, htn⟩ := mem_filter.mp ht
  have hu : t = univ := eq_of_subset_of_card_le (subset_univ _) (by simpa using htn.ge)
  have hD' : D = univ := eq_univ_of_forall fun s => hD.down (hu ▸ htD) (subset_univ s)
  subst D
  funext j
  have hM : missing (univ : Family n) j.val = ∅ := by simp [missing]
  simpa [fVector, hM, skeleton, j.isLt.le, show j.val ≤ n by omega] using
    fEntry_add_card_missing (univ : Family n) j.val

end D5.S3.Combinatorics.Kozlov
