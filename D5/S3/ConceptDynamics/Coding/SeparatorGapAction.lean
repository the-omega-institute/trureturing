/- GID: D5/S3/ConceptDynamics/Coding/SeparatorGapAction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/SeparatorGapAction
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Length-separated separator replacements on arbitrary bilateral histories. -/
import D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Data.Finset.NoncommProd

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.SeparatorGapAction

open EssentialWordRealization StandardBeamHomeomorphisms
open FiniteWindowTableCriterion (historyWindow)
universe u v w

/-- A common separator and injectively indexed, separator-free data lengths. -/
structure Family (E : Type u) (I : ℕ → Type v) (d : ℕ → ℕ) where
  separator : E
  positive : ∀ n, 0 < d n
  length_injective : Function.Injective d
  data : ∀ n, I n → Fin (d n) → E
  data_injective : ∀ n, Function.Injective (data n)
  avoids : ∀ n i j, data n i j ≠ separator

variable {E : Type u} {I : ℕ → Type v} {d : ℕ → ℕ} (F : Family E I d)

/-- Two consecutive separators, without any eligibility assumption on the data. -/
private def Gap (x : ℤ → E) (s : ℤ) (l : ℕ) : Prop :=
  x s = F.separator ∧ x (s + (l : ℤ) + 1) = F.separator ∧
    ∀ t : ℤ, s < t → t < s + (l : ℤ) + 1 → x t ≠ F.separator

/-- Selection is tested on the entire gap; other gaps and both infinite tails are arbitrary. -/
def Selected (n : ℕ) (x : ℤ → E) (s : ℤ) (i : I n) : Prop :=
  x s = F.separator ∧ x (s + (d n : ℤ) + 1) = F.separator ∧
    ∀ j : Fin (d n), x (s + 1 + (j.val : ℤ)) = F.data n i j

private theorem selected_gap {n : ℕ} {x : ℤ → E} {s : ℤ} {i : I n}
    (h : Selected F n x s i) : Gap F x s (d n) := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro t ht hr
  let j : Fin (d n) := ⟨(t-s-1).toNat, by omega⟩
  have he : s + 1 + (j.val : ℤ) = t := by dsimp [j]; omega
  rw [← he, h.2.2 j]
  exact F.avoids n i j

/-- Overlapping open intervals between consecutive separators have identical endpoints. -/
private theorem gap_bounds {x : ℤ → E} {s a t : ℤ} {l k : ℕ}
    (hs : Gap F x s l) (ha : Gap F x a k)
    (hst : s < t ∧ t < s + (l : ℤ) + 1)
    (hat : a < t ∧ t < a + (k : ℤ) + 1) : s = a ∧ l = k := by
  have he : s = a := by
    rcases lt_trichotomy s a with h | h | h
    · exact False.elim (hs.2.2 a h (by omega) ha.1)
    · exact h
    · exact False.elim (ha.2.2 s h (by omega) hs.1)
  subst a
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy l k with h | h | h
  · exact False.elim (ha.2.2 (s + (l : ℤ) + 1) (by omega) (by omega) hs.2.1)
  · exact h
  · exact False.elim (hs.2.2 (s + (k : ℤ) + 1) (by omega) (by omega) ha.2.1)

private theorem label_unique {n : ℕ} {x : ℤ → E} {s : ℤ} {i j : I n}
    (hi : Selected F n x s i) (hj : Selected F n x s j) : i = j := by
  apply F.data_injective n
  funext k
  exact (hi.2.2 k).symm.trans (hj.2.2 k)

private structure Hit (n : ℕ) (x : ℤ → E) (t : ℤ) where
  start : ℤ
  symbol : I n
  offset : Fin (d n)
  selected : Selected F n x start symbol
  coordinate : t = start + 1 + (offset.val : ℤ)

private theorem hit_bounds {n m : ℕ} {x : ℤ → E} {s t : ℤ}
    (hs : Gap F x s (d m)) (ht : s < t ∧ t < s + (d m : ℤ) + 1)
    (hit : Hit F n x t) : hit.start = s ∧ n = m := by
  have hj := hit.offset.isLt
  have hc := hit.coordinate
  obtain ⟨ha, hd⟩ := gap_bounds F (selected_gap F hit.selected) hs
    (by omega) ht
  exact ⟨ha, F.length_injective hd⟩

/-- Only the selected interiors are replaced, simultaneously on the whole sequence. -/
def replace (n : ℕ) (σ : Equiv.Perm (I n)) (x : ℤ → E) (t : ℤ) : E := by
  classical
  exact if h : Nonempty (Hit F n x t) then
    F.data n (σ (Classical.choice h).symbol) (Classical.choice h).offset
  else x t

private theorem replace_off (n : ℕ) (σ : Equiv.Perm (I n)) {x : ℤ → E} {t : ℤ}
    (h : ¬ Nonempty (Hit F n x t)) : replace F n σ x t = x t := by
  classical
  simp only [replace, dif_neg h]

private theorem replace_at (n : ℕ) (σ : Equiv.Perm (I n)) {x : ℤ → E}
    {s : ℤ} {i : I n} (hs : Selected F n x s i) (j : Fin (d n)) :
    replace F n σ x (s + 1 + (j.val : ℤ)) = F.data n (σ i) j := by
  classical
  have h : Nonempty (Hit F n x (s + 1 + (j.val : ℤ))) := ⟨⟨s, i, j, hs, rfl⟩⟩
  rw [replace, dif_pos h]
  let hit := Classical.choice h
  have hj := j.isLt
  have ha := (hit_bounds F (selected_gap F hs) (by omega) hit).1
  have hi : hit.symbol = i := label_unique F (by simpa only [ha] using hit.selected) hs
  have ho : hit.offset = j := by
    apply Fin.ext
    have hc := hit.coordinate
    omega
  change F.data n (σ hit.symbol) hit.offset = _
  rw [hi, ho]

/-- Exactly the original separator positions survive; no separator is created. -/
theorem separator_iff (n : ℕ) (σ : Equiv.Perm (I n)) (x : ℤ → E) (t : ℤ) :
    replace F n σ x t = F.separator ↔ x t = F.separator := by
  classical
  unfold replace
  split_ifs with h
  · let hit := Classical.choice h
    have hc := hit.coordinate
    have hne : x t ≠ F.separator := by
      rw [hc, hit.selected.2.2 hit.offset]
      exact F.avoids n hit.symbol hit.offset
    exact iff_of_false (F.avoids n (σ hit.symbol) hit.offset) hne
  · rfl

private theorem gap_iff (n : ℕ) (σ : Equiv.Perm (I n)) (x : ℤ → E) (s : ℤ) (l : ℕ) :
    Gap F (replace F n σ x) s l ↔ Gap F x s l := by
  simp only [Gap, ne_eq, separator_iff]

private theorem forward (n : ℕ) (σ : Equiv.Perm (I n)) {x : ℤ → E}
    {s : ℤ} {i : I n} (hs : Selected F n x s i) :
    Selected F n (replace F n σ x) s (σ i) :=
  ⟨(separator_iff F n σ x s).mpr hs.1,
    (separator_iff F n σ x _).mpr hs.2.1, replace_at F n σ hs⟩

/-- Both directions hold even when a gap was initially not a code word. -/
theorem selected_same (n : ℕ) (σ : Equiv.Perm (I n)) (x : ℤ → E) (s : ℤ) (i : I n) :
    Selected F n (replace F n σ x) s (σ i) ↔ Selected F n x s i := by
  classical
  constructor
  · intro hs
    have hg := (gap_iff F n σ x s (d n)).mp (selected_gap F hs)
    by_cases hold : ∃ j, Selected F n x s j
    · obtain ⟨j, hj⟩ := hold
      have he := σ.injective (label_unique F (forward F n σ hj) hs)
      simpa only [he] using hj
    · have hoff (j : Fin (d n)) : replace F n σ x (s + 1 + (j.val : ℤ)) =
          x (s + 1 + (j.val : ℤ)) := by
        apply replace_off
        rintro ⟨hit⟩
        have hj := j.isLt
        have ha := (hit_bounds F hg (by omega) hit).1
        exact hold ⟨hit.symbol, by simpa only [ha] using hit.selected⟩
      have hnew : Selected F n x s (σ i) :=
        ⟨hg.1, hg.2.1, fun j => (hoff j).symm.trans (hs.2.2 j)⟩
      exact False.elim (hold ⟨σ i, hnew⟩)
  · exact forward F n σ

private theorem off_other_gap {n m : ℕ} (hnm : n ≠ m) (σ : Equiv.Perm (I n))
    {x : ℤ → E} {s : ℤ} (hs : Gap F x s (d m)) (j : Fin (d m)) :
    replace F n σ x (s + 1 + (j.val : ℤ)) = x (s + 1 + (j.val : ℤ)) := by
  apply replace_off
  rintro ⟨hit⟩
  have hj := j.isLt
  exact hnm (hit_bounds F hs (by omega) hit).2

/-- A different length keeps every selected data coordinate pointwise fixed. -/
theorem replace_on_other_gap {n m : ℕ} (hnm : n ≠ m) (σ : Equiv.Perm (I n))
    {x : ℤ → E} {s : ℤ} {i : I m} (hs : Selected F m x s i) (j : Fin (d m)) :
    replace F n σ x (s + 1 + (j.val : ℤ)) = x (s + 1 + (j.val : ℤ)) :=
  off_other_gap F hnm σ (selected_gap F hs) j

/-- Different lengths neither destroy nor create eligibility, on all sequences. -/
theorem selected_other {n m : ℕ} (hnm : n ≠ m) (σ : Equiv.Perm (I n))
    (x : ℤ → E) (s : ℤ) (i : I m) :
    Selected F m (replace F n σ x) s i ↔ Selected F m x s i := by
  constructor
  · intro hs
    have hg := (gap_iff F n σ x s (d m)).mp (selected_gap F hs)
    exact ⟨hg.1, hg.2.1, fun j =>
      (off_other_gap F hnm σ hg j).symm.trans (hs.2.2 j)⟩
  · intro hs
    exact ⟨(separator_iff F n σ x _).mpr hs.1,
      (separator_iff F n σ x _).mpr hs.2.1, fun j =>
        (replace_on_other_gap F hnm σ hs j).trans (hs.2.2 j)⟩

private theorem hit_same (n : ℕ) (σ : Equiv.Perm (I n)) (x : ℤ → E) (t : ℤ) :
    Nonempty (Hit F n (replace F n σ x) t) ↔ Nonempty (Hit F n x t) := by
  constructor
  · rintro ⟨hit⟩
    refine ⟨⟨hit.start, σ.symm hit.symbol, hit.offset, ?_, hit.coordinate⟩⟩
    apply (selected_same F n σ x _ _).mp
    simpa only [Equiv.apply_symm_apply] using hit.selected
  · rintro ⟨hit⟩
    exact ⟨⟨hit.start, σ hit.symbol, hit.offset, forward F n σ hit.selected, hit.coordinate⟩⟩

private theorem hit_other {n m : ℕ} (hnm : n ≠ m) (σ : Equiv.Perm (I n))
    (x : ℤ → E) (t : ℤ) :
    Nonempty (Hit F m (replace F n σ x) t) ↔ Nonempty (Hit F m x t) := by
  constructor
  · rintro ⟨hit⟩
    exact ⟨⟨hit.start, hit.symbol, hit.offset,
      (selected_other F hnm σ x _ _).mp hit.selected, hit.coordinate⟩⟩
  · rintro ⟨hit⟩
    exact ⟨⟨hit.start, hit.symbol, hit.offset,
      (selected_other F hnm σ x _ _).mpr hit.selected, hit.coordinate⟩⟩

/-- Composition has the ordinary, noncommutative order within each coordinate. -/
theorem replace_mul (n : ℕ) (σ τ : Equiv.Perm (I n)) (x : ℤ → E) :
    replace F n σ (replace F n τ x) = replace F n (σ * τ) x := by
  classical
  funext t
  by_cases h : Nonempty (Hit F n x t)
  · let hit := Classical.choice h
    rw [hit.coordinate, replace_at F n σ (forward F n τ hit.selected),
      replace_at F n (σ * τ) hit.selected]
    rfl
  · rw [replace_off F n σ (mt (hit_same F n τ x t).mp h),
      replace_off F n τ h, replace_off F n (σ * τ) h]

private theorem replace_one (n : ℕ) (x : ℤ → E) : replace F n 1 x = x := by
  classical
  funext t
  by_cases h : Nonempty (Hit F n x t)
  · let hit := Classical.choice h
    rw [hit.coordinate, replace_at F n 1 hit.selected]
    exact (hit.selected.2.2 hit.offset).symm
  · exact replace_off F n 1 h

/-- Spatial interval independence proves commutation; it is not an assumed action law. -/
theorem replace_commute {n m : ℕ} (hnm : n ≠ m) (σ : Equiv.Perm (I n))
    (τ : Equiv.Perm (I m)) (x : ℤ → E) :
    replace F n σ (replace F m τ x) = replace F m τ (replace F n σ x) := by
  classical
  funext t
  by_cases hn : Nonempty (Hit F n x t)
  · let hit := Classical.choice hn
    have hs := (selected_other F hnm.symm τ x _ _).mpr hit.selected
    have hf := forward F n σ hit.selected
    rw [hit.coordinate, replace_at F n σ hs,
      replace_on_other_gap F hnm.symm τ hf, replace_at F n σ hit.selected]
  · have hn' := mt (hit_other F hnm.symm τ x t).mp hn
    rw [replace_off F n σ hn']
    by_cases hm : Nonempty (Hit F m x t)
    · let hit := Classical.choice hm
      have hs := (selected_other F hnm σ x _ _).mpr hit.selected
      rw [hit.coordinate, replace_at F m τ hit.selected, replace_at F m τ hs]
    · rw [replace_off F m τ hm,
        replace_off F m τ (mt (hit_other F hnm σ x t).mp hm), replace_off F n σ hn]

/-- A finite symmetric window determines each output edge. -/
theorem replace_local (n : ℕ) (σ : Equiv.Perm (I n)) (x y : ℤ → E) (t : ℤ)
    (hxy : ∀ s : ℤ, t - ((d n + 1 : ℕ) : ℤ) ≤ s →
      s ≤ t + ((d n + 1 : ℕ) : ℤ) → x s = y s) :
    replace F n σ x t = replace F n σ y t := by
  classical
  have transfer : ∀ {x y : ℤ → E},
      (∀ s : ℤ, t - ((d n + 1 : ℕ) : ℤ) ≤ s →
        s ≤ t + ((d n + 1 : ℕ) : ℤ) → x s = y s) →
      ∀ hit : Hit F n x t, Selected F n y hit.start hit.symbol := by
    intro x y h hit
    have ht := hit.coordinate
    have hj := hit.offset.isLt
    refine ⟨?_, ?_, ?_⟩
    · rw [← h hit.start (by omega) (by omega)]
      exact hit.selected.1
    · rw [← h (hit.start + (d n : ℤ) + 1) (by omega) (by omega)]
      exact hit.selected.2.1
    · intro j
      have hji := j.isLt
      rw [← h (hit.start + 1 + (j.val : ℤ)) (by omega) (by omega)]
      exact hit.selected.2.2 j
  by_cases hx : Nonempty (Hit F n x t)
  · let hit := Classical.choice hx
    rw [hit.coordinate, replace_at F n σ hit.selected, replace_at F n σ (transfer hxy hit)]
  · have hy : ¬ Nonempty (Hit F n y t) := by
      rintro ⟨hit⟩
      exact hx ⟨⟨hit.start, hit.symbol, hit.offset,
        transfer (fun s h₁ h₂ => (hxy s h₁ h₂).symm) hit, hit.coordinate⟩⟩
    rw [replace_off F n σ hx, replace_off F n σ hy]
    exact hxy t (by omega) (by omega)

private theorem selected_translate (n : ℕ) (x : ℤ → E) (s c : ℤ) (i : I n) :
    Selected F n (fun t => x (t + c)) s i ↔ Selected F n x (s + c) i := by
  simp only [Selected]
  constructor <;> rintro ⟨hl, hr, hd⟩
  · exact ⟨hl, by simpa [add_assoc, add_comm, add_left_comm] using hr,
      fun j => by simpa [add_assoc, add_comm, add_left_comm] using hd j⟩
  · exact ⟨hl, by simpa [add_assoc, add_comm, add_left_comm] using hr,
      fun j => by simpa [add_assoc, add_comm, add_left_comm] using hd j⟩

private theorem replace_translate (n : ℕ) (σ : Equiv.Perm (I n))
    (x : ℤ → E) (c t : ℤ) :
    replace F n σ (fun s => x (s + c)) t = replace F n σ x (t + c) := by
  classical
  by_cases h : Nonempty (Hit F n (fun s => x (s + c)) t)
  · let hit := Classical.choice h
    have hs := (selected_translate F n x hit.start c hit.symbol).mp hit.selected
    have ht : t + c = (hit.start + c) + 1 + (hit.offset.val : ℤ) := by
      have hc := hit.coordinate
      omega
    calc
      _ = replace F n σ (fun s => x (s+c)) (hit.start+1+(hit.offset.val : ℤ)) :=
        congrArg _ hit.coordinate
      _ = F.data n (σ hit.symbol) hit.offset := replace_at F n σ hit.selected _
      _ = replace F n σ x ((hit.start+c)+1+(hit.offset.val : ℤ)) :=
        (replace_at F n σ hs _).symm
      _ = _ := congrArg _ ht.symm
  · have h' : ¬ Nonempty (Hit F n x (t + c)) := by
      rintro ⟨hit⟩
      apply h
      exact ⟨⟨hit.start-c, hit.symbol, hit.offset,
        (selected_translate F n x _ c _).mpr (by simpa using hit.selected),
        by have hc := hit.coordinate; omega⟩⟩
    rw [replace_off F n σ h, replace_off F n σ h']

variable {V : Type w} (G : DirectedMultigraph V E)

/-- Data paths run from the separator's TARGET to its SOURCE; no loop is assumed. -/
structure Paths : Prop where
  data_legal : ∀ n i (j : Fin (d n)), ∀ hj : j.val + 1 < d n,
    G.target (F.data n i j) = G.source (F.data n i ⟨j.val + 1, hj⟩)
  data_source : ∀ n i, G.source (F.data n i ⟨0, F.positive n⟩) = G.target F.separator
  data_target : ∀ n i,
    G.target (F.data n i ⟨d n - 1, by have hd := F.positive n; omega⟩) =
      G.source F.separator

variable (P : Paths F G)

include P in
private theorem replace_legal (n : ℕ) (σ : Equiv.Perm (I n)) (x : History G) (t : ℤ) :
    G.target (replace F n σ x.val t) = G.source (replace F n σ x.val (t + 1)) := by
  classical
  by_cases ht : Nonempty (Hit F n x.val t)
  · let hit := Classical.choice ht
    rw [hit.coordinate, replace_at F n σ hit.selected]
    by_cases hj : hit.offset.val + 1 < d n
    · have hn : hit.start + 1 + (hit.offset.val : ℤ) + 1 =
          hit.start + 1 + ((hit.offset.val + 1 : ℕ) : ℤ) := by omega
      rw [hn, replace_at F n σ hit.selected ⟨_, hj⟩]
      exact P.data_legal n (σ hit.symbol) hit.offset hj
    · have hi := hit.offset.isLt
      have ho : hit.offset = ⟨d n - 1, by have hd := F.positive n; omega⟩ := by
        apply Fin.ext
        dsimp only
        omega
      have hn : hit.start + 1 + (hit.offset.val : ℤ) + 1 =
          hit.start + (d n : ℤ) + 1 := by omega
      rw [hn, (separator_iff F n σ x.val _).mpr hit.selected.2.1, ho, P.data_target]
  · rw [replace_off F n σ ht]
    by_cases hn : Nonempty (Hit F n x.val (t + 1))
    · let hit := Classical.choice hn
      have hz : hit.offset.val = 0 := by
        by_contra hz
        apply ht
        exact ⟨⟨hit.start, hit.symbol,
          ⟨hit.offset.val-1, by have hi := hit.offset.isLt; omega⟩, hit.selected,
          by dsimp only; have hc := hit.coordinate; omega⟩⟩
      have ho : hit.offset = ⟨0, F.positive n⟩ := Fin.ext hz
      have hc : t + 1 = hit.start + 1 + (0 : ℤ) := by
        have hc := hit.coordinate
        omega
      have hs := x.property t
      have he := hit.selected.2.2 ⟨0, F.positive n⟩
      have hr := replace_at F n σ hit.selected ⟨0, F.positive n⟩
      simp only [Fin.val_zero, Int.natCast_zero] at he hr
      rw [← hc] at he
      rw [hc, hr, P.data_source]
      rw [he, P.data_source] at hs
      exact hs
    · rw [replace_off F n σ hn]
      exact x.property t

/-- The actual legal-history map, with all noncoded tails retained. -/
def onHistory (n : ℕ) (σ : Equiv.Perm (I n)) (x : History G) : History G :=
  ⟨replace F n σ x.val, replace_legal F G P n σ x⟩

private def windowExtension (n : ℕ) (w : Fin (2 * (d n + 1) + 1) → E) (s : ℤ) : E :=
  if h : 0 ≤ s + ((d n + 1 : ℕ) : ℤ) ∧
      s + ((d n + 1 : ℕ) : ℤ) < (2 * (d n + 1) + 1 : ℕ) then
    w ⟨(s + ((d n + 1 : ℕ) : ℤ)).toNat, by omega⟩
  else w ⟨d n + 1, by omega⟩

private theorem onHistory_continuous [TopologicalSpace E] [DiscreteTopology E]
    (n : ℕ) (σ : Equiv.Perm (I n)) : Continuous (onHistory F G P n σ) := by
  classical
  apply Continuous.subtype_mk
  apply continuous_pi
  intro t
  let f : LegalWord G (2 * (d n + 1) + 1) → E :=
    fun w => replace F n σ (windowExtension n w.edge) 0
  have he : (fun x : History G => (onHistory F G P n σ x).val t) =
      f ∘ (fun x => historyWindow G x (t - ((d n + 1 : ℕ) : ℤ)) _) := by
    funext x
    change replace F n σ x.val t = replace F n σ (windowExtension n _) 0
    rw [← (by simpa using replace_translate F n σ x.val t 0 :
      replace F n σ (fun s => x.val (s+t)) 0 = replace F n σ x.val t)]
    apply replace_local F n σ
    intro s hs₁ hs₂
    have hb : 0 ≤ s + ((d n + 1 : ℕ) : ℤ) ∧
        s + ((d n + 1 : ℕ) : ℤ) < (2 * (d n + 1) + 1 : ℕ) := by omega
    change x.val (s+t) = windowExtension n _ s
    unfold windowExtension
    rw [dif_pos hb]
    change x.val (s+t) = x.val (t - ((d n + 1 : ℕ) : ℤ) +
      (((s + ((d n + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ))
    apply congrArg x.val
    omega
  change Continuous (fun x : History G => (onHistory F G P n σ x).val t)
  rw [he]
  exact (continuous_of_discreteTopology : Continuous f).comp
    (FiniteWindowTableCriterion.historyWindow_continuous G _ _)

/-- Permuting one length gives a homeomorphism with its actual local inverse. -/
def homeomorph [TopologicalSpace E] [DiscreteTopology E]
    (n : ℕ) (σ : Equiv.Perm (I n)) : History G ≃ₜ History G where
  toFun := onHistory F G P n σ
  invFun := onHistory F G P n σ⁻¹
  left_inv x := Subtype.ext (by
    change replace F n σ⁻¹ (replace F n σ x.val) = x.val
    rw [replace_mul, inv_mul_cancel, replace_one])
  right_inv x := Subtype.ext (by
    change replace F n σ (replace F n σ⁻¹ x.val) = x.val
    rw [replace_mul, mul_inv_cancel, replace_one])
  continuous_toFun := onHistory_continuous F G P n σ
  continuous_invFun := onHistory_continuous F G P n σ⁻¹

variable [TopologicalSpace E] [DiscreteTopology E]

/-- Each coordinate acts in the ORIGINAL unit-shift centralizer. -/
def action (n : ℕ) : Equiv.Perm (I n) →* FullAut G where
  toFun σ := ⟨homeomorph F G P n σ, by
    intro x
    apply Subtype.ext
    funext t
    exact replace_translate F n σ x.val 1 t⟩
  map_one' := by
    apply Subtype.ext
    ext x t
    exact congrFun (replace_one F n x.val) t
  map_mul' σ τ := by
    apply Subtype.ext
    ext x t
    exact congrFun (replace_mul F n σ τ x.val).symm t

private theorem action_commute {n m : ℕ} (hnm : n ≠ m)
    (σ : Equiv.Perm (I n)) (τ : Equiv.Perm (I m)) :
    Commute (action F G P n σ) (action F G P m τ) := by
  apply Subtype.ext
  ext x t
  exact congrFun (replace_commute F hnm σ τ x.val) t

/-- Finite support is eventual identity, with no commutativity imposed within a fiber. -/
abbrev FinitePerm (J : ℕ → Type v) :=
  RestrictedProduct (fun n => Equiv.Perm (J n))
    (fun n => (↑(⊥ : Subgroup (Equiv.Perm (J n))) : Set (Equiv.Perm (J n))))
    Filter.cofinite

private def support (g : FinitePerm I) : Finset ℕ :=
  (Filter.eventually_cofinite.mp (show ∀ᶠ n in Filter.cofinite, g n = 1 from by
    filter_upwards [g.property] with n hn
    exact Subgroup.mem_bot.mp hn)).toFinset

private theorem mem_support (g : FinitePerm I) (n : ℕ) :
    n ∈ support g ↔ g n ≠ 1 := by
  classical
  exact Set.Finite.mem_toFinset _

private def fold (s : Finset ℕ) (g : ∀ n, Equiv.Perm (I n)) : FullAut G :=
  s.noncommProd (fun n => action F G P n (g n))
    (fun _ _ _ _ h => action_commute F G P h _ _)

private theorem fold_insert (s : Finset ℕ) (a : ℕ) (ha : a ∉ s)
    (g : ∀ n, Equiv.Perm (I n)) :
    fold F G P (insert a s) g = action F G P a (g a) * fold F G P s g := by
  classical
  exact Finset.noncommProd_insert_of_notMem _ _ _ _ ha

private theorem fold_mul (s : Finset ℕ) (g h : ∀ n, Equiv.Perm (I n)) :
    fold F G P s (g*h) = fold F G P s g * fold F G P s h := by
  unfold fold
  simp only [Pi.mul_apply, map_mul]
  exact Finset.noncommProd_mul_distrib _ _ _ _
    (fun _ _ _ _ hnm => action_commute F G P hnm _ _)

private theorem fold_enlarge {s t : Finset ℕ} (hst : s ⊆ t)
    (g : ∀ n, Equiv.Perm (I n)) (hz : ∀ n ∈ t, n ∉ s → g n = 1) :
    fold F G P t g = fold F G P s g := by
  classical
  have he : t = s ∪ (t \ s) := (Finset.union_sdiff_of_subset hst).symm
  have ho : fold F G P (t \ s) g = 1 := by
    unfold fold
    rw [Finset.noncommProd_eq_pow_card _ _ _ 1, one_pow]
    intro n hn
    rw [hz n (Finset.mem_sdiff.mp hn).1 (Finset.mem_sdiff.mp hn).2, map_one]
  calc
    fold F G P t g = fold F G P (s ∪ (t \ s)) g := congrArg (fun r => fold F G P r g) he
    _ = fold F G P s g * fold F G P (t \ s) g :=
      Finset.noncommProd_union_of_disjoint Finset.disjoint_sdiff _ _
    _ = _ := by rw [ho, mul_one]

/-- The finite fold gives one simultaneous action of the countable finite-support product. -/
def finiteAction : FinitePerm I →* FullAut G where
  toFun g := fold F G P (support g) g
  map_one' := by
    have he : support (1 : FinitePerm I) = ∅ := by
      classical
      ext n
      simp only [mem_support, RestrictedProduct.one_apply, ne_eq, not_true_eq_false,
        Finset.notMem_empty]
    simp only [he, fold, Finset.noncommProd_empty]
  map_mul' g h := by
    classical
    let s := support g ∪ support h
    have hg : support g ⊆ s := Finset.subset_union_left
    have hh : support h ⊆ s := Finset.subset_union_right
    have hgh : support (g*h) ⊆ s := by
      intro n hn
      by_contra hns
      have hn₁ : g n = 1 := not_not.mp (mt (mem_support g n).mpr
        (fun hn => hns (Finset.mem_union_left _ hn)))
      have hn₂ : h n = 1 := not_not.mp (mt (mem_support h n).mpr
        (fun hn => hns (Finset.mem_union_right _ hn)))
      exact (mem_support (g*h) n).mp hn (by simp [hn₁, hn₂])
    have pad (a : FinitePerm I) (ha : support a ⊆ s) :
        fold F G P s a = fold F G P (support a) a :=
      fold_enlarge F G P ha a (fun n _ hn => not_not.mp (mt (mem_support a n).mpr hn))
    rw [← pad (g*h) hgh, ← pad g hg, ← pad h hh]
    exact fold_mul F G P s g h

private theorem fold_selected (s : Finset ℕ) (g : ∀ n, Equiv.Perm (I n))
    (x : History G) (n : ℕ) (a : ℤ) (i : I n) (hs : Selected F n x.val a i) :
    Selected F n ((fold F G P s g).val x).val a
      ((if n ∈ s then g n else 1) i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [fold, Finset.noncommProd_empty, Finset.notMem_empty,
      if_false, Equiv.Perm.one_apply]
    exact hs
  | @insert b s hb ih =>
    rw [fold_insert F G P s b hb]
    by_cases hbn : b = n
    · subst b
      simp only [hb, if_false, Equiv.Perm.one_apply] at ih
      simp only [Finset.mem_insert_self, if_true]
      exact forward F n (g n) ih
    · simp only [Finset.mem_insert, Ne.symm hbn, false_or]
      exact (selected_other F hbn (g b) _ _ _).mpr ih

/-- A subgroup containing every active coordinate contains the finite-support action. -/
theorem finiteAction_mem (H : Subgroup (FullAut G)) (g : FinitePerm I)
    (hg : ∀ n, action F G P n (g n) ∈ H) : finiteAction F G P g ∈ H := by
  exact Finset.noncommProd_induction (support g) _
    (fun _ _ _ _ h => action_commute F G P h _ _) (fun z => z ∈ H)
    (fun _ _ => H.mul_mem) H.one_mem (fun n _ => hg n)

/-- Every coordinate can be observed on its own gap, regardless of the exterior history. -/
theorem finiteAction_at_selected (g : FinitePerm I) (x : History G) (n : ℕ)
    (s : ℤ) (i : I n) (hs : Selected F n x.val s i) (j : Fin (d n)) :
    ((finiteAction F G P g).val x).val (s + 1 + (j.val : ℤ)) = F.data n (g n i) j := by
  classical
  have he : (if n ∈ support g then g n else 1) = g n := by
    split_ifs with h
    · rfl
    · exact (not_not.mp (mt (mem_support g n).mpr h)).symm
  have hsel := fold_selected F G P (support g) g x n s i hs
  rw [he] at hsel
  exact hsel.2.2 j

private def templateEdge (n : ℕ) (i : I n) (j : Fin (d n + 2)) : E :=
  if h : 0 < j.val ∧ j.val < d n + 1 then F.data n i ⟨j.val-1, by omega⟩
  else F.separator

private theorem template_data (n : ℕ) (i : I n) (j : Fin (d n)) :
    templateEdge F n i ⟨1+j.val, by omega⟩ = F.data n i j := by
  have hj := j.isLt
  simp only [templateEdge, dif_pos (by omega : 0 < 1+j.val ∧ 1+j.val < d n+1)]
  congr 1
  apply Fin.ext
  dsimp only
  omega

private def templateWord (n : ℕ) (i : I n) : LegalWord G (d n + 2) where
  edge := templateEdge F n i
  legal := by
    intro j hj
    have hd := F.positive n
    by_cases h₀ : j.val = 0
    · simp only [templateEdge, h₀, lt_self_iff_false, false_and, dif_neg,
        zero_add, zero_lt_one, true_and, Nat.sub_self,
        dif_pos (by omega : 1 < d n + 1)]
      exact (P.data_source n i).symm
    · by_cases h₁ : j.val + 1 < d n + 1
      · have hb : 0 < j.val ∧ j.val < d n + 1 := by omega
        have hc : 0 < j.val + 1 ∧ j.val + 1 < d n + 1 := by omega
        simp only [templateEdge, dif_pos hb, dif_pos hc]
        convert P.data_legal n i ⟨j.val-1, by omega⟩ (by dsimp; omega) using 1
        congr 2
        apply Fin.ext
        dsimp only
        omega
      · have hb : 0 < j.val ∧ j.val < d n + 1 := by omega
        have hc : ¬ (0 < j.val+1 ∧ j.val+1 < d n+1) := by omega
        simp only [templateEdge, dif_pos hb, dif_neg hc]
        have he : (⟨j.val-1, by omega⟩ : Fin (d n)) =
            ⟨d n-1, by omega⟩ := by apply Fin.ext; dsimp only; omega
        rw [he, P.data_target]

include P in
/-- A genuine legal realization supplies an observable witness for every label and length. -/
private theorem exists_selected [Fintype V] [Fintype E] [DecidableEq V] (hG : Essential G) (n : ℕ) (i : I n) :
    ∃ x : History G, Selected F n x.val 0 i := by
  obtain ⟨x, hx⟩ := exists_history_containing G hG (templateWord F G P n i) (by omega)
  refine ⟨x, ?_, ?_, ?_⟩
  · simpa [templateWord, templateEdge] using hx ⟨0, by omega⟩
  · have he := hx ⟨d n+1, by omega⟩
    simpa [templateWord, templateEdge] using he
  · intro j
    have he := hx ⟨1+j.val, by omega⟩
    simpa only [templateWord, template_data, Int.natCast_add, Int.natCast_one,
      zero_add] using he

/-- Joint faithfulness of the whole finite-support product on the original history space. -/
theorem finiteAction_injective [Fintype V] [Fintype E] [DecidableEq V] (hG : Essential G) :
    Function.Injective (finiteAction F G P) := by
  intro g h he
  apply RestrictedProduct.ext
  intro n
  apply Equiv.ext
  intro i
  obtain ⟨x, hx⟩ := exists_selected F G P hG n i
  apply F.data_injective n
  funext j
  have hobs := congrArg (fun f : FullAut G => (f.val x).val (0+1+(j.val : ℤ))) he
  rw [finiteAction_at_selected F G P g x n 0 i hx j,
    finiteAction_at_selected F G P h x n 0 i hx j] at hobs
  exact hobs

end D5.S3.ConceptDynamics.Coding.SeparatorGapAction
