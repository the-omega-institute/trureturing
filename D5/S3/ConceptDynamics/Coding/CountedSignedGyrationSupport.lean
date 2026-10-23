/- GID: D5/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed support normalization and dense occurrence-rank reindexing. -/

/-
This file removes the zero binomial terms and reindexes the remaining
DEPENDENT WordType sum by supported vertex cycles and dense rank vectors.
No primitivity test is made on the underlying vertex cycle.
-/
import D5.S3.ConceptDynamics.Coding.CountedPositiveTriangleLocalizedConsumer
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration

open scoped BigOperators
open CountedMatrixOverlap

namespace SignedSupport

variable {n m d : ℕ} [NeZero d]

def entries (R : Matrix (Fin n) (Fin m) ℤ)
    (S : Matrix (Fin m) (Fin n) ℤ) : Entry n m → ℤ :=
  Sum.elim (fun ij => R ij.1 ij.2) (fun ji => S ji.1 ji.2)

def term (z : Entry n m → ℤ) (w : VertexWord n m d)
    (T : WordType w) : ℤ :=
  wordWeight (sourceEdge w (widths T) (rankLabels T))
    (targetEdge w (widths T) (rankLabels T)) *
      ∏ e : Entry n m, Ring.choose (z e) (widths T e)

def Supported (z : Entry n m → ℤ) (w : VertexWord n m d) : Prop :=
  ∀ e : Entry n m, Nonempty (Occurrence w e) → z e ≠ 0

def Normal (z : Entry n m → ℤ) {w : VertexWord n m d}
    (T : WordType w) : Prop :=
  ∀ e : Entry n m, z e = 1 → widths T e ≤ 1

private theorem width_pos {w : VertexWord n m d} (T : WordType w)
    (e : Entry n m) (a : Occurrence w e) : 0 < widths T e :=
  Nat.zero_lt_of_lt ((T e).2.val a).isLt

private theorem width_zero_of_absent {w : VertexWord n m d}
    (T : WordType w) (e : Entry n m) (ha : ¬ Nonempty (Occurrence w e)) :
    widths T e = 0 := by
  by_contra h
  obtain ⟨a, _⟩ := (T e).2.property ⟨0, Nat.pos_of_ne_zero h⟩
  exact ha ⟨a⟩

private theorem choose_one_of_le_one (k : ℕ) (hk : k ≤ 1) :
    Ring.choose (1 : ℤ) k = 1 := by
  interval_cases k <;> norm_num [Ring.choose_natCast]

private theorem choose_one_of_one_lt (k : ℕ) (hk : 1 < k) :
    Ring.choose (1 : ℤ) k = 0 := by
  change Ring.choose ((1 : ℕ) : ℤ) k = 0
  rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero]

private theorem choose_neg_one (k : ℕ) :
    Ring.choose (-1 : ℤ) k = (-1 : ℤ)^k := by
  change Ring.multichoose ((-1 : ℤ) - (k : ℤ) + 1) k = (-1 : ℤ)^k
  rw [show (-1 : ℤ) - (k : ℤ) + 1 = -(k : ℤ) by ring,
    Ring.multichoose_neg_self]

/-- A zero matrix entry used by a cycle forces a zero factor, even when
other entries are negative. This is not a nonnegative-realization argument. -/
theorem term_zero_of_unsupported (z : Entry n m → ℤ)
    (w : VertexWord n m d) (T : WordType w) (hw : ¬ Supported z w) :
    term z w T = 0 := by
  classical
  obtain ⟨e, he⟩ := not_forall.mp hw
  obtain ⟨ha, hz⟩ := Classical.not_imp.mp he
  have hzero : z e = 0 := not_ne_iff.mp hz
  obtain ⟨a⟩ := ha
  have hprod : (∏ e : Entry n m, Ring.choose (z e) (widths T e)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    rw [hzero]
    exact Ring.choose_zero_pos ℤ (width_pos T e a)
  simp only [term, hprod, mul_zero]

/-- Used positive binary entries have only the width-one term. -/
theorem term_zero_of_not_normal (z : Entry n m → ℤ)
    (w : VertexWord n m d) (T : WordType w) (hT : ¬ Normal z T) :
    term z w T = 0 := by
  classical
  obtain ⟨e, he⟩ := not_forall.mp hT
  obtain ⟨hz, hk⟩ := Classical.not_imp.mp he
  have hprod : (∏ e : Entry n m, Ring.choose (z e) (widths T e)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    rw [hz]
    exact choose_one_of_one_lt _ (Nat.lt_of_not_ge hk)
  simp only [term, hprod, mul_zero]

/-- An absent fibre has its original unique width-zero pattern and factor
one. Negative entries keep ALL widths and their exact negative binomials. -/
theorem binomial_product (z : Entry n m → ℤ)
    (hz : ∀ e, z e = -1 ∨ z e = 0 ∨ z e = 1)
    (w : VertexWord n m d) (hw : Supported z w)
    (T : WordType w) (hT : Normal z T) :
    (∏ e : Entry n m, Ring.choose (z e) (widths T e)) =
      ∏ e : Entry n m, if z e = -1 then (-1 : ℤ)^(widths T e) else 1 := by
  classical
  apply Finset.prod_congr rfl
  intro e _
  rcases hz e with he | he | he
  · simp [he, choose_neg_one]
  · have ha : ¬ Nonempty (Occurrence w e) := by
      intro ha
      exact hw e ha he
    rw [width_zero_of_absent T e ha]
    simp
  · simp only [he, choose_one_of_le_one _ (hT e he),
      show (1 : ℤ) ≠ -1 by decide, if_false]

/-! A pattern is recovered from its NATURAL rank labels. The image-card
criterion is an executable formulation of being an initial interval; it
also treats the empty occurrence set without a separate supplied value. -/

def natImage {O : Type*} [Fintype O] (f : O → ℕ) : Finset ℕ := by
  classical
  exact Finset.univ.image f

private theorem pattern_image {O : Type*} [Fintype O] (P : Pattern O) :
    natImage (fun a => (P.2.val a).val) = Finset.range P.1.val := by
  classical
  ext k
  simp only [natImage, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact (P.2.val a).isLt
  · intro hk
    obtain ⟨a, ha⟩ := P.2.property ⟨k, hk⟩
    exact ⟨a, congrArg Fin.val ha⟩

theorem pattern_image_card {O : Type*} [Fintype O] (P : Pattern O) :
    (natImage (fun a => (P.2.val a).val)).card = P.1.val := by
  rw [pattern_image, Finset.card_range]

theorem pattern_ext_nat {O : Type*} [Fintype O] (P Q : Pattern O)
    (h : ∀ a, (P.2.val a).val = (Q.2.val a).val) : P = Q := by
  have hi : natImage (fun a => (P.2.val a).val) =
      natImage (fun a => (Q.2.val a).val) := congrArg natImage (funext h)
  have hk : P.1 = Q.1 := Fin.ext (by
    simpa only [pattern_image_card] using congrArg Finset.card hi)
  rcases P with ⟨k, f, hf⟩
  rcases Q with ⟨l, g, hg⟩
  dsimp only at hk h
  subst l
  have hfg : f = g := funext (fun a => Fin.ext (h a))
  subst g
  rfl

/-- No arbitrary labels are compressed here: input labels already form
the initial interval [0,card(image)). The condition is proved at the call. -/
def patternOfNat {O : Type*} [Fintype O] (f : O → ℕ)
    (hf : ∀ a, f a < (natImage f).card) : Pattern O := by
  classical
  let k := (natImage f).card
  have hk : k < Fintype.card O + 1 := by
    change (natImage f).card < Fintype.card O + 1
    exact Nat.lt_succ_of_le (by
      simpa only [natImage, Finset.card_univ] using
        Finset.card_image_le (s := Finset.univ) (f := f))
  let r : O → Fin k := fun a => ⟨f a, hf a⟩
  have himage : (Finset.univ.image r).image Fin.val = natImage f := by
    ext v
    simp [natImage, r]
  have hcard : (Finset.univ.image r).card = Fintype.card (Fin k) := by
    rw [Fintype.card_fin]
    change _ = (natImage f).card
    rw [← himage, Finset.card_image_of_injective _ Fin.val_injective]
  have hr : Function.Surjective r := by
    have hu : Finset.univ.image r = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        (by simpa only [Finset.card_univ] using hcard.ge)
    intro b
    have hb : b ∈ Finset.univ.image r := by rw [hu]; exact Finset.mem_univ _
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hb
    exact ⟨a, ha⟩
  exact ⟨⟨k, hk⟩, r, hr⟩

private theorem constant_bound {O : Type*} [Fintype O] (a : O) :
    (0 : ℕ) < (natImage (fun _ : O => 0)).card := by
  classical
  exact Finset.card_pos.mpr ⟨0, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩

def sSlots (w : VertexWord n m d) (e : Fin m × Fin n) : Finset (Fin d) :=
  Finset.univ.filter (fun t => (w.2 t, w.1 (t+1)) = e)

def rankWidth (w : VertexWord n m d) (l : Fin d → ℕ)
    (e : Fin m × Fin n) : ℕ := ((sSlots w e).image l).card

private theorem s_image (w : VertexWord n m d) (l : Fin d → ℕ)
    (e : Fin m × Fin n) :
    natImage (fun a : Occurrence w (Sum.inr e) => l a.val) =
      (sSlots w e).image l := by
  classical
  ext k
  simp only [natImage, sSlots, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.val, a.property, ha⟩
  · rintro ⟨t, ht, hk⟩
    exact ⟨⟨t, ht⟩, hk⟩

private theorem s_card (w : VertexWord n m d) (e : Fin m × Fin n) :
    Fintype.card (Occurrence w (Sum.inr e)) = (sSlots w e).card := by
  classical
  change Fintype.card {t : Fin d // (w.2 t, w.1 (t+1)) = e} = _
  simp [sSlots, Fintype.card_subtype]

/-- Bounds are per OCCURRENCE FIBRE, not d independent arbitrary labels.
A positive S entry has exactly the single label zero. -/
def rankVectors (S : Matrix (Fin m) (Fin n) ℤ) (w : VertexWord n m d) :
    Finset (Fin d → ℕ) :=
  (Fintype.piFinset fun t : Fin d =>
    Finset.range (if S (w.2 t) (w.1 (t+1)) = -1 then
      (sSlots w (w.2 t, w.1 (t+1))).card else 1)).filter
    (fun l => ∀ t : Fin d, l t < rankWidth w l (w.2 t, w.1 (t+1)))

def sRanks {w : VertexWord n m d} (T : WordType w) : Fin d → ℕ :=
  fun t => ((T (Sum.inr (w.2 t, w.1 (t+1)))).2.val ⟨t, rfl⟩).val

private theorem sRanks_at {w : VertexWord n m d} (T : WordType w)
    (e : Fin m × Fin n) (a : Occurrence w (Sum.inr e)) :
    sRanks T a.val = ((T (Sum.inr e)).2.val a).val := by
  rcases a with ⟨t, ht⟩
  cases ht
  rfl

private theorem width_sRanks {w : VertexWord n m d} (T : WordType w)
    (e : Fin m × Fin n) : rankWidth w (sRanks T) e = widths T (Sum.inr e) := by
  rw [rankWidth, ← s_image]
  have h : (fun a : Occurrence w (Sum.inr e) => sRanks T a.val) =
      (fun a => ((T (Sum.inr e)).2.val a).val) := funext (sRanks_at T e)
  rw [h, pattern_image_card]
  rfl

private theorem ranks_zero {w : VertexWord n m d} (T : WordType w)
    (e : Entry n m) (he : widths T e ≤ 1) (a : Occurrence w e) :
    ((T e).2.val a).val = 0 := by
  have h := ((T e).2.val a).isLt
  change _ < widths T e at h
  omega

theorem sRanks_mem (R : Matrix (Fin n) (Fin m) ℤ)
    (S : Matrix (Fin m) (Fin n) ℤ)
    (hS : ∀ j i, S j i = -1 ∨ S j i = 0 ∨ S j i = 1)
    (w : VertexWord n m d) (hw : Supported (entries R S) w)
    (T : WordType w) (hT : Normal (entries R S) T) :
    sRanks T ∈ rankVectors S w := by
  classical
  rw [rankVectors, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · intro t
    rw [Finset.mem_range]
    by_cases hn : S (w.2 t) (w.1 (t+1)) = -1
    · rw [if_pos hn, ← s_card]
      exact lt_of_lt_of_le
        (((T (Sum.inr (w.2 t, w.1 (t+1)))).2.val ⟨t, rfl⟩).isLt)
        (Nat.le_of_lt_succ (T (Sum.inr (w.2 t, w.1 (t+1)))).1.isLt)
    · have hs : S (w.2 t) (w.1 (t+1)) = 1 := by
        rcases hS (w.2 t) (w.1 (t+1)) with h | h | h
        · exact False.elim (hn h)
        · exact False.elim (hw (Sum.inr (w.2 t, w.1 (t+1))) ⟨⟨t, rfl⟩⟩ h)
        · exact h
      rw [if_neg hn]
      change ((T (Sum.inr (w.2 t, w.1 (t+1)))).2.val ⟨t, rfl⟩).val < 1
      rw [ranks_zero T (Sum.inr (w.2 t, w.1 (t+1)))
        (hT (Sum.inr (w.2 t, w.1 (t+1))) hs) ⟨t, rfl⟩]
      decide
  · intro t
    rw [width_sRanks]
    exact ((T (Sum.inr (w.2 t, w.1 (t+1)))).2.val ⟨t, rfl⟩).isLt

def typeOfRanks (S : Matrix (Fin m) (Fin n) ℤ) (w : VertexWord n m d)
    (l : Fin d → ℕ) (hl : l ∈ rankVectors S w) : WordType w := by
  classical
  intro e
  cases e with
  | inl ij => exact patternOfNat (fun _ : Occurrence w (Sum.inl ij) => 0) constant_bound
  | inr ji =>
    apply patternOfNat (fun a : Occurrence w (Sum.inr ji) => l a.val)
    intro a
    rw [s_image]
    have h := (Finset.mem_filter.mp hl).2 a.val
    change l a.val < rankWidth w l ji
    simpa only [a.property] using h

@[simp] theorem sRanks_typeOfRanks (S : Matrix (Fin m) (Fin n) ℤ)
    (w : VertexWord n m d) (l : Fin d → ℕ) (hl : l ∈ rankVectors S w) :
    sRanks (typeOfRanks S w l hl) = l := rfl

private theorem typeOfRanks_normal (R : Matrix (Fin n) (Fin m) ℤ)
    (S : Matrix (Fin m) (Fin n) ℤ) (w : VertexWord n m d)
    (l : Fin d → ℕ) (hl : l ∈ rankVectors S w) :
    Normal (entries R S) (typeOfRanks S w l hl) := by
  classical
  intro e he
  have himage : (natImage (fun _ : Occurrence w e => 0)).card ≤ 1 := by
    exact Finset.card_le_one.mpr (by
      intro a ha b hb
      simp only [natImage, Finset.mem_image, Finset.mem_univ, true_and] at ha hb
      obtain ⟨_, rfl⟩ := ha
      obtain ⟨_, rfl⟩ := hb
      rfl)
  cases e with
  | inl ij => exact himage
  | inr ji =>
    change (natImage (fun a : Occurrence w (Sum.inr ji) => l a.val)).card ≤ 1
    have hz (a : Occurrence w (Sum.inr ji)) : l a.val = 0 := by
      have ht := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hl).1 a.val
      have hs : S (w.2 a.val) (w.1 (a.val+1)) = 1 := by
        change S ji.1 ji.2 = 1 at he
        simpa only [← a.property] using he
      simp only [hs, show (1 : ℤ) ≠ -1 by decide, if_false, Finset.mem_range] at ht
      omega
    simpa only [funext hz] using himage

theorem typeOfRanks_sRanks (R : Matrix (Fin n) (Fin m) ℤ)
    (S : Matrix (Fin m) (Fin n) ℤ)
    (hR : ∀ i j, R i j = 0 ∨ R i j = 1)
    (hS : ∀ j i, S j i = -1 ∨ S j i = 0 ∨ S j i = 1)
    (w : VertexWord n m d) (hw : Supported (entries R S) w)
    (T : WordType w) (hT : Normal (entries R S) T) :
    typeOfRanks S w (sRanks T) (sRanks_mem R S hS w hw T hT) = T := by
  funext e
  apply pattern_ext_nat
  intro a
  cases e with
  | inl ij =>
    have hr : R ij.1 ij.2 = 1 := by
      rcases hR ij.1 ij.2 with h | h
      · exact False.elim (hw _ ⟨a⟩ h)
      · exact h
    exact (ranks_zero T (Sum.inl ij) (hT (Sum.inl ij) hr) a).symm
  | inr ji => exact sRanks_at T ji a

def coefficient (S : Matrix (Fin m) (Fin n) ℤ)
    (w : VertexWord n m d) (l : Fin d → ℕ) : ℤ :=
  ∏ e : Fin m × Fin n, if S e.1 e.2 = -1 then
    (-1 : ℤ)^(rankWidth w l e) else 1

def rankedTerm (S : Matrix (Fin m) (Fin n) ℤ)
    (w : VertexWord n m d) (l : Fin d → ℕ) : ℤ := by
  classical
  exact if hl : l ∈ rankVectors S w then
    wordWeight
      (sourceEdge w (widths (typeOfRanks S w l hl))
        (rankLabels (typeOfRanks S w l hl)))
      (targetEdge w (widths (typeOfRanks S w l hl))
        (rankLabels (typeOfRanks S w l hl))) * coefficient S w l
  else 0

/-- The efficient support index keeps only possible middle vertices.
It enumerates n^d outside-vertex sequences, not (nm)^d vertex words. -/
def middleWords (R : Matrix (Fin n) (Fin m) ℤ)
    (S : Matrix (Fin m) (Fin n) ℤ) (a : Fin d → Fin n) :
    Finset (Fin d → Fin m) :=
  Fintype.piFinset fun t : Fin d => Finset.univ.filter fun j : Fin m =>
    R (a t) j ≠ 0 ∧ S j (a (t+1)) ≠ 0

theorem middleWords_iff (R : Matrix (Fin n) (Fin m) ℤ)
    (S : Matrix (Fin m) (Fin n) ℤ) (a : Fin d → Fin n) (b : Fin d → Fin m) :
    b ∈ middleWords R S a ↔ Supported (entries R S) (a,b) := by
  classical
  simp only [middleWords, Fintype.mem_piFinset, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h e ha
    cases e with
    | inl ij =>
      obtain ⟨⟨t, ht⟩⟩ := ha
      simpa [entries, ← ht] using (h t).1
    | inr ji =>
      obtain ⟨⟨t, ht⟩⟩ := ha
      simpa [entries, ← ht] using (h t).2
  · intro h t
    exact ⟨h (Sum.inl (a t, b t)) ⟨⟨t,rfl⟩⟩,
      h (Sum.inr (b t, a (t+1))) ⟨⟨t,rfl⟩⟩⟩

/-- This is already an exact reindexing of the ORIGINAL polynomial sum.
The only remaining non-executable operation in this intermediate expression
is the original ranked-edge wordWeight; its order transport is separate. -/
theorem signedGyrationLift_supported_surjections
    (R : Matrix (Fin n) (Fin m) ℤ) (S : Matrix (Fin m) (Fin n) ℤ)
    (hR : ∀ i j, R i j = 0 ∨ R i j = 1)
    (hS : ∀ j i, S j i = -1 ∨ S j i = 0 ∨ S j i = 1) :
    signedGyrationLift (d := d) (entries R S) =
      ∑ a : Fin d → Fin n, ∑ b ∈ middleWords R S a,
        ∑ l ∈ rankVectors S (a,b), rankedTerm S (a,b) l := by
  classical
  have hz : ∀ e, entries R S e = -1 ∨ entries R S e = 0 ∨ entries R S e = 1 := by
    intro e
    cases e with
    | inl ij =>
      rcases hR ij.1 ij.2 with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    | inr ji => exact hS ji.1 ji.2
  unfold signedGyrationLift
  change (∑ w : VertexWord n m d, ∑ T : WordType w, term (entries R S) w T) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_subset (Finset.subset_univ (middleWords R S a))]
  · apply Finset.sum_congr rfl
    intro b hb
    have hw := (middleWords_iff R S a b).mp hb
    let good : Finset (WordType (a,b)) := Finset.univ.filter (Normal (entries R S))
    have hrestrict : (∑ T : WordType (a,b), term (entries R S) (a,b) T) =
        ∑ T ∈ good, term (entries R S) (a,b) T := by
      symm
      apply Finset.sum_subset (Finset.subset_univ good)
      intro T _ hT
      exact term_zero_of_not_normal _ _ T (by simpa [good] using hT)
    rw [hrestrict]
    refine Finset.sum_bij (fun T hT => sRanks T) ?_ ?_ ?_ ?_
    · intro T hT
      exact sRanks_mem R S hS (a,b) hw T ((Finset.mem_filter.mp hT).2)
    · intro T hT U hU he
      have hT' := typeOfRanks_sRanks R S hR hS (a,b) hw T (Finset.mem_filter.mp hT).2
      have hU' := typeOfRanks_sRanks R S hR hS (a,b) hw U (Finset.mem_filter.mp hU).2
      calc
        T = typeOfRanks S (a,b) (sRanks T) _ := hT'.symm
        _ = typeOfRanks S (a,b) (sRanks U) _ := by congr 1
        _ = U := hU'
    · intro l hl
      exact ⟨typeOfRanks S (a,b) l hl,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, typeOfRanks_normal R S (a,b) l hl⟩,
        sRanks_typeOfRanks S (a,b) l hl⟩
    · intro T hT
      have hN := (Finset.mem_filter.mp hT).2
      have ht := typeOfRanks_sRanks R S hR hS (a,b) hw T hN
      have hm := sRanks_mem R S hS (a,b) hw T hN
      rw [rankedTerm, dif_pos hm]
      rw [ht]
      unfold term
      congr 1
      rw [binomial_product (entries R S) hz (a,b) hw T hN,
        Fintype.prod_sum_type]
      have hleft : (∏ e : Fin n × Fin m,
          if entries R S (Sum.inl e) = -1 then (-1 : ℤ)^(widths T (Sum.inl e))
          else 1) = 1 := by
        apply Finset.prod_eq_one
        intro e _
        rcases hR e.1 e.2 with h | h <;> simp [entries, h]
      rw [hleft, one_mul]
      apply Finset.prod_congr rfl
      intro e _
      simp only [entries, Sum.elim_inr, width_sRanks]
      rfl
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro T _
    exact term_zero_of_unsupported _ _ T (by
      simpa only [← middleWords_iff R S a b] using hb)

end SignedSupport

end D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
