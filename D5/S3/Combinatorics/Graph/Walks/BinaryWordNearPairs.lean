/- GID: D5/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/BinaryWordNearPairs
   mirror-E: none(waiver:no-computational-evidence)
   anchors: [mathlib/module/Mathlib.Data.Sym.Sym2]
   utility: none
   digest: Canonical ancestor and opposite-branch representations of actual binary-word pairs. -/

import D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.SetTheory.Cardinal.Finite

/-! Literal unordered pairs and their canonical longest-common-prefix decomposition. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.BinaryWordNearPairs

open BinaryWordGeometry
open scoped BigOperators

/-- The ancestor is the first endpoint, or the two endpoints occupy the
false and true child branches, respectively. Every suffix is a literal word. -/
inductive Code
  | ancestor (root : Word) (bit : Bool) (suffix : Word)
  | branch (root leftSuffix rightSuffix : Word)
  deriving DecidableEq

def Code.root : Code → Word
  | .ancestor w _ _ => w
  | .branch w _ _ => w

def Code.left : Code → Word
  | .ancestor w _ _ => w
  | .branch w s _ => w ++ false :: s

def Code.right : Code → Word
  | .ancestor w b s => w ++ b :: s
  | .branch w _ t => w ++ true :: t

def Code.cost : Code → ℕ
  | .ancestor _ _ s => s.length + 1
  | .branch _ s t => s.length + t.length + 2

/-- Actual unordered word pairs, with no quotient by length or distance. -/
def Code.pair (c : Code) : Sym2 Word := s(c.left, c.right)

/-- The literal distinct unordered physical pairs under the stated bounds. -/
def Near (L D : ℕ) (p : Sym2 Word) : Prop :=
  ∃ u v : Word, p = s(u, v) ∧ u ≠ v ∧ u.length ≤ L ∧ v.length ≤ L ∧
    distance u v ≤ 2 * D

/-- Endpoint heights and charged edit distance of a canonical representation. -/
def Code.Valid (L D : ℕ) (c : Code) : Prop :=
  c.left.length ≤ L ∧ c.right.length ≤ L ∧ c.cost ≤ 2 * D

private def Code.prepend (b : Bool) : Code → Code
  | .ancestor w a s => .ancestor (b :: w) a s
  | .branch w s t => .branch (b :: w) s t

private theorem pair_prepend (b : Bool) (c : Code) :
    (c.prepend b).pair = Sym2.map (List.cons b) c.pair := by
  cases c <;> rfl

private theorem code_geometry (c : Code) :
    lcp c.left c.right = c.root ∧ lcp c.right c.left = c.root ∧
    c.left ≠ c.right ∧ distance c.left c.right = c.cost ∧
    distance c.right c.left = c.cost := by
  have anc (w : Word) (b : Bool) (s : Word) :
      lcp w (w ++ b :: s) = w ∧ lcp (w ++ b :: s) w = w := by
    induction w with
    | nil => simp [lcp]
    | cons a w ih => simpa [lcp] using ih
  have br (w s t : Word) :
      lcp (w ++ false :: s) (w ++ true :: t) = w ∧
      lcp (w ++ true :: t) (w ++ false :: s) = w := by
    induction w with
    | nil => simp [lcp]
    | cons a w ih => simpa [lcp] using ih
  cases c with
  | ancestor w b s =>
    obtain ⟨h₁, h₂⟩ := anc w b s
    have hn : w ≠ w ++ b :: s := by
      intro h
      have := congrArg List.length h
      simp only [List.length_append, List.length_cons] at this
      omega
    simp only [Code.left, Code.right, Code.root, Code.cost]
    refine ⟨h₁, h₂, hn, ?_, ?_⟩ <;>
      simp [distance, h₁, h₂, List.length_append] <;> omega
  | branch w s t =>
    obtain ⟨h₁, h₂⟩ := br w s t
    have hn : w ++ false :: s ≠ w ++ true :: t := by simp
    simp only [Code.left, Code.right, Code.root, Code.cost]
    refine ⟨h₁, h₂, hn, ?_, ?_⟩ <;>
      simp [distance, h₁, h₂, List.length_append] <;> omega

private theorem pair_injective : Function.Injective Code.pair := by
  intro c d h
  have hr : c.root = d.root := by
    rcases Sym2.eq_iff.mp h with h | h
    · rw [← (code_geometry c).1, h.1, h.2, (code_geometry d).1]
    · rw [← (code_geometry c).1, h.1, h.2, (code_geometry d).2.1]
  cases c with
  | ancestor w b s =>
    cases d with
    | ancestor z a t =>
      change w = z at hr
      subst z
      rcases Sym2.eq_iff.mp h with h | h
      · have ht := List.append_cancel_left h.2
        simp only [List.cons.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        rfl
      · have hh := congrArg List.length h.1
        simp [Code.left, Code.right] at hh
    | branch z t r =>
      change w = z at hr
      subst z
      rcases Sym2.eq_iff.mp h with h | h <;>
        have hh := congrArg List.length h.1 <;>
        simp [Code.left, Code.right] at hh
  | branch w s t =>
    cases d with
    | ancestor z a r =>
      change w = z at hr
      subst z
      rcases Sym2.eq_iff.mp h with h | h
      · have hh := congrArg List.length h.1
        simp [Code.left] at hh
      · have hh := congrArg List.length h.2
        simp [Code.left, Code.right] at hh
    | branch z r q =>
      change w = z at hr
      subst z
      rcases Sym2.eq_iff.mp h with h | h
      · have hs := List.append_cancel_left h.1
        have ht := List.append_cancel_left h.2
        simp only [List.cons.injEq, true_and] at hs ht
        cases hs
        cases ht
        rfl
      · have hh := List.append_cancel_left h.1
        simp at hh

private theorem pair_exhausts (u v : Word) (hne : u ≠ v) :
    ∃ c : Code, c.pair = s(u, v) := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact (hne rfl).elim
    | cons b s => exact ⟨.ancestor [] b s, rfl⟩
  | cons a u ih =>
    cases v with
    | nil => exact ⟨.ancestor [] a u, Sym2.eq_swap⟩
    | cons b v =>
      by_cases hab : a = b
      · subst b
        obtain ⟨c, hc⟩ := ih v (fun h => hne (congrArg (List.cons a) h))
        refine ⟨c.prepend a, ?_⟩
        rw [pair_prepend, hc, Sym2.map_mk]
      · cases a <;> cases b
        · exact (hab rfl).elim
        · exact ⟨.branch [] u v, rfl⟩
        · exact ⟨.branch [] v u, Sym2.eq_swap⟩
        · exact (hab rfl).elim

private theorem valid_iff (L D : ℕ) (c : Code) :
    c.Valid L D ↔ Near L D c.pair := by
  obtain ⟨_, _, hn, hd, hdr⟩ := code_geometry c
  constructor
  · rintro ⟨hl, hr, hb⟩
    exact ⟨c.left, c.right, rfl, hn, hl, hr, hd ▸ hb⟩
  · rintro ⟨u, v, hp, _, hu, hv, hb⟩
    rcases Sym2.eq_iff.mp hp with h | h
    · exact ⟨by simpa [h.1] using hu, by simpa [h.2] using hv,
        by simpa [← h.1, ← h.2, hd] using hb⟩
    · exact ⟨by simpa [h.1] using hv, by simpa [h.2] using hu,
        by simpa [← h.1, ← h.2, hdr] using hb⟩

/-- Each distinct physical near pair has exactly one ancestor or oriented
opposite-branch representation. No representation or distance premise is assumed. -/
theorem canonical_representation (L D : ℕ) :
    Function.Injective Code.pair ∧
    ∀ p : Sym2 Word, Near L D p ↔ ∃! c : Code, c.Valid L D ∧ c.pair = p := by
  refine ⟨pair_injective, fun p => ?_⟩
  constructor
  · intro hp
    obtain ⟨u, v, rfl, hn, hu, hv, hb⟩ := hp
    obtain ⟨c, hc⟩ := pair_exhausts u v hn
    refine ⟨c, ⟨(valid_iff L D c).mpr ?_, hc⟩, ?_⟩
    · rw [hc]
      exact ⟨u, v, rfl, hn, hu, hv, hb⟩
    · intro d hd
      exact pair_injective (hd.2.trans hc.symm)
  · rintro ⟨c, ⟨hc, rfl⟩, _⟩
    exact (valid_iff L D c).mp hc

/-- Ordered branch depths, with the first depth belonging to the false branch. -/
abbrev BranchIndex (t D : ℕ) :=
  {ij : Fin t × Fin t // ij.1.val + ij.2.val + 2 ≤ 2 * D}

/-- The finite data at remaining height t. Indices are one less than positive
physical depths; the ancestor bit is included among the freely chosen letters. -/
abbrev LocalData (t D : ℕ) :=
  (Σ d : Fin (min (2 * D) t), Bool × List.Vector Bool d.val) ⊕
    (Σ ij : BranchIndex t D,
      List.Vector Bool ij.val.1.val × List.Vector Bool ij.val.2.val)

/-- Finite representations: remaining height, root word, and endpoint suffixes. -/
abbrev FiniteData (L D : ℕ) :=
  Σ t : Fin L, List.Vector Bool (L - (t.val + 1)) × LocalData (t.val + 1) D

private def toCode {L D : ℕ} (x : FiniteData L D) : Code :=
  match x.2.2 with
  | .inl ⟨_, b, s⟩ => .ancestor x.2.1.val b s.val
  | .inr ⟨_, s, t⟩ => .branch x.2.1.val s.val t.val

private theorem toCode_valid {L D : ℕ} (x : FiniteData L D) :
    (toCode x).Valid L D := by
  rcases x with ⟨t, w, z⟩
  have hw := w.property
  have ht := t.isLt
  cases z with
  | inl z =>
    rcases z with ⟨d, b, s⟩
    have hs := s.property
    have hd := d.isLt
    simp only [toCode, Code.Valid, Code.left, Code.right, Code.cost,
      List.length_append, List.length_cons]
    omega
  | inr z =>
    rcases z with ⟨⟨⟨i, j⟩, hij⟩, s, r⟩
    have hs := s.property
    have hr := r.property
    have hi := i.isLt
    have hj := j.isLt
    simp only [toCode, Code.Valid, Code.left, Code.right, Code.cost,
      List.length_append, List.length_cons]
    dsimp only at hs hr hij ⊢
    omega

private theorem toCode_root {L D : ℕ} (x : FiniteData L D) :
    (toCode x).root = x.2.1.val := by
  rcases x with ⟨t, w, z⟩
  cases z <;> rfl

private theorem toCode_injective (L D : ℕ) :
    Function.Injective (@toCode L D) := by
  rintro ⟨t, w, z⟩ ⟨u, v, q⟩ he
  have hr := congrArg Code.root he
  simp only [toCode_root] at hr
  have htu : t = u := by
    apply Fin.ext
    have hh := congrArg List.length hr
    have hw := w.property
    have hv := v.property
    have ht := t.isLt
    have hu := u.isLt
    omega
  cases htu
  have hwv : w = v := Subtype.ext hr
  cases hwv
  suffices z = q by cases this; rfl
  cases z with
  | inl z =>
    rcases z with ⟨d, b, s⟩
    cases q with
    | inr q => cases he
    | inl q =>
      rcases q with ⟨e, a, r⟩
      simp only [toCode, Code.ancestor.injEq, true_and] at he
      have hde : d = e := by
        apply Fin.ext
        have hh := congrArg List.length he.2
        simpa only [s.property, r.property] using hh
      cases hde
      have hsr : s = r := Subtype.ext he.2
      cases hsr
      cases he.1
      rfl
  | inr z =>
    rcases z with ⟨⟨⟨i, j⟩, hij⟩, s, r⟩
    cases q with
    | inl q => cases he
    | inr q =>
      rcases q with ⟨⟨⟨k, l⟩, hkl⟩, a, b⟩
      simp only [toCode, Code.branch.injEq, true_and] at he
      have hik : i = k := by
        apply Fin.ext
        have hh := congrArg List.length he.1
        simpa only [s.property, a.property] using hh
      have hjl : j = l := by
        apply Fin.ext
        have hh := congrArg List.length he.2
        simpa only [r.property, b.property] using hh
      cases hik
      cases hjl
      have hsa : s = a := Subtype.ext he.1
      have hrb : r = b := Subtype.ext he.2
      cases hsa
      cases hrb
      rfl

private theorem toCode_surjective (L D : ℕ) (c : Code) (hc : c.Valid L D) :
    ∃ x : FiniteData L D, toCode x = c := by
  cases c with
  | ancestor w b s =>
    simp only [Code.Valid, Code.left, Code.right, Code.cost,
      List.length_append, List.length_cons] at hc
    let t : Fin L := ⟨L - w.length - 1, by omega⟩
    have ht : L - (t.val + 1) = w.length := by dsimp [t]; omega
    let d : Fin (min (2 * D) (t.val + 1)) := ⟨s.length, by dsimp [t]; omega⟩
    exact ⟨⟨t, ⟨w, ht.symm⟩, .inl ⟨d, b, ⟨s, rfl⟩⟩⟩, rfl⟩
  | branch w s r =>
    simp only [Code.Valid, Code.left, Code.right, Code.cost,
      List.length_append, List.length_cons] at hc
    let t : Fin L := ⟨L - w.length - 1, by omega⟩
    have ht : L - (t.val + 1) = w.length := by dsimp [t]; omega
    let i : Fin (t.val + 1) := ⟨s.length, by dsimp [t]; omega⟩
    let j : Fin (t.val + 1) := ⟨r.length, by dsimp [t]; omega⟩
    exact ⟨⟨t, ⟨w, ht.symm⟩,
      .inr ⟨⟨(i, j), hc.2.2⟩, ⟨s, rfl⟩, ⟨r, rfl⟩⟩⟩, rfl⟩

/-- A finite representation bijection with the actual distinct unordered
physical near pairs, including all height and edit-budget cutoffs. -/
noncomputable def physicalPairEquiv (L D : ℕ) :
    FiniteData L D ≃ {p : Sym2 Word // Near L D p} :=
  Equiv.ofBijective
    (fun x => ⟨(toCode x).pair, (valid_iff L D _).mp (toCode_valid x)⟩)
    ⟨fun x y h => toCode_injective L D (pair_injective (congrArg Subtype.val h)), by
      rintro ⟨p, hp⟩
      obtain ⟨c, ⟨hc, he⟩, _⟩ := (canonical_representation L D).2 p |>.mp hp
      obtain ⟨x, rfl⟩ := toCode_surjective L D c hc
      exact ⟨x, Subtype.ext he⟩⟩

/-- Cardinality of the physical near-pair set, rather than a scalar recurrence. -/
noncomputable def pairCount (L D : ℕ) : ℕ := Nat.card {p : Sym2 Word // Near L D p}

private theorem local_card (t D : ℕ) :
    Fintype.card (LocalData t D) =
      (∑ d ∈ Finset.range (min (2 * D) t), 2 ^ (d + 1)) +
      ∑ i ∈ Finset.range t, ∑ j ∈ Finset.range t,
        if i + j + 2 ≤ 2 * D then 2 ^ (i + j) else 0 := by
  classical
  simp only [LocalData, Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod,
    card_vector, Fintype.card_bool]
  congr 1
  · calc
      _ = ∑ d : Fin (min (2 * D) t), 2 ^ (d.val + 1) := by
        apply Finset.sum_congr rfl
        intro d _
        simp [pow_succ, Nat.mul_comm]
      _ = _ := Fin.sum_univ_eq_sum_range (fun d : ℕ => (2 : ℕ) ^ (d + 1)) _
  · simp only [← pow_add]
    rw [← Finset.sum_subtype (Finset.univ.filter
      (fun ij : Fin t × Fin t => ij.1.val + ij.2.val + 2 ≤ 2 * D))
      (by simp) (fun ij : Fin t × Fin t => (2 : ℕ) ^ (ij.1.val + ij.2.val))]
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    calc
      _ = ∑ i : Fin t, ∑ j ∈ Finset.range t,
          if i.val + j + 2 ≤ 2 * D then 2 ^ (i.val + j) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only using Fin.sum_univ_eq_sum_range
          (fun j : ℕ => if i.val + j + 2 ≤ 2 * D then (2 : ℕ) ^ (i.val + j) else 0) t
      _ = _ := Fin.sum_univ_eq_sum_range
        (fun i : ℕ => ∑ j ∈ Finset.range t,
          if i + j + 2 ≤ 2 * D then (2 : ℕ) ^ (i + j) else 0) t

private theorem shifted_sum (n : ℕ) (f : ℕ → ℕ) :
    (∑ d ∈ Finset.range n, f (d + 1)) = ∑ d ∈ Finset.Icc 1 n, f d := by
  calc
    _ = ∑ d ∈ Finset.Ico 0 n, f (d + 1) := by rw [Nat.Ico_zero_eq_range]
    _ = ∑ d ∈ Finset.Ico 1 (n + 1), f d := by
      simpa using Finset.sum_Ico_add' f 0 n 1
    _ = _ := by rw [Finset.Ico_add_one_right_eq_Icc]

/-- The exact source sum, with natural exponents and positive-depth ranges. -/
def sourceSum (L D : ℕ) : ℕ :=
  ∑ t ∈ Finset.Icc 1 L, 2 ^ (L - t) *
    ((∑ d ∈ Finset.Icc 1 (min (2 * D) t), 2 ^ d) +
      ∑ i ∈ Finset.Icc 1 t,
        ∑ j ∈ (Finset.Icc 1 t).filter (fun j => i + j ≤ 2 * D), 2 ^ (i + j - 2))

/-- Exact IV.113: the count is of distinct unordered actual binary words.
The finite-data equivalence supplies the representation and counting bridge. -/
theorem exact_count (L D : ℕ) : pairCount L D = sourceSum L D := by
  classical
  rw [pairCount, ← Nat.card_congr (physicalPairEquiv L D), Nat.card_eq_fintype_card]
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_prod, card_vector, Fintype.card_bool, local_card]
  rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => (2 : ℕ) ^ (L - (t + 1)) *
    ((∑ d ∈ Finset.range (min (2 * D) (t + 1)), 2 ^ (d + 1)) +
      ∑ i ∈ Finset.range (t + 1), ∑ j ∈ Finset.range (t + 1),
        if i + j + 2 ≤ 2 * D then 2 ^ (i + j) else 0)) L]
  rw [show sourceSum L D = ∑ t ∈ Finset.range L, 2 ^ (L - (t + 1)) *
    ((∑ d ∈ Finset.Icc 1 (min (2 * D) (t + 1)), 2 ^ d) +
      ∑ i ∈ Finset.Icc 1 (t + 1),
        ∑ j ∈ (Finset.Icc 1 (t + 1)).filter (fun j => i + j ≤ 2 * D),
          2 ^ (i + j - 2)) from (shifted_sum L _).symm]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  congr 1
  · exact shifted_sum _ _
  · simp_rw [Finset.sum_filter]
    rw [← shifted_sum (t + 1)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← shifted_sum (t + 1)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [show i + 1 + (j + 1) = i + j + 2 by omega, Nat.add_sub_cancel]

#print axioms canonical_representation
#print axioms physicalPairEquiv
#print axioms exact_count

end D5.S3.Combinatorics.Graph.Walks.BinaryWordNearPairs
