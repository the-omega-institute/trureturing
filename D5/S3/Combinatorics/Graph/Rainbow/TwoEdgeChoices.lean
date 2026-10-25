/- GID: D5/S3/Combinatorics/Graph/Rainbow/TwoEdgeChoices
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Rainbow/TwoEdgeChoices
   mirror-E: none(waiver:general-deterministic-theorems)
   anchors: [mathlib/module/Mathlib.Combinatorics.Digraph.Basic]
   utility: none
   digest: Repeated-colour endpoint sparsity and three disjoint tagged-coordinate classes. -/

import D5.S3.Combinatorics.Graph.Brooks.Coloring
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
Repeated-colour endpoint mass and disjoint tagged-coordinate classes for actual
two-edge choices in a properly coloured directed graph. The quantitative consumer
retains an arbitrary deterministic base family and the original vertex count.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.Rainbow.TwoEdgeChoices

variable {V C : Type*} [Fintype V]

/-- Source properness: injectivity on each outgoing star separately. -/
def OutProper (G : Digraph V) (c : V → V → C) : Prop :=
  ∀ u, Set.InjOn (c u) {x | G.Adj u x}

/-- Source properness: injectivity on each incoming star separately. -/
def InProper (G : Digraph V) (c : V → V → C) : Prop :=
  ∀ w, Set.InjOn (fun x => c x w) {x | G.Adj x w}

noncomputable def outNeighbors (G : Digraph V) (u : V) : Finset V := by
  classical
  exact univ.filter (G.Adj u)

/-- Actual intermediate vertices of two directed edges. No rainbow claim is built in. -/
noncomputable def twoStep (G : Digraph V) (u w : V) : Finset V := by
  classical
  exact (outNeighbors G u).filter (fun x => G.Adj x w)

/-- Repeated-colour choices, including all endpoints when counting total mass. -/
noncomputable def repeated (G : Digraph V) (c : V → V → C) (u w : V) : Finset V := by
  classical
  exact (outNeighbors G u).filter (fun x => G.Adj x w ∧ c u x = c x w)

/-- Only choices with two genuinely different literal colours survive. -/
noncomputable def rainbow (c : V → V → C) (u w : V) (A : Finset V) : Finset V := by
  classical
  exact A.filter (fun x => c u x ≠ c x w)

/-- The outgoing properness at the middle vertex bounds the entire repeated-colour mass.
The bound retains the actual outdegree, which can be much smaller than the vertex count. -/
theorem repeated_colour_mass_le_outdegree (G : Digraph V) (c : V → V → C)
    (hout : OutProper G c) (u : V) :
    (∑ w : V, (repeated G c u w).card) ≤ (outNeighbors G u).card := by
  classical
  let r : V → V → Prop := fun x w => G.Adj x w ∧ c u x = c x w
  have hf (x : V) : (univ.filter (r x)).card ≤ 1 := by
    apply card_le_one.mpr
    intro w hw z hz
    have hw' := (mem_filter.mp hw).2
    have hz' := (mem_filter.mp hz).2
    exact hout x hw'.1 hz'.1 (hw'.2.symm.trans hz'.2)
  calc
    (∑ w : V, (repeated G c u w).card) =
        ∑ x ∈ outNeighbors G u, (univ.filter (r x)).card := by
      exact (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        r (s := outNeighbors G u) (t := univ)).symm
    _ ≤ ∑ _x ∈ outNeighbors G u, 1 := sum_le_sum (fun x _ => hf x)
    _ = (outNeighbors G u).card := by simp

/-- Vertex and colour coordinates have different tags, even if the underlying types coincide. -/
noncomputable def taggedSupport (a b : V → C) (x : V) : Finset (V ⊕ C) := by
  classical
  exact {Sum.inl x, Sum.inr (a x), Sum.inr (b x)}

noncomputable def colourPair (a b : V → C) (x : V) : Finset C := by
  classical
  exact {a x, b x}

/-- The actual conflict relation is intersection of the two literal colour sets. -/
noncomputable def choiceConflict (A : Finset V) (a b : V → C) : SimpleGraph A where
  Adj x y := x ≠ y ∧ ¬ Disjoint (colourPair a b x) (colourPair a b y)
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, fun hd => h.2 hd.symm⟩
  loopless := by
    constructor
    intro x h
    exact h.1 rfl

omit [Fintype V] in
private theorem conflict_degree_le_two (A : Finset V) (a b : V → C)
    [DecidableRel (choiceConflict A a b).Adj]
    (ha : Set.InjOn a A) (hb : Set.InjOn b A) (x : A) :
    (choiceConflict A a b).degree x ≤ 2 := by
  classical
  let L : Finset A := univ.filter (fun y => a x = b y)
  let R : Finset A := univ.filter (fun y => b x = a y)
  have hL : L.card ≤ 1 := by
    apply card_le_one.mpr
    intro y hy z hz
    apply Subtype.ext
    exact hb y.property z.property
      (((mem_filter.mp hy).2).symm.trans (mem_filter.mp hz).2)
  have hR : R.card ≤ 1 := by
    apply card_le_one.mpr
    intro y hy z hz
    apply Subtype.ext
    exact ha y.property z.property
      (((mem_filter.mp hy).2).symm.trans (mem_filter.mp hz).2)
  have hsub : (choiceConflict A a b).neighborFinset x ⊆ L ∪ R := by
    intro y hy
    have hxy := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
    have hne : (x : V) ≠ y := fun he => hxy.1 (Subtype.ext he)
    have haa : a x ≠ a y := fun he => hne (ha x.property y.property he)
    have hbb : b x ≠ b y := fun he => hne (hb x.property y.property he)
    have hh : a x = b y ∨ b x = a y := by
      by_contra h
      have h1 : a x ≠ b y := fun he => h (Or.inl he)
      have h2 : b x ≠ a y := fun he => h (Or.inr he)
      apply hxy.2
      apply disjoint_left.mpr
      intro q hqx hqy
      simp only [colourPair, mem_insert, mem_singleton] at hqx hqy
      rcases hqx with hqx | hqx <;> rcases hqy with hqy | hqy
      · exact haa (hqx.symm.trans hqy)
      · exact h1 (hqx.symm.trans hqy)
      · exact h2 (hqx.symm.trans hqy)
      · exact hbb (hqx.symm.trans hqy)
    rcases hh with h | h
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨mem_univ _, h⟩))
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ _, h⟩))
  have hcard := (card_le_card hsub).trans (card_union_le L R)
  change ((choiceConflict A a b).neighborFinset x).card ≤ 2
  omega

/-- An actual partition into three classes with pairwise disjoint tagged supports. -/
def ThreeClasses (A : Finset V) (a b : V → C) (T : Fin 3 → Finset V) : Prop :=
  (∀ i, T i ⊆ A) ∧
  (∀ x, x ∈ A ↔ ∃ i, x ∈ T i) ∧
  (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧
  (∀ i, (T i : Set V).Pairwise (fun x y =>
    Disjoint (taggedSupport a b x) (taggedSupport a b y))) ∧
  (∑ i : Fin 3, (T i).card) = A.card

omit [Fintype V] in
/-- Separate injectivity gives degree at most two in the actual colour-conflict graph.
The existing greedy colouring supplier then constructs three disjoint-coordinate classes. -/
theorem exists_three_disjoint_classes (A : Finset V) (a b : V → C)
    (ha : Set.InjOn a A) (hb : Set.InjOn b A) :
    ∃ T : Fin 3 → Finset V, ThreeClasses A a b T := by
  classical
  let H := choiceConflict A a b
  let rank : A → ℕ := fun x => (Fintype.equivFin A x).val
  have hrank : Function.Injective rank :=
    Fin.val_injective.comp (Fintype.equivFin A).injective
  have hdeg (x : A) : ((H.neighborFinset x).filter (fun y => rank y < rank x)).card < 3 := by
    have hle := card_le_card (filter_subset (fun y => rank y < rank x) (H.neighborFinset x))
    have htwo := conflict_degree_le_two A a b ha hb x
    change (H.neighborFinset x).card ≤ 2 at htwo
    omega
  obtain ⟨k⟩ := BrooksSubcubic.colorable_of_lower_neighbors_lt H 3 rank hrank hdeg
  let label : V → Fin 3 := fun x => if hx : x ∈ A then k ⟨x, hx⟩ else 0
  let T : Fin 3 → Finset V := fun i => A.filter (fun x => label x = i)
  refine ⟨T, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact filter_subset _ _
  · intro x
    simp only [T, mem_filter]
    exact ⟨fun hx => ⟨label x, hx, rfl⟩, fun ⟨_, hx, _⟩ => hx⟩
  · intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    exact hij (((mem_filter.mp hxi).2).symm.trans (mem_filter.mp hxj).2)
  · intro i x hx y hy hxy
    have hxA := (mem_filter.mp hx).1
    have hyA := (mem_filter.mp hy).1
    have hcol : k ⟨x, hxA⟩ = k ⟨y, hyA⟩ := by
      have h1 := (mem_filter.mp hx).2
      have h2 := (mem_filter.mp hy).2
      simpa only [label, dite_eq_left hxA, dite_eq_left hyA] using h1.trans h2.symm
    have hd : Disjoint (colourPair a b x) (colourPair a b y) := by
      by_contra hn
      exact k.valid (show H.Adj ⟨x, hxA⟩ ⟨y, hyA⟩ from
        ⟨fun he => hxy (congrArg Subtype.val he), hn⟩) hcol
    apply disjoint_left.mpr
    intro z hzx hzy
    cases z with
    | inl v =>
      have h1 : v = x := by simpa [taggedSupport] using hzx
      have h2 : v = y := by simpa [taggedSupport] using hzy
      exact hxy (h1.symm.trans h2)
    | inr q =>
      apply (disjoint_left.mp hd)
      · simpa [taggedSupport, colourPair] using hzx
      · simpa [taggedSupport, colourPair] using hzy
  · simpa [T] using
      sum_card_fiberwise_eq_card_filter A (univ : Finset (Fin 3)) label

/-- Threshold exceptions are defined using the actual repeated-colour fibers. -/
noncomputable def exceptions (G : Digraph V) (c : V → V → C) (u : V) (t : ℝ) : Finset V := by
  classical
  exact univ.filter (fun w => t < (repeated G c u w).card)

private theorem exception_card_lt (G : Digraph V) (c : V → V → C)
    (hout : OutProper G c) (u : V) (t : ℝ) (ht : 0 < t)
    (hn : 0 < Fintype.card V) :
    ((exceptions G c u t).card : ℝ) < Fintype.card V / t := by
  classical
  let B := exceptions G c u t
  have hm : (∑ w : V, ((repeated G c u w).card : ℝ)) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast (repeated_colour_mass_le_outdegree G c hout u).trans (card_le_univ _)
  apply (lt_div_iff₀ ht).mpr
  by_cases hB : B.Nonempty
  · have hlt : (B.card : ℝ) * t < ∑ w ∈ B, ((repeated G c u w).card : ℝ) := by
      rw [← nsmul_eq_mul, ← sum_const]
      exact sum_lt_sum_of_nonempty hB (fun w hw => (mem_filter.mp hw).2)
    have hle : (∑ w ∈ B, ((repeated G c u w).card : ℝ)) ≤
        ∑ w : V, ((repeated G c u w).card : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ B) (fun _ _ _ => Nat.cast_nonneg _)
    exact hlt.trans_le (hle.trans hm)
  · have hz : B.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hB)
    change (B.card : ℝ) * t < Fintype.card V
    rw [hz]
    simpa using (show (0 : ℝ) < Fintype.card V by exact_mod_cast hn)

private theorem rainbow_card_add_loss (G : Digraph V) (c : V → V → C)
    (u w : V) (A : Finset V) (hA : A ⊆ twoStep G u w) :
    A.card ≤ (rainbow c u w A).card + (repeated G c u w).card := by
  classical
  have hsub : (A.filter (fun x => c u x = c x w)) ⊆ repeated G c u w := by
    intro x hx
    have hxA := hA (mem_filter.mp hx).1
    exact mem_filter.mpr ⟨(mem_filter.mp hxA).1,
      (mem_filter.mp hxA).2, (mem_filter.mp hx).2⟩
  have he := card_filter_add_card_filter_not (s := A) (fun x => c u x = c x w)
  have hle := card_le_card hsub
  simpa only [rainbow] using (show A.card ≤
    (A.filter (fun x => ¬ c u x = c x w)).card + (repeated G c u w).card by omega)

/-- The first consumed deterministic core of the repaired longer connector.
For any actual base family at a nonexceptional distinct endpoint, produce enough genuine
rainbow simple two-edge paths and partition all of them into disjoint tagged-coordinate classes. -/
theorem deterministic_rainbow_choice_core (G : Digraph V) (c : V → V → C)
    (hout : OutProper G c) (hin : InProper G c) (hloop : ∀ x, ¬ G.Adj x x)
    (ν : ℝ) (hν : 0 < ν) (hn : 0 < Fintype.card V) (u : V) :
    let n : ℝ := Fintype.card V
    let B := exceptions G c u (ν * n / 16)
    (B.card : ℝ) < 16 / ν ∧
    ∀ w, u ≠ w → w ∉ B → ∀ A : Finset V, A ⊆ twoStep G u w →
      ν * n / 4 ≤ (A.card : ℝ) →
      ∃ T : Fin 3 → Finset V,
        ThreeClasses (rainbow c u w A) (c u) (fun x => c x w) T ∧
        3 * ν * n / 16 ≤ ((rainbow c u w A).card : ℝ) ∧
        (∀ x ∈ rainbow c u w A,
          G.Adj u x ∧ G.Adj x w ∧ u ≠ x ∧ x ≠ w ∧ u ≠ w ∧ c u x ≠ c x w ∧
            (taggedSupport (c u) (fun y => c y w) x).card = 3) := by
  classical
  dsimp only
  let n : ℝ := Fintype.card V
  have hn' : 0 < n := by
    dsimp only [n]
    exact_mod_cast hn
  have ht : 0 < ν * n / 16 := by positivity
  constructor
  · have h := exception_card_lt G c hout u (ν * n / 16) ht hn
    change ((exceptions G c u (ν * n / 16)).card : ℝ) < n / (ν * n / 16) at h
    have he : n / (ν * n / 16) = 16 / ν := by
      field_simp [ne_of_gt hν, ne_of_gt hn']
    simpa only [he] using h
  · intro w huw hw A hA hsize
    have hloss : ((repeated G c u w).card : ℝ) ≤ ν * n / 16 := by
      simpa only [exceptions, mem_filter, mem_univ, true_and, not_lt] using hw
    have hcount := rainbow_card_add_loss G c u w A hA
    have hcount' : (A.card : ℝ) ≤
        (rainbow c u w A).card + (repeated G c u w).card := by exact_mod_cast hcount
    have hrsub : rainbow c u w A ⊆ A := filter_subset _ _
    have ha : Set.InjOn (c u) (rainbow c u w A) := by
      intro x hx y hy hxy
      exact hout u (mem_filter.mp (mem_filter.mp (hA (hrsub hx))).1).2
        (mem_filter.mp (mem_filter.mp (hA (hrsub hy))).1).2 hxy
    have hb : Set.InjOn (fun x => c x w) (rainbow c u w A) := by
      intro x hx y hy hxy
      exact hin w (mem_filter.mp (hA (hrsub hx))).2
        (mem_filter.mp (hA (hrsub hy))).2 hxy
    obtain ⟨T, hT⟩ := exists_three_disjoint_classes (rainbow c u w A)
      (c u) (fun x => c x w) ha hb
    refine ⟨T, hT, by linarith, ?_⟩
    intro x hx
    have hux := (mem_filter.mp (mem_filter.mp (hA (hrsub hx))).1).2
    have hxw := (mem_filter.mp (hA (hrsub hx))).2
    have hc := (mem_filter.mp hx).2
    refine ⟨hux, hxw, ?_, ?_, huw, hc, ?_⟩
    · intro he
      exact hloop u (he.symm ▸ hux)
    · intro he
      exact hloop w (he ▸ hxw)
    · simp [taggedSupport, hc]

end D5.S3.Combinatorics.Graph.Rainbow.TwoEdgeChoices
