/- GID: D5/S3/Topology/PathContiguity
   generality: G
   mirror-B: D5/B/S3/Topology/PathContiguity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Basic]
   utility: none
   digest: Relative contiguity of maps from finite complexes to an interval. -/

module

public import D5.S3.Topology.BarycentricBaseRigidity
public import Mathlib.Data.Set.Function
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import OmegaBuild.Commands

/-! # Relative contiguity of maps to a finite path

An edge of the source may map to a vertex or an edge of the target. Lowering a
maximal excess value by one gives a contiguous step toward any pointwise
smaller map. The pointwise minimum supplies a common map to descend to.
-/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false

namespace D5.S3.Topology.PathContiguity

open Relation
open scoped BigOperators

variable {V : Type*}

/-- The vertex values lie in `[0,N]` and the values on each edge differ by at most one. -/
def IsIntervalMap (G : SimpleGraph V) (N : ℕ) (f : V → ℕ) : Prop :=
  (∀ x, f x ≤ N) ∧ ∀ ⦃x y⦄, G.Adj x y → f x ≤ f y + 1 ∧ f y ≤ f x + 1

/-- The union of the images of each vertex or edge has spread at most one.
Quantifying over ordered pairs of endpoints tests both directions on each edge. -/
def Contiguous (G : SimpleGraph V) (f g : V → ℕ) : Prop :=
  ∀ ⦃x y⦄, x = y ∨ G.Adj x y → max (f x) (g x) ≤ min (f y) (g y) + 1

/-- Both maps have values in the interval and agree with `r` at all vertices of `S`. -/
def RelativeContiguous (G : SimpleGraph V) (N : ℕ) (S : Set V) (r f g : V → ℕ) : Prop :=
  (∀ x, f x ≤ N) ∧ (∀ x, g x ≤ N) ∧
    Set.EqOn f r S ∧ Set.EqOn g r S ∧ Contiguous G f g

instance (G : SimpleGraph V) (N : ℕ) (S : Set V) (r : V → ℕ) :
    Std.Symm (RelativeContiguous G N S r) where
  symm f g h := by
    rcases h with ⟨hf, hg, hfr, hgr, hc⟩
    refine ⟨hg, hf, hgr, hfr, ?_⟩
    intro x y hxy
    simpa only [max_comm, min_comm] using hc hxy

private theorem isIntervalMap_min {G : SimpleGraph V} {N : ℕ} {f g : V → ℕ}
    (hf : IsIntervalMap G N f) (hg : IsIntervalMap G N g) :
    IsIntervalMap G N (fun x => min (f x) (g x)) := by
  have edge {x y : V} (hxy : G.Adj x y) : min (f x) (g x) ≤ min (f y) (g y) + 1 := by
    rcases le_total (f y) (g y) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (hf.2 hxy).1
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (hg.2 hxy).1
  exact ⟨fun x => (min_le_left _ _).trans (hf.1 x), fun _ _ hxy => ⟨edge hxy, edge hxy.symm⟩⟩

private theorem descend [Fintype V] {G : SimpleGraph V} {N : ℕ} {S : Set V} {r h : V → ℕ}
    (hh : IsIntervalMap G N h) (hhr : Set.EqOn h r S) :
    ∀ n : ℕ, ∀ f : V → ℕ, (∑ x, f x) = n → IsIntervalMap G N f →
      (∀ x, h x ≤ f x) → Set.EqOn f r S →
      ReflTransGen (RelativeContiguous G N S r) f h := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hsum hf hle hfr
    by_cases heq : f = h
    · subst f
      exact .refl
    have hex : ∃ x, h x < f x := by
      by_contra hnone
      exact heq (funext fun x => le_antisymm (le_of_not_gt fun hx => hnone ⟨x, hx⟩) (hle x))
    let excess : Finset V := Finset.univ.filter fun x => h x < f x
    have hne : excess.Nonempty := by
      obtain ⟨x, hx⟩ := hex
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
    obtain ⟨x, hx, hmax⟩ := excess.exists_max_image f hne
    have hxlt : h x < f x := (Finset.mem_filter.mp hx).2
    -- A higher neighbor would have no excess, violating the edge bound for h.
    have neighbor_le (y : V) (hxy : G.Adj x y) : f y ≤ f x := by
      apply le_of_not_gt
      intro hgt
      have hyeq : f y = h y := by
        refine le_antisymm (le_of_not_gt ?_) (hle y)
        intro hy
        exact (not_le_of_gt hgt) (hmax y (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩))
      have hbound := (hh.2 hxy).2
      omega
    let f' : V → ℕ := fun y => if y = x then f x - 1 else f y
    have hnew_le (y : V) : f' y ≤ f y := by
      by_cases hy : y = x
      · subst y
        simpa only [f', ite_eq_left rfl] using Nat.sub_le (f x) 1
      · simp only [f', ite_eq_right hy, le_rfl]
    have hle_new (y : V) : h y ≤ f' y := by
      by_cases hy : y = x
      · subst y
        simp only [f', ite_eq_left rfl]
        omega
      · simpa only [f', ite_eq_right hy] using hle y
    -- On an incident edge the old and new values lie in [f x - 1, f x].
    have cross {y z : V} (hyz : y = z ∨ G.Adj y z) : f y ≤ f' z + 1 := by
      by_cases hz : z = x
      · subst z
        have hy : f y ≤ f x := by
          rcases hyz with he | hyx
          · rw [he]
          · exact neighbor_le y hyx.symm
        simp only [f', ite_eq_left rfl]
        omega
      · have hy : f y ≤ f z + 1 := by
          rcases hyz with he | hadj
          · rw [he]
            exact Nat.le_succ _
          · exact (hf.2 hadj).1
        simpa only [f', ite_eq_right hz] using hy
    have hf' : IsIntervalMap G N f' :=
      ⟨fun y => (hnew_le y).trans (hf.1 y),
        fun _ _ hyz => ⟨(hnew_le _).trans (cross (.inr hyz)),
          (hnew_le _).trans (cross (.inr hyz.symm))⟩⟩
    have hf'r : Set.EqOn f' r S := by
      intro y hy
      exact le_antisymm ((hnew_le y).trans (hfr hy).le) ((hhr hy).ge.trans (hle_new y))
    have hstep : RelativeContiguous G N S r f f' := by
      refine ⟨hf.1, hf'.1, hfr, hf'r, ?_⟩
      intro y z hyz
      rw [max_eq_left (hnew_le y), min_eq_right (hnew_le z)]
      exact cross hyz
    have hlt : f' x < f x := by
      simp only [f', ite_eq_left rfl]
      omega
    have hsum_lt : (∑ y, f' y) < n := by
      rw [← hsum]
      exact Finset.sum_lt_sum (fun y _ => hnew_le y) ⟨x, Finset.mem_univ x, hlt⟩
    exact ReflTransGen.head hstep (ih _ hsum_lt f' rfl hf' hle_new hf'r)

/-- Two simplicial maps from a finite graph to `[0,N]` that agree on `S`
are connected by a finite contiguity chain fixing their values on `S`. -/
theorem relative_contiguity [Finite V] (G : SimpleGraph V) (N : ℕ) (S : Set V)
    {f g : V → ℕ} (hf : IsIntervalMap G N f) (hg : IsIntervalMap G N g)
    (hfix : Set.EqOn f g S) :
    ReflTransGen (RelativeContiguous G N S f) f g := by
  classical
  let := Fintype.ofFinite V
  let h : V → ℕ := fun x => min (f x) (g x)
  have hh : IsIntervalMap G N h := isIntervalMap_min hf hg
  have hhfix : Set.EqOn h f S := by
    intro x hx
    change min (f x) (g x) = f x
    rw [hfix hx, min_self]
  have hfh : ReflTransGen (RelativeContiguous G N S f) f h :=
    descend hh hhfix _ f rfl hf (fun x => min_le_left (f x) (g x)) (fun _ _ => rfl)
  have hgh : ReflTransGen (RelativeContiguous G N S f) g h :=
    descend hh hhfix _ g rfl hg (fun x => min_le_right (f x) (g x)) hfix.symm
  exact hfh.trans (symm hgh)

open BarycentricGraphDistance (Vertex oneSkeleton)
open BarycentricBaseRigidity (faceImage)

/-- The path complex with vertices `0,…,N` and edges between consecutive values. -/
def intervalComplex (N : ℕ) : PreAbstractSimplicialComplex ℕ where
  faces := {s | s.Nonempty ∧ (∀ a ∈ s, a ≤ N) ∧ ∀ a ∈ s, ∀ b ∈ s, a ≤ b + 1}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun _ hsub hne =>
      ⟨hne, fun a ha => hs.2.1 a (hsub ha),
        fun a ha b hb => hs.2.2 a (hsub ha) b (hsub hb)⟩⟩

section Complex

variable {X : Type}

-- Clipping makes the lift defined on every labeling. It is the identity on
-- values at most N.
private def toVertexMap {P : PreAbstractSimplicialComplex X} (N : ℕ) (f : Vertex P → ℕ) :
    Vertex P → Vertex (intervalComplex N) := fun x => by
  refine ⟨min (f x) N, Finset.singleton_nonempty _, ?_, ?_⟩
  · intro a ha
    rw [Finset.mem_singleton.mp ha]
    exact min_le_right _ _
  · intro a ha b hb
    rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]
    exact Nat.le_succ _

private theorem contiguous_toVertexMap [DecidableEq X]
    {P : PreAbstractSimplicialComplex X} {N : ℕ} {f g : Vertex P → ℕ}
    (hf : ∀ x, f x ≤ N) (hg : ∀ x, g x ≤ N) (hc : Contiguous (oneSkeleton P) f g) :
    BarycentricBaseRigidity.Contiguous (toVertexMap N f) (toVertexMap N g) := by
  let : DecidableEq ℕ := Classical.decEq ℕ
  intro s hs
  have preimage (a : Vertex P → ℕ) (ha : ∀ x, a x ≤ N) {n : ℕ}
      (hn : n ∈ faceImage (toVertexMap N a) hs) :
      ∃ x : Vertex P, x.val ∈ s ∧ n = a x := by
    unfold faceImage at hn
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hn
    let v : Vertex P := ⟨x.val, (P.isRelLowerSet_faces hs).2
      (Finset.singleton_subset_iff.mpr x.property) (Finset.singleton_nonempty _)⟩
    change min (a v) N = n at hx
    exact ⟨v, x.property, hx.symm.trans (min_eq_left (ha v))⟩
  have from_union {n : ℕ}
      (hn : n ∈ faceImage (toVertexMap N f) hs ∪ faceImage (toVertexMap N g) hs) :
      ∃ x : Vertex P, x.val ∈ s ∧
        n ≤ N ∧ n ≤ max (f x) (g x) ∧ min (f x) (g x) ≤ n := by
    rcases Finset.mem_union.mp hn with hn | hn
    · obtain ⟨x, hx, rfl⟩ := preimage f hf hn
      exact ⟨x, hx, hf x, le_max_left _ _, min_le_left _ _⟩
    · obtain ⟨x, hx, rfl⟩ := preimage g hg hn
      exact ⟨x, hx, hg x, le_max_right _ _, min_le_right _ _⟩
  have hne : (faceImage (toVertexMap N f) hs).Nonempty :=
    Finset.image_nonempty.mpr (Finset.attach_nonempty_iff.mpr (P.isRelLowerSet_faces hs).1)
  refine ⟨hne.mono Finset.subset_union_left, ?_, ?_⟩
  · intro n hn
    obtain ⟨_, _, hbound, _, _⟩ := from_union hn
    exact hbound
  · intro a ha b hb
    obtain ⟨x, hx, _, haMax, _⟩ := from_union ha
    obtain ⟨y, hy, _, _, hyMin⟩ := from_union hb
    have hxy : x = y ∨ (oneSkeleton P).Adj x y := by
      by_cases he : x = y
      · exact Or.inl he
      · exact Or.inr ⟨he, (P.isRelLowerSet_faces hs).2
          (Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩)
          (Finset.insert_nonempty _ _)⟩
    exact haMax.trans ((hc hxy).trans (Nat.add_le_add_right hyMin 1))

/-- The relative chain expressed in the facewise contiguity API.
Each face is checked by applying the one-skeleton bound to every pair of its vertices. -/
theorem relative_complex_contiguity {P : PreAbstractSimplicialComplex X}
    [DecidableEq X] [Finite (Vertex P)] (N : ℕ) (S : Set (Vertex P))
    {f g : Vertex P → Vertex (intervalComplex N)}
    (hf : IsIntervalMap (oneSkeleton P) N (fun x => (f x).val))
    (hg : IsIntervalMap (oneSkeleton P) N (fun x => (g x).val))
    (hfix : Set.EqOn f g S) :
    ReflTransGen
      (fun a b : Vertex P → Vertex (intervalComplex N) =>
        BarycentricBaseRigidity.Contiguous a b ∧ Set.EqOn a f S ∧ Set.EqOn b f S) f g := by
  let F : Vertex P → ℕ := fun x => (f x).val
  let H : Vertex P → ℕ := fun x => (g x).val
  let R (a b : Vertex P → Vertex (intervalComplex N)) :=
    BarycentricBaseRigidity.Contiguous a b ∧ Set.EqOn a f S ∧ Set.EqOn b f S
  have hfixed : Set.EqOn F H S := by
    intro x hx
    exact congrArg Subtype.val (hfix hx)
  have hchain := relative_contiguity (oneSkeleton P) N S hf hg hfixed
  have fix_lift {a : Vertex P → ℕ} (ha : ∀ x, a x ≤ N) (h : Set.EqOn a F S) :
      Set.EqOn (toVertexMap N a) f S := by
    intro x hx
    exact Subtype.ext ((min_eq_left (ha x)).trans (h hx))
  have hstep (a b : Vertex P → ℕ) (h : RelativeContiguous (oneSkeleton P) N S F a b) :
      R (toVertexMap N a) (toVertexMap N b) := by
    rcases h with ⟨ha, hb, haf, hbf, hc⟩
    exact ⟨contiguous_toVertexMap ha hb hc, fix_lift ha haf, fix_lift hb hbf⟩
  have hlift : ReflTransGen R (toVertexMap N F) (toVertexMap N H) :=
    ReflTransGen.lift (toVertexMap N) hstep F H hchain
  have hF : toVertexMap N F = f := by
    funext x
    exact Subtype.ext (min_eq_left (hf.1 x))
  have hH : toVertexMap N H = g := by
    funext x
    exact Subtype.ext (min_eq_left (hg.1 x))
  rw [hF, hH] at hlift
  exact hlift

end Complex

end D5.S3.Topology.PathContiguity
