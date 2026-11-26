/- GID: D5/S3/Topology/BarycentricGraphDistance
   generality: G
   mirror-B: D5/B/S3/Topology/BarycentricGraphDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric]
   utility: none
   digest: Barycentric subdivision doubles extended graph distance between subcomplexes. -/

module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Lattice
import OmegaBuild.Commands

/-! # Graph distance under barycentric subdivision

A shortest walk between subcomplexes in the face comparability graph
alternates between inclusion minima and maxima. Vertices chosen in successive
minima lie together in the intervening maximum. In the other direction, each
edge of the original complex is bisected at its two-vertex face.
-/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false

namespace D5.S3.Topology.BarycentricGraphDistance

open SimpleGraph
open scoped ENat

variable {V : Type*}

/-- A vertex of the original complex, represented by its singleton face. -/
abbrev Vertex (J : PreAbstractSimplicialComplex V) := {x : V // ({x} : Finset V) ∈ J}

/-- A vertex of the barycentric subdivision, represented by its nonempty face. -/
abbrev Face (J : PreAbstractSimplicialComplex V) := {s : Finset V // s ∈ J}

/-- The one-skeleton of the original complex. -/
def oneSkeleton [DecidableEq V] (J : PreAbstractSimplicialComplex V) : SimpleGraph (Vertex J) where
  Adj x y := x ≠ y ∧ ({x.val, y.val} : Finset V) ∈ J
  symm := ⟨fun x y ⟨hne, hface⟩ =>
    ⟨Ne.symm hne, Finset.pair_comm x.val y.val ▸ hface⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The one-skeleton of the barycentric subdivision. -/
def subdivisionGraph (J : PreAbstractSimplicialComplex V) : SimpleGraph (Face J) where
  Adj s t := s < t ∨ t < s
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.elim (lt_irrefl _) (lt_irrefl _)⟩

/-- The original vertices belonging to a subcomplex. -/
def vertexSet (J P : PreAbstractSimplicialComplex V) : Set (Vertex J) :=
  {x | ({x.val} : Finset V) ∈ P}

/-- The subdivided vertices belonging to a subcomplex. -/
def subdivisionVertexSet (J P : PreAbstractSimplicialComplex V) : Set (Face J) :=
  {s | s.val ∈ P}

/-- Extended distance between vertex sets, with the empty infimum equal to infinity. -/
noncomputable def graphSetEdist {α : Type*} (G : SimpleGraph α) (S T : Set α) : ℕ∞ :=
  ⨅ s : S, ⨅ t : T, G.edist s.val t.val

private theorem graphSetEdist_le_walk {α : Type*} {G : SimpleGraph α} {S T : Set α}
    {s t : α} (hs : s ∈ S) (ht : t ∈ T) (p : G.Walk s t) :
    graphSetEdist G S T ≤ p.length := by
  unfold graphSetEdist
  exact iInf_le_of_le (⟨s, hs⟩ : S) (iInf_le_of_le (⟨t, ht⟩ : T) p.edist_le)

variable {J P Q : PreAbstractSimplicialComplex V}

private theorem singleton_mem {s : Finset V} {x : V} (hs : s ∈ J) (hx : x ∈ s) :
    ({x} : Finset V) ∈ J :=
  (J.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty _)

private def singletonFace (x : Vertex J) : Face J := ⟨{x.val}, x.property⟩

private theorem singletonFace_lt {x : Vertex J} {s : Face J} {y : V}
    (hx : x.val ∈ s.val) (hy : y ∈ s.val) (hne : y ≠ x.val) : singletonFace x < s := by
  classical
  change ({x.val} : Finset V) ⊂ s.val
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr hx, ?_⟩
  intro h
  exact hne (Finset.mem_singleton.mp (h ▸ hy : y ∈ ({x.val} : Finset V)))

private theorem exists_bisected_walk [DecidableEq V] {x y : Vertex J}
    (p : (oneSkeleton J).Walk x y) :
    ∃ q : (subdivisionGraph J).Walk (singletonFace x) (singletonFace y),
      q.length = 2 * p.length := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons x y z h p ih =>
    obtain ⟨q, hq⟩ := ih
    let e : Face J := ⟨{x.val, y.val}, h.2⟩
    have hne : x.val ≠ y.val := fun he => h.1 (Subtype.ext he)
    have hx : singletonFace x < e :=
      singletonFace_lt (by simp [e]) (by simp [e] : y.val ∈ e.val) hne.symm
    have hy : singletonFace y < e :=
      singletonFace_lt (by simp [e]) (by simp [e] : x.val ∈ e.val) hne
    refine ⟨.cons (Or.inl hx) (.cons (Or.inr hy) q), ?_⟩
    change q.length + 1 + 1 = 2 * (p.length + 1)
    omega

private theorem shortest_tail {a b c : Face J}
    (hab : (subdivisionGraph J).Adj a b) (p : (subdivisionGraph J).Walk b c)
    (hmin : ∀ t : Face J, t.val ∈ Q → ∀ q : (subdivisionGraph J).Walk a t,
      (Walk.cons hab p).length ≤ q.length) :
    ∀ t : Face J, t.val ∈ Q →
      ∀ q : (subdivisionGraph J).Walk b t, p.length ≤ q.length := by
  intro t ht q
  have h := hmin t ht (Walk.cons hab q)
  simpa only [Walk.length_cons, Nat.add_le_add_iff_right] using h

private theorem shortest_tail_ascends {c d b : Face J}
    (hdc : d < c) (p : (subdivisionGraph J).Walk d b) (hb : b.val ∈ Q)
    (hmin : ∀ t : Face J, t.val ∈ Q → ∀ q : (subdivisionGraph J).Walk c t,
      (Walk.cons (Or.inr hdc : (subdivisionGraph J).Adj c d) p).length ≤ q.length) :
    ¬ p.Nil → d < p.snd := by
  intro hn
  rcases p.adj_snd hn with hde | hed
  · exact hde
  · have h := hmin b hb (Walk.cons (Or.inr (hed.trans hdc)) p.tail)
    have hlen := p.length_tail_add_one hn
    change p.length + 1 ≤ p.tail.length + 1 at h
    omega

variable [DecidableEq V]

-- Consume a rise and a fall at each step. The suffix is still shortest to the target set.
private theorem compress_ascending_shortest (n : ℕ) {a b : Face J}
    (p : (subdivisionGraph J).Walk a b) (hsize : p.length ≤ n) (hb : b.val ∈ Q)
    (hmin : ∀ t : Face J, t.val ∈ Q →
      ∀ q : (subdivisionGraph J).Walk a t, p.length ≤ q.length)
    (hup : ¬ p.Nil → a < p.snd) (x : Vertex J) (hx : x.val ∈ a.val) :
    ∃ y : Vertex J, y.val ∈ b.val ∧
      ∃ q : (oneSkeleton J).Walk x y, 2 * q.length ≤ p.length := by
  induction n using Nat.strong_induction_on generalizing a b x with
  | h n ih =>
    cases p with
    | nil => exact ⟨x, hx, .nil, by simp⟩
    | @cons a c b hac r =>
      have hac' : a < c := by
        simpa only [Walk.snd_cons] using hup (by simp)
      cases r with
      | nil =>
        have ha : a.val ∈ Q := (Q.isRelLowerSet_faces hb).2 hac'.le
          (J.isRelLowerSet_faces a.property).1
        have h := hmin a ha Walk.nil
        change 1 ≤ 0 at h
        omega
      | @cons c d b hcd p =>
        have hdc : d < c := by
          rcases hcd with hcd | hdc
          · have h := hmin b hb (Walk.cons (Or.inl (hac'.trans hcd)) p)
            change p.length + 1 + 1 ≤ p.length + 1 at h
            omega
          · exact hdc
        have hcmin := shortest_tail hac _ hmin
        have hdmin := shortest_tail hcd p hcmin
        have hdup := shortest_tail_ascends hdc p hb hcmin
        have hlt : p.length < n := by
          change p.length + 1 + 1 ≤ n at hsize
          omega
        obtain ⟨v, hv⟩ := (J.isRelLowerSet_faces d.property).1
        let z : Vertex J := ⟨v, singleton_mem d.property hv⟩
        obtain ⟨y, hy, q, hq⟩ := ih p.length hlt p le_rfl hb hdmin hdup z hv
        by_cases h : x = z
        · subst x
          refine ⟨y, hy, q, ?_⟩
          change 2 * q.length ≤ p.length + 1 + 1
          omega
        · have hedge : (oneSkeleton J).Adj x z := by
            refine ⟨h, (J.isRelLowerSet_faces c.property).2 ?_ (by simp)⟩
            exact Finset.insert_subset_iff.mpr
              ⟨hac'.le hx, Finset.singleton_subset_iff.mpr (hdc.le hv)⟩
          refine ⟨y, hy, .cons hedge q, ?_⟩
          change 2 * (q.length + 1) ≤ p.length + 1 + 1
          omega

/-- A face walk between subcomplexes yields a walk between their original vertices
using at most half as many edges. The chosen endpoints may move within the subcomplexes. -/
theorem exists_walk_of_face_walk {a b : Face J}
    (ha : a ∈ subdivisionVertexSet J P) (hb : b ∈ subdivisionVertexSet J Q)
    (p : (subdivisionGraph J).Walk a b) :
    ∃ x ∈ vertexSet J P, ∃ y ∈ vertexSet J Q,
      ∃ q : (oneSkeleton J).Walk x y, 2 * q.length ≤ p.length := by
  classical
  let hasWalk (n : ℕ) : Prop :=
    ∃ s : Face J, s.val ∈ P ∧ ∃ t : Face J, t.val ∈ Q ∧
      ∃ w : (subdivisionGraph J).Walk s t, w.length = n
  have hHas : ∃ n, hasWalk n := ⟨p.length, a, ha, b, hb, p, rfl⟩
  obtain ⟨s, hs, t, ht, w, hw⟩ := Nat.find_spec hHas
  have hmin {u v : Face J} (hu : u.val ∈ P) (hv : v.val ∈ Q)
      (r : (subdivisionGraph J).Walk u v) : w.length ≤ r.length :=
    hw.trans_le (Nat.find_min' hHas ⟨u, hu, v, hv, r, rfl⟩)
  have hup : ¬ w.Nil → s < w.snd := by
    intro hn
    rcases w.adj_snd hn with h | h
    · exact h
    · have hm : w.snd.val ∈ P := (P.isRelLowerSet_faces hs).2 h.le
        (J.isRelLowerSet_faces w.snd.property).1
      have hshort := hmin hm ht w.tail
      have hlen := w.length_tail_add_one hn
      omega
  obtain ⟨u, hu⟩ := (J.isRelLowerSet_faces s.property).1
  let x : Vertex J := ⟨u, singleton_mem s.property hu⟩
  obtain ⟨y, hy, q, hq⟩ :=
    compress_ascending_shortest w.length w le_rfl ht (fun _ => hmin hs) hup x hu
  exact ⟨x, singleton_mem hs hu, y, singleton_mem ht hy, q, hq.trans (hmin ha hb p)⟩

/-- Barycentric subdivision doubles the extended one-skeleton distance between
subcomplexes. The endpoint sets are taken inside the ambient complex `J`.
Empty endpoint sets and disconnected pairs have distance `⊤`. -/
theorem subdivision_edist_eq_two_mul :
    graphSetEdist (subdivisionGraph J) (subdivisionVertexSet J P) (subdivisionVertexSet J Q) =
      2 * graphSetEdist (oneSkeleton J) (vertexSet J P) (vertexSet J Q) := by
  apply le_antisymm
  · conv_rhs => unfold graphSetEdist SimpleGraph.edist
    simp only [ENat.mul_iInf_of_ne (by decide : (2 : ℕ∞) ≠ 0)]
    refine le_iInf fun x => le_iInf fun y => le_iInf fun p => ?_
    obtain ⟨q, hq⟩ := exists_bisected_walk p
    have hlength : (q.length : ℕ∞) = 2 * (p.length : ℕ∞) := by exact_mod_cast hq
    rw [← hlength]
    exact graphSetEdist_le_walk (s := singletonFace x.val) (t := singletonFace y.val)
      x.property y.property q
  · conv_rhs => unfold graphSetEdist SimpleGraph.edist
    refine le_iInf fun a => le_iInf fun b => le_iInf fun p => ?_
    obtain ⟨x, hx, y, hy, q, hq⟩ := exists_walk_of_face_walk a.property b.property p
    calc
      _ ≤ 2 * (q.length : ℕ∞) := by
        gcongr
        exact graphSetEdist_le_walk hx hy q
      _ ≤ (p.length : ℕ∞) := by exact_mod_cast hq

/-- If a full subcomplex `W` contains the ambient original vertices within distance `D`
of `P ≤ J`, then any ambient face within `2 * D` face-graph steps of a face of `P`
belongs to `W`. Fullness is expressed on the faces of `J`. -/
theorem mem_full_subcomplex_of_face_walk {W : PreAbstractSimplicialComplex V}
    (hPJ : P ≤ J)
    (hfull : ∀ s : Face J, (∀ v ∈ s.val, ({v} : Finset V) ∈ W) → s.val ∈ W)
    {D : ℕ}
    (hnear : ∀ x : Vertex J,
      graphSetEdist (oneSkeleton J) {x} (vertexSet J P) ≤ (D : ℕ∞) → x ∈ vertexSet J W)
    {a b : Face J} (hb : b ∈ subdivisionVertexSet J P)
    (p : (subdivisionGraph J).Walk a b) (hp : p.length ≤ 2 * D) :
    a ∈ subdivisionVertexSet J W := by
  classical
  have mem_of_walk {x y : Vertex J} (hy : y ∈ vertexSet J P)
      (q : (oneSkeleton J).Walk x y) (hlen : q.length ≤ D) : x ∈ vertexSet J W :=
    hnear x ((graphSetEdist_le_walk (Set.mem_singleton x) hy q).trans (by exact_mod_cast hlen))
  have hPW : P ≤ W := by
    intro s hs
    refine hfull ⟨s, hPJ hs⟩ fun v hv => ?_
    let x : Vertex J := ⟨v, singleton_mem (hPJ hs) hv⟩
    exact mem_of_walk (x := x) (singleton_mem hs hv) .nil (Nat.zero_le D)
  by_cases ha : a.val ∈ P
  · exact hPW ha
  let hasWalk (n : ℕ) : Prop :=
    ∃ t : Face J, t.val ∈ P ∧ ∃ w : (subdivisionGraph J).Walk a t, w.length = n
  have hHas : ∃ n, hasWalk n := ⟨p.length, b, hb, p, rfl⟩
  obtain ⟨t, ht, w, hw⟩ := Nat.find_spec hHas
  have hmin (s : Face J) (hs : s.val ∈ P) (q : (subdivisionGraph J).Walk a s) :
      w.length ≤ q.length := hw.trans_le (Nat.find_min' hHas ⟨s, hs, q, rfl⟩)
  have hwlen := (hmin b hb p).trans hp
  -- The first valley lies in a face containing the starting face.
  have finish {c d : Face J} (hac : a.val ⊆ c.val) (hdc : d < c)
      (r : (subdivisionGraph J).Walk d t) (hr : r.length < 2 * D)
      (hcmin : ∀ s : Face J, s.val ∈ P → ∀ q : (subdivisionGraph J).Walk c s,
        (Walk.cons (Or.inr hdc : (subdivisionGraph J).Adj c d) r).length ≤ q.length) :
      a ∈ subdivisionVertexSet J W := by
    obtain ⟨v, hv⟩ := (J.isRelLowerSet_faces d.property).1
    let z : Vertex J := ⟨v, singleton_mem d.property hv⟩
    have hdmin := shortest_tail (Or.inr hdc) r hcmin
    obtain ⟨y, hy, q, hq⟩ := compress_ascending_shortest r.length r le_rfl ht hdmin
      (shortest_tail_ascends hdc r ht hcmin) z hv
    have hyP : y ∈ vertexSet J P := singleton_mem ht hy
    apply hfull a
    intro u hu
    let x : Vertex J := ⟨u, singleton_mem a.property hu⟩
    change x ∈ vertexSet J W
    by_cases he : x = z
    · rw [he]
      exact mem_of_walk hyP q (by omega)
    · have hedge : (oneSkeleton J).Adj x z := by
        refine ⟨he, (J.isRelLowerSet_faces c.property).2 ?_ (by simp)⟩
        exact Finset.insert_subset_iff.mpr
          ⟨hac hu, Finset.singleton_subset_iff.mpr (hdc.le hv)⟩
      exact mem_of_walk hyP (.cons hedge q) (by rw [Walk.length_cons]; omega)
  cases w with
  | nil => exact (ha ht).elim
  | @cons a c t hac r =>
    have hcmin := shortest_tail hac r hmin
    rcases hac with hac' | hca
    · cases r with
      | nil =>
        exact (ha ((P.isRelLowerSet_faces ht).2 hac'.le
          (J.isRelLowerSet_faces a.property).1)).elim
      | @cons c d t hcd r =>
        have hdc : d < c := by
          rcases hcd with hcd' | hdc
          · have h := hmin t ht (Walk.cons (Or.inl (hac'.trans hcd')) r)
            change r.length + 1 + 1 ≤ r.length + 1 at h
            omega
          · exact hdc
        change r.length + 1 + 1 ≤ 2 * D at hwlen
        exact finish hac'.le hdc r (by omega) hcmin
    · change r.length + 1 ≤ 2 * D at hwlen
      exact finish (Finset.Subset.refl _) hca r (by omega) hmin

end D5.S3.Topology.BarycentricGraphDistance
