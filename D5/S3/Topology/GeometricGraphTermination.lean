/- GID: D5/S3/Topology/GeometricGraphTermination
   generality: G
   mirror-B: D5/B/S3/Topology/GeometricGraphTermination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.MetricSpace.Pseudo.Lemmas]
   utility: none
   digest: A geometric nullhomotopy of a graph map gives fixed-target contiguity. -/

import D5.S3.Geometry.FiniteSimplicialJoin
import D5.S3.Geometry.FiniteVertexOpenStar
import D5.S3.Topology.GraphSubdivisionPositions
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Algebra.Monoid.FunOnFinite
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Fixed-target graph termination from a geometric nullhomotopy

The pullbacks of target vertex stars have a Lebesgue number on the compact
cylinder. Label each space-time mesh point by a star whose pullback contains
its ball. A point over any one vertex of a source face meets all the balls
from that face at two successive times.
-/

namespace D5.S3.Topology.GeometricGraphTermination

open D5.S3.Geometry
open FiniteConeCollapse (faceSimplex realization_mem_iff)
open FiniteSimplicialJoin (Space)
open BarycentricBaseRigidity (Contiguous faceImage)
open BarycentricGraphDistance (Face Vertex)
open BarycentricNeighborhoodIteration (iteratedAmbient subdivision)
open GraphSubdivisionIntervals (originalSupport originalSupport_mem)
open Relation (ReflTransGen)
open Set
open scoped BigOperators ContinuousMap unitInterval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {X Y Z : Type}

variable {A : PreAbstractSimplicialComplex X} {K : PreAbstractSimplicialComplex Y}
variable {P : PreAbstractSimplicialComplex Z}

private theorem singleton_of_mem {s : Finset Z} (hs : s ∈ P) {x : Z} (hx : x ∈ s) :
    ({x} : Finset Z) ∈ P :=
  (P.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hx)
    (Finset.singleton_nonempty _)

private theorem mem_faceImage_iff (f : Vertex P → Vertex K) {s : Finset Z} (hs : s ∈ P)
    {y : Y} : y ∈ faceImage f hs ↔ ∃ x : Vertex P, x.val ∈ s ∧ (f x).val = y := by
  classical
  unfold faceImage
  constructor
  · intro hy
    obtain ⟨x, _, he⟩ := Finset.mem_image.mp hy
    exact ⟨⟨x.val, singleton_of_mem hs x.property⟩, x.property, he⟩
  · rintro ⟨x, hx, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨x.val, hx⟩, Finset.mem_attach _ _, rfl⟩

private theorem contiguous_of_face_carriers {f g : Vertex P → Vertex K}
    (h : ∀ s : Finset Z, s ∈ P → ∃ t : Finset Y, t ∈ K ∧
      ∀ x : Vertex P, x.val ∈ s → (f x).val ∈ t ∧ (g x).val ∈ t) :
    Contiguous f g := by
  classical
  intro s hs
  obtain ⟨t, ht, hc⟩ := h s hs
  have hf : faceImage f hs ⊆ t := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_faceImage_iff f hs).mp hy
    exact (hc x hx).1
  have hg : faceImage g hs ⊆ t := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_faceImage_iff g hs).mp hy
    exact (hc x hx).2
  obtain ⟨a, ha⟩ := (P.isRelLowerSet_faces hs).1
  let x : Vertex P := ⟨a, singleton_of_mem hs ha⟩
  have hne : (faceImage f hs).Nonempty :=
    ⟨(f x).val, (mem_faceImage_iff f hs).mpr ⟨x, ha, rfl⟩⟩
  exact (K.isRelLowerSet_faces ht).2 (Finset.union_subset hf hg)
    (hne.mono Finset.subset_union_left)

section Cylinder

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

private theorem face_contains_positive_coordinates (q : Space K) :
    ∃ s : Finset Y, s ∈ K ∧ ∀ y, 0 < q.val y → y ∈ s := by
  obtain ⟨s, hs, hq⟩ := (realization_mem_iff K q.val).mp q.property
  refine ⟨s, hs, fun y hy => ?_⟩
  by_contra hn
  exact (ne_of_gt hy) (hq.2.2 y hn)

private theorem exists_vertex_in_star (q : Space K) :
    ∃ v : Vertex K, q ∈ FiniteVertexOpenStar.star K v.val := by
  obtain ⟨s, hs, hq⟩ := (realization_mem_iff K q.val).mp q.property
  have hpos : ∃ y, 0 < q.val y := by
    by_contra h
    have hb : (∑ y, q.val y) ≤ 0 :=
      Finset.sum_nonpos fun y _ => le_of_not_gt (fun hy => h ⟨y, hy⟩)
    linarith [hq.2.1]
  obtain ⟨y, hy⟩ := hpos
  have hys : y ∈ s := by
    by_contra hn
    exact (ne_of_gt hy) (hq.2.2 y hn)
  exact ⟨⟨y, singleton_of_mem hs hys⟩, hy⟩

/-- One positive radius works at every point of the homotopy cylinder. -/
theorem cylinder_star_radius (H : C(I × Space A, Space K)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ label : I × Space A → Vertex K,
      ∀ z w, dist w z < δ → H w ∈ FiniteVertexOpenStar.star K (label z).val := by
  classical
  letI : CompactSpace (Space A) := FiniteSimplicialJoin.realizationCompactSpace A
  let cover (v : Vertex K) : Set (I × Space A) :=
    H ⁻¹' FiniteVertexOpenStar.star K v.val
  have hopen (v : Vertex K) : IsOpen (cover v) :=
    (FiniteVertexOpenStar.isOpen_star K v.val).preimage H.continuous
  have hcover : (Set.univ : Set (I × Space A)) ⊆ ⋃ v : Vertex K, cover v := by
    intro z _
    obtain ⟨v, hv⟩ := exists_vertex_in_star (H z)
    exact Set.mem_iUnion.mpr ⟨v, hv⟩
  obtain ⟨δ, hδ, hr⟩ := lebesgue_number_lemma_of_metric isCompact_univ hopen hcover
  have hball (z : I × Space A) : ∃ v, Metric.ball z δ ⊆ cover v := hr z (Set.mem_univ z)
  exact ⟨δ, hδ, fun z => (hball z).choose,
    fun z w hw => (hball z).choose_spec (Metric.mem_ball.mpr hw)⟩

private def meshTime (n j : ℕ) : I := by
  refine ⟨(↑(min j (n + 1)) : ℝ) / ((n : ℝ) + 1), ?_, ?_⟩
  · positivity
  · apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
    simpa only [one_mul, Nat.cast_add, Nat.cast_one] using
      (show (↑(min j (n + 1)) : ℝ) ≤ ↑(n + 1) by exact_mod_cast min_le_right j (n + 1))

private theorem meshTime_zero (n : ℕ) : meshTime n 0 = 0 := by
  apply Subtype.ext
  change (↑(min 0 (n + 1)) : ℝ) / ((n : ℝ) + 1) = 0
  simp

private theorem meshTime_last (n : ℕ) : meshTime n (n + 1) = 1 := by
  apply Subtype.ext
  change (↑(min (n + 1) (n + 1)) : ℝ) / ((n : ℝ) + 1) = 1
  rw [min_self, Nat.cast_add, Nat.cast_one, div_self (by positivity : (n : ℝ) + 1 ≠ 0)]

private theorem dist_meshTime_succ (n j : ℕ) (hj : j < n + 1) :
    dist (meshTime n j) (meshTime n (j + 1)) = 1 / ((n : ℝ) + 1) := by
  have hj' : j + 1 ≤ n + 1 := Nat.succ_le_of_lt hj
  rw [Subtype.dist_eq, Real.dist_eq]
  change |(↑(min j (n + 1)) : ℝ) / ((n : ℝ) + 1) -
    (↑(min (j + 1) (n + 1)) : ℝ) / ((n : ℝ) + 1)| = _
  rw [min_eq_left hj.le, min_eq_left hj', Nat.cast_add, Nat.cast_one, ← sub_div]
  rw [show (j : ℝ) - ((j : ℝ) + 1) = -1 by ring, abs_div, abs_neg, abs_one,
    abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]

/-- Label the vertices of a positioned complex along a time mesh. The ball
condition can be supplied by `cylinder_star_radius`. The carrier of each
bottom label is prescribed by the positive coordinates at time zero. -/
theorem contiguous_labels_of_small_faces (H : C(I × Space A, Space K))
    {δ : ℝ} (hδ : 0 < δ) (label : I × Space A → Vertex K)
    (hlabel : ∀ z w, dist w z < δ → H w ∈ FiniteVertexOpenStar.star K (label z).val)
    (position : Vertex P → Space A)
    (hsmall : ∀ (s : Finset Z), s ∈ P → ∀ x y : Vertex P,
      x.val ∈ s → y.val ∈ s → dist (position x) (position y) < δ)
    (bottom : Vertex P → Finset Y)
    (hbottom : ∀ x y, 0 < (H (0, position x)).val y → y ∈ bottom x)
    (base : Vertex K)
    (htop : ∀ p, H (1, p) = FiniteVertexCylinder.vertexPoint K base.val base.property) :
    ∃ N : ℕ, ∃ row : ℕ → Vertex P → Vertex K,
      (∀ x, (row 0 x).val ∈ bottom x) ∧
      row N = (fun _ => base) ∧
      ∀ j < N, Contiguous (row j) (row (j + 1)) := by
  classical
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  let row (j : ℕ) (x : Vertex P) := label (meshTime n j, position x)
  have hat (j : ℕ) (x : Vertex P) :
      0 < (H (meshTime n j, position x)).val (row j x).val :=
    hlabel _ _ (by rw [dist_self]; exact hδ)
  refine ⟨n + 1, row, ?_, ?_, ?_⟩
  · intro x
    apply hbottom x
    simpa only [meshTime_zero] using hat 0 x
  · funext x
    have hpos := hat (n + 1) x
    rw [meshTime_last, htop] at hpos
    apply Subtype.ext
    by_contra hne
    simpa [FiniteVertexCylinder.vertexPoint, Pi.single_apply, hne, Ne.symm hne] using hpos
  · intro j hj
    apply contiguous_of_face_carriers
    intro s hs
    obtain ⟨a, ha⟩ := (P.isRelLowerSet_faces hs).1
    let x : Vertex P := ⟨a, singleton_of_mem hs ha⟩
    let sample : I × Space A := (meshTime n j, position x)
    obtain ⟨t, ht, hpos⟩ := face_contains_positive_coordinates (H sample)
    refine ⟨t, ht, fun y hy =>
      ⟨hpos _ (hlabel (meshTime n j, position y) sample ?_),
       hpos _ (hlabel (meshTime n (j + 1), position y) sample ?_)⟩⟩
    · change dist sample (meshTime n j, position y) < δ
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by simpa [sample] using hδ, hsmall s hs x y ha hy⟩
    · change dist sample (meshTime n (j + 1), position y) < δ
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨(dist_meshTime_succ n j hj).trans_lt hn, hsmall s hs x y ha hy⟩

end Cylinder

private theorem originalSupport_mono (A : PreAbstractSimplicialComplex X) (m : ℕ) :
    ∀ {s t : Finset (iteratedAmbient A m).1}, s ⊆ t →
      originalSupport A m s ⊆ originalSupport A m t := by
  classical
  induction m with
  | zero =>
    intro s t h
    exact h
  | succ m ih =>
    intro s t h
    exact ih (Finset.biUnion_subset_biUnion_of_subset_left Subtype.val h)



section Termination

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

private theorem contiguous_of_original_support {m : ℕ} {f : Vertex A → Vertex K}
    (hf : ∀ (s : Finset X) (hs : s ∈ A), faceImage f hs ∈ K)
    {g g' : Vertex (iteratedAmbient A m).2 → Vertex K}
    (hg : ∀ x, (g x).val ∈ faceImage f (originalSupport_mem m x.property))
    (hg' : ∀ x, (g' x).val ∈ faceImage f (originalSupport_mem m x.property)) :
    Contiguous g g' := by
  apply contiguous_of_face_carriers
  intro s hs
  let ht := originalSupport_mem m hs
  refine ⟨faceImage f ht, hf _ ht, ?_⟩
  intro x hx
  have hsub := originalSupport_mono A m (Finset.singleton_subset_iff.mpr hx)
  constructor
  · obtain ⟨a, ha, he⟩ := (mem_faceImage_iff f _).mp (hg x)
    exact (mem_faceImage_iff f ht).mpr ⟨a, hsub ha, he⟩
  · obtain ⟨a, ha, he⟩ := (mem_faceImage_iff f _).mp (hg' x)
    exact (mem_faceImage_iff f ht).mpr ⟨a, hsub ha, he⟩

open scoped Classical in
private theorem oriented_edges :
    ∃ left right : {e : Face A // e.val.val.card = 2} → Vertex A,
      ∀ e, e.val.val = {(left e).val, (right e).val} ∧ left e ≠ right e := by
  classical
  have pair (e : {e : Face A // e.val.val.card = 2}) :
      ∃ x y : Vertex A, e.val.val = {x.val, y.val} ∧ x ≠ y := by
    obtain ⟨a, b, hn, hab⟩ := Finset.card_eq_two.mp e.property
    let x : Vertex A := ⟨a, singleton_of_mem e.val.property
      (hab.symm ▸ Finset.mem_insert_self a {b})⟩
    let y : Vertex A := ⟨b, singleton_of_mem e.val.property
      (hab.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b))⟩
    exact ⟨x, y, hab, fun h => hn (congrArg Subtype.val h)⟩
  choose left right h using pair
  exact ⟨left, right, h⟩

/-- A supported geometric nullhomotopy to a realized vertex gives a uniform
fixed-target contiguity contraction for all sufficiently fine subdivisions. -/
theorem supported_graph_map_contracts_of_vertex_homotopy
    (hdim : ∀ s ∈ A, (s : Finset X).card ≤ 2)
    (f : Vertex A → Vertex K) (hf : ∀ (s : Finset X) (hs : s ∈ A), faceImage f hs ∈ K)
    (H : C(I × Space A, Space K))
    (hbottom : ∀ (s : Finset X) (hs : s ∈ A) (p : Space A),
      p.val ∈ faceSimplex s → ∀ y, 0 < (H (0, p)).val y → y ∈ faceImage f hs)
    (base : Vertex K)
    (htop : ∀ p, H (1, p) = FiniteVertexCylinder.vertexPoint K base.val base.property) :
    ∃ d : ℕ, ∀ m, d ≤ m →
      ∀ select : Vertex (iteratedAmbient A m).2 → Vertex A,
        (∀ x, (select x).val ∈ originalSupport A m {x.val}) →
        ReflTransGen Contiguous (f ∘ select) (fun _ => base) := by
  obtain ⟨δ, hδ, label, hlabel⟩ := cylinder_star_radius H
  obtain ⟨d, hd⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨d, ?_⟩
  intro m hm select hselect
  have hpow : (1 / 2 : ℝ) ^ m < δ :=
    (pow_le_pow_of_le_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hm).trans_lt hd
  obtain ⟨left, right, horient⟩ := oriented_edges (A := A)
  obtain ⟨position, hsupport, hmesh⟩ := GraphSubdivisionPositions.exists_positions A hdim m
    left right horient
  have hsmall (s : Finset (iteratedAmbient A m).1) (hs : s ∈ (iteratedAmbient A m).2)
      (x y : Vertex (iteratedAmbient A m).2) (hx : x.val ∈ s) (hy : y.val ∈ s) :
      dist (position x) (position y) < δ := by
    change dist (position x).val (position y).val < δ
    apply (dist_pi_lt_iff hδ).2
    intro w
    rw [Real.dist_eq]
    rw [div_pow, one_pow] at hpow
    exact (hmesh s hs x y hx hy w).trans_lt hpow
  let bottom (x : Vertex (iteratedAmbient A m).2) :=
    faceImage f (originalSupport_mem m x.property)
  obtain ⟨N, row, hfirst, hlast, hstep⟩ :=
    contiguous_labels_of_small_faces H hδ label hlabel position hsmall bottom
      (fun x y hy => by
        obtain ⟨s, hs, hp⟩ := (realization_mem_iff A _).mp (position x).property
        exact hbottom _ (originalSupport_mem m x.property) _ ⟨hp.1, hp.2.1, hsupport x⟩ y hy)
      base htop
  have hinit : Contiguous (f ∘ select) (row 0) := by
    apply contiguous_of_original_support hf _ hfirst
    intro x
    exact (mem_faceImage_iff f _).mpr ⟨select x, hselect x, rfl⟩
  have hchain (j : ℕ) (hj : j ≤ N) : ReflTransGen Contiguous (row 0) (row j) := by
    induction j with
    | zero => exact .refl
    | succ j ih =>
      exact (ih (by omega)).tail (hstep j (by omega))
  exact (ReflTransGen.single hinit).trans (hlast ▸ hchain N le_rfl)

private def extendVertexMap (fallback : Vertex K) (f : Vertex A → Vertex K) (x : X) : Y := by
  classical
  exact if hx : ({x} : Finset X) ∈ A then (f ⟨x, hx⟩).val else fallback.val

private theorem linearMap_mem_faceImage
    (fallback : Vertex K) (f : Vertex A → Vertex K)
    {s : Finset X} (hs : s ∈ A) {p : X → ℝ} (hp : p ∈ faceSimplex s) :
    FunOnFinite.linearMap ℝ ℝ (extendVertexMap fallback f) p ∈ faceSimplex (faceImage f hs) := by
  classical
  let g := extendVertexMap fallback f
  have he (y : Y) : FunOnFinite.linearMap ℝ ℝ g p y = ∑ x with g x = y, p x :=
    FunOnFinite.linearMap_apply_apply ℝ ℝ g p y
  refine ⟨fun y => ?_, ?_, fun y hy => ?_⟩
  · rw [he]
    exact Finset.sum_nonneg fun x _ => hp.1 x
  · change (∑ y : Y, FunOnFinite.linearMap ℝ ℝ g p y) = 1
    exact (Finset.sum_congr rfl (fun y _ => he y)).trans
      ((Finset.sum_fiberwise Finset.univ g p).trans hp.2.1)
  · rw [he]
    apply Finset.sum_eq_zero
    intro x hx
    apply hp.2.2 x
    intro hxs
    let v : Vertex A := ⟨x, singleton_of_mem hs hxs⟩
    have hv : g x = (f v).val := dif_pos v.property
    exact hy ((mem_faceImage_iff f hs).mpr ⟨v, hxs,
      hv.symm.trans (Finset.mem_filter.mp hx).2⟩)

/-- The affine realization of a simplicial vertex map. Coordinates on unused
source labels vanish, so their extension by the fallback does not contribute. -/
def realizedVertexMap (fallback : Vertex K) (f : Vertex A → Vertex K)
    (hf : ∀ (s : Finset X) (hs : s ∈ A), faceImage f hs ∈ K) : C(Space A, Space K) where
  toFun p := ⟨FunOnFinite.linearMap ℝ ℝ (extendVertexMap fallback f) p.val, by
    obtain ⟨s, hs, hp⟩ := (realization_mem_iff A _).mp p.property
    exact (realization_mem_iff K _).mpr
      ⟨_, hf s hs, linearMap_mem_faceImage fallback f hs hp⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (FunOnFinite.continuous_linearMap ℝ ℝ (extendVertexMap fallback f)).comp
      continuous_subtype_val

/-- A homotopy to any constant of the target realization gives a common
vertex constant for every supported vertex selection at sufficiently fine depth. -/
theorem supported_graph_map_contracts_of_homotopy
    (hdim : ∀ s ∈ A, (s : Finset X).card ≤ 2)
    (f : Vertex A → Vertex K) (hf : ∀ (s : Finset X) (hs : s ∈ A), faceImage f hs ∈ K)
    (F : C(Space A, Space K))
    (hF : ∀ (s : Finset X) (hs : s ∈ A) (p : Space A),
      p.val ∈ faceSimplex s → (F p).val ∈ faceSimplex (faceImage f hs))
    (q : Space K) (H : F.Homotopy (ContinuousMap.const (Space A) q)) :
    ∃ (base : Vertex K) (d : ℕ), ∀ m, d ≤ m →
      ∀ select : Vertex (iteratedAmbient A m).2 → Vertex A,
        (∀ x, (select x).val ∈ originalSupport A m {x.val}) →
        ReflTransGen Contiguous (f ∘ select) (fun _ => base) := by
  obtain ⟨base, hq⟩ := exists_vertex_in_star q
  let contraction := FiniteVertexOpenStar.contraction K base.val base.property
  let extension : (ContinuousMap.const (Space A) q).Homotopy
      (ContinuousMap.const (Space A) (FiniteVertexCylinder.vertexPoint K base.val base.property)) :=
    { toFun := fun z => (contraction (z.1, ⟨q, hq⟩)).val
      continuous_toFun := continuous_subtype_val.comp (contraction.continuous.comp
        (continuous_fst.prodMk continuous_const))
      map_zero_left := fun _ => congrArg Subtype.val (contraction.toHomotopy.apply_zero ⟨q, hq⟩)
      map_one_left := fun _ => congrArg Subtype.val (contraction.toHomotopy.apply_one ⟨q, hq⟩) }
  let extended := H.trans extension
  refine ⟨base, supported_graph_map_contracts_of_vertex_homotopy hdim f hf
    extended.toContinuousMap ?_ base extended.apply_one⟩
  intro s hs p hp y hy
  change 0 < (extended (0, p)).val y at hy
  rw [extended.apply_zero] at hy
  by_contra hn
  exact (ne_of_gt hy) ((hF s hs p hp).2.2 y hn)

/-- Fixed-target termination for the affine realization of a simplicial
graph map. The conclusion is uniform in the original-support selection. -/
theorem realized_graph_map_contracts
    (hdim : ∀ s ∈ A, (s : Finset X).card ≤ 2)
    (fallback : Vertex K) (f : Vertex A → Vertex K)
    (hf : ∀ (s : Finset X) (hs : s ∈ A), faceImage f hs ∈ K)
    (q : Space K)
    (H : (realizedVertexMap fallback f hf).Homotopy (ContinuousMap.const (Space A) q)) :
    ∃ (base : Vertex K) (d : ℕ), ∀ m, d ≤ m →
      ∀ select : Vertex (iteratedAmbient A m).2 → Vertex A,
        (∀ x, (select x).val ∈ originalSupport A m {x.val}) →
        ReflTransGen Contiguous (f ∘ select) (fun _ => base) :=
  supported_graph_map_contracts_of_homotopy hdim f hf (realizedVertexMap fallback f hf)
    (fun _ hs _ hp => linearMap_mem_faceImage fallback f hs hp) q H

end Termination

end

end D5.S3.Topology.GeometricGraphTermination
