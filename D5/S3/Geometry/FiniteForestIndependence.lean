/- GID: D5/S3/Geometry/FiniteForestIndependence
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteForestIndependence
   mirror-E: none(waiver:native-forest-classification)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Native finite-forest independence realizations are contractible or spheres. -/
import D5.S3.Geometry.FiniteGraphIndependenceReduction
import D5.S3.Geometry.FiniteComponentClosure.Transport
import D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError

/-!
# Independence realizations of finite forests

A leaf fold leaves the induced graph outside its neighbor's closed neighborhood
and one disjoint edge. The native realization is therefore its augmented join
with the two-point complex. Strict cardinal induction includes disconnected
forests, empty residuals, and the zero-sphere.

The classification is classical: Ehrenborg--Hetyei, The topology of the
independence complex, Corollary 6.1, DOI 10.1016/j.ejc.2005.04.010.
-/

noncomputable section
open Set Topology ContinuousMap
open scoped BigOperators unitInterval

namespace D5.S3.Geometry.FiniteForestIndependence

open FiniteCoordinateTruncation FiniteGraphIndependenceReduction
open FiniteGraphVertexSubstitution FiniteSimplicialJoin FiniteComponentClosure
open private disjointGraph restricted_join
  from D5.S3.Geometry.FiniteGraphVertexSubstitution
open private joinCongr pointJoinContraction twoPoint
  from D5.S3.Geometry.FiniteComponentClosure.Transport
open FiniteConeCollapse.ConePair (cone_segment)

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Vertices outside the closed neighborhood of the leaf's neighbor. -/
def residualSet (G : SimpleGraph V) (v : V) : Set V :=
  {x | ¬ G.Adj v x ∧ x ≠ v}

/-- All neighbors of v except the chosen leaf u. -/
def deleted (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun d => G.Adj v d ∧ d ≠ u

private theorem survivor (G : SimpleGraph V) (u v : V) : u ∉ deleted G u v := by
  classical
  simp [deleted]

private theorem domination (G : SimpleGraph V) (u v : V)
    (hleaf : ∀ w, G.Adj u w → w = v) :
    ∀ d ∈ deleted G u v, G.neighborSet u ⊆ G.neighborSet d := by
  classical
  intro d hd w hw
  have hdv : G.Adj v d := (Finset.mem_filter.mp hd).2.1
  have : w = v := hleaf w hw
  subst w
  exact hdv.symm

/-- Concrete retained labels: residual vertices on the left, u and v on the right. -/
def leafLabelsEquiv (G : SimpleGraph V) (u v : V) (huv : G.Adj u v) :
    Retained (deleted G u v) ≃ (residualSet G v ⊕ Bool) := by
  classical
  have hru : u ∉ residualSet G v := fun h => h.1 huv.symm
  have hrv : v ∉ residualSet G v := fun h => h.2 rfl
  refine {
    toFun := fun x => if hu : x.val = u then Sum.inr true else
      if hv : x.val = v then Sum.inr false else
        Sum.inl ⟨x.val, ?_⟩
    invFun := Sum.elim (fun r => ⟨r.val, ?_⟩)
      (fun b => if b then ⟨u, survivor G u v⟩ else ⟨v, ?_⟩)
    left_inv := ?_
    right_inv := ?_ }
  · refine ⟨?_, hv⟩
    intro h
    exact x.property (by simp [deleted, h, hu])
  · simp only [deleted, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    exact fun h => (r.property.1 h).elim
  · simp [deleted]
  · intro x
    by_cases hu : x.val = u
    · apply Subtype.ext
      simp [hu]
    · by_cases hv : x.val = v
      · apply Subtype.ext
        simp [hv, huv.ne.symm]
      · simp [hu, hv]
  · rintro (r | b)
    · have hu : r.val ≠ u := fun h => hru (h ▸ r.property)
      have hv : r.val ≠ v := r.property.2
      simp [hu, hv]
    · cases b <;> simp [huv.ne.symm]

/-- The retained graph is the actual induced residual disjoint from K2. -/
def leafGraphIso (G : SimpleGraph V) (u v : V) (huv : G.Adj u v)
    (hleaf : ∀ w, G.Adj u w → w = v) :
    disjointGraph (G.induce (residualSet G v)) (⊤ : SimpleGraph Bool) ≃g
      G.induce {b | b ∉ deleted G u v} where
  toEquiv := (leafLabelsEquiv G u v huv).symm
  map_rel_iff' := by
    have hru (r : residualSet G v) : ¬ G.Adj u r.val :=
      fun h => r.property.2 (hleaf r.val h)
    have hrv (r : residualSet G v) : ¬ G.Adj v r.val := r.property.1
    rintro (a | a) (b | b)
    · rfl
    · cases b
      · change G.Adj a.val v ↔ False
        simp [show ¬ G.Adj a.val v from fun h => hrv a h.symm]
      · change G.Adj a.val u ↔ False
        simp [show ¬ G.Adj a.val u from fun h => hru a h.symm]
    · cases a
      · change G.Adj v b.val ↔ False
        simp [hrv]
      · change G.Adj u b.val ↔ False
        simp [hru]
    · cases a <;> cases b <;>
        simp [leafLabelsEquiv, disjointGraph, huv, huv.symm]

omit [Fintype V] in
private theorem disjoint_complex {W : Type*} [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    (independenceComplex (disjointGraph G H)).toPreAbstractSimplicialComplex =
      simplicialJoin (independenceComplex G).toPreAbstractSimplicialComplex
        (independenceComplex H).toPreAbstractSimplicialComplex := by
  have hp : Sum.elim (fun _ : V => True) (fun _ : W => True) =
      (fun _ : V ⊕ W => True) := by funext x; cases x <;> rfl
  simpa only [hp, unrestricted] using
    (restricted_join G H (fun _ => True) (fun _ => True)).symm

private theorem edge_complex :
    (independenceComplex (⊤ : SimpleGraph Bool)).toPreAbstractSimplicialComplex =
      twoPoints := by
  ext s
  change (s.Nonempty ∧ (⊤ : SimpleGraph Bool).IsIndepSet (s : Set Bool)) ↔ s.card = 1
  constructor
  · rintro ⟨hn, hi⟩
    obtain ⟨a, ha⟩ := hn
    have he : s = {a} := by
      ext b
      simp only [Finset.mem_singleton]
      exact ⟨fun hb => by_contra fun h => hi hb ha h (by simpa using h),
        fun h => h.symm ▸ ha⟩
    simp [he]
  · intro h
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact (independenceComplex (⊤ : SimpleGraph Bool)).singleton_mem a

open Classical in
/-- Native leaf reduction, including an empty residual, into the augmented join. -/
def leafEquiv (G : SimpleGraph V) (u v : V) (huv : G.Adj u v)
    (hleaf : ∀ w, G.Adj u w → w = v) :
    Ispace G ≃ₕ Space (simplicialJoin
      (independenceComplex (G.induce (residualSet G v))).toPreAbstractSimplicialComplex
      twoPoints) :=
  ((foldEquiv G u (deleted G u v) (survivor G u v) (domination G u v hleaf)).trans
    (graphIsoHomeomorph (leafGraphIso G u v huv hleaf).symm).toHomotopyEquiv).trans
    (Homeomorph.setCongr (congrArg FiniteConeCollapse.realization
      ((disjoint_complex _ _).trans (congrArg (simplicialJoin _) edge_complex)))).toHomotopyEquiv

private def isolatedCone (G : SimpleGraph V) (u : V) (hu : ∀ w, ¬ G.Adj u w) :
    FiniteConeCollapse.ConePair V where
  ambient := (independenceComplex G).toPreAbstractSimplicialComplex
  cone := (independenceComplex G).toPreAbstractSimplicialComplex
  inclusion := le_rfl
  apex := u
  apex_face := (independenceComplex G).singleton_mem u
  cone_face := by
    rintro s ⟨_, hs⟩
    refine ⟨Finset.insert_nonempty _ _, ?_⟩
    intro a ha b hb hab hadj
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hu b hadj
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hu a hadj.symm
      · exact hs ha hb hab hadj

/-- An actual isolated vertex contracts the entire native realization to its apex. -/
theorem isolated_contractible (G : SimpleGraph V) (u : V) (hu : ∀ w, ¬ G.Adj u w) :
    ContractibleSpace (Ispace G) := by
  let P := isolatedCone G u hu
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨P.apexPoint, ⟨straight _ _ ?_⟩⟩
  intro t x
  exact cone_segment P x x.property t t.property.1 t.property.2

omit [Fintype V] [DecidableEq V] in
private theorem empty_faces (G : SimpleGraph V) [IsEmpty V] :
    ∀ s, s ∉ (independenceComplex G).toPreAbstractSimplicialComplex := by
  rintro s ⟨hn, _⟩
  obtain ⟨a, _⟩ := hn
  exact isEmptyElim a

private theorem join_contractible {W : Type*} [TopologicalSpace W]
    [ContractibleSpace W] (y : Space twoPoints) :
    ContractibleSpace (OrdinaryJoin W (Space twoPoints)) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit W
  let d := joinCongr e (HomotopyEquiv.refl (Space twoPoints))
  let : ContractibleSpace (OrdinaryJoin Unit (Space twoPoints)) :=
    (contractible_iff_id_nullhomotopic _).mpr
      ⟨Quotient.mk _ ((), y, (0 : I)), ⟨pointJoinContraction () y⟩⟩
  exact d.contractibleSpace

/-- Every finite forest has empty labels, a contractible native independence
realization, or the homotopy type of a standard sphere of natural dimension. -/
theorem classification (G : SimpleGraph V) (hG : G.IsAcyclic) :
    IsEmpty V ∨ ContractibleSpace (Ispace G) ∨
      ∃ n : ℕ, Nonempty (Ispace G ≃ₕ EuclideanSphereJoin.StdSphere n) := by
  classical
  suffices hall : ∀ n, ∀ (W : Type u) [Fintype W] [DecidableEq W],
      Fintype.card W = n → ∀ (F : SimpleGraph W), F.IsAcyclic →
        IsEmpty W ∨ ContractibleSpace (Ispace F) ∨
          ∃ d : ℕ, Nonempty (Ispace F ≃ₕ EuclideanSphereJoin.StdSphere d) from
    hall (Fintype.card V) V rfl G hG
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ hn F hF
    rcases isEmpty_or_nonempty W with he | hne
    · exact Or.inl he
    let := hne
    have hleaf :=
      D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError.forest_not_two_neighbors F hF
    push Not at hleaf
    obtain ⟨u, hu⟩ := hleaf
    by_cases hi : ∀ w, ¬ F.Adj u w
    · exact Or.inr (Or.inl (isolated_contractible F u hi))
    push Not at hi
    obtain ⟨v, huv⟩ := hi
    have huv' : ∀ w, F.Adj u w → w = v := fun w hw => hu w v hw huv
    let R := residualSet F v
    let K := (independenceComplex (F.induce R)).toPreAbstractSimplicialComplex
    let e := leafEquiv F u v huv huv'
    have hlt : Fintype.card R < Fintype.card W :=
      Fintype.card_subtype_lt (x := v) (fun h => h.2 rfl)
    have hr := ih (Fintype.card R) (by omega) R rfl (F.induce R) (hF.induce R)
    right
    rcases hr with he | hc | ⟨d, ⟨hd⟩⟩
    · let := he
      right
      exact ⟨0, ⟨e.trans ((emptyLeftJoinHomeomorph K twoPoints
        (empty_faces (F.induce R))).symm.trans twoPointSphereHomeomorph).toHomotopyEquiv⟩⟩
    · let := hc
      obtain ⟨c⟩ := ContractibleSpace.hequiv_unit (Ispace (F.induce R))
      let : Nonempty (Ispace (F.induce R)) := ⟨c.invFun ()⟩
      let j := FiniteSimplicialJoin.joinHomeomorph K twoPoints
        inferInstance ⟨twoPoint true⟩
      letI := join_contractible (W := Ispace (F.induce R)) (twoPoint true)
      left
      exact (e.trans j.symm.toHomotopyEquiv).contractibleSpace
    · let : Nonempty (Ispace (F.induce R)) := ⟨hd.invFun (EuclideanSphereJoin.coordinatePoint d)⟩
      let j := FiniteSimplicialJoin.joinHomeomorph K twoPoints
        inferInstance ⟨twoPoint true⟩
      right
      exact ⟨d + 0 + 1, ⟨((e.trans j.symm.toHomotopyEquiv).trans
        (joinCongr hd twoPointSphereHomeomorph.toHomotopyEquiv)).trans
        (EuclideanSphereJoin.sphereJoinHomeomorph d 0).toHomotopyEquiv⟩⟩

end D5.S3.Geometry.FiniteForestIndependence
