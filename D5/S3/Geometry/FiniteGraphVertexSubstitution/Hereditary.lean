/- GID: D5/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGraphVertexSubstitution/Hereditary
   mirror-E: none(waiver:finite-graph-vertex-substitution)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Actual mixed graph stages and hereditary substitution induction retain all current fibers. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.FiniteGraphVertexSubstitution

noncomputable section
open Set Topology
open scoped BigOperators ContinuousMap

namespace D5.S3.Geometry.FiniteGraphVertexSubstitution

open FiniteConeCollapse FiniteSimplicialJoin FiniteConeUnionWedge
open private native_mem vertex univInduceIso from D5.S3.Geometry.FiniteGraphVertexSubstitution
universe u w

section Stages
variable {V : Type u} [Fintype V] [DecidableEq V] {D : V → Type w}
variable [∀ v, Fintype (D v)] [∀ v, DecidableEq (D v)]

/-- Mixed fibers: final fibers on the replaced set and singletons elsewhere. -/
def stageFiber (R : Finset V) (v : V) : Type w :=
  if v ∈ R then D v else PUnit

instance stageFiberFintype (R : Finset V) (v : V) : Fintype (stageFiber (D := D) R v) := by
  unfold stageFiber
  split_ifs <;> infer_instance

instance stageFiberDecidableEq (R : Finset V) (v : V) :
    DecidableEq (stageFiber (D := D) R v) := by
  unfold stageFiber
  split_ifs <;> infer_instance

instance stageFiberNonempty [∀ v, Nonempty (D v)] (R : Finset V) (v : V) :
    Nonempty (stageFiber (D := D) R v) := by
  unfold stageFiber
  split_ifs <;> infer_instance

/-- Actual mixed graphs, transported across the two branch equalities. -/
def stageGraphs (H : ∀ v, SimpleGraph (D v)) (R : Finset V) (v : V) :
    SimpleGraph (stageFiber (D := D) R v) := by
  by_cases h : v ∈ R
  · exact (H v).comap (cast (by simp only [stageFiber, if_pos h]))
  · exact (⊥ : SimpleGraph PUnit).comap (cast (by simp only [stageFiber, if_neg h]))

private def stageSelectedIso (H : ∀ v, SimpleGraph (D v)) (R : Finset V)
    (v : V) (h : v ∈ R) : stageGraphs H R v ≃g H v where
  toEquiv := Equiv.cast (by simp [stageFiber, h])
  map_rel_iff' := by intro a b; simp [stageGraphs, h, Equiv.cast]

private def stageSingletonIso (H : ∀ v, SimpleGraph (D v)) (R : Finset V)
    (v : V) (h : v ∉ R) : stageGraphs H R v ≃g (⊥ : SimpleGraph PUnit) where
  toEquiv := Equiv.cast (by simp [stageFiber, h])
  map_rel_iff' := by intro a b; simp [stageGraphs, h, Equiv.cast]

/-- The initial mixed stage is genuinely the base graph. -/
def initialStageIso (G : SimpleGraph V) (H : ∀ v, SimpleGraph (D v)) :
    substitution G (stageGraphs H ∅) ≃g G :=
  (substitutionFiberIso G _ _ (fun v => stageSingletonIso H ∅ v (by simp))).trans
    (singletonSubstitutionIso G)

/-- The final mixed stage is genuinely the original full substitution. -/
def finalStageIso (G : SimpleGraph V) (H : ∀ v, SimpleGraph (D v)) :
    substitution G (stageGraphs H Finset.univ) ≃g substitution G H :=
  substitutionFiberIso G _ _ (fun v => stageSelectedIso H Finset.univ v (by simp))

private def replacementAtIso (H : ∀ v, SimpleGraph (D v)) (R : Finset V) (v : V) :
    newGraphs (stageGraphs H R) v (H v) v ≃g H v where
  toEquiv := Equiv.cast (by simp [newFiber])
  map_rel_iff' := by intro a b; simp [newGraphs, Equiv.cast]

private def replacementAwayIso (H : ∀ v, SimpleGraph (D v)) (R : Finset V)
    (v z : V) (hz : z ≠ v) :
    newGraphs (stageGraphs H R) v (H v) z ≃g stageGraphs H R z where
  toEquiv := Equiv.cast (by simp [newFiber, hz])
  map_rel_iff' := by intro a b; simp [newGraphs, hz, Equiv.cast]

private def replacementStageFiberIso (H : ∀ v, SimpleGraph (D v))
    (R : Finset V) (v z : V) :
    newGraphs (stageGraphs H R) v (H v) z ≃g stageGraphs H (insert v R) z := by
  by_cases hz : z = v
  · subst z
    exact (replacementAtIso H R v).trans (stageSelectedIso H (insert v R) v (by simp)).symm
  · apply (replacementAwayIso H R v z hz).trans
    by_cases hr : z ∈ R
    · exact (stageSelectedIso H R z hr).trans
        (stageSelectedIso H (insert v R) z (by simp [hr])).symm
    · exact (stageSingletonIso H R z hr).trans
        (stageSingletonIso H (insert v R) z (by simp [hz, hr])).symm

/-- A single supplier replacement is the next actual mixed stage. -/
def replacementStageIso (G : SimpleGraph V) (H : ∀ v, SimpleGraph (D v))
    (R : Finset V) (v : V) :
    substitution G (newGraphs (stageGraphs H R) v (H v)) ≃g
      substitution G (stageGraphs H (insert v R)) :=
  substitutionFiberIso G _ _ (replacementStageFiberIso H R v)

end Stages


section HereditaryCore

private def pointIndependenceHomeomorph :
    Space (independenceComplex (⊥ : SimpleGraph PUnit.{u + 1})).toPreAbstractSimplicialComplex ≃ₜ
      PUnit.{u + 1} where
  toFun _ := PUnit.unit
  invFun _ := vertex _ PUnit.unit ((independenceComplex _).singleton_mem _)
  left_inv x := by
    apply Subtype.ext
    funext a
    cases a
    obtain ⟨s, hs, hx⟩ := (native_mem _ x.val).mp x.property
    have hx1 := hx.2.1
    simpa [vertex, Pi.single_apply] using hx1.symm
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

/-- Inference inputs for a class of actual spaces; none is asserted for W here. -/
private abbrev ClassHomotopyClosed
    (C : (X : Type u) → [TopologicalSpace X] → Prop) : Prop :=
  ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y],
    (X ≃ₕ Y) → C X → C Y

private abbrev ClassJoinClosed
    (C : (X : Type u) → [TopologicalSpace X] → Prop) : Prop :=
  ∀ {U X : Type u} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    (M : PreAbstractSimplicialComplex U) (N : PreAbstractSimplicialComplex X),
    Nonempty (Space M) → Nonempty (Space N) → C (Space M) → C (Space N) →
      C (OrdinaryJoin (Space M) (Space N))

private abbrev ClassVertexWedgeClosed
    (C : (X : Type u) → [TopologicalSpace X] → Prop) : Prop :=
  ∀ {U X : Type u} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    (M : PreAbstractSimplicialComplex U) (N : PreAbstractSimplicialComplex X)
    (a : Space M) (b : Space N),
    (∃ v, a.val = Pi.single v 1) → (∃ w, b.val = Pi.single w 1) →
    C (Space M) → C (Space N) → C (Wedge a b)

/-- Strong induction on the actual base cardinality, with an inner induction
on the replaced vertices. The right summand always retains all current fibers. -/
private theorem hereditarySubstitutionCore
    (C : (X : Type u) → [TopologicalSpace X] → Prop)
    (hom : ClassHomotopyClosed C) (point : C PUnit.{u + 1})
    (join : ClassJoinClosed C) (wedge : ClassVertexWedgeClosed C)
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {D : V → Type u} [∀ v, Fintype (D v)] [∀ v, DecidableEq (D v)]
    [∀ v, Nonempty (D v)] (G : SimpleGraph V) (H : ∀ v, SimpleGraph (D v))
    (hbase : ∀ S : Set V, S.Nonempty →
      C (Space (independenceComplex (G.induce S)).toPreAbstractSimplicialComplex))
    (hfiber : ∀ v, C (Space (independenceComplex (H v)).toPreAbstractSimplicialComplex)) :
    C (Space (independenceComplex (substitution G H)).toPreAbstractSimplicialComplex) := by
  classical
  generalize hn : Fintype.card V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    have hstageFiber (R : Finset V) (v : V) :
        C (Space (independenceComplex (stageGraphs H R v)).toPreAbstractSimplicialComplex) := by
      by_cases hv : v ∈ R
      · exact hom (graphIsoHomeomorph (stageSelectedIso H R v hv)).symm.toHomotopyEquiv
          (hfiber v)
      · exact hom (graphIsoHomeomorph (stageSingletonIso H R v hv)).symm.toHomotopyEquiv
          (hom pointIndependenceHomeomorph.symm.toHomotopyEquiv point)
    have hstage : ∀ R : Finset V,
        C (Space (independenceComplex
          (substitution G (stageGraphs H R))).toPreAbstractSimplicialComplex) := by
      intro R
      induction R using Finset.induction_on with
      | empty =>
        have hb := hbase Set.univ ⟨Classical.choice (inferInstance : Nonempty V), trivial⟩
        have hg := hom (graphIsoHomeomorph (univInduceIso G)).toHomotopyEquiv hb
        exact hom (graphIsoHomeomorph (initialStageIso G H)).symm.toHomotopyEquiv hg
      | @insert v R hv hr =>
        let e0 := stageSingletonIso H R v hv
        let d0 : stageFiber (D := D) R v := e0.symm PUnit.unit
        have hsingle : ∀ d : stageFiber (D := D) R v, d = d0 := by
          intro d
          exact e0.injective (Subsingleton.elim _ _)
        let l0 : D v := Classical.choice (inferInstance : Nonempty (D v))
        let M := linkComplex G (stageGraphs H R) v
        let N := (independenceComplex (H v)).toPreAbstractSimplicialComplex
        have hN : C (Space N) := hfiber v
        have hNne : Nonempty (Space N) :=
          ⟨vertex N l0 ((independenceComplex (H v)).singleton_mem l0)⟩
        have hright : C (Space (simplicialJoin M N)) := by
          by_cases hL : Nonempty (LinkBaseSet G v)
          · letI : Nonempty (LinkBaseSet G v) := hL
            have hlt : Fintype.card (LinkBaseSet G v) < n := by
              rw [← hn]
              apply Fintype.card_lt_of_injective_of_notMem
                (fun x : LinkBaseSet G v => x.val) Subtype.val_injective (b := v)
              rintro ⟨x, hx⟩
              exact x.property.1 hx
            have hb : ∀ S : Set (LinkBaseSet G v), S.Nonempty →
                C (Space (independenceComplex
                  ((G.induce (LinkBaseSet G v)).induce S)).toPreAbstractSimplicialComplex) := by
              intro S hs
              exact hom (graphIsoHomeomorph
                (nestedInduceIso G (LinkBaseSet G v) S)).symm.toHomotopyEquiv
                (hbase (Subtype.val '' S) (hs.image Subtype.val))
            have hM : C (Space M) := by
              exact ih (Fintype.card (LinkBaseSet G v)) hlt
                (G := G.induce (LinkBaseSet G v))
                (H := fun x : LinkBaseSet G v => stageGraphs H R x.val)
                hb (fun x => hstageFiber R x.val) rfl
            let x : LinkBaseSet G v := Classical.choice hL
            let d : stageFiber (D := D) R x.val := Classical.choice inferInstance
            have hMne : Nonempty (Space M) :=
              ⟨vertex M ⟨x, d⟩ ((independenceComplex _).singleton_mem _)⟩
            exact hom (FiniteSimplicialJoin.joinHomeomorph M N hMne hNne).toHomotopyEquiv
              (join M N hMne hNne hM hN)
          · have hempty : ∀ s, s ∉ M := by
              intro s hs
              obtain ⟨x, _⟩ := (M.isRelLowerSet_faces hs).1
              exact hL ⟨x.1⟩
            exact hom (emptyLeftJoinHomeomorph M N hempty).toHomotopyEquiv hN
        have hw := wedge
          (independenceComplex (substitution G (stageGraphs H R))).toPreAbstractSimplicialComplex
          (simplicialJoin M N) (oldPoint G (stageGraphs H R) v d0)
          (joinPoint G (stageGraphs H R) v (H v) l0)
          ⟨⟨v, d0⟩, rfl⟩ ⟨Sum.inr l0, rfl⟩ hr hright
        have hnew := hom
          (oneVertexReplacementEquiv G (stageGraphs H R) v (H v) d0 hsingle l0).symm hw
        exact hom (graphIsoHomeomorph (replacementStageIso G H R v)).toHomotopyEquiv hnew
    exact hom (graphIsoHomeomorph (finalStageIso G H)).toHomotopyEquiv (hstage Finset.univ)

#print axioms hereditarySubstitutionCore

end HereditaryCore

end D5.S3.Geometry.FiniteGraphVertexSubstitution
