/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Number rectangular edge fibers for the actual outgoing split. -/

/- Rectangular endpoint fibers retain empty fibers and every parallel edge. The numbered positive future recoding agrees with the actual outgoing lift. -/
import D5.S3.ConceptDynamics.Coding.TwoSidedFiniteInduction
import Mathlib.Logic.Equiv.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.OutSplitNumberedRecoding

open EssentialWordRealization
open CountedMatrixOverlap

namespace Rect
variable {I J A : Type*} {n m : ℕ}
variable [Fintype A]
variable (iv : I ≃ Fin n) (jv : J ≃ Fin m) (s : A → I) (t : A → J)

def endpoints (a : A) : Fin n × Fin m := (iv (s a),jv (t a))
abbrev Fibre (i : Fin n) (j : Fin m) := {a : A // endpoints iv jv s t a = (i,j)}
instance (i : Fin n) (j : Fin m) : Fintype (Fibre iv jv s t i j) := by
  classical
  infer_instance

def matrix : CountMat n m := fun i j => Fintype.card (Fibre iv jv s t i j)

private def edgeSigma : Edge (matrix iv jv s t) ≃
    (Σ z : Fin n × Fin m, Fin (matrix iv jv s t z.1 z.2)) where
  toFun e := ⟨(e.source,e.target),e.number⟩
  invFun a := ⟨a.1.1,a.1.2,a.2⟩
  left_inv e := by cases e; rfl
  right_inv a := by rcases a with ⟨⟨i,j⟩,k⟩; rfl

def decode : Edge (matrix iv jv s t) ≃ A :=
  (edgeSigma iv jv s t).trans
    ((Equiv.sigmaCongrRight fun z : Fin n × Fin m => (Fintype.equivFin (Fibre iv jv s t z.1 z.2)).symm).trans
      (Equiv.sigmaFiberEquiv (endpoints iv jv s t)))

theorem decode_endpoints (e : Edge (matrix iv jv s t)) :
    iv (s (decode iv jv s t e)) = e.source ∧
    jv (t (decode iv jv s t e)) = e.target := by
  have h := ((Fintype.equivFin (Fibre iv jv s t e.source e.target)).symm e.number).property
  exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩

theorem encode_endpoints (a : A) :
    ((decode iv jv s t).symm a).source = iv (s a) ∧
    ((decode iv jv s t).symm a).target = jv (t a) := by
  have h := decode_endpoints iv jv s t ((decode iv jv s t).symm a)
  rw [(decode iv jv s t).apply_symm_apply] at h
  exact ⟨h.1.symm,h.2.symm⟩

end Rect

variable {V E L : Type*} [Fintype V] [Fintype E] [Fintype L]
variable [DecidableEq V] [DecidableEq L]
variable (G : DirectedMultigraph V E) (p : E → L)

def oldNumber : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
def newNumber : ActualOutSplit.Vertex G p ≃ Fin (Fintype.card (ActualOutSplit.Vertex G p)) := Fintype.equivFin _

/-- R half-edges are the retained partition classes themselves. -/
abbrev R : CountMat (Fintype.card V) (Fintype.card (ActualOutSplit.Vertex G p)) :=
  Rect.matrix (oldNumber (V := V)) (newNumber G p)
    (fun u : ActualOutSplit.Vertex G p => u.val.1) id

/-- S half-edges are original edges, including every parallel identity. -/
abbrev S : CountMat (Fintype.card (ActualOutSplit.Vertex G p)) (Fintype.card V) :=
  Rect.matrix (newNumber G p) (oldNumber (V := V)) (ActualOutSplit.start G p) G.target

abbrev rDecode := Rect.decode (oldNumber (V := V)) (newNumber G p)
  (fun u : ActualOutSplit.Vertex G p => u.val.1) id
abbrev sDecode := Rect.decode (newNumber G p) (oldNumber (V := V)) (ActualOutSplit.start G p) G.target

private theorem r_source (r : Edge (R G p)) :
    oldNumber (V := V) (rDecode G p r).val.1 = r.source :=
  (Rect.decode_endpoints _ _ _ _ r).1
private theorem r_target (r : Edge (R G p)) :
    newNumber G p (rDecode G p r) = r.target :=
  (Rect.decode_endpoints _ _ _ _ r).2
private theorem s_source (s : Edge (S G p)) :
    newNumber G p (ActualOutSplit.start G p (sDecode G p s)) = s.source :=
  (Rect.decode_endpoints _ _ _ _ s).1
private theorem s_target (s : Edge (S G p)) :
    oldNumber (V := V) (G.target (sDecode G p s)) = s.target :=
  (Rect.decode_endpoints _ _ _ _ s).2

private def oldEncode (e : E) : Edge (R G p * S G p) :=
  join (R G p) (S G p) ((rDecode G p).symm (ActualOutSplit.start G p e)) ((sDecode G p).symm e) (by
    rw [(Rect.encode_endpoints _ _ _ _ _).2,(Rect.encode_endpoints _ _ _ _ _).1]
    rfl)

private def oldDecode (e : Edge (R G p * S G p)) : E :=
  sDecode G p (split (R G p) (S G p) e).2

/-- Numbering of the actual old edges by RS, not an assumed order match. -/
def oldEdgeEquiv : Edge (R G p * S G p) ≃ E where
  toFun := oldDecode G p
  invFun := oldEncode G p
  left_inv e := by
    have hp : (split (R G p) (S G p) e).1.target =
        (split (R G p) (S G p) e).2.source := rfl
    have hclass : rDecode G p (split (R G p) (S G p) e).1 =
        ActualOutSplit.start G p (sDecode G p (split (R G p) (S G p) e).2) := by
      apply (newNumber G p).injective
      exact (r_target G p _).trans (hp.trans (s_source G p _).symm)
    change oldEncode G p (oldDecode G p e) = e
    unfold oldEncode oldDecode
    have hr : (rDecode G p).symm (ActualOutSplit.start G p (sDecode G p (split (R G p) (S G p) e).2)) =
        (split (R G p) (S G p) e).1 := by
      rw [← hclass]
      exact (rDecode G p).symm_apply_apply _
    simp only [hr, Equiv.symm_apply_apply]
    exact join_split (R G p) (S G p) e
  right_inv e := by
    have hs := split_join (R G p) (S G p)
      ((rDecode G p).symm (ActualOutSplit.start G p e)) ((sDecode G p).symm e)
      (show ((rDecode G p).symm (ActualOutSplit.start G p e)).target =
        ((sDecode G p).symm e).source by
          rw [(Rect.encode_endpoints _ _ _ _ _).2,(Rect.encode_endpoints _ _ _ _ _).1]
          rfl)
    change sDecode G p (split (R G p) (S G p) (oldEncode G p e)).2 = e
    rw [show split (R G p) (S G p) (oldEncode G p e) = _ from hs]
    exact (sDecode G p).apply_symm_apply e

private def newDecode (a : Edge (S G p * R G p)) : ActualOutSplit.SplitEdge G p := by
  let e := sDecode G p (split (S G p) (R G p) a).1
  let u := rDecode G p (split (S G p) (R G p) a).2
  have hu : G.target e = u.val.1 := by
    apply (oldNumber (V := V)).injective
    exact (s_target G p (split (S G p) (R G p) a).1).trans
      (r_source G p (split (S G p) (R G p) a).2).symm
  refine ⟨(e,u.val.2),?_⟩
  obtain ⟨f,hf,hp⟩ := u.property
  exact ⟨f,hf.trans hu.symm,hp⟩

private def newEncode (a : ActualOutSplit.SplitEdge G p) : Edge (S G p * R G p) :=
  join (S G p) (R G p) ((sDecode G p).symm a.val.1)
    ((rDecode G p).symm (ActualOutSplit.finish G p a)) (by
      rw [(Rect.encode_endpoints _ _ _ _ _).2,(Rect.encode_endpoints _ _ _ _ _).1]
      rfl)

def newEdgeEquiv : Edge (S G p * R G p) ≃ ActualOutSplit.SplitEdge G p where
  toFun := newDecode G p
  invFun := newEncode G p
  left_inv a := by
    have hf : ActualOutSplit.finish G p (newDecode G p a) =
        rDecode G p (split (S G p) (R G p) a).2 := by
      apply ActualOutSplit.vertex_ext
      · apply (oldNumber (V := V)).injective
        exact (s_target G p (split (S G p) (R G p) a).1).trans
          (r_source G p (split (S G p) (R G p) a).2).symm
      · rfl
    change newEncode G p (newDecode G p a) = a
    unfold newEncode
    change join (S G p) (R G p)
      ((sDecode G p).symm (sDecode G p (split (S G p) (R G p) a).1))
      ((rDecode G p).symm (ActualOutSplit.finish G p (newDecode G p a))) _ = a
    simp only [hf, Equiv.symm_apply_apply]
    exact join_split (S G p) (R G p) a
  right_inv a := by
    apply ActualOutSplit.edge_ext
    · change sDecode G p (split (S G p) (R G p) (newEncode G p a)).1 = a.val.1
      simp only [newEncode,split_join,(sDecode G p).apply_symm_apply]
    · change (rDecode G p (split (S G p) (R G p) (newEncode G p a)).2).val.2 = a.val.2
      simp only [newEncode,split_join,(rDecode G p).apply_symm_apply,ActualOutSplit.finish]

theorem old_endpoints (a : Edge (R G p * S G p)) :
    oldNumber (V := V) (G.source (oldEdgeEquiv G p a)) = a.source ∧
    oldNumber (V := V) (G.target (oldEdgeEquiv G p a)) = a.target := by
  let r := (split (R G p) (S G p) a).1
  let s := (split (R G p) (S G p) a).2
  have hc : ActualOutSplit.start G p (sDecode G p s) = rDecode G p r := by
    apply (newNumber G p).injective
    exact (s_source G p s).trans (r_target G p r).symm
  constructor
  · exact (congrArg (fun u : ActualOutSplit.Vertex G p => oldNumber (V := V) u.val.1) hc).trans
      (r_source G p r)
  · exact s_target G p s

theorem new_endpoints (a : Edge (S G p * R G p)) :
    newNumber G p ((ActualOutSplit.graph G p).source (newEdgeEquiv G p a)) = a.source ∧
    newNumber G p ((ActualOutSplit.graph G p).target (newEdgeEquiv G p a)) = a.target := by
  constructor
  · exact s_source G p (split (S G p) (R G p) a).1
  · have hu : ActualOutSplit.finish G p (newDecode G p a) =
        rDecode G p (split (S G p) (R G p) a).2 := by
      apply ActualOutSplit.vertex_ext
      · apply (oldNumber (V := V)).injective
        exact (s_target G p (split (S G p) (R G p) a).1).trans
          (r_source G p (split (S G p) (R G p) a).2).symm
      · rfl
    change newNumber G p (ActualOutSplit.finish G p (newDecode G p a)) = a.target
    rw [hu]
    exact r_target G p (split (S G p) (R G p) a).2




/-- An edge equivalence with explicit vertex numbering induces a literal
numbered Path homeomorphism. Consumed for both products below. -/
private def pathNumber {I A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    {n : ℕ} (F : DirectedMultigraph I A) (iv : I ≃ Fin n) (B : CountMat n n)
    (e : Edge B ≃ A)
    (he : ∀ a, iv (F.source (e a)) = a.source ∧ iv (F.target (e a)) = a.target) :
    History F ≃ₜ Path B where
  toFun x := ⟨fun t => e.symm (x.val t),by
    intro t
    have ha := he (e.symm (x.val t))
    have hb := he (e.symm (x.val (t+1)))
    rw [e.apply_symm_apply] at ha hb
    exact ha.2.symm.trans ((congrArg iv (x.property t)).trans hb.1)⟩
  invFun x := ⟨fun t => e (x.val t),by
    intro t
    apply iv.injective
    exact (he _).2.trans ((x.property t).trans (he _).1.symm)⟩
  left_inv x := by
    apply Subtype.ext
    funext t
    exact e.apply_symm_apply _
  right_inv x := by
    apply Subtype.ext
    funext t
    exact e.symm_apply_apply _
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro t
    exact (continuous_of_discreteTopology : Continuous e.symm).comp
      ((continuous_apply t).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro t
    exact (continuous_of_discreteTopology : Continuous e).comp
      ((continuous_apply t).comp continuous_subtype_val)

section Topology
variable [TopologicalSpace E] [DiscreteTopology E]
variable [TopologicalSpace L] [DiscreteTopology L]

def oldPaths : History G ≃ₜ Path (R G p * S G p) :=
  pathNumber G (oldNumber (V := V)) _ (oldEdgeEquiv G p) (old_endpoints G p)
def newPaths : History (ActualOutSplit.graph G p) ≃ₜ Path (S G p * R G p) :=
  pathNumber (ActualOutSplit.graph G p) (newNumber G p) _ (newEdgeEquiv G p) (new_endpoints G p)

/-- Decoding the EXISTING numbered positive elementary recoding is exactly
the actual outgoing partition lift. There is no shift or inverse substitution. -/
theorem numbered_recoding (x : History G) :
    elementaryHomeomorph (R G p) (S G p) (oldPaths G p x) =
      newPaths G p (ActualOutSplit.lift G p x) := by
  apply Subtype.ext
  funext t
  apply (newEdgeEquiv G p).injective
  change newDecode G p
    (join (S G p) (R G p)
      (split (R G p) (S G p) ((oldPaths G p x).val t)).2
      (split (R G p) (S G p) ((oldPaths G p x).val (t+1))).1 ((oldPaths G p x).property t)) =
    newEdgeEquiv G p ((newEdgeEquiv G p).symm ((ActualOutSplit.lift G p x).val t))
  rw [(newEdgeEquiv G p).apply_symm_apply]
  apply ActualOutSplit.edge_ext
  · change sDecode G p (split (S G p) (R G p) (join (S G p) (R G p) _ _ _)).1 = x.val t
    rw [split_join]
    change oldDecode G p ((oldEdgeEquiv G p).symm (x.val t)) = x.val t
    exact (oldEdgeEquiv G p).apply_symm_apply _
  · change (rDecode G p (split (S G p) (R G p) (join (S G p) (R G p) _ _ _)).2).val.2 = _
    rw [split_join]
    have hs := (oldEdgeEquiv G p).apply_symm_apply (x.val (t+1))
    let a := (oldPaths G p x).val (t+1)
    have hc : rDecode G p (split (R G p) (S G p) a).1 =
        ActualOutSplit.start G p (sDecode G p (split (R G p) (S G p) a).2) := by
      apply (newNumber G p).injective
      exact (r_target G p (split (R G p) (S G p) a).1).trans
        (s_source G p (split (R G p) (S G p) a).2).symm
    exact (congrArg (fun u : ActualOutSplit.Vertex G p => u.val.2) hc).trans (congrArg p hs)
end Topology

end D5.S3.ConceptDynamics.Coding.OutSplitNumberedRecoding
