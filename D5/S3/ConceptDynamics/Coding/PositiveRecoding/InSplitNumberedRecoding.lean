/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/InSplitNumberedRecoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Number the actual incoming split and retain its time correction. -/

/- Incoming split numbering uses the existing rectangular fiber enumerator and counted split/join. Lift carries a negative unit-time correction; forget uses the opposite positive recoding. -/
import D5.S3.ConceptDynamics.Coding.TwoSidedFiniteInduction
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.OutSplitNumberedRecoding
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.FiniteGraphRelabelHomeomorph
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.NumberedPositiveInverseLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.InSplitNumberedRecoding
open EssentialWordRealization CountedMatrixOverlap
open OutSplitNumberedRecoding
open ZeroWindowRelabeling (Relabel)
variable {V E L : Type*} [Fintype V] [Fintype E] [Fintype L]
variable [DecidableEq V] [DecidableEq L]
variable (G : DirectedMultigraph V E) (p : E → L)

def oldNumber : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
def newNumber : ActualInSplit.Vertex G p ≃ Fin (Fintype.card (ActualInSplit.Vertex G p)) := Fintype.equivFin _
/-- R half-edges are original edges, ending at their incoming label class. -/
abbrev R : CountMat (Fintype.card V) (Fintype.card (ActualInSplit.Vertex G p)) :=
  Rect.matrix (oldNumber (V := V)) (newNumber G p) G.source (ActualInSplit.finish G p)
/-- S half-edges are retained classes, returning to their old vertex. -/
abbrev S : CountMat (Fintype.card (ActualInSplit.Vertex G p)) (Fintype.card V) :=
  Rect.matrix (newNumber G p) (oldNumber (V := V)) id
    (fun u : ActualInSplit.Vertex G p => u.val.1)
abbrev rDecode := Rect.decode (oldNumber (V := V)) (newNumber G p) G.source (ActualInSplit.finish G p)
abbrev sDecode := Rect.decode (newNumber G p) (oldNumber (V := V)) id
  (fun u : ActualInSplit.Vertex G p => u.val.1)

private theorem pair_class (r : Edge (R G p)) (s : Edge (S G p)) (h : r.target = s.source) :
    ActualInSplit.finish G p (rDecode G p r) = sDecode G p s := by
  apply (newNumber G p).injective
  exact (Rect.decode_endpoints _ _ _ _ r).2.trans
    (h.trans (Rect.decode_endpoints _ _ _ _ s).1.symm)

private def oldEncode (e : E) : Edge (R G p * S G p) :=
  join (R G p) (S G p) ((rDecode G p).symm e)
    ((sDecode G p).symm (ActualInSplit.finish G p e)) (by
      rw [(Rect.encode_endpoints _ _ _ _ _).2,(Rect.encode_endpoints _ _ _ _ _).1]
      rfl)
private def oldDecode (a : Edge (R G p * S G p)) : E :=
  rDecode G p (split (R G p) (S G p) a).1

def oldEdgeEquiv : Edge (R G p * S G p) ≃ E where
  toFun := oldDecode G p
  invFun := oldEncode G p
  left_inv a := by
    have hc := pair_class G p (split (R G p) (S G p) a).1
      (split (R G p) (S G p) a).2 rfl
    change oldEncode G p (oldDecode G p a) = a
    unfold oldEncode oldDecode
    simp only [hc,(rDecode G p).symm_apply_apply,(sDecode G p).symm_apply_apply]
    exact join_split (R G p) (S G p) a
  right_inv e := by
    change rDecode G p (split (R G p) (S G p) (oldEncode G p e)).1 = e
    simp only [oldEncode,split_join,(rDecode G p).apply_symm_apply]

private def newDecode (a : Edge (S G p * R G p)) : ActualInSplit.SplitEdge G p := by
  let u := sDecode G p (split (S G p) (R G p) a).1
  let e := rDecode G p (split (S G p) (R G p) a).2
  have hu : u.val.1 = G.source e := by
    apply (oldNumber (V := V)).injective
    exact (Rect.decode_endpoints _ _ _ _ (split (S G p) (R G p) a).1).2.trans
      (Rect.decode_endpoints _ _ _ _ (split (S G p) (R G p) a).2).1.symm
  refine ⟨(u.val.2,e),?_⟩
  obtain ⟨f,hf,hp⟩ := u.property
  exact ⟨f,hf.trans hu,hp⟩
private def newEncode (a : ActualInSplit.SplitEdge G p) : Edge (S G p * R G p) :=
  join (S G p) (R G p) ((sDecode G p).symm (ActualInSplit.start G p a))
    ((rDecode G p).symm a.val.2) (by
      rw [(Rect.encode_endpoints _ _ _ _ _).2,(Rect.encode_endpoints _ _ _ _ _).1]
      rfl)

private theorem new_start (a : Edge (S G p * R G p)) :
    ActualInSplit.start G p (newDecode G p a) =
      sDecode G p (split (S G p) (R G p) a).1 := by
  apply ActualInSplit.vertex_ext
  · apply (oldNumber (V := V)).injective
    exact (Rect.decode_endpoints _ _ _ _ (split (S G p) (R G p) a).2).1.trans
      (Rect.decode_endpoints _ _ _ _ (split (S G p) (R G p) a).1).2.symm
  · rfl

def newEdgeEquiv : Edge (S G p * R G p) ≃ ActualInSplit.SplitEdge G p where
  toFun := newDecode G p
  invFun := newEncode G p
  left_inv a := by
    change newEncode G p (newDecode G p a) = a
    unfold newEncode
    change join (S G p) (R G p)
      ((sDecode G p).symm (ActualInSplit.start G p (newDecode G p a)))
      ((rDecode G p).symm (rDecode G p (split (S G p) (R G p) a).2)) _ = a
    simp only [new_start,(sDecode G p).symm_apply_apply,(rDecode G p).symm_apply_apply]
    exact join_split (S G p) (R G p) a
  right_inv a := by
    apply ActualInSplit.edge_ext
    · change (sDecode G p (split (S G p) (R G p) (newEncode G p a)).1).val.2 = a.val.1
      simp only [newEncode,split_join,(sDecode G p).apply_symm_apply,ActualInSplit.start]
    · change rDecode G p (split (S G p) (R G p) (newEncode G p a)).2 = a.val.2
      simp only [newEncode,split_join,(rDecode G p).apply_symm_apply]

theorem old_endpoints (a : Edge (R G p * S G p)) :
    oldNumber (V := V) (G.source (oldEdgeEquiv G p a)) = a.source ∧
    oldNumber (V := V) (G.target (oldEdgeEquiv G p a)) = a.target := by
  constructor
  · exact (Rect.decode_endpoints _ _ _ _ (split (R G p) (S G p) a).1).1
  · have hc := pair_class G p (split (R G p) (S G p) a).1
      (split (R G p) (S G p) a).2 rfl
    exact (congrArg (fun u : ActualInSplit.Vertex G p => oldNumber (V := V) u.val.1) hc).trans
      (Rect.decode_endpoints _ _ _ _ (split (R G p) (S G p) a).2).2

theorem new_endpoints (a : Edge (S G p * R G p)) :
    newNumber G p ((ActualInSplit.graph G p).source (newEdgeEquiv G p a)) = a.source ∧
    newNumber G p ((ActualInSplit.graph G p).target (newEdgeEquiv G p a)) = a.target := by
  constructor
  · change newNumber G p (ActualInSplit.start G p (newDecode G p a)) = a.source
    rw [new_start]
    exact (Rect.decode_endpoints _ _ _ _ (split (S G p) (R G p) a).1).1
  · exact (Rect.decode_endpoints _ _ _ _ (split (S G p) (R G p) a).2).2

def counted {n : ℕ} (B : CountMat n n) : DirectedMultigraph (Fin n) (Edge B) :=
  ⟨Edge.source,Edge.target⟩
def oldRelabel : Relabel (counted (R G p * S G p)) G where
  vertex := (oldNumber (V := V)).symm
  edge := oldEdgeEquiv G p
  source a := by
    apply (oldNumber (V := V)).injective
    rw [(oldNumber (V := V)).apply_symm_apply]
    exact (old_endpoints G p a).1
  target a := by
    apply (oldNumber (V := V)).injective
    rw [(oldNumber (V := V)).apply_symm_apply]
    exact (old_endpoints G p a).2

def newRelabel : Relabel (counted (S G p * R G p)) (ActualInSplit.graph G p) where
  vertex := (newNumber G p).symm
  edge := newEdgeEquiv G p
  source a := by
    apply (newNumber G p).injective
    rw [(newNumber G p).apply_symm_apply]
    exact (new_endpoints G p a).1
  target a := by
    apply (newNumber G p).injective
    rw [(newNumber G p).apply_symm_apply]
    exact (new_endpoints G p a).2

section Topology
variable [TopologicalSpace E] [DiscreteTopology E]
variable [TopologicalSpace L] [DiscreteTopology L]
def oldPaths : History G ≃ₜ Path (R G p * S G p) := (oldRelabel G p).homeomorph.symm
def newPaths : History (ActualInSplit.graph G p) ≃ₜ Path (S G p * R G p) :=
  (newRelabel G p).homeomorph.symm

/-- Incoming FORGET is the opposite positive recoding, with no time shift. -/
theorem numbered_forget (z : History (ActualInSplit.graph G p)) :
    elementaryHomeomorph (S G p) (R G p) (newPaths G p z) =
      oldPaths G p (ActualInSplit.forget G p z) := by
  apply Subtype.ext
  funext t
  apply (oldEdgeEquiv G p).injective
  change oldEdgeEquiv G p ((elementaryHomeomorph (S G p) (R G p) (newPaths G p z)).val t) =
    oldEdgeEquiv G p ((oldEdgeEquiv G p).symm (z.val t).val.2)
  rw [(oldEdgeEquiv G p).apply_symm_apply]
  change oldDecode G p (join (R G p) (S G p)
    (split (S G p) (R G p) ((newPaths G p z).val t)).2
    (split (S G p) (R G p) ((newPaths G p z).val (t+1))).1
      ((newPaths G p z).property t)) = (z.val t).val.2
  simp only [oldDecode,split_join]
  change (newDecode G p ((newEdgeEquiv G p).symm (z.val t))).val.2 = _
  exact congrArg (fun e : ActualInSplit.SplitEdge G p => e.val.2)
    ((newEdgeEquiv G p).apply_symm_apply (z.val t))

/-- Incoming LIFT is positive R,S with the necessary -1 correction. -/
theorem numbered_lift (x : History G) :
    newPaths G p (ActualInSplit.lift G p x) =
      NumberedPositiveInverseLaws.translate (S G p * R G p) (-1)
        (elementaryHomeomorph (R G p) (S G p) (oldPaths G p x)) := by
  have hf := numbered_forget G p (ActualInSplit.lift G p x)
  rw [ActualInSplit.forget_lift] at hf
  have hi := congrArg (elementaryHomeomorph (S G p) (R G p)).symm hf
  rw [(elementaryHomeomorph (S G p) (R G p)).symm_apply_apply] at hi
  exact hi.trans (NumberedPositiveInverseLaws.inverse_eq_negative_positive (S G p) (R G p) _)
end Topology
end D5.S3.ConceptDynamics.Coding.InSplitNumberedRecoding
