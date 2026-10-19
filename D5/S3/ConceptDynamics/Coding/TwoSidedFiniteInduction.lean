/- GID: D5/S3/ConceptDynamics/Coding/TwoSidedFiniteInduction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/TwoSidedFiniteInduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Constructed finite two-sided split towers with supported in/out inverse-window decrease. -/

import D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
import D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
import Mathlib.Data.Fintype.Card


set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.ActualOutSplit

open EssentialWordRealization
open FiniteWindowTableCriterion (shift)

variable {V E L : Type*}
variable (G : DirectedMultigraph V E) (p : E → L)

abbrev Vertex := {z : V × L // ∃ e, G.source e = z.1 ∧ p e = z.2}
abbrev SplitEdge := {z : E × L // ∃ f, G.source f = G.target z.1 ∧ p f = z.2}

instance [Fintype V] [Fintype E] [Fintype L] : Fintype (Vertex G p) := by
  classical
  infer_instance
instance [Fintype E] [Fintype L] : Fintype (SplitEdge G p) := by
  classical
  infer_instance

def start (e : E) : Vertex G p := ⟨(G.source e,p e),e,rfl,rfl⟩
def finish (e : SplitEdge G p) : Vertex G p := ⟨(G.target e.val.1,e.val.2),e.property⟩
def graph : DirectedMultigraph (Vertex G p) (SplitEdge G p) :=
  ⟨fun e => start G p e.val.1,finish G p⟩

@[ext] theorem vertex_ext {u v : Vertex G p}
    (h₁ : u.val.1 = v.val.1) (h₂ : u.val.2 = v.val.2) : u = v :=
  Subtype.ext (Prod.ext h₁ h₂)
@[ext] theorem edge_ext {e f : SplitEdge G p}
    (h₁ : e.val.1 = f.val.1) (h₂ : e.val.2 = f.val.2) : e = f :=
  Subtype.ext (Prod.ext h₁ h₂)

theorem essential (hG : Essential G) : Essential (graph G p) := by
  constructor
  · intro v
    obtain ⟨e,he,hp⟩ := v.property
    obtain ⟨f,hf⟩ := hG.outgoing (G.target e)
    refine ⟨⟨(e,p f),f,hf,rfl⟩,?_⟩
    exact vertex_ext G p he hp
  · intro v
    obtain ⟨e,he⟩ := hG.incoming v.val.1
    refine ⟨⟨(e,v.val.2),?_⟩,?_⟩
    · obtain ⟨f,hf,hp⟩ := v.property
      exact ⟨f,hf.trans he.symm,hp⟩
    · exact vertex_ext G p he rfl

def lift (x : History G) : History (graph G p) :=
  ⟨fun t => ⟨(x.val t,p (x.val (t+1))),x.val (t+1),(x.property t).symm,rfl⟩,
    fun t => vertex_ext G p (x.property t) rfl⟩

def forget (z : History (graph G p)) : History G :=
  ⟨fun t => (z.val t).val.1,
    fun t => congrArg (fun v : Vertex G p => v.val.1) (z.property t)⟩

theorem label_next (z : History (graph G p)) (t : ℤ) :
    (z.val t).val.2 = p ((z.val (t+1)).val.1) :=
  congrArg (fun v : Vertex G p => v.val.2) (z.property t)

@[simp] theorem forget_lift (x : History G) : forget G p (lift G p x) = x := rfl
@[simp] theorem lift_forget (z : History (graph G p)) : lift G p (forget G p z) = z := by
  apply Subtype.ext
  funext t
  exact edge_ext G p rfl (label_next G p z t).symm

section Topology
variable [TopologicalSpace E] [DiscreteTopology E]
variable [TopologicalSpace L] [DiscreteTopology L]

def homeomorph : History G ≃ₜ History (graph G p) where
  toFun := lift G p
  invFun := forget G p
  left_inv := forget_lift G p
  right_inv := lift_forget G p
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro t
    apply Continuous.subtype_mk
    exact ((continuous_apply t).comp continuous_subtype_val).prodMk
      ((continuous_of_discreteTopology : Continuous p).comp
        ((continuous_apply (t+1)).comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro t
    exact (continuous_of_discreteTopology : Continuous
      (fun e : SplitEdge G p => e.val.1)).comp
        ((continuous_apply t).comp continuous_subtype_val)
end Topology

end D5.S3.ConceptDynamics.Coding.ActualOutSplit

end


set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.OutSplitConjugacyDecrease

open EssentialWordRealization FiniteWindowTableCriterion

variable {V E W D : Type*}
variable (G : DirectedMultigraph V E) (H : DirectedMultigraph W D)

/-- An ordinary finite graph morphism, not a presentation hypothesis. -/
structure Code where
  vertex : V → W
  edge : E → D
  source : ∀ e, H.source (edge e) = vertex (G.source e)
  target : ∀ e, H.target (edge e) = vertex (G.target e)

variable {G H}

def mapHistory (c : Code G H) (x : History G) : History H :=
  ⟨fun t => c.edge (x.val t),fun t =>
    (c.target _).trans ((congrArg c.vertex (x.property t)).trans (c.source _).symm)⟩

def splitVertex (c : Code G H) (u : ActualOutSplit.Vertex G c.edge) : ActualOutSplit.Vertex H id := by
  refine ⟨(c.vertex u.val.1,u.val.2),u.val.2,?_,rfl⟩
  obtain ⟨e,he,hp⟩ := u.property
  change H.source u.val.2 = c.vertex u.val.1
  rw [← hp,c.source,he]

def splitEdge (c : Code G H) (e : ActualOutSplit.SplitEdge G c.edge) : ActualOutSplit.SplitEdge H id := by
  refine ⟨(c.edge e.val.1,e.val.2),e.val.2,?_,rfl⟩
  obtain ⟨f,hf,hp⟩ := e.property
  change H.source e.val.2 = H.target (c.edge e.val.1)
  rw [← hp,c.source,hf,c.target]

def splitCode (c : Code G H) : Code (ActualOutSplit.graph G c.edge) (ActualOutSplit.graph H id) where
  vertex := splitVertex c
  edge := splitEdge c
  source e := ActualOutSplit.vertex_ext H id (c.source e.val.1) rfl
  target e := ActualOutSplit.vertex_ext H id (c.target e.val.1) rfl

section Conjugacy
variable [TopologicalSpace E] [DiscreteTopology E]
variable [TopologicalSpace D] [DiscreteTopology D]
variable (c : Code G H) (P : History G ≃ₜ History H)
variable (hP : ∀ x t, (P x).val t = c.edge (x.val t))

def changed : History (ActualOutSplit.graph G c.edge) ≃ₜ History (ActualOutSplit.graph H id) :=
  ((ActualOutSplit.homeomorph G c.edge).symm.trans P).trans (ActualOutSplit.homeomorph H id)

/-- Both changed presentations and this conjugacy are constructed. -/
theorem square (x : History G) :
    changed c P (ActualOutSplit.lift G c.edge x) = ActualOutSplit.lift H id (P x) := by
  change ActualOutSplit.lift H id (P (ActualOutSplit.forget G c.edge (ActualOutSplit.lift G c.edge x))) = _
  rw [ActualOutSplit.forget_lift]

include hP in
/-- The horizontal changed map has this actual one-block formula on ALL
legal split histories, including those not supplied as lifts. -/
theorem changed_one_block (z : History (ActualOutSplit.graph G c.edge)) (t : ℤ) :
    (changed c P z).val t = splitEdge c (z.val t) := by
  apply ActualOutSplit.edge_ext H id
  · exact hP (ActualOutSplit.forget G c.edge z) t
  · exact (hP (ActualOutSplit.forget G c.edge z) (t+1)).trans (ActualOutSplit.label_next G c.edge z t).symm

variable [Fintype V] [Fintype E] [DecidableEq V]
variable [Fintype W] [Fintype D] [DecidableEq W]
variable (hH : Essential H) (M N : ℕ)
variable (Q : LegalWord H (M+(N+1)+1) → E)
variable (hQ : ∀ y t, Q (historyWindow H y (t-(M:ℤ)) (M+(N+1)+1)) = (P.symm y).val t)

/-- Expand a nonempty full-out-split word. The final second component is
essential: dropping it would fail to shorten the inverse window. -/
def expand (w : LegalWord (ActualOutSplit.graph H id) (M+N+1)) : LegalWord H (M+(N+1)+1) where
  edge j := if hj : j.val < M+N+1 then (w.edge ⟨j.val,hj⟩).val.1
    else (w.edge ⟨M+N,by omega⟩).val.2
  legal j hj := by
    have hj0 : j.val < M+N+1 := by omega
    by_cases hn : j.val+1 < M+N+1
    · have hs := w.legal ⟨j.val,hj0⟩ hn
      have ha := congrArg (fun u : ActualOutSplit.Vertex H id => u.val.1) hs
      have hc : H.target (w.edge ⟨j.val,hj0⟩).val.1 =
          H.source (w.edge ⟨j.val+1,hn⟩).val.1 := ha
      simpa only [dif_pos hj0,dif_pos hn] using hc
    · have hlast : j.val = M+N := by omega
      have hp := (w.edge ⟨M+N,by omega⟩).property
      obtain ⟨f,hf,hid⟩ := hp
      have hc : H.target (w.edge ⟨M+N,by omega⟩).val.1 =
          H.source (w.edge ⟨M+N,by omega⟩).val.2 := by
        change f = _ at hid
        exact hf.symm.trans (congrArg H.source hid)
      simpa only [hlast, dif_pos (show M+N < M+N+1 by omega),
        dif_neg (Nat.lt_irrefl (M+N+1))] using hc

/-- Exact expansion on every legal history. -/
theorem expand_window (z : History (ActualOutSplit.graph H id)) (t : ℤ) :
    expand (H := H) M N
      (historyWindow (ActualOutSplit.graph H id) z (t-(M:ℤ)) (M+N+1)) =
    historyWindow H (ActualOutSplit.forget H id z) (t-(M:ℤ)) (M+(N+1)+1) := by
  apply legalWord_ext
  funext j
  by_cases hj : j.val < M+N+1
  · simp only [expand,historyWindow,dif_pos hj,ActualOutSplit.forget]
  · have he : j.val = M+N+1 := by have := j.isLt; omega
    have hn := ActualOutSplit.label_next H id z (t-(M:ℤ)+((M+N:ℕ):ℤ))
    have ht : t-(M:ℤ)+((M+N:ℕ):ℤ)+1 = t-(M:ℤ)+(j.val:ℤ) := by omega
    simpa only [expand,historyWindow,dif_neg hj,ActualOutSplit.forget,id_eq,ht] using hn


/-- A total finite table on all legal new target words, not a table only
on known image windows. Its membership proof uses essentiality. -/
def recover (w : LegalWord (ActualOutSplit.graph H id) (M+N+1)) : ActualOutSplit.SplitEdge G c.edge :=
  ⟨(Q (expand (H := H) M N w),(w.edge ⟨M,by omega⟩).val.2),
    by
      let u := expand (H := H) M N w
      obtain ⟨y,hy⟩ := every_prescribed_word_has_actual_history H hH u (by omega)
      have hw : historyWindow H y 0 (M+(N+1)+1) = u := by
        apply legalWord_ext
        funext j
        simpa only [historyWindow,zero_add] using hy j
      have hr := hQ y (M:ℤ)
      rw [sub_self,hw] at hr
      have hnext : y.val ((M:ℤ)+1) = (w.edge ⟨M,by omega⟩).val.2 := by
        by_cases hn : M+1 < M+N+1
        · have ha : y.val ((M:ℤ)+1) = (w.edge ⟨M+1,hn⟩).val.1 := by
            simpa only [u,expand,dif_pos hn,Int.natCast_add,Int.natCast_one] using
              hy ⟨M+1,by omega⟩
          have hb := congrArg (fun v : ActualOutSplit.Vertex H id => v.val.2)
            (w.legal ⟨M,by omega⟩ hn)
          exact ha.trans hb.symm
        · have he : M+N = M := by omega
          have hj : ¬ M+1 < M+N+1 := hn
          simpa only [u,expand,he, dif_neg (Nat.lt_irrefl (M+1)),Int.natCast_add,Int.natCast_one] using
            hy ⟨M+1,by omega⟩
      refine ⟨(P.symm y).val ((M:ℤ)+1),?_,?_⟩
      · rw [hr]
        exact ((P.symm y).property (M:ℤ)).symm
      · have hp := hP (P.symm y) ((M:ℤ)+1)
        rw [P.apply_symm_apply] at hp
        exact hp.symm.trans hnext⟩

/-- Exact certified inverse window (M,N) for the new horizontal code. -/
theorem recover_window (z : History (ActualOutSplit.graph H id)) (t : ℤ) :
    recover c P hP hH M N Q hQ
      (historyWindow (ActualOutSplit.graph H id) z (t-(M:ℤ)) (M+N+1)) =
      ((changed c P).symm z).val t := by
  apply ActualOutSplit.edge_ext G c.edge
  · change Q (expand (H := H) M N _) = (P.symm (ActualOutSplit.forget H id z)).val t
    rw [expand_window]
    exact hQ (ActualOutSplit.forget H id z) t
  · change (z.val (t-(M:ℤ)+(M:ℤ))).val.2 =
      c.edge ((P.symm (ActualOutSplit.forget H id z)).val (t+1))
    have hp := hP (P.symm (ActualOutSplit.forget H id z)) (t+1)
    rw [P.apply_symm_apply] at hp
    simpa only [sub_add_cancel,ActualOutSplit.forget] using
      (ActualOutSplit.label_next H id z t).trans hp


end Conjugacy
end D5.S3.ConceptDynamics.Coding.OutSplitConjugacyDecrease

end


set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.ActualInSplit
open EssentialWordRealization
open FiniteWindowTableCriterion (shift)
variable {V E L : Type*} (G : DirectedMultigraph V E) (p : E → L)

abbrev Vertex := {z : V × L // ∃ e, G.target e = z.1 ∧ p e = z.2}
abbrev SplitEdge := {z : L × E // ∃ f, G.target f = G.source z.2 ∧ p f = z.1}
instance [Fintype V] [Fintype E] [Fintype L] : Fintype (Vertex G p) := by
  classical
  infer_instance
instance [Fintype E] [Fintype L] : Fintype (SplitEdge G p) := by
  classical
  infer_instance

def start (e : SplitEdge G p) : Vertex G p := ⟨(G.source e.val.2,e.val.1),e.property⟩
def finish (e : E) : Vertex G p := ⟨(G.target e,p e),e,rfl,rfl⟩
def graph : DirectedMultigraph (Vertex G p) (SplitEdge G p) :=
  ⟨start G p,fun e => finish G p e.val.2⟩
@[ext] theorem vertex_ext {u v : Vertex G p}
    (h₁ : u.val.1 = v.val.1) (h₂ : u.val.2 = v.val.2) : u = v :=
  Subtype.ext (Prod.ext h₁ h₂)
@[ext] theorem edge_ext {e f : SplitEdge G p}
    (h₁ : e.val.1 = f.val.1) (h₂ : e.val.2 = f.val.2) : e = f :=
  Subtype.ext (Prod.ext h₁ h₂)

theorem essential (hG : Essential G) : Essential (graph G p) := by
  constructor
  · intro v
    obtain ⟨e,he⟩ := hG.outgoing v.val.1
    refine ⟨⟨(v.val.2,e),?_⟩,vertex_ext G p he rfl⟩
    obtain ⟨f,hf,hp⟩ := v.property
    exact ⟨f,hf.trans he.symm,hp⟩
  · intro v
    obtain ⟨e,he,hp⟩ := v.property
    obtain ⟨f,hf⟩ := hG.incoming (G.source e)
    exact ⟨⟨(p f,e),f,hf,rfl⟩,vertex_ext G p he hp⟩

def lift (x : History G) : History (graph G p) :=
  ⟨fun t => ⟨(p (x.val (t-1)),x.val t),x.val (t-1),by
      simpa only [sub_add_cancel] using x.property (t-1),rfl⟩,
    fun t => vertex_ext G p (x.property t) (by
      change p (x.val t) = p (x.val (t+1-1))
      rw [add_sub_cancel_right])⟩
def forget (z : History (graph G p)) : History G :=
  ⟨fun t => (z.val t).val.2,
    fun t => congrArg (fun v : Vertex G p => v.val.1) (z.property t)⟩
theorem label_prev (z : History (graph G p)) (t : ℤ) :
    (z.val t).val.1 = p ((z.val (t-1)).val.2) := by
  have h := congrArg (fun v : Vertex G p => v.val.2) (z.property (t-1))
  change p ((z.val (t-1)).val.2) = (z.val (t-1+1)).val.1 at h
  simpa only [sub_add_cancel] using h.symm
@[simp] theorem forget_lift (x : History G) : forget G p (lift G p x) = x := rfl
@[simp] theorem lift_forget (z : History (graph G p)) : lift G p (forget G p z) = z := by
  apply Subtype.ext
  funext t
  exact edge_ext G p (label_prev G p z t).symm rfl
section Topology
variable [TopologicalSpace E] [DiscreteTopology E]
variable [TopologicalSpace L] [DiscreteTopology L]
def homeomorph : History G ≃ₜ History (graph G p) where
  toFun := lift G p
  invFun := forget G p
  left_inv := forget_lift G p
  right_inv := lift_forget G p
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro t
    apply Continuous.subtype_mk
    exact ((continuous_of_discreteTopology : Continuous p).comp
      ((continuous_apply (t-1)).comp continuous_subtype_val)).prodMk
      ((continuous_apply t).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro t
    exact (continuous_of_discreteTopology : Continuous
      (fun e : SplitEdge G p => e.val.2)).comp
        ((continuous_apply t).comp continuous_subtype_val)
end Topology
end D5.S3.ConceptDynamics.Coding.ActualInSplit

end


set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.InSplitConjugacyDecrease
open EssentialWordRealization FiniteWindowTableCriterion
open OutSplitConjugacyDecrease (Code)
variable {V E W D : Type*} {G : DirectedMultigraph V E} {H : DirectedMultigraph W D}

def splitVertex (c : Code G H) (u : ActualInSplit.Vertex G c.edge) : ActualInSplit.Vertex H id := by
  refine ⟨(c.vertex u.val.1,u.val.2),u.val.2,?_,rfl⟩
  obtain ⟨e,he,hp⟩ := u.property
  change H.target u.val.2 = c.vertex u.val.1
  rw [← hp,c.target,he]
def splitEdge (c : Code G H) (e : ActualInSplit.SplitEdge G c.edge) : ActualInSplit.SplitEdge H id := by
  refine ⟨(e.val.1,c.edge e.val.2),e.val.1,?_,rfl⟩
  obtain ⟨f,hf,hp⟩ := e.property
  change H.target e.val.1 = H.source (c.edge e.val.2)
  rw [← hp,c.target,hf,c.source]
def splitCode (c : Code G H) : Code (ActualInSplit.graph G c.edge) (ActualInSplit.graph H id) where
  vertex := splitVertex c
  edge := splitEdge c
  source e := ActualInSplit.vertex_ext H id (c.source e.val.2) rfl
  target e := ActualInSplit.vertex_ext H id (c.target e.val.2) rfl

section Conjugacy
variable [TopologicalSpace E] [DiscreteTopology E]
variable [TopologicalSpace D] [DiscreteTopology D]
variable (c : Code G H) (P : History G ≃ₜ History H)
variable (hP : ∀ x t, (P x).val t = c.edge (x.val t))

def changed : History (ActualInSplit.graph G c.edge) ≃ₜ History (ActualInSplit.graph H id) :=
  ((ActualInSplit.homeomorph G c.edge).symm.trans P).trans (ActualInSplit.homeomorph H id)
theorem square (x : History G) :
    changed c P (ActualInSplit.lift G c.edge x) = ActualInSplit.lift H id (P x) := by
  change ActualInSplit.lift H id (P (ActualInSplit.forget G c.edge (ActualInSplit.lift G c.edge x))) = _
  rw [ActualInSplit.forget_lift]
include hP in
theorem changed_one_block (z : History (ActualInSplit.graph G c.edge)) (t : ℤ) :
    (changed c P z).val t = splitEdge c (z.val t) := by
  apply ActualInSplit.edge_ext H id
  · exact (hP (ActualInSplit.forget G c.edge z) (t-1)).trans
      (ActualInSplit.label_prev G c.edge z t).symm
  · exact hP (ActualInSplit.forget G c.edge z) t

variable [Fintype V] [Fintype E] [DecidableEq V]
variable [Fintype W] [Fintype D] [DecidableEq W]
variable (hH : Essential H) (M N : ℕ)
variable (Q : LegalWord H ((M+1)+N+1) → E)
variable (hQ : ∀ y t, Q (historyWindow H y (t-((M+1:ℕ):ℤ)) ((M+1)+N+1)) = (P.symm y).val t)

/-- Prepend the actual preceding edge carried by the first split edge. -/
def expand (w : LegalWord (ActualInSplit.graph H id) (M+N+1)) : LegalWord H ((M+1)+N+1) where
  edge j := if hz : j.val = 0 then (w.edge ⟨0,by omega⟩).val.1
    else (w.edge ⟨j.val-1,by have := j.isLt; omega⟩).val.2
  legal j hj := by
    by_cases hz : j.val = 0
    · have hn : ¬ j.val+1 = 0 := by omega
      obtain ⟨f,hf,hid⟩ := (w.edge ⟨0,by omega⟩).property
      change f = _ at hid
      have he : H.target (w.edge ⟨0,by omega⟩).val.1 =
          H.source (w.edge ⟨0,by omega⟩).val.2 :=
        (congrArg H.target hid).symm.trans hf
      simpa only [hz,Nat.zero_add,Nat.sub_self,
        dite_true,dif_neg (show ¬ (1:ℕ)=0 by omega)] using he
    · have hn : ¬ j.val+1 = 0 := by omega
      have hprev : j.val-1+1 = j.val := by omega
      have hs := w.legal ⟨j.val-1,by omega⟩ (by
        change j.val-1+1 < M+N+1
        omega)
      have he : H.target (w.edge ⟨j.val-1,by omega⟩).val.2 =
          H.source (w.edge ⟨j.val-1+1,by omega⟩).val.2 :=
        congrArg (fun v : ActualInSplit.Vertex H id => v.val.1) hs
      simpa only [dif_neg hz,dif_neg hn,Nat.add_sub_cancel,hprev] using he

theorem expand_window (z : History (ActualInSplit.graph H id)) (t : ℤ) :
    expand (H := H) M N
      (historyWindow (ActualInSplit.graph H id) z (t-(M:ℤ)) (M+N+1)) =
    historyWindow H (ActualInSplit.forget H id z) (t-((M+1:ℕ):ℤ)) ((M+1)+N+1) := by
  apply legalWord_ext
  funext j
  by_cases hz : j.val = 0
  · have hp := ActualInSplit.label_prev H id z (t-(M:ℤ))
    have ht : t-(M:ℤ)-1 = t-((M+1:ℕ):ℤ)+(j.val:ℤ) := by omega
    simpa only [expand,historyWindow,dif_pos hz,ActualInSplit.forget,id_eq,
      Int.natCast_zero,add_zero,ht] using hp
  · have ht : t-(M:ℤ)+((j.val-1:ℕ):ℤ) =
        t-((M+1:ℕ):ℤ)+(j.val:ℤ) := by omega
    simp only [expand,historyWindow,dif_neg hz,ActualInSplit.forget,ht]


/-- Total table on every legal split word, including words not given as images. -/
def recover (w : LegalWord (ActualInSplit.graph H id) (M+N+1)) : ActualInSplit.SplitEdge G c.edge :=
  ⟨((w.edge ⟨M,by omega⟩).val.1,Q (expand (H := H) M N w)),
    by
      let u := expand (H := H) M N w
      obtain ⟨y,hy⟩ := every_prescribed_word_has_actual_history H hH u (by omega)
      have hw : historyWindow H y 0 ((M+1)+N+1) = u := by
        apply legalWord_ext
        funext j
        simpa only [historyWindow,zero_add] using hy j
      have hr := hQ y ((M+1:ℕ):ℤ)
      rw [sub_self,hw] at hr
      have hprev : y.val (M:ℤ) = (w.edge ⟨M,by omega⟩).val.1 := by
        by_cases hm : M = 0
        · subst M
          simpa only [u,expand,Int.natCast_zero,eq_self,dite_true] using hy ⟨0,by omega⟩
        · have ha : y.val (M:ℤ) = (w.edge ⟨M-1,by omega⟩).val.2 := by
            simpa only [u,expand,dif_neg hm] using hy ⟨M,by omega⟩
          have hs := congrArg (fun v : ActualInSplit.Vertex H id => v.val.2)
            (w.legal ⟨M-1,by omega⟩ (by
              change M-1+1 < M+N+1
              omega))
          have hidx : M-1+1 = M := by omega
          exact ha.trans (by simpa only [ActualInSplit.graph,ActualInSplit.start,ActualInSplit.finish,id_eq,hidx] using hs)
      refine ⟨(P.symm y).val (M:ℤ),?_,?_⟩
      · rw [hr]
        simpa only [Int.natCast_add,Int.natCast_one] using (P.symm y).property (M:ℤ)
      · have hp := hP (P.symm y) (M:ℤ)
        rw [P.apply_symm_apply] at hp
        exact hp.symm.trans hprev⟩

theorem recover_window (z : History (ActualInSplit.graph H id)) (t : ℤ) :
    recover c P hP hH M N Q hQ
      (historyWindow (ActualInSplit.graph H id) z (t-(M:ℤ)) (M+N+1)) =
      ((changed c P).symm z).val t := by
  apply ActualInSplit.edge_ext G c.edge
  · change (z.val (t-(M:ℤ)+(M:ℤ))).val.1 =
      c.edge ((P.symm (ActualInSplit.forget H id z)).val (t-1))
    have hp := hP (P.symm (ActualInSplit.forget H id z)) (t-1)
    rw [P.apply_symm_apply] at hp
    simpa only [sub_add_cancel,ActualInSplit.forget] using
      (ActualInSplit.label_prev H id z t).trans hp
  · change Q (expand (H := H) M N _) = (P.symm (ActualInSplit.forget H id z)).val t
    rw [expand_window]
    exact hQ (ActualInSplit.forget H id z) t

end Conjugacy
end D5.S3.ConceptDynamics.Coding.InSplitConjugacyDecrease

end


set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.ZeroWindowRelabeling
open EssentialWordRealization FiniteWindowTableCriterion
open OutSplitConjugacyDecrease (Code)
variable {V E W D : Type*} {G : DirectedMultigraph V E} {H : DirectedMultigraph W D}

structure Relabel (G : DirectedMultigraph V E) (H : DirectedMultigraph W D) where
  vertex : V ≃ W
  edge : E ≃ D
  source : ∀ e, H.source (edge e) = vertex (G.source e)
  target : ∀ e, H.target (edge e) = vertex (G.target e)
def Relabel.code (r : Relabel G H) : Code G H :=
  ⟨r.vertex,r.edge,r.source,r.target⟩
def Relabel.history (r : Relabel G H) : History G → History H :=
  OutSplitConjugacyDecrease.mapHistory r.code

def single (G : DirectedMultigraph V E) (e : E) : LegalWord G 1 where
  edge _ := e
  legal i hi := by have := i.isLt; omega

def double (G : DirectedMultigraph V E) (e f : E) (h : G.target e = G.source f) : LegalWord G 2 where
  edge i := if i.val = 0 then e else f
  legal i hi := by
    have hz : i.val = 0 := by omega
    simp only [hz,if_pos rfl,show ¬ (0:ℕ)+1=0 by omega,if_false]
    exact h

section Zero
variable [Fintype V] [Fintype E] [DecidableEq V]
variable [Fintype W] [Fintype D] [DecidableEq W]
variable [TopologicalSpace E] [DiscreteTopology E]
variable [TopologicalSpace D] [DiscreteTopology D]
variable (hG : Essential G) (hH : Essential H)
variable (c : Code G H) (P : History G ≃ₜ History H)
variable (hP : ∀ x t, (P x).val t = c.edge (x.val t))
variable (Q : LegalWord H 1 → E)
variable (hQ : ∀ y t, Q (historyWindow H y t 1) = (P.symm y).val t)

private theorem window_single (y : History H) (t : ℤ) :
    historyWindow H y t 1 = single H (y.val t) := by
  apply legalWord_ext
  funext j
  have hj : j.val = 0 := by have := j.isLt; omega
  simp only [historyWindow,single,hj,Int.natCast_zero,add_zero]

include hG hP hQ in
theorem edge_left (e : E) : Q (single H (c.edge e)) = e := by
  obtain ⟨x,hx⟩ := every_prescribed_word_has_actual_history G hG (single G e) (by omega)
  have he : x.val 0 = e := hx ⟨0,by omega⟩
  have h := hQ (P x) 0
  rw [P.symm_apply_apply,window_single,hP,he] at h
  exact h

include hH hP hQ in
theorem edge_right (d : D) : c.edge (Q (single H d)) = d := by
  obtain ⟨y,hy⟩ := every_prescribed_word_has_actual_history H hH (single H d) (by omega)
  have hd : y.val 0 = d := hy ⟨0,by omega⟩
  have h := hQ y 0
  rw [window_single,hd] at h
  have hp := hP (P.symm y) 0
  rw [P.apply_symm_apply,hd,← h] at hp
  exact hp.symm

def edgeEquiv : E ≃ D where
  toFun := c.edge
  invFun d := Q (single H d)
  left_inv := edge_left hG c P hP Q hQ
  right_inv := edge_right hH c P hP Q hQ

include hG hH hP hQ in
/-- Incoming at v and outgoing at w become a legal H pair if q(v)=q(w).
The zero-window inverse recovers precisely those two ACTUAL G edges. -/
theorem vertex_injective : Function.Injective c.vertex := by
  intro v w hvw
  obtain ⟨e,he⟩ := hG.incoming v
  obtain ⟨f,hf⟩ := hG.outgoing w
  have hpair : H.target (c.edge e) = H.source (c.edge f) := by
    rw [c.target,c.source,he,hf,hvw]
  obtain ⟨y,hy⟩ := every_prescribed_word_has_actual_history H hH
    (double H (c.edge e) (c.edge f) hpair) (by omega)
  have hy0 : y.val 0 = c.edge e := by simpa only [double,eq_self,ite_true,Int.natCast_zero] using hy ⟨0,by omega⟩
  have hy1 : y.val 1 = c.edge f := by
    simpa only [double,show ¬ (1:ℕ)=0 by omega,if_false,Int.natCast_one] using hy ⟨1,by omega⟩
  have hinj := (edgeEquiv hG hH c P hP Q hQ).injective
  have hx0 : (P.symm y).val 0 = e := hinj (by
    have hp := hP (P.symm y) 0
    rw [P.apply_symm_apply,hy0] at hp
    exact hp.symm)
  have hx1 : (P.symm y).val 1 = f := hinj (by
    have hp := hP (P.symm y) 1
    rw [P.apply_symm_apply,hy1] at hp
    exact hp.symm)
  have hs := (P.symm y).property 0
  rw [zero_add,hx0,hx1,he,hf] at hs
  exact hs

include hG hH hP hQ in
theorem vertex_surjective : Function.Surjective c.vertex := by
  intro w
  obtain ⟨d,hd⟩ := hH.outgoing w
  let e := (edgeEquiv hG hH c P hP Q hQ).symm d
  refine ⟨G.source e,?_⟩
  have he : c.edge e = d := (edgeEquiv hG hH c P hP Q hQ).apply_symm_apply d
  exact (c.source e).symm.trans ((congrArg H.source he).trans hd)

/-- Both bijections are derived, with no supplied graph-presentation premise. -/
def relabel : Relabel G H where
  vertex := Equiv.ofBijective c.vertex
    ⟨vertex_injective hG hH c P hP Q hQ,vertex_surjective hG hH c P hP Q hQ⟩
  edge := edgeEquiv hG hH c P hP Q hQ
  source := c.source
  target := c.target

theorem literal_history (x : History G) :
    (relabel hG hH c P hP Q hQ).history x = P x := by
  apply Subtype.ext
  funext t
  exact (hP x t).symm
end Zero
end D5.S3.ConceptDynamics.Coding.ZeroWindowRelabeling

end


set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.TwoSidedFiniteInduction
open EssentialWordRealization FiniteWindowTableCriterion
open OutSplitConjugacyDecrease (Code)
open ZeroWindowRelabeling (Relabel)

/-- Bundling permits induction to quantify over each changed finite graph.
No nonempty-edge hypothesis or default vertex/edge is imposed. -/
structure Presentation where
  V : Type
  E : Type
  finiteV : Fintype V
  finiteE : Fintype E
  eqV : DecidableEq V
  eqE : DecidableEq E
  topology : TopologicalSpace E
  discrete : @DiscreteTopology E topology
  graph : DirectedMultigraph V E
  essential : Essential graph
attribute [instance] Presentation.finiteV Presentation.finiteE
attribute [instance] Presentation.eqV Presentation.eqE Presentation.topology Presentation.discrete

abbrev Hist (F : Presentation) := History F.graph

def out (F T : Presentation) (p : F.E → T.E) : Presentation where
  V := ActualOutSplit.Vertex F.graph p
  E := ActualOutSplit.SplitEdge F.graph p
  finiteV := inferInstance
  finiteE := inferInstance
  eqV := Classical.decEq _
  eqE := Classical.decEq _
  topology := inferInstance
  discrete := inferInstance
  graph := ActualOutSplit.graph F.graph p
  essential := ActualOutSplit.essential F.graph p F.essential

def incoming (F T : Presentation) (p : F.E → T.E) : Presentation where
  V := ActualInSplit.Vertex F.graph p
  E := ActualInSplit.SplitEdge F.graph p
  finiteV := inferInstance
  finiteE := inferInstance
  eqV := Classical.decEq _
  eqE := Classical.decEq _
  topology := inferInstance
  discrete := inferInstance
  graph := ActualInSplit.graph F.graph p
  essential := ActualInSplit.essential F.graph p F.essential

/-- Concrete tower syntax; no constructor accepts a homeomorphism. -/
inductive Tower : Presentation → Presentation → Type 1
  | nil (F : Presentation) : Tower F F
  | outgoing {F K : Presentation} (T : Presentation) (p : F.E → T.E)
      (tail : Tower (out F T p) K) : Tower F K
  | incoming {F K : Presentation} (T : Presentation) (p : F.E → T.E)
      (tail : Tower (TwoSidedFiniteInduction.incoming F T p) K) : Tower F K

namespace Tower
variable {F K : Presentation}
def length : {F K : Presentation} → Tower F K → ℕ
  | _, _, .nil _ => 0
  | _, _, .outgoing _ _ tail => tail.length+1
  | _, _, .incoming _ _ tail => tail.length+1

def toHomeomorph : {F K : Presentation} → Tower F K → (Hist F ≃ₜ Hist K)
  | _, _, .nil _ => Homeomorph.refl _
  | F, _, .outgoing _ p tail =>
      (ActualOutSplit.homeomorph F.graph p).trans tail.toHomeomorph
  | F, _, .incoming _ p tail =>
      (ActualInSplit.homeomorph F.graph p).trans tail.toHomeomorph
end Tower

/-- Data produced by the recursion. The ONLY terminal horizontal map is a
finite vertex-and-edge graph isomorphism. The diagram is literal on all x. -/
structure Terminal (F H : Presentation) (P : Hist F ≃ₜ Hist H) (k : ℕ) where
  source : Presentation
  target : Presentation
  left : Tower F source
  right : Tower H target
  relabel : Relabel source.graph target.graph
  source_depth : left.length = k
  target_depth : right.length = k
  square : ∀ x : Hist F,
    right.toHomeomorph (P x) = relabel.history (left.toHomeomorph x)

/-- Actual strong induction on the carried, not necessarily minimal,
inverse-radius sum. Each recursive call consumes a constructed new table. -/
def reduce : ∀ (k : ℕ) (F H : Presentation) (c : Code F.graph H.graph)
    (P : Hist F ≃ₜ Hist H)
    (hP : ∀ x t, (P x).val t = c.edge (x.val t))
    (M N : ℕ) (Q : LegalWord H.graph (M+N+1) → F.E)
    (hQ : ∀ y t, Q (historyWindow H.graph y (t-(M:ℤ)) (M+N+1)) = (P.symm y).val t),
    M+N = k → Terminal F H P k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro F H c P hP M N Q hQ hk
    cases N with
    | succ n =>
      let F' := out F H c.edge
      let H' := out H H id
      let c' : Code F'.graph H'.graph := OutSplitConjugacyDecrease.splitCode c
      let P' : Hist F' ≃ₜ Hist H' := OutSplitConjugacyDecrease.changed c P
      have hp' : ∀ x t, (P' x).val t = c'.edge (x.val t) :=
        OutSplitConjugacyDecrease.changed_one_block c P hP
      let Q' : LegalWord H'.graph (M+n+1) → F'.E :=
        OutSplitConjugacyDecrease.recover c P hP H.essential M n Q hQ
      have hq' : ∀ y t, Q' (historyWindow H'.graph y (t-(M:ℤ)) (M+n+1)) =
          (P'.symm y).val t :=
        OutSplitConjugacyDecrease.recover_window c P hP H.essential M n Q hQ
      let r := ih (M+n) (by omega) F' H' c' P' hp' M n Q' hq' rfl
      refine ⟨r.source,r.target,.outgoing H c.edge r.left,.outgoing H id r.right,
        r.relabel,?_,?_,?_⟩
      · change r.left.length+1 = k
        rw [r.source_depth]
        omega
      · change r.right.length+1 = k
        rw [r.target_depth]
        omega
      · intro x
        have hs := r.square (ActualOutSplit.lift F.graph c.edge x)
        change r.right.toHomeomorph
          (OutSplitConjugacyDecrease.changed c P (ActualOutSplit.lift F.graph c.edge x)) = _ at hs
        rw [OutSplitConjugacyDecrease.square] at hs
        exact hs
    | zero =>
      cases M with
      | succ m =>
        let F' := incoming F H c.edge
        let H' := incoming H H id
        let c' : Code F'.graph H'.graph := InSplitConjugacyDecrease.splitCode c
        let P' : Hist F' ≃ₜ Hist H' := InSplitConjugacyDecrease.changed c P
        have hp' : ∀ x t, (P' x).val t = c'.edge (x.val t) :=
          InSplitConjugacyDecrease.changed_one_block c P hP
        let Q' : LegalWord H'.graph (m+0+1) → F'.E :=
          InSplitConjugacyDecrease.recover c P hP H.essential m 0 Q hQ
        have hq' : ∀ y t, Q' (historyWindow H'.graph y (t-(m:ℤ)) (m+0+1)) =
            (P'.symm y).val t :=
          InSplitConjugacyDecrease.recover_window c P hP H.essential m 0 Q hQ
        let r := ih (m+0) (by omega) F' H' c' P' hp' m 0 Q' hq' rfl
        refine ⟨r.source,r.target,.incoming H c.edge r.left,.incoming H id r.right,
          r.relabel,?_,?_,?_⟩
        · change r.left.length+1 = k
          rw [r.source_depth]
          omega
        · change r.right.length+1 = k
          rw [r.target_depth]
          omega
        · intro x
          have hs := r.square (ActualInSplit.lift F.graph c.edge x)
          change r.right.toHomeomorph
            (InSplitConjugacyDecrease.changed c P (ActualInSplit.lift F.graph c.edge x)) = _ at hs
          rw [InSplitConjugacyDecrease.square] at hs
          exact hs
      | zero =>
        have hq0 : ∀ y t, Q (historyWindow H.graph y t 1) = (P.symm y).val t := by
          intro y t
          simpa only [Nat.zero_add,Nat.add_zero,Int.natCast_zero,sub_zero] using hQ y t
        let r := ZeroWindowRelabeling.relabel F.essential H.essential c P hP Q hq0
        refine ⟨F,H,.nil F,.nil H,r,?_,?_,?_⟩
        · change 0 = k
          omega
        · change 0 = k
          omega
        · intro x
          exact (ZeroWindowRelabeling.literal_history F.essential H.essential c P hP Q hq0 x).symm

end D5.S3.ConceptDynamics.Coding.TwoSidedFiniteInduction

end
