/- GID: D5/S3/ConceptDynamics/Coding/FullOutSplitWordIdentification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FullOutSplitWordIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite full outgoing splits identify with legal-word graphs at every depth. -/

import D5.S3.ConceptDynamics.Coding.TwoSidedFiniteInduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.FullOutSplitWordIdentification
open EssentialWordRealization FiniteWindowTableCriterion
open ZeroWindowRelabeling (Relabel single)

universe u
variable {V E : Type u} {W D : Type*} (G : DirectedMultigraph V E)

def «prefix» {n : ℕ} (w : LegalWord G (n+1)) : LegalWord G n :=
  sliceWord G w 0 n (by omega)

def suffix {n : ℕ} (w : LegalWord G (n+1)) : LegalWord G n :=
  sliceWord G w 1 n (by omega)

/-- Only positive depths have word vertices. -/
def BlockVertex : ℕ → Type _
  | 0 => V
  | n+1 => LegalWord G (n+1)

def blockGraph : (n : ℕ) → DirectedMultigraph (BlockVertex G n) (LegalWord G (n+1))
  | 0 => ⟨fun w => G.source (w.edge ⟨0,by omega⟩),
      fun w => G.target (w.edge ⟨0,by omega⟩)⟩
  | _+1 => ⟨«prefix» G,suffix G⟩

theorem consecutive (n : ℕ) (w : LegalWord G (n+2)) :
    (blockGraph G n).target («prefix» G w) =
      (blockGraph G n).source (suffix G w) := by
  cases n with
  | zero => exact w.legal ⟨0,by omega⟩ (by dsimp; omega)
  | succ n =>
      apply legalWord_ext
      funext j
      simp only [blockGraph,«prefix»,suffix,sliceWord,Nat.zero_add]

private theorem first_seam (n : ℕ) (u v : LegalWord G (n+1))
    (h : (blockGraph G n).target u = (blockGraph G n).source v) :
    G.target (u.edge ⟨0,by omega⟩) = G.source (v.edge ⟨0,by omega⟩) := by
  cases n with
  | zero => exact h
  | succ n =>
      have ho := congrArg (fun w : LegalWord G (n+1) => w.edge ⟨0,by omega⟩) h
      change u.edge ⟨1,by omega⟩ = v.edge ⟨0,by omega⟩ at ho
      exact (u.legal ⟨0,by omega⟩ (by dsimp; omega)).trans (congrArg G.source ho)

/-- Prepend the first edge of u to v. Its seam is proved from actual
block endpoints, including the distinct depth-zero endpoint condition. -/
def join (n : ℕ) (u v : LegalWord G (n+1))
    (h : (blockGraph G n).target u = (blockGraph G n).source v) :
    LegalWord G (n+2) where
  edge j := if hz : j.val = 0 then u.edge ⟨0,by omega⟩
    else v.edge ⟨j.val-1,by omega⟩
  legal j hj := by
    by_cases hz : j.val = 0
    · simpa [hz] using first_seam G n u v h
    · have hn : ¬ j.val+1=0 := by omega
      have hk : (j.val-1)+1 < n+1 := by omega
      simpa [hz,hn,show j.val-1+1=j.val by omega] using
        v.legal ⟨j.val-1,by omega⟩ hk

theorem prefix_join (n : ℕ) (u v : LegalWord G (n+1))
    (h : (blockGraph G n).target u = (blockGraph G n).source v) :
    «prefix» G (join G n u v h) = u := by
  apply legalWord_ext
  funext j
  by_cases hz : j.val = 0
  · have hj0 : j = 0 := Fin.ext hz
    subst j
    rfl
  · have hj0 : j ≠ 0 := fun he => hz (congrArg Fin.val he)
    cases n with
    | zero => have := j.isLt; omega
    | succ n =>
        have ho := congrArg (fun w : LegalWord G (n+1) =>
          w.edge ⟨j.val-1,by omega⟩) h
        change u.edge ⟨1+(j.val-1),_⟩ = v.edge ⟨0+(j.val-1),_⟩ at ho
        have hj : 1+(j.val-1)=j.val := by omega
        simpa [«prefix»,sliceWord,join,hz,hj,hj0] using ho.symm

theorem suffix_join (n : ℕ) (u v : LegalWord G (n+1))
    (h : (blockGraph G n).target u = (blockGraph G n).source v) :
    suffix G (join G n u v h) = v := by
  apply legalWord_ext
  funext j
  have hz : ¬ 1+j.val=0 := by omega
  have hj : 1+j.val-1=j.val := by omega
  simp [suffix,sliceWord,join,hz,hj]

theorem join_prefix_suffix (n : ℕ) (w : LegalWord G (n+2)) :
    join G n («prefix» G w) (suffix G w) (consecutive G n w) = w := by
  apply legalWord_ext
  funext j
  by_cases hz : j.val=0
  · have hj0 : j = 0 := Fin.ext hz
    subst j
    rfl
  · have hj : 1+(j.val-1)=j.val := by omega
    have hj0 : j ≠ 0 := fun he => hz (congrArg Fin.val he)
    simp [join,hz,suffix,sliceWord,hj,hj0]

/-- The finite depth-zero identification changes no original vertex. -/
def zero : Relabel G (blockGraph G 0) where
  vertex := Equiv.refl V
  edge :=
    { toFun := single G
      invFun := fun w => w.edge ⟨0,by omega⟩
      left_inv := fun _ => rfl
      right_inv := by
        intro w
        apply legalWord_ext
        funext j
        have hj : j.val=0 := by have := j.isLt; omega
        apply congrArg w.edge
        exact Fin.ext hj.symm }
  source _ := rfl
  target _ := rfl

variable {G} {H : DirectedMultigraph W D} {n : ℕ}
variable (r : Relabel H (blockGraph G n))

private theorem full_vertex_source (u : ActualOutSplit.Vertex H id) :
    H.source u.val.2 = u.val.1 := by
  obtain ⟨e,hs,he⟩ := u.property
  change e = u.val.2 at he
  exact (congrArg H.source he).symm.trans hs

private theorem full_edge_seam (e : ActualOutSplit.SplitEdge H id) :
    H.target e.val.1 = H.source e.val.2 := by
  obtain ⟨f,hs,hf⟩ := e.property
  change f = e.val.2 at hf
  exact hs.symm.trans (congrArg H.source hf)

private theorem transported_seam (e : ActualOutSplit.SplitEdge H id) :
    (blockGraph G n).target (r.edge e.val.1) =
      (blockGraph G n).source (r.edge e.val.2) := by
  rw [r.target,r.source,full_edge_seam e]

private def expandVertex (w : LegalWord G (n+1)) : ActualOutSplit.Vertex H id :=
  ActualOutSplit.start H id (r.edge.symm w)

private def expandEdge (w : LegalWord G (n+2)) : ActualOutSplit.SplitEdge H id :=
  ⟨(r.edge.symm («prefix» G w),r.edge.symm (suffix G w)),
    r.edge.symm (suffix G w),by
      apply r.vertex.injective
      rw [← r.source,← r.target,r.edge.apply_symm_apply,r.edge.apply_symm_apply]
      exact (consecutive G n w).symm,rfl⟩

/-- A local finite construction, used only with the recursively constructed
r below. Neither this nor the tower accepts any history homeomorphism. -/
def step : Relabel (ActualOutSplit.graph H id) (blockGraph G (n+1)) where
  vertex :=
    { toFun := fun u => r.edge u.val.2
      invFun := expandVertex r
      left_inv := by
        intro u
        apply ActualOutSplit.vertex_ext
        · change H.source (r.edge.symm (r.edge u.val.2)) = u.val.1
          rw [r.edge.symm_apply_apply]
          exact full_vertex_source u
        · exact r.edge.symm_apply_apply _
      right_inv := fun w => r.edge.apply_symm_apply w }
  edge :=
    { toFun := fun e => join G n (r.edge e.val.1) (r.edge e.val.2) (transported_seam r e)
      invFun := expandEdge r
      left_inv := by
        intro e
        apply ActualOutSplit.edge_ext
        · change r.edge.symm («prefix» G (join G n _ _ _)) = e.val.1
          rw [prefix_join,r.edge.symm_apply_apply]
        · change r.edge.symm (suffix G (join G n _ _ _)) = e.val.2
          rw [suffix_join,r.edge.symm_apply_apply]
      right_inv := by
        intro w
        change join G n (r.edge (r.edge.symm («prefix» G w)))
          (r.edge (r.edge.symm (suffix G w))) _ = w
        simp only [r.edge.apply_symm_apply]
        exact join_prefix_suffix G n w }
  source e := prefix_join G n _ _ (transported_seam r e)
  target e := suffix_join G n _ _ (transported_seam r e)

end D5.S3.ConceptDynamics.Coding.FullOutSplitWordIdentification

namespace D5.S3.ConceptDynamics.Coding.RepeatedFullOutSplit
open EssentialWordRealization FiniteWindowTableCriterion
open ZeroWindowRelabeling (Relabel)
open TwoSidedFiniteInduction (Presentation Hist Tower out)
open FullOutSplitWordIdentification

/-- The zero stage is literally the supplied finite essential graph. -/
def stage (F : Presentation) : ℕ → Presentation
  | 0 => F
  | n+1 => out (stage F n) (stage F n) id

/-- Constructed finite bijections at every stage; no relabeling premise. -/
def identification (F : Presentation) : (n : ℕ) →
    Relabel (stage F n).graph (blockGraph F.graph n)
  | 0 => zero F.graph
  | n+1 => step (identification F n)

/-- This composite is defined from the actual repeated lifts, before any
comparison with the response graph or its existing history homeomorphism. -/
def repeated (F : Presentation) : (n : ℕ) → Hist F ≃ₜ Hist (stage F n)
  | 0 => Homeomorph.refl _
  | n+1 => (repeated F n).trans (ActualOutSplit.homeomorph (stage F n).graph id)

theorem flatten_window (F : Presentation) (n : ℕ) (x : Hist F) (t : ℤ) :
    (identification F n).edge ((repeated F n x).val t) =
      historyWindow F.graph x t (n+1) := by
  induction n generalizing t with
  | zero =>
      apply legalWord_ext
      funext j
      have hj : j.val=0 := by have := j.isLt; omega
      change x.val t = x.val (t+(j.val:ℤ))
      simp only [hj,Int.natCast_zero,add_zero]
  | succ n ih =>
      change join F.graph n
        ((identification F n).edge ((repeated F n x).val t))
        ((identification F n).edge ((repeated F n x).val (t+1)))
        (by
          exact ((identification F n).target _).trans
            ((congrArg (identification F n).vertex ((repeated F n x).property t)).trans
              ((identification F n).source _).symm)) = _
      simp only [ih t,ih (t+1)]
      apply legalWord_ext
      funext j
      by_cases hz : j.val=0
      · have hj0 : j = 0 := Fin.ext hz
        subst j
        simp [join,historyWindow]
      · simp only [join,hz,dif_neg,historyWindow]
        apply congrArg x.val
        omega

/-- Append one actual full split to the already existing tower syntax.
This is a local consumed recursion, not an additional tower framework. -/
def appendFull {F K : Presentation} : Tower F K → Tower F (out K K id)
  | .nil _ => .outgoing _ id (.nil _)
  | .outgoing T p tail => .outgoing T p (appendFull tail)
  | .incoming T p tail => .incoming T p (appendFull tail)

private theorem appendFull_length {F K : Presentation} (A : Tower F K) :
    (appendFull A).length = A.length+1 := by
  induction A with
  | nil F => rfl
  | outgoing T p tail ih =>
      change (appendFull tail).length+1 = (tail.length+1)+1
      rw [ih]
  | incoming T p tail ih =>
      change (appendFull tail).length+1 = (tail.length+1)+1
      rw [ih]

private theorem appendFull_apply {F K : Presentation} (A : Tower F K) (x : Hist F) :
    (appendFull A).toHomeomorph x =
      ActualOutSplit.lift K.graph id (A.toHomeomorph x) := by
  induction A with
  | nil F => rfl
  | outgoing T p tail ih => exact ih _
  | incoming T p tail ih => exact ih _

/-- Actual tower data, compatible with the predecessor finite split tower. -/
def tower (F : Presentation) : (n : ℕ) → Tower F (stage F n)
  | 0 => .nil F
  | n+1 => appendFull (tower F n)

theorem tower_length (F : Presentation) (n : ℕ) : (tower F n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (appendFull (tower F n)).length = n+1
      rw [appendFull_length,ih]

theorem tower_apply (F : Presentation) (n : ℕ) (x : Hist F) :
    (tower F n).toHomeomorph x = repeated F n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (appendFull (tower F n)).toHomeomorph x = _
      rw [appendFull_apply,ih] <;> rfl

end D5.S3.ConceptDynamics.Coding.RepeatedFullOutSplit
