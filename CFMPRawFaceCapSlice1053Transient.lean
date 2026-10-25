import D5.S3.Geometry.Hyperideal.EdgeStarTransitions
import D5.S3.Geometry.Gluing.ActualLinkAffineFan
import Batteries.Tactic.OpenPrivate
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology

namespace D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate

open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing faceEdge edgeVertices)
open D5.S3.Geometry.Gluing.ActualLinkAffineFan (TruncatedTetrahedron TruncatedPoint alpha)
open private coordinate_le_one cap_unique from D5.S3.Geometry.Gluing.ActualLinkAffineFan

variable {T : Type*}

-- All declarations in this file are transient, pending exact compilation and admission.
-- No group-model presentation or replacement face table is an input.
def chi (f : Fin 4) : Equiv.Perm (Fin 3) :=
  if f = 0 then 1 else Equiv.swap 0 2

def frame (f : Fin 4) : Fin 4 ≃ Option (Fin 3) :=
  (finSuccEquiv' f).trans (Equiv.optionCongr (chi f))

def oppositeVertex (f : Fin 4) (n : Fin 3) : Fin 4 :=
  (frame f).symm (some n)

-- This extension is derived from the actual edge-slot map, without extra data.
def sigma (P : RawFacePairing T) (x : T × Fin 4) : Equiv.Perm (Fin 4) :=
  (frame x.2).trans ((Equiv.optionCongr (P.faceMap x)).trans
    (frame (P.facePair x).2).symm)

private theorem frame_at (f : Fin 4) : frame f f = none := by
  change (Equiv.optionCongr (chi f)) ((finSuccEquiv' f) f) = none
  exact congrArg (Equiv.optionCongr (chi f)) (finSuccEquiv'_at f)

private theorem frame_none (f : Fin 4) : (frame f).symm none = f := by
  apply (frame f).injective
  simp [frame_at]

private theorem sigma_face (P : RawFacePairing T) (x : T × Fin 4) :
    sigma P x x.2 = (P.facePair x).2 := by
  change (frame (P.facePair x).2).symm
    ((Equiv.optionCongr (P.faceMap x)) (frame x.2 x.2)) = _
  rw [frame_at]
  exact frame_none _

private theorem sigma_opposite (P : RawFacePairing T) (x : T × Fin 4) (n : Fin 3) :
    sigma P x (oppositeVertex x.2 n) =
      oppositeVertex (P.facePair x).2 (P.faceMap x n) := by
  simp [sigma, oppositeVertex]

private theorem paired_twice (P : RawFacePairing T) (x : T × Fin 4) :
    P.facePair (P.facePair x) = x := by
  have h := congrArg (fun e : Equiv.Perm (T × Fin 4) => e x) P.pairInvolutive
  simpa using h

private theorem sigma_inverse (P : RawFacePairing T) (x : T × Fin 4) :
    sigma P (P.facePair x) = (sigma P x).symm := by
  have hm : P.faceMap (P.facePair x) = (P.faceMap x).symm := by
    apply Equiv.ext
    intro n
    have h := P.mapInverse x ((P.faceMap x).symm n)
    simpa using h
  ext i
  simp [sigma, paired_twice P x, hm]

private theorem endpoint_incidence (f : Fin 4) (n : Fin 3) (v : Fin 4) :
    (v = (edgeVertices (faceEdge f n)).1 ∨
      v = (edgeVertices (faceEdge f n)).2) ↔
      ∃ r : Fin 3, r ≠ n ∧ oppositeVertex f r = v := by
  fin_cases f <;> fin_cases n <;> fin_cases v <;> decide

-- The derived permutation transports the endpoints of each original edge slot.
private theorem sigma_endpoint_iff (P : RawFacePairing T) (x : T × Fin 4)
    (n : Fin 3) (v : Fin 4) :
    (v = (edgeVertices (faceEdge x.2 n)).1 ∨
      v = (edgeVertices (faceEdge x.2 n)).2) ↔
    (sigma P x v = (edgeVertices
      (faceEdge (P.facePair x).2 (P.faceMap x n))).1 ∨
      sigma P x v = (edgeVertices
      (faceEdge (P.facePair x).2 (P.faceMap x n))).2) := by
  rw [endpoint_incidence, endpoint_incidence]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨P.faceMap x r, (P.faceMap x).injective.ne hr,
      (sigma_opposite P x r).symm⟩
  · rintro ⟨r, hr, he⟩
    refine ⟨(P.faceMap x).symm r, ?_, ?_⟩
    · intro h
      apply hr
      exact ((P.faceMap x).apply_symm_apply r).symm.trans (congrArg (P.faceMap x) h)
    · apply (sigma P x).injective
      rw [sigma_opposite, (P.faceMap x).apply_symm_apply]
      exact he

-- The existing generic corner supplier uses increasing face-vertex slots.
-- Conjugate the actual edge-slot map into that exact frame, retaining the same p.
private theorem chi_apply_apply (f : Fin 4) (n : Fin 3) : chi f (chi f n) = n := by
  by_cases h : f = 0 <;> simp [chi,h]

private theorem frame_faceVertex (f : Fin 4) (r : Fin 3) :
    frame f (D5.S3.Geometry.Hyperideal.ActualCornerTransport.faceVertex f r) =
      some (chi f r) := by
  fin_cases f <;> fin_cases r <;> decide

def cornerPairing (P : RawFacePairing T) :
    D5.S3.Geometry.Hyperideal.ActualCornerTransport.Pairing T where
  p := P.facePair
  involutive := paired_twice P
  fixedPointFree := P.pairFixedFree
  sigma x := (chi x.2).trans
    ((P.faceMap x).trans (chi (P.facePair x).2))
  compatible := by
    intro x r
    change chi (P.facePair (P.facePair x)).2
      (P.faceMap (P.facePair x)
        (chi (P.facePair x).2
          (chi (P.facePair x).2 (P.faceMap x (chi x.2 r))))) = r
    rw [paired_twice P x,chi_apply_apply,P.mapInverse,chi_apply_apply]

private theorem sigma_faceVertex (P : RawFacePairing T) (x : T × Fin 4)
    (r : Fin 3) :
    sigma P x (D5.S3.Geometry.Hyperideal.ActualCornerTransport.faceVertex x.2 r) =
      D5.S3.Geometry.Hyperideal.ActualCornerTransport.faceVertex (P.facePair x).2
        ((cornerPairing P).sigma x r) := by
  apply (frame (P.facePair x).2).injective
  change (frame (P.facePair x).2)
    ((frame (P.facePair x).2).symm
      ((Equiv.optionCongr (P.faceMap x))
        (frame x.2
          (D5.S3.Geometry.Hyperideal.ActualCornerTransport.faceVertex x.2 r)))) = _
  simp only [Equiv.apply_symm_apply,frame_faceVertex]
  simp [cornerPairing,chi_apply_apply]

private theorem face_edge_frame (f : Fin 4) (r : Fin 3) :
    D5.S3.Geometry.Hyperideal.ActualCornerTransport.faceEdge f r =
      faceEdge f (chi f r) := by
  fin_cases f <;> fin_cases r <;> decide

-- The corner supplier retains the exact original edge generator under the frame.
private theorem corner_edge_step_iff (P : RawFacePairing T) (i j : T × Fin 6) :
    D5.S3.Geometry.Hyperideal.ActualCornerTransport.edgeRel (cornerPairing P) i j ↔
      P.edgeStep i j := by
  constructor
  · rintro ⟨⟨x,r⟩,hi,hj⟩
    refine ⟨x,chi x.2 r,?_,?_⟩
    · simpa [D5.S3.Geometry.Hyperideal.ActualCornerTransport.edge,face_edge_frame]
        using hi.symm
    · simpa [D5.S3.Geometry.Hyperideal.ActualCornerTransport.edge,
        D5.S3.Geometry.Hyperideal.ActualCornerTransport.J,
        cornerPairing,face_edge_frame,chi_apply_apply] using hj.symm
  · rintro ⟨x,n,hi,hj⟩
    refine ⟨(x,chi x.2 n),?_,?_⟩
    · simpa [D5.S3.Geometry.Hyperideal.ActualCornerTransport.edge,
        face_edge_frame,chi_apply_apply] using hi.symm
    · simpa [D5.S3.Geometry.Hyperideal.ActualCornerTransport.edge,
        D5.S3.Geometry.Hyperideal.ActualCornerTransport.J,
        cornerPairing,face_edge_frame,chi_apply_apply] using hj.symm

abbrev Vertex (P : RawFacePairing T) :=
  D5.S3.Geometry.Hyperideal.ActualCornerTransport.Vertex (cornerPairing P)

abbrev label (P : RawFacePairing T) (a : T × Fin 4) : Vertex P :=
  D5.S3.Geometry.Hyperideal.ActualCornerTransport.label (cornerPairing P) a

abbrev Raw (T : Type*) := (T × Fin 4) × (Fin 4 → ℝ)

def Carrier (P : RawFacePairing T) (ν : Vertex P) : Set (Raw T) :=
  {x | x.2 x.1.2 = 0 ∧ (∀ i, 0 ≤ x.2 i) ∧
    (∑ i, x.2 i) = 1 ∧ label P x.1 = ν}

abbrev Point (P : RawFacePairing T) (ν : Vertex P) := ↥(Carrier P ν)

def move (P : RawFacePairing T) (f : Fin 4) (x : Raw T) : Raw T :=
  (((P.facePair (x.1.1,f)).1, sigma P (x.1.1,f) x.1.2),
    fun i => x.2 ((sigma P (x.1.1,f)).symm i))

private theorem move_carrier (P : RawFacePairing T) {ν : Vertex P}
    (x : Point P ν) (f : Fin 4) (hfj : f ≠ x.val.1.2) :
    move P f x.val ∈ Carrier P ν := by
  obtain ⟨hj,hn,hs,hν⟩ := x.property
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [move, Equiv.symm_apply_apply] using hj
  · intro i
    exact hn _
  · exact ((sigma P (x.val.1.1,f)).symm.sum_comp x.val.2).trans hs
  · obtain ⟨r,hr⟩ : ∃ r : Fin 3,
        D5.S3.Geometry.Hyperideal.ActualCornerTransport.faceVertex f r = x.val.1.2 := by
      generalize x.val.1.2 = j at hfj ⊢
      fin_cases f <;> fin_cases j <;>
        simp_all [D5.S3.Geometry.Hyperideal.ActualCornerTransport.faceVertex,
          Fin.exists_fin_succ]
    have hcorner :
        D5.S3.Geometry.Hyperideal.ActualCornerTransport.cornerRel (cornerPairing P)
          x.val.1 (move P f x.val).1 := by
      refine ⟨((x.val.1.1,f),r),?_,?_⟩
      · exact Prod.ext rfl hr
      · change
          ((P.facePair (x.val.1.1,f)).1,
            D5.S3.Geometry.Hyperideal.ActualCornerTransport.faceVertex
              (P.facePair (x.val.1.1,f)).2
              ((cornerPairing P).sigma (x.val.1.1,f) r)) =
          ((P.facePair (x.val.1.1,f)).1, sigma P (x.val.1.1,f) x.val.1.2)
        apply Prod.ext
        · rfl
        · rw [← sigma_faceVertex,hr]
    have h : label P x.val.1 = label P (move P f x.val).1 :=
      Quotient.sound (Relation.EqvGen.rel _ _ hcorner)
    exact h.symm.trans hν

def pairedPoint (P : RawFacePairing T) {ν : Vertex P}
    (x : Point P ν) (f : Fin 4) (hfj : f ≠ x.val.1.2) : Point P ν :=
  ⟨move P f x.val,move_carrier P x f hfj⟩

def Step (P : RawFacePairing T) {ν : Vertex P} (x y : Point P ν) : Prop :=
  ∃ f : Fin 4, f ≠ x.val.1.2 ∧ x.val.2 f = 0 ∧ y.val = move P f x.val

abbrev Related (P : RawFacePairing T) {ν : Vertex P} :=
  Relation.EqvGen (Step P (ν := ν))

-- TruncatedTetrahedron and TruncatedPoint are the existing unchanged carriers.
def truncatedMove (P : RawFacePairing T) (f : Fin 4) (a : TruncatedPoint T) :
    TruncatedPoint T :=
  ((P.facePair (a.1,f)).1, ⟨fun i => a.2.val ((sigma P (a.1,f)).symm i),
    (fun i => a.2.property.1 _),
    ((sigma P (a.1,f)).symm.sum_comp a.2.val).trans a.2.property.2⟩)

def TruncatedStep (P : RawFacePairing T) (a b : TruncatedPoint T) : Prop :=
  ∃ f : Fin 4, a.2.val f = 0 ∧ b = truncatedMove P f a

def Slice (P : RawFacePairing T) (ν : Vertex P) : Set (TruncatedPoint T) :=
  {a | ∃ j : Fin 4, a.2.val j = 3/4 ∧ label P (a.1,j) = ν}

private theorem alpha_mem (P : RawFacePairing T) {ν : Vertex P}
    (p : Point P ν) :
    (∀ i, 0 ≤ alpha p.val.1.2 p.val.2 i ∧ alpha p.val.1.2 p.val.2 i ≤ 3/4) ∧
    (∑ i, alpha p.val.1.2 p.val.2 i) = 1 := by
  obtain ⟨hj,hn,hs,_⟩ := p.property
  constructor
  · intro i
    have hi := hn i
    have hu := coordinate_le_one hn hs i
    by_cases he : i = p.val.1.2
    · subst i; norm_num [alpha,hj]
    · simp only [alpha,if_neg he,zero_add]; constructor <;> linarith
  · simp only [alpha,Finset.sum_add_distrib]
    rw [← Finset.sum_div,hs]
    norm_num
/-- Literal affine map from the entire original corner triangle into its cap. -/
def toTruncation (P : RawFacePairing T) {ν : Vertex P}
    (p : Point P ν) : TruncatedPoint T :=
  (p.val.1.1,⟨alpha p.val.1.2 p.val.2,alpha_mem P p⟩)
private theorem toTruncation_mem (P : RawFacePairing T) {ν : Vertex P}
    (p : Point P ν) : toTruncation P p ∈ Slice P ν :=
  ⟨p.val.1.2,by simp [toTruncation,alpha,p.property.1],p.property.2.2.2⟩
private theorem toTruncation_injective (P : RawFacePairing T) {ν : Vertex P} :
    Function.Injective (toTruncation P (ν := ν)) := by
  intro p q h
  have ht := congrArg Prod.fst h
  have ha := congrArg (fun z : TruncatedPoint T => z.2.val) h
  have hj : p.val.1.2 = q.val.1.2 := by
    apply cap_unique (toTruncation P p)
      (show (toTruncation P p).2.val p.val.1.2 = 3/4 by
        simp [toTruncation,alpha,p.property.1])
    rw [h]
    simp [toTruncation,alpha,q.property.1]
  apply Subtype.ext
  apply Prod.ext (Prod.ext ht hj)
  funext i
  have hh := congrFun ha i
  change alpha p.val.1.2 p.val.2 i = alpha q.val.1.2 q.val.2 i at hh
  simp only [alpha,hj] at hh
  linarith
private theorem cap_preimage (P : RawFacePairing T) (a : TruncatedPoint T) (j : Fin 4)
    (hj : a.2.val j = 3/4) :
    ∃ p : Point P (label P (a.1,j)), toTruncation P p = a := by
  let b : Fin 4 → ℝ := fun i => if i = j then 0 else 4 * a.2.val i
  have hb : (∑ i, b i) = 1 := by
    have hs := a.2.property.2
    fin_cases j <;> simp [b,Fin.sum_univ_succ] at * <;> linarith
  let p : Point P (label P (a.1,j)) :=
    ⟨((a.1,j),b),by
      refine ⟨by simp [b],?_,hb,rfl⟩
      intro i
      dsimp only [b]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (by norm_num) (a.2.property.1 i).1⟩
  refine ⟨p,Prod.ext rfl (Subtype.ext ?_)⟩
  funext i
  change alpha j b i = a.2.val i
  by_cases hi : i = j
  · subst i; simp [alpha,b,hj]
  · simp [alpha,b,hi]
/-- Both full carriers, including every boundary tie, correspond under alpha. -/
theorem actual_slice_carriers (P : RawFacePairing T) (ν : Vertex P) :
    Function.Bijective (fun p : Point P ν =>
      (⟨toTruncation P p,toTruncation_mem P p⟩ : ↥(Slice P ν))) := by
  constructor
  · intro p q h
    exact toTruncation_injective P (congrArg Subtype.val h)
  · rintro ⟨a,j,hj,hν⟩
    obtain ⟨p,hp⟩ := cap_preimage P a j hj
    subst ν
    exact ⟨p,Subtype.ext hp⟩
private theorem alpha_paired (P : RawFacePairing T) {ν : Vertex P}
    (p : Point P ν) (f : Fin 4) (hf : f ≠ p.val.1.2) :
    toTruncation P (pairedPoint P p f hf) = truncatedMove P f (toTruncation P p) := by
  apply Prod.ext
  · rfl
  apply Subtype.ext
  funext i
  change alpha (sigma P (p.val.1.1,f) p.val.1.2) (fun k => p.val.2 ((sigma P (p.val.1.1,f)).symm k)) i =
    alpha p.val.1.2 p.val.2 ((sigma P (p.val.1.1,f)).symm i)
  simp only [alpha, Equiv.symm_apply_eq]
private theorem truncated_step_lift (P : RawFacePairing T) {ν : Vertex P}
    (p : Point P ν) {a : TruncatedPoint T} (h : TruncatedStep P (toTruncation P p) a) :
    ∃ q : Point P ν, Step P p q ∧ toTruncation P q = a := by
  obtain ⟨f,hf,rfl⟩ := h
  have hfj : f ≠ p.val.1.2 := by
    intro he; subst f
    change alpha _ _ _ = 0 at hf
    simp [alpha,p.property.1] at hf
  have hz : p.val.2 f = 0 := by
    change alpha _ _ _ = 0 at hf
    simp only [alpha,if_neg hfj,zero_add] at hf
    linarith
  exact ⟨pairedPoint P p f hfj,⟨f,hfj,hz,rfl⟩,alpha_paired P p f hfj⟩
/-- The exact guarded original face generators correspond in both directions. -/
theorem actual_slice_step_iff (P : RawFacePairing T) {ν : Vertex P}
    (p q : Point P ν) :
    Step P p q ↔ TruncatedStep P (toTruncation P p) (toTruncation P q) := by
  constructor
  · rintro ⟨f,hfj,hf,hq⟩
    have he : q = pairedPoint P p f hfj := Subtype.ext hq
    subst q
    refine ⟨f,?_,alpha_paired P p f hfj⟩
    change alpha _ _ _ = 0
    simp [alpha,hfj,hf]
  · intro h
    obtain ⟨z,hz,he⟩ := truncated_step_lift P p h
    exact (toTruncation_injective P he) ▸ hz
private theorem slice_labels_unique (P : RawFacePairing T) {a : TruncatedPoint T}
    {ν μ : Vertex P} (hν : a ∈ Slice P ν) (hμ : a ∈ Slice P μ) :
    ν = μ := by
  obtain ⟨j,hj,hν⟩ := hν
  obtain ⟨k,hk,hμ⟩ := hμ
  have he := cap_unique a hj hk
  subst k
  exact hν.symm.trans hμ
private theorem slice_step_invariant (P : RawFacePairing T) (ν : Vertex P)
    {a b : TruncatedPoint T} (h : TruncatedStep P a b) :
    a ∈ Slice P ν ↔ b ∈ Slice P ν := by
  constructor
  · intro ha
    obtain ⟨p,hp⟩ := (actual_slice_carriers P ν).2 ⟨a,ha⟩
    have hp' : toTruncation P p = a := congrArg Subtype.val hp
    rw [← hp'] at h
    obtain ⟨q,_,hq⟩ := truncated_step_lift P p h
    rw [← hq]
    exact toTruncation_mem P q
  · intro hb
    obtain ⟨f,hf,hmove⟩ := h
    obtain ⟨j,hj,hν⟩ := hb
    have hc : a.2.val ((sigma P (a.1,f)).symm j) = 3/4 := by
      rw [hmove] at hj
      exact hj
    obtain ⟨p,hp⟩ := cap_preimage P a ((sigma P (a.1,f)).symm j) hc
    have hh : TruncatedStep P (toTruncation P p) b := by
      rw [hp]; exact ⟨f,hf,hmove⟩
    obtain ⟨q,_,hq⟩ := truncated_step_lift P p hh
    have hb' := toTruncation_mem P q
    rw [hq] at hb'
    have he := slice_labels_unique P hb' ⟨j,hj,hν⟩
    exact ⟨(sigma P (a.1,f)).symm j,hc,he⟩
private theorem slice_chain_invariant (P : RawFacePairing T) (ν : Vertex P)
    {a b : TruncatedPoint T} (h : Relation.EqvGen (TruncatedStep P) a b) :
    a ∈ Slice P ν ↔ b ∈ Slice P ν := by
  induction h with
  | rel a b h => exact slice_step_invariant P ν h
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
/-- Reflection uses the complete ambient face closure: every intermediate
representative remains in the same original cap component. -/
theorem actual_slice_eqvgen_iff (P : RawFacePairing T) {ν : Vertex P}
    (p q : Point P ν) : Related P p q ↔
    Relation.EqvGen (TruncatedStep P) (toTruncation P p) (toTruncation P q) := by
  constructor
  · intro h
    induction h with
    | rel p q h => exact Relation.EqvGen.rel _ _ ((actual_slice_step_iff P p q).mp h)
    | refl p => exact Relation.EqvGen.refl _
    | symm p q _ ih => exact ih.symm
    | trans p q r _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans (r := TruncatedStep P)
        (toTruncation P p) (toTruncation P q) (toTruncation P r) ih₁ ih₂
  · intro h
    let e := Equiv.ofBijective (fun p : Point P ν =>
      (⟨toTruncation P p,toTruncation_mem P p⟩ : ↥(Slice P ν)))
      (actual_slice_carriers P ν)
    have lift : ∀ {a b : TruncatedPoint T}, Relation.EqvGen (TruncatedStep P) a b →
        ∀ (ha : a ∈ Slice P ν) (hb : b ∈ Slice P ν),
        Related P (e.symm ⟨a,ha⟩) (e.symm ⟨b,hb⟩) := by
      intro a b hab
      induction hab with
      | rel a b hab =>
        intro ha hb
        apply Relation.EqvGen.rel
        apply (actual_slice_step_iff P _ _).mpr
        have he (z : ↥(Slice P ν)) : toTruncation P (e.symm z) = z.val :=
          congrArg Subtype.val (e.apply_symm_apply z)
        rw [he,he]
        exact hab
      | refl a => exact fun _ _ => Relation.EqvGen.refl _
      | symm a b _ ih => exact fun ha hb => (ih hb ha).symm
      | trans a b c hab _ ih₁ ih₂ =>
        intro ha hc
        have hb := (slice_chain_invariant P ν hab).mp ha
        exact Relation.EqvGen.trans _ _ _ (ih₁ ha hb) (ih₂ hb hc)
    have hh := lift h (toTruncation_mem P p) (toTruncation_mem P q)
    change Related P (e.symm (e p)) (e.symm (e q)) at hh
    simpa only [e.symm_apply_apply] using hh
section Topology
variable [TopologicalSpace T] [DiscreteTopology T]
private theorem continuous_toTruncation (P : RawFacePairing T)
    {ν : Vertex P} : Continuous (toTruncation P (ν := ν)) := by
  apply Continuous.prodMk (continuous_fst.comp (continuous_fst.comp continuous_subtype_val))
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact ((continuous_of_discreteTopology : Continuous
    (fun j : Fin 4 => if i = j then (3/4 : ℝ) else 0)).comp
      (continuous_snd.comp (continuous_fst.comp continuous_subtype_val))).add
    (((continuous_apply i).comp (continuous_snd.comp continuous_subtype_val)).div_const 4)
private theorem compact_original_carrier (P : RawFacePairing T)
    (ν : Vertex P) [Finite T] : IsCompact (Carrier P ν) := by
  have heval : Continuous (fun x : Raw T => x.2 x.1.2) := by
    have h : Continuous (fun z : (Fin 4 → ℝ) × Fin 4 => z.1 z.2) :=
      continuous_prod_of_discrete_right.mpr (fun k => continuous_apply k)
    exact h.comp (continuous_snd.prodMk continuous_fst.snd)
  have hclosed : IsClosed (Carrier P ν) := by
    apply (isClosed_eq heval continuous_const).inter
    apply IsClosed.inter
    · have he : {x : Raw T | ∀ i : Fin 4, 0 ≤ x.2 i} =
          ⋂ i : Fin 4, {x : Raw T | 0 ≤ x.2 i} := by ext x; simp
      change IsClosed {x : Raw T | ∀ i : Fin 4, 0 ≤ x.2 i}
      rw [he]
      exact isClosed_iInter fun i => isClosed_le continuous_const
        ((continuous_apply i).comp continuous_snd)
    · apply IsClosed.inter
      · exact isClosed_eq (by fun_prop) continuous_const
      · exact (isClosed_discrete {d : T × Fin 4 | label P d = ν}).preimage
          continuous_fst
  apply (isCompact_univ.prod (isCompact_Icc :
    IsCompact (Set.Icc (fun _ : Fin 4 => (0 : ℝ)) (fun _ => 1)))).of_isClosed_subset hclosed
  intro p hp
  exact ⟨Set.mem_univ _,hp.2.1,fun i => coordinate_le_one hp.2.1 hp.2.2.1 i⟩
/-- The affine carrier equivalence uses the actual subspace topology of the
original cap inside the original retained tetrahedra. -/
def actualSliceHomeomorph (P : RawFacePairing T) (ν : Vertex P) [Finite T] :
    Point P ν ≃ₜ ↥(Slice P ν) := by
  letI : CompactSpace (Point P ν) :=
    isCompact_iff_compactSpace.mp (compact_original_carrier P ν)
  let f : Point P ν → ↥(Slice P ν) := fun p =>
    ⟨toTruncation P p,toTruncation_mem P p⟩
  have hf : IsHomeomorph f := isHomeomorph_iff_continuous_bijective.mpr
    ⟨(continuous_toTruncation P).subtype_mk _,actual_slice_carriers P ν⟩
  exact hf.homeomorph f
abbrev TruncatedQuotient (P : RawFacePairing T) :=
  Quotient (Relation.EqvGen.setoid (TruncatedStep P))
/-- Image of the actual labeled cap in the full original truncated quotient. -/
def quotientSlice (P : RawFacePairing T) (ν : Vertex P) :
    Set (TruncatedQuotient P) :=
  (@Quotient.mk' _ (Relation.EqvGen.setoid (TruncatedStep P))) '' Slice P ν
private theorem slice_closed (P : RawFacePairing T) (ν : Vertex P) :
    IsClosed (Slice P ν) := by
  have he : Slice P ν = ⋃ j : Fin 4,
      {a : TruncatedPoint T | a.2.val j = 3/4} ∩
      {a | label P (a.1,j) = ν} := by
    ext a
    simp only [Slice,Set.mem_setOf_eq,Set.mem_iUnion,Set.mem_inter_iff]
  rw [he]
  apply isClosed_iUnion_of_finite
  intro j
  exact (isClosed_eq ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))
    continuous_const).inter
      ((isClosed_discrete {t : T | label P (t,j) = ν}).preimage continuous_fst)
private theorem slice_quotient_restriction (P : RawFacePairing T)
    (ν : Vertex P) :
    ((@Quotient.mk' _ (Relation.EqvGen.setoid (TruncatedStep P))) ⁻¹' quotientSlice P ν =
      Slice P ν) ∧
    Topology.IsQuotientMap ((quotientSlice P ν).restrictPreimage
      (@Quotient.mk' _ (Relation.EqvGen.setoid (TruncatedStep P)))) := by
  let q : TruncatedPoint T → TruncatedQuotient P :=
    @Quotient.mk' _ (Relation.EqvGen.setoid (TruncatedStep P))
  let U := quotientSlice P ν
  have hs : q ⁻¹' U = Slice P ν := by
    ext a
    constructor
    · rintro ⟨b,hb,he⟩
      exact (slice_chain_invariant P ν (Quotient.exact he)).mp hb
    · intro ha
      exact ⟨a,ha,rfl⟩
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  have hU : IsClosed U := hq.isClosed_preimage.mp (by
    rw [hs]
    exact slice_closed P ν)
  refine ⟨hs,Topology.isQuotientMap_iff_isClosed.mpr ⟨hq.surjective.restrictPreimage _,?_⟩⟩
  intro s
  rw [hU.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed,
    ← hq.isClosed_preimage,
    (hU.preimage hq.continuous).isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed,
    Set.image_val_preimage_restrictPreimage]
/-- The original full corner quotient equals the cap image in the full original
truncated quotient, equipped with the inherited topology. No correspondence,
slice-invariance, or quotient-topology hypothesis is supplied by the caller. -/
def actualSliceQuotientHomeomorph (P : RawFacePairing T)
    (ν : Vertex P) [Finite T] :
    Quotient (Relation.EqvGen.setoid (Step P (ν := ν))) ≃ₜ ↥(quotientSlice P ν) := by
  let q : TruncatedPoint T → TruncatedQuotient P :=
    @Quotient.mk' _ (Relation.EqvGen.setoid (TruncatedStep P))
  let U := quotientSlice P ν
  have hs := (slice_quotient_restriction P ν).1
  let e : ↥(Slice P ν) ≃ₜ ↥(q ⁻¹' U) := Homeomorph.setCongr hs.symm
  let f : Point P ν → ↥U :=
    U.restrictPreimage q ∘ e ∘ actualSliceHomeomorph P ν
  have hf : Topology.IsQuotientMap f :=
    (slice_quotient_restriction P ν).2.comp
      (e.isQuotientMap.comp (actualSliceHomeomorph P ν).isQuotientMap)
  have hk : ∀ p r, Related P p r ↔ f p = f r := by
    intro p r
    rw [actual_slice_eqvgen_iff]
    constructor
    · intro h; exact Subtype.ext (Quotient.sound h)
    · intro h; exact Quotient.exact (congrArg Subtype.val h)
  let fC : C(Point P ν, ↥U) := ⟨f,hf.continuous⟩
  exact (Homeomorph.Quotient.congrRight hk).trans
    (Topology.IsQuotientMap.homeomorph (f := fC) hf)

end Topology

-- Exact source identity check; it does not impose a group-model presentation.
example (P : RawFacePairing T) (x : T × Fin 4) :
    sigma P x x.2 = (P.facePair x).2 ∧
    (∀ n, sigma P x (oppositeVertex x.2 n) =
      oppositeVertex (P.facePair x).2 (P.faceMap x n)) ∧
    sigma P (P.facePair x) = (sigma P x).symm ∧
    (∀ n v, (v = (edgeVertices (faceEdge x.2 n)).1 ∨
      v = (edgeVertices (faceEdge x.2 n)).2) ↔
      (sigma P x v = (edgeVertices
        (faceEdge (P.facePair x).2 (P.faceMap x n))).1 ∨
       sigma P x v = (edgeVertices
        (faceEdge (P.facePair x).2 (P.faceMap x n))).2)) :=
  ⟨sigma_face P x, sigma_opposite P x, sigma_inverse P x, sigma_endpoint_iff P x⟩

example (P : RawFacePairing T) (i j : T × Fin 6) :
    D5.S3.Geometry.Hyperideal.ActualCornerTransport.edgeRel (cornerPairing P) i j ↔
      P.edgeStep i j := corner_edge_step_iff P i j

#print axioms actual_slice_eqvgen_iff
#print axioms actualSliceQuotientHomeomorph
end D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate.actual_slice_eqvgen_iff,
      ``D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate.actualSliceQuotientHomeomorph] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1053 exact raw-p cap-slice target absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1053 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP1053 CHECKED {name} axioms={axioms}"
