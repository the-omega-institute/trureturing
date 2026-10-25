import D5.S3.Geometry.Hyperideal.EdgeStarTransitions
import D5.S3.Geometry.Hyperideal.S4OppositePairAction
import D5.S3.Geometry.Hyperideal.PositiveFlatClassification
-- The parent must stage section71-629-global-check.lean under this transient
-- module name, with its own exact620 dependency. Neither is presumed compiled.
import CFMPSection71Global629Transient
import Lean.Util.CollectAxioms

-- Source candidate only: no compilation or kernel acceptance is asserted.
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

noncomputable section
open scoped Matrix BigOperators Classical

namespace Section71Relabel648

open D5.S3.Geometry.Hyperideal.EdgeStarTransitions
open D5.S3.Geometry.Hyperideal.S4OppositePairAction (edgeIndex)
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
open D5.S3.Geometry.Hyperideal.PositiveFlatClassification (Genuine)
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes (numerator rad cosine)
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)

abbrev V := Fin 4
abbrev J := Fin 6
abbrev P4 := Equiv.Perm V

-- A permutation sends NEW vertices to OLD vertices. Local lengths are pullbacks.
def edgeTo (s : P4) (j : J) : J :=
  edgeIndex (s (edgeVertices j).1) (s (edgeVertices j).2)

private theorem edge_inverse_table :
    ∀ (s : P4) (j : J), edgeTo s.symm (edgeTo s j) = j := by
  decide

def edgePerm (s : P4) : Equiv.Perm J where
  toFun := edgeTo s
  invFun := edgeTo s.symm
  left_inv := edge_inverse_table s
  right_inv := by
    intro j
    simpa using edge_inverse_table s.symm j

-- This constructs the three-slot permutation from actual K4 incidence.
-- It is not an assumed incidence bijection.
private theorem slot_exists_table :
    ∀ (s : P4) (f : V), ∃ d : Equiv.Perm (Fin 3),
      ∀ n, faceEdge (s f) (d n) = edgeTo s (faceEdge f n) := by
  decide

def slot (s : P4) (f : V) : Equiv.Perm (Fin 3) :=
  Classical.choose (slot_exists_table s f)

theorem slot_spec (s : P4) (f : V) (n : Fin 3) :
    faceEdge (s f) (slot s f n) = edgePerm s (faceEdge f n) :=
  Classical.choose_spec (slot_exists_table s f) n

variable {T : Type*}

def faces (s : T → P4) : Equiv.Perm (T × V) where
  toFun x := (x.1, s x.1 x.2)
  invFun x := (x.1, (s x.1).symm x.2)
  left_inv := by rintro ⟨t,f⟩; simp
  right_inv := by rintro ⟨t,f⟩; simp

def occurrences (s : T → P4) : Equiv.Perm (Occurrence T) where
  toFun x := (x.1, edgePerm (s x.1) x.2)
  invFun x := (x.1, (edgePerm (s x.1)).symm x.2)
  left_inv := by rintro ⟨t,j⟩; simp
  right_inv := by rintro ⟨t,j⟩; simp

def newFace (p : RawFacePairing T) (s : T → P4) (x : T × V) : T × V :=
  (faces s).symm (p.facePair (faces s x))

theorem faces_newFace (p : RawFacePairing T) (s : T → P4) (x : T × V) :
    faces s (newFace p s x) = p.facePair (faces s x) := by
  exact (faces s).apply_symm_apply _

private theorem pair_twice (p : RawFacePairing T) (x : T × V) :
    p.facePair (p.facePair x) = x := by
  have h := congrArg (fun a : Equiv.Perm (T × V) => a x) p.pairInvolutive
  simpa using h

theorem newFace_twice (p : RawFacePairing T) (s : T → P4) (x : T × V) :
    newFace p s (newFace p s x) = x := by
  apply (faces s).injective
  rw [faces_newFace, faces_newFace, pair_twice]

def newMap (p : RawFacePairing T) (s : T → P4) (x : T × V) :
    Equiv.Perm (Fin 3) :=
  (slot (s x.1) x.2).trans
    ((p.faceMap (faces s x)).trans
      (slot (s (newFace p s x).1) (newFace p s x).2).symm)

def relabel (p : RawFacePairing T) (s : T → P4) : RawFacePairing T where
  facePair := (faces s).trans (p.facePair.trans (faces s).symm)
  faceMap := newMap p s
  pairInvolutive := by
    apply Equiv.ext
    intro x
    exact newFace_twice p s x
  pairFixedFree := by
    intro x hx
    apply p.pairFixedFree (faces s x)
    have h := congrArg (faces s) hx
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using h
  mapInverse := by
    intro x n
    change newMap p s (newFace p s x) (newMap p s x n) = n
    simp only [newMap, Equiv.trans_apply, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply, newFace_twice, faces_newFace, p.mapInverse]

theorem source_transport (s : T → P4) (x : T × V) (n : Fin 3) :
    occurrences s (x.1, faceEdge x.2 n) =
      ((faces s x).1, faceEdge (faces s x).2 (slot (s x.1) x.2 n)) := by
  apply Prod.ext
  · rfl
  · exact (slot_spec (s x.1) x.2 n).symm

theorem target_transport (p : RawFacePairing T) (s : T → P4)
    (x : T × V) (n : Fin 3) :
    occurrences s ((newFace p s x).1,
      faceEdge (newFace p s x).2 (newMap p s x n)) =
      ((p.facePair (faces s x)).1,
        faceEdge (p.facePair (faces s x)).2
          (p.faceMap (faces s x) (slot (s x.1) x.2 n))) := by
  rw [source_transport, faces_newFace]
  simp only [newMap, Equiv.trans_apply, Equiv.apply_symm_apply]

theorem edgeStep_transport (p : RawFacePairing T) (s : T → P4)
    (i j : Occurrence T) :
    (relabel p s).edgeStep i j ↔ p.edgeStep (occurrences s i) (occurrences s j) := by
  constructor
  · rintro ⟨x,n,rfl,rfl⟩
    refine ⟨faces s x, slot (s x.1) x.2 n, source_transport s x n, ?_⟩
    exact target_transport p s x n
  · rintro ⟨y,m,hi,hj⟩
    let x := (faces s).symm y
    let n := (slot (s x.1) x.2).symm m
    have hx : faces s x = y := (faces s).apply_symm_apply y
    have hn : slot (s x.1) x.2 n = m :=
      (slot (s x.1) x.2).apply_symm_apply m
    refine ⟨x,n,?_,?_⟩
    · apply (occurrences s).injective
      rw [source_transport, hx, hn]
      exact hi
    · apply (occurrences s).injective
      change occurrences s j = occurrences s
        ((newFace p s x).1, faceEdge (newFace p s x).2 (newMap p s x n))
      rw [target_transport, hx, hn]
      exact hj

-- Relation closure is transported, not replaced by equality of numeric lengths.
private theorem eqvGen_map {A B : Type*} {r : A → A → Prop} {q : B → B → Prop}
    (f : A → B) (hf : ∀ a b, r a b → q (f a) (f b))
    {a b : A} (h : Relation.EqvGen r a b) : Relation.EqvGen q (f a) (f b) := by
  induction h with
  | rel a b hab => exact Relation.EqvGen.rel _ _ (hf a b hab)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab hbc ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc

theorem edgeClosure_transport (p : RawFacePairing T) (s : T → P4)
    (i j : Occurrence T) :
    Relation.EqvGen (relabel p s).edgeStep i j ↔
      Relation.EqvGen p.edgeStep (occurrences s i) (occurrences s j) := by
  constructor
  · exact eqvGen_map (occurrences s) (fun a b => (edgeStep_transport p s a b).mp)
  · intro h
    have hback := eqvGen_map (occurrences s).symm (fun a b hab =>
      (edgeStep_transport p s _ _).mpr (by simpa using hab)) h
    simpa using hback

def globalEdges (p : RawFacePairing T) (s : T → P4) :
    (relabel p s).GlobalEdge ≃ p.GlobalEdge :=
  Quotient.congr (occurrences s) (edgeClosure_transport p s)

@[simp] theorem globalEdges_label (p : RawFacePairing T) (s : T → P4)
    (t : T) (j : J) :
    globalEdges p s ((relabel p s).edgeLabel t j) = p.edgeLabel t (edgePerm (s t) j) := rfl

def field (p : RawFacePairing T) (s : T → P4) (ell : p.GlobalEdge → ℝ) :
    (relabel p s).GlobalEdge → ℝ := ell ∘ globalEdges p s

def values (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (t : T) (j : J) : ℝ :=
  Real.cosh (ell (p.edgeLabel t j))

theorem values_transport (p : RawFacePairing T) (s : T → P4)
    (ell : p.GlobalEdge → ℝ) (t : T) :
    values (relabel p s) (field p s ell) t = values p ell t ∘ edgePerm (s t) := rfl

-- Full symbolic S4 identities. No Gram realization or positivity is assumed,
-- so the clipped angle identity applies to the flat sectors as well.
theorem numerator_transport (x : J → ℝ) (s : P4) (j : J) :
    rawNum (x ∘ edgePerm s) j = rawNum x (edgePerm s j) := by
  have h01 : s (0 : V) ≠ s 1 := s.injective.ne (by decide)
  have h02 : s (0 : V) ≠ s 2 := s.injective.ne (by decide)
  have h03 : s (0 : V) ≠ s 3 := s.injective.ne (by decide)
  have h12 : s (1 : V) ≠ s 2 := s.injective.ne (by decide)
  have h13 : s (1 : V) ≠ s 3 := s.injective.ne (by decide)
  have h23 : s (2 : V) ≠ s 3 := s.injective.ne (by decide)
  generalize hs0 : s (0 : V) = a0 at *
  generalize hs1 : s (1 : V) = a1 at *
  generalize hs2 : s (2 : V) = a2 at *
  generalize hs3 : s (3 : V) = a3 at *
  fin_cases a0 <;> fin_cases a1 <;> simp_all
  all_goals fin_cases a2 <;> simp_all
  all_goals fin_cases a3 <;> simp_all
  all_goals
    fin_cases j <;>
      simp_all [rawNum, edgePerm, edgeTo, edgeVertices, edgeIndex, frame,
        numerator, Function.comp_def] <;> ring

theorem radicands_transport (x : J → ℝ) (s : P4) (j : J) :
    (leftRad (x ∘ edgePerm s) j = leftRad x (edgePerm s j) ∧
      rightRad (x ∘ edgePerm s) j = rightRad x (edgePerm s j)) ∨
    (leftRad (x ∘ edgePerm s) j = rightRad x (edgePerm s j) ∧
      rightRad (x ∘ edgePerm s) j = leftRad x (edgePerm s j)) := by
  have h01 : s (0 : V) ≠ s 1 := s.injective.ne (by decide)
  have h02 : s (0 : V) ≠ s 2 := s.injective.ne (by decide)
  have h03 : s (0 : V) ≠ s 3 := s.injective.ne (by decide)
  have h12 : s (1 : V) ≠ s 2 := s.injective.ne (by decide)
  have h13 : s (1 : V) ≠ s 3 := s.injective.ne (by decide)
  have h23 : s (2 : V) ≠ s 3 := s.injective.ne (by decide)
  generalize hs0 : s (0 : V) = a0 at *
  generalize hs1 : s (1 : V) = a1 at *
  generalize hs2 : s (2 : V) = a2 at *
  generalize hs3 : s (3 : V) = a3 at *
  fin_cases a0 <;> fin_cases a1 <;> simp_all
  all_goals fin_cases a2 <;> simp_all
  all_goals fin_cases a3 <;> simp_all
  all_goals
    fin_cases j <;>
      simp_all [leftRad, rightRad, edgePerm, edgeTo, edgeVertices, edgeIndex,
        frame, rad, Function.comp_def]
  all_goals solve
    | (left; constructor <;> ring)
    | (right; constructor <;> ring)
    | (left; ring)
    | (right; ring)
    | ring

private theorem raw_quotient (x : J → ℝ) (j : J) :
    rawCos x j = rawNum x j / (Real.sqrt (leftRad x j) * Real.sqrt (rightRad x j)) := by
  unfold rawCos rawNum leftRad rightRad cosine
  rw [div_div]

theorem rawCos_transport (x : J → ℝ) (s : P4) (j : J) :
    rawCos (x ∘ edgePerm s) j = rawCos x (edgePerm s j) := by
  rw [raw_quotient, raw_quotient, numerator_transport]
  rcases radicands_transport x s j with h | h
  · rw [h.1,h.2]
  · rw [h.1,h.2,mul_comm]

theorem extendedAngle_transport (x : J → ℝ) (s : P4) (j : J) :
    extendedAngle (x ∘ edgePerm s) j = extendedAngle x (edgePerm s j) := by
  unfold extendedAngle
  rw [rawCos_transport]

theorem genuine_transport (x : J → ℝ) (s : P4) :
    Genuine (x ∘ edgePerm s) ↔ Genuine x := by
  constructor
  · intro h j
    obtain ⟨k,rfl⟩ := (edgePerm s).surjective j
    simpa only [rawCos_transport] using h k
  · intro h j
    simpa only [rawCos_transport] using h (edgePerm s j)

def localLow (v : J → ℝ) (h : ℝ) (f : V) : Prop :=
  ∃ m : Fin 3, v (faceEdge f m) < h

theorem low_transport (p : RawFacePairing T) (s : T → P4)
    (ell : p.GlobalEdge → ℝ) (h : ℝ) (t : T) (f : V) :
    localLow (values (relabel p s) (field p s ell) t) h f ↔
      localLow (values p ell t) h (s t f) := by
  rw [values_transport]
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨slot (s t) f n,?_⟩
    simpa only [slot_spec, Function.comp_apply] using hn
  · rintro ⟨m,hm⟩
    refine ⟨(slot (s t) f).symm m,?_⟩
    have he := slot_spec (s t) f ((slot (s t) f).symm m)
    rw [Equiv.apply_symm_apply] at he
    simpa only [Function.comp_apply, ← he] using hm

def flags (s : T → P4) : Equiv.Perm (T × (V × Fin 3)) where
  toFun d := (d.1,(s d.1 d.2.1,slot (s d.1) d.2.1 d.2.2))
  invFun d := (d.1,((s d.1).symm d.2.1,
    (slot (s d.1) ((s d.1).symm d.2.1)).symm d.2.2))
  left_inv := by rintro ⟨t,f,n⟩; simp
  right_inv := by rintro ⟨t,f,n⟩; simp

def Fiber (p : RawFacePairing T) (e : p.GlobalEdge) :=
  {o : Occurrence T // p.edgeLabel o.1 o.2 = e}

noncomputable instance fiberFintype [Fintype T]
    (p : RawFacePairing T) (e : p.GlobalEdge) : Fintype (Fiber p e) := by
  classical
  unfold Fiber
  infer_instance

theorem label_iff (p : RawFacePairing T) (s : T → P4)
    (e : p.GlobalEdge) (o : Occurrence T) :
    (relabel p s).edgeLabel o.1 o.2 = (globalEdges p s).symm e ↔
      p.edgeLabel (occurrences s o).1 (occurrences s o).2 = e := by
  rcases o with ⟨t,j⟩
  change (relabel p s).edgeLabel t j = (globalEdges p s).symm e ↔
    p.edgeLabel t (edgePerm (s t) j) = e
  constructor
  · intro he
    calc
      p.edgeLabel t (edgePerm (s t) j) =
          globalEdges p s ((relabel p s).edgeLabel t j) :=
        (globalEdges_label p s t j).symm
      _ = globalEdges p s ((globalEdges p s).symm e) := congrArg (globalEdges p s) he
      _ = e := (globalEdges p s).apply_symm_apply e
  · intro he
    apply (globalEdges p s).injective
    calc
      globalEdges p s ((relabel p s).edgeLabel t j) =
          p.edgeLabel t (edgePerm (s t) j) := globalEdges_label p s t j
      _ = e := he
      _ = globalEdges p s ((globalEdges p s).symm e) :=
        ((globalEdges p s).apply_symm_apply e).symm

def fiberEquiv (p : RawFacePairing T) (s : T → P4) (e : p.GlobalEdge) :
    Fiber (relabel p s) ((globalEdges p s).symm e) ≃ Fiber p e :=
  Equiv.subtypeEquiv (occurrences s) (label_iff p s e)

def LowFiber (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (h : ℝ) (e : p.GlobalEdge) :=
  {d : T × (V × Fin 3) // localLow (values p ell d.1) h d.2.1 ∧
    p.edgeLabel d.1 (faceEdge d.2.1 d.2.2) = e}

def lowFiberEquiv (p : RawFacePairing T) (s : T → P4)
    (ell : p.GlobalEdge → ℝ) (h : ℝ) (e : p.GlobalEdge) :
    LowFiber (relabel p s) (field p s ell) h ((globalEdges p s).symm e) ≃
      LowFiber p ell h e := by
  apply Equiv.subtypeEquiv (flags s)
  rintro ⟨t,f,n⟩
  change (localLow (values (relabel p s) (field p s ell) t) h f ∧
    (relabel p s).edgeLabel t (faceEdge f n) = (globalEdges p s).symm e) ↔
    (localLow (values p ell t) h (s t f) ∧
      p.edgeLabel t (faceEdge (s t f) (slot (s t) f n)) = e)
  rw [low_transport, slot_spec]
  exact and_congr Iff.rfl (label_iff p s e (t,faceEdge f n))

def angle (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (o : Occurrence T) : ℝ :=
  extendedAngle (values p ell o.1) o.2

theorem angle_transport (p : RawFacePairing T) (s : T → P4)
    (ell : p.GlobalEdge → ℝ) (o : Occurrence T) :
    angle (relabel p s) (field p s ell) o = angle p ell (occurrences s o) := by
  exact extendedAngle_transport (values p ell o.1) (s o.1) o.2

theorem angle_sum_transport [Fintype T] (p : RawFacePairing T) (s : T → P4)
    (ell : p.GlobalEdge → ℝ) (e : p.GlobalEdge) :
    (∑ o : Fiber (relabel p s) ((globalEdges p s).symm e),
      angle (relabel p s) (field p s ell) o.val) =
      ∑ o : Fiber p e, angle p ell o.val := by
  classical
  calc
    _ = ∑ o : Fiber (relabel p s) ((globalEdges p s).symm e),
        angle p ell (fiberEquiv p s e o).val := by
      apply Finset.sum_congr rfl
      intro o _
      exact angle_transport p s ell o.val
    _ = _ := Equiv.sum_comp (fiberEquiv p s e) (fun o => angle p ell o.val)

def GenuineFiber (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (e : p.GlobalEdge) := {o : Fiber p e // Genuine (values p ell o.val.1)}

noncomputable instance genuineFiberFintype [Fintype T]
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (e : p.GlobalEdge) :
    Fintype (GenuineFiber p ell e) := by
  classical
  unfold GenuineFiber
  infer_instance

def genuineFiberEquiv (p : RawFacePairing T) (s : T → P4)
    (ell : p.GlobalEdge → ℝ) (e : p.GlobalEdge) :
    GenuineFiber (relabel p s) (field p s ell) ((globalEdges p s).symm e) ≃
      GenuineFiber p ell e := by
  apply Equiv.subtypeEquiv (fiberEquiv p s e)
  intro o
  change Genuine (values (relabel p s) (field p s ell) o.val.1) ↔
    Genuine (values p ell o.val.1)
  rw [values_transport]
  exact genuine_transport _ _

-- These are the actual six-length block assumptions after genuine vertex
-- relabeling. Parameters vary independently with t. No angle-vector or
-- beta-equality assumption is added.
def BlockData (p : RawFacePairing T) (s : T → P4)
    (ell : p.GlobalEdge → ℝ) (h : ℝ) : Prop :=
  ∀ t : T, ∃ r u : ℝ,
    values p ell t ∘ edgePerm (s t) = Section71ExactCheck620.six r h u ∧
      ((h < r ∧ h < u ∧
          extendedAngle (Section71ExactCheck620.six r h u) 0 = Real.pi) ∨
        (1 + 2 * h ≤ r ∧ Genuine (Section71ExactCheck620.six r h u) ∧
          Real.tan (Real.arccos (cosine r h h u h h) / 2) ≤ (1 : ℝ) / 2))

theorem normalized_data (p : RawFacePairing T) (s : T → P4)
    (ell : p.GlobalEdge → ℝ) (h : ℝ) (data : BlockData p s ell h) :
    Section71GlobalCheck629.FixedAxisData (relabel p s) (field p s ell) h := by
  intro t
  obtain ⟨r,u,hshape,hkind⟩ := data t
  refine ⟨r,u,?_,hkind⟩
  change values (relabel p s) (field p s ell) t = _
  exact (values_transport p s ell t).trans hshape

-- Conditional source composition with629. This is not an assertion that629,
-- this candidate or the original Section71.1 has passed a Lean build.
theorem original_edge_obstruction [Fintype T]
    (p : RawFacePairing T) (s : T → P4) (ell : p.GlobalEdge → ℝ) (h : ℝ)
    (hpos : ∀ e, 0 < ell e) (hh : 1 < h) (data : BlockData p s ell h)
    (e : p.GlobalEdge) (he : Real.cosh (ell e) = h) :
    Even (Fintype.card (GenuineFiber p ell e)) ∧
      (∑ o : Fiber p e, angle p ell o.val) ≠ 2 * Real.pi := by
  classical
  have hp : ∀ a, 0 < field p s ell a := fun a => hpos (globalEdges p s a)
  have he' : Real.cosh (field p s ell ((globalEdges p s).symm e)) = h := by
    simpa only [field,Function.comp_apply,Equiv.apply_symm_apply] using he
  have hb := Section71GlobalCheck629.fixed_axes_edge_obstruction
    (relabel p s) (field p s ell) h hp hh (normalized_data p s ell h data)
    ((globalEdges p s).symm e) he'
  have hev : Even (Fintype.card
      (GenuineFiber (relabel p s) (field p s ell) ((globalEdges p s).symm e))) := hb.1
  have hc := Fintype.card_congr (genuineFiberEquiv p s ell e)
  rw [hc] at hev
  have hne : (∑ o : Fiber (relabel p s) ((globalEdges p s).symm e),
      angle (relabel p s) (field p s ell) o.val) ≠ 2 * Real.pi := hb.2
  rw [angle_sum_transport] at hne
  exact ⟨hev,hne⟩

theorem original_no_closed_angle_sum [Fintype T] [Nonempty T]
    (p : RawFacePairing T) (s : T → P4) (ell : p.GlobalEdge → ℝ) (h : ℝ)
    (hpos : ∀ e, 0 < ell e) (hh : 1 < h) (data : BlockData p s ell h) :
    ¬ (∀ e : p.GlobalEdge, (∑ o : Fiber p e, angle p ell o.val) = 2 * Real.pi) := by
  intro hclosed
  obtain ⟨t⟩ := (inferInstance : Nonempty T)
  obtain ⟨r,u,hshape,hkind⟩ := data t
  let e := p.edgeLabel t (edgePerm (s t) 1)
  have he : Real.cosh (ell e) = h := by
    have hv := congrFun hshape 1
    simpa only [values,Function.comp_apply,Section71ExactCheck620.six,
      Matrix.cons_val,Fin.reduceFinMk,Fin.isValue] using hv
  exact (original_edge_obstruction p s ell h hpos hh data e he).2 (hclosed e)

end Section71Relabel648

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``Section71Relabel648.edgeClosure_transport,
      ``Section71Relabel648.rawCos_transport,
      ``Section71Relabel648.lowFiberEquiv,
      ``Section71Relabel648.original_edge_obstruction,
      ``Section71Relabel648.original_no_closed_angle_sum] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"Section71-648 declaration absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"Section71-648 disallowed axiom {ax} for {name}"
    Lean.logInfo m!"Section71-648 CHECKED {name} axioms={axioms}"
