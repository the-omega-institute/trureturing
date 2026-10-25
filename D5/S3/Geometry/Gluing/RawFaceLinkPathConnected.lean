/- GID: D5/S3/Geometry/Gluing/RawFaceLinkPathConnected
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/RawFaceLinkPathConnected
   mirror-E: none(waiver:raw-face-link-path-connected-topological-result)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.PathConnected]
   utility: none
   digest: Original raw-face vertex-label quotients are path connected for arbitrary topological tags. -/

import D5.S3.Geometry.Hyperideal.EdgeStarTransitions
import D5.S3.Geometry.Hyperideal.ActualCornerTransport
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology

namespace D5.S3.Geometry.Gluing.RawFaceLinkPathConnected

open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Hyperideal.ActualCornerTransport
  (Corner Slot faceVertex b J cornerRel)

variable {T : Type*}

def chi (f : Fin 4) : Equiv.Perm (Fin 3) :=
  if f = 0 then 1 else Equiv.swap 0 2

def frame (f : Fin 4) : Fin 4 ≃ Option (Fin 3) :=
  (finSuccEquiv' f).trans (Equiv.optionCongr (chi f))

def sigma (P : RawFacePairing T) (x : T × Fin 4) : Equiv.Perm (Fin 4) :=
  (frame x.2).trans ((Equiv.optionCongr (P.faceMap x)).trans
    (frame (P.facePair x).2).symm)

private theorem paired_twice (P : RawFacePairing T) (x : T × Fin 4) :
    P.facePair (P.facePair x) = x := by
  have h := congrArg (fun e : Equiv.Perm (T × Fin 4) => e x) P.pairInvolutive
  simpa using h

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

/-- A representative corner supplies an actual point of the full closed triangle.
There is no separate Nonempty T assumption: a supplied label has a representative. -/
private theorem point_at (P : RawFacePairing T) (ν : Vertex P)
    (c : Corner T) (hc : label P c = ν) :
    ∃ x : Point P ν, x.val.1 = c := by
  classical
  obtain ⟨k,hk⟩ : ∃ k : Fin 4, k ≠ c.2 := by
    generalize c.2 = j
    fin_cases j <;> decide
  refine ⟨⟨(c,fun i => if i = k then 1 else 0),?_,?_,?_,hc⟩,rfl⟩
  · change (if c.2 = k then (1 : ℝ) else 0) = 0
    simp [Ne.symm hk]
  · intro i
    change 0 ≤ (if i = k then (1 : ℝ) else 0)
    split_ifs <;> norm_num
  · simp

/-- Each original corner generator has an actual nonempty crossing face in the
full original Point carrier. The witness is delta_k with k different from both
the omitted corner and the crossing face. Its actual pairedPoint has the exact
target tag b (J (cornerPairing P) i); no distinctness of the two tags is needed. -/
private theorem actual_generator_witness (P : RawFacePairing T) (ν : Vertex P)
    (i : Slot T) (hν : label P (b i) = ν) :
    ∃ z w : Point P ν,
      z.val.1 = b i ∧ w.val.1 = b (J (cornerPairing P) i) ∧ Step P z w := by
  classical
  rcases i with ⟨⟨t,f⟩,r⟩
  let j := faceVertex f r
  have hfj : f ≠ j := by
    dsimp [j]
    fin_cases f <;> fin_cases r <;> decide
  obtain ⟨k,hkf,hkj⟩ : ∃ k : Fin 4, k ≠ f ∧ k ≠ j := by
    generalize j = j'
    fin_cases f <;> fin_cases j' <;> decide
  have hlabel : label P (t,j) = ν := hν
  let z : Point P ν := ⟨((t,j),fun a => if a = k then 1 else 0),
    by
      change (if j = k then (1 : ℝ) else 0) = 0
      simp [Ne.symm hkj],
    by
      intro a
      change 0 ≤ (if a = k then (1 : ℝ) else 0)
      split_ifs <;> norm_num,
    by simp,hlabel⟩
  let w : Point P ν := pairedPoint P z f hfj
  have hzw : Step P z w := by
    refine ⟨f,hfj,?_,rfl⟩
    change (if f = k then (1 : ℝ) else 0) = 0
    simp [Ne.symm hkf]
  have hw : w.val.1 = b (J (cornerPairing P) ((t,f),r)) := by
    change ((P.facePair (t,f)).1, sigma P (t,f) (faceVertex f r)) =
      ((P.facePair (t,f)).1,
        faceVertex (P.facePair (t,f)).2 ((cornerPairing P).sigma (t,f) r))
    exact Prod.ext rfl (sigma_faceVertex P (t,f) r)
  exact ⟨z,w,rfl,hw,hzw⟩

section Topology

variable [TopologicalSpace T]

/-- The complete closed barycentric triangle at one original tag descends to
paths in the original Step quotient through a continuous constant-tag inclusion. -/
private theorem same_tag_joined (P : RawFacePairing T) (ν : Vertex P)
    (x y : Point P ν) (htag : x.val.1 = y.val.1) :
    Joined (Quotient.mk (Relation.EqvGen.setoid (Step P (ν := ν))) x)
      (Quotient.mk (Relation.EqvGen.setoid (Step P (ν := ν))) y) := by
  classical
  let L := Quotient (Relation.EqvGen.setoid (Step P (ν := ν)))
  let π : Point P ν → L := Quotient.mk _
  have hπ : Continuous π := continuous_quotient_mk'
  change Joined (π x) (π y)
  let C : Set (Fin 4 → ℝ) :=
    {z | z x.val.1.2 = 0 ∧ (∀ i, 0 ≤ z i) ∧ (∑ i, z i) = 1}
  have hc : Convex ℝ C := by
    intro a ha b hb s t hs ht hst
    refine ⟨?_,?_,?_⟩
    · change s * a x.val.1.2 + t * b x.val.1.2 = 0
      rw [ha.1,hb.1,mul_zero,mul_zero,add_zero]
    · intro i
      exact add_nonneg (mul_nonneg hs (ha.2.1 i)) (mul_nonneg ht (hb.2.1 i))
    · change (∑ i : Fin 4, (s * a i + t * b i)) = 1
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
        ha.2.2,hb.2.2,mul_one,mul_one,hst]
  have hx : x.val.2 ∈ C := ⟨x.property.1,x.property.2.1,x.property.2.2.1⟩
  have hy : y.val.2 ∈ C := by
    exact ⟨by rw [htag]; exact y.property.1,y.property.2.1,y.property.2.2.1⟩
  let inclusion : C → Point P ν := fun z =>
    ⟨(x.val.1,z.val),z.property.1,z.property.2.1,z.property.2.2,x.property.2.2.2⟩
  have hi : Continuous inclusion := by
    exact (continuous_const.prodMk continuous_subtype_val).subtype_mk _
  have h := ((hc.isPathConnected ⟨x.val.2,hx⟩).joinedIn _ hx _ hy).joined_subtype
  have hx' : inclusion ⟨x.val.2,hx⟩ = x := Subtype.ext rfl
  have hy' : inclusion ⟨y.val.2,hy⟩ = y := by
    apply Subtype.ext
    exact Prod.ext htag rfl
  simpa only [Function.comp_apply,hx',hy'] using (h.map (hπ.comp hi))

/-- An original corner generator joins any points in its two full triangles:
move within the first triangle to an actual face witness, identify that witness
with its actual pairedPoint in the Step quotient, and move in the target triangle. -/
private theorem across_generator_joined (P : RawFacePairing T) (ν : Vertex P)
    (i : Slot T) (x y : Point P ν)
    (hx : x.val.1 = b i) (hy : y.val.1 = b (J (cornerPairing P) i)) :
    Joined (Quotient.mk (Relation.EqvGen.setoid (Step P (ν := ν))) x)
      (Quotient.mk (Relation.EqvGen.setoid (Step P (ν := ν))) y) := by
  let π : Point P ν → Quotient (Relation.EqvGen.setoid (Step P (ν := ν))) :=
    Quotient.mk _
  have hlabel : label P (b i) = ν := by
    rw [← hx]
    exact x.property.2.2.2
  obtain ⟨z,w,hz,hw,hzw⟩ := actual_generator_witness P ν i hlabel
  have he : π z = π w := Quotient.sound (Relation.EqvGen.rel _ _ hzw)
  have hxz : Joined (π x) (π z) := same_tag_joined P ν x z (hx.trans hz.symm)
  have hwy : Joined (π w) (π y) := same_tag_joined P ν w y (hw.trans hy.symm)
  have hzy : Joined (π z) (π y) := by
    rw [he]
    exact hwy
  exact hxz.trans hzy

/-- Lift the actual equivalence closure of cornerRel, retaining every
intermediate original corner and choosing its Point representative in the same
label. EqvGen induction handles finite chains without Fintype T. -/
private theorem corner_chain_joined (P : RawFacePairing T) (ν : Vertex P)
    {c d : Corner T} (h : Relation.EqvGen (cornerRel (cornerPairing P)) c d) :
    ∀ (x y : Point P ν), x.val.1 = c → y.val.1 = d →
      Joined (Quotient.mk (Relation.EqvGen.setoid (Step P (ν := ν))) x)
        (Quotient.mk (Relation.EqvGen.setoid (Step P (ν := ν))) y) := by
  induction h with
  | rel c d h =>
    intro x y hx hy
    obtain ⟨i,hi,hj⟩ := h
    exact across_generator_joined P ν i x y (hx.trans hi.symm) (hy.trans hj.symm)
  | refl c =>
    intro x y hx hy
    exact same_tag_joined P ν x y (hx.trans hy.symm)
  | symm c d _ ih =>
    intro x y hx hy
    exact (ih y x hy hx).symm
  | trans c d e hcd _ ih₁ ih₂ =>
    intro x y hx hy
    have hlabels : label P c = label P d := Quotient.sound hcd
    have hdlabel : label P d = ν := by
      calc
        label P d = label P c := hlabels.symm
        _ = label P x.val.1 := congrArg (label P) hx.symm
        _ = ν := x.property.2.2.2
    obtain ⟨z,hz⟩ := point_at P ν d hdlabel
    exact (ih₁ x z hx hz).trans (ih₂ z y hz hy)

/-- The label equations on the original Point carrier supply exactly the
cornerRel equivalence chain required by corner_chain_joined. -/
private theorem original_points_joined (P : RawFacePairing T) (ν : Vertex P)
    (x y : Point P ν) :
    Joined (Quotient.mk (Relation.EqvGen.setoid (Step P (ν := ν))) x)
      (Quotient.mk (Relation.EqvGen.setoid (Step P (ν := ν))) y) := by
  have hlabels : label P x.val.1 = label P y.val.1 :=
    x.property.2.2.2.trans y.property.2.2.2.symm
  have hchain : Relation.EqvGen (cornerRel (cornerPairing P)) x.val.1 y.val.1 :=
    Quotient.exact hlabels
  exact corner_chain_joined P ν hchain x y rfl rfl

/-- For every topological tag space and every raw face pairing, each original
vertex-label quotient of the full closed Point carrier by the guarded Step
relation is path connected. Raw carries the product topology, Point the subtype
topology, and the EqvGen quotient the quotient topology. -/
theorem original_quotient_path_connected (P : RawFacePairing T) (ν : Vertex P) :
    PathConnectedSpace (Quotient (Relation.EqvGen.setoid (Step P (ν := ν)))) := by
  refine ⟨?_,?_⟩
  · obtain ⟨c,hc⟩ := Quotient.exists_rep ν
    obtain ⟨x,_⟩ := point_at P ν c hc
    exact ⟨Quotient.mk _ x⟩
  · intro p q
    induction p using Quotient.inductionOn with
    | h x =>
      induction q using Quotient.inductionOn with
      | h y => exact original_points_joined P ν x y

end Topology

end D5.S3.Geometry.Gluing.RawFaceLinkPathConnected
