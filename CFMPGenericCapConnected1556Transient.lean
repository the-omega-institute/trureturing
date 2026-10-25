/-
Draft module: CFMPGenericCapConnected1556Transient

UNCOMPILED implementation candidate. This file has not been elaborated, its
checked-environment guards have not run, and it is not a canonical admission.
It uses the exact original RawFaceCapSliceCandidate objects from the operative
CFMPRawFaceCapSlice1053Transient source, without a group-model presentation.
-/
import CFMPRawFaceCapSlice1053Transient
import Mathlib.Analysis.Convex.PathConnected
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology

namespace CFMPGenericCapConnected1556Transient

open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Hyperideal.ActualCornerTransport
  (Corner Slot faceVertex b J cornerRel)

-- Reuse the compatibility already proved for the SAME original sigma and
-- cornerPairing. No second face frame or duplicated private proof is introduced.
open private sigma_faceVertex from CFMPRawFaceCapSlice1053Transient

variable {T : Type*}

/-- A representative corner supplies an actual point of the full closed triangle.
There is no separate Nonempty T assumption: a supplied label has a representative. -/
theorem point_at (P : RawFacePairing T) (ν : Vertex P)
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
theorem actual_generator_witness (P : RawFacePairing T) (ν : Vertex P)
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

variable [TopologicalSpace T] [instDiscreteT : DiscreteTopology T]
include instDiscreteT

/-- The complete closed barycentric triangle at one original tag descends to
paths in the original Step quotient. This adapts the LOCAL same_tag proof of
ActualLinkPathConnected, rather than calling a nonexistent exported theorem. -/
theorem same_tag_joined (P : RawFacePairing T) (ν : Vertex P)
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
theorem across_generator_joined (P : RawFacePairing T) (ν : Vertex P)
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
theorem corner_chain_joined (P : RawFacePairing T) (ν : Vertex P)
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
theorem original_points_joined (P : RawFacePairing T) (ν : Vertex P)
    (x y : Point P ν) :
    Joined (Quotient.mk (Relation.EqvGen.setoid (Step P (ν := ν))) x)
      (Quotient.mk (Relation.EqvGen.setoid (Step P (ν := ν))) y) := by
  have hlabels : label P x.val.1 = label P y.val.1 :=
    x.property.2.2.2.trans y.property.2.2.2.symm
  have hchain : Relation.EqvGen (cornerRel (cornerPairing P)) x.val.1 y.val.1 :=
    Quotient.exact hlabels
  exact corner_chain_joined P ν hchain x y rfl rfl

/-- For every original vertex label, the quotient of the ENTIRE original
closed Point carrier by the original guarded Step relation is path connected.
No finiteness, connectedness premise, or extra edge-reversal condition is used. -/
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

/-- The actual cap image, with its inherited topology in the full original
truncated quotient, is path connected. Finiteness is added only at this existing
homeomorphism application; no replacement cap quotient is introduced. -/
theorem actual_cap_path_connected [Finite T] (P : RawFacePairing T) (ν : Vertex P) :
    PathConnectedSpace ↥(quotientSlice P ν) := by
  letI : PathConnectedSpace (Quotient (Relation.EqvGen.setoid (Step P (ν := ν)))) :=
    original_quotient_path_connected P ν
  exact (actualSliceQuotientHomeomorph P ν).pathConnectedSpace

end Topology

-- These guards are part of the draft, NOT an execution receipt. They must run
-- with the exact operative dependency on the caller-selected Mac Studio.
-- Check every useful declaration introduced here and the reused exact bridges.
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPGenericCapConnected1556Transient.point_at,
      ``CFMPGenericCapConnected1556Transient.actual_generator_witness,
      ``CFMPGenericCapConnected1556Transient.same_tag_joined,
      ``CFMPGenericCapConnected1556Transient.across_generator_joined,
      ``CFMPGenericCapConnected1556Transient.corner_chain_joined,
      ``CFMPGenericCapConnected1556Transient.original_points_joined,
      ``CFMPGenericCapConnected1556Transient.original_quotient_path_connected,
      ``CFMPGenericCapConnected1556Transient.actual_cap_path_connected,
      ``sigma_faceVertex,
      ``D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate.actual_slice_eqvgen_iff,
      ``D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate.actualSliceQuotientHomeomorph] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1556 exact original-object target absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1556 disallowed axiom {ax} in {name}"
    Lean.logInfo m!"CFMP1556 CHECKED {name} axioms={axioms}"

end CFMPGenericCapConnected1556Transient
