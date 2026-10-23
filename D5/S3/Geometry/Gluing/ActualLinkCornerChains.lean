/- GID: D5/S3/Geometry/Gluing/ActualLinkCornerChains
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/ActualLinkCornerChains
   mirror-E: none(waiver:actual-affine-link-chain-analysis)
   anchors: [mathlib/module/Mathlib.Topology.Constructions]
   utility: none
   digest: Original affine corner chains preserve strict ordered-corner neighborhoods. -/

import D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
namespace D5.S3.Geometry.Gluing.ActualLinkCornerChains
open D5.S3.Geometry.Hyperideal.ActualCornerTransport
open D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

/-- The four whole-face permutations, including the inverse directions. -/
def facePerm (f : Fin 4) : Equiv.Perm (Fin 4) where
  toFun i := ![![3,0,1,2], ![3,2,0,1], ![2,3,1,0], ![1,2,3,0]] f i
  invFun i := ![![1,2,3,0], ![2,3,1,0], ![3,2,0,1], ![3,0,1,2]] f i
  left_inv := by intro i; fin_cases f <;> fin_cases i <;> decide
  right_inv := by intro i; fin_cases f <;> fin_cases i <;> decide

def reverseFace (f : Fin 4) : Fin 4 := ![3,2,1,0] f
def faceWord (u v : G) (f : Fin 4) : G := ![u,v,v⁻¹,u⁻¹] f

private theorem reverse_perm (f : Fin 4) :
    facePerm (reverseFace f) = (facePerm f).symm := by
  fin_cases f <;> ext i <;> fin_cases i <;> rfl

private theorem perm_face (f : Fin 4) : facePerm f f = reverseFace f := by
  fin_cases f <;> rfl

private theorem reverse_word (u v : G) (f : Fin 4) :
    faceWord u v (reverseFace f) = (faceWord u v f)⁻¹ := by
  fin_cases f <;> simp [faceWord, reverseFace]

/-- Whole-face extension of the frozen pairing's actual slot map. -/
theorem frozen_face_data (u v : G) (t : Ω) (f : Fin 4) (r : Fin 3) :
    facePair u v (t,f) = (act t (faceWord u v f), reverseFace f) ∧
    facePerm f (faceVertex f r) = faceVertex (reverseFace f) (slotMap f r) := by
  fin_cases f <;> fin_cases r <;> simp [facePair, faceWord, reverseFace, facePerm,
    faceVertex, slotMap]

abbrev Raw (Ω : Type*) := Corner Ω × (Fin 4 → ℝ)

/-- The full closed corner triangle, tagged by the same actual corner class. -/
def Carrier (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) : Set (Raw Ω) :=
  {x | x.2 x.1.2 = 0 ∧ (∀ i, 0 ≤ x.2 i) ∧
    (∑ i, x.2 i) = 1 ∧ label (pairing u v) x.1 = ν}

abbrev Point (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) := ↥(Carrier u v ν)

def move (u v : G) (f : Fin 4) (x : Raw Ω) : Raw Ω :=
  ((act x.1.1 (faceWord u v f), facePerm f x.1.2),
    fun i => x.2 ((facePerm f).symm i))


private theorem move_carrier (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (x : Point u v ν) (f : Fin 4) (hfj : f ≠ x.val.1.2) :
    move u v f x.val ∈ Carrier u v ν := by
  obtain ⟨hj,hn,hs,hν⟩ := x.property
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [move, Equiv.symm_apply_apply] using hj
  · intro i
    exact hn _
  · exact ((facePerm f).symm.sum_comp x.val.2).trans hs
  · obtain ⟨r,hr⟩ : ∃ r : Fin 3, faceVertex f r = x.val.1.2 := by
      generalize x.val.1.2 = j at hfj ⊢
      fin_cases f <;> fin_cases j <;>
        simp_all [faceVertex, Fin.exists_fin_succ]
    have hd := frozen_face_data u v x.val.1.1 f r
    have hc := actual_step u v x.val.1.1 f r
    rw [hd.1, ← hd.2, hr] at hc
    have hl : label (pairing u v) x.val.1 =
        label (pairing u v) (move u v f x.val).1 :=
      Quotient.sound (s := Relation.EqvGen.setoid (cornerRel (pairing u v))) hc
    exact hl.symm.trans hν

/-- The actual affine image in the same frozen corner class, for each permitted side. -/
def pairedPoint (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (x : Point u v ν) (f : Fin 4) (hfj : f ≠ x.val.1.2) : Point u v ν :=
  ⟨move u v f x.val, move_carrier u v x f hfj⟩

private theorem paired_distinct (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (x : Point u v ν) (f : Fin 4) (hfj : f ≠ x.val.1.2) :
    pairedPoint u v x f hfj ≠ x := by
  intro h
  have hj := congrArg (fun z : Point u v ν => z.val.1.2) h
  change facePerm f x.val.1.2 = x.val.1.2 at hj
  generalize x.val.1.2 = j at hj
  fin_cases f <;> fin_cases j <;> simp [facePerm] at hj

/-- The omitted corner is never an additional side of its link triangle. -/
def Step (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (x y : Point u v ν) : Prop :=
  ∃ f : Fin 4, f ≠ x.val.1.2 ∧ x.val.2 f = 0 ∧ y.val = move u v f x.val

abbrev Related (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)} :=
  Relation.EqvGen (Step u v (ν := ν))

/-- Actual ordered edge endpoints; no sorting or endpoint reversal is performed. -/
abbrev Dart (Ω : Type*) := Corner Ω × Fin 4

def dartMove (u v : G) (f : Fin 4) (d : Dart Ω) : Dart Ω :=
  ((act d.1.1 (faceWord u v f), facePerm f d.1.2), facePerm f d.2)

def DartStep (u v : G) (d e : Dart Ω) : Prop :=
  ∃ f : Fin 4, f ≠ d.1.2 ∧ f ≠ d.2 ∧ e = dartMove u v f d

abbrev DartRelated (u v : G) := Relation.EqvGen (DartStep (Ω := Ω) u v)

/-- Strict regions indexed by the original ordered-dart component, not by an assumed cycle. -/
def Neighborhood (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (d : Dart Ω) : Set (Point u v ν) :=
  {x | ∃ k : Fin 4, 1/2 < x.val.2 k ∧ DartRelated u v d (x.val.1,k)}

private theorem move_inverse (u v : G) (f : Fin 4) (x : Raw Ω) :
    move u v (reverseFace f) (move u v f x) = x := by
  apply Prod.ext
  · apply Prod.ext
    · simp [move, reverse_word, act_mul]
    · simp [move, reverse_perm]
  · funext i
    simp [move, reverse_perm]

private theorem step_symmetric (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    {x y : Point u v ν} (h : Step u v x y) : Step u v y x := by
  obtain ⟨f,hfj,hf,hy⟩ := h
  refine ⟨reverseFace f, ?_, ?_, ?_⟩
  · rw [hy]
    change reverseFace f ≠ facePerm f x.val.1.2
    rw [← perm_face]
    exact (facePerm f).injective.ne hfj
  · rw [hy]
    change x.val.2 ((facePerm f).symm (reverseFace f)) = 0
    rw [← perm_face, Equiv.symm_apply_apply]
    exact hf
  · rw [hy, move_inverse]

private theorem step_neighborhood (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (d : Dart Ω) {x y : Point u v ν} (h : Step u v x y)
    (hx : x ∈ Neighborhood u v d) : y ∈ Neighborhood u v d := by
  obtain ⟨f,hfj,hf,hy⟩ := h
  obtain ⟨k,hk,hd⟩ := hx
  have hfk : f ≠ k := by
    intro heq
    subst k
    rw [hf] at hk
    norm_num at hk
  refine ⟨facePerm f k, ?_, ?_⟩
  · rw [hy]
    simpa only [move, Equiv.symm_apply_apply] using hk
  · apply Relation.EqvGen.trans _ _ _ hd
    apply Relation.EqvGen.rel
    refine ⟨f,hfj,hfk,?_⟩
    rw [hy]
    rfl

private theorem chain_neighborhood (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (d : Dart Ω) {x y : Point u v ν} (h : Related u v x y) :
    x ∈ Neighborhood u v d ↔ y ∈ Neighborhood u v d := by
  induction h with
  | rel x y h =>
    exact ⟨step_neighborhood u v d h, step_neighborhood u v d (step_symmetric u v h)⟩
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Interior points and open edge points retain the original side guards. -/
def Interior {u v : G} {ν : Vertex (pairing (Ω := Ω) u v)} (x : Point u v ν) : Prop :=
  ∀ f, f ≠ x.val.1.2 → x.val.2 f ≠ 0

def EdgePoint {u v : G} {ν : Vertex (pairing (Ω := Ω) u v)}
    (x : Point u v ν) (f : Fin 4) : Prop :=
  f ≠ x.val.1.2 ∧ x.val.2 f = 0 ∧
    ∀ g, g ≠ x.val.1.2 → x.val.2 g = 0 → g = f

private theorem step_unique (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    {x y z : Point u v ν} {f : Fin 4} (hx : EdgePoint x f)
    (hy : Step u v x y) (hz : Step u v x z) : y = z := by
  obtain ⟨g,hgj,hg,hy⟩ := hy
  obtain ⟨k,hkj,hk,hz⟩ := hz
  apply Subtype.ext
  rw [hy,hz,hx.2.2 g hgj hg,hx.2.2 k hkj hk]

private theorem step_edge (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    {x y : Point u v ν} {f : Fin 4} (hx : EdgePoint x f)
    (hy : Step u v x y) : EdgePoint y (reverseFace f) := by
  obtain ⟨g,hgj,hg,hy⟩ := hy
  have hgf := hx.2.2 g hgj hg
  subst g
  refine ⟨?_, ?_, ?_⟩
  · rw [hy]
    change reverseFace f ≠ facePerm f x.val.1.2
    rw [← perm_face]
    exact (facePerm f).injective.ne hx.1
  · rw [hy]
    change x.val.2 ((facePerm f).symm (reverseFace f)) = 0
    rw [← perm_face, Equiv.symm_apply_apply]
    exact hx.2.1
  · intro g hgj hg
    rw [hy] at hgj hg
    change g ≠ facePerm f x.val.1.2 at hgj
    change x.val.2 ((facePerm f).symm g) = 0 at hg
    have hj : (facePerm f).symm g ≠ x.val.1.2 := by
      intro hh
      apply hgj
      rw [← hh, Equiv.apply_symm_apply]
    have hh := hx.2.2 _ hj hg
    calc
      g = facePerm f ((facePerm f).symm g) := (Equiv.apply_symm_apply _ _).symm
      _ = facePerm f f := congrArg (facePerm f) hh
      _ = reverseFace f := perm_face f

private theorem edge_chain_forward (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    {a b : Point u v ν} (h : Related u v a b) :
    ∀ {x : Point u v ν} {f : Fin 4}, EdgePoint x f →
      (a = x ∨ Step u v x a) → (b = x ∨ Step u v x b) := by
  intro x f hx ha
  have forward {a b : Point u v ν} (hab : Step u v a b)
      (ha : a = x ∨ Step u v x a) : b = x ∨ Step u v x b := by
    rcases ha with rfl | ha
    · exact Or.inr hab
    · exact Or.inl (step_unique u v (step_edge u v hx ha) hab
        (step_symmetric u v ha))
  have invariant : ∀ {a b : Point u v ν}, Related u v a b →
      ((a = x ∨ Step u v x a) ↔ (b = x ∨ Step u v x b)) := by
    intro a b hh
    induction hh with
    | rel a b hab => exact ⟨forward hab, forward (step_symmetric u v hab)⟩
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (invariant h).mp ha

/-- Complete chains at a positive side point have at most two original representatives. -/
private theorem side_chain_normal_form (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (x y : Point u v ν) (f : Fin 4) (hx : EdgePoint x f) :
    Related u v x y ↔ y = x ∨ Step u v x y := by
  constructor
  · intro h
    exact edge_chain_forward u v h hx (Or.inl rfl)
  · rintro (rfl | h)
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ h


/-- Exactly two representatives at a positive side point, with the actual paired representative. -/
private theorem positive_side_normal_form (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (x y : Point u v ν) (f : Fin 4) (hx : EdgePoint x f) :
    pairedPoint u v x f hx.1 ≠ x ∧
      (Related u v x y ↔ y = x ∨ y = pairedPoint u v x f hx.1) := by
  refine ⟨paired_distinct u v x f hx.1, ?_⟩
  rw [side_chain_normal_form u v x y f hx]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (step_unique u v hx h ⟨f,hx.1,hx.2.1,rfl⟩)
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨f,hx.1,hx.2.1,rfl⟩

/-- Interior points have singleton classes in the full original relation. -/
private theorem interior_normal_form (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (x y : Point u v ν) (hx : Interior x) : Related u v x y ↔ y = x := by
  constructor
  · intro h
    have forward {a b : Point u v ν} (hab : Step u v a b) (ha : a = x) : b = x := by
      subst a
      obtain ⟨f,hfj,hf,_⟩ := hab
      exact False.elim (hx f hfj hf)
    have inv : ∀ {a b : Point u v ν}, Related u v a b → (a = x ↔ b = x) := by
      intro a b hh
      induction hh with
      | rel a b hab => exact ⟨forward hab, forward (step_symmetric u v hab)⟩
      | refl a => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact (inv h).mp rfl
  · rintro rfl
    exact Relation.EqvGen.refl _

/-- Saturation is proved in the full original relation before restricting any chain. -/
private theorem strict_neighborhood_saturated (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (d : Dart Ω) (x y : Point u v ν) (h : Related u v x y) :
    x ∈ Neighborhood u v d ↔ y ∈ Neighborhood u v d :=
  chain_neighborhood u v d h

/-- Reflection through the actual strict neighborhood retains every transitive intermediate. -/
private theorem strict_chain_reflection (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (d : Dart Ω) (x y : ↥(Neighborhood u v (ν := ν) d)) :
    Related u v x.val y.val ↔
      Relation.EqvGen (fun a b : ↥(Neighborhood u v (ν := ν) d) =>
        Step u v a.val b.val) x y := by
  constructor
  · intro h
    have lift : ∀ {a b : Point u v ν}, Related u v a b →
        ∀ (ha : a ∈ Neighborhood u v d) (hb : b ∈ Neighborhood u v d),
        Relation.EqvGen (fun a b : ↥(Neighborhood u v (ν := ν) d) =>
          Step u v a.val b.val) ⟨a,ha⟩ ⟨b,hb⟩ := by
      intro a b hab
      induction hab with
      | rel a b h => exact fun _ _ => Relation.EqvGen.rel _ _ h
      | refl a => exact fun _ _ => Relation.EqvGen.refl _
      | symm a b _ ih => exact fun ha hb => (ih hb ha).symm
      | trans a b c hab hbc ih₁ ih₂ =>
        intro ha hc
        have hb := (strict_neighborhood_saturated u v d a b hab).mp ha
        exact Relation.EqvGen.trans _ _ _ (ih₁ ha hb) (ih₂ hb hc)
    exact lift h x.property y.property
  · intro h
    induction h with
    | rel a b h => exact Relation.EqvGen.rel _ _ h
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Source-specific full-chain analysis, with no cycle or relation-correspondence hypothesis. -/
theorem actual_guarded_point_analysis (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (x y : Point u v ν) :
    (Interior x → (Related u v x y ↔ y = x)) ∧
    (∀ (f : Fin 4) (hx : EdgePoint x f),
      pairedPoint u v x f hx.1 ≠ x ∧
        (Related u v x y ↔ y = x ∨ y = pairedPoint u v x f hx.1)) ∧
    (∀ d : Dart Ω, Related u v x y →
      (x ∈ Neighborhood u v d ↔ y ∈ Neighborhood u v d)) ∧
    (∀ (d : Dart Ω) (hx : x ∈ Neighborhood u v d) (hy : y ∈ Neighborhood u v d),
      Related u v x y ↔
        Relation.EqvGen (fun a b : ↥(Neighborhood u v (ν := ν) d) =>
          Step u v a.val b.val) ⟨x,hx⟩ ⟨y,hy⟩) := by
  refine ⟨interior_normal_form u v x y, positive_side_normal_form u v x y, ?_, ?_⟩
  · exact fun d => strict_neighborhood_saturated u v d x y
  · exact fun d hx hy => strict_chain_reflection u v d ⟨x,hx⟩ ⟨y,hy⟩

end D5.S3.Geometry.Gluing.ActualLinkCornerChains
