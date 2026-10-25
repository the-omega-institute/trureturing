/- GID: D5/S3/Geometry/Gluing/ActualLinkCyclicPresentation
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/ActualLinkCyclicPresentation
   mirror-E: none(waiver:actual-link-side-orbits-and-generated-cyclic-seams)
   anchors: [mathlib/module/Mathlib.Logic.Relation,
     mathlib/module/Mathlib.Data.Fintype.Quotient]
   utility: none
   digest: Actual link triangles give signed side-orbit words and the original flag quotient. -/

import D5.S3.Geometry.Gluing.CyclicP1GeneratedVertices
import D5.S3.Geometry.Gluing.ActualEndpointReturnClasses

set_option autoImplicit false
noncomputable section

namespace D5.S3.Geometry.Gluing.ActualLinkCyclicPresentation

open D5.S3.Geometry.Hyperideal.ActualCornerTransport
open D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits
open D5.S3.Geometry.Gluing.ActualLinkCornerChains
open D5.S3.Geometry.Gluing.ActualEndpointReturnClasses

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

/-- Every actual corner occurrence is a separate triangle, even when words coincide. -/
def Face (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :=
  {c : Corner Ω // label (pairing u v) c = ν}

/-- A side remembers the sheet, corner and omitted tetrahedral face. -/
def Side (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :=
  {s : Corner Ω × Fin 4 // s.2 ≠ s.1.2 ∧ label (pairing u v) s.1 = ν}

private def next (r : Fin 3) : Fin 3 := ![1, 2, 0] r
private def prev (r : Fin 3) : Fin 3 := ![2, 0, 1] r

/-- Inverse to the increasing enumeration of the vertices other than j.
The unused diagonal entries have no geometric meaning. -/
private def localIndex (j k : Fin 4) : Fin 3 :=
  ![![0,0,1,2], ![0,0,1,2], ![0,1,0,2], ![0,1,2,0]] j k

private theorem local_vertex_ne (j : Fin 4) (r : Fin 3) : faceVertex j r ≠ j := by
  fin_cases j <;> fin_cases r <;> decide

private theorem vertex_index (j k : Fin 4) (h : k ≠ j) :
    faceVertex j (localIndex j k) = k := by
  fin_cases j <;> fin_cases k <;>
    simp_all [localIndex, faceVertex]

/-- Side r omits local vertex r and runs from next r to prev r. -/
def faceSide (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (c : Face u v ν) (r : Fin 3) : Side u v ν :=
  ⟨(c.val, faceVertex c.val.2 r), local_vertex_ne c.val.2 r, c.property⟩

private def sideFace (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) : Face u v ν := ⟨s.val.1, s.property.2⟩

private def sideIndex (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) : Fin 3 := localIndex s.val.1.2 s.val.2

private theorem side_enumeration (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) : faceSide u v (sideFace u v s) (sideIndex u v s) = s := by
  apply Subtype.ext
  exact Prod.ext rfl (vertex_index _ _ s.property.1)

private def tip (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) (b : Bool) : Fin 4 :=
  faceVertex s.val.1.2 (if b then prev (sideIndex u v s) else next (sideIndex u v s))

/-- Literal ordered flags at the two ends of a local side. -/
def sideFlag (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) (b : Bool) : Flag u v ν :=
  ⟨(s.val.1, tip u v s b), by
    refine ⟨?_, s.property.2⟩
    exact (local_vertex_ne s.val.1.2 _).symm⟩

/-- The affine parameter of this locally oriented side, with its actual corner tag. -/
def sideParameter (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) (t : ℝ) : Raw Ω :=
  (s.val.1, fun i => if i = tip u v s false then 1 - t
    else if i = tip u v s true then t else 0)

private theorem tip_guard (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) (b : Bool) : s.val.2 ≠ tip u v s b := by
  obtain ⟨c,r,hs⟩ : ∃ (c : Face u v ν) (r : Fin 3), faceSide u v c r = s :=
    ⟨sideFace u v s, sideIndex u v s, side_enumeration u v s⟩
  subst s
  rcases c with ⟨⟨t,j⟩,hl⟩
  fin_cases j <;> fin_cases r <;> cases b <;>
    simp [faceSide, sideIndex, tip, localIndex, faceVertex, next, prev]

/-- The actual affine transport supplies the target corner label. -/
def pairedSide (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) : Side u v ν :=
  ⟨((act s.val.1.1 (faceWord u v s.val.2), facePerm s.val.2 s.val.1.2),
      reverseFace s.val.2), by
    constructor
    · have h := s.property.1
      generalize s.val.1.2 = j at h ⊢
      generalize s.val.2 = f at h ⊢
      fin_cases j <;> fin_cases f <;> simp_all [reverseFace, facePerm]
    · exact (pairedPoint u v (endpoint u v (sideFlag u v s false))
        s.val.2 s.property.1).property.2.2.2⟩

private theorem pairedSide_involutive (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} : Function.Involutive (pairedSide u v (ν := ν)) := by
  rintro ⟨⟨⟨t,j⟩,f⟩,hf,hl⟩
  apply Subtype.ext
  fin_cases f <;> fin_cases j <;>
    simp [pairedSide, facePerm, reverseFace, faceWord, act_mul]

private theorem pairedSide_ne (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) : pairedSide u v s ≠ s := by
  intro h
  have h := congrArg (fun a : Side u v ν => a.val.2) h
  change reverseFace s.val.2 = s.val.2 at h
  generalize s.val.2 = f at h
  fin_cases f <;> simp [reverseFace] at h

/-- This Boolean records the action of the actual face permutation on the two
local endpoints; it does not compare globally identified vertex classes. -/
private def transportFlip (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) : Bool :=
  decide (facePerm s.val.2 (tip u v s false) = tip u v (pairedSide u v s) true)

private theorem endpoint_transport (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (s : Side u v ν) (b : Bool) :
    (sideFlag u v (pairedSide u v s) (Bool.xor b (transportFlip u v s))).val =
      dartMove u v s.val.2 (sideFlag u v s b).val := by
  rcases s with ⟨⟨⟨t,j⟩,f⟩,hf,hl⟩
  apply Prod.ext
  · rfl
  · fin_cases j <;> fin_cases f <;> cases b <;>
      simp_all [sideFlag, tip, sideIndex, localIndex, transportFlip,
        pairedSide, facePerm, faceVertex, reverseFace, next, prev, dartMove]

private theorem flip_reverse (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) : transportFlip u v (pairedSide u v s) = transportFlip u v s := by
  rcases s with ⟨⟨⟨t,j⟩,f⟩,hf,hl⟩
  fin_cases j <;> fin_cases f <;>
    simp_all [transportFlip, pairedSide, tip, sideIndex, localIndex,
      facePerm, faceVertex, reverseFace, next, prev]

private theorem parameter_transport (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (s : Side u v ν) (t : ℝ) :
    move u v s.val.2 (sideParameter u v s t) =
      sideParameter u v (pairedSide u v s) (if transportFlip u v s then 1 - t else t) := by
  apply Prod.ext
  · rfl
  · funext i
    rcases s with ⟨⟨⟨a,j⟩,f⟩,hf,hl⟩
    fin_cases j <;> fin_cases f <;> fin_cases i <;>
      simp_all [move, sideParameter, tip, sideIndex, localIndex, transportFlip,
        pairedSide, facePerm, faceVertex, reverseFace, next, prev] <;> ring

private theorem paired_flags_related (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (s : Side u v ν) (b : Bool) :
    DartRelated u v (sideFlag u v s b).val
      (sideFlag u v (pairedSide u v s) (Bool.xor b (transportFlip u v s))).val :=
  Relation.EqvGen.rel _ _ ⟨s.val.2, s.property.1, tip_guard u v s b,
    endpoint_transport u v s b⟩

/-- Two sides are equivalent exactly when they are the actual paired occurrences. -/
private def sideSetoid (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :
    Setoid (Side u v ν) where
  r s t := t = s ∨ t = pairedSide u v s
  iseqv := by
    refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
    · intro s t h
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (pairedSide_involutive u v s).symm
    · intro s t a hst hta
      rcases hst with rfl | rfl
      · exact hta
      · rcases hta with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (pairedSide_involutive u v s)

private abbrev Edge (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :=
  Quotient (sideSetoid u v ν)

private def orbit (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) : Edge u v ν := Quotient.mk _ s

private theorem orbit_paired (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) : orbit u v (pairedSide u v s) = orbit u v s :=
  (Quotient.sound (s := sideSetoid u v ν) (Or.inr rfl)).symm

private theorem representative_exists (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (e : Edge u v ν) :
    ∃ s : Side u v ν, orbit u v s = e := by
  refine Quotient.inductionOn e ?_
  intro s
  exact ⟨s, rfl⟩

private def representative (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (e : Edge u v ν) : Side u v ν := Classical.choose (representative_exists u v e)

private theorem representative_orbit (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (e : Edge u v ν) :
    orbit u v (representative u v e) = e := Classical.choose_spec (representative_exists u v e)

private theorem representative_cases (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (s : Side u v ν) :
    s = representative u v (orbit u v s) ∨
      s = pairedSide u v (representative u v (orbit u v s)) :=
  Quotient.exact (representative_orbit u v (orbit u v s))

variable [Finite Ω]

private instance faceFinite (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :
    Finite (Face u v ν) := by unfold Face; infer_instance
private instance sideFinite (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :
    Finite (Side u v ν) := by unfold Side; infer_instance
private instance faceFintype (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :
    Fintype (Face u v ν) := Fintype.ofFinite _
private instance edgeFintype (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :
    Fintype (Edge u v ν) := Fintype.ofFinite _

private def edgeEnumeration (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :=
  Fintype.equivFin (Edge u v ν)

private def edgeName (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) : Fin (Fintype.card (Edge u v ν)) := edgeEnumeration u v ν (orbit u v s)

private def coordinate (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) (b : Bool) : Bool := by
  classical
  exact if s = representative u v (orbit u v s) then b
    else Bool.xor b (transportFlip u v (representative u v (orbit u v s)))

private def code (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) (b : Bool) : CyclicP1GeneratedVertices.Endpoint (Fintype.card (Edge u v ν)) :=
  (edgeName u v s, coordinate u v s b)

private def occurrence (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (s : Side u v ν) : CyclicP1GeneratedVertices.SignedDart (Fin (Fintype.card (Edge u v ν))) :=
  if coordinate u v s false then .neg (edgeName u v s) else .pos (edgeName u v s)

private theorem occurrence_ends (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (s : Side u v ν) :
    CyclicP1GeneratedVertices.initial (occurrence u v s) = code u v s false ∧
    CyclicP1GeneratedVertices.terminal (occurrence u v s) = code u v s true ∧
    (occurrence u v s).edge = edgeName u v s := by
  classical
  have hc : coordinate u v s true = !(coordinate u v s false) := by
    unfold coordinate
    split_ifs <;> cases transportFlip u v (representative u v (orbit u v s)) <;> rfl
  cases h : coordinate u v s false <;>
    simp [occurrence, code, hc, h, CyclicP1GeneratedVertices.initial,
      CyclicP1GeneratedVertices.terminal, CyclicP1GeneratedVertices.SignedDart.edge]

private theorem occurrence_endpoint (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (s : Side u v ν) (b : Bool) :
    (if b then CyclicP1GeneratedVertices.terminal (occurrence u v s)
      else CyclicP1GeneratedVertices.initial (occurrence u v s)) = code u v s b := by
  cases b
  · exact (occurrence_ends u v s).1
  · exact (occurrence_ends u v s).2.1

private theorem code_representative (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (e : Edge u v ν) (b : Bool) :
    code u v (representative u v e) b = (edgeEnumeration u v ν e, b) := by
  classical
  simp [code, edgeName, coordinate, representative_orbit]

private theorem code_paired (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (s : Side u v ν) (b : Bool) :
    code u v (pairedSide u v s) (Bool.xor b (transportFlip u v s)) = code u v s b := by
  classical
  have ho := orbit_paired u v s
  apply Prod.ext
  · exact congrArg (edgeEnumeration u v ν) ho
  · change coordinate u v (pairedSide u v s) _ = coordinate u v s b
    unfold coordinate
    rw [ho]
    rcases representative_cases u v s with h | h
    · have hn : pairedSide u v s ≠ representative u v (orbit u v s) := by
        rw [← h]; exact pairedSide_ne u v s
      rw [if_neg hn, if_pos h, ← h]
      cases b <;> cases transportFlip u v s <;> rfl
    · have hn : s ≠ representative u v (orbit u v s) := by
        intro he
        exact pairedSide_ne u v (representative u v (orbit u v s)) (h.symm.trans he)
      have hp : pairedSide u v s = representative u v (orbit u v s) := by
        rw [h, pairedSide_involutive u v]
      rw [if_pos hp, if_neg hn]
      congr 1
      rw [h, flip_reverse]

private def rawFlag (u v : G) (ν : Vertex (pairing (Ω := Ω) u v))
    (x : CyclicP1GeneratedVertices.Endpoint (Fintype.card (Edge u v ν))) : Flag u v ν :=
  sideFlag u v (representative u v ((edgeEnumeration u v ν).symm x.1)) x.2

private theorem rawFlag_code (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (s : Side u v ν) (b : Bool) :
    DartRelated u v (rawFlag u v ν (code u v s b)).val (sideFlag u v s b).val := by
  classical
  change DartRelated u v
    (sideFlag u v (representative u v ((edgeEnumeration u v ν).symm
      (edgeEnumeration u v ν (orbit u v s)))) (coordinate u v s b)).val _
  rw [Equiv.symm_apply_apply]
  rcases representative_cases u v s with h | h
  · have hc : coordinate u v s b = b := by
      unfold coordinate
      exact if_pos h
    rw [hc, ← h]
    exact Relation.EqvGen.refl _
  · have hn : s ≠ representative u v (orbit u v s) := by
      intro he
      exact pairedSide_ne u v (representative u v (orbit u v s)) (h.symm.trans he)
    have hc : coordinate u v s b =
        Bool.xor b (transportFlip u v (representative u v (orbit u v s))) := by
      simp [coordinate, hn]
    rw [hc]
    have hh := paired_flags_related u v (representative u v (orbit u v s))
      (Bool.xor b (transportFlip u v (representative u v (orbit u v s))))
    have hb : Bool.xor (Bool.xor b (transportFlip u v
        (representative u v (orbit u v s))))
        (transportFlip u v (representative u v (orbit u v s))) = b := by
      cases b <;> cases transportFlip u v (representative u v (orbit u v s)) <;> rfl
    simpa only [hb, ← h] using hh

private def triangleWord (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (c : Face u v ν) : List (CyclicP1GeneratedVertices.SignedDart (Fin (Fintype.card (Edge u v ν)))) :=
  [occurrence u v (faceSide u v c 0), occurrence u v (faceSide u v c 1),
    occurrence u v (faceSide u v c 2)]

private def presentation (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :
    CyclicP1GeneratedVertices.FiniteCyclicPresentation where
  edgeCount := Fintype.card (Edge u v ν)
  faces := List.ofFn (fun i : Fin (Fintype.card (Face u v ν)) =>
    triangleWord u v ((Fintype.equivFin (Face u v ν)).symm i))

private def facePosition (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :
    Face u v ν ≃ Fin (presentation u v ν).faces.length :=
  (Fintype.equivFin (Face u v ν)).trans
    (finCongr (by simp [presentation])).symm

private theorem word_at_position (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (c : Face u v ν) :
    (presentation u v ν).faces.get (facePosition u v ν c) = triangleWord u v c := by
  simp [presentation, facePosition]

private theorem word_mem (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (c : Face u v ν) : triangleWord u v c ∈ (presentation u v ν).faces := by
  rw [← word_at_position u v c]
  exact List.get_mem _ _

/-- A literal P1 seam joins two occurrences of the same vertex of one triangle. -/
private theorem seam_flags (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (c : Face u v ν) (r : Fin 3) :
    sideFlag u v (faceSide u v c r) true =
      sideFlag u v (faceSide u v c (next r)) false := by
  apply Subtype.ext
  apply Prod.ext rfl
  rcases c with ⟨⟨t,j⟩,hl⟩
  fin_cases j <;> fin_cases r <;>
    rfl

private theorem triangle_seam (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (c : Face u v ν) (r : Fin 3) :
    CyclicP1GeneratedVertices.Related (presentation u v ν) (code u v (faceSide u v c r) true)
      (code u v (faceSide u v c (next r)) false) := by
  apply Relation.EqvGen.rel
  refine ⟨triangleWord u v c, word_mem u v c, ?_⟩
  have h0 := occurrence_ends u v (faceSide u v c 0)
  have h1 := occurrence_ends u v (faceSide u v c 1)
  have h2 := occurrence_ends u v (faceSide u v c 2)
  fin_cases r <;>
    simp [triangleWord, CyclicP1GeneratedVertices.cyclePairs, CyclicP1GeneratedVertices.seams, next, ← h0.1, ← h0.2.1,
      ← h1.1, ← h1.2.1, ← h2.1, ← h2.2.1]

private def selectedSide (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (d : Flag u v ν) : Side u v ν :=
  faceSide u v ⟨d.val.1, d.property.2⟩ (prev (localIndex d.val.1.2 d.val.2))

private theorem selected_flag (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (d : Flag u v ν) : sideFlag u v (selectedSide u v d) false = d := by
  apply Subtype.ext
  apply Prod.ext rfl
  rcases d with ⟨⟨⟨t,j⟩,k⟩,hjk,hl⟩
  fin_cases j <;> fin_cases k <;>
    simp_all [sideFlag, selectedSide, faceSide, tip, sideIndex,
      localIndex, faceVertex, next, prev]

private def flagCode (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (d : Flag u v ν) : CyclicP1GeneratedVertices.Endpoint (presentation u v ν).edgeCount :=
  code u v (selectedSide u v d) false

/-- At either end of a side, selecting the outgoing occurrence changes only a
literal triangle seam. This statement precedes any quotient construction. -/
private theorem flagCode_incidence (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (s : Side u v ν) (b : Bool) :
    CyclicP1GeneratedVertices.Related (presentation u v ν) (flagCode u v (sideFlag u v s b)) (code u v s b) := by
  obtain ⟨c,r,hs⟩ : ∃ (c : Face u v ν) (r : Fin 3), faceSide u v c r = s :=
    ⟨sideFace u v s, sideIndex u v s, side_enumeration u v s⟩
  subst s
  cases b with
  | false =>
    have hs : selectedSide u v (sideFlag u v (faceSide u v c r) false) = faceSide u v c r := by
      apply Subtype.ext
      apply Prod.ext rfl
      rcases c with ⟨⟨t,j⟩,hl⟩
      fin_cases j <;> fin_cases r <;> rfl
    rw [flagCode, hs]
    exact Relation.EqvGen.refl _
  | true =>
    have hs : selectedSide u v (sideFlag u v (faceSide u v c r) true) =
        faceSide u v c (next r) := by
      apply Subtype.ext
      apply Prod.ext rfl
      rcases c with ⟨⟨t,j⟩,hl⟩
      fin_cases j <;> fin_cases r <;> rfl
    rw [flagCode, hs]
    exact (triangle_seam u v c r).symm

private theorem flag_on_side (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (d : Flag u v ν) (f : Fin 4) (hfj : f ≠ d.val.1.2) (hfk : f ≠ d.val.2) :
    ∃ b : Bool, sideFlag u v (⟨(d.val.1,f),hfj,d.property.2⟩ : Side u v ν) b = d := by
  rcases d with ⟨⟨⟨t,j⟩,k⟩,hjk,hl⟩
  fin_cases j <;> fin_cases k <;> fin_cases f <;>
    first
    | exact False.elim (hjk rfl)
    | exact False.elim (hfj rfl)
    | exact False.elim (hfk rfl)
    | exact ⟨false, rfl⟩
    | exact ⟨true, rfl⟩

/-- Every original guarded dart generator is a paired-side identification
between two triangle seams. No relation-correspondence premise is used. -/
private theorem dartStep_to_seams (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (d e : Flag u v ν)
    (h : DartStep u v d.val e.val) :
    CyclicP1GeneratedVertices.Related (presentation u v ν) (flagCode u v d) (flagCode u v e) := by
  obtain ⟨f,hfj,hfk,he⟩ := h
  let s : Side u v ν := ⟨(d.val.1,f),hfj,d.property.2⟩
  obtain ⟨b,hb⟩ := flag_on_side u v d f hfj hfk
  have ht : sideFlag u v (pairedSide u v s) (Bool.xor b (transportFlip u v s)) = e := by
    apply Subtype.ext
    calc
      _ = dartMove u v f (sideFlag u v s b).val := endpoint_transport u v s b
      _ = dartMove u v f d.val := congrArg (fun a : Flag u v ν => dartMove u v f a.val) hb
      _ = e.val := he.symm
  have hd := flagCode_incidence u v s b
  have he' := flagCode_incidence u v (pairedSide u v s) (Bool.xor b (transportFlip u v s))
  rw [hb] at hd
  rw [ht, code_paired] at he'
  exact hd.trans _ _ _ he'.symm

private theorem dartRelated_to_seams (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (d e : Flag u v ν)
    (h : DartRelated u v d.val e.val) :
    CyclicP1GeneratedVertices.Related (presentation u v ν) (flagCode u v d) (flagCode u v e) := by
  have hr := ((actual_endpoint_return_classes u v ν).2.1 d e).mp h
  induction hr with
  | rel d e h => exact dartStep_to_seams u v d e h
  | refl d => exact Relation.EqvGen.refl _
  | symm d e _ ih => exact ih.symm
  | trans d e a _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂

private def endpointClass (u v : G) (ν : Vertex (pairing (Ω := Ω) u v))
    (x : CyclicP1GeneratedVertices.Endpoint (presentation u v ν).edgeCount) : FlagQuotient u v ν :=
  Quotient.mk _ (rawFlag u v ν x)

private theorem endpointClass_code (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} (s : Side u v ν) (b : Bool) :
    endpointClass u v ν (code u v s b) = Quotient.mk _ (sideFlag u v s b) :=
  Quotient.sound (rawFlag_code u v s b)

/-- Every literal face seam has equal images in the original DartRelated
quotient: first transport the chosen side representative, then use the common
local vertex of that same triangle. -/
private theorem seam_to_flags (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    {x y : CyclicP1GeneratedVertices.Endpoint (presentation u v ν).edgeCount}
    (h : CyclicP1GeneratedVertices.Step (presentation u v ν) x y) : endpointClass u v ν x = endpointClass u v ν y := by
  obtain ⟨w,hw,hxy⟩ := h
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
  let c := (Fintype.equivFin (Face u v ν)).symm i
  change (x,y) ∈ CyclicP1GeneratedVertices.cyclePairs (triangleWord u v c) at hxy
  have localSeam (r : Fin 3) :
      endpointClass u v ν (CyclicP1GeneratedVertices.terminal (occurrence u v (faceSide u v c r))) =
        endpointClass u v ν (CyclicP1GeneratedVertices.initial (occurrence u v (faceSide u v c (next r)))) := by
    rw [(occurrence_ends u v _).2.1, (occurrence_ends u v _).1,
      endpointClass_code, endpointClass_code, seam_flags]
  simp only [triangleWord, CyclicP1GeneratedVertices.cyclePairs, CyclicP1GeneratedVertices.seams, List.mem_cons,
    List.mem_singleton, Prod.mk.injEq] at hxy
  rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact localSeam 0
  · exact localSeam 1
  · exact localSeam 2

private theorem seams_to_flags (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    {x y : CyclicP1GeneratedVertices.Endpoint (presentation u v ν).edgeCount}
    (h : CyclicP1GeneratedVertices.Related (presentation u v ν) x y) : endpointClass u v ν x = endpointClass u v ν y := by
  induction h with
  | rel x y h => exact seam_to_flags u v h
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private def vertexMap (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :
    CyclicP1GeneratedVertices.Vertices (presentation u v ν) → FlagQuotient u v ν :=
  Quotient.lift (endpointClass u v ν) (fun _ _ h => seams_to_flags u v h)

private def flagMap (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :
    FlagQuotient u v ν → CyclicP1GeneratedVertices.Vertices (presentation u v ν) :=
  Quotient.map (flagCode u v) (fun d e h => dartRelated_to_seams u v d e h)

private def verticesEquiv (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :
    CyclicP1GeneratedVertices.Vertices (presentation u v ν) ≃ FlagQuotient u v ν where
  toFun := vertexMap u v ν
  invFun := flagMap u v ν
  left_inv := by
    intro a
    refine Quotient.inductionOn a ?_
    rintro ⟨e,b⟩
    change Quotient.mk _ (flagCode u v (rawFlag u v ν (e,b))) = Quotient.mk _ (e,b)
    apply Quotient.sound
    have h := flagCode_incidence u v
      (representative u v ((edgeEnumeration u v ν).symm e)) b
    simpa only [rawFlag, code_representative, Equiv.apply_symm_apply] using h
  right_inv := by
    intro a
    refine Quotient.inductionOn a ?_
    intro d
    change endpointClass u v ν (flagCode u v d) = Quotient.mk _ d
    rw [flagCode, endpointClass_code, selected_flag]

private theorem every_edge_occurs (u v : G) (ν : Vertex (pairing (Ω := Ω) u v))
    (e : Fin (presentation u v ν).edgeCount) : CyclicP1GeneratedVertices.Occurs (presentation u v ν) e := by
  let s := representative u v ((edgeEnumeration u v ν).symm e)
  let c := sideFace u v s
  let r := sideIndex u v s
  refine ⟨triangleWord u v c, word_mem u v c, occurrence u v (faceSide u v c r), ?_, ?_⟩
  · fin_cases r <;> simp [triangleWord]
  · rw [(occurrence_ends u v _).2.2, side_enumeration]
    change edgeEnumeration u v ν
      (orbit u v (representative u v ((edgeEnumeration u v ν).symm e))) = e
    rw [representative_orbit, Equiv.apply_symm_apply]

/-- Finite signed words of the actual link, retaining every triangle occurrence.
The edge-name fibers are the two actual paired sides. The vertex equivalence
commutes at both ends of every occurrence with the unchanged ordered Flag.
This is a combinatorial quotient equivalence, with no assertion about full
affine-point quotients, manifold charts, orientation, Euler characteristic or genus. -/
theorem actual_link_cyclic_vertices (u v : G)
    (ν : Vertex (pairing (Ω := Ω) u v)) :
    ∃ (P : CyclicP1GeneratedVertices.FiniteCyclicPresentation)
      (facepositionequiv : Face u v ν ≃ Fin P.faces.length)
      (name : Side u v ν → Fin P.edgeCount)
      (dart : Side u v ν → CyclicP1GeneratedVertices.SignedDart (Fin P.edgeCount))
      (flip : Side u v ν → Bool)
      (vertices : CyclicP1GeneratedVertices.Vertices P ≃ FlagQuotient u v ν),
      (∀ c : Face u v ν, P.faces.get (facepositionequiv c) =
        [dart (faceSide u v c 0), dart (faceSide u v c 1), dart (faceSide u v c 2)]) ∧
      (∀ i : Fin P.faces.length, (P.faces.get i).length = 3) ∧
      (∀ e : Fin P.edgeCount, CyclicP1GeneratedVertices.Occurs P e) ∧
      (∀ s : Side u v ν, (dart s).edge = name s) ∧
      (∀ s t : Side u v ν, name s = name t ↔ t = s ∨ t = pairedSide u v s) ∧
      (Function.Involutive (pairedSide u v (ν := ν))) ∧
      (∀ s : Side u v ν, pairedSide u v s ≠ s) ∧
      (∀ (s : Side u v ν) (b : Bool),
        (sideFlag u v (pairedSide u v s) (Bool.xor b (flip s))).val =
          dartMove u v s.val.2 (sideFlag u v s b).val) ∧
      (∀ (s : Side u v ν) (t : ℝ),
        move u v s.val.2 (sideParameter u v s t) =
          sideParameter u v (pairedSide u v s) (if flip s then 1 - t else t)) ∧
      (∀ (s : Side u v ν) (b : Bool),
        (if Bool.xor b (flip s) then CyclicP1GeneratedVertices.terminal (dart (pairedSide u v s))
          else CyclicP1GeneratedVertices.initial (dart (pairedSide u v s))) =
        (if b then CyclicP1GeneratedVertices.terminal (dart s)
          else CyclicP1GeneratedVertices.initial (dart s))) ∧
      (∀ s : Side u v ν,
        vertices (Quotient.mk _ (CyclicP1GeneratedVertices.initial (dart s))) = Quotient.mk _ (sideFlag u v s false) ∧
        vertices (Quotient.mk _ (CyclicP1GeneratedVertices.terminal (dart s))) = Quotient.mk _ (sideFlag u v s true)) := by
  classical
  refine ⟨presentation u v ν, facePosition u v ν, edgeName u v, occurrence u v, transportFlip u v,
    verticesEquiv u v ν, word_at_position u v, ?_, every_edge_occurs u v ν,
    fun s => (occurrence_ends u v s).2.2, ?_, pairedSide_involutive u v,
    pairedSide_ne u v, endpoint_transport u v, parameter_transport u v, ?_, ?_⟩
  · intro i
    obtain ⟨c,rfl⟩ := (facePosition u v ν).surjective i
    rw [word_at_position]
    rfl
  · intro s t
    constructor
    · intro h
      exact Quotient.exact ((edgeEnumeration u v ν).injective h)
    · intro h
      exact congrArg (edgeEnumeration u v ν) (Quotient.sound h)
  · intro s b
    rw [occurrence_endpoint, occurrence_endpoint, code_paired]
  · intro s
    constructor
    · change endpointClass u v ν (CyclicP1GeneratedVertices.initial (occurrence u v s)) = _
      rw [(occurrence_ends u v s).1, endpointClass_code]
    · change endpointClass u v ν (CyclicP1GeneratedVertices.terminal (occurrence u v s)) = _
      rw [(occurrence_ends u v s).2.1, endpointClass_code]

end D5.S3.Geometry.Gluing.ActualLinkCyclicPresentation
