/- GID: D5/S3/Topology/RankColouredTetrahedron
   generality: I
   mirror-B: D5/B/S3/Topology/RankColouredTetrahedron
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Proper rank colours pull the chamber constraints back to arbitrary faces. -/

import D5.S3.Topology.OrdinaryTetrahedronCollar

/-! A rank colouring provides one set of coordinates for the local
tetrahedron certificate over every old face. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.RankColouredTetrahedron

open BarycentricGraphDistance (Face subdivisionGraph)
open BarycentricNeighborhoodIteration (iteratedAmbient)
open GraphSubdivisionIntervals (originalSupport)
open TetrahedronCollar16

noncomputable section

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

variable {X : Type} {K : PreAbstractSimplicialComplex X}

private theorem map_face (colour : X → Fin 4) (s : Finset X) (hs : s ∈ K) :
    @Finset.image X (Fin 4) (Classical.decEq (Fin 4)) colour s ∈ orderedTetrahedron := by
  exact ⟨(K.isRelLowerSet_faces hs).1.image _, Finset.subset_univ _⟩

private def localVertex (colour : X → Fin 4) (v : Face (iteratedAmbient K 2).2) :
    Face (iteratedAmbient orderedTetrahedron 2).2 :=
  (OrdinarySubdivisionMap.iterate colour (map_face colour) 3).val v

private def tableEquiv : V₃ ≃ Face (iteratedAmbient orderedTetrahedron 2).2 :=
  Equiv.ofBijective literalFace₃ literalFace₃_bijective

/-- A vertex has one certificate row, irrespective of the choice of
any larger chamber containing its old support. -/
def row (colour : X → Fin 4) (v : Face (iteratedAmbient K 2).2) : V₃ :=
  tableEquiv.symm (localVertex colour v)

private theorem row_eq (colour : X → Fin 4) (v : Face (iteratedAmbient K 2).2) :
    literalFace₃ (row colour v) = localVertex colour v :=
  tableEquiv.apply_symm_apply _

/-- A rank colour occurs in the certificate's old carrier exactly when
it occurs on the old support of the actual subdivided vertex. -/
theorem mem_carrier_row (colour : X → Fin 4) (v : Face (iteratedAmbient K 2).2)
    (a : Fin 4) :
    a.val ∈ carrier (row colour v) ↔
      ∃ x ∈ originalSupport K 3 {v}, colour x = a := by
  rw [← literalFace₃_carrier (row colour v) a, row_eq]
  have hs := OrdinarySubdivisionMap.originalSupport_image colour (map_face colour) 3
    ({v} : Finset (Face (iteratedAmbient K 2).2))
  change originalSupport orderedTetrahedron 3
    (({v} : Finset _).image (localVertex colour)) =
      (originalSupport K 3 {v}).image colour at hs
  rw [Finset.image_singleton] at hs
  rw [hs, Finset.mem_image]

/-- A pulled-back certificate collar is the genuine collar defined by
the corresponding old vertex colour, even if the colour map folds faces. -/
theorem row_inCollar (colour : X → Fin 4) (c : Color)
    (v : Face (iteratedAmbient K 2).2) :
    InCollar c (row colour v) ↔
      OrdinarySubdivisionMap.inTwoCutCollar (hasColour c ∘ colour) v := by
  rw [← literalFace₃_inCollar c (row colour v), row_eq]
  exact OrdinarySubdivisionMap.inTwoCutCollar_iterate_iff colour (map_face colour)
    (hasColour c ∘ colour) (hasColour c) (fun _ => rfl) v

private theorem localVertex_le (colour : X → Fin 4)
    {u v : Face (iteratedAmbient K 2).2} (h : u ≤ v) :
    localVertex colour u ≤ localVertex colour v := by
  change u.val.image (OrdinarySubdivisionMap.iterate colour (map_face colour) 2).val ⊆
    v.val.image (OrdinarySubdivisionMap.iterate colour (map_face colour) 2).val
  exact Finset.image_subset_image h

/-- Colouring sends a subdivision edge to a certificate edge or
collapses it to one row. -/
theorem row_eq_or_adj (colour : X → Fin 4) {u v : Face (iteratedAmbient K 2).2}
    (h : (subdivisionGraph (iteratedAmbient K 2).2).Adj u v) :
    row colour u = row colour v ∨ graph.Adj (row colour u) (row colour v) := by
  by_cases he : row colour u = row colour v
  · exact Or.inl he
  · refine Or.inr ((literalFace₃_adj _ _).2 ?_)
    rw [row_eq, row_eq]
    have hne : localVertex colour u ≠ localVertex colour v := fun h => he (congrArg tableEquiv.symm h)
    rcases h with h | h
    · exact Or.inl (lt_of_le_of_ne (localVertex_le colour h.le) hne)
    · exact Or.inr (lt_of_le_of_ne (localVertex_le colour h.le) hne.symm)

/-- No subdivision edge joins a main region to an extra region of the
same colour after pulling back the tetrahedron labels. -/
theorem main_extra_separated (colour : X → Fin 4) {c : Color}
    {u v : Face (iteratedAmbient K 2).2} (hu : Main c (row colour u))
    (hv : Extra c (row colour v)) :
    ¬ (subdivisionGraph (iteratedAmbient K 2).2).Adj u v := by
  intro h
  rcases row_eq_or_adj colour h with he | h
  · have hs := hu.2
    rw [he, hv.2] at hs
    cases hs
  · exact TetrahedronCollar16.main_extra_separated hu hv h



/-- The main region of the actual third subdivision given by the pulled-back
chamber rows. -/
def mainRegion (colour : X → Fin 4) (c : Color) : Set (Face (iteratedAmbient K 2).2) :=
  {u | Main c (row colour u)}

private def readRow (colour : X → Fin 4) (c : Color) :
    mainRegion (K := K) colour c → TetrahedronCollar16.onMain c :=
  fun u => ⟨row colour u.val, u.property⟩

/-- One relative interval homotopy works simultaneously on all old chambers.
The equality case accounts for edges collapsed by the colour map. -/
theorem relative_retraction_on_rows (colour : X → Fin 4) (c : Color) :
    let region := mainRegion (K := K) colour c
    let G := (subdivisionGraph (iteratedAmbient K 2).2).induce region
    let e := readRow (K := K) colour c
    let S := e ⁻¹' endpointFibers c
    let r := fun x : region => retractionHeight c (row colour x.val)
    Relation.ReflTransGen (PathContiguity.RelativeContiguous G 8 S r) r
      (fun x => height (row colour x.val) / 2) := by
  intro region G e S r
  let lift (a : TetrahedronCollar16.onMain c → ℕ) (x : region) := a (e x)
  refine Relation.ReflTransGen.lift lift ?_ _ _ (TetrahedronCollar16.relative_retraction c)
  intro a b h
  obtain ⟨ha, hb, har, hbr, hc⟩ := h
  refine ⟨fun x => ha (e x), fun x => hb (e x), fun _ hx => har hx, fun _ hx => hbr hx, ?_⟩
  intro u v huv
  apply hc
  rcases huv with he | hadj
  · exact Or.inl (congrArg e he)
  · rcases row_eq_or_adj colour (show (subdivisionGraph (iteratedAmbient K 2).2).Adj u.val v.val
      from hadj) with he | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr he

private theorem support_mono (m : ℕ) :
    Monotone (originalSupport K m) := by
  induction m with
  | zero => exact monotone_id
  | succ m ih =>
    intro s t h
    exact ih (Finset.biUnion_subset_biUnion_of_subset_left
      (fun u : Face (iteratedAmbient K m).2 => u.val) h)

private theorem support_pair_mem {u v : Face (iteratedAmbient K 2).2}
    (h : (subdivisionGraph (iteratedAmbient K 2).2).Adj u v) :
    originalSupport K 3 {u, v} ∈ K := by
  apply GraphSubdivisionIntervals.originalSupport_mem 3
  change ({u, v} : Finset (Face (iteratedAmbient K 2).2)) ∈
    BarycentricBaseRigidity.sd (iteratedAmbient K 2).2
  refine ⟨Finset.insert_nonempty _ _, ?_, fun q _ => q.property⟩
  rw [Finset.coe_insert, Finset.coe_singleton]
  rcases h with h | h
  · exact IsChain.pair h
  · rw [Set.pair_comm]
    exact IsChain.pair h

/-- When the rank colouring is injective on each old face, adjacent
subdivided vertices that both carry a given rank lift it to the same
old vertex. This is the agreement used by the main and extra regions. -/
theorem eq_of_shared_carrier_colour (colour : X → Fin 4)
    (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X))
    {u v : Face (iteratedAmbient K 2).2}
    (h : (subdivisionGraph (iteratedAmbient K 2).2).Adj u v)
    {x y : X} (hx : x ∈ originalSupport K 3 {u}) (hy : y ∈ originalSupport K 3 {v})
    (hcolour : colour x = colour y) : x = y := by
  have hu : ({u} : Finset _) ⊆ {u, v} := by simp
  have hv : ({v} : Finset _) ⊆ {u, v} := by simp
  exact hinj _ (support_pair_mem h) (support_mono 3 hu hx) (support_mono 3 hv hy) hcolour

/-- The selected old vertices in the support of a subdivided vertex. -/
def colourSupport (colour : X → Fin 4) (c : Color)
    (u : Face (iteratedAmbient K 2).2) : Finset X :=
  (originalSupport K 3 {u}).filter fun x => hasColour c (colour x) = true

private theorem extra_support_edge (colour : X → Fin 4)
    (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X)) {c : Color}
    {u : Face (iteratedAmbient K 2).2} (hu : Extra c (row colour u)) :
    ∃ x ∈ originalSupport K 3 {u}, ∃ y ∈ originalSupport K 3 {u},
      (colour x).val = low (opposite c) ∧ (colour y).val = high (opposite c) ∧
      colourSupport colour (opposite c) u = {x, y} := by
  let d := opposite c
  have hb (e : Color) : low e < 4 ∧ high e < 4 := by fin_cases e <;> decide
  let l : Fin 4 := ⟨low d, (hb d).1⟩
  let r : Fin 4 := ⟨high d, (hb d).2⟩
  obtain ⟨x, hx, hxl⟩ := (mem_carrier_row colour u l).mp (pocket_conditions hu).2.1
  obtain ⟨y, hy, hyr⟩ := (mem_carrier_row colour u r).mp (pocket_conditions hu).2.2
  let U := originalSupport K 3 {u}
  have hU : U ∈ K := GraphSubdivisionIntervals.originalSupport_mem 3
    (BarycentricBaseRigidity.vertexOfFace _ u).property
  have he : colourSupport colour d u = {x, y} := by
    ext z
    simp only [colourSupport, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hc⟩
      simp only [hasColour, Bool.or_eq_true, beq_iff_eq] at hc
      rcases hc with hc | hc
      · exact Or.inl (hinj U hU hz hx ((Fin.ext hc).trans hxl.symm))
      · exact Or.inr (hinj U hU hz hy ((Fin.ext hc).trans hyr.symm))
    · rintro (rfl | rfl)
      · exact ⟨hx, by simp [hasColour, hxl, l]⟩
      · exact ⟨hy, by simp [hasColour, hyr, r]⟩
  exact ⟨x, hx, y, hy, congrArg Fin.val hxl, congrArg Fin.val hyr, he⟩

/-- The opposite-colour support is one old edge throughout an extra
component. The pullback uses one proper rank colouring on every face. -/
theorem extra_component_support (colour : X → Fin 4)
    (hinj : ∀ s ∈ K, Set.InjOn colour (s : Set X)) (c : Color)
    (u v : {w : Face (iteratedAmbient K 2).2 | Extra c (row colour w)})
    (h : ((subdivisionGraph (iteratedAmbient K 2).2).induce
      {w | Extra c (row colour w)}).Reachable u v) :
    (colourSupport colour (opposite c) u.val).card = 2 ∧
      colourSupport colour (opposite c) u.val = colourSupport colour (opposite c) v.val := by
  constructor
  · obtain ⟨x, _, y, _, hx, hy, he⟩ := extra_support_edge colour hinj u.property
    have hxy : x ≠ y := by
      intro e
      subst y
      rw [hx, high] at hy
      exact (Nat.ne_of_lt (Nat.lt_succ_self _)) hy
    rw [he, Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using hxy),
      Finset.card_singleton]
  have step {a b : {w : Face (iteratedAmbient K 2).2 | Extra c (row colour w)}}
      (hab : (subdivisionGraph (iteratedAmbient K 2).2).Adj a.val b.val) :
      colourSupport colour (opposite c) a.val = colourSupport colour (opposite c) b.val := by
    obtain ⟨x, hx, y, hy, hxl, hyr, ha⟩ := extra_support_edge colour hinj a.property
    obtain ⟨z, hz, w, hw, hzl, hwr, hb⟩ := extra_support_edge colour hinj b.property
    have hl := eq_of_shared_carrier_colour colour hinj hab hx hz (Fin.ext (hxl.trans hzl.symm))
    have hr := eq_of_shared_carrier_colour colour hinj hab hy hw (Fin.ext (hyr.trans hwr.symm))
    rw [ha, hb, hl, hr]
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hab _ ih => exact (step hab).trans ih

end

end D5.S3.Topology.RankColouredTetrahedron
