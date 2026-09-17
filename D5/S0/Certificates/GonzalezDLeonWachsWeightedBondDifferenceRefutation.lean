/- GID: D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation.claim; result=D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation.result; claim=D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation.claim
   digest: Nine vertices refute the weighted bond difference real-rootedness conjecture. -/

import D5.S0.Certificates.GonzalezDLeonWachsThreeVertexMobius

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.GonzalezDLeonWachsWeightedBondDifferenceRefutation

open Finset
open D5.S0.Certificates.GonzalezDLeonWachsWeightedBondSource
open D5.S0.Certificates.GonzalezDLeonWachsThreeVertexMobius

noncomputable section
private def fiberGraph (G : SimpleGraph (Fin 3)) : SimpleGraph (Fin 3 × Fin 3) where
  Adj x y := x.1 = y.1 ∧ G.Adj x.2 y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x.2 h.2⟩

private def fiberInclusion (G : SimpleGraph (Fin 3)) (i : Fin 3) :
    G →g fiberGraph G where
  toFun u := (i, u)
  map_rel' h := ⟨rfl, h⟩
private theorem fiberGraph_reachable_first
    {G : SimpleGraph (Fin 3)} {x y : Fin 3 × Fin 3}
    (h : (fiberGraph G).Reachable x y) : x.1 = y.1 := by
  obtain ⟨walk⟩ := h
  induction walk with
  | nil => rfl
  | cons h _ ih => exact h.1.trans ih

private theorem fiberGraph_reachable_iff
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) (x y : Fin 3 × Fin 3) :
    (fiberGraph G).Reachable x y ↔ x.1 = y.1 := by
  refine ⟨fiberGraph_reachable_first, ?_⟩
  rcases x with ⟨i, u⟩
  rcases y with ⟨j, v⟩
  intro h
  change i = j at h
  subst j
  exact (hG u v).map (fiberInclusion G i)

private def fiberComponentEquiv
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) :
    (fiberGraph G).ConnectedComponent ≃ Fin 3 where
  toFun := Quot.lift Prod.fst (fun _ _ h => fiberGraph_reachable_first h)
  invFun i := (fiberGraph G).connectedComponentMk (i, 0)
  left_inv := by
    intro component
    induction component using Quot.ind with
    | _ x =>
      exact SimpleGraph.ConnectedComponent.sound
        ((fiberGraph_reachable_iff hG (x.1, 0) x).mpr rfl)
  right_inv i := rfl

private theorem fiberGraph_component_count
    {G : SimpleGraph (Fin 3)} (hG : G.Connected) :
    Nat.card (fiberGraph G).ConnectedComponent = 3 := by
  rw [Nat.card_congr (fiberComponentEquiv hG)]
  simp

private theorem fiberPath_lt_fiberTriangle : fiberGraph pathThree < fiberGraph triangleThree := by
  have hle : pathThree ≤ triangleThree := by
    change pathThree ≤ ⊤
    exact le_top
  refine lt_of_le_of_ne (fun x y h => ⟨h.1, hle h.2⟩) ?_
  intro heq
  have hadj := congrArg
    (fun G : SimpleGraph (Fin 3 × Fin 3) => G.Adj (0, 0) (0, 2)) heq
  simp [fiberGraph, pathThree, triangleThree, SimpleGraph.pathGraph_adj] at hadj

/- Connectivity in the induced block, not mere containment, excludes crossing
   between fibers. This applies to every block of the original source carrier. -/
private theorem fiberBlock_first_eq
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G))
    {block : Finset (Fin 3 × Fin 3)} (hb : block ∈ P.val.partition.parts)
    {x y : Fin 3 × Fin 3} (hx : x ∈ block) (hy : y ∈ block) : x.1 = y.1 := by
  have hr := (P.property block hb) ⟨x, hx⟩ ⟨y, hy⟩
  exact fiberGraph_reachable_first (hr.map (SimpleGraph.Embedding.induce _).toHom)

private def fiberLift (i : Fin 3) (block : Finset (Fin 3)) : Finset (Fin 3 × Fin 3) :=
  block.image fun u => (i, u)

private theorem fiberLift_injective (i : Fin 3) : Function.Injective (fiberLift i) := by
  intro A B h
  ext u
  have hm := congrArg (fun S => (i, u) ∈ S) h
  simpa [fiberLift, eq_comm, and_comm] using hm

private theorem fiberBlock_eq_lift
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G))
    {block : Finset (Fin 3 × Fin 3)} (hb : block ∈ P.val.partition.parts)
    {x : Fin 3 × Fin 3} (hx : x ∈ block) :
    block = fiberLift x.1 (block.image Prod.snd) := by
  ext y
  constructor
  · intro hy
    refine Finset.mem_image.mpr ⟨y.2, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    · exact Prod.ext (fiberBlock_first_eq P hb hy hx).symm rfl
  · intro hy
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hy
    obtain ⟨z, hz, hzu⟩ := Finset.mem_image.mp hu
    have hzi := fiberBlock_first_eq P hb hz hx
    have hzy : z = y := by
      rw [← heq, ← hzu]
      exact Prod.ext hzi rfl
    exact hzy ▸ hz

private def fiberRestrictionPartition
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) (i : Fin 3) :
    Finpartition (univ : Finset (Fin 3)) := by
  let parts := (univ : Finset (Fin 3)).powerset.filter
    (fun block => fiberLift i block ∈ P.val.partition.parts)
  have hmem : ∀ block, block ∈ parts ↔ fiberLift i block ∈ P.val.partition.parts := by
    intro block
    simp [parts]
  refine Finpartition.ofExistsUnique parts (fun _ _ => subset_univ _) ?_ ?_
  · intro u _
    obtain ⟨block, hb, hu⟩ := P.val.partition.exists_mem (mem_univ (i, u))
    let localBlock := block.image Prod.snd
    have heq := fiberBlock_eq_lift P hb hu
    refine ⟨localBlock, ⟨(hmem _).mpr (heq ▸ hb), ?_⟩, ?_⟩
    · exact mem_image.mpr ⟨(i, u), hu, rfl⟩
    · intro other hother
      apply fiberLift_injective i
      have hotherMem := (hmem other).mp hother.1
      have huOther : (i, u) ∈ fiberLift i other := by
        simpa [fiberLift] using hother.2
      exact (P.val.partition.existsUnique_mem (mem_univ (i, u))).unique
        ⟨hotherMem, huOther⟩ ⟨heq ▸ hb, heq ▸ hu⟩
  · intro hzero
    have hbad := (hmem ∅).mp hzero
    simpa [fiberLift] using P.val.partition.ne_bot hbad

private def fiberRestrictionWeighted
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) (i : Fin 3) :
    WeightedPartition (Fin 3) where
  partition := fiberRestrictionPartition P i
  weight block := ⟨P.val.weight (fiberLift i block), by
    by_cases hb : block ∈ (fiberRestrictionPartition P i).parts
    · have hlt := P.val.weight_lt_card _ (by
        simpa [fiberRestrictionPartition] using hb)
      have hcardLift : (fiberLift i block).card = block.card :=
        Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
      rw [hcardLift] at hlt
      have hcard : block.card ≤ 3 := by
        simpa using Finset.card_le_card (subset_univ block)
      simp only [Fintype.card_fin]
      omega
    · have hz := P.val.weight_eq_zero _ (by
        simpa [fiberRestrictionPartition] using hb)
      simp [hz]⟩
  weight_lt_card := by
    intro block hb
    have hlt := P.val.weight_lt_card _ (by
      simpa [fiberRestrictionPartition] using hb)
    have hcardLift : (fiberLift i block).card = block.card :=
      Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
    rwa [hcardLift] at hlt
  weight_eq_zero := by
    intro block hb
    apply Fin.ext
    change (P.val.weight (fiberLift i block) : Nat) = 0
    exact congrArg Fin.val
      (P.val.weight_eq_zero _ (by simpa [fiberRestrictionPartition] using hb))

private def fiberBlockProjectionHom
    (G : SimpleGraph (Fin 3)) (i : Fin 3) (block : Finset (Fin 3)) :
    (fiberGraph G).induce (fiberLift i block : Set (Fin 3 × Fin 3)) →g
      G.induce (block : Set (Fin 3)) where
  toFun x := ⟨x.val.2, (by
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp x.property
    have hueq : u = x.val.2 := congrArg Prod.snd heq
    exact hueq ▸ hu)⟩
  map_rel' h := h.2

private def fiberRestriction
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) (i : Fin 3) :
    ConnectedWeightedPartition G := by
  refine ⟨fiberRestrictionWeighted P i, ?_⟩
  intro block hb
  change block ∈ (fiberRestrictionPartition P i).parts at hb
  have hc := P.property _ (by simpa [fiberRestrictionPartition] using hb)
  exact hc.map (fiberBlockProjectionHom G i block) (by
    intro u
    exact ⟨⟨(i, u.val), Finset.mem_image.mpr ⟨u.val, u.property, rfl⟩⟩, rfl⟩)

private theorem fiberLift_eq_fiberLift
    {i j : Fin 3} {A B : Finset (Fin 3)} (hA : A.Nonempty)
    (h : fiberLift i A = fiberLift j B) : i = j ∧ A = B := by
  obtain ⟨u, hu⟩ := hA
  have hm : (i, u) ∈ fiberLift j B := h ▸ (by simpa [fiberLift] using hu)
  have hij : i = j := by
    have : u ∈ B ∧ j = i := by simpa [fiberLift] using hm
    exact this.2.symm
  subst j
  exact ⟨rfl, fiberLift_injective i h⟩

private def fiberGlueParts
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G) :
    Finset (Finset (Fin 3 × Fin 3)) :=
  univ.biUnion fun i => (components i).val.partition.parts.image (fiberLift i)

private def fiberGluePartition
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G) :
    Finpartition (univ : Finset (Fin 3 × Fin 3)) := by
  refine Finpartition.ofExistsUnique (fiberGlueParts components)
    (fun _ _ => subset_univ _) ?_ ?_
  · rintro ⟨i, u⟩ _
    obtain ⟨A, hA, hu⟩ := (components i).val.partition.exists_mem (mem_univ u)
    refine ⟨fiberLift i A, ⟨(by simpa [fiberGlueParts] using ⟨i, A, hA, rfl⟩),
      by simpa [fiberLift] using hu⟩, ?_⟩
    intro other hother
    obtain ⟨j, B, hB, rfl⟩ := (by
      simpa [fiberGlueParts] using hother.1 :
        ∃ j B, B ∈ (components j).val.partition.parts ∧ fiberLift j B = other)
    have hm : i = j ∧ u ∈ B := by
      have : u ∈ B ∧ j = i := by simpa [fiberLift] using hother.2
      exact ⟨this.2.symm, this.1⟩
    change i = j ∧ u ∈ B at hm
    rcases hm with ⟨rfl, huB⟩
    have hBA := ((components i).val.partition.existsUnique_mem (mem_univ u)).unique
      ⟨hB, huB⟩ ⟨hA, hu⟩
    exact congrArg (fiberLift i) hBA
  · intro hzero
    obtain ⟨i, A, hA, heq⟩ := (by
      simpa [fiberGlueParts] using hzero :
        ∃ i A, A ∈ (components i).val.partition.parts ∧ fiberLift i A = ∅)
    have hc := congrArg Finset.card heq
    simp [fiberLift] at hc
    exact (components i).val.partition.ne_bot hA hc

private def fiberGlueOrigin
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G)
    (block : Finset (Fin 3 × Fin 3)) (hb : block ∈ fiberGlueParts components) :
    Σ i : Fin 3, (components i).val.partition.parts := by
  let h : ∃ i A, A ∈ (components i).val.partition.parts ∧ fiberLift i A = block := by
    simpa [fiberGlueParts] using hb
  exact ⟨h.choose, ⟨h.choose_spec.choose, h.choose_spec.choose_spec.1⟩⟩

private def fiberGlueWeighted
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G) :
    WeightedPartition (Fin 3 × Fin 3) where
  partition := fiberGluePartition components
  weight block := if hb : block ∈ fiberGlueParts components then
    let origin := fiberGlueOrigin components block hb
    ⟨(components origin.1).val.weight origin.2.val, by
      have hlt := (components origin.1).val.weight origin.2.val |>.isLt
      simp only [Fintype.card_prod, Fintype.card_fin] at *
      omega⟩
    else 0
  weight_lt_card := by
    intro block hb
    change block ∈ fiberGlueParts components at hb
    simp only [dif_pos hb]
    have hlt := (components (fiberGlueOrigin components block hb).1).val.weight_lt_card
      _ (fiberGlueOrigin components block hb).2.property
    have horigin : fiberLift (fiberGlueOrigin components block hb).1
        (fiberGlueOrigin components block hb).2.val = block := by
      unfold fiberGlueOrigin
      exact ((show ∃ i A, A ∈ (components i).val.partition.parts ∧
        fiberLift i A = block by simpa [fiberGlueParts] using hb)).choose_spec.choose_spec.2
    have hc := congrArg Finset.card horigin
    have hcardLift : (fiberLift (fiberGlueOrigin components block hb).1
        (fiberGlueOrigin components block hb).2.val).card =
        (fiberGlueOrigin components block hb).2.val.card :=
      Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
    rw [hcardLift] at hc
    exact hc ▸ hlt
  weight_eq_zero := by
    intro block hb
    change block ∉ fiberGlueParts components at hb
    simp only [dif_neg hb]

private def fiberBlockInclusionHom
    (G : SimpleGraph (Fin 3)) (i : Fin 3) (block : Finset (Fin 3)) :
    G.induce (block : Set (Fin 3)) →g
      (fiberGraph G).induce (fiberLift i block : Set (Fin 3 × Fin 3)) where
  toFun u := ⟨(i, u.val), Finset.mem_image.mpr ⟨u.val, u.property, rfl⟩⟩
  map_rel' h := ⟨rfl, h⟩

private def fiberGlue
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G) :
    ConnectedWeightedPartition (fiberGraph G) := by
  refine ⟨fiberGlueWeighted components, ?_⟩
  intro block hb
  change block ∈ fiberGlueParts components at hb
  obtain ⟨i, A, hA, rfl⟩ := (by
    simpa [fiberGlueParts] using hb :
      ∃ i A, A ∈ (components i).val.partition.parts ∧ fiberLift i A = block)
  exact ((components i).property A hA).map (fiberBlockInclusionHom G i A) (by
    intro x
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp x.property
    exact ⟨⟨u, hu⟩, Subtype.ext heq⟩)

@[simp] private theorem fiberGlue_lift_mem
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G)
    (i : Fin 3) (A : Finset (Fin 3)) :
    fiberLift i A ∈ (fiberGlue components).val.partition.parts ↔
      A ∈ (components i).val.partition.parts := by
  change fiberLift i A ∈ fiberGlueParts components ↔ _
  constructor
  · intro h
    obtain ⟨j, B, hB, heq⟩ := (by
      simpa [fiberGlueParts] using h :
        ∃ j B, B ∈ (components j).val.partition.parts ∧ fiberLift j B = fiberLift i A)
    obtain ⟨hji, hBA⟩ := fiberLift_eq_fiberLift
      ((components j).val.partition.nonempty_of_mem_parts hB) heq
    subst j
    exact hBA ▸ hB
  · intro hA
    simpa [fiberGlueParts] using ⟨i, A, hA, rfl⟩

@[simp] private theorem fiberGlue_weight_lift
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G)
    (i : Fin 3) (A : Finset (Fin 3)) :
    ((fiberGlue components).val.weight (fiberLift i A) : Nat) =
      ((components i).val.weight A : Nat) := by
  by_cases hA : A ∈ (components i).val.partition.parts
  · have hb : fiberLift i A ∈ fiberGlueParts components :=
      (by simpa [fiberGlueParts] using ⟨i, A, hA, rfl⟩)
    change ((fiberGlueWeighted components).weight (fiberLift i A) : Nat) = _
    simp only [fiberGlueWeighted, dif_pos hb]
    have hs : fiberLift (fiberGlueOrigin components (fiberLift i A) hb).1
        (fiberGlueOrigin components (fiberLift i A) hb).2.val = fiberLift i A := by
      unfold fiberGlueOrigin
      exact ((show ∃ j B, B ∈ (components j).val.partition.parts ∧
        fiberLift j B = fiberLift i A by
          simpa [fiberGlueParts] using hb)).choose_spec.choose_spec.2
    generalize fiberGlueOrigin components (fiberLift i A) hb = origin at hs ⊢
    rcases origin with ⟨j, B⟩
    obtain ⟨hji, hBA⟩ := fiberLift_eq_fiberLift
      ((components j).val.partition.nonempty_of_mem_parts B.property) hs
    change j = i at hji
    subst j
    simp only [hBA]
  · have hb : fiberLift i A ∉ (fiberGlue components).val.partition.parts := by
      simpa using hA
    rw [(fiberGlue components).val.weight_eq_zero _ hb,
      (components i).val.weight_eq_zero _ hA]
    rfl

private theorem fiberRestriction_glue
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G)
    (i : Fin 3) : fiberRestriction (fiberGlue components) i = components i := by
  apply Subtype.ext
  apply WeightedPartition.ext
  · apply Finpartition.ext
    ext A
    exact (show A ∈ (fiberRestrictionPartition (fiberGlue components) i).parts ↔
        fiberLift i A ∈ (fiberGlue components).val.partition.parts by
          simp [fiberRestrictionPartition]).trans (fiberGlue_lift_mem components i A)
  · funext A
    apply Fin.ext
    exact fiberGlue_weight_lift components i A

private theorem fiberGlue_restriction
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) :
    fiberGlue (fiberRestriction P) = P := by
  have hparts : (fiberGlue (fiberRestriction P)).val.partition = P.val.partition := by
    apply Finpartition.ext
    ext block
    change block ∈ fiberGlueParts (fiberRestriction P) ↔ _
    constructor
    · intro hb
      obtain ⟨i, A, hA, rfl⟩ := (by
        simpa [fiberGlueParts] using hb :
          ∃ i A, A ∈ (fiberRestriction P i).val.partition.parts ∧ fiberLift i A = block)
      change A ∈ (fiberRestrictionPartition P i).parts at hA
      simpa [fiberRestrictionPartition] using hA
    · intro hb
      obtain ⟨x, hx⟩ := P.val.partition.nonempty_of_mem_parts hb
      have heq := fiberBlock_eq_lift P hb hx
      simpa [fiberGlueParts] using
        ⟨x.1, block.image Prod.snd,
          (show block.image Prod.snd ∈ (fiberRestrictionPartition P x.1).parts by
            simpa [fiberRestrictionPartition] using heq ▸ hb), heq.symm⟩
  apply Subtype.ext
  apply WeightedPartition.ext hparts
  funext block
  by_cases hb : block ∈ P.val.partition.parts
  · obtain ⟨x, hx⟩ := P.val.partition.nonempty_of_mem_parts hb
    have heq := fiberBlock_eq_lift P hb hx
    apply Fin.ext
    calc
      ((fiberGlue (fiberRestriction P)).val.weight block : Nat) =
          ((fiberGlue (fiberRestriction P)).val.weight
            (fiberLift x.1 (block.image Prod.snd)) : Nat) :=
        congrArg (fun B => ((fiberGlue (fiberRestriction P)).val.weight B : Nat)) heq
      _ = ((fiberRestriction P x.1).val.weight (block.image Prod.snd) : Nat) :=
        fiberGlue_weight_lift _ _ _
      _ = (P.val.weight (fiberLift x.1 (block.image Prod.snd)) : Nat) := rfl
      _ = (P.val.weight block : Nat) := congrArg (fun B => (P.val.weight B : Nat)) heq.symm
  · rw [P.val.weight_eq_zero _ hb,
      (fiberGlue (fiberRestriction P)).val.weight_eq_zero _ (by simpa [hparts] using hb)]

private def fiberSourceEquiv (G : SimpleGraph (Fin 3)) :
    ConnectedWeightedPartition (fiberGraph G) ≃ (Fin 3 → ConnectedWeightedPartition G) where
  toFun := fiberRestriction
  invFun := fiberGlue
  left_inv := fiberGlue_restriction
  right_inv components := funext (fiberRestriction_glue components)

private def fiberRestrictionChild
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) (i : Fin 3)
    (A : (fiberRestrictionPartition P i).parts) : P.val.partition.parts :=
  ⟨fiberLift i A.val, by simpa [fiberRestrictionPartition] using A.property⟩

private theorem fiberRestriction_children
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G))
    (i : Fin 3) (upper : Finset (Fin 3)) :
    (children (fiberRestrictionPartition P i) upper).image (fiberRestrictionChild P i) =
      children P.val.partition (fiberLift i upper) := by
  have hlift : ∀ A B : Finset (Fin 3), fiberLift i A ⊆ fiberLift i B ↔ A ⊆ B := by
    intro A B
    constructor
    · intro h u hu
      simpa [fiberLift] using
        h (show (i, u) ∈ fiberLift i A from by simpa [fiberLift] using hu)
    · intro h x hx
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨u, h hu, heq⟩
  ext lower
  simp only [mem_image, children, mem_filter, mem_attach, true_and]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (hlift A.val upper).mpr hA
  · intro hsub
    obtain ⟨x, hx⟩ := P.val.partition.nonempty_of_mem_parts lower.property
    have hxi : x.1 = i := by
      obtain ⟨u, _, heq⟩ := Finset.mem_image.mp (hsub hx)
      exact (congrArg Prod.fst heq).symm
    have heq := fiberBlock_eq_lift P lower.property hx
    rw [hxi] at heq
    let A := lower.val.image Prod.snd
    have hA : A ∈ (fiberRestrictionPartition P i).parts := by
      simpa [fiberRestrictionPartition] using heq ▸ lower.property
    refine ⟨⟨A, hA⟩, ?_, ?_⟩
    · exact (hlift A upper).mp (heq ▸ hsub)
    · exact Subtype.ext heq.symm

private theorem fiberRestriction_childWeightSum
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G))
    (i : Fin 3) (upper : Finset (Fin 3)) :
    childWeightSum (fiberRestriction P i).val upper =
      childWeightSum P.val (fiberLift i upper) := by
  unfold childWeightSum
  rw [← fiberRestriction_children P i upper,
    Finset.sum_image (show Function.Injective (fiberRestrictionChild P i) from by
      intro A B h
      exact Subtype.ext (fiberLift_injective i (congrArg Subtype.val h))).injOn]
  apply Finset.sum_congr rfl
  intro A _
  rfl

private theorem fiberRestriction_partition_le_iff
    {G : SimpleGraph (Fin 3)} (P Q : ConnectedWeightedPartition (fiberGraph G)) :
    P.val.partition ≤ Q.val.partition ↔
      ∀ i, (fiberRestrictionPartition P i) ≤ (fiberRestrictionPartition Q i) := by
  have hlift : ∀ i A B, fiberLift i A ⊆ fiberLift i B ↔ A ⊆ B := by
    intro i A B
    constructor
    · intro h u hu
      simpa [fiberLift] using
        h (show (i, u) ∈ fiberLift i A from by simpa [fiberLift] using hu)
    · intro h x hx
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨u, h hu, heq⟩
  constructor
  · intro h i A hA
    have hAlift : fiberLift i A ∈ P.val.partition.parts := by
      simpa [fiberRestrictionPartition] using hA
    obtain ⟨upper, hupper, hsub⟩ := h hAlift
    obtain ⟨u, hu⟩ := (fiberRestrictionPartition P i).nonempty_of_mem_parts hA
    have heq := fiberBlock_eq_lift Q hupper
      (hsub (show (i, u) ∈ fiberLift i A from by simpa [fiberLift] using hu))
    refine ⟨upper.image Prod.snd, (by
      simpa [fiberRestrictionPartition] using heq ▸ hupper), ?_⟩
    exact (hlift i A _).mp (heq ▸ hsub)
  · intro h block hb
    obtain ⟨x, hx⟩ := P.val.partition.nonempty_of_mem_parts hb
    have heq := fiberBlock_eq_lift P hb hx
    have hA : block.image Prod.snd ∈ (fiberRestrictionPartition P x.1).parts := by
      simpa [fiberRestrictionPartition] using heq ▸ hb
    obtain ⟨upper, hu, hsub⟩ := h x.1 hA
    refine ⟨fiberLift x.1 upper, (by
      simpa [fiberRestrictionPartition] using hu), ?_⟩
    rw [heq]
    exact (hlift x.1 _ upper).mpr hsub

private theorem fiberRestriction_le_iff
    {G : SimpleGraph (Fin 3)} (P Q : ConnectedWeightedPartition (fiberGraph G)) :
    P ≤ Q ↔ ∀ i, fiberRestriction P i ≤ fiberRestriction Q i := by
  have hcard : ∀ (R : ConnectedWeightedPartition (fiberGraph G)) i upper,
      (children (fiberRestrictionPartition R i) upper).card =
        (children R.val.partition (fiberLift i upper)).card := by
    intro R i upper
    rw [← fiberRestriction_children R i upper,
      Finset.card_image_of_injective _ (show Function.Injective
        (fiberRestrictionChild R i) from by
          intro A B h
          exact Subtype.ext (fiberLift_injective i (congrArg Subtype.val h)))]
  change WeightedRefines P.val Q.val ↔
    ∀ i, WeightedRefines (fiberRestriction P i).val (fiberRestriction Q i).val
  constructor
  · intro h i
    refine ⟨(fiberRestriction_partition_le_iff P Q).mp h.1 i, ?_⟩
    intro upper
    have hu : fiberLift i upper.val ∈ Q.val.partition.parts := by
      have hup := upper.property
      change upper.val ∈ (fiberRestrictionPartition Q i).parts at hup
      simpa [fiberRestrictionPartition] using hup
    obtain ⟨d, hd, hw⟩ := h.2 ⟨fiberLift i upper.val, hu⟩
    refine ⟨d, ?_, ?_⟩
    · change d < (children (fiberRestrictionPartition P i) upper.val).card
      rwa [hcard P i upper.val]
    · change ((fiberRestrictionWeighted Q i).weight upper.val : Nat) =
        childWeightSum (fiberRestriction P i).val upper.val + d
      rw [fiberRestriction_childWeightSum]
      exact hw
  · intro h
    refine ⟨(fiberRestriction_partition_le_iff P Q).mpr (fun i => (h i).1), ?_⟩
    intro upper
    obtain ⟨x, hx⟩ := Q.val.partition.nonempty_of_mem_parts upper.property
    have heq := fiberBlock_eq_lift Q upper.property hx
    have hu : upper.val.image Prod.snd ∈ (fiberRestrictionPartition Q x.1).parts := by
      simpa [fiberRestrictionPartition] using heq ▸ upper.property
    obtain ⟨d, hd, hw⟩ := (h x.1).2 ⟨upper.val.image Prod.snd, hu⟩
    refine ⟨d, ?_, ?_⟩
    · change d < (children (fiberRestrictionPartition P x.1) (upper.val.image Prod.snd)).card at hd
      rw [hcard P] at hd
      simpa only [← heq] using hd
    · change ((fiberRestrictionWeighted Q x.1).weight (upper.val.image Prod.snd) : Nat) =
        childWeightSum (fiberRestriction P x.1).val (upper.val.image Prod.snd) + d at hw
      rw [fiberRestriction_childWeightSum] at hw
      change (Q.val.weight (fiberLift x.1 (upper.val.image Prod.snd)) : Nat) =
        childWeightSum P.val (fiberLift x.1 (upper.val.image Prod.snd)) + d at hw
      simpa only [← heq] using hw

private def fiberSourceOrderIso (G : SimpleGraph (Fin 3)) :
    ConnectedWeightedPartition (fiberGraph G) ≃o (Fin 3 → ConnectedWeightedPartition G) where
  toEquiv := fiberSourceEquiv G
  map_rel_iff' := by
    intro P Q
    exact (fiberRestriction_le_iff P Q).symm

private theorem fiberGlue_totalBlockWeight
    {G : SimpleGraph (Fin 3)} (components : Fin 3 → ConnectedWeightedPartition G) :
    totalBlockWeight (fiberGlue components).val =
      ∑ i, totalBlockWeight (components i).val := by
  have hdisjoint : Set.PairwiseDisjoint (↑(univ : Finset (Fin 3)))
      (fun i => (components i).val.partition.parts.image (fiberLift i)) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro block hi hj
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hi
    obtain ⟨B, hB, heq⟩ := mem_image.mp hj
    have hji := (fiberLift_eq_fiberLift
      ((components j).val.partition.nonempty_of_mem_parts hB) heq).1
    exact hij hji.symm
  change (∑ block ∈ fiberGlueParts components,
    ((fiberGlue components).val.weight block : Nat)) = _
  unfold fiberGlueParts
  rw [Finset.sum_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_image (fiberLift_injective i).injOn]
  exact Finset.sum_congr rfl (fun A _ => fiberGlue_weight_lift components i A)

private theorem fiber_isMax_iff
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) :
    IsMax P ↔ ∀ i, IsMax (fiberRestriction P i) := by
  rw [← (fiberSourceOrderIso G).isMax_apply]
  change IsMax (fiberRestriction P) ↔ _
  constructor
  · intro h i Q hiQ
    have hle : fiberRestriction P ≤ Function.update (fiberRestriction P) i Q := by
      intro j
      by_cases hji : j = i
      · subst j; simpa using hiQ
      · simp [Function.update_of_ne hji]
    have hback := h hle i
    simpa using hback
  · intro h Q hPQ i
    exact h i (hPQ i)

private theorem finite_mu_orderIso
    {α β : Type*} [Finite α] [PartialOrder α] [PartialOrder β]
    [DecidableEq α] [DecidableEq β]
    [LocallyFiniteOrder α] [LocallyFiniteOrder β] (e : α ≃o β) (a b : α) :
    (IncidenceAlgebra.mu ℤ) (e a) (e b) = (IncidenceAlgebra.mu ℤ) a b := by
  classical
  induction b using (Finite.wellFounded_of_trans_of_irrefl
      ((· < ·) : α → α → Prop)).induction with
  | h b ih =>
    by_cases hab : a = b
    · subst b; simp
    · rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne (e.injective.ne hab),
        IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hab]
      congr 1
      symm
      apply Finset.sum_bij (fun x _ => e x)
      · intro x hx
        simpa only [Finset.mem_Ico, e.le_iff_le, e.lt_iff_lt] using hx
      · intro x _ y _ hxy
        exact e.injective hxy
      · intro y hy
        refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
        simpa only [Finset.mem_Ico, ← e.le_iff_le, ← e.lt_iff_lt,
          e.apply_symm_apply] using hy
      · intro x hx
        exact (ih x (Finset.mem_Ico.mp hx).2).symm

private def sourceTripleOrderIso (G : SimpleGraph (Fin 3)) :
    (Fin 3 → ConnectedWeightedPartition G) ≃o
      (ConnectedWeightedPartition G ×
        (ConnectedWeightedPartition G × ConnectedWeightedPartition G)) where
  toFun f := (f 0, f 1, f 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv p := rfl
  map_rel_iff' := by
    intro f g
    change (f 0 ≤ g 0 ∧ f 1 ≤ g 1 ∧ f 2 ≤ g 2) ↔ ∀ i, f i ≤ g i
    constructor
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    · intro h; exact ⟨h 0, h 1, h 2⟩

private def fiberSourceTripleOrderIso (G : SimpleGraph (Fin 3)) :=
  (fiberSourceOrderIso G).trans (sourceTripleOrderIso G)

private theorem fiber_mu_product
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) :
    (IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition (fiberGraph G)) P =
      (IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G) (fiberRestriction P 0) *
        ((IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G) (fiberRestriction P 1) *
          (IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G) (fiberRestriction P 2)) := by
  classical
  rw [← finite_mu_orderIso (fiberSourceTripleOrderIso G) ⊥ P,
    (fiberSourceTripleOrderIso G).map_bot,
    ← IncidenceAlgebra.mu_prod_mu, IncidenceAlgebra.prod_apply,
    ← IncidenceAlgebra.mu_prod_mu, IncidenceAlgebra.prod_apply]
  rfl

private def sourceSummand
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (P : ConnectedWeightedPartition G) : Polynomial ℝ := by
  classical
  exact if IsMax P then
    Polynomial.C (((IncidenceAlgebra.mu ℤ) (⊥ : ConnectedWeightedPartition G) P : ℤ) : ℝ) *
      Polynomial.X ^ totalBlockWeight P.val else 0

private theorem fiber_sourceSummand_product
    {G : SimpleGraph (Fin 3)} (P : ConnectedWeightedPartition (fiberGraph G)) :
    sourceSummand P = sourceSummand (fiberRestriction P 0) *
      (sourceSummand (fiberRestriction P 1) * sourceSummand (fiberRestriction P 2)) := by
  classical
  have hmax : IsMax P ↔ IsMax (fiberRestriction P 0) ∧
      IsMax (fiberRestriction P 1) ∧ IsMax (fiberRestriction P 2) := by
    rw [fiber_isMax_iff]
    constructor
    · intro h; exact ⟨h 0, h 1, h 2⟩
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
  have hweight : totalBlockWeight P.val =
      totalBlockWeight (fiberRestriction P 0).val +
        (totalBlockWeight (fiberRestriction P 1).val +
          totalBlockWeight (fiberRestriction P 2).val) := by
    have hsum := fiberGlue_totalBlockWeight (fiberRestriction P)
    rw [fiberGlue_restriction] at hsum
    rw [hsum]
    simp [Fin.sum_univ_succ]
  unfold sourceSummand
  by_cases h0 : IsMax (fiberRestriction P 0) <;>
    by_cases h1 : IsMax (fiberRestriction P 1) <;>
      by_cases h2 : IsMax (fiberRestriction P 2)
  all_goals simp only [hmax, h0, h1, h2, and_self, and_true, and_false,
    if_true, if_false, zero_mul, mul_zero]
  rw [fiber_mu_product, hweight, Int.cast_mul, Int.cast_mul,
    Polynomial.C_mul, Polynomial.C_mul, pow_add, pow_add]
  ring

private theorem fiberGraph_sourceMobiusPolynomial
    (G : SimpleGraph (Fin 3)) :
    sourceMobiusPolynomial (fiberGraph G) = (sourceMobiusPolynomial G) ^ 3 := by
  classical
  have hsumGlobal : sourceMobiusPolynomial (fiberGraph G) =
      ∑ P : ConnectedWeightedPartition (fiberGraph G), sourceSummand P := by
    simp only [sourceMobiusPolynomial, Finset.sum_filter, sourceSummand]
  have hsumLocal : sourceMobiusPolynomial G =
      ∑ P : ConnectedWeightedPartition G, sourceSummand P := by
    simp only [sourceMobiusPolynomial, Finset.sum_filter, sourceSummand]
  rw [hsumGlobal, hsumLocal]
  let e := fiberSourceTripleOrderIso G
  have heq : (∑ P : ConnectedWeightedPartition (fiberGraph G), sourceSummand P) =
      ∑ p : ConnectedWeightedPartition G ×
        (ConnectedWeightedPartition G × ConnectedWeightedPartition G),
          sourceSummand p.1 * (sourceSummand p.2.1 * sourceSummand p.2.2) := by
    apply Fintype.sum_equiv e.toEquiv
    intro P
    exact fiber_sourceSummand_product P
  rw [heq]
  simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

private def obstructionQuartic : Polynomial ℝ :=
  7 * Polynomial.X ^ 4 + 37 * Polynomial.X ^ 3 +
    63 * Polynomial.X ^ 2 + 37 * Polynomial.X + 7

private theorem obstructionQuartic_no_real_root (x : ℝ) :
    Polynomial.eval x obstructionQuartic ≠ 0 := by
  intro hx
  let a : ℝ := 2 + 5 * x + 2 * x ^ 2
  let b : ℝ := 1 + 3 * x + x ^ 2
  have hsum : (2 * a + b) ^ 2 + 3 * b ^ 2 = 0 := by
    have heval : Polynomial.eval x obstructionQuartic =
        7 * x ^ 4 + 37 * x ^ 3 + 63 * x ^ 2 + 37 * x + 7 := by
      simp [obstructionQuartic, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow]
    rw [heval] at hx
    dsimp [a, b]
    nlinarith [hx]
  have hb : b = 0 := by nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
  have ha : a = 0 := by nlinarith [sq_nonneg (2 * a + b)]
  have hzero : x = 0 := by dsimp [a, b] at ha hb; nlinarith
  simp [b, hzero] at hb

private theorem obstructionQuartic_not_splits : ¬ Polynomial.Splits obstructionQuartic := by
  intro hs
  have hd : Polynomial.natDegree obstructionQuartic = 4 := by
    unfold obstructionQuartic
    compute_degree!
  obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero
    (Polynomial.degree_ne_of_natDegree_ne (by rw [hd]; norm_num))
  exact obstructionQuartic_no_real_root x hx

private theorem fiber_source_difference_not_splits :
    ¬ Polynomial.Splits
      (sourceMobiusPolynomial (fiberGraph triangleThree) -
        sourceMobiusPolynomial (fiberGraph pathThree)) := by
  rw [fiberGraph_sourceMobiusPolynomial, triangle_three_source_mobius_polynomial,
    fiberGraph_sourceMobiusPolynomial, path_three_source_mobius_polynomial]
  have hfactor :
      (2 + 5 * Polynomial.X + 2 * Polynomial.X ^ 2 : Polynomial ℝ) ^ 3 -
        (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 3 =
        (Polynomial.X + 1) ^ 2 * obstructionQuartic := by
    unfold obstructionQuartic
    ring
  rw [hfactor]
  intro hs
  have hleft : ((Polynomial.X + 1 : Polynomial ℝ) ^ 2) ≠ 0 := by
    apply pow_ne_zero
    intro heq
    have hev := congrArg (Polynomial.eval (0 : ℝ)) heq
    norm_num at hev
  have hparts := (Polynomial.splits_mul' (f :=
    (Polynomial.X + 1 : Polynomial ℝ) ^ 2) (g := obstructionQuartic)).mp hs
  exact obstructionQuartic_not_splits (hparts.2.resolve_right hleft)

/-- The literal, all-graphs assertion of Conjecture 4.13(2) in arXiv:2608.08692v1.
    The source permits disconnected graphs with the same component count. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G H : SimpleGraph V),
    H ≤ G → Nat.card G.ConnectedComponent = Nat.card H.ConnectedComponent →
      Polynomial.Splits
        ((-1 : Polynomial ℝ) ^
            (Fintype.card V - Nat.card G.ConnectedComponent) *
          (sourceMobiusPolynomial G - sourceMobiusPolynomial H))

theorem result : ¬ claim := by
  intro h
  have hcomponentsG := fiberGraph_component_count
    (SimpleGraph.connected_top : triangleThree.Connected)
  have hcomponentsH := fiberGraph_component_count
    (by simpa [pathThree] using SimpleGraph.pathGraph_connected 2 : pathThree.Connected)
  change Nat.card (fiberGraph triangleThree).ConnectedComponent = 3 at hcomponentsG
  have hs := h (Fin 3 × Fin 3) (fiberGraph triangleThree) (fiberGraph pathThree)
    fiberPath_lt_fiberTriangle.le (hcomponentsG.trans hcomponentsH.symm)
  rw [show Fintype.card (Fin 3 × Fin 3) = 9 by norm_num, hcomponentsG] at hs
  norm_num at hs
  exact fiber_source_difference_not_splits hs


end

end D5.S0.Certificates.GonzalezDLeonWachsWeightedBondDifferenceRefutation
