/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CrossWitnessTotal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CrossWitnessTotal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Opposite cross faces at one axis satisfy the unrestricted and common-parity caps. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EdgeStarAmbient
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PairedFibreAnyAxis
import Batteries.Tactic.OpenPrivate

/-!
# Geometric counts of opposite cross faces in the nine-cube

A four-face is counted by its active axes and frozen bits. A witness across
separated supports forces an apex with three paired neighbours at the chosen
main axis. Huang energy bounds the number of witness fibres of this kind.

The projected apex also depends only on the actual anchor edge. The directions
at its two endpoints determine the five-face, so changing the order of its
axes or exchanging the endpoints does not change the antipodal projection.
For a common witness parity the anchor injection uses the complementary
parity, which gives a sharper bound when combined with the energy count.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CrossWitnessTotal

section Apex

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip)
open BalancedCubeGirth (flip_comm)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions)
open Q4FaceCapacity (DeficiencyWitness project)
open Q9ThreeAxisBlock (active)
open Q9ThreeAxisBoundaryTransport (columnParity)
open CoordinateHalves.Q9ThreeAxisCapacityTransport (faceSupport)
open Q9EdgeStarAmbient (BalancedLeaves Separated remainingAxes)

open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private CubeCoordinateFace.adj_lift_iff CubeCoordinateFace.lift_active
  CubeCoordinateFace.lift_inactive from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9ThreeAxisCapacityTransport
open private edgeStar headLift top basedLift basedLift_flip addRoot_adj
  localSupport mem_localSupport rootBits transverseSlice literalSupport faceMask
  slice_image parity_faceMask deficiencyWitness_translate zero_side_impossible
  oppositeWitness_forces faceSupport_eq_slice column_with_frozen_bit
  projected_ne_of_agree projected_eq_split parity_eq_add skip_main main_not_active from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EdgeStarAmbient

private theorem flip_antipodal_head :
    ∀ b : Bool, flip (headLift b top) 0 = headLift (!b) top := by
  decide +kernel

abbrev FourFaceCode := Finset (Fin 9) × Q 9

/-- The active directions and the frozen bits, with false in the active coordinates. -/
def fourFaceCode (M : Finset (Fin 9)) (z : Q 9) : FourFaceCode :=
  (M, fun j => if j ∈ M then false else z j)

/-- The data of an ambient opposite witness at its specified even representative. -/
def OppositeFaceAt (axes : Fin 5 ↪ Fin 9) (root : Q 9) (D : Finset (Q 9))
    (r : Fin 4) (z : Q 9) : Prop :=
  (∀ j, (¬ ∃ k, axes k = j) → z j = root j) ∧
    (∑ j : Fin 9, z j) = false ∧
    (∑ j : Fin 8, z ((axes 0).succAbove j)) ≠
      (∑ j : Fin 8, root ((axes 0).succAbove j)) ∧
    DeficiencyWitness (faceSupport D (remainingAxes axes r) z (axes 0)) 0
      (columnParity (remainingAxes axes r) z false)

/-- The selected endpoint of a single main-axis fibre with three paired neighbours. -/
private def IsThreeContactApex (D : Finset (Q 9)) (i : Fin 9) (x : Q 9) : Prop :=
  x ∈ D ∧ (directions D x).card = 3 ∧ flip x i ∉ D ∧
    ∀ j ∈ directions D x, flip (flip x j) i ∈ D

private theorem fourFaceCode_eq_of_agree (M : Finset (Fin 9)) (z x : Q 9)
    (hagree : ∀ j ∉ M, z j = x j) : fourFaceCode M z = fourFaceCode M x := by
  unfold fourFaceCode
  apply congrArg (Prod.mk M)
  funext j
  by_cases hj : j ∈ M
  · simp only [ite_eq_left hj]
  · simp only [ite_eq_right hj, hagree j hj]

/-- Transport the defect while keeping the omitted bit of its slice explicit. -/
private theorem opposite_slice_of_literal (axes : Fin 5 ↪ Fin 9) (root : Q 9)
    (D : Finset (Q 9)) (r : Fin 4) (ε b : Bool)
    (hpar : b + ε ≠ ∑ j : Fin 4, root (axes j.succ))
    (h : DeficiencyWitness (transverseSlice (literalSupport axes root D) r ε) 0 b) :
    DeficiencyWitness
      (transverseSlice (localSupport axes root D) r (ε + rootBits axes root r.succ))
      0 (!(ε + rootBits axes root r.succ)) := by
  let v := rootBits axes root
  let p := cubeParity (project 0 (faceMask r v))
  have hs : (∑ j : Fin 4, root (axes j.succ)) = v r.succ + p :=
    parity_faceMask r v
  have hb : b + p = !(ε + v r.succ) := by
    rw [hs] at hpar
    generalize h₁ : v r.succ = f at hpar ⊢
    generalize h₂ : p = g at hpar ⊢
    revert hpar
    cases b <;> cases ε <;> cases f <;> cases g <;> decide
  change DeficiencyWitness (transverseSlice (localSupport axes root D) r (ε + v r.succ))
    0 (!(ε + v r.succ))
  rw [slice_image axes root D r ε, ← hb]
  exact deficiencyWitness_translate _ _ _ _ h

open Classical in
/-- A separated witness yields an apex whose three selected directions are the
transverse directions of the four-face. Its frozen bits agree with z and its
transverse coordinates are antipodal to the root. -/
private theorem opposite_face_has_apex (C D : Finset (Q 9))
    (hreg : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, u ≠ v ∧ ¬ (hypercube 9).Adj u v)
    (axes : Fin 5 ↪ Fin 9) (root z : Q 9) (s : Fin 4 → Bool) (r : Fin 4)
    (hs : BalancedLeaves s) (hstar : ∀ u ∈ edgeStar s, basedLift axes root u ∈ C)
    (hw : OppositeFaceAt axes root D r z) :
    ∃ x : Q 9, IsThreeContactApex D (axes 0) x ∧
      directions D x = active (remainingAxes axes r) ∧
      ((∑ j : Fin 8, x ((axes 0).succAbove j)) = ∑ j : Fin 8, root ((axes 0).succAbove j)) ∧
      (∀ j ∉ insert (axes 0) (active (remainingAxes axes r)), x j = z j) ∧
      (∀ j : Fin 4, x (axes j.succ) = !(root (axes j.succ))) ∧
      ∀ j, (¬ ∃ k, axes k = j) → x j = root j := by
  obtain ⟨hag, hz, hp, hdef⟩ := hw
  have hlocalSep : Separated s (localSupport axes root D) := by
    intro u hu v hv
    obtain ⟨hne, hna⟩ :=
      hsep _ (hstar u hu) _ ((mem_localSupport axes root D v).mp hv)
    refine ⟨fun he => hne (congrArg (basedLift axes root) he), ?_⟩
    intro huv
    exact hna ((CubeCoordinateFace.adj_lift_iff axes root _ _).mpr (addRoot_adj axes root huv))
  have hpar : columnParity (remainingAxes axes r) z false + z (axes r.succ) ≠
      ∑ j : Fin 4, root (axes j.succ) := by
    rw [column_with_frozen_bit axes z r hz]
    exact projected_ne_of_agree axes root z hag hp
  rw [faceSupport_eq_slice axes root z D r hag] at hdef
  have hslice := opposite_slice_of_literal axes root D r _ _ hpar hdef
  have hfar : z (axes r.succ) + rootBits axes root r.succ = true := by
    cases hb : z (axes r.succ) + rootBits axes root r.succ with
    | false =>
      exact (zero_side_impossible hs hlocalSep r (by simpa only [hb, Bool.not_false] using hslice)).elim
    | true => rfl
  obtain ⟨⟨a, ha⟩, hspokes⟩ :=
    oppositeWitness_forces hs hlocalSep r ⟨_, hslice⟩
  let x := basedLift axes root (headLift a top)
  let spokes := remainingAxes axes r
  have hx : x ∈ D := (mem_localSupport axes root D _).mp ha
  have hspoke (b : Bool) (j : Fin 3) :
      flip (basedLift axes root (headLift b top)) (spokes j) ∈ D := by
    change flip (basedLift axes root (headLift b top)) (axes (r.succ.succAbove j.succ)) ∈ D
    rw [skip_main, ← basedLift_flip]
    exact (mem_localSupport axes root D _).mp
      (hspokes (r.succAbove j) (Fin.succAbove_ne r j) b)
  have hcard := regular_directions D hreg hx
  have hdirs : directions D x = active spokes := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp (show j ∈ Finset.univ.map spokes from hj)
      exact (mem_directions D x _).mpr (hspoke a k)
    · rw [hcard]
      simp [active]
  have hmate : flip x (axes 0) ∉ D := by
    intro hm
    have hi := (mem_directions D x (axes 0)).mpr hm
    rw [hdirs] at hi
    exact main_not_active axes r hi
  have hpaired : ∀ j ∈ directions D x, flip (flip x j) (axes 0) ∈ D := by
    have hmateLift : flip x (axes 0) = basedLift axes root (headLift (!a) top) := by
      change flip (basedLift axes root (headLift a top)) (axes 0) = _
      rw [← basedLift_flip, flip_antipodal_head]
    intro j hj
    rw [hdirs, active] at hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hj
    rw [flip_comm x (spokes k) (axes 0), hmateLift]
    exact hspoke (!a) k
  have htransverse (j : Fin 4) : x (axes j.succ) = !(root (axes j.succ)) := by
    change basedLift axes root (headLift a top) (axes j.succ) = _
    unfold basedLift
    rw [CubeCoordinateFace.lift_active]
    change headLift a top j.succ + root (axes j.succ) = _
    have hbit : headLift a top j.succ = true := by
      simpa only [headLift, top, Fin.succAbove_zero_apply] using
        (Fin.insertNth_apply_succAbove (α := fun _ => Bool) (0 : Fin 5) a top j)
    rw [hbit]
    cases root (axes j.succ) <;> rfl
  have hfrozen (j : Fin 9) (hj : ¬ ∃ k, axes k = j) : x j = root j := by
    exact CubeCoordinateFace.lift_inactive axes root _ hj
  have homit : x (axes r.succ) = z (axes r.succ) := by
    apply (parity_eq_add _ _ (root (axes r.succ))).mp
    calc
      x (axes r.succ) + root (axes r.succ) = true := by
        rw [htransverse]
        cases root (axes r.succ) <;> rfl
      _ = z (axes r.succ) + root (axes r.succ) := hfar.symm
  have hprojected : (∑ j : Fin 8, x ((axes 0).succAbove j)) =
      ∑ j : Fin 8, root ((axes 0).succAbove j) := by
    have hfour : (∑ j : Fin 4, x (axes j.succ)) =
        ∑ j : Fin 4, root (axes j.succ) := by
      calc
        _ = ∑ j : Fin 4, ((true : Bool) + root (axes j.succ)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [htransverse j]
          cases root (axes j.succ) <;> rfl
        _ = _ := by
          rw [Finset.sum_add_distrib]
          have hzero : (∑ _ : Fin 4, (true : Bool)) = 0 := by decide
          rw [hzero, zero_add]
    have hoffsum : (∑ j ∈ Finset.univ \ Finset.univ.map axes, x j) =
        ∑ j ∈ Finset.univ \ Finset.univ.map axes, root j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hout : ¬ ∃ k, axes k = j := by
        rintro ⟨k, hk⟩
        exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_map.mpr ⟨k, Finset.mem_univ k, hk⟩)
      exact hfrozen j hout
    rw [projected_eq_split axes x, projected_eq_split axes root, hoffsum, hfour]
  refine ⟨x, ⟨hx, hcard, hmate, hpaired⟩, hdirs, hprojected, ?_, htransverse, hfrozen⟩
  intro j hj
  by_cases hjAxes : ∃ k, axes k = j
  · obtain ⟨k, rfl⟩ := hjAxes
    by_cases hk : k = r.succ
    · subst k
      exact homit
    · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq hk
      exfalso
      apply hj
      refine Fin.cases ?_ (fun l => ?_) t
      · rw [Fin.succ_succAbove_zero]
        exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        change axes (r.succ.succAbove l.succ) ∈ Finset.univ.map (remainingAxes axes r)
        exact Finset.mem_map.mpr ⟨l, Finset.mem_univ _, rfl⟩
  · exact (hfrozen j hjAxes).trans (hag j hjAxes).symm

/-- A geometric face code obtained from a based balanced star and an opposite witness. -/
def IsCrossOppositeFace (C D : Finset (Q 9)) (i : Fin 9) (F : FourFaceCode) : Prop :=
  ∃ (axes : Fin 5 ↪ Fin 9) (root z : Q 9) (s : Fin 4 → Bool) (r : Fin 4),
    axes 0 = i ∧ BalancedLeaves s ∧
    (∀ u ∈ edgeStar s, basedLift axes root u ∈ C) ∧ OppositeFaceAt axes root D r z ∧
    F = fourFaceCode (insert i (active (remainingAxes axes r))) z

end Apex

section Energy

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip IsBalanced)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9ThreeAxisBlock (active)
open Q9EdgeStarAmbient (BalancedLeaves remainingAxes)
open Q9OccupiedFibreParity (doubleFibres)
open Q9PairedFibreAnyAxis (singleFibres mem_singleFibres triple_contact_card_le)
open private edgeStar basedLift from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EdgeStarAmbient
open private liftVertex insert_drop flip_insert dropCoordinate_flip_keep parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

private abbrev dropAxis (i : Fin 9) (x : Q 9) : Q 8 :=
  Fin.removeNth (α := fun _ : Fin 9 => Bool) i x

/-- The face is specified by its active axes and frozen bits. The parity class
is imposed on the witness representative after projection along the main axis. -/
def IsCrossOppositeFaceOfParity (C D : Finset (Q 9)) (i : Fin 9) (p : Bool)
    (F : FourFaceCode) : Prop :=
  ∃ (axes : Fin 5 ↪ Fin 9) (root z : Q 9) (s : Fin 4 → Bool) (r : Fin 4),
    axes 0 = i ∧ BalancedLeaves s ∧
    (∀ u ∈ edgeStar s, basedLift axes root u ∈ C) ∧ OppositeFaceAt axes root D r z ∧
    (∑ j : Fin 8, z (i.succAbove j)) = p ∧
    F = fourFaceCode (insert i (active (remainingAxes axes r))) z

private theorem other_lift (i : Fin 9) (x : Q 9) :
    liftVertex i (!(x i)) (dropAxis i x) = flip x i := by
  have hself : liftVertex i (x i) (dropAxis i x) = x := insert_drop i x
  rw [← flip_insert, hself]

private theorem mem_double_projected_iff (D : Finset (Q 9)) (i : Fin 9) (p : Bool)
    (x : Q 9) :
    dropAxis i x ∈ doubleFibres D i p ↔
      (x ∈ D ∧ flip x i ∈ D) ∧ cubeParity (dropAxis i x) = p := by
  have hself : liftVertex i (x i) (dropAxis i x) = x := insert_drop i x
  have hother := other_lift i x
  simp only [doubleFibres, Finset.mem_filter, Finset.mem_univ, true_and, cubeParity]
  cases hbit : x i <;>
    simp only [hbit, Bool.not_false, Bool.not_true] at hself hother
  · simp only [hself, hother]
  · simp only [hself, hother, (and_comm : (flip x i ∈ D ∧ x ∈ D) ↔ (x ∈ D ∧ flip x i ∈ D))]

private theorem apex_projects_to_triple_contact {D : Finset (Q 9)} {i : Fin 9}
    {p : Bool} {x : Q 9} (ha : IsThreeContactApex D i x)
    (hp : cubeParity (dropAxis i x) = !p) :
    dropAxis i x ∈ (singleFibres D i (!p)).filter
      (fun q => (directions (doubleFibres D i p) q).card = 3) := by
  obtain ⟨hx, hcard, hmate, hpaired⟩ := ha
  have hsingle : dropAxis i x ∈ singleFibres D i (!p) := by
    refine mem_singleFibres.mpr ⟨hp, ?_⟩
    have hself : liftVertex i (x i) (dropAxis i x) = x := insert_drop i x
    have hother := other_lift i x
    cases hbit : x i <;>
      simp only [hbit, Bool.not_false, Bool.not_true] at hself hother
    · left
      rw [hself, hother]
      exact ⟨hx, hmate⟩
    · right
      rw [hself, hother]
      exact ⟨hx, hmate⟩
  have hmem (k : Fin 8) :
      k ∈ directions (doubleFibres D i p) (dropAxis i x) ↔
        i.succAbove k ∈ directions D x := by
    have hdrop : dropAxis i (flip x (i.succAbove k)) = flip (dropAxis i x) k :=
      dropCoordinate_flip_keep i k x
    have hpar : cubeParity (dropAxis i (flip x (i.succAbove k))) = p := by
      rw [hdrop]
      have he : cubeParity (flip (dropAxis i x) k) = !cubeParity (dropAxis i x) :=
        parity_flip (dropAxis i x) k
      simpa only [hp, Bool.not_not] using he
    rw [mem_directions (doubleFibres D i p), ← hdrop, mem_double_projected_iff]
    constructor
    · intro hk
      exact (mem_directions D x _).mpr hk.1.1
    · intro hk
      exact ⟨⟨(mem_directions D x _).mp hk, hpaired _ hk⟩, hpar⟩
  have hdirs : (directions (doubleFibres D i p) (dropAxis i x)).map i.succAboveEmb =
      directions D x := by
    ext j
    constructor
    · intro hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
      exact (hmem k).mp hk
    · intro hj
      have hji : j ≠ i := by
        intro he
        subst j
        exact hmate ((mem_directions D x i).mp hj)
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
      exact Finset.mem_map.mpr ⟨k, (hmem k).mpr hj, rfl⟩
  have hcount := (congrArg Finset.card hdirs).trans hcard
  exact Finset.mem_filter.mpr ⟨hsingle, by simpa only [Finset.card_map] using hcount⟩

private theorem single_projection_inj {D : Finset (Q 9)} {i : Fin 9} {x y : Q 9}
    (hmate : flip x i ∉ D) (hy : y ∈ D) (hq : dropAxis i x = dropAxis i y) : x = y := by
  have hxy : y = liftVertex i (y i) (dropAxis i x) := by
    rw [hq]
    exact (insert_drop i y).symm
  by_cases hbit : y i = x i
  · rw [hbit] at hxy
    have hself : liftVertex i (x i) (dropAxis i x) = x := insert_drop i x
    exact (hxy.trans hself).symm
  · rw [Bool.eq_not_of_ne hbit, other_lift] at hxy
    exact (hmate (hxy ▸ hy)).elim

open Classical in
/-- Each face uses a distinct single fibre of parity !p with exactly three
paired neighbours of parity p. -/
private theorem cross_opposite_faces_into_triple_contacts (C D : Finset (Q 9)) (i : Fin 9)
    (p : Bool) (faces : Finset FourFaceCode)
    (hreg : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, u ≠ v ∧ ¬ (hypercube 9).Adj u v)
    (hfaces : ∀ F ∈ faces, IsCrossOppositeFaceOfParity C D i p F) :
    ∃ fibre : FourFaceCode → Q 8, Set.InjOn fibre (faces : Set FourFaceCode) ∧
      Set.MapsTo fibre (faces : Set FourFaceCode)
        (↑((singleFibres D i (!p)).filter
          (fun q => (directions (doubleFibres D i p) q).card = 3)) : Set (Q 8)) := by
  have hex (F : FourFaceCode) (hF : F ∈ faces) :
      ∃ x, IsThreeContactApex D i x ∧ cubeParity (dropAxis i x) = !p ∧
        F = fourFaceCode (insert i (directions D x)) x := by
    obtain ⟨axes, root, z, s, r, hi, hs, hstar, hw, hzpar, hcode⟩ := hfaces F hF
    obtain ⟨x, hx, hdirs, hprojected, hfreeze, _, _⟩ :=
      opposite_face_has_apex C D hreg hsep axes root z s r hs hstar hw
    obtain ⟨_, _, hne, _⟩ := hw
    rw [hi, hzpar] at hne
    rw [hi] at hx hprojected hfreeze
    refine ⟨x, hx, hprojected.trans (Bool.eq_not_of_ne hne.symm), ?_⟩
    rw [hcode, hdirs]
    exact fourFaceCode_eq_of_agree _ _ _ (fun j hj => (hfreeze j hj).symm)
  let apex (F : FourFaceCode) : Q 9 :=
    if hF : F ∈ faces then Classical.choose (hex F hF) else fun _ => false
  have hapex (F : FourFaceCode) (hF : F ∈ faces) :
      IsThreeContactApex D i (apex F) ∧ cubeParity (dropAxis i (apex F)) = !p ∧
        F = fourFaceCode (insert i (directions D (apex F))) (apex F) := by
    simpa only [apex, dite_eq_left hF] using Classical.choose_spec (hex F hF)
  refine ⟨fun F => dropAxis i (apex F), ?_, ?_⟩
  · intro F hF G hG he
    obtain ⟨hFa, _, hFc⟩ := hapex F hF
    obtain ⟨hGa, _, hGc⟩ := hapex G hG
    have hEq : apex F = apex G := single_projection_inj hFa.2.2.1 hGa.1 he
    rw [hFc, hGc, hEq]
  · intro F hF
    exact apex_projects_to_triple_contact (hapex F hF).1 (hapex F hF).2.1

open Classical in
/-- Fixed-axis energy cap for the geometric faces anchored in C and witnessed in D. -/
private theorem cross_opposite_face_card_budget (C D : Finset (Q 9)) (i : Fin 9)
    (p : Bool) (faces : Finset FourFaceCode)
    (hreg : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbal : IsBalanced D)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, u ≠ v ∧ ¬ (hypercube 9).Adj u v)
    (hfaces : ∀ F ∈ faces, IsCrossOppositeFaceOfParity C D i p F) :
    3 * faces.card ≤ 2 * (doubleFibres D i p).card := by
  obtain ⟨fibre, hinj, hmaps⟩ :=
    cross_opposite_faces_into_triple_contacts C D i p faces hreg hsep hfaces
  have hcard := Finset.card_le_card_of_injOn fibre hmaps hinj
  exact (Nat.mul_le_mul_left 3 hcard).trans (triple_contact_card_le hreg hbal i p)

end Energy

section Anchor

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions)
open Q9ThreeAxisBlock (active)
open Q9EdgeStarAmbient (BalancedLeaves remainingAxes)
open Q9OccupiedFibreParity (doubleFibres)

open private zero unit headLift edgeStar endpoint_mem leaf_mem leaf_words lift_zero
  basedLift basedLift_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EdgeStarAmbient
open private liftVertex insert_drop from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity

private theorem anchor_leaf_word :
    ∀ (b : Bool) (j : Fin 4),
      headLift b (unit j) = flip (headLift b (zero 4)) j.succ := by
  decide +kernel

private theorem anchor_axes_eq (C : Finset (Q 9)) (root : Q 9) (i : Fin 9)
    (hx : root ∈ C) (hy : flip root i ∈ C)
    (hxdeg : (directions C root).card = 3)
    (hydeg : (directions C (flip root i)).card = 3)
    (axes : Fin 5 ↪ Fin 9) (s : Fin 4 → Bool) (hi : axes 0 = i)
    (hstar : ∀ x ∈ edgeStar s, basedLift axes root x ∈ C) :
    Finset.univ.map axes = directions C root ∪ directions C (flip root i) := by
  have hiRoot : i ∈ directions C root := (mem_directions _ _ _).mpr hy
  have hiMate : i ∈ directions C (flip root i) :=
    (mem_directions _ _ _).mpr (by simpa only [BalancedCriticalSpectrum.flip_flip] using hx)
  have hendpoint (b : Bool) : basedLift axes root (headLift b (zero 4)) =
      (if b then flip root i else root) := by
    cases b
    · change basedLift axes root (headLift false (fun _ => false)) = root
      rw [leaf_words.1, lift_zero]
    · change basedLift axes root (headLift true (fun _ => false)) = flip root i
      rw [leaf_words.2.1, basedLift_flip, lift_zero, hi]
  have hsub : Finset.univ.map axes ⊆ directions C root ∪ directions C (flip root i) := by
    intro k hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hk
    refine Fin.cases ?_ (fun t => ?_) j
    · rw [hi]
      exact Finset.mem_union.mpr (Or.inl hiRoot)
    · have hleaf := hstar _ (leaf_mem s t)
      rw [anchor_leaf_word, basedLift_flip, hendpoint] at hleaf
      cases hside : s t
      · exact Finset.mem_union.mpr (Or.inl
          ((mem_directions _ _ _).mpr (by simpa [hside] using hleaf)))
      · exact Finset.mem_union.mpr (Or.inr
          ((mem_directions _ _ _).mpr (by simpa [hside] using hleaf)))
  apply Finset.eq_of_subset_of_card_le hsub
  have hcard : (Finset.univ.map axes).card = 5 := by simp
  have hcommon : 0 < (directions C root ∩ directions C (flip root i)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_inter.mpr ⟨hiRoot, hiMate⟩⟩
  have hunion := Finset.card_union_add_card_inter (directions C root)
    (directions C (flip root i))
  rw [hxdeg, hydeg] at hunion
  omega

set_option backward.isDefEq.respectTransparency false

/-- A geometric opposite witness whose actual anchor edge projects to q. -/
private def IsCrossOppositeFaceAtAnchor (C D : Finset (Q 9)) (i : Fin 9)
    (F : FourFaceCode) (q : Q 8) : Prop :=
  ∃ (axes : Fin 5 ↪ Fin 9) (root z : Q 9) (s : Fin 4 → Bool) (r : Fin 4),
    axes 0 = i ∧ BalancedLeaves s ∧
    (∀ u ∈ edgeStar s, basedLift axes root u ∈ C) ∧ OppositeFaceAt axes root D r z ∧
    F = fourFaceCode (insert i (active (remainingAxes axes r))) z ∧ dropAxis i root = q

private theorem star_endpoints (C : Finset (Q 9)) (i : Fin 9)
    (axes : Fin 5 ↪ Fin 9) (root : Q 9) (s : Fin 4 → Bool) (hi : axes 0 = i)
    (hstar : ∀ u ∈ edgeStar s, basedLift axes root u ∈ C) :
    root ∈ C ∧ flip root i ∈ C := by
  have hroot := hstar _ (endpoint_mem s false)
  have hmate := hstar _ (endpoint_mem s true)
  change basedLift axes root (headLift false (fun _ => false)) ∈ C at hroot
  change basedLift axes root (headLift true (fun _ => false)) ∈ C at hmate
  rw [leaf_words.1, lift_zero] at hroot
  rw [leaf_words.2.1, basedLift_flip, lift_zero, hi] at hmate
  exact ⟨hroot, hmate⟩

private noncomputable def anchorDirections (C : Finset (Q 9)) (i : Fin 9)
    (q : Q 8) : Finset (Fin 9) :=
  directions C (liftVertex i false q) ∪ directions C (liftVertex i true q)

open Classical in
private theorem star_axes_eq (C : Finset (Q 9)) (i : Fin 9)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (axes : Fin 5 ↪ Fin 9) (root : Q 9) (s : Fin 4 → Bool) (hi : axes 0 = i)
    (hstar : ∀ u ∈ edgeStar s, basedLift axes root u ∈ C) :
    Finset.univ.map axes = anchorDirections C i (dropAxis i root) := by
  obtain ⟨hx, hy⟩ := star_endpoints C i axes root s hi hstar
  have haxes := anchor_axes_eq C root i hx hy (regular_directions C hreg hx)
    (regular_directions C hreg hy) axes s hi hstar
  have hself : liftVertex i (root i) (dropAxis i root) = root := insert_drop i root
  have hother := other_lift i root
  unfold anchorDirections
  cases hb : root i <;>
    simp only [hb, Bool.not_false, Bool.not_true] at hself hother
  · rw [hself, hother]
    exact haxes
  · rw [hother, hself, Finset.union_comm]
    exact haxes

private noncomputable def antipodalFibre (C : Finset (Q 9)) (i : Fin 9) (q : Q 8) : Q 8 :=
  fun k => if i.succAbove k ∈ anchorDirections C i q then !(q k) else q k

open Classical in
/-- The actual apex projects to the antipode of the anchor in its five-face.
Its three selected directions and frozen bits determine the face code. -/
private theorem anchored_face_has_apex (C D : Finset (Q 9)) (i : Fin 9)
    (hregC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hregD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, u ≠ v ∧ ¬ (hypercube 9).Adj u v)
    {F : FourFaceCode} {q : Q 8} (hF : IsCrossOppositeFaceAtAnchor C D i F q) :
    ∃ x : Q 9, x ∈ D ∧ flip x i ∉ D ∧ dropAxis i x = antipodalFibre C i q ∧
      F = fourFaceCode (insert i (directions D x)) x := by
  classical
  obtain ⟨axes, root, z, s, r, hi, hs, hstar, hw, hcode, hq⟩ := hF
  obtain ⟨x, hx, hdirs, _, hfreeze, htransverse, hfrozen⟩ :=
    opposite_face_has_apex C D hregD hsep axes root z s r hs hstar hw
  rw [hi] at hx hfreeze
  refine ⟨x, hx.1, hx.2.2.1, ?_, ?_⟩
  · have haxes := star_axes_eq C i hregC axes root s hi hstar
    rw [← hq]
    funext k
    change x (i.succAbove k) =
      if i.succAbove k ∈ anchorDirections C i (dropAxis i root) then
        !(root (i.succAbove k)) else root (i.succAbove k)
    rw [← haxes]
    by_cases hk : i.succAbove k ∈ Finset.univ.map axes
    · rw [ite_eq_left hk]
      obtain ⟨j, _, he⟩ := Finset.mem_map.mp hk
      have hj : j ≠ 0 := by
        intro hj
        rw [hj, hi] at he
        exact Fin.succAbove_ne i k he.symm
      obtain ⟨t, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj
      rw [← he]
      exact htransverse t
    · rw [ite_eq_right hk]
      exact hfrozen _ (fun ⟨j, hj⟩ => hk (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, hj⟩))
  · rw [hcode, hdirs]
    exact fourFaceCode_eq_of_agree _ _ _ (fun j hj => (hfreeze j hj).symm)

open Classical in
/-- Opposite witnesses in D on a common actual anchor fibre have the same code. -/
private theorem anchor_fibre_determines_cross_opposite_face (C D : Finset (Q 9)) (i : Fin 9)
    (hregC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hregD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, u ≠ v ∧ ¬ (hypercube 9).Adj u v)
    {F G : FourFaceCode} {q : Q 8}
    (hF : IsCrossOppositeFaceAtAnchor C D i F q)
    (hG : IsCrossOppositeFaceAtAnchor C D i G q) : F = G := by
  obtain ⟨x, _, hmate, hxq, hFc⟩ := anchored_face_has_apex C D i hregC hregD hsep hF
  obtain ⟨y, hy, _, hyq, hGc⟩ := anchored_face_has_apex C D i hregC hregD hsep hG
  have hxy : x = y := single_projection_inj hmate hy (hxq.trans hyq.symm)
  rw [hFc, hGc, hxy]

open Classical in
/-- Any family of geometric cross faces of witness parity p injects into
the actual complementary anchor fibres in C. -/
private theorem cross_opposite_faces_into_anchor_fibres (C D : Finset (Q 9)) (i : Fin 9)
    (p : Bool) (faces : Finset FourFaceCode)
    (hregC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hregD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, u ≠ v ∧ ¬ (hypercube 9).Adj u v)
    (hfaces : ∀ F ∈ faces, IsCrossOppositeFaceOfParity C D i p F) :
    ∃ anchor : FourFaceCode → Q 8, Set.InjOn anchor (faces : Set FourFaceCode) ∧
      ∀ F ∈ faces, anchor F ∈ doubleFibres C i (!p) ∧
        IsCrossOppositeFaceAtAnchor C D i F (anchor F) := by
  have hex (F : FourFaceCode) (hF : F ∈ faces) :
      ∃ q ∈ doubleFibres C i (!p), IsCrossOppositeFaceAtAnchor C D i F q := by
    obtain ⟨axes, root, z, s, r, hi, hs, hstar, hw, hzpar, hcode⟩ := hfaces F hF
    refine ⟨dropAxis i root, ?_, ⟨axes, root, z, s, r, hi, hs, hstar, hw, hcode, rfl⟩⟩
    apply (mem_double_projected_iff C i (!p) root).mpr
    have hne := hw.2.2.1
    rw [hi, hzpar] at hne
    exact ⟨star_endpoints C i axes root s hi hstar, Bool.eq_not_of_ne hne.symm⟩
  let anchor (F : FourFaceCode) : Q 8 :=
    if hF : F ∈ faces then Classical.choose (hex F hF) else fun _ => false
  have hanchor (F : FourFaceCode) (hF : F ∈ faces) :
      anchor F ∈ doubleFibres C i (!p) ∧ IsCrossOppositeFaceAtAnchor C D i F (anchor F) := by
    simpa only [anchor, dite_eq_left hF] using Classical.choose_spec (hex F hF)
  refine ⟨anchor, ?_, hanchor⟩
  intro F hF G hG he
  have hGq := (hanchor G hG).2
  rw [← he] at hGq
  exact anchor_fibre_determines_cross_opposite_face C D i hregC hregD hsep
    (hanchor F hF).2 hGq

open Classical in
private theorem cross_opposite_face_anchor_card_le (C D : Finset (Q 9)) (i : Fin 9)
    (p : Bool) (faces : Finset FourFaceCode)
    (hregC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hregD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, u ≠ v ∧ ¬ (hypercube 9).Adj u v)
    (hfaces : ∀ F ∈ faces, IsCrossOppositeFaceOfParity C D i p F) :
    faces.card ≤ (doubleFibres C i (!p)).card := by
  obtain ⟨anchor, hinj, hanchor⟩ :=
    cross_opposite_faces_into_anchor_fibres C D i p faces hregC hregD hsep hfaces
  exact Finset.card_le_card_of_injOn anchor (fun F hF => (hanchor F hF).1) hinj

end Anchor

section Counts

set_option backward.isDefEq.respectTransparency false

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count)
open Q9OccupiedFibreParity (doubleFibres)
open private doubleFibres_partition from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity

private theorem separated_symm {C D : Finset (Q 9)}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, u ≠ v ∧ ¬ (hypercube 9).Adj u v) :
    ∀ u ∈ D, ∀ v ∈ C, u ≠ v ∧ ¬ (hypercube 9).Adj u v := by
  intro u hu v hv
  obtain ⟨hne, hna⟩ := hsep v hv u hu
  exact ⟨hne.symm, fun h => hna h.symm⟩

open Classical in
private theorem cross_opposite_faces_direction_budget (C D : Finset (Q 9)) (i : Fin 9)
    (faces : Finset FourFaceCode) (hfaces : ∀ F ∈ faces, IsCrossOppositeFace C D i F)
    (hreg : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbal : IsBalanced D)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, u ≠ v ∧ ¬ (hypercube 9).Adj u v) :
    3 * faces.card ≤ 2 * directionEdges D i := by
  classical
  let evenFaces := faces.filter (IsCrossOppositeFaceOfParity C D i false)
  let oddFaces := faces.filter (IsCrossOppositeFaceOfParity C D i true)
  have hcover : faces ⊆ evenFaces ∪ oddFaces := by
    intro F hF
    have hcross := hfaces F hF
    obtain ⟨axes, root, z, s, r, hi, hs, hstar, hw, hcode⟩ := hcross
    cases hp : (∑ j : Fin 8, z (i.succAbove j)) with
    | false =>
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hF, ⟨axes, root, z, s, r, hi, hs, hstar, hw, hp, hcode⟩⟩)
    | true =>
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hF, ⟨axes, root, z, s, r, hi, hs, hstar, hw, hp, hcode⟩⟩)
  have heven := cross_opposite_face_card_budget C D i false evenFaces hreg hbal hsep
    (fun F hF => by
      change F ∈ faces.filter (IsCrossOppositeFaceOfParity C D i false) at hF
      exact (Finset.mem_filter.mp hF).2)
  have hodd := cross_opposite_face_card_budget C D i true oddFaces hreg hbal hsep
    (fun F hF => by
      change F ∈ faces.filter (IsCrossOppositeFaceOfParity C D i true) at hF
      exact (Finset.mem_filter.mp hF).2)
  have hcoverCard := (Finset.card_le_card hcover).trans (Finset.card_union_le evenFaces oddFaces)
  have hpartition : (doubleFibres D i false).card + (doubleFibres D i true).card =
      directionEdges D i := doubleFibres_partition D i false
  change 3 * faces.card ≤ 2 * directionEdges D i
  omega

open Classical in
/-- The unrestricted geometric union has a linear budget in the total support size. -/
private theorem cross_opposite_faces_union_budget (C D : Finset (Q 9)) (i : Fin 9)
    (facesCD facesDC : Finset FourFaceCode)
    (hfacesCD : ∀ F ∈ facesCD, IsCrossOppositeFace C D i F)
    (hfacesDC : ∀ F ∈ facesDC, IsCrossOppositeFace D C i F)
    (hregC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hregD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbalC : IsBalanced C) (hbalD : IsBalanced D)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, u ≠ v ∧ ¬ (hypercube 9).Adj u v) :
    9 * (facesCD ∪ facesDC).card ≤ C.card + D.card := by
  have hCD := cross_opposite_faces_direction_budget C D i facesCD hfacesCD hregD hbalD hsep
  have hDC := cross_opposite_faces_direction_budget D C i facesDC hfacesDC hregC hbalC (separated_symm hsep)
  have hC : 6 * directionEdges C i = C.card := direction_edge_count (d := 3) C hregC hbalC i
  have hD : 6 * directionEdges D i = D.card := direction_edge_count (d := 3) D hregD hbalD i
  have hUnion := Finset.card_union_le facesCD facesDC
  omega

open Classical in
/-- At most 28 distinct opposite cross faces occur at a fixed axis with at most
258 total vertices. -/
theorem cross_opposite_faces_union_card_le_28 (C D : Finset (Q 9)) (i : Fin 9)
    (facesCD facesDC : Finset FourFaceCode)
    (hfacesCD : ∀ F ∈ facesCD, IsCrossOppositeFace C D i F)
    (hfacesDC : ∀ F ∈ facesDC, IsCrossOppositeFace D C i F)
    (hregC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hregD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbalC : IsBalanced C) (hbalD : IsBalanced D)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, u ≠ v ∧ ¬ (hypercube 9).Adj u v)
    (hsize : C.card + D.card ≤ 258) :
    (facesCD ∪ facesDC).card ≤ 28 := by
  have hbudget := cross_opposite_faces_union_budget C D i facesCD facesDC hfacesCD hfacesDC hregC hregD hbalC hbalD hsep
  omega

open Classical in
/-- The matched-parity budget for arbitrary families of opposite geometric
cross faces in both directions. -/
private theorem arbitrary_matched_parity_cross_faces_union_budget
    (C D : Finset (Q 9)) (i : Fin 9) (p : Bool)
    (facesCD facesDC : Finset FourFaceCode)
    (hfacesCD : ∀ F ∈ facesCD, IsCrossOppositeFaceOfParity C D i p F)
    (hfacesDC : ∀ F ∈ facesDC, IsCrossOppositeFaceOfParity D C i p F)
    (hregC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hregD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbalC : IsBalanced C) (hbalD : IsBalanced D)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, u ≠ v ∧ ¬ (hypercube 9).Adj u v) :
    15 * (facesCD ∪ facesDC).card ≤ C.card + D.card := by
  have hsepDC := separated_symm hsep
  have hCDanchor := cross_opposite_face_anchor_card_le C D i p facesCD hregC hregD hsep hfacesCD
  have hDCanchor := cross_opposite_face_anchor_card_le D C i p facesDC hregD hregC hsepDC hfacesDC
  have hCDwitness := cross_opposite_face_card_budget C D i p facesCD hregD hbalD hsep hfacesCD
  have hDCwitness := cross_opposite_face_card_budget D C i p facesDC hregC hbalC hsepDC hfacesDC
  have hUnion := Finset.card_union_le facesCD facesDC
  have hCpart := doubleFibres_partition C i p
  have hDpart := doubleFibres_partition D i p
  have hC : 6 * directionEdges C i = C.card := direction_edge_count (d := 3) C hregC hbalC i
  have hD : 6 * directionEdges D i = D.card := direction_edge_count (d := 3) D hregD hbalD i
  omega

open Classical in
/-- At most 17 geometric cross faces of a common witness parity occur in
the two directions for separated supports with at most 258 total vertices. -/
theorem arbitrary_matched_parity_cross_faces_union_card_le_17
    (C D : Finset (Q 9)) (i : Fin 9) (p : Bool)
    (facesCD facesDC : Finset FourFaceCode)
    (hfacesCD : ∀ F ∈ facesCD, IsCrossOppositeFaceOfParity C D i p F)
    (hfacesDC : ∀ F ∈ facesDC, IsCrossOppositeFaceOfParity D C i p F)
    (hregC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hregD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbalC : IsBalanced C) (hbalD : IsBalanced D)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, u ≠ v ∧ ¬ (hypercube 9).Adj u v)
    (hsize : C.card + D.card ≤ 258) :
    (facesCD ∪ facesDC).card ≤ 17 := by
  have hbudget := arbitrary_matched_parity_cross_faces_union_budget C D i p facesCD facesDC
    hfacesCD hfacesDC hregC hregD hbalC hbalD hsep
  omega

end Counts

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CrossWitnessTotal
