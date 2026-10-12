/- GID: D5/S3/ConceptDynamics/Coding/StandardBeamPushforward
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/StandardBeamPushforward
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: The full commuting history-homeomorphism group acts by actual set pushforward. -/
import D5.S3.ConceptDynamics.Coding.StandardTaggedBeams
import D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.StandardBeamPushforward
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.StandardBeamGeometry
open D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms
open D5.S3.ConceptDynamics.Coding.StandardBeamEndpointRows
open D5.S3.ConceptDynamics.Coding.StandardBeamCoordinates
open D5.S3.ConceptDynamics.Coding.StandardTaggedBeams
open D5.S3.ConceptDynamics.Coding.StandardBeamColimitCuts
open scoped BigOperators Matrix

universe u v
variable {V : Type u} {E : Type v} (G : DirectedMultigraph V E)
variable [Fintype V] [Fintype E] [DecidableEq V]
variable [TopologicalSpace V] [DiscreteTopology V]
variable [TopologicalSpace E] [DiscreteTopology E]
variable (hG : Essential G)

/-- A disjoint finite union of BEAMS, normalized at a common cut, is matched
by the disjoint sum of their intrinsic ray partitions. -/
def disjointBeamPartsEquiv {I : Type*} [Finite I] (U : I → Set (History G)) (n : ℤ)
    (hU : ∀ i, AtCut G (U i) n) (hd : ∀ i j, i ≠ j → Disjoint (U i) (U j)) :
    (Σ i : I, Parts G (U i) n) ≃ Parts G (⋃ i, U i) n := by
  let f : (Σ i : I, Parts G (U i) n) → Parts G (⋃ i, U i) n := fun P =>
    ⟨P.2.val, P.2.property.trans (Set.subset_iUnion _ P.1)⟩
  apply Equiv.ofBijective f
  constructor
  · intro P Q he
    have hs : P.2.val = Q.2.val := congrArg Subtype.val he
    have hij : P.1 = Q.1 := by
      by_contra hij
      obtain ⟨x, hx⟩ := RayAt.nonempty G P.2.val
      have hy : x ∈ Q.2.val.val := hs ▸ hx
      exact Set.disjoint_left.mp (hd P.1 Q.1 hij) (P.2.property hx) (Q.2.property hy)
    apply Sigma.ext hij
    apply (Subtype.heq_iff_coe_eq (fun R => by rw [hij])).mpr
    exact hs
  · intro P
    obtain ⟨x, hx⟩ := RayAt.nonempty G P.val
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (P.property hx)
    have he : P.val = rayAt G x n :=
      RayAt.eq_of_inter G _ _ x hx (self_mem_ray G _ _)
    refine ⟨⟨i, P.val, ?_⟩, Subtype.ext rfl⟩
    rw [he]
    exact (hU i).2 x hi

theorem endpointRow_disjointBeams {I : Type*} [Finite I] (U : I → Set (History G)) (n : ℤ)
    (hU : ∀ i, AtCut G (U i) n) (hd : ∀ i j, i ≠ j → Disjoint (U i) (U j)) :
    letI : Fintype I := Fintype.ofFinite _
    letI (i : I) : Finite (Parts G (U i) n) := (hU i).1
    letI : Finite (Parts G (⋃ i, U i) n) := (atCut_iUnion G U n hU).1
    endpointRow G (⋃ i, U i) n = ∑ i : I, endpointRow G (U i) n := by
  letI : Fintype I := Fintype.ofFinite _
  letI (i : I) : Finite (Parts G (U i) n) := (hU i).1
  letI (i : I) : Fintype (Parts G (U i) n) := Fintype.ofFinite _
  letI : Finite (Parts G (⋃ i, U i) n) := (atCut_iUnion G U n hU).1
  letI : Fintype (Parts G (⋃ i, U i) n) := Fintype.ofFinite _
  have he := Fintype.sum_equiv (disjointBeamPartsEquiv G U n hU hd)
    (fun P => (Pi.single (RayAt.endpoint G P.2.val) (1 : ℤ) : V → ℤ))
    (fun P => (Pi.single (RayAt.endpoint G P.val) (1 : ℤ) : V → ℤ)) (fun _ => rfl)
  simpa only [endpointRow, Fintype.sum_sigma] using he.symm

include hG

/-- Coordinates add for ACTUAL disjoint unions at a common cut. -/
theorem beamCoordinate_disjointBeams {I : Type*} [Finite I] (U : I → Beam G) (n : ℤ)
    (hU : ∀ i, AtCut G (U i).val n) (hd : ∀ i j, i ≠ j → Disjoint (U i).val (U j).val) :
    letI : Fintype I := Fintype.ofFinite _
    beamCoordinate G (⟨⋃ i, (U i).val, n, atCut_iUnion G _ n hU⟩ : Beam G) =
      ∑ i : I, beamCoordinate G (U i) := by
  letI : Fintype I := Fintype.ofFinite _
  rw [beamCoordinate_at G hG _ n (atCut_iUnion G _ n hU)]
  simp_rw [beamCoordinate_at G hG _ n (hU _)]
  unfold coordinateAt
  rw [endpointRow_disjointBeams G _ n hU hd, map_sum]

/-- Actual whole-ray images of a parallel pair have the same intrinsic
coordinate, by the conjugated-splice matching at n+a+b+d. -/
theorem parallel_image_coordinate (h : FullAut G) (alpha beta : History G) (n : ℤ)
    (ep : endpoint G alpha n = endpoint G beta n) :
    beamCoordinate G (imageBeam G hG h
      (⟨ray G alpha n, n, ray_atCut G hG alpha n⟩ : Beam G)) =
    beamCoordinate G (imageBeam G hG h
      (⟨ray G beta n, n, ray_atCut G hG beta n⟩ : Beam G)) := by
  obtain ⟨a, b, c, d, hab, hcd⟩ := fullAut_has_two_windows G h
  let ell := n + (a : ℤ) + (b : ℤ) + (d : ℤ)
  have hA := atCut_mono G hG (image_ray_atCut G hG h hab hcd alpha n)
    (show n + (d : ℤ) ≤ ell by dsimp [ell]; omega)
  have hB := atCut_mono G hG (image_ray_atCut G hG h hab hcd beta n)
    (show n + (d : ℤ) ≤ ell by dsimp [ell]; omega)
  rw [beamCoordinate_at G hG _ ell hA, beamCoordinate_at G hG _ ell hB]
  unfold coordinateAt
  congr 1
  letI : Finite (Parts G (h.val '' ray G alpha n) ell) := hA.1
  letI : Finite (Parts G (h.val '' ray G beta n) ell) := hB.1
  letI : Fintype (Parts G (h.val '' ray G alpha n) ell) := Fintype.ofFinite _
  letI : Fintype (Parts G (h.val '' ray G beta n) ell) := Fintype.ofFinite _
  exact Fintype.sum_equiv (conjugatePartsEquiv G hG h hab hcd alpha beta n ep) _ _
    (fun P => by rw [conjugatePartsEquiv_endpoint G hG h hab hcd alpha beta n ep])

/-- Exact image decomposition of ANY actual beam by its intrinsic ray pieces. -/
theorem image_coordinate_partition (h : FullAut G) (U : Beam G) (n : ℤ)
    (hn : AtCut G U.val n) :
    letI : Finite (Parts G U.val n) := hn.1
    letI : Fintype (Parts G U.val n) := Fintype.ofFinite _
    beamCoordinate G (imageBeam G hG h U) =
      ∑ P : Parts G U.val n,
        beamCoordinate G (imageBeam G hG h
          (⟨P.val.val, n, by
            rw [RayAt.set_eq G P.val]
            exact ray_atCut G hG _ n⟩ : Beam G)) := by
  letI : Finite (Parts G U.val n) := hn.1
  letI : Fintype (Parts G U.val n) := Fintype.ofFinite _
  let rays (P : Parts G U.val n) : Beam G := ⟨P.val.val, n, by
    rw [RayAt.set_eq G P.val]; exact ray_atCut G hG _ n⟩
  let images (P : Parts G U.val n) := imageBeam G hG h (rays P)
  obtain ⟨a, b, c, d, hab, hcd⟩ := fullAut_has_two_windows G h
  have him (P : Parts G U.val n) : AtCut G (images P).val (n + (d : ℤ)) := by
    change AtCut G (h.val '' P.val.val) _
    rw [RayAt.set_eq G P.val]
    exact image_ray_atCut G hG h hab hcd _ n
  have hd (P Q : Parts G U.val n) (hpq : P ≠ Q) : Disjoint (images P).val (images Q).val := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have he : x = z := h.val.injective (hxy.trans hzy.symm)
    exact Set.disjoint_left.mp (parts_disjoint G P Q hpq) hx (he.symm ▸ hz)
  have he : imageBeam G hG h U =
      (⟨⋃ P, (images P).val, n + (d : ℤ), atCut_iUnion G _ _ him⟩ : Beam G) := by
    apply Subtype.ext
    change h.val '' U.val = ⋃ P : Parts G U.val n, h.val '' P.val.val
    calc
      h.val '' U.val = h.val '' (⋃ P : Parts G U.val n, P.val.val) :=
        congrArg (fun S : Set (History G) => h.val '' S) (parts_union G hn)
      _ = _ := Set.image_iUnion
  rw [he]
  exact beamCoordinate_disjointBeams G hG images _ him hd

/-- Apply the homeomorphism to each beam while keeping its original tag. -/
def imageObject (h : FullAut G) (A : Object G) : Object G :=
  ⟨A.Tag, A.finiteTag, fun i => imageBeam G hG h (A.beam i)⟩

private theorem imageObject_plus (h : FullAut G) (A B : Object G) :
    imageObject G hG h (plus G A B) = plus G (imageObject G hG h A) (imageObject G hG h B) := by
  change Object.mk (A.Tag ⊕ B.Tag) _ _ = Object.mk (A.Tag ⊕ B.Tag) _ _
  congr 1
  funext i
  cases i <;> rfl

theorem imageObject_value_partition (h : FullAut G) (A : Object G) (n : ℤ)
    (hn : Normalized G A n) :
    letI : Finite (Pieces G A n) := piecesFinite G hn
    letI : Fintype (Pieces G A n) := Fintype.ofFinite _
    objectValue G (imageObject G hG h A) =
      ∑ P : Pieces G A n,
        beamCoordinate G (imageBeam G hG h
          (⟨P.2.val.val, n, by
            rw [RayAt.set_eq G P.2.val]; exact ray_atCut G hG _ n⟩ : Beam G)) := by
  letI (i : A.Tag) : Finite (Parts G (A.beam i).val n) := (hn i).1
  letI (i : A.Tag) : Fintype (Parts G (A.beam i).val n) := Fintype.ofFinite _
  letI : Finite (Pieces G A n) := piecesFinite G hn
  letI piecesFintype : Fintype (Pieces G A n) := Fintype.ofFinite _
  let partValue (i : A.Tag) (P : Parts G (A.beam i).val n) : RowLimit G :=
    beamCoordinate G (imageBeam G hG h
      (⟨P.val.val, n, by
        rw [RayAt.set_eq G P.val]; exact ray_atCut G hG _ n⟩ : Beam G))
  calc
    objectValue G (imageObject G hG h A) =
        ∑ i : (imageObject G hG h A).Tag,
          beamCoordinate G ((imageObject G hG h A).beam i) := rfl
    _ = ∑ i : A.Tag, ∑ P : Parts G (A.beam i).val n, partValue i P := by
      apply Finset.sum_congr rfl
      intro i _
      exact image_coordinate_partition G hG h (A.beam i) n (hn i)
    _ = ∑ P : Pieces G A n, partValue P.1 P.2 := by
      rw [show piecesFintype =
        @Sigma.instFintype A.Tag (fun i => Parts G (A.beam i).val n)
          (fun i => inferInstance) inferInstance from Subsingleton.elim _ _]
      exact (Fintype.sum_sigma' partValue).symm

/-- FULL-domain quotient compatibility, without a supplied window, beam-image
promise, algebraic action, or colimit isomorphism premise. -/
theorem imageObject_equivalent (h : FullAut G) {A B : Object G} (he : Equivalent G A B) :
    Equivalent G (imageObject G hG h A) (imageObject G hG h B) := by
  obtain ⟨n, ⟨m⟩⟩ := he
  apply (equivalent_iff_value_eq G hG _ _).mpr
  rw [imageObject_value_partition G hG h A n m.left,
    imageObject_value_partition G hG h B n m.right]
  letI : Finite (Pieces G A n) := piecesFinite G m.left
  letI : Finite (Pieces G B n) := piecesFinite G m.right
  letI : Fintype (Pieces G A n) := Fintype.ofFinite _
  letI : Fintype (Pieces G B n) := Fintype.ofFinite _
  apply Fintype.sum_equiv m.pieces
  intro P
  have heq := parallel_image_coordinate G hG h
    (RayAt.representative G P.2.val) (RayAt.representative G (m.pieces P).2.val)
    n (m.endpoints P).symm
  simpa only [← RayAt.set_eq] using heq

def monoidImage (h : FullAut G) : BeamMonoid G hG →+ BeamMonoid G hG where
  toFun := Quotient.map (imageObject G hG h) (fun _ _ he => imageObject_equivalent G hG h he)
  map_zero' := by
    change objectClass G hG (imageObject G hG h (empty G)) = objectClass G hG (empty G)
    congr 1
    change Object.mk PEmpty _ (fun i => imageBeam G hG h (PEmpty.elim i)) =
      Object.mk PEmpty _ PEmpty.elim
    congr 1
    funext i
    exact PEmpty.elim i
  map_add' x y := by
    refine Quotient.inductionOn₂ x y (fun A B => ?_)
    change objectClass G hG (imageObject G hG h (plus G A B)) =
      objectClass G hG (plus G (imageObject G hG h A) (imageObject G hG h B))
    rw [imageObject_plus]

@[simp] theorem monoidImage_class (h : FullAut G) (A : Object G) :
    monoidImage G hG h (objectClass G hG A) = objectClass G hG (imageObject G hG h A) := rfl

private theorem imageObject_one (A : Object G) : imageObject G hG 1 A = A := by
  cases A with
  | mk I hI U =>
    change Object.mk I hI (fun i => imageBeam G hG 1 (U i)) = Object.mk I hI U
    congr 1
    funext i
    exact imageBeam_one G hG (U i)

private theorem imageObject_mul (g h : FullAut G) (A : Object G) :
    imageObject G hG (g * h) A = imageObject G hG g (imageObject G hG h A) := by
  cases A with
  | mk I hI U =>
    change Object.mk I hI _ = Object.mk I hI _
    congr 1
    funext i
    exact imageBeam_mul G hG g h (U i)

theorem monoidImage_one : monoidImage G hG 1 = AddMonoidHom.id _ := by
  ext x
  refine Quotient.inductionOn x (fun A => ?_)
  change objectClass G hG (imageObject G hG 1 A) = objectClass G hG A
  rw [imageObject_one]

theorem monoidImage_mul (g h : FullAut G) :
    monoidImage G hG (g * h) = (monoidImage G hG g).comp (monoidImage G hG h) := by
  ext x
  refine Quotient.inductionOn x (fun A => ?_)
  change objectClass G hG (imageObject G hG (g * h) A) =
    objectClass G hG (imageObject G hG g (imageObject G hG h A))
  rw [imageObject_mul]

def groupImage (h : FullAut G) : BeamGroup G hG →+ BeamGroup G hG :=
  (Algebra.GrothendieckGroup.lift
    ((intoGroup G hG).comp (monoidImage G hG h)).toMultiplicativeLeft).toAdditive

@[simp] theorem groupImage_into (h : FullAut G) (x : BeamMonoid G hG) :
    groupImage G hG h (intoGroup G hG x) = intoGroup G hG (monoidImage G hG h x) := by
  have he := (Algebra.GrothendieckGroup.lift
    (M := Multiplicative (BeamMonoid G hG))
    (G := Algebra.GrothendieckGroup (Multiplicative (BeamMonoid G hG)))).left_inv
      ((intoGroup G hG).comp (monoidImage G hG h)).toMultiplicativeLeft
  exact DFunLike.congr_fun he (Multiplicative.ofAdd x)

/-- Library universal property gives equality after checking original beam generators. -/
private theorem groupHom_ext {f g : BeamGroup G hG →+ BeamGroup G hG}
    (he : ∀ x, f (intoGroup G hG x) = g (intoGroup G hG x)) : f = g := by
  apply AddMonoidHom.toMultiplicative.injective
  apply (Algebra.GrothendieckGroup.lift
    (M := Multiplicative (BeamMonoid G hG))
    (G := Algebra.GrothendieckGroup (Multiplicative (BeamMonoid G hG)))).symm.injective
  ext x
  exact he (Multiplicative.toAdd x)

theorem groupImage_one : groupImage G hG 1 = AddMonoidHom.id _ := by
  apply groupHom_ext G hG
  intro x
  rw [groupImage_into, monoidImage_one]
  rfl

theorem groupImage_mul (g h : FullAut G) :
    groupImage G hG (g * h) = (groupImage G hG g).comp (groupImage G hG h) := by
  apply groupHom_ext G hG
  intro x
  rw [AddMonoidHom.comp_apply, groupImage_into, groupImage_into, groupImage_into,
    monoidImage_mul]
  rfl

/-- Invertibility comes from the ACTUAL inverse homeomorphism. -/
def groupImageEquiv (h : FullAut G) : BeamGroup G hG ≃+ BeamGroup G hG where
  toFun := groupImage G hG h
  invFun := groupImage G hG h⁻¹
  map_add' := (groupImage G hG h).map_add
  left_inv x := by
    have he := groupImage_mul G hG h⁻¹ h
    rw [inv_mul_cancel, groupImage_one] at he
    exact (DFunLike.congr_fun he x).symm
  right_inv x := by
    have he := groupImage_mul G hG h h⁻¹
    rw [mul_inv_cancel, groupImage_one] at he
    exact (DFunLike.congr_fun he x).symm

/-- Full covariant integral representation on the actual geometric beam group. -/
def fullBeamRepresentation : FullAut G →* (BeamGroup G hG ≃ₗ[ℤ] BeamGroup G hG) where
  toFun h := (groupImageEquiv G hG h).toIntLinearEquiv
  map_one' := by
    ext x
    exact DFunLike.congr_fun (groupImage_one G hG) x
  map_mul' g h := by
    ext x
    exact DFunLike.congr_fun (groupImage_mul G hG g h) x

@[simp] theorem fullBeamRepresentation_object (h : FullAut G) (A : Object G) :
    fullBeamRepresentation G hG h (objectGroup G hG A) =
      objectGroup G hG (imageObject G hG h A) := groupImage_into G hG h _

end D5.S3.ConceptDynamics.Coding.StandardBeamPushforward
