/- GID: D5/S3/ConceptDynamics/Coding/StandardBeamIdentification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/StandardBeamIdentification
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Both inverse identities between geometric beam completion and the integer row colimit. -/
import D5.S3.ConceptDynamics.Coding.StandardTaggedBeams

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.StandardBeamIdentification
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.StandardBeamGeometry
open D5.S3.ConceptDynamics.Coding.StandardBeamEndpointRows
open D5.S3.ConceptDynamics.Coding.StandardBeamCoordinates
open D5.S3.ConceptDynamics.Coding.StandardBeamColimitCuts
open D5.S3.ConceptDynamics.Coding.StandardTaggedBeams
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy (stationaryTransition)
open scoped BigOperators Matrix

universe u v
variable {V : Type u} {E : Type v} (G : DirectedMultigraph V E)
variable [Fintype V] [Fintype E] [DecidableEq V] (hG : Essential G)

private theorem quotientValue_injective : Function.Injective (quotientValue G hG) := by
  intro x y he
  revert he
  refine Quotient.inductionOn₂ x y (fun A B => ?_)
  intro he
  exact Quotient.sound ((equivalent_iff_value_eq G hG A B).mpr he)

/-- F's injectivity is a consequence of the PROVED geometric eventual-row
criterion and the library's localization universal property. -/
theorem F_injective : Function.Injective (F G hG) := by
  let M := Multiplicative (BeamMonoid G hG)
  let P := Multiplicative (RowLimit G)
  let f := Localization.monoidOf (⊤ : Submonoid M)
  let g : M →* P := (quotientValue G hG).toMultiplicative
  have hg : ∀ y : (⊤ : Submonoid M), IsUnit (g y) := fun _ => Group.isUnit _
  have hinj : Function.Injective g := quotientValue_injective G hG
  have hf : Function.Injective (f.lift hg) := (f.lift_injective_iff hg).mpr (by
    intro x y
    constructor
    · exact f.eq_of_eq hg
    · intro he
      rw [hinj he])
  exact hf

/-- Chosen full actual history ending at u at cut N. Auxiliary choices
are erased by same-cut past splice and the geometric matching criterion. -/
def chosenRay (u : V) (N : ℕ) : Beam G :=
  ⟨ray G (vertexHistory G hG u (N : ℤ)) (N : ℤ),
    (N : ℤ), ray_atCut G hG _ _⟩

def chosenClass (u : V) (N : ℕ) : BeamGroup G hG :=
  objectGroup G hG (singleton G (chosenRay G hG u N))

@[simp] theorem F_chosenClass (u : V) (N : ℕ) :
    F G hG (chosenClass G hG u N) = stage (rowTransition G) N (Pi.single u 1) := by
  rw [chosenClass, F_objectGroup]
  unfold objectValue
  letI : Fintype (StandardTaggedBeams.singleton G (chosenRay G hG u N)).Tag :=
    Fintype.ofFinite _
  letI : Subsingleton (StandardTaggedBeams.singleton G (chosenRay G hG u N)).Tag :=
    inferInstanceAs (Subsingleton PUnit)
  rw [Fintype.sum_subsingleton
    (fun i : (StandardTaggedBeams.singleton G (chosenRay G hG u N)).Tag =>
      beamCoordinate G ((StandardTaggedBeams.singleton G (chosenRay G hG u N)).beam i))
    (PUnit.unit : (StandardTaggedBeams.singleton G (chosenRay G hG u N)).Tag)]
  change beamCoordinate G (chosenRay G hG u N) = _
  rw [beamCoordinate_at G hG _ (N : ℤ) (ray_atCut G hG _ _)]
  change coordinateAt G (ray G (vertexHistory G hG u (N : ℤ)) (N : ℤ)) (N : ℤ)
    (ray_atCut G hG _ _) = _
  rw [coordinateAt_ray G hG, vertexHistory_endpoint G hG, intStage_nat]

/-- The inverse's stage map is the FULL signed integer basis sum. -/
def JStage (N : ℕ) : (V → ℤ) →ₗ[ℤ] BeamGroup G hG where
  toFun z := ∑ u : V, z u • chosenClass G hG u N
  map_add' z w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c z := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

private theorem row_basis_sum (z : V → ℤ) : (∑ u : V, z u • Pi.single u (1 : ℤ)) = z := by
  classical
  funext t
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, eq_comm]

/-- FJ on each native stage is actual ray endpoint/refinement counting. -/
theorem F_JStage (N : ℕ) (z : V → ℤ) :
    F G hG (JStage G hG N z) = stage (rowTransition G) N z := by
  change F G hG (∑ u : V, z u • chosenClass G hG u N) = _
  rw [map_sum]
  have he : (∑ u : V, F G hG (z u • chosenClass G hG u N)) =
      ∑ u : V, stage (rowTransition G) N (z u • Pi.single u 1) := by
    apply Finset.sum_congr rfl
    intro u _
    rw [map_zsmul, F_chosenClass]
    exact ((stage (rowTransition G) N).map_smul (z u) (Pi.single u 1)).symm
  rw [he]
  rw [← map_sum, row_basis_sum]

/-- Stage compatibility follows from ACTUAL geometric eventual matching.
F_injective invokes matchingOfRows, whose components are past splices;
F_JStage invokes chosen full rays, coordinateAt_ray and ray refinement.
No promised isomorphism or unexplained stage compatibility is assumed. -/
theorem JStage_compatible (i j : ℕ) (hij : i ≤ j) (z : V → ℤ) :
    JStage G hG j (stationaryTransition (rowTransition G) i j hij z) = JStage G hG i z := by
  apply F_injective G hG
  rw [F_JStage, F_JStage]
  exact Module.DirectLimit.of_f (R := ℤ) (ι := ℕ) (G := fun _ : ℕ => V → ℤ)
    (f := stationaryTransition (rowTransition G))
    (i := i) (j := j) (hij := hij) (x := z)

/-- The original Module.DirectLimit universal property constructs J. -/
def J : RowLimit G →ₗ[ℤ] BeamGroup G hG :=
  Module.DirectLimit.lift ℤ ℕ (fun _ : ℕ => V → ℤ) (stationaryTransition (rowTransition G))
    (JStage G hG) (JStage_compatible G hG)

@[simp] theorem J_stage (N : ℕ) (z : V → ℤ) :
    J G hG (stage (rowTransition G) N z) = JStage G hG N z :=
  by simp only [J, stage, Module.DirectLimit.lift_of]

/-- FIRST inverse identity on the whole native integer row colimit. -/
theorem FJ : (F G hG).toIntLinearMap.comp (J G hG) = LinearMap.id := by
  apply Module.DirectLimit.hom_ext
  intro N
  apply LinearMap.ext
  intro z
  change F G hG (J G hG (stage (rowTransition G) N z)) = stage (rowTransition G) N z
  rw [J_stage, F_JStage]

/-- SECOND inverse identity on the actual Grothendieck group. Injectivity
was proved from geometric common refinement; formal differences are handled
by Mathlib localization, without inventing another group foundation. -/
theorem JF : (J G hG).comp (F G hG).toIntLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply F_injective G hG
  exact LinearMap.congr_fun (FJ G hG) (F G hG x)

def beamRowEquiv : BeamGroup G hG ≃ₗ[ℤ] RowLimit G where
  toFun := F G hG
  invFun := J G hG
  map_add' := (F G hG).map_add
  map_smul' := (F G hG).toIntLinearMap.map_smul
  left_inv x := LinearMap.congr_fun (JF G hG) x
  right_inv z := LinearMap.congr_fun (FJ G hG) z

end D5.S3.ConceptDynamics.Coding.StandardBeamIdentification
