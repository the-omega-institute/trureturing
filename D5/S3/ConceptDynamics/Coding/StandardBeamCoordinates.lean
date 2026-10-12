/- GID: D5/S3/ConceptDynamics/Coding/StandardBeamCoordinates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/StandardBeamCoordinates
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Intrinsic integer beam coordinates independent of every integer cut. -/
import D5.S3.ConceptDynamics.Coding.StandardBeamEndpointRows
import D5.S3.ConceptDynamics.Coding.StandardBeamColimitCuts

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.StandardBeamCoordinates
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.StandardBeamGeometry
open D5.S3.ConceptDynamics.Coding.StandardBeamEndpointRows
open D5.S3.ConceptDynamics.Coding.StandardBeamColimitCuts
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy (StationaryModule)
open scoped BigOperators Matrix

universe u v
variable {V : Type u} {E : Type v} (G : DirectedMultigraph V E)
variable [Fintype V] [Fintype E] [DecidableEq V] (hG : Essential G)

def rowTransition : Module.End ℤ (V → ℤ) := (adjacency G).toLinearMapRight'
abbrev RowLimit := StationaryModule (rowTransition G)

theorem rowTransition_power (r : ℕ) (z : V → ℤ) :
    ((rowTransition G) ^ r) z = z ᵥ* adjacency G ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    change (z ᵥ* adjacency G ^ r) ᵥ* adjacency G = _
    rw [Matrix.vecMul_vecMul, ← pow_succ]

/-- The coordinate of the ACTUAL intrinsic partition at an integer cut. -/
def coordinateAt (U : Set (History G)) (n : ℤ) (hn : AtCut G U n) : RowLimit G := by
  letI : Finite (Parts G U n) := hn.1
  exact intStage (rowTransition G) n (endpointRow G U n)

/-- A true refinement of the same subset moves the row forward by B^r. -/
theorem coordinateAt_refine (U : Set (History G)) (n : ℤ) (hn : AtCut G U n) (r : ℕ) :
    coordinateAt G U n hn =
      coordinateAt G U (n + (r : ℤ)) (atCut_mono G hG hn (by omega)) := by
  letI : Finite (Parts G U n) := hn.1
  letI : Finite (Parts G U (n + (r : ℤ))) := (atCut_mono G hG hn (by omega)).1
  unfold coordinateAt
  rw [endpointRow_refine G hG hn r, ← rowTransition_power G]
  exact intStage_refine (rowTransition G) n r _

include hG in
/-- Choice-independent comparison, including negative cuts and equal sets
with unique continuation. Both coordinates refine to their common integer cut. -/
theorem coordinateAt_eq (U : Set (History G)) (n m : ℤ)
    (hn : AtCut G U n) (hm : AtCut G U m) : coordinateAt G U n hn = coordinateAt G U m hm := by
  let k := max n m
  let rn := (k - n).toNat
  let rm := (k - m).toNat
  have hen : n + (rn : ℤ) = k := by dsimp [rn, k]; omega
  have hem : m + (rm : ℤ) = k := by dsimp [rm, k]; omega
  have hn' := coordinateAt_refine G hG U n hn rn
  have hm' := coordinateAt_refine G hG U m hm rm
  simp only [hen] at hn'
  simp only [hem] at hm'
  exact hn'.trans hm'.symm

/-- Select a cut only to define the function. coordinateAt_eq removes it. -/
def beamCoordinate (U : Beam G) : RowLimit G :=
  coordinateAt G U.val (Classical.choose U.property) (Classical.choose_spec U.property)

include hG in
theorem beamCoordinate_at (U : Beam G) (n : ℤ) (hn : AtCut G U.val n) :
    beamCoordinate G U = coordinateAt G U.val n hn :=
  coordinateAt_eq G hG U.val _ n _ hn

/-- The original actual ray gives the expected integer basis coordinate. -/
theorem coordinateAt_ray (alpha : History G) (n : ℤ) :
    coordinateAt G (ray G alpha n) n (ray_atCut G hG alpha n) =
      intStage (rowTransition G) n (Pi.single (endpoint G alpha n) 1) := by
  letI : Finite (Parts G (ray G alpha n) n) := (ray_atCut G hG alpha n).1
  exact congrArg (intStage (rowTransition G) n) (endpointRow_ray G hG alpha n)

end D5.S3.ConceptDynamics.Coding.StandardBeamCoordinates
