/- GID: D5/S3/Zeros/GRH/Lib/Cohomology/Etale/TestCohomology
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Cohomology/Etale/TestCohomology
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Cohomology.Etale.TestCohomology. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Cohomology/Etale/TestCohomology.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Cohomology.Etale.Defs
import D5.S3.Zeros.GRH.Lib.General.Algebra.AdicRingHomExt
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: Test rings, functors of points, locally constant coefficients, cohomology as Ext. -/

open PrimeSpectrum AlgebraicGeometry CategoryTheory

variable (A) [CommRing A]

/-- A is an absolutely integrally closed local domain: a local domain in which every monic
polynomial of positive degree has a root. -/
class IsAICLocal extends IsDomain A, IsLocalRing A, IsAIC A

/-- A is a test ring: reduced, absolutely integrally closed, and any a, b admit an idempotent e
with a ∣ eb and b ∣ (1 − e)a. -/
structure IsTest extends IsAIC A where
  (isComparableRing : IsComparableRing (· : A → A)) isReduced : IsReduced A

/-- The category of test rings (`IsTest`), as a full subcategory of commutative
rings. -/
abbrev TestRing := @ObjectProperty.FullSubcategory CommRingCat.{0} _ (IsTest ·)

/-- The inclusion functor from the category of test rings into the category of commutative
rings. -/
abbrev testIncl : TestRing ⥤ CommRingCat := ObjectProperty.ι _

/-- The category of covariant functors from (small) commutative rings to sets of the next
universe. -/
abbrev PointFunctor := CommRingCat.{0} ⥤ Type 1

variable (Λ : Ab.{0}) {X Y : PointFunctor} (u : X ⟶ Y) {R} (s : X ⟶ reprBy R) (I : Set R) {B} (φ :
  R ⟶ B)

/-- For an abelian group Λ, the functor on commutative rings sending A to the group of locally
constant functions Spec A → Λ. -/
def locConstSpec : CommRingCat.{0} ⥤ Ab := .mk _
    (AddCommGrpCat.ofHom <| LocallyConstant.comapAddMonoidHom (Z := Λ) ⟨_, continuous_comap ·.hom⟩)

/-- For an abelian group Λ, the coefficient functor on test rings sending A to the group of
locally constant functions Spec A → Λ. -/
def locConstCoeff := liftCoeff (testIncl ⋙ locConstSpec Λ)

/-- For a map u: X → Y of set-valued functors on rings, its restriction to a map of functors on
test rings. -/
abbrev mapOnTests := testIncl.whiskerLeft u

/-- For u: X → Y and each degree i, the pull-back homomorphism H^i(Y, Λ) → H^i(X, Λ) on
cohomology computed on test rings. -/
noncomputable abbrev HV.map := H.map (locConstCoeff Λ) (freeAb.map (mapOnTests u))

/-- The property of a map u: X → Y of functors on rings that pull-back H^i(Y, Λ) → H^i(X, Λ) is
bijective for all i. -/
abbrev Components := IsCohomEquiv (locConstCoeff Λ) (freeAb.map (mapOnTests u))

/-- The image of u : X → Y, restricted to test rings, is dense in Y (`IsCohomDense`) for the
coefficient functor of locally constant functions Spec A → Λ. -/
abbrev HasCohomDenseImage := IsCohomDense (locConstCoeff Λ) (.range (mapOnTests u))

/-- For a morphism s: X → Spec R, the map from the functor of points of X to h_R sending x ∈
X(A) to the ring map R → A of s∘x. -/
noncomputable def pointsToBase {X R} (s : X ⟶ Spec R) : Scheme.Spec.rightOp ⋙ uliftYoneda X ⟶ reprBy
  R := ⟨fun _ ↦ ↾(⟨Spec.preimage <| ·.1 ≫ s⟩), by delta reprBy reprFunctor; aesop⟩

/-- For s: X → h_R and a point x ∈ X(B), the ring homomorphism R → B that is the image of x
under s. -/
def baseRingMap (x : X B) : R ⟶ B := (s B x).1

@[simp] lemma baseRingMap_map {B'} f x : baseRingMap s (@X.map B B' f x) =
  baseRingMap s x ≫ f := by aesop (add simp baseRingMap)

/-- For s: X → h_R and a subset I of R, the subfunctor of points x ∈ X(B) whose structure map R
→ B sends I to 0. -/
def zeroPoints := Subfunctor.mk (fun _ ↦ {x | ∀ a ∈ I, baseRingMap s x a = 0}) (by aesop)

/-- For s: X → h_R and a subset I of R, the subfunctor of points x ∈ X(B) whose structure map R
→ B sends every element of I to a unit. -/
def unitPoints :=
  Subfunctor.mk (fun _ ↦ {x | ∀ a ∈ I, IsUnit (baseRingMap s x a)}) (by simp_all [IsUnit.map])

/-- For s: X → h_R and a ring map φ: R → B, the base change X_B = X ×_{h_R} h_B. -/
abbrev baseChangeOf := fibreProd s (reprMap φ)
