/- GID: D5/S3/Observer/AgencyHolonomy/GoldenScalarDihedralBlindness
   generality: I
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/GoldenScalarDihedralBlindness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden-unit scalar completion forgets ordered prime-word dihedral holonomy. -/

import D5.S3.Analytic.Dilation.GoldenUnitZetaReflection
import D5.S3.Observer.AgencyHolonomy.GoldenCharacterQuotient
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/- Library-search audit trail (2026-09-02):
   * The exact D5 owner `golden_unit_zeta_reflection` supplies the concrete
     quadratic-integer lattice zeta together with reflection and one golden
     regulator period. It is imported and applied on that unchanged carrier.
   * The exact D5 owner `GoldenCharacterQuotient` supplies unramified primes,
     the golden character, and concrete split/inert witnesses. Body-shape
     searches found no D5 infinite-dihedral rapidity action or group-valued
     prime-step word product.
   * Pinned Mathlib supplies `DihedralGroup 0`, its normal forms and group laws,
     plus `Function.Periodic.int_mul` for all integral regulator shifts. No
     library theorem combines these with the scalar-world recovery obstruction.
   * Searches of the installed non-Mathlib Lean packages found no theorem about
     golden prime holonomy or completed-scalar recovery. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencyHolonomy.GoldenScalarDihedralBlindness

open D5.S3.Observer.AgencyHolonomy.GoldenCharacterQuotient
open scoped goldenRatio

noncomputable section

/-- The source's infinite-dihedral action on rapidity. The rotation `r (-1)`
is the positive golden regulator boost, while `sr 0` is reflection. -/
@[instance_reducible] def goldenDihedralAction :
    MulAction (DihedralGroup 0) Real where
  smul g eta :=
    match g with
    | DihedralGroup.r k =>
        eta - ((ZMod.cast k : Int) : Real) *
          (2 * Real.log Real.goldenRatio)
    | DihedralGroup.sr k =>
        -eta + ((ZMod.cast k : Int) : Real) *
          (2 * Real.log Real.goldenRatio)
  one_smul eta := by
    change eta - ((0 : Int) : Real) *
      (2 * Real.log Real.goldenRatio) = eta
    ring
  mul_smul g h eta := by
    rcases g with k | k <;> rcases h with l | l
    · change eta - ((ZMod.cast (k + l) : Int) : Real) *
          (2 * Real.log Real.goldenRatio) =
        (eta - ((ZMod.cast l : Int) : Real) *
          (2 * Real.log Real.goldenRatio)) -
        ((ZMod.cast k : Int) : Real) *
          (2 * Real.log Real.goldenRatio)
      rw [ZMod.cast_add']
      push_cast
      ring
    · change -eta + ((ZMod.cast (l - k) : Int) : Real) *
          (2 * Real.log Real.goldenRatio) =
        (-eta + ((ZMod.cast l : Int) : Real) *
          (2 * Real.log Real.goldenRatio)) -
        ((ZMod.cast k : Int) : Real) *
          (2 * Real.log Real.goldenRatio)
      rw [ZMod.cast_sub']
      push_cast
      ring
    · change -eta + ((ZMod.cast (k + l) : Int) : Real) *
          (2 * Real.log Real.goldenRatio) =
        -(eta - ((ZMod.cast l : Int) : Real) *
          (2 * Real.log Real.goldenRatio)) +
        ((ZMod.cast k : Int) : Real) *
          (2 * Real.log Real.goldenRatio)
      rw [ZMod.cast_add']
      push_cast
      ring
    · change eta - ((ZMod.cast (l - k) : Int) : Real) *
          (2 * Real.log Real.goldenRatio) =
        -(-eta + ((ZMod.cast l : Int) : Real) *
          (2 * Real.log Real.goldenRatio)) +
        ((ZMod.cast k : Int) : Real) *
          (2 * Real.log Real.goldenRatio)
      rw [ZMod.cast_sub']
      push_cast
      ring

local instance : MulAction (DihedralGroup 0) Real := goldenDihedralAction

/-- One unramified prime contributes the proper boost followed by reflection
exactly when its golden character is negative. -/
def goldenPrimeStep (p : UnramifiedPrime) : DihedralGroup 0 :=
  (DihedralGroup.r (-1 : ZMod 0)) *
    (DihedralGroup.sr (0 : ZMod 0)) ^
      (if goldenCharacter p = 1 then 0 else 1)

/-- Path-ordered holonomy is the product of the prime steps in word order. -/
def goldenPrimeHolonomy (word : List UnramifiedPrime) : DihedralGroup 0 :=
  (word.map goldenPrimeStep).prod

/-- The completed golden-unit scalar is invariant under every infinite-dihedral
rapidity transform. Consequently no decoder of the complete scalar world can
recover every ordered prime-word holonomy, and every pair of distinct
holonomies has the same completed scalar world. -/
theorem golden_scalar_dihedrally_blind :
    let sigmaPlus : Int × Int -> Real := fun alpha =>
      (alpha.1 : Real) + (alpha.2 : Real) * Real.goldenRatio
    let sigmaMinus : Int × Int -> Real := fun alpha =>
      (alpha.1 : Real) + (alpha.2 : Real) * Real.goldenConj
    let anisotropicForm : Real -> Int × Int -> Real := fun eta alpha =>
      Real.exp eta * sigmaPlus alpha ^ 2 +
        Real.exp (-eta) * sigmaMinus alpha ^ 2
    let goldenUnitZeta : Complex -> Real -> Complex := fun s eta =>
      ∑' alpha : {alpha : Int × Int // alpha ≠ 0},
        (anisotropicForm eta alpha : Complex) ^ (-s)
    let completedWorld : Real -> List UnramifiedPrime -> Complex -> Complex :=
      fun eta word s =>
        goldenUnitZeta s (goldenPrimeHolonomy word • eta)
    (∀ (s : Complex) (eta : Real) (g : DihedralGroup 0),
        goldenUnitZeta s (g • eta) = goldenUnitZeta s eta) ∧
      (∀ eta : Real,
        ¬ ∃ recover : (Complex -> Complex) -> DihedralGroup 0,
          ∀ word : List UnramifiedPrime,
            recover (completedWorld eta word) = goldenPrimeHolonomy word) ∧
      (∃ first second : List UnramifiedPrime,
          goldenPrimeHolonomy first ≠ goldenPrimeHolonomy second) ∧
      (∀ (eta : Real) (first second : List UnramifiedPrime),
        completedWorld eta first = completedWorld eta second) := by
  dsimp only
  let sigmaPlus : Int × Int -> Real := fun alpha =>
    (alpha.1 : Real) + (alpha.2 : Real) * Real.goldenRatio
  let sigmaMinus : Int × Int -> Real := fun alpha =>
    (alpha.1 : Real) + (alpha.2 : Real) * Real.goldenConj
  let anisotropicForm : Real -> Int × Int -> Real := fun eta alpha =>
    Real.exp eta * sigmaPlus alpha ^ 2 +
      Real.exp (-eta) * sigmaMinus alpha ^ 2
  let goldenUnitZeta : Complex -> Real -> Complex := fun s eta =>
    ∑' alpha : {alpha : Int × Int // alpha ≠ 0},
      (anisotropicForm eta alpha : Complex) ^ (-s)
  let completedWorld : Real -> List UnramifiedPrime -> Complex -> Complex :=
    fun eta word s => goldenUnitZeta s (goldenPrimeHolonomy word • eta)
  change
    (∀ (s : Complex) (eta : Real) (g : DihedralGroup 0),
        goldenUnitZeta s (g • eta) = goldenUnitZeta s eta) ∧
      (∀ eta : Real,
        ¬ ∃ recover : (Complex -> Complex) -> DihedralGroup 0,
          ∀ word : List UnramifiedPrime,
            recover (completedWorld eta word) = goldenPrimeHolonomy word) ∧
      (∃ first second : List UnramifiedPrime,
          goldenPrimeHolonomy first ≠ goldenPrimeHolonomy second) ∧
      (∀ (eta : Real) (first second : List UnramifiedPrime),
        completedWorld eta first = completedWorld eta second)
  have sourceSymmetries :=
    D5.S3.Analytic.Dilation.GoldenUnitZetaReflection.golden_unit_zeta_reflection
  dsimp only at sourceSymmetries
  have reflection : ∀ (s : Complex) (eta : Real),
      goldenUnitZeta s eta = goldenUnitZeta s (-eta) :=
    sourceSymmetries.1
  have periodic : ∀ s : Complex,
      Function.Periodic (goldenUnitZeta s)
        (2 * Real.log Real.goldenRatio) :=
    sourceSymmetries.2
  have invariant : ∀ (s : Complex) (eta : Real) (g : DihedralGroup 0),
      goldenUnitZeta s (g • eta) = goldenUnitZeta s eta := by
    intro s eta g
    rcases g with k | k
    · exact (periodic s).sub_int_mul_eq (ZMod.cast k : Int)
    · calc
        goldenUnitZeta s
            (-eta + ((ZMod.cast k : Int) : Real) *
              (2 * Real.log Real.goldenRatio)) =
            goldenUnitZeta s (-eta) :=
          (periodic s).int_mul (ZMod.cast k : Int) (-eta)
        _ = goldenUnitZeta s eta := (reflection s eta).symm
  have characterValues := goldenCharacter_witness_values
  have distinctHolonomies :
      goldenPrimeHolonomy [eleven, two] ≠
        goldenPrimeHolonomy [two, eleven] := by
    norm_num [goldenPrimeHolonomy, goldenPrimeStep,
      characterValues.1, characterValues.2.2.1]
  have sameWorld : ∀ (eta : Real) (first second : List UnramifiedPrime),
      completedWorld eta first = completedWorld eta second := by
    intro eta first second
    funext s
    exact (invariant s eta (goldenPrimeHolonomy first)).trans
      (invariant s eta (goldenPrimeHolonomy second)).symm
  refine ⟨invariant, ?_, ⟨[eleven, two], [two, eleven], distinctHolonomies⟩,
    sameWorld⟩
  intro eta
  rintro ⟨recover, recovers⟩
  apply distinctHolonomies
  calc
    goldenPrimeHolonomy [eleven, two] =
        recover (completedWorld eta [eleven, two]) :=
      (recovers [eleven, two]).symm
    _ = recover (completedWorld eta [two, eleven]) :=
      congrArg recover
        (sameWorld eta [eleven, two] [two, eleven])
    _ = goldenPrimeHolonomy [two, eleven] := recovers [two, eleven]

#print axioms goldenDihedralAction
#print axioms goldenPrimeStep
#print axioms goldenPrimeHolonomy
#print axioms golden_scalar_dihedrally_blind

end

end D5.S3.Observer.AgencyHolonomy.GoldenScalarDihedralBlindness
