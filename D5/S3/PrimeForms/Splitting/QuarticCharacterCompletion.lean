/- GID: D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Splitting/QuarticCharacterCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Quartic mod-five roots make the mod-sixty profile injective; edges audited. -/
/- Library-search audit trail (2026-08-25):
   * Exact repository searches for quartic characters, `psiFive`, `mu4`, and the target
     statement found no equivalent declaration; the digestion atom has no coverage GID.
   * Nearby hits are `PowerCharacter`, the exact two-element three-ring fibers, the theorem
     that all binary characters are redundant, and the non-homomorphic orientation bit.
   * Pinned Mathlib provides `ZMod.unitsMap`, `ZMod.rootsOfUnityAddChar`,
     `restrictRootsOfUnity`, and the injectivity of the standard additive character.
   * Searches by the generalized shapes `Units (ZMod n)`, cyclic unit groups, primitive
     roots, and homomorphisms into `rootsOfUnity` found no ready-made mod-sixty completion.
   * The construction below composes those canonical maps and invokes the existing
     orientation theorem, so it neither rebuilds CRT nor wraps an already-proved result.
-/

import D5.S3.Factorization.Galois.GeneralPowerCharacterLayer
import D5.S3.PrimeForms.Splitting.ModFiveOrientationBit
import D5.S3.PrimeForms.Splitting.QuadraticCharacterProfileRedundancy
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.Splitting.QuarticCharacterCompletion

open D5.S3.Factorization.Galois.GeneralPowerCharacterLayer
open D5.S3.PrimeForms.Splitting.ModFiveOrientationBit
open D5.S3.PrimeForms.Splitting.QuadraticCharacterProfileRedundancy
open D5.S3.PrimeForms.Splitting.ThreeRingProfileFibers

private noncomputable def binaryRootCharacter :
    Multiplicative (ZMod 2) →* complexNthRootsOfUnity 2 :=
  (restrictRootsOfUnity Circle.coeHom 2).comp
    (ZMod.rootsOfUnityAddChar 2).toMonoidHom

private noncomputable def quarticRootCharacter :
    Multiplicative (ZMod 4) →* complexNthRootsOfUnity 4 :=
  (restrictRootsOfUnity Circle.coeHom 4).comp
    (ZMod.rootsOfUnityAddChar 4).toMonoidHom

private theorem binaryRootCharacter_injective :
    Function.Injective binaryRootCharacter := by
  intro x y hxy
  apply_fun fun z : complexNthRootsOfUnity 2 => ((z : ℂˣ) : ℂ) at hxy
  change ((ZMod.toCircle x.toAdd : Circle) : ℂ) =
    ((ZMod.toCircle y.toAdd : Circle) : ℂ) at hxy
  have hcircle : ZMod.toCircle x.toAdd = ZMod.toCircle y.toAdd :=
    Subtype.ext hxy
  have hadd : x.toAdd = y.toAdd := ZMod.injective_toCircle hcircle
  exact congrArg Multiplicative.ofAdd hadd

private theorem quarticRootCharacter_injective :
    Function.Injective quarticRootCharacter := by
  intro x y hxy
  apply_fun fun z : complexNthRootsOfUnity 4 => ((z : ℂˣ) : ℂ) at hxy
  change ((ZMod.toCircle x.toAdd : Circle) : ℂ) =
    ((ZMod.toCircle y.toAdd : Circle) : ℂ) at hxy
  have hcircle : ZMod.toCircle x.toAdd = ZMod.toCircle y.toAdd :=
    Subtype.ext hxy
  have hadd : x.toAdd = y.toAdd := ZMod.injective_toCircle hcircle
  exact congrArg Multiplicative.ofAdd hadd

/- The four unit residues modulo five are powers `2^0, 2^1, 2^2, 2^3`.
The table is total on `(ZMod 5)ˣ`, and its two homomorphism laws are checked on that
finite group, making the discrete logarithm independent of integer representatives. -/
private def modFiveLog : (ZMod 5)ˣ →* Multiplicative (ZMod 4) where
  toFun u := Multiplicative.ofAdd
    (if (u : ZMod 5) = 1 then 0 else
      if (u : ZMod 5) = 2 then 1 else
        if (u : ZMod 5) = 4 then 2 else 3)
  map_one' := by decide
  map_mul' := by
    set_option maxRecDepth 100000 in
      decide

/-- The quadratic character `chi_{-4}`, using the Gaussian split/inert reading. -/
noncomputable def chiMinusFour : PowerCharacter ((ZMod 60)ˣ) 2 :=
  binaryRootCharacter.comp gaussianCharacter

/-- The quadratic character `chi_{-3}`, using the Eisenstein split/inert reading. -/
noncomputable def chiMinusThree : PowerCharacter ((ZMod 60)ˣ) 2 :=
  binaryRootCharacter.comp eisensteinCharacter

/-- The quartic character through reduction modulo five. The canonical reduction is followed
by the well-defined discrete logarithm base two and the standard character into `mu_4`. -/
noncomputable def psiFive : PowerCharacter ((ZMod 60)ˣ) 4 :=
  quarticRootCharacter.comp
    (modFiveLog.comp (ZMod.unitsMap (by norm_num : 5 ∣ 60)))

/-- The quadratic-quadratic-quartic completion `Psi_60`. -/
noncomputable def psiSixty :
    (ZMod 60)ˣ →* complexNthRootsOfUnity 2 ×
      complexNthRootsOfUnity 2 × complexNthRootsOfUnity 4 :=
  chiMinusFour.prod (chiMinusThree.prod psiFive)

/-- The lift `7` of the modulo-five generator `2` is sent by `psiFive` to `i`. -/
theorem psi_five_maps_mod_five_generator_two_to_i :
    (((psiFive (ZMod.unitOfCoprime 7 (by decide)) :
      complexNthRootsOfUnity 4) : ℂˣ) : ℂ) = Complex.I := by
  change ZMod.stdAddChar (1 : ZMod 4) = Complex.I
  calc
    ZMod.stdAddChar (1 : ZMod 4) =
        Complex.exp
          (2 * Real.pi * Complex.I * (1 : ℤ) / ((4 : ℝ) : ℂ)) := by
      convert ZMod.stdAddChar_coe (N := 4) (1 : ℤ) using 1 <;> norm_num
    _ = Complex.I := by
      convert Complex.exp_pi_div_two_mul_I using 2
      all_goals push_cast
      all_goals ring
#print axioms psi_five_maps_mod_five_generator_two_to_i

/-- The quartic completion separates all unit classes modulo sixty. Its final step reuses the
same-fiber separation conclusion of the preceding modulo-five orientation theorem. -/
theorem psi_sixty_injective : Function.Injective psiSixty := by
  intro u v huv
  have hFour : chiMinusFour u = chiMinusFour v :=
    congrArg Prod.fst huv
  have hThree : chiMinusThree u = chiMinusThree v :=
    congrArg (fun z => z.2.1) huv
  have hFive : psiFive u = psiFive v :=
    congrArg (fun z => z.2.2) huv
  have hGaussian : gaussianCharacter u = gaussianCharacter v :=
    binaryRootCharacter_injective hFour
  have hEisenstein : eisensteinCharacter u = eisensteinCharacter v :=
    binaryRootCharacter_injective hThree
  have hFiveLog :
      modFiveLog (ZMod.unitsMap (by norm_num : 5 ∣ 60) u) =
        modFiveLog (ZMod.unitsMap (by norm_num : 5 ∣ 60) v) :=
    quarticRootCharacter_injective hFive
  have hProfileOrientation :
      triRingImage u = triRingImage v ∧
        modFiveOrientation u = modFiveOrientation v := by
    clear huv hFour hThree hFive
    set_option maxRecDepth 100000 in
      decide +revert
  obtain ⟨hProfile, hOrientation⟩ := hProfileOrientation
  exact mod_five_orientation_separates_fibers_but_is_not_homomorphic.1.2
    (triRingImage u) u v rfl hProfile.symm hOrientation
#print axioms psi_sixty_injective

/-- The binary three-ring image identifies the distinct classes `1` and `49`, while the
quartic completion separates them. This witnesses the strict gain from `mu_2^3` to
`mu_2^2 x mu_4`. -/
theorem quadratic_profile_collision_but_quartic_completion_separates :
    ∃ u v : (ZMod 60)ˣ,
      u ≠ v ∧ triRingImage u = triRingImage v ∧ psiSixty u ≠ psiSixty v := by
  let u := ZMod.unitOfCoprime 1 (by decide : Nat.Coprime 1 60)
  let v := ZMod.unitOfCoprime 49 (by decide : Nat.Coprime 49 60)
  refine ⟨u, v, by decide, by decide, ?_⟩
  intro h
  exact (by decide : u ≠ v) (psi_sixty_injective h)
#print axioms quadratic_profile_collision_but_quartic_completion_separates

section DegenerateAudit

-- An empty carrier is impossible here because the fixed unit group contains its identity.
example : Nonempty ((ZMod 60)ˣ) := ⟨1⟩

-- The completion preserves the identity.
example : psiSixty 1 = 1 := map_one psiSixty

-- On a one-element source, even the constant character is injective.
example : Function.Injective (1 : Unit →* complexNthRootsOfUnity 4) := by
  intro x y _
  exact Subsingleton.elim x y

private def classOne : (ZMod 60)ˣ := ZMod.unitOfCoprime 1 (by decide)

private def classEleven : (ZMod 60)ˣ := ZMod.unitOfCoprime 11 (by decide)

private def classNineteen : (ZMod 60)ˣ := ZMod.unitOfCoprime 19 (by decide)

private def classTwentyNine : (ZMod 60)ˣ := ZMod.unitOfCoprime 29 (by decide)

-- The trivial character cannot separate this nontrivial source.
example : ¬Function.Injective (1 : PowerCharacter ((ZMod 60)ˣ) 4) := by
  intro h
  exact (by decide : classOne ≠ classEleven) (h rfl)

-- The identity homomorphism is the opposite degenerate map and is injective.
example : Function.Injective (MonoidHom.id ((ZMod 60)ˣ)) := by
  intro x y h
  exact h

-- At `n = 0`, the imported general power-character theorem still has its totalized meaning.
example :
    powerCharacterJointKernel ((ZMod 60)ˣ) 0 = ⊥ ∧
      powerSubgroup ((ZMod 60)ˣ) 0 = ⊥ := by
  rw [power_character_joint_kernel_eq_power_subgroup]
  constructor <;> ext x <;>
    simp [powerSubgroup, MonoidHom.mem_range, powMonoidHom_apply, eq_comm]

-- Four named unit classes receive distinct completed values from the identity class.
example :
    psiSixty classOne ≠ psiSixty classEleven ∧
      psiSixty classOne ≠ psiSixty classNineteen ∧
      psiSixty classOne ≠ psiSixty classTwentyNine := by
  constructor
  · intro h
    exact (by decide : classOne ≠ classEleven) (psi_sixty_injective h)
  constructor
  · intro h
    exact (by decide : classOne ≠ classNineteen) (psi_sixty_injective h)
  · intro h
    exact (by decide : classOne ≠ classTwentyNine) (psi_sixty_injective h)

end DegenerateAudit

end D5.S3.PrimeForms.Splitting.QuarticCharacterCompletion
