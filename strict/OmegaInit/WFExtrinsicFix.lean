/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module
prelude
public import OmegaInit.WF

port_proof WellFounded.fix.congr_simp

/- The unrestricted types of the following operators each imply Classical.choice.
Use a unit input in each argument, an always-true recursion relation and a constant
nonempty result type. The step can recur at the same input. The operator must then
return an element of that result type. The checked reductions are choiceFromFix,
choiceFromFix₂ and choiceFromFix₃ in OmegaChecks.InitBoundaries.

  WellFounded.extrinsicFix, WellFounded.extrinsicFix₂, WellFounded.extrinsicFix₃
  WellFounded.partialExtrinsicFix, WellFounded.partialExtrinsicFix₂, WellFounded.partialExtrinsicFix₃
  WellFounded.opaqueFix₃

The following statements form the unrestricted operator in an endpoint. Its
arguments do not use the accessibility or well-foundedness proof. The pinned
endpoint checks are in OmegaChecks.InitBoundaries.ChoiceOperands.

  WellFounded.extrinsicFix_eq_apply, WellFounded.extrinsicFix_eq_fix, WellFounded.extrinsicFix_invImage
  WellFounded.extrinsicFix₂_eq_apply, WellFounded.extrinsicFix₂_eq_fix
  WellFounded.extrinsicFix₃_eq_apply, WellFounded.extrinsicFix₃_eq_fix
  WellFounded.partialExtrinsicFix_eq_apply, WellFounded.partialExtrinsicFix_eq_apply_of_acc,
  WellFounded.partialExtrinsicFix_eq_fix
  WellFounded.partialExtrinsicFix₂_eq_apply, WellFounded.partialExtrinsicFix₂_eq_apply_of_acc,
  WellFounded.partialExtrinsicFix₂_eq_fix, WellFounded.partialExtrinsicFix₂_eq_partialExtrinsicFix
  WellFounded.partialExtrinsicFix₃_eq_apply, WellFounded.partialExtrinsicFix₃_eq_apply_of_acc,
  WellFounded.partialExtrinsicFix₃_eq_fix, WellFounded.partialExtrinsicFix₃_eq_partialExtrinsicFix

The two endpoints of WellFounded.extrinsicFix.congr_simp already require an
element for the unit-input construction above. -/
