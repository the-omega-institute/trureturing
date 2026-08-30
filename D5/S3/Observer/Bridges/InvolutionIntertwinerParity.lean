/- GID: D5/S3/Observer/Bridges/InvolutionIntertwinerParity
   generality: G
   mirror-B: D5/B/S3/Observer/Bridges/InvolutionIntertwinerParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An intertwiner between two involutive observer systems transports fixed and sign-changing sectors, while existence of an arithmetic-to-spectral intertwiner remains a separate obligation. -/

import Mathlib

/- Library-search audit trail (2026-08-30):
   * Repository searches for a typed involution intertwiner transporting even
     and odd observer sectors found no exact D5 owner.
   * Existing semiconjugacy owners concern dynamics rather than the parity
     decomposition of two involutions.
   * Pinned Mathlib supplies additive homomorphisms and elementary logic. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Bridges.InvolutionIntertwinerParity

universe u v

/-- A bridge intertwines two involutions when applying the source involution
before the bridge equals applying the target involution afterwards. -/
def IntertwinesInvolutions {X : Type u} {Y : Type v}
    (sourceInvolution : X → X) (targetInvolution : Y → Y)
    (bridge : X → Y) : Prop :=
  ∀ x, bridge (sourceInvolution x) = targetInvolution (bridge x)

/-- Intertwining transports source fixed points to target fixed points. -/
theorem fixed_sector_maps
    {X : Type u} {Y : Type v}
    {sourceInvolution : X → X} {targetInvolution : Y → Y}
    {bridge : X → Y}
    (hIntertwines : IntertwinesInvolutions sourceInvolution
      targetInvolution bridge)
    {x : X} (hFixed : sourceInvolution x = x) :
    targetInvolution (bridge x) = bridge x := by
  rw [← hIntertwines x, hFixed]

/-- An additive intertwiner transports a sign-changing source vector to a
sign-changing target vector. -/
theorem odd_sector_maps
    {X : Type u} {Y : Type v}
    [AddGroup X] [AddGroup Y]
    {sourceInvolution : X → X} {targetInvolution : Y → Y}
    {bridge : X →+ Y}
    (hIntertwines : IntertwinesInvolutions sourceInvolution
      targetInvolution bridge)
    {x : X} (hOdd : sourceInvolution x = -x) :
    targetInvolution (bridge x) = -bridge x := by
  rw [← hIntertwines x, hOdd, map_neg]

/-- If the bridge is injective and the target image is fixed, then a source
point cannot hide a nontrivial involution displacement. -/
theorem fixed_sector_reflects_of_injective
    {X : Type u} {Y : Type v}
    {sourceInvolution : X → X} {targetInvolution : Y → Y}
    {bridge : X → Y}
    (hIntertwines : IntertwinesInvolutions sourceInvolution
      targetInvolution bridge)
    (hInjective : Function.Injective bridge)
    {x : X} (hTargetFixed : targetInvolution (bridge x) = bridge x) :
    sourceInvolution x = x := by
  apply hInjective
  rw [hIntertwines x, hTargetFixed]

/-- A constant bridge can intertwine involutions while erasing all source
parity information. -/
theorem constant_intertwiner_can_erase_parity :
    IntertwinesInvolutions Bool.not id (fun _ : Bool => false) ∧
      ¬ Function.Injective (fun _ : Bool => false) := by
  constructor
  · intro x
    rfl
  · intro hInjective
    have hEq : false = true := hInjective rfl
    decide at hEq

/-- Concrete nondegenerate parity transport on integers. -/
example :
    IntertwinesInvolutions (fun z : ℤ => -z) (fun z : ℤ => -z) id := by
  intro z
  rfl

#print axioms fixed_sector_maps
#print axioms odd_sector_maps
#print axioms fixed_sector_reflects_of_injective
#print axioms constant_intertwiner_can_erase_parity

end D5.S3.Observer.Bridges.InvolutionIntertwinerParity
