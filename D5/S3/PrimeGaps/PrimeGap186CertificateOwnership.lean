/- GID: D5/S3/PrimeGaps/PrimeGap186CertificateOwnership
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Assign every finite physical-certificate obligation to an explicit coarse source owner. -/

import D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

/-!
The upstream numerical input is finite but heterogeneous. This module separates the logical
ownership of a certificate cell from the analytic proof of its inequality. It introduces no
numerical inequality and no project axiom.
-/

namespace D5.S3.PrimeGaps.PrimeGap186CertificateOwnership

open D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

/-- The three finite classes of numerical obligations in the physical certificate. -/
inductive PhysicalObligationClass
  | outer
  | inner
  | scalar
  deriving DecidableEq, Repr

/-- A canonical finite address for every numerical obligation. -/
inductive PhysicalObligationAddress
  | outer (index : Fin 104)
  | inner (index : Fin 45)
  | scalar (index : Fin 3)
  deriving DecidableEq, Repr

instance : Fintype PhysicalObligationAddress := Fintype.ofFinite _

/-- Classification forgets only the local index. -/
def PhysicalObligationAddress.obligationClass : PhysicalObligationAddress → PhysicalObligationClass
  | .outer _ => .outer
  | .inner _ => .inner
  | .scalar _ => .scalar

/-- The physical numerical package contains exactly 152 independently addressable obligations. -/
theorem card_physicalObligationAddress :
    Fintype.card PhysicalObligationAddress = 152 := by
  native_decide

/-- Coarse owner for outer numerical cells. The exact fine schedule is intentionally a later layer.
The partition into three source groups is deterministic and exhaustive. -/
def outerOwner (j : Fin 104) : PhysicalSourceGroup :=
  if j.val < 35 then .outerH2
  else if j.val < 70 then .outerH25
  else .outerH3

/-- Coarse owner for inner numerical cells. -/
def innerOwner (j : Fin 45) : PhysicalSourceGroup :=
  if j.val < 15 then .innerH2
  else if j.val < 30 then .innerH25
  else .innerH3

/-- Scalar cap/trial obligations are global and therefore have no single source-group owner. -/
def PhysicalObligationAddress.coarseOwner : PhysicalObligationAddress → Option PhysicalSourceGroup
  | .outer j => some (outerOwner j)
  | .inner j => some (innerOwner j)
  | .scalar _ => none

/-- Every outer numerical obligation is assigned to an outer group. -/
theorem outerOwner_isOuter (j : Fin 104) : (outerOwner j).isOuter = true := by
  unfold outerOwner
  split <;> split <;> simp [PhysicalSourceGroup.isOuter]

/-- Every inner numerical obligation is assigned to an inner group. -/
theorem innerOwner_isOuter_false (j : Fin 45) : (innerOwner j).isOuter = false := by
  unfold innerOwner
  split <;> split <;> simp [PhysicalSourceGroup.isOuter]

/-- A non-scalar obligation always has a unique coarse source owner. -/
theorem nonscalar_has_coarse_owner (a : PhysicalObligationAddress)
    (h : a.obligationClass ≠ .scalar) :
    ∃! g : PhysicalSourceGroup, a.coarseOwner = some g := by
  cases a with
  | outer j =>
      refine ⟨outerOwner j, rfl, ?_⟩
      intro y hy
      simpa using Option.some.inj hy.symm
  | inner j =>
      refine ⟨innerOwner j, rfl, ?_⟩
      intro y hy
      simpa using Option.some.inj hy.symm
  | scalar j =>
      simp [PhysicalObligationAddress.obligationClass] at h

/-- Scalar obligations are exactly the owner-free cells. -/
theorem coarseOwner_eq_none_iff_scalar (a : PhysicalObligationAddress) :
    a.coarseOwner = none ↔ a.obligationClass = .scalar := by
  cases a <;> simp [PhysicalObligationAddress.coarseOwner,
    PhysicalObligationAddress.obligationClass]

/-- Every outer cell has an outer owner and every inner cell has an inner owner. -/
theorem ownership_respects_orientation (a : PhysicalObligationAddress) :
    match a with
    | .outer j => (outerOwner j).isOuter = true
    | .inner j => (innerOwner j).isOuter = false
    | .scalar _ => True := by
  cases a with
  | outer j => exact outerOwner_isOuter j
  | inner j => exact innerOwner_isOuter_false j
  | scalar j => trivial

#print axioms PhysicalObligationAddress
#print axioms card_physicalObligationAddress
#print axioms outerOwner
#print axioms innerOwner
#print axioms nonscalar_has_coarse_owner
#print axioms coarseOwner_eq_none_iff_scalar
#print axioms ownership_respects_orientation

end D5.S3.PrimeGaps.PrimeGap186CertificateOwnership
