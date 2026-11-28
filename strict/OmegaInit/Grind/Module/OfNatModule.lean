/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Grind.Module.Envelope

namespace Omega.Lean.Grind.IntModule.OfNatModule

public theorem of_eq {α} [NatModule α] {a b : α} {a' b' : Q α}
    (h₁ : Eq (toQ a) a') (h₂ : Eq (toQ b) b') (h : Eq a b) : Eq a' b' :=
  h₁.symm.trans ((congrArg toQ h).trans h₂)

/- The conclusion of of_le compares a' and b' using instLEQOfOrderedAdd.
The conclusion of of_not_le negates that same comparison. Both use the
canonical quotient lift with arbitrary order parameters. Its representative
coherence at universe zero implies propext by
OmegaChecks.InitBoundaries.EnvelopeOrder.propextFromModuleLift.
The converse and the reconstruction of the full comparison are checked by
moduleLiftFromPropext and moduleOrderFromPropext. -/

/- add_congr uses addition projected from ofNatModule on its two arbitrary
quotient arguments. smul_congr uses natural scalar multiplication projected
from the same instance. On natural-number pairs, the specified computations
and the group's cancellation law identify (1,1) with (0,0) in the quotient.
The representative model distinguishes those pairs, as checked in
OmegaChecks.InitBoundaries.RepresentativeQuotient.refuteEnvelopeCancellation. -/

end Omega.Lean.Grind.IntModule.OfNatModule
