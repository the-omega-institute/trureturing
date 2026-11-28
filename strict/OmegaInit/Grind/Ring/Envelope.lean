/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Kim Morrison
-/
module
prelude
public import OmegaInit.Core

port_proof Quot.lift.congr_simp
port_definition Lean.Grind.Ring.OfSemiring.r.match_1 with_native_code
port_definition Lean.Grind.Ring.OfSemiring.sub.match_1 with_native_code
port_definition Lean.Grind.Ring.OfSemiring.npow.match_1 with_native_code

/- The public semiring relation and carrier require Lean.Grind.Semiring.
Q.exact and toQ_inj have constructive proofs under the additional hypotheses
in OmegaChecks.InitBoundaries.RingEnvelopeExact. The canonical quotient lifts
for add, sub, mul and neg require identifying the classes of (1, 1) and (0, 0).
OmegaChecks.InitBoundaries.EnvelopeCancellation checks these obligations.
The public types of instIsPreorderQ and instOrderedAddQ fix the unrestricted quotient
comparison. Its representative coherence is equivalent to propext at universe zero
by propextFromRingLift and ringLiftFromPropext in OmegaChecks.InitBoundaries.EnvelopeOrder. -/
