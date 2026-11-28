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
by propextFromRingLift and ringLiftFromPropext in OmegaChecks.InitBoundaries.EnvelopeOrder.
With propext, ringOrderFromPropext reconstructs the full pinned LE instance on the
quotient. The bare LE type also admits the constant-false comparison. -/
/- instLTQOfOrderedAdd uses that same canonical comparison in both directions,
at the two arbitrary quotient inputs. With propext, ringStrictOrderFromPropext
reconstructs the pinned strict comparison and its public reduction. -/

/- The official types of toQ_natCast, toQ_pow, instNoNatZeroDivisorsQOfAddRightCancel
and instIsCharPQOfAddRightCancel use the semiring projection of ofSemiring. Its
specified arithmetic on Nat representatives forces the classes of (1, 1) and (0, 0)
to agree. Both class premises hold over the same Nat, with characteristic zero.
The natural-cast equality is in the second envelope. EnvelopeCancellation.nestedNatCast
constructs it for any semiring on the first envelope whose casts have the specified
values. RingInstanceFormation checks these occurrences of the pinned instance. -/

/- instOrderedRingQOfLawfulOrderLTOfExistsAddOfLT selects ofSemiring in its semiring index.
Nat realizes the strict order, preorder, ordered ring and additive existence premises together.
The selected quotient ring requires the pinned cancellation law on the representative (1,0). -/
