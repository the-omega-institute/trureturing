/- GID: D5/S3/Weil/ZetaRvm/BacklundDefs
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   digest: Port the shared Backlund zero-set definition. -/

/- Ported from anthropics/formal-math commit 2bafb8c88f177284a2123b5fefa2ff84e2365eb6.
   Modified by trureturing on 2026-09-04: repository routing and canonical ZeroData assembly. -/
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/BacklundDefs.lean — shared definition for Backlund's bound.
The Jensen count `reZeroSet_card_le` is in Zeta23/RvM/ReZeroCount.lean; the
argument-variation half and the assembly of `backlund_horizontal` are in
Zeta23/RvM/Backlund.lean.
-/
import D5.S3.Weil.ZetaCore.InstancePriorities
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Complex

noncomputable section

namespace Zeta23
namespace RvM

/-- The zero set of `σ ↦ Re ζ(σ+iT)` on `[1/2, 2]` (used by
`reZeroSet_card_le` and `im_integral_logDeriv_le` / `backlund_horizontal`). -/
def reZeroSet (T : ℝ) : Set ℝ :=
  {σ | σ ∈ Set.Icc (1/2 : ℝ) 2 ∧ (riemannZeta (σ + T * I)).re = 0}

lemma mem_reZeroSet {T σ : ℝ} :
    σ ∈ reZeroSet T ↔ σ ∈ Set.Icc (1/2 : ℝ) 2 ∧ (riemannZeta (σ + T * I)).re = 0 := Iff.rfl

end RvM
end Zeta23

end
