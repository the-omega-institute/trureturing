/- GID: D5/S3/Weil/ZetaGamma/GammaFactsComplete
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   digest: Assemble the unconditional GammaFacts certificate. -/

/- Ported from anthropics/formal-math commit 2bafb8c88f177284a2123b5fefa2ff84e2365eb6.
   Modified by trureturing on 2026-09-04: repository routing and canonical ZeroData assembly. -/
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/Complete.lean — assembly of H-Γ:
All nine fields of Zeta23.GammaFacts ([eq:mufacts] + the Γ-halves of [eq:muints])
are proved: even/smooth (Zeta23/GammaFacts.lean), monotoneOn/mu_zero_le/
neg_one_lt_mu_zero/deriv_bound (Zeta23/GammaFacts/Mu.lean, via the digamma
partial-fraction series), stirling (Zeta23/GammaFacts/StirlingVert.lean, C = 20/2π),
int_mu/int_mu_sq (Zeta23/GammaFacts/IntMu.lean, from stirling + FTC).
-/
import D5.S3.Weil.ZetaCore.Hypotheses
import D5.S3.Weil.ZetaGamma.GammaFacts
import D5.S3.Weil.ZetaGamma.GammaMu
import D5.S3.Weil.ZetaGamma.GammaIntMu
import D5.S3.Weil.ZetaGamma.GammaStirlingVert

noncomputable section

namespace Zeta23

/-- GammaFacts from any Stirling bound for μ (the only analytically deep field). -/
theorem gammaFacts_of_stirling (hst : MuInts.StirlingHyp) : GammaFacts :=
  ⟨mu_even, mu_smooth, MuFields.mu_monotoneOn, MuFields.mu_zero_le, MuFields.neg_one_lt_mu_zero,
    hst, MuFields.mu_deriv_bound, MuInts.int_mu_of_stirling hst, MuInts.int_mu_sq_of_stirling hst⟩

/-- **H-Γ, unconditionally.** -/
theorem gammaFacts : GammaFacts := gammaFacts_of_stirling StirlingVert.mu_stirling

end Zeta23
