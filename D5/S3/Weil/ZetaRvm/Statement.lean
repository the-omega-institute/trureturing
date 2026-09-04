/- GID: D5/S3/Weil/ZetaRvm/Statement
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   digest: Assemble RiemannVonMangoldt for the canonical zeta-zero configuration. -/

/- Ported from anthropics/formal-math commit 2bafb8c88f177284a2123b5fefa2ff84e2365eb6.
   Modified by trureturing on 2026-09-04: repository routing and canonical ZeroData assembly. -/
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/Statement.lean — Riemann–von Mangoldt assembly:
  Zeta23.RvM.riemannVonMangoldt (hΓ : GammaFacts) : RiemannVonMangoldt zetaZeroConfig
from Zeta23.RvM.rvM_main (MainTerm.lean) and Zeta23.RvM.zetaZeroConfig_local_count
(LocalCount.lean). Conditional on the Γ-facts by design (Stirling enters only through
`GammaFacts`).
-/
import D5.S3.Weil.ZetaRvm.MainTerm

noncomputable section

namespace Zeta23.RvM

/-- **H-RvM for Mathlib's ζ**, given the Γ-facts. -/
theorem riemannVonMangoldt (hΓ : GammaFacts) : RiemannVonMangoldt zetaZeroConfig :=
  ⟨rvM_main hΓ, zetaZeroConfig_local_count⟩

end Zeta23.RvM
