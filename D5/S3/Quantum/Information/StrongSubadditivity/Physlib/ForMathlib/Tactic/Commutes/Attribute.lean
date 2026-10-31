/- GID: D5/S3/Quantum/Information/StrongSubadditivity/Physlib/ForMathlib/Tactic/Commutes/Attribute
   generality: G
   mirror-B: none(waiver:upstream-proof-closure)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consumed Physlib strong-subadditivity proof closure. -/

/- Adapted from leanprover-community/physlib, revision
2725b6f621901d4cd330869e9b77105045c1582e, QuantumInfo/ForMathlib/Tactic/Commutes/Attribute.lean.
Changes: D5 import paths, bounded modules, and local supplier elaboration options.
Retire this port when the receiving pinned Mathlib provides the equivalent declarations.
Apache-2.0 license text is included in the sibling ForMathlib/Misc.lean. -/
/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Aesop.Frontend.Command

/-!
# Commutes Rule Set

This module defines the `Commutes` Aesop rule set which is used by the
`commutes` tactic. Aesop rule sets only become visible once the file in which
they're declared is imported, so we must put this declaration into its own file.
-/

@[expose] public section

set_option relaxedAutoImplicit true

declare_aesop_rule_sets [Commutes] (default := false)
