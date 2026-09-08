/- GID: D5/S3/Weil/ZetaLinear/Bounds/CoordinateDepthProbe
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: A five-segment coordinate resolves to a Lean module the gate admits. -/

import Mathlib.Tactic.NormNum

/- Trigger payload for the coordinate-depth change merged as #6414.

   This module exists to make the admission judges evaluate a coordinate that the
   previous grammar refused: `D5/S3/Weil/ZetaLinear/Bounds/CoordinateDepthProbe` is five
   segments, and `parts.Length is 3 or 4` rejected every such address. The layer PR's
   green was vacuous for that predicate because its own diff contained no five-segment
   path, so this payload supplies one on the permissive side, where a judge that had not
   actually changed would report an SL-000 finding.

   The bucket is chosen, not arbitrary: `D5/S3/Weil/ZetaLinear/` holds 24 modules whose
   members are 100% frozen (2026-09-08 reading), so it also demonstrates that opening a
   subdomain under a full, fully frozen bucket is a pure addition - it never moves a
   frozen module and therefore never meets the freeze law.

   This PR is a probe. It is read for its verdicts and closed; it is not merged and
   nothing here is deposited or frozen. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaLinear.Bounds.CoordinateDepthProbe

theorem coordinate_depth_probe_bound : (2 : ℕ) ≤ 4 := by norm_num

end D5.S3.Weil.ZetaLinear.Bounds.CoordinateDepthProbe
