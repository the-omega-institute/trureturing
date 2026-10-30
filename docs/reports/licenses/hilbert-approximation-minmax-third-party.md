# Hilbert approximation-number min-max third-party license

The following notices and full license accompany the selected adapted
proofs of the approximation-number strict-threshold min-max bound.
They cover the four selected files at the immutable revision named
below. They do not license unrelated supplier or vendored content.

## Selected-source attribution and change notice

# Hilbert approximation-number min-max source attribution

The selected proof source is https://github.com/AIQ-Kitware/aiq-dkps-formalization at revision 8924c4cc743d2f193bb4f39bee800790698a681b.

The following source headers are preserved in the adapted unit:

- ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean: Copyright (c) 2026 Kitware, Inc. All rights reserved. Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh. The supplier credits Mathlib PR #32126 and Davis--Kahan commit fc38eb48b9b49f2e1d87fe0c7022dc5e262820a7.
- ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean: Copyright (c) 2026 Kitware, Inc. All rights reserved. Authors: Jon Crall, Claude Fable 5, OpenAI GPT-5.6 Thinking. The supplier credits DavisKahan/OperatorIdeal/ApproximationNumbers/OperatorModulus.lean and ForMathlib/Analysis/InnerProductSpace/OperatorAbsoluteValue.lean at fc38eb4.
- ForTauCeti/Analysis/InnerProductSpace/Spectral/Cutoff.lean and ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean: Copyright (c) 2026 Kitware, Inc. All rights reserved. Authors: Jon Crall, Claude Opus 5. The supplier attributes the CFC proof to authored-in-place work and distinguishes it from the Spectra PVM proof of the same target statement.

All four selected files are released under Apache 2.0. The accompanying LICENSE is the full original text. The supplier source audit limits vendor/lean/NOTICE.md to vendored Lean; that vendor source is excluded. This attribution preserves the supplier's statements and does not certify independent derivation. SchurHorn and Singular.Subspace are excluded from this unit.

Changes by OpenAI Codex: selected declarations only, native namespace, private consumed support, complex specialization with pinned Mathlib CFC, and direct pinned Mathlib extraction of the finite independent family. Retire the slice when this repository's pinned Mathlib contains equivalent declarations with the full original hypotheses.

## Verbatim selected source headers

```text
ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh
-/

ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, OpenAI GPT-5.6 Thinking
-/

ForTauCeti/Analysis/InnerProductSpace/Spectral/Cutoff.lean
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

```

## Verbatim selected source provenance

```text
ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean
## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib/Analysis/Normed/Operator/ApproximationNumber.lean`
  at Davis--Kahan commit `fc38eb48b9b49f2e1d87fe0c7022dc5e262820a7`.
* Original declarations: `ContinuousLinearMap.approximationNumber` and the order
  and ideal API in the same namespace, plus two pieces of plumbing that have
  since moved out so that this module carries approximation-number API and
  nothing else: the universe helper `Cardinal.le_natCast_of_lift_le` (now the iff
  `Cardinal.lift_le_natCast` in `ForTauCeti/SetTheory/Cardinal/Lift.lean`) and
  the rank-of-composition bounds `rank_comp_left_le_of_rank_le` and
  `rank_comp_right_le_rank` (now `ContinuousLinearMap.rank_comp_le_natCast_right`
  and `ContinuousLinearMap.rank_comp_le_left` in
  `ForTauCeti/LinearAlgebra/Dimension/RankComp.lean`, generalized to
  `LinearMap`).
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss,
  Arnav Mehta, Rawad Kansoh; Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* The Davis--Kahan file was itself adapted from Mathlib PR #32126.
* Extraction class: **copied**, converted to the Tau Ceti module system, then
  renamed conclusion-outward per the signature-polish backlog
  No mathematical change; see Appendix A of that document for the name index.
* Spectra influence: **none** — this module has no Spectra dependency and never
  did; it imports only Mathlib.


ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean
## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original modules: `DavisKahan/OperatorIdeal/ApproximationNumbers/OperatorModulus.lean`
  (`rectangularOperatorModulus` and its API, Jon Crall / OpenAI GPT-5.6 Thinking)
  and `ForMathlib/Analysis/InnerProductSpace/OperatorAbsoluteValue.lean`
  (`operatorAbs` and its API, Jon Crall / Claude Fable 5), both at Davis--Kahan
  commit `fc38eb4`; Apache 2.0.
* Extraction class: **unified and generalized**.  Per the signature-polish
  backlog, the two parallel APIs —
  one rectangular, one square — are replaced by this single rectangular
  definition with dot notation on `ContinuousLinearMap`.  The square-only
  composition laws `norm_operatorAbs_mul` / `norm_mul_operatorAbs` are
  generalized to rectangular operators here, and reproved from the pointwise
  isometry instead of the C⋆-identity; the uniqueness and commutation results
  are likewise generalized.
* Spectra influence: **none** — the construction uses Mathlib together with the reusable
  `ForTauCeti` scalar-transport functional calculus.


ForTauCeti/Analysis/InnerProductSpace/Spectral/Cutoff.lean
## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.  The smooth
  cutoff section arrived later, from
  `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxReal.lean`, where it had been
  written `private` against one Hilbert space; it is stated here for any.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none**.  `vendor/Spectra` proves the corresponding facts through its
  projection-valued-measure and Borel functional calculus layer; the point of this module is
  that the continuous functional calculus already in Mathlib suffices.


ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean
## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none in the proof.**  The statement is the one
  `DavisKahan/Interop/Spectra/ApproximationNumberMinMax.lean` carried as
  `exists_linearIndependent_lowerBound_of_lt_approximationNumber_complex`, whose proof
  used Spectra's projection-valued measures; nothing of that proof is reused here.


```

## Full original Apache 2.0 license

```text
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright 2026 "Kitware Inc"

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
```
