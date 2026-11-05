# Hilbert approximation-number Ky Fan source license

The selected source is AIQ-Kitware/aiq-dkps-formalization revision
8924c4cc743d2f193bb4f39bee800790698a681b, under Apache-2.0.
The complex endpoint is ContinuousLinearMap.kyFanGauge_add_le_complex in
ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/KyFan.lean, SHA-256
b25b4fdae0546ccc3795ee7301e76f371ef02a0c2b306f0294c75f4f6bc0c744.
The approximation number is the infimum of the actual operator-norm error over
bounded maps of rank at most n. The gauge is its finite prefix sum n < k.
The theorem retains independent source and target universes, completeness of
both complex Hilbert spaces, actual rectangular bounded maps, and every natural k.
It assumes neither compactness nor separability nor positive dimension.

The native proof reuses MinMaxLowerBound.exists_independent_lower_bound, the
existing finite rectangular variational upper bound and its original attaining
orthonormal pair, and the existing finite spectral decomposition and test-space
bounds in HermitianEigenvaluePerturbation. The additional argument constructs
spectral truncations, compares rank-bounded errors, transports finite coordinates,
compresses the joint range, and combines finite source restrictions.
No supplier SchurHorn or Singular.Subspace proof is imported or copied.
The finite rectangular proof retains its separate revision
64e234954217f3ca907ac980c8cbde2900109a66 and existing license notice.
The existing spectral support retains its LeanPool revision
bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8 and its notice chain.

These are classical approximation-number and Ky Fan results; no mathematical
novelty is claimed. They do not identify compact or Hilbert-Schmidt spectral
sequences, an infinite Ky Fan sum, Shirokov's cost J, or a convex roof.
Retire the adapted source slices when this repository's pinned Mathlib supplies
equivalent declarations with the same hypotheses, and use direct imports.

## Original selected source headers

```text
ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh
-/

ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMax.lean
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/FiniteDimensional.lean
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/FiniteRestriction.lean
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/

ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/KyFan.lean
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
```

## Original source attribution chain

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


ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMax.lean
## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module:
  `ForMathlib/Analysis/Normed/Operator/ApproximationNumberMinMax.lean`
  at Davis--Kahan commit `fc38eb48b9b49f2e1d87fe0c7022dc5e262820a7`.
* Original declarations:
  `ContinuousLinearMap.le_approximationNumber_of_finrank_lt` and
  `ContinuousLinearMap.le_approximationNumber_of_linearIndependent`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Extraction class: **copied**, converted to the Tau Ceti module system.
  Declaration names are unchanged (they already extend the canonical Mathlib
  namespace).  No mathematical change.
* Spectra influence: **none** — this module imports only Mathlib and the
  sibling `Basic` and `CourantFischer` staging modules.


ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/FiniteDimensional.lean
## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module:
  `ForMathlib/Analysis/Normed/Operator/ApproximationNumberSingularValues.lean`
  at Davis--Kahan commit `fc38eb48b9b49f2e1d87fe0c7022dc5e262820a7`.
* Original declarations: `ContinuousLinearMap.approximationNumber_eq_singularValues`
  and the Eckart--Young bounds in the same namespace.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Extraction class: **copied**, converted to the Tau Ceti module system.
  Declaration names are unchanged (they already extend the canonical Mathlib
  namespace); references to the Courant--Fischer helpers track the redesigned
  API (`OrthonormalBasis.spanIndices` in `BasisSpan.lean` and the
  `LinearMap.IsSymmetric`-namespace eigenvalue results).  No mathematical
  change.
* Spectra influence: **none** — this module imports only Mathlib and the
  sibling `Basic` and `CourantFischer` staging modules.


ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/FiniteRestriction.lean
## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/Interop/Spectra/ApproximationNumberMinMax.lean`.
* Original declarations: `TauCeti.DavisKahan.Experimental.{`
  `approximationNumber_comp_subtypeL_le, finiteRestrictionApproximationNumbers,`
  `finiteRestrictionApproximationNumbers_upperBound,`
  `exists_finiteRestrictionApproximationNumber_gt_of_lt,`
  `approximationNumber_isLUB_finiteRestrictions,`
  `lt_approximationNumber_iff_exists_finiteDimensional_lowerBound}`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Extraction class: **copied and renamespaced**.  The statements are unchanged apart from
  the generalisation of `approximationNumber_comp_subtypeL_le` to an arbitrary `RCLike`
  field; the declarations move from `TauCeti.DavisKahan.Experimental` to
  `ContinuousLinearMap`, so that dot notation resolves.
* Spectra influence: **none**.  The module was under `DavisKahan/Interop/Spectra/` because
  its threshold theorem was once proved from `vendor/Spectra`'s projection-valued measures.
  That proof was replaced on 2026-07-28 by
  `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean`, after which
  nothing here touched Spectra and the module belonged in the staging layer.


ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/KyFan.lean
## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/OperatorIdeal/ApproximationNumbers/Core.lean`.
* Original declarations: `TauCeti.DavisKahan.Experimental.ExactSinTheta.{`
  `kyFanApproximationGauge, kyFanApproximationGauge_neg, kyFanApproximationGauge_zero,`
  `kyFanApproximationGauge_zero_map, kyFanApproximationGauge_one,`
  `kyFanApproximationGauge_smul, kyFanApproximationGauge_nonneg,`
  `kyFanApproximationGauge_adjoint, kyFanApproximationGauge_comp_le,`
  `opNorm_le_kyFanApproximationGauge, kyFanApproximationGauge_le_nat_mul_opNorm,`
  `kyFanSum_le_kyFanApproximationGauge,`
  `kyFanSum_eq_kyFanApproximationGauge,`
  `kyFanApproximationGauge_add_le_finiteDimensional,`
  `approximationSingularValue_restrict_mono,`
  `approximationSingularValue_orthogonalProjectionOnto_comp_eq,`
  `kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq,`
  `kyFanApproximationGauge_add_le_finiteSource,`
  `exists_finiteRestrictionApproximationNumber_add_gt,`
  `kyFanApproximationGauge_add_le_complex}`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Extraction class: **copied and renamespaced**.  The gauge moves to
  `ContinuousLinearMap.kyFanGauge` with the operator first so dot notation resolves, and
  `approximationSingularValue n K` is spelled `K.approximationNumber n` throughout — it was
  only ever an alias for it.  No proof was changed except for those renamings.
* Spectra influence: **none**, as of the replacement of the min--max bridge on 2026-07-28.

```

## Full supplier license

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
