---
bibkey: tao2026newton
authors: Terence Tao
year: 2026
title: "The Newton and Maclaurin inequalities for symmetric polynomials"
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/e3c1793d0e097d9b8d782a323e91c99c2ef0d64c/Mathlib/Analysis/MeanInequalitiesSymmetric.lean
claim: "Newton inequalities for elementary symmetric functions of arbitrary real multisets; licensed source of the Crown prerequisite."
strata_touched:
  - D5/S3/Analytic/RealRootedCoefficientNewton
  - D5/S3/Combinatorics/Geometry/CrownOrderPolytopeLogConcavity
license: Apache-2.0
triage: anchor
---

# Newton inequalities: immutable source and license

## Verified locator

URL: https://github.com/leanprover-community/mathlib4/blob/e3c1793d0e097d9b8d782a323e91c99c2ef0d64c/Mathlib/Analysis/MeanInequalitiesSymmetric.lean

The reduced Newton inequality is taken from Mathlib PR 42876 at immutable
revision `e3c1793d0e097d9b8d782a323e91c99c2ef0d64c`. Its source SHA-256 is
`daab9424b8817d3e6bf62f14fe1bfb1c35cf96a47157897d46af2f64a70da2f2`.
It applies to arbitrary real multisets, including repeated entries and zero.
The Crown proof applies it to the negated root multiset of the auxiliary
scalar polynomial and converts elementary symmetric functions to coefficients
by the pinned Vieta theorem. The actual geometric f-polynomial is not assumed
to split.

The source's toolchain is `leanprover/lean4:v4.34.0-rc1`; this repository pins
`v4.33.0`. The port retains the upstream derivative-root and strong-induction
proof. Its modifications specialize prerequisites to real numbers, localize
normalization facts inside the proof, retain only the reduced Newton conclusion,
and adapt imports and one natural-binomial cast to the current pin. The
coefficient conversion belongs to the substantive Crown proof, with all
out-of-degree cases treated there.

The following additional source files at the same immutable revision supply
only the prerequisites needed by Newton:

| Source path under Mathlib | Copyright and authors | SHA-256 |
| --- | --- | --- |
| Analysis/MeanInequalitiesSymmetric.lean | Copyright (c) 2026 Terence Tao. All rights reserved. Authors: Terence Tao. | daab9424b8817d3e6bf62f14fe1bfb1c35cf96a47157897d46af2f64a70da2f2 |
| RingTheory/MvPolynomial/Symmetric/Defs.lean | Copyright (c) 2020 Hanting Zhang. All rights reserved. Authors: Hanting Zhang, Johan Commelin. | e264f728dc8586158d77094d234f03f42a04e3cdf4dc0ba64103b5a7d7d0fb96 |
| Algebra/Order/Chebyshev.lean | Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved. Authors: Mantas Bakšys, Yaël Dillies. | 6bacf35e3e6ab8a22482156c9b8b18a33da465e436d18b8c7f6144086ff55164 |
| Data/Multiset/Fintype.lean | Copyright (c) 2022 Kyle Miller. All rights reserved. Authors: Kyle Miller. | 27a111c793931c87c9946e0041a1e533d88901c2cf166bdbccd75df88a2430c7 |

All four upstream files state that they are released under Apache 2.0 as
described in the upstream LICENSE. The official LICENSE fetched at this
revision has SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`;
its complete text is reproduced below. The root `NOTICE` URL at this immutable
revision returned HTTP 404 on 2026-09-20; the source headers contain no separate
NOTICE reference.

Retirement condition: when this repository's own future pinned Mathlib contains
equivalent Newton and prerequisite declarations, delete the local port and
replace its Crown use by direct imports and applications of those declarations.
Upstream acceptance alone does not satisfy this condition.

## Apache License 2.0 (complete upstream text)

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

   Copyright {yyyy} {name of copyright owner}

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
