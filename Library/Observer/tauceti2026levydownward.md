---
bibkey: tauceti2026levydownward
authors: The Tau Ceti contributors; Cameron Freer and the Exchangeability Project contributors
year: 2026
title: Reverse crossings and Levy downward conditional expectation convergence
doi: null
url: https://github.com/TauCetiProject/TauCeti/tree/c9dbc67d6e3f1254d3da41c391cd1af512ea3b7f
claim: An antitone sequence of ambient sub-sigma-algebras on an arbitrary finite measure space gives almost-everywhere and L1 convergence of the actual real conditional expectations to conditional expectation at the raw infimum, by finite-horizon reversal, crossing estimates, uniform integrability and raw-infimum limit identification.
strata_touched:
  - D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/DecreasingConditioning/ReverseCrossings
  - D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/DecreasingConditioning/LevyDownward
license: Apache-2.0
triage: anchor
---

# Source and scope

The source is TauCetiProject/TauCeti at immutable revision
`c9dbc67d6e3f1254d3da41c391cd1af512ea3b7f`. The real fixed-input
`tendsto_ae_and_eLpNorm_condExp_iInf` construction proves both almost-everywhere
and L1 convergence to the actual conditional expectation at the raw infimum of
an antitone sequence of sigma-algebras. The measure is finite and the underlying
measurable space is arbitrary. The nonintegrable-input branch uses the defining
zero conditional expectation. The construction does not assume a reverse-limit
or conditional-convergence premise.

The finite-horizon crossing argument retains its endpoint comparison at N+1.
The infinite-horizon construction uses a common measurable representative at
the raw infimum, uniform integrability, Vitali convergence and the tower
property. No completion, countable generation, standard Borel hypothesis,
adaptedness or eventually constant sequence is part of the fixed-input result.
The varying-integrand Hunt theorem requires its additional joint tail argument;
it is not asserted by the fixed-input source contract alone.

The source uses Lean 4.36.0-rc2 and Mathlib
`1b1ccf4b088b32fa3f23f2de1127433254a81e1e`. The receiving pins are
Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The source-preserving port form of A17.2 applies to this mismatch.
The scope is the real AE/L1 proof; complex, general-Lp, conditional-law,
composition and factorization extensions are excluded.

## Verified locator

- URL: https://github.com/TauCetiProject/TauCeti/tree/c9dbc67d6e3f1254d3da41c391cd1af512ea3b7f
- Combined construction: `TauCeti/Probability/Martingale/Convergence.lean`,
  `tendsto_ae_and_eLpNorm_condExp_iInf`.
- Upstream public projections: `tendsto_ae_condExp_iInf` and
  `tendsto_eLpNorm_condExp_iInf` in the same source.
- Source ancestry: https://github.com/cameronfreer/exchangeability/tree/e0532e59ceff23edab44dda9ab0655debbc9cc22

# Source correspondence

`ReverseCrossings` takes the consumed finite-horizon reversal, pathwise
crossing-time comparison, congruence and uniform reverse-crossing estimate
from Reverse, Crossings/TimeReversal, Crossings/Pathwise and Crossings/Bounds,
with the conditional positive-part estimate from ConditionalExpectation.
`LevyDownward` takes the antitone-limit construction from AntitoneLimit,
the raw-infimum representative helpers from AEStronglyMeasurable,
the conditional L1 continuity identification from ConditionalExpectation,
and the combined fixed-input argument from Convergence.
All applicable original copyright and authorship notices remain adjacent to
adapted code. Source declarations that already have exact receiving suppliers
are used directly. The port does not claim literature originality.

# Retirement

At a Mathlib revision actually adopted by this repository, an equivalent
supplier must preserve the complete quantified contract and admit a compiled
exact replacement application with the permitted axiom closure. Replace the
corresponding port by that supplier once this criterion holds. Availability on
an unadopted revision or acceptance upstream does not suffice. Retire each
superseded dependency separately while retaining any still-needed joint limit
construction.

# Immutable source locators

- `TauCeti/Probability/Martingale/Reverse.lean`: SHA-256 `c3b8ce1fbd0dc1e7644bc7257036d181cb765f757a3f083bdbf3691f9751079f`;
  https://github.com/TauCetiProject/TauCeti/blob/c9dbc67d6e3f1254d3da41c391cd1af512ea3b7f/TauCeti/Probability/Martingale/Reverse.lean
- `TauCeti/Probability/Martingale/Crossings/TimeReversal.lean`: SHA-256 `653b53059c68bd69ab2085f6523672882a477903ec6d0f04758433798d935cd9`;
  https://github.com/TauCetiProject/TauCeti/blob/c9dbc67d6e3f1254d3da41c391cd1af512ea3b7f/TauCeti/Probability/Martingale/Crossings/TimeReversal.lean
- `TauCeti/Probability/Martingale/Crossings/Pathwise.lean`: SHA-256 `5321b24b330b7ff4ff3a7bc7c2c85aa729e590c094089982cc14524463c9b1f5`;
  https://github.com/TauCetiProject/TauCeti/blob/c9dbc67d6e3f1254d3da41c391cd1af512ea3b7f/TauCeti/Probability/Martingale/Crossings/Pathwise.lean
- `TauCeti/Probability/Martingale/Crossings/Bounds.lean`: SHA-256 `ea6c68915b05d2f2ef29cb99d7c72862ec3afb8bc4637fa8ceed926295d71b24`;
  https://github.com/TauCetiProject/TauCeti/blob/c9dbc67d6e3f1254d3da41c391cd1af512ea3b7f/TauCeti/Probability/Martingale/Crossings/Bounds.lean
- `TauCeti/Probability/Martingale/AntitoneLimit.lean`: SHA-256 `60506d3e471fe5a6dfe97930c4370966d47b52f65d264e000d088932c0db65b2`;
  https://github.com/TauCetiProject/TauCeti/blob/c9dbc67d6e3f1254d3da41c391cd1af512ea3b7f/TauCeti/Probability/Martingale/AntitoneLimit.lean
- `TauCeti/Probability/Martingale/Convergence.lean`: SHA-256 `fcd0c79af703d6a63e18b9b41e6b90dd14cbd81f8b9cac1914592fd107d4c998`;
  https://github.com/TauCetiProject/TauCeti/blob/c9dbc67d6e3f1254d3da41c391cd1af512ea3b7f/TauCeti/Probability/Martingale/Convergence.lean
- `TauCeti/MeasureTheory/Function/AEStronglyMeasurable.lean`: SHA-256 `b7a5d6decc4b581f45ddc7dbb24240ccbc40a9018248e6865f7c2881fd4a05b6`;
  https://github.com/TauCetiProject/TauCeti/blob/c9dbc67d6e3f1254d3da41c391cd1af512ea3b7f/TauCeti/MeasureTheory/Function/AEStronglyMeasurable.lean
- `TauCeti/MeasureTheory/Function/ConditionalExpectation.lean`: SHA-256 `60c16acac0c0e77d83dd12ec84ace0f1b4b10f78a13490cbb04ded4031009c45`;
  https://github.com/TauCetiProject/TauCeti/blob/c9dbc67d6e3f1254d3da41c391cd1af512ea3b7f/TauCeti/MeasureTheory/Function/ConditionalExpectation.lean

The complete immutable source trees list no NOTICE file. The source explicitly
acknowledges Cameron Freer/exchangeability at the immutable ancestry above.
Both applicable Apache-2.0 license texts follow verbatim, including appendices.

# Tau Ceti Apache-2.0 license

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

# Exchangeability Apache-2.0 license

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
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright 2025 The Exchangeability Project contributors

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
