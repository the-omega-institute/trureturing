---
bibkey: tauceti2026partitionalternants
authors: The Tau Ceti contributors
year: 2026
title: TauCeti alternant coefficients and partition beta-numbers
doi: null
url: https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156
claim: Alternant coefficients count signed exponent permutations; beta-numbers recover the literal Young diagram and partition label.
strata_touched:
  - D5/S3/Combinatorics/Partitions/PartitionAlternantCoefficients
license: Apache-2.0
triage: anchor
---

# Partition alternant coefficients for symmetric-group characters

## Verified locator

https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156

## Selected source and adaptation

The repository pins Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
TauCeti at the revision above declares Lean 4.35.0 and Mathlib ccbef15ebdb41c2addfac682131f83c75904c3c1.
The different Mathlib revision requires the A17.2 port form. Public source is not evidence
of native compatibility. No Lake dependency or TauCeti import is introduced.

Only the following declaration slices are retained, with their proof bodies unchanged.
Visibility, surrounding namespaces and qualifications of the root YoungDiagram type are
adapted to this repository. Unused declarations from the source files are omitted.

- `TauCeti/RingTheory/MvPolynomial/Symmetric/Alternant.lean:92`: `alternant` (2 source lines).
- `TauCeti/RingTheory/MvPolynomial/Symmetric/Alternant.lean:98`: `alternant_def` (3 source lines).
- `TauCeti/RingTheory/MvPolynomial/Symmetric/Alternant.lean:104`: `alternant_eq_sum` (3 source lines).
- `TauCeti/RingTheory/MvPolynomial/Symmetric/Alternant.lean:110`: `coeff_alternant` (20 source lines).
- `TauCeti/RingTheory/MvPolynomial/Symmetric/Alternant.lean:133`: `coeff_alternant_of_injective` (15 source lines).
- `TauCeti/Combinatorics/Young/Diagram.lean:64`: `rowLen_eq_zero_of_colLen_le` (5 source lines).
- `TauCeti/Combinatorics/Young/Diagram.lean:87`: `rowLen_injective` (6 source lines).
- `TauCeti/Combinatorics/Young/BetaNumbers.lean:67`: `betaNumber` (1 source lines).
- `TauCeti/Combinatorics/Young/BetaNumbers.lean:69`: `betaNumber_def` (2 source lines).
- `TauCeti/Combinatorics/Young/BetaNumbers.lean:74`: `betaNumber_lt_betaNumber` (9 source lines).
- `TauCeti/Combinatorics/Young/BetaNumbers.lean:99`: `eq_of_betaNumber_eq` (9 source lines).
- `TauCeti/Combinatorics/Young/BetaNumbers.lean:110`: `strictAnti_betaNumber` (3 source lines).
- `TauCeti/Combinatorics/Young/Partitions.lean:60`: `ofPartition_injective` (2 source lines).

The selected slice contains 13 declarations from four source files, totaling 80 source
lines including the adjacent explanatory comment. Those four complete files have a
12-file TauCeti import closure totaling 2,144 lines. The retained declaration slice
needs none of the other declarations from that whole-file closure. These are source
measurements, not a compiled constant-dependency report.

All selected private helpers are consumed by `partition_alternant_coefficient`.
The new argument compares the sorted lists of beta-numbers carried into one another by
a permutation, recovers equality of the Young diagrams, and then uses injectivity of
Mathlib's literal `YoungDiagram.ofPartition`. It does not choose an arbitrary labeling
of irreducible representations.

## Boundary and retirement

This unit supplies source for the coefficient-isolation step at every degree and finite
row bound, including zero padding. It does not supply Schur polynomials, a Specht module,
the Frobenius expansion or the equality with an ordinary trace. It does not assume any
of these missing statements as a hypothesis. Native checking and axiom-closure inspection
remain pending.

Delete each port and use a direct Mathlib reference when the Mathlib revision pinned in
this repository's own lake-manifest.json contains an equivalent declaration with the
same hypotheses and conclusions, verified by a native build at that pin. The source file
and declaration names above identify the comparison targets. Acceptance into some other
upstream revision does not trigger retirement.

## Remaining mathematical comparison

The intended character comparison uses the same partition throughout:

1. For a positive cycle list, identify the product of power sums with `psumPart` of
   the full permutation partition. Fixed points contribute parts equal to one.
2. Use `psumPart_eq_sum_spechtCharValue_smul_schurPoly` from
   `TauCeti/RepresentationTheory/Symmetric/FrobeniusCharacteristic.lean:164`.
   This theorem holds for an arbitrary finite alphabet and degree. The separate
   basis equivalence with its degree bound is not the required input.
3. Multiply by the descending staircase alternant. For shapes inside the alphabet
   bound, use `diagramSchurPoly_mul_alternant` from
   `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Bialternant.lean:254`.
   Taller shapes vanish by `schurPoly_eq_zero_iff` from Schur/Basic. The coefficient
   identity in this unit then selects the original partition, without relabeling.
4. Match the three-variable descending determinant to the existing HSW
   `vandermonde3`; its orientation is the descending staircase, not the ascending
   Vandermonde convention.
5. Use `spechtCharValue_eq_spechtChar` from
   `TauCeti/RepresentationTheory/Symmetric/Specht/Character.lean:179`, and then
   `character_spechtModuleℂ_intCast` from Specht/Complex.lean:111. The latter
   compares the ordinary character of `spechtModuleℂ` with the integer character.
   Its source definition is the complex scalar extension of the rational
   polytabloid `spechtModule`, labeled by the same `YoungDiagram.ofPartition`.

The whole-file import closure of FrobeniusCharacteristic, Specht/Complex and
Schur/Bialternant has 145 TauCeti files and 33,681 lines at the cited revision.
This is an upper bound; it is not a measured necessity for the selected declarations,
and this unit does not vendor it. The repository's existing finite-character,
induction and Mackey interfaces must be reused where their actual statements match;
putting duplicate generic algebra under TauCeti namespaces would create a second
source. The selected coefficient proof has no such character-algebra prerequisite.

## Copyright and NOTICE chain

The selected Diagram and Partitions files carry:
Copyright (c) 2026 Tau Ceti. All rights reserved.
The selected BetaNumbers and Alternant files carry:
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
All four name The Tau Ceti contributors as authors and refer to the root LICENSE.
The complete immutable upstream archive contains no file named NOTICE or NOTICE.*;
there is no additional NOTICE file in the selected source ancestry.

## Complete upstream license

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
