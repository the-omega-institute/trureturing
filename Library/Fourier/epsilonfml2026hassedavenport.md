---
bibkey: epsilonfml2026hassedavenport
authors: fukubillueda-web contributors
year: 2026
title: epsilon_FML finite-field Hasse–Davenport supplier
doi: null
url: https://github.com/fukubillueda-web/epsilon_FML/tree/b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed
claim: The pinned epsilon_FML source supplies the exact Langlands-normalized Hasse–Davenport lift for arbitrary finite extensions and nontrivial additive characters.
strata_touched:
  - D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/HasseDavenportLift
license: Apache-2.0
triage: anchor
---

<!-- GID: D5/L/Fourier/epsilonfml2026hassedavenport -->
# Exact Hasse–Davenport supplier from epsilon_FML

This source card records the attributed upstream supplier used by the finite-field character-sums port.

## Verified locator

https://github.com/fukubillueda-web/epsilon_FML/tree/b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed

The pinned source locator is `LanglandsFirstMainLemma/FiniteField/HasseDavenportLift.lean`, declaration `LanglandsFirstMainLemma.hasseDavenportLift` (source line 461). The retained source bytes have SHA-256 `2f205c2d7c9720f870934bd332215032d23ab044e36db0baac999a655b4a65fd`. The source manifest and retained proof closure below bind the imported prerequisites. This locator attributes the exact code supplier; no manuscript theorem number or original mathematical priority is claimed.

## Provenance

- Repository: <https://github.com/fukubillueda-web/epsilon_FML>
- Immutable source commit: `b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed`
- Upstream toolchain: `leanprover/lean4:v4.32.2` with Mathlib revision `905b95818eb32af7874a58b427f50c1711a5e96c`.
- Target toolchain: repository Lean 4.33.0 with Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Port location: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma`.
- Namespace preserved: `LanglandsFirstMainLemma`.
- No NOTICE file occurs in the pinned source tree.

## Exact source manifest

The original source manifest has 14 files and 225458 total bytes. The retained proof closure has nine non-target Lean modules plus the target. The original downloaded bytes, including the omitted metadata-only Prelude, remain identified by the hashes below.

| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| `LICENSE` | 11357 | `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4` |
| `lean-toolchain` | 25 | `2bdc48adfa58d0017e538a0ad117c5d73d35deec879978f909406a80c8037273` |
| `lake-manifest.json` | 3904 | `8c68da26c0f6d7994949aa9ff57ddb59f5b4d6ddc74f66224f1d884c7381dcc2` |
| `LanglandsFirstMainLemma/FiniteField/HasseDavenportLift.lean` | 18646 | `2f205c2d7c9720f870934bd332215032d23ab044e36db0baac999a655b4a65fd` |
| `LanglandsFirstMainLemma/FiniteField/CharacterAPI.lean` | 8181 | `2d85103e46bc5ed75c9d2593e62f5dffb67f3b43ef45139c3f13923734b0b555` |
| `LanglandsFirstMainLemma/FiniteField/EulerProduct.lean` | 33840 | `5410cca856f03d5184bb781272813d2b8cf26e7f8072c36bb56a792d6345c517` |
| `LanglandsFirstMainLemma/LocalField/Extension.lean` | 45231 | `dcd038574652cc2b33b7ccb53f54232e012989e328bb039820b4662dca2216a9` |
| `LanglandsFirstMainLemma/Basic/FiniteProducts.lean` | 15465 | `2be274197ca116a61945e92a3b6aa6e505e1e05b40c0f5e33da5d769dc2bedec` |
| `LanglandsFirstMainLemma/LocalField/ResidueField.lean` | 10881 | `4ecc7e8f9e52ea3c30e6eea722487edbe174075d80251f92ad4bc1ebcdd5eab7` |
| `LanglandsFirstMainLemma/FiniteField/PolynomialWeights.lean` | 7463 | `ac18dcb74071925205d5c5e17edef72721bce96c8192327f815f565d5186dc87` |
| `LanglandsFirstMainLemma/Prelude.lean` | 1222 | `de829026dfc3ad0b35b9325f423da4a1465bc8d46c84086520a2fe07eda20907` |
| `LanglandsFirstMainLemma/LocalField/UnitFiltration.lean` | 27606 | `9421870db84fc04026fa9e90fbdb4c3c94385c14f78c25b9e655ed2ebc79f019` |
| `LanglandsFirstMainLemma/LocalField/Lattices.lean` | 22972 | `ff37ebdfbdf904bbcf7d1b0fc0156abe7ca53bc14a63234f23052baf4e063e70` |
| `LanglandsFirstMainLemma/LocalField/Valuation.lean` | 18665 | `d1d40703fde462c5e1023e8aff759ab1956b8111ce1272e8f5c994511a857522` |

## Retained proof closure

The ten retained modules, in import-compatible order, are:

1. `Basic/FiniteProducts.lean`
2. `LocalField/Valuation.lean`
3. `LocalField/Lattices.lean`
4. `LocalField/UnitFiltration.lean`
5. `LocalField/ResidueField.lean`
6. `FiniteField/CharacterAPI.lean`
7. `FiniteField/PolynomialWeights.lean`
8. `FiniteField/EulerProduct.lean`
9. `LocalField/Extension.lean`
10. `FiniteField/HasseDavenportLift.lean`

Paths are relative to the preserved `LanglandsFirstMainLemma` namespace and port location. FiniteProducts and Valuation import Mathlib directly. The upstream `Prelude.lean` contains only `blueprintScaffoldVersion`, `plannedModuleCount`, `authoritativeManuscript`, and `PendingTask := True`; none has a proof consumer in these ten modules. These four metadata definitions and their Blueprint descriptor are omitted from the live port. The Prelude row in the original source manifest records attribution, not a retained mathematical module.

Every mathematical definition, theorem statement, proof body and namespace in the ten modules is retained, including the degree-zero quotient compatibility proofs and explicit normal-subgroup instances required by the target Mathlib revision. Import and attribution normalization introduces no replacement declaration.

## Ported theorem

The public target is the exact upstream declaration `LanglandsFirstMainLemma.hasseDavenportLift` in `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/HasseDavenportLift.lean`.

For fields `k` and `K` with finite underlying types and an algebra structure, a finite multiplicative character `χ`, a finite additive character `ψ`, and `ψ ≠ 1`, the theorem states

```text
langlandsGaussSum (normMulChar k K χ) (traceAddChar k K ψ) =
  langlandsGaussSum χ ψ ^ Module.finrank k K
```

The normalization is `langlandsGaussSum(χ, ψ) = -gaussSum(χ⁻¹, ψ)`. The proof uses the actual norm and trace pullbacks, the closed-point power identity, and the Euler-product identity. The multiplicative character is unrestricted, so the trivial character is included; only the additive character is required to be nontrivial. This is upstream reuse, not a new mathematical-priority claim or an open-problem resolution.

The Lean 4.33 port keeps the original proof architecture. It supplies explicit normal-subgroup instances at the degree-zero unit quotient because the target Mathlib revision does not infer those commutative-group instances automatically, and names the quotient parameters explicitly. These edits do not alter the theorem statement or normalization.

## License

The following is the exact `LICENSE` file from the pinned source tree.

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

   Copyright [yyyy] [name of copyright owner]

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
