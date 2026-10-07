---
bibkey: openai2026volterra
authors: OpenAI
year: 2026
title: "OpenAI math Volterra majorants and factorial integral helpers"
doi: null
url: https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a
claim: "The pinned source gives a normalized factorial integral identity, an exponential Volterra supersolution and a uniform bound obtained by ordered iteration; a private helper consumes the integral proof in the literal curvature recursion."
strata_touched:
  - D5/S3/Arith/Robin/PrimePrefixCurvatureVolterraFactorial
license: Apache-2.0
triage: anchor
---

# Volterra source for the literal curvature recursion

Source repository `openai/math`, immutable commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` (6 October 2026).
The repository's [formalization catalogue](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/formalization.yaml)
attributes its authorship to OpenAI. Its [README](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/README.md)
describes output produced by an internal OpenAI model. This is repository
attribution to the OpenAI math contributors, without an invented personal
author or copyright line.

The exact leaves are:

- [VolterraMajorant.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/VolterraMajorant.lean),
  SHA256 `3622a473582f2111b174f3a04d69e56a928d781a3507e8d1035e55bb1bc1a7df`.
- [VolterraSup.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Regularity/VolterraSup.lean),
  SHA256 `9337e1b7cab9ebdbada182329b51920067d627b9025ff0b1b38a0b0d0b7a171a`.

Both full leaves were read and their Git blobs checked against the complete
immutable Analysis tree. The first imports Mathlib; the second imports
Mathlib and the first leaf. Upstream uses Lean `v4.34.1` and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The local consumer must be adapted
to this repository's pinned `v4.33.0`; no wholesale dependency upgrade is implied.

## Exact contracts and actual consumption

`OAI.RVM.integral_Icc_factorial_tail` states, for every real C, natural n and
real t≥0,

$$
C\int_{[0,t]}\frac{(Cu)^n}{n!}\,du
=\frac{(Ct)^{n+1}}{(n+1)!}.
$$

Its proof uses accurate polynomial integration and `Nat.factorial_succ`.
`OAI.RVM.exists_tame_volterra_majorant`, for D,C,F≥0, supplies continuous
monotone H with H(t)≥1 for t≥0 and

$$
D+C\int_{[0,t]}[1+(F+1)(1+H(u))]du\le H(t).
$$

The explicit H is `(D+1) exp((2C(F+2)+1)t)`.
`OAI.RVM.volterra_uniform_bound` assumes a nonnegative finite initial bound
on u over [0,U] and improvement against every continuous upper bound g by
`D+C∫[0,t](1+g)`. For D,C≥0 and U≤H it yields a common nonnegative upper
bound independent of that initial bound. The proof uses the supersolutions
`z(t)+L(Ct)^n/n!` and Mathlib's factorial summability.

The modified private helper in
`D5/S3/Arith/Robin/PrimePrefixCurvatureVolterraFactorial.lean` retains the
upstream factorial-integral statement and proof body. Only visibility is
changed from the source lemma to a private theorem. Its actual consumers
`integral_factorial`, `lift_factorial` and `volterra_bound` are private
steps in the proof of the same original curvature residual. The operator is

$$
(Tf)(v)=e^{-v}\int_0^v a(s)\int_0^s(s-t)f(t)dt\,ds.
$$

The exact lift primitive raises normalized degree by two; the outer primitive
raises it by one. The already paid coefficient bound a≤1/3 and the true
residual recurrence give, for every natural n and v≥0,

$$
0\le R_n(v),\qquad
|R_n(v)|\le\frac{v^{3n}}{2\cdot3^n(3n)!}.
$$

The public result also recovers the literal original curvature uniformly on
each [0,V], V≥0. The auxiliary comparison n!≤(3n)! is used only in proving
that the exact rate tends to zero. Compact uniform convergence does not pay
complete logarithmic-moment convergence or the signed Robin arithmetic tail.
The full majorant and generic uniform-bound lemmas are inspected suppliers,
with no copied or imported local declarations for them. This is a source
transplant consumed by a new actual-object proof, without a mathematical
priority claim or a Robin/RH completion claim.

## Licence and notices

The complete upstream [Apache-2.0 LICENSE](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/LICENSE)
was read and retained (11,357 bytes; SHA256
`c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`).
Root LICENSE and lean/LICENSE have the same Git blob
`261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64`. Any distributed code adaptation
retains the full licence, source attribution and its modification notice.
The licence appendix contains the unfilled template
`Copyright [yyyy] [name of copyright owner]`; neither source leaf supplies
an additional author or copyright header. No filled copyright line is inferred.

No NOTICE exists in the immutable root, lean or lean/OAI directory listings,
or in the complete, untruncated Analysis subtree containing these leaves.
This is the inspected source scope; it is not a claim about unrelated
subtrees of the entire repository.

## Complete upstream licence

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
