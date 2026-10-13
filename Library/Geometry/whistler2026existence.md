---
bibkey: whistler2026existence
authors: William Whistler
year: 2026
title: Existence of transition systems with orientations
doi: null
url: https://github.com/Vilin97/lean-pool/blob/762dd054ea9168a4aba93ae86b536b1bd841ce66/LeanPool/RegtsSevenster/RS/Novel/Skein/TransitionExists.lean
claim: For two independently fixed-point-free involutions a and t on a finite set, the walk a composed with t has disjoint t-paired orbits; comparison of their minima gives a Boolean orientation flipped by both involutions, including the empty set.
strata_touched:
  - D5/S3/Geometry/Hyperideal/EdgeStarTransitions
license: Apache-2.0
triage: anchor
---

<!-- GID: D5/L/Geometry/whistler2026existence -->
# Paired walk orbits and orientation

## Locator

The source is William Whistler's *Existence of transition systems with
orientations*, in `Vilin97/lean-pool`, revision
`762dd054ea9168a4aba93ae86b536b1bd841ce66`, file
`LeanPool/RegtsSevenster/RS/Novel/Skein/TransitionExists.lean`.

URL: https://github.com/Vilin97/lean-pool/blob/762dd054ea9168a4aba93ae86b536b1bd841ce66/LeanPool/RegtsSevenster/RS/Novel/Skein/TransitionExists.lean

Source SHA-256:
`df9680ee85b0b8cd6ad57687b97a701060209d47e28814f8adc023c416c58d70`.
The selected declarations are
`RS.EdgeSubset.TransitionSystem.pairing_not_sameCycle` (line 296) and
`RS.EdgeSubset.TransitionSystem.buildOrientation` (line 400), together with
the conjugation and orbit identities used by those proof leaves.
The pooled source's original repository is
https://github.com/willwhistler/regts-sevenster, as identified in its NOTICE.

The exact source declaration statements are reproduced below. The surrounding
source parameters are `{α : Type} {W : Fragment α} {F : EdgeSubset W}`.

Source ID `RS.EdgeSubset.TransitionSystem.pairing_not_sameCycle`, line 296:

```lean
theorem pairing_not_sameCycle (κ : F.TransitionSystem)
    {f : W.Flag} (hf : f ∈ F.flags) :
    ¬ κ.walkPerm.SameCycle ⟨f, hf⟩
      ⟨W.pairing f, F.pairing_mem f hf⟩
```

Source ID `RS.EdgeSubset.TransitionSystem.buildOrientation`, line 400:

```lean
noncomputable def EdgeSubset.TransitionSystem.buildOrientation
    (κ : F.TransitionSystem) : κ.Orientation
```

## Mathematical statement and argument

Let $D$ be a finite set in any universe, and let $a,t:D\to D$ be
permutations with $a^2=t^2=1$, $a(x)\ne x$ and $t(x)\ne x$ for every
$x\in D$. Neither $a\ne t$ nor disjointness of their pairs is assumed.
Set $w=a\circ t$, with $t$ applied first. Then $x$ and $t(x)$ lie in
different $w$-orbits for every $x$. There exists $b:D\to\{0,1\}$ such that

$$b(a(x))=1-b(x),\qquad b(t(x))=1-b(x).$$

Indeed, $twt=w^{-1}$, so $tw^nt=w^{-n}$ for every integer $n$. If
$w^m(x)=t(x)$ for a positive integer $m$, then
$t(w^{n+m}(x))=w^{-n}(x)$. For $m=2j$, take $n=-j$ to obtain a fixed
point of $t$. For $m=2j+1$, the same substitution gives
$t(w(g))=g$ with $g=w^j(x)$. Applying $t$ gives $w(g)=t(g)$, hence
$a(t(g))=t(g)$, a fixed point of $a$. Both contradict the hypotheses.

Order $D$ by transporting the order on $\operatorname{Fin}(|D|)$ through
a finite-set equivalence. Let $q(x)$ be the minimum of the $w$-orbit of
$x$. The orbit is nonempty because it contains $x$. Its minimum is
constant on that orbit, and $q(t(x))\ne q(x)$ by the disjointness just
proved. Moreover, $w(t(x))=a(x)$ and $w(t(a(x)))=x$, so

$$q(a(x))=q(t(x)),\qquad q(t(a(x)))=q(x).$$

Define $b(x)=1$ exactly when $q(t(x))<q(x)$. The two displayed identities
interchange the unequal minima under $a$, and $t^2=1$ interchanges them
under $t$. Thus both operations flip $b$. If $D$ is empty, the unique
function to $\{0,1\}$ satisfies all conclusions; no orbit minimum is
evaluated without an element $x$.

## Actual face-edge incidence

For a finite tetrahedral face pairing, take
$D=T\times(\operatorname{Fin}4\times\operatorname{Fin}3)$.
Here $t$ switches the two faces incident to the same local edge, while
$a$ crosses the paired whole face using its exact three-slot map.
The inverse slot-map law makes $a$ involutive, and fixed-freeness of the
whole-face pairing makes $a$ fixed-free. The tetrahedral incidence table
makes $t$ involutive and fixed-free. Hence $w=a\circ t$ is the actual
normal-circle walk, in that order.

The Boolean orientation selects one incoming flag at each local edge
occurrence. Its other incident flag is outgoing. Crossing that outgoing
flag gives the selected incoming flag of the next occurrence, yielding
the `entersFace` identity in `FacePairedTriangulation.edgeStars`.
This construction counts occurrences even under self-gluings and repeated
global edge labels. It supplies no geometric realization, common edge
length, minimum-degree condition, or nonlinear exclusion conclusion.

## Source adaptation and direct reuse

The adapted orbit argument is retained while the receiving repository's own
pinned Mathlib lacks an equivalent declaration for arbitrary finite sets with
two independently fixed-point-free involutions, including coincident involutions
and the empty set. When an equivalent declaration is available in that pinned
Mathlib, remove the corresponding source adaptation and directly reuse that
declaration in the actual orientation construction. The retirement condition is
decided against the receiving repository's pinned revision; acceptance into an
upstream Mathlib revision alone does not meet it.

## Copyright and attribution notices

The adapted proof in `D5/S3/Geometry/Hyperideal/EdgeStarTransitions.lean`
retains the source copyright, license and Authors notices:

```text
/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/
```

The following is the applicable attribution text from the pooled source's
NOTICE; it retains the aggregation copyright and the complete
RegtsSevenster entry with its original-license context:

```text
Lean Pool
=========

Copyright the Lean Pool contributors and the respective project authors.

Lean Pool is licensed under the Apache License, Version 2.0. See the LICENSE
file for the full license text.

Lean Pool is an aggregation of third-party Lean 4 formalizations. Each project
under LeanPool/ is the work of its original authors, who retain copyright as
recorded in the per-file headers and in LeanPool/projects.yml. This NOTICE file
records, for every pooled project, the upstream repository it was imported from
and the license under which it was originally published.

--------------------------------------------------------------------------------
Projects originally licensed under the Apache License, Version 2.0
--------------------------------------------------------------------------------

These projects were imported from repositories already licensed under the
Apache License, Version 2.0, and are redistributed here under the same license.

  LeanPool/RegtsSevenster            https://github.com/willwhistler/regts-sevenster
```

The NOTICE contains one RegtsSevenster entry, in its Apache-2.0 section.
Its MIT, relicensing and additional-attribution sections concern other
projects. `NOTICE.extra.yml` contains no RegtsSevenster entry. The material
adapted here consists of the named orientation proof leaves and their
conjugation/orbit arguments from `TransitionExists.lean`; no other pooled
project's source or additional-attribution material is included.

The immutable notice sources are
https://github.com/Vilin97/lean-pool/blob/762dd054ea9168a4aba93ae86b536b1bd841ce66/NOTICE
and
https://github.com/Vilin97/lean-pool/blob/762dd054ea9168a4aba93ae86b536b1bd841ce66/NOTICE.extra.yml.
Their SHA-256 values are respectively
`befa4919716c32d1edc7512e4ea76917c90ee5aec74b513a9fda3bb7ba97c923`
and
`41b9d8eeedee68df9f184965d831c57b9d29f0ea9d3932517b84c7bdd8d81465`.

## Apache License, Version 2.0

The complete source LICENSE follows, including its application appendix.
Its immutable source is
https://github.com/Vilin97/lean-pool/blob/762dd054ea9168a4aba93ae86b536b1bd841ce66/LICENSE,
with SHA-256
`c95bae1d1ce0235ecccd3560b772ec1efb97f348a79f0fbe0a634f0c2ccefe2c`.

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
