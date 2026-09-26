---
bibkey: zhao2023algorithm
authors: Yuyang Zhao
year: 2023
title: Algorithm graph interfaces and verified depth-first search, revision ce7dc1da
doi: null
url: https://github.com/astrainfinita/Algorithm/tree/ce7dc1da842c7c5b8096a886d803acfb24d71a67
claim: Finite adjacency interfaces and shared-visited depth-first forest construction with termination, visited-set invariants and reachability correctness.
strata_touched:
  - D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Forest
  - D5/S3/ConceptDynamics/DagSemantics/DepthFirst/ElementAccess
  - D5/S3/ConceptDynamics/DagSemantics/DepthFirst/MultisetView
  - D5/S3/ConceptDynamics/DagSemantics/DepthFirst/ListView
  - D5/S3/ConceptDynamics/DagSemantics/DepthFirst/FiniteSupport
  - D5/S3/ConceptDynamics/DagSemantics/DepthFirst/DefaultDictionary
  - D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Adjacency
  - D5/S3/ConceptDynamics/DagSemantics/DepthFirst/ForestInvariant
  - D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Search
  - D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Postorder
license: Apache-2.0
triage: anchor
---
<!-- GID: D5/L/ConceptDynamics/zhao2023algorithm -->
# zhao2023algorithm

## Verified locator

Immutable source: [astrainfinita/Algorithm](https://github.com/astrainfinita/Algorithm/tree/ce7dc1da842c7c5b8096a886d803acfb24d71a67),
revision `ce7dc1da842c7c5b8096a886d803acfb24d71a67`.
The source pins Lean `v4.33.0` and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
The retained source carries Yuyang Zhao's 2023 and 2024 copyright notices.
The DFinsupp source acknowledges modification from `Mathlib.Data.DFinsupp.Basic`;
that attribution is preserved in FiniteSupport. The upstream distribution has no
NOTICE file. The complete upstream Apache-2.0 license follows below.

## Source excerpts

All target modules are under `D5/S3/ConceptDynamics/DagSemantics/DepthFirst/`.
The hashes identify complete original files; the targets retain selected commands,
not the complete files. The original namespaces, data structures, algorithm and
substantive inductive proofs are retained. Modifications are canonical headers,
import relocation and reduction, pruning unused declarations, and inlining thin
helper proofs at their live uses. Explicit local proof terms replace omitted
elaboration support. Finite-support membership is supplied directly by pinned
Mathlib DFinsupp.mem_support_toFun after reusing the original function and
support-witness fields with the designated default as the local zero. No separate
membership theorem is retained. No independent DFS correctness proof replaces
the source.

| Target | Original file | SHA-256 |
|---|---|---|
| Forest | `Algorithm/Data/Forest.lean` | `7973e7cf6f2c5a49cf7601a54b65a799ff770c2cd2ef42e6e9606fa058ac6a84` |
| ElementAccess | `Algorithm/Data/Classes/GetElem.lean` | `6352d90a50f5967f5ee49af5517ba217935587ab1b7bdcca437558a6fcda9788` |
| MultisetView | `Algorithm/Data/Classes/ToMultiset.lean` | `85e26664252b1446cfa8a8f33a9d98eb90a5222df251febdb2c9d7def0021031` |
| ListView | `Algorithm/Data/Classes/ToList.lean` | `5f56abdfed3a25b00d5b30e5c2245dd6bd4dd81ed465773e5795d00dd5eac49e` |
| FiniteSupport | `Algorithm/Data/DFinsupp/Defs.lean` | `d55408ddbb56e6d34478e16d937e3fb6e9aaa56cb2194ac9f1603cd3bd78f778` |
| DefaultDictionary | `Algorithm/Data/Classes/DefaultDict.lean` | `6f27e7117aa8c03fe1f37d072c229f0fd56f9d9244a80ff28e1233c2dc05a864` |
| Adjacency | `Algorithm/Data/Graph/AdjList.lean` | `58be2504b53361e0e89b5cbeb98cc508a78895d8f0da348670a29ae23989f2d9` |
| ForestInvariant | `Algorithm/Data/Graph/IsDFSForest.lean` | `a04915e24a94a6226afd88c0c855839673debe42b3d5f48078daae269423ba55` |
| Search | `Algorithm/Graph/DFS.lean` | `3318a4986d24eda954cbd3c70b6004ec9e61bb8958b74b00a65edbe3c21d07f7` |

The excerpt contains rooted forests and postorder lists; indexed collection and
finite-support interfaces; the finite vector default dictionary; adjacency,
paths and successor sets; the DFS forest invariant; and the original DFS
recursion with its root-inclusion, visited-inclusion and invariant proofs.
Forest append/preorder, erasure APIs, quotient dictionaries and alternate DFS
implementations are omitted. Derived reachability/specification wrappers are
omitted; their consumers directly apply the invariant theorems and normalize
sets. This is a source transplant with no added Lake package dependency.

Postorder is a repository derivation using these invariant proofs. Its theorem
states that a DFS forest's postorder has no repeated vertices, has exactly the
forest support as its membership set, and any edge from an earlier to a later
output vertex has a return path. If no emitted vertex lies on a nonempty cycle in the full graph, every
emitted dependency precedes its source. With an empty initial visited set,
successor closure allows this assumption to be weakened to acyclicity of
the subgraph induced by emitted vertices. The DFS invariant permits
an initially visited set, so the forest support records newly visited vertices;
coverage of all vertices reachable from supplied roots additionally uses the
algorithm's empty initial visited set and its reachability proofs.

These results describe the Lean graph, collection and recursive algorithm.
They do not establish correspondence with C# collections, string equality,
root sorting, parser input, stack limits or physical execution. Finite tests of
an implementation do not supply that universal refinement.

Retirement condition: when the repository's actual pinned Mathlib supplies
proved-equivalent declarations and their faithful applications compile, replace
this transplant with direct Mathlib imports and uses. A proposed upstream merge
alone does not satisfy this condition.

## License

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
