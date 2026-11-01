# ClusterAlgebras polygon carrier attribution

This repository adapts the consumed `IsSegment`, `IsSide`, `IsDiagonal`, `Cross`, and
`IsTriangulation` definitions from AxiomMath/ClusterAlgebras revision
`a9174706bce3bcb0fa342b4614f98ef2acb7f91c`, authored by Ashvin A. Swaminathan and
copyright Axiom Math. It also adapts the cyclic-order translation lemmas from
`ClusterAlgebras/TypeA/Polygon.lean` (Alexey Sorokin) and
`ClusterAlgebras/Plabic/CornerTriangulation.lean` (Colin Defant) at that revision.
The consumed carrier definitions and crossing endpoint lemma are owned by
`D5/S3/Geometry/Polygons/PolygonEarSlideGeometry.lean`; the cyclic-order
translation adaptations are owned by
`D5/S3/Geometry/Polygons/PolygonEarSlide.lean`. The ear-slide declarations are
new and the adapted source has been modified for this repository's carrier and
pinned Mathlib.

For each adapted declaration, when an equivalent declaration exists in the
Mathlib revision selected by this repository's `lake-manifest.json`, delete that
adapted declaration and replace its uses with direct references to the selected
Mathlib declaration.

The exact Catalan count cone in
`D5/S3/Geometry/Polygons/PolygonCatalanSupplier.lean` retains the original
copyright and author headers of Ashvin A. Swaminathan and Alexey Sorokin.
The immutable source is https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c.
There is no NOTICE file in its 513-file source tree. The complete LICENSE has
SHA-256 `c95bae1d1ce0235ecccd3560b772ec1efb97f348a79f0fbe0a634f0c2ccefe2c`.
The source pins Lean 4.31.0; this repository selects Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. This is a source transplant.

| Source | Source SHA-256 | Retained source lines |
| --- | --- | --- |
| `ClusterAlgebras/PolygonTriangulation.lean` | `55028ccea628bbb03a4a280ea592312b73a5556e8778eb0e233f560925bf7274` | 47–50, 56–83, 88–95, 143–153 |
| `ClusterAlgebras/TypeA/Catalan.lean` | `a2619b6452e3915dcd11a4d77b1ffb3eee874760369a3fc3ed2c301a51334d82` | 27–46 |
| `ClusterAlgebras/TypeA/Interval.lean` | `f634c80fe40b42acfb3ccbd8335fbfde1bd8d97515471732275873f04ea9faeb` | 51–555 |
| `ClusterAlgebras/TypeA/Polygon.lean` | `a9308cdc283b71be372d254ee8098700188e8569017d869f5b65769d54956364` | 62–67, 74–239, 286–304, 347–387, 415–458 |
| `ClusterAlgebras/TypeA/Flips.lean` | `0d9969e370379d31abb3248e5e6dad19404e621c69fb90309ef2e6adf06481f7` | 535–548 |

Only module/import/public/attribute and namespace-boundary metadata are
adapted. Original declaration names and proof bodies are retained. Fan declarations are excluded from this count cone. The 32 additional
flip-only declarations have the separate owner specified below. The consumer identifies the complete original
triangulation carrier by the identity on chord sets and applies
`ClusterAlgebras.TypeA.encard_setOf_isTriangulation`; `catalanNumber` is
extensionally and definitionally Mathlib's `catalan`.

The flip source owner is
`D5/S3/Geometry/Polygons/PolygonTraceFlip.lean`. It imports the sole shared
supplier `PolygonCatalanSupplier` and retains only the following 32 additional
declarations, with the original `ClusterAlgebras` identities and exact source
texts (excluding the final line terminator). The count owner's 69 declarations
and this flip-only set have 101 unique identities: the original 75-declaration
flip cone shares 43 identities with the count cone. No shared declaration is
copied into the flip owner. These source-ownership statements do not assert
integration or verification of a dependent module.

The flip-only source attribution is Copyright (c) 2026 Axiom Math;
Ashvin A. Swaminathan (`PolygonTriangulation.lean`) and Alexey Sorokin
(`TypeA/Polygon.lean`, `FiniteType/External.lean`). The receiver-pinned
Mathlib replacement condition above also applies to every retained flip-only
declaration. Module, import, public-section and attribute metadata are adapted;
the declaration names and proof bodies in this table are exact licensed reuse.
The local conditioned trace construction and injective reconstruction are
separate repository mathematics, not part of the source transplant.

| Flip-only source | Source SHA-256 |
| --- | --- |
| `ClusterAlgebras/FiniteType/External.lean` | `f6198da90d8a36ed9e34fad2a104a6f7470ba56ecbc6db00651299a64cc806b3` |
| `ClusterAlgebras/PolygonTriangulation.lean` | `55028ccea628bbb03a4a280ea592312b73a5556e8778eb0e233f560925bf7274` |
| `ClusterAlgebras/TypeA/Polygon.lean` | `a9308cdc283b71be372d254ee8098700188e8569017d869f5b65769d54956364` |

| Original identity | Source and inclusive lines | Exact declaration SHA-256 |
| --- | --- | --- |
| `ClusterAlgebras.sbtw_rotate_four` | `ClusterAlgebras/PolygonTriangulation.lean` 101–105 | `6e0fedc2b33d0748958aab6763d286325e1b7291118bc3b5684f7ee2b9b51b43` |
| `ClusterAlgebras.Cross.symm` | `ClusterAlgebras/PolygonTriangulation.lean` 108–112 | `ecb1d08006804127e30cea6426802891b8dc7f1b545c903f40d240c617586292` |
| `ClusterAlgebras.segments` | `ClusterAlgebras/PolygonTriangulation.lean` 157–158 | `c6dcfd3f379629e5547ba74439738c247c03a8b9147228e011e713243955e4e1` |
| `ClusterAlgebras.mem_segments` | `ClusterAlgebras/PolygonTriangulation.lean` 162–164 | `a2adeacd889f0f4dabec6aecbc5779de6e65286d093ca17136b1076e2aa3f976` |
| `ClusterAlgebras.flipTriangulation` | `ClusterAlgebras/FiniteType/External.lean` 55–57 | `c89b2bf15e3975e66a7fc82d8dc1b2fa1ee52c7cba381d514ad07d13db9a0ee0` |
| `ClusterAlgebras.IsFlipReplacement` | `ClusterAlgebras/FiniteType/External.lean` 63–65 | `06e6979319283946aa41e060464d1cf2f91d450c39fc4fcf2ca2b3b4f286cfc7` |
| `ClusterAlgebras.TypeA.not_cross_self` | `ClusterAlgebras/TypeA/Polygon.lean` 243–246 | `d8239b2c8369766d18cb7b0f270aeeb756075a4d0a5d2c5a88b29674df39caf5` |
| `ClusterAlgebras.TypeA.basePos_self` | `ClusterAlgebras/TypeA/Polygon.lean` 260–261 | `0021bc35fbd60f9e8128d0ea6370697e0650d617b4cc58d4b6e724bdd0e3fd92` |
| `ClusterAlgebras.TypeA.basePos_self_lt_of_ne` | `ClusterAlgebras/TypeA/Polygon.lean` 264–267 | `08beb3b6115db1ad34dcfab111fbd19720d5b2c1353de0100f9bca1c1c78d9ef` |
| `ClusterAlgebras.TypeA.sbtw_iff_basePos` | `ClusterAlgebras/TypeA/Polygon.lean` 272–275 | `6d2f67d866993642407944312cf8bdfd699ed50688361ebf1a859ce85f4680fb` |
| `ClusterAlgebras.TypeA.bijOn_basePosSeg_isSide` | `ClusterAlgebras/TypeA/Polygon.lean` 316–345 | `ce5103c51bdf9913aa1b7190e1d18e7e47a9fb497bbc23df0076a56992ea9afa` |
| `ClusterAlgebras.TypeA.not_cross_of_isSide` | `ClusterAlgebras/TypeA/Polygon.lean` 396–403 | `3160b0ffa5459fdd761225975a8f1e251980efaa0a735456d4333bfc23e77ac1` |
| `ClusterAlgebras.TypeA.IsTriangulation.not_cross` | `ClusterAlgebras/TypeA/Polygon.lean` 407–413 | `6b712320d0f1b927e8f1d9ad356af4064c08c45da92ef0da61cceff513184c9c` |
| `ClusterAlgebras.TypeA.mem_segments_iff_basePosSeg` | `ClusterAlgebras/TypeA/Polygon.lean` 463–471 | `7dcc9301f2ecd0931a68c14a65653e5b37a0996c5a3fd6704db6e79c571833fb` |
| `ClusterAlgebras.TypeA.isSegment_mk_of_ne` | `ClusterAlgebras/TypeA/Polygon.lean` 477–478 | `be5581a41bda8276c17f18583831bcfa4c333c9da2d3676742dd9515db9fc3df` |
| `ClusterAlgebras.TypeA.mem_segments_iff_of_basePos_lt` | `ClusterAlgebras/TypeA/Polygon.lean` 482–486 | `6e094127bf5c2aae353cbd3e630e8318bad1264c89eb88f51ee9cff378b49bd1` |
| `ClusterAlgebras.TypeA.IsTriangulation.existsUnique_apex` | `ClusterAlgebras/TypeA/Polygon.lean` 492–521 | `75e69cd9b7dc0388dace468c9ed82ae808d8416db093f02772b302496f32b7c1` |
| `ClusterAlgebras.TypeA.quadrilateral_basePos` | `ClusterAlgebras/TypeA/Polygon.lean` 531–540 | `05b45a5229561c70bd633cb31e92563f348be00251911499ec9c0ae216ed76a1` |
| `ClusterAlgebras.TypeA.quadrilateral_cross` | `ClusterAlgebras/TypeA/Polygon.lean` 545–554 | `a9bee7496829d13974b4b1a77aecaad00354d6281e78448c4ed6b03bef839c2f` |
| `ClusterAlgebras.TypeA.cross_mk_of_interleave` | `ClusterAlgebras/TypeA/Polygon.lean` 583–588 | `dca2abcc45390c313879296bc86fe1f6aea02d0ee64556e14bcf48b032533fbe` |
| `ClusterAlgebras.TypeA.quadrilateral_cross_left_of_basePos` | `ClusterAlgebras/TypeA/Polygon.lean` 591–607 | `ab0b6538ed35d054b54b4d9c5ab10ad9ea7ea840b99b517d4ce3d9f50bb3dfe6` |
| `ClusterAlgebras.TypeA.quadrilateral_cross_right_of_basePos` | `ClusterAlgebras/TypeA/Polygon.lean` 611–630 | `af6dd2f003cd53ca9e0ae7056c6dbeffeb885d2ffb0a7d1f6fc9e04170cdb932` |
| `ClusterAlgebras.TypeA.quadrilateral_cross_left` | `ClusterAlgebras/TypeA/Polygon.lean` 635–646 | `23d4f4a97227224a68317a5e4b89307829881962f4379e6ef27f916243a378f1` |
| `ClusterAlgebras.TypeA.quadrilateral_cross_right` | `ClusterAlgebras/TypeA/Polygon.lean` 651–664 | `e9cd3b8f75a26486f998e899a24604fdb022692d898c6a7fa03f3a3eecf5edf4` |
| `ClusterAlgebras.TypeA.IsFlipQuadrilateral` | `ClusterAlgebras/TypeA/Polygon.lean` 674–676 | `33d00c634af9ba8d917bf290d871d42a020a9f74f093d83c76aada3b705cafcb` |
| `ClusterAlgebras.TypeA.IsDiagonal.exists_sbtw` | `ClusterAlgebras/TypeA/Polygon.lean` 681–689 | `180cc0a13d06e253c81a3a38084d270764518c86bfa0a253df138bc1204ddb83` |
| `ClusterAlgebras.TypeA.mem_segments_flipTriangulation` | `ClusterAlgebras/TypeA/Polygon.lean` 692–696 | `2b2d4a551319cda3bdbe41042b19bf919b2be27dd749d96609c2ee43c3a07d7c` |
| `ClusterAlgebras.TypeA.IsFlipQuadrilateral.rim_ne` | `ClusterAlgebras/TypeA/Polygon.lean` 699–704 | `ddbdecd2ca0deeb9a23f9bb55ab2d395ee1b92633b91c32fb2f8a2c3398b9769` |
| `ClusterAlgebras.TypeA.IsTriangulation.existsUnique_apex_of_mem` | `ClusterAlgebras/TypeA/Polygon.lean` 710–718 | `f91158540de413a73c337985ade78709b0bc310db962b1394f7de1cc1c910854` |
| `ClusterAlgebras.TypeA.IsFlipQuadrilateral.isFlipReplacement` | `ClusterAlgebras/TypeA/Polygon.lean` 723–762 | `561d403614d62d665eb01761ecf43715de363faca4e4dab6e8d110b72c576a4f` |
| `ClusterAlgebras.TypeA.IsFlipQuadrilateral.eq_of_isFlipReplacement` | `ClusterAlgebras/TypeA/Polygon.lean` 766–784 | `3f3331173e5bae2426a5fc09bc0b3ec1850456355f14c6f85c7748d0bb6f4123` |
| `ClusterAlgebras.TypeA.IsTriangulation.existsUnique_isFlipReplacement` | `ClusterAlgebras/TypeA/Polygon.lean` 847–854 | `5f423818cf2356a226295a749c233fe6e3ab454cdcbc92338a1d5cefc0af8d35` |

The adapted source is distributed under the Apache License, Version 2.0 below.

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
