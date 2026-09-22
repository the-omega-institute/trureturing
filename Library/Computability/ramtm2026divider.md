---
bibkey: ramtm2026divider
authors: Szymon Toruńczyk and Codex 5.6
year: 2026
title: "Computability and polynomial-time equivalence of Turing machines and word RAMs"
doi: null
url: https://github.com/szymtor/RAM-TM/tree/6fe5a3d94f6c2da46cc2c5ab98cd36997b130737
claim: "The fixed Boolean-stack restoring divider has exact positive-divisor quotient and remainder semantics with a quadratic source-step runtime."
strata_touched:
  - D5/S0/Computability/PhysicalDivider/WordArithmetic
  - D5/S0/Computability/PhysicalDivider/Machine
  - D5/S0/Computability/PhysicalDivider/Inspection
  - D5/S0/Computability/PhysicalDivider/Shift
  - D5/S0/Computability/PhysicalDivider/SubtractLoops
  - D5/S0/Computability/PhysicalDivider/Finalize
  - D5/S0/Computability/PhysicalDivider/Rounds
  - D5/S0/Computability/PhysicalDivider/Positive
  - D5/S0/Computability/PhysicalDivider/StackGrowth
  - D5/S0/Computability/PhysicalDivider/ArithmeticExecution
  - D5/S0/Computability/PhysicalDivider/CallExecution
license: Apache-2.0
triage: anchor
---

# Boolean-stack restoring division

The source is RAM-TM commit `6fe5a3d94f6c2da46cc2c5ab98cd36997b130737`.
Its `manifest.yaml` credits Szymon Toruńczyk and Codex 5.6. The retained source
files contain no additional copyright notice. The complete upstream license
is reproduced below; the source archive contains no NOTICE file. No Lax13
source is included: it is absent from the selected declaration closure.

Upstream pins are Lean `v4.30.0` and Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. These files use this repository's
Lean `v4.33.0` and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
The original namespace `Lax51Proofs.RamToTM` and substantive proof arguments
are preserved. Import routing, explicit unfolding of generated defaults and
`Nat.ModEq`, and equivalent congruence/simplifier syntax are the adaptations.
Merely binding helper proofs are placed locally in their original consumers,
with source locations retained at each insertion.

The arithmetic theorem reaches the source `.done` configuration. It is not
a theorem about physical bit microsteps, reusable physical return frames,
or all-prefix physical storage. The stack-growth theorem must be applied
within short rounds when a linear width bound is needed.

Retirement condition: when this repository's own adopted Mathlib pin provides
equivalent declarations, consumers should use those declarations directly.
Any retirement or migration remains subject to the repository's frozen-content
rules. Acceptance into a different or hypothetical Mathlib revision is not
the retirement condition.

The physical call proof also retains the `bitsValue_append_false` argument
from `WordOperations.lean:37-41` locally to identify the executed padding.
The inverse `fixedBits_bitsValue` supplies the fixed-word equality; no additional
arithmetic declaration is introduced.

## Exact source files

All source paths below are relative to the immutable repository root.

| Source | SHA-256 |
| --- | --- |
| `proofs/Lax51Proofs/RamToTM/DivideMacro.lean` | `aed37971b87b95081105db72edf38148289d3de3e4267bf08d4d033b05c9e207` |
| `proofs/Lax51Proofs/RamToTM/FixedWord.lean` | `1fc582175bda92a59e75bba1eaebd66ececd526a56e3a3544f802b81b7ac1281` |
| `proofs/Lax51Proofs/RamToTM/StackGrowthBounds.lean` | `232b639dfd17a66b775ef1998788c469aa8a6ce6de466857be98db7ad0e7189a` |
| `proofs/Lax51Proofs/RamToTM/WordOperations.lean` | `35f34cc1a462fa1384d34e55c1f45fe280471d97c8df88e023304dcb1c8085ad` |

## Declaration mapping

Names below are in `Lax51Proofs.RamToTM`. An inline name identifies original proof material retained locally, rather than an additional top-level declaration.

| Local module | Declaration | Original source lines | Inlined source declarations |
| --- | --- | --- | --- |
| `WordArithmetic` | `bitsValue` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:10-12` |  |
| `WordArithmetic` | `fixedBits` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:15-17` |  |
| `WordArithmetic` | `fixedBits_length` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:19-20` |  |
| `WordArithmetic` | `bitsValue_fixedBits` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:41-47` | `bit_mod_two_pow` |
| `WordArithmetic` | `fullSubtractor` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:215-217` |  |
| `WordArithmetic` | `subBits` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:224-228` |  |
| `WordArithmetic` | `subBorrowOut` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:230-233` |  |
| `WordArithmetic` | `subBits_length_of_eq` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:235-245` |  |
| `WordArithmetic` | `subBits_value_identity` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:247-266` | `fullSubtractor_value` |
| `WordArithmetic` | `fixedBits_sub_borrow` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:300-311` | `fullSubtractor_value`, `sub_borrow_head_tail` |
| `WordArithmetic` | `subBorrowOut_fixed_false` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:322-342` | `fullSubtractor_value`, `sub_borrow_head_tail` |
| `WordArithmetic` | `fixedBits_bitsValue` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:416-421` |  |
| `WordArithmetic` | `fixedBits_take` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:423-430` |  |
| `WordArithmetic` | `shiftInBit` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:439-441` |  |
| `WordArithmetic` | `fixedBits_zero` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:473-475` |  |
| `WordArithmetic` | `msbValueFrom` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:542-544` |  |
| `WordArithmetic` | `msbValue` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:546-546` |  |
| `WordArithmetic` | `msbValueFrom_append` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:548-550` |  |
| `WordArithmetic` | `msbValue_reverse` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:552-559` |  |
| `WordArithmetic` | `DivisionScan` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:561-563` |  |
| `WordArithmetic` | `divisionScanStep` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:565-570` |  |
| `WordArithmetic` | `divisionScan` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:572-574` |  |
| `WordArithmetic` | `divisionScan_invariant` | `proofs/Lax51Proofs/RamToTM/FixedWord.lean:626-639` | `divisionScanStep_invariant` |
| `WordArithmetic` | `divisionScan_quotient_length` | `proofs/Lax51Proofs/RamToTM/WordOperations.lean:82-91` |  |
| `Machine` | `DivControl` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:14-21` |  |
| `Machine` | `DivControl.clearHeld` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:23-23` |  |
| `Machine` | `DivControl.diffBit` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:25-26` |  |
| `Machine` | `DivControl.subAdvance` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:28-31` |  |
| `Machine` | `DivStack` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:33-36` |  |
| `Machine` | `DivLabel` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:38-46` |  |
| `Machine` | `divMoveIteration` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:48-54` |  |
| `Machine` | `divDiscardIteration` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:56-61` |  |
| `Machine` | `divMachine` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:63-135` |  |
| `Machine` | `divStacks` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:137-146` |  |
| `Machine` | `divCfg` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:148-154` |  |
| `Machine` | `divInitialCfg` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:156-157` |  |
| `Machine` | `divCleanCfg` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:159-163` |  |
| `Machine` | `divDoneCfg` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:165-168` |  |
| `Machine` | `divPhaseCfg` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:170-178` |  |
| `Machine` | `divSubCfg` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:180-188` |  |
| `Inspection` | `containsTrue` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:190-192` |  |
| `Inspection` | `containsTrue_false_bitsValue_zero` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:207-213` |  |
| `Inspection` | `div_inspect_iterate` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:237-249` | `div_step_inspect_cons` |
| `Inspection` | `div_restore_inspected_iterate` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:274-287` | `div_step_restore_inspected_cons` |
| `Shift` | `div_shiftFirst_iterate` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:385-400` | `div_step_shiftFirst_cons` |
| `Shift` | `div_shiftSecond_iterate` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:441-456` | `div_step_shiftSecond_cons` |
| `Shift` | `div_shift_pipeline` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:470-540` | `div_step_outer_cons`, `div_step_shiftDiscard_cons`, `div_step_shiftFirst_nil`, `div_step_shiftPrepend`, `div_step_shiftSecond_nil` |
| `SubtractLoops` | `div_subtract_iterate` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:567-592` | `div_step_subtract_cons` |
| `SubtractLoops` | `div_restoreDivisor_iterate` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:619-634` | `div_step_restoreDivisor_cons` |
| `SubtractLoops` | `div_discardDifference_iterate` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:676-687` | `div_step_discardDifference_cons` |
| `SubtractLoops` | `div_restoreRemainder_iterate` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:713-726` | `div_step_restoreRemainder_cons` |
| `SubtractLoops` | `div_discardOldRemainder_iterate` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:752-763` | `div_step_discardOldRemainder_cons` |
| `SubtractLoops` | `div_restoreDifference_iterate` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:789-802` | `div_step_restoreDifference_cons` |
| `Finalize` | `div_finalize_true` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:815-868` | `div_step_choose_true`, `div_step_discardDifference_nil`, `div_step_emit`, `div_step_restoreRemainder_nil` |
| `Finalize` | `div_finalize_false` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:870-923` | `div_step_choose_false`, `div_step_discardOldRemainder_nil`, `div_step_emit`, `div_step_restoreDifference_nil` |
| `Finalize` | `div_subtract_pipeline` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:925-990` | `div_step_restoreDivisor_nil`, `div_step_subtract_nil` |
| `Rounds` | `div_round` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:992-1026` | `shiftInBit_length` |
| `Rounds` | `div_round_fixed` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:1028-1069` | `bitsValue_fixedBits_of_lt`, `divisionScan_candidate_lt_extra_bit`, `fixedBits_sub_of_le`, `shiftInBit_fixed`, `subBorrowOut_fixed_eq_decide_lt`, `subBorrowOut_fixed_false_of_le` |
| `Rounds` | `div_rounds_fixed` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:1071-1098` | `divisionScanStep_invariant` |
| `Positive` | `divPositiveRunTime` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:1106-1107` |  |
| `Positive` | `divMachine_positive_correct` | `proofs/Lax51Proofs/RamToTM/DivideMacro.lean:1182-1260` | `bitsValue_fixedBits_of_lt`, `div_step_dispatch_true`, `div_step_inspect_nil`, `div_step_outer_nil`, `div_step_restore_inspected_nil`, `divisionScan_fixed_correct`, `divisionScan_zero_correct` |
| `StackGrowth` | `stmtPushCount` | `proofs/Lax51Proofs/RamToTM/StackGrowthBounds.lean:7-14` |  |
| `StackGrowth` | `stepAux_stack_length_le` | `proofs/Lax51Proofs/RamToTM/StackGrowthBounds.lean:16-48` |  |
| `StackGrowth` | `programPushBound` | `proofs/Lax51Proofs/RamToTM/StackGrowthBounds.lean:50-52` |  |
| `StackGrowth` | `iterate_stack_length_le` | `proofs/Lax51Proofs/RamToTM/StackGrowthBounds.lean:79-112` | `iterate_optionBind_none`, `step_stack_length_le`, `stmtPushCount_le_programPushBound` |

## Full upstream license

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
