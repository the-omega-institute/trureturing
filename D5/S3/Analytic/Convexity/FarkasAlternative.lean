/- GID: D5/S3/Analytic/Convexity/FarkasAlternative
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/FarkasAlternative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite Bartl construction yields equality and inequality alternatives over ordered scalars. -/

/-
Source: madvorak/duality, revision 7e6502ab40b9ea7d42bd2eadc115b6a8b653392f.
https://github.com/madvorak/duality/tree/7e6502ab40b9ea7d42bd2eadc115b6a8b653392f
Original files: Common.lean, FarkasBartl.lean, FarkasBasic.lean.
The mathematical source accompanies the work of Martin Dvorak and Vladimir Kolmogorov.
Modified for Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d:
namespaces and theorem names, unbundled ordered algebra, current notation and APIs,
local normalization in the original coordinate-elimination proof,
and removal of unused declarations and the diagnostic Linters import.
The mathematical constructions and quantified contracts are retained.
Retirement: replace with a native declaration at the Mathlib revision actually
adopted by this repository only after that declaration's exact type and direct
instantiation preserve these ordered-scalar and extended-coefficient contracts,
including finite primal/dual attainment and the standard axiom closure.
An upstream acceptance or a declaration on an unadopted revision is insufficient.

Apache-2.0: full upstream LICENSE (including its appendix) follows verbatim.
-/
/-
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
-/
/-
The following full Apache-2.0 text is the historical/current Mathlib license,
retained for the EReal source attribution chain used by ExtendedFarkas.
-/
/-
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
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Sum
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace D5.S3.Analytic.Convexity.FarkasAlternative

noncomputable section

private def withoutLastMap {m : ℕ} {R W : Type*} [Semiring R] [AddCommMonoid W] [Module R W]
    (A : W →ₗ[R] Fin m.succ → R) :
    W →ₗ[R] Fin m → R :=
  ⟨⟨
    fun w : W => fun i : Fin m => A w i.castSucc,
  by
    intros
    ext
    simp
  ⟩,
  by
    intros
    ext
    simp
  ⟩

prefix:max "▀" => withoutLastMap

private def auxLinMaps {m : ℕ} {R W : Type*} [Ring R] [AddCommMonoid W] [Module R W]
    (A : W →ₗ[R] Fin m.succ → R) (y : W) :
    W →ₗ[R] Fin m → R :=
  ⟨⟨
    ▀A - (A · ⟨m, m.lt_add_one⟩ • ▀A y),
  by
    intros
    ext
    simp only [withoutLastMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, map_add, smul_eq_mul, add_mul]
    abel
  ⟩,
  by
    intros
    ext
    simp [withoutLastMap, mul_sub, mul_assoc]
  ⟩

private def auxLinMap {m : ℕ} {R V W : Type*} [Semiring R] [AddCommGroup V] [Module R V] [AddCommMonoid W] [Module R W]
    (A : W →ₗ[R] Fin m.succ → R) (b : W →ₗ[R] V) (y : W) : W →ₗ[R] V :=
  ⟨⟨
    b - (A · ⟨m, m.lt_add_one⟩ • b y),
  by
    intros
    simp only [Pi.add_apply, Pi.sub_apply, map_add, add_smul]
    abel
  ⟩,
  by
    intros
    -- note that `simp` does not work here
    simp only [Pi.smul_apply, Pi.sub_apply, LinearMapClass.map_smul, RingHom.id_apply, smul_sub, IsScalarTower.smul_assoc]
  ⟩

variable {R V W : Type*}

theorem fin_farkas_bartl {n : ℕ} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module R V] [PosSMulMono R V] [AddCommGroup W] [Module R W]
    (A : W →ₗ[R] Fin n → R) (b : W →ₗ[R] V) :
    (∃ x : Fin n → V, 0 ≤ x ∧ ∀ w : W, ∑ j : Fin n, A w j • x j = b w) ≠ (∃ y : W, 0 ≤ A y ∧ b y < 0) := by
  classical
  have industep_farkas_bartl {m : ℕ} (ih : ∀ A₀ : W →ₗ[R] Fin m → R, ∀ b₀ : W →ₗ[R] V,
        (∀ y₀ : W, 0 ≤ A₀ y₀ → 0 ≤ b₀ y₀) →
          (∃ x₀ : Fin m → V, 0 ≤ x₀ ∧ ∀ w₀ : W, ∑ i₀ : Fin m, A₀ w₀ i₀ • x₀ i₀ = b₀ w₀))
      {A : W →ₗ[R] Fin m.succ → R} {b : W →ₗ[R] V} (hAb : ∀ y : W, 0 ≤ A y → 0 ≤ b y) :
      ∃ x : Fin m.succ → V, 0 ≤ x ∧ ∀ w : W, ∑ i : Fin m.succ, A w i • x i = b w := by
    classical
    have filter_yielding_singleton_attach_sum {m : ℕ}
        (f : Fin m.succ → R) (v : V) :
        ∑ j ∈ (Finset.univ.filter (fun i : Fin m.succ => ¬(i.val < m))).attach, f j.val • v =
        f ⟨m, m.lt_add_one⟩ • v := by
      classical
      have singlet : Finset.univ.filter (fun i : Fin m.succ => ¬(i.val < m)) = {⟨m, m.lt_add_one⟩}
      · rw [Finset.ext_iff]
        intro i
        constructor <;> rw [Finset.mem_singleton, Finset.mem_filter] <;> intro hi
        · have him := hi.right
          push Not at him
          exact Fin.ext (le_antisymm (Nat.le_of_lt_succ i.isLt) him)
        · refine ⟨Finset.mem_univ i, ?_⟩
          rw [hi]
          push Not
          rfl
      rw [singlet, Finset.sum_attach _ (fun j : Fin m.succ => f j • v), Finset.sum_singleton]
    have impossible_index {m : ℕ} {i : Fin m.succ} (hi : ¬(i.val < m)) (i_neq_m : i ≠ ⟨m, m.lt_add_one⟩) : False := by
      classical
      push Not at hi
      exact i_neq_m (Fin.ext (le_antisymm (Fin.succ_le_succ_iff.mp i.isLt) hi))
    have finishing_piece {m : ℕ}
        {A : W →ₗ[R] Fin m.succ → R} {w : W} {x : Fin m → V} :
        ∑ i : Fin m, ▀A w i • x i =
        ∑ i : { j : Fin m.succ // j ∈ Finset.univ.filter (·.val < m) }, A w i.val • x ⟨i.val.val, by aesop⟩ := by
      classical
      apply
        Finset.sum_bij'
          (fun i : Fin m => fun _ => (⟨⟨i.val, by omega⟩, by aesop⟩ : { a : Fin m.succ // a ∈ Finset.univ.filter (·.val < m) }))
          (fun i' : { a : Fin m.succ // a ∈ Finset.univ.filter (·.val < m) } => fun _ => ⟨i'.val.val, by aesop⟩)
          (by aesop)
          (by aesop)
          (by aesop)
          (by aesop)
      intros
      rfl
    if
      is_easy : ∀ y : W, 0 ≤ ▀A y → 0 ≤ b y
    then
      obtain ⟨x, hx, hxb⟩ := ih ▀A b is_easy
      use (fun i : Fin m.succ => if hi : i.val < m then x ⟨i.val, hi⟩ else 0)
      constructor
      · intro i
        if hi : i.val < m then
          clear * - hi hx
          aesop
        else
          simp [hi]
      · intro w
        simp_rw [smul_dite, smul_zero]
        rw [Finset.sum_dite, Finset.sum_const_zero, add_zero]
        convert hxb w using 1
        symm
        apply finishing_piece
    else
      push Not at is_easy
      obtain ⟨y', hay', hby'⟩ := is_easy
      let M : Fin m.succ := ⟨m, lt_add_one m⟩ -- the last (new) index
      let y : W := (A y' M)⁻¹ • y' -- rescaled `y'`
      have hAy' : A y' M < 0
      · by_contra! contr
        exact (
          (hAb y' (fun i : Fin m.succ =>
            if hi : i.val < m then
              hay' ⟨i, hi⟩
            else if hiM : i = M then
              hiM ▸ contr
            else
              (impossible_index hi hiM).elim
          )).trans_lt hby'
        ).false
      have hAy : A y M = 1
      · convert inv_mul_cancel₀ hAy'.ne
        simp [y]
      have hAA : ∀ w : W, A (w - (A w M • y)) M = 0
      · intro w
        simp [hAy]
      have hbA : ∀ w : W, 0 ≤ ▀A (w - (A w M • y)) → 0 ≤ b (w - (A w M • y))
      · intro w hw
        apply hAb
        intro i
        if hi : i.val < m then
          exact hw ⟨i, hi⟩
        else if hiM : i = M then
          rw [hiM, hAA, Pi.zero_apply]
        else
          exfalso
          exact impossible_index hi hiM
      have hbAb : ∀ w : W, 0 ≤ (▀A - (A · M • ▀A y)) w → 0 ≤ (b - (A · M • b y)) w
      · simpa using hbA
      obtain ⟨x', hx', hxb'⟩ := ih (auxLinMaps A y) (auxLinMap A b y) hbAb
      use (fun i : Fin m.succ => if hi : i.val < m then x' ⟨i.val, hi⟩ else b y - ∑ i : Fin m, ▀A y i • x' i)
      constructor
      · intro i
        if hi : i.val < m then
          clear * - hi hx'
          aesop
        else
          have hAy'' : (A y' M)⁻¹ ≤ 0
          · exact (inv_neg''.mpr hAy').le
          have hay : ▀A y ≤ 0
          · simpa [y] using smul_nonpos_of_nonpos_of_nonneg hAy'' hay'
          have hby : 0 ≤ b y
          · simpa [y] using smul_nonneg_of_nonpos_of_nonpos hAy'' hby'.le
          simpa [hi] using (Finset.sum_nonpos (fun i _ => smul_nonpos_of_nonpos_of_nonneg (hay i) (hx' i))).trans hby
      · intro w
        have haAa : ∑ i : Fin m, (▀A w i - A w M * ▀A y i) • x' i = b w - A w M • b y
        · simpa [auxLinMaps, auxLinMap] using hxb' w
        rw [←add_eq_of_eq_sub haAa]
        simp_rw [smul_dite]
        rw [Finset.sum_dite]
        erw [filter_yielding_singleton_attach_sum]
        simp_rw [sub_smul]
        rw [Finset.sum_sub_distrib]
        simp_rw [←smul_smul, ←Finset.smul_sum]
        symm
        rw [smul_sub, finishing_piece]
        apply add_comm_sub
  have neq_of_iff_neg {P Q : Prop} (h : P ↔ ¬Q) : P ≠ Q := by tauto
  apply neq_of_iff_neg
  push Not
  refine ⟨fun ⟨x, hx, hb⟩ y hy => hb y ▸ Finset.sum_nonneg (fun i _ => smul_nonneg (hy i) (hx i)), ?_⟩
  induction n generalizing b with -- note that `A` is "generalized" automatically
  | zero =>
    have A_tauto (w : W) : 0 ≤ A w
    · intro j
      exfalso
      apply Nat.not_lt_zero
      exact j.isLt
    intro hAb
    refine ⟨0, le_refl 0, fun w : W => ?_⟩
    simp_rw [Pi.zero_apply, smul_zero, Finset.sum_const_zero]
    apply le_antisymm (hAb w (A_tauto w))
    simpa using hAb (-w) (A_tauto (-w))
  | succ m ih =>
    exact industep_farkas_bartl ih

theorem fintype_farkas_bartl {J : Type*} [Fintype J] [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Module R V] [PosSMulMono R V] [AddCommGroup W] [Module R W]
    (A : W →ₗ[R] J → R) (b : W →ₗ[R] V) :
    (∃ x : J → V, 0 ≤ x ∧ ∀ w : W, ∑ j : J, A w j • x j = b w) ≠ (∃ y : W, 0 ≤ A y ∧ b y < 0) := by
  classical
  convert
    fin_farkas_bartl ⟨⟨fun w : W => fun j' => A w ((Fintype.equivFin J).symm j'), by aesop⟩, by aesop⟩ b
      using 1
  · constructor <;> intro ⟨x, hx, hA⟩
    · use x ∘ (Fintype.equivFin J).invFun
      constructor
      · intro j
        simpa using hx ((Fintype.equivFin J).invFun j)
      · intro w
        convert hA w
        apply Finset.sum_equiv (Fintype.equivFin J).symm <;>
        · intros
          simp
    · use x ∘ (Fintype.equivFin J).toFun
      constructor
      · intro j
        simpa using hx ((Fintype.equivFin J).toFun j)
      · intro w
        convert hA w
        apply Finset.sum_equiv (Fintype.equivFin J) <;>
        · intro
          simp
  · constructor <;> intro ⟨y, hAy, hby⟩ <;> refine ⟨y, fun j => ?_, hby⟩
    · simpa using hAy ((Fintype.equivFin J).invFun j)
    · simpa using hAy ((Fintype.equivFin J).toFun j)

theorem almost_farkas_bartl {J : Type*} [Fintype J] [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup W] [Module R W]
    (A : W →ₗ[R] J → R) (b : W →ₗ[R] R) :
    (∃ x : J → R, 0 ≤ x ∧ ∀ w : W, ∑ j : J, A w j • x j = b w) ≠ (∃ y : W, 0 ≤ A y ∧ b y < 0) :=
  fintype_farkas_bartl A b

theorem coordinate_farkas_bartl {I J : Type*} [Fintype J] [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (A : (I → R) →ₗ[R] J → R) (b : (I → R) →ₗ[R] R) :
    (∃ x : J → R, 0 ≤ x ∧ ∀ w : I → R, ∑ j : J, A w j • x j = b w) ≠ (∃ y : I → R, 0 ≤ A y ∧ b y < 0) :=
  almost_farkas_bartl A b

/- Let's move from linear maps to matrices, which give more familiar
(albeit less general) formulations of the theorems of alternative. -/

variable {I J F : Type*} [Fintype I] [Fintype J] [Field F] [LinearOrder F] [IsStrictOrderedRing F]

open scoped Matrix

macro "finishit" : tactic => `(tactic| -- should be `private macro` which Lean does not allow
  unfold Matrix.mulVec Matrix.vecMul dotProduct <;>
  simp_rw [Finset.sum_mul] <;> rw [Finset.sum_comm] <;>
  congr <;> ext <;> congr <;> ext <;> ring)

/-- A system of linear equalities over nonnegative variables has a solution if and only if
we cannot obtain a contradiction by taking a linear combination of the inequalities. -/
theorem equality_farkas (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, 0 ≤ x ∧ A *ᵥ x = b) ≠ (∃ y : I → F, 0 ≤ Aᵀ *ᵥ y ∧ b ⬝ᵥ y < 0) := by
  classical
  convert
    coordinate_farkas_bartl Aᵀ.mulVecLin ⟨⟨(b ⬝ᵥ ·), dotProduct_add b⟩, (dotProduct_smul · b)⟩
      using 3
  · constructor <;> intro ⟨hx, hAx⟩ <;> refine ⟨hx, ?_⟩
    · intro
      simp
      rw [←hAx]
      finishit
    · simp at hAx
      apply dotProduct_eq
      intro w
      rw [←hAx w]
      finishit
  · rfl

/- Let's move to the "symmetric" variants now. They will also be used in the upcoming extended setting
and in the upcoming theory of linear programming. -/

/-- A system of linear inequalities over nonnegative variables has a solution if and only if
we cannot obtain a contradiction by taking a nonnegative linear combination of the inequalities. -/
theorem inequality_farkas [DecidableEq I] (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, 0 ≤ x ∧ A *ᵥ x ≤ b) ≠ (∃ y : I → F, 0 ≤ y ∧ 0 ≤ Aᵀ *ᵥ y ∧ b ⬝ᵥ y < 0) := by
  classical
  let A' : Matrix I (I ⊕ J) F := Matrix.fromCols 1 A
  convert equality_farkas A' b using 1 <;> constructor
  · intro ⟨x, hx, hAxb⟩
    use Sum.elim (b - A *ᵥ x) x
    constructor
    · rw [Sum.nonneg_elim_iff]
      exact ⟨fun i : I => sub_nonneg_of_le (hAxb i), hx⟩
    · aesop
  · intro ⟨x, hx, hAxb⟩
    use x ∘ Sum.inr
    constructor
    · intro
      apply hx
    · intro i
      have hi := congr_fun hAxb i
      simp [A', Matrix.mulVec, dotProduct, Matrix.fromCols] at hi
      rw [←hi]
      apply le_add_of_nonneg_left
      apply Fintype.sum_nonneg
      rw [Pi.le_def]
      intro
      rw [Pi.zero_apply]
      apply mul_nonneg
      · apply Matrix.zero_le_one_elem
      · apply hx
  · intro ⟨y, hy, hAy, hby⟩
    refine ⟨y, ?_, hby⟩
    intro k
    cases k with
    | inl i => simpa [A', Matrix.mulVec, dotProduct, Matrix.fromCols] using dotProduct_nonneg_of_nonneg (Matrix.zero_le_one_elem · i) hy
    | inr j => apply hAy
  · intro ⟨y, hAy, hby⟩
    have h1Ay : 0 ≤ (Matrix.fromRows (1 : Matrix I I F) Aᵀ *ᵥ y)
    · intro k
      simp only [A', Matrix.transpose_fromCols, Matrix.transpose_one] at hAy
      apply hAy
    refine ⟨y, ?_, fun j : J => h1Ay (Sum.inr j), hby⟩
    intro i
    simpa using h1Ay (Sum.inl i)

/-- A system of linear inequalities over nonnegative variables has a solution if and only if
we cannot obtain a contradiction by taking a nonnegative linear combination of the inequalities;
midly reformulated. -/
theorem inequality_farkas_neg [DecidableEq I] (A : Matrix I J F) (b : I → F) :
    (∃ x : J → F, 0 ≤ x ∧ A *ᵥ x ≤ b) ≠ (∃ y : I → F, 0 ≤ y ∧ -Aᵀ *ᵥ y ≤ 0 ∧ b ⬝ᵥ y < 0) := by
  classical
  convert inequality_farkas A b using 5
  rw [Matrix.neg_mulVec, ←neg_zero]
  constructor <;> intro hAx i <;> simpa using hAx i

end

end D5.S3.Analytic.Convexity.FarkasAlternative
