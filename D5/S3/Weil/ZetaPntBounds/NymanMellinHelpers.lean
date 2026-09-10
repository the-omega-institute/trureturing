/- GID: D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/NymanMellinHelpers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Live prerequisites of the licensed fractional Mellin source port. -/

/-
Source port: jrgochan/prime, commit ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2.
Copyright 2026 Jason Robert Gochanour. Licensed under Apache-2.0.
The complete upstream license is retained in NymanMellinHelpers.lean.
Modified by trureturing, 2026-09-08: trimmed imports and unused declarations,
routed namespaces, current-pin API adaptation, exact prerequisite reuse.
Retirement: when this repository's installed future mathlib pin contains an
equivalent declaration, use it directly in new content; any frozen port remains
subject to the repository's frozen-content migration rules.
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
      copyright notice that is included in or attached to the work.

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
      submitted to the Licensor for inclusion in the Work by the copyright owner
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
      on behalf of whom a Contribution has been received by the Licensor and
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
          within such NOTICE file, excluding any notices that do not
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

   Copyright 2026 Jason Robert Gochanour

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

import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

noncomputable section
open Complex Real MeasureTheory Set Filter Topology
namespace D5.S3.Weil.ZetaPntBounds.NymanMellinHelpers

private lemma norm_ofReal_cpow (x : ℝ) (hx : 0 < x) (s : ℂ) :
    ‖(x : ℂ) ^ s‖ = x ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hx s

open Topology in
/-- (N+1)^{1-σ} → 0 for σ > 1, via `tendsto_rpow_neg_atTop`. -/
private lemma rpow_neg_tendsto' (σ : ℝ) (hσ : 1 < σ) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (1 - σ)) atTop (nhds 0) := by
  have hp : 0 < σ - 1 := by linarith
  have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h2 := (tendsto_rpow_neg_atTop hp).comp h1
  refine h2.congr (fun N => ?_)
  simp only [Function.comp]; congr 1; ring

open Topology in
/-- N·(1/(N+1))^s → 0 as N → ∞ for Re(s) > 1.
    Proof: ‖N·(1/(N+1))^s‖ ≤ (N+1)^{1-Re(s)} → 0 by squeeze. -/
lemma tail_vanishes (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => (↑N : ℂ) * (↑(1/((N:ℝ)+1)) : ℂ) ^ s) atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have h_tail := (NormedAddGroup.tendsto_nhds_zero.mp) (rpow_neg_tendsto' s.re hs) ε hε
  filter_upwards [h_tail] with N hN
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  calc ‖(↑N : ℂ) * (↑(1/((N:ℝ)+1)) : ℂ) ^ s‖
      = (N : ℝ) * ‖(↑(1/((N:ℝ)+1)) : ℂ) ^ s‖ := by
        rw [norm_mul, Complex.norm_natCast]
    _ = (N : ℝ) * (1 / ((N : ℝ) + 1)) ^ s.re := by
        rw [norm_ofReal_cpow _ (by positivity) _]
    _ ≤ ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1)) ^ s.re := by
        apply mul_le_mul_of_nonneg_right _
          (rpow_nonneg (by positivity : (0:ℝ) ≤ 1/((N:ℝ)+1)) s.re)
        show (N : ℝ) ≤ (N : ℝ) + 1; linarith
    _ = ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ (-s.re) := by
        congr 1; rw [one_div]
        rw [inv_rpow (by positivity : (0:ℝ) ≤ (N:ℝ)+1), rpow_neg (by positivity)]
    _ = ((N : ℝ) + 1) ^ (1 - s.re) := by
        rw [mul_comm, ← rpow_add_one (ne_of_gt hN1)]; congr 1; ring
    _ ≤ ‖((N : ℝ) + 1) ^ (1 - s.re)‖ := le_norm_self _
    _ < ε := hN

open Topology in
/-- Partial sums of ζ(s) converge: ∑_{n=0}^{N-1} 1/((n+1)^s) → ζ(s). -/
lemma partial_zeta_tendsto (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, 1 / (↑((n:ℝ)+1) : ℂ) ^ s)
      atTop (nhds (riemannZeta s)) := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  have h0 : (1 : ℂ) / (0 : ℂ) ^ s = 0 := by
    rw [zero_cpow (by intro h; rw [h, zero_re] at hs; linarith), div_zero]
  have hS := summable_one_div_nat_cpow.mpr hs
  have hH := hS.hasSum.tendsto_sum_nat
  apply Filter.Tendsto.congr (fun N => _) (hH.comp (tendsto_add_atTop_nat 1))
  intro N; simp only [Function.comp]
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, h0, add_zero]
  congr 1; ext n; congr 1; push_cast; ring


/-- The upstream quotient-power API, bound to the installed mathlib theorem. -/
lemma ofReal_div_cpow (k n : ℕ) (_hk : 1 ≤ k) (_hn : 1 ≤ n) (s : ℂ) :
    (↑((k:ℝ)/(n:ℝ)) : ℂ) ^ s = (↑(k:ℝ) : ℂ) ^ s * (↑(n:ℝ) : ℂ) ^ (-s) := by
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg (Nat.cast_nonneg k)
    (Nat.cast_nonneg n), div_eq_mul_inv, Complex.cpow_neg]

/-- Restricted Mellin transform, copied from upstream Basic.lean. -/
def mellinRestricted (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) * f t

/-- Fractional basis, copied from upstream Basic.lean. -/
def fractBasisC (k : ℕ) (x : ℝ) : ℂ :=
  (↑(Int.fract ((k : ℝ) / x)) : ℂ)

end D5.S3.Weil.ZetaPntBounds.NymanMellinHelpers
