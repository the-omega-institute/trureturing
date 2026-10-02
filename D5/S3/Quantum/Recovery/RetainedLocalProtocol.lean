/- GID: D5/S3/Quantum/Recovery/RetainedLocalProtocol
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/RetainedLocalProtocol
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Retaining inaccessible Kraus outputs reproduces every actual coarse prefix and terminal on all matrices. -/

/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
/-
Selected-source spectral data and proof-local steps: QuantumInfo/Channels/MatrixMap.lean
(choi_matrix_eq_map_proj, exists_kraus_of_choi_PSD, choi_map_inv).
Immutable source: https://github.com/leanprover-community/physlib/tree/6a09b2d1761a0d4430083045a247eb121d8da260
Adaptation: canonical CP/density interfaces, local protocol data and proof-local
finite-coordinate normalization; no standalone selected-source theorem.
Retirement condition: replace these selected steps by direct applications when
equivalent statements are available in this repository pinned Mathlib;
current pin db584cd6d46c92f209a44c0f1c829460d327499d.
The complete immutable upstream tree contains no NOTICE file.
Full upstream license:
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

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteStateChannel
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Fin.Basic
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace D5.S3.Quantum.Recovery.FiniteLocalProtocol
open scoped BigOperators
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel
variable {A : Type} [Fintype A] [DecidableEq A]
variable {R : Type} [Fintype R] {Feedback : Type}

abbrev Coordinates (d : A → ℕ) := (a : A) → Fin (d a)
abbrev State (R : Type) (d : A → ℕ) := Matrix (R × Coordinates d) (R × Coordinates d) ℂ
abbrev LocalState (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev Rest (R : Type) (d : A → ℕ) (a : A) :=
  R × ((b : { b // b ≠ a }) → Fin (d b))

/-- A spectator (the system and any reference) is never acted upon. -/
noncomputable def inputSplit (R : Type) (d : A → ℕ) (a : A) :
    (R × Coordinates d) ≃ Fin (d a) × Rest R d a :=
  (Equiv.prodCongr (Equiv.refl R) (Equiv.piSplitAt a (fun b => Fin (d b)))).trans
    { toFun := fun x => (x.2.1, x.1, x.2.2)
      invFun := fun x => (x.2.1, x.1, x.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

noncomputable def action {m n : ℕ}
    (φ : CompletelyPositiveMap (CStarMatrix (Fin m) (Fin m) ℂ)
      (CStarMatrix (Fin n) (Fin n) ℂ)) (X : LocalState m) : LocalState n :=
  CStarMatrix.ofMatrix.symm (φ (CStarMatrix.ofMatrix X))

structure Instrument (d : A → ℕ) where
  actor : A
  outcomes : ℕ
  output : Fin outcomes → A → ℕ
  unchanged : ∀ y b, b ≠ actor → output y b = d b
  operation : (y : Fin outcomes) →
    CompletelyPositiveMap (CStarMatrix (Fin (d actor)) (Fin (d actor)) ℂ)
      (CStarMatrix (Fin (output y actor)) (Fin (output y actor)) ℂ)
  trace_preserving : ∀ X : LocalState (d actor),
    ∑ y, Matrix.trace (action (operation y) X) = Matrix.trace X

noncomputable def outputSplit (R : Type) {d : A → ℕ}
    (J : Instrument d) (y : Fin J.outcomes) :
    (R × Coordinates (J.output y)) ≃ Fin (J.output y J.actor) × Rest R d J.actor :=
  (inputSplit R (J.output y) J.actor).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl R)
      (Equiv.piCongrRight (fun b =>
        Equiv.cast (congrArg Fin (J.unchanged y b b.property))))))

variable {R : Type} [Fintype R]

/-- The other holders' row and column coordinates are fixed while the actor's
    entire local matrix is passed to its coarse CP map. No Kraus label occurs. -/
noncomputable def step {d : A → ℕ} (J : Instrument d) (y : Fin J.outcomes)
    (X : State R d) : State R (J.output y) := fun p q =>
  let e := inputSplit R d J.actor
  let f := outputSplit R J y
  action (J.operation y)
    (fun i j => X (e.symm (i, (f p).2)) (e.symm (j, (f q).2))) (f p).1 (f q).1

inductive Tree (Feedback : Type) : (A → ℕ) → Type
  | leaf {d} (feedback : Feedback) : Tree Feedback d
  | node {d} (instrument : Instrument d)
      (child : (y : Fin instrument.outcomes) → Tree Feedback (instrument.output y)) :
        Tree Feedback d

/-- Histories contain precisely observed outcomes. Feedback is attached to leaves. -/
structure Terminal (Feedback R : Type) (A : Type) where
  history : List ℕ
  feedback : Feedback
  dimensions : A → ℕ
  state : State R dimensions

variable {Feedback : Type}

/-- The returned matrices retain all accessible memories. Different terminals
    may have different dimensions. The list enumerates observed histories only. -/
noncomputable def terminalOutputs {d : A → ℕ} :
    Tree Feedback d → State R d → List (Terminal Feedback R A)
  | .leaf f, X => [⟨[], f, d, X⟩]
  | .node J child, X => (List.ofFn (fun y =>
      (terminalOutputs (child y) (step J y X)).map
        (fun z => { z with history := y.val :: z.history }))).flatten

noncomputable def terminalTrace {d : A → ℕ} (T : Tree Feedback d) (X : State R d) : ℂ :=
  ((terminalOutputs T X).map (fun z => Matrix.trace z.state)).sum

/-- Independent local auxiliary states. Their density matrices, rather than
    purification witnesses, are part of the physical protocol data. -/
structure ProductAncillas (A : Type) where
  dimension : A → ℕ
  density : (a : A) →
    D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Fin (dimension a))

/-- Append the independent mixed auxiliaries, leaving the source/reference
    matrix unrestricted. Finite product coordinates are only a local reindexing. -/
noncomputable def appendAncillas {H : A → ℕ} (η : ProductAncillas A)
    (X : State R H) : State R (fun a => H a * η.dimension a) := fun p q =>
  X (p.1, fun a => (finProdFinEquiv.symm (p.2 a)).1)
    (q.1, fun a => (finProdFinEquiv.symm (q.2 a)).1) *
    ∏ a, (η.density a).1 (finProdFinEquiv.symm (p.2 a)).2
      (finProdFinEquiv.symm (q.2 a)).2

structure Protocol (Feedback : Type) (H : A → ℕ) where
  ancillas : ProductAncillas A
  tree : Tree Feedback (fun a => H a * ancillas.dimension a)

noncomputable def Protocol.run {H : A → ℕ} (P : Protocol Feedback H)
    (X : State R H) : List (Terminal Feedback R A) :=
  terminalOutputs P.tree (appendAncillas P.ancillas X)


abbrev Hidden {d : A → ℕ} (J : Instrument d) (y : Fin J.outcomes) :=
  Fin (J.output y J.actor) × Fin (d J.actor)

noncomputable def chosenKraus {d : A → ℕ} (J : Instrument d) (y : Fin J.outcomes) :
    Hidden J y → Matrix (Fin (J.output y J.actor)) (Fin (d J.actor)) ℂ := by
  classical
  let C : Matrix (Hidden J y) (Hidden J y) ℂ :=
    fun p q => action (J.operation y) (Matrix.single p.2 q.2 1) p.1 q.1
  exact fun k i j => if h : C.IsHermitian then
    h.eigenvectorUnitary (i,j) k * (Real.sqrt (h.eigenvalues k) : ℂ) else 0

abbrev RetainedState (R G : Type) (d : A → ℕ) :=
  Matrix ((R × Coordinates d) × G) ((R × Coordinates d) × G) ℂ

noncomputable def traceGarbage {G : Type} [Fintype G] {d : A → ℕ}
    (X : RetainedState R G d) : State R d := fun p q => ∑ g, X (p,g) (q,g)

/-- Coherent local dilation. Old garbage coordinates are passed unchanged to
both input entries; only the new hidden coordinate selects a Kraus operator.
Neither hidden coordinate is an argument of the observed tree's child function. -/
noncomputable def retainedStep {G : Type} {d : A → ℕ}
    (J : Instrument d) (y : Fin J.outcomes) (X : RetainedState R G d) :
    RetainedState R (Hidden J y × G) (J.output y) := fun p q =>
  let e := inputSplit R d J.actor
  let f := outputSplit R J y
  ∑ i, ∑ j, chosenKraus J y p.2.1 (f p.1).1 i *
    X (e.symm (i,(f p.1).2),p.2.2) (e.symm (j,(f q.1).2),q.2.2) *
    star (chosenKraus J y q.2.1 (f q.1).1 j)

/-- Garbage is traced only at leaves, after the whole retained execution.
The accumulating hidden type never changes the observed control tree. -/
noncomputable def retainedOutputs {d : A → ℕ} (T : Tree Feedback d) :
    {G : Type} → [Fintype G] → RetainedState R G d → List (Terminal Feedback R A) :=
  match T with
  | .leaf f => fun X => [⟨[], f, d, traceGarbage X⟩]
  | .node J child => fun X => (List.ofFn (fun y =>
      (retainedOutputs (child y) (retainedStep J y X)).map
        (fun z => { z with history := y.val :: z.history }))).flatten

/-- Every observed prefix, including root and early leaves. -/
noncomputable def coarsePrefixes {d : A → ℕ} (T : Tree Feedback d)
    (X : State R d) : List (Terminal (Option Feedback) R A) :=
  match T with
  | .leaf f => [⟨[], some f, d, X⟩]
  | .node J child => ⟨[], none, d, X⟩ ::
      (List.ofFn (fun y => (coarsePrefixes (child y) (step J y X)).map
        (fun z => { z with history := y.val :: z.history }))).flatten

/-- Prefix observations trace a copy for reporting only. Recursion passes the
untraced retained state to the next edge. -/
noncomputable def retainedPrefixes {d : A → ℕ} (T : Tree Feedback d) :
    {G : Type} → [Fintype G] → RetainedState R G d →
      List (Terminal (Option Feedback) R A) :=
  match T with
  | .leaf f => fun X => [⟨[], some f, d, traceGarbage X⟩]
  | .node J child => fun X => ⟨[], none, d, traceGarbage X⟩ ::
      (List.ofFn (fun y => (retainedPrefixes (child y) (retainedStep J y X)).map
        (fun z => { z with history := y.val :: z.history }))).flatten

/-- All-matrix recursive faithfulness, with arbitrary untouched spectator and
arbitrary initial correlations with finite inaccessible garbage. -/
theorem recursive_coarse_retained {d : A → ℕ} (T : Tree Feedback d) :
    ∀ {G : Type} [Fintype G] (X : RetainedState R G d),
      retainedOutputs T X = terminalOutputs T (traceGarbage X) ∧
      retainedPrefixes T X = coarsePrefixes T (traceGarbage X) ∧
      (match T with
        | .leaf _ => True
        | .node J _ => ∀ y (M : LocalState (d J.actor)),
            action (J.operation y) M = ∑ k,
              chosenKraus J y k * M * (chosenKraus J y k).conjTranspose) := by
  induction T with
  | leaf f => intro G _ X; exact ⟨rfl, rfl, True.intro⟩
  | @node d J child ih =>
    intro G _ X
    have exactK (y : Fin J.outcomes) (M : LocalState (d J.actor)) :
        action (J.operation y) M = ∑ k,
          chosenKraus J y k * M * (chosenKraus J y k).conjTranspose := by
      -- Physlib MatrixMap.choi_matrix_eq_map_proj, exists_kraus_of_choi_PSD
      -- and choi_map_inv, specialized inside the actual recursive edge proof.
      classical
      let m := d J.actor
      let n := J.output y J.actor
      let f : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
        CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
          ((J.operation y).toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
      let C : Matrix (Hidden J y) (Hidden J y) ℂ :=
        fun p q => f (Matrix.single p.2 q.2 1) p.1 q.1
      have cp : PhyslibLeaf.MatrixMap.IsCompletelyPositive f := by
        intro k M hM
        let Z := (flattenCStar (a := Fin m) k).symm (CStarMatrix.ofMatrix M)
        have hZ : 0 ≤ Z := map_nonneg (flattenCStar (a := Fin m) k).symm
          (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hM.nonneg)
        have hY := (J.operation y).map_cstarMatrix_nonneg Z hZ
        have hflat := map_nonneg (flattenCStar (a := Fin n) k) hY
        have heq := flatten_intertwines f k Z
        simp only [Z, StarAlgEquiv.apply_symm_apply, Equiv.symm_apply_apply] at heq
        have hout : 0 ≤ CStarMatrix.ofMatrix
            (PhyslibLeaf.MatrixMap.kron f LinearMap.id M) := by
          rw [← heq]
          exact hflat
        exact Matrix.nonneg_iff_posSemidef.mp
          (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hout)
      let v : Fin m × Fin m → ℂ := fun x => if x.1 = x.2 then 1 else 0
      have proj : C = PhyslibLeaf.MatrixMap.kron f LinearMap.id
          (Matrix.vecMulVec v (star v)) := by
        ext ⟨b₁,i₁⟩ ⟨b₂,i₂⟩
        simp [C, PhyslibLeaf.MatrixMap.kron_def, v, Matrix.vecMulVec, Matrix.single, ite_and]
      have hC : C.PosSemidef := by
        rw [proj]
        exact cp m (Matrix.posSemidef_vecMulVec_self_star v)
      have chosen (k : Hidden J y) (i : Fin n) (j : Fin m) :
          chosenKraus J y k i j = hC.1.eigenvectorUnitary (i,j) k *
            (Real.sqrt (hC.1.eigenvalues k) : ℂ) := by
        simp only [chosenKraus]
        exact dif_pos hC.1
      have spectral (p q : Hidden J y) : C p q =
          ∑ k, chosenKraus J y k p.1 p.2 * star (chosenKraus J y k q.1 q.2) := by
        calc
          C p q = ∑ k, hC.1.eigenvectorUnitary p k *
              (hC.1.eigenvalues k : ℂ) * star (hC.1.eigenvectorUnitary q k) := by
            conv_lhs => rw [hC.1.spectral_theorem]
            simp [Matrix.mul_apply, Matrix.diagonal]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro k _
            rw [chosen, chosen]
            simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
            have hs : (Real.sqrt (hC.1.eigenvalues k) : ℂ) *
                (Real.sqrt (hC.1.eigenvalues k) : ℂ) = (hC.1.eigenvalues k : ℂ) := by
              exact_mod_cast Real.mul_self_sqrt (hC.eigenvalues_nonneg k)
            rw [← hs]
            ring
      have expand : M = ∑ i, ∑ j, M i j • Matrix.single i j 1 := by
        ext i j
        simp [Matrix.single, Matrix.sum_apply, ite_and]
      have linear : f M = ∑ i, ∑ j, M i j • f (Matrix.single i j 1) := by
        conv_lhs => rw [expand]
        simp only [map_sum, map_smul]
      change f M = _
      rw [linear]
      ext b c
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      change (∑ i, ∑ j, M i j * C (b,i) (c,j)) = _
      simp_rw [spectral]
      simp only [Finset.mul_sum, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    have edge (y : Fin J.outcomes) :
        traceGarbage (retainedStep J y X) = step J y (traceGarbage X) := by
      ext p q
      dsimp only [step]
      rw [exactK y]
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
      change (∑ kg : Hidden J y × G, ∑ i, ∑ j,
        chosenKraus J y kg.1 (outputSplit R J y p).1 i *
          X ((inputSplit R d J.actor).symm (i,(outputSplit R J y p).2),kg.2)
            ((inputSplit R d J.actor).symm (j,(outputSplit R J y q).2),kg.2) *
          star (chosenKraus J y kg.1 (outputSplit R J y q).1 j)) = _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro k _
      simp only [traceGarbage, Finset.mul_sum, Finset.sum_mul]
      conv_rhs => rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    refine ⟨?_, ?_, exactK⟩
    · simp only [retainedOutputs, terminalOutputs]
      congr 1
      apply congrArg List.ofFn
      funext y
      rw [(ih y _).1, edge]
    · simp only [retainedPrefixes, coarsePrefixes]
      congr 2
      apply congrArg List.ofFn
      funext y
      rw [(ih y _).2.1, edge]

end D5.S3.Quantum.Recovery.FiniteLocalProtocol
