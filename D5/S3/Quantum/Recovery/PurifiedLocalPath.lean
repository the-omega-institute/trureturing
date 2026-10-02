/- GID: D5/S3/Quantum/Recovery/PurifiedLocalPath
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PurifiedLocalPath
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Actual observed paths with mixed product ancillas factor into accumulated local maps with inaccessible garbage. -/

/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa
-/
/-
Selected-source spectral data and proof-local steps: QuantumInfo/States/Mixed/MState.lean
(MState.purify, MState.purify_spec).
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

import D5.S3.Quantum.Recovery.RetainedLocalProtocol
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Order
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
open Matrix
open scoped Matrix ComplexOrder
namespace D5.S3.Quantum.Recovery.ProductPrefixRigidity

variable {A I : Type*} [Fintype A] [DecidableEq A] [Nonempty I]
variable (H : A → Type*) (R : ℕ → A → Type*)
variable [∀ a, Fintype (H a)] [∀ a, DecidableEq (H a)]
variable [∀ t a, Fintype (R t a)] [∀ t a, DecidableEq (R t a)]

def accumulated (B : ∀ a, Matrix (R 0 a) (H a) ℂ)
    (E : ∀ t a, Matrix (R (t+1) a) (R t a) ℂ) :
    ∀ t a, Matrix (R t a) (H a) ℂ
  | 0, a => B a
  | t+1, a => E t a * accumulated B E t a

def gram {X Y : Type*} [Fintype Y] (L : Matrix Y X ℂ) : Matrix X X ℂ := Lᴴ * L

def readout {X : Type*} [Fintype X] (Q : Matrix X X ℂ) (v : X → ℂ) : ℝ :=
  (star v ⬝ᵥ (Q *ᵥ v)).re

def productMap {T : A → Type*} (L : ∀ a, Matrix (T a) (H a) ℂ) :
    Matrix (∀ a, T a) (∀ a, H a) ℂ := fun y x => ∏ a, L a (y a) (x a)

end D5.S3.Quantum.Recovery.ProductPrefixRigidity

namespace D5.S3.Quantum.Recovery.FiniteLocalProtocol
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
noncomputable section
variable {A : Type} [Fintype A] [DecidableEq A]

/-- Each new inaccessible index belongs only to the actual actor. Other
holders acquire only a singleton coordinate, canonically equivalent to no change. -/
def LocalHidden {d : A → ℕ} (J : Instrument d) (y : Fin J.outcomes) (a : A) : Type :=
  { u : Unit // a = J.actor } → Hidden J y

noncomputable instance localHiddenFintype {d : A → ℕ} (J : Instrument d)
    (y : Fin J.outcomes) (a : A) : Fintype (LocalHidden J y a) := by
  classical
  unfold LocalHidden
  infer_instance

def distributeHidden {d : A → ℕ} (J : Instrument d) (y : Fin J.outcomes) :
    Hidden J y ≃ ((a : A) → LocalHidden J y a) where
  toFun k _ _ := k
  invFun f := f J.actor ⟨(),rfl⟩
  left_inv _ := rfl
  right_inv f := by
    funext a h
    rcases h with ⟨u, h⟩
    subst a
    congr 1

/-- Holder-indexed accumulated matrices, together with the actual ordered
hidden stack and the explicit regrouping equivalence. No rigidity fields. -/
structure LocalFactors (H d : A → ℕ) where
  garbage : A → Type
  finiteGarbage : ∀ a, Fintype (garbage a)
  stack : Type
  finiteStack : Fintype stack
  regroup : stack ≃ ((a : A) → garbage a)
  matrix : (a : A) → Matrix (Fin (d a) × garbage a) (Fin (H a)) ℂ

attribute [instance] LocalFactors.finiteGarbage LocalFactors.finiteStack

variable {H d : A → ℕ}

def LocalFactors.advanceMatrix (F : LocalFactors H d) (J : Instrument d)
    (y : Fin J.outcomes) (a : A) :
    Matrix (Fin (J.output y a) × (LocalHidden J y a × F.garbage a)) (Fin (H a)) ℂ
  := by
    intro p x
    by_cases h : a = J.actor
    · subst a
      exact ∑ i, chosenKraus J y (p.2.1 ⟨(),rfl⟩) p.1 i *
        F.matrix J.actor (i,p.2.2) x
    · exact F.matrix a (Fin.cast (J.unchanged y a h) p.1, p.2.2) x

@[reducible] def LocalFactors.advance (F : LocalFactors H d) (J : Instrument d) (y : Fin J.outcomes) :
    LocalFactors H (J.output y) where
  garbage a := LocalHidden J y a × F.garbage a
  finiteGarbage a := inferInstance
  stack := Hidden J y × F.stack
  finiteStack := inferInstance
  regroup :=
    { toFun := fun k a => (distributeHidden J y k.1 a, F.regroup k.2 a)
      invFun := fun f => ((distributeHidden J y).symm (fun a => (f a).1),
        F.regroup.symm (fun a => (f a).2))
      left_inv := fun k => by simp
      right_inv := fun f => by simp }
  matrix := F.advanceMatrix J y

/-- Product amplitudes on the actual ordered hidden coordinates. -/
def LocalFactors.amplitude (F : LocalFactors H d) (q : Coordinates d × F.stack)
    (x : Coordinates H) : ℂ :=
  D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap (fun a => Fin (H a)) F.matrix
    (fun a => (q.1 a, F.regroup q.2 a)) x

/-- All-matrix linear extension, keeping the spectator row/column untouched. -/
def LocalFactors.lift {R : Type} (F : LocalFactors H d) (X : State R H) :
    RetainedState R F.stack d := fun p q =>
  ∑ x : Coordinates H, ∑ z : Coordinates H,
    F.amplitude (p.1.2,p.2) x * X (p.1.1,x) (q.1.1,z) *
      star (F.amplitude (q.1.2,q.2) z)

/-- A prefix is selected only through observed outcomes of the existing tree. -/
inductive ObservedPath {Feedback : Type} : {d : A → ℕ} → Tree Feedback d → Type
  | here {d : A → ℕ} {T : Tree Feedback d} : ObservedPath T
  | next {d : A → ℕ} {J : Instrument d} {child : ∀ y, Tree Feedback (J.output y)}
      (y : Fin J.outcomes) (tail : ObservedPath (child y)) :
        ObservedPath (.node J child)

variable {Feedback : Type}

def ObservedPath.endDimensions : {d : A → ℕ} → {T : Tree Feedback d} →
    ObservedPath T → A → ℕ
  | d, _, .here => d
  | _, _, .next _ tail => tail.endDimensions

def ObservedPath.factors : {d : A → ℕ} → {T : Tree Feedback d} →
    (path : ObservedPath T) → LocalFactors H d → LocalFactors H path.endDimensions
  | _, _, .here, F => F
  | _, _, .next y tail, F => tail.factors (F.advance _ y)

def ObservedPath.stack : {d : A → ℕ} → {T : Tree Feedback d} →
    ObservedPath T → Type → Type
  | _, _, .here, G => G
  | _, _, .next (J := J) y tail, G => tail.stack (Hidden J y × G)

def ObservedPath.execute {R : Type} : {d : A → ℕ} → {T : Tree Feedback d} →
    (path : ObservedPath T) → {G : Type} → RetainedState R G d →
    RetainedState R (path.stack G) path.endDimensions
  | _, _, .here, _, X => X
  | _, _, .next y tail, _, X => tail.execute (retainedStep _ y X)

def ObservedPath.stackEquiv : {d : A → ℕ} → {T : Tree Feedback d} →
    (path : ObservedPath T) → (F : LocalFactors H d) →
    (path.factors F).stack ≃ path.stack F.stack
  | _, _, .here, F => Equiv.refl F.stack
  | _, _, .next y tail, F => tail.stackEquiv (F.advance _ y)

end
end D5.S3.Quantum.Recovery.FiniteLocalProtocol

namespace D5.S3.Quantum.Recovery.FiniteLocalProtocol
noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
variable {A : Type} [Fintype A] [DecidableEq A]
variable {H d : A → ℕ} {R Feedback : Type}

/-- Spectral purification data for the actual independent local density. -/
def ProductAncillas.purification (η : ProductAncillas A) (a : A) :
    (Fin (η.dimension a) × Fin (η.dimension a)) → ℂ := by
  classical
  let ρ := CStarMatrix.ofMatrix.symm (η.density a).1
  have hp : ρ.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (η.density a).2.1)
  exact fun (i,j) => hp.1.eigenvectorUnitary i j *
    (Real.sqrt (hp.1.eigenvalues j) : ℂ)

def ProductAncillas.rootFactors (η : ProductAncillas A) (H : A → ℕ) :
    LocalFactors H (fun a => H a * η.dimension a) where
  garbage a := Fin (η.dimension a)
  finiteGarbage a := inferInstance
  stack := (a : A) → Fin (η.dimension a)
  finiteStack := inferInstance
  regroup := Equiv.refl _
  matrix a p x := if (finProdFinEquiv.symm p.1).1 = x then
    η.purification a ((finProdFinEquiv.symm p.1).2, p.2) else 0

/-- The literal rectangular local edge, tensored with identity on old local garbage. -/
def LocalFactors.edge (F : LocalFactors H d) (J : Instrument d)
    (y : Fin J.outcomes) (a : A) :
    Matrix (Fin (J.output y a) × (LocalHidden J y a × F.garbage a))
      (Fin (d a) × F.garbage a) ℂ := by
  classical
  intro p q
  by_cases h : a = J.actor
  · subst a
    exact if q.2 = p.2.2 then chosenKraus J y (p.2.1 ⟨(),rfl⟩) p.1 q.1 else 0
  · exact if q = (Fin.cast (J.unchanged y a h) p.1, p.2.2) then 1 else 0

@[reducible] def ObservedPath.frame {d : A → ℕ} {T : Tree Feedback d}
    (path : ObservedPath T) (F : LocalFactors H d) : ℕ → (Σ d, LocalFactors H d)
  | 0 => ⟨d,F⟩
  | t+1 => match path with
    | .here => ⟨d,F⟩
    | .next y tail => tail.frame (F.advance _ y) t
termination_by structural t => t

abbrev ObservedPath.localCoordinates {T : Tree Feedback d} (path : ObservedPath T)
    (F : LocalFactors H d) (t : ℕ) (a : A) : Type :=
  Fin ((path.frame F t).1 a) × (path.frame F t).2.garbage a

noncomputable instance pathCoordinateFintype {T : Tree Feedback d}
    (path : ObservedPath T) (F : LocalFactors H d) (t : ℕ) (a : A) :
    Fintype (path.localCoordinates F t a) := inferInstanceAs
      (Fintype (Fin ((path.frame F t).1 a) × (path.frame F t).2.garbage a))

noncomputable instance pathCoordinateDecidableEq {T : Tree Feedback d}
    (path : ObservedPath T) (F : LocalFactors H d) (t : ℕ) (a : A) :
    DecidableEq (path.localCoordinates F t a) := Classical.decEq _

def ObservedPath.edges : {d : A → ℕ} → {T : Tree Feedback d} →
    (path : ObservedPath T) → (F : LocalFactors H d) → (t : ℕ) → (a : A) →
      Matrix (path.localCoordinates F (t+1) a) (path.localCoordinates F t a) ℂ
  | d, _, .here, F, 0, a => by
      classical
      exact (1 : Matrix (Fin (d a) × F.garbage a) (Fin (d a) × F.garbage a) ℂ)
  | d, _, .here, F, _+1, a => by
      classical
      exact (1 : Matrix (Fin (d a) × F.garbage a) (Fin (d a) × F.garbage a) ℂ)
  | _, _, .next (J := J) y _, F, 0, a => F.edge J y a
  | _, _, .next y tail, F, t+1, a => tail.edges (F.advance _ y) t a

def ObservedPath.actorAt [Nonempty A] : {d : A → ℕ} → {T : Tree Feedback d} →
    ObservedPath T → ℕ → A
  | _, _, .here, _ => Classical.choice inferInstance
  | _, _, .next (J := J) _ _, 0 => J.actor
  | _, _, .next _ tail, t+1 => tail.actorAt t

def ObservedPath.length : {d : A → ℕ} → {T : Tree Feedback d} → ObservedPath T → ℕ
  | _, _, .here => 0
  | _, _, .next _ tail => tail.length + 1

def ObservedPath.history : {d : A → ℕ} → {T : Tree Feedback d} → ObservedPath T → List ℕ
  | _, _, .here => []
  | _, _, .next y tail => y.val :: tail.history

def ObservedPath.endFeedback : {d : A → ℕ} → {T : Tree Feedback d} →
    ObservedPath T → Option Feedback
  | _, .leaf f, .here => some f
  | _, .node _ _, .here => none
  | _, _, .next _ tail => tail.endFeedback

@[instance_reducible] noncomputable def ObservedPath.stackFintype : {d : A → ℕ} → {T : Tree Feedback d} →
    (path : ObservedPath T) → {G : Type} → [Fintype G] → Fintype (path.stack G)
  | _, _, .here, _, inst => inst
  | _, _, .next _ tail, _, _ => tail.stackFintype
attribute [instance] ObservedPath.stackFintype

def ObservedPath.report {T : Tree Feedback d} (path : ObservedPath T)
    {G : Type} [Fintype G] (X : RetainedState R G d) : Terminal (Option Feedback) R A :=
  ⟨path.history, path.endFeedback, path.endDimensions, traceGarbage (path.execute X)⟩

/-- Actual mixed-ancilla local protocol prefixes factor through accumulated
holder-local matrices. The hidden-stack regrouping is explicit, root purification
is selected internally, and the report belongs to the original coarse prefix list.
No scalarity, isometry or probability-independence is assumed. -/
theorem purified_local_path_bridge [Nonempty A] [Fintype R]
    (P : Protocol Feedback H) (X : State R H) :
    let F := P.ancillas.rootFactors H
    traceGarbage (F.lift X) = appendAncillas P.ancillas X ∧
    (∀ a, D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram (F.matrix a) = 1) ∧
    ∀ path : ObservedPath P.tree,
      path.report (F.lift X) ∈ coarsePrefixes P.tree (appendAncillas P.ancillas X) ∧
      path.execute (F.lift X) =
        ((path.factors F).lift X).submatrix
          (fun p => (p.1, (path.stackEquiv F).symm p.2))
          (fun p => (p.1, (path.stackEquiv F).symm p.2)) ∧
      path.frame F path.length = ⟨path.endDimensions, path.factors F⟩ ∧
      (∀ t a, D5.S3.Quantum.Recovery.ProductPrefixRigidity.accumulated (fun a => Fin (H a))
        (path.localCoordinates F) (path.frame F 0).2.matrix (path.edges F) t a =
          (path.frame F t).2.matrix a) ∧
      (∀ t a, a ≠ path.actorAt t → ∃ e : path.localCoordinates F (t+1) a ≃
        path.localCoordinates F t a,
        path.edges F t a = (1 : Matrix (path.localCoordinates F t a)
          (path.localCoordinates F t a) ℂ).submatrix e id) := by
  classical
  have path_factorization {d : A → ℕ} {T : Tree Feedback d} (path : ObservedPath T)
      (F : LocalFactors H d) (X : State R H) :
      path.execute (F.lift X) =
        ((path.factors F).lift X).submatrix
          (fun p => (p.1, (path.stackEquiv F).symm p.2))
          (fun p => (p.1, (path.stackEquiv F).symm p.2)) := by
    classical
    have edge_amp {d : A → ℕ} (F : LocalFactors H d) (J : Instrument d)
        (y : Fin J.outcomes) (p : R × Coordinates (J.output y))
        (k : Hidden J y) (g : F.stack) (x : Coordinates H) :
        (F.advance J y).amplitude (p.2,(k,g)) x =
          ∑ i, chosenKraus J y k (outputSplit R J y p).1 i *
            F.amplitude (((inputSplit R d J.actor).symm
              (i,(outputSplit R J y p).2)).2,g) x := by
      change (∏ a, F.advanceMatrix J y a
        (p.2 a, (distributeHidden J y k a, F.regroup g a)) (x a)) = _
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ J.actor)]
      simp only [LocalFactors.advanceMatrix, dif_pos rfl]
      dsimp only [distributeHidden, Equiv.coe_fn_mk]
      simp only [dite_true]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [LocalFactors.amplitude, D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap]
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ J.actor)]
      have act : ((inputSplit R d J.actor).symm
          (i,(outputSplit R J y p).2)).2 J.actor = i := by
        simp [inputSplit, Equiv.piSplitAt]
      simp only [act]
      change (_ * _) * _ = _ * (_ * _)
      rw [mul_assoc]
      congr 2
      apply Finset.prod_congr rfl
      intro a ha
      have h : a ≠ J.actor := (Finset.mem_erase.mp ha).1
      simp [LocalFactors.advanceMatrix, h, inputSplit, outputSplit, Equiv.piSplitAt,
        Equiv.piCongrRight]
      congr 2
      apply Fin.ext
      simp only [Fin.val_cast]
      have cast_val {m n : ℕ} (e : m = n) (v : Fin m) :
          (cast (congrArg Fin e) v).val = v.val := by cases e; rfl
      exact (cast_val (J.unchanged y a h) (p.2 a)).symm
    have edge {d : A → ℕ} (F : LocalFactors H d) (J : Instrument d)
        (y : Fin J.outcomes) :
        retainedStep J y (F.lift X) = (F.advance J y).lift X := by
      ext p q
      dsimp only [retainedStep, LocalFactors.lift]
      conv_rhs =>
        arg 2; ext x; arg 2; ext z
        rw [edge_amp, edge_amp]
      simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
      conv_lhs =>
        arg 2; ext i
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      conv_lhs =>
        arg 2; ext i
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      have rp : ((inputSplit R d J.actor).symm
        (i,(outputSplit R J y p.1).2)).1 = p.1.1 := rfl
      have rq : ((inputSplit R d J.actor).symm
        (j,(outputSplit R J y q.1).2)).1 = q.1.1 := rfl
      rw [rp, rq]
      ring
    induction path with
    | here => rfl
    | next y tail ih =>
      simp only [ObservedPath.execute, ObservedPath.factors, ObservedPath.stackEquiv]
      rw [edge]
      exact ih (F.advance _ y)
  -- Physlib MState.purify and purify_spec: the selected spectral construction
  -- is checked here on the live actual initialization path.
  have purification_marginal (η : ProductAncillas A) (a : A)
      (u v : Fin (η.dimension a)) :
      (∑ g, η.purification a (u,g) * star (η.purification a (v,g))) =
        (η.density a).1 u v := by
    let ρ := CStarMatrix.ofMatrix.symm (η.density a).1
    have hp : ρ.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (η.density a).2.1)
    have spectral : (η.density a).1 u v =
        ∑ g, hp.1.eigenvectorUnitary u g * (hp.1.eigenvalues g : ℂ) *
          star (hp.1.eigenvectorUnitary v g) := by
      change ρ u v = _
      conv_lhs => rw [hp.1.spectral_theorem]
      simp [Matrix.mul_apply, Matrix.diagonal]
    rw [spectral]
    apply Finset.sum_congr rfl
    intro g _
    simp only [ProductAncillas.purification, star_mul, Complex.star_def, Complex.conj_ofReal]
    have hs : (Real.sqrt (hp.1.eigenvalues g) : ℂ) *
        (Real.sqrt (hp.1.eigenvalues g) : ℂ) = (hp.1.eigenvalues g : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt (hp.eigenvalues_nonneg g)
    rw [← hs]
    ring
  have root_trace_check (η : ProductAncillas A) (X : State R H) :
      traceGarbage ((η.rootFactors H).lift X) = appendAncillas η X := by
    classical
    have amp (p : Coordinates (fun a => H a * η.dimension a))
        (g : (a : A) → Fin (η.dimension a)) (x : Coordinates H) :
        (η.rootFactors H).amplitude (p,g) x =
          if (fun a => (finProdFinEquiv.symm (p a)).1) = x then
            ∏ a, η.purification a ((finProdFinEquiv.symm (p a)).2, g a) else 0 := by
      change (∏ a, if (finProdFinEquiv.symm (p a)).1 = x a then
        η.purification a ((finProdFinEquiv.symm (p a)).2, g a) else 0) = _
      rw [Fintype.prod_ite_zero]
      simp only [funext_iff]
    have collapse (p q : (R × Coordinates (fun a => H a * η.dimension a)) ×
        ((a : A) → Fin (η.dimension a))) :
        (η.rootFactors H).lift X p q =
          X (p.1.1, fun a => (finProdFinEquiv.symm (p.1.2 a)).1)
            (q.1.1, fun a => (finProdFinEquiv.symm (q.1.2 a)).1) *
          ∏ a, (η.purification a ((finProdFinEquiv.symm (p.1.2 a)).2,p.2 a) *
            star (η.purification a ((finProdFinEquiv.symm (q.1.2 a)).2,q.2 a))) := by
      dsimp only [LocalFactors.lift]
      simp_rw [amp]
      simp only [apply_ite, ite_mul, zero_mul, mul_ite, mul_zero, star_zero,
        Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [star_prod, Finset.prod_mul_distrib]
      ring
    have local_trace (a : A) (u v : Fin (η.dimension a)) :
        (∑ g, η.purification a (u,g) * star (η.purification a (v,g))) =
          (η.density a).1 u v := by
      exact purification_marginal η a u v
    ext p q
    change (∑ g, (η.rootFactors H).lift X (p,g) (q,g)) = _
    simp_rw [collapse]
    rw [← Finset.mul_sum]
    erw [← Fintype.prod_sum (fun a (g : Fin (η.dimension a)) =>
      η.purification a ((finProdFinEquiv.symm (p.2 a)).2,g) *
      star (η.purification a ((finProdFinEquiv.symm (q.2 a)).2,g)))]
    simp_rw [local_trace]
    rfl
  have path_accumulation_check {d : A → ℕ} {T : Tree Feedback d} (path : ObservedPath T)
      (F : LocalFactors H d) :
      ∀ t a, D5.S3.Quantum.Recovery.ProductPrefixRigidity.accumulated (fun a => Fin (H a))
        (path.localCoordinates F) (path.frame F 0).2.matrix (path.edges F) t a =
          (path.frame F t).2.matrix a := by
    classical
    have edge {d : A → ℕ} (F : LocalFactors H d) (J : Instrument d)
        (y : Fin J.outcomes) (a : A) :
        (F.advance J y).matrix a = F.edge J y a * F.matrix a := by
      ext p x
      by_cases h : a = J.actor
      · subst a
        simp [LocalFactors.advance, LocalFactors.advanceMatrix, LocalFactors.edge,
          Matrix.mul_apply, Fintype.sum_prod_type]
      · simp [LocalFactors.advance, LocalFactors.advanceMatrix, LocalFactors.edge,
          h, Matrix.mul_apply]
    have step : ∀ t a, (path.frame F (t+1)).2.matrix a =
        path.edges F t a * (path.frame F t).2.matrix a := by
      induction path with
      | here => intro t a; cases t <;> simp [ObservedPath.frame, ObservedPath.edges]
      | next y tail ih =>
        intro t a
        cases t with
        | zero => exact edge F _ y a
        | succ t => exact ih (F.advance _ y) t a
    intro t a
    induction t with
    | zero => rfl
    | succ t ih =>
      dsimp only [D5.S3.Quantum.Recovery.ProductPrefixRigidity.accumulated]
      rw [ih]
      exact (step t a).symm
  have root_isometry_check (η : ProductAncillas A) (a : A) :
      D5.S3.Quantum.Recovery.ProductPrefixRigidity.gram ((η.rootFactors H).matrix a) = 1 := by
    classical
    have hn : (∑ u, star (η.purification a u) * η.purification a u) = (1 : ℂ) := by
      rw [Fintype.sum_prod_type]
      simp_rw [mul_comm (star _) _, purification_marginal]
      exact (η.density a).2.2
    ext x z
    change (∑ p : Fin (H a * η.dimension a) × Fin (η.dimension a),
      star ((η.rootFactors H).matrix a p x) * (η.rootFactors H).matrix a p z) = _
    rw [← (Equiv.prodCongr (finProdFinEquiv :
      Fin (H a) × Fin (η.dimension a) ≃ Fin (H a * η.dimension a))
        (Equiv.refl (Fin (η.dimension a)))).sum_comp]
    simp only [Fintype.sum_prod_type]
    simp only [ProductAncillas.rootFactors, Equiv.prodCongr_apply,
      Equiv.refl_apply, Equiv.symm_apply_apply, Prod.map_apply]
    by_cases h : x = z
    · subst z
      simp only [apply_ite, star_zero, ite_mul, zero_mul, mul_ite, mul_zero,
        Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, Matrix.one_apply_eq]
      simpa only [Fintype.sum_prod_type] using hn
    · simp [apply_ite, h, Matrix.one_apply, eq_comm]
  have path_inactive_check {d : A → ℕ} {T : Tree Feedback d}
      (path : ObservedPath T) (F : LocalFactors H d) :
      ∀ t a, a ≠ path.actorAt t → ∃ e : path.localCoordinates F (t+1) a ≃
        path.localCoordinates F t a,
        path.edges F t a = (1 : Matrix (path.localCoordinates F t a)
          (path.localCoordinates F t a) ℂ).submatrix e id := by
    classical
    induction path with
    | here =>
      intro t a _
      cases t <;> refine ⟨Equiv.refl _, ?_⟩ <;> ext p q <;>
        simp only [ObservedPath.edges, Matrix.submatrix_apply, Equiv.refl_apply,
          id_eq, Matrix.one_apply] <;> split_ifs <;> simp_all <;> aesop
    | @next d J child y tail ih =>
      intro t a h
      cases t with
      | succ t => exact ih (F.advance J y) t a h
      | zero =>
        change a ≠ J.actor at h
        let e : (Fin (J.output y a) × (LocalHidden J y a × F.garbage a)) ≃
            (Fin (d a) × F.garbage a) :=
          { toFun := fun p => (Fin.cast (J.unchanged y a h) p.1, p.2.2)
            invFun := fun p => (Fin.cast (J.unchanged y a h).symm p.1,
              (fun u => (h u.2).elim, p.2))
            left_inv := fun p => by
              ext
              · simp
              · funext u; exact (h u.2).elim
              · rfl
            right_inv := fun p => by ext <;> simp }
        refine ⟨e, ?_⟩
        ext p q
        simp only [ObservedPath.edges, Matrix.submatrix_apply, Matrix.one_apply, id_eq]
        simp only [LocalFactors.edge, dif_neg h, e]
        split_ifs <;> simp_all only [Equiv.coe_fn_mk, eq_comm, not_true_eq_false, not_false_eq_true] <;> aesop
  have endpoint_check {d : A → ℕ} {T : Tree Feedback d} (path : ObservedPath T)
      (F : LocalFactors H d) :
      path.frame F path.length = ⟨path.endDimensions, path.factors F⟩ := by
    induction path with
    | here => rfl
    | next y tail ih => exact ih (F.advance _ y)
  have actual_prefix_check {d : A → ℕ} {T : Tree Feedback d} (path : ObservedPath T) :
      ∀ {G : Type} [Fintype G] (X : RetainedState R G d),
        path.report X ∈ retainedPrefixes T X := by
    induction path with
    | @here d T =>
      intro G _ X
      cases T <;> simp [ObservedPath.report, ObservedPath.history,
        ObservedPath.endFeedback, ObservedPath.endDimensions, ObservedPath.execute,
        retainedPrefixes] <;> congr 1 <;> exact Subsingleton.elim _ _
    | @next d J child y tail ih =>
      intro G _ X
      apply List.mem_cons_of_mem
      apply List.mem_flatten.mpr
      refine ⟨_, List.mem_ofFn.mpr ⟨y,rfl⟩, ?_⟩
      apply List.mem_map.mpr
      refine ⟨tail.report (retainedStep J y X), ih _, ?_⟩
      rfl
  refine ⟨root_trace_check P.ancillas X, root_isometry_check P.ancillas, ?_⟩
  intro path
  let F := P.ancillas.rootFactors H
  refine ⟨?_, path_factorization path F X, endpoint_check path F,
    path_accumulation_check path F, path_inactive_check path F⟩
  have h := actual_prefix_check path (F.lift X)
  rw [(recursive_coarse_retained P.tree (F.lift X)).2.1] at h
  simpa only [F, root_trace_check] using h

end
end D5.S3.Quantum.Recovery.FiniteLocalProtocol

namespace D5.S3.Quantum.Recovery.FiniteLocalProtocol
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
variable {A S : Type} [Fintype A] [DecidableEq A] [Fintype S] [DecidableEq S]

noncomputable def recordTrace {d : A → ℕ} (X : State S d) : Matrix S S ℂ :=
  fun i j => ∑ r : Coordinates d, X (i,r) (j,r)

/-- Prepare common-label records without restricting the system matrix. -/
noncomputable def commonPreparation {H : A → ℕ}
    (s : (a : A) → S → Fin (H a) → ℂ) (X : Matrix S S ℂ) : State S H :=
  fun p q => X p.1 q.1 * ∏ a, s a p.1 (p.2 a) * star (s a q.1 (q.2 a))

variable {Feedback : Type}

/-- Input-independent observed leaf addresses. Hidden Kraus labels are absent. -/
def Tree.Leaves {d : A → ℕ} : Tree Feedback d → Type
  | .leaf _ => Unit
  | .node J child => (y : Fin J.outcomes) × (child y).Leaves

noncomputable instance Tree.fintypeLeaves {d : A → ℕ}
    (T : Tree Feedback d) : Fintype T.Leaves := by
  induction T with
  | leaf => exact inferInstanceAs (Fintype Unit)
  | node J child ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((y : Fin J.outcomes) × (child y).Leaves))

/-- Execute the original coarse maps down one observed leaf address. -/
noncomputable def Tree.branch {d : A → ℕ}
    (T : Tree Feedback d) (X : State S d) :
    T.Leaves → Terminal Feedback S A :=
  match T with
  | .leaf U => fun _ => ⟨[], U, d, X⟩
  | .node J child => fun w =>
      let z := (child w.1).branch (step J w.1 X) w.2
      { z with history := w.1.val :: z.history }

/-- The retained path selected by an actual observed leaf address. -/
def Tree.leafPath {d : A → ℕ} (T : Tree Feedback d) :
    T.Leaves → ObservedPath T := match T with
  | .leaf _ => fun _ => .here
  | .node _ child => fun w => .next w.1 ((child w.1).leafPath w.2)

def Tree.leafFeedback {d : A → ℕ} (T : Tree Feedback d) :
    T.Leaves → Feedback := match T with
  | .leaf y => fun _ => y
  | .node _ child => fun w => (child w.1).leafFeedback w.2


end
end D5.S3.Quantum.Recovery.FiniteLocalProtocol

namespace D5.S3.Quantum.Recovery.FiniteLocalProtocol
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
variable {A : Type} [Fintype A] [DecidableEq A]
variable {H d : A → ℕ} {Y : Type}

def LocalFactors.inputEffect (F : LocalFactors H d) :
    Matrix (Coordinates H) (Coordinates H) ℂ :=
  ProductPrefixRigidity.productMap (fun a => Fin (H a))
    (fun a => ProductPrefixRigidity.gram (F.matrix a))

def Tree.descendantEffect (T : Tree Y d) (F : LocalFactors H d) :
    Matrix (Coordinates H) (Coordinates H) ℂ :=
  ∑ w : T.Leaves, ((T.leafPath w).factors F).inputEffect

def recordPreparation {I : Type} (q : I → Coordinates H → ℂ)
    (X : Matrix I I ℂ) : State I H :=
  fun p z => X p.1 z.1 * q p.1 p.2 * star (q z.1 z.2)

def InputEffectTreeLaws [Nonempty A] (P : Protocol Y H) : Prop :=
    (∀ a, ProductPrefixRigidity.gram ((P.ancillas.rootFactors H).matrix a) = 1) ∧
    (P.ancillas.rootFactors H).inputEffect = 1 ∧
    (∀ {d : A → ℕ} (F : LocalFactors H d),
      F.inputEffect.PosSemidef ∧
      ∀ a, (ProductPrefixRigidity.gram (F.matrix a)).PosSemidef) ∧
    (∀ {d : A → ℕ} (F : LocalFactors H d) (J : Instrument d),
      (∑ y, (F.advance J y).inputEffect) = F.inputEffect ∧
      (∑ y, ProductPrefixRigidity.gram ((F.advance J y).matrix J.actor)) =
        ProductPrefixRigidity.gram (F.matrix J.actor) ∧
      ∀ y a, a ≠ J.actor →
        ProductPrefixRigidity.gram ((F.advance J y).matrix a) =
          ProductPrefixRigidity.gram (F.matrix a)) ∧
    (∀ {d : A → ℕ} (T : Tree Y d) (F : LocalFactors H d),
      T.descendantEffect F = F.inputEffect) ∧
    (∀ (I : Type) [Fintype I] (q : I → Coordinates H → ℂ)
      (X : Matrix I I ℂ) (w : P.tree.Leaves) (i j : I),
      recordTrace (P.tree.branch
        (appendAncillas P.ancillas (recordPreparation q X)) w).state i j =
      (star (q j) ⬝ᵥ ((((P.tree.leafPath w).factors
        (P.ancillas.rootFactors H)).inputEffect) *ᵥ q i)) * X i j)


end
end D5.S3.Quantum.Recovery.FiniteLocalProtocol
