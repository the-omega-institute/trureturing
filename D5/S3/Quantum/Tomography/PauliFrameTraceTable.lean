/- GID: D5/S3/Quantum/Tomography/PauliFrameTraceTable
   generality: I
   mirror-B: D5/B/S3/Quantum/Tomography/PauliFrameTraceTable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Tomography/PauliFrameTraceTable.claim; result=D5/S3/Quantum/Tomography/PauliFrameTraceTable.result; claim=D5/S3/Quantum/Tomography/PauliFrameTraceTable.claim
   digest: Equal labelled Pauli overlap tables do not determine the dimension of the generated real Jordan carrier. -/

/-
The trace table is a direct application of Pauli trace orthogonality. The generated
carriers use the real Jordan product on the original complex matrices.
-/

import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import Mathlib.LinearAlgebra.Trace

open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace D5.S3.Quantum.Tomography.PauliFrameTraceTable

open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Information
open D5.S3.Quantum.FiniteDimensional

abbrev Op := Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ
abbrev Bits := Fin 2 × Fin 2

/-- The original real Jordan product in the common matrix algebra. -/
def jordan (A B : Op) : Op := (1 / 2 : ℝ) • (A * B + B * A)

/-- Closure under the actual matrix Jordan product. -/
def JordanClosed (S : Submodule ℝ Op) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, jordan A B ∈ S

/-- The smallest real Jordan-closed carrier containing every labelled atom. -/
def generated (p : Fin 3 → Bits → Op) : Submodule ℝ Op :=
  sInf {S | (∀ i st, p i st ∈ S) ∧ JordanClosed S}

/-- All Hermitian matrices in the common four-dimensional complex Hilbert space. -/
def complexCarrier : Submodule ℝ Op := selfAdjoint.submodule ℝ Op

/-- The embedded real symmetric matrices. -/
def realCarrier : Submodule ℝ Op where
  carrier := {A | A ∈ complexCarrier ∧ ∀ x y, (A x y).im = 0}
  zero_mem' := ⟨complexCarrier.zero_mem, by simp⟩
  add_mem' := by
    rintro A B ⟨hA, hAr⟩ ⟨hB, hBr⟩
    exact ⟨complexCarrier.add_mem hA hB, by simpa using fun x y => congrArg₂ (· + ·) (hAr x y) (hBr x y)⟩
  smul_mem' := by
    rintro r A ⟨hA, hAr⟩
    refine ⟨complexCarrier.smul_mem r hA, ?_⟩
    intro x y
    simp [Matrix.smul_apply, hAr]

/-- The whole labelled twelve-by-twelve two-point table. -/
def table (p : Fin 3 → Bits → Op) : Fin 3 → Fin 3 → Bits → Bits → ℂ :=
  fun i j st uv => Matrix.trace (p i st * p j uv)

/-- Three complete rank-one projector frames in the fixed common environment. -/
def Complete (p : Fin 3 → Bits → Op) : Prop :=
  (∀ i st, (p i st).IsHermitian ∧ p i st * p i st = p i st ∧ (p i st).rank = 1) ∧
    (∀ i st uv, st ≠ uv → p i st * p i uv = 0) ∧
    (∀ i, ∑ st, p i st = 1)

/-- A whole-table postprocessor recovers Jordan dimension for every complete triple. -/
def claim : Prop :=
  ∃ post : (Fin 3 → Fin 3 → Bits → Bits → ℂ) → ℕ,
    ∀ p : Fin 3 → Bits → Op, Complete p → post (table p) = Module.finrank ℝ (generated p)

private lemma generated_mem (p : Fin 3 → Bits → Op) (i : Fin 3) (st : Bits) :
    p i st ∈ generated p := by
  apply Submodule.mem_sInf.mpr
  intro S hS
  exact hS.1 i st

private lemma generated_closed (p : Fin 3 → Bits → Op) : JordanClosed (generated p) := by
  intro A hA B hB
  apply Submodule.mem_sInf.mpr
  intro S hS
  exact hS.2 A (Submodule.mem_sInf.mp hA S hS) B (Submodule.mem_sInf.mp hB S hS)

private lemma generated_le (p : Fin 3 → Bits → Op) (S : Submodule ℝ Op)
    (hp : ∀ i st, p i st ∈ S) (hS : JordanClosed S) : generated p ≤ S :=
  sInf_le ⟨hp, hS⟩

private def eps (b : Fin 2) : ℂ := if b = 0 then 1 else -1

private def proj (A B C : Fin 2 → Pauli) (st : Bits) : Op :=
  (1 / 4 : ℂ) • ((1 : Op) + eps st.1 • wordOp A + eps st.2 • wordOp B +
    (eps st.1 * eps st.2) • wordOp C)

private def E (st : Bits) : Op :=
  proj ![Pauli.Z, Pauli.I] ![Pauli.I, Pauli.Z] ![Pauli.Z, Pauli.Z] st

private def F (st : Bits) : Op :=
  proj ![Pauli.X, Pauli.I] ![Pauli.I, Pauli.X] ![Pauli.X, Pauli.X] st

private def Gr (st : Bits) : Op :=
  proj ![Pauli.X, Pauli.Z] ![Pauli.Z, Pauli.X] ![Pauli.Y, Pauli.Y] st

private def Gc (st : Bits) : Op :=
  proj ![Pauli.Y, Pauli.I] ![Pauli.I, Pauli.Y] ![Pauli.Y, Pauli.Y] st

/-- The two labelled triples use the same first two contexts and differ only in G. -/
def frame (c : Bool) (i : Fin 3) (st : Fin 2 × Fin 2) :
    Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  if i = 0 then E st else if i = 1 then F st else if c then Gr st else Gc st

private lemma proj_recover (A B C : Fin 2 → Pauli) :
    proj A B C (0, 0) + proj A B C (0, 1) + proj A B C (1, 0) +
        proj A B C (1, 1) = 1 ∧
    proj A B C (0, 0) + proj A B C (0, 1) - proj A B C (1, 0) -
        proj A B C (1, 1) = wordOp A ∧
    proj A B C (0, 0) - proj A B C (0, 1) + proj A B C (1, 0) -
        proj A B C (1, 1) = wordOp B ∧
    proj A B C (0, 0) - proj A B C (0, 1) - proj A B C (1, 0) +
        proj A B C (1, 1) = wordOp C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [proj, eps] <;> module

private lemma recovered_mem (S : Submodule ℝ Op) (A B C : Fin 2 → Pauli)
    (h : ∀ st, proj A B C st ∈ S) :
    (1 : Op) ∈ S ∧ wordOp A ∈ S ∧ wordOp B ∈ S ∧ wordOp C ∈ S := by
  obtain ⟨h0, h1, h2, h3⟩ := proj_recover A B C
  exact ⟨h0 ▸ S.add_mem (S.add_mem (S.add_mem (h _) (h _)) (h _)) (h _),
    h1 ▸ S.sub_mem (S.sub_mem (S.add_mem (h _) (h _)) (h _)) (h _),
    h2 ▸ S.sub_mem (S.add_mem (S.sub_mem (h _) (h _)) (h _)) (h _),
    h3 ▸ S.add_mem (S.sub_mem (S.sub_mem (h _) (h _)) (h _)) (h _)⟩

private lemma word_two_mul (p q r s : Pauli) :
    wordOp ![p, q] * wordOp ![r, s] =
      (letterPhase p r * letterPhase q s) • wordOp ![letterProduct p r, letterProduct q s] := by
  rw [word_mul]
  congr 1
  simp [Fin.prod_univ_two]

private lemma word_ii : wordOp ![Pauli.I, Pauli.I] = (1 : Op) := by
  convert (word_one (n := 2)) using 2
  ext i
  fin_cases i <;> rfl

private lemma tensor_factors (p q : Pauli) :
    jordan (wordOp ![p, Pauli.I]) (wordOp ![Pauli.I, q]) = wordOp ![p, q] := by
  cases p <;> cases q <;>
    simp [jordan, word_two_mul, letterPhase, letterProduct,
      add_smul, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul] <;> module

private lemma real_generators (c : Bool) :
    ∀ p q : Pauli, (p ≠ Pauli.Y ∧ q ≠ Pauli.Y) ∨ (p = Pauli.Y ∧ q = Pauli.Y) →
      wordOp ![p, q] ∈ generated (frame c) := by
  let S := generated (frame c)
  have hE := recovered_mem S ![Pauli.Z, Pauli.I] ![Pauli.I, Pauli.Z]
    ![Pauli.Z, Pauli.Z] (fun st => by simpa [frame, E] using generated_mem (frame c) 0 st)
  have hF := recovered_mem S ![Pauli.X, Pauli.I] ![Pauli.I, Pauli.X]
    ![Pauli.X, Pauli.X] (fun st => by simpa [frame, F] using generated_mem (frame c) 1 st)
  have hleft (p : Pauli) (hp : p ≠ Pauli.Y) : wordOp ![p, Pauli.I] ∈ S := by
    cases p
    · simpa only [show ![Pauli.I, Pauli.I] = (fun _ : Fin 2 => Pauli.I) by ext i; fin_cases i <;> rfl,
        word_one] using hE.1
    · exact hF.2.1
    · exact False.elim (hp rfl)
    · exact hE.2.1
  have hright (q : Pauli) (hq : q ≠ Pauli.Y) : wordOp ![Pauli.I, q] ∈ S := by
    cases q
    · exact hleft Pauli.I (by decide)
    · exact hF.2.2.1
    · exact False.elim (hq rfl)
    · exact hE.2.2.1
  have hbasic (p q : Pauli) (hp : p ≠ Pauli.Y) (hq : q ≠ Pauli.Y) : wordOp ![p, q] ∈ S := by
    rw [← tensor_factors]
    exact generated_closed (frame c) _ (hleft p hp) _ (hright q hq)
  intro p q h
  rcases h with ⟨hp, hq⟩ | ⟨rfl, rfl⟩
  · exact hbasic p q hp hq
  · have h := generated_closed (frame c) _ (hbasic .X .Z (by decide) (by decide))
        _ (hbasic .Z .X (by decide) (by decide))
    convert h using 1
    simp [jordan, word_two_mul, letterPhase, letterProduct,
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, ← add_smul] <;> norm_num

private lemma complex_generators : ∀ p q : Pauli,
    wordOp ![p, q] ∈ generated (frame false) := by
  let S := generated (frame false)
  have hG := recovered_mem S ![Pauli.Y, Pauli.I] ![Pauli.I, Pauli.Y]
    ![Pauli.Y, Pauli.Y] (fun st => by simpa [frame, Gc] using generated_mem (frame false) 2 st)
  have hleft (p : Pauli) : wordOp ![p, Pauli.I] ∈ S := by
    by_cases hp : p = Pauli.Y
    · simpa [hp] using hG.2.1
    · exact real_generators false p .I (Or.inl ⟨hp, by decide⟩)
  have hright (q : Pauli) : wordOp ![Pauli.I, q] ∈ S := by
    by_cases hq : q = Pauli.Y
    · simpa [hq] using hG.2.2.1
    · exact real_generators false .I q (Or.inl ⟨by decide, hq⟩)
  intro p q
  rw [← tensor_factors]
  exact generated_closed (frame false) _ (hleft p) _ (hright q)

private def EvenY (w : Fin 2 → Pauli) : Prop :=
  (w 0 ≠ Pauli.Y ∧ w 1 ≠ Pauli.Y) ∨ (w 0 = Pauli.Y ∧ w 1 = Pauli.Y)

private instance : DecidablePred EvenY := fun w => by unfold EvenY; infer_instance

private abbrev RealWord := {w : Fin 2 → Pauli // EvenY w}

private lemma word_entry_parity (p q : Pauli) (x y : Fin 2 → Fin 2) :
    (EvenY ![p, q] → (wordOp ![p, q] x y).im = 0) ∧
    (¬ EvenY ![p, q] → (wordOp ![p, q] x y).re = 0) := by
  generalize h0 : x 0 = x0
  generalize h1 : x 1 = x1
  generalize k0 : y 0 = y0
  generalize k1 : y 1 = y1
  cases p <;> cases q <;>
    fin_cases x0 <;> fin_cases x1 <;> fin_cases y0 <;> fin_cases y1 <;>
    norm_num [EvenY, wordOp, tensorOp, Fin.prod_univ_two, pauliMatrix,
      qubitX, qubitZ, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two, h0, h1, k0, k1]

private lemma real_word_mem (w : RealWord) : wordOp w.1 ∈ realCarrier := by
  refine ⟨word_hermitian w.1, ?_⟩
  have hw : w.1 = ![w.1 0, w.1 1] := by ext i; fin_cases i <;> rfl
  intro x y
  rw [hw]
  apply (word_entry_parity _ _ x y).1
  simpa [EvenY] using w.2

private lemma real_coefficient (A : Op) (hA : A.IsHermitian) (w : Fin 2 → Pauli) :
    (4 : ℂ)⁻¹ * Matrix.trace (wordOp w * A) =
      (((Matrix.trace (wordOp w * A)).re / 4 : ℝ) : ℂ) := by
  have ht := D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.trace_hermitian_product_real
    (wordOp w) A (word_hermitian w) hA
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, ht, div_eq_mul_inv] <;> ring

private lemma hermitian_expansion (A : Op) (hA : A.IsHermitian) :
    A = ∑ w : Fin 2 → Pauli, ((Matrix.trace (wordOp w * A)).re / 4 : ℝ) • wordOp w := by
  calc
    A = ∑ w : Fin 2 → Pauli,
        ((4 : ℂ)⁻¹ * Matrix.trace (wordOp w * A)) • wordOp w := by
      simpa only [show (2 : ℂ) ^ 2 = 4 by norm_num] using word_expansion A
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      rw [real_coefficient A hA w]
      exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

private lemma odd_coefficient_zero (A : realCarrier) (w : Fin 2 → Pauli) (hw : ¬ EvenY w) :
    (Matrix.trace (wordOp w * A.1)).re = 0 := by
  have he : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
  have hr (x y : Fin 2 → Fin 2) : (wordOp w x y).re = 0 := by
    rw [he]
    apply (word_entry_parity _ _ x y).2
    simpa [EvenY] using hw
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.mul_re, hr, A.2.2]

private lemma real_expansion (A : realCarrier) :
    A.1 = ∑ w : RealWord, ((Matrix.trace (wordOp w.1 * A.1)).re / 4 : ℝ) • wordOp w.1 := by
  classical
  have he := hermitian_expansion A.1 A.2.1
  rw [← Fintype.sum_subtype_add_sum_subtype EvenY] at he
  have hz : (∑ w : {w : Fin 2 → Pauli // ¬ EvenY w},
      ((Matrix.trace (wordOp w.1 * A.1)).re / 4 : ℝ) • wordOp w.1) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    rw [odd_coefficient_zero A w.1 w.2]
    simp
  simpa only [hz, add_zero] using he

private lemma complex_closed : JordanClosed complexCarrier := by
  intro A hA B hB
  change (jordan A B).IsHermitian
  change A.IsHermitian at hA
  change B.IsHermitian at hB
  change ((1 / 2 : ℝ) • (A * B + B * A)).IsHermitian
  rw [Matrix.IsHermitian]
  simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    hA.eq, hB.eq, add_comm]

private lemma real_closed : JordanClosed realCarrier := by
  rintro A ⟨hA, hAr⟩ B ⟨hB, hBr⟩
  refine ⟨complex_closed A hA B hB, ?_⟩
  intro x y
  simp [jordan, Matrix.mul_apply, Complex.mul_im, hAr, hBr]

private lemma frame_hermitian (c : Bool) (i : Fin 3) (st : Bits) :
    (frame c i st).IsHermitian := by
  have hproj (A B C : Fin 2 → Pauli) : (proj A B C st).IsHermitian := by
    change (proj A B C st)ᴴ = proj A B C st
    fin_cases st <;>
      norm_num [proj, eps, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
        Matrix.conjTranspose_neg, word_hermitian]
  unfold frame
  split_ifs <;> apply hproj

private lemma real_frame_mem (i : Fin 3) (st : Bits) : frame true i st ∈ realCarrier := by
  have hword (p q : Pauli) (h : EvenY ![p, q]) : wordOp ![p, q] ∈ realCarrier :=
    real_word_mem ⟨![p, q], h⟩
  have hproj (A B C : Fin 2 → Pauli) (hA : wordOp A ∈ realCarrier)
      (hB : wordOp B ∈ realCarrier) (hC : wordOp C ∈ realCarrier) :
      proj A B C st ∈ realCarrier := by
    have hI : (1 : Op) ∈ realCarrier := ⟨Matrix.isHermitian_one, by
      intro x y
      simp only [Matrix.one_apply]
      split_ifs <;> norm_num⟩
    have eps_real (b : Fin 2) : eps b = ((if b = 0 then 1 else -1 : ℝ) : ℂ) := by
      unfold eps; split_ifs <;> simp
    simp only [proj, eps_real, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_ofNat, ← Complex.ofReal_div, ← RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact realCarrier.smul_mem _ (realCarrier.add_mem
      (realCarrier.add_mem (realCarrier.add_mem hI (realCarrier.smul_mem _ hA))
        (realCarrier.smul_mem _ hB)) (realCarrier.smul_mem _ hC))
  fin_cases i <;> simp only [frame, Fin.isValue, ↓reduceIte, Bool.true_eq]
  · exact hproj _ _ _ (hword .Z .I (by decide)) (hword .I .Z (by decide))
      (hword .Z .Z (by decide))
  · exact hproj _ _ _ (hword .X .I (by decide)) (hword .I .X (by decide))
      (hword .X .X (by decide))
  · exact hproj _ _ _ (hword .X .Z (by decide)) (hword .Z .X (by decide))
      (hword .Y .Y (by decide))

/-- The original real triple generates exactly the real symmetric carrier. -/
theorem real_generated : generated (frame true) = realCarrier := by
  apply le_antisymm
  · exact generated_le _ _ real_frame_mem real_closed
  · intro A hA
    have he := real_expansion ⟨A, hA⟩
    change A = _ at he
    rw [he]
    apply Submodule.sum_mem
    intro w _
    apply Submodule.smul_mem
    have he : w.1 = ![w.1 0, w.1 1] := by ext i; fin_cases i <;> rfl
    rw [he]
    exact real_generators true _ _ w.2

/-- The original complex triple generates the whole common Hermitian carrier. -/
theorem complex_generated : generated (frame false) = complexCarrier := by
  apply le_antisymm
  · exact generated_le _ _ (frame_hermitian false) complex_closed
  · intro A hA
    rw [hermitian_expansion A hA]
    apply Submodule.sum_mem
    intro w _
    apply Submodule.smul_mem
    have he : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
    rw [he]
    exact complex_generators _ _

private def realCoordinates : realCarrier ≃ₗ[ℝ] (RealWord → ℝ) := by
  classical
  exact {
    toFun := fun A w => (Matrix.trace (wordOp w.1 * A.1)).re / 4
    invFun := fun f => ⟨∑ w : RealWord, f w • wordOp w.1,
      realCarrier.sum_mem fun w _ => realCarrier.smul_mem _ (real_word_mem w)⟩
    left_inv := fun A => Subtype.ext (real_expansion A).symm
    right_inv := by
      intro f
      funext w
      have heq (u v : RealWord) : u.1 = v.1 ↔ u = v := Subtype.val_injective.eq_iff
      simp [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
        word_trace_pair, heq, Complex.real_smul, show (2 : ℂ) ^ 2 = 4 by norm_num]
    map_add' := by
      intro A B
      funext w
      simp [Matrix.mul_add, Matrix.trace_add, add_div]
    map_smul' := by
      intro r A
      funext w
      simp [Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul]
      ring }

private def qubitIndex : (Fin 2 → Fin 2) ≃ Fin 4 :=
  (Fintype.equivFin (Fin 2 → Fin 2)).trans (finCongr (by decide))

private def complexCoordinates : complexCarrier ≃ₗ[ℝ]
    D5.S3.Quantum.Measurement.BasisMeasurementProjection.HermitianSpace 4 where
  toFun A := ⟨A.1.submatrix qubitIndex.symm qubitIndex.symm,
    (show A.1.IsHermitian from A.2).submatrix _⟩
  invFun A := ⟨A.1.submatrix qubitIndex qubitIndex,
    (show A.1.IsHermitian from A.2).submatrix _⟩
  left_inv A := by apply Subtype.ext; ext x y; simp
  right_inv A := by apply Subtype.ext; ext x y; simp
  map_add' A B := rfl
  map_smul' r A := rfl

/-- Dimensions of the two actual generated real carriers. -/
theorem generated_dimensions :
    Module.finrank ℝ (generated (frame true)) = 10 ∧
      Module.finrank ℝ (generated (frame false)) = 16 := by
  constructor
  · rw [real_generated, realCoordinates.finrank_eq, Module.finrank_fintype_fun_eq_card]
    change Fintype.card {w : Fin 2 → Pauli // EvenY w} = 10
    decide
  · rw [complex_generated, complexCoordinates.finrank_eq,
      D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition.hermitian_space_finrank]
    norm_num


private lemma word_trace (p : Fin 2 → Pauli) :
    Matrix.trace (wordOp p) = if p = (fun _ => Pauli.I) then 4 else 0 := by
  have h := word_trace_pair p (fun _ => Pauli.I)
  rw [word_one, mul_one] at h
  simpa only [show (2 : ℂ) ^ 2 = 4 by norm_num] using h

private lemma word_trace_zero {p : Fin 2 → Pauli} (h : ∃ i, p i ≠ Pauli.I) :
    Matrix.trace (wordOp p) = 0 := by
  rw [word_trace]
  split_ifs with hp
  · obtain ⟨i, hi⟩ := h
    exact False.elim (hi (congrFun hp i))
  · rfl

/-- Both real and complex choices give the same twelve-by-twelve labelled trace table. -/
theorem trace_table (c : Bool) (i j : Fin 3) (st uv : Fin 2 × Fin 2) :
    Matrix.trace (frame c i st * frame c j uv) =
      if i = j then (if st = uv then (1 : ℂ) else 0) else (1 / 4 : ℂ) := by
  have hZI : Matrix.trace (wordOp ![Pauli.Z, Pauli.I]) = 0 :=
    word_trace_zero ⟨0, by decide⟩
  have hIZ : Matrix.trace (wordOp ![Pauli.I, Pauli.Z]) = 0 :=
    word_trace_zero ⟨1, by decide⟩
  have hZZ : Matrix.trace (wordOp ![Pauli.Z, Pauli.Z]) = 0 :=
    word_trace_zero ⟨0, by decide⟩
  have hXI : Matrix.trace (wordOp ![Pauli.X, Pauli.I]) = 0 :=
    word_trace_zero ⟨0, by decide⟩
  have hIX : Matrix.trace (wordOp ![Pauli.I, Pauli.X]) = 0 :=
    word_trace_zero ⟨1, by decide⟩
  have hXX : Matrix.trace (wordOp ![Pauli.X, Pauli.X]) = 0 :=
    word_trace_zero ⟨0, by decide⟩
  have hXZ : Matrix.trace (wordOp ![Pauli.X, Pauli.Z]) = 0 :=
    word_trace_zero ⟨0, by decide⟩
  have hZX : Matrix.trace (wordOp ![Pauli.Z, Pauli.X]) = 0 :=
    word_trace_zero ⟨1, by decide⟩
  have hYY : Matrix.trace (wordOp ![Pauli.Y, Pauli.Y]) = 0 :=
    word_trace_zero ⟨0, by decide⟩
  have hYI : Matrix.trace (wordOp ![Pauli.Y, Pauli.I]) = 0 :=
    word_trace_zero ⟨0, by decide⟩
  have hIY : Matrix.trace (wordOp ![Pauli.I, Pauli.Y]) = 0 :=
    word_trace_zero ⟨1, by decide⟩
  fin_cases c <;> fin_cases i <;> fin_cases j <;> fin_cases st <;> fin_cases uv <;>
    simp [frame, E, F, Gr, Gc, proj, eps, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_one, word_trace_pair, word_trace, hZI, hIZ, hZZ, hXI, hIX,
      hXX, hXZ, hZX, hYY, hYI, hIY] <;>
    norm_num

private lemma frame_mul (c : Bool) (i : Fin 3) (st uv : Bits) :
    frame c i st * frame c i uv = if st = uv then frame c i st else 0 := by
  fin_cases c <;> fin_cases i <;> fin_cases st <;> fin_cases uv <;>
    simp [frame, E, F, Gr, Gc, proj, eps, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, word_two_mul, letterPhase, letterProduct, word_ii] <;>
    module

private lemma frame_sum (c : Bool) (i : Fin 3) : ∑ st : Bits, frame c i st = 1 := by
  have hp (A B C : Fin 2 → Pauli) : ∑ st : Bits, proj A B C st = 1 := by
    simpa only [Fintype.sum_prod_type, Fin.sum_univ_two, add_assoc] using
      (proj_recover A B C).1
  unfold frame
  split_ifs <;> apply hp

private lemma idempotent_rank_one (A : Op) (hA : A * A = A) (ht : Matrix.trace A = 1) :
    A.rank = 1 := by
  have hi : IsIdempotentElem A.toLin' := by
    change A.toLin'.comp A.toLin' = A.toLin'
    rw [← Matrix.toLin'_mul, hA]
  have hr := ((LinearMap.isProj_range_iff_isIdempotentElem A.toLin').mpr hi).trace
  rw [Matrix.trace_toLin'_eq, ht] at hr
  change (1 : ℂ) = (A.rank : ℂ) at hr
  exact_mod_cast hr.symm

/-- Every context is a complete orthogonal frame of four rank-one projectors. -/
theorem frame_complete (c : Bool) : Complete (frame c) := by
  refine ⟨?_, ?_, frame_sum c⟩
  · intro i st
    have hi : frame c i st * frame c i st = frame c i st := by simp [frame_mul]
    have ht : Matrix.trace (frame c i st) = 1 := by
      simpa [hi] using trace_table c i i st st
    exact ⟨frame_hermitian c i st, hi, idempotent_rank_one _ hi ht⟩
  · intro i st uv h
    simpa only [frame_mul, if_neg h]

/-- The whole labelled two-point table cannot determine Jordan closure dimension. -/
theorem result : ¬ claim := by
  rintro ⟨post, hpost⟩
  have ht : table (frame true) = table (frame false) := by
    funext i j st uv
    exact (trace_table true i j st uv).trans (trace_table false i j st uv).symm
  have hr := hpost (frame true) (frame_complete true)
  have hc := hpost (frame false) (frame_complete false)
  rw [generated_dimensions.1] at hr
  rw [generated_dimensions.2] at hc
  rw [ht, hc] at hr
  norm_num at hr

#print axioms frame
#print axioms trace_table
#print axioms real_generated
#print axioms complex_generated
#print axioms generated_dimensions
#print axioms frame_complete
#print axioms result

end D5.S3.Quantum.Tomography.PauliFrameTraceTable
