/- GID: D5/S3/Quantum/Recovery/DiagonalRecordCapacity
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/DiagonalRecordCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact quantum memory dimension for finite diagonal experiments. -/

import D5.S3.Quantum.Recovery.CanonicalPetzEquality
import D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity
import D5.S3.Quantum.Foundation.FinitePreparationChannel
import D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation

/-!
For commuting experiments, the likelihood classes describe the classical sufficient
part of the Koashi–Imoto decomposition (Phys. Rev. A 66, 022318). The fixed-reference
entropy statement uses Petz's sufficiency theorem (Commun. Math. Phys. 105, 123–131).
-/

noncomputable section

namespace D5.S3.Quantum.Recovery.DiagonalRecordCapacity

open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FinitePreparationChannel
open D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation (diagonalState)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Recovery.CanonicalPetzEquality
open D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity

variable {B : Type} [Fintype B] [DecidableEq B] {I : Type*}

/-- A reference probability law and a family supported on its positive coordinates. -/
structure DiagonalExperiment (B : Type) [Fintype B] (I : Type*) where
  reference : B → ℝ
  comparison : I → B → ℝ
  reference_nonneg : ∀ b, 0 ≤ reference b
  reference_sum : ∑ b, reference b = 1
  comparison_nonneg : ∀ i b, 0 ≤ comparison i b
  comparison_sum : ∀ i, ∑ b, comparison i b = 1
  comparison_zero : ∀ i b, reference b = 0 → comparison i b = 0

namespace DiagonalExperiment

variable (D : DiagonalExperiment B I)

def referenceState : DensityState B :=
  diagonalState D.reference D.reference_nonneg D.reference_sum

def comparisonState (i : I) : DensityState B :=
  diagonalState (D.comparison i) (D.comparison_nonneg i) (D.comparison_sum i)

/-- The likelihood vector, evaluated on the positive reference support for counting. -/
def likelihood (b : B) (i : I) : ℝ := D.comparison i b / D.reference b

def likelihoodClasses : Finset (I → ℝ) := by
  classical
  exact (Finset.univ.filter fun b => 0 < D.reference b).image D.likelihood

def PreservesEntropy {d : ℕ} (channel : QuantumChannel B (Fin d)) : Prop :=
  ∀ i, extendedQuantumRelativeEntropy (D.comparisonState i) D.referenceState =
    extendedQuantumRelativeEntropy (channel.mapState (D.comparisonState i))
      (channel.mapState D.referenceState)

/-- The labels enumerate exactly the distinct likelihood vectors on the reference support. -/
def LabelsClasses {n : ℕ} (label : B → Fin n) : Prop :=
  (∀ j, ∃ b, 0 < D.reference b ∧ label b = j) ∧
  ∀ b c, 0 < D.reference b → 0 < D.reference c →
    (label b = label c ↔ D.likelihood b = D.likelihood c)

omit [DecidableEq B] in
private theorem reference_exists_pos : ∃ b, 0 < D.reference b := by
  by_contra! h
  have hzero : ∀ b, D.reference b = 0 := fun b =>
    le_antisymm (h b) (D.reference_nonneg b)
  simpa [hzero] using D.reference_sum

omit [DecidableEq B] in
private theorem comparison_eq_mul (i : I) (b : B) :
    D.comparison i b = D.reference b * D.likelihood b i := by
  by_cases h : D.reference b = 0
  · simp [h, D.comparison_zero i b h]
  · rw [likelihood, mul_div_cancel₀ _ h]

private theorem comparison_supported (i : I) :
    SupportContained (D.comparisonState i) D.referenceState := by
  intro v hv
  change (diagonal fun b => (D.reference b : ℂ)) *ᵥ v = 0 at hv
  change (diagonal fun b => (D.comparison i b : ℂ)) *ᵥ v = 0
  funext b
  have hb : (D.reference b : ℂ) * v b = 0 := by
    simpa only [mulVec_diagonal, Pi.zero_apply] using congrFun hv b
  rw [mulVec_diagonal, Pi.zero_apply]
  rcases mul_eq_zero.mp hb with h | h
  · simp [D.comparison_zero i b (Complex.ofReal_eq_zero.mp h)]
  · simp [h]

omit [DecidableEq B] in
/-- A stochastic recovery that fixes both a reference law and its tilted law
cannot move any positive-reference transition between different likelihoods. -/
private theorem likelihood_eq_of_positive_transition
    (p likelihood : B → ℝ) (K : B → B → ℝ)
    (hp : ∀ b, 0 ≤ p b) (hK : ∀ b c, 0 ≤ K b c)
    (hrow : ∀ b, ∑ c, K b c = 1)
    (href : ∀ c, ∑ b, p b * K b c = p c)
    (htilt : ∀ c, ∑ b, p b * K b c * likelihood b = p c * likelihood c)
    {b c : B} (hpositive : 0 < p b * K b c) : likelihood b = likelihood c := by
  classical
  have hleft (b : B) :
      ∑ c, p b * K b c * likelihood b ^ 2 = p b * likelihood b ^ 2 := by
    calc
      _ = ∑ c, (p b * likelihood b ^ 2) * K b c :=
        Finset.sum_congr rfl (fun _ _ => by ring)
      _ = _ := by rw [← Finset.mul_sum, hrow, mul_one]
  have hright (c : B) :
      ∑ b, p b * K b c * likelihood c ^ 2 = p c * likelihood c ^ 2 := by
    rw [← Finset.sum_mul, href]
  have hcross (c : B) :
      ∑ b, p b * K b c * likelihood b * likelihood c = p c * likelihood c ^ 2 := by
    rw [← Finset.sum_mul, htilt]
    ring
  let gap (b c : B) := p b * K b c * (likelihood b - likelihood c) ^ 2
  have hgap (b c : B) : 0 ≤ gap b c :=
    mul_nonneg (mul_nonneg (hp b) (hK b c)) (sq_nonneg _)
  have ht : ∑ b, ∑ c, gap b c = 0 := by
    have hexpand (b c : B) : gap b c =
        p b * K b c * likelihood b ^ 2 + p b * K b c * likelihood c ^ 2 -
          2 * (p b * K b c * likelihood b * likelihood c) := by
      dsimp [gap]
      ring
    simp only [hexpand, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hleft]
    rw [Finset.sum_comm (f := fun b c => p b * K b c * likelihood c ^ 2)]
    rw [Finset.sum_comm (f := fun b c => p b * K b c * likelihood b * likelihood c)]
    simp only [hright, hcross]
    ring
  have hall := (Fintype.sum_eq_zero_iff_of_nonneg
    (fun b => Finset.sum_nonneg (fun c _ => hgap b c))).mp ht
  have hb : ∑ c, gap b c = 0 := congrFun hall b
  have hc := congrFun ((Fintype.sum_eq_zero_iff_of_nonneg (hgap b)).mp hb) c
  change p b * K b c * (likelihood b - likelihood c) ^ 2 = 0 at hc
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero
    ((mul_eq_zero.mp hc).resolve_left hpositive.ne'))

private def basisState (b : B) : DensityState B :=
  diagonalState (fun c => if c = b then 1 else 0)
    (fun c => by split_ifs <;> norm_num)
    (by simp)

private theorem basisState_matrix (b : B) :
    CStarMatrix.ofMatrix.symm (basisState b).1 = Matrix.single b b 1 := by
  ext i j
  change (diagonal fun c => ((if c = b then 1 else 0 : ℝ) : ℂ)) i j = _
  by_cases hij : i = j
  · subst j
    by_cases hi : b = i
    · subst i
      simp
    · simp [hi, Ne.symm hi]
  · rw [diagonal_apply_ne _ hij, Matrix.single_apply]
    exact (ite_eq_right (fun h => (hij (h.1.symm.trans h.2)).elim)).symm

private theorem basisDecomposition (w : B → ℝ) :
    CStarMatrix.ofMatrix (diagonal fun b => (w b : ℂ)) =
      ∑ b, (w b : ℂ) • (basisState b).1 := by
  apply CStarMatrix.ofMatrixL.symm.injective
  change diagonal (fun b => (w b : ℂ)) =
    CStarMatrix.ofMatrixL.symm (∑ b, (w b : ℂ) • (basisState b).1)
  rw [map_sum, ← Matrix.sum_single_eq_diagonal]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_smul]
  change Matrix.single b b (w b : ℂ) =
    (w b : ℂ) • CStarMatrix.ofMatrix.symm (basisState b).1
  rw [basisState_matrix, Matrix.smul_single, smul_eq_mul, mul_one]

private theorem state_posSemidef {A : Type*} [Fintype A] [DecidableEq A]
    (ρ : DensityState A) :
    (CStarMatrix.ofMatrix.symm ρ.1).PosSemidef :=
  (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.nonnegative :
    0 ≤ CStarMatrix.ofMatrix.symm ρ.1).posSemidef

/-- The channel followed by the basis measurement, applied to each basis input. -/
private def transition (T : QuantumChannel B B) (b c : B) : ℝ :=
  ((T.mapState (basisState b)).1 c c).re

private theorem transition_nonneg (T : QuantumChannel B B) (b c : B) :
    0 ≤ transition T b c :=
  (Complex.nonneg_iff.mp ((state_posSemidef (T.mapState (basisState b))).diag_nonneg
    (i := c))).1

private theorem transition_rows (T : QuantumChannel B B) (b : B) :
    ∑ c, transition T b c = 1 := by
  have h := congrArg Complex.reLm (T.mapState (basisState b)).trace_eq_one
  change Complex.reLm (∑ c, (T.mapState (basisState b)).1 c c) = Complex.reLm 1 at h
  rw [map_sum] at h
  simpa only [transition, Complex.reLm_coe, Complex.one_re] using h

private theorem transition_diagonal (T : QuantumChannel B B)
    (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b = 1) (c : B) :
    ((T.mapState (diagonalState w hw hs)).1 c c).re = ∑ b, w b * transition T b c := by
  have hdecomp : (diagonalState w hw hs).1 = ∑ b, (w b : ℂ) • (basisState b).1 :=
    basisDecomposition w
  let L := CStarMatrix.ofMatrixL.symm.toLinearMap.comp T.toCompletelyPositiveMap.toLinearMap
  change (L (diagonalState w hw hs).1 c c).re = _
  rw [hdecomp, map_sum]
  simp only [map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  change Complex.reLm _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b _
  change ((w b : ℂ) * (T.mapState (basisState b)).1 c c).re =
    w b * ((T.mapState (basisState b)).1 c c).re
  simp [Complex.mul_re]

private theorem stationary_of_recovers (T : QuantumChannel B B)
    (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b = 1)
    (h : T.mapState (diagonalState w hw hs) = diagonalState w hw hs) (c : B) :
    ∑ b, w b * transition T b c = w c := by
  rw [← transition_diagonal T w hw hs, h]
  change ((diagonal fun b => (w b : ℂ)) c c).re = w c
  simp

private theorem label_eq_of_transition {n d : ℕ} {label : B → Fin n}
    (hlabel : D.LabelsClasses label) (encoder : QuantumChannel B (Fin d))
    (recovery : QuantumChannel (Fin d) B)
    (href : recovery.mapState (encoder.mapState D.referenceState) = D.referenceState)
    (hcomp : ∀ i, recovery.mapState (encoder.mapState (D.comparisonState i)) =
      D.comparisonState i)
    {b c : B} (hb : 0 < D.reference b) (hbc : 0 < transition (recovery.comp encoder) b c) :
    label b = label c := by
  let T := recovery.comp encoder
  have hstationary (c : B) : ∑ b, D.reference b * transition T b c = D.reference c :=
    stationary_of_recovers T _ D.reference_nonneg D.reference_sum
      ((QuantumChannel.comp_mapState recovery encoder D.referenceState).trans href) c
  have hc : 0 < D.reference c := by
    rw [← hstationary c]
    exact lt_of_lt_of_le (mul_pos hb hbc) (Finset.single_le_sum
      (fun x _ => mul_nonneg (D.reference_nonneg x) (transition_nonneg T x c))
      (Finset.mem_univ b))
  apply (hlabel.2 b c hb hc).mpr
  funext i
  apply likelihood_eq_of_positive_transition D.reference (fun b => D.likelihood b i)
    (transition T) D.reference_nonneg (transition_nonneg T) (transition_rows T) hstationary
  · intro x
    have h := stationary_of_recovers T _ (D.comparison_nonneg i) (D.comparison_sum i)
      ((QuantumChannel.comp_mapState recovery encoder (D.comparisonState i)).trans (hcomp i)) x
    simp_rw [D.comparison_eq_mul i] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro y _
    ring
  · exact mul_pos hb hbc

private def classProjector {n : ℕ} (label : B → Fin n) (j : Fin n) : Matrix B B ℂ :=
  diagonal fun b => if label b = j then 1 else 0

omit [Fintype B] in
private theorem classProjector_sum {n : ℕ} (label : B → Fin n) :
    ∑ j, classProjector label j = 1 := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [classProjector, Matrix.sum_apply]
  · simp [classProjector, Matrix.sum_apply, diagonal_apply_ne _ h, Matrix.one_apply_ne h]

/-- Common physical recovery forces at least one memory dimension per likelihood class. -/
theorem labels_card_le_of_recovery {n d : ℕ} {label : B → Fin n}
    (hlabel : D.LabelsClasses label) (encoder : QuantumChannel B (Fin d))
    (recovery : QuantumChannel (Fin d) B)
    (href : recovery.mapState (encoder.mapState D.referenceState) = D.referenceState)
    (hcomp : ∀ i, recovery.mapState (encoder.mapState (D.comparisonState i)) =
      D.comparisonState i) :
    n ≤ d := by
  classical
  choose rep hrep hlabelRep using hlabel.1
  let ρ := fun i => encoder.mapState (basisState (rep i))
  let R := actual_kraus_representation recovery
  let E := fun j => krausAdjoint R.kraus (classProjector label j)
  refine finite_memory_history_capacity (fun i => CStarMatrix.ofMatrix.symm (ρ i).1) E
    (fun i => ⟨state_posSemidef (ρ i), (ρ i).trace_eq_one⟩) ?_ ?_ ?_
  · intro j
    apply Matrix.posSemidef_sum
    intro k _
    apply Matrix.PosSemidef.conjTranspose_mul_mul_same
    apply Matrix.PosSemidef.diagonal
    intro b
    change 0 ≤ (if label b = j then (1 : ℂ) else 0)
    split_ifs <;> simp
  · change ∑ j, ∑ k, (R.kraus k)ᴴ * classProjector label j * R.kraus k = 1
    rw [Finset.sum_comm]
    calc
      _ = ∑ k, (R.kraus k)ᴴ * R.kraus k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← Matrix.sum_mul, ← Matrix.mul_sum, classProjector_sum, Matrix.mul_one]
      _ = 1 := R.hkraus
  · intro i j
    rw [Matrix.trace_mul_comm]
    change (_ * krausAdjoint R.kraus (classProjector label j)).trace = _
    rw [actual_kraus_trace_pair recovery]
    let out := (recovery.comp encoder).mapState (basisState (rep i))
    change (CStarMatrix.ofMatrix.symm out.1 * classProjector label j).trace = _
    have hzero (c : B) (hc : label c ≠ i) :
        transition (recovery.comp encoder) (rep i) c = 0 := by
      apply le_antisymm _ (transition_nonneg _ _ _)
      apply le_of_not_gt
      intro hpos
      have heq := D.label_eq_of_transition hlabel encoder recovery href hcomp (hrep i) hpos
      exact hc (heq.symm.trans (hlabelRep i))
    have hentry (c : B) (hc : label c ≠ i) : out.1 c c = 0 :=
      Complex.ext (hzero c hc) (by
        simpa using (Complex.nonneg_iff.mp ((state_posSemidef out).diag_nonneg (i := c))).2.symm)
    have hsum : ∑ c, out.1 c c = 1 := out.trace_eq_one
    simp only [Matrix.trace, Matrix.diag, classProjector, Matrix.mul_diagonal]
    calc
      _ = ∑ c, (if i = j then out.1 c c else 0) := by
        apply Finset.sum_congr rfl
        intro c _
        by_cases hc : label c = i
        · simp [hc]
        · simp [hentry c hc]
      _ = _ := by split_ifs <;> simp [hsum]

private theorem nonempty_of_state {A : Type*} [Fintype A] [DecidableEq A]
    (ρ : DensityState A) : Nonempty A := by
  rcases isEmpty_or_nonempty A with h | h
  · simpa [Matrix.trace] using ρ.trace_eq_one
  · exact h

/-- Fixed-reference Umegaki equality for a family is equivalent to a single
physical recovery channel for the comparison states and reference state. -/
theorem preservesEntropy_iff_recovery {d : ℕ} (encoder : QuantumChannel B (Fin d)) :
    D.PreservesEntropy encoder ↔
      ∃ recovery : QuantumChannel (Fin d) B,
        recovery.mapState (encoder.mapState D.referenceState) = D.referenceState ∧
        ∀ i, recovery.mapState (encoder.mapState (D.comparisonState i)) =
          D.comparisonState i := by
  have : Nonempty B := nonempty_of_state D.referenceState
  have : Nonempty (Fin d) := nonempty_of_state (encoder.mapState D.referenceState)
  constructor
  · intro h
    obtain ⟨recovery, _, href, hs⟩ :=
      supported_entropy_equality_iff_fixed_petz_recovery encoder D.referenceState
    refine ⟨recovery, href, fun i => (hs _ (D.comparison_supported i)).mp ?_⟩
    let M := supported_relative_modular_model encoder _ _ (D.comparison_supported i)
    have hi := h i
    rw [extendedQuantumRelativeEntropy_eq_coe_of_support (D.comparison_supported i),
      extendedQuantumRelativeEntropy_eq_coe_of_support M.outputSupport] at hi
    exact WithTop.coe_inj.mp hi
  · rintro ⟨recovery, href, hcomp⟩ i
    have hback := extended_quantum_relative_entropy_channel_dpi recovery
      (encoder.mapState (D.comparisonState i)) (encoder.mapState D.referenceState)
    rw [href, hcomp i] at hback
    exact le_antisymm hback (extended_quantum_relative_entropy_channel_dpi encoder _ _)

private def classMass {n : ℕ} (label : B → Fin n) (w : B → ℝ) (j : Fin n) : ℝ :=
  ∑ b, if label b = j then w b else 0

omit [DecidableEq B] in
private theorem referenceClassMass_pos {n : ℕ} {label : B → Fin n}
    (hlabel : D.LabelsClasses label) (j : Fin n) : 0 < classMass label D.reference j := by
  obtain ⟨b, hb, hj⟩ := hlabel.1 j
  have hle := Finset.single_le_sum
    (f := fun c => if label c = j then D.reference c else 0)
    (fun c _ => by split_ifs <;> simp [D.reference_nonneg])
    (Finset.mem_univ b)
  rw [ite_eq_left hj] at hle
  exact hb.trans_le hle

private def conditionalReference {n : ℕ} {label : B → Fin n}
    (hlabel : D.LabelsClasses label) (j : Fin n) : DensityState B :=
  diagonalState (fun b => (if label b = j then D.reference b else 0) /
      classMass label D.reference j)
    (fun b => div_nonneg (by split_ifs <;> simp [D.reference_nonneg])
      (D.referenceClassMass_pos hlabel j).le)
    (by rw [← Finset.sum_div]; exact div_self (D.referenceClassMass_pos hlabel j).ne')

omit [DecidableEq B] in
private theorem classMass_mul {n : ℕ} (label : B → Fin n) (w r : B → ℝ)
    (ratio : Fin n → ℝ) (h : ∀ b, w b = r b * ratio (label b)) (j : Fin n) :
    classMass label w j = classMass label r j * ratio j := by
  unfold classMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : label b = j <;> simp [hb, h]

private theorem recover_diagonal {n : ℕ} {label : B → Fin n}
    (hlabel : D.LabelsClasses label)
    (encoder : QuantumChannel B (Fin n)) (decoder : QuantumChannel (Fin n) B)
    (hencode : ∀ X : Matrix B B ℂ,
      CStarMatrix.ofMatrix.symm (encoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        ∑ b, X b b • CStarMatrix.ofMatrix.symm (basisState (label b)).1)
    (hdecode : ∀ Y : Matrix (Fin n) (Fin n) ℂ,
      CStarMatrix.ofMatrix.symm (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix Y)) =
        ∑ j, Y j j • CStarMatrix.ofMatrix.symm (D.conditionalReference hlabel j).1)
    (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b = 1)
    (ratio : Fin n → ℝ) (h : ∀ b, w b = D.reference b * ratio (label b)) :
    decoder.mapState (encoder.mapState (diagonalState w hw hs)) = diagonalState w hw hs := by
  let Y := CStarMatrix.ofMatrix.symm (encoder.mapState (diagonalState w hw hs)).1
  have hdiag (j : Fin n) : Y j j = (classMass label w j : ℂ) := by
    change (CStarMatrix.ofMatrix.symm (encoder.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (diagonal fun b => (w b : ℂ))))) j j = _
    rw [hencode]
    simp only [Matrix.sum_apply, Matrix.smul_apply, diagonal_apply_eq, basisState_matrix,
      classMass, Complex.ofReal_sum, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hbj : label b = j <;> simp [hbj]
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change CStarMatrix.ofMatrix.symm (decoder.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix Y)) = diagonal (fun b => (w b : ℂ))
  rw [hdecode]
  ext b c
  simp only [Matrix.sum_apply, Matrix.smul_apply, hdiag, conditionalReference, diagonalState,
    Equiv.symm_apply_apply, smul_eq_mul]
  by_cases hbc : b = c
  · subst c
    simp only [diagonal_apply_eq, classMass_mul label w D.reference ratio h]
    rw [Finset.sum_eq_single (label b)]
    · rw [ite_eq_left rfl, ← Complex.ofReal_mul, Complex.ofReal_inj, h b]
      have hn := (D.referenceClassMass_pos hlabel (label b)).ne'
      field_simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  · simp [diagonal_apply_ne _ hbc]

/-- Measuring the likelihood class and preparing its basis state gives a physical
encoder. Conditional preparation from the reference law gives a common decoder. -/
theorem recovery_attains_labels {n : ℕ} {label : B → Fin n}
    (hlabel : D.LabelsClasses label) :
    ∃ encoder : QuantumChannel B (Fin n), ∃ decoder : QuantumChannel (Fin n) B,
      decoder.mapState (encoder.mapState D.referenceState) = D.referenceState ∧
      ∀ i, decoder.mapState (encoder.mapState (D.comparisonState i)) = D.comparisonState i := by
  classical
  obtain ⟨encoder, hencode⟩ := finite_preparation_quantum_channel (basisState ∘ label)
  obtain ⟨decoder, hdecode⟩ :=
    finite_preparation_quantum_channel (D.conditionalReference hlabel)
  refine ⟨encoder, decoder, ?_, ?_⟩
  · exact D.recover_diagonal hlabel encoder decoder hencode hdecode
      D.reference D.reference_nonneg D.reference_sum (fun _ => 1) (fun b => (mul_one _).symm)
  · intro i
    choose rep hrep hclass using hlabel.1
    refine D.recover_diagonal hlabel encoder decoder hencode hdecode
      (D.comparison i) (D.comparison_nonneg i) (D.comparison_sum i)
      (fun j => D.likelihood (rep j) i) (fun b => ?_)
    rw [D.comparison_eq_mul i]
    rcases (D.reference_nonneg b).eq_or_lt with hb | hb
    · simp [← hb]
    · rw [congrFun ((hlabel.2 b (rep (label b)) hb (hrep (label b))).mp
        (hclass (label b)).symm) i]

omit [DecidableEq B] in
private theorem mem_likelihoodClasses (v : I → ℝ) :
    v ∈ D.likelihoodClasses ↔ ∃ b, 0 < D.reference b ∧ D.likelihood b = v := by
  classical
  simp [likelihoodClasses, Finset.mem_image]

omit [DecidableEq B] in
/-- Any exact enumeration of the supported classes has the canonical class count. -/
theorem likelihoodClasses_card_of_labels {n : ℕ} {label : B → Fin n}
    (hlabel : D.LabelsClasses label) : D.likelihoodClasses.card = n := by
  classical
  choose rep hrep hclass using hlabel.1
  let f (j : Fin n) : ↥D.likelihoodClasses :=
    ⟨D.likelihood (rep j), (D.mem_likelihoodClasses _).mpr ⟨rep j, hrep j, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro j k hjk
    have h := (hlabel.2 (rep j) (rep k) (hrep j) (hrep k)).mpr (congrArg Subtype.val hjk)
    rwa [hclass j, hclass k] at h
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨b, hb, he⟩ := (D.mem_likelihoodClasses v).mp v.property
    refine ⟨label b, Subtype.ext ?_⟩
    exact ((hlabel.2 (rep (label b)) b (hrep _) hb).mp (hclass _)).trans he
  simpa using (Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

omit [DecidableEq B] in
private theorem exists_class_labels :
    ∃ label : B → Fin D.likelihoodClasses.card, D.LabelsClasses label := by
  classical
  let e : ↥D.likelihoodClasses ≃ Fin D.likelihoodClasses.card :=
    (Fintype.equivFin _).trans (finCongr (Fintype.card_coe _))
  obtain ⟨b₀, hb₀⟩ := D.reference_exists_pos
  let code (b : B) (hb : 0 < D.reference b) : Fin D.likelihoodClasses.card :=
    e ⟨D.likelihood b, (D.mem_likelihoodClasses _).mpr ⟨b, hb, rfl⟩⟩
  let label (b : B) := if h : 0 < D.reference b then code b h else code b₀ hb₀
  refine ⟨label, ?_, ?_⟩
  · intro j
    obtain ⟨b, hb, he⟩ := (D.mem_likelihoodClasses (e.symm j)).mp (e.symm j).property
    refine ⟨b, hb, ?_⟩
    have hsub : (⟨D.likelihood b, (D.mem_likelihoodClasses _).mpr ⟨b, hb, rfl⟩⟩ :
        ↥D.likelihoodClasses) = e.symm j := Subtype.ext he
    simp [label, hb, code, hsub]
  · intro b c hb hc
    simp only [label, dite_eq_left hb, dite_eq_left hc, code, Equiv.apply_eq_iff_eq,
      Subtype.mk.injEq]

/-- The positive-reference likelihood class count is the exact minimum memory
dimension under a common physical recovery of the whole diagonal experiment. -/
theorem sharp_recovery_dimension :
    (∀ {d : ℕ} (encoder : QuantumChannel B (Fin d)) (recovery : QuantumChannel (Fin d) B),
      recovery.mapState (encoder.mapState D.referenceState) = D.referenceState →
      (∀ i, recovery.mapState (encoder.mapState (D.comparisonState i)) = D.comparisonState i) →
      D.likelihoodClasses.card ≤ d) ∧
    ∃ encoder : QuantumChannel B (Fin D.likelihoodClasses.card),
      ∃ recovery : QuantumChannel (Fin D.likelihoodClasses.card) B,
        recovery.mapState (encoder.mapState D.referenceState) = D.referenceState ∧
        ∀ i, recovery.mapState (encoder.mapState (D.comparisonState i)) =
          D.comparisonState i := by
  obtain ⟨label, hlabel⟩ := D.exists_class_labels
  exact ⟨fun encoder recovery => D.labels_card_le_of_recovery hlabel encoder recovery,
    D.recovery_attains_labels hlabel⟩

/-- The exact minimum memory dimension over CPTP encoders preserving every
comparison state's Umegaki relative entropy against the fixed reference. -/
theorem sharp_entropy_dimension :
    (∀ {d : ℕ} (encoder : QuantumChannel B (Fin d)),
      D.PreservesEntropy encoder → D.likelihoodClasses.card ≤ d) ∧
    ∃ encoder : QuantumChannel B (Fin D.likelihoodClasses.card), D.PreservesEntropy encoder := by
  obtain ⟨hlower, encoder, recovery, href, hcomp⟩ := D.sharp_recovery_dimension
  refine ⟨fun channel h => ?_, encoder,
    (D.preservesEntropy_iff_recovery encoder).mpr ⟨recovery, href, hcomp⟩⟩
  obtain ⟨decoder, hr, hc⟩ := (D.preservesEntropy_iff_recovery channel).mp h
  exact hlower channel decoder hr hc

#print axioms sharp_recovery_dimension
#print axioms sharp_entropy_dimension

end DiagonalExperiment

namespace Basis

export _root_.D5.S3.Quantum.Recovery.DiagonalRecordCapacity.DiagonalExperiment
  (basisState basisDecomposition)

end Basis

end D5.S3.Quantum.Recovery.DiagonalRecordCapacity
