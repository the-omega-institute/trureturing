/- GID: D5/S3/Quantum/PredictionDepth/FiniteSequentialWordCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/PredictionDepth/FiniteSequentialWordCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete centered sequential word effects admit dimension-bounded finite certificates. -/

import D5.S3.Quantum.Completion.SequentialWordObservationResidual
import D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/- Library-search audit trail (2026-08-27):
   * Exact family hits `sequentialWordEffect`, `centeredEffect`,
     `traceZeroHermitian`, and `trace_zero_hermitian_finrank` supply the source
     word semantics, canonical centering operation, exact real carrier, and its
     dimension.
   * Exact pinned-Mathlib hit `Submodule.exists_fun_fin_finrank_span_eq`
     extracts the finite spanning subfamily and is applied directly.
   * Repository searches found one private bounded-monotone-rank helper in
     `CenteredEffectStabilityDepthBound`, but no public theorem for arbitrary
     generator words or for the two certificate clauses together.
   * Body-shape searches found no real-linear map from `HermitianSpace` to
     `traceZeroHermitian` built from `centeredEffect`; the public map below wraps
     that canonical operation rather than restating its matrix formula. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate

open D5.S3.Quantum.Completion.SequentialWordObservationResidual
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence
open D5.S3.Quantum.Measurement.BasisMeasurementProjection

local instance matrixNormedAddCommGroup (d : Nat) :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixComplexInnerProductSpace (d : Nat) :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace (d : Nat) :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

private theorem hermitian_trace_eq_re {d : Nat} (effect : HermitianSpace d) :
    Matrix.trace effect.1 = ((Matrix.trace effect.1).re : ℂ) := by
  have heffectStar := effect.2
  change star effect.1 = effect.1 at heffectStar
  have heffect : effect.1ᴴ = effect.1 := by
    simpa only [Matrix.star_eq_conjTranspose] using heffectStar
  have htraceStar : star (Matrix.trace effect.1) = Matrix.trace effect.1 := by
    calc
      star (Matrix.trace effect.1) = Matrix.trace effect.1ᴴ :=
        (Matrix.trace_conjTranspose effect.1).symm
      _ = Matrix.trace effect.1 := by rw [heffect]
  exact (Complex.conj_eq_iff_re.mp htraceStar).symm

private theorem centered_effect_is_hermitian {d : Nat} [NeZero d]
    (effect : HermitianSpace d) : (centeredEffect effect.1).IsHermitian := by
  have heffect : effect.1.IsHermitian := by
    have heffectStar := effect.2
    change star effect.1 = effect.1 at heffectStar
    change effect.1ᴴ = effect.1
    simpa only [Matrix.star_eq_conjTranspose] using heffectStar
  refine heffect.sub ?_
  exact Matrix.IsHermitian.smul (by simp)
    (by
      rw [isSelfAdjoint_iff]
      rw [hermitian_trace_eq_re effect]
      simp)

private theorem centered_effect_trace_zero {d : Nat} [NeZero d]
    (effect : HermitianSpace d) : Matrix.trace (centeredEffect effect.1) = 0 := by
  simp only [centeredEffect, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin]
  change Matrix.trace effect.1 -
    (Matrix.trace effect.1 / (d : ℂ)) * d = 0
  field_simp [show (d : ℂ) ≠ 0 by exact_mod_cast NeZero.ne d]
  simp

/-- Canonical trace removal on the exact real Hermitian carrier, obtained by
corestricting the imported matrix-level `centeredEffect`. -/
def centeredHermitianMap (d : Nat) [NeZero d] :
    HermitianSpace d →ₗ[ℝ] traceZeroHermitian d := by
  refine
    { toFun := fun effect =>
        ⟨⟨centeredEffect effect.1, centered_effect_is_hermitian effect⟩,
          centered_effect_trace_zero effect⟩
      map_add' := ?_
      map_smul' := ?_ }
  · intro first second
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    simp only [centeredEffect, Submodule.coe_add, Matrix.trace_add, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    ring
  · intro scalar effect
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    simp only [centeredEffect, Submodule.coe_smul_of_tower, Matrix.trace_smul,
      Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul,
      Complex.real_smul, RingHom.id_apply]
    ring

private theorem identity_hermitian_ne_zero (d : Nat) [NeZero d] :
    identityHermitian d ≠ 0 := by
  intro hzero
  have hvalue : (1 : Matrix (Fin d) (Fin d) ℂ) = 0 :=
    congrArg Subtype.val hzero
  exact one_ne_zero hvalue

private theorem bounded_monotone_has_equal_step
    (rankAt : Nat → Nat) (terminalRank : Nat)
    (hmono : Monotone rankAt) (hbound : ∀ n, rankAt n ≤ terminalRank) :
    ∃ m ≤ terminalRank - rankAt 0, rankAt m = rankAt (m + 1) := by
  by_contra h
  push Not at h
  let gap := terminalRank - rankAt 0
  have hgrow : ∀ n ≤ gap + 1, rankAt 0 + n ≤ rankAt n := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        have hnGap : n ≤ gap := by omega
        have hle : rankAt n ≤ rankAt (n + 1) := hmono (Nat.le_succ n)
        have hne := h n hnGap
        have hlt : rankAt n < rankAt (n + 1) := lt_of_le_of_ne hle hne
        have hprev := ih (by omega)
        omega
  have hlast := hbound (gap + 1)
  have htooLarge := hgrow (gap + 1) (by omega)
  dsimp [gap] at htooLarge hlast
  omega

/-- If all centered effects generated by finite instrument words span the real
trace-zero Hermitian carrier, then a finite word set of size at most `d^2 - 1`
already spans it, and words of some length at most `d^2 - 1` already span it. -/
theorem finite_sequential_word_certificate
    (d : Nat) [NeZero d] {Alphabet : Type*}
    (instrumentDual : Alphabet → HermitianSpace d →ₗ[ℝ] HermitianSpace d)
    (hcomplete :
      Submodule.span ℝ
          (Set.range fun word : List Alphabet =>
            centeredHermitianMap d (sequentialWordEffect instrumentDual word)) = ⊤) :
    (∃ selected : Finset (List Alphabet),
        selected.card ≤ d ^ 2 - 1 ∧
          Submodule.span ℝ
              (Set.range fun word : selected =>
                centeredHermitianMap d
                  (sequentialWordEffect instrumentDual word.1)) = ⊤) ∧
      ∃ n ≤ d ^ 2 - 1,
        Submodule.span ℝ
            {effect | ∃ word : List Alphabet,
              word.length ≤ n ∧
                effect = centeredHermitianMap d
                  (sequentialWordEffect instrumentDual word)} = ⊤ := by
  classical
  let centeredWords := fun word : List Alphabet =>
    centeredHermitianMap d (sequentialWordEffect instrumentDual word)
  obtain ⟨basisEffects, hbasisMem, hbasisSpan, _hbasisIndependent⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range centeredWords)
  choose chosen hchosen using hbasisMem
  let selected : Finset (List Alphabet) := Finset.univ.image chosen
  have hselectedSpan :
      Submodule.span ℝ
          (Set.range fun word : selected => centeredWords word.1) = ⊤ := by
    apply top_unique
    rw [← hcomplete, ← hbasisSpan]
    apply Submodule.span_mono
    rintro value ⟨i, rfl⟩
    exact
      (show basisEffects i ∈ Set.range (fun word : selected => centeredWords word.1) from
        ⟨⟨chosen i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩,
          hchosen i⟩)
  have hselectedCard : selected.card ≤ d ^ 2 - 1 := by
    calc
      selected.card ≤ Finset.univ.card := Finset.card_image_le
      _ = Module.finrank ℝ
          (Submodule.span ℝ (Set.range centeredWords)) := by simp
      _ = Module.finrank ℝ (traceZeroHermitian d) := by rw [hcomplete, finrank_top]
      _ = d ^ 2 - 1 := trace_zero_hermitian_finrank d
  refine ⟨⟨selected, hselectedCard, hselectedSpan⟩, ?_⟩
  let rawSpace := fun n : Nat =>
    Submodule.span ℝ
      {effect | ∃ word : List Alphabet,
        word.length ≤ n ∧ effect = sequentialWordEffect instrumentDual word}
  let centeredSpace := fun n : Nat =>
    Submodule.span ℝ
      {effect | ∃ word : List Alphabet,
        word.length ≤ n ∧ effect = centeredWords word}
  have hrawMono : Monotone rawSpace := by
    intro m n hmn
    apply Submodule.span_mono
    rintro effect ⟨word, hlength, rfl⟩
    exact ⟨word, hlength.trans hmn, rfl⟩
  have hrawZero : rawSpace 0 = ℝ ∙ identityHermitian d := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro effect ⟨word, hlength, rfl⟩
      have hword : word = [] :=
        List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlength)
      subst word
      exact Submodule.mem_span_singleton_self (identityHermitian d)
    · apply Submodule.span_le.mpr
      intro effect heffect
      rw [Set.mem_singleton_iff] at heffect
      subst effect
      apply Submodule.subset_span
      exact ⟨[], by simp, rfl⟩
  let rankAt := fun n => Module.finrank ℝ (rawSpace n)
  have hrankMono : Monotone rankAt := fun m n hmn =>
    Submodule.finrank_mono (hrawMono hmn)
  have hrankBound : ∀ n, rankAt n ≤ d ^ 2 := by
    intro n
    calc
      rankAt n ≤ Module.finrank ℝ (HermitianSpace d) := Submodule.finrank_le _
      _ = d ^ 2 := hermitian_space_finrank d
  obtain ⟨stableIndex, hstableBound, hstableRank⟩ :=
    bounded_monotone_has_equal_step rankAt (d ^ 2) hrankMono hrankBound
  have hstableSpace : rawSpace stableIndex = rawSpace (stableIndex + 1) :=
    Submodule.eq_of_le_of_finrank_eq
      (hrawMono (Nat.le_succ stableIndex)) hstableRank
  have hstableStep : ∀ n, rawSpace n = rawSpace (n + 1) →
      rawSpace (n + 1) = rawSpace (n + 2) := by
    intro n hstable
    apply le_antisymm
    · exact hrawMono (by omega)
    · apply Submodule.span_le.mpr
      rintro effect ⟨word, hlength, rfl⟩
      cases word with
      | nil =>
          apply Submodule.subset_span
          exact ⟨[], by simp, rfl⟩
      | cons generator rest =>
          have hrestSucc : rest.length ≤ n + 1 := by
            simp only [List.length_cons] at hlength
            omega
          have hrestMem : sequentialWordEffect instrumentDual rest ∈ rawSpace n := by
            rw [hstable]
            apply Submodule.subset_span
            exact ⟨rest, hrestSucc, rfl⟩
          have hmapped : instrumentDual generator
                (sequentialWordEffect instrumentDual rest) ∈ rawSpace (n + 1) := by
            refine Submodule.span_induction
              (p := fun value _ =>
                instrumentDual generator value ∈ rawSpace (n + 1))
              ?_ ?_ ?_ ?_ hrestMem
            · rintro value ⟨shortWord, hshort, rfl⟩
              apply Submodule.subset_span
              refine ⟨generator :: shortWord, ?_, ?_⟩
              · simp only [List.length_cons]
                omega
              · simp [sequentialWordEffect]
            · simpa using Submodule.zero_mem (rawSpace (n + 1))
            · intro first second _ _ hfirst hsecond
              simpa using Submodule.add_mem (rawSpace (n + 1)) hfirst hsecond
            · intro scalar value _ hvalue
              simpa using Submodule.smul_mem (rawSpace (n + 1)) scalar hvalue
          simpa [sequentialWordEffect] using hmapped
  have hconsecutive : ∀ offset,
      rawSpace (stableIndex + offset) = rawSpace (stableIndex + offset + 1) := by
    intro offset
    induction offset with
    | zero => simpa using hstableSpace
    | succ offset ih =>
        simpa only [Nat.add_succ, Nat.add_zero] using
          hstableStep (stableIndex + offset) ih
  have hpermanent : ∀ offset,
      rawSpace (stableIndex + offset) = rawSpace stableIndex := by
    intro offset
    induction offset with
    | zero => simp
    | succ offset ih =>
      calc
          rawSpace (stableIndex + offset.succ) =
              rawSpace (stableIndex + offset) := by
            simpa only [Nat.add_succ, Nat.add_zero] using
              (hconsecutive offset).symm
          _ = rawSpace stableIndex := ih
  have hallRaw : ∀ word : List Alphabet,
      sequentialWordEffect instrumentDual word ∈ rawSpace stableIndex := by
    intro word
    rcases le_total word.length stableIndex with hlength | hlength
    · apply Submodule.subset_span
      exact ⟨word, hlength, rfl⟩
    · obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hlength
      have hword : sequentialWordEffect instrumentDual word ∈ rawSpace word.length := by
        apply Submodule.subset_span
        exact ⟨word, le_rfl, rfl⟩
      rw [hoffset, hpermanent offset] at hword
      exact hword
  have hcenteredOfRaw : ∀ effect : HermitianSpace d,
      effect ∈ rawSpace stableIndex →
        centeredHermitianMap d effect ∈ centeredSpace stableIndex := by
    intro effect heffect
    induction heffect using Submodule.span_induction with
    | mem value hvalue =>
        rcases hvalue with ⟨word, hlength, rfl⟩
        apply Submodule.subset_span
        exact ⟨word, hlength, rfl⟩
    | zero => simpa using Submodule.zero_mem (centeredSpace stableIndex)
    | add first second _ _ hfirst hsecond =>
        simpa using Submodule.add_mem (centeredSpace stableIndex) hfirst hsecond
    | smul scalar value _ hvalue =>
        simpa using Submodule.smul_mem (centeredSpace stableIndex) scalar hvalue
  have hallCentered : ∀ word : List Alphabet,
      centeredWords word ∈ centeredSpace stableIndex := fun word =>
    hcenteredOfRaw (sequentialWordEffect instrumentDual word) (hallRaw word)
  have hcenteredTop : centeredSpace stableIndex = ⊤ := by
    apply top_unique
    rw [← hcomplete]
    apply Submodule.span_le.mpr
    rintro effect ⟨word, rfl⟩
    exact hallCentered word
  have hrawZeroRank : rankAt 0 = 1 := by
    change Module.finrank ℝ (rawSpace 0) = 1
    rw [hrawZero]
    exact finrank_span_singleton (identity_hermitian_ne_zero d)
  have hdepthBound : stableIndex ≤ d ^ 2 - 1 := by
    rw [hrawZeroRank] at hstableBound
    exact hstableBound
  exact ⟨stableIndex, hdepthBound, hcenteredTop⟩

#print axioms centeredHermitianMap
#print axioms finite_sequential_word_certificate

end D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate
