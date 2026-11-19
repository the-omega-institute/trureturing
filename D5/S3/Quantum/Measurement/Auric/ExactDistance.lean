/- GID: D5/S3/Quantum/Measurement/Auric/ExactDistance
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/ExactDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Matching lower and upper bounds for the original flagged instrument. -/

import D5.S3.Quantum.Measurement.Auric.ScoreReadout
import D5.S3.Quantum.Measurement.Auric.SimulatorUpper

/-! # Matching lower and upper bounds for the original flagged instrument -/

namespace D5.S3.Quantum.Measurement.Auric.ExactDistance

open _root_.Matrix
open D5.S3.Quantum.Foundation
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Measurement.Auric.ProjectiveTree
open D5.S3.Quantum.Measurement.Auric.FiveLevelReadout
  (inputVector witnessFrame two_flag_score_le_trace_error)
open D5.S3.Quantum.Measurement.Auric.DiamondBounds
open D5.S3.Quantum.Measurement.Auric.FiveLevelTilt
open D5.S3.Quantum.Measurement.Auric.ScoreReadout
open D5.S3.Quantum.Measurement.Auric.SimulatorUpper
open D5.S3.Quantum.Measurement.Auric.TiltedPermutationGram (activeLevel)
open D5.S3.Quantum.Measurement.Auric.TiltedInstrument (witnessZero witnessOne)
open scoped ComplexOrder MatrixOrder

private def witnessCoord (j : Flag) : Fin 3 ↪ FlaggedCoord :=
  ⟨fun i => flagCoord j (coherentCoord j i), fun _ _ h =>
    coherentCoord_inj j (Prod.ext
      (congrArg (fun x : FlaggedCoord => x.1.2) h)
      (congrArg (fun x : FlaggedCoord => x.2) h))⟩

private theorem witnessFrame_on_coord (r : ℝ) (j : Flag) (i : Fin 3) :
    witnessFrame r (witnessCoord j i) j = (![1, 1, (r : ℂ)] : Fin 3 → ℂ) i := by
  fin_cases j <;> fin_cases i <;>
    simp [witnessFrame, witnessCoord, flagCoord, coherentCoord, activeLevel,
      witnessZero, witnessOne]

private theorem witnessFrame_off_coord (r : ℝ) (j : Flag) (x : FlaggedCoord)
    (hx : x ∉ Set.range (witnessCoord j)) : witnessFrame r x j = 0 := by
  rcases x with ⟨⟨a, o⟩, i⟩
  by_cases h : a = j
  · subst a
    by_cases hoi : o = i
    · subst o
      fin_cases j <;> fin_cases i <;>
        simp [witnessFrame, witnessZero, witnessOne]
      all_goals
        exfalso
        first
        | exact hx ⟨0, rfl⟩
        | exact hx ⟨1, rfl⟩
        | exact hx ⟨2, rfl⟩
    · by_cases hj : j = 0 <;> simp [witnessFrame, witnessZero, witnessOne, hoi, hj]
  · simp [witnessFrame, h]

private theorem sum_witness_support {a b : Type*} [Fintype a] [Fintype b]
    (e : b ↪ a) (f : a → ℂ) (hf : ∀ x, x ∉ Set.range e → f x = 0) :
    ∑ x, f x = ∑ i, f (e i) := by
  classical
  have h := Finset.sum_subset
    (Finset.subset_univ (Finset.univ.map e))
    (fun x _ hx => hf x (by simpa using hx))
  simpa only [Finset.sum_map] using h.symm

/-- The full weighted output projection and the three active coordinates
evaluate the same Choi witness. -/
theorem measuredScore_eq_choiWitnessScore (r : ℝ) (F : RecordedMap) :
    measuredScore r F = (choiWitnessScore r F).re := by
  unfold measuredScore choiWitnessScore
  apply congrArg Complex.re
  have hsum (j : Flag) :
      ((witnessFrame r)ᴴ * F.choi_matrix * witnessFrame r) j j =
        ∑ i : Fin 3, ∑ k : Fin 3, (![1, 1, (r : ℂ)] : Fin 3 → ℂ) i *
          F.choi_matrix (flagCoord j (coherentCoord j i)) (flagCoord j (coherentCoord j k)) *
          (![1, 1, (r : ℂ)] : Fin 3 → ℂ) k := by
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, ← mul_assoc]
    rw [sum_witness_support (witnessCoord j)]
    · apply Finset.sum_congr rfl
      intro i _
      rw [sum_witness_support (witnessCoord j)]
      · apply Finset.sum_congr rfl
        intro k _
        have hr (l : Fin 3) : star ((![1, 1, (r : ℂ)] : Fin 3 → ℂ) l) =
            (![1, 1, (r : ℂ)] : Fin 3 → ℂ) l := by fin_cases l <;> simp
        rw [witnessFrame_on_coord, witnessFrame_on_coord, hr]
        rfl
      · intro x hx
        rw [witnessFrame_off_coord r j x hx, mul_zero]
    · intro x hx
      simp [witnessFrame_off_coord r j x hx]
  simp only [Matrix.trace, Matrix.diag, hsum]

private theorem choi_sum {s : Type*} [Fintype s] (F : s → RecordedMap) :
    (∑ i, F i).choi_matrix = ∑ i, (F i).choi_matrix := by
  ext ⟨o, x⟩ ⟨p, y⟩
  simp only [MatrixMap.choi_matrix, LinearMap.sum_apply, Matrix.sum_apply]

private theorem choi_smul (c : ℝ) (F : RecordedMap) :
    ((c : ℂ) • F).choi_matrix = c • F.choi_matrix := by
  ext ⟨o, x⟩ ⟨p, y⟩
  simp only [MatrixMap.choi_matrix, LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.real_smul]

private theorem measuredScore_sum {s : Type*} [Fintype s] (r : ℝ) (F : s → RecordedMap) :
    measuredScore r (∑ i, F i) = ∑ i, measuredScore r (F i) := by
  simp only [measuredScore, choi_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum,
    Complex.re_sum]

private theorem measuredScore_smul (r c : ℝ) (F : RecordedMap) :
    measuredScore r ((c : ℂ) • F) = c * measuredScore r F := by
  simp only [measuredScore, choi_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem measuredScore_sub (r : ℝ) (F G : RecordedMap) :
    measuredScore r (F - G) = measuredScore r F - measuredScore r G := by
  have h : (F - G).choi_matrix = F.choi_matrix - G.choi_matrix := rfl
  simp only [measuredScore, h, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]

/-- A finite input-independent draw of a deterministic projective strategy. -/
def FiniteProtocolMixture (F : RecordedMap) : Prop :=
  ∃ (m : ℕ) (p : Fin m → Protocol Level) (w : Fin m → ℝ),
    (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ F = ∑ i, (w i : ℂ) • protocolMap (p i)

theorem FiniteProtocolMixture.cp {F : RecordedMap} (hF : FiniteProtocolMixture F) :
    F.IsCompletelyPositive := by
  obtain ⟨m, p, w, hw, _, rfl⟩ := hF
  rw [MatrixMap.choi_PSD_iff_CP_map, choi_sum]
  apply Matrix.posSemidef_sum
  intro i _
  rw [choi_smul]
  exact ((MatrixMap.choi_PSD_iff_CP_map _).1 (protocolMap_cp (p i))).smul (hw i)

theorem FiniteProtocolMixture.tp {F : RecordedMap} (hF : FiniteProtocolMixture F) :
    F.IsTracePreserving := by
  obtain ⟨m, p, w, _, hsum, rfl⟩ := hF
  intro X
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Matrix.trace_sum, Matrix.trace_smul,
    fun i => protocolMap_tp (p i) X, smul_eq_mul, ← Finset.sum_mul, ← Complex.ofReal_sum, hsum,
    Complex.ofReal_one, one_mul]

theorem FiniteProtocolMixture.score_le {F : RecordedMap} (hF : FiniteProtocolMixture F)
    (r : WitnessInterval) : measuredScore r F ≤ tiltScore r (tiltMass r) := by
  obtain ⟨m, p, w, hw, hsum, rfl⟩ := hF
  rw [measuredScore_sum]
  simp_rw [measuredScore_smul]
  calc
    _ ≤ ∑ i, w i * tiltScore r (tiltMass r) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (measuredScore_protocolMap_le r _) (hw i)
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

/-- The fixed normalized purification lower-bounds the unhalved error
of every finite randomized projective protocol by the same value. -/
theorem matching_lower_bound (r : WitnessInterval) (hr : matchingResidual r (tiltMass r) = 0)
    (F : RecordedMap) (hF : FiniteProtocolMixture F) :
    2 * matchingWeight r ≤ FiniteTraceDistance.traceNorm
      (MatrixMap.kron (target - F) (LinearMap.id : MatrixMap Level Level ℂ)
        (vecMulVec (inputVector r) (star (inputVector r)))) := by
  have ht : target.IsCompletelyPositive := MatrixMap.of_kraus_isCompletelyPositive _
  have hr0 : (0 : ℝ) < r := by linarith [r.property.1]
  have h := two_flag_score_le_trace_error r hr0 target F ht hF.cp
    (fun X => (target_trace X).trans (hF.tp X).symm)
  change 2 * (((r : ℝ) + 2 * Real.sqrt 2)⁻¹)^2 * measuredScore r (target - F) ≤ _ at h
  have hmax : measuredScore r F ≤ measuredScore r (matchingSimulator r) := by
    rw [measuredScore_eq_choiWitnessScore (r : ℝ) (matchingSimulator r),
      matchingSimulator_score_eq, Complex.ofReal_re]
    exact hF.score_le r
  have hd : measuredScore r (target - matchingSimulator r) ≤ measuredScore r (target - F) := by
    rw [measuredScore_sub, measuredScore_sub]
    exact sub_le_sub_left hmax _
  rw [measuredScore_eq_choiWitnessScore, matchingSimulator_choiWitnessScore r hr,
    Complex.ofReal_re] at hd
  have hn : (r : ℝ) + 2 * Real.sqrt 2 ≠ 0 := by positivity
  calc
    2 * matchingWeight r =
        2 * (((r : ℝ) + 2 * Real.sqrt 2)⁻¹)^2 *
          (matchingWeight r * ((r : ℝ) + 2 * Real.sqrt 2)^2) := by field_simp [hn]
    _ ≤ _ := (mul_le_mul_of_nonneg_left hd (by positivity)).trans h

private abbrev SimulatorDraw := Flag × Flag × Phases

private theorem protocolMap_apply (p : Protocol Level) (X : Matrix Level Level ℂ) :
    protocolMap p X = CStarMatrix.ofMatrix.symm
      ((flaggedChannel p).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) := by
  rw [flaggedChannel_apply]
  simp only [protocolMap, MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk]

/-- The minimizing map is an input-independent finite draw of allowed
one-measurement protocols on the original register. -/
theorem matchingSimulator_finite (r : WitnessInterval) :
    FiniteProtocolMixture (matchingSimulator r) := by
  classical
  let p := tiltMass r
  let c := Real.sqrt (1 - p)
  let t := Real.sqrt p
  let n := tiltNormalizer r p
  let T (a : SimulatorDraw) := simulatorTerm c t (c/n) (r*t/n) a.1 a.2.1 a.2.2
  have hreal (a : SimulatorDraw) : ∃ q : Protocol Level, protocolMap q = T a := by
    obtain ⟨q, _, _, h⟩ := matchingSimulator_realized r a.1 a.2.1 a.2.2
    refine ⟨q, LinearMap.ext fun X => ?_⟩
    exact (protocolMap_apply q X).trans (h X)
  choose q hq using hreal
  let m := Fintype.card SimulatorDraw
  let e := Fintype.equivFin SimulatorDraw
  have hm : m = 4096 := by
    simp [m, Fintype.card_fin, Fintype.card_prod]
  refine ⟨m, q ∘ e.symm, fun _ => (1 / 4096 : ℝ), fun _ => by positivity, ?_, ?_⟩
  · simp [Fintype.card_fin, hm]
  · have he := e.symm.sum_comp (fun a => (1 / 4096 : ℂ) • protocolMap (q a))
    simp only [hq] at he
    have hweight : ((1 / 4096 : ℝ) : ℂ) = (1 / 4096 : ℂ) := by norm_num
    change matchingSimulator r = ∑ i : Fin m, ((1 / 4096 : ℝ) : ℂ) • protocolMap (q (e.symm i))
    simp_rw [hweight, hq]
    rw [he, Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, T, ← Finset.smul_sum]
    change simulator c t _ _ = _
    unfold simulator
    rw [Fintype.card_fin]
    simp only [← Finset.smul_sum, smul_smul]
    have hw : (1 / 4 : ℂ) * ((4 : ℂ) ^ 5)⁻¹ = 1 / 4096 := by norm_num
    rw [hw]

/-- One root of the matching equation has a finite simulator attaining
the sharp upper bound, while a single normalized input certifies the same
lower bound against every finite randomized protocol. -/
theorem exact_finite_protocol_distance :
    ∃ r : WitnessInterval, matchingResidual r (tiltMass r) = 0 ∧
      FiniteProtocolMixture (matchingSimulator r) ∧
      (vecMulVec (inputVector r) (star (inputVector r))).trace = 1 ∧
      (∀ F, FiniteProtocolMixture F →
        2 * matchingWeight r ≤ FiniteTraceDistance.traceNorm
          (MatrixMap.kron (target - F) (LinearMap.id : MatrixMap Level Level ℂ)
            (vecMulVec (inputVector r) (star (inputVector r))))) ∧
      ∀ (R : Type) [Fintype R] [DecidableEq R] (X : Matrix (Level × R) (Level × R) ℂ),
        FiniteTraceDistance.traceNorm
          (MatrixMap.kron (target - matchingSimulator r) (LinearMap.id : MatrixMap R R ℂ) X) ≤
          2 * matchingWeight r * FiniteTraceDistance.traceNorm X := by
  obtain ⟨r, hr⟩ := exists_matchingResidual_zero
  have hr0 : (0 : ℝ) < r := by linarith [r.property.1]
  exact ⟨r, hr, matchingSimulator_finite r,
    D5.S3.Quantum.Measurement.Auric.FiveLevelReadout.input_purification_trace r hr0,
    matching_lower_bound r hr, fun _ _ _ X => matchingSimulator_upper r hr X⟩

end D5.S3.Quantum.Measurement.Auric.ExactDistance
