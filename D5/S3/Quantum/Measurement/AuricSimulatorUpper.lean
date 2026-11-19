import D5.S3.Quantum.Measurement.AuricTiltedPermutationGram
import D5.S3.Quantum.Measurement.AuricDiamondBounds

/-! # Complete flagged maps and the matching upper bound for the tilted simulator -/

namespace D5.S3.Quantum.Measurement.AuricSimulatorUpper

open _root_.Matrix
open D5.S3.Quantum.Foundation
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Measurement.AuricProjectiveTree
open D5.S3.Quantum.Measurement.AuricPhaseTwirledGram
open D5.S3.Quantum.Measurement.AuricTiltedSymmetries
open D5.S3.Quantum.Measurement.AuricTiltedPermutationGram
open D5.S3.Quantum.Measurement.AuricCoherentSlack
open D5.S3.Quantum.Measurement.AuricFiveLevelTilt
open D5.S3.Quantum.Measurement.AuricDiamondBounds
open scoped ComplexOrder MatrixOrder

set_option maxRecDepth 4096

noncomputable section

abbrev Level := Fin 5
abbrev Flag := Fin 2
abbrev Phases := Level → Fin 4
abbrev RecordedMap := MatrixMap Level (Flag × Level) ℂ
abbrev ChoiCoord := Level × Level
abbrev FlaggedCoord := (Flag × Level) × Level

def targetKraus (j : Flag) : Matrix Level Level ℂ :=
  diagonal fun i => if i = 4 then (Real.sqrt 2 / 2 : ℝ) else
    if i ∈ Set.range (activeLevel j) then 1 else 0

def flagged (K : Flag → Matrix Level Level ℂ) : RecordedMap :=
  MatrixMap.of_kraus (fun j => flagKraus j (K j)) (fun j => flagKraus j (K j))

def target : RecordedMap := flagged targetKraus

def phasePermutedKraus (c t d b : ℝ) (s v : Flag) (phases : Phases) (j : Flag) :
    Matrix Level Level ℂ :=
  (phaseUnitary phases).val * permutedKraus c t d b s v j * (phaseUnitary phases).valᴴ

def simulatorTerm (c t d b : ℝ) (s v : Flag) (phases : Phases) : RecordedMap :=
  flagged (phasePermutedKraus c t d b s v phases)

def simulator (c t d b : ℝ) : RecordedMap :=
  (1 / 4 : ℂ) • ∑ s : Flag, ∑ v : Flag,
    ((4 : ℂ) ^ Fintype.card Level)⁻¹ • ∑ phases : Phases, simulatorTerm c t d b s v phases

private theorem perm_conjugate (e : Equiv.Perm Level) (K : Matrix Level Level ℂ) :
    (permutationUnitary e).val * K * (permutationUnitary e).valᴴ = K.submatrix e e := by
  change (e.permMatrix ℂ) * K * (e.permMatrix ℂ)ᴴ = _
  rw [Matrix.conjTranspose_permMatrix, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  rfl

/-- Every term of the mixture is the full recorded channel of the same-register protocol. -/
theorem simulatorTerm_realized (c t d b : ℝ) (hc : c ^ 2 + t ^ 2 = 1)
    (hd : d ^ 2 + b ^ 2 = 1) (s v : Flag) (phases : Phases) :
    ∃ p : Protocol Level, ∃ e : Terminal p ≃ Flag,
      (∀ j, flag p (e.symm j) = permuteFlag s j ∧
        kraus p (e.symm j) = phasePermutedKraus c t d b s v phases (permuteFlag s j)) ∧
      ∀ X, CStarMatrix.ofMatrix.symm ((flaggedChannel p).toCompletelyPositiveMap
        (CStarMatrix.ofMatrix X)) = simulatorTerm c t d b s v phases X := by
  obtain ⟨p, e, he⟩ := realizes_phase_permuted_tilt c t d b hc hd
    (permuteLevel s v) (permuteFlag s) phases
  have hK (j : Flag) : flag p (e.symm j) = permuteFlag s j ∧
      kraus p (e.symm j) = phasePermutedKraus c t d b s v phases (permuteFlag s j) := by
    refine ⟨(he j).1, (he j).2.trans ?_⟩
    simp only [phasePermutedKraus, permutedKraus, Equiv.symm_apply_apply]
    change ((phaseUnitary phases).val * (permutationUnitary (permuteLevel s v)).val) *
      tiltedKraus c t d b j *
        ((phaseUnitary phases).val * (permutationUnitary (permuteLevel s v)).val)ᴴ = _
    rw [Matrix.conjTranspose_mul, ← perm_conjugate]
    simp only [Matrix.mul_assoc]
  refine ⟨p, e, hK, fun X => ?_⟩
  rw [flaggedChannel_apply, ← Equiv.sum_comp e.symm]
  simp only [hK, simulatorTerm, flagged, MatrixMap.of_kraus, LinearMap.sum_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  exact Equiv.sum_comp (permuteFlag s) (fun j =>
    flagKraus j (phasePermutedKraus c t d b s v phases j) * X *
      (flagKraus j (phasePermutedKraus c t d b s v phases j))ᴴ)

private theorem trace_flagged (K : Flag → Matrix Level Level ℂ)
    (X : Matrix Level Level ℂ) :
    (flagged K X).trace = ((∑ j, (K j)ᴴ * K j) * X).trace := by
  change (∑ j, flagKraus j (K j) * X * (flagKraus j (K j))ᴴ).trace = _
  rw [Matrix.trace_sum, Finset.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← flagKraus_effect j (K j), Matrix.trace_mul_cycle]

theorem target_trace (X : Matrix Level Level ℂ) : (target X).trace = X.trace := by
  have h : (∑ j, (targetKraus j)ᴴ * targetKraus j) = 1 := by
    rw [Fin.sum_univ_two]
    simp only [targetKraus, diagonal_conjTranspose, diagonal_mul_diagonal]
    ext i k
    by_cases hk : i = k
    · subst k
      simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      have hs := congrArg Complex.ofReal (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
      push_cast at hs
      fin_cases i <;> norm_num [activeLevel, Set.mem_range, Fin.exists_fin_succ, Pi.add_apply,
        Pi.mul_apply, Complex.star_def, ← pow_two]
      linear_combination hs / 2
    · simp only [Matrix.add_apply, Matrix.diagonal_apply_ne _ hk, Matrix.one_apply_ne hk, add_zero]
  rw [target, trace_flagged, h, Matrix.one_mul]

theorem simulatorTerm_trace (c t d b : ℝ) (hc : c ^ 2 + t ^ 2 = 1)
    (hd : d ^ 2 + b ^ 2 = 1) (s v : Flag) (phases : Phases) (X : Matrix Level Level ℂ) :
    (simulatorTerm c t d b s v phases X).trace = X.trace := by
  obtain ⟨p, e, he, _⟩ := simulatorTerm_realized c t d b hc hd s v phases
  have h := flagged_normalized p
  rw [← Equiv.sum_comp e.symm] at h
  simp only [he, flagKraus_effect] at h
  rw [Equiv.sum_comp (permuteFlag s) (fun j =>
    (phasePermutedKraus c t d b s v phases j)ᴴ * phasePermutedKraus c t d b s v phases j)] at h
  rw [simulatorTerm, trace_flagged, h, Matrix.one_mul]

theorem simulator_trace (c t d b : ℝ) (hc : c ^ 2 + t ^ 2 = 1)
    (hd : d ^ 2 + b ^ 2 = 1) (X : Matrix Level Level ℂ) :
    (simulator c t d b X).trace = X.trace := by
  simp only [simulator, LinearMap.smul_apply, LinearMap.sum_apply, Matrix.trace_smul,
    Matrix.trace_sum, simulatorTerm_trace c t d b hc hd, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  norm_num
  ring

private def targetWeight (c a h r : ℝ) : ℝ :=
  (Real.sqrt 2 * ((1-a)*(3+a)/4) + r * (1-Real.sqrt 2*(c/2+(1+a)*h/4))) /
    (2 * Real.sqrt 2 + r)

def matchingWeight (r : WitnessInterval) : ℝ :=
  (Real.sqrt 2 * sectorDifference r (tiltMass r) + r * coherenceDifference r (tiltMass r)) /
    (2 * Real.sqrt 2 + r)

def matchingSimulator (r : WitnessInterval) : RecordedMap :=
  let p := tiltMass r
  let c := Real.sqrt (1 - p)
  let t := Real.sqrt p
  let n := tiltNormalizer r p
  simulator c t (c / n) (r * t / n)


private def gram {n : Type*} (z : n → ℂ) : Matrix n n ℂ := vecMulVec z (star z)

private def inclusion {a m : Type*} [DecidableEq m] (e : a → m) : Matrix m a ℂ :=
  fun i k => if e k = i then 1 else 0

private def extend {a m : Type*} [Fintype a] [DecidableEq m] (e : a → m)
    (G : Matrix a a ℂ) : Matrix m m ℂ :=
  inclusion e * G * (inclusion e)ᴴ

private theorem extend_inside {a m : Type*} [Fintype a] [DecidableEq a] [DecidableEq m]
    {e : a → m} (he : Function.Injective e) (G : Matrix a a ℂ) (i k : a) :
    extend e G (e i) (e k) = G i k := by
  simp [extend, inclusion, Matrix.mul_apply, Matrix.conjTranspose_apply, he.eq_iff]

private theorem extend_out_left {a m : Type*} [Fintype a] [DecidableEq m] {e : a → m}
    (G : Matrix a a ℂ) {i k : m} (hi : i ∉ Set.range e) : extend e G i k = 0 := by
  have h (x : a) : e x ≠ i := fun hx => hi ⟨x, hx⟩
  simp [extend, inclusion, Matrix.mul_apply, h]

private theorem extend_out_right {a m : Type*} [Fintype a] [DecidableEq m] {e : a → m}
    (G : Matrix a a ℂ) {i k : m} (hk : k ∉ Set.range e) : extend e G i k = 0 := by
  have h (x : a) : e x ≠ k := fun hx => hk ⟨x, hx⟩
  simp [extend, inclusion, Matrix.mul_apply, Matrix.conjTranspose_apply, h]

def flagCoord (j : Flag) (p : ChoiCoord) : FlaggedCoord := ((j, p.1), p.2)

private theorem flagCoord_inj (j : Flag) : Function.Injective (flagCoord j) := by
  intro a b h
  exact Prod.ext (congrArg (fun x : FlaggedCoord => x.1.2) h) (congrArg (fun x : FlaggedCoord => x.2) h)

private theorem flagCoord_out {j k : Flag} (h : j ≠ k) (p : ChoiCoord) :
    flagCoord j p ∉ Set.range (flagCoord k) := by
  rintro ⟨q, hq⟩
  exact h (congrArg (fun x : FlaggedCoord => x.1.1) hq).symm

private def flagBlocks (G : Flag → Matrix ChoiCoord ChoiCoord ℂ) :
    Matrix FlaggedCoord FlaggedCoord ℂ :=
  ∑ j, extend (flagCoord j) (G j)

private theorem flagBlocks_same (G : Flag → Matrix ChoiCoord ChoiCoord ℂ)
    (j : Flag) (p q : ChoiCoord) :
    flagBlocks G (flagCoord j p) (flagCoord j q) = G j p q := by
  rw [flagBlocks, Matrix.sum_apply, Finset.sum_eq_single j]
  · exact extend_inside (flagCoord_inj j) _ _ _
  · intro k _ h
    exact extend_out_left _ (flagCoord_out h.symm p)
  · simp

private theorem flagBlocks_diff (G : Flag → Matrix ChoiCoord ChoiCoord ℂ)
    {j k : Flag} (h : j ≠ k) (p q : ChoiCoord) :
    flagBlocks G (flagCoord j p) (flagCoord k q) = 0 := by
  rw [flagBlocks, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hj : j = l
  · exact extend_out_right _ (flagCoord_out (by simpa [← hj] using h.symm) q)
  · exact extend_out_left _ (flagCoord_out hj p)

private theorem choi_flagged_same (K : Flag → Matrix Level Level ℂ)
    (j : Flag) (p q : ChoiCoord) :
    (flagged K).choi_matrix (flagCoord j p) (flagCoord j q) =
      gram (choiVector (K j)) p q := by
  rw [flagged, MatrixMap.choi_of_kraus, Matrix.sum_apply, Finset.sum_eq_single j]
  · simp [gram, flagCoord, flagKraus, choiVector, Matrix.vecMulVec, Pi.star_apply]
  · intro k _ h
    simp [flagCoord, flagKraus, Matrix.vecMulVec, h.symm]
  · simp

private theorem choi_flagged_diff (K : Flag → Matrix Level Level ℂ)
    {j k : Flag} (h : j ≠ k) (p q : ChoiCoord) :
    (flagged K).choi_matrix (flagCoord j p) (flagCoord k q) = 0 := by
  rw [flagged, MatrixMap.choi_of_kraus, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hj : j = l
  · have hk : k ≠ l := by simpa [← hj] using h.symm
    simp [flagKraus, flagCoord, Matrix.vecMulVec, hk]
  · simp [flagKraus, flagCoord, Matrix.vecMulVec, hj]

def coherentCoord (j : Flag) (i : Fin 3) : ChoiCoord :=
  (activeLevel j i, activeLevel j i)

theorem coherentCoord_inj (j : Flag) : Function.Injective (coherentCoord j) := by
  fin_cases j <;> decide

private theorem coherentVector_eq_zero (K : Matrix Level Level ℂ) (j : Flag)
    (hK : ∀ i, i ∉ Set.range (activeLevel j) → K i i = 0)
    (p : ChoiCoord) (hp : p ∉ Set.range (coherentCoord j)) : coherentVector K p = 0 := by
  rcases p with ⟨o, i⟩
  by_cases h : o = i
  · subst i
    have hout : o ∉ Set.range (activeLevel j) := by
      rintro ⟨k, hk⟩
      exact hp ⟨k, by simp [coherentCoord, hk]⟩
    simpa [coherentVector, choiVector] using hK o hout
  · simp [coherentVector, h]

private theorem gram_coherent (K : Matrix Level Level ℂ) (j : Flag)
    (hK : ∀ i, i ∉ Set.range (activeLevel j) → K i i = 0) :
    gram (coherentVector K) =
      extend (coherentCoord j) (gram fun i => K (activeLevel j i) (activeLevel j i)) := by
  ext p q
  by_cases hp : p ∈ Set.range (coherentCoord j)
  · by_cases hq : q ∈ Set.range (coherentCoord j)
    · obtain ⟨i, rfl⟩ := hp
      obtain ⟨k, rfl⟩ := hq
      rw [extend_inside (coherentCoord_inj j)]
      simp [gram, Matrix.vecMulVec, Pi.star_apply, coherentVector, coherentCoord, choiVector]
    · rw [extend_out_right _ hq]
      simp [gram, Matrix.vecMulVec, Pi.star_apply, coherentVector_eq_zero K j hK q hq]
  · rw [extend_out_left _ hp]
    simp [gram, Matrix.vecMulVec, Pi.star_apply, coherentVector_eq_zero K j hK p hp]

private theorem target_outside (j : Flag) (i : Level) (hi : i ∉ Set.range (activeLevel j)) :
    targetKraus j i i = 0 := by
  have h4 : i ≠ 4 := by
    rintro rfl
    apply hi
    refine ⟨2, ?_⟩
    fin_cases j <;> rfl
  simp only [targetKraus, Matrix.diagonal_apply_eq, if_neg h4, if_neg hi]

private theorem gram_target (j : Flag) :
    gram (choiVector (targetKraus j)) = extend (coherentCoord j) targetCoherentGram := by
  have hv : choiVector (targetKraus j) = coherentVector (targetKraus j) := by
    funext p
    by_cases h : p.1 = p.2 <;> simp [coherentVector, choiVector, targetKraus, h, Ne.symm]
  rw [hv, gram_coherent _ j (target_outside j)]
  congr 1
  have h (i : Fin 3) : targetKraus j (activeLevel j i) (activeLevel j i) =
      ((![(1 : ℝ), 1, Real.sqrt 2 / 2] i : ℝ) : ℂ) := by
    have hi : activeLevel j i ∈ Set.range (activeLevel j) := ⟨i, rfl⟩
    simp only [targetKraus, Matrix.diagonal_apply_eq, if_pos hi]
    fin_cases j <;> fin_cases i <;> rfl
  ext i k
  simp only [targetCoherentGram, averagedCoherentGram_apply_aux, gram, vecMulVec_apply,
    Pi.star_apply, h, Complex.star_def, Complex.conj_ofReal]

private def remainder (c t d b : ℝ) (j : Flag) : Matrix ChoiCoord ChoiCoord ℂ :=
  (1 / 4 : ℝ) • ∑ s : Flag, ∑ v : Flag, incoherentGram (permutedKraus c t d b s v j)

private theorem remainder_psd (c t d b : ℝ) (j : Flag) :
    (remainder c t d b j).PosSemidef := by
  apply Matrix.PosSemidef.smul _ (by norm_num)
  exact Matrix.posSemidef_sum _ fun s _ =>
    Matrix.posSemidef_sum _ fun v _ => incoherentGram_psd _

private theorem choi_simulator_same (c t d b : ℝ) (j : Flag) (p q : ChoiCoord) :
    (simulator c t d b).choi_matrix (flagCoord j p) (flagCoord j q) =
      (extend (coherentCoord j) (averagedCoherentGram c (d*c) (b*t)) + remainder c t d b j) p q := by
  have hterm (s v : Flag) (phases : Phases) :
      (simulatorTerm c t d b s v phases).choi_matrix (flagCoord j p) (flagCoord j q) =
        choiVector (phasePermutedKraus c t d b s v phases j) p *
          star (choiVector (phasePermutedKraus c t d b s v phases j) q) := by
    rw [simulatorTerm, choi_flagged_same]
    rfl
  have hphase (s v : Flag) :
      ((4 : ℂ) ^ Fintype.card Level)⁻¹ *
        (∑ phases : Phases,
          (simulatorTerm c t d b s v phases).choi_matrix (flagCoord j p) (flagCoord j q)) =
      (gram (coherentVector (permutedKraus c t d b s v j)) +
        incoherentGram (permutedKraus c t d b s v j)) p q := by
    simp_rw [hterm]
    rw [mul_comm, ← div_eq_mul_inv]
    exact phase_averaged_gram_decomposition (permutedKraus c t d b s v j) p q
  have hsum :
      (1 / 4 : ℂ) * (∑ s : Flag, ∑ v : Flag,
          ((4 : ℂ) ^ Fintype.card Level)⁻¹ *
            ∑ phases : Phases, (simulatorTerm c t d b s v phases).choi_matrix
              (flagCoord j p) (flagCoord j q)) =
      (simulator c t d b).choi_matrix (flagCoord j p) (flagCoord j q) := by
    simp only [simulator, MatrixMap.choi_matrix, flagCoord, LinearMap.sum_apply,
      LinearMap.smul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← hsum]
  simp_rw [hphase, Matrix.add_apply, Finset.sum_add_distrib, mul_add]
  have hquarter (z : ℂ) : (1 / 4 : ℝ) • z = (1 / 4 : ℂ) * z := by
    rw [Complex.real_smul]
    norm_num
  have hrem : remainder c t d b j p q =
      (1 / 4 : ℂ) * ∑ s : Flag, ∑ v : Flag, incoherentGram (permutedKraus c t d b s v j) p q := by
    simp only [remainder, Matrix.smul_apply, Matrix.sum_apply, hquarter]
  rw [hrem]
  congr 1
  simp_rw [gram_coherent _ j (diagonal_zero_outside_active c t d b _ _ j)]
  by_cases hp : p ∈ Set.range (coherentCoord j)
  · by_cases hq : q ∈ Set.range (coherentCoord j)
    · obtain ⟨i, rfl⟩ := hp
      obtain ⟨k, rfl⟩ := hq
      simp_rw [extend_inside (coherentCoord_inj j)]
      rw [← averaged_coherent_block c t d b j]
      simp only [Matrix.smul_apply, Matrix.sum_apply, hquarter, gram]
    · simp_rw [extend_out_right _ hq, Finset.sum_const_zero, mul_zero]
  · simp_rw [extend_out_left _ hp, Finset.sum_const_zero, mul_zero]

private theorem choi_simulator_diff (c t d b : ℝ) {j k : Flag} (h : j ≠ k)
    (p q : ChoiCoord) :
    (simulator c t d b).choi_matrix (flagCoord j p) (flagCoord k q) = 0 := by
  have hterm (s v : Flag) (phases : Phases) :
      (simulatorTerm c t d b s v phases).choi_matrix (flagCoord j p) (flagCoord k q) = 0 :=
    choi_flagged_diff _ h _ _
  simp only [MatrixMap.choi_matrix, flagCoord] at hterm ⊢
  simp only [simulator, LinearMap.smul_apply, LinearMap.sum_apply, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul, hterm, Finset.sum_const_zero, mul_zero]

private theorem choi_slack (c t d b w : ℝ) :
    (((w : ℂ) • target) - (target - simulator c t d b)).choi_matrix =
      flagBlocks (fun j =>
        extend (coherentCoord j) (w • targetCoherentGram -
          (targetCoherentGram - averagedCoherentGram c (d*c) (b*t))) + remainder c t d b j) := by
  ext ⟨⟨j, o⟩, i⟩ ⟨⟨k, o'⟩, i'⟩
  let p : ChoiCoord := (o, i)
  let q : ChoiCoord := (o', i')
  change (((w : ℂ) • target) - (target - simulator c t d b)).choi_matrix
      (flagCoord j p) (flagCoord k q) =
    flagBlocks (fun j => extend (coherentCoord j) (w • targetCoherentGram -
      (targetCoherentGram - averagedCoherentGram c (d*c) (b*t))) + remainder c t d b j)
      (flagCoord j p) (flagCoord k q)
  have h (F G H : RecordedMap) :
      ((w : ℂ) • F - (G - H)).choi_matrix (flagCoord j p) (flagCoord k q) =
        (w : ℂ) * F.choi_matrix (flagCoord j p) (flagCoord k q) -
          (G.choi_matrix (flagCoord j p) (flagCoord k q) -
            H.choi_matrix (flagCoord j p) (flagCoord k q)) := rfl
  rw [h]
  by_cases hj : j = k
  · subst k
    rw [flagBlocks_same, choi_simulator_same, target, choi_flagged_same, gram_target]
    by_cases hp : p ∈ Set.range (coherentCoord j)
    · by_cases hq : q ∈ Set.range (coherentCoord j)
      · obtain ⟨l, hl⟩ := hp
        obtain ⟨m, hm⟩ := hq
        rw [← hl, ← hm]
        simp only [Matrix.add_apply, extend_inside (coherentCoord_inj j), Matrix.sub_apply,
          Matrix.smul_apply, Complex.real_smul]
        ring
      · simp only [Matrix.add_apply, extend_out_right _ hq, mul_zero, zero_add, sub_sub_cancel]
    · simp only [Matrix.add_apply, extend_out_left _ hp, mul_zero, zero_add, sub_sub_cancel]
  · rw [flagBlocks_diff _ hj, choi_simulator_diff _ _ _ _ hj p q]
    simp [target, choi_flagged_diff _ hj]

/-- Choi CP equivalence transfers the padded coherent slack and positive phase remainder
to the complete two-flag error map. -/
theorem simulator_cp_majorized (c t d b r : ℝ) (hr : 0 < r)
    (hmatch : (2-r/Real.sqrt 2) * (1-Real.sqrt 2*(c/2+(1+d*c)*(b*t)/4)) +
      Real.sqrt 2 * r * ((1-c^2-(b*t)^2)/2) - (1-d*c)*(3+d*c)/4 = 0)
    (hpos : (1-d*c)*(3+d*c)/4 ≤ 2*(1-Real.sqrt 2*(c/2+(1+d*c)*(b*t)/4))) :
    (((targetWeight c (d*c) (b*t) r : ℝ) : ℂ) • target -
      (target - simulator c t d b)).IsCompletelyPositive := by
  rw [MatrixMap.choi_PSD_iff_CP_map, choi_slack]
  apply Matrix.posSemidef_sum
  intro j _
  have hcoh := (coherent_flag_majorized c (d*c) (b*t) r hr hmatch hpos)
  have hpad := hcoh.mul_mul_conjTranspose_same (inclusion (coherentCoord j))
  exact (hpad.add (remainder_psd c t d b j)).mul_mul_conjTranspose_same _


theorem matchingSimulator_realized (r : WitnessInterval) (s v : Flag) (phases : Phases) :
    let p := tiltMass r
    let c := Real.sqrt (1 - p)
    let t := Real.sqrt p
    let n := tiltNormalizer r p
    ∃ protocol : Protocol Level, ∃ e : Terminal protocol ≃ Flag,
      (∀ j, flag protocol (e.symm j) = permuteFlag s j ∧
        kraus protocol (e.symm j) =
          phasePermutedKraus c t (c/n) (r*t/n) s v phases (permuteFlag s j)) ∧
      ∀ X, CStarMatrix.ofMatrix.symm ((flaggedChannel protocol).toCompletelyPositiveMap
        (CStarMatrix.ofMatrix X)) = simulatorTerm c t (c/n) (r*t/n) s v phases X := by
  have hr : (1 : ℝ) < r := by linarith [r.property.1]
  have hp := (tiltMass_spec r).1
  have hpUnit : tiltMass r ∈ Set.Icc (0 : ℝ) 1 := ⟨hp.1.le, by linarith [hp.2]⟩
  obtain ⟨hc, hd, _⟩ := tilt_parameters r hr _ hpUnit
  exact simulatorTerm_realized _ _ _ _ hc hd s v phases

/-- The actual finite simulator satisfies the matching unhalved bound on every complex
input and every finite reference system. -/
theorem matchingSimulator_upper (r : WitnessInterval)
    (hm : matchingResidual r (tiltMass r) = 0)
    {R : Type*} [Fintype R] [DecidableEq R]
    (X : Matrix (Level × R) (Level × R) ℂ) :
    FiniteTraceDistance.traceNorm
      (MatrixMap.kron (target - matchingSimulator r) (LinearMap.id : MatrixMap R R ℂ) X) ≤
      2 * matchingWeight r * FiniteTraceDistance.traceNorm X := by
  let p := tiltMass r
  let c := Real.sqrt (1 - p)
  let t := Real.sqrt p
  let n := tiltNormalizer r p
  let d := c / n
  let b := r * t / n
  have hr : (1 : ℝ) < r := by linarith [r.property.1]
  have hr0 : (0 : ℝ) < r := by linarith
  have hp := (tiltMass_spec r).1
  have hpUnit : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp.1.le, by linarith [hp.2]⟩
  obtain ⟨hc, hd, ha, hb, _⟩ := tilt_parameters r hr p hpUnit
  change c ^ 2 + t ^ 2 = 1 at hc
  change d ^ 2 + b ^ 2 = 1 at hd
  change d * c = tiltedActive r p at ha
  change b * t = tiltedSpectator r p at hb
  have hcsq : c ^ 2 = 1 - p := Real.sq_sqrt (sub_nonneg.mpr hpUnit.2)
  have hV : (1 - c ^ 2 - (b*t)^2) / 2 = spectatorDifference r p := by
    rw [hcsq, hb, spectatorDifference]
    ring
  have hU : (1-d*c)*(3+d*c)/4 = sectorDifference r p := by rw [ha, sectorDifference]
  have hC : 1-Real.sqrt 2*(c/2+(1+d*c)*(b*t)/4) = coherenceDifference r p := by
    rw [ha, hb, coherenceDifference]
  have hw : targetWeight c (d*c) (b*t) r = matchingWeight r := by
    unfold targetWeight matchingWeight
    rw [hU, hC]
  have hmajor := simulator_cp_majorized c t d b r hr0
    (by rw [hV, hU, hC]; exact hm)
    (by rw [hU, hC]; exact sectorDifference_le_twice_coherence r)
  rw [hw] at hmajor
  have hn : 1 ≤ n := by
    change 1 ≤ Real.sqrt (1 + ((r : ℝ)^2 - 1)*p)
    apply Real.le_sqrt_of_sq_le
    have h : 0 ≤ (r : ℝ)^2 - 1 := by nlinarith
    nlinarith only [mul_nonneg h hpUnit.1]
  have ha0 : 0 ≤ tiltedActive r p := div_nonneg (sub_nonneg.mpr hpUnit.2) (by linarith)
  have ha1 : tiltedActive r p ≤ 1 :=
    (div_le_iff₀ (show 0 < n by linarith)).2 (by linarith [hpUnit.1])
  have hU0 : 0 ≤ sectorDifference r p := by
    unfold sectorDifference
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr ha1) (by linarith)) (by norm_num)
  have hC0 : 0 ≤ coherenceDifference r p := by
    linarith [sectorDifference_le_twice_coherence r]
  have hw0 : 0 ≤ matchingWeight r := by
    unfold matchingWeight
    exact div_nonneg (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hU0)
      (mul_nonneg hr0.le hC0)) (by positivity)
  let H : RecordedMap := (matchingWeight r : ℂ) • target
  have hH : H.IsCompletelyPositive := by
    rw [MatrixMap.choi_PSD_iff_CP_map]
    have hTarget : target.choi_matrix.PosSemidef :=
      (MatrixMap.choi_PSD_iff_CP_map _).1 (MatrixMap.of_kraus_isCompletelyPositive _)
    have heq : H.choi_matrix = matchingWeight r • target.choi_matrix := by
      ext a b
      rfl
    rw [heq]
    exact hTarget.smul hw0
  have htrace (Y : Matrix Level Level ℂ) : ((target - simulator c t d b) Y).trace = 0 := by
    simp only [LinearMap.sub_apply, Matrix.trace_sub, target_trace,
      simulator_trace c t d b hc hd, sub_self]
  have htraceH (Y : Matrix Level Level ℂ) : (H Y).trace = (matchingWeight r : ℂ) * Y.trace := by
    simp only [H, LinearMap.smul_apply, Matrix.trace_smul, target_trace, smul_eq_mul]
  have hsim : matchingSimulator r = simulator c t d b := rfl
  rw [hsim]
  have hmajorH : (H - (target - simulator c t d b)).IsCompletelyPositive := hmajor
  exact amplified_traceNorm_le_of_completelyPositive_majorant (r := R)
    (target - simulator c t d b) H (matchingWeight r) hH hmajorH htrace htraceH X

/-- The scalar matching equation has a root and the corresponding actual simulator realizes
the upper bound for all finite reference systems with the same choice of the root. -/
theorem exists_matchingSimulator_upper :
    ∃ r : WitnessInterval, matchingResidual r (tiltMass r) = 0 ∧
      ∀ (R : Type) [Fintype R] [DecidableEq R] (X : Matrix (Level × R) (Level × R) ℂ),
        FiniteTraceDistance.traceNorm
          (MatrixMap.kron (target - matchingSimulator r) (LinearMap.id : MatrixMap R R ℂ) X) ≤
          2 * matchingWeight r * FiniteTraceDistance.traceNorm X := by
  obtain ⟨r, hr⟩ := exists_matchingResidual_zero
  exact ⟨r, hr, fun _ _ _ X => matchingSimulator_upper r hr X⟩

#print axioms simulatorTerm_realized
#print axioms matchingSimulator_realized
#print axioms simulator_cp_majorized
#print axioms matchingSimulator_upper
#print axioms exists_matchingSimulator_upper


/-- The two-flag unnormalized Choi score in §3, with weights (1, 1, r)
on each flag's equal-input-and-output coordinates. -/
def choiWitnessScore (r : ℝ) (F : RecordedMap) : ℂ :=
  let z : Fin 3 → ℂ := ![1, 1, (r : ℂ)]
  ∑ j : Flag, ∑ i : Fin 3, ∑ k : Fin 3, z i *
    F.choi_matrix (flagCoord j (coherentCoord j i)) (flagCoord j (coherentCoord j k)) * z k

private theorem simulator_coherent_entry (c t d b : ℝ) (j : Flag) (i k : Fin 3) :
    (simulator c t d b).choi_matrix
      (flagCoord j (coherentCoord j i)) (flagCoord j (coherentCoord j k)) =
      averagedCoherentGram c (d*c) (b*t) i k := by
  rw [choi_simulator_same]
  have hzero (s v : Flag) :
      incoherentGram (permutedKraus c t d b s v j) (coherentCoord j i) (coherentCoord j k) = 0 := by
    by_cases hik : coherentCoord j i = coherentCoord j k
    · rw [hik]
      simp [incoherentGram, coherentCoord]
    · exact Matrix.diagonal_apply_ne _ hik
  simp [Matrix.add_apply, extend_inside (coherentCoord_inj j), remainder, hzero,
    Matrix.smul_apply]

private theorem coherent_simulator_score (c a h r : ℝ) :
    let z : Fin 3 → ℂ := ![1, 1, (r : ℂ)]
    (∑ i : Fin 3, ∑ k : Fin 3, z i * averagedCoherentGram c a h i k * z k) =
      ((((2+r*c)^2+(1+a+r*h)^2)/2 : ℝ) : ℂ) := by
  dsimp only
  push_cast
  simp [Fin.sum_univ_succ, averagedCoherentGram, averagedCoherentGram_apply_aux,
    Matrix.smul_apply, Matrix.add_apply, Complex.real_smul]
  ring

/-- The same simulator saturates the universal terminal score bound. -/
theorem matchingSimulator_score_eq (r : WitnessInterval) :
    choiWitnessScore r (matchingSimulator r) = (tiltScore r (tiltMass r) : ℂ) := by
  let p := tiltMass r
  let c := Real.sqrt (1 - p)
  let t := Real.sqrt p
  let n := tiltNormalizer r p
  let d := c / n
  let b := r * t / n
  have hr : (1 : ℝ) < r := by linarith [r.property.1]
  have hp := (tiltMass_spec r).1
  have hpUnit : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp.1.le, by linarith [hp.2]⟩
  obtain ⟨_, _, _, _, hpar⟩ := tilt_parameters r hr p hpUnit
  change d * c + (r : ℝ) * (b * t) = n at hpar
  change choiWitnessScore _ (simulator c t d b) = _
  unfold choiWitnessScore
  simp_rw [simulator_coherent_entry, coherent_simulator_score]
  rw [tiltScore_eq_branch_sum r p hr hpUnit, Fin.sum_univ_two]
  have he : (1 + d * c + (r : ℝ) * (b * t)) = 1 + n := by linarith only [hpar]
  simp only [he]
  change (((((2 + (r : ℝ) * c)^2 + (1 + n)^2) / 2) : ℝ) : ℂ) +
    (((((2 + (r : ℝ) * c)^2 + (1 + n)^2) / 2) : ℝ) : ℂ) =
      (((2 + (r : ℝ) * c)^2 + (1 + n)^2 : ℝ) : ℂ)
  push_cast
  ring

private theorem coherent_score_difference (c a h r : ℝ) :
    let z : Fin 3 → ℂ := ![1, 1, (r : ℂ)]
    (∑ i : Fin 3, ∑ k : Fin 3, z i *
      (targetCoherentGram - averagedCoherentGram c a h) i k * z k) =
      ((2 * ((1-a)*(3+a)/4) + 2 * Real.sqrt 2 * r *
        (1-Real.sqrt 2*(c/2+(1+a)*h/4)) + r^2 * ((1-c^2-h^2)/2) : ℝ) : ℂ) := by
  dsimp only
  set s := Real.sqrt (2 : ℝ) with hs
  have hs2 : s ^ 2 = 2 := by rw [hs, Real.sq_sqrt (by norm_num)]
  apply Complex.ext <;>
    simp [Fin.sum_univ_succ, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.add_apply, targetCoherentGram, averagedCoherentGram,
      averagedCoherentGram_apply_aux, Complex.real_smul, Complex.mul_re,
      Complex.mul_im, pow_two, ← hs] <;>
    nlinarith only [hs2, congrArg (fun x : ℝ => x * r^2) hs2,
      congrArg (fun x : ℝ => x * r * c) hs2,
      congrArg (fun x : ℝ => x * r * h) hs2,
      congrArg (fun x : ℝ => x * r * a * h) hs2]

/-- The exact same recorded target and simulator used in the norm bound attain
the matching Choi score difference. The normalization in §3 divides by
(r + 2√2)², so the associated probability difference is w. -/
theorem matchingSimulator_choiWitnessScore (r : WitnessInterval)
    (hm : matchingResidual r (tiltMass r) = 0) :
    choiWitnessScore r (target - matchingSimulator r) =
      ((matchingWeight r * (r + 2 * Real.sqrt 2)^2 : ℝ) : ℂ) := by
  let p := tiltMass r
  let c := Real.sqrt (1 - p)
  let t := Real.sqrt p
  let n := tiltNormalizer r p
  let d := c / n
  let b := r * t / n
  have hr : (1 : ℝ) < r := by linarith [r.property.1]
  have hr0 : (0 : ℝ) < r := by linarith
  have hp := (tiltMass_spec r).1
  have hpUnit : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp.1.le, by linarith [hp.2]⟩
  obtain ⟨_, _, ha, hb, _⟩ := tilt_parameters r hr p hpUnit
  change d * c = tiltedActive r p at ha
  change b * t = tiltedSpectator r p at hb
  have hcsq : c ^ 2 = 1 - p := Real.sq_sqrt (sub_nonneg.mpr hpUnit.2)
  have hV : (1 - c ^ 2 - (b*t)^2) / 2 = spectatorDifference r p := by
    rw [hcsq, hb, spectatorDifference]
    ring
  have hU : (1-d*c)*(3+d*c)/4 = sectorDifference r p := by rw [ha, sectorDifference]
  have hC : 1-Real.sqrt 2*(c/2+(1+d*c)*(b*t)/4) = coherenceDifference r p := by
    rw [ha, hb, coherenceDifference]
  have hentry (j : Flag) (i k : Fin 3) :
      (target - matchingSimulator r).choi_matrix
        (flagCoord j (coherentCoord j i)) (flagCoord j (coherentCoord j k)) =
        (targetCoherentGram - averagedCoherentGram c (d*c) (b*t)) i k := by
    have hsim : matchingSimulator r = simulator c t d b := rfl
    have hsub (F G : RecordedMap) (x y : FlaggedCoord) : (F - G).choi_matrix x y =
        F.choi_matrix x y - G.choi_matrix x y := rfl
    rw [hsim, hsub]
    rw [simulator_coherent_entry, target, choi_flagged_same, gram_target,
      extend_inside (coherentCoord_inj j), Matrix.sub_apply]
  unfold choiWitnessScore
  simp_rw [hentry, coherent_score_difference, hU, hV, hC]
  have hcalc := (matching_certificate r (sectorDifference r p) (spectatorDifference r p)
    (coherenceDifference r p) hr0 hm (sectorDifference_le_twice_coherence r)).2
  change _ = matchingWeight r * ((r : ℝ) + 2 * Real.sqrt 2)^2 / 2 at hcalc
  rw [hcalc, Fin.sum_univ_two]
  push_cast
  ring

#print axioms matchingSimulator_choiWitnessScore

end
end D5.S3.Quantum.Measurement.AuricSimulatorUpper
