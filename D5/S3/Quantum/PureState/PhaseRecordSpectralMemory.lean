/- GID: D5/S3/Quantum/PureState/PhaseRecordSpectralMemory
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/PhaseRecordSpectralMemory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The largest dual eigenvalues bound pure-state guessing through finite quantum memory. -/

import D5.S3.Quantum.PureState.PhaseRecordMemory
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Order

/-!
# Spectral upper bounds for pure-state decoding with finite quantum memory

For the standard minimum-error discrimination dual, see Eldar–Megretski–Verghese
(arXiv:quant-ph/0205178, equations (15)–(20) and (26)).
Kennedy's 1974 uniqueness result for linearly independent pure signals gives the
known exact phase memory threshold together with the dimension bound.
The finite spectral-tail refinement in the research note is credited to GPT 6 Pro,
NyxID broker task fa3e253d-6611-433d-99cd-442df97ebcc1.
-/

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Subentropy.GuessingProbability
open JointRecordDecoding PhaseRecordMemory

namespace PhaseRecordSpectralMemory

noncomputable section

variable {ι μ X : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ] [Fintype X]

/-- Keep only the direction of the square-root image of the signal in its effect.
The effect's score on the signal survives and the trace is bounded by the original
effect's expectation on a normalized vector. -/
private theorem compressEffect (E : Matrix ι ι ℂ) (hE : E.PosSemidef)
    (ψ : ι → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ v : ι → ℂ, star v ⬝ᵥ v = 1 →
      (trace (E * rankOneDensity v)).re ≤ b) :
    ∃ F : Matrix ι ι ℂ, 0 ≤ F ∧ F ≤ E ∧
      trace (F * rankOneDensity ψ) = trace (E * rankOneDensity ψ) ∧
      (trace F).re ≤ b := by
  let S := CFC.sqrt E
  have hS : S.PosSemidef := (CFC.sqrt_nonneg E).posSemidef
  have hSH : Sᴴ = S := hS.isHermitian.eq
  have hSS : S * S = E := CFC.sqrt_mul_sqrt_self E hE.nonneg
  let w := S *ᵥ ψ
  by_cases hw : w = 0
  · refine ⟨0, le_rfl, hE.nonneg, ?_, by simpa using hb⟩
    rw [← (pure_state_handshake ψ hψ E).2.2, ← hSS, ← mulVec_mulVec]
    simp [show S *ᵥ ψ = 0 from hw]
  · let a := (star w ⬝ᵥ w).re
    have ha : 0 < a := (Complex.pos_iff.mp (dotProduct_star_self_pos_iff.mpr hw)).1
    have haC : (a : ℂ) = star w ⬝ᵥ w :=
      Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg w)).2)
    let r := Real.sqrt a
    let v := ((r : ℂ)⁻¹) • w
    have hr : r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    have hwr : (r : ℂ) • v = w := by
      simp [v, smul_smul, hrC]
    have hv : star v ⬝ᵥ v = 1 := by
      change star (((r : ℂ)⁻¹) • w) ⬝ᵥ (((r : ℂ)⁻¹) • w) = 1
      rw [star_smul, smul_dotProduct, dotProduct_smul, ← haC]
      simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
      have hrsq : (r : ℂ) * (r : ℂ) = (a : ℂ) := by
        exact_mod_cast Real.mul_self_sqrt ha.le
      field_simp
      simpa only [pow_two] using hrsq.symm
    let P := rankOneDensity v
    have hP : P.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
    have hQ : (1 - P).PosSemidef := by
      have hQH : (1 - P)ᴴ = 1 - P := (Matrix.isHermitian_one.sub hP.isHermitian).eq
      have hPP : P * P = P := (pure_state_handshake v hv P).1
      have hQQ : (1 - P)ᴴ * (1 - P) = 1 - P := by
        rw [hQH, sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, hPP, sub_self, sub_zero]
      rw [← hQQ]
      exact Matrix.posSemidef_conjTranspose_mul_self _
    have hPw : P *ᵥ w = w := by
      rw [← hwr, mulVec_smul]
      congr 1
      simp [P, rankOneDensity, vecMulVec_mulVec, hv]
    let F := S * P * S
    refine ⟨F, (by simpa only [F, hSH] using (hP.conjTranspose_mul_mul_same S).nonneg),
      Matrix.le_iff.mpr ?_, ?_, ?_⟩
    · rw [← hSS, show S * S - F = S * (1 - P) * S by simp [F, mul_sub, sub_mul]]
      simpa only [hSH] using hQ.conjTranspose_mul_mul_same S
    · rw [← (pure_state_handshake ψ hψ F).2.2, ← (pure_state_handshake ψ hψ E).2.2]
      have hFψ : F *ᵥ ψ = E *ᵥ ψ := by
        change (S * P * S) *ᵥ ψ = _
        rw [← hSS, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
        change S *ᵥ (P *ᵥ w) = S *ᵥ w
        rw [hPw]
      rw [hFψ]
    · simpa only [F, trace_mul_comm (S * P) S, ← mul_assoc, hSS] using hbound v hv

/-- Trace against a positive matrix is monotone in the other argument. -/
private theorem tracePair_mono {A B F : Matrix ι ι ℂ} (hF : F.PosSemidef) (hAB : A ≤ B) :
    (trace (F * A)).re ≤ (trace (F * B)).re := by
  have h := RHLinalg.trace_mul_nonneg_of_posSemidef hF (Matrix.le_iff.mp hAB)
  change 0 ≤ (trace (F * (B - A))).re at h
  simpa only [mul_sub, trace_sub, Complex.sub_re, sub_nonneg] using h

private theorem tracePair_smul_one (v : ι → ℂ) (hv : star v ⬝ᵥ v = 1) (c : ℝ) :
    (trace ((c • (1 : Matrix ι ι ℂ)) * rankOneDensity v)).re = c := by
  rw [smul_mul_assoc, one_mul, trace_smul, rankOneDensity, trace_vecMulVec, dotProduct_comm, hv]
  simp

private theorem output_norm_le_trace {D : Matrix μ μ ℂ} (hD : D.PosSemidef) :
    ‖D‖ ≤ (trace D).re := by
  let A : HermitianMat μ ℂ := ⟨D, hD.isHermitian⟩
  have h := HermitianMat.le_trace_smul_one (HermitianMat.zero_le_iff.mpr hD : 0 ≤ A)
  change D ≤ (trace D).re • 1 at h
  apply (CStarAlgebra.norm_le_iff_le_algebraMap D (Complex.nonneg_iff.mp hD.trace_nonneg).1
    hD.nonneg).mpr
  simpa only [Algebra.algebraMap_eq_smul_one] using h

private theorem pullEffect_norm_smul_one (Φ : QuantumChannel ι μ)
    {D : Matrix μ μ ℂ} (hD : D.PosSemidef) : pullEffect Φ D ≤ ‖D‖ • 1 := by
  have h : D ≤ ‖D‖ • 1 := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (IsSelfAdjoint.le_algebraMap_norm_self D (show IsSelfAdjoint D from hD.isHermitian.eq))
  have hsub := pullEffect_posSemidef Φ (Matrix.le_iff.mp h)
  apply Matrix.le_iff.mpr
  have hscalar (c : ℝ) (A : Matrix μ μ ℂ) : c • A = (c : ℂ) • A := by
    ext i j
    simp [Complex.real_smul]
  rw [map_sub, hscalar ‖D‖ 1, map_smul, pullEffect_one] at hsub
  exact hsub

omit [Fintype X] in
/-- Rank-one compression preserves each signal score and bounds each compressed
effect trace by the trace of the corresponding memory effect. -/
theorem exists_memory_effect_family (ψ : X → ι → ℂ)
    (hψ : ∀ x, star (ψ x) ⬝ᵥ ψ x = 1)
    (Φ : QuantumChannel ι μ) (D : X → Matrix μ μ ℂ)
    (hD : ∀ x, (D x).PosSemidef) :
    ∃ F : X → Matrix ι ι ℂ, (∀ x, 0 ≤ F x) ∧
      (∀ x, F x ≤ pullEffect Φ (D x)) ∧
      (∀ x, trace (F x * rankOneDensity (ψ x)) =
        trace (pullEffect Φ (D x) * rankOneDensity (ψ x))) ∧
      (∀ x, (trace (F x)).re ≤ (trace (D x)).re) := by
  let E := fun x => pullEffect Φ (D x)
  have hE (x : X) : (E x).PosSemidef := pullEffect_posSemidef Φ (hD x)
  have hlocal (x : X) : ∃ F : Matrix ι ι ℂ, 0 ≤ F ∧ F ≤ E x ∧
      trace (F * rankOneDensity (ψ x)) = trace (E x * rankOneDensity (ψ x)) ∧
      (trace F).re ≤ (trace (D x)).re := by
    obtain ⟨F, hF, hFE, hscore, htrace⟩ :=
      compressEffect _ (hE x) _ (hψ x) ‖D x‖ (norm_nonneg _) (by
        intro v hv
        have hP : (rankOneDensity v).PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
        have h := tracePair_mono hP (pullEffect_norm_smul_one Φ (hD x))
        rw [trace_mul_comm (rankOneDensity v) (pullEffect Φ (D x)),
          trace_mul_comm (rankOneDensity v) (‖D x‖ • 1), tracePair_smul_one v hv] at h
        exact h)
    exact ⟨F, hF, hFE, hscore, htrace.trans (output_norm_le_trace (hD x))⟩
  choose F hF hFE hscore htrace using hlocal
  exact ⟨F, hF, hFE, hscore, htrace⟩

/-- A finite ensemble encoded into an arbitrary CPTP memory has a trace-budget witness
for every feasible pure-state discrimination dual. -/
theorem exists_memory_effect (p : X → ℝ) (ψ : X → ι → ℂ)
    (hψ : ∀ x, star (ψ x) ⬝ᵥ ψ x = 1) (Y : Matrix ι ι ℂ)
    (hY : ∀ x, ((p x : ℂ) • rankOneDensity (ψ x)) ≤ Y)
    (Φ : QuantumChannel ι μ) (D : X → Matrix μ μ ℂ)
    (hD : ∀ x, (D x).PosSemidef) (hsD : ∑ x, D x = 1) :
    ∃ F : Matrix ι ι ℂ, 0 ≤ F ∧ F ≤ 1 ∧ (trace F).re ≤ Fintype.card μ ∧
      successProbability p (fun x => Φ.mapState (pureState (ψ x) (hψ x))) D ≤
        (trace (F * Y)).re := by
  obtain ⟨F, hF, hFE, hscore, htrace⟩ := exists_memory_effect_family ψ hψ Φ D hD
  refine ⟨∑ x, F x, Finset.sum_nonneg (fun x _ => hF x), ?_, ?_, ?_⟩
  · calc
      ∑ x, F x ≤ ∑ x, pullEffect Φ (D x) := Finset.sum_le_sum (fun x _ => hFE x)
      _ = 1 := sum_pullEffect Φ D hsD
  · rw [trace_sum, Complex.re_sum]
    calc
      ∑ x, (trace (F x)).re ≤ ∑ x, (trace (D x)).re := Finset.sum_le_sum (fun x _ => htrace x)
      _ = Fintype.card μ := by rw [← Complex.re_sum, ← trace_sum, hsD, trace_one]; simp
  · rw [successProbability, Matrix.sum_mul, trace_sum, Complex.re_sum]
    apply Finset.sum_le_sum
    intro x _
    have h := tracePair_mono (hF x).posSemidef (hY x)
    rw [Matrix.mul_smul, trace_smul, hscore x] at h
    rw [pullEffect_trace] at h
    change p x * (trace (D x * channelMatrix Φ (rankOneDensity (ψ x)))).re ≤ _
    simpa only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] using h

omit [DecidableEq ι] in
/-- Bounded nonnegative weights of total mass at most `M` can capture at most the
sum over any set of the `min M (card ι)` largest entries. -/
private theorem weighted_sum_le_top (a w : ι → ℝ) (M : ℕ) (J : Finset ι)
    (hJ : J.card = min M (Fintype.card ι))
    (htop : ∀ i ∈ J, ∀ j ∉ J, a j ≤ a i)
    (ha : ∀ i, 0 ≤ a i) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hw : ∑ i, w i ≤ M) : ∑ i, a i * w i ≤ ∑ i ∈ J, a i := by
  classical
  have hbudget : ∑ i, w i ≤ (J.card : ℝ) := by
    rw [hJ, Nat.cast_min]
    exact le_min hw (by
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hw1 i))
  by_cases hne : J.Nonempty
  · let c := J.inf' hne a
    have hc : 0 ≤ c := Finset.le_inf' hne a fun i _ => ha i
    have hci i (hi : i ∈ J) : c ≤ a i := Finset.inf'_le a hi
    have hjc j (hj : j ∉ J) : a j ≤ c :=
      Finset.le_inf' hne a fun i hi => htop i hi j hj
    let K := Finset.univ \ J
    have split (f : ι → ℝ) : (∑ i ∈ K, f i) + ∑ i ∈ J, f i = ∑ i, f i :=
      Finset.sum_sdiff (Finset.subset_univ J)
    have hmass : (∑ i ∈ K, w i) ≤ ∑ i ∈ J, (1 - w i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      linarith [split w]
    calc
      ∑ i, a i * w i = (∑ i ∈ K, a i * w i) + ∑ i ∈ J, a i * w i := (split _).symm
      _ ≤ c * (∑ i ∈ K, w i) + ∑ i ∈ J, a i * w i := by
        rw [Finset.mul_sum]
        exact add_le_add_left (Finset.sum_le_sum (s := K) fun i hi =>
          mul_le_mul_of_nonneg_right (hjc i (Finset.mem_sdiff.mp hi).2) (hw0 i)) _
      _ ≤ c * (∑ i ∈ J, (1 - w i)) + ∑ i ∈ J, a i * w i :=
        add_le_add_left (mul_le_mul_of_nonneg_left hmass hc) _
      _ ≤ ∑ i ∈ J, a i := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i hi => ?_
        have h := mul_le_mul_of_nonneg_right (hci i hi) (sub_nonneg.mpr (hw1 i))
        linarith
  · have hJ0 := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hJ0, Finset.card_empty, Nat.cast_zero] at hbudget
    have hz i : w i = 0 := le_antisymm
      ((Finset.single_le_sum (fun j _ => hw0 j) (Finset.mem_univ i)).trans hbudget) (hw0 i)
    simp [hz, hJ0]

private theorem trace_diag_mul (a : ι → ℝ) (F : Matrix ι ι ℂ) :
    (trace (F * diagonal fun i => (a i : ℂ))).re = ∑ i, a i * (F i i).re := by
  simp [trace, diag, mul_diagonal, Complex.mul_re, mul_comm]

private theorem trace_diagonal_le_top (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (F : Matrix ι ι ℂ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (M : ℕ)
    (hFtr : (trace F).re ≤ M) (J : Finset ι) (hJ : J.card = min M (Fintype.card ι))
    (htop : ∀ i ∈ J, ∀ j ∉ J, a j ≤ a i) :
    (trace (F * diagonal fun i => (a i : ℂ))).re ≤ ∑ i ∈ J, a i := by
  rw [trace_diag_mul]
  have hf0 i : 0 ≤ (F i i).re :=
    (Complex.nonneg_iff.mp (hF0.posSemidef.diag_nonneg (i := i))).1
  have hf1 i : (F i i).re ≤ 1 := by
    have h := (Complex.nonneg_iff.mp ((Matrix.le_iff.mp hF1).diag_nonneg (i := i))).1
    simpa only [Matrix.sub_apply, one_apply_eq, Complex.sub_re, Complex.one_re, sub_nonneg] using h
  exact weighted_sum_le_top a _ M J hJ htop ha hf0 hf1 (by simpa [trace, diag] using hFtr)

/-- Sum of the largest `min M (card ι)` eigenvalues in Mathlib's decreasing enumeration. -/
def largestEigenvalueSum {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) (M : ℕ) : ℝ :=
  ∑ i : Fin (min M (Fintype.card ι)), hY.eigenvalues₀ (Fin.castLE (min_le_right _ _) i)

private theorem trace_conj_unitary (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    trace (Unitary.conjStarAlgAut ℂ _ U A) = trace A := by
  rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

private theorem trace_le_largestEigenvalueSum {Y F : Matrix ι ι ℂ} (hY : Y.PosSemidef)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (M : ℕ) (hFtr : (trace F).re ≤ M) :
    (trace (F * Y)).re ≤ largestEigenvalueSum hY.isHermitian M := by
  let U := hY.isHermitian.eigenvectorUnitary
  let T := Unitary.conjStarAlgAut ℂ _ (star U)
  let G := T F
  let e := hY.isHermitian.eigenvalues
  have hGY : T Y = diagonal (fun i => (e i : ℂ)) :=
    hY.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hG0 : 0 ≤ G := map_nonneg T hF0
  have hG1 : G ≤ 1 := by simpa [G] using (OrderHomClass.mono T hF1)
  have hGtr : (trace G).re ≤ M := by
    change (trace (Unitary.conjStarAlgAut ℂ _ (star U) F)).re ≤ M
    rwa [trace_conj_unitary]
  have hpair : trace (F * Y) = trace (G * diagonal fun i => (e i : ℂ)) := by
    rw [← hGY, ← show T (F * Y) = G * T Y from map_mul T F Y]
    exact (trace_conj_unitary (star U) (F * Y)).symm
  let equiv : Fin (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (Fintype.card_fin _)
  let emb := (Fin.castLEEmb (min_le_right M (Fintype.card ι))).trans equiv.toEmbedding
  let J := Finset.univ.map emb
  have hJ : J.card = min M (Fintype.card ι) := by simp [J]
  have htop : ∀ i ∈ J, ∀ j ∉ J, e j ≤ e i := by
    intro i hi j hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hi
    have hjge : min M (Fintype.card ι) ≤ (equiv.symm j).val := by
      by_contra! h
      apply hj
      exact Finset.mem_map.mpr ⟨⟨_, h⟩, Finset.mem_univ _, equiv.apply_symm_apply j⟩
    apply hY.isHermitian.eigenvalues₀_antitone
    change (equiv.symm (emb k)).val ≤ (equiv.symm j).val
    exact (show (equiv.symm (emb k)).val < min M (Fintype.card ι) by
      simpa [emb] using k.isLt).le.trans hjge
  rw [hpair]
  have h := trace_diagonal_le_top e hY.eigenvalues_nonneg G hG0 hG1 M hGtr J hJ htop
  simpa [J, Finset.sum_map, emb, e, Matrix.IsHermitian.eigenvalues,
    largestEigenvalueSum, equiv] using h

omit [DecidableEq ι] [Fintype X] in
/-- A dual dominating the weighted signal densities is positive for a nonempty ensemble. -/
theorem pure_dual_posSemidef [Nonempty X] (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (ψ : X → ι → ℂ) (Y : Matrix ι ι ℂ)
    (hY : ∀ x, ((p x : ℂ) • rankOneDensity (ψ x)) ≤ Y) : Y.PosSemidef := by
  let x : X := Classical.choice inferInstance
  have hρ : (rankOneDensity (ψ x)).PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  have hpC : 0 ≤ (p x : ℂ) := Complex.nonneg_iff.mpr ⟨by simpa using hp x, by simp⟩
  have hscaled := hρ.smul hpC
  exact (hscaled.nonneg.trans (hY x)).posSemidef

/-- Any finite pure-state ensemble, arbitrary CPTP encoder and any output POVM
satisfy the upper bound given by the largest eigenvalues of a positive feasible dual.
The sum includes all eigenvalues when the memory dimension is at least the input dimension. -/
theorem pure_success_le_largestEigenvalueSum (p : X → ℝ) (ψ : X → ι → ℂ)
    (hψ : ∀ x, star (ψ x) ⬝ᵥ ψ x = 1) (Y : Matrix ι ι ℂ) (hY0 : Y.PosSemidef)
    (hY : ∀ x, ((p x : ℂ) • rankOneDensity (ψ x)) ≤ Y)
    (Φ : QuantumChannel ι μ) (D : X → Matrix μ μ ℂ)
    (hD : ∀ x, (D x).PosSemidef) (hsD : ∑ x, D x = 1) :
    successProbability p (fun x => Φ.mapState (pureState (ψ x) (hψ x))) D ≤
      largestEigenvalueSum hY0.isHermitian (Fintype.card μ) := by
  obtain ⟨F, hF0, hF1, hFtr, hscore⟩ := exists_memory_effect p ψ hψ Y hY Φ D hD hsD
  exact hscore.trans (trace_le_largestEigenvalueSum hY0 hF0 hF1 _ hFtr)

/-- Uniform phase decoding through any CPTP memory has success at most the amplitude
sum on any set of the largest coordinates, scaled by `S/N`. -/
theorem phase_success_le_top [Nonempty ι] (u : ι → ι → ℂ) (t : ι → ℝ)
    (hu : ∀ j i, ‖u j i‖ = 1) (ht : ∑ i, t i ^ 2 = 1) (ht0 : ∀ i, 0 ≤ t i)
    (Φ : QuantumChannel ι μ) (D : ι → Matrix μ μ ℂ)
    (hD : ∀ j, (D j).PosSemidef) (hsD : ∑ j, D j = 1)
    (J : Finset ι) (hJ : J.card = min (Fintype.card μ) (Fintype.card ι))
    (htop : ∀ i ∈ J, ∀ j ∉ J, t j ≤ t i) :
    successProbability (uniformPrior ι) (fun j => Φ.mapState (phaseState u t hu ht j)) D ≤
      ((∑ i, t i) / Fintype.card ι) * ∑ i ∈ J, t i := by
  let c : ℝ := (Fintype.card ι : ℝ)⁻¹
  let S := ∑ i, t i
  let Y := c • phaseDual t
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => ht0 i)
  have hY (j : ι) : ((uniformPrior ι j : ℂ) • rankOneDensity (phaseVector u t j)) ≤ Y := by
    apply Matrix.le_iff.mpr
    have h := diagonal_sub_rankOne_posSemidef t ht0 (u j) (hu j)
    have hscaled := h.smul hc
    change (c • (phaseDual t - rankOneDensity (phaseVector u t j))).PosSemidef at hscaled
    rw [smul_sub] at hscaled
    exact hscaled
  obtain ⟨F, hF0, hF1, hFtr, hscore⟩ := exists_memory_effect (uniformPrior ι) (phaseVector u t)
    (phaseVector_norm u t hu ht) Y hY Φ D hD hsD
  have hdiag : Y = diagonal (fun i => ((c * S * t i : ℝ) : ℂ)) := by
    rw [show Y = c • phaseDual t from rfl, phaseDual, ← diagonal_smul]
    congr 1
    funext i
    simp [S, mul_assoc]
  have h := trace_diagonal_le_top (fun i => c * S * t i)
    (fun i => mul_nonneg (mul_nonneg hc hS) (ht0 i)) F hF0 hF1 _ hFtr J hJ
    (fun i hi j hj => mul_le_mul_of_nonneg_left (htop i hi j hj) (mul_nonneg hc hS))
  rw [hdiag] at hscore
  simp only [← Finset.mul_sum] at h
  exact hscore.trans (by simpa [S, c, div_eq_inv_mul] using h)

/-- The omitted amplitudes bound the deficit from the full-carrier benchmark
`S²/N`, which is attained for orthogonal phase rows. -/
theorem phase_spectral_tail_gap [Nonempty ι] (u : ι → ι → ℂ) (t : ι → ℝ)
    (hu : ∀ j i, ‖u j i‖ = 1) (ht : ∑ i, t i ^ 2 = 1) (ht0 : ∀ i, 0 ≤ t i)
    (Φ : QuantumChannel ι μ) (D : ι → Matrix μ μ ℂ)
    (hD : ∀ j, (D j).PosSemidef) (hsD : ∑ j, D j = 1)
    (J : Finset ι) (hJ : J.card = min (Fintype.card μ) (Fintype.card ι))
    (htop : ∀ i ∈ J, ∀ j ∉ J, t j ≤ t i) :
    ((∑ i, t i) / Fintype.card ι) * (∑ i ∈ Finset.univ \ J, t i) ≤
      (∑ i, t i) ^ 2 / Fintype.card ι -
        successProbability (uniformPrior ι) (fun j => Φ.mapState (phaseState u t hu ht j)) D := by
  have h := phase_success_le_top u t hu ht ht0 Φ D hD hsD J hJ htop
  have hsum : (∑ i ∈ Finset.univ \ J, t i) + ∑ i ∈ J, t i = ∑ i, t i :=
    Finset.sum_sdiff (Finset.subset_univ J)
  apply (le_sub_iff_add_le).mpr
  calc
    _ ≤ ((∑ i, t i) / Fintype.card ι) * (∑ i ∈ Finset.univ \ J, t i) +
        ((∑ i, t i) / Fintype.card ι) * ∑ i ∈ J, t i := add_le_add_right h _
    _ = (∑ i, t i) ^ 2 / Fintype.card ι := by rw [← mul_add, hsum]; ring

/-- For orthogonal phase rows, the same tail bounds the loss of the optimal output
POVM relative to the actual full-carrier guessing probability. -/
theorem phase_pGuess_spectral_tail_gap [Nonempty ι] (u : ι → ι → ℂ) (t : ι → ℝ)
    (hu : ∀ j i, ‖u j i‖ = 1) (ht : ∑ i, t i ^ 2 = 1) (ht0 : ∀ i, 0 ≤ t i)
    (horth : ∀ i l, ∑ j, u j i * star (u j l) =
      if i = l then (Fintype.card ι : ℂ) else 0)
    (Φ : QuantumChannel ι μ)
    (J : Finset ι) (hJ : J.card = min (Fintype.card μ) (Fintype.card ι))
    (htop : ∀ i ∈ J, ∀ j ∉ J, t j ≤ t i) :
    ((∑ i, t i) / Fintype.card ι) * (∑ i ∈ Finset.univ \ J, t i) ≤
      pGuess (uniformPrior ι) (phaseState u t hu ht) -
        pGuess (uniformPrior ι) (fun j => Φ.mapState (phaseState u t hu ht j)) := by
  let p := uniformPrior ι
  let ρ := fun j => Φ.mapState (phaseState u t hu ht j)
  have hp : ∀ j, 0 ≤ p j := by intro j; dsimp [p, uniformPrior]; positivity
  have hpsum : ∑ j, p j = 1 := by
    simp [p, uniformPrior]
  have hcarrier : pGuess p (phaseState u t hu ht) = (∑ i, t i) ^ 2 / Fintype.card ι := by
    change pGuess (uniformPrior ι) (fun j =>
      pureState (phaseVector u t j) (phaseVector_norm u t hu ht j)) = _
    rw [pGuess_phase u t hu horth ht0 ht, div_eq_inv_mul]
  let tail := ((∑ i, t i) / Fintype.card ι) * (∑ i ∈ Finset.univ \ J, t i)
  have hmem : pGuess p ρ ≤ pGuess p (phaseState u t hu ht) - tail := by
    apply csSup_le (pGuess_bounds p hp hpsum ρ).1
    rintro _ ⟨D, hD, hsD, rfl⟩
    rw [hcarrier]
    have h := phase_spectral_tail_gap u t hu ht ht0 Φ D hD hsD J hJ htop
    change tail ≤ (∑ i, t i) ^ 2 / Fintype.card ι - successProbability p ρ D at h
    linarith
  change tail ≤ pGuess p (phaseState u t hu ht) - pGuess p ρ
  linarith [hmem]

end
end PhaseRecordSpectralMemory
