import D5.S3.Quantum.Measurement.AuricProjectionFrames
import D5.S3.Quantum.Measurement.AuricRankThreeTwoScratch
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Unitary

/-! # Reduction of flagged terminal scores to normalized compressed branches -/

namespace D5.S3.Quantum.Measurement.AuricProtocolScore

open _root_.Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Measurement.AuricBranchDual
open D5.S3.Quantum.Measurement.AuricRankOneFour
open D5.S3.Quantum.Measurement.AuricRankThreeTwo
open D5.S3.Quantum.Measurement.AuricFiveLevelTilt
open D5.S3.Quantum.Measurement.AuricProjectiveTree
open scoped ComplexOrder

private def flaggedKrausMap {a i : Type*} [Fintype a] [DecidableEq a] [Fintype i]
    (f : i → Fin 2) (K : i → Matrix (Fin 5) a ℂ) (j : Fin 2) : MatrixMap a (Fin 5) ℂ :=
  let L := fun h => if f h = j then K h else 0
  MatrixMap.of_kraus L L

private theorem flaggedKrausMap_cp {a i : Type*} [Fintype a] [DecidableEq a] [Fintype i]
    (f : i → Fin 2) (K : i → Matrix (Fin 5) a ℂ) (j : Fin 2) :
    (flaggedKrausMap f K j).IsCompletelyPositive :=
  MatrixMap.of_kraus_isCompletelyPositive _

private theorem flaggedKrausMap_tp {a i : Type*} [Fintype a] [DecidableEq a] [Fintype i]
    (f : i → Fin 2) (K : i → Matrix (Fin 5) a ℂ) (hK : ∑ h, (K h)ᴴ * K h = 1) :
    (∑ j, flaggedKrausMap f K j).IsTracePreserving := by
  have hsum : (∑ j, flaggedKrausMap f K j) = MatrixMap.of_kraus K K := by
    ext X u v
    simp only [flaggedKrausMap, MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.sum_eq_single (f h)]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  rw [hsum]
  exact MatrixMap.IsTracePreserving.of_kraus_isTracePreserving K K hK

private theorem flaggedKrausMap_score {a i : Type*} [Fintype a] [DecidableEq a] [Fintype i]
    (D : Fin 2 → Matrix (Fin 5) a ℂ)
    (f : i → Fin 2) (K : i → Matrix (Fin 5) a ℂ) :
    flaggedChoiScore D (flaggedKrausMap f K) = ∑ h, ‖((D (f h))ᴴ * K h).trace‖ ^ 2 := by
  unfold flaggedKrausMap
  rw [flaggedChoiScore_of_kraus]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_eq_single (f h)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

private theorem compressedKraus_normalized {m : ℕ} {i : Type*} [Fintype i]
    (K : i → Matrix (Fin 5) (Fin 5) ℂ) (V : Matrix (Fin 5) (Fin m) ℂ)
    (hV : Vᴴ * V = 1) (hK : ∑ h, (K h)ᴴ * K h = V * Vᴴ) :
    ∑ h, (K h * V)ᴴ * (K h * V) = 1 := by
  have he (h : i) : (K h * V)ᴴ * (K h * V) = Vᴴ * ((K h)ᴴ * K h) * V := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  simp_rw [he, ← Matrix.sum_mul, ← Matrix.mul_sum, hK]
  rw [← Matrix.mul_assoc Vᴴ V Vᴴ, hV, Matrix.one_mul, hV]

private theorem compressedKraus_pairing {m : ℕ}
    (K D : Matrix (Fin 5) (Fin 5) ℂ) (V : Matrix (Fin 5) (Fin m) ℂ)
    (hK : K * (V * Vᴴ) = K) :
    ((D * V)ᴴ * (K * V)).trace = (Dᴴ * K).trace := by
  rw [Matrix.conjTranspose_mul, Matrix.trace_mul_cycle Vᴴ Dᴴ (K * V),
    Matrix.mul_assoc K V Vᴴ, hK, Matrix.trace_mul_comm K Dᴴ]

private theorem compressedKraus_score {m : ℕ} {i : Type*} [Fintype i]
    (r : WitnessInterval) (f : i → Fin 2) (K : i → Matrix (Fin 5) (Fin 5) ℂ)
    (V : Matrix (Fin 5) (Fin m) ℂ) (hK : ∀ h, K h * (V * Vᴴ) = K h) :
    flaggedChoiScore (fun j => flagTest r j * V)
      (flaggedKrausMap f (fun h => K h * V)) =
      ∑ h, ‖((flagTest r (f h))ᴴ * K h).trace‖ ^ 2 := by
  rw [flaggedKrausMap_score]
  exact Finset.sum_congr rfl fun h _ => by rw [compressedKraus_pairing _ _ _ (hK h)]

private theorem zero_tiltScore_le_optimal (r : WitnessInterval) :
    tiltScore r 0 ≤ tiltScore r (tiltMass r) := by
  have h := tiltMass_spec r
  have hp : tiltMass r ∈ Set.Ioo (0 : ℝ) 1 := ⟨h.1.1, h.1.2.trans (by norm_num)⟩
  have hr : 1 < (r : ℝ) := by linarith [r.property.1]
  exact (tiltScore_lt_of_ne_maximizer r (tiltMass r) 0 hr hp h.2
    (by norm_num) (ne_of_lt h.1.1)).le

/-- The two score bounds apply to arbitrary terminal Kraus families
whose right supports are the two complementary first outcomes. -/
theorem complementary_terminal_score_le {i l : Type*} [Fintype i] [Fintype l]
    (r : WitnessInterval) (E : Matrix (Fin 5) (Fin 5) ℂ) (hE : E.IsHermitian)
    (hidem : E * E = E) (hzero : E ≠ 0) (hone : E ≠ 1)
    (f : i → Fin 2) (g : l → Fin 2) (K : i → Matrix (Fin 5) (Fin 5) ℂ)
    (L : l → Matrix (Fin 5) (Fin 5) ℂ)
    (hKright : ∀ h, K h * E = K h) (hLright : ∀ h, L h * (1 - E) = L h)
    (hK : ∑ h, (K h)ᴴ * K h = E) (hL : ∑ h, (L h)ᴴ * L h = 1 - E) :
    (∑ h, ‖((flagTest r (f h))ᴴ * K h).trace‖ ^ 2) +
      (∑ h, ‖((flagTest r (g h))ᴴ * L h).trace‖ ^ 2) ≤ tiltScore r (tiltMass r) := by
  obtain ⟨m, k, hm, hk, hmk, U, W, hU, hW, hUE, hWE⟩ :=
    AuricProjectionFrames.exists_complementary_frames E hE hidem hzero hone
  rw [Fintype.card_fin] at hmk
  have hcompl : U * Uᴴ + W * Wᴴ = 1 := by
    rw [hUE, hWE, add_sub_cancel]
  have hKnorm := compressedKraus_normalized K U hU (hK.trans hUE.symm)
  have hLnorm := compressedKraus_normalized L W hW (hL.trans hWE.symm)
  have hKtp := flaggedKrausMap_tp f (fun h => K h * U) hKnorm
  have hLtp := flaggedKrausMap_tp g (fun h => L h * W) hLnorm
  rw [← compressedKraus_score r f K U (fun h => by simpa only [hUE] using hKright h),
    ← compressedKraus_score r g L W (fun h => by simpa only [hWE] using hLright h)]
  have hr : 1 ≤ (r : ℝ) := by linarith [r.property.1]
  have hcases : (m = 1 ∧ k = 4) ∨ (m = 2 ∧ k = 3) ∨
      (m = 3 ∧ k = 2) ∨ (m = 4 ∧ k = 1) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (rank_one_four_cp_score_le U W hU hW hcompl r hr _ _ (flaggedKrausMap_cp _ _)
      (flaggedKrausMap_cp _ _) hKtp hLtp).trans
      ((rank_one_four_constant_lt_tiltScore r).le.trans (zero_tiltScore_le_optimal r))
  · rw [add_comm]
    exact rank_three_two_cp_score_le W U hW hU (by simpa only [add_comm] using hcompl) r _ _
      (flaggedKrausMap_cp _ _) (flaggedKrausMap_cp _ _) hLtp hKtp
  · exact rank_three_two_cp_score_le U W hU hW hcompl r _ _
      (flaggedKrausMap_cp _ _) (flaggedKrausMap_cp _ _) hKtp hLtp
  · rw [add_comm]
    exact (rank_one_four_cp_score_le W U hW hU (by simpa only [add_comm] using hcompl) r hr _ _
      (flaggedKrausMap_cp _ _) (flaggedKrausMap_cp _ _) hLtp hKtp).trans
      ((rank_one_four_constant_lt_tiltScore r).le.trans (zero_tiltScore_le_optimal r))

private theorem unitary_score_le (r : WitnessInterval) (j : Fin 2)
    (U : Matrix.unitaryGroup (Fin 5) ℂ) :
    ‖((flagTest r j)ᴴ * U.val).trace‖ ^ 2 ≤ tiltScore r (tiltMass r) := by
  have hr : 1 < (r : ℝ) := by linarith [r.property.1]
  have he (i : Fin 5) : ‖U.val i i‖ ≤ 1 := by
    have hU := Matrix.mem_unitaryGroup_iff.mp U.prop
    have h := Finset.single_le_sum (f := fun k => ‖U.val i k‖ ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    have hnorm := Matrix.unitary_row_sum_norm_sq U.val hU i
    rw [hnorm] at h
    nlinarith only [h, norm_nonneg (U.val i i)]
  have hN : ‖((flagTest r j)ᴴ * U.val).trace‖ ≤ 2 + r := by
    have hr₀ : 0 ≤ (r : ℝ) := by linarith
    fin_cases j
    · change ‖((flagTest r 0)ᴴ * U.val).trace‖ ≤ 2 + r
      have hT : ((flagTest r 0)ᴴ * U.val).trace =
          U.val 0 0 + U.val 1 1 + (r : ℂ) * U.val 4 4 := by
        simp [flagTest, diagonal_conjTranspose, diagonal_mul, Matrix.trace, Fin.sum_univ_succ,
          add_assoc]
      rw [hT]
      have hprod : ‖(r : ℂ) * U.val 4 4‖ ≤ r := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr₀]
        nlinarith only [mul_le_mul_of_nonneg_left (he 4) hr₀]
      linarith only [norm_add_le (U.val 0 0 + U.val 1 1) ((r : ℂ) * U.val 4 4),
        norm_add_le (U.val 0 0) (U.val 1 1), he 0, he 1, hprod]
    · change ‖((flagTest r 1)ᴴ * U.val).trace‖ ≤ 2 + r
      have hT : ((flagTest r 1)ᴴ * U.val).trace =
          U.val 2 2 + U.val 3 3 + (r : ℂ) * U.val 4 4 := by
        simp [flagTest, diagonal_conjTranspose, diagonal_mul, Matrix.trace, Fin.sum_univ_succ,
          add_assoc]
      rw [hT]
      have hprod : ‖(r : ℂ) * U.val 4 4‖ ≤ r := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr₀]
        nlinarith only [mul_le_mul_of_nonneg_left (he 4) hr₀]
      linarith only [norm_add_le (U.val 2 2 + U.val 3 3) ((r : ℂ) * U.val 4 4),
        norm_add_le (U.val 2 2) (U.val 3 3), he 2, he 3, hprod]
  apply (pow_le_pow_left₀ (norm_nonneg _) hN 2).trans
  apply le_trans _ (zero_tiltScore_le_optimal r)
  rw [tiltScore_eq_branch_sum _ _ hr (by norm_num)]
  norm_num

private theorem firstSingleEffect_hermitian_idempotent {k : ℕ}
    (u : Matrix.unitaryGroup (Fin 5) ℂ) (P : CompletePVM (Fin 5) k) (i : Fin k) :
    let E := firstGroupEffect u P {i}
    E.IsHermitian ∧ E * E = E := by
  dsimp only
  simp only [firstGroupEffect, Finset.sum_singleton]
  have hU : u.val * u.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp u.prop
  refine ⟨?_, ?_⟩
  · exact Matrix.isHermitian_conjTranspose_mul_mul _ (P.hermitian i)
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc u.val u.valᴴ, hU, Matrix.one_mul,
      ← Matrix.mul_assoc (P.proj i), P.idempotent]

private theorem firstGroupEffect_erase {k : ℕ}
    (u : Matrix.unitaryGroup (Fin 5) ℂ) (P : CompletePVM (Fin 5) k) (i : Fin k) :
    firstGroupEffect u P (Finset.univ.erase i) = 1 - firstGroupEffect u P {i} := by
  have hU : u.valᴴ * u.val = 1 := Matrix.mem_unitaryGroup_iff'.mp u.prop
  have hP : (∑ j ∈ Finset.univ.erase i, P.proj j) = 1 - P.proj i := by
    have h := Finset.sum_erase_add Finset.univ (fun j => P.proj j) (Finset.mem_univ i)
    exact eq_sub_of_add_eq (h.trans P.complete)
  simp only [firstGroupEffect, Finset.sum_singleton, hP, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, hU]

private theorem firstSingleEffect_proper {k : ℕ}
    (u : Matrix.unitaryGroup (Fin 5) ℂ) (P : CompletePVM (Fin 5) k) (i : Fin k)
    (hzero : P.proj i ≠ 0) (hone : P.proj i ≠ 1) :
    firstGroupEffect u P {i} ≠ 0 ∧ firstGroupEffect u P {i} ≠ 1 := by
  have hU : u.val * u.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp u.prop
  have hrecover : u.val * firstGroupEffect u P {i} * u.valᴴ = P.proj i := by
    simp only [firstGroupEffect, Finset.sum_singleton, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc u.val u.valᴴ, hU, Matrix.one_mul, Matrix.mul_one]
  constructor
  · intro h
    exact hzero (by simpa [h] using hrecover.symm)
  · intro h
    exact hone (by simpa [h, hU] using hrecover.symm)

private def maskedTerminal {k : ℕ} (u : unitaryGroup (Fin 5) ℂ)
    (P : CompletePVM (Fin 5) k) (d : Fin k → Protocol (Fin 5))
    (s : Finset (Fin k)) (h : Sigma (fun i => Terminal (d i))) : Matrix (Fin 5) (Fin 5) ℂ :=
  if h.1 ∈ s then kraus (.branch u k P d) h else 0

private theorem maskedTerminal_effect {k : ℕ} (u : unitaryGroup (Fin 5) ℂ)
    (P : CompletePVM (Fin 5) k) (d : Fin k → Protocol (Fin 5)) (s : Finset (Fin k)) :
    ∑ h : Terminal (.branch u k P d), (maskedTerminal u P d s h)ᴴ * maskedTerminal u P d s h =
      firstGroupEffect u P s := by
  change ∑ h : Sigma (fun i => Terminal (d i)),
    (maskedTerminal u P d s h)ᴴ * maskedTerminal u P d s h = _
  rw [Fintype.sum_sigma]
  have hFilter : Finset.univ.filter (· ∈ s) = s := by ext i; simp
  rw [← sum_group_terminal_effects u P d s]
  conv_rhs => rw [← hFilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [maskedTerminal, hi]

private theorem maskedTerminal_right_support {k : ℕ} (u : unitaryGroup (Fin 5) ℂ)
    (P : CompletePVM (Fin 5) k) (d : Fin k → Protocol (Fin 5)) (s : Finset (Fin k))
    (h : Terminal (.branch u k P d)) :
    maskedTerminal u P d s h * firstGroupEffect u P s = maskedTerminal u P d s h := by
  rcases h with ⟨i, v⟩
  by_cases hi : i ∈ s
  · simpa only [maskedTerminal, hi, ite_true] using terminal_has_group_right_support u P d s i hi v
  · simp [maskedTerminal, hi]

private theorem nontrivialBranch_score_le (r : WitnessInterval) {k : ℕ}
    (u : unitaryGroup (Fin 5) ℂ) (P : CompletePVM (Fin 5) k) (d : Fin k → Protocol (Fin 5))
    (i : Fin k) (hzero : P.proj i ≠ 0) (hone : P.proj i ≠ 1) :
    ∑ h : Terminal (.branch u k P d),
      ‖((flagTest r (flag (.branch u k P d) h))ᴴ * kraus (.branch u k P d) h).trace‖ ^ 2 ≤
        tiltScore r (tiltMass r) := by
  let E := firstGroupEffect u P {i}
  let K := maskedTerminal u P d {i}
  let L := maskedTerminal u P d (Finset.univ.erase i)
  let f := flag (.branch u k P d)
  have hE := firstSingleEffect_hermitian_idempotent u P i
  have hEproper := firstSingleEffect_proper u P i hzero hone
  have hcompl := firstGroupEffect_erase u P i
  have hLr : ∀ h, L h * (1 - E) = L h := by
    intro h
    rw [← hcompl]
    exact maskedTerminal_right_support u P d (Finset.univ.erase i) h
  have hBound := complementary_terminal_score_le r E hE.1 hE.2 hEproper.1 hEproper.2
    f f K L (maskedTerminal_right_support _ _ _ _) hLr
    (maskedTerminal_effect _ _ _ _)
    (by simpa only [hcompl] using maskedTerminal_effect u P d (Finset.univ.erase i))
  rw [← Finset.sum_add_distrib] at hBound
  refine le_trans (le_of_eq ?_) hBound
  apply Finset.sum_congr rfl
  intro h _
  by_cases hi : h.1 = i <;> simp [K, L, f, maskedTerminal, hi]

private theorem trivialPVM_unique {k : ℕ} (P : CompletePVM (Fin 5) k)
    (hP : ∀ i, P.proj i = 0 ∨ P.proj i = 1) :
    ∃ i, P.proj i = 1 ∧ ∀ j, j ≠ i → P.proj j = 0 := by
  classical
  have hs : ∃ i, P.proj i = 1 := by
    by_contra! hn
    have hall : ∀ i, P.proj i = 0 := fun i => (hP i).resolve_right (hn i)
    have hbad := P.complete
    simp [hall] at hbad
  obtain ⟨i, hi⟩ := hs
  refine ⟨i, hi, fun j hj => (hP j).resolve_right ?_⟩
  intro hjone
  have h := P.orthogonal j i hj
  simp [hi, hjone] at h

/-- Every deterministic same-register projective strategy, even with
arbitrary finite branching and unitary feedback, has score at most the
tilted optimum. The prefix permits absorption of the trivial measurements. -/
theorem protocol_score_le (r : WitnessInterval) (p : Protocol (Fin 5))
    (u : unitaryGroup (Fin 5) ℂ) :
    ∑ h : Terminal p, ‖((flagTest r (flag p h))ᴴ * (kraus p h * u.val)).trace‖ ^ 2 ≤
      tiltScore r (tiltMass r) := by
  classical
  induction p generalizing u with
  | leaf j v =>
    change (∑ _h : Unit, ‖((flagTest r j)ᴴ * (v.val * u.val)).trace‖ ^ 2) ≤ _
    simpa only [Fintype.sum_unique, Submonoid.coe_mul] using unitary_score_le r j (v * u)
  | branch v k P d ih =>
    let w : unitaryGroup (Fin 5) ℂ := v * u
    let q : Protocol (Fin 5) := .branch w k P d
    have heq :
        (∑ h : Terminal (.branch v k P d),
          ‖((flagTest r (flag (.branch v k P d) h))ᴴ *
            (kraus (.branch v k P d) h * u.val)).trace‖ ^ 2) =
        ∑ h : Terminal q, ‖((flagTest r (flag q h))ᴴ * kraus q h).trace‖ ^ 2 := by
      apply Finset.sum_congr rfl
      rintro ⟨i, a⟩ _
      change ‖((flagTest r (flag (d i) a))ᴴ *
          ((kraus (d i) a * (P.proj i * v.val)) * u.val)).trace‖ ^ 2 =
        ‖((flagTest r (flag (d i) a))ᴴ *
          (kraus (d i) a * (P.proj i * (v.val * u.val)))).trace‖ ^ 2
      simp only [Matrix.mul_assoc]
    rw [heq]
    by_cases hn : ∃ i, P.proj i ≠ 0 ∧ P.proj i ≠ 1
    · obtain ⟨i, hi₀, hi₁⟩ := hn
      exact nontrivialBranch_score_le r w P d i hi₀ hi₁
    · push Not at hn
      obtain ⟨i, hi, hrest⟩ := trivialPVM_unique P (fun j => or_iff_not_imp_left.mpr (hn j))
      change (∑ h : Sigma (fun j => Terminal (d j)),
        ‖((flagTest r (flag (d h.1) h.2))ᴴ *
          (kraus (d h.1) h.2 * (P.proj h.1 * w.val))).trace‖ ^ 2) ≤ _
      rw [Fintype.sum_sigma, Finset.sum_eq_single i]
      · simpa only [hi, Matrix.one_mul] using ih i w
      · intro j _ hj
        simp [hrest j hj]
      · simp

end D5.S3.Quantum.Measurement.AuricProtocolScore
