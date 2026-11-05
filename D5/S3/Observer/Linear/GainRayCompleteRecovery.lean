/- GID: D5/S3/Observer/Linear/GainRayCompleteRecovery
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayCompleteRecovery
   mirror-E: none(waiver:full-native-complete-recovery)
   anchors: []
   utility: none
   digest: One literal trajectory recovers the whole world and exact coefficients. -/

import D5.S3.Observer.Linear.GainRayCompleteCritical

/-! Full native-world identification on a single fixed chronological word. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace D5.S3.Observer.Linear.GainRay

/-- A fixed chronological word, with a read after every individual atom. -/
def recoveryWord (d : ℕ) : List Bool :=
  List.replicate (2 * (d + 1)) false ++ [true] ++ List.replicate (2 * d + 1) false

private theorem recovery_length (d : ℕ) : (recoveryWord d).length = 4 * d + 4 := by
  simp [recoveryWord]
  omega

/-- A nonzero degree-bounded gain cannot vanish once in every disjoint adjacent pair. -/
private theorem consecutive_nonroots (d s : ℕ) (β : Coeff d) (hβ : β ≠ 0) :
    ∃ j : Fin (d + 1),
      (gain d β).eval ((s + 2 * j.val : ℕ) : ℝ) ≠ 0 ∧
      (gain d β).eval ((s + 2 * j.val + 1 : ℕ) : ℝ) ≠ 0 := by
  classical
  by_contra h
  have hz : ∀ j : Fin (d + 1), ∃ r : ℕ, (r = 0 ∨ r = 1) ∧
      (gain d β).eval ((s + 2 * j.val + r : ℕ) : ℝ) = 0 := by
    intro j
    by_cases hj : (gain d β).eval ((s + 2 * j.val : ℕ) : ℝ) = 0
    · exact ⟨0, Or.inl rfl, by simpa using hj⟩
    · exact ⟨1, Or.inr rfl, by simpa using not_and.mp (not_exists.mp h j) hj⟩
  choose r hr hz using hz
  let t : Fin (d + 1) → ℝ := fun j => ((s + 2 * j.val + r j : ℕ) : ℝ)
  have ht : Function.Injective t := by
    intro i j he
    change ((s + 2 * i.val + r i : ℕ) : ℝ) = ((s + 2 * j.val + r j : ℕ) : ℝ) at he
    have hn : s + 2 * i.val + r i = s + 2 * j.val + r j := by exact_mod_cast he
    have hi := hr i
    have hj := hr j
    apply Fin.ext
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> omega
  apply hβ
  apply evaluation_injective d (d + 1) t ht le_rfl
  ext j
  rw [evaluation_polynomial, hz]
  simp [evaluate]

private theorem recovery_prefix (d : ℕ) (i : ℕ) (hi : i ≤ 2 * (d + 1)) :
    (recoveryWord d).take i = List.replicate i false := by
  unfold recoveryWord
  rw [List.append_assoc, List.take_append_of_le_length (by simp; omega)]
  simp [min_eq_left hi]

private theorem recovery_tail (d r : ℕ) (hr : r ≤ 2 * d + 1) :
    acquisition ((recoveryWord d).take (2 * (d + 1) + 1 + r)) =
      action false ^ r * action true * action false ^ (2 * (d + 1)) := by
  have ht : (recoveryWord d).take (2 * (d + 1) + 1 + r) =
      List.replicate (2 * (d + 1)) false ++ [true] ++ List.replicate r false := by
    unfold recoveryWord
    rw [List.append_assoc, List.take_append]
    simp only [List.length_replicate, List.take_replicate]
    rw [min_eq_right (by omega), show 2 * (d + 1) + 1 + r-2 * (d + 1) = r + 1 by omega]
    simp [List.take_replicate, min_eq_left hr]
  rw [ht]
  have hp (r : ℕ) :
      acquisition (List.replicate (2 * (d + 1)) false ++ [true] ++ List.replicate r false) =
      action false ^ r * action true * action false ^ (2 * (d + 1)) := by
    induction r with
    | zero => simp [acquisition_append, acquisition_pure]
    | succ r ih =>
        rw [List.replicate_succ', ← List.append_assoc, acquisition_append, ih, pow_succ']
        simp only [Matrix.mul_assoc]
  exact hp r

private theorem powers_trace (S T : Mat)
    (h0 : Matrix.trace S = Matrix.trace T)
    (h1 : Matrix.trace (action false * S) = Matrix.trace (action false * T))
    (k : ℕ) : Matrix.trace (action false ^ k * S) =
      Matrix.trace (action false ^ k * T) := by
  cases k with
  | zero => simpa using h0
  | succ k =>
      obtain ⟨a,b,_,_,he⟩ := m_power_coordinates k
      simp [he, Matrix.add_mul, Matrix.trace_add,
        Matrix.trace_smul, h0, h1]

private theorem backwards_trace (S T : Mat) (k : ℕ)
    (h0 : Matrix.trace (action false ^ k * S) = Matrix.trace (action false ^ k * T))
    (h1 : Matrix.trace (action false ^ (k + 1) * S) =
      Matrix.trace (action false ^ (k + 1) * T)) :
    Matrix.trace S = Matrix.trace T ∧
      Matrix.trace (action false * S) = Matrix.trace (action false * T) := by
  have hm : action false ^ 2 = action false + (1 : Mat) := by
    rw [action_m_shape]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  induction k with
  | zero => simpa using And.intro h0 h1
  | succ k ih =>
      apply ih ?_ h0
      have he (U : Mat) :
          Matrix.trace (action false ^ (k + 1 + 1) * U) =
          Matrix.trace (action false ^ (k + 1) * U) + Matrix.trace (action false ^ k * U) := by
        rw [show k + 1 + 1 = k + 2 by omega, pow_add, hm, Matrix.mul_add,
          Matrix.mul_one, Matrix.add_mul, Matrix.trace_add]
        rw [← pow_succ]
      rw [he S, he T] at h1
      linarith

private theorem four_traces (S T : Mat)
    (h0 : Matrix.trace S = Matrix.trace T)
    (hM : Matrix.trace (action false * S) = Matrix.trace (action false * T))
    (hJ : Matrix.trace (action true * S) = Matrix.trace (action true * T))
    (hMJ : Matrix.trace (action false * (action true * S)) =
      Matrix.trace (action false * (action true * T))) : S = T := by
  simp [action_m_shape, action_j_shape, Matrix.trace, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two] at h0 hM hJ hMJ
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp at * <;> linarith

/-- Equal literal histories on the fixed word force the entire original target. -/
theorem recovery_identifies (d : ℕ) (W V : World d)
    (h : readings W (recoveryWord d) = readings V (recoveryWord d)) :
    W.source = V.source ∧ W.coeff = V.coeff ∧ W.drift = V.drift := by
  have hp : readings W (List.replicate (2 * (d + 1)) false) =
      readings V (List.replicate (2 * (d + 1)) false) := by
    ext i
    have hi : i.val ≤ 2 * (d + 1) := by have := i.isLt; simp at this; omega
    have he := congrFun h ⟨i.val, by rw [recovery_length]; omega⟩
    simpa only [readings, readAt, recovery_prefix d i.val hi,
      List.take_replicate, min_eq_left hi] using he
  have hb : W.coeff = V.coeff := by
    rw [← pureM_exact_beta d W, ← pureM_exact_beta d V, hp]
  have hn : acquisition [] = (1 : Mat) := by
    simpa using acquisition_pure false 0
  have hd : W.drift = V.drift := by
    have he := congrFun hp 0
    simpa [readings, readAt, hn, W.legal.2.2, V.legal.2.2, hb] using he
  have htrace : Matrix.trace W.source = Matrix.trace V.source :=
    W.legal.2.2.trans V.legal.2.2.symm
  have hM : Matrix.trace (action false * W.source) =
      Matrix.trace (action false * V.source) := by
    obtain ⟨j,hj,_⟩ := consecutive_nonroots d 1 V.coeff V.nonzero
    have hi : 1 + 2 * j.val ≤ 2 * (d + 1) := by have := j.isLt; omega
    have he := congrFun hp ⟨1 + 2 * j.val, by simp; omega⟩
    dsimp [readings, readAt] at he
    rw [List.take_replicate, min_eq_left hi, acquisition_pure, hb, hd] at he
    obtain ⟨a,b,_,hbpos,heq⟩ := m_power_coordinates (2 * j.val)
    rw [show 1 + 2 * j.val = 2 * j.val + 1 by omega, heq] at he
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, htrace] at he
    have he' := mul_left_cancel₀ (by simpa [Nat.add_comm] using hj)
      (add_right_cancel he)
    nlinarith
  obtain ⟨j,hj,hj'⟩ := consecutive_nonroots d (2 * (d + 1) + 1) V.coeff V.nonzero
  have tail_eq (r : ℕ) (hr : r ≤ 2 * d + 1)
      (hg : (gain d V.coeff).eval ((2 * (d + 1) + 1 + r : ℕ) : ℝ) ≠ 0) :
      Matrix.trace (action false ^ r * (action true * (action false ^ (2 * (d + 1)) * W.source))) =
      Matrix.trace (action false ^ r * (action true * (action false ^ (2 * (d + 1)) * V.source))) := by
    have he := congrFun h ⟨2 * (d + 1) + 1 + r, by rw [recovery_length]; omega⟩
    dsimp [readings, readAt] at he
    rw [recovery_tail d r hr, hb, hd] at he
    simpa only [Matrix.mul_assoc] using mul_left_cancel₀ hg (add_right_cancel he)
  have hjpair := backwards_trace _ _ (2 * j.val)
    (tail_eq _ (by have := j.isLt; omega) hj)
    (tail_eq _ (by have := j.isLt; omega) (by simpa [Nat.add_assoc] using hj'))
  have hS : action false ^ (2 * (d + 1)) * W.source =
      action false ^ (2 * (d + 1)) * V.source := by
    apply four_traces
    · exact powers_trace _ _ htrace hM _
    · simpa only [← Matrix.mul_assoc, ← pow_succ'] using
        powers_trace _ _ htrace hM (2 * (d + 1) + 1)
    · exact hjpair.1
    · exact hjpair.2
  have hu : IsUnit (action false ^ (2 * (d + 1))) := by
    rw [← acquisition_pure]
    exact acquisition_unit _
  exact ⟨hu.mul_left_cancel hS, hb, hd⟩

/-- Zero extension of the original exact prefix readout. No entry uses observations. -/
def recoveryMatrix (d : ℕ) : Readout d (recoveryWord d) :=
  fun k i => if hi : i.val ≤ 2 * (d + 1) then
    exactBetaReadout d k ⟨i.val, by simp; omega⟩ else 0

private theorem recovery_matrix_exact (d : ℕ) (W : World d) :
    (recoveryMatrix d).mulVec (readings W (recoveryWord d)) = W.coeff := by
  ext k
  have he := congrFun (pureM_exact_beta d W) k
  have hn : (recoveryWord d).length + 1 = (2 * (d + 1) + 1) + (2 * d + 2) := by
    rw [recovery_length]
    omega
  change (∑ i : Fin ((recoveryWord d).length + 1),
    (if hi : i.val ≤ 2 * (d + 1) then
      exactBetaReadout d k ⟨i.val, by simp; omega⟩ else 0) * readAt W (recoveryWord d) i.val) = W.coeff k
  rw [hn, Fin.sum_univ_add]
  have hsmall (i : Fin (2 * (d + 1) + 1)) : i.val ≤ 2 * (d + 1) := by omega
  have hlarge (i : Fin (2 * d + 2)) : ¬ (2 * (d + 1) + 1 + i.val ≤ 2 * (d + 1)) := by omega
  simp only [Fin.val_castAdd, Fin.val_natAdd, dite_eq_left (hsmall _),
    dite_eq_right (hlarge _), zero_mul, Finset.sum_const_zero, add_zero]
  simp only [Matrix.mulVec, dotProduct] at he
  convert he using 1
  refine Fintype.sum_equiv (finCongr (show 2 * (d + 1) + 1 =
    (List.replicate (2 * (d + 1)) false).length + 1 by simp)) _ _ ?_
  intro i
  congr 1
  simp [readAt, recovery_prefix d i.val (hsmall i), readings,
    List.take_replicate, min_eq_left (hsmall i)]

/-- A singleton at every word, including words that cannot be reached. -/
def recoveryReadout (d : ℕ) (w : List Bool) : Readout d w :=
  if h : w = recoveryWord d then h.symm ▸ recoveryMatrix d else 0

/-- All decisions are total and use only the word length, hence only history. -/
def recoveryProtocol (d : ℕ) : Protocol d where
  palette w := {recoveryReadout d w}
  countable _ := Set.countable_singleton _
  decide w _ := if h : w.length < (recoveryWord d).length then
    Sum.inl (recoveryWord d)[w.length] else
    Sum.inr ⟨recoveryReadout d w, Set.mem_singleton _⟩

open Classical in
/-- On unrealizable histories the answer is zero; on a nonempty fiber choose a world.
Identification, rather than the definition, proves that its target is the actual one. -/
def recoveryAnswer (d : ℕ) (w : List Bool) (h : History w) :
    Mat × Polynomial ℝ × ℝ :=
  if he : ∃ W : World d, readings W w = h then
    let W := Classical.choose he
    (W.source, gain d W.coeff, W.drift)
  else (0, 0, 0)

private theorem recovery_answer_exact (d : ℕ) (W : World d) :
    recoveryAnswer d (recoveryWord d) (readings W (recoveryWord d)) =
      (W.source, gain d W.coeff, W.drift) := by
  classical
  have he : ∃ V : World d, readings V (recoveryWord d) = readings W (recoveryWord d) :=
    ⟨W, rfl⟩
  have hid := recovery_identifies d (Classical.choose he) W (Classical.choose_spec he)
  simp only [recoveryAnswer, dite_eq_left he]
  rw [hid.1, hid.2.1, hid.2.2]

private theorem recovery_reaches (d : ℕ) (W : World d) (k : ℕ)
    (hk : k ≤ (recoveryWord d).length) :
    Reaches (recoveryProtocol d) W ((recoveryWord d).take k) := by
  induction k with
  | zero => simpa using (Reaches.initial (P := recoveryProtocol d) (W := W))
  | succ k ih =>
      have hlt : k < (recoveryWord d).length := by omega
      rw [List.take_succ_eq_append_getElem hlt]
      apply Reaches.step (ih (by omega))
      simp [recoveryProtocol, List.length_take, min_eq_left (Nat.le_of_lt hlt), hlt]

private theorem recovery_terminates (d : ℕ) (W : World d) :
    Terminates (recoveryProtocol d) W (recoveryWord d)
      ⟨recoveryReadout d _, Set.mem_singleton _⟩ := by
  constructor
  · simpa using recovery_reaches d W _ le_rfl
  · simp [recoveryProtocol]

/-- Complete recovery on the original whole-world domain, with scalar one at every
actual terminal. The policy, answer and singleton matrices are total. -/
theorem complete_recovery (d : ℕ) (_hd : 1 ≤ d) :
    CompleteCorrect (recoveryProtocol d) (recoveryAnswer d) (4 * d + 5) ∧
    ∀ (W : World d) (w : List Bool)
      (C : {C : Readout d w // C ∈ (recoveryProtocol d).palette w}),
      Terminates (recoveryProtocol d) W w C →
        w = recoveryWord d ∧ w.length + 1 = 4 * d + 5 ∧
        C.1.mulVec (readings W w) = W.coeff ∧
        recoveryAnswer d w (readings W w) = (W.source, gain d W.coeff, W.drift) := by
  constructor
  · intro W
    refine ⟨recoveryWord d, ⟨recoveryReadout d _, Set.mem_singleton _⟩,
      recovery_terminates d W, ?_, ?_, recovery_answer_exact d W⟩
    · have := recovery_length d
      omega
    · refine ⟨1, one_ne_zero, ?_⟩
      simpa [recoveryReadout] using recovery_matrix_exact d W
  · intro W w C ht
    have hf := recovery_terminates d W
    have hp := terminal_extends_reached (recoveryProtocol d) W w (recoveryWord d)
      ⟨recoveryReadout d _, Set.mem_singleton _⟩ ht.1 hf
    have hq := terminal_extends_reached (recoveryProtocol d) W (recoveryWord d) w C hf.1 ht
    have hw : w = recoveryWord d := hp.eq_of_length_le hq.length_le
    subst w
    have hC : C.1 = recoveryReadout d (recoveryWord d) := Set.mem_singleton_iff.mp C.2
    refine ⟨rfl, by have := recovery_length d; omega, ?_, recovery_answer_exact d W⟩
    simpa [hC, recoveryReadout] using recovery_matrix_exact d W

#print axioms recovery_identifies
#print axioms complete_recovery
end D5.S3.Observer.Linear.GainRay
