/- GID: D5/S3/Observer/CubicGain/MixedTripleExclusion
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/MixedTripleExclusion
   mirror-E: none(waiver:entire-cubic-world-mixed-prefix-exclusion)
   anchors: []
   utility: none
   digest: Full response intersections retain the original complete worlds and chronological mixed prefix. -/

import D5.S3.Observer.Linear.GainRayWordGeometry

/-! Entire cubic worlds and current-support losing response trees. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix Classical
namespace D5.S3.Observer.CubicGain.MixedTripleExclusion
open D5.S3.Observer.Linear.GainRay

abbrev World3 := D5.S3.Observer.Linear.GainRay.World 3

/-- The whole response intersection of the current support, at the next original clock. -/
def responseSlice (T : Finset World3) (v : List Bool) (E : Bool) (z : ℝ) : Finset World3 :=
  T.filter (fun W => readAt W (v ++ [E]) (v.length + 1) = z)

/-- Every node has its own stopping guard. Descendants filter the current support. -/
def Losing : ℕ → Finset World3 → List Bool → Prop
  | 0, T, _ => 2 ≤ T.card
  | n + 1, T, v => 2 ≤ T.card ∧ ∀ E : Bool, ∃ z : ℝ,
      Losing n (responseSlice T v E z) (v ++ [E])

private theorem losing_guard (n : ℕ) (T : Finset World3) (v : List Bool)
    (h : Losing n T v) : 2 ≤ T.card := by
  cases n with
  | zero => exact h
  | succ n => exact h.1

private theorem responseSlice_subset (T : Finset World3) (v : List Bool) (E : Bool) (z : ℝ) :
    responseSlice T v E z ⊆ T := Finset.filter_subset _ _

private theorem losing_pair_step (n : ℕ) (T : Finset World3) (v : List Bool)
    (hT : T.card = 2) (h : Losing (n + 1) T v) (E : Bool) :
    ∃ z : ℝ, (∀ W ∈ T, readAt W (v ++ [E]) (v.length + 1) = z) ∧
      Losing n T (v ++ [E]) := by
  obtain ⟨z,hz⟩ := h.2 E
  have he : responseSlice T v E z = T :=
    Finset.eq_of_subset_of_card_le (responseSlice_subset T v E z)
      (by rw [hT]; exact losing_guard n _ _ hz)
  refine ⟨z, ?_, he ▸ hz⟩
  intro W hW
  have hm : W ∈ responseSlice T v E z := he.symm ▸ hW
  exact (Finset.mem_filter.mp hm).2

private theorem losing_pair_suffix (n : ℕ) (T : Finset World3) (v : List Bool)
    (hT : T.card = 2) (h : Losing n T v) (u : List Bool) (hu : u.length ≤ n) :
    Losing (n - u.length) T (v ++ u) ∧
      (u ≠ [] → ∀ W ∈ T, ∀ Z ∈ T,
        readAt W (v ++ u) (v.length + u.length) =
          readAt Z (v ++ u) (v.length + u.length)) := by
  induction u using List.reverseRecOn generalizing n with
  | nil =>
    constructor
    · simpa using h
    · intro hu0
      exact (hu0 rfl).elim
  | append_singleton u E ih =>
    have hlen : u.length < n := by simpa using hu
    obtain ⟨hprev,_⟩ := ih n h (by omega)
    obtain ⟨k,hk⟩ : ∃ k, n - u.length = k + 1 := ⟨n - u.length - 1, by omega⟩
    rw [hk] at hprev
    obtain ⟨z,hz,hnext⟩ := losing_pair_step k T (v ++ u) hT hprev E
    constructor
    · convert hnext using 1 <;> simp only [List.length_append, List.length_singleton, List.append_assoc] <;> omega
    · intro _ W hW Z hZ
      have hw := hz W hW
      have hz' := hz Z hZ
      simpa [List.append_assoc, List.length_append, Nat.add_assoc] using hw.trans hz'.symm

private theorem two_product_equal_trace (S : Mat) (c : ℝ)
    (h : ∀ E F : Bool, Matrix.trace (action F * action E * S) = c) :
    S = !![c,0;0,0] := by
  have hJJ := h true true
  have hJM := h true false
  have hMJ := h false true
  have hMM := h false false
  simp [action_j_shape, action_m_shape, Matrix.mul_apply, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const] at hJJ hJM hMJ hMM
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

private theorem three_product_equal_trace (S : Mat) (c : ℝ)
    (h : ∀ E F G : Bool, Matrix.trace (action G * action F * action E * S) = c) :
    S = 0 ∧ c = 0 := by
  have hJJJ := h true true true
  have hJJM := h true true false
  have hJMJ := h true false true
  have hJMM := h true false false
  have hMMJ := h false false true
  simp [action_j_shape, action_m_shape, Matrix.mul_apply, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const] at hJJJ hJJM hJMJ hJMM hMMJ
  have hzero : S = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  exact ⟨hzero, by simpa [hzero] using hJJJ.symm⟩



private theorem acquisition_concat (v u : List Bool) :
    acquisition (v ++ u) = acquisition u * acquisition v := by
  have h := (D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.raw_word_signed_bound v).2.2.2.1 u
  simpa only [acquisition, Raw, Matrix.map_mul] using
    congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A.map (Int.castRingHom ℝ)) h

private theorem acquisition_two (E F : Bool) :
    acquisition [E,F] = action F * action E := by
  have hE : acquisition [E] = action E := by simpa using acquisition_pure E 1
  change acquisition ([E] ++ [F]) = _
  rw [acquisition_append, hE]

private theorem acquisition_three (E F G : Bool) :
    acquisition [E,F,G] = action G * action F * action E := by
  change acquisition ([E,F] ++ [G]) = _
  rw [acquisition_append, acquisition_two, Matrix.mul_assoc]

private theorem read_concat (W : World3) (v u : List Bool) :
    readAt W (v ++ u) (v.length + u.length) =
      (gain 3 W.coeff).eval ((v.length + u.length : ℕ) : ℝ) *
        Matrix.trace (acquisition u * acquisition v * W.source) + W.drift := by
  rw [← List.length_append, readAt, List.take_length, acquisition_concat]

private theorem pair_read_difference (n : ℕ) (T : Finset World3) (v : List Bool)
    (hT : T.card = 2) (h : Losing n T v)
    (W Z : World3) (hW : W ∈ T) (hZ : Z ∈ T)
    (u : List Bool) (hu : u ≠ []) (hun : u.length ≤ n) :
    Matrix.trace (acquisition u * (acquisition v *
      ((gain 3 W.coeff).eval ((v.length + u.length : ℕ) : ℝ) • W.source -
        (gain 3 Z.coeff).eval ((v.length + u.length : ℕ) : ℝ) • Z.source))) =
      Z.drift - W.drift := by
  have he := (losing_pair_suffix n T v hT h u hun).2 hu W hW Z hZ
  rw [read_concat, read_concat] at he
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul, ← Matrix.mul_assoc]
  linarith

private theorem pair_common_drift (n : ℕ) (T : Finset World3) (v : List Bool)
    (hT : T.card = 2) (h : Losing n T v) (hn : 3 ≤ n)
    (W Z : World3) (hW : W ∈ T) (hZ : Z ∈ T) : W.drift = Z.drift := by
  let S : Mat := acquisition v *
    ((gain 3 W.coeff).eval ((v.length + 3 : ℕ) : ℝ) • W.source -
      (gain 3 Z.coeff).eval ((v.length + 3 : ℕ) : ℝ) • Z.source)
  have hh : ∀ E F G : Bool,
      Matrix.trace (action G * action F * action E * S) = Z.drift - W.drift := by
    intro E F G
    simpa only [List.length_cons, List.length_nil, zero_add, acquisition_three,
      Matrix.mul_assoc] using
      pair_read_difference n T v hT h W Z hW hZ [E,F,G] (by simp) (by simpa using hn)
  have hc := (three_product_equal_trace S (Z.drift-W.drift) hh).2
  linarith

private theorem weighted_sources_zero (W Z : World3) (hP : W.source ≠ Z.source)
    (a b : ℝ) (he : a • W.source = b • Z.source) : a = 0 ∧ b = 0 := by
  have ht := congrArg Matrix.trace he
  simp only [Matrix.trace_smul, W.legal.2.2, Z.legal.2.2, smul_eq_mul, mul_one] at ht
  have ha : a = 0 := by
    by_contra hane
    apply hP
    ext i k
    apply mul_left_cancel₀ hane
    have hentry := congrFun (congrFun he i) k
    simpa only [Matrix.smul_apply, smul_eq_mul, ← ht] using hentry
  exact ⟨ha, by simpa [ha] using ht.symm⟩

private theorem pair_gain_zero (n : ℕ) (T : Finset World3) (v : List Bool)
    (hT : T.card = 2) (h : Losing n T v) (hn : 3 ≤ n)
    (W Z : World3) (hW : W ∈ T) (hZ : Z ∈ T) (hP : W.source ≠ Z.source)
    (j : ℕ) (hj : 2 ≤ j) (hjn : j ≤ n) :
    (gain 3 W.coeff).eval ((v.length+j : ℕ) : ℝ) = 0 ∧
      (gain 3 Z.coeff).eval ((v.length+j : ℕ) : ℝ) = 0 := by
  let D : Mat := (gain 3 W.coeff).eval ((v.length+j : ℕ) : ℝ) • W.source -
    (gain 3 Z.coeff).eval ((v.length+j : ℕ) : ℝ) • Z.source
  let p : List Bool := List.replicate (j-2) true
  have hlen : p.length + 2 = j := by simp [p]; omega
  have hd := pair_common_drift n T v hT h hn W Z hW hZ
  have hh : ∀ E F : Bool,
      Matrix.trace (action F * action E * (acquisition (v ++ p) * D)) = 0 := by
    intro E F
    have hu : (p ++ [E,F]).length = j := by simpa using hlen
    have he := pair_read_difference n T v hT h W Z hW hZ (p ++ [E,F])
      (by simp) (by rw [hu]; exact hjn)
    simpa only [hu, hd, sub_self, acquisition_concat, acquisition_two,
      Matrix.mul_assoc] using he
  have hz := two_product_equal_trace (acquisition (v ++ p) * D) 0 hh
  have hm0 : (!![0,0;0,0] : Mat) = 0 := by
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  rw [hm0] at hz
  have hz' : acquisition (v ++ p) * D = acquisition (v ++ p) * 0 := by simpa using hz
  have hd0 : D = 0 := (acquisition_unit (v ++ p)).mul_left_cancel hz'
  exact weighted_sources_zero W Z hP _ _ (sub_eq_zero.mp hd0)



private theorem four_evaluations (β γ : Coeff 3) (t : Fin 4 → ℝ)
    (ht : Function.Injective t)
    (he : ∀ i, (gain 3 β).eval (t i) = (gain 3 γ).eval (t i)) : β = γ := by
  apply evaluation_injective 3 4 t ht (by omega)
  ext i
  simpa only [evaluation_polynomial] using he i

private theorem not_four_roots (W : World3) (t : Fin 4 → ℝ)
    (ht : Function.Injective t) : ¬ ∀ i, (gain 3 W.coeff).eval (t i) = 0 := by
  intro he
  apply W.nonzero
  apply four_evaluations W.coeff 0 t ht
  intro i
  simpa [gain, Polynomial.ofFn_eq_sum_monomial] using he i

private theorem common_gain_source (j m b : ℝ) (v : List Bool)
    (hv : v = [true,false] ∨ v = [false,true]) (W Z : World3)
    (hWJ : readAt W [true] 1 = j) (hWM : readAt W [false] 1 = m)
    (hWQ : readAt W v 2 = b)
    (hZJ : readAt Z [true] 1 = j) (hZM : readAt Z [false] 1 = m)
    (hZQ : readAt Z v 2 = b)
    (hd : W.drift = Z.drift) (hg : gain 3 W.coeff = gain 3 Z.coeff)
    (hg1 : (gain 3 W.coeff).eval 1 ≠ 0)
    (hg2 : (gain 3 W.coeff).eval 2 ≠ 0) : W.source = Z.source := by
  have hread (u : List Bool) (hz : (gain 3 W.coeff).eval (u.length : ℝ) ≠ 0)
      (he : readAt W u u.length = readAt Z u u.length) :
      Matrix.trace (acquisition u * W.source) = Matrix.trace (acquisition u * Z.source) := by
    simp only [readAt, List.take_length, ← hd, ← hg] at he
    exact mul_left_cancel₀ hz (add_right_cancel he)
  have hj := hread [true] (by simpa using hg1) (hWJ.trans hZJ.symm)
  have hm := hread [false] (by simpa using hg1) (hWM.trans hZM.symm)
  have hvlen : v.length = 2 := by rcases hv with rfl | rfl <;> rfl
  have hq := hread v (by simpa [hvlen] using hg2)
    (by simpa [hvlen] using hWQ.trans hZQ.symm)
  have htW := W.legal.2.2
  have htZ := Z.legal.2.2
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at htW htZ
  rcases hv with rfl | rfl
  all_goals
    simp [acquisition, Raw,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      Matrix.mul_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_two] at hj hm hq
    ext i k
    fin_cases i <;> fin_cases k <;> dsimp only <;> linarith

/-- Both first-response equations constrain each of the same three complete worlds.
The recursion begins at the chosen chronological mixed word and uses clocks three to seven. -/
theorem mixed_prefix_three_world_exclusion (a₀ j m b : ℝ) (hℓ : m-j ≠ 0)
    (v : List Bool) (hv : v = [true,false] ∨ v = [false,true])
    (T : Finset World3) (hT : T.card = 3)
    (hP : ∀ W ∈ T, ∀ Z ∈ T, W ≠ Z → W.source ≠ Z.source)
    (hreads : ∀ W ∈ T, readAt W [] 0 = a₀ ∧ readAt W [true] 1 = j ∧
      readAt W [false] 1 = m ∧ readAt W v 2 = b) : ¬ Losing 5 T v := by
  classical
  intro hL
  have hvlen : v.length = 2 := by rcases hv with rfl | rfl <;> rfl
  have third_full : ∀ E : Bool, ∃ z : ℝ,
      responseSlice T v E z = T ∧ Losing 4 T (v ++ [E]) := by
    intro E
    obtain ⟨z,hz⟩ := hL.2 E
    let S := responseSlice T v E z
    have hsub : S ⊆ T := responseSlice_subset T v E z
    have hlow : 2 ≤ S.card := losing_guard 4 S (v ++ [E]) hz
    have hhigh : S.card ≤ 3 := by simpa [hT] using Finset.card_le_card hsub
    have hnotpair : S.card ≠ 2 := by
      intro h2
      obtain ⟨W,hW,Z,hZ,hWZ⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
      have hWroot := hsub hW
      have hZroot := hsub hZ
      have hsource : W.source ≠ Z.source := hP W hWroot Z hZroot hWZ
      have hd := pair_common_drift 4 S (v ++ [E]) h2 hz (by omega) W Z hW hZ
      have h5 := pair_gain_zero 4 S (v ++ [E]) h2 hz (by omega) W Z hW hZ
        hsource 2 (by omega) (by omega)
      have h6 := pair_gain_zero 4 S (v ++ [E]) h2 hz (by omega) W Z hW hZ
        hsource 3 (by omega) (by omega)
      have h7 := pair_gain_zero 4 S (v ++ [E]) h2 hz (by omega) W Z hW hZ
        hsource 4 (by omega) (by omega)
      norm_num [List.length_append, hvlen] at h5 h6 h7
      have h0W := (hreads W hWroot).1
      have h0Z := (hreads Z hZroot).1
      simp [readAt, acquisition, Raw,
        D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
        W.legal.2.2, Z.legal.2.2, ← hd] at h0W h0Z
      have h0 : (gain 3 W.coeff).eval 0 = (gain 3 Z.coeff).eval 0 := by linarith
      have ht0 : Function.Injective (![0,5,6,7] : Fin 4 → ℝ) := by
        intro i k he
        fin_cases i <;> fin_cases k <;> norm_num at *
      have hc : W.coeff = Z.coeff := four_evaluations W.coeff Z.coeff
        ![0,5,6,7] ht0 (by intro i; fin_cases i <;> simp [h0,h5,h6,h7])
      have hn (r : ℝ) (hr : r = 1 ∨ r = 2) : (gain 3 W.coeff).eval r ≠ 0 := by
        intro her
        apply not_four_roots W ![r,5,6,7]
          (by rcases hr with rfl | rfl <;> intro i k he <;>
              fin_cases i <;> fin_cases k <;> norm_num at *)
        intro i
        fin_cases i <;> simp [her,h5,h6,h7]
      exact hsource (common_gain_source j m b v hv W Z
        (hreads W hWroot).2.1 (hreads W hWroot).2.2.1 (hreads W hWroot).2.2.2
        (hreads Z hZroot).2.1 (hreads Z hZroot).2.2.1 (hreads Z hZroot).2.2.2
        hd (congrArg (gain 3) hc) (hn 1 (Or.inl rfl)) (hn 2 (Or.inr rfl)))
    have he : S = T := Finset.eq_of_subset_of_card_le hsub (by rw [hT]; omega)
    exact ⟨z,he,he ▸ hz⟩
  obtain ⟨zJ,hJ,hJL⟩ := third_full true
  obtain ⟨zM,hM,hML⟩ := third_full false
  have shared_third (E : Bool) (z : ℝ) (he : responseSlice T v E z = T)
      (W : World3) (hW : W ∈ T) : readAt W (v ++ [E]) 3 = z := by
    have hm : W ∈ responseSlice T v E z := he.symm ▸ hW
    simpa [hvlen] using (Finset.mem_filter.mp hm).2
  have fourth_m_not_pair : ∀ z : ℝ,
      Losing 3 (responseSlice T (v ++ [true]) false z) (v ++ [true] ++ [false]) →
        (responseSlice T (v ++ [true]) false z).card ≠ 2 := by
    intro z hz h2
    let S := responseSlice T (v ++ [true]) false z
    have hsub : S ⊆ T := responseSlice_subset T (v ++ [true]) false z
    obtain ⟨W,hW,Z,hZ,hWZ⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
    have hWroot := hsub hW
    have hZroot := hsub hZ
    have hsource := hP W hWroot Z hZroot hWZ
    have hd := pair_common_drift 3 S (v ++ [true] ++ [false]) h2 hz
      (by omega) W Z hW hZ
    have h6 := pair_gain_zero 3 S (v ++ [true] ++ [false]) h2 hz
      (by omega) W Z hW hZ hsource 2 (by omega) (by omega)
    have h7 := pair_gain_zero 3 S (v ++ [true] ++ [false]) h2 hz
      (by omega) W Z hW hZ hsource 3 (by omega) (by omega)
    norm_num [List.length_append, hvlen] at h6 h7
    have hWJ := shared_third true zJ hJ W hWroot
    have hZJ := shared_third true zJ hJ Z hZroot
    have hWM := shared_third false zM hM W hWroot
    have hZM := shared_third false zM hM Z hZroot
  obtain ⟨zFourthM,hFourthM⟩ := hJL.2 false
  have hFourthMsub := responseSlice_subset T (v ++ [true]) false zFourthM
  have hFourthMlow := losing_guard 3 _ _ hFourthM
  have hFourthMhigh : (responseSlice T (v ++ [true]) false zFourthM).card ≤ 3 :=
    by simpa [hT] using Finset.card_le_card hFourthMsub
  have hFourthMwhole : responseSlice T (v ++ [true]) false zFourthM = T :=
    Finset.eq_of_subset_of_card_le hFourthMsub
      (by rw [hT]; have hn := fourth_m_not_pair zFourthM hFourthM; omega)
  have shared_fourth_sibling (W Z : World3) (hW : W ∈ T) (hZ : Z ∈ T) :
      readAt W (v ++ [true] ++ [false]) 4 = readAt Z (v ++ [true] ++ [false]) 4 := by
    have hWm : W ∈ responseSlice T (v ++ [true]) false zFourthM := hFourthMwhole.symm ▸ hW
    have hZm : Z ∈ responseSlice T (v ++ [true]) false zFourthM := hFourthMwhole.symm ▸ hZ
    have hw := (Finset.mem_filter.mp hWm).2
    have hz := (Finset.mem_filter.mp hZm).2
    simpa [hvlen] using hw.trans hz.symm

end D5.S3.Observer.CubicGain.MixedTripleExclusion
