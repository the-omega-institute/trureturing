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
  have hz' : acquisition (v ++ p) * D = acquisition (v ++ p) * 0 := by simpa using hz
  have hd0 : D = 0 := (acquisition_unit (v ++ p)).mul_left_cancel hz'
  exact weighted_sources_zero W Z hP _ _ (sub_eq_zero.mp hd0)

end D5.S3.Observer.CubicGain.MixedTripleExclusion
