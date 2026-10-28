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
private theorem equal_read_difference (W Z : World3) (v u : List Bool)
    (he : readAt W (v ++ u) (v.length+u.length) = readAt Z (v ++ u) (v.length+u.length)) :
    Matrix.trace (acquisition u * (acquisition v *
      ((gain 3 W.coeff).eval ((v.length + u.length : ℕ) : ℝ) • W.source -
        (gain 3 Z.coeff).eval ((v.length + u.length : ℕ) : ℝ) • Z.source))) =
      Z.drift - W.drift := by
  rw [read_concat, read_concat] at he
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul, ← Matrix.mul_assoc]
  linarith
private theorem pair_read_difference (n : ℕ) (T : Finset World3) (v : List Bool)
    (hT : T.card = 2) (h : Losing n T v)
    (W Z : World3) (hW : W ∈ T) (hZ : Z ∈ T)
    (u : List Bool) (hu : u ≠ []) (hun : u.length ≤ n) :
    Matrix.trace (acquisition u * (acquisition v *
      ((gain 3 W.coeff).eval ((v.length + u.length : ℕ) : ℝ) • W.source -
        (gain 3 Z.coeff).eval ((v.length + u.length : ℕ) : ℝ) • Z.source))) =
      Z.drift - W.drift := by
  exact equal_read_difference W Z v u ((losing_pair_suffix n T v hT h u hun).2 hu W hW Z hZ)
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

private theorem pair_gain_zero_of_drift (n : ℕ) (T : Finset World3) (v : List Bool)
    (hT : T.card = 2) (h : Losing n T v)
    (W Z : World3) (hW : W ∈ T) (hZ : Z ∈ T) (hd : W.drift = Z.drift) (hP : W.source ≠ Z.source)
    (j : ℕ) (hj : 2 ≤ j) (hjn : j ≤ n) :
    (gain 3 W.coeff).eval ((v.length+j : ℕ) : ℝ) = 0 ∧
      (gain 3 Z.coeff).eval ((v.length+j : ℕ) : ℝ) = 0 := by
  let D : Mat := (gain 3 W.coeff).eval ((v.length+j : ℕ) : ℝ) • W.source -
    (gain 3 Z.coeff).eval ((v.length+j : ℕ) : ℝ) • Z.source
  let p : List Bool := List.replicate (j-2) true
  have hlen : p.length + 2 = j := by simp [p]; omega
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

private theorem pair_gain_zero (n : ℕ) (T : Finset World3) (v : List Bool)
    (hT : T.card = 2) (h : Losing n T v) (hn : 3 ≤ n)
    (W Z : World3) (hW : W ∈ T) (hZ : Z ∈ T) (hP : W.source ≠ Z.source)
    (j : ℕ) (hj : 2 ≤ j) (hjn : j ≤ n) :
    (gain 3 W.coeff).eval ((v.length+j : ℕ) : ℝ) = 0 ∧
      (gain 3 Z.coeff).eval ((v.length+j : ℕ) : ℝ) = 0 := by
  exact pair_gain_zero_of_drift n T v hT h W Z hW hZ
    (pair_common_drift n T v hT h hn W Z hW hZ) hP j hj hjn

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
    have h00 : W.source 0 0 = Z.source 0 0 := by linarith
    have h01 : W.source 0 1 = Z.source 0 1 := by linarith
    have h10 : W.source 1 0 = Z.source 1 0 := by linarith
    have h11 : W.source 1 1 = Z.source 1 1 := by linarith
    exact Matrix.ext (fun i k => by
      fin_cases i <;> fin_cases k <;>
        first | exact h00 | exact h01 | exact h10 | exact h11)
private def nx (W : World3) : ℝ := W.source 0 1 / W.source 1 1
private def ny (W : World3) : ℝ := W.source 1 0 / W.source 1 1
private def nr (W : World3) : Mat := !![nx W * ny W,nx W;ny W,1]
private def nc (W : World3) : Coeff 3 := W.source 1 1 • W.coeff
private def nh (W : World3) (t : ℝ) : ℝ := (gain 3 (nc W)).eval t

private theorem norm_source (W : World3) :
    0 < nx W ∧ 0 < ny W ∧ W.source = W.source 1 1 • nr W ∧
      (1 + nx W * ny W) * W.source 1 1 = 1 := by
  have hp := W.legal.1 1 1
  have hn := ne_of_gt hp
  obtain ⟨u,r,hu,hr,he,-,-⟩ := source_chart_exact W.source W.legal
  have hd : W.source 0 0 * W.source 1 1 = W.source 0 1 * W.source 1 0 := by
    rw [he]
    simp [sourceChart]
    ring
  have ht : W.source 0 0 + W.source 1 1 = 1 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using W.legal.2.2
  refine ⟨div_pos (W.legal.1 0 1) hp,div_pos (W.legal.1 1 0) hp,?_,?_⟩
  · ext i k
    fin_cases i <;> fin_cases k <;> simp [nr,nx,ny]
    · field_simp
      nlinarith
    · field_simp
    · field_simp
  · dsimp [nx,ny]
    field_simp
    nlinarith

private theorem nh_eval (W : World3) (t : ℝ) :
    nh W t = W.source 1 1 * (gain 3 W.coeff).eval t := by
  change (gain 3 (W.source 1 1 • W.coeff)).eval t = _
  rw [show gain 3 (W.source 1 1 • W.coeff) = W.source 1 1 • gain 3 W.coeff from
    (Polynomial.ofFn 4).map_smul _ _, Polynomial.eval_smul]
  rfl

private theorem norm_read (W : World3) (u : List Bool) :
    readAt W u u.length = nh W (u.length : ℝ) * Matrix.trace (acquisition u * nr W) + W.drift := by
  rw [readAt, List.take_length, (norm_source W).2.2.1, Matrix.mul_smul, Matrix.trace_smul,
    nh_eval]
  simp only [smul_eq_mul]
  ring

private theorem norm_first (W : World3) (a₀ j m : ℝ)
    (h0 : readAt W [] 0 = a₀) (hj : readAt W [true] 1 = j)
    (hm : readAt W [false] 1 = m) :
    nh W 1 = m-j ∧ W.drift = j-(m-j)*(nx W+ny W) ∧
      (1+nx W*ny W)*nh W 0 = a₀-W.drift := by
  have hj' := norm_read W [true]
  have hm' := norm_read W [false]
  have h0' := norm_read W []
  simp [acquisition, Raw,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
    D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
    nr, Matrix.mul_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_two] at hj' hm' h0'
  have h1 : nh W 1 = m-j := by linarith
  refine ⟨h1, ?_, ?_⟩
  · rw [h1] at hj'
    nlinarith only [hj', hj]
  · nlinarith only [h0', h0]

private theorem norm_injective (W Z : World3) (hx : nx W = nx Z) (hy : ny W = ny Z) :
    W.source = Z.source := by
  have hqW := (norm_source W).2.2.2
  have hqZ := (norm_source Z).2.2.2
  have hq : 1 + nx W * ny W ≠ 0 := by
    have := (norm_source W).1
    have := (norm_source W).2.1
    positivity
  have hd : W.source 1 1 = Z.source 1 1 := by
    apply mul_left_cancel₀ hq
    simpa [← hx,← hy] using hqW.trans hqZ.symm
  rw [(norm_source W).2.2.1,(norm_source Z).2.2.1]
  simp [nr,hx,hy,hd]
private theorem nh_zero (W : World3) (t : ℝ) : nh W t = 0 ↔ (gain 3 W.coeff).eval t = 0 := by
  rw [nh_eval, mul_eq_zero]
  simp [ne_of_gt (W.legal.1 1 1)]

private theorem nh_four (W : World3) (t : Fin 4 → ℝ) (ht : Function.Injective t) :
    ¬ ∀ i, nh W (t i) = 0 := by
  intro he
  exact not_four_roots W t ht (fun i => (nh_zero W (t i)).mp (he i))

private theorem norm_third_L (W : World3) :
    readAt W [true,false,true] 3 = nh W 3 * (nx W*ny W+nx W+ny W) + W.drift ∧
    readAt W [true,false,false] 3 = nh W 3 * (nx W*ny W+2*nx W+ny W+1) + W.drift := by
  have hj := norm_read W [true,false,true]
  have hm := norm_read W [true,false,false]
  norm_num [acquisition, Raw,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
    D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
    nr, Matrix.mul_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_two] at hj hm
  constructor <;> nlinarith

private theorem norm_third_U (W : World3) :
    readAt W [false,true,true] 3 = nh W 3 * (nx W+ny W+1) + W.drift ∧
    readAt W [false,true,false] 3 = nh W 3 * (nx W+ny W+2) + W.drift := by
  have hj := norm_read W [false,true,true]
  have hm := norm_read W [false,true,false]
  norm_num [acquisition, Raw,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
    D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
    nr, Matrix.mul_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_two] at hj hm
  constructor <;> nlinarith

private theorem left_third_root (W Z : World3) (hs : nx W+ny W = nx Z+ny Z)
    (hd : W.drift = Z.drift) (hP : W.source ≠ Z.source)
    (hj : readAt W [true,false,true] 3 = readAt Z [true,false,true] 3)
    (hm : readAt W [true,false,false] 3 = readAt Z [true,false,false] 3) :
    nh W 3 = 0 ∧ nh Z 3 = 0 := by
  have hW := norm_third_L W
  have hZ := norm_third_L Z
  rw [hW.1,hZ.1,← hd] at hj
  rw [hW.2,hZ.2,← hd] at hm
  have he : nh W 3 * (nx W+1) = nh Z 3 * (nx Z+1) := by linarith
  have hpoly : nh W 3 * (nx W - nx Z) * (nx W*nx Z+nx W+nx Z) = 0 := by
    linear_combination -(nx Z+1)*hj +
      (nx Z*ny Z+nx Z+ny Z)*he + nh W 3*(nx Z+1)*(nx W+1)*hs
  have hp : 0 < nx W*nx Z+nx W+nx Z := by
    have := (norm_source W).1
    have := (norm_source Z).1
    positivity
  have hxne : nx W ≠ nx Z := by
    intro hx
    exact hP (norm_injective W Z hx (by linarith))
  have hw : nh W 3 = 0 := (mul_eq_zero.mp
    ((mul_eq_zero.mp hpoly).resolve_right (ne_of_gt hp))).resolve_right (sub_ne_zero.mpr hxne)
  have hz : nh Z 3 = 0 := by
    have hpZ : nx Z+1 ≠ 0 := by have := (norm_source Z).1; positivity
    exact (mul_eq_zero.mp (by simpa [hw] using he.symm)).resolve_right hpZ
  exact ⟨hw,hz⟩

private theorem roots_identify (a₀ j m b : ℝ) (v : List Bool)
    (hv : v = [true,false] ∨ v = [false,true]) (W Z : World3)
    (hW : readAt W [] 0 = a₀ ∧ readAt W [true] 1 = j ∧ readAt W [false] 1 = m ∧ readAt W v 2 = b)
    (hZ : readAt Z [] 0 = a₀ ∧ readAt Z [true] 1 = j ∧ readAt Z [false] 1 = m ∧ readAt Z v 2 = b)
    (hd : W.drift = Z.drift) (t : Fin 3 → ℝ)
    (ht : ∀ r : ℝ, r = 0 ∨ r = 1 ∨ r = 2 → Function.Injective (Fin.cons r t))
    (hw : ∀ i, (gain 3 W.coeff).eval (t i) = 0)
    (hz : ∀ i, (gain 3 Z.coeff).eval (t i) = 0) : W.source = Z.source := by
  have h0W := hW.1
  have h0Z := hZ.1
  simp [readAt, acquisition, Raw,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
    W.legal.2.2,Z.legal.2.2,← hd] at h0W h0Z
  have he0 : (gain 3 W.coeff).eval 0 = (gain 3 Z.coeff).eval 0 := by linarith
  have hc : W.coeff = Z.coeff := four_evaluations W.coeff Z.coeff (Fin.cons 0 t)
    (ht 0 (Or.inl rfl)) (by intro i; refine Fin.cases he0 (fun k => ?_) i; simp [hw,hz])
  have hn (r : ℝ) (hr : r = 1 ∨ r = 2) : (gain 3 W.coeff).eval r ≠ 0 := by
    intro he
    exact not_four_roots W (Fin.cons r t) (ht r (Or.inr hr))
      (by intro i; refine Fin.cases he (fun k => ?_) i; simpa using hw k)
  exact common_gain_source j m b v hv W Z hW.2.1 hW.2.2.1 hW.2.2.2
    hZ.2.1 hZ.2.2.1 hZ.2.2.2 hd (congrArg (gain 3) hc)
    (hn 1 (Or.inl rfl)) (hn 2 (Or.inr rfl))

private theorem normalized_equal_read (W Z : World3) (u : List Bool)
    (hc : nc W = nc Z) (hd : W.drift = Z.drift)
    (hn : nh W (u.length : ℝ) ≠ 0)
    (he : readAt W u u.length = readAt Z u u.length) :
    Matrix.trace (acquisition u * nr W) = Matrix.trace (acquisition u * nr Z) := by
  rw [norm_read,norm_read,← hd] at he
  have hnz : nh Z (u.length : ℝ) = nh W (u.length : ℝ) := by simp [nh,hc]
  rw [hnz] at he
  exact mul_left_cancel₀ hn (add_right_cancel he)

private theorem fourth_pair_constraint (a₀ j m b : ℝ) (hℓ : m-j ≠ 0)
    (v : List Bool) (hv : v = [true,false] ∨ v = [false,true]) (E F : Bool)
    (W Z : World3) (hP : W.source ≠ Z.source)
    (hW : readAt W [] 0 = a₀ ∧ readAt W [true] 1 = j ∧ readAt W [false] 1 = m ∧ readAt W v 2 = b)
    (hZ : readAt Z [] 0 = a₀ ∧ readAt Z [true] 1 = j ∧ readAt Z [false] 1 = m ∧ readAt Z v 2 = b)
    (hd : W.drift = Z.drift)
    (h6 : (gain 3 W.coeff).eval 6 = 0 ∧ (gain 3 Z.coeff).eval 6 = 0)
    (h7 : (gain 3 W.coeff).eval 7 = 0 ∧ (gain 3 Z.coeff).eval 7 = 0)
    (hj : readAt W (v ++ [true]) 3 = readAt Z (v ++ [true]) 3)
    (hm : readAt W (v ++ [false]) 3 = readAt Z (v ++ [false]) 3)
    (h4 : readAt W (v ++ [E,F]) 4 = readAt Z (v ++ [E,F]) 4)
    (h5 : readAt W (v ++ [E,F,true]) 5 = readAt Z (v ++ [E,F,true]) 5) :
    E = true ∧ F = true ∧
      readAt W (v ++ [true,false]) 4 ≠ readAt Z (v ++ [true,false]) 4 := by
  have fW := norm_first W a₀ j m hW.1 hW.2.1 hW.2.2.1
  have fZ := norm_first Z a₀ j m hZ.1 hZ.2.1 hZ.2.2.1
  have hs : nx W+ny W = nx Z+ny Z := by
    apply mul_left_cancel₀ hℓ
    linarith [fW.2.1,fZ.2.1]
  rcases hv with rfl | rfl
  · have hr := left_third_root W Z hs hd hP (by simpa using hj) (by simpa using hm)
    have hrW := (nh_zero W 3).mp hr.1
    have hrZ := (nh_zero Z 3).mp hr.2
    exact (hP (roots_identify a₀ j m b [true,false] (Or.inl rfl) W Z hW hZ hd
      ![3,6,7] (by intro r hr; rcases hr with rfl | rfl | rfl <;> intro i k he <;> fin_cases i <;> fin_cases k <;> norm_num at *)
      (by intro i; fin_cases i <;> simp [hrW,h6,h7])
      (by intro i; fin_cases i <;> simp [hrZ,h6,h7]))).elim
  · have tW := norm_third_U W
    have tZ := norm_third_U Z
    have he3 : nh W 3 = nh Z 3 := by
      simp only [List.cons_append,List.nil_append] at hj hm
      rw [tW.1,tZ.1,← hd] at hj
      rw [tW.2,tZ.2,← hd] at hm
      linarith
    have hc : nc W = nc Z := four_evaluations (nc W) (nc Z) ![1,3,6,7]
      (by intro i k he <;> fin_cases i <;> fin_cases k <;> norm_num at *)
      (by intro i; change nh W _ = nh Z _; fin_cases i <;>
        first | exact fW.1.trans fZ.1.symm | exact he3 | simp [nh_eval,h6,h7])
    have hnh (r : ℝ) : nh Z r = nh W r := by simp [nh,hc]
    have hq (he0 : a₀-W.drift ≠ 0) : nx W*ny W = nx Z*ny Z := by
      have hn : nh W 0 ≠ 0 := by
        intro he
        exact he0 (by simpa [he] using fW.2.2.symm)
      have he : (1+nx W*ny W)*nh W 0 = (1+nx Z*ny Z)*nh W 0 := by
        rw [fW.2.2,← hnh 0,fZ.2.2,← hd]
      have := mul_right_cancel₀ hn he
      linarith
    have second (hn : nh W 2 ≠ 0) :
        nx W*ny W+ny W = nx Z*ny Z+ny Z := by
      have he := normalized_equal_read W Z [false,true] hc hd (by simpa using hn)
        (hW.2.2.2.trans hZ.2.2.2.symm)
      norm_num [acquisition,Raw,
        D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
        D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
        D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
        nr,Matrix.mul_apply,Matrix.trace,Matrix.diag,Fin.sum_univ_two] at he
      linarith
    by_cases hz0 : a₀-W.drift = 0
    · have he0 : nh W 0 = 0 := by
        have hqpos : 0 < 1+nx W*ny W := by
          have := (norm_source W).1
          have := (norm_source W).2.1
          positivity
        exact (mul_eq_zero.mp (by simpa [hz0] using fW.2.2)).resolve_left (ne_of_gt hqpos)
      have hn (r : ℝ) (hr : r = 2 ∨ r = 4 ∨ r = 5) : nh W r ≠ 0 := by
        intro he
        apply nh_four W ![r,0,6,7]
          (by rcases hr with rfl | rfl | rfl <;> intro i k he <;> fin_cases i <;> fin_cases k <;> norm_num at *)
        intro i
        fin_cases i <;> simp [he,he0,nh_eval,h6,h7]
      have hsecond := second (hn 2 (Or.inl rfl))
      have e4 := normalized_equal_read W Z ([false,true] ++ [E,F]) hc hd
        (by simpa using hn 4 (Or.inr (Or.inl rfl))) (by simpa using h4)
      have e5 := normalized_equal_read W Z ([false,true] ++ [E,F,true]) hc hd
        (by simpa using hn 5 (Or.inr (Or.inr rfl))) (by simpa using h5)
      have heEF : E = true ∧ F = true := by
        cases E <;> cases F
        all_goals try exact ⟨rfl,rfl⟩
        all_goals
          exfalso
          simp [acquisition,Raw,
            D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
            D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
            D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
            nr,Matrix.mul_apply,Matrix.trace,Matrix.diag,Fin.sum_univ_two] at e4 e5
          apply hP
          apply norm_injective W Z <;> nlinarith only [hs,hsecond,e4,e5]
      refine ⟨heEF.1,heEF.2,?_⟩
      intro he
      have es := normalized_equal_read W Z [false,true,true,false] hc hd
        (by simpa using hn 4 (Or.inr (Or.inl rfl))) (by simpa using he)
      simp [acquisition,Raw,
        D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
        D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
        D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
        nr,Matrix.mul_apply,Matrix.trace,Matrix.diag,Fin.sum_univ_two] at es
      exact hP (norm_injective W Z (by linarith) (by linarith))
    · have hprod := hq hz0
      have he2 : nh W 2 = 0 := by
        by_contra hn
        have he := second hn
        exact hP (norm_injective W Z (by linarith) (by linarith))
      have hn (r : ℝ) (hr : r = 4 ∨ r = 5) : nh W r ≠ 0 := by
        intro he
        apply nh_four W ![r,2,6,7]
          (by rcases hr with rfl | rfl <;> intro i k he <;> fin_cases i <;> fin_cases k <;> norm_num at *)
        intro i
        fin_cases i <;> simp [he,he2,nh_eval,h6,h7]
      have e4 := normalized_equal_read W Z ([false,true] ++ [E,F]) hc hd
        (by simpa using hn 4 (Or.inl rfl)) (by simpa using h4)
      have e5 := normalized_equal_read W Z ([false,true] ++ [E,F,true]) hc hd
        (by simpa using hn 5 (Or.inr rfl)) (by simpa using h5)
      exfalso
      cases E <;> cases F
      all_goals
        simp [acquisition,Raw,
          D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
          D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
          D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
          nr,Matrix.mul_apply,Matrix.trace,Matrix.diag,Fin.sum_univ_two] at e4 e5
        apply hP
        apply norm_injective W Z <;> nlinarith only [hs,hprod,e4,e5]

private theorem mixed_weighted_zero (W Z : World3) (hP : W.source ≠ Z.source)
    (v : List Bool) (hv : v = [true,false] ∨ v = [false,true]) (a b c : ℝ)
    (he : acquisition v * (a • W.source - b • Z.source) = !![c,0;0,0]) :
    c = 0 ∧ a = 0 ∧ b = 0 := by
  rw [(norm_source W).2.2.1,(norm_source Z).2.2.1] at he
  have e00 := congrArg (fun S : Mat => S 0 0) he
  have e01 := congrArg (fun S : Mat => S 0 1) he
  have e10 := congrArg (fun S : Mat => S 1 0) he
  have e11 := congrArg (fun S : Mat => S 1 1) he
  have dW := ne_of_gt (W.legal.1 1 1)
  have dZ := ne_of_gt (Z.legal.1 1 1)
  rcases hv with rfl | rfl
  all_goals
    simp [acquisition,Raw,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      nr,Matrix.mul_apply,Matrix.trace,Matrix.diag,Fin.sum_univ_two] at e00 e01 e10 e11
    have hab : a*W.source 1 1 = b*Z.source 1 1 := by linarith
    have ha : a = 0 := by
      by_contra ha
      have hane := mul_ne_zero ha dW
      have hx : nx W = nx Z := by
        apply mul_left_cancel₀ hane
        first
        | linear_combination e01 - nx Z*hab
        | linear_combination e01 - (nx Z+1)*hab
      have hy : ny W = ny Z := by
        apply mul_left_cancel₀ hane
        first
        | linear_combination e10 - ny Z*hab
        | have hxpos : nx W+1 ≠ 0 := by have := (norm_source W).1; positivity
          apply mul_left_cancel₀ hxpos
          rw [← hx] at e10
          linear_combination e10 - (nx W*ny Z+ny Z)*hab
      exact hP (norm_injective W Z hx hy)
    have hb : b = 0 := by
      exact (mul_eq_zero.mp (by simpa [ha] using hab.symm)).resolve_right dZ
    exact ⟨by simpa [ha,hb] using e00.symm,ha,hb⟩

private theorem odd_trace_obstruction (A : Mat) (hdet : A.det = -1) (e : ℝ) (he : e ≠ 0)
    (h0 : Matrix.trace (A * (e • !![0,1;-1,0])) = 0)
    (hj : Matrix.trace (action true * A * (e • !![0,1;-1,0])) = 0)
    (hm : Matrix.trace (action false * A * (e • !![0,1;-1,0])) = 0) : False := by
  simp [action_j_shape,action_m_shape,Matrix.mul_apply,Matrix.vecMul,
    dotProduct,Matrix.trace,Matrix.diag,Fin.sum_univ_two] at h0 hj hm
  have h01 : A 0 1 = 0 := by
    apply mul_left_cancel₀ he
    linear_combination hm - hj - h0
  have h10 : A 1 0 = 0 := by
    apply mul_left_cancel₀ he
    linear_combination hm - hj
  have hdiag : A 0 0 = A 1 1 := by
    apply mul_left_cancel₀ he
    linear_combination hj
  simp [Matrix.det_fin_two,h01,h10,hdiag] at hdet
  nlinarith [sq_nonneg (A 1 1)]

private theorem fifth_pair_nezero (a₀ j m b : ℝ) (W Z : World3)
    (hP : W.source ≠ Z.source)
    (hW : readAt W [] 0 = a₀ ∧ readAt W [true] 1 = j ∧ readAt W [false] 1 = m ∧ readAt W [false,true] 2 = b)
    (hZ : readAt Z [] 0 = a₀ ∧ readAt Z [true] 1 = j ∧ readAt Z [false] 1 = m ∧ readAt Z [false,true] 2 = b)
    (hd : W.drift = Z.drift) (hs : nx W+ny W = nx Z+ny Z)
    (hc0 : a₀-W.drift ≠ 0) (h3 : nh W 3 = nh Z 3)
    (h4 : (gain 3 W.coeff).eval 4 = 0 ∧ (gain 3 Z.coeff).eval 4 = 0)
    (h7 : (gain 3 W.coeff).eval 7 = 0 ∧ (gain 3 Z.coeff).eval 7 = 0)
    (u : List Bool) (hu : u.length = 5)
    (h5 : readAt W u 5 = readAt Z u 5)
    (h6 : ∀ E : Bool, readAt W (u ++ [E]) 6 = readAt Z (u ++ [E]) 6) : False := by
  have fW := norm_first W a₀ j m hW.1 hW.2.1 hW.2.2.1
  have fZ := norm_first Z a₀ j m hZ.1 hZ.2.1 hZ.2.2.1
  have hc : nc W = nc Z := four_evaluations (nc W) (nc Z) ![1,3,4,7]
    (by intro i k he <;> fin_cases i <;> fin_cases k <;> norm_num at *)
    (by intro i; change nh W _ = nh Z _; fin_cases i <;>
      first | exact fW.1.trans fZ.1.symm | exact h3 | simp [nh_eval,h4,h7])
  have hnh (r : ℝ) : nh Z r = nh W r := by simp [nh,hc]
  have hn0 : nh W 0 ≠ 0 := by intro he; exact hc0 (by simpa [he] using fW.2.2.symm)
  have hp : nx W*ny W = nx Z*ny Z := by
    have eq0 : (1+nx W*ny W)*nh W 0 = (1+nx Z*ny Z)*nh W 0 := by
      rw [fW.2.2,← hnh 0,fZ.2.2,← hd]
    have := mul_right_cancel₀ hn0 eq0
    linarith
  have he2 : nh W 2 = 0 := by
    by_contra hn
    have he := normalized_equal_read W Z [false,true] hc hd (by simpa using hn)
      (hW.2.2.2.trans hZ.2.2.2.symm)
    norm_num [acquisition,Raw,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      nr,Matrix.mul_apply,Matrix.trace,Matrix.diag,Fin.sum_univ_two] at he
    exact hP (norm_injective W Z (by linarith) (by linarith))
  have hn (r : ℝ) (hr : r = 5 ∨ r = 6) : nh W r ≠ 0 := by
    intro he
    apply nh_four W ![r,2,4,7]
      (by rcases hr with rfl | rfl <;> intro i k he <;> fin_cases i <;> fin_cases k <;> norm_num at *)
    intro i
    fin_cases i <;> simp [he,he2,nh_eval,h4,h7]
  have hD : nr W-nr Z = (nx W-nx Z) • (!![0,1;-1,0] : Mat) := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [nr] <;> linarith
  have hx : nx W-nx Z ≠ 0 := by
    intro he
    exact hP (norm_injective W Z (by linarith) (by linarith))
  have e5 := normalized_equal_read W Z u hc hd (by simpa [hu] using hn 5 (Or.inl rfl))
    (by simpa [hu] using h5)
  have e6 (E : Bool) := normalized_equal_read W Z (u ++ [E]) hc hd
    (by simpa [hu] using hn 6 (Or.inr rfl)) (by simpa [hu] using h6 E)
  have ht : Matrix.trace (acquisition u * (nr W-nr Z)) = 0 := by
    rw [Matrix.mul_sub,Matrix.trace_sub,e5,sub_self]
  have hta (E : Bool) : Matrix.trace (action E * acquisition u * (nr W-nr Z)) = 0 := by
    have he := e6 E
    rw [acquisition_append] at he
    rw [Matrix.mul_sub,Matrix.trace_sub,he,sub_self]
  have hdet : (acquisition u).det = -1 := by
    have raw := (D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.raw_word_signed_bound u).2.2.1
    have he := ((Int.castRingHom ℝ).map_det (Raw u)).symm
    change (acquisition u).det = _ at he
    rw [he]
    simp [Raw,raw,hu]
  rw [hD] at ht
  have hj := hta true
  have hm := hta false
  rw [hD] at hj hm
  exact odd_trace_obstruction (acquisition u) hdet (nx W-nx Z) hx ht hj hm

private theorem three_quadratic (T : Finset World3) (hT : T.card = 3)
    (hP : ∀ W ∈ T, ∀ Z ∈ T, W ≠ Z → W.source ≠ Z.source)
    (s C lam : ℝ) (hs : ∀ W ∈ T, nx W+ny W = s)
    (hq : ∀ W ∈ T, nx W*ny W+lam*ny W = C) : False := by
  obtain ⟨W,Z,X,hWZ,hWX,hZX,hset⟩ := Finset.card_eq_three.mp hT
  have hW : W ∈ T := by simp [hset]
  have hZ : Z ∈ T := by simp [hset]
  have hX : X ∈ T := by simp [hset]
  have distinct (U V : World3) (hU : U ∈ T) (hV : V ∈ T) (hne : U ≠ V) : ny U ≠ ny V := by
    intro he
    exact hP U hU V hV hne (norm_injective U V (by linarith [hs U hU,hs V hV]) he)
  have hYZ := distinct W Z hW hZ hWZ
  have hYX := distinct W X hW hX hWX
  have hZX' := distinct Z X hZ hX hZX
  let p : Polynomial ℝ := Polynomial.X^2 - Polynomial.C (s+lam)*Polynomial.X + Polynomial.C C
  have hp (U : World3) (hU : U ∈ T) : p.eval (ny U) = 0 := by
    simp only [p,Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_pow,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    linear_combination ny U*(hs U hU) - hq U hU
  have hzero : p = 0 := Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
    (Finset.univ : Finset (Fin 3))
    (v := ![ny W,ny Z,ny X])
    (by intro i _ k _ he; fin_cases i <;> fin_cases k <;> simp_all)
    (by norm_num; dsimp [p]; compute_degree)
    (by intro i _; fin_cases i <;> first | exact hp W hW | exact hp Z hZ | exact hp X hX)
  have he := congrArg (fun q : Polynomial ℝ => q.coeff 2) hzero
  norm_num [p,Polynomial.coeff_X_pow,Polynomial.coeff_C_mul_X] at he

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
      exact hsource (roots_identify a₀ j m b v hv W Z (hreads W hWroot) (hreads Z hZroot)
        hd ![5,6,7] (by intro r hr; rcases hr with rfl | rfl | rfl <;> intro i k he <;>
          fin_cases i <;> fin_cases k <;> norm_num at *)
        (by intro i; fin_cases i <;> simp [h5,h6,h7])
        (by intro i; fin_cases i <;> simp [h5,h6,h7]))
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
    have hScard : S.card = 2 := h2
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
    have h4 : readAt W (v ++ [true,false]) 4 = readAt Z (v ++ [true,false]) 4 := by
      have hw := (Finset.mem_filter.mp hW).2
      have hz' := (Finset.mem_filter.mp hZ).2
      simpa [hvlen,List.append_assoc] using hw.trans hz'.symm
    have h5 := (losing_pair_suffix 3 S (v ++ [true] ++ [false]) hScard hz
      [true] (by simp)).2 (by simp) W hW Z hZ
    have hc := fourth_pair_constraint a₀ j m b hℓ v hv true false W Z hsource
      (hreads W hWroot) (hreads Z hZroot) hd h6 h7 (hWJ.trans hZJ.symm)
      (hWM.trans hZM.symm) h4 (by simpa [hvlen,List.append_assoc] using h5)
    exact Bool.false_ne_true hc.2.1
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

  have fourth_full : ∀ E F : Bool, ∃ z : ℝ,
      responseSlice T (v ++ [E]) F z = T ∧ Losing 3 T (v ++ [E] ++ [F]) := by
    intro E F
    obtain ⟨_,_,hEL⟩ := third_full E
    obtain ⟨z,hz⟩ := hEL.2 F
    let S := responseSlice T (v ++ [E]) F z
    have hsub : S ⊆ T := responseSlice_subset T (v ++ [E]) F z
    have hlow : 2 ≤ S.card := losing_guard 3 _ _ hz
    have hhigh : S.card ≤ 3 := by simpa [hT] using Finset.card_le_card hsub
    have hnotpair : S.card ≠ 2 := by
      intro h2
      obtain ⟨W,hW,Z,hZ,hWZ⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
      have hWr := hsub hW
      have hZr := hsub hZ
      have hsource := hP W hWr Z hZr hWZ
      have hd := pair_common_drift 3 S (v ++ [E] ++ [F]) h2 hz (by omega) W Z hW hZ
      have h6 := pair_gain_zero 3 S (v ++ [E] ++ [F]) h2 hz (by omega)
        W Z hW hZ hsource 2 (by omega) (by omega)
      have h7 := pair_gain_zero 3 S (v ++ [E] ++ [F]) h2 hz (by omega)
        W Z hW hZ hsource 3 (by omega) (by omega)
      norm_num [List.length_append,hvlen] at h6 h7
      have h4 : readAt W (v ++ [E,F]) 4 = readAt Z (v ++ [E,F]) 4 := by
        have hw := (Finset.mem_filter.mp hW).2
        have hz' := (Finset.mem_filter.mp hZ).2
        simpa [hvlen,List.append_assoc] using hw.trans hz'.symm
      have h5 := (losing_pair_suffix 3 S (v ++ [E] ++ [F]) h2 hz
        [true] (by simp)).2 (by simp) W hW Z hZ
      have hc := fourth_pair_constraint a₀ j m b hℓ v hv E F W Z hsource
        (hreads W hWr) (hreads Z hZr) hd h6 h7
        ((shared_third true zJ hJ W hWr).trans (shared_third true zJ hJ Z hZr).symm)
        ((shared_third false zM hM W hWr).trans (shared_third false zM hM Z hZr).symm)
        h4 (by simpa [hvlen,List.append_assoc] using h5)
      exact hc.2.2 (by simpa [List.append_assoc] using shared_fourth_sibling W Z hWr hZr)
    have he : S = T := Finset.eq_of_subset_of_card_le hsub (by rw [hT]; omega)
    exact ⟨z,he,he ▸ hz⟩
  have pair_fourth (W Z : World3) (hW : W ∈ T) (hZ : Z ∈ T) (hne : W ≠ Z) :
      W.drift = Z.drift ∧ (gain 3 W.coeff).eval 4 = 0 ∧ (gain 3 Z.coeff).eval 4 = 0 := by
    let D : Mat := (gain 3 W.coeff).eval 4 • W.source - (gain 3 Z.coeff).eval 4 • Z.source
    have hh : ∀ E F : Bool,
        Matrix.trace (action F * action E * (acquisition v * D)) = Z.drift-W.drift := by
      intro E F
      obtain ⟨z,he,_⟩ := fourth_full E F
      have hw : W ∈ responseSlice T (v ++ [E]) F z := he.symm ▸ hW
      have hz : Z ∈ responseSlice T (v ++ [E]) F z := he.symm ▸ hZ
      have hr := ((Finset.mem_filter.mp hw).2).trans ((Finset.mem_filter.mp hz).2).symm
      have hr' : readAt W (v ++ [E,F]) (v.length+[E,F].length) =
          readAt Z (v ++ [E,F]) (v.length+[E,F].length) := by
        simpa [hvlen,List.append_assoc] using hr
      have hdif := equal_read_difference W Z v [E,F] hr'
      simpa [D,acquisition_two,hvlen,Matrix.mul_assoc] using hdif
    have hc := two_product_equal_trace (acquisition v * D) (Z.drift-W.drift) hh
    have hz := mixed_weighted_zero W Z (hP W hW Z hZ hne) v hv
      ((gain 3 W.coeff).eval 4) ((gain 3 Z.coeff).eval 4) (Z.drift-W.drift) hc
    exact ⟨by linarith [hz.1],hz.2.1,hz.2.2⟩
  have all_drift (W Z : World3) (hW : W ∈ T) (hZ : Z ∈ T) : W.drift = Z.drift := by
    by_cases he : W = Z
    · rw [he]
    · exact (pair_fourth W Z hW hZ he).1
  have all_fourth (W : World3) (hW : W ∈ T) : (gain 3 W.coeff).eval 4 = 0 := by
    obtain ⟨Z,hZ,hne⟩ := Finset.exists_mem_ne (show 1 < T.card by omega) W
    exact (pair_fourth W Z hW hZ hne.symm).2.1
  obtain ⟨W₀,hW₀⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  let s : ℝ := nx W₀+ny W₀
  let c : ℝ := a₀-W₀.drift
  have first (W : World3) (hW : W ∈ T) := norm_first W a₀ j m
    (hreads W hW).1 (hreads W hW).2.1 (hreads W hW).2.2.1
  have sums (W Z : World3) (hW : W ∈ T) (hZ : Z ∈ T) : nx W+ny W = nx Z+ny Z := by
    apply mul_left_cancel₀ hℓ
    linarith [(first W hW).2.1,(first Z hZ).2.1,all_drift W Z hW hZ]
  have sum0 (W : World3) (hW : W ∈ T) : nx W+ny W = s := sums W W₀ hW hW₀
  have left_root (hvL : v = [true,false]) (W : World3) (hW : W ∈ T) : (gain 3 W.coeff).eval 3 = 0 := by
    obtain ⟨Z,hZ,hne⟩ := Finset.exists_mem_ne (show 1 < T.card by omega) W
    apply (nh_zero W 3).mp
    exact (left_third_root W Z (sums W Z hW hZ) (all_drift W Z hW hZ)
      (hP W hW Z hZ hne.symm)
      (by simpa [hvL] using (shared_third true zJ hJ W hW).trans (shared_third true zJ hJ Z hZ).symm)
      (by simpa [hvL] using (shared_third false zM hM W hW).trans (shared_third false zM hM Z hZ).symm)).1
  have right_third (hvU : v = [false,true]) (W Z : World3) (hW : W ∈ T) (hZ : Z ∈ T) : nh W 3 = nh Z 3 := by
    have hj := (shared_third true zJ hJ W hW).trans (shared_third true zJ hJ Z hZ).symm
    have hm := (shared_third false zM hM W hW).trans (shared_third false zM hM Z hZ).symm
    simp only [hvU,List.cons_append,List.nil_append] at hj hm
    rw [(norm_third_U W).1,(norm_third_U Z).1] at hj
    rw [(norm_third_U W).2,(norm_third_U Z).2] at hm
    linarith [all_drift W Z hW hZ]
  have zero_initial (hc : c = 0) (W : World3) (hW : W ∈ T) : nh W 0 = 0 := by
    have hp : 1+nx W*ny W ≠ 0 := by
      have := (norm_source W).1; have := (norm_source W).2.1; positivity
    have he := (first W hW).2.2
    have hd := all_drift W W₀ hW hW₀
    have hz : (1+nx W*ny W)*nh W 0 = 0 := he.trans (by dsimp [c] at hc; linarith [hd])
    exact (mul_eq_zero.mp hz).resolve_left hp
  have coef_zero_initial (hvU : v = [false,true]) (hc : c = 0)
      (W Z : World3) (hW : W ∈ T) (hZ : Z ∈ T) : nc W = nc Z := by
    apply four_evaluations (nc W) (nc Z) ![0,1,3,4]
      (by intro i k he <;> fin_cases i <;> fin_cases k <;> norm_num at *)
    intro i
    fin_cases i
    · exact (zero_initial hc W hW).trans (zero_initial hc Z hZ).symm
    · exact (first W hW).1.trans (first Z hZ).1.symm
    · exact right_third hvU W Z hW hZ
    · exact ((nh_zero W 4).mpr (all_fourth W hW)).trans ((nh_zero Z 4).mpr (all_fourth Z hZ)).symm
  have quadratic_one (hvU : v = [false,true])
      (hco : ∀ W ∈ T, nc W = nc W₀) (hn2 : nh W₀ 2 ≠ 0) : False := by
    apply three_quadratic T hT hP s (nx W₀*ny W₀+ny W₀) 1 sum0
    intro W hW
    have hnW : nh W 2 ≠ 0 := by simpa [nh,hco W hW] using hn2
    have hr := normalized_equal_read W W₀ [false,true] (hco W hW) (all_drift W W₀ hW hW₀)
      (by simpa using hnW) (by simpa [hvU] using (hreads W hW).2.2.2.trans (hreads W₀ hW₀).2.2.2.symm)
    norm_num [acquisition,Raw,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      nr,Matrix.mul_apply,Matrix.trace,Matrix.diag,Fin.sum_univ_two] at hr
    linarith
  have fifth_full : ∀ E F G : Bool, ∃ z : ℝ,
      responseSlice T (v ++ [E] ++ [F]) G z = T ∧ Losing 2 T (v ++ [E] ++ [F] ++ [G]) := by
    intro E F G
    obtain ⟨_,_,hEF⟩ := fourth_full E F
    obtain ⟨z,hz⟩ := hEF.2 G
    let S := responseSlice T (v ++ [E] ++ [F]) G z
    let u := v ++ [E] ++ [F] ++ [G]
    have hu : u.length = 5 := by simp [u,hvlen]
    have hsub : S ⊆ T := responseSlice_subset T (v ++ [E] ++ [F]) G z
    have hlow : 2 ≤ S.card := losing_guard 2 _ _ hz
    have hhigh : S.card ≤ 3 := by simpa [hT] using Finset.card_le_card hsub
    have hnotpair : S.card ≠ 2 := by
      intro h2
      obtain ⟨W,hW,Z,hZ,hne⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
      have hWr := hsub hW
      have hZr := hsub hZ
      have hd := all_drift W Z hWr hZr
      have hsource := hP W hWr Z hZr hne
      have h7 := pair_gain_zero_of_drift 2 S u h2 hz W Z hW hZ hd hsource 2 (by omega) (by omega)
      norm_num [hu] at h7
      rcases hv with hvL | hvU
      · exact hsource (roots_identify a₀ j m b v (Or.inl hvL) W Z (hreads W hWr) (hreads Z hZr)
          hd ![3,4,7] (by intro r hr; rcases hr with rfl | rfl | rfl <;> intro i k he <;> fin_cases i <;> fin_cases k <;> norm_num at *)
          (by intro i; fin_cases i <;> simp [left_root hvL W hWr,all_fourth W hWr,h7])
          (by intro i; fin_cases i <;> simp [left_root hvL Z hZr,all_fourth Z hZr,h7]))
      · by_cases hc : c = 0
        · have hco (Y : World3) (hY : Y ∈ T) : nc Y = nc W₀ := coef_zero_initial hvU hc Y W₀ hY hW₀
          apply quadratic_one hvU hco
          intro he2
          apply nh_four W₀ ![2,0,4,7]
            (by intro i k he <;> fin_cases i <;> fin_cases k <;> norm_num at *)
          intro i
          fin_cases i
          · exact he2
          · exact zero_initial hc W₀ hW₀
          · simp [nh_eval,all_fourth W₀ hW₀]
          · have he7 : nh W 7 = 0 := (nh_zero W 7).mpr h7.1
            simpa [nh,hco W hWr] using he7
        · have h5 : readAt W u 5 = readAt Z u 5 := by
            have he := ((Finset.mem_filter.mp hW).2).trans ((Finset.mem_filter.mp hZ).2).symm
            simpa [u,hvlen] using he
          have h6 (A : Bool) : readAt W (u ++ [A]) 6 = readAt Z (u ++ [A]) 6 := by
            have he := (losing_pair_suffix 2 S u h2 hz [A] (by simp)).2 (by simp) W hW Z hZ
            simpa [hu] using he
          exact fifth_pair_nezero a₀ j m b W Z hsource
            (by simpa [hvU] using hreads W hWr) (by simpa [hvU] using hreads Z hZr)
            hd (sums W Z hWr hZr) (by simpa [c,all_drift W W₀ hWr hW₀] using hc)
            (right_third hvU W Z hWr hZr) ⟨all_fourth W hWr,all_fourth Z hZr⟩ h7 u hu h5 h6
    have he : S = T := Finset.eq_of_subset_of_card_le hsub (by rw [hT]; omega)
    exact ⟨z,he,he ▸ hz⟩
  have pair_fifth (W Z : World3) (hW : W ∈ T) (hZ : Z ∈ T) (hne : W ≠ Z) :
      (gain 3 W.coeff).eval 5 = 0 ∧ (gain 3 Z.coeff).eval 5 = 0 := by
    let D : Mat := (gain 3 W.coeff).eval 5 • W.source - (gain 3 Z.coeff).eval 5 • Z.source
    have hh : ∀ E F G : Bool,
        Matrix.trace (action G * action F * action E * (acquisition v * D)) = 0 := by
      intro E F G
      obtain ⟨z,he,_⟩ := fifth_full E F G
      have hw : W ∈ responseSlice T (v ++ [E] ++ [F]) G z := he.symm ▸ hW
      have hz : Z ∈ responseSlice T (v ++ [E] ++ [F]) G z := he.symm ▸ hZ
      have hr := ((Finset.mem_filter.mp hw).2).trans ((Finset.mem_filter.mp hz).2).symm
      have hr' : readAt W (v ++ [E,F,G]) (v.length+[E,F,G].length) =
          readAt Z (v ++ [E,F,G]) (v.length+[E,F,G].length) := by simpa [hvlen,List.append_assoc] using hr
      have hdif := equal_read_difference W Z v [E,F,G] hr'
      simpa [D,acquisition_three,hvlen,Matrix.mul_assoc,all_drift W Z hW hZ] using hdif
    have hz := (three_product_equal_trace (acquisition v * D) 0 hh).1
    have hz' : acquisition v * D = acquisition v * 0 := by simpa using hz
    have hD := (acquisition_unit v).mul_left_cancel hz'
    exact weighted_sources_zero W Z (hP W hW Z hZ hne) _ _ (sub_eq_zero.mp hD)
  have all_fifth (W : World3) (hW : W ∈ T) : (gain 3 W.coeff).eval 5 = 0 := by
    obtain ⟨Z,hZ,hne⟩ := Finset.exists_mem_ne (show 1 < T.card by omega) W
    exact (pair_fifth W Z hW hZ hne.symm).1
  rcases hv with hvL | hvU
  · obtain ⟨Z,hZ,hne⟩ := Finset.exists_mem_ne (show 1 < T.card by omega) W₀
    exact hP W₀ hW₀ Z hZ hne.symm (roots_identify a₀ j m b v (Or.inl hvL) W₀ Z
      (hreads W₀ hW₀) (hreads Z hZ) (all_drift W₀ Z hW₀ hZ) ![3,4,5]
      (by intro r hr; rcases hr with rfl | rfl | rfl <;> intro i k he <;> fin_cases i <;> fin_cases k <;> norm_num at *)
      (by intro i; fin_cases i <;> simp [left_root hvL W₀ hW₀,all_fourth W₀ hW₀,all_fifth W₀ hW₀])
      (by intro i; fin_cases i <;> simp [left_root hvL Z hZ,all_fourth Z hZ,all_fifth Z hZ]))
  · by_cases hc : c = 0
    · apply quadratic_one hvU (fun W hW => coef_zero_initial hvU hc W W₀ hW hW₀)
      intro he2
      apply nh_four W₀ ![2,0,4,5]
        (by intro i k he <;> fin_cases i <;> fin_cases k <;> norm_num at *)
      intro i
      fin_cases i <;> simp [he2,zero_initial hc W₀ hW₀,nh_eval,all_fourth W₀ hW₀,all_fifth W₀ hW₀]
    · have hco (W : World3) (hW : W ∈ T) : nc W = nc W₀ := by
        apply four_evaluations (nc W) (nc W₀) ![1,3,4,5]
          (by intro i k he <;> fin_cases i <;> fin_cases k <;> norm_num at *)
        intro i
        fin_cases i
        · exact (first W hW).1.trans (first W₀ hW₀).1.symm
        · exact right_third hvU W W₀ hW hW₀
        · exact ((nh_zero W 4).mpr (all_fourth W hW)).trans ((nh_zero W₀ 4).mpr (all_fourth W₀ hW₀)).symm
        · exact ((nh_zero W 5).mpr (all_fifth W hW)).trans ((nh_zero W₀ 5).mpr (all_fifth W₀ hW₀)).symm
      have hn0 : nh W₀ 0 ≠ 0 := by
        intro he
        exact hc (by dsimp [c]; simpa [he] using (first W₀ hW₀).2.2.symm)
      apply three_quadratic T hT hP s (nx W₀*ny W₀) 0 sum0
      intro W hW
      have eq0 : (1+nx W*ny W)*nh W₀ 0 = (1+nx W₀*ny W₀)*nh W₀ 0 := by
        have he := (first W hW).2.2
        simpa [nh,hco W hW,all_drift W W₀ hW hW₀] using he.trans (first W₀ hW₀).2.2.symm
      have := mul_right_cancel₀ hn0 eq0
      linarith

end D5.S3.Observer.CubicGain.MixedTripleExclusion
