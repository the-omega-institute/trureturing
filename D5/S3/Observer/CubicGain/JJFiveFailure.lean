/- GID: D5/S3/Observer/CubicGain/JJFiveFailure
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/JJFiveFailure
   mirror-E: none(waiver:exact-complete-world-five-read-obstruction)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Observer/CubicGain/JJFiveFailure.five_read_recovery_claim; result=D5/S3/Observer/CubicGain/JJFiveFailure.result; claim=D5/S3/Observer/CubicGain/JJFiveFailure.five_read_recovery_claim
   digest: Sixty-four prescribed complete targets share one ancestor assignment and obstruct five further reads on the whole JJ fiber. -/

import D5.S3.Observer.CubicGain.CompleteFailure

/-! Fixed complete worlds on every five-action continuation below JJ. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix Classical

namespace D5.S3.Observer.CubicGain.JJFiveFailure
open D5.S3.Observer.Linear.GainRay
open D5.S3.Observer.CubicGain.CompleteFailure

private def pStar : Mat := (1 / 2 : ℝ) • !![1, 1; 1, 1]
private def rZero : Mat := !![-1, -1; 1, 1]
private def lZero : Mat := !![-1, 1; -1, 1]
private def rLine (u : ℝ) : Mat := pStar + u • rZero
private def lLine (u : ℝ) : Mat := pStar + u • lZero
private def alpha (H : Mat) : ℝ := Matrix.trace (H * rZero)
private def beta (H : Mat) : ℝ := Matrix.trace (H * lZero)
private def scale (H : Mat) : ℝ := 4 * (1 + |alpha H| + |beta H|)

/-- The three exact cases are selected by the terminal chronological matrix. -/
def qSource (H : Mat) (e : Bool) : Mat :=
  if alpha H = 0 then rLine (if e then 1 / 4 else -(1 / 4))
  else if beta H = 0 then lLine (if e then 1 / 4 else -(1 / 4))
  else if e then lLine (alpha H / scale H) else rLine (beta H / scale H)

private theorem transpose_legal (P : Mat) (h : LegalSource P) : LegalSource P.transpose := by
  exact ⟨fun i j => h.1 j i, by simpa using h.2.1, by simpa using h.2.2⟩

private theorem lLine_legal (u : ℝ) (hu : |u| < 1 / 2) : LegalSource (lLine u) := by
  have he : lLine u = identicalRow (1 / 2 + u) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lLine, pStar, lZero, identicalRow] <;> ring
  rw [he]
  have hb := abs_lt.mp hu
  exact identical_row_legal _ (by linarith [hb.1]) (by linarith [hb.2])

private theorem rLine_legal (u : ℝ) (hu : |u| < 1 / 2) : LegalSource (rLine u) := by
  have he : rLine u = (lLine u).transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rLine, lLine, pStar, rZero, lZero]
  rw [he]
  exact transpose_legal _ (lLine_legal u hu)

private theorem line_signatures (u : ℝ) :
    Matrix.trace (rLine u) = 1 ∧ Matrix.trace (lLine u) = 1 ∧
    Matrix.trace (action true * rLine u) = 1 ∧
    Matrix.trace (action true * lLine u) = 1 := by
  repeat' constructor
  all_goals simp [rLine, lLine, pStar, rZero, lZero, action_j_shape,
    Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

private theorem scale_bounds (H : Mat) :
    0 < scale H ∧ |alpha H / scale H| < 1 / 4 ∧
      |beta H / scale H| < 1 / 4 := by
  have ha := abs_nonneg (alpha H)
  have hb := abs_nonneg (beta H)
  have hs : 0 < scale H := by dsimp [scale]; positivity
  refine ⟨hs, ?_, ?_⟩
  all_goals rw [abs_div, abs_of_pos hs, div_lt_iff₀ hs]
  all_goals dsimp [scale]; linarith

private theorem qSource_legal (H : Mat) (e : Bool) : LegalSource (qSource H e) := by
  have hb := scale_bounds H
  by_cases ha : alpha H = 0
  · simpa [qSource, ha] using rLine_legal (if e then 1 / 4 else -(1 / 4))
      (by cases e <;> norm_num)
  · by_cases hb' : beta H = 0
    · simpa [qSource, ha, hb'] using lLine_legal (if e then 1 / 4 else -(1 / 4))
        (by cases e <;> norm_num)
    · cases e
      · simpa [qSource, ha, hb'] using
          rLine_legal _ (hb.2.2.trans (by norm_num : (1 / 4 : ℝ) < 1 / 2))
      · simpa [qSource, ha, hb'] using
          lLine_legal _ (hb.2.1.trans (by norm_num : (1 / 4 : ℝ) < 1 / 2))

private theorem qSource_signature (H : Mat) (e : Bool) :
    Matrix.trace (action true * qSource H e) = 1 := by
  by_cases ha : alpha H = 0
  · simp only [qSource, ha, ↓reduceIte]
    exact (line_signatures _).2.2.1
  · by_cases hb : beta H = 0
    · simp only [qSource, ha, hb, ↓reduceIte]
      exact (line_signatures _).2.2.2
    · cases e
      · simpa [qSource, ha, hb] using (line_signatures (beta H / scale H)).2.2.1
      · simpa [qSource, ha, hb] using (line_signatures (alpha H / scale H)).2.2.2

private theorem line_intersection (u v : ℝ) (h : rLine u = lLine v) : u = 0 ∧ v = 0 := by
  have h00 := congrArg (fun P : Mat => P 0 0) h
  have h01 := congrArg (fun P : Mat => P 0 1) h
  simp [rLine, lLine, pStar, rZero, lZero] at h00 h01
  constructor <;> linarith

private theorem qSource_distinct (H : Mat) : qSource H false ≠ qSource H true := by
  unfold qSource
  by_cases ha : alpha H = 0
  · simp only [ha, ↓reduceIte, Bool.false_eq_true]
    intro h
    have h00 := congrArg (fun P : Mat => P 0 0) h
    norm_num [rLine, pStar, rZero] at h00
  · by_cases hb : beta H = 0
    · simp only [ha, hb, ↓reduceIte, Bool.false_eq_true]
      intro h
      have h00 := congrArg (fun P : Mat => P 0 0) h
      norm_num [lLine, pStar, lZero] at h00
    · simp only [ha, hb, ↓reduceIte, Bool.false_eq_true]
      intro h
      have hz := (line_intersection _ _ h).2
      exact (div_ne_zero ha (ne_of_gt (scale_bounds H).1)) hz

private theorem qSource_collision (H : Mat) :
    Matrix.trace (H * qSource H false) = Matrix.trace (H * qSource H true) := by
  have hr (u : ℝ) : Matrix.trace (H * rLine u) = Matrix.trace (H * pStar) + u * alpha H := by
    simp [rLine, alpha, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul]
  have hl (u : ℝ) : Matrix.trace (H * lLine u) = Matrix.trace (H * pStar) + u * beta H := by
    simp [lLine, beta, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul]
  unfold qSource
  by_cases ha : alpha H = 0
  · simp [ha, hr]
  · by_cases hb : beta H = 0
    · simp [ha, hb, hl]
    · simp only [ha, hb, ↓reduceIte, Bool.false_eq_true, hr, hl]
      ring

/-- The fixed radical pair, with true denoting its transpose. -/
def aSource (e : Bool) : Mat :=
  let P : Mat := (1 / 768 : ℝ) •
    !![607, 372 + Real.sqrt 40657; 372 - Real.sqrt 40657, 161]
  if e then P.transpose else P

/-- The second fixed radical pair. -/
def bSource (e : Bool) : Mat :=
  let P : Mat := !![9 / 10, (44 + Real.sqrt 1207) / 90;
    (44 - Real.sqrt 1207) / 90, 1 / 10]
  if e then P.transpose else P

private theorem aSource_legal (e : Bool) : LegalSource (aSource e) := by
  have hs : 0 < Real.sqrt (40657 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs' : Real.sqrt (40657 : ℝ) < 372 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have he := Real.sq_sqrt (show (0 : ℝ) ≤ 40657 by norm_num)
  apply (legal_source_iff (aSource e)).mpr
  cases e <;> refine ⟨?_, ?_, ?_⟩
  all_goals first
    | (intro i j; fin_cases i <;> fin_cases j <;> norm_num [aSource] <;> nlinarith)
    | (norm_num [aSource, Matrix.det_fin_two]; nlinarith)
    | norm_num [aSource, Matrix.trace, Fin.sum_univ_two]

private theorem bSource_legal (e : Bool) : LegalSource (bSource e) := by
  have hs : 0 < Real.sqrt (1207 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs' : Real.sqrt (1207 : ℝ) < 44 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have he := Real.sq_sqrt (show (0 : ℝ) ≤ 1207 by norm_num)
  apply (legal_source_iff (bSource e)).mpr
  cases e <;> refine ⟨?_, ?_, ?_⟩
  all_goals first
    | (intro i j; fin_cases i <;> fin_cases j <;> norm_num [bSource] <;> nlinarith)
    | (norm_num [bSource, Matrix.det_fin_two]; nlinarith)
    | norm_num [bSource, Matrix.trace, Fin.sum_univ_two]

private theorem aSource_distinct : aSource false ≠ aSource true := by
  intro h
  have he := congrArg (fun P : Mat => P 0 1) h
  norm_num [aSource] at he
  have hs : 0 < Real.sqrt (40657 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  linarith

private theorem bSource_distinct : bSource false ≠ bSource true := by
  intro h
  have he := congrArg (fun P : Mat => P 0 1) h
  norm_num [bSource] at he
  have hs : 0 < Real.sqrt (1207 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  linarith

private def cCoeff : Coeff 3 := ![-48, 148 / 5, -6, 2 / 5]
private def aCoeff : Coeff 3 := ![-1344 / 25, 3424 / 125, -576 / 125, 32 / 125]
private def bCoeff : Coeff 3 := ![-252 / 5, 141 / 5, -51 / 10, 3 / 10]

private theorem cCoeff_ne : cCoeff ≠ 0 := by intro h; have := congrFun h 3; norm_num [cCoeff] at this
private theorem aCoeff_ne : aCoeff ≠ 0 := by intro h; have := congrFun h 3; norm_num [aCoeff] at this
private theorem bCoeff_ne : bCoeff ≠ 0 := by intro h; have := congrFun h 3; norm_num [bCoeff] at this

private theorem entire_gains (t : ℝ) :
    (gain 3 cCoeff).eval t = (2 / 5 : ℝ) * (t - 4) * (t - 5) * (t - 6) ∧
    (gain 3 aCoeff).eval t = (32 / 125 : ℝ) * (t - 5) * (t - 6) * (t - 7) ∧
    (gain 3 bCoeff).eval t = (3 / 10 : ℝ) * (t - 4) * (t - 6) * (t - 7) := by
  simp [gain, Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_four, cCoeff, aCoeff, bCoeff]
  constructor
  · ring
  constructor <;> ring

/-- A five-letter suffix chooses one of the 32 leaves below JJ. -/
def terminalWord (u : List Bool) : List Bool := [true, true] ++ u

/-- All sources, entire gains and drifts are fixed simultaneously by this map. -/
def world (u : List Bool) (e : Bool) : World 3 :=
  if u.getD 0 false then
    ⟨qSource (acquisition (terminalWord u)) e,
      qSource_legal _ e, cCoeff, cCoeff_ne, 48⟩
  else if u.getD 1 false then
    ⟨bSource e, bSource_legal e, bCoeff, bCoeff_ne, 252 / 5⟩
  else ⟨aSource e, aSource_legal e, aCoeff, aCoeff_ne, 1344 / 25⟩

private theorem world_distinct (u : List Bool) : world u false ≠ world u true := by
  intro h
  have hs := congrArg World.source h
  unfold world at hs
  split_ifs at hs
  · exact qSource_distinct _ hs
  · exact bSource_distinct hs
  · exact aSource_distinct hs

/-- The single common response attached to each suffix-prefix below JJ. -/
def response (v : List Bool) : ℝ :=
  if v.length = 0 then 192 / 5
  else if v.getD 0 false then
    if v.length = 1 then 228 / 5
    else if v.length < 5 then 48
    else 48 + (12 / 5 : ℝ) * Matrix.trace
      (acquisition (terminalWord v) * qSource (acquisition (terminalWord v)) false)
  else if v.length = 1 then 1163 / 25
  else if v.getD 1 false then
    if v.length = 2 then 252 / 5
    else if v.length = 3 then (if v.getD 2 false then 7657 / 150 else 3833 / 75)
    else 252 / 5
  else if v.length = 2 then 25207 / 500 else 1344 / 25

private def fullResponse (v : List Bool) : ℝ :=
  if v.length = 0 then 0 else if v.length = 1 then 24 else response (v.drop 2)

private theorem acquisition_zero : acquisition [] = 1 := by
  simp [acquisition, Raw, D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word]

private theorem acquisition_j : acquisition [true] = action true := by
  simpa using acquisition_pure true 1

private theorem acquisition_jj : acquisition [true, true] = 1 := by
  change acquisition ([true] ++ [true]) = 1
  rw [acquisition_append, acquisition_j, action_j_shape]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

private theorem acquisition_third (E : Bool) : acquisition [true, true, E] = action E := by
  change acquisition ([true, true] ++ [E]) = action E
  rw [acquisition_append, acquisition_jj, mul_one]

private theorem acquisition_fourth (E F : Bool) :
    acquisition [true, true, E, F] = action F * action E := by
  change acquisition ([true, true, E] ++ [F]) = _
  rw [acquisition_append, acquisition_third]

private theorem acquisition_fifth (E F G : Bool) :
    acquisition [true, true, E, F, G] = action G * (action F * action E) := by
  change acquisition ([true, true, E, F] ++ [G]) = _
  rw [acquisition_append, acquisition_fourth]

private theorem a_traces (e : Bool) :
    Matrix.trace (action true * aSource e) = 31 / 32 ∧
    Matrix.trace (action false * aSource e) = 905 / 768 ∧
    Matrix.trace (action false * action false * aSource e) = 1673 / 768 := by
  cases e <;> repeat' constructor
  all_goals norm_num [aSource, action_j_shape, action_m_shape,
    Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

private theorem b_traces (e : Bool) :
    Matrix.trace (action true * bSource e) = 44 / 45 ∧
    Matrix.trace (action false * bSource e) = 97 / 90 ∧
    Matrix.trace (action true * (action true * action false) * bSource e) = 97 / 90 ∧
    Matrix.trace (action false * (action true * action false) * bSource e) = 53 / 45 := by
  cases e <;> repeat' constructor
  all_goals norm_num [bSource, action_j_shape, action_m_shape,
    Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

private theorem gain_samples (i : Fin 8) :
    (gain 3 cCoeff).eval (i.val : ℝ) =
      (![-48, -24, -48 / 5, -12 / 5, 0, 0, 0, 12 / 5] : Fin 8 → ℝ) i ∧
    (gain 3 aCoeff).eval (i.val : ℝ) =
      (![-1344 / 25, -768 / 25, -384 / 25, -768 / 125, -192 / 125, 0, 0, 0] :
        Fin 8 → ℝ) i ∧
    (gain 3 bCoeff).eval (i.val : ℝ) =
      (![-252 / 5, -27, -12, -18 / 5, 0, 3 / 5, 0, 0] : Fin 8 → ℝ) i := by
  rw [(entire_gains _).1, (entire_gains _).2.1, (entire_gains _).2.2]
  fin_cases i <;> norm_num

private theorem world_reads (u : List Bool) (hu : u.length = 5) (e : Bool) (i : Fin 8) :
    readAt (world u e) (terminalWord u) i.val = fullResponse ((terminalWord u).take i.val) := by
  obtain ⟨a, t, rfl, ht⟩ := List.length_eq_succ_iff.mp hu
  obtain ⟨b, c, d, f, rfl⟩ := List.length_eq_four.mp ht
  have hcs := (gain_samples i).1
  have has := (gain_samples i).2.1
  have hbs := (gain_samples i).2.2
  cases a
  · cases b
    · have hj := (a_traces e).1
      have hm := (a_traces e).2.1
      have hmm := (a_traces e).2.2
      have htr := (aSource_legal e).2.2
      fin_cases i <;>
        norm_num [readAt, world, terminalWord, fullResponse, response,
          acquisition_zero, acquisition_j, acquisition_jj, acquisition_third,
          acquisition_fourth, hj, hm, hmm, htr, hcs, has, hbs,
          hcs, has, hbs]
    · have hj := (b_traces e).1
      have hm := (b_traces e).2.1
      have hjm := (b_traces e).2.2.1
      have hmm := (b_traces e).2.2.2
      have htr := (bSource_legal e).2.2
      cases c <;> fin_cases i <;>
        norm_num [readAt, world, terminalWord, fullResponse, response,
          acquisition_zero, acquisition_j, acquisition_jj, acquisition_third,
          acquisition_fourth, acquisition_fifth, hj, hm, hjm, hmm, htr,
          hcs, has, hbs]
  · have hj := qSource_signature (acquisition (terminalWord [true, b, c, d, f])) e
    have htr := (qSource_legal (acquisition (terminalWord [true, b, c, d, f])) e).2.2
    have hlast : Matrix.trace (acquisition (terminalWord [true, b, c, d, f]) *
        qSource (acquisition (terminalWord [true, b, c, d, f])) e) =
        Matrix.trace (acquisition (terminalWord [true, b, c, d, f]) *
          qSource (acquisition (terminalWord [true, b, c, d, f])) false) := by
      cases e
      · rfl
      · exact (qSource_collision _).symm
    fin_cases i <;>
      norm_num [readAt, world, terminalWord, fullResponse, response,
        acquisition_zero, acquisition_j, acquisition_jj, acquisition_third,
        hj, htr, hlast, hcs, has, hbs]

private def suffixes : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (suffixes n).image (false :: ·) ∪ (suffixes n).image (true :: ·)

private theorem mem_suffixes (n : ℕ) (u : List Bool) : u ∈ suffixes n ↔ u.length = n := by
  induction n generalizing u with
  | zero => simp [suffixes]
  | succ n ih =>
    cases u with
    | nil => simp [suffixes]
    | cons E u => cases E <;> simp [suffixes, ih]

private def support (v : List Bool) (n : ℕ) : Finset (World 3) :=
  (suffixes n).biUnion (fun u => {world (v ++ u) false, world (v ++ u) true})

private theorem support_guard (v : List Bool) (n : ℕ) :
    (support v n : Set (World 3)).Nontrivial := by
  let u := List.replicate n false
  have hu : u ∈ suffixes n := (mem_suffixes n u).mpr (List.length_replicate ..)
  refine ⟨world (v ++ u) false, ?_, world (v ++ u) true, ?_, world_distinct _⟩
  all_goals exact Finset.mem_biUnion.mpr ⟨u, hu, by simp⟩

private theorem support_child (v : List Bool) (n : ℕ) (E : Bool) :
    support (v ++ [E]) n ⊆ support v (n + 1) := by
  intro W hW
  obtain ⟨u, hu, hWu⟩ := Finset.mem_biUnion.mp hW
  have hu' : E :: u ∈ suffixes (n + 1) :=
    (mem_suffixes _ _).mpr (by simp [(mem_suffixes _ _).mp hu])
  apply Finset.mem_biUnion.mpr
  refine ⟨E :: u, hu', ?_⟩
  simpa [List.append_assoc] using hWu

private theorem read_prefix (W : World 3) (v u : List Bool) (i : ℕ) (hi : i ≤ v.length) :
    readAt W (v ++ u) i = readAt W v i := by
  simp [readAt, List.take_append_of_le_length hi]

private theorem support_response (v : List Bool) (n : ℕ) (E : Bool)
    (hlen : v.length + n + 1 = 5) (W : World 3)
    (hW : W ∈ support (v ++ [E]) n) :
    readAt W (terminalWord v ++ [E]) ((terminalWord v).length + 1) =
      response (v ++ [E]) := by
  obtain ⟨u, hu, hWu⟩ := Finset.mem_biUnion.mp hW
  have hul := (mem_suffixes _ _).mp hu
  have hfull : ((v ++ [E]) ++ u).length = 5 := by simp; omega
  have hi : (terminalWord (v ++ [E])).length < 8 := by
    simp [terminalWord]; omega
  have hvlen : (terminalWord (v ++ [E])).length = (terminalWord v).length + 1 := by
    simp [terminalWord]
  have hword : terminalWord ((v ++ [E]) ++ u) = terminalWord (v ++ [E]) ++ u := by
    simp [terminalWord, List.append_assoc]
  have hp (e : Bool) :
      readAt (world ((v ++ [E]) ++ u) e) (terminalWord v ++ [E])
        ((terminalWord v).length + 1) = response (v ++ [E]) := by
    have hh := world_reads _ hfull e ⟨(terminalWord (v ++ [E])).length, hi⟩
    simp only [hword, read_prefix _ _ _ _ (le_refl _), List.take_append,
      List.take_length, Nat.sub_self, List.take_zero, List.append_nil] at hh
    simpa [fullResponse, terminalWord, List.append_assoc] using hh
  simp only [Finset.mem_insert, Finset.mem_singleton] at hWu
  rcases hWu with rfl | rfl
  · exact hp false
  · exact hp true

private theorem support_loses (n : ℕ) (v : List Bool) (hlen : v.length + n = 5) :
    Loses n (support v n : Set (World 3)) (terminalWord v) := by
  induction n generalizing v with
  | zero => exact support_guard v 0
  | succ n ih =>
    refine ⟨support_guard v (n + 1), ?_⟩
    intro E
    refine ⟨response (v ++ [E]), ?_⟩
    apply loses_mono (ih (v ++ [E]) (by simp; omega))
    intro W hW
    exact ⟨support_child v n E hW, support_response v n E (by omega) W hW⟩

/-- The original initial-inclusive history. -/
def jjHistory : History [true, true] := ![0, 24, 192 / 5]

/-- Cross-leaf repetitions are retained as labelled slots, then deduplicated
only when taking the actual finite family of complete worlds. -/
def family : Finset (World 3) := support [] 5

private theorem family_compatible : (family : Set (World 3)) ⊆ wholeSet [true, true] jjHistory := by
  intro W hW
  obtain ⟨u, hu, hWu⟩ := Finset.mem_biUnion.mp hW
  have hul := (mem_suffixes _ _).mp hu
  have hp (e : Bool) : world u e ∈ wholeSet [true, true] jjHistory := by
    change readings (world u e) [true, true] = jjHistory
    ext i
    have hi : i.val < 8 := by have := i.isLt; simp at this; omega
    have hh := world_reads u hul e ⟨i.val, hi⟩
    have hread := read_prefix (world u e) [true, true] u i.val (by
      have := i.isLt; simp at this; simp; omega)
    change readAt (world u e) [true, true] i.val = _
    rw [← hread]
    change readAt (world u e) (terminalWord u) i.val = _
    rw [hh]
    fin_cases i <;> norm_num [terminalWord, fullResponse, response, jjHistory]
  simp only [List.nil_append, Finset.mem_insert, Finset.mem_singleton] at hWu
  rcases hWu with rfl | rfl
  · exact hp false
  · exact hp true

/-- The exact source-domain bridge and both actual five-level failures. -/
theorem jj_five_failure :
    (∀ (P : Mat) (p : Polynomial ℝ) (δ : ℝ),
      (∃ W : World 3, W.source = P ∧ gain 3 W.coeff = p ∧ W.drift = δ) ↔
        (∀ i j, 0 < P i j) ∧ P.det = 0 ∧ Matrix.trace P = 1 ∧
          p ≠ 0 ∧ p.natDegree ≤ 3) ∧
    (∀ u : List Bool, u.length = 5 → world u false ≠ world u true ∧
      ∀ (e : Bool) (i : Fin 8),
        readAt (world u e) (terminalWord u) i.val =
          fullResponse ((terminalWord u).take i.val)) ∧
    (family : Set (World 3)) ⊆ wholeSet [true, true] jjHistory ∧
    MixedTripleExclusion.Losing 5 family [true, true] ∧
    Loses 5 (wholeSet [true, true] jjHistory : Set (World 3)) [true, true] := by
  have hl : Loses 5 (family : Set (World 3)) [true, true] := by
    simpa [family, terminalWord] using support_loses 5 [] (by simp)
  exact ⟨whole_domain 3, fun u hu => ⟨world_distinct u, world_reads u hu⟩,
    family_compatible, (finite_losing_iff ..).mp hl, loses_mono hl family_compatible⟩

/-- An unrestricted deterministic complete-target recovery policy on the actual
whole fiber, allowed to stop at any earlier node, with five further readings. -/
def five_read_recovery_claim : Prop :=
  ∃ P : Policy 3, ∀ W ∈ wholeSet [true, true] jjHistory, Identifies P 5 [true, true] W

theorem result : ¬ five_read_recovery_claim := by
  rintro ⟨P, hP⟩
  exact loses_excludes_policy _ _ jjHistory (fun _ h => h) jj_five_failure.2.2.2.2 P hP

end D5.S3.Observer.CubicGain.JJFiveFailure
