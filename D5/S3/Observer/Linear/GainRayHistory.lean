/- GID: D5/S3/Observer/Linear/GainRayHistory
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayHistory
   mirror-E: none(waiver:whole-world-and-literal-real-history)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.OfFn, mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank, mathlib/module/Mathlib.LinearAlgebra.Lagrange]
   utility: none
   digest: Whole polynomial worlds support literal initial-inclusive acquisition and arbitrary deterministic actual-history decisions. -/

import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Lagrange
import D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace D5.S3.Observer.Linear.GainRay

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ
abbrev Coeff (d : ℕ) := Fin (d + 1) → ℝ

def LegalSource (P : Mat) : Prop :=
  (∀ i j, 0 < P i j) ∧ P.rank = 1 ∧ Matrix.trace P = 1

def gain (d : ℕ) (β : Coeff d) : Polynomial ℝ := Polynomial.ofFn (d + 1) β

/-- No condition is imposed on an individual coefficient or sample. -/
structure World (d : ℕ) where
  source : Mat
  legal : LegalSource source
  coeff : Coeff d
  nonzero : coeff ≠ 0
  drift : ℝ

/-- The full positive chart of normalized sources. -/
def sourceChart (x r : ℝ) : Mat := (1 + x * r)⁻¹ • !![1, r; x, x * r]

private theorem chart_rank (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    (sourceChart x r).rank = 1 := by
  have hden : 0 < 1 + x * r := by positivity
  have houter : sourceChart x r = Matrix.vecMulVec
      ![(1 + x * r)⁻¹, x / (1 + x * r)] ![1, r] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sourceChart, Matrix.vecMulVec, div_eq_mul_inv] <;> ring
  have hle : (sourceChart x r).rank ≤ 1 := by
    rw [houter]
    exact Matrix.rank_vecMulVec_le _ _
  have hpos : 0 < (sourceChart x r).rank := by
    change 0 < Module.finrank ℝ (LinearMap.range (sourceChart x r).mulVecLin)
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨(sourceChart x r).mulVec ![1, 0], ⟨![1, 0], rfl⟩⟩, ?_⟩
    intro h
    have he := congrArg (fun v : LinearMap.range (sourceChart x r).mulVecLin => v.1 0) h
    have hn : (1 + x * r)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hden)
    exact hn (by simpa [sourceChart, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using he)
  omega

theorem source_chart_legal (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    LegalSource (sourceChart x r) := by
  have hd : 0 < 1 + x * r := by positivity
  refine ⟨?_, chart_rank x r hx hr, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [sourceChart] <;> positivity
  · simp [sourceChart, Matrix.trace, Fin.sum_univ_two]
    field_simp

/-- Every original legal source occurs, with its original matrix unchanged. -/
theorem source_chart_exact (P : Mat) (hP : LegalSource P) :
    ∃ x r : ℝ, 0 < x ∧ 0 < r ∧ P = sourceChart x r ∧
      x = P 1 0 / P 0 0 ∧ r = P 0 1 / P 0 0 := by
  have ha := hP.1 0 0
  have hb := hP.1 0 1
  have hc := hP.1 1 0
  have hdet : P.det = 0 := by
    by_contra hn
    have he := Matrix.rank_of_det_ne_zero hn
    rw [hP.2.1] at he
    norm_num at he
  have ht : P 0 0 + P 1 1 = 1 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using hP.2.2
  have hd : P 0 0 * P 1 1 = P 0 1 * P 1 0 := by
    simpa [Matrix.det_fin_two, sub_eq_zero] using hdet
  refine ⟨P 1 0 / P 0 0, P 0 1 / P 0 0, div_pos hc ha, div_pos hb ha, ?_, rfl, rfl⟩
  have hz : P 0 0 ≠ 0 := ne_of_gt ha
  have hinv : (1 + (P 1 0 / P 0 0) * (P 0 1 / P 0 0))⁻¹ = P 0 0 := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sourceChart, hinv]
  · field_simp
  · field_simp
  · field_simp
    nlinarith

/-- Nodes are explicit; original acquisition uses their consecutive natural casts. -/
def evaluation (d n : ℕ) (t : Fin n → ℝ) : Matrix (Fin n) (Fin (d + 1)) ℝ :=
  fun i k => t i ^ (k : ℕ)

def evaluate (d n : ℕ) (t : Fin n → ℝ) : Coeff d →ₗ[ℝ] (Fin n → ℝ) :=
  Matrix.mulVecLin (evaluation d n t)

/-- The evaluation matrix acts on exactly the same ordinary whole polynomial. -/
theorem evaluation_polynomial (d n : ℕ) (t : Fin n → ℝ) (β : Coeff d)
    (i : Fin n) : evaluate d n t β i = (gain d β).eval (t i) := by
  simp [evaluate, evaluation, Matrix.mulVecLin, Matrix.mulVec, dotProduct, gain,
    Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum, mul_comm]

/-- All original clock embeddings are injective, including the zero clock. -/
def clocks (n : ℕ) (i : Fin n) : ℝ := (i.val : ℝ)

/-- Enough distinct clocks determine the whole ordinary coefficient vector. -/
theorem evaluation_injective (d n : ℕ) (t : Fin n → ℝ)
    (ht : Function.Injective t) (hn : d + 1 ≤ n) :
    Function.Injective (evaluate d n t) := by
  intro β γ he
  apply Polynomial.injective_ofFn (d + 1)
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (Finset.univ : Finset (Fin n))
    (fun _ _ _ _ h => ht h)
  · simpa using lt_of_lt_of_le (Polynomial.ofFn_degree_lt β) (by exact_mod_cast hn)
  · simpa using lt_of_lt_of_le (Polynomial.ofFn_degree_lt γ) (by exact_mod_cast hn)
  · intro i _
    change (gain d β).eval (t i) = (gain d γ).eval (t i)
    rw [← evaluation_polynomial, ← evaluation_polynomial]
    exact congrFun he i

/-- At most d+1 distinct prescribed values are attained without a sign promise. -/
theorem evaluation_surjective (d n : ℕ) (t : Fin n → ℝ)
    (ht : Function.Injective t) (hn : n ≤ d + 1) :
    Function.Surjective (evaluate d n t) := by
  intro y
  classical
  by_cases hz : n = 0
  · subst n
    exact ⟨0, Subsingleton.elim _ _⟩
  let p := Lagrange.interpolate (Finset.univ : Finset (Fin n)) t y
  have hp : p.degree < (n : ℕ) := by
    simpa [p] using Lagrange.degree_interpolate_lt (s := Finset.univ) (v := t) y
      (fun _ _ _ _ h => ht h)
  have hdeg : p.natDegree < d + 1 := by
    by_cases h0 : p = 0
    · simp [h0]
    · exact ((Polynomial.natDegree_lt_iff_degree_lt h0).mpr hp).trans_le hn
  refine ⟨Polynomial.toFn (d + 1) p, ?_⟩
  ext i
  rw [evaluation_polynomial]
  change (Polynomial.ofFn (d + 1) (Polynomial.toFn (d + 1) p)).eval (t i) = _
  rw [Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hdeg]
  exact Lagrange.eval_interpolate_at_node _ (fun _ _ _ _ h => ht h) (Finset.mem_univ i)

/-- The coefficient-and-drift extension of the pure-J history map is onto. -/
theorem pureJ_history_surjective (d n : ℕ) (hn : n ≤ d + 1) :
    Function.Surjective (fun b : Coeff d × ℝ =>
      fun i : Fin n => (gain d b.1).eval (clocks n i) + b.2) := by
  intro y
  have ht : Function.Injective (clocks n) := by
    intro i j h
    apply Fin.ext
    dsimp [clocks] at h
    exact_mod_cast h
  obtain ⟨β, hβ⟩ := evaluation_surjective d n (clocks n) ht hn y
  refine ⟨(β, 0), ?_⟩
  ext i
  simpa [evaluation_polynomial] using congrFun hβ i

abbrev Raw := D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word

def action (a : Bool) : Mat :=
  (D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic a).map (Int.castRingHom ℝ)

/-- False is M, true is J, in chronological list order. -/
def acquisition (w : List Bool) : Mat := (Raw w).map (Int.castRingHom ℝ)

/-- Appending one atom applies that one matrix on the left. -/
theorem acquisition_append (w : List Bool) (a : Bool) :
    acquisition (w ++ [a]) = action a * acquisition w := by
  have h := (D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.raw_word_signed_bound w).2.2.2.1 [a]
  simp only [acquisition, h, Matrix.map_mul]
  congr 1
  simp [Raw, D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word, action]

/-- Repetition is the literal native trajectory of matrix powers. -/
theorem acquisition_pure (a : Bool) (n : ℕ) :
    acquisition (List.replicate n a) = action a ^ n := by
  induction n with
  | zero => simp [acquisition, Raw,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word]
  | succ n ih => rw [List.replicate_succ', acquisition_append, ih, pow_succ']

/-- A read at its original natural clock; the initial read uses the identity. -/
def readAt {d : ℕ} (W : World d) (w : List Bool) (i : ℕ) : ℝ :=
  (gain d W.coeff).eval (i : ℝ) * Matrix.trace (acquisition (w.take i) * W.source) + W.drift

abbrev History (w : List Bool) := Fin (w.length + 1) → ℝ
abbrev Readout (d : ℕ) (w : List Bool) := Matrix (Fin (d + 1)) (Fin (w.length + 1)) ℝ

def readings {d : ℕ} (W : World d) (w : List Bool) : History w :=
  fun i => readAt W w i.val

/-- Zero is allowed for collinearity, but never for gain-ray success. -/
def Collinear {d : ℕ} (β v : Coeff d) : Prop := ∃ s : ℝ, v = s • β

def Succeeds {d : ℕ} (W : World d) (w : List Bool) (C : Readout d w) : Prop :=
  ∃ s : ℝ, s ≠ 0 ∧ C.mulVec (readings W w) = s • W.coeff

/-- Each palette is fixed before observations; only its selection is adaptive.
The set may be empty, finite or countably infinite. -/
structure Protocol (d : ℕ) where
  palette : ∀ w : List Bool, Set (Readout d w)
  countable : ∀ w, (palette w).Countable
  decide : ∀ w : List Bool, History w → Bool ⊕ {C : Readout d w // C ∈ palette w}

/-- Reaching a word entails every preceding actual decision and its immediate read.
There is no initial action and no action without its read. -/
inductive Reaches {d : ℕ} (P : Protocol d) (W : World d) : List Bool → Prop
  | initial : Reaches P W []
  | step {w : List Bool} {a : Bool} : Reaches P W w →
      P.decide w (readings W w) = Sum.inl a → Reaches P W (w ++ [a])

def Terminates {d : ℕ} (P : Protocol d) (W : World d) (w : List Bool)
    (C : {C : Readout d w // C ∈ P.palette w}) : Prop :=
  Reaches P W w ∧ P.decide w (readings W w) = Sum.inr C

/-- A total-read bound counts the initial read and every executed atom's read. -/
def UniformlySuccessful {d : ℕ} (P : Protocol d) (N : ℕ) : Prop :=
  ∀ W : World d, ∃ w C, Terminates P W w C ∧ w.length + 1 ≤ N ∧ Succeeds W w C.1

private theorem readings_before_append {d : ℕ} (W W' : World d) (w : List Bool) (a : Bool)
    (h : readings W (w ++ [a]) = readings W' (w ++ [a])) :
    readings W w = readings W' w := by
  ext i
  have hi : i.val ≤ w.length := by omega
  have he := congrFun h ⟨i.val, by simp <;> omega⟩
  simpa [readings, readAt, List.take_append_of_le_length hi] using he

/-- The identical values are actual for both worlds, through all prior decisions. -/
theorem identical_prefix_transfer {d : ℕ} (P : Protocol d) (W W' : World d)
    (w : List Bool) (hr : Reaches P W w)
    (he : readings W w = readings W' w) :
    Reaches P W' w ∧ P.decide w (readings W w) = P.decide w (readings W' w) := by
  have replay : ∀ v, Reaches P W v → readings W v = readings W' v → Reaches P W' v := by
    intro v hv
    induction hv with
    | initial => intro _; exact .initial
    | @step v a hv hd ih =>
        intro h
        have hpre := readings_before_append W W' v a h
        exact .step (ih hpre) (by rw [← hpre]; exact hd)
  exact ⟨replay w hr he, congrArg (P.decide w) he⟩

/-- The transferred next M is forced even if later observations and decisions differ. -/
theorem identical_prefix_firstM {d : ℕ} (P : Protocol d) (W W' : World d)
    (n : ℕ) (hr : Reaches P W (List.replicate n true))
    (he : readings W (List.replicate n true) = readings W' (List.replicate n true))
    (hd : P.decide (List.replicate n true) (readings W (List.replicate n true)) =
      Sum.inl false) :
    Reaches P W' (List.replicate n true ++ [false]) := by
  obtain ⟨hr', hdecision⟩ := identical_prefix_transfer P W W' _ hr he
  exact .step hr' (hdecision.symm.trans hd)

theorem reaches_take {d : ℕ} (P : Protocol d) (W : World d)
    {w : List Bool} (hr : Reaches P W w) (k : ℕ) (hk : k ≤ w.length) :
    Reaches P W (w.take k) := by
  induction hr with
  | initial => simpa using (Reaches.initial (P := P) (W := W))
  | @step w a hw hd ih =>
      by_cases h : k ≤ w.length
      · rw [List.take_append_of_le_length h]
        exact ih h
      · have he : k = (w ++ [a]).length := by simp at hk ⊢; omega
        rw [he, List.take_length]
        exact .step hw hd

private theorem reached_unique_length {d : ℕ} (P : Protocol d) (W : World d)
    {w v : List Bool} (hw : Reaches P W w) (hv : Reaches P W v)
    (hlen : w.length = v.length) : w = v := by
  induction hw generalizing v with
  | initial =>
      have he : v.length = 0 := hlen.symm
      exact (List.length_eq_zero_iff.mp he).symm
  | @step w a hw hd ih =>
      cases hv with
      | initial => simp at hlen
      | @step v b hv he =>
          have hp : w = v := ih hv (by simpa using hlen)
          subst v
          have hab : a = b := Sum.inl.inj (hd.symm.trans he)
          rw [hab]

/-- Every reached prefix belongs to the very same actual terminal word. -/
theorem terminal_extends_reached {d : ℕ} (P : Protocol d) (W : World d)
    (p w : List Bool) (C : {C : Readout d w // C ∈ P.palette w})
    (hp : Reaches P W p) (ht : Terminates P W w C) : p <+: w := by
  by_cases hlen : p.length ≤ w.length
  · have he : p = w.take p.length := reached_unique_length P W hp
      (reaches_take P W ht.1 p.length hlen) (by simp [hlen])
    rw [he]
    exact List.take_prefix _ _
  · have hlt : w.length < p.length := by omega
    have hq := reaches_take P W hp (w.length + 1) hlt
    have hqlen : (p.take (w.length + 1)).length = w.length + 1 := by simp; omega
    generalize hqeq : p.take (w.length + 1) = q at hq hqlen
    cases hq with
    | initial => simp at hqlen
    | @step v a hv hd =>
        have hvlen : v.length = w.length := by simp at hqlen; omega
        have he : v = w := reached_unique_length P W hv ht.1 hvlen
        subst v
        rw [ht.2] at hd
        contradiction

/-- Chart coordinates impose only positivity and a nonzero whole coefficient vector. -/
def chartWorld (d : ℕ) (x r : ℝ) (hx : 0 < x) (hr : 0 < r)
    (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ) : World d :=
  ⟨sourceChart x r, source_chart_legal x r hx hr, β, hβ, δ⟩

/-- The full chart's pure-J factors at the original consecutive clocks. -/
theorem source_chart_pureJ (x r : ℝ) (hx : 0 < x) (hr : 0 < r) (n : ℕ) :
    Matrix.trace (acquisition (List.replicate n true) * sourceChart x r) =
      if n % 2 = 0 then 1 else (x + r) / (1 + x * r) := by
  have hj : action true ^ 2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [action, D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
        pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  rw [acquisition_pure, pow_eq_pow_mod n hj]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp only [h, pow_zero, one_mul, ite_true]
    exact (source_chart_legal x r hx hr).2.2
  · have hn : ¬n % 2 = 0 := by omega
    simp only [h, pow_one, if_neg (by omega : ¬(1 : ℕ) = 0)]
    simp [action, D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      sourceChart, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]
    <;> ring

def identicalRow (θ : ℝ) : Mat := !![1 - θ, θ; 1 - θ, θ]

private theorem identical_row_chart (θ : ℝ) (hθ' : θ < 1) :
    identicalRow θ = sourceChart 1 (θ / (1 - θ)) := by
  have ht : 1 - θ ≠ 0 := by linarith
  have hi : (1 + 1 * (θ / (1 - θ)))⁻¹ = 1 - θ := by
    apply inv_eq_of_mul_eq_one_right
    field_simp
    ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [identicalRow, sourceChart, hi] <;> field_simp <;> ring

/-- Every parameter in the open unit interval gives a legal original source. -/
theorem identical_row_legal (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1) :
    LegalSource (identicalRow θ) := by
  rw [identical_row_chart θ hθ']
  exact source_chart_legal 1 _ zero_lt_one (div_pos hθ (by linarith))

def rowWorld (d : ℕ) (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1)
    (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ) : World d :=
  ⟨identicalRow θ, identical_row_legal θ hθ hθ', β, hβ, δ⟩

private theorem identical_row_J (θ : ℝ) : action true * identicalRow θ = identicalRow θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [action, identicalRow,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      Matrix.mul_apply, Fin.sum_univ_two]

private theorem identical_row_pureJ (θ : ℝ) (n : ℕ) :
    acquisition (List.replicate n true) * identicalRow θ = identicalRow θ := by
  induction n with
  | zero => simp [acquisition, Raw,
      D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word]
  | succ n ih =>
      rw [List.replicate_succ', acquisition_append, mul_assoc, ih, identical_row_J]

/-- Every pure-J prefix, including no actions, has its original clock polynomial reads. -/
theorem identical_row_readings (d : ℕ) (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1)
    (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ) (n : ℕ) :
    readings (rowWorld d θ hθ hθ' β hβ δ) (List.replicate n true) =
      fun i : Fin ((List.replicate n true).length + 1) =>
        (gain d β).eval (i.val : ℝ) + δ := by
  ext i
  change (gain d β).eval (i.val : ℝ) *
    Matrix.trace (acquisition ((List.replicate n true).take i.val) * identicalRow θ) + δ = _
  rw [List.take_replicate, identical_row_pureJ]
  simp [identicalRow, Matrix.trace, Fin.sum_univ_two]

#print axioms terminal_extends_reached
#print axioms identical_prefix_firstM
end D5.S3.Observer.Linear.GainRay
