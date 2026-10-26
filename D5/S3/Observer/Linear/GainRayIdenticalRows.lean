/- GID: D5/S3/Observer/Linear/GainRayIdenticalRows
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayIdenticalRows
   mirror-E: none(waiver:whole-identical-row-annihilation)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Center]
   utility: none
   digest: Exact native identical-row suffix support and annihilation. -/

import D5.S3.Observer.Linear.GainRayHistory
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The full identical-row family retains every original acquisition clock. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace D5.S3.Observer.Linear.GainRay

/-- The two coordinates of the actual cumulative matrix acting on the all-one column. -/
def rowCoordinates (w : List Bool) : Fin 2 → ℝ := (acquisition w).mulVec ![1, 1]

private theorem row_coordinates_nil : rowCoordinates [] = ![1, 1] := by
  simp [rowCoordinates, acquisition, Raw,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word]

private theorem row_coordinates_append (w : List Bool) (a : Bool) :
    rowCoordinates (w ++ [a]) =
      if a then ![rowCoordinates w 1, rowCoordinates w 0]
      else ![rowCoordinates w 1, rowCoordinates w 0 + rowCoordinates w 1] := by
  rw [rowCoordinates, acquisition_append, ← Matrix.mulVec_mulVec]
  cases a <;> ext i <;> fin_cases i <;>
    simp [action, D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, rowCoordinates]

private theorem row_coordinates_invariant (w : List Bool) :
    0 < rowCoordinates w 0 ∧ 0 < rowCoordinates w 1 ∧
      (rowCoordinates w 0 = rowCoordinates w 1 ↔ false ∉ w) ∧
      (false ∉ w → rowCoordinates w = ![1, 1]) := by
  induction w using List.reverseRecOn with
  | nil => simp [row_coordinates_nil]
  | append_singleton w a ih =>
      rw [row_coordinates_append]
      cases a
      · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.cons_val_zero,
          Matrix.cons_val_one, List.mem_append, List.mem_singleton,
          or_true, not_true_eq_false, iff_false, false_implies, and_true]
        exact ⟨ih.2.1, add_pos ih.1 ih.2.1, by linarith [ih.1]⟩
      · simp only [↓reduceIte, Matrix.cons_val_zero,
          Matrix.cons_val_one, List.mem_append, List.mem_singleton,
          Bool.false_eq_true, or_false]
        refine ⟨ih.2.1, ih.1, eq_comm.trans ih.2.2.1, ?_⟩
        intro h
        rw [ih.2.2.2 h]
        simp

/-- Constant and theta coefficients, indexed by every initial-inclusive native clock. -/
def rowBase (w : List Bool) : History w := fun i => rowCoordinates (w.take i.val) 0
def rowSlope (w : List Bool) : History w :=
  fun i => rowCoordinates (w.take i.val) 1 - rowCoordinates (w.take i.val) 0

/-- The affine trace identity uses the literal cumulative native matrix. -/
theorem identical_row_trace (w : List Bool) (θ : ℝ) :
    Matrix.trace (acquisition w * identicalRow θ) =
      rowCoordinates w 0 + θ * (rowCoordinates w 1 - rowCoordinates w 0) := by
  simp [rowCoordinates, identicalRow, Matrix.trace, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  ring

/-- No later legal continuation can erase the theta coefficient after the first M. -/
theorem identical_row_slope_support (w : List Bool) (i : Fin (w.length + 1)) :
    rowSlope w i ≠ 0 ↔ false ∈ w.take i.val := by
  have h := (row_coordinates_invariant (w.take i.val)).2.2.1
  simp only [rowSlope, ne_eq, sub_eq_zero]
  tauto

private theorem firstM_mem_take (k : ℕ) (tail : List Bool) (i : ℕ) :
    false ∈ (List.replicate k true ++ [false] ++ tail).take i ↔ k < i := by
  rw [List.append_assoc]
  by_cases h : i ≤ k
  · rw [List.take_append_of_le_length (by simpa using h)]
    simp [List.take_replicate, Nat.not_lt.mpr h]
  · have hk : k < i := by omega
    rw [List.take_append, List.take_replicate]
    cases he : i - k with
    | zero => omega
    | succ j => simp [he, hk]

/-- Exact entire suffix: the first M is at clock k+1, and every later read has nonzero slope. -/
theorem identical_row_entire_suffix (k : ℕ) (tail : List Bool)
    (i : Fin ((List.replicate k true ++ [false] ++ tail).length + 1)) :
    rowSlope (List.replicate k true ++ [false] ++ tail) i ≠ 0 ↔ k < i.val := by
  rw [identical_row_slope_support, firstM_mem_take]

private theorem row_base_before (w : List Bool) (i : Fin (w.length + 1))
    (hi : false ∉ w.take i.val) : rowBase w i = 1 := by
  simp [rowBase, (row_coordinates_invariant (w.take i.val)).2.2.2 hi]

/-- The coefficient map at the original consecutive clocks, with an arbitrary factor vector. -/
def rowMap (d : ℕ) (w : List Bool) (C : Readout d w) (f : History w) :
    Coeff d →ₗ[ℝ] Coeff d :=
  (Matrix.mulVecLin C).comp
    ((Matrix.mulVecLin (Matrix.diagonal f)).comp (evaluate d (w.length + 1) (clocks _)))

private theorem row_map_apply (d : ℕ) (w : List Bool) (C : Readout d w)
    (f : History w) (β : Coeff d) :
    rowMap d w C f β = C.mulVec (fun i => f i * (gain d β).eval (i.val : ℝ)) := by
  change C.mulVec ((Matrix.diagonal f).mulVec
    (evaluate d (w.length + 1) (clocks _) β)) = _
  congr 1
  ext i
  rw [Matrix.mulVec_diagonal, evaluation_polynomial]
  rfl

/-- Universal collinearity is tested only on legal identical-row worlds with nonzero whole gain. -/
def RowUniversallyCollinear (d : ℕ) (w : List Bool) (C : Readout d w) : Prop :=
  ∀ (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1) (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ),
    Collinear β (C.mulVec (readings (rowWorld d θ hθ hθ' β hβ δ) w))

theorem row_readings_affine (d : ℕ) (w : List Bool)
    (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1) (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ) :
    readings (rowWorld d θ hθ hθ' β hβ δ) w =
      (fun i => (rowBase w i + θ * rowSlope w i) *
        (gain d β).eval (i.val : ℝ)) + δ • (fun _ => 1) := by
  ext i
  simp [readings, readAt, rowWorld, identical_row_trace, rowBase, rowSlope,
    mul_comm]

private theorem row_collinear_affine (d : ℕ) (w : List Bool) (C : Readout d w)
    (h : RowUniversallyCollinear d w C) (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1)
    (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ) :
    Collinear β (rowMap d w C (rowBase w + θ • rowSlope w) β +
      δ • C.mulVec (fun _ => 1)) := by
  have he := h θ hθ hθ' β hβ δ
  rw [row_readings_affine, Matrix.mulVec_add, Matrix.mulVec_smul] at he
  simpa only [row_map_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using he

private theorem row_drift_zero (d : ℕ) (hd : 1 ≤ d) (w : List Bool)
    (C : Readout d w) (h : RowUniversallyCollinear d w C) :
    C.mulVec (fun _ => 1) = 0 := by
  classical
  ext j
  let q : Fin (d + 1) := if j = 0 then ⟨1, by omega⟩ else 0
  have hq : q ≠ j := by
    dsimp [q]
    split_ifs with hj
    · subst j; exact Fin.ne_of_val_ne (by simp)
    · exact Ne.symm hj
  let β : Coeff d := Pi.single q 1
  have hb : β ≠ 0 := by
    intro he
    have hj := congrFun he q
    simp [β] at hj
  obtain ⟨s, hs⟩ := row_collinear_affine d w C h (1/2) (by norm_num)
    (by norm_num) β hb 0
  obtain ⟨t, ht⟩ := row_collinear_affine d w C h (1/2) (by norm_num)
    (by norm_num) β hb 1
  have hs' := congrFun hs j
  have ht' := congrFun ht j
  simp [β, Ne.symm hq] at hs' ht'
  change C.mulVec (fun _ => 1) j = 0
  linarith

private theorem row_scalar_at (d : ℕ) (w : List Bool) (C : Readout d w)
    (h : RowUniversallyCollinear d w C) (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1) :
    ∃ s : ℝ, rowMap d w C (rowBase w + θ • rowSlope w) = s • LinearMap.id := by
  apply LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
  intro β hli
  by_cases hb : β = 0
  · subst β
    exact (hli.ne_zero 0) (by simp)
  obtain ⟨s, hs⟩ := row_collinear_affine d w C h θ hθ hθ' β hb 0
  simp only [zero_smul, add_zero] at hs
  have hz := hli.eq_zero_of_pair (s := -s) (t := 1) (by simp [hs])
  exact one_ne_zero hz.2

/-- Both affine coefficients are scalar maps and the constant drift is annihilated. -/
theorem identical_row_scalar_identity (d : ℕ) (hd : 1 ≤ d) (w : List Bool)
    (C : Readout d w) (h : RowUniversallyCollinear d w C) :
    C.mulVec (fun _ => 1) = 0 ∧ ∃ lam0 lam1 : ℝ,
      rowMap d w C (rowBase w) = lam0 • LinearMap.id ∧
      rowMap d w C (rowSlope w) = lam1 • LinearMap.id := by
  refine ⟨row_drift_zero d hd w C h, ?_⟩
  obtain ⟨a, ha⟩ := row_scalar_at d w C h (1/3) (by norm_num) (by norm_num)
  obtain ⟨b, hb⟩ := row_scalar_at d w C h (2/3) (by norm_num) (by norm_num)
  have hf (θ : ℝ) (β : Coeff d) :
      rowMap d w C (rowBase w + θ • rowSlope w) β =
        rowMap d w C (rowBase w) β + θ • rowMap d w C (rowSlope w) β := by
    simp only [row_map_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_add]
    congr 1
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨2*a-b, 3*(b-a), ?_, ?_⟩
  all_goals
    apply LinearMap.ext
    intro β
    apply funext
    intro j
    have h₁ := congrFun (LinearMap.congr_fun ha β) j
    have h₂ := congrFun (LinearMap.congr_fun hb β) j
    rw [hf] at h₁ h₂
    simp only [Pi.add_apply, Pi.smul_apply, LinearMap.smul_apply, LinearMap.id_apply,
      smul_eq_mul] at h₁ h₂ ⊢
    linarith

private theorem row_short_suffix_zero (d : ℕ) (hd : 1 ≤ d) (w : List Bool)
    (C : Readout d w) (h : RowUniversallyCollinear d w C)
    (n : ℕ) (hn : n ≤ w.length + 1) (hr : w.length + 1 - n < d + 1)
    (hs : ∀ i : Fin (w.length + 1), rowSlope w i ≠ 0 ↔ n ≤ i.val) :
    C.mulVec (fun _ => 1) = 0 ∧
    rowMap d w C (rowSlope w) = 0 ∧
    (∀ i : Fin (w.length + 1), n ≤ i.val → ∀ a, C a i = 0) ∧
    rowMap d w C (rowBase w) = 0 := by
  classical
  obtain ⟨hD, lam0, lam1, h₀, h₁⟩ := identical_row_scalar_identity d hd w C h
  let r := w.length + 1 - n
  let t : Fin r → ℝ := fun j => ((n + j.val : ℕ) : ℝ)
  have ht : Function.Injective t := by
    intro i j he
    apply Fin.ext
    dsimp [t] at he
    have he' : n + i.val = n + j.val := by exact_mod_cast he
    omega
  have hz (i : Fin (w.length + 1)) (hi : i.val < n) : rowSlope w i = 0 := by
    by_contra hh
    have := (hs i).mp hh
    omega
  have factor (β γ : Coeff d) (he : evaluate d r t β = evaluate d r t γ) :
      rowMap d w C (rowSlope w) β = rowMap d w C (rowSlope w) γ := by
    rw [row_map_apply, row_map_apply]
    congr 1
    ext i
    by_cases hi : i.val < n
    · simp [hz i hi]
    · let j : Fin r := ⟨i.val - n, by dsimp [r]; omega⟩
      have hj : t j = (i.val : ℝ) := by
        dsimp [t, j]
        congr 1
        omega
      have he' := congrFun he j
      rw [evaluation_polynomial, evaluation_polynomial, hj] at he'
      rw [he']
  have hlam1 : lam1 = 0 := by
    by_contra hne
    have hinj : Function.Injective (evaluate d r t) := by
      intro β γ he
      have hf := factor β γ he
      rw [h₁] at hf
      simp only [LinearMap.smul_apply, LinearMap.id_apply] at hf
      exact (smul_right_injective _ hne) hf
    have hdim := LinearMap.finrank_le_finrank_of_injective hinj
    have : d + 1 ≤ r := by simpa [Coeff, Module.finrank_pi] using hdim
    dsimp [r] at this
    omega
  have hB : rowMap d w C (rowSlope w) = 0 := by simpa [hlam1] using h₁
  have hC : ∀ i : Fin (w.length + 1), n ≤ i.val → ∀ a, C a i = 0 := by
    intro i hi
    have hbi : rowSlope w i ≠ 0 := (hs i).mpr hi
    obtain ⟨β, hβ⟩ := evaluation_surjective d r t ht (by dsimp [r]; omega)
      (fun j => if n + j.val = i.val then (rowSlope w i)⁻¹ else 0)
    have hv : (fun l : Fin (w.length + 1) =>
        rowSlope w l * (gain d β).eval (l.val : ℝ)) = Pi.single i 1 := by
      ext l
      by_cases hl : l.val < n
      · have hli : l ≠ i := by intro he; subst l; omega
        simp [hz l hl, hli]
      · let j : Fin r := ⟨l.val - n, by dsimp [r]; omega⟩
        have hj : n + j.val = l.val := by dsimp [j]; omega
        have he := congrFun hβ j
        rw [evaluation_polynomial] at he
        change (gain d β).eval ((n + j.val : ℕ) : ℝ) = _ at he
        rw [hj] at he
        rw [he]
        by_cases hli : l = i
        · subst l
          simp [hbi]
        · have hne : l.val ≠ i.val := fun he => hli (Fin.ext he)
          simp [hne, hli]
    have he := LinearMap.congr_fun hB β
    rw [row_map_apply, hv, Matrix.mulVec_single_one] at he
    intro a
    exact congrFun he a
  have hbase : rowMap d w C (rowBase w) (Pi.single 0 1) = C.mulVec (fun _ => 1) := by
    rw [row_map_apply]
    ext a
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : n ≤ i.val
    · simp [hC i hi a]
    · have hni : false ∉ w.take i.val := by
        intro hm
        have := (hs i).mp ((identical_row_slope_support w i).mpr hm)
        exact hi this
      rw [row_base_before w i hni]
      have hg : (gain d (Pi.single 0 1)).eval (i.val : ℝ) = 1 := by
        change (gain d (Pi.single 0 1)).eval (clocks (w.length + 1) i) = 1
        rw [← evaluation_polynomial d (w.length + 1) (clocks _) (Pi.single 0 1) i]
        simp [evaluate, evaluation, Matrix.mulVec, dotProduct, Pi.single_apply]
      simp [hg]
  have hlam0 : lam0 = 0 := by
    rw [h₀, hD] at hbase
    have he := congrFun hbase 0
    simpa using he
  exact ⟨hD, hB, hC, by simpa [hlam0] using h₀⟩

private theorem row_output_zero (d : ℕ) (w : List Bool) (C : Readout d w)
    (hD : C.mulVec (fun _ => 1) = 0)
    (hU : rowMap d w C (rowBase w) = 0)
    (hB : rowMap d w C (rowSlope w) = 0)
    (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1) (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ) :
    C.mulVec (readings (rowWorld d θ hθ hθ' β hβ δ) w) = 0 := by
  have hv : (fun i : Fin (w.length + 1) =>
      (rowBase w i + θ * rowSlope w i) * (gain d β).eval (i.val : ℝ)) =
      (fun i => rowBase w i * (gain d β).eval (i.val : ℝ)) +
        θ • (fun i => rowSlope w i * (gain d β).eval (i.val : ℝ)) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have he : C.mulVec (readings (rowWorld d θ hθ hθ' β hβ δ) w) =
      rowMap d w C (rowBase w) β + θ • rowMap d w C (rowSlope w) β +
        δ • C.mulVec (fun _ => 1) := by
    rw [row_readings_affine, hv]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, row_map_apply]
  simp [he, hU, hB, hD]

/-- An arbitrary pure-J word, including no actions, has no nonzero universal ray output. -/
theorem identical_row_pureJ_annihilation (d : ℕ) (hd : 1 ≤ d) (w : List Bool)
    (C : Readout d w) (h : RowUniversallyCollinear d w C) (hw : false ∉ w) :
    C.mulVec (fun _ => 1) = 0 ∧
    rowMap d w C (rowBase w) = 0 ∧ rowMap d w C (rowSlope w) = 0 := by
  have hs (i : Fin (w.length + 1)) : rowSlope w i ≠ 0 ↔ w.length + 1 ≤ i.val := by
    rw [identical_row_slope_support]
    constructor
    · intro hm; exact (hw (List.mem_of_mem_take hm)).elim
    · intro hi; omega
  obtain ⟨hD, hB, _, hU⟩ := row_short_suffix_zero d hd w C h (w.length + 1)
    (by omega) (by omega) hs
  exact ⟨hD, hU, hB⟩

/-- Every column at and after the first M vanishes when its entire suffix has fewer than m reads. -/
theorem identical_row_suffix_annihilation (d : ℕ) (hd : 1 ≤ d) (k : ℕ)
    (tail : List Bool) (hr : tail.length + 1 < d + 1)
    (C : Readout d (List.replicate k true ++ [false] ++ tail))
    (h : RowUniversallyCollinear d (List.replicate k true ++ [false] ++ tail) C) :
    C.mulVec (fun _ => 1) = 0 ∧
    (∀ i : Fin ((List.replicate k true ++ [false] ++ tail).length + 1),
      k < i.val → ∀ a, C a i = 0) ∧
    rowMap d (List.replicate k true ++ [false] ++ tail) C
      (rowBase (List.replicate k true ++ [false] ++ tail)) = 0 ∧
    rowMap d (List.replicate k true ++ [false] ++ tail) C
      (rowSlope (List.replicate k true ++ [false] ++ tail)) = 0 := by
  have hs (i : Fin ((List.replicate k true ++ [false] ++ tail).length + 1)) :
      rowSlope (List.replicate k true ++ [false] ++ tail) i ≠ 0 ↔ k + 1 ≤ i.val := by
    rw [identical_row_entire_suffix]
    omega
  obtain ⟨hD, hB, hC, hU⟩ := row_short_suffix_zero d hd _ C h (k + 1)
    (by simp) (by simpa using hr) hs
  exact ⟨hD, fun i hi => hC i (by omega), hU, hB⟩

/-- Whole Lemma 9.2 on legal native worlds: universal collinearity forces zero everywhere. -/
theorem identical_row_annihilation (d : ℕ) (hd : 1 ≤ d) (w : List Bool)
    (C : Readout d w) (h : RowUniversallyCollinear d w C)
    (hw : false ∉ w ∨ ∃ (k : ℕ) (tail : List Bool),
      w = List.replicate k true ++ [false] ++ tail ∧ tail.length + 1 < d + 1) :
    ∀ (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1) (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ),
      C.mulVec (readings (rowWorld d θ hθ hθ' β hβ δ) w) = 0 ∧
      ¬ Succeeds (rowWorld d θ hθ hθ' β hβ δ) w C := by
  have hz : C.mulVec (fun _ => 1) = 0 ∧
      rowMap d w C (rowBase w) = 0 ∧ rowMap d w C (rowSlope w) = 0 := by
    rcases hw with hw | ⟨k, tail, rfl, hr⟩
    · exact identical_row_pureJ_annihilation d hd w C h hw
    · obtain ⟨hD, _, hU, hB⟩ := identical_row_suffix_annihilation d hd k tail hr C h
      exact ⟨hD, hU, hB⟩
  intro θ hθ hθ' β hβ δ
  have he := row_output_zero d w C hz.1 hz.2.1 hz.2.2 θ hθ hθ' β hβ δ
  refine ⟨he, ?_⟩
  rintro ⟨s, hs, hsβ⟩
  exact (smul_ne_zero hs hβ) (hsβ.symm.trans he)

#print axioms identical_row_trace
#print axioms identical_row_slope_support
#print axioms identical_row_entire_suffix
#print axioms identical_row_scalar_identity
#print axioms identical_row_pureJ_annihilation
#print axioms identical_row_suffix_annihilation
#print axioms identical_row_annihilation

end D5.S3.Observer.Linear.GainRay
