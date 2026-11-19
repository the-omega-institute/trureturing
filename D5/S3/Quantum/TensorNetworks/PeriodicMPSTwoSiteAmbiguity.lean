/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteAmbiguity
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteAmbiguity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual periodic two-site phase ambiguity via parity presentations. -/

import D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection

/-! Parity presentations give collisions in the actual periodic two-site fibre. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteAmbiguity

open PeriodicMPSParentIntersection
open UniformMPSExpectedDimensionRefutation (traceWord)
open scoped BigOperators Matrix

noncomputable section

/-- The raw two-site density of the actual periodic state. -/
def rawTwo (A : Fin 2 → Bond) (r : ℕ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  twoFlattening A r * (twoFlattening A r).conjTranspose

/-- A diagonal zero symbol and a symmetric off-diagonal one symbol. -/
def parityPair (a b q : ℂ) : Fin 2 → Bond :=
  ![!![a, 0; 0, b], !![0, q; q, 0]]

private theorem parity_spanning (a b q : ℂ) (hq : q ≠ 0) (hab : a ^ 2 ≠ b ^ 2) :
    TwoSiteSpanning (parityPair a b q) := by
  classical
  apply Submodule.eq_top_iff'.mpr
  intro M
  let A := parityPair a b q
  let S := Submodule.span ℂ (Set.range fun p : Fin 2 × Fin 2 => A p.1 * A p.2)
  have hp (i j : Fin 2) : A i * A j ∈ S := Submodule.subset_span ⟨(i, j), rfl⟩
  have hd : a ^ 2 - b ^ 2 ≠ 0 := sub_ne_zero.mpr hab
  have hm := S.add_mem
    (S.add_mem
      (S.smul_mem ((M 0 0 - M 1 1) / (a ^ 2 - b ^ 2)) (hp 0 0))
      (S.smul_mem ((a ^ 2 * M 1 1 - b ^ 2 * M 0 0) / (q ^ 2 * (a ^ 2 - b ^ 2)))
        (hp 1 1)))
    (S.add_mem
      (S.smul_mem ((a * M 0 1 - b * M 1 0) / (q * (a ^ 2 - b ^ 2))) (hp 0 1))
      (S.smul_mem ((a * M 1 0 - b * M 0 1) / (q * (a ^ 2 - b ^ 2))) (hp 1 0)))
  convert hm using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, parityPair] <;>
    field_simp <;> ring

lemma flattening_entry (A : Fin 2 → Bond) (r : ℕ) (i j : Fin 2)
    (w : Word (r + 2)) :
    twoFlattening A r (i, j) w = (A i * A j * wordMatrix A w).trace := by
  change (wordMatrix A (Fin.append ![i, j] w)).trace = _
  rw [wordMatrix_append]
  simp [wordMatrix, List.ofFn_succ]

private lemma parity_product_shape (a b q : ℂ) :
    ∀ (n : ℕ) (w : Word n),
      (∃ x y, wordMatrix (parityPair a b q) w = !![x, 0; 0, y]) ∨
        ∃ x y, wordMatrix (parityPair a b q) w = !![0, x; y, 0] := by
  intro n
  induction n with
  | zero =>
    intro w
    left
    exact ⟨1, 1, by simp [wordMatrix, List.ofFn_zero, Matrix.one_fin_two]⟩
  | succ n ih =>
    intro w
    rw [← Fin.cons_self_tail w, wordMatrix_cons]
    rcases ih (Fin.tail w) with ⟨x, y, hx⟩ | ⟨x, y, hx⟩
    · rw [hx]
      have hw : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
      rcases hw (w 0) with h | h
      · left
        refine ⟨a * x, b * y, ?_⟩
        rw [h]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [parityPair, Matrix.mul_apply, Fin.sum_univ_two]
      · right
        refine ⟨q * y, q * x, ?_⟩
        rw [h]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [parityPair, Matrix.mul_apply, Fin.sum_univ_two]
    · rw [hx]
      have hw : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
      rcases hw (w 0) with h | h
      · right
        refine ⟨a * x, b * y, ?_⟩
        rw [h]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [parityPair, Matrix.mul_apply, Fin.sum_univ_two]
      · left
        refine ⟨q * y, q * x, ?_⟩
        rw [h]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [parityPair, Matrix.mul_apply, Fin.sum_univ_two]

private lemma rawTwo_entry (A : Fin 2 → Bond) (r : ℕ) (p s : Fin 2 × Fin 2) :
    rawTwo A r p s = ∑ w, twoFlattening A r p w * star (twoFlattening A r s w) := by
  simp [rawTwo, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma rawTwo_star_swap (A : Fin 2 → Bond) (r : ℕ) (p s : Fin 2 × Fin 2) :
    star (rawTwo A r p s) = rawTwo A r s p := by
  simp only [rawTwo_entry, star_sum, star_mul, star_star]

lemma parity_cross (a b q : ℂ) (r : ℕ) (i j k : Fin 2) :
    rawTwo (parityPair a b q) r (i, i) (j, k) = 0 ∨ j = k := by
  by_cases h : j = k
  · exact Or.inr h
  left
  rw [rawTwo_entry]
  apply Finset.sum_eq_zero
  intro w _
  obtain ⟨x, y, hx⟩ | ⟨x, y, hx⟩ := parity_product_shape a b q (r + 2) w
  · rw [flattening_entry, flattening_entry, hx]
    have hz : ((parityPair a b q j * parityPair a b q k) * !![x, 0; 0, y]).trace = 0 := by
      fin_cases j <;> fin_cases k <;>
        simp_all [parityPair, Matrix.trace, Fin.sum_univ_two]
    simp [hz]
  · rw [flattening_entry, flattening_entry, hx]
    have hz : ((parityPair a b q i * parityPair a b q i) * !![0, x; y, 0]).trace = 0 := by
      fin_cases i <;> simp [parityPair, Matrix.trace, Fin.sum_univ_two]
    simp [hz]

private lemma wordMatrix_reverse (A : Fin 2 → Bond) (hA : ∀ i, (A i).transpose = A i)
    {n : ℕ} (w : Word n) :
    wordMatrix A (w ∘ Fin.rev) = (wordMatrix A w).transpose := by
  induction n with
  | zero => simp [wordMatrix, List.ofFn_zero]
  | succ n ih =>
    have he : w ∘ Fin.rev = Fin.cons (w (Fin.last n)) (Fin.init w ∘ Fin.rev) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [Function.comp_def, Fin.rev_succ, Fin.init]
    rw [he, wordMatrix_cons, ih, ← hA (w (Fin.last n)), ← Matrix.transpose_mul,
      ← wordMatrix_snoc, Fin.snoc_init_self]

private lemma parity_flattening_reverse (a b q : ℂ) (r : ℕ) (i j : Fin 2)
    (w : Word (r + 2)) :
    twoFlattening (parityPair a b q) r (i, j) (w ∘ Fin.rev) =
      twoFlattening (parityPair a b q) r (j, i) w := by
  have hs (k : Fin 2) : (parityPair a b q k).transpose = parityPair a b q k := by
    fin_cases k <;> ext x y <;> fin_cases x <;> fin_cases y <;> rfl
  rw [flattening_entry, flattening_entry, wordMatrix_reverse _ hs,
    ← hs i, ← hs j, ← Matrix.transpose_mul, ← Matrix.transpose_mul,
    Matrix.trace_transpose, Matrix.trace_mul_comm]
  simp only [hs]

private lemma parity_odd_swap (a b q : ℂ) (r : ℕ) :
    rawTwo (parityPair a b q) r (0, 1) (1, 0) =
      rawTwo (parityPair a b q) r (1, 0) (0, 1) := by
  rw [rawTwo_entry, rawTwo_entry]
  let e : Word (r + 2) ≃ Word (r + 2) :=
    { toFun := fun w => w ∘ Fin.rev
      invFun := fun w => w ∘ Fin.rev
      left_inv := fun w => by funext i; simp
      right_inv := fun w => by funext i; simp }
  exact Fintype.sum_equiv e _ _ (fun w => by
    change _ = twoFlattening (parityPair a b q) r (1, 0) (w ∘ Fin.rev) *
      star (twoFlattening (parityPair a b q) r (0, 1) (w ∘ Fin.rev))
    rw [parity_flattening_reverse, parity_flattening_reverse])

private def phaseConjugate (η : ℂ) (A : Fin 2 → Bond) : Fin 2 → Bond :=
  fun i => (![1, η] : Fin 2 → ℂ) i • (A i).map (starRingEnd ℂ)

private def phaseWeight (η : ℂ) (i : Fin 2) : ℂ := (![1, η] : Fin 2 → ℂ) i

private lemma phaseWeight_unit (η : ℂ) (hη : η * star η = 1) (i : Fin 2) :
    phaseWeight η i * star (phaseWeight η i) = 1 := by
  fin_cases i
  · simp [phaseWeight]
  · exact hη

private lemma phaseConjugate_product (η : ℂ) (A : Fin 2 → Bond) (n : ℕ) (w : Word n) :
    wordMatrix (phaseConjugate η A) w =
      (∏ i, phaseWeight η (w i)) • (wordMatrix A w).map (starRingEnd ℂ) := by
  induction n with
  | zero => simp [wordMatrix, List.ofFn_zero, Matrix.map_one]
  | succ n ih =>
    rw [← Fin.cons_self_tail w, wordMatrix_cons, wordMatrix_cons, ih,
      Fin.prod_univ_succ, Matrix.map_mul]
    simp [phaseConjugate, phaseWeight, smul_smul, mul_comm]

private lemma phaseConjugate_entry (η : ℂ) (A : Fin 2 → Bond) (r : ℕ) (i j : Fin 2)
    (w : Word (r + 2)) :
    twoFlattening (phaseConjugate η A) r (i, j) w =
      (phaseWeight η i * phaseWeight η j * ∏ k, phaseWeight η (w k)) *
        star (twoFlattening A r (i, j) w) := by
  simp only [flattening_entry, phaseConjugate_product]
  change ((phaseWeight η i • (A i).map (starRingEnd ℂ)) *
      (phaseWeight η j • (A j).map (starRingEnd ℂ)) *
      ((∏ k, phaseWeight η (w k)) • (wordMatrix A w).map (starRingEnd ℂ))).trace = _
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.map_mul,
    Matrix.trace_smul, smul_eq_mul, ← AddMonoidHom.map_trace (starRingEnd ℂ), Complex.star_def]
  ring

private lemma phaseConjugate_raw (η : ℂ) (hη : η * star η = 1) (A : Fin 2 → Bond)
    (r : ℕ) (p s : Fin 2 × Fin 2) :
    rawTwo (phaseConjugate η A) r p s =
      (phaseWeight η p.1 * phaseWeight η p.2 *
        star (phaseWeight η s.1 * phaseWeight η s.2)) * star (rawTwo A r p s) := by
  rw [rawTwo_entry, rawTwo_entry, star_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rcases p with ⟨i, j⟩
  rcases s with ⟨k, l⟩
  rw [phaseConjugate_entry, phaseConjugate_entry]
  have hweight : (∏ t, phaseWeight η (w t)) * star (∏ t, phaseWeight η (w t)) = 1 := by
    rw [star_prod, ← Finset.prod_mul_distrib]
    simp only [phaseWeight_unit η hη, Finset.prod_const_one]
  simp only [star_mul, star_star] at *
  linear_combination
    (phaseWeight η i * phaseWeight η j * star (phaseWeight η k) *
      star (phaseWeight η l) * star (twoFlattening A r (i, j) w) *
      twoFlattening A r (k, l) w) * hweight

private lemma phase_for_entry (z : ℂ) :
    ∃ η : ℂ, η * star η = 1 ∧ star η ^ 2 * star z = z := by
  by_cases h : z = 0
  · exact ⟨1, by simp [h]⟩
  let d : ℂ := (‖z‖ : ℝ)
  have hd : d ≠ 0 := by simpa [d] using h
  have hstar : star d = d := Complex.conj_ofReal _
  have hmul : z * star z = d ^ 2 := by
    simpa [d] using Complex.mul_conj' z
  refine ⟨star z / d, ?_, ?_⟩ <;> rw [star_div₀, star_star, hstar]
  · field_simp
    linear_combination hmul
  · field_simp
    linear_combination hmul

private lemma parity_matching (a b q : ℂ) (r : ℕ) :
    ∃ η : ℂ, η * star η = 1 ∧
      rawTwo (phaseConjugate η (parityPair a b q)) r = rawTwo (parityPair a b q) r := by
  let A := parityPair a b q
  obtain ⟨η, hη, hz⟩ := phase_for_entry (rawTwo A r (0, 0) (1, 1))
  refine ⟨η, hη, ?_⟩
  have hc (i j k : Fin 2) (h : j ≠ k) : rawTwo A r (i, i) (j, k) = 0 :=
    (parity_cross a b q r i j k).resolve_right h
  have hcr (i j k : Fin 2) (h : j ≠ k) : rawTwo A r (j, k) (i, i) = 0 := by
    rw [← rawTwo_star_swap, hc i j k h, star_zero]
  have hrev : η ^ 2 * rawTwo A r (0, 0) (1, 1) = rawTwo A r (1, 1) (0, 0) := by
    simpa only [star_mul, star_pow, star_star, rawTwo_star_swap, mul_comm] using congrArg star hz
  have hz' : (starRingEnd ℂ) η ^ 2 * rawTwo A r (1, 1) (0, 0) =
      rawTwo A r (0, 0) (1, 1) := by
    change star η ^ 2 * rawTwo A r (1, 1) (0, 0) = rawTwo A r (0, 0) (1, 1)
    rw [← rawTwo_star_swap A r (0, 0) (1, 1)]
    exact hz
  have hη' : η * (starRingEnd ℂ) η = 1 := hη
  have hsq : η ^ 2 * (starRingEnd ℂ) η ^ 2 = 1 := by
    change η ^ 2 * star η ^ 2 = 1
    rw [← mul_pow, hη, one_pow]
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [phaseConjugate_raw η hη]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [phaseWeight, rawTwo_star_swap, hc, hcr, ← pow_two,
      parity_odd_swap a b q r, A] <;>
    first | exact hz' | exact hrev | rw [hη', one_mul] | rw [hsq, one_mul]

private def zeroWord (n : ℕ) : Word n := fun _ => 0

private def adjacentWord (r : ℕ) : Word (r + 4) :=
  Fin.cons 1 (Fin.cons 1 (zeroWord (r + 2)))

private def separatedWord (r : ℕ) : Word (r + 4) :=
  Fin.cons 1 (Fin.cons 0 (Fin.cons 1 (zeroWord (r + 1))))

private def adjacentValue (a b q : ℂ) (r : ℕ) : ℂ := q ^ 2 * (a ^ (r + 2) + b ^ (r + 2))

private def separatedValue (a b q : ℂ) (r : ℕ) : ℂ :=
  q ^ 2 * (b * a ^ (r + 1) + a * b ^ (r + 1))

private lemma parity_zero_product (a b q : ℂ) (n : ℕ) :
    wordMatrix (parityPair a b q) (zeroWord n) = !![a ^ n, 0; 0, b ^ n] := by
  change (List.ofFn fun _ : Fin n => parityPair a b q 0).prod = _
  rw [List.ofFn_const, List.prod_replicate]
  have h : parityPair a b q 0 = Matrix.diagonal ![a, b] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h, Matrix.diagonal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma parity_adjacent (a b q : ℂ) (r : ℕ) :
    gamma (parityPair a b q) (r + 4) 1 (adjacentWord r) = adjacentValue a b q r := by
  simp only [gamma, one_mul, adjacentWord, wordMatrix_cons, parity_zero_product]
  simp [adjacentValue, parityPair, Matrix.trace, Fin.sum_univ_two]
  ring

private lemma parity_separated (a b q : ℂ) (r : ℕ) :
    gamma (parityPair a b q) (r + 4) 1 (separatedWord r) = separatedValue a b q r := by
  simp only [gamma, one_mul, separatedWord, wordMatrix_cons, parity_zero_product]
  simp [separatedValue, parityPair, Matrix.trace, Fin.sum_univ_two]
  ring

private lemma phaseConjugate_amplitude (η : ℂ) (A : Fin 2 → Bond) {n : ℕ} (w : Word n) :
    gamma (phaseConjugate η A) n 1 w =
      (∏ i, phaseWeight η (w i)) * star (gamma A n 1 w) := by
  simp only [gamma, one_mul, phaseConjugate_product, Matrix.trace_smul, smul_eq_mul,
    ← AddMonoidHom.map_trace (starRingEnd ℂ)]
  rfl

private lemma parity_incompatible (a b q η : ℂ) (r : ℕ) (hη : η * star η = 1)
    (h : ((separatedValue a b q r) * star (adjacentValue a b q r)).im ≠ 0) :
    ∀ c : ℂ, gamma (phaseConjugate η (parityPair a b q)) (r + 4) 1 ≠
      c • gamma (parityPair a b q) (r + 4) 1 := by
  intro c he
  have h0 := congrFun he (adjacentWord r)
  have h1 := congrFun he (separatedWord r)
  simp only [Pi.smul_apply, smul_eq_mul, phaseConjugate_amplitude, parity_adjacent] at h0
  simp only [Pi.smul_apply, smul_eq_mul, phaseConjugate_amplitude, parity_separated] at h1
  have he0 : η ^ 2 * star (adjacentValue a b q r) = c * adjacentValue a b q r := by
    simpa [adjacentWord, Fin.prod_univ_succ, phaseWeight, zeroWord, pow_two] using h0
  have he1 : η ^ 2 * star (separatedValue a b q r) = c * separatedValue a b q r := by
    simpa [separatedWord, Fin.prod_univ_succ, phaseWeight, zeroWord, pow_two] using h1
  have hn : η ^ 2 ≠ 0 := by
    intro hz
    have hzero : η = 0 := by simpa [pow_two] using hz
    simp [hzero] at hη
  let z := separatedValue a b q r * star (adjacentValue a b q r)
  have hz : η ^ 2 * z = η ^ 2 * star z := by
    simp only [z, star_mul, star_star]
    linear_combination separatedValue a b q r * he0 - adjacentValue a b q r * he1
  have hi := congrArg Complex.im (mul_left_cancel₀ hn hz)
  simp only [Complex.star_def, Complex.conj_im] at hi
  exact h (by change z.im = 0; linarith)

private lemma witness_im (r : ℕ) :
    (separatedValue 1 (Complex.I / 2) 1 r * star (adjacentValue 1 (Complex.I / 2) 1 r)).im ≠ 0 := by
  cases r with
  | zero =>
    norm_num [separatedValue, adjacentValue, Complex.star_def, Complex.mul_im, Complex.div_re,
      Complex.div_im, Complex.normSq_apply, pow_two, Complex.mul_re]
  | succ r =>
    let t : ℂ := Complex.I / 2
    let x := t ^ (r + 2)
    let y := t ^ (r + 3)
    have ht : ‖t‖ = 1 / 2 := by norm_num [t, norm_div]
    have hti : t.im = 1 / 2 := by norm_num [t, Complex.div_im, Complex.normSq_apply]
    have hx : ‖x‖ ≤ 1 / 4 := by
      rw [show x = t ^ r * t ^ 2 by simp [x, pow_add], norm_mul, norm_pow t 2, ht]
      have hxr : ‖t ^ r‖ ≤ 1 := by rw [norm_pow, ht]; exact pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith [norm_nonneg (t ^ r)]
    have hy : ‖y‖ ≤ 1 / 8 := by
      rw [show y = x * t by simp [x, y, pow_succ], norm_mul, ht]
      linarith
    let e := x + (t + x) * star y
    have he : ‖e‖ ≤ 11 / 32 := calc
      ‖e‖ ≤ ‖x‖ + ‖(t + x) * star y‖ := norm_add_le _ _
      _ = ‖x‖ + ‖t + x‖ * ‖y‖ := by rw [norm_mul, norm_star]
      _ ≤ 1 / 4 + (1 / 2 + 1 / 4) * (1 / 8) := by
        have htx : ‖t + x‖ ≤ 1 / 2 + 1 / 4 := by
          linarith [norm_add_le t x]
        gcongr
      _ = _ := by norm_num
    have heq : separatedValue 1 t 1 (r + 1) * star (adjacentValue 1 t 1 (r + 1)) = t + e := by
      simp only [separatedValue, adjacentValue, one_pow, mul_one, one_mul, star_add, star_one,
        e, x, y]
      ring
    change (separatedValue 1 t 1 (r + 1) * star (adjacentValue 1 t 1 (r + 1))).im ≠ 0
    rw [heq, Complex.add_im, hti]
    have hi := (abs_le.mp (Complex.abs_im_le_norm e)).1
    linarith

def parityCondition (x : Fin 3 → ℂ) (r : ℕ) : Prop :=
  x 2 ≠ 0 ∧ x 0 ^ 2 ≠ x 1 ^ 2 ∧
  (separatedValue (x 0) (x 1) (x 2) r * star (adjacentValue (x 0) (x 1) (x 2) r)).im ≠ 0

lemma parityCondition_open (r : ℕ) : IsOpen {x | parityCondition x r} := by
  refine (isOpen_ne_fun (continuous_apply 2) continuous_const).inter
    ((isOpen_ne_fun ((continuous_apply 0).pow _) ((continuous_apply 1).pow _)).inter ?_)
  apply isOpen_ne_fun _ continuous_const
  apply Complex.continuous_im.comp
  unfold separatedValue adjacentValue
  fun_prop

lemma parityCondition_nonempty (r : ℕ) : {x | parityCondition x r}.Nonempty := by
  refine ⟨![1, Complex.I / 2, 1], one_ne_zero, ?_, witness_im r⟩
  intro he
  have h := congrArg Complex.re he
  norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply, pow_two, Complex.mul_re] at h

/-- The parity condition gives a spanning target and an actual nonproportional
competitor with identical raw two-site density. -/
theorem parity_actual_collision (x : Fin 3 → ℂ) (r : ℕ) (h : parityCondition x r) :
    TwoSiteSpanning (parityPair (x 0) (x 1) (x 2)) ∧
      ∃ B : Fin 2 → Bond,
        rawTwo B r = rawTwo (parityPair (x 0) (x 1) (x 2)) r ∧
        (∀ c : ℂ, gamma B (r + 4) 1 ≠ c • gamma (parityPair (x 0) (x 1) (x 2)) (r + 4) 1) := by
  refine ⟨parity_spanning _ _ _ h.1 h.2.1, ?_⟩
  obtain ⟨η, hη, he⟩ := parity_matching (x 0) (x 1) (x 2) r
  exact ⟨phaseConjugate η _, he, parity_incompatible _ _ _ η r hη h.2.2⟩

/-- For every ring of length `r + 4`, two sites fail to recover the phase of an
actual rank-four target, while three sites distinguish its competitor. -/
theorem actual_two_site_ambiguity (r : ℕ) :
    ∃ A B : Fin 2 → Bond, (twoFlattening A r).rank = 4 ∧
      rawTwo B r = rawTwo A r ∧ (∀ c : ℂ, gamma B (r + 4) 1 ≠ c • gamma A (r + 4) 1) ∧
      rawThree B r ≠ rawThree A r := by
  obtain ⟨x, hx⟩ := parityCondition_nonempty r
  obtain ⟨hspan, B, hraw, hneq⟩ := parity_actual_collision x r hx
  let A := parityPair (x 0) (x 1) (x 2)
  have hr := rank_of_spanning A hspan r
  refine ⟨A, B, hr, hraw, hneq, fun hthree => ?_⟩
  obtain ⟨c, _, hc⟩ := ((rank_locus_inhabited_and_phase_recovery r).2 _ _ hr).mp hthree
  exact hneq c hc

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteAmbiguity
