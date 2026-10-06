/- GID: D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsBulk
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsBulk
   mirror-E: none(waiver:catalan-transfer-enumeration)
   anchors: []
   utility: none
   digest: Catalan transfer coefficients and Fibonacci exit weights enumerate the bulk. -/

import D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchingsWordSeries
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchings

open TripleAvoidingMatchingsDefs PowerSeries
set_option maxHeartbeats 1000000 in
-- Matrix convolution and coefficient induction retain both automaton phases.
/-- The height-two suffix count is the Catalan--Fibonacci transfer series times
its boundary continuation. Coefficient induction handles every bulk height. -/
theorem bulk_enumeration :
    wordSeries 2 false = X * expand 2 (by decide) hSeries * wordSeries 1 false := by
  let D : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]
  let d : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ) := D.map C
  let E : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ) :=
    fun i j => mk fun k => (catalan k : ℤ) * (D ^ k) i j
  let mc (k : ℕ) (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ :=
    fun i j => coeff k (A i j)
  have emc (k : ℕ) : mc k E = (catalan k : ℤ) • D ^ k := by
    ext i j
    simp [mc, E, Matrix.smul_apply]
  have md (k : ℕ) (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ)) :
      mc k (A * d) = mc k A * D := by
    ext i j
    change coeff k ((A * d) i j) = (mc k A * D) i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [map_sum, d, Matrix.map_apply, coeff_mul_C, mc]
  have dm (k : ℕ) (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ)) :
      mc k (d * A) = D * mc k A := by
    ext i j
    change coeff k ((d * A) i j) = (D * mc k A) i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [map_sum, d, Matrix.map_apply, coeff_C_mul, mc]
  have mm (k : ℕ) (A B : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ)) :
      mc k (A * B) = ∑ ij ∈ Finset.antidiagonal k, mc ij.1 A * mc ij.2 B := by
    ext i j
    simp only [mc, Matrix.mul_apply, map_sum, coeff_mul, Matrix.sum_apply]
    exact Finset.sum_comm
  have prod (k : ℕ) : mc k (E * E * d) = (catalan (k + 1) : ℤ) • D ^ (k + 1) := by
    rw [md, mm, Finset.sum_mul]
    calc
      (∑ ij ∈ Finset.antidiagonal k, (mc ij.1 E * mc ij.2 E) * D) =
          ∑ ij ∈ Finset.antidiagonal k,
            ((catalan ij.1 : ℤ) * (catalan ij.2 : ℤ)) • D ^ (k + 1) := by
        apply Finset.sum_congr rfl
        intro ij hij
        rw [emc, emc, smul_mul_smul, smul_mul_assoc]
        congr 1
        rw [← pow_add, ← pow_succ, Finset.mem_antidiagonal.mp hij]
      _ = (∑ ij ∈ Finset.antidiagonal k,
          ((catalan ij.1 : ℤ) * (catalan ij.2 : ℤ))) • D ^ (k + 1) :=
        Finset.sum_smul.symm
      _ = (catalan (k + 1) : ℤ) • D ^ (k + 1) := by
        congr 1
        exact_mod_cast (catalan_succ' k).symm
  have eqE : E = 1 + (X : PowerSeries ℤ) • (E * E * d) := by
    apply Matrix.ext
    intro i j
    apply PowerSeries.ext
    intro k
    cases k with
    | zero => simp [E, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
    | succ k =>
      have hh := congrFun (congrFun (prod k) i) j
      by_cases hij : i = j
      all_goals simpa [mc, E, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
        coeff_succ_X_mul, coeff_one, hij] using hh.symm
  have comm : Commute d E := by
    change d * E = E * d
    apply Matrix.ext
    intro i j
    apply PowerSeries.ext
    intro k
    have hh : mc k (d * E) = mc k (E * d) := by
      rw [dm, md, emc, mul_smul_comm, smul_mul_assoc]
      exact congrArg ((catalan k : ℤ) • ·) ((Commute.refl D).pow_right k).eq
    exact congrFun (congrFun hh i) j
  let ex := expand 2 (by decide) (R := ℤ)
  let e := E.map ex
  have de : d.map ex = d := by ext i j; simp [d, Matrix.map_apply]
  have mapX (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ)) :
      ((X : PowerSeries ℤ) • A).map ex = (X ^ 2 : PowerSeries ℤ) • A.map ex := by
    apply Matrix.ext
    intro i j
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, ex, expand_X]
  have ee : e = 1 + (X ^ 2 : PowerSeries ℤ) • (e * e * d) := by
    have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ) => A.map ex) eqE
    rw [Matrix.map_add _ (map_add ex), mapX, Matrix.map_mul, Matrix.map_mul, de] at hh
    simpa only [Matrix.map_one ex (map_zero ex) (map_one ex)] using hh
  have ce : Commute d e := by
    change d * e = e * d
    have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ) => A.map ex) comm.eq
    simpa only [Matrix.map_mul, de] using hh
  let b : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ) := !![2, 0; 1, 0]
  let B := wordSeries 1 false • b
  let V (k : ℕ) : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ) :=
    (X ^ (k + 1) * wordSeries 1 false) • (e ^ (k + 1) * d ^ k * b)
  have pe (k : ℕ) : e ^ (k + 2) =
      e ^ (k + 1) + (X ^ 2 : PowerSeries ℤ) • (e ^ (k + 3) * d) := by
    calc
      e ^ (k + 2) = e ^ (k + 1) * e := by rw [pow_succ]
      _ = e ^ (k + 1) * (1 + (X ^ 2 : PowerSeries ℤ) • (e * e * d)) :=
        congrArg (e ^ (k + 1) * ·) ee
      _ = _ := by
        rw [mul_add, mul_one, Matrix.mul_smul]
        congr 1
        congr 1
        rw [← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_succ]
  have v0 : V 0 = (X : PowerSeries ℤ) • V 1 + (X : PowerSeries ℤ) • B := by
    dsimp [V, B]
    simp only [pow_zero, pow_one, mul_one]
    conv_lhs => rw [ee]
    rw [add_mul, one_mul, Matrix.smul_mul, smul_add, smul_smul]
    simp only [pow_two, smul_smul, mul_assoc]
    apply Matrix.ext
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have vs (k : ℕ) : V (k + 1) =
      (X : PowerSeries ℤ) • V (k + 2) + (X : PowerSeries ℤ) • (d * V k) := by
    have hm : d * (e ^ (k + 1) * d ^ k * b) = e ^ (k + 1) * d ^ (k + 1) * b := by
      rw [← mul_assoc, ← mul_assoc, (ce.pow_right (k + 1)).eq,
        mul_assoc (e ^ (k + 1)), ← pow_succ']
    have hd' : (e ^ (k + 3) * d) * d ^ (k + 1) * b =
        e ^ (k + 3) * d ^ (k + 2) * b := by
      rw [mul_assoc (e ^ (k + 3)), ← pow_succ']
    simp only [V, Nat.add_assoc, Matrix.mul_smul, hm]
    rw [pe k]
    simp only [add_mul, Matrix.smul_mul, hd', smul_add, smul_smul]
    simp only [pow_succ]
    apply Matrix.ext
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  let W (k : ℕ) : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ) :=
    !![wordSeries (k + 2) false, 0; wordSeries (k + 2) true, 0]
  obtain ⟨_, _, h2n, h2f, hbn, hbf, _⟩ := word_series_recursion
  have w0 : W 0 = (X : PowerSeries ℤ) • W 1 + (X : PowerSeries ℤ) • B := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    all_goals simp [W, B, b, smul_eq_mul]
    · linear_combination h2n
    · exact h2f
  have ws (k : ℕ) : W (k + 1) =
      (X : PowerSeries ℤ) • W (k + 2) + (X : PowerSeries ℤ) • (d * W k) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    all_goals simp [W, d, D, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul, Nat.add_assoc]
    · simpa [Nat.add_assoc] using hbn k
    · simpa [Nat.add_assoc] using hbf k
  have ma (l : ℕ) (A B : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ)) :
      mc l (A + B) = mc l A + mc l B := by
    ext i j
    change coeff l (A i j + B i j) = _
    rw [map_add]
    rfl
  have mx (l : ℕ) (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ)) :
      mc (l + 1) ((X : PowerSeries ℤ) • A) = mc l A := by
    ext i j
    simp [mc, Matrix.smul_apply, smul_eq_mul, coeff_succ_X_mul]
  have mz (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℤ)) :
      mc 0 ((X : PowerSeries ℤ) • A) = 0 := by
    ext i j
    simp [mc, Matrix.smul_apply, smul_eq_mul]
  have uniq : ∀ l k, mc l (W k) = mc l (V k) := by
    intro l
    induction l with
    | zero =>
      intro k
      cases k with
      | zero => rw [w0, v0, ma, ma, mz, mz, mz]
      | succ k => rw [ws, vs, ma, ma, mz, mz, mz, mz]
    | succ l ih =>
      intro k
      cases k with
      | zero => rw [w0, v0, ma, ma, mx, mx, mx, ih]
      | succ k => rw [ws, vs, ma, ma, mx, mx, mx, mx, dm, dm, ih, ih]
  have eqWV : W 0 = V 0 := by
    apply Matrix.ext
    intro i j
    apply PowerSeries.ext
    intro l
    exact congrFun (congrFun (uniq l 0) i) j
  have fib : ∀ k, (D ^ k) 0 0 = (Nat.fib (k + 1) : ℤ) ∧
      (D ^ k) 0 1 = (Nat.fib k : ℤ) := by
    intro k
    induction k with
    | zero => norm_num [D]
    | succ k ih =>
      rw [pow_succ]
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      rw [ih.1, ih.2]
      norm_num [D, Nat.fib_add_two, Nat.cast_add]
      ring
  have contract : 2 * E 0 0 + E 0 1 = hSeries := by
    apply PowerSeries.ext
    intro k
    have hf := fib k
    have hf3 : (Nat.fib (k + 3) : ℤ) =
        2 * (Nat.fib (k + 1) : ℤ) + (Nat.fib k : ℤ) := by
      rw [show k + 3 = (k + 1) + 2 by omega, Nat.fib_add_two,
        show k + 1 + 1 = k + 2 by omega, Nat.fib_add_two]
      push_cast
      ring
    simp only [two_mul, map_add, E, coeff_mk, hSeries, Nat.cast_mul, hf.1, hf.2, hf3]
    ring
  have ec : 2 * e 0 0 + e 0 1 = ex hSeries := by
    have hh := congrArg ex contract
    simpa [e, Matrix.map_apply, map_add, map_mul, map_ofNat] using hh
  have hh := congrFun (congrFun eqWV 0) 0
  simp [W, V, b, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two] at hh
  rw [← ec]
  linear_combination hh
end D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchings
