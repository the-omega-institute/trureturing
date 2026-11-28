/- GID: D5/S3/Matrix/HomogeneousWordPowersSingular
   generality: G
   mirror-B: none(waiver:covered-by-shitov-size-three-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Classification of eventually full singular size-three matrix spaces and the dimension estimates needed for the upper bound. -/

import D5.S3.Matrix.HomogeneousWordPowers

/-! Omega original.

Classification of eventually full singular size-three matrix spaces and the dimension estimates needed for the upper bound. -/

set_option autoImplicit false

open scoped Pointwise
open Matrix

namespace OmegaMath.HomogeneousWordPowers

variable {K : Type*} [Field K]

local notation "Mat" => Matrix (Fin 3) (Fin 3) K

private theorem no_common_kernel_of_positive_full (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) :
    ∀ v : Fin 3 → K, (∀ A ∈ L, A *ᵥ v = 0) → v = 0 := by
  intro v hv
  have hpow : ∀ n : ℕ, 0 < n → ∀ X ∈ L ^ n, X *ᵥ v = 0 := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
        rw [pow_succ]
        intro Z hZ
        refine Submodule.mul_induction_on hZ ?_ ?_
        · intro X hX Y hY
          rw [← Matrix.mulVec_mulVec, hv Y hY]
          simp
        · intro X Y hX hY
          rw [Matrix.add_mulVec, hX, hY, add_zero]
  obtain ⟨m, hm, htop⟩ := hfull
  have h1 : (1 : Mat) ∈ L ^ m := by rw [htop]; trivial
  simpa using hpow m hm 1 h1

private theorem no_common_cokernel_of_positive_full (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) :
    ∀ v : Fin 3 → K, (∀ A ∈ L, v ᵥ* A = 0) → v = 0 := by
  intro v hv
  have hpow : ∀ n : ℕ, 0 < n → ∀ X ∈ L ^ n, v ᵥ* X = 0 := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
        rw [pow_succ']
        intro Z hZ
        refine Submodule.mul_induction_on hZ ?_ ?_
        · intro X hX Y hY
          rw [← Matrix.vecMul_vecMul, hv X hX]
          simp
        · intro X Y hX hY
          rw [Matrix.vecMul_add, hX, hY, add_zero]
  obtain ⟨m, hm, htop⟩ := hfull
  have h1 : (1 : Mat) ∈ L ^ m := by rw [htop]; trivial
  simpa using hpow m hm 1 h1

/-- A positive full power has neither a common right kernel nor a common left kernel. -/
theorem eventually_full_reduced
    (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) :
    (∀ v : Fin 3 → K, (∀ A ∈ L, A *ᵥ v = 0) → v = 0) ∧
      (∀ v : Fin 3 → K, (∀ A ∈ L, v ᵥ* A = 0) → v = 0) := by
  exact ⟨no_common_kernel_of_positive_full L hfull,
    no_common_cokernel_of_positive_full L hfull⟩

/-- The rank-one branch is impossible as soon as its common-kernel/common-cokernel
    alternative has been established. -/
theorem exclude_rank_one_branch
    (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (hbranch :
      (∃ v : Fin 3 → K, v ≠ 0 ∧ ∀ A ∈ L, A *ᵥ v = 0) ∨
      (∃ v : Fin 3 → K, v ≠ 0 ∧ ∀ A ∈ L, v ᵥ* A = 0)) :
    False := by
  rcases hbranch with ⟨v, hv, hkill⟩ | ⟨v, hv, hkill⟩
  · exact hv (no_common_kernel_of_positive_full L hfull v hkill)
  · exact hv (no_common_cokernel_of_positive_full L hfull v hkill)

private theorem exists_diagonal_rank_normal_form (A : Mat) :
    ∃ P Q : Matˣ, (P : Mat) * A * (Q : Mat) =
      Matrix.diagonal (fun i : Fin 3 => if i.val < A.rank then 1 else 0) := by
  obtain ⟨V, U, e, hV, hU, hA⟩ := Matrix.exists_rank_normal_form A
  have hsize : A.rank + (Fintype.card (Fin 3) - A.rank) = 3 := by
    have hr := A.rank_le_width
    simp only [Fintype.card_fin]
    omega
  let f : Fin A.rank ⊕ Fin (Fintype.card (Fin 3) - A.rank) ≃ Fin 3 :=
    finSumFinEquiv.trans (finCongr hsize)
  let σ : Fin 3 ≃ Fin 3 := f.symm.trans e.symm
  let S : Mat := (1 : Mat).submatrix σ id
  let T : Mat := (1 : Mat).submatrix id σ
  have hST : S * T = 1 := by
    change (1 : Mat).submatrix σ (Equiv.refl _) * T = 1
    rw [Matrix.one_submatrix_mul]
    simp [T, Matrix.submatrix_submatrix]
  obtain ⟨P, hP⟩ := ((isUnit_iff_exists_inv).2 ⟨T, hST⟩).mul hV
  obtain ⟨Q, hQ⟩ := hU.mul ((isUnit_iff_exists_inv').2 ⟨S, hST⟩)
  refine ⟨P, Q, ?_⟩
  rw [hP, hQ, mul_assoc S V A, ← mul_assoc (S * (V * A)) U T,
    mul_assoc S (V * A) U]
  change (1 : Mat).submatrix σ (Equiv.refl _) * (V * A * U) *
    (1 : Mat).submatrix (Equiv.refl _) σ = _
  rw [Matrix.one_submatrix_mul, Matrix.mul_submatrix_one, hA]
  ext i j
  obtain ⟨i, rfl⟩ := f.surjective i
  obtain ⟨j, rfl⟩ := f.surjective j
  simp only [Matrix.submatrix_apply, Function.comp_apply, id_eq, Equiv.refl_symm,
    Equiv.refl_apply, σ, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
    Matrix.diagonal_apply, f.injective.eq_iff]
  rcases i with i | i <;> rcases j with j | j
  · simp [f, Matrix.one_apply, i.isLt]
  · simp [f]
  · simp [f]
  · simp [f, show ¬ A.rank + i.val < A.rank by omega]

/-- A size-three matrix subspace of upper rank one has a nonzero common right or left
kernel vector. The rank bound applies to every member of the subspace. -/
theorem rank_le_one_common_kernel_or_left_kernel (L : Submodule K Mat)
    (hrank : ∀ A ∈ L, A.rank ≤ 1) :
    (∃ v : Fin 3 → K, v ≠ 0 ∧ ∀ A ∈ L, A *ᵥ v = 0) ∨
    (∃ v : Fin 3 → K, v ≠ 0 ∧ ∀ A ∈ L, v ᵥ* A = 0) := by
  classical
  let v : Fin 3 → K := Pi.single (1 : Fin 3) 1
  have hv : v ≠ 0 := by
    intro h
    simpa [v] using congrFun h 1
  by_cases hex : ∃ A ∈ L, A ≠ 0
  swap
  · push Not at hex
    exact Or.inl ⟨v, hv, fun A hA => by simp [hex A hA]⟩
  obtain ⟨A, hA, hne⟩ := hex
  have hrA : A.rank = 1 := by
    have hpos : A.rank ≠ 0 := by
      intro hz
      rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at hz
      exact hne (Matrix.toLin'.injective (by simpa [Matrix.toLin'_apply'] using hz))
    have := hrank A hA
    omega
  obtain ⟨P, Q, hpivot⟩ := exists_diagonal_rank_normal_form A
  let e := (P.mulLeftLinearEquiv K Mat).trans (Q.mulRightLinearEquiv K)
  let M := L.map e.toLinearMap
  have he (B : Mat) : e B = (P : Mat) * B * (Q : Mat) := rfl
  let E : Mat := Matrix.diagonal (fun i : Fin 3 => if i.val < 1 then 1 else 0)
  have hE : E ∈ M := by
    refine Submodule.mem_map.mpr ⟨A, hA, ?_⟩
    change e A = E
    simpa only [he, E, hrA] using hpivot
  have hminor (B : Mat) (hB : B ∈ M) (i j : Fin 3) :
      B 0 0 * B i j - B 0 j * B i 0 = 0 := by
    obtain ⟨C, hC, rfl⟩ := Submodule.mem_map.mp hB
    have hr : (e C).rank ≤ 1 := by
      rw [he, Matrix.rank_mul_eq_left_of_isUnit_det, Matrix.rank_mul_eq_right_of_isUnit_det]
      · exact hrank C hC
      · exact (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
      · exact (Matrix.isUnit_iff_isUnit_det _).mp Q.isUnit
    let N := (e C).submatrix (![0, i] : Fin 2 → Fin 3) (![0, j] : Fin 2 → Fin 3)
    have hn : N.det = 0 := by
      by_contra h
      have hle := (Matrix.rank_submatrix_le (e C) (![0, i] : Fin 2 → Fin 3)
        (![0, j] : Fin 2 → Fin 3)).trans hr
      change N.rank ≤ 1 at hle
      rw [Matrix.rank_of_det_ne_zero h, Fintype.card_fin] at hle
      omega
    rw [Matrix.det_fin_two] at hn
    exact hn
  have hblock (B : Mat) (hB : B ∈ M) (i j : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) :
      B i j = 0 := by
    have h : (1 + B 0 0) * B i j - B 0 j * B i 0 = 0 := by
      simpa [E, Matrix.diagonal_apply, hi, Ne.symm hj] using
        hminor (E + B) (M.add_mem hE hB) i j
    linear_combination h - hminor B hB i j
  have hcross (B : Mat) (hB : B ∈ M) (i j : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) :
      B 0 j * B i 0 = 0 := by
    simpa [hblock B hB i j hi hj] using hminor B hB i j
  by_cases hrows : ∀ B ∈ M, ∀ i : Fin 3, i ≠ 0 → B i 0 = 0
  · refine Or.inr ⟨v ᵥ* (P : Mat), ?_, ?_⟩
    · intro h
      apply hv
      simpa [Matrix.vecMul_vecMul] using congrArg (fun w => w ᵥ* (↑P⁻¹ : Mat)) h
    · intro B hB
      have hmem : e B ∈ M := Submodule.mem_map.mpr ⟨B, hB, rfl⟩
      have hkill : v ᵥ* e B = 0 := by
        change Pi.single (1 : Fin 3) 1 ᵥ* e B = 0
        rw [Matrix.single_one_vecMul]
        funext j
        by_cases hj : j = 0
        · simpa [hj] using hrows (e B) hmem 1 (by decide)
        · exact hblock (e B) hmem 1 j (by decide) hj
      have hcancel := congrArg (fun w => w ᵥ* (↑Q⁻¹ : Mat)) hkill
      simpa only [he, Matrix.vecMul_vecMul, mul_assoc, Units.mul_inv, mul_one,
        Matrix.zero_vecMul] using hcancel
  · push Not at hrows
    obtain ⟨C, hC, i, hi, hCi⟩ := hrows
    have hcols (B : Mat) (hB : B ∈ M) (j : Fin 3) (hj : j ≠ 0) : B 0 j = 0 := by
      by_contra hBj
      have hCj := (mul_eq_zero.mp (hcross C hC i j hi hj)).resolve_right hCi
      have hBi := (mul_eq_zero.mp (hcross B hB i j hi hj)).resolve_left hBj
      have hsum := hcross (C + B) (M.add_mem hC hB) i j hi hj
      exact (mul_ne_zero hBj hCi) (by simpa [hCj, hBi] using hsum)
    refine Or.inl ⟨(Q : Mat) *ᵥ v, ?_, ?_⟩
    · intro h
      apply hv
      simpa [Matrix.mulVec_mulVec] using congrArg (fun w => (↑Q⁻¹ : Mat) *ᵥ w) h
    · intro B hB
      have hmem : e B ∈ M := Submodule.mem_map.mpr ⟨B, hB, rfl⟩
      have hkill : e B *ᵥ v = 0 := by
        change e B *ᵥ Pi.single (1 : Fin 3) 1 = 0
        rw [Matrix.mulVec_single_one]
        funext i
        by_cases hi : i = 0
        · simpa [hi] using hcols (e B) hmem 1 (by decide)
        · exact hblock (e B) hmem i 1 hi (by decide)
      have hcancel := congrArg (fun w => (↑P⁻¹ : Mat) *ᵥ w) hkill
      simpa only [he, Matrix.mulVec_mulVec, ← mul_assoc, Units.inv_mul, one_mul,
        Matrix.mulVec_zero] using hcancel

/-- An all-singular size-three subspace with a positive full power contains a rank-two matrix. -/
theorem exists_rank_two_of_eventually_full_of_det_eq_zero (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) (hsing : ∀ A ∈ L, A.det = 0) :
    ∃ A ∈ L, A.rank = 2 := by
  by_contra h
  apply exclude_rank_one_branch L hfull
  apply rank_le_one_common_kernel_or_left_kernel L
  intro A hA
  have htwo : A.rank ≠ 2 := fun hr => h ⟨A, hA, hr⟩
  have hthree : A.rank ≠ 3 := by
    intro hr
    have hsurj : Function.Surjective A.mulVec :=
      Matrix.mulVec_surjective_iff_rank_eq_card.mpr (by simpa using hr)
    have hunit := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
    have hdet := (Matrix.isUnit_iff_isUnit_det A).mp hunit
    exact hdet.ne_zero (hsing A hA)
  have hwidth := A.rank_le_width
  omega

/-- Normalizing a rank-two pivot in an all-singular space over an infinite field gives
the bottom-right, quadratic, and cubic constraints for every normalized member. -/
theorem rank_two_pencil_constraints [Infinite K] (L : Submodule K Mat)
    (hsing : ∀ B ∈ L, B.det = 0) {A : Mat} (hA : A ∈ L) (hrank : A.rank = 2) :
    ∃ P Q : Matˣ, (P : Mat) * A * (Q : Mat) =
        Matrix.diagonal (fun i : Fin 3 => if i.val < 2 then 1 else 0) ∧
      ∀ B ∈ L,
        let M := (P : Mat) * B * (Q : Mat)
        let U : Matrix (Fin 2) (Fin 2) K := M.submatrix Fin.castSucc Fin.castSucc
        let u : Fin 2 → K := fun i => M i.castSucc 2
        let v : Fin 2 → K := fun j => M 2 j.castSucc
        M 2 2 = 0 ∧ v ⬝ᵥ u = 0 ∧ v ⬝ᵥ (U *ᵥ u) = 0 := by
  obtain ⟨P, Q, hPQ⟩ := exists_diagonal_rank_normal_form A
  let D : Mat := Matrix.diagonal (fun i : Fin 3 => if i.val < 2 then 1 else 0)
  let e := (P.mulLeftLinearEquiv K Mat).trans (Q.mulRightLinearEquiv K)
  have hD : e A = D := by
    change (P : Mat) * A * (Q : Mat) = D
    simpa only [D, hrank] using hPQ
  refine ⟨P, Q, hD, ?_⟩
  intro B hB M U u v
  have heB : e B = M := rfl
  have hdet (t : K) : (D + t • M).det = 0 := by
    rw [← hD, ← heB, ← map_smul, ← map_add]
    change ((P : Mat) * (A + t • B) * (Q : Mat)).det = 0
    simp [Matrix.det_mul, hsing _ (L.add_mem hA (L.smul_mem t hB))]
  let d := M 2 2
  let traceU := M 0 0 + M 1 1
  let detU := M 0 0 * M 1 1 - M 0 1 * M 1 0
  let vu := M 2 0 * M 0 2 + M 2 1 * M 1 2
  let vUu := M 2 0 * (M 0 0 * M 0 2 + M 0 1 * M 1 2) +
    M 2 1 * (M 1 0 * M 0 2 + M 1 1 * M 1 2)
  let p := Polynomial.C d * Polynomial.X + Polynomial.C (d * traceU - vu) * Polynomial.X ^ 2 +
    Polynomial.C (d * detU - traceU * vu + vUu) * Polynomial.X ^ 3
  have hp : p = 0 := by
    apply Polynomial.zero_of_eval_zero
    intro t
    calc
      p.eval t = (D + t • M).det := by
        rw [Matrix.det_fin_three]
        simp only [p, Polynomial.eval_add, Polynomial.eval_C_mul, Polynomial.eval_X,
          Polynomial.eval_X_pow, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        norm_num [D, Matrix.diagonal_apply, d, traceU, detU, vu, vUu]
        ring
      _ = 0 := hdet t
  have hd : d = 0 := by
    have h : p.coeff 1 = 0 := by rw [hp, Polynomial.coeff_zero]
    norm_num only [p, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, if_true, if_false, add_zero] at h
    exact h
  have hvu : vu = 0 := by
    have h : p.coeff 2 = 0 := by rw [hp, Polynomial.coeff_zero]
    norm_num only [p, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, if_true, if_false, add_zero, zero_add, hd, zero_mul,
      zero_sub] at h
    exact neg_eq_zero.mp h
  have hvUu : vUu = 0 := by
    have h : p.coeff 3 = 0 := by rw [hp, Polynomial.coeff_zero]
    norm_num only [p, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, if_true, if_false, zero_add, hd, hvu, zero_mul,
      mul_zero, sub_zero] at h
    exact h
  refine ⟨hd, ?_, ?_⟩
  · rw [dotProduct, Fin.sum_univ_two]
    exact hvu
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact hvUu

private abbrev pencilColumn (B : Mat) : Fin 2 → K := ![B 0 2, B 1 2]

private abbrev pencilRow (B : Mat) : Fin 2 → K := ![B 2 0, B 2 1]

private abbrev pencilBlock (B : Mat) : Matrix (Fin 2) (Fin 2) K :=
  B.submatrix Fin.castSucc Fin.castSucc

private theorem pencil_polarization (M : Submodule K Mat)
    (hquad : ∀ B ∈ M, pencilRow B ⬝ᵥ pencilColumn B = 0)
    {B C : Mat} (hB : B ∈ M) (hC : C ∈ M) :
    pencilRow B ⬝ᵥ pencilColumn C + pencilRow C ⬝ᵥ pencilColumn B = 0 := by
  have h := hquad (B + C) (M.add_mem hB hC)
  simp only [pencilColumn, pencilRow, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.add_apply] at *
  linear_combination h - hquad B hB - hquad C hC

private theorem fin_two_exists_smul_of_cross_eq_zero {a z : Fin 2 → K} (ha : a ≠ 0)
    (h : a 0 * z 1 - a 1 * z 0 = 0) : ∃ s : K, s • a = z := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  refine ⟨z i / a i, ?_⟩
  ext j
  fin_cases i <;> fin_cases j <;> simp only [Pi.smul_apply, smul_eq_mul] at *
  · exact div_mul_cancel₀ _ hi
  · change z 0 / a 0 * a 1 = z 1
    change a 0 ≠ 0 at hi
    rw [div_mul_eq_mul_div₀, div_eq_iff hi]
    linear_combination -h
  · change z 1 / a 1 * a 0 = z 0
    change a 1 ≠ 0 at hi
    rw [div_mul_eq_mul_div₀, div_eq_iff hi]
    linear_combination h
  · exact div_mul_cancel₀ _ hi

private theorem normalized_pencil_compression [Infinite K] (M : Submodule K Mat)
    (hdiag : ∀ B ∈ M, B 2 2 = 0)
    (hcube : ∀ B ∈ M, pencilRow B ⬝ᵥ (pencilBlock B *ᵥ pencilColumn B) = 0)
    (hu : ∃ B ∈ M, pencilColumn B ≠ 0) (hv : ∃ B ∈ M, pencilRow B ≠ 0)
    {a : Fin 2 → K} (ha : a ≠ 0)
    (hcol : ∀ B ∈ M, a 0 * B 1 2 - a 1 * B 0 2 = 0)
    (hrow : ∀ B ∈ M, B 2 0 * a 0 + B 2 1 * a 1 = 0) :
    ∃ H D : Submodule K (Fin 3 → K),
      Module.finrank K H = 2 ∧ Module.finrank K D = 1 ∧
      ∀ B ∈ M, ∀ z ∈ H, B *ᵥ z ∈ D := by
  let w : Fin 2 → K := ![-a 1, a 0]
  have hw : w ≠ 0 := by
    intro h
    apply ha
    have h0 : a 1 = 0 := by simpa [w] using congrFun h 0
    have h1 : a 0 = 0 := by simpa [w] using congrFun h 1
    funext k
    fin_cases k
    · exact h1
    · exact h0
  have hcol' (B : Mat) (hB : B ∈ M) : ∃ x : K, x • a = pencilColumn B :=
    fin_two_exists_smul_of_cross_eq_zero ha (hcol B hB)
  have hrow' (B : Mat) (hB : B ∈ M) : ∃ y : K, y • w = pencilRow B :=
    fin_two_exists_smul_of_cross_eq_zero hw (by
      simp only [w, pencilRow, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination -hrow B hB)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  let f := Matrix.entryLinearMap K K i.castSucc (2 : Fin 3)
  let g := Matrix.entryLinearMap K K (2 : Fin 3) j.castSucc
  have hf (B : Mat) : f B = pencilColumn B i := by fin_cases i <;> rfl
  have hg (B : Mat) : g B = pencilRow B j := by fin_cases j <;> rfl
  let k : Module.Dual K Mat :=
    (w 0 * a 0) • Matrix.entryLinearMap K K 0 0 +
    (w 0 * a 1) • Matrix.entryLinearMap K K 0 1 +
    (w 1 * a 0) • Matrix.entryLinearMap K K 1 0 +
    (w 1 * a 1) • Matrix.entryLinearMap K K 1 1
  have hk (B : Mat) : k B = w 0 * (B 0 0 * a 0 + B 0 1 * a 1) +
      w 1 * (B 1 0 * a 0 + B 1 1 * a 1) := by
    simp [k]
    ring
  have hfne : ∃ B ∈ M, f B ≠ 0 := by
    obtain ⟨B, hB, hne⟩ := hu
    obtain ⟨x, hx⟩ := hcol' B hB
    have hxne : x ≠ 0 := by rintro rfl; exact hne (by simpa using hx.symm)
    refine ⟨B, hB, ?_⟩
    rw [hf, ← hx, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hxne hi
  have hgne : ∃ B ∈ M, g B ≠ 0 := by
    obtain ⟨B, hB, hne⟩ := hv
    obtain ⟨y, hy⟩ := hrow' B hB
    have hyne : y ≠ 0 := by rintro rfl; exact hne (by simpa using hy.symm)
    refine ⟨B, hB, ?_⟩
    rw [hg, ← hy, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hyne hj
  -- The cubic identity rules out a point where all three linear forms are nonzero.
  have hkzero (B : Mat) (hB : B ∈ M) : k B = 0 := by
    by_contra hne
    let forms : Fin 3 → Module.Dual K Mat := ![f, g, k]
    have hforms : ∀ n, ∃ X ∈ M, forms n X ≠ 0 := by
      intro n
      fin_cases n
      · exact hfne
      · exact hgne
      · exact ⟨B, hB, hne⟩
    obtain ⟨X, hX, hall⟩ :=
      Module.Dual.exists_forall_mem_ne_zero_of_forall_exists M forms hforms
    obtain ⟨x, hx⟩ := hcol' X hX
    obtain ⟨y, hy⟩ := hrow' X hX
    have hxne : x ≠ 0 := by
      rintro rfl
      exact hall 0 (by rw [show forms 0 = f from rfl, hf, ← hx]; simp)
    have hyne : y ≠ 0 := by
      rintro rfl
      exact hall 1 (by rw [show forms 1 = g from rfl, hg, ← hy]; simp)
    have hc := hcube X hX
    rw [← hx, ← hy, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, smul_eq_mul] at hc
    have hval : w ⬝ᵥ (pencilBlock X *ᵥ a) = k X := by
      rw [hk]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rfl
    rw [hval] at hc
    exact (mul_ne_zero hxne (mul_ne_zero hyne (hall 2))) hc
  let a₃ : Fin 3 → K := ![a 0, a 1, 0]
  let e₃ : Fin 3 → K := Pi.single 2 1
  let H := Submodule.span K (Set.range (![a₃, e₃] : Fin 2 → Fin 3 → K))
  let D := Submodule.span K ({a₃} : Set (Fin 3 → K))
  have ha₃ : a₃ ≠ 0 := by
    intro h
    apply hi
    have he := congrFun h i.castSucc
    fin_cases i <;> exact he
  have hind : LinearIndependent K (![a₃, e₃] : Fin 2 → Fin 3 → K) := by
    apply (LinearIndependent.pair_iff' ha₃).2
    intro s h
    have he := congrFun h (2 : Fin 3)
    simp [a₃, e₃] at he
  refine ⟨H, D, by simpa [H] using finrank_span_eq_card hind, finrank_span_singleton ha₃, ?_⟩
  intro B hB
  have hea : B *ᵥ a₃ ∈ D := by
    let z := pencilBlock B *ᵥ a
    have hz : a 0 * z 1 - a 1 * z 0 = 0 := by
      have h := hkzero B hB
      rw [hk] at h
      simp only [z, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      change a 0 * (B 1 0 * a 0 + B 1 1 * a 1) -
        a 1 * (B 0 0 * a 0 + B 0 1 * a 1) = 0
      simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one] at h
      linear_combination h
    obtain ⟨s, hs⟩ := fin_two_exists_smul_of_cross_eq_zero ha hz
    apply Submodule.mem_span_singleton.mpr
    refine ⟨s, ?_⟩
    ext n
    fin_cases n
    · have he := congrFun hs 0
      simpa [a₃, z, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three] using he
    · have he := congrFun hs 1
      simpa [a₃, z, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three] using he
    · simpa [a₃, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using (hrow B hB).symm
  have hee : B *ᵥ e₃ ∈ D := by
    obtain ⟨s, hs⟩ := hcol' B hB
    apply Submodule.mem_span_singleton.mpr
    refine ⟨s, ?_⟩
    rw [show e₃ = Pi.single (2 : Fin 3) 1 from rfl, Matrix.mulVec_single_one]
    ext n
    fin_cases n
    · simpa [a₃, pencilColumn] using congrFun hs 0
    · simpa [a₃, pencilColumn] using congrFun hs 1
    · simpa [a₃] using (hdiag B hB).symm
  have hle : H ≤ D.comap B.mulVecLin := by
    apply Submodule.span_le.mpr
    rintro v ⟨n, rfl⟩
    fin_cases n
    · exact hea
    · exact hee
  exact fun z hz => hle hz

private abbrev rankTwoPivot : Mat :=
  Matrix.diagonal (fun i : Fin 3 => if i.val < 2 then 1 else 0)

private theorem normalized_pencil_alternating [NeZero (2 : K)] (M : Submodule K Mat)
    (hA : rankTwoPivot ∈ M)
    (hdiag : ∀ B ∈ M, B 2 2 = 0)
    (hquad : ∀ B ∈ M, pencilRow B ⬝ᵥ pencilColumn B = 0)
    (hcube : ∀ B ∈ M, pencilRow B ⬝ᵥ (pencilBlock B *ᵥ pencilColumn B) = 0)
    (hv : ∃ B ∈ M, pencilRow B ≠ 0)
    (hsurj : ∀ x y : K, ∃ B ∈ M, B 0 2 = x ∧ B 1 2 = y) :
    ∃ P Q : Matˣ, ∀ C : Mat, C.transpose = -C ↔
      ∃ B ∈ M, (P : Mat) * B * (Q : Mat) = C := by
  obtain ⟨X, hX, hx₀, hx₁⟩ := hsurj 1 0
  obtain ⟨Y, hY, hy₀, hy₁⟩ := hsurj 0 1
  have hpol (B C : Mat) (hB : B ∈ M) (hC : C ∈ M) :
      B 2 0 * C 0 2 + B 2 1 * C 1 2 + (C 2 0 * B 0 2 + C 2 1 * B 1 2) = 0 := by
    simpa only [pencilColumn, pencilRow, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] using pencil_polarization M hquad hB hC
  have hX20 : X 2 0 = 0 := by
    simpa [pencilColumn, pencilRow, dotProduct, Fin.sum_univ_two, hx₀, hx₁] using hquad X hX
  have hY21 : Y 2 1 = 0 := by
    simpa [pencilColumn, pencilRow, dotProduct, Fin.sum_univ_two, hy₀, hy₁] using hquad Y hY
  let c := X 2 1
  have hY20 : Y 2 0 = -c := by
    have h := hpol X Y hX hY
    simp [hx₀, hx₁, hy₀, hy₁] at h
    dsimp [c]
    linear_combination h
  have hrow (B : Mat) (hB : B ∈ M) :
      B 2 0 = -c * B 1 2 ∧ B 2 1 = c * B 0 2 := by
    have h0 := hpol B X hB hX
    have h1 := hpol B Y hB hY
    simp [hx₀, hx₁, hX20] at h0
    simp [hy₀, hy₁, hY20, hY21] at h1
    constructor
    · dsimp [c]
      linear_combination h0
    · linear_combination h1
  have hc : c ≠ 0 := by
    obtain ⟨B, hB, hn⟩ := hv
    intro h
    obtain ⟨h0, h1⟩ := hrow B hB
    exact hn (by ext i; fin_cases i <;> simp [pencilRow, h0, h1, h])
  have hpoly (B : Mat) (hB : B ∈ M) :
      B 1 0 * B 0 2 ^ 2 + (B 1 1 - B 0 0) * B 0 2 * B 1 2 -
        B 0 1 * B 1 2 ^ 2 = 0 := by
    obtain ⟨h0, h1⟩ := hrow B hB
    have h := hcube B hB
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
    change B 2 0 * (B 0 0 * B 0 2 + B 0 1 * B 1 2) +
      B 2 1 * (B 1 0 * B 0 2 + B 1 1 * B 1 2) = 0 at h
    rw [h0, h1] at h
    apply (mul_eq_zero.mp (show c * _ = 0 from ?_)).resolve_left hc
    linear_combination h
  -- Adding a zero-column member to the three test columns forces its block to be scalar.
  have hker (B : Mat) (hB : B ∈ M) (h0 : B 0 2 = 0) (h1 : B 1 2 = 0) :
      B 1 0 = 0 ∧ B 0 1 = 0 ∧ B 0 0 = B 1 1 := by
    have h10 : B 1 0 = 0 := by
      have h := hpoly (X + B) (M.add_mem hX hB)
      simp [Matrix.add_apply, hx₀, hx₁, h0, h1] at h
      have hx := hpoly X hX
      simp [hx₀, hx₁] at hx
      linear_combination h - hx
    have h01 : B 0 1 = 0 := by
      have h := hpoly (Y + B) (M.add_mem hY hB)
      simp [Matrix.add_apply, hy₀, hy₁, h0, h1] at h
      have hy := hpoly Y hY
      simp [hy₀, hy₁] at hy
      linear_combination -h - hy
    refine ⟨h10, h01, ?_⟩
    have h := hpoly (X + Y + B) (M.add_mem (M.add_mem hX hY) hB)
    have hxy := hpoly (X + Y) (M.add_mem hX hY)
    simp [Matrix.add_apply, hx₀, hx₁, hy₀, hy₁, h0, h1, h10, h01] at h hxy
    linear_combination hxy - h
  let b₀ := X 0 0 - X 1 1
  let b₁ := X 0 1
  have hX10 : X 1 0 = 0 := by simpa [hx₀, hx₁] using hpoly X hX
  have hY01 : Y 0 1 = 0 := by simpa [hy₀, hy₁] using hpoly Y hY
  have hYparams : Y 1 0 = b₀ ∧ Y 1 1 - Y 0 0 = b₁ := by
    have hp := hpoly (X + Y) (M.add_mem hX hY)
    have hm := hpoly (X - Y) (M.sub_mem hX hY)
    simp [Matrix.add_apply, Matrix.sub_apply, hx₀, hx₁, hy₀, hy₁, hX10, hY01] at hp hm
    constructor
    · apply sub_eq_zero.mp
      apply (mul_eq_zero.mp (show (2 : K) * _ = 0 from ?_)).resolve_left two_ne_zero
      dsimp [b₀]
      linear_combination hp - hm
    · apply sub_eq_zero.mp
      apply (mul_eq_zero.mp (show (2 : K) * _ = 0 from ?_)).resolve_left two_ne_zero
      dsimp [b₁]
      linear_combination hp + hm
  have hblock (B : Mat) (hB : B ∈ M) :
      B 1 0 = B 1 2 * b₀ ∧ B 0 1 = B 0 2 * b₁ ∧
      B 0 0 - B 1 1 = B 0 2 * b₀ - B 1 2 * b₁ := by
    let C := B - B 0 2 • X - B 1 2 • Y
    have hC : C ∈ M := M.sub_mem (M.sub_mem hB (M.smul_mem _ hX)) (M.smul_mem _ hY)
    have hc0 : C 0 2 = 0 := by simp [C, Matrix.sub_apply, Matrix.smul_apply, hx₀, hy₀]
    have hc1 : C 1 2 = 0 := by simp [C, Matrix.sub_apply, Matrix.smul_apply, hx₁, hy₁]
    obtain ⟨h10, h01, hd⟩ := hker C hC hc0 hc1
    simp only [C, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h10 h01 hd
    refine ⟨?_, ?_, ?_⟩
    · simpa [hX10, hYparams.1, sub_eq_zero] using h10
    · simpa [hY01, b₁, sub_eq_zero] using h01
    · dsimp [b₀, b₁]
      linear_combination hd - B 1 2 * hYparams.2
  let S : Mat := !![0, 1, 0; -1, 0, 0; 0, 0, c⁻¹]
  let T : Mat := !![1, 0, 0; 0, 1, 0; -b₀, -b₁, 1]
  have hS : IsUnit S := by
    apply (Matrix.isUnit_iff_isUnit_det S).mpr
    simpa [S, Matrix.det_fin_three] using (inv_ne_zero hc).isUnit
  have hT : IsUnit T := by
    apply (Matrix.isUnit_iff_isUnit_det T).mpr
    simp [T, Matrix.det_fin_three]
  obtain ⟨P, hP⟩ := hS
  obtain ⟨Q, hQ⟩ := hT
  let skew (s x y : K) : Mat := !![0, s, y; -s, 0, -x; -y, x, 0]
  have hskew (s x y : K) : (skew s x y).transpose = -skew s x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skew, Matrix.transpose_apply]
  let scalar (B : Mat) := B 1 1 - B 1 2 * b₁
  have htransform (B : Mat) (hB : B ∈ M) :
      S * B * T = skew (scalar B) (B 0 2) (B 1 2) := by
    obtain ⟨h10, h01, hdiff⟩ := hblock B hB
    obtain ⟨h20, h21⟩ := hrow B hB
    have h00 : B 0 0 = B 1 1 + (B 0 2 * b₀ - B 1 2 * b₁) := by
      linear_combination hdiff
    have hd := hdiag B hB
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
      simp [S, T, scalar, skew, h00, h10, h01, h20, h21, hd, ← mul_assoc, hc] <;> ring
  refine ⟨P, Q, fun C => ⟨?_, ?_⟩⟩
  · intro hC
    have hc (i j : Fin 3) : C j i = -C i j := congr_fun (congr_fun hC i) j
    have hz (i : Fin 3) : C i i = 0 := by
      apply (mul_eq_zero.mp (show (2 : K) * C i i = 0 from ?_)).resolve_left two_ne_zero
      linear_combination hc i i
    have hshape : C = skew (C 0 1) (-C 1 2) (C 0 2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [skew, hz, hc 0 1, hc 0 2, hc 1 2]
    let x := -C 1 2
    let y := C 0 2
    let t := C 0 1 - x * scalar X - y * scalar Y
    let B := x • X + y • Y + t • (rankTwoPivot : Mat)
    have hB : B ∈ M := M.add_mem (M.add_mem (M.smul_mem x hX) (M.smul_mem y hY))
      (M.smul_mem t hA)
    refine ⟨B, hB, ?_⟩
    have hb₀ : B 0 2 = x := by
      simp [B, Matrix.add_apply, Matrix.smul_apply, rankTwoPivot, hx₀, hy₀]
    have hb₁ : B 1 2 = y := by
      simp [B, Matrix.add_apply, Matrix.smul_apply, rankTwoPivot, hx₁, hy₁]
    have hs : scalar B = C 0 1 := by
      simp [scalar, B, t, Matrix.add_apply, Matrix.smul_apply,
        rankTwoPivot, hx₁, hy₁]
      ring
    rw [hP, hQ, htransform B hB, hb₀, hb₁, hs]
    exact hshape.symm
  · rintro ⟨B, hB, rfl⟩
    rw [hP, hQ, htransform B hB]
    exact hskew _ _ _

private def unitMulVecEquiv (P : Matˣ) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) :=
  LinearEquiv.ofLinearMap (f := (P : Mat).mulVecLin) (g := (↑P⁻¹ : Mat).mulVecLin)
    (by rw [← Matrix.mulVecLin_mul, Units.mul_inv, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, Units.inv_mul, Matrix.mulVecLin_one])

/-- An all-singular subspace of size-three matrices with a positive full power either
maps a fixed plane into a fixed line, or is equivalent under independent invertible
left and right multiplication to the whole skew-symmetric matrix space. -/
theorem singular_space_classification [Infinite K] [NeZero (2 : K)] (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) (hsing : ∀ B ∈ L, B.det = 0) :
    (∃ H D : Submodule K (Fin 3 → K),
      Module.finrank K H = 2 ∧ Module.finrank K D = 1 ∧
      ∀ B ∈ L, ∀ z ∈ H, B *ᵥ z ∈ D) ∨
    (∃ P Q : Matˣ, ∀ C : Mat, C.transpose = -C ↔
      ∃ B ∈ L, (P : Mat) * B * (Q : Mat) = C) := by
  classical
  obtain ⟨A, hA, hrank⟩ := exists_rank_two_of_eventually_full_of_det_eq_zero L hfull hsing
  obtain ⟨P, Q, hPQ, hconstraints⟩ := rank_two_pencil_constraints L hsing hA hrank
  let e := (P.mulLeftLinearEquiv K Mat).trans (Q.mulRightLinearEquiv K)
  let M := L.map e.toLinearMap
  have he (B : Mat) : e B = (P : Mat) * B * (Q : Mat) := rfl
  have hM (B : Mat) (hB : B ∈ L) : e B ∈ M := Submodule.mem_map.mpr ⟨B, hB, rfl⟩
  have hPivot : (rankTwoPivot : Mat) ∈ M := by
    have h : e A = rankTwoPivot := (he A).trans hPQ
    rw [← h]
    exact hM A hA
  have hnorm (B : Mat) (hB : B ∈ M) :
      B 2 2 = 0 ∧ pencilRow B ⬝ᵥ pencilColumn B = 0 ∧
      pencilRow B ⬝ᵥ (pencilBlock B *ᵥ pencilColumn B) = 0 := by
    obtain ⟨C, hC, rfl⟩ := Submodule.mem_map.mp hB
    have hcol (B : Mat) : (fun i : Fin 2 => B i.castSucc 2) = pencilColumn B := by
      funext i
      fin_cases i <;> rfl
    have hrow (B : Mat) : (fun i : Fin 2 => B 2 i.castSucc) = pencilRow B := by
      funext i
      fin_cases i <;> rfl
    change (e C) 2 2 = 0 ∧ pencilRow (e C) ⬝ᵥ pencilColumn (e C) = 0 ∧
      pencilRow (e C) ⬝ᵥ (pencilBlock (e C) *ᵥ pencilColumn (e C)) = 0
    simpa only [he, hcol, hrow] using hconstraints C hC
  have hd (B : Mat) (hB : B ∈ M) := (hnorm B hB).1
  have hquad (B : Mat) (hB : B ∈ M) := (hnorm B hB).2.1
  have hcube (B : Mat) (hB : B ∈ M) := (hnorm B hB).2.2
  let z : Fin 3 → K := Pi.single 2 1
  have hz : z ≠ 0 := by intro h; simpa [z] using congrFun h 2
  have hu : ∃ B ∈ M, pencilColumn B ≠ 0 := by
    by_contra! h
    have hk : ∀ B ∈ L, B *ᵥ ((Q : Mat) *ᵥ z) = 0 := by
      intro B hB
      have hc := h (e B) (hM B hB)
      have h0 : e B 0 2 = 0 := congrFun hc 0
      have h1 : e B 1 2 = 0 := congrFun hc 1
      have hkill : e B *ᵥ z = 0 := by
        rw [show z = Pi.single (2 : Fin 3) 1 from rfl, Matrix.mulVec_single_one]
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact hd (e B) (hM B hB)
      have hcancel := congrArg (fun w => (↑P⁻¹ : Mat) *ᵥ w) hkill
      simpa only [he, Matrix.mulVec_mulVec, ← mul_assoc, Units.inv_mul, one_mul,
        Matrix.mulVec_zero] using hcancel
    have hcancel := congrArg (fun w => (↑Q⁻¹ : Mat) *ᵥ w)
      (no_common_kernel_of_positive_full L hfull _ hk)
    exact hz (by simpa [Matrix.mulVec_mulVec] using hcancel)
  have hv : ∃ B ∈ M, pencilRow B ≠ 0 := by
    by_contra! h
    have hk : ∀ B ∈ L, (z ᵥ* (P : Mat)) ᵥ* B = 0 := by
      intro B hB
      have hc := h (e B) (hM B hB)
      have h0 : e B 2 0 = 0 := congrFun hc 0
      have h1 : e B 2 1 = 0 := congrFun hc 1
      have hkill : z ᵥ* e B = 0 := by
        rw [show z = Pi.single (2 : Fin 3) 1 from rfl, Matrix.single_one_vecMul]
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact hd (e B) (hM B hB)
      have hcancel := congrArg (fun w => w ᵥ* (↑Q⁻¹ : Mat)) hkill
      simpa only [he, Matrix.vecMul_vecMul, mul_assoc, Units.mul_inv, mul_one,
        Matrix.zero_vecMul] using hcancel
    have hcancel := congrArg (fun w => w ᵥ* (↑P⁻¹ : Mat))
      (no_common_cokernel_of_positive_full L hfull _ hk)
    exact hz (by simpa [Matrix.vecMul_vecMul] using hcancel)
  by_cases hsurj : ∀ x y : K, ∃ B ∈ M, B 0 2 = x ∧ B 1 2 = y
  · obtain ⟨S, T, hST⟩ := normalized_pencil_alternating M hPivot hd hquad hcube hv hsurj
    refine Or.inr ⟨S * P, Q * T, fun C => ?_⟩
    rw [hST C]
    constructor
    · rintro ⟨B, hB, h⟩
      obtain ⟨B₀, hB₀, rfl⟩ := Submodule.mem_map.mp hB
      change (S : Mat) * e B₀ * (T : Mat) = C at h
      exact ⟨B₀, hB₀, by simpa only [he, Units.val_mul, mul_assoc] using h⟩
    · rintro ⟨B, hB, h⟩
      exact ⟨e B, hM B hB, by simpa only [he, Units.val_mul, mul_assoc] using h⟩
  · obtain ⟨X, hX, hx⟩ := hu
    let a := pencilColumn X
    have hc (B : Mat) (hB : B ∈ M) : a 0 * B 1 2 - a 1 * B 0 2 = 0 := by
      by_contra! h
      apply hsurj
      intro x y
      let Δ := a 0 * B 1 2 - a 1 * B 0 2
      let s := (x * B 1 2 - y * B 0 2) / Δ
      let t := (a 0 * y - a 1 * x) / Δ
      refine ⟨s • X + t • B, M.add_mem (M.smul_mem s hX) (M.smul_mem t hB), ?_, ?_⟩
      · change s * a 0 + t * B 0 2 = x
        dsimp [s, t]
        field_simp [show Δ ≠ 0 from h]
        dsimp [Δ]
        ring
      · change s * a 1 + t * B 1 2 = y
        dsimp [s, t]
        field_simp [show Δ ≠ 0 from h]
        dsimp [Δ]
        ring
    have hvu (B : Mat) (hB : B ∈ M) : B 2 0 * a 0 + B 2 1 * a 1 = 0 := by
      obtain ⟨s, hs⟩ := fin_two_exists_smul_of_cross_eq_zero hx (z := pencilColumn B) (hc B hB)
      have h := pencil_polarization M hquad hB hX
      rw [← hs, dotProduct_smul, show pencilRow X ⬝ᵥ a = 0 from hquad X hX,
        smul_zero, add_zero] at h
      simpa [a, pencilRow, dotProduct, Fin.sum_univ_two] using h
    obtain ⟨H, D, hH, hD, hmap⟩ :=
      normalized_pencil_compression M hd hcube ⟨X, hX, hx⟩ hv hx hc hvu
    let q := unitMulVecEquiv Q
    let p := unitMulVecEquiv P⁻¹
    refine Or.inl ⟨H.map q.toLinearMap, D.map p.toLinearMap,
      (q.finrank_map_eq H).trans hH, (p.finrank_map_eq D).trans hD, ?_⟩
    intro B hB w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    refine Submodule.mem_map.mpr ⟨e B *ᵥ v, hmap (e B) (hM B hB) v hv, ?_⟩
    change (↑P⁻¹ : Mat) *ᵥ (e B *ᵥ v) = B *ᵥ ((Q : Mat) *ᵥ v)
    rw [he, Matrix.mulVec_mulVec, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul,
      ← Matrix.mulVec_mulVec]

end OmegaMath.HomogeneousWordPowers
