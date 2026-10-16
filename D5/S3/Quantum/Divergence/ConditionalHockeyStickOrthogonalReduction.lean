/- GID: D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Conditional hockey-stick ratios admit an orthogonal reduction independent of gamma. -/

import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Information.PartialTraceMutualInformation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction

open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation

def IsState {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : Prop := X.PosSemidef ∧ X.trace = 1

private def rt {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : ℝ := X.trace.re

def posTrace {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : ℝ := rt (X⁺)

def E {n : Type*} [Fintype n] [DecidableEq n]
    (γ : ℝ) (ρ σ : Matrix n n ℂ) : ℝ := posTrace (ρ - γ • σ)

private def ptr {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A]
    (X : Matrix (R × A) (R × A) ℂ) : Matrix R R ℂ := partialTraceRight X

noncomputable def amp {A B R : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) (X : Matrix (R × A) (R × A) ℂ) : Matrix (R × B) (R × B) ℂ :=
  CStarMatrix.ofMatrix.symm
    (referenceLinear N (CStarMatrix.ofMatrix X))

def gap {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A]
    (γ : ℝ) (ρ σ : Matrix (R × A) (R × A) ℂ) : ℝ :=
  E γ ρ σ - E γ (ptr ρ) (ptr σ)

noncomputable def ratios
    {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) (γ : ℝ) (orth : Bool) : Set ℝ :=
  {x | ∃ (R : Type) (fR : Fintype R) (dR : DecidableEq R),
      letI := fR
      letI := dR
      ∃ ρ σ : Matrix (R × A) (R × A) ℂ,
        IsState ρ ∧ IsState σ ∧
        (orth = true → ρ * σ = 0) ∧
        0 < gap γ ρ σ ∧
        x = gap γ (amp N ρ) (amp N σ) / gap γ ρ σ}

private theorem state_nonempty {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : IsState X) : Nonempty n := by
  classical
  by_contra hn
  haveI : IsEmpty n := not_nonempty_iff.mp hn
  have hz : X.trace = 0 := by simp [Matrix.trace]
  exact one_ne_zero (hX.2.symm.trans hz)

private theorem rt_nonneg_psd {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.PosSemidef) : 0 ≤ rt X := by
  rw [rt, hX.isHermitian.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum, Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => hX.eigenvalues_nonneg i

private theorem posTrace_smul {n : Type*} [Fintype n] [DecidableEq n]
    (c : ℝ) (hc : 0 ≤ c) (X : Matrix n n ℂ) :
    posTrace (c • X) = c * posTrace X := by
  unfold posTrace rt
  rw [CFC.posPart_smul_of_nonneg hc, Matrix.trace_smul]
  simp [Complex.mul_re]

private theorem posTrace_psd {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.PosSemidef) : posTrace X = rt X := by
  rw [posTrace, (CFC.posPart_eq_self X).mpr hX.nonneg]

private theorem posTrace_neg_psd {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.PosSemidef) : posTrace (-X) = 0 := by
  rw [posTrace]
  have hz : (-X)⁺ = 0 :=
    (CFC.posPart_eq_zero_iff (-X)).mpr (neg_nonpos.mpr hX.nonneg)
  rw [hz]
  simp [rt]

private def dsum {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (X : Matrix n n ℂ) (Y : Matrix m m ℂ) : Matrix (n ⊕ m) (n ⊕ m) ℂ :=
  Matrix.fromBlocks X 0 0 Y

private theorem dsum_psd {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    {X : Matrix n n ℂ} {Y : Matrix m m ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : (dsum X Y).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.fromBlocks hX.isHermitian
    · ext <;> simp
    · exact hY.isHermitian
  · intro x
    classical
    let x₁ : n → ℂ := fun i => x (Sum.inl i)
    let x₂ : m → ℂ := fun i => x (Sum.inr i)
    have h1 := hX.dotProduct_mulVec_nonneg x₁
    have h2 := hY.dotProduct_mulVec_nonneg x₂
    simpa [dsum, Matrix.mulVec, dotProduct, x₁, x₂, Fintype.sum_sum_type] using
      add_nonneg h1 h2

private theorem dsum_mul {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (X X' : Matrix n n ℂ) (Y Y' : Matrix m m ℂ) :
    dsum X Y * dsum X' Y' = dsum (X * X') (Y * Y') := by
  rw [dsum, dsum, dsum, Matrix.fromBlocks_multiply]
  simp [dsum]

private theorem posPart_dsum {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    {X : Matrix n n ℂ} {Y : Matrix m m ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (dsum X Y)⁺ = dsum X⁺ Y⁺ := by
  have hP : 0 ≤ dsum X⁺ Y⁺ := Matrix.nonneg_iff_posSemidef.mpr
    (dsum_psd (Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg X))
      (Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg Y)))
  have hQ : 0 ≤ dsum X⁻ Y⁻ := Matrix.nonneg_iff_posSemidef.mpr
    (dsum_psd (Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg X))
      (Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg Y)))
  have hpq : dsum X⁺ Y⁺ * dsum X⁻ Y⁻ = 0 := by
    rw [dsum_mul]
    rw [CFC.posPart_mul_negPart, CFC.posPart_mul_negPart]
    simp [dsum]
  have hdecomp : dsum X Y = dsum X⁺ Y⁺ - dsum X⁻ Y⁻ := by
    rw [show dsum X⁺ Y⁺ - dsum X⁻ Y⁻ = dsum (X⁺ - X⁻) (Y⁺ - Y⁻) by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [dsum, sub_eq_add_neg]]
    rw [CFC.posPart_sub_negPart X hX, CFC.posPart_sub_negPart Y hY]
  exact (CFC.posPart_negPart_unique hdecomp hpq hP hQ).1

private theorem posTrace_dsum {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    {X : Matrix n n ℂ} {Y : Matrix m m ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    posTrace (dsum X Y) = posTrace X + posTrace Y := by
  rw [posTrace, posPart_dsum hX hY]
  simp [posTrace, rt, dsum, Matrix.trace, Fintype.sum_sum_type]

private theorem posPart_reindex {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (e : n ≃ m) {X : Matrix n n ℂ}
    (hX : X.IsHermitian) : (X.reindex e e)⁺ = (X⁺).reindex e e := by
  have hP : 0 ≤ (X⁺).reindex e e :=
    ((Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg X)).submatrix e.symm).nonneg
  have hQ : 0 ≤ (X⁻).reindex e e :=
    ((Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg X)).submatrix e.symm).nonneg
  have hpq : (X⁺).reindex e e * (X⁻).reindex e e = 0 := by
    rw [Matrix.reindex_apply, Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv]
    rw [CFC.posPart_mul_negPart]
    simp
  have hdecomp : X.reindex e e = (X⁺).reindex e e - (X⁻).reindex e e := by
    rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply]
    calc
      X.submatrix e.symm e.symm = (X⁺ - X⁻).submatrix e.symm e.symm := by
        rw [CFC.posPart_sub_negPart X hX]
      _ = X⁺.submatrix e.symm e.symm - X⁻.submatrix e.symm e.symm := by
        ext i j
        simp [Matrix.submatrix]
  exact (CFC.posPart_negPart_unique hdecomp hpq hP hQ).1

private theorem posTrace_reindex {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (e : n ≃ m) {X : Matrix n n ℂ}
    (hX : X.IsHermitian) : posTrace (X.reindex e e) = posTrace X := by
  unfold posTrace rt
  rw [posPart_reindex e hX]
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.diag, Matrix.submatrix_apply]
  rw [Complex.re_sum, Complex.re_sum]
  exact Equiv.sum_comp e.symm (fun i : n => (X⁺ i i).re)

private def flagEquiv (R A : Type*) :
    (R ⊕ (Unit ⊕ Unit)) × A ≃ (R × A) ⊕ (A ⊕ A) := by
  exact (Equiv.sumProdDistrib R (Unit ⊕ Unit) A).trans
    (Equiv.sumCongr (Equiv.refl (R × A))
      ((Equiv.sumProdDistrib Unit Unit A).trans
        (Equiv.sumCongr (Equiv.uniqueProd A Unit) (Equiv.uniqueProd A Unit))))

private def flag {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A]
    (X : Matrix (R × A) (R × A) ℂ) (Y Z : Matrix A A ℂ) :
    Matrix ((R ⊕ (Unit ⊕ Unit)) × A) ((R ⊕ (Unit ⊕ Unit)) × A) ℂ :=
  Matrix.reindex (flagEquiv R A).symm (flagEquiv R A).symm (dsum X (dsum Y Z))

private theorem trace_reindex {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (e : n ≃ m) (X : Matrix n n ℂ) :
    (X.reindex e e).trace = X.trace := by
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.diag, Matrix.submatrix_apply]
  rw [Equiv.sum_comp e.symm (fun i : n => X i i)]

private theorem flag_psd {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A]
    {X : Matrix (R × A) (R × A) ℂ} {Y Z : Matrix A A ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hZ : Z.PosSemidef) :
    (flag X Y Z).PosSemidef := by
  unfold flag
  rw [Matrix.reindex_apply]
  exact (dsum_psd hX (dsum_psd hY hZ)).submatrix (flagEquiv R A)

private theorem trace_flag {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A]
    (X : Matrix (R × A) (R × A) ℂ) (Y Z : Matrix A A ℂ) :
    (flag X Y Z).trace = X.trace + Y.trace + Z.trace := by
  unfold flag
  rw [trace_reindex]
  simp [dsum, Matrix.trace, Fintype.sum_sum_type]
  ring

private theorem flag_mul {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A]
    (X X' : Matrix (R × A) (R × A) ℂ) (Y Y' Z Z' : Matrix A A ℂ) :
    flag X Y Z * flag X' Y' Z' = flag (X * X') (Y * Y') (Z * Z') := by
  unfold flag
  change (Matrix.reindexRingEquiv ℂ (flagEquiv R A).symm) (dsum X (dsum Y Z)) *
      (Matrix.reindexRingEquiv ℂ (flagEquiv R A).symm) (dsum X' (dsum Y' Z')) = _
  rw [← (Matrix.reindexRingEquiv ℂ (flagEquiv R A).symm).map_mul]
  rw [dsum_mul, dsum_mul]
  rfl

private theorem flag_sub_smul {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A]
    (t : ℝ) (X X' : Matrix (R × A) (R × A) ℂ)
    (Y Y' Z Z' : Matrix A A ℂ) :
    flag X Y Z - t • flag X' Y' Z' =
      flag (X - t • X') (Y - t • Y') (Z - t • Z') := by
  unfold flag
  let T := Matrix.reindexLinearEquiv ℝ ℂ (flagEquiv R A).symm (flagEquiv R A).symm
  change T (dsum X (dsum Y Z)) - t • T (dsum X' (dsum Y' Z')) = _
  calc
    T (dsum X (dsum Y Z)) - t • T (dsum X' (dsum Y' Z')) =
        T (dsum X (dsum Y Z)) - T (t • dsum X' (dsum Y' Z')) := by
      congr 1
    _ = T (dsum X (dsum Y Z) - t • dsum X' (dsum Y' Z')) := by
      exact (T.map_sub _ _).symm
    _ = T (dsum (X - t • X') (dsum (Y - t • Y') (Z - t • Z'))) := by
      congr 1
      ext i j
      rcases i with i | i
      · rcases j with j | j
        · simp [dsum, sub_eq_add_neg]
        · rcases j with j | j <;> simp [dsum, sub_eq_add_neg]
      · rcases i with i | i
        · rcases j with j | j
          · simp [dsum, sub_eq_add_neg]
          · rcases j with j | j <;> simp [dsum, sub_eq_add_neg]
        · rcases j with j | j
          · simp [dsum, sub_eq_add_neg]
          · rcases j with j | j <;> simp [dsum, sub_eq_add_neg]
    _ = _ := rfl

private theorem posTrace_flag {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A]
    {X : Matrix (R × A) (R × A) ℂ} {Y Z : Matrix A A ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (hZ : Z.IsHermitian) :
    posTrace (flag X Y Z) = posTrace X + posTrace Y + posTrace Z := by
  have hYZ : (dsum Y Z).IsHermitian :=
    Matrix.IsHermitian.fromBlocks hY (by simp) hZ
  have hXYZ : (dsum X (dsum Y Z)).IsHermitian :=
    Matrix.IsHermitian.fromBlocks hX (by simp) hYZ
  unfold flag
  rw [posTrace_reindex (flagEquiv R A).symm hXYZ]
  rw [posTrace_dsum hX hYZ, posTrace_dsum hY hZ]
  ring

private def act {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) (X : Matrix A A ℂ) : Matrix B B ℂ :=
  CStarMatrix.ofMatrix.symm
    (N.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))

private theorem act_state {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) {X : Matrix A A ℂ} (hX : IsState X) :
    IsState (act N X) := by
  refine ⟨Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
        (map_nonneg N.toCompletelyPositiveMap
          (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
            (Matrix.nonneg_iff_posSemidef.mpr hX.1)))), ?_⟩
  change Matrix.trace (CStarMatrix.ofMatrix.symm
      (N.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))) = 1
  exact (N.trace_preserving (CStarMatrix.ofMatrix X)).trans hX.2

private theorem act_zero {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) : act N (0 : Matrix A A ℂ) = 0 := by
  ext b d
  simp [act]

private theorem amp_state {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) {X : Matrix (R × A) (R × A) ℂ} (hX : IsState X) :
    IsState (amp N X) := by
  let rho : DensityState (R × A) := ⟨CStarMatrix.ofMatrix X,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (Matrix.nonneg_iff_posSemidef.mpr hX.1), hX.2⟩
  refine ⟨?_, ?_⟩
  · have hp := (referenceState N rho).2.1
    change 0 ≤ referenceAction N rho.1 at hp
    exact Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hp)
  · have ht := (referenceState N rho).2.2
    change Matrix.trace (referenceAction N rho.1) = 1 at ht
    exact ht

private theorem amp_entry {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) (X : Matrix (R × A) (R × A) ℂ)
    (r s : R) (b d : B) :
    amp N X (r, b) (s, d) =
      act N (fun a a' => X (r, a) (s, a')) b d := by
  rfl

private theorem ptr_sub_smul {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A]
    (t : ℝ) (X Y : Matrix (R × A) (R × A) ℂ) :
    ptr (X - t • Y) = ptr X - t • ptr Y := by
  ext i j
  simp [ptr, partialTraceRight, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.mul_sum, sub_eq_add_neg]

private theorem ptr_amp {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) (X : Matrix (R × A) (R × A) ℂ) :
    ptr (amp N X) = ptr X := by
  ext r s
  change (∑ b, amp N X (r, b) (s, b)) = ∑ a, X (r, a) (s, a)
  simp_rw [amp_entry]
  let Z : Matrix A A ℂ := fun a a' => X (r, a) (s, a')
  have h := N.trace_preserving (CStarMatrix.ofMatrix Z)
  change (∑ b, act N Z b b) = ∑ a, Z a a at h
  simpa [Z, act, Matrix.trace] using h

private theorem amp_flag {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) (X : Matrix (R × A) (R × A) ℂ)
    (Y Z : Matrix A A ℂ) :
    amp N (flag X Y Z) = flag (amp N X) (act N Y) (act N Z) := by
  ext ⟨r, b⟩ ⟨s, d⟩
  simp only [amp_entry]
  rcases r with r | r
  · rcases s with s | s
    · exact (amp_entry N X r s b d).symm
    · rcases s with s | s
      · simp [flag, flagEquiv, Matrix.reindex_apply, dsum, act]
        try exact congrArg (fun M : Matrix B B ℂ => M b d) (act_zero N)
      · simp [flag, flagEquiv, Matrix.reindex_apply, dsum, act]
        try exact congrArg (fun M : Matrix B B ℂ => M b d) (act_zero N)
  · rcases r with r | r
    · rcases s with s | s
      · simp [flag, flagEquiv, Matrix.reindex_apply, dsum, act]
        try exact congrArg (fun M : Matrix B B ℂ => M b d) (act_zero N)
      · rcases s with s | s
        · simp [flag, flagEquiv, Matrix.reindex_apply, dsum, act]
          try exact congrArg (fun M : Matrix B B ℂ => M b d) (act_zero N)
        · simp [flag, flagEquiv, Matrix.reindex_apply, dsum, act]
          try exact congrArg (fun M : Matrix B B ℂ => M b d) (act_zero N)
    · rcases s with s | s
      · simp [flag, flagEquiv, Matrix.reindex_apply, dsum, act]
        try exact congrArg (fun M : Matrix B B ℂ => M b d) (act_zero N)
      · rcases s with s | s
        · simp [flag, flagEquiv, Matrix.reindex_apply, dsum, act]
          try exact congrArg (fun M : Matrix B B ℂ => M b d) (act_zero N)
        · simp [flag, flagEquiv, Matrix.reindex_apply, dsum, act]
          try exact congrArg (fun M : Matrix B B ℂ => M b d) (act_zero N)

private theorem ptr_flag {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A]
    (X : Matrix (R × A) (R × A) ℂ) (Y Z : Matrix A A ℂ) :
    ptr (flag X Y Z) =
      dsum (ptr X)
        (dsum (Y.trace • (1 : Matrix Unit Unit ℂ))
          (Z.trace • (1 : Matrix Unit Unit ℂ))) := by
  ext r s
  rcases r with r | r
  · rcases s with s | s
    · simp [ptr, flag, flagEquiv, Matrix.reindex_apply, dsum, partialTraceRight,
        Matrix.trace, Fintype.sum_sum_type]
    · rcases s with s | s
      · simp [ptr, flag, flagEquiv, Matrix.reindex_apply, dsum, partialTraceRight,
          Matrix.trace, Fintype.sum_sum_type]
      · simp [ptr, flag, flagEquiv, Matrix.reindex_apply, dsum, partialTraceRight,
          Matrix.trace, Fintype.sum_sum_type]
  · rcases r with r | r
    · rcases s with s | s
      · simp [ptr, flag, flagEquiv, Matrix.reindex_apply, dsum, partialTraceRight,
          Matrix.trace, Fintype.sum_sum_type]
      · rcases s with s | s
        · simp [ptr, flag, flagEquiv, Matrix.reindex_apply, dsum, partialTraceRight,
            Matrix.trace, Fintype.sum_sum_type]

        · simp [ptr, flag, flagEquiv, Matrix.reindex_apply, dsum, partialTraceRight,
            Matrix.trace, Fintype.sum_sum_type]
    · rcases s with s | s
      · simp [ptr, flag, flagEquiv, Matrix.reindex_apply, dsum, partialTraceRight,
          Matrix.trace, Fintype.sum_sum_type]
      · rcases s with s | s
        · simp [ptr, flag, flagEquiv, Matrix.reindex_apply, dsum, partialTraceRight,
            Matrix.trace, Fintype.sum_sum_type]
        · simp [ptr, flag, flagEquiv, Matrix.reindex_apply, dsum, partialTraceRight,
            Matrix.trace, Fintype.sum_sum_type]

private theorem flag_weights (p q δ : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hδ : 0 < δ) :
    let c := (1 + p + q / δ)⁻¹
    let a := 1 - c * p
    let b := δ - c * q
    0 < c ∧ 0 ≤ a ∧ 0 ≤ b ∧ c * p + a = 1 ∧
      (c / δ) * q + b / δ = 1 := by
  dsimp
  have hden : 0 < 1 + p + q / δ := by positivity
  have hc : 0 < (1 + p + q / δ)⁻¹ := inv_pos.mpr hden
  have haeq : 1 - (1 + p + q / δ)⁻¹ * p =
      (1 + p + q / δ)⁻¹ * (1 + q / δ) := by
    field_simp
    ring
  have hbeq : δ - (1 + p + q / δ)⁻¹ * q =
      (1 + p + q / δ)⁻¹ * δ * (1 + p) := by
    field_simp
    ring
  have ha : 0 ≤ 1 - (1 + p + q / δ)⁻¹ * p := by rw [haeq]; positivity
  have hb : 0 ≤ δ - (1 + p + q / δ)⁻¹ * q := by rw [hbeq]; positivity
  refine ⟨hc, ha, hb, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring

private def pureFiller {A : Type*} [Fintype A] [DecidableEq A]
    (a₀ : A) : Matrix A A ℂ :=
  Matrix.diagonal (fun a => if a = a₀ then 1 else 0)

private theorem pure_filler_state {A : Type*} [Fintype A] [DecidableEq A]
    (a₀ : A) : IsState (pureFiller a₀) := by
  refine ⟨Matrix.posSemidef_diagonal_iff.mpr (fun a => by positivity), ?_⟩
  simp [pureFiller, Matrix.trace]
def claim : Prop :=
  ∀ (A B : Type) [Fintype A] [DecidableEq A]
      [Fintype B] [DecidableEq B] (N : QuantumChannel A B),
    (∀ γ : ℝ, 1 ≤ γ → ratios N γ false = ratios N γ true) ∧
    (∀ γ δ : ℝ, 1 ≤ γ → 1 ≤ δ → ratios N γ false = ratios N δ false)

theorem result : claim := by
  sorry

end D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
