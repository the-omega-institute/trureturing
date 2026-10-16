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
  simp only [Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => hX.eigenvalues_nonneg i

private theorem trace_psd {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.PosSemidef) : X.trace = ((rt X : ℝ) : ℂ) := by
  have h := hX.isHermitian.trace_eq_sum_eigenvalues
  apply Complex.ext
  · rfl
  · change X.trace.im = 0
    rw [h]
    simp [Complex.im_sum]

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
  unfold rt; simp

private theorem posTrace_neg_smul {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.PosSemidef) (c : ℝ) (hc : 0 ≤ c) :
    posTrace (-c • X) = 0 := by
  rw [show -c • X = -(c • X) by ext i j; simp]
  exact posTrace_neg_psd (hX.smul hc)

private theorem trace_smul_psd {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.PosSemidef) (c : ℝ) :
    (c • X).trace = ((c * rt X : ℝ) : ℂ) := by
  rw [Matrix.trace_smul, trace_psd hX]
  simp [Complex.ofReal_mul]

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
    · ext; simp
    · exact hY.isHermitian
  · intro x
    classical
    let x₁ : n → ℂ := fun i => x (Sum.inl i)
    let x₂ : m → ℂ := fun i => x (Sum.inr i)
    have h1 := hX.dotProduct_mulVec_nonneg x₁
    have h2 := hY.dotProduct_mulVec_nonneg x₂
    unfold dsum; simpa [Matrix.mulVec, dotProduct, x₁, x₂, Fintype.sum_sum_type] using
      add_nonneg h1 h2

private theorem dsum_mul {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (X X' : Matrix n n ℂ) (Y Y' : Matrix m m ℂ) :
    dsum X Y * dsum X' Y' = dsum (X * X') (Y * Y') := by
  rw [dsum, dsum, dsum, Matrix.fromBlocks_multiply]
  simp

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
    unfold dsum; simp
  have hdecomp : dsum X Y = dsum X⁺ Y⁺ - dsum X⁻ Y⁻ := by
    rw [show dsum X⁺ Y⁺ - dsum X⁻ Y⁻ = dsum (X⁺ - X⁻) (Y⁺ - Y⁻) by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> (unfold dsum; simp [sub_eq_add_neg])]
    rw [CFC.posPart_sub_negPart X hX, CFC.posPart_sub_negPart Y hY]
  exact (CFC.posPart_negPart_unique hdecomp hpq hP hQ).1

private theorem posTrace_dsum {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    {X : Matrix n n ℂ} {Y : Matrix m m ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    posTrace (dsum X Y) = posTrace X + posTrace Y := by
  rw [posTrace, posPart_dsum hX hY]
  unfold posTrace rt dsum; simp [Matrix.trace, Fintype.sum_sum_type]

open Classical in
private theorem posPart_reindex {n m : Type*} [Fintype n]
    [Fintype m] (e : n ≃ m) {X : Matrix n n ℂ}
    (hX : X.IsHermitian) : (X.reindex e e)⁺ = (X⁺).reindex e e := by
  classical
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

private theorem trace_reindex {n m : Type*} [Fintype n]
    [Fintype m] (e : n ≃ m) (X : Matrix n n ℂ) :
    (X.reindex e e).trace = X.trace := by
  classical
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
  unfold dsum; simp [Matrix.trace, Fintype.sum_sum_type]
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
        · unfold dsum; simp [sub_eq_add_neg]
        · rcases j with j | j <;> (unfold dsum; simp [sub_eq_add_neg])
      · rcases i with i | i
        · rcases j with j | j
          · unfold dsum; simp [sub_eq_add_neg]
          · rcases j with j | j <;> (unfold dsum; simp [sub_eq_add_neg])
        · rcases j with j | j
          · unfold dsum; simp [sub_eq_add_neg]
          · rcases j with j | j <;> (unfold dsum; simp [sub_eq_add_neg])
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
  unfold act; simp

private theorem act_sub_smul {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) (t : ℝ) (X Y : Matrix A A ℂ) :
    act N (X - t • Y) = act N X - t • act N Y := by
  unfold act
  have hmap : CStarMatrix.ofMatrix (X - t • Y) =
      CStarMatrix.ofMatrix X - (t : ℂ) • CStarMatrix.ofMatrix Y := by
    ext i j
    simp [sub_eq_add_neg]
  rw [hmap, map_sub, map_smul]
  rfl

private theorem act_smul {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) (t : ℝ) (X : Matrix A A ℂ) :
    act N (t • X) = t • act N X := by
  unfold act
  have hmap : CStarMatrix.ofMatrix (t • X) =
      (t : ℂ) • CStarMatrix.ofMatrix X := by
    ext i j
    simp
  rw [hmap, map_smul]
  rfl

private theorem ptr_smul {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A]
    (t : ℝ) (X : Matrix (R × A) (R × A) ℂ) :
    ptr (t • X) = t • ptr X := by
  ext r s
  unfold ptr; simp [partialTraceRight, Finset.smul_sum]

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

private theorem amp_smul {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) (t : ℝ) (X : Matrix (R × A) (R × A) ℂ) :
    amp N (t • X) = t • amp N X := by
  ext ⟨r, b⟩ ⟨s, d⟩
  rw [amp_entry]
  let Z : Matrix A A ℂ := fun a a' => X (r, a) (s, a')
  have harg : (fun a a' => (t • X) (r, a) (s, a')) = t • Z := by
    ext a a'
    change (t : ℂ) * X (r, a) (s, a') =
      (t : ℂ) * X (r, a) (s, a')
    rfl
  rw [harg]
  have hact := act_smul N t Z
  change act N (t • Z) b d = t * act N Z b d
  rw [hact]
  rfl

private theorem amp_sub_smul {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) (t : ℝ) (X Y : Matrix (R × A) (R × A) ℂ) :
    amp N (X - t • Y) = amp N X - t • amp N Y := by
  ext ⟨r, b⟩ ⟨s, d⟩
  let Z : Matrix A A ℂ := fun a a' => X (r, a) (s, a')
  let W : Matrix A A ℂ := fun a a' => Y (r, a) (s, a')
  change act N (Z - t • W) b d = (act N Z - t • act N W) b d
  exact congrArg (fun M : Matrix B B ℂ => M b d) (act_sub_smul N t Z W)

private theorem ptr_sub_smul {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [DecidableEq A]
    (t : ℝ) (X Y : Matrix (R × A) (R × A) ℂ) :
    ptr (X - t • Y) = ptr X - t • ptr Y := by
  ext i j
  unfold ptr; simp [partialTraceRight, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.mul_sum, sub_eq_add_neg]

private theorem ptr_amp {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) (X : Matrix (R × A) (R × A) ℂ) :
    ptr (amp N X) = ptr X := by
  ext r s
  change (∑ b, amp N X (r, b) (s, b)) = ∑ a, X (r, a) (s, a)
  let Z : Matrix A A ℂ := fun a a' => X (r, a) (s, a')
  have h := N.trace_preserving (CStarMatrix.ofMatrix Z)
  change (∑ b, act N Z b b) = ∑ a, Z a a at h
  exact h

private theorem amp_flag {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) (X : Matrix (R × A) (R × A) ℂ)
    (Y Z : Matrix A A ℂ) :
    amp N (flag X Y Z) = flag (amp N X) (act N Y) (act N Z) := by
  ext ⟨r, b⟩ ⟨s, d⟩
  rw [amp_entry]
  rcases r with r | r
  · rcases s with s | s
    · rfl
    · rcases s with s | s
      all_goals
        change act N (0 : Matrix A A ℂ) b d = 0
        exact congrArg (fun M : Matrix B B ℂ => M b d) (act_zero N)
  · rcases r with r | r
    · rcases s with s | s
      · change act N (0 : Matrix A A ℂ) b d = 0
        exact congrArg (fun M : Matrix B B ℂ => M b d) (act_zero N)
      · rcases s with s | s
        · rfl
        · change act N (0 : Matrix A A ℂ) b d = 0
          exact congrArg (fun M : Matrix B B ℂ => M b d) (act_zero N)
    · rcases s with s | s
      · change act N (0 : Matrix A A ℂ) b d = 0
        exact congrArg (fun M : Matrix B B ℂ => M b d) (act_zero N)
      · rcases s with s | s
        · change act N (0 : Matrix A A ℂ) b d = 0
          exact congrArg (fun M : Matrix B B ℂ => M b d) (act_zero N)
        · rfl

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
    · unfold ptr flag flagEquiv dsum; simp [Matrix.reindex_apply, partialTraceRight,
        Matrix.trace]
    · rcases s with s | s
      · unfold ptr flag flagEquiv dsum; simp [Matrix.reindex_apply, partialTraceRight,
          Matrix.trace]
      · unfold ptr flag flagEquiv dsum; simp [Matrix.reindex_apply, partialTraceRight,
          Matrix.trace]
  · rcases r with r | r
    · rcases s with s | s
      · unfold ptr flag flagEquiv dsum; simp [Matrix.reindex_apply, partialTraceRight,
          Matrix.trace]
      · rcases s with s | s
        · unfold ptr flag flagEquiv dsum; simp [Matrix.reindex_apply, partialTraceRight,
            Matrix.trace]
        · unfold ptr flag flagEquiv dsum; simp [Matrix.reindex_apply, partialTraceRight,
            Matrix.trace]
    · rcases s with s | s
      · unfold ptr flag flagEquiv dsum; simp [Matrix.reindex_apply, partialTraceRight,
          Matrix.trace]
      · rcases s with s | s
        · unfold ptr flag flagEquiv dsum; simp [Matrix.reindex_apply, partialTraceRight,
            Matrix.trace]
        · unfold ptr flag flagEquiv dsum; simp [Matrix.reindex_apply, partialTraceRight,
            Matrix.trace]

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
  unfold pureFiller; simp [Matrix.trace]

private theorem flag_transfer
    {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) (γ δ : ℝ) (hδ : 0 < δ)
    (ρ σ : Matrix (R × A) (R × A) ℂ)
    (hρ : IsState ρ) (hσ : IsState σ) :
    ∃ c : ℝ, ∃ ρ' σ' : Matrix ((R ⊕ (Unit ⊕ Unit)) × A)
        ((R ⊕ (Unit ⊕ Unit)) × A) ℂ,
      0 < c ∧ IsState ρ' ∧ IsState σ' ∧ ρ' * σ' = 0 ∧
      gap δ ρ' σ' = c * gap γ ρ σ ∧
      gap δ (amp N ρ') (amp N σ') =
        c * gap γ (amp N ρ) (amp N σ) := by
  let H : Matrix (R × A) (R × A) ℂ := ρ - γ • σ
  have hH : H.IsHermitian := by
    unfold H
    exact hρ.1.isHermitian.sub (hσ.1.isHermitian.smul (by
      rw [isSelfAdjoint_iff]
      rfl))
  let P : Matrix (R × A) (R × A) ℂ := H⁺
  let Q : Matrix (R × A) (R × A) ℂ := H⁻
  have hP : P.PosSemidef := by
    unfold P
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg H)
  have hQ : Q.PosSemidef := by
    unfold Q
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)
  have hPQ : P * Q = 0 := by
    unfold P Q
    exact CFC.posPart_mul_negPart H
  have hHdecomp : H = P - Q := by
    unfold P Q
    exact (CFC.posPart_sub_negPart H hH).symm
  let p : ℝ := rt P
  let q : ℝ := rt Q
  have hp : 0 ≤ p := by exact rt_nonneg_psd hP
  have hq : 0 ≤ q := by exact rt_nonneg_psd hQ
  let c : ℝ := (1 + p + q / δ)⁻¹
  let a : ℝ := 1 - c * p
  let b : ℝ := δ - c * q
  have hw : 0 < c ∧ 0 ≤ a ∧ 0 ≤ b ∧ c * p + a = 1 ∧
      (c / δ) * q + b / δ = 1 := by
    exact flag_weights p q δ hp hq hδ
  rcases hw with ⟨hc, ha, hb, hca, hcb⟩
  have hRA : Nonempty (R × A) := state_nonempty hρ
  let a₀ : A := (Classical.choice hRA).2
  let τ : Matrix A A ℂ := pureFiller a₀
  have hτ : IsState τ := pure_filler_state a₀
  let ρ' : Matrix ((R ⊕ (Unit ⊕ Unit)) × A)
      ((R ⊕ (Unit ⊕ Unit)) × A) ℂ :=
    flag (c • P) (a • τ) 0
  let σ' : Matrix ((R ⊕ (Unit ⊕ Unit)) × A)
      ((R ⊕ (Unit ⊕ Unit)) × A) ℂ :=
    flag ((c / δ) • Q) 0 ((b / δ) • τ)
  have hρ'psd : ρ'.PosSemidef := by
    unfold ρ'
    exact flag_psd (hP.smul (le_of_lt hc)) (hτ.1.smul ha) Matrix.PosSemidef.zero
  have hσ'psd : σ'.PosSemidef := by
    unfold σ'
    exact flag_psd (hQ.smul (le_of_lt (div_pos hc hδ))) Matrix.PosSemidef.zero
      (hτ.1.smul (div_nonneg hb (le_of_lt hδ)))
  have hτrt : rt τ = 1 := by
    have ht := congrArg Complex.re hτ.2
    unfold rt; simpa using ht
  have hρ'trace : ρ'.trace = 1 := by
    unfold ρ'
    rw [trace_flag, trace_smul_psd hP c, trace_smul_psd hτ.1 a,
      Matrix.trace_zero, hτrt, mul_one, add_zero, ← Complex.ofReal_add]
    exact congrArg Complex.ofReal hca
  have hσ'trace : σ'.trace = 1 := by
    unfold σ'
    rw [trace_flag, trace_smul_psd hQ (c / δ), Matrix.trace_zero,
      trace_smul_psd hτ.1 (b / δ), hτrt, mul_one, add_zero, ← Complex.ofReal_add]
    exact congrArg Complex.ofReal hcb
  have hρ' : IsState ρ' := ⟨hρ'psd, hρ'trace⟩
  have hσ' : IsState σ' := ⟨hσ'psd, hσ'trace⟩
  have horth : ρ' * σ' = 0 := by
    unfold ρ' σ'
    rw [flag_mul]
    have hfirst : (c • P) * ((c / δ) • Q) = 0 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, hPQ]
      simp
    rw [hfirst]
    unfold flag
    rw [Matrix.reindex_apply]
    ext i j
    unfold dsum; simp
  have hsub : ρ' - δ • σ' = flag (c • H) (a • τ) (-b • τ) := by
    unfold ρ' σ'
    rw [flag_sub_smul]
    have hfirst : c • P - δ • ((c / δ) • Q) = c • H := by
      calc
        c • P - δ • ((c / δ) • Q) = c • (P - Q) := by
          rw [smul_smul]
          have h : δ * (c / δ) = c := mul_div_cancel₀ _ (ne_of_gt hδ)
          rw [h]
          ext i j
          simp [sub_eq_add_neg]
        _ = c • H := congrArg (fun X => c • X) hHdecomp.symm
    rw [hfirst]
    rw [show a • τ - δ • (0 : Matrix A A ℂ) = a • τ by simp]
    rw [show 0 - δ • ((b / δ) • τ) = -b • τ by
        rw [smul_smul]
        have h : δ * (b / δ) = b := mul_div_cancel₀ _ (ne_of_gt hδ)
        rw [h]
        ext i j
        simp]
  have hE : E δ ρ' σ' = c * E γ ρ σ + a := by
    rw [show E δ ρ' σ' = posTrace (flag (c • H) (a • τ) (-b • τ)) by
      unfold E
      rw [hsub]]
    have hnegτ : (-b • τ).IsHermitian := by
      rw [show -b • τ = -(b • τ) by ext i j; simp]
      exact (hτ.1.smul hb).isHermitian.neg
    have hcH : (c • H).IsHermitian := hH.smul (by
      rw [isSelfAdjoint_iff]
      rfl)
    have haτ : (a • τ).IsHermitian := hτ.1.isHermitian.smul (by
      rw [isSelfAdjoint_iff]
      rfl)
    rw [posTrace_flag hcH haτ hnegτ]
    rw [posTrace_smul c (le_of_lt hc), posTrace_smul a ha,
      posTrace_neg_smul hτ.1 b hb, posTrace_psd hτ.1]
    rw [hτrt]
    rw [mul_one, add_zero]
    have hHE : posTrace H = E γ ρ σ := by rfl
    rw [hHE]
  have hptrHdef : ptr H = ptr ρ - γ • ptr σ := by
    unfold H
    exact ptr_sub_smul γ ρ σ
  have hptrρ : (ptr ρ).PosSemidef := by
    exact partialTraceRight_posSemidef hρ.1
  have hptrσ : (ptr σ).PosSemidef := by
    exact partialTraceRight_posSemidef hσ.1
  have hptrH : (ptr H).IsHermitian := by
    rw [hptrHdef]
    exact hptrρ.isHermitian.sub (hptrσ.isHermitian.smul (by
      rw [isSelfAdjoint_iff]
      rfl))
  have hptrsub : ptr ρ' - δ • ptr σ' =
      dsum (c • ptr H)
        (dsum (a • (1 : Matrix Unit Unit ℂ))
          (-b • (1 : Matrix Unit Unit ℂ))) := by
    calc
      ptr ρ' - δ • ptr σ' = ptr (ρ' - δ • σ') :=
        (ptr_sub_smul δ ρ' σ').symm
      _ = ptr (flag (c • H) (a • τ) (-b • τ)) := by rw [hsub]
      _ = dsum (ptr (c • H))
          (dsum (((a • τ).trace) • (1 : Matrix Unit Unit ℂ))
            (((-b • τ).trace) • (1 : Matrix Unit Unit ℂ))) := by
        rw [ptr_flag]
      _ = dsum (c • ptr H)
          (dsum (a • (1 : Matrix Unit Unit ℂ))
            (-b • (1 : Matrix Unit Unit ℂ))) := by
        rw [ptr_smul]
        rw [Matrix.trace_smul, hτ.2, Matrix.trace_smul, hτ.2]
        simp
  have hone : (1 : Matrix Unit Unit ℂ).PosSemidef := Matrix.PosSemidef.one
  have hEptr : E δ (ptr ρ') (ptr σ') =
      c * E γ (ptr ρ) (ptr σ) + a := by
    rw [show E δ (ptr ρ') (ptr σ') =
        posTrace (ptr ρ' - δ • ptr σ') by rfl]
    rw [hptrsub]
    have hcptr : (c • ptr H).IsHermitian := hptrH.smul (by
      rw [isSelfAdjoint_iff]
      rfl)
    have haone : (a • (1 : Matrix Unit Unit ℂ)).IsHermitian :=
      hone.isHermitian.smul (by rw [isSelfAdjoint_iff]; rfl)
    have hbone : (-b • (1 : Matrix Unit Unit ℂ)).IsHermitian := by
      rw [show -b • (1 : Matrix Unit Unit ℂ) =
          -(b • (1 : Matrix Unit Unit ℂ)) by ext i j; simp]
      exact (hone.smul hb).isHermitian.neg
    have hzero : (0 : Matrix Unit Unit ℂ).conjTranspose = 0 := by
      ext i j
      simp
    have hinner : (dsum (a • (1 : Matrix Unit Unit ℂ))
        (-b • (1 : Matrix Unit Unit ℂ))).IsHermitian := by
      unfold dsum
      exact Matrix.IsHermitian.fromBlocks haone hzero hbone
    rw [posTrace_dsum hcptr hinner, posTrace_dsum haone hbone]
    rw [posTrace_smul c (le_of_lt hc), posTrace_smul a ha,
      posTrace_neg_smul hone b hb, posTrace_psd hone]
    have hptrE : posTrace (ptr H) = E γ (ptr ρ) (ptr σ) := by
      rw [hptrHdef]
      rfl
    rw [hptrE]
    rw [show rt (1 : Matrix Unit Unit ℂ) = 1 by
      unfold rt
      simp [Matrix.trace], mul_one, add_zero]
  have hHB : (amp N H).IsHermitian := by
    unfold H
    rw [amp_sub_smul]
    exact (amp_state N hρ).1.isHermitian.sub
      ((amp_state N hσ).1.isHermitian.smul (by rw [isSelfAdjoint_iff]; rfl))
  have hτB : IsState (act N τ) := act_state N hτ
  have houtsub : amp N ρ' - δ • amp N σ' =
      flag (c • amp N H) (a • act N τ) (-b • act N τ) := by
    rw [← amp_sub_smul, hsub, amp_flag, amp_smul, act_smul, act_smul]
  have hEB : E δ (amp N ρ') (amp N σ') =
      c * E γ (amp N ρ) (amp N σ) + a := by
    unfold E
    rw [houtsub]
    have hcHB : (c • amp N H).IsHermitian :=
      hHB.smul (by rw [isSelfAdjoint_iff]; rfl)
    have haτB : (a • act N τ).IsHermitian :=
      (hτB.1.smul ha).isHermitian
    have hnτB : (-b • act N τ).IsHermitian := by
      rw [neg_smul]
      exact (hτB.1.smul hb).isHermitian.neg
    rw [posTrace_flag hcHB haτB hnτB, posTrace_smul c (le_of_lt hc),
      posTrace_smul a ha, posTrace_neg_smul hτB.1 b hb, posTrace_psd hτB.1]
    have ht : rt (act N τ) = 1 := by unfold rt; rw [hτB.2, Complex.one_re]
    rw [ht]
    have hh : amp N H = amp N ρ - γ • amp N σ := amp_sub_smul N γ ρ σ
    rw [hh]
    ring
  refine ⟨c, ρ', σ', hc, hρ', hσ', horth, ?_, ?_⟩
  · unfold gap
    rw [hE, hEptr]
    ring
  · unfold gap
    rw [hEB, ptr_amp, ptr_amp, hEptr, ptr_amp, ptr_amp]
    ring

private theorem orth_subset {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (N : QuantumChannel A B) (γ : ℝ) :
    ratios N γ true ⊆ ratios N γ false := by
  rintro x ⟨R, fR, dR, ρ, σ, hρ, hσ, _, hg, hx⟩
  exact ⟨R, fR, dR, ρ, σ, hρ, hσ, by simp, hg, hx⟩

private theorem transfer_subset {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (N : QuantumChannel A B)
    (γ δ : ℝ) (hδ : 0 < δ) : ratios N γ false ⊆ ratios N δ true := by
  rintro x ⟨R, fR, dR, ρ, σ, hρ, hσ, _, hg, hx⟩
  letI := fR
  letI := dR
  obtain ⟨c, ρ', σ', hc, hρ', hσ', ho, hi, hb⟩ :=
    flag_transfer N γ δ hδ ρ σ hρ hσ
  refine ⟨R ⊕ (Unit ⊕ Unit), inferInstance, inferInstance,
    ρ', σ', hρ', hσ', fun _ => ho, ?_, ?_⟩
  · rw [hi]
    exact mul_pos hc hg
  · rw [hb, hi, mul_div_mul_left _ _ (ne_of_gt hc)]
    exact hx
def claim : Prop :=
  ∀ (A B : Type) [Fintype A] [DecidableEq A]
      [Fintype B] [DecidableEq B] (N : QuantumChannel A B),
    (∀ γ : ℝ, 1 ≤ γ → ratios N γ false = ratios N γ true) ∧
    (∀ γ δ : ℝ, 1 ≤ γ → 1 ≤ δ → ratios N γ false = ratios N δ false)

theorem result : claim := by
  intro A B _ _ _ _ N
  constructor
  · intro γ hγ
    exact Set.Subset.antisymm
      (transfer_subset N γ γ (lt_of_lt_of_le zero_lt_one hγ))
      (orth_subset N γ)
  · intro γ δ hγ hδ
    exact Set.Subset.antisymm
      ((transfer_subset N γ δ (lt_of_lt_of_le zero_lt_one hδ)).trans (orth_subset N δ))
      ((transfer_subset N δ γ (lt_of_lt_of_le zero_lt_one hγ)).trans (orth_subset N γ))

end D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
