/- GID: D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredBellRestriction
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ConditionalExpansion/FilteredBellRestriction
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Input isometries order filtered-channel ratios and give a strict Bell bound. -/

import D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredBellKernelUpperBound
import D5.S3.Quantum.Information.PartialTrace.Isometries

/-! Restricting the input of a normalized filtered channel to an isometric subspace
embeds the smaller channel's conditional trace-expansion ratios in the original set. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FilteredBellRestriction

open Matrix
open scoped CStarAlgebra ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

open FilteredBellKernelProjection (filtered_channel_bell_upper_bound)
open FilteredChannelConditionalGap
  (filterAction exists_filtered_channel filtered_channel_ratio_lower_bound)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
  (act amp amp_entry gap E ptr posTrace ratios)
open D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation (amp_psd)
open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft partialTraceRight)
open D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance (partialTrace_isometries)
open RHLinalg (rtrace)

private def embed {n m : Type} [Fintype n] (V : Matrix m n ℂ)
    (X : Matrix n n ℂ) : Matrix m m ℂ := V * X * Vᴴ

private theorem embed_mul {n m : Type} [Fintype n] [Fintype m] [DecidableEq n]
    (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (X Y : Matrix n n ℂ) :
    embed V X * embed V Y = embed V (X * Y) := by
  calc
    _ = V * X * (Vᴴ * V) * Y * Vᴴ := by simp only [embed, Matrix.mul_assoc]
    _ = _ := by simp only [embed, hV, Matrix.mul_one, Matrix.mul_assoc]

private theorem embed_trace {n m : Type} [Fintype n] [Fintype m] [DecidableEq n]
    (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (X : Matrix n n ℂ) :
    (embed V X).trace = X.trace := by
  rw [embed, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]

private theorem embed_psd {n m : Type} [Fintype n] [Finite m] (V : Matrix m n ℂ)
    {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    (embed V X).PosSemidef :=
  hX.mul_mul_conjTranspose_same V

private theorem embed_sub_smul {n m : Type} [Fintype n] (V : Matrix m n ℂ)
    (γ : ℝ) (X Y : Matrix n n ℂ) :
    embed V (X - γ • Y) = embed V X - γ • embed V Y := by
  simp only [embed, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]

private theorem posTrace_embed {n m : Type} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (V : Matrix m n ℂ) (hV : Vᴴ * V = 1)
    {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    posTrace (embed V X) = posTrace X := by
  have hp : (embed V X)⁺ = embed V X⁺ := by
    apply (CFC.posPart_negPart_unique (b := embed V X⁺) (c := embed V X⁻) ?_ ?_ ?_ ?_).1
    · rw [← one_smul ℝ (embed V X⁻), ← embed_sub_smul, one_smul,
        CFC.posPart_sub_negPart X hX]
    · rw [embed_mul V hV, CFC.posPart_mul_negPart]
      simp [embed]
    · exact (embed_psd V (CFC.posPart_nonneg X).posSemidef).nonneg
    · exact (embed_psd V (CFC.negPart_nonneg X).posSemidef).nonneg
  change rtrace (embed V X)⁺ = rtrace X⁺
  rw [hp]
  exact congrArg Complex.re (embed_trace V hV X⁺)

variable {R S T A B E' : Type}
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype E'] [DecidableEq E']

omit [Fintype S] [DecidableEq A] in
private theorem tensor_isometry (V : Matrix A S ℂ) (hV : Vᴴ * V = 1) :
    ((1 : Matrix R R ℂ) ⊗ₖ V)ᴴ * ((1 : Matrix R R ℂ) ⊗ₖ V) = 1 := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, hV, Matrix.one_kronecker_one]

private theorem gap_embed (V : Matrix A S ℂ) (hV : Vᴴ * V = 1)
    (γ : ℝ) {ρ σ : Matrix (R × S) (R × S) ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    gap γ (embed ((1 : Matrix R R ℂ) ⊗ₖ V) ρ)
        (embed ((1 : Matrix R R ℂ) ⊗ₖ V) σ) = gap γ ρ σ := by
  have hm (Z : Matrix (R × S) (R × S) ℂ) :
      ptr (embed ((1 : Matrix R R ℂ) ⊗ₖ V) Z) = ptr Z := by
    simpa only [ptr, embed, Matrix.kronecker, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one]
      using partialTrace_isometries (1 : Matrix R R ℂ) V hV Z
  unfold gap E
  rw [hm, hm, ← embed_sub_smul, posTrace_embed _ (tensor_isometry V hV)]
  exact hρ.sub (hσ.smul (IsSelfAdjoint.all γ))

omit [DecidableEq S] [Fintype A] [DecidableEq A] in
private theorem embed_entries (V : Matrix A S ℂ)
    (X : Matrix (R × S) (R × S) ℂ) (r s : R) (i j : A) :
    embed ((1 : Matrix R R ℂ) ⊗ₖ V) X (r, i) (s, j) =
      embed V (fun a b => X (r, a) (s, b)) i j := by
  simp [embed, Matrix.mul_apply, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Fintype.sum_prod_type, Matrix.one_apply, ite_mul, mul_ite, Finset.sum_ite_irrel]

private theorem amp_intertwines (N : QuantumChannel A B) (M : QuantumChannel S T)
    (V : Matrix A S ℂ) (W : Matrix B T ℂ)
    (h : ∀ X, act N (embed V X) = embed W (act M X))
    (Z : Matrix (R × S) (R × S) ℂ) :
    amp N (embed ((1 : Matrix R R ℂ) ⊗ₖ V) Z) =
      embed ((1 : Matrix R R ℂ) ⊗ₖ W) (amp M Z) := by
  ext ⟨r, i⟩ ⟨s, j⟩
  rw [amp_entry, embed_entries]
  have hin : (fun a b => embed ((1 : Matrix R R ℂ) ⊗ₖ V) Z (r, a) (s, b)) =
      embed V (fun a b => Z (r, a) (s, b)) := by
    ext a b
    exact embed_entries V Z r s a b
  have hout : (fun a b => amp M Z (r, a) (s, b)) =
      act M (fun a b => Z (r, a) (s, b)) := by
    ext a b
    exact amp_entry M Z r s a b
  rw [hin, hout, h]

private theorem ratios_subset_of_intertwining
    (N : QuantumChannel A B) (M : QuantumChannel S T)
    (V : Matrix A S ℂ) (W : Matrix B T ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (h : ∀ X, act N (embed V X) = embed W (act M X)) (γ : ℝ) (orth : Bool) :
    ratios M γ orth ⊆ ratios N γ orth := by
  rintro x ⟨r, fr, dr, ρ, σ, hρ, hρt, hσ, hσt, horth, hg, rfl⟩
  let _ := fr
  let _ := dr
  let J := (1 : Matrix r r ℂ) ⊗ₖ V
  have hJ : Jᴴ * J = 1 := tensor_isometry V hV
  have hig := gap_embed V hV γ hρ.isHermitian hσ.isHermitian
  refine ⟨r, fr, dr, embed J ρ, embed J σ, embed_psd J hρ, (embed_trace J hJ ρ).trans hρt,
    embed_psd J hσ, (embed_trace J hJ σ).trans hσt, ?_, hig ▸ hg, ?_⟩
  · intro ho
    rw [embed_mul J hJ, horth ho]
    simp [embed]
  · rw [amp_intertwines N M V W h, amp_intertwines N M V W h, hig,
      gap_embed W hW γ (amp_psd M hρ).isHermitian (amp_psd M hσ).isHermitian]

/-- The filter on a subspace is the compression by the input isometry
tensored with the environment identity. -/
def compressFilter (V : Matrix A S ℂ) (G : Matrix (A × E') (A × E') ℂ) :
    Matrix (S × E') (S × E') ℂ :=
  (V ⊗ₖ (1 : Matrix E' E' ℂ))ᴴ * G * (V ⊗ₖ (1 : Matrix E' E' ℂ))

omit [Fintype S] [DecidableEq A] in
private theorem tensor_right_isometry (V : Matrix A S ℂ) (hV : Vᴴ * V = 1) :
    (V ⊗ₖ (1 : Matrix E' E' ℂ))ᴴ * (V ⊗ₖ (1 : Matrix E' E' ℂ)) = 1 := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, hV, Matrix.one_kronecker_one]

omit [Fintype S] in
/-- Compression preserves positive definiteness and the trace-preserving normalization. -/
theorem compressFilter_posDef_normalized [Finite S]
    (V : Matrix A S ℂ) (hV : Vᴴ * V = 1)
    (G : Matrix (A × E') (A × E') ℂ) (hG : G.PosDef)
    (hnorm : (Fintype.card E' : ℝ)⁻¹ • partialTraceRight G = 1) :
    (compressFilter V G).PosDef ∧
      (Fintype.card E' : ℝ)⁻¹ • partialTraceRight (compressFilter V G) = 1 := by
  let _ := Fintype.ofFinite S
  let J := V ⊗ₖ (1 : Matrix E' E' ℂ)
  have hJ : Jᴴ * J = 1 := tensor_right_isometry V hV
  constructor
  · change (Jᴴ * G * J).PosDef
    apply hG.conjTranspose_mul_mul_same
    intro x y hxy
    have h := congrArg (fun z => Jᴴ *ᵥ z) hxy
    simpa only [Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec] using h
  · have ht : partialTraceRight (compressFilter V G) = Vᴴ * partialTraceRight G * V := by
      simpa only [compressFilter, Matrix.kronecker, Matrix.conjTranspose_kronecker,
        Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose] using
        partialTrace_isometries Vᴴ (1 : Matrix E' E' ℂ)
          (by rw [Matrix.conjTranspose_one, Matrix.one_mul]) G
    rw [ht, ← Matrix.smul_mul, ← Matrix.mul_smul, hnorm, Matrix.mul_one, hV]

/--
info: 'FilteredBellRestriction.compressFilter_posDef_normalized' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms compressFilter_posDef_normalized

/-- An isometric input restriction preserves each admissible ratio as a witness
for the full channel. -/
theorem compressed_filter_ratios_subset
    (V : Matrix A S ℂ) (hV : Vᴴ * V = 1)
    (G : Matrix (A × E') (A × E') ℂ) (hG : G.PosDef)
    (hnorm : (Fintype.card E' : ℝ)⁻¹ • partialTraceRight G = 1)
    (N : QuantumChannel A (A × E')) (hN : ∀ X, act N X = filterAction G X)
    (M : QuantumChannel S (S × E')) (hM : ∀ X, act M X = filterAction (compressFilter V G) X)
    (γ : ℝ) (orth : Bool) :
    ratios M γ orth ⊆ ratios N γ orth := by
  let H := compressFilter V G
  let J := V ⊗ₖ (1 : Matrix E' E' ℂ)
  let P := CFC.sqrt G
  let Q := CFC.sqrt H
  let W := P * J * Q⁻¹
  have hH : H.PosDef := (compressFilter_posDef_normalized V hV G hG hnorm).1
  have hP : P.IsHermitian := (CFC.sqrt_nonneg G).posSemidef.isHermitian
  have hQ : Q.IsHermitian := (CFC.sqrt_nonneg H).posSemidef.isHermitian
  have hPP : P * P = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hQQ : Q * Q = H := CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg
  have hQu : IsUnit Q := isUnit_mul_self_iff.mp (hQQ ▸ hH.isUnit)
  let _ := hQu.invertible
  have hWQ : W * Q = P * J := by
    dsimp only [W]
    rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one]
  have hQW : Q * Wᴴ = Jᴴ * P := by
    simpa only [Matrix.conjTranspose_mul, hP.eq, hQ.eq] using
      congrArg Matrix.conjTranspose hWQ
  have hW : Wᴴ * W = 1 := by
    calc
      _ = Q⁻¹ * (Jᴴ * (P * P) * J) * Q⁻¹ := by
        simp only [W, Matrix.conjTranspose_mul, hP.eq, hQ.inv.eq, Matrix.mul_assoc]
      _ = Q⁻¹ * (Q * Q) * Q⁻¹ := by rw [hPP, hQQ]; rfl
      _ = 1 := by rw [← Matrix.mul_assoc Q⁻¹, Matrix.inv_mul_of_invertible,
        Matrix.one_mul, Matrix.mul_inv_of_invertible]
  apply ratios_subset_of_intertwining N M V W hV hW
  intro X
  rw [hN, hM]
  have hX : embed V X ⊗ₖ (1 : Matrix E' E' ℂ) = J * (X ⊗ₖ (1 : Matrix E' E' ℂ)) * Jᴴ := by
    simp only [embed, J, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  unfold filterAction
  rw [hX]
  simp only [Matrix.mul_smul, Matrix.smul_mul, embed]
  congr 1
  calc
    _ = (P * J) * (X ⊗ₖ (1 : Matrix E' E' ℂ)) * (Jᴴ * P) := by
      simp only [P, Matrix.mul_assoc]
    _ = _ := by
      rw [← hWQ, ← hQW]
      simp only [H, Q, Matrix.mul_assoc]

/--
info: 'FilteredBellRestriction.compressed_filter_ratios_subset' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms compressed_filter_ratios_subset

section ThreeByTwo

open D5.S3.Quantum.Divergence.ConditionalExpansion (exists_bell_kernel_ratio_le)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)
open UnitaryReconstruction.LiuWildChoiObstruction (pairMatrix)

private abbrev Input := Bool ⊕ Unit
private abbrev Env := Bool

private def diagonalWeight (p : Input × Env) : ℝ :=
  p.1.elim (fun b => if b = p.2 then 1 / 2 else 3 / 2) (fun _ => 1)

/-- In the product basis the three rows of the diagonal are
`(1/2, 3/2)`, `(3/2, 1/2)`, and `(1, 1)`. -/
def threeByTwoFilter : Matrix (Input × Env) (Input × Env) ℂ :=
  Matrix.diagonal (fun p => (diagonalWeight p : ℂ))

private def firstTwo : Matrix Input Bool ℂ :=
  fun i j => if i = Sum.inl j then 1 else 0

private theorem firstTwo_isometry : firstTwoᴴ * firstTwo = 1 := by
  ext i j
  cases i <;> cases j <;>
    norm_num [firstTwo, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
      Fintype.sum_bool]

private theorem traceRight_diagonal {a b : Type} [DecidableEq a] [DecidableEq b] [Fintype b]
    (f : a × b → ℂ) :
    partialTraceRight (Matrix.diagonal f) = Matrix.diagonal (fun i => ∑ e, f (i, e)) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [partialTraceRight]
  · simp [partialTraceRight, hij]

private theorem traceLeft_diagonal {a b : Type} [DecidableEq a] [DecidableEq b] [Fintype a]
    (f : a × b → ℂ) :
    partialTraceLeft (Matrix.diagonal f) = Matrix.diagonal (fun i => ∑ a, f (a, i)) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [partialTraceLeft]
  · simp [partialTraceLeft, hij]

private theorem diagonal_inv_of_nonzero {n : Type} [Fintype n] [DecidableEq n]
    (v : n → ℂ) (hv : ∀ i, v i ≠ 0) :
    (Matrix.diagonal v)⁻¹ = Matrix.diagonal (fun i => (v i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  have h : (fun i => v i * (v i)⁻¹) = fun _ => 1 := funext fun i => mul_inv_cancel₀ (hv i)
  rw [h, Matrix.diagonal_one]

private theorem threeByTwo_posDef : threeByTwoFilter.PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  rintro ⟨i, e⟩
  rcases i with b | u
  · cases b <;> cases e <;> norm_num [diagonalWeight]
  · norm_num [diagonalWeight]

private theorem diagonalWeight_ne_zero (p : Input × Env) : (diagonalWeight p : ℂ) ≠ 0 :=
  ((Matrix.posDef_diagonal_iff.mp threeByTwo_posDef) p).ne'

private theorem threeByTwo_normalized :
    (Fintype.card Env : ℝ)⁻¹ • partialTraceRight threeByTwoFilter = 1 := by
  rw [threeByTwoFilter, traceRight_diagonal, ← Matrix.diagonal_smul, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases i with b | u
  · cases b <;> norm_num [Fintype.sum_bool, diagonalWeight, Complex.real_smul]
  · norm_num [Fintype.sum_bool, diagonalWeight, Complex.real_smul]

private theorem threeByTwo_restricted :
    compressFilter firstTwo threeByTwoFilter =
      Matrix.diagonal (fun p : Bool × Env => (diagonalWeight (Sum.inl p.1, p.2) : ℂ)) := by
  ext ⟨i, f⟩ ⟨j, g⟩
  cases i <;> cases f <;> cases j <;> cases g <;>
    norm_num [compressFilter, firstTwo, threeByTwoFilter, diagonalWeight,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_bool]

private theorem threeByTwo_inverse_right_norm :
    ‖((Fintype.card Env : ℝ)⁻¹ • partialTraceRight threeByTwoFilter⁻¹)‖ = 4 / 3 := by
  let L : Input → ℂ := Sum.elim (fun _ => 4 / 3) (fun _ => 1)
  have hL : (Fintype.card Env : ℝ)⁻¹ • partialTraceRight threeByTwoFilter⁻¹ =
      Matrix.diagonal L := by
    rw [threeByTwoFilter, diagonal_inv_of_nonzero _ diagonalWeight_ne_zero,
      traceRight_diagonal, ← Matrix.diagonal_smul]
    congr 1
    funext i
    rcases i with b | u
    · cases b <;>
        norm_num [L, Fintype.sum_bool, diagonalWeight, Complex.real_smul]
    · norm_num [L, Fintype.sum_bool, diagonalWeight, Complex.real_smul]
  rw [hL, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    rintro (b | u) <;> norm_num [L, norm_div]
  · have h := norm_le_pi_norm (f := L) (Sum.inl false)
    norm_num [L, norm_div] at h ⊢
    exact h

private theorem threeByTwo_restricted_bell_bound :
    rtrace (((Fintype.card Bool : ℝ)⁻¹ •
      partialTraceLeft (compressFilter firstTwo threeByTwoFilter)⁻¹)⁻¹) /
      Fintype.card Env = 3 / 4 := by
  have hM : (Fintype.card Bool : ℝ)⁻¹ •
      partialTraceLeft (compressFilter firstTwo threeByTwoFilter)⁻¹ =
      Matrix.diagonal (fun _ : Env => (4 / 3 : ℂ)) := by
    rw [threeByTwo_restricted, diagonal_inv_of_nonzero _
      (fun p : Bool × Env => diagonalWeight_ne_zero (Sum.inl p.1, p.2)), traceLeft_diagonal,
      ← Matrix.diagonal_smul]
    congr 1
    funext f
    cases f <;> norm_num [Fintype.sum_bool, diagonalWeight, Complex.real_smul]
  rw [hM, diagonal_inv_of_nonzero _ (by intro _; norm_num)]
  norm_num [rtrace, Matrix.trace_diagonal, Fintype.sum_bool]

private theorem threeByTwo_full_bell_bound :
    rtrace (((Fintype.card Input : ℝ)⁻¹ • partialTraceLeft threeByTwoFilter⁻¹)⁻¹) /
      Fintype.card Env = 9 / 11 := by
  have hM : (Fintype.card Input : ℝ)⁻¹ • partialTraceLeft threeByTwoFilter⁻¹ =
      Matrix.diagonal (fun _ : Env => (11 / 9 : ℂ)) := by
    rw [threeByTwoFilter, diagonal_inv_of_nonzero _ diagonalWeight_ne_zero, traceLeft_diagonal,
      ← Matrix.diagonal_smul]
    congr 1
    funext f
    cases f <;> norm_num [Fintype.sum_sum_type, Fintype.sum_bool, diagonalWeight,
      Complex.real_smul]
  rw [hM, diagonal_inv_of_nonzero _ (by intro _; norm_num)]
  norm_num [rtrace, Matrix.trace_diagonal, Fintype.sum_bool]

/-- The actual finite-reference conditional trace-distance expansion coefficient
of the three-by-two diagonal filter is `3/4`. The full-input Bell expression
is `9/11`. -/
theorem threeByTwo_strict_bell_bound :
    ∃ N : QuantumChannel Input (Input × Env),
      (∀ X, act N X = filterAction threeByTwoFilter X) ∧
      sInf (ratios N 1 false) = 3 / 4 ∧
      rtrace (((Fintype.card Input : ℝ)⁻¹ • partialTraceLeft threeByTwoFilter⁻¹)⁻¹) /
        Fintype.card Env = 9 / 11 ∧
      sInf (ratios N 1 false) <
        rtrace (((Fintype.card Input : ℝ)⁻¹ • partialTraceLeft threeByTwoFilter⁻¹)⁻¹) /
          Fintype.card Env := by
  let G := threeByTwoFilter
  let H := compressFilter firstTwo G
  obtain ⟨N, hN⟩ := exists_filtered_channel G threeByTwo_posDef threeByTwo_normalized
  obtain ⟨hH, hHnorm⟩ := compressFilter_posDef_normalized firstTwo firstTwo_isometry
    G threeByTwo_posDef threeByTwo_normalized
  obtain ⟨M, hM⟩ := exists_filtered_channel H hH hHnorm
  have hsubset := compressed_filter_ratios_subset firstTwo firstTwo_isometry G threeByTwo_posDef
    threeByTwo_normalized N hN M hM 1 false
  have hd : 2 ≤ Fintype.card Bool := by simp
  have hne : (ratios M 1 false).Nonempty := by
    obtain ⟨ρ, σ, horth, hgap, _⟩ := exists_bell_kernel_ratio_le M hd 1 zero_lt_one
    exact ⟨_, Option Bool, inferInstance, inferInstance, pairMatrix ρ, pairMatrix σ,
      density_posSemidef ρ, ρ.2.2, density_posSemidef σ, σ.2.2, fun _ => horth, hgap, rfl⟩
  have hlower (x : ℝ) (hx : x ∈ ratios N 1 false) : 3 / 4 ≤ x := by
    have h := filtered_channel_ratio_lower_bound G threeByTwo_posDef threeByTwo_normalized
      N hN 1 false hx
    rw [show G = threeByTwoFilter from rfl, threeByTwo_inverse_right_norm] at h
    norm_num at h ⊢
    exact h
  have hupper := filtered_channel_bell_upper_bound H hH hHnorm M hM hd 1 le_rfl false
  rw [show H = compressFilter firstTwo threeByTwoFilter from rfl,
    threeByTwo_restricted_bell_bound] at hupper
  have hcoeff : sInf (ratios N 1 false) = 3 / 4 :=
    le_antisymm ((csInf_le_csInf ⟨_, hlower⟩ hne hsubset).trans hupper)
      (le_csInf (hne.mono hsubset) hlower)
  refine ⟨N, hN, hcoeff, threeByTwo_full_bell_bound, ?_⟩
  rw [hcoeff, threeByTwo_full_bell_bound]
  norm_num

/--
info: 'FilteredBellRestriction.threeByTwo_strict_bell_bound' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms threeByTwo_strict_bell_bound

end ThreeByTwo

end FilteredBellRestriction
