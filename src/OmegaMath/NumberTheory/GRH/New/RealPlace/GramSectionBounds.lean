import OmegaMath.NumberTheory.GRH.Lib.General.Analysis.HolomorphicIntegral
import OmegaMath.NumberTheory.GRH.New.RealPlace.FrameNorm
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Real-place Bessel integrals: band limits, energy and open-cell bound (see
New.Filling.FillingData).

This file: Definition of open-cell section, its domain, differentiability, norm and derivative
bounds. -/

noncomputable section


open Matrix Function Fin Metric Real Complex Norms.L2Operator Shape
variable {𝔰 : Shape} (x) (Z : 𝔰.FrameMat)

/-- For a complex n×n matrix Z, n = ϱ + 1 the length of the frame, the last diagonal entry ξ of
Z⁻¹. -/
def invCorner := Z⁻¹ 𝔰.top 𝔰.top

/-- The set Ω of invertible complex (ϱ+1)×(ϱ+1) matrices Z such that the last diagonal entry ξ
of Z⁻¹ satisfies |ξ| < 1. -/
def Shape.openCell := {Z : 𝔰.FrameMat | det Z ≠ 0 ∧ ‖invCorner Z‖ < 1}

/-- For a (ϱ+1)×(ϱ+1) complex matrix Z, the real number 1 − |ξ|², ξ the last diagonal entry of
Z⁻¹. -/
def cornerDefect := 1 - ‖invCorner Z‖ ^ 2

/-- Z lies in Ω (`Shape.openCell`), and ‖Z‖, ‖Z⁻¹‖ (operator norms) and δ^{−1/2} are at most P,
where δ = 1 − |ξ|², ξ the last diagonal entry of Z⁻¹. -/
def IsBoundedInCell P := Z ∈ openCell ∧ ‖Z⁻¹‖ ≤ P ∧ ‖Z‖ ≤ P ∧ (√(cornerDefect Z))⁻¹ ≤ P

/-- For a complex number x, the (ϱ+1)×(ϱ+1) diagonal matrix diag(1, …, 1, x). -/
def diagLast : 𝔰.FrameMat := diagonal (snoc 1 x)

variable (W := Zᴴ) (s := (1 - invCorner Z * invCorner W).sqrt)

/-- For Z and W (by default Zᴴ), the matrix with last row (0, …, 0, −1) and other entries
−(W⁻¹)_{a,last}(Z⁻¹)_{last,b}, halved unless b is last. -/
def sectionCoeff := diagLast (𝔰 := 𝔰) 0 - 1 - diagLast (𝔰 :=
  𝔰) 0 * W⁻¹ * (1 - diagLast (𝔰 := 𝔰) 2⁻¹) * Z⁻¹ * diagLast (𝔰 := 𝔰) 2

/-- The matrix (F·Y + F'·diag(1, …, 1, s))·Z, with F the frame, F' = (e*₁, …, e*_ϱ, x_{k₀}), Y =
`sectionCoeff`; its columns are the images of the frame under γ_Z. -/
def sectionFrame := (𝔰.frameCols * sectionCoeff Z W + 𝔰.dualFrameCols * @diagLast 𝔰 s) * Z

/-- The matrix 1 − FFᴴ − F'F'ᴴ + SFᴴ + (FW⁻¹ − S·Y(W, Z))·diag(1, …, 1, s⁻¹)·F'ᴴ, with S =
`sectionFrame`, Y = `sectionCoeff`; by default W = Zᴴ, s = √δ. -/
def sectionMatrix := 1 + (sectionFrame Z W - 𝔰.frameCols) * 𝔰.frameColsᴴ + ((𝔰.frameCols * W⁻¹ -
  sectionFrame Z W * sectionCoeff W Z) * @diagLast 𝔰 s⁻¹ - 𝔰.dualFrameCols) * 𝔰.dualFrameColsᴴ

variable {Z} (h : Z ∈ 𝔰.openCell)
attribute [local simp] gramDiscReal frameDisc cornerDefect mul_conj' forall_fin_succ' diagLast
  l2_opNorm_conjTranspose openCell invCorner
  dist_eq_norm isUnit_iff_isUnit_det slitPlane_ne_zero mem_slitPlane_of_norm_lt_one Complex.sqrt
attribute [local simp ←] conjTranspose_nonsing_inv ofReal_pow

lemma gramDiscReal_eq (h : det Z ≠ 0) : gramDiscReal Z = ‖det Z‖ ^ 2 * cornerDefect Z := by
  simp [Z.inv_def, adjugate_fin_succ_eq_det_submatrix', field]; rfl

lemma mem_openCell_iff :
  Z ∈ openCell ↔ 0 < gramDiscReal Z := by by_cases Z.det = 0 <;> simp_all [↓gramDiscReal_eq]

@[fun_prop] lemma continuous_gramDiscReal :
  Continuous (@gramDiscReal 𝔰) := by fun_prop [gramDiscReal, frameDisc, leadingMinor]

/-- The open cell, the domain of the double coset section, is an open set. -/
lemma isOpen_openCell : IsOpen 𝔰.openCell :=
  Set.ext (@mem_openCell_iff 𝔰) ▸ isOpen_Ioi.preimage continuous_gramDiscReal

include h

lemma differentiableAt_sectionMatrix_uncurry (o : W ∈ openCell) :
  DifferentiableAt ℂ (sectionMatrix · ·).uncurry (Z, W) := by
  repeat erw [differentiableAt_pi] <;> intro
  have : ∀ i j, Differentiable ℂ (@diagLast 𝔰 · i j) := by simp [diagonal, eq_comm]
  have := mul_lt_mul'' h.2 o.2
  simp_all only [uncurry, sectionMatrix, sectionFrame, sectionCoeff, invCorner,
    nonsing_inv_eq_ringInverse, mul_apply,
    Matrix.add_apply, sub_eq_add_neg, Matrix.neg_apply]; fun_prop (disch := simp_all)

lemma cornerDefect_pos : 0 < cornerDefect Z := by aesop

@[simp] lemma sqrt_eq_sqrt_cornerDefect : (1 - invCorner Z * invCorner Zᴴ).sqrt = √(cornerDefect
  Z) := by simp_all [sqrt_eq_rpow, ofReal_cpow, le_of_lt]

/-- For Z in the open set Ω (Z invertible, with last diagonal entry of Z⁻¹ of absolute value
less than 1), the matrix-valued map `sectionMatrix`, as a function of its matrix argument,
is real-differentiable at Z. -/
lemma differentiableAt_sectionMatrix : DifferentiableAt ℝ sectionMatrix Z :=
  .comp Z (f := fun Z ↦ (Z, star Z))
  ((differentiableAt_sectionMatrix_uncurry Zᴴ h (by simpa)).restrictScalars ℝ) (by fun_prop)

omit h in
/-- Let r > 0, P ≥ 8, and let every y within r of Z lie in Ω with ‖y⁻¹‖, ‖y‖, δ(y)^{−1/2} ≤ P.
Then the matrix of γ_Z has norm ≤ P¹², and its real derivative in Z has norm ≤ 2P¹²/r. -/
lemma norm_sectionMatrix_le (_ : Z ∈ 𝔰.openCell) {P r} (hr : 0 < r) (hP : 8 ≤ P)
  (H : ∀ y ∈ ball Z r, IsBoundedInCell y P) :
  ‖sectionMatrix Z‖ ≤ P ^ 12 ∧ ‖fderiv ℝ sectionMatrix Z‖ ≤ 2 * P ^ 12 / r :=
  have b {x y} (hp : (x, y) ∈ ball (Z, Zᴴ) r) : _ ∧ ‖sectionMatrix x y‖ ≤ P ^ 12 := by
    simp [IsBoundedInCell, ← (y - _).l2_opNorm_conjTranspose] at hp H
    obtain ⟨⟨o, _, _, q⟩, _, o', _, -⟩ := H _ hp.1, (by simp [pi_norm_le_iff_of_nonempty] :
      ∀ s, ‖diagLast (𝔰 := 𝔰) s‖ ≤ 1 + ‖s‖), by simpa using H _ hp.2
    use differentiableAt_sectionMatrix_uncurry _ o o'; delta sectionMatrix sectionFrame
      sectionCoeff; trans; repeat' first
      | apply_assumption (transparency := .reducible) [mul_le_mul_of_nonneg, norm_add_le_of_le,
        norm_sub_le_of_le, norm_inclMatrix_le_one, (l2_opNorm_mul ..).trans] | positivity | simp
              [Injective, norm_cpow_of_imp, ← by simpa using sqrt_eq_rpow] | rfl
    grw [← (_ : 4⁻¹ * cornerDefect x ≤ ‖_‖), norm_sub_le, norm_mul, o.2, o'.2,
      sqrt_le_self_iff.2] <;> simp [o]; grw [q, ← sub_nonneg]
    obtain ⟨t, _, rfl⟩ := exists_nonneg_add_of_le hP; ring; bound
    grw [← norm_sub_norm_le, norm_mul, o'.2, norm_one]; nlinarith
  ⟨(b (by simpa)).2, norm_fderiv_le_of_lip' ℝ (by bound) (.mono (ball_mem_nhds Z hr) fun y ↦
    by simpa [two_mul, ← conjTranspose_sub] using
    norm_sub_le_of_holomorphic_bdd (Prod.rec @b) (y, yᴴ))⟩
