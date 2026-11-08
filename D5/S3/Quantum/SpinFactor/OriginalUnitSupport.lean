/- GID: D5/S3/Quantum/SpinFactor/OriginalUnitSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinFactor/OriginalUnitSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.PosDef, mathlib/module/Mathlib.Algebra.QuadraticDiscriminant]
   utility: none
   digest: Norm-support readings of an original unit output annihilate its second label. -/

module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Tactic

/-! A unit-row prerequisite on an arbitrary, possibly incomplete original carrier.
The total relation has no linearity or output-closure assumption. The original
generated three-axis and affine-identification theorems are not asserted here. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Matrix ComplexOrder

namespace D5.S3.Quantum.SpinFactor.OriginalUnitSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original directed two-table, with its real Jordan diagonal. -/
def table (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (α : E →ₗ[ℝ] ℝ) (a b : E) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(α (S a a) : ℂ), (α (S a b) : ℂ) - Complex.I * (α (D a b) : ℂ);
     (α (S b a) : ℂ) - Complex.I * (α (D b a) : ℂ), (α (S b b) : ℂ)]

/-- All original positive readings, retaining their actual, unnormalized masses. -/
def P2 (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (P : Set (E →ₗ[ℝ] ℝ)) : Prop :=
  ∀ α ∈ P, ∀ a b, (table S D α a b).PosSemidef

/-- The complete element-valued original balance, on all three original labels. -/
def PB (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E) : Prop :=
  ∀ a b c,
    D (b + (D a b - S a c)) (c + (S a b + D a c)) -
      D (b - (D a b - S a c)) (c - (S a b + D a c)) =
        -(2 : ℝ) • S b (D a b - S a c) -
          (2 : ℝ) • S c (S a b + D a c)

private theorem determinant_bound
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (P : Set (E →ₗ[ℝ] ℝ)) (hP : P2 S D P)
    (hc : ∀ x y, S x y = S y x)
    (α : E →ₗ[ℝ] ℝ) (hα : α ∈ P) (a b : E) :
    (α (D a b)) ^ 2 ≤ α (S a a) * α (S b b) - (α (S a b)) ^ 2 := by
  have hs : α (D b a) = -α (D a b) := by
    have h := congrArg Complex.im ((hP α hα a b).1.apply 0 1)
    simpa [table] using h
  have hd := (Complex.nonneg_iff.mp (hP α hα a b).det_nonneg).1
  simp [table, Matrix.det_fin_two, hc b a, hs,
    Complex.mul_re, Complex.mul_im] at hd
  nlinarith

private theorem square_nonneg
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (P : Set (E →ₗ[ℝ] ℝ)) (hP : P2 S D P)
    (α : E →ₗ[ℝ] ℝ) (hα : α ∈ P) (x : E) : 0 ≤ α (S x x) := by
  have h := (hP α hα x x).diag_nonneg (i := 0)
  simpa [table] using (Complex.nonneg_iff.mp h).1

private theorem scalar_pair_zero
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (P : Set (E →ₗ[ℝ] ℝ)) (hP : P2 S D P)
    (hc : ∀ x y, S x y = S y x) (u : E) (hu : ∀ x, S u x = x)
    (hsep : ∀ x, (∀ α ∈ P, α x = 0) → x = 0) (r s : ℝ) :
    D (r • u) (s • u) = 0 := by
  apply hsep
  intro α hα
  have h := determinant_bound S D P hP hc α hα (r • u) (s • u)
  simp [map_smul, hu, smul_eq_mul] at h
  nlinarith [sq_nonneg (α (D (r • u) (s • u)))]

private theorem null_square_orthogonal
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hc : ∀ x y, B x y = B y x)
    (hp : ∀ x, 0 ≤ B x x) (w : E) (hw : B w w = 0) (x : E) :
    B w x = 0 := by
  have hd := discrim_le_zero (a := B x x) (b := 2 * B w x) (c := 0) (fun t : ℝ => by
    have h := hp (w + t • x)
    simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hw, hc x w] at h
    nlinarith only [h])
  simp only [discrim, mul_zero, sub_zero] at hd
  nlinarith [sq_nonneg (B w x)]

/-- A norm-support state of a nonzero original unit output reads its second
label and its Jordan product with that output as zero. This is a finite P2/PB
consequence; the state is used only to read the same fixed original output. -/
theorem support_unit_obstruction
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (P : Set (E →ₗ[ℝ] ℝ)) (hP : P2 S D P) (hPB : PB S D)
    (hc : ∀ x y, S x y = S y x) (u : E) (hu : ∀ x, S u x = x)
    (hsq : ∀ x, ‖S x x‖ = ‖x‖ ^ 2)
    (hsep : ∀ x, (∀ α ∈ P, α x = 0) → x = 0)
    (μ : ℝ) (b : E) (α : E →ₗ[ℝ] ℝ) (hα : α ∈ P)
    (hαu : α u = 1) (hαnorm : ∀ x, |α x| ≤ ‖x‖)
    (Z : ℝ) (hZ : Z ≠ 0) (hread : α (D (μ • u) b) = Z)
    (hnorm : |Z| = ‖D (μ • u) b‖) :
    α (S b (D (μ • u) b)) = 0 ∧ α b = 0 := by
  let h := D (μ • u) b
  let B := S.compr₂ α
  have hBc (x y : E) : B x y = B y x := congrArg α (hc x y)
  have hBu (x : E) : B u x = α x := congrArg α (hu x)
  have hBp (x : E) : 0 ≤ B x x := square_nonneg S D P hP α hα x
  have hhh : B h h ≤ Z ^ 2 := by
    calc
      B h h ≤ |α (S h h)| := le_abs_self _
      _ ≤ ‖S h h‖ := hαnorm _
      _ = Z ^ 2 := by rw [hsq, ← hnorm, sq_abs]
  let w := h - Z • u
  have hww : B w w = 0 := by
    have hp := hBp w
    dsimp [w] at hp ⊢
    simp [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hBu, hBc h u, hαu, show α h = Z from hread] at hp ⊢
    nlinarith
  have hW (x : E) : B w x = 0 := null_square_orthogonal B hBc hBp w hww x
  have hWr (x : E) : B x w = 0 := (hBc x w).trans (hW x)
  have hh (x : E) : B h x = Z * α x := by
    have ht := hW x
    simpa [w, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hBu, sub_eq_zero] using ht
  let k := μ * Z / (1 + μ ^ 2)
  have hk : (1 + μ ^ 2) * k = μ * Z := by dsimp [k]; field_simp
  let ν := h - (μ * k) • u
  let ω := μ • b
  let rp := b + ν
  let rm := b - ν
  let sp := k • u + ω
  let sm := k • u - ω
  have hsp : sp = μ • rp - μ • w := by
    calc
      sp = μ • rp - μ • w + ((1 + μ ^ 2) * k - μ * Z) • u := by
        dsimp [sp, rp, ν, ω, w]; module
      _ = μ • rp - μ • w := by rw [hk, sub_self, zero_smul, add_zero]
  have hsm : sm = -μ • rm - μ • w := by
    calc
      sm = -μ • rm - μ • w + ((1 + μ ^ 2) * k - μ * Z) • u := by
        dsimp [sm, rm, ν, ω, w]; module
      _ = -μ • rm - μ • w := by rw [hk, sub_self, zero_smul, add_zero]
  have gram_zero (r s : E) (v : ℝ) (hs : s = v • r - μ • w) :
      B r r * B s s - (B r s) ^ 2 = 0 := by
    rw [hs]
    simp [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hW, hWr]
    ring
  have read_zero (r s : E) (hg : B r r * B s s - (B r s) ^ 2 = 0) :
      α (D r s) = 0 := by
    have hd := determinant_bound S D P hP hc α hα r s
    change (α (D r s)) ^ 2 ≤ B r r * B s s - (B r s) ^ 2 at hd
    rw [hg] at hd
    nlinarith [sq_nonneg (α (D r s))]
  have hpz := read_zero rp sp (gram_zero rp sp μ hsp)
  have hmz := read_zero rm sm (gram_zero rm sm (-μ) hsm)
  have hinner := scalar_pair_zero S D P hP hc u hu hsep μ k
  have hp := congrArg α (hPB (μ • u) b (k • u))
  have hν : D (μ • u) b - S (μ • u) (k • u) = ν := by
    simp [ν, h, map_smul, hu, smul_smul, mul_comm]
  have hω : S (μ • u) b + D (μ • u) (k • u) = ω := by
    simp [ω, map_smul, hu, hinner]
  rw [hν, hω] at hp
  change α (D rp sp - D rm sm) = _ at hp
  rw [map_sub, hpz, hmz] at hp
  have hhbu : B b u = α b := (hBc b u).trans (hBu b)
  have hbh : B b h = Z * α b := (hBc b h).trans (hh b)
  have he : α (S b h) = 0 := by
    change B b h = 0
    change (0 : ℝ) - 0 =
      α (-(2 : ℝ) • S b ν - (2 : ℝ) • S (k • u) ω) at hp
    simp only [map_sub, α.map_smul, smul_eq_mul] at hp
    change 0 - 0 = -(2 : ℝ) * B b ν - 2 * B (k • u) ω at hp
    simp [ν, ω, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hBu, hhbu] at hp
    nlinarith only [hp]
  refine ⟨he, ?_⟩
  change B b h = 0 at he
  rw [hbh] at he
  exact (mul_eq_zero.mp he).resolve_left hZ

end D5.S3.Quantum.SpinFactor.OriginalUnitSupport
