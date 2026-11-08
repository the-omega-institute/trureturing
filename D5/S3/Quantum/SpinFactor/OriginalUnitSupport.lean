/- GID: D5/S3/Quantum/SpinFactor/OriginalUnitSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinFactor/OriginalUnitSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.PosDef]
   utility: none
   digest: Norm-support readings of an original unit output annihilate its second label. -/

module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Tactic
public import D5.S3.Topology.OrderNormSupport

/-! A unit-row prerequisite on an arbitrary, possibly incomplete original carrier.
The total relation has no linearity or output-closure assumption. The original
generated three-axis and affine-identification theorems are not asserted here.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/28178. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Matrix ComplexOrder

namespace D5.S3.Quantum.SpinFactor.OriginalUnitSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original directed two-table, including its unknown diagonal responses. -/
def table (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (α : E →ₗ[ℝ] ℝ) (a b : E) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(α (S a a) : ℂ) - Complex.I * (α (D a a) : ℂ),
     (α (S a b) : ℂ) - Complex.I * (α (D a b) : ℂ);
     (α (S b a) : ℂ) - Complex.I * (α (D b a) : ℂ),
     (α (S b b) : ℂ) - Complex.I * (α (D b b) : ℂ)]

/-- All original positive readings, retaining their actual, unnormalized masses. -/
def P2 (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (P : Set (E →ₗ[ℝ] ℝ)) : Prop :=
  ∀ α ∈ P, ∀ a b, (table S D α a b).PosSemidef

/-- The real square readout of a pair of original labels. -/
def squareReadout (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (α : E →ₗ[ℝ] ℝ) (b c : E) : ℝ :=
  α (S b b) + α (S c c) + 2 * α (D b c)

/-- The complete original reading balance, on all three original labels. -/
def PB (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (P : Set (E →ₗ[ℝ] ℝ)) : Prop :=
  ∀ α ∈ P, ∀ a b c,
    squareReadout S D α (b + (D a b - S a c)) (c + (S a b + D a c)) =
      squareReadout S D α (b - (D a b - S a c)) (c - (S a b + D a c))

private theorem finite_difference
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (P : Set (E →ₗ[ℝ] ℝ)) (hPB : PB S D P)
    (hc : ∀ x y, S x y = S y x)
    (hsep : ∀ x, (∀ α ∈ P, α x = 0) → x = 0) (a b c : E) :
    D (b + (D a b - S a c)) (c + (S a b + D a c)) -
      D (b - (D a b - S a c)) (c - (S a b + D a c)) =
        -(2 : ℝ) • S b (D a b - S a c) -
          (2 : ℝ) • S c (S a b + D a c) := by
  apply sub_eq_zero.mp
  apply hsep
  intro α hα
  let ν := D a b - S a c
  let ω := S a b + D a c
  have hp : squareReadout S D α (b + ν) (c + ω) =
      squareReadout S D α (b - ν) (c - ω) := hPB α hα a b c
  change α (D (b + ν) (c + ω) - D (b - ν) (c - ω) -
    (-(2 : ℝ) • S b ν - (2 : ℝ) • S c ω)) = 0
  simp only [squareReadout, map_add, map_sub, LinearMap.add_apply,
    LinearMap.sub_apply] at hp
  rw [hc ν b, hc ω c] at hp
  simp only [map_sub, map_smul, smul_eq_mul]
  linarith only [hp]

private theorem determinant_bound
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (P : Set (E →ₗ[ℝ] ℝ)) (hP : P2 S D P)
    (hc : ∀ x y, S x y = S y x)
    (α : E →ₗ[ℝ] ℝ) (hα : α ∈ P) (a b : E) :
    (α (D a b)) ^ 2 ≤ α (S a a) * α (S b b) - (α (S a b)) ^ 2 := by
  have ha : α (D a a) = 0 := by
    have h := congrArg Complex.im ((hP α hα a b).1.apply 0 0)
    simp [table] at h
    linarith
  have hb : α (D b b) = 0 := by
    have h := congrArg Complex.im ((hP α hα a b).1.apply 1 1)
    simp [table] at h
    linarith
  have hs : α (D b a) = -α (D a b) := by
    have h := congrArg Complex.im ((hP α hα a b).1.apply 0 1)
    simpa [table] using h
  have hd := (Complex.nonneg_iff.mp (hP α hα a b).det_nonneg).1
  simp [table, Matrix.det_fin_two, hc b a, ha, hb, hs,
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
    (P : Set (E →ₗ[ℝ] ℝ)) (hP : P2 S D P) (hPB : PB S D P)
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
  have hp := congrArg α (finite_difference S D P hPB hc hsep (μ • u) b (k • u))
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


private theorem p2_skew_original
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (P : Set (E →ₗ[ℝ] ℝ)) (hP : P2 S D P)
    (hsep : ∀ x, (∀ α ∈ P, α x = 0) → x = 0) (a b : E) :
    D b a = -D a b := by
  apply eq_neg_iff_add_eq_zero.mpr
  apply hsep
  intro α hα
  have h := congrArg Complex.im ((hP α hα a b).1.apply 0 1)
  simp [table] at h
  simpa only [map_add] using (by linarith : α (D b a) + α (D a b) = 0)

private def quadraticElement (S : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (D : E → E → E) (a b : E) (z : Fin 2 → ℂ) : E :=
  ((z 0).re ^ 2 + (z 0).im ^ 2) • S a a +
  ((z 1).re ^ 2 + (z 1).im ^ 2) • S b b +
  (2 * ((z 0).re * (z 1).re + (z 0).im * (z 1).im)) • S a b +
  (2 * ((z 0).re * (z 1).im - (z 0).im * (z 1).re)) • D a b

private theorem quadratic_read
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (hc : ∀ x y, S x y = S y x) (hsk : ∀ a b, D b a = -D a b)
    (β : E →ₗ[ℝ] ℝ) (a b : E) (z : Fin 2 → ℂ) :
    star z ⬝ᵥ (table S D β a b *ᵥ z) =
      (β (quadraticElement S D a b z) : ℂ) := by
  have hself (x : E) : D x x = 0 := by
    have h := hsk x x
    have hz : (2 : ℝ) • D x x = 0 := by rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp h
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  apply Complex.ext <;>
    simp [table, quadraticElement, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      hself, hsk a b, hc b a, map_add, map_smul, smul_eq_mul,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, pow_two] <;> ring

private theorem positive_p2
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (P : Set (E →ₗ[ℝ] ℝ)) (hP : P2 S D P)
    (hc : ∀ x y, S x y = S y x)
    (hsep : ∀ x, (∀ α ∈ P, α x = 0) → x = 0)
    (C : Set E) (hexact : ∀ x, x ∈ C ↔ ∀ α ∈ P, 0 ≤ α x) :
    P2 S D {β | ∀ x ∈ C, 0 ≤ β x} := by
  have hsk := p2_skew_original S D P hP hsep
  intro β hβ a b
  have hself (x : E) : D x x = 0 := by
    have h := hsk x x
    have hz : (2 : ℝ) • D x x = 0 := by rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp h
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [table, Matrix.conjTranspose_apply, hself, hsk a b, hc b a, sub_eq_add_neg]
  · intro z
    rw [quadratic_read S D hc hsk]
    have hw : quadraticElement S D a b z ∈ C := by
      apply (hexact _).mpr
      intro α hα
      have h := (hP α hα a b).dotProduct_mulVec_nonneg z
      rw [quadratic_read S D hc hsk] at h
      exact_mod_cast h
    exact_mod_cast hβ _ hw

private theorem pb_any_reading
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (P : Set (E →ₗ[ℝ] ℝ)) (hPB : PB S D P)
    (hc : ∀ x y, S x y = S y x)
    (hsep : ∀ x, (∀ α ∈ P, α x = 0) → x = 0) :
    PB S D Set.univ := by
  intro β _ a b c
  have hp := congrArg β (finite_difference S D P hPB hc hsep a b c)
  let ν := D a b - S a c
  let ω := S a b + D a c
  change squareReadout S D β (b + ν) (c + ω) =
    squareReadout S D β (b - ν) (c - ω)
  change β (D (b + ν) (c + ω) - D (b - ν) (c - ω)) =
    β (-(2 : ℝ) • S b ν - (2 : ℝ) • S c ω) at hp
  simp only [map_sub, map_smul, smul_eq_mul] at hp
  simp only [squareReadout, map_add, map_sub, LinearMap.add_apply,
    LinearMap.sub_apply]
  rw [hc ν b, hc ω c]
  linarith only [hp]

/-- Exact-cone extension of the original support obstruction excludes every
closed semidefinite norm ball. The nonzero support telescope remains explicit;
no existence of such a state or output is inferred. -/
theorem positive_support_unit_boundary
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (P : Set (E →ₗ[ℝ] ℝ)) (hP : P2 S D P) (hPB : PB S D P)
    (hc : ∀ x y, S x y = S y x) (u : E) (hu : ∀ x, S u x = x)
    (hsq : ∀ x, ‖S x x‖ = ‖x‖ ^ 2)
    (hsep : ∀ x, (∀ α ∈ P, α x = 0) → x = 0)
    (C : Set E) (hexact : ∀ x, x ∈ C ↔ ∀ α ∈ P, 0 ≤ α x)
    (μ : ℝ) (b : E) (β : E →ₗ[ℝ] ℝ)
    (hβ : ∀ x ∈ C, 0 ≤ β x) (hβu : β u = 1)
    (hβnorm : ∀ x, |β x| ≤ ‖x‖)
    (Z : ℝ) (hZ : Z ≠ 0) (hread : β (D (μ • u) b) = Z)
    (hnorm : |Z| = ‖D (μ • u) b‖) :
    μ ≠ 0 ∧ ∀ t : ℝ, |t| < ‖b - t • u‖ := by
  let Q : Set (E →ₗ[ℝ] ℝ) := {γ | ∀ x ∈ C, 0 ≤ γ x}
  have hQ : P2 S D Q := positive_p2 S D P hP hc hsep C hexact
  have hBQ : PB S D Q := fun γ _ => pb_any_reading S D P hPB hc hsep γ (Set.mem_univ _)
  have hPQ : P ⊆ Q := by
    intro α hα x hx
    exact (hexact x).mp hx α hα
  have hsepQ : ∀ x, (∀ α ∈ Q, α x = 0) → x = 0 := by
    intro x hx
    exact hsep x (fun α hα => hx α (hPQ hα))
  have hβQ : β ∈ Q := hβ
  have hb := (support_unit_obstruction S D Q hQ hBQ hc u hu hsq hsepQ
    μ b β hβQ hβu hβnorm Z hZ hread hnorm).2
  have hd := determinant_bound S D Q hQ hc β hβQ (μ • u) b
  rw [hread] at hd
  simp [map_smul, hu, hβu, hb, smul_eq_mul] at hd
  constructor
  · intro hμ
    rw [hμ] at hd
    exact hZ (by nlinarith [sq_nonneg Z])
  · intro t
    by_contra hnot
    have hn : ‖b - t • u‖ ≤ |t| := le_of_not_gt hnot
    have hbnd : β (S (b - t • u) (b - t • u)) ≤ t ^ 2 := by
      calc
        β (S (b - t • u) (b - t • u)) ≤ |β (S (b - t • u) (b - t • u))| := le_abs_self _
        _ ≤ ‖S (b - t • u) (b - t • u)‖ := hβnorm _
        _ = ‖b - t • u‖ ^ 2 := hsq _
        _ ≤ |t| ^ 2 := by nlinarith [norm_nonneg (b - t • u), abs_nonneg t]
        _ = t ^ 2 := sq_abs t
    have hbu : S b u = b := (hc b u).trans (hu b)
    simp [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hu, hbu, hb, hβu] at hbnd
    have hbs : β (S b b) ≤ 0 := by nlinarith only [hbnd]
    have hprod := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg μ) hbs
    exact hZ (by nlinarith [sq_nonneg Z])

/-- On the same arbitrary original carrier, every second label in a closed
semidefinite norm ball has zero unit row. The support reading is constructed
from the original order-unit cone, rather than supplied as an extra premise. -/
theorem unit_row_closed_ball
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (P : Set (E →ₗ[ℝ] ℝ)) (hP : P2 S D P) (hPB : PB S D P)
    (A : D5.S3.Topology.OrderUnitNorm.Data E)
    (hc : ∀ x y, S x y = S y x) (hu : ∀ x, S A.unit x = x)
    (hsq : ∀ x, ‖S x x‖ = ‖x‖ ^ 2)
    (hsep : ∀ x, (∀ α ∈ P, α x = 0) → x = 0)
    (hexact : ∀ x, x ∈ A.cone ↔ ∀ α ∈ P, 0 ≤ α x)
    (horder : ∀ x, A.orderNorm x = ‖x‖)
    (μ : ℝ) (b : E) (t : ℝ) (hball : ‖b - t • A.unit‖ ≤ |t|) :
    D (μ • A.unit) b = 0 := by
  by_contra hh
  obtain ⟨β, hβ, hβu, hβnorm, hn⟩ := A.positive_norm_support (D (μ • A.unit) b) hh
  rw [horder] at hn
  have hZ : β (D (μ • A.unit) b) ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hn
    exact hh (norm_eq_zero.mp hn.symm)
  have hb := positive_support_unit_boundary S D P hP hPB hc A.unit hu hsq hsep
    (A.cone : Set E) hexact μ b β hβ hβu
    (fun x => by simpa only [horder] using hβnorm x)
    (β (D (μ • A.unit) b)) hZ rfl hn
  exact (not_lt_of_ge hball) (hb.2 t)

/-- All positive and negative original second inputs have zero unit rows.
The original exact cone and order norm supply every support reading used. -/
theorem unit_row_semidefinite
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (P : Set (E →ₗ[ℝ] ℝ)) (hP : P2 S D P) (hPB : PB S D P)
    (A : D5.S3.Topology.OrderUnitNorm.Data E)
    (hc : ∀ x y, S x y = S y x) (hu : ∀ x, S A.unit x = x)
    (hsq : ∀ x, ‖S x x‖ = ‖x‖ ^ 2)
    (hsep : ∀ x, (∀ α ∈ P, α x = 0) → x = 0)
    (hexact : ∀ x, x ∈ A.cone ↔ ∀ α ∈ P, 0 ≤ α x)
    (horder : ∀ x, A.orderNorm x = ‖x‖)
    (μ : ℝ) (b : E) (hb : b ∈ A.cone ∨ -b ∈ A.cone) :
    D (μ • A.unit) b = 0 := by
  have ball (c : E) (hc : c ∈ A.cone) :
      ‖c - (‖c‖ / 2) • A.unit‖ ≤ ‖c‖ / 2 := by
    by_cases hw : c - (‖c‖ / 2) • A.unit = 0
    · simp only [hw, norm_zero]
      positivity
    obtain ⟨β, hβ, hβu, hβnorm, hn⟩ :=
      A.positive_norm_support (c - (‖c‖ / 2) • A.unit) hw
    have hbc : 0 ≤ β c := hβ c hc
    have hbound : β c ≤ ‖c‖ :=
      (le_abs_self _).trans (by simpa only [horder] using hβnorm c)
    rw [horder, map_sub, map_smul, hβu, smul_eq_mul, mul_one] at hn
    rw [← hn]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rcases hb with hp | hm
  · exact unit_row_closed_ball S D P hP hPB A hc hu hsq hsep hexact horder μ b
      (‖b‖ / 2) (by simpa only [abs_of_nonneg (by positivity : 0 ≤ ‖b‖ / 2)] using ball b hp)
  · apply unit_row_closed_ball S D P hP hPB A hc hu hsq hsep hexact horder μ b
      (-(‖b‖ / 2))
    have hn := ball (-b) hm
    have he : -b - (‖-b‖ / 2) • A.unit = -(b - (-(‖b‖ / 2)) • A.unit) := by
      rw [norm_neg]
      module
    rw [he, norm_neg] at hn
    simpa only [norm_neg, abs_neg, abs_of_nonneg (by positivity : 0 ≤ ‖b‖ / 2)] using hn

end D5.S3.Quantum.SpinFactor.OriginalUnitSupport
