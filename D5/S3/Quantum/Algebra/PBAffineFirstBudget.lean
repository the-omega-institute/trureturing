/- GID: D5/S3/Quantum/Algebra/PBAffineFirstBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBAffineFirstBudget
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.Real.Sqrt]
   utility: none
   digest: Original PB and same-readout P2 force the affine transverse budget. -/

import D5.S3.Quantum.Algebra.PBActualOuterBudget
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Same-original-label affine PB budgets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/28369 -/

namespace D5.S3.Quantum.Algebra.PBAffineFirstBudget

open Filter Topology
open PBActualOuterBudget

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The same real-linear functional reads every original label in this determinant. -/
def gram (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (φ : E →ₗ[ℝ] ℝ) (a b : E) : ℝ :=
  φ (J a a) * φ (J b b) - φ (J a b) ^ 2

/-- Leading coefficients of two square-root budgets, including a zero coefficient.
Only explicit scalar expressions vary; no response is evaluated at a limiting label. -/
theorem leading_budget (c d p₀ p₁ p₂ q₀ q₁ q₂ : ℝ)
    (h : ∀ a : ℝ, |c - a * d| ≤
      Real.sqrt (p₀ + 2*a*p₁ + a^2*p₂) +
      Real.sqrt (q₀ + 2*a*q₁ + a^2*q₂)) :
    |d| ≤ Real.sqrt p₂ + Real.sqrt q₂ := by
  have hl : Tendsto (fun δ : ℝ => |δ*c-d|) (𝓝[>] 0) (𝓝 |d|) := by
    have hc : Continuous (fun δ : ℝ => |δ*c-d|) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun δ : ℝ =>
      Real.sqrt (δ^2*p₀+2*δ*p₁+p₂) + Real.sqrt (δ^2*q₀+2*δ*q₁+q₂))
      (𝓝[>] 0) (𝓝 (Real.sqrt p₂ + Real.sqrt q₂)) := by
    have hc : Continuous (fun δ : ℝ =>
      Real.sqrt (δ^2*p₀+2*δ*p₁+p₂) + Real.sqrt (δ^2*q₀+2*δ*q₁+q₂)) := by
      fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hd : 0 < δ := hδ
  have scale (a b e : ℝ) :
      δ * Real.sqrt (a + 2*δ⁻¹*b + (δ⁻¹)^2*e) =
        Real.sqrt (δ^2*a + 2*δ*b + e) := by
    calc
      _ = Real.sqrt (δ^2) * Real.sqrt (a+2*δ⁻¹*b+(δ⁻¹)^2*e) := by
        rw [Real.sqrt_sq hd.le]
      _ = Real.sqrt (δ^2*(a+2*δ⁻¹*b+(δ⁻¹)^2*e)) :=
        (Real.sqrt_mul (sq_nonneg δ) _).symm
      _ = _ := by congr 1; field_simp [ne_of_gt hd]
  calc
    |δ*c-d| = δ * |c-δ⁻¹*d| := by
      calc
        _ = |δ*(c-δ⁻¹*d)| := by congr 1; field_simp [ne_of_gt hd]
        _ = _ := by rw [abs_mul, abs_of_pos hd]
    _ ≤ δ * (Real.sqrt (p₀+2*δ⁻¹*p₁+(δ⁻¹)^2*p₂) +
        Real.sqrt (q₀+2*δ⁻¹*q₁+(δ⁻¹)^2*q₂)) :=
      mul_le_mul_of_nonneg_left (h δ⁻¹) hd.le
    _ = _ := by rw [mul_add, scale, scale]

theorem gram_shift (J : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hs : ∀ a b, J a b = J b a) (φ : E →ₗ[ℝ] ℝ)
    (A B n : E) (θ α : ℝ) :
    gram J φ (A + α • n) (B + (θ*α) • n) =
      gram J φ A B + 2*α*(θ*φ (J A A)*φ (J n B) +
        φ (J n A)*φ (J B B) - φ (J A B)*(φ (J n B)+θ*φ (J n A))) +
      α^2*gram J φ n (B-θ • A) := by
  simp only [gram, map_add, map_sub, map_smul, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hs A n, hs B n, hs B A]
  ring

/-- Source 162.2 on the original total response. The only D-specific supplier is
the actual anchor 161.4 for the very same affine first label. The finite Jordan
expression x-J(h,J(h,x)) is exactly the original transverse projection. -/
theorem actual_affine_first_budget
    (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (u h p q : E) (D : E → E → E)
    (hs : ∀ a b, J a b = J b a) (hu : ∀ a, J u a = a)
    (hh : J h h = u) (hp : J h p = 0) (hq : J h q = 0)
    (hpq : J p q = 0) (hPB : PB J D)
    (φ : E →ₗ[ℝ] ℝ)
    (hP2 : ∀ a b, φ (D a b) ^ 2 ≤ gram J φ a b)
    (s r : ℝ)
    (anchor : ∀ t α : ℝ,
      D (s • u + r • h) (t • p + α • (u+h)) = (r*t) • q)
    (x : E) (t : ℝ) :
    let g := D (s • u+r • h) x
    let k := J h x
    let v := x-J h k
    let θ := s+r
    let Z := (1+s*θ) • x+(r*θ) • k
    2 * |r| * |φ (t • q+v)| ≤
      Real.sqrt (gram J φ (u+h) (Z+g-(r*t) • p-(r*θ*t) • q)) +
      Real.sqrt (gram J φ (u+h) (Z-g+(r*t) • p-(r*θ*t) • q)) := by
  let a := s • u+r • h
  let n := u+h
  let g := D a x
  let k := J h x
  let v := x-J h k
  let θ := s+r
  let A := t • (p+r • q)-s • x-r • k
  let B := x+g+(s*t) • p
  let C := t • (p-r • q)+s • x+r • k
  let F := x-g-(s*t) • p
  have hj (y : E) : J a y = s • y + r • J h y := by
    simp [a, hu]
  have hnh : J h n = n := by simp [n, hh, hs h u, hu, add_comm]
  have hnq : J n q = q := by simp [n, hu, hq]
  have hnx : J n x = x+k := by simp [n, hu, k]
  have hnk : J n k = k+J h k := by simp [n, hu]
  have finite (α : ℝ) :
      |φ ((2*r*t) • J p k-2 • J x g)-α*(2*r*φ (t • q+v))| ≤
        Real.sqrt (gram J φ (A+α • n) (B+(θ*α) • n)) +
        Real.sqrt (gram J φ (C+α • n) (F+(-θ*α) • n)) := by
    let b := t • p+α • n
    let ν := (r*t) • q-s • x-r • k
    let ω := (s*t) • p+(θ*α) • n+g
    have hab : D a b = (r*t) • q := anchor t α
    have han : J a n = θ • n := by rw [hj, hnh]; dsimp [θ]; module
    have hax : J a x = s • x+r • k := hj x
    have hap : J a p = s • p := by rw [hj, hp, smul_zero, add_zero]
    have habj : J a b = (s*t) • p+(θ*α) • n := by
      simp only [b, map_add, map_smul, hap, han]
      module
    have hpb := hPB a b x
    change D (b+(D a b-J a x)) (x+(J a b+D a x)) -
      D (b-(D a b-J a x)) (x-(J a b+D a x)) = _ at hpb
    rw [hab, hax, habj] at hpb
    have hν : (r*t) • q-(s • x+r • k) = ν := by dsimp [ν]; module
    have hω : (s*t) • p+(θ*α) • n+D a x = ω := rfl
    rw [hν, hω] at hpb
    have rp : b+ν = A+α • n := by dsimp [b, ν, A]; module
    have rm : b-ν = C+α • n := by dsimp [b, ν, C]; module
    have sp : x+ω = B+(θ*α) • n := by dsimp [ω, B, g]; module
    have sm : x-ω = F+(-θ*α) • n := by dsimp [ω, F, g]; module
    have rhs : (-2 : ℝ) • (J b ν+J x ω) =
        (2*r*t) • J p k-2 • J x g-(2*α*r) • (t • q+v) := by
      simp only [b, ν, ω, map_add, map_sub, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply,
        hpq, hnq, hnx, hnk, hs x p, hs x n]
      dsimp [v, θ]
      module
    have bound (y z : E) : |φ (D y z)| ≤ Real.sqrt (gram J φ y z) := by
      exact Real.abs_le_sqrt (hP2 y z)
    have heq : φ (D (b+ν) (x+ω))-φ (D (b-ν) (x-ω)) =
        φ ((2*r*t) • J p k-2 • J x g)-α*(2*r*φ (t • q+v)) := by
      rw [← map_sub, hpb, rhs]
      simp only [map_sub, map_smul, smul_eq_mul]
      ring
    rw [← heq]
    calc
      _ ≤ |φ (D (b+ν) (x+ω))|+|φ (D (b-ν) (x-ω))| := abs_sub _ _
      _ ≤ _ := by
        simpa only [rp, rm, sp, sm] using
          add_le_add (bound (b+ν) (x+ω)) (bound (b-ν) (x-ω))
  have lead := leading_budget (φ ((2*r*t) • J p k-2 • J x g))
    (2*r*φ (t • q+v))
    (gram J φ A B)
    (θ*φ (J A A)*φ (J n B)+φ (J n A)*φ (J B B)-φ (J A B)*(φ (J n B)+θ*φ (J n A)))
    (gram J φ n (B-θ • A))
    (gram J φ C F)
    ((-θ)*φ (J C C)*φ (J n F)+φ (J n C)*φ (J F F)-φ (J C F)*(φ (J n F)+(-θ)*φ (J n C)))
    (gram J φ n (F-(-θ) • C))
    (by intro α; simpa only [gram_shift J hs] using finite α)
  have wp : B-θ • A = (1+s*θ) • x+(r*θ) • k+g-(r*t) • p-(r*θ*t) • q := by
    dsimp [A, B, θ]
    module
  have wm : F-(-θ) • C = (1+s*θ) • x+(r*θ) • k-g+(r*t) • p-(r*θ*t) • q := by
    dsimp [C, F, θ]
    module
  rw [wp, wm] at lead
  simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    a, n, g, k, v, θ, mul_assoc] using lead

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local notation "⟪" x ", " y "⟫" => inner ℝ x y

def realPerp (η : H) : H →ₗ[ℝ] H where
  toFun z := z-⟪η,z⟫ • η
  map_add' z w := by simp only [inner_add_right, add_smul]; abel
  map_smul' a z := by
    change a • z-⟪η,a • z⟫ • η = a • (z-⟪η,z⟫ • η)
    simp only [inner_smul_right, smul_sub, smul_smul]

private theorem norm_first_derivative (w z : H) (hw : ‖w‖ = 1) :
    HasDerivAt (fun δ : ℝ => ‖δ • z+w‖) ⟪w,z⟫ 0 := by
  have hv : HasDerivAt (fun δ : ℝ => δ • z+w) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const z).add_const w
  have hn := hv.norm_sq.sqrt (by simp [hw])
  simpa [hw, Real.sqrt_sq (norm_nonneg _)] using hn

/-- Both ends of the original real parameter become a differentiable minimum
after reciprocal rescaling. This uses no derivative of a response. -/
theorem two_ended_budget (r A : ℝ) (hr : r ≠ 0) (w zp zm : H)
    (hw : ‖w‖ = 1)
    (h : ∀ t : ℝ, 2 * |r| * |t+A| ≤ ‖zp-(r*t) • w‖+‖zm+(r*t) • w‖) :
    2*r*A = ⟪w,zm⟫-⟪w,zp⟫ := by
  have scaled (δ : ℝ) :
      2 * |1+δ*(r*A)| ≤ ‖δ • zp-w‖+‖δ • zm+w‖ := by
    by_cases hd : δ = 0
    · norm_num [hd, hw]
    have hc : δ*(r*(δ*r)⁻¹) = 1 := by field_simp
    have hl : |δ| * (2 * |r| * |(δ*r)⁻¹+A|) = 2 * |1+δ*(r*A)| := by
      calc
        _ = 2 * |δ*r*((δ*r)⁻¹+A)| := by rw [abs_mul, abs_mul]; ring
        _ = _ := by rw [mul_add, mul_inv_cancel₀ (mul_ne_zero hd hr)]; ring
    have hp : |δ| * ‖zp-(r*(δ*r)⁻¹) • w‖ = ‖δ • zp-w‖ := by
      rw [← Real.norm_eq_abs δ, ← norm_smul, smul_sub, smul_smul, hc, one_smul]
    have hm : |δ| * ‖zm+(r*(δ*r)⁻¹) • w‖ = ‖δ • zm+w‖ := by
      rw [← Real.norm_eq_abs δ, ← norm_smul, smul_add, smul_smul, hc, one_smul]
    have hb := mul_le_mul_of_nonneg_left (h ((δ*r)⁻¹)) (abs_nonneg δ)
    rwa [hl, mul_add, hp, hm] at hb
  let F := fun δ : ℝ => ‖δ • zp-w‖+‖δ • zm+w‖-2 * |1+δ*(r*A)|
  have hmin : IsLocalMin F 0 := by
    apply Filter.Eventually.of_forall
    intro δ
    change F 0 ≤ F δ
    have hzero : F 0 = 0 := by norm_num [F, hw]
    rw [hzero]
    exact sub_nonneg.mpr (scaled δ)
  have hp := norm_first_derivative (-w) zp (by simpa using hw)
  have hm := norm_first_derivative w zm hw
  have ha : HasDerivAt (fun δ : ℝ => |1+δ*(r*A)|) (r*A) 0 := by
    have hv : HasDerivAt (fun δ : ℝ => 1+δ*(r*A)) (r*A) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (r*A)).const_add 1
    have ho : HasDerivAt (fun z : ℝ => |z|) 1 (1+0*(r*A)) := by
      simpa using hasDerivAt_abs_pos (show (0 : ℝ) < 1 by norm_num)
    convert ho.comp 0 hv using 1 <;> first | rfl | simp
  have hf : HasDerivAt F (-⟪w,zp⟫+⟪w,zm⟫-2*(r*A)) 0 := by
    convert (hp.add hm).sub (ha.const_mul 2) using 1
    all_goals try rfl
    all_goals try simp only [inner_neg_left]
    all_goals ext δ
    all_goals simp [F, sub_eq_add_neg]
  have he := hmin.hasDerivAt_eq_zero hf
  linarith

/-- Source 163.4 obtained from the actual original PB/P2 budget. The vector
readout is unnormalised, so the common positive factor cancels without changing
the original domain or imposing a mass on its evaluations. -/
theorem actual_affine_vector_budget
    (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (u h p q : E) (D : E → E → E)
    (hs : ∀ a b, J a b = J b a) (hu : ∀ a, J u a = a)
    (hh : J h h = u) (hp : J h p = 0) (hq : J h q = 0)
    (hpq : J p q = 0) (hPB : PB J D)
    (R : Readout (H := H) J u D ⊤) (s r : ℝ)
    (anchor : ∀ t α : ℝ,
      D (s • u+r • h) (t • p+α • (u+h)) = (r*t) • q)
    (ξ η : H) (hη : ‖η‖ = 1)
    (hhξ : R.op h ξ = -ξ) (hhη : R.op h η = η)
    (hqξ : R.op q ξ = η) (hηp : ⟪η,R.op p ξ⟫ = 0)
    (x : E) (t : ℝ) :
    let g := D (s • u+r • h) x
    let k := J h x
    let v := x-J h k
    let θ := s+r
    let Z := (1+s*θ) • x+(r*θ) • k
    let P := fun z : H => z-⟪η,z⟫ • η
    2 * |r| * |t+⟪η,R.op v ξ⟫| ≤
      ‖P (R.op (Z+g) ξ)-(r*t) • R.op p ξ‖ +
      ‖P (R.op (Z-g) ξ)+(r*t) • R.op p ξ‖ := by
  let g := D (s • u+r • h) x
  let k := J h x
  let v := x-J h k
  let θ := s+r
  let Z := (1+s*θ) • x+(r*θ) • k
  let n := u+h
  let P := realPerp η
  have hηη : ⟪η,η⟫ = 1 := by simp [hη]
  have readj (a b : E) (z : H) :
      reading R z (J a b) = ⟪R.op a z,R.op b z⟫ :=
    reading_jordan R (Submodule.mem_top) (Submodule.mem_top) z
  have diag (z : H) (ε : ℝ) (hz : R.op h z = ε • z) (he : ε^2 = 1) :
      reading R z v = 0 ∧ reading R z q = 0 := by
    have hk : reading R z k = ε*reading R z x := by
      dsimp [k]
      rw [readj, hz, inner_smul_left]
      rfl
    have hv : reading R z v = 0 := by
      simp only [v, map_sub, readj, hz, inner_smul_left]
      change reading R z x-ε*reading R z k = 0
      rw [hk]
      linear_combination -(reading R z x)*he
    have hqz := readj h q z
    rw [hq, map_zero, hz, inner_smul_left] at hqz
    change 0 = ε*reading R z q at hqz
    constructor
    · exact hv
    · have hε : ε ≠ 0 := by intro hz; simp [hz] at he
      exact (mul_eq_zero.mp hqz.symm).resolve_left hε
  have dξ := diag ξ (-1) (by simpa using hhξ) (by norm_num)
  have dη := diag η 1 (by simpa using hhη) (by norm_num)
  have hnξ : R.op n ξ = 0 := by simp [n, R.unit, hhξ]
  have hnη : R.op n η = (2 : ℝ) • η := by simp [n, R.unit, hhη, two_smul]
  have exactGram (W : E) (δ : ℝ) :
      gram J (reading R (ξ+δ • η)) n W =
        4*δ^2*‖P (R.op W ξ+δ • R.op W η)‖^2 := by
    rw [gram, readj, readj, readj]
    have hn : R.op n (ξ+δ • η) = (2*δ) • η := by
      simp [hnξ, hnη, smul_smul, mul_comm]
    rw [hn]
    have hW : R.op W (ξ+δ • η) = R.op W ξ+δ • R.op W η := by simp
    rw [hW]
    simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      hηη, mul_one]
    rw [real_inner_self_eq_norm_sq]
    have perp (z : H) : ‖P z‖^2 = ‖z‖^2-⟪η,z⟫^2 := by
      change ‖z-⟪η,z⟫ • η‖^2 = _
      rw [norm_sub_sq_real, inner_smul_right, real_inner_comm z η, norm_smul]
      simp only [hη, mul_one, Real.norm_eq_abs, sq_abs]
      ring
    rw [perp]
    ring
  have exactRead (δ : ℝ) :
      reading R (ξ+δ • η) (t • q+v) = 2*δ*(t+⟪η,R.op v ξ⟫) := by
    have sy (a : E) : ⟪ξ,R.op a η⟫ = ⟪η,R.op a ξ⟫ := by
      rw [← R.symmetric a ξ η, real_inner_comm]
    simp only [reading, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right]
    change _ = _
    have dxv : ⟪ξ,R.op v ξ⟫ = 0 := dξ.1
    have dxq : ⟪ξ,R.op q ξ⟫ = 0 := dξ.2
    have dev : ⟪η,R.op v η⟫ = 0 := dη.1
    have deq : ⟪η,R.op q η⟫ = 0 := dη.2
    rw [dxv, dxq, dev, deq, sy q, sy v, hqξ, hηη]
    simp only [RCLike.conj_to_real]
    ring
  have finite (δ : ℝ) (hδ : 0 < δ) :
      2 * |r| * |t+⟪η,R.op v ξ⟫| ≤
        ‖P (R.op (Z+g-(r*t) • p-(r*θ*t) • q) ξ+
          δ • R.op (Z+g-(r*t) • p-(r*θ*t) • q) η)‖ +
        ‖P (R.op (Z-g+(r*t) • p-(r*θ*t) • q) ξ+
          δ • R.op (Z-g+(r*t) • p-(r*θ*t) • q) η)‖ := by
    have hb := actual_affine_first_budget J u h p q D hs hu hh hp hq hpq hPB
      (reading R (ξ+δ • η)) (fun a b => R.p2 (ξ+δ • η) a b) s r anchor x t
    change 2 * |r| * |reading R (ξ+δ • η) (t • q+v)| ≤ _ at hb
    rw [exactRead, exactGram, exactGram] at hb
    have sqr (z : H) : Real.sqrt (4*δ^2*‖z‖^2) = 2*δ*‖z‖ := by
      rw [show 4*δ^2*‖z‖^2 = (2*δ*‖z‖)^2 by ring,
        Real.sqrt_sq (by positivity)]
    rw [sqr, sqr, abs_mul, abs_mul, abs_of_pos hδ] at hb
    simp only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hb
    apply le_of_mul_le_mul_left (a := 2*δ) (a0 := by positivity)
    convert hb using 1 <;> ring
  have hl : Tendsto (fun _ : ℝ => 2 * |r| * |t+⟪η,R.op v ξ⟫|)
      (𝓝[>] 0) (𝓝 (2 * |r| * |t+⟪η,R.op v ξ⟫|)) := tendsto_const_nhds
  have hr : Tendsto (fun δ : ℝ =>
      ‖P (R.op (Z+g-(r*t) • p-(r*θ*t) • q) ξ+
        δ • R.op (Z+g-(r*t) • p-(r*θ*t) • q) η)‖ +
      ‖P (R.op (Z-g+(r*t) • p-(r*θ*t) • q) ξ+
        δ • R.op (Z-g+(r*t) • p-(r*θ*t) • q) η)‖)
      (𝓝[>] 0) (𝓝 (‖P (R.op (Z+g) ξ)-(r*t) • R.op p ξ‖ +
        ‖P (R.op (Z-g) ξ)+(r*t) • R.op p ξ‖)) := by
    have hc : Continuous (fun δ : ℝ =>
      ‖P (R.op (Z+g-(r*t) • p-(r*θ*t) • q) ξ+
        δ • R.op (Z+g-(r*t) • p-(r*θ*t) • q) η)‖ +
      ‖P (R.op (Z-g+(r*t) • p-(r*θ*t) • q) ξ+
        δ • R.op (Z-g+(r*t) • p-(r*θ*t) • q) η)‖) := by
      dsimp [P, realPerp]
      fun_prop
    have pp : P (R.op p ξ) = R.op p ξ := by simp [P, realPerp, hηp]
    have pq : P (R.op q ξ) = 0 := by simp [P, realPerp, hqξ, hη]
    simpa only [zero_smul, add_zero, map_sub, map_add, map_smul,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      pp, pq, smul_zero, sub_zero] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto hl hr (by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact finite δ hδ)

/-- Source 163.6 for each actual anchor, retaining either sign of the original r.
The fixed old value g is read throughout; no linearity of D is used. -/
theorem actual_affine_anchor_identity
    (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (u h p q : E) (D : E → E → E)
    (hs : ∀ a b, J a b = J b a) (hu : ∀ a, J u a = a)
    (hh : J h h = u) (hp : J h p = 0) (hq : J h q = 0)
    (hpq : J p q = 0) (hPB : PB J D)
    (R : Readout (H := H) J u D ⊤) (s r : ℝ) (hr : r ≠ 0)
    (anchor : ∀ t α : ℝ,
      D (s • u+r • h) (t • p+α • (u+h)) = (r*t) • q)
    (ξ η : H) (hη : ‖η‖ = 1)
    (hhξ : R.op h ξ = -ξ) (hhη : R.op h η = η)
    (hqξ : R.op q ξ = η) (hηp : ⟪η,R.op p ξ⟫ = 0)
    (hpξ : ‖R.op p ξ‖ = 1) (x : E) :
    r*⟪η,R.op (x-J h (J h x)) ξ⟫ =
      -⟪R.op p ξ,R.op (D (s • u+r • h) x) ξ⟫ := by
  let g := D (s • u+r • h) x
  let v := x-J h (J h x)
  let θ := s+r
  let Z := (1+s*θ) • x+(r*θ) • J h x
  let P := realPerp η
  have hb := two_ended_budget r ⟪η,R.op v ξ⟫ hr (R.op p ξ)
    (P (R.op (Z+g) ξ)) (P (R.op (Z-g) ξ)) hpξ (fun t =>
      actual_affine_vector_budget J u h p q D hs hu hh hp hq hpq hPB R s r
        anchor ξ η hη hhξ hhη hqξ hηp x t)
  have hpe : ⟪R.op p ξ,η⟫ = 0 := by rw [real_inner_comm, hηp]
  have hd : ⟪R.op p ξ,P (R.op (Z-g) ξ)⟫-
      ⟪R.op p ξ,P (R.op (Z+g) ξ)⟫ = -2*⟪R.op p ξ,R.op g ξ⟫ := by
    simp only [P, realPerp, LinearMap.coe_mk, AddHom.coe_mk, inner_sub_right,
      inner_smul_right, hpe, mul_zero, sub_zero, map_sub, map_add,
      LinearMap.sub_apply, LinearMap.add_apply, inner_add_right]
    ring
  rw [hd] at hb
  change r*⟪η,R.op v ξ⟫ = -⟪R.op p ξ,R.op g ξ⟫
  linarith

#print axioms actual_affine_first_budget
#print axioms actual_affine_vector_budget
#print axioms actual_affine_anchor_identity

end D5.S3.Quantum.Algebra.PBAffineFirstBudget
