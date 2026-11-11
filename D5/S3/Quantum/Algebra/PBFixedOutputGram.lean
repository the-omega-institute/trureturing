/- GID: D5/S3/Quantum/Algebra/PBFixedOutputGram
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBFixedOutputGram
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Symmetric]
   utility: none
   digest: Scalar fixed-output PB yields transverse identities through full vector Gram budgets. -/

import D5.S3.Quantum.Algebra.PBAffineFirstBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Algebra.PBFixedOutputGram

open Filter Topology PBAffineFirstBudget

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The scalar budget for one original probe and one common reading. -/
def scalarPB (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (κ ρ : E →ₗ[ℝ] E)
    (t k g x : E) (φ : E →ₗ[ℝ] ℝ) : Prop :=
  |φ ((-2 : ℝ) • (J x (κ x-k)+J t (ρ x+g)))| ≤
    Real.sqrt (gram J φ (x+(κ x-k)) (t+(ρ x+g))) +
    Real.sqrt (gram J φ (x-(κ x-k)) (t-(ρ x+g)))

/-- Primitive spectral-pair relations for the known Jordan and commutator rows. -/
structure SpectralPair (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (κ ρ : E →ₗ[ℝ] E) where
  e : E
  j : E
  n : E
  μ : ℝ
  λ : ℝ
  kappa_e : κ e = λ • j
  kappa_n : κ n = 0
  rho_e : ρ e = μ • e
  rho_n : ρ n = (μ+λ) • n
  jordan_ej : J e j = 0
  jordan_nj : J n j = j

/-- A Jordan representation, with no response or separate P2 field. -/
structure VectorModel (J : E →ₗ[ℝ] E →ₗ[ℝ] E) where
  op : E →ₗ[ℝ] (H →ₗ[ℝ] H)
  symmetric : ∀ a, (op a).IsSymmetric
  jordan : ∀ a b, op (J a b) =
    (1/2 : ℝ) • ((op a).comp (op b)+(op b).comp (op a))

/-- The reading acts on the entire represented space. -/
def vectorReading {J : E →ₗ[ℝ] E →ₗ[ℝ] E}
    (R : VectorModel (H := H) J) (v : H) : E →ₗ[ℝ] ℝ where
  toFun a := ⟪v,R.op a v⟫
  map_add' a b := by simp [inner_add_right]
  map_smul' a b := by simp [inner_smul_right]

private theorem reading_jordan {J : E →ₗ[ℝ] E →ₗ[ℝ] E}
    (R : VectorModel (H := H) J) (a b : E) (v : H) :
    vectorReading R v (J a b) = ⟪R.op a v,R.op b v⟫ := by
  simp only [vectorReading, LinearMap.coe_mk, AddHom.coe_mk, R.jordan,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    inner_smul_right, inner_add_right]
  rw [← R.symmetric a v (R.op b v), ← R.symmetric b v (R.op a v), real_inner_comm]
  ring

private theorem first_budget (J : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hs : ∀ a b, J a b = J b a) (κ ρ : E →ₗ[ℝ] E)
    (F : SpectralPair J κ ρ) (t k g : E) (φ : E →ₗ[ℝ] ℝ)
    (hPB : ∀ T α : ℝ, scalarPB J κ ρ t k g (T • F.e+α • F.n) φ)
    (T : ℝ) :
    let a := F.μ+F.λ
    let V := a • J F.n t-J F.n k
    let Z := t+a • k
    2 * |φ ((F.λ*T) • F.j+V)| ≤
      Real.sqrt (gram J φ F.n (Z+g-(F.λ*T) • F.e-(a*F.λ*T) • F.j)) +
      Real.sqrt (gram J φ F.n (Z-g+(F.λ*T) • F.e-(a*F.λ*T) • F.j)) := by
  let a := F.μ+F.λ
  let V := a • J F.n t-J F.n k
  let Z := t+a • k
  let A := T • (F.e+F.λ • F.j)-k
  let B := t+g+(F.μ*T) • F.e
  let C := T • (F.e-F.λ • F.j)+k
  let D := t-g-(F.μ*T) • F.e
  let L := (2*T) • J F.e k-(2*F.μ*T) • J t F.e-2 • J t g
  have finite (α : ℝ) :
      |φ L-α*(2*φ ((F.λ*T) • F.j+V))| ≤
        Real.sqrt (gram J φ (A+α • F.n) (B+(a*α) • F.n)) +
        Real.sqrt (gram J φ (C+α • F.n) (D+(-a*α) • F.n)) := by
    have hb := hPB T α
    have hk : κ (T • F.e+α • F.n) = (F.λ*T) • F.j := by
      simp [F.kappa_e, F.kappa_n, smul_smul, mul_comm]
    have hr : ρ (T • F.e+α • F.n) = (F.μ*T) • F.e+(a*α) • F.n := by
      simp [F.rho_e, F.rho_n, a, smul_smul, mul_comm]
    have hp : T • F.e+α • F.n+(κ (T • F.e+α • F.n)-k) = A+α • F.n := by
      rw [hk]; dsimp [A]; module
    have hm : T • F.e+α • F.n-(κ (T • F.e+α • F.n)-k) = C+α • F.n := by
      rw [hk]; dsimp [C]; module
    have sp : t+(ρ (T • F.e+α • F.n)+g) = B+(a*α) • F.n := by
      rw [hr]; dsimp [B]; module
    have sm : t-(ρ (T • F.e+α • F.n)+g) = D+(-a*α) • F.n := by
      rw [hr]; dsimp [D]; module
    have hl : (-2 : ℝ) • (J (T • F.e+α • F.n)
        (κ (T • F.e+α • F.n)-k)+J t (ρ (T • F.e+α • F.n)+g)) =
        L-(2*α) • ((F.λ*T) • F.j+V) := by
      rw [hk, hr]
      simp only [map_add, map_sub, map_smul, LinearMap.add_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, F.jordan_ej, F.jordan_nj,
        smul_zero, zero_sub, hs t F.n]
      dsimp [L, V]
      module
    unfold scalarPB at hb
    rw [hp, hm, sp, sm, hl] at hb
    simpa only [map_sub, map_smul, smul_eq_mul, mul_assoc] using hb
  have lead := leading_budget (φ L) (2*φ ((F.λ*T) • F.j+V))
    (gram J φ A B)
    (a*φ (J A A)*φ (J F.n B)+φ (J F.n A)*φ (J B B)-
      φ (J A B)*(φ (J F.n B)+a*φ (J F.n A)))
    (gram J φ F.n (B-a • A))
    (gram J φ C D)
    ((-a)*φ (J C C)*φ (J F.n D)+φ (J F.n C)*φ (J D D)-
      φ (J C D)*(φ (J F.n D)+(-a)*φ (J F.n C)))
    (gram J φ F.n (D-(-a) • C))
    (by intro α; simpa only [gram_shift J hs] using finite α)
  have wp : B-a • A = Z+g-(F.λ*T) • F.e-(a*F.λ*T) • F.j := by
    dsimp [A, B, Z, a]; module
  have wm : D-(-a) • C = Z-g+(F.λ*T) • F.e-(a*F.λ*T) • F.j := by
    dsimp [C, D, Z, a]; module
  rw [wp, wm] at lead
  simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using lead

/-- The mixed-vector limit of the scalar PB, with every complementary component retained. -/
private theorem vector_budget (J : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hs : ∀ a b, J a b = J b a) (κ ρ : E →ₗ[ℝ] E)
    (F : SpectralPair J κ ρ) (R : VectorModel (H := H) J) (t k g : E)
    (hPB : ∀ (v : H) (T α : ℝ),
      scalarPB J κ ρ t k g (T • F.e+α • F.n) (vectorReading R v))
    (ξ η ν : H) (d : ℝ) (hη : ‖η‖ = 1)
    (hnξ : R.op F.n ξ = 0) (hnη : R.op F.n η = (2 : ℝ) • η)
    (hjξ : R.op F.j ξ = d • η) (heξ : R.op F.e ξ = d • ν)
    (hην : ⟪η,ν⟫ = 0)
    (hdiagξ : ⟪ξ,R.op ((F.μ+F.λ) • J F.n t-J F.n k) ξ⟫ = 0)
    (hdiagη : ⟪η,R.op ((F.μ+F.λ) • J F.n t-J F.n k) η⟫ = 0)
    (hjjξ : ⟪ξ,R.op F.j ξ⟫ = 0) (hjjη : ⟪η,R.op F.j η⟫ = 0)
    (T : ℝ) :
    let V := (F.μ+F.λ) • J F.n t-J F.n k
    let Z := t+(F.μ+F.λ) • k
    2 * |F.λ*T*d+⟪η,R.op V ξ⟫| ≤
      ‖realPerp η (R.op (Z+g) ξ)-(F.λ*T*d) • ν‖ +
      ‖realPerp η (R.op (Z-g) ξ)+(F.λ*T*d) • ν‖ := by
  let a := F.μ+F.λ
  let V := a • J F.n t-J F.n k
  let Z := t+a • k
  let P := realPerp η
  let Wp := Z+g-(F.λ*T) • F.e-(a*F.λ*T) • F.j
  let Wm := Z-g+(F.λ*T) • F.e-(a*F.λ*T) • F.j
  have hηη : ⟪η,η⟫ = 1 := by simp [hη]
  have exactGram (W : E) (ε : ℝ) :
      gram J (vectorReading R (ξ+ε • η)) F.n W =
        4*ε^2*‖P (R.op W ξ+ε • R.op W η)‖^2 := by
    rw [gram, reading_jordan, reading_jordan, reading_jordan]
    have hn : R.op F.n (ξ+ε • η) = (2*ε) • η := by
      simp [hnξ, hnη, smul_smul, mul_comm]
    rw [hn, map_add, map_smul]
    simp only [inner_smul_left, inner_smul_right, hηη, mul_one]
    rw [real_inner_self_eq_norm_sq]
    have perp (z : H) : ‖P z‖^2 = ‖z‖^2-⟪η,z⟫^2 := by
      change ‖z-⟪η,z⟫ • η‖^2 = _
      rw [norm_sub_sq_real, inner_smul_right, real_inner_comm z η, norm_smul]
      simp only [hη, mul_one, Real.norm_eq_abs, sq_abs]
      ring
    rw [perp]
    ring
  have exactRead (ε : ℝ) :
      vectorReading R (ξ+ε • η) ((F.λ*T) • F.j+V) =
        2*ε*(F.λ*T*d+⟪η,R.op V ξ⟫) := by
    have sy (b : E) : ⟪ξ,R.op b η⟫ = ⟪η,R.op b ξ⟫ := by
      rw [← R.symmetric b ξ η, real_inner_comm]
    simp only [vectorReading, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right]
    rw [hjjξ, hjjη, hdiagξ, hdiagη, sy F.j, sy V, hjξ, inner_smul_right, hηη]
    ring
  have finite (ε : ℝ) (hε : 0 < ε) :
      2 * |F.λ*T*d+⟪η,R.op V ξ⟫| ≤
        ‖P (R.op Wp ξ+ε • R.op Wp η)‖ +
        ‖P (R.op Wm ξ+ε • R.op Wm η)‖ := by
    have hb := first_budget J hs κ ρ F t k g (vectorReading R (ξ+ε • η))
      (hPB (ξ+ε • η)) T
    change 2 * |vectorReading R (ξ+ε • η) ((F.λ*T) • F.j+V)| ≤ _ at hb
    rw [exactRead, exactGram, exactGram] at hb
    have sqr (z : H) : Real.sqrt (4*ε^2*‖z‖^2) = 2*ε*‖z‖ := by
      rw [show 4*ε^2*‖z‖^2 = (2*ε*‖z‖)^2 by ring,
        Real.sqrt_sq (by positivity)]
    rw [sqr, sqr, abs_mul, abs_mul, abs_of_pos hε] at hb
    simp only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hb
    apply le_of_mul_le_mul_left (a := 2*ε) (a0 := by positivity)
    convert hb using 1 <;> ring
  have pp : P (R.op F.e ξ) = d • ν := by
    simp [P, realPerp, heξ, hην]
  have pq : P (R.op F.j ξ) = 0 := by simp [P, realPerp, hjξ, hηη]
  have hr : Tendsto (fun ε : ℝ =>
      ‖P (R.op Wp ξ+ε • R.op Wp η)‖ + ‖P (R.op Wm ξ+ε • R.op Wm η)‖)
      (𝓝[>] 0) (𝓝 (‖P (R.op (Z+g) ξ)-(F.λ*T*d) • ν‖ +
        ‖P (R.op (Z-g) ξ)+(F.λ*T*d) • ν‖)) := by
    have hc : Continuous (fun ε : ℝ =>
      ‖P (R.op Wp ξ+ε • R.op Wp η)‖ + ‖P (R.op Wm ξ+ε • R.op Wm η)‖) := by
      dsimp [P, realPerp]; fun_prop
    simpa only [Wp, Wm, zero_smul, add_zero, map_sub, map_add, map_smul,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      pp, pq, smul_zero, sub_zero, smul_smul, mul_assoc] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hr (by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact finite ε hε)

/-- PB alone identifies a transverse real reading of the fixed output.
The vectors and operators act on the full representation, including its environment. -/
theorem fixed_output_anchor_identity (J : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (hs : ∀ a b, J a b = J b a) (κ ρ : E →ₗ[ℝ] E)
    (F : SpectralPair J κ ρ) (R : VectorModel (H := H) J) (t k g : E)
    (hPB : ∀ (v : H) (T α : ℝ),
      scalarPB J κ ρ t k g (T • F.e+α • F.n) (vectorReading R v))
    (ξ η ν : H) (d : ℝ) (hd : d ≠ 0) (hλ : F.λ ≠ 0)
    (hη : ‖η‖ = 1) (hν : ‖ν‖ = 1)
    (hnξ : R.op F.n ξ = 0) (hnη : R.op F.n η = (2 : ℝ) • η)
    (hjξ : R.op F.j ξ = d • η) (heξ : R.op F.e ξ = d • ν)
    (hην : ⟪η,ν⟫ = 0)
    (hdiagξ : ⟪ξ,R.op ((F.μ+F.λ) • J F.n t-J F.n k) ξ⟫ = 0)
    (hdiagη : ⟪η,R.op ((F.μ+F.λ) • J F.n t-J F.n k) η⟫ = 0)
    (hjjξ : ⟪ξ,R.op F.j ξ⟫ = 0) (hjjη : ⟪η,R.op F.j η⟫ = 0) :
    ⟪ν,R.op g ξ⟫ = -⟪η,R.op ((F.μ+F.λ) • J F.n t-J F.n k) ξ⟫ := by
  let V := (F.μ+F.λ) • J F.n t-J F.n k
  let Z := t+(F.μ+F.λ) • k
  let P := realPerp η
  have hb := two_ended_budget (F.λ*d) (⟪η,R.op V ξ⟫/(F.λ*d))
    (mul_ne_zero hλ hd) ν (P (R.op (Z+g) ξ)) (P (R.op (Z-g) ξ)) hν
    (by
      intro T
      have h := vector_budget J hs κ ρ F R t k g hPB ξ η ν d hη
        hnξ hnη hjξ heξ hην hdiagξ hdiagη hjjξ hjjη T
      have heq : 2*|F.λ*d|*|T+⟪η,R.op V ξ⟫/(F.λ*d)| =
          2*|F.λ*T*d+⟪η,R.op V ξ⟫| := by
        rw [mul_assoc, ← abs_mul]
        congr 2
        field_simp
        <;> ring
      rw [heq]
      convert h using 1 <;> congr 2 <;> ring)
  have hνη : ⟪ν,η⟫ = 0 := by rw [real_inner_comm, hην]
  have heq : ⟪ν,P (R.op (Z-g) ξ)⟫-⟪ν,P (R.op (Z+g) ξ)⟫ =
      -2*⟪ν,R.op g ξ⟫ := by
    simp only [P, realPerp, LinearMap.coe_mk, AddHom.coe_mk, inner_sub_right,
      inner_smul_right, hνη, mul_zero, sub_zero, map_sub, map_add,
      LinearMap.sub_apply, LinearMap.add_apply, inner_add_right]
    ring
  rw [heq, mul_div_cancel₀ _ (mul_ne_zero hλ hd)] at hb
  change ⟪ν,R.op g ξ⟫ = -⟪η,R.op V ξ⟫
  linarith

#print axioms fixed_output_anchor_identity

end D5.S3.Quantum.Algebra.PBFixedOutputGram
