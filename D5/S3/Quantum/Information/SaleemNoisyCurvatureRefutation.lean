/- GID: D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SaleemNoisyCurvatureRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.claim; result=D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.result; claim=D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation.claim
   digest: A smooth amplitude-damped two-qubit probe has CoE = 1 and QFI = 8/15. -/

/-
proof_shape: generator_block: bind-only; consumers: trajectory
proof_shape: rho_initial: bind-only; consumers: trajectory
proof_shape: rho0_density: bind-only; consumers: result
proof_shape: dq: bind-only; consumers: ddp, dap, dbp, dcp, dyp
proof_shape: ddp: bind-only; consumers: trajectory
proof_shape: dap: bind-only; consumers: trajectory
proof_shape: dbp: bind-only; consumers: trajectory
proof_shape: dcp: bind-only; consumers: trajectory
proof_shape: dyp: bind-only; consumers: trajectory
proof_shape: trajectory: bind-only; consumers: result
proof_shape: q_point: bind-only; consumers: rho_at_one
proof_shape: rho_at_one: bind-only; consumers: rho_point, deriv_rho_one, concurrence_near
proof_shape: trig_point: bind-only; consumers: rho_point, sld_point, concurrence_near, curvature
proof_shape: rho_point: bind-only; consumers: sld_point, qfi_point
proof_shape: block_derivative: bind-only; consumers: deriv_rho_one
proof_shape: deriv_rho_one: bind-only; consumers: sld_point
proof_shape: sld_point: bind-only; consumers: result
proof_shape: qfi_point: bind-only; consumers: result
proof_shape: spin_product: bind-only; consumers: block_concurrence
proof_shape: spin_charpoly: bind-only; consumers: spin_roots
proof_shape: spin_roots: bind-only; consumers: block_concurrence
proof_shape: sort_four: bind-only; consumers: block_concurrence
proof_shape: block_concurrence: bind-only; consumers: concurrence_near
proof_shape: concurrence_near: bind-only; consumers: concurrence_smooth, curvature
proof_shape: concurrence_smooth: bind-only; consumers: result
proof_shape: smoothC_first: bind-only; consumers: curvature
proof_shape: curvature: bind-only; consumers: result
proof_shape: result: bind-only; consumers: none
escape_witness: none
admission_basis: open-problem-resolution (#17681; Refuted)
Direct frozen dependencies:
  D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.sigmaMinus
  statement_id: sha256:c264f3f829c1e636a8bda11595bc0450f9c1f68e682d98b81949f6a58ffa931f
  D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.IsDensity
  statement_id: sha256:0386217fa1109c4358c01b5fe2db195888fa2f776c05e63cec2e880416d1c8ff
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
The pair-indexed matrix type is written out; exponential decay uses Real.exp directly.
-/

import D5.S3.Quantum.Dynamics.PronkoFredkinNonCyclicAnnihilation
import D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation

noncomputable section

namespace D5.S3.Quantum.Information.SaleemNoisyCurvatureRefutation

open Matrix Complex
open scoped ComplexOrder
open D5.S3.Quantum.Dynamics.PronkoFredkinNonCyclicAnnihilation (sigmaMinus)
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation (IsDensity)


/-- The jump operators `σ₋ ⊗ I` and `I ⊗ σ₋`, with the frozen `σ₋ = !![0, 0; 1, 0] = |1⟩⟨0|`
(arXiv:2504.13729, Appendix B: `σ₋ = (σx − iσy)/2`). -/
def jump1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := Matrix.kroneckerMap (· * ·) sigmaMinus (1 : Matrix (Fin 2) (Fin 2) ℂ)
def jump2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) sigmaMinus

/-- The flip-flop Hamiltonian `H_g = g (|01⟩⟨10| + |10⟩⟨01|)` (Eq. (21) with `η_xy = 1`). -/
def hamiltonian (g : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a b => if (a = (0, 1) ∧ b = (1, 0)) ∨ (a = (1, 0) ∧ b = (0, 1)) then (g : ℂ) else 0

/-- The dissipator `D[O](ρ) = O ρ O† − (O†O ρ + ρ O†O)/2`. -/
def dissipator (O ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := O * ρ * Oᴴ - (1 / 2 : ℂ) • (Oᴴ * O * ρ + ρ * (Oᴴ * O))

/-- The GKSL generator of Eq. (41): `−i[H_g, ρ] + κ Σ_j D[σ₋^{(j)}](ρ)`. -/
def generator (g κ : ℝ) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (-I) • (hamiltonian g * ρ - ρ * hamiltonian g) + (κ : ℂ) • (dissipator jump1 ρ + dissipator jump2 ρ)

/-- `ρ : g ↦ t ↦ ρ_g(t)` solves Eq. (41) with the parameter-independent initial state `ρ₀`
(entrywise derivatives in `t`). -/
def IsTrajectory (ρ₀ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (κ : ℝ) (ρ : ℝ → ℝ → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop :=
  (∀ g, ρ g 0 = ρ₀) ∧ ∀ g t a b, HasDerivAt (fun s => ρ g s a b) (generator g κ (ρ g t) a b) t

/-- `σ_y ⊗ σ_y`. -/
def sigmaYY : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kroneckerMap (· * ·) (!![0, -I; I, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![0, -I; I, 0]

/-- Wootters concurrence (Section II): `C = max(0, λ₁ − λ₂ − λ₃ − λ₄)`, the `λ_j` being the
square roots, in decreasing order, of the eigenvalues of `R = ρ (σ_y ⊗ σ_y) ρ* (σ_y ⊗ σ_y)`. -/
def concurrence (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  let l := ((ρ * sigmaYY * ρ.map star * sigmaYY).charpoly.roots.map (fun z => Real.sqrt z.re)).sort
    (· ≥ ·)
  max 0 (l.getD 0 0 - l.getD 1 0 - l.getD 2 0 - l.getD 3 0)

/-- The entrywise `g`-derivative `∂_g ρ_g(t)`. -/
def derivG (ρ : ℝ → ℝ → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (g t : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun a b => deriv (fun g' => ρ g' t a b) g

/-- `L` is a symmetric logarithmic derivative of `ρ` along `dρ`: Hermitian with `dρ = (ρL + Lρ)/2`. -/
def IsSLD (ρ dρ L : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : Prop := L.IsHermitian ∧ dρ = (1 / 2 : ℂ) • (ρ * L + L * ρ)

/-- Saleem et al., arXiv:2504.13729v4, Section IV.B: "in all cases we conjecture that CoE ≤ QFI"
for the open evolution (41): for every initial density matrix, `κ > 0`, `t > 0`, and every `g` at
which the concurrence is twice differentiable in `g`, `CoE = −∂²_g C ≤ F_Q = Tr(ρ L²)` for the SLD `L`. -/
def claim : Prop :=
  ∀ (ρ₀ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (κ t : ℝ) (ρ : ℝ → ℝ → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ), IsDensity ρ₀ → 0 < κ → 0 < t → IsTrajectory ρ₀ κ ρ →
    ∀ g : ℝ, ContDiffAt ℝ 2 (fun g' => concurrence (ρ g' t)) g →
      ∀ L : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, IsSLD (ρ g t) (derivG ρ g t) L →
        -(deriv (deriv fun g' => concurrence (ρ g' t)) g) ≤ (ρ g t * L * L).trace.re



set_option maxHeartbeats 2000000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

/-- The complex block form in computational-basis order. -/
private def block (d b c a y : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun x z =>
  if x = z then
    (if x = (0, 0) then (d : ℂ) else if x = (0, 1) then b else if x = (1, 0) then c else a)
  else if x = (0, 1) ∧ z = (1, 0) then (y : ℂ) * I
  else if x = (1, 0) ∧ z = (0, 1) then -(y : ℂ) * I else 0

private def dp (κ t : ℝ) : ℝ := Real.exp (-κ * t) ^ 2 / 16
private def ap (κ t : ℝ) : ℝ := 1 - Real.exp (-κ * t) + Real.exp (-κ * t) ^ 2 / 16
private def bp (κ g t : ℝ) : ℝ := Real.exp (-κ * t) * (1 - Real.exp (-κ * t) / 8 + Real.cos (2*g*t)/2) / 2
private def cp (κ g t : ℝ) : ℝ := Real.exp (-κ * t) * (1 - Real.exp (-κ * t) / 8 - Real.cos (2*g*t)/2) / 2
private def yp (κ g t : ℝ) : ℝ := Real.exp (-κ * t) * Real.sin (2*g*t) / 4

private def rho (κ g t : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := block (dp κ t) (bp κ g t) (cp κ g t) (ap κ t) (yp κ g t)
private def rho0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := block (1/16) (11/16) (3/16) (1/16) 0

private theorem generator_block (κ g d b c a y : ℝ) :
    generator g κ (block d b c a y) =
      block (-2*κ*d) (-2*g*y-κ*b+κ*d) (2*g*y-κ*c+κ*d) (κ*(b+c)) (g*(b-c)-κ*y) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [generator, dissipator, jump1, jump2, sigmaMinus, hamiltonian, block,
      Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, star_add, star_mul, star_sub,
      Complex.star_def, Complex.conj_ofReal] <;>
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

private theorem rho_initial (κ g : ℝ) : rho κ g 0 = rho0 := by
  simp [rho, rho0, dp, ap, bp, cp, yp]
  norm_num

private theorem rho0_density : IsDensity rho0 := by
  have hd : rho0 = Matrix.diagonal (fun x : Fin 2 × Fin 2 =>
      if x = (0,0) then (1/16:ℂ) else if x = (0,1) then 11/16 else
      if x = (1,0) then 3/16 else 1/16) := by
    ext ⟨i,j⟩ ⟨k,l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [rho0, block, Matrix.diagonal]
  rw [hd]
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> norm_num [Complex.nonneg_iff]
  · norm_num [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem dq (κ t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-κ * t)) (-κ * Real.exp (-κ * t)) t := by
  change HasDerivAt (fun x : ℝ => Real.exp (-κ*x)) (-κ*Real.exp (-κ*t)) t
  convert (((hasDerivAt_id t).const_mul (-κ)).exp) using 1 <;> simp [mul_comm]


private theorem ddp (κ t : ℝ) : HasDerivAt (dp κ) (-2*κ*dp κ t) t := by
  convert ((dq κ t).pow 2).div_const 16 using 1
  all_goals first | rfl | (norm_num [dp]; ring)

private theorem dap (κ t : ℝ) : HasDerivAt (ap κ) (κ*(bp κ 0 t + cp κ 0 t)) t := by
  convert (((hasDerivAt_const t (1:ℝ)).sub (dq κ t)).add
    (((dq κ t).pow 2).div_const 16)) using 1 <;> first | rfl | (norm_num [ap, bp, cp]; ring)

private theorem dbp (κ g t : ℝ) : HasDerivAt (bp κ g)
      (-2*g*yp κ g t-κ*bp κ g t+κ*dp κ t) t := by
  have ht := ((hasDerivAt_id t).const_mul (2*g)).cos
  convert ((dq κ t).mul (((hasDerivAt_const t (1:ℝ)).sub ((dq κ t).div_const 8)).add
    (ht.div_const 2))).div_const 2 using 1 <;> first | rfl | (norm_num [bp, yp, dp]; ring)

private theorem dcp (κ g t : ℝ) : HasDerivAt (cp κ g)
      (2*g*yp κ g t-κ*cp κ g t+κ*dp κ t) t := by
  have ht := ((hasDerivAt_id t).const_mul (2*g)).cos
  convert ((dq κ t).mul (((hasDerivAt_const t (1:ℝ)).sub ((dq κ t).div_const 8)).sub
    (ht.div_const 2))).div_const 2 using 1 <;> first | rfl | (norm_num [cp, yp, dp]; ring)

private theorem dyp (κ g t : ℝ) : HasDerivAt (yp κ g)
      (g*(bp κ g t-cp κ g t)-κ*yp κ g t) t := by
  have ht := ((hasDerivAt_id t).const_mul (2*g)).sin
  convert ((dq κ t).mul ht).div_const 4 using 1 <;> first | rfl | (norm_num [bp, cp, yp]; ring)

private theorem trajectory (κ : ℝ) : IsTrajectory rho0 κ (rho κ) := by
  refine ⟨rho_initial κ, ?_⟩
  intro g t ⟨i,j⟩ ⟨k,l⟩
  rw [rho, generator_block]
  have hA : κ*(bp κ 0 t+cp κ 0 t) = κ*(bp κ g t+cp κ g t) := by
    dsimp [bp, cp]; ring
  have hda := (dap κ t).ofReal_comp
  rw [hA] at hda
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [rho, block, Fin.reduceFinMk, Prod.mk.injEq, Fin.reduceEq, and_self,
      if_true, if_false, and_true, and_false, false_and, true_and] <;>
    first
    | exact (ddp κ t).ofReal_comp
    | exact (dbp κ g t).ofReal_comp
    | exact (dcp κ g t).ofReal_comp
    | exact hda
    | simpa only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg] using
        ((dyp κ g t).ofReal_comp.mul_const I)
    | simpa only [neg_mul, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg] using
        ((show HasDerivAt (fun s : ℝ => (-(yp κ g s):ℝ)) (-(g*(bp κ g t-cp κ g t)-κ*yp κ g t)) t from (dyp κ g t).neg).ofReal_comp.mul_const I)
    | exact hasDerivAt_const t (0:ℂ)

private theorem q_point : Real.exp (-Real.log 2) = 1/2 := by
  simp [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2)]

private theorem rho_at_one (g : ℝ) : rho (Real.log 2) g 1 =
    block (1/64) ((15+8*Real.cos (2*g))/64) ((15-8*Real.cos (2*g))/64)
      (33/64) (Real.sin (2*g)/8) := by
  unfold rho
  simp only [dp, bp, cp, ap, yp, mul_one, q_point]
  congr 1 <;> ring

private def gstar : ℝ := Real.pi/4

private theorem trig_point : 2*gstar = Real.pi/2 := by unfold gstar; ring

private theorem rho_point : rho (Real.log 2) gstar 1 = block (1/64) (15/64) (15/64) (33/64) (1/8) := by
  rw [rho_at_one, trig_point]
  norm_num

private theorem block_derivative (d b c a y d' b' c' a' y' : ℝ → ℝ) (x : ℝ)
    (hd : HasDerivAt d (d' x) x) (hb : HasDerivAt b (b' x) x)
    (hc : HasDerivAt c (c' x) x) (ha : HasDerivAt a (a' x) x)
    (hy : HasDerivAt y (y' x) x) (u v : Fin 2 × Fin 2) :
    HasDerivAt (fun z => block (d z) (b z) (c z) (a z) (y z) u v)
      (block (d' x) (b' x) (c' x) (a' x) (y' x) u v) x := by
  rcases u with ⟨i,j⟩
  rcases v with ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [block, Fin.reduceFinMk, Prod.mk.injEq, Fin.reduceEq, and_self,
      if_true, if_false, and_true, and_false, false_and, true_and] <;>
    first
    | exact hd.ofReal_comp
    | exact hb.ofReal_comp
    | exact hc.ofReal_comp
    | exact ha.ofReal_comp
    | exact hy.ofReal_comp.mul_const I
    | exact hy.ofReal_comp.neg.mul_const I
    | exact hasDerivAt_const x (0:ℂ)

private theorem deriv_rho_one (g : ℝ) : derivG (rho (Real.log 2)) g 1 =
    block 0 (-Real.sin (2*g)/4) (Real.sin (2*g)/4) 0 (Real.cos (2*g)/4) := by
  have hb : HasDerivAt (fun z : ℝ => (15+8*Real.cos (2*z))/64) (-Real.sin (2*g)/4) g := by
    convert ((hasDerivAt_const g (15:ℝ)).add
      ((((hasDerivAt_id g).const_mul 2).cos).const_mul 8)).div_const 64 using 1 <;> first | rfl | (norm_num; ring)
  have hc : HasDerivAt (fun z : ℝ => (15-8*Real.cos (2*z))/64) (Real.sin (2*g)/4) g := by
    convert ((hasDerivAt_const g (15:ℝ)).sub
      ((((hasDerivAt_id g).const_mul 2).cos).const_mul 8)).div_const 64 using 1 <;> first | rfl | (norm_num; ring)
  have hy : HasDerivAt (fun z : ℝ => Real.sin (2*z)/8) (Real.cos (2*g)/4) g := by
    convert (((hasDerivAt_id g).const_mul 2).sin).div_const 8 using 1 <;> first | rfl | (norm_num; ring)
  ext i j
  simp only [derivG, Matrix.of_apply, rho_at_one]
  exact (block_derivative _ _ _ _ _ (fun _ => 0) (fun z => -Real.sin (2*z)/4)
    (fun z => Real.sin (2*z)/4) (fun _ => 0) (fun z => Real.cos (2*z)/4) g
    (hasDerivAt_const g (1/64)) hb hc (hasDerivAt_const g (33/64)) hy i j).deriv

private def sld : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := Matrix.diagonal (fun x => if x = (0,1) then (-16/15:ℂ)
  else if x = (1,0) then 16/15 else 0)

private theorem sld_point : IsSLD (rho (Real.log 2) gstar 1) (derivG (rho (Real.log 2)) gstar 1) sld := by
  constructor
  · ext ⟨i,j⟩ ⟨k,l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [sld, Matrix.IsHermitian, Matrix.conjTranspose_apply, Matrix.diagonal]
  · rw [rho_point, deriv_rho_one, trig_point]
    ext ⟨i,j⟩ ⟨k,l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [sld, block, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.diagonal] <;> apply Complex.ext <;> norm_num

private theorem qfi_point : (rho (Real.log 2) gstar 1 * sld * sld).trace.re = 8/15 := by
  rw [rho_point]
  norm_num [sld, block, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.diagonal]
open Polynomial

private def spinBlock (d b c a y : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun x z =>
  if x = z then
    (if x = (0,0) ∨ x = (1,1) then ((a*d:ℝ):ℂ) else ((b*c+y^2:ℝ):ℂ))
  else if x = (0,1) ∧ z = (1,0) then ((2*b*y:ℝ):ℂ)*I
  else if x = (1,0) ∧ z = (0,1) then -((2*c*y:ℝ):ℂ)*I else 0

private theorem spin_product (d b c a y : ℝ) :
    block d b c a y * sigmaYY * (block d b c a y).map star * sigmaYY = spinBlock d b c a y := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [block, spinBlock, sigmaYY, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.map_apply, Complex.star_def] <;>
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, pow_two] <;> ring

private theorem spin_charpoly (d b c a y : ℝ) :
    (spinBlock d b c a y).charpoly =
      (X-C ((a*d:ℝ):ℂ))^2 *
      (X^2-C ((2*(b*c+y^2):ℝ):ℂ)*X+C (((b*c-y^2)^2:ℝ):ℂ)) := by
  rw [← Matrix.charpoly_reindex finProdFinEquiv]
  rw [Matrix.charpoly, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three]
  simp [Matrix.charmatrix, Matrix.submatrix, Matrix.reindex_apply, finProdFinEquiv, spinBlock,
    Fin.succAbove, Fin.divNat, Fin.modNat]
  simp only [map_ofNat]
  ring_nf
  simp [← map_pow, Complex.I_sq]
  ring

private theorem spin_roots (d b c a y : ℝ) (hbc : 0 ≤ b*c) :
    (spinBlock d b c a y).charpoly.roots =
      {(((Real.sqrt (b*c)+y)^2:ℝ):ℂ), (((Real.sqrt (b*c)-y)^2:ℝ):ℂ),
       ((a*d:ℝ):ℂ), ((a*d:ℝ):ℂ)} := by
  have hs : (Real.sqrt (b*c))^2 = b*c := Real.sq_sqrt hbc
  have he1 : ((2*(b*c+y^2):ℝ):ℂ) =
      (((Real.sqrt (b*c)+y)^2:ℝ):ℂ)+(((Real.sqrt (b*c)-y)^2:ℝ):ℂ) := by
    have he : 2*(b*c+y^2) = (Real.sqrt (b*c)+y)^2+(Real.sqrt (b*c)-y)^2 := by nlinarith
    exact_mod_cast he
  have he2 : (((b*c-y^2)^2:ℝ):ℂ) =
      (((Real.sqrt (b*c)+y)^2:ℝ):ℂ)*(((Real.sqrt (b*c)-y)^2:ℝ):ℂ) := by
    have he : (b*c-y^2)^2 = (Real.sqrt (b*c)+y)^2*(Real.sqrt (b*c)-y)^2 := by
      calc
        (b*c-y^2)^2 = ((Real.sqrt (b*c))^2-y^2)^2 := by rw [hs]
        _ = (Real.sqrt (b*c)+y)^2*(Real.sqrt (b*c)-y)^2 := by ring
    exact_mod_cast he
  have hf : (spinBlock d b c a y).charpoly =
      (({(((Real.sqrt (b*c)+y)^2:ℝ):ℂ), (((Real.sqrt (b*c)-y)^2:ℝ):ℂ),
       ((a*d:ℝ):ℂ), ((a*d:ℝ):ℂ)} : Multiset ℂ).map (fun z => X-C z)).prod := by
    rw [spin_charpoly, he1, he2]
    simp [Multiset.insert_eq_cons, map_add, map_mul]
    ring
  rw [hf, Polynomial.roots_multiset_prod_X_sub_C]

private theorem sort_four (a b c d : ℝ) (h1 : b ≤ a) (h2 : c ≤ b) (h3 : d ≤ c) :
    (({a,b,c,d}:Multiset ℝ).sort (· ≥ ·)) = [a,b,c,d] := by
  rw [Multiset.insert_eq_cons, Multiset.sort_cons, Multiset.insert_eq_cons, Multiset.sort_cons,
    Multiset.insert_eq_cons, Multiset.sort_cons, Multiset.sort_singleton]
  · intro x hx; rw [Multiset.mem_singleton] at hx; linarith
  · intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> linarith
  · intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> linarith

private theorem block_concurrence (d b c a y : ℝ) (hbc : 0 ≤ b*c) (hy : 0 ≤ y)
    (horder : Real.sqrt (a*d) ≤ Real.sqrt (b*c)-y) (hpos : Real.sqrt (a*d) ≤ y) :
    concurrence (block d b c a y) = 2*y-2*Real.sqrt (a*d) := by
  have hr := Real.sqrt_nonneg (a*d)
  have hs := Real.sqrt_nonneg (b*c)
  have hmy : 0 ≤ Real.sqrt (b*c)-y := le_trans hr horder
  have hpy : 0 ≤ Real.sqrt (b*c)+y := by positivity
  unfold concurrence
  rw [spin_product, spin_roots d b c a y hbc]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Complex.ofReal_re, Real.sqrt_sq_eq_abs, abs_of_nonneg hpy, abs_of_nonneg hmy]
  have hsort := sort_four (Real.sqrt (b*c)+y) (Real.sqrt (b*c)-y) (Real.sqrt (a*d)) (Real.sqrt (a*d)) (by linarith) horder (le_refl _)
  simp only [Multiset.insert_eq_cons] at hsort
  rw [hsort]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [max_eq_right (by linarith)]
  ring
open Filter Topology

private def smoothC (g : ℝ) : ℝ := Real.sin (2*g)/4 - Real.sqrt 33/32

private theorem concurrence_near : (fun g => concurrence (rho (Real.log 2) g 1)) =ᶠ[𝓝 gstar] smoothC := by
  let B : ℝ → ℝ := fun g => (15+8*Real.cos (2*g))/64
  let C : ℝ → ℝ := fun g => (15-8*Real.cos (2*g))/64
  let Y : ℝ → ℝ := fun g => Real.sin (2*g)/8
  let r : ℝ := Real.sqrt (33/4096)
  have hbval : B gstar = 15/64 := by simp [B, trig_point]
  have hcval : C gstar = 15/64 := by simp [C, trig_point]
  have hyval : Y gstar = 1/8 := by simp [Y, trig_point]
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r^2 = 33/4096 := Real.sq_sqrt (by norm_num)
  have hr7 : r < 7/64 := by nlinarith
  have hsval : Real.sqrt (B gstar*C gstar) = 15/64 := by
    rw [hbval, hcval]
    norm_num [Real.sqrt_div, ← sq]
  have hbc : ∀ᶠ g in 𝓝 gstar, 0 < B g*C g :=
    (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) gstar).eventually_lt
      (by dsimp [B,C]; fun_prop) (by rw [hbval,hcval]; norm_num)
  have hY : ∀ᶠ g in 𝓝 gstar, 0 < Y g :=
    (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) gstar).eventually_lt
      (by dsimp [Y]; fun_prop) (by rw [hyval]; norm_num)
  have hord : ∀ᶠ g in 𝓝 gstar, r < Real.sqrt (B g*C g)-Y g :=
    (continuousAt_const : ContinuousAt (fun _ : ℝ => r) gstar).eventually_lt
      (by dsimp [B,C,Y]; fun_prop) (by rw [hsval,hyval]; linarith)
  have hpos : ∀ᶠ g in 𝓝 gstar, r < Y g :=
    (continuousAt_const : ContinuousAt (fun _ : ℝ => r) gstar).eventually_lt
      (by dsimp [Y]; fun_prop) (by rw [hyval]; linarith)
  filter_upwards [hbc,hY,hord,hpos] with g hbc hY hord hpos
  rw [rho_at_one]
  have hcon := block_concurrence (1/64) (B g) (C g) (33/64) (Y g)
    hbc.le hY.le (by convert hord.le using 1 <;> first | rfl | norm_num [r,Real.sqrt_div]) (by convert hpos.le using 1 <;> first | rfl | norm_num [r,Real.sqrt_div])
  change concurrence (block _ (B g) (C g) _ (Y g)) = smoothC g
  rw [hcon]
  norm_num [smoothC, Y, Real.sqrt_div]
  ring

private theorem concurrence_smooth : ContDiffAt ℝ 2 (fun g => concurrence (rho (Real.log 2) g 1)) gstar := by
  have hs : ContDiffAt ℝ 2 smoothC gstar := by unfold smoothC; fun_prop
  exact hs.congr_of_eventuallyEq concurrence_near

private theorem smoothC_first (g : ℝ) : deriv smoothC g = Real.cos (2*g)/2 := by
  apply HasDerivAt.deriv
  unfold smoothC
  convert (((((hasDerivAt_id g).const_mul 2).sin).div_const 4).sub_const (Real.sqrt 33/32)) using 1 <;>
    first | rfl | (norm_num; ring)

private theorem curvature : deriv (deriv (fun g => concurrence (rho (Real.log 2) g 1))) gstar = -1 := by
  rw [concurrence_near.deriv.deriv_eq]
  have hfun : deriv smoothC = fun g => Real.cos (2*g)/2 := funext smoothC_first
  rw [hfun]
  have hder : HasDerivAt (fun g : ℝ => Real.cos (2*g)/2) (-Real.sin (2*gstar)) gstar := by
    convert (((hasDerivAt_id gstar).const_mul 2).cos).div_const 2 using 1 <;>
      first | rfl | (norm_num; ring)
  rw [hder.deriv, trig_point]
  norm_num

theorem result : ¬ claim := by
  intro hclaim
  have bound := hclaim rho0 (Real.log 2) 1 (rho (Real.log 2)) rho0_density
    (Real.log_pos (by norm_num)) (by norm_num) (trajectory (Real.log 2))
    gstar concurrence_smooth sld sld_point
  rw [curvature, qfi_point] at bound
  norm_num at bound


end D5.S3.Quantum.Information.SaleemNoisyCurvatureRefutation
end
