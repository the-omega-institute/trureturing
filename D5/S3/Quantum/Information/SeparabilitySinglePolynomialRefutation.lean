/- GID: D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.claim; result=D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.result; claim=D5/S3/Quantum/Information/SeparabilitySinglePolynomialRefutation.claim
   digest: No single polynomial inequality characterizes all bipartite separable states. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity
import D5.S3.Quantum.Information.SLDSpectralEnergy

/-! An affine family of qubit–qutrit states excludes a single polynomial separability criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option linter.style.longLine false

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open D5.S3.Resource.CompositeCones
open D5.S3.Resource.EntanglementWitness
open D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite (partialTranspose)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)

namespace D5.S3.Quantum.Information.SeparabilitySinglePolynomialRefutation

noncomputable section

/-- Real and imaginary coordinates of the matrix entries. -/
def coords {m n : ℕ} (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (Fin m × Fin n) × (Fin m × Fin n) × Bool → ℝ :=
  fun (p, q, b) => if b then (ρ p q).im else (ρ p q).re

/-- Polynomial invariance on density operators under arbitrary local unitary conjugations. -/
def IsInvariant {m n : ℕ}
    (f : MvPolynomial ((Fin m × Fin n) × (Fin m × Fin n) × Bool) ℝ) : Prop :=
  ∀ (UA : unitaryGroup (Fin m) ℂ) (UB : unitaryGroup (Fin n) ℂ)
    (ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ), IsDensity ρ →
    MvPolynomial.eval (coords
      (((UA : Matrix _ _ ℂ) ⊗ₖ (UB : Matrix _ _ ℂ)) * ρ *
        ((UA : Matrix _ _ ℂ) ⊗ₖ (UB : Matrix _ _ ℂ))ᴴ)) f =
      MvPolynomial.eval (coords ρ) f

/-- The dimension-dependent single-inequality separability question of Krüger and Werner. -/
def claim : Prop :=
  ∀ m n : ℕ, 2 ≤ m → 2 ≤ n →
    ∃ f : MvPolynomial ((Fin m × Fin n) × (Fin m × Fin n) × Bool) ℝ,
      IsInvariant f ∧ ∀ ρ : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
        IsDensity ρ → (0 ≤ MvPolynomial.eval (coords ρ) f ↔ separableCone ρ)

private def rho (x y : ℝ) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
  fun p q =>
    if p = q then
      if p = (0, 0) ∨ p = (1, 1) then ((1 / 8 + 3 * x / 40 - y / 40 : ℝ) : ℂ)
      else if p = (0, 1) ∨ p = (1, 2) then ((1 / 8 - x / 40 + 3 * y / 40 : ℝ) : ℂ)
      else ((1 / 4 - x / 20 - y / 20 : ℝ) : ℂ)
    else if (p = (0, 1) ∧ q = (1, 0)) ∨ (p = (1, 0) ∧ q = (0, 1)) then
      ((-1 / 8 + x / 8 + y / 40 : ℝ) : ℂ)
    else if (p = (0, 2) ∧ q = (1, 1)) ∨ (p = (1, 1) ∧ q = (0, 2)) then
      ((-1 / 8 + x / 40 + y / 8 : ℝ) : ℂ)
    else 0

private def positiveCoefficients (x y : ℝ) : Fin 8 → ℝ :=
  ![(5 + 3 * x - y) / 40, (5 - x + 3 * y) / 40,
    (5 - 5 * x - y) / 240, (5 - x - 5 * y) / 240,
    (5 + 7 * x + 11 * y) / 120, (5 + 11 * x + 7 * y) / 120,
    (5 + 11 * x - y) / 80, (5 - x + 11 * y) / 80]

private def positiveVectors : Fin 8 → (Fin 2 × Fin 3 → ℂ) :=
  ![Pi.single (0, 0) 1, Pi.single (1, 2) 1,
    2 • Pi.single (0, 1) 1 - 3 • Pi.single (1, 0) 1,
    2 • Pi.single (1, 1) 1 - 3 • Pi.single (0, 2) 1,
    Pi.single (0, 1) 1, Pi.single (1, 1) 1,
    Pi.single (1, 0) 1, Pi.single (0, 2) 1]

private lemma rho_trace (x y : ℝ) : (rho x y).trace = 1 := by
  norm_num [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_three, rho]
  ring

set_option maxHeartbeats 2000000 in
private lemma rho_positive_decomposition (x y : ℝ) :
    rho x y = ∑ i : Fin 8, positiveCoefficients x y i •
      vecMulVec (positiveVectors i) (star (positiveVectors i)) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [rho, positiveCoefficients, positiveVectors, Fin.sum_univ_succ,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.single_apply,
      Pi.star_apply, Complex.real_smul, map_ofNat] <;> push_cast <;> ring

private lemma rho_posSemidef {x y : ℝ} (hx : |x| ≤ 1 / 4) (hy : |y| ≤ 1 / 4) :
    (rho x y).PosSemidef := by
  rw [rho_positive_decomposition]
  apply Matrix.posSemidef_sum
  intro i _
  apply (posSemidef_vecMulVec_self_star _).smul
  obtain ⟨hxl, hxu⟩ := abs_le.mp hx
  obtain ⟨hyl, hyu⟩ := abs_le.mp hy
  fin_cases i <;> dsimp [positiveCoefficients] <;> linarith

private lemma rho_density {x y : ℝ} (hx : |x| ≤ 1 / 4) (hy : |y| ≤ 1 / 4) :
    IsDensity (rho x y) := by
  exact ⟨rho_posSemidef hx hy, rho_trace x y⟩

private lemma rho_affine (x y : ℝ) :
    rho x y = (1 - x - y) • rho 0 0 + x • rho 1 0 + y • rho 0 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [rho, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul] <;>
      ring

set_option maxHeartbeats 2000000 in
private lemma base_zero_separable : separableCone (rho 0 0) := by
  let a : Fin 6 → Fin 2 → ℂ :=
    ![![1, 1], ![1, Complex.I], ![1, -1], ![1, -Complex.I], ![1, 0], ![0, 1]]
  let b : Fin 6 → Fin 3 → ℂ :=
    ![![1, -1, 1], ![-1, Complex.I, 1], ![1, 1, 1], ![-1, -Complex.I, 1],
      ![0, 0, 1], ![1, 0, 0]]
  let c : Fin 6 → ℝ := ![1 / 32, 1 / 32, 1 / 32, 1 / 32, 1 / 8, 1 / 8]
  refine ⟨6, fun i => c i • vecMulVec (a i) (star (a i)),
    fun i => vecMulVec (b i) (star (b i)), ?_, ?_⟩
  · intro i
    refine ⟨(posSemidef_vecMulVec_self_star _).smul ?_,
      posSemidef_vecMulVec_self_star _⟩
    fin_cases i <;> norm_num [c]
  · ext ⟨u, v⟩ ⟨w, z⟩
    fin_cases u <;> fin_cases v <;> fin_cases w <;> fin_cases z <;>
      norm_num [a, b, c, rho, Fin.sum_univ_succ, Matrix.sum_apply,
        Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
        Pi.star_apply, Complex.real_smul, Complex.ext_iff]

set_option maxHeartbeats 2000000 in
private lemma base_one_separable : separableCone (rho 1 0) := by
  let a : Fin 8 → Fin 2 → ℂ :=
    ![![1, 1], ![1, Complex.I], ![1, -1], ![1, -Complex.I],
      ![1, 0], ![0, 1], ![1, 0], ![0, 1]]
  let b : Fin 8 → Fin 3 → ℂ :=
    ![![0, 1, -1], ![0, 1, -Complex.I], ![0, 1, 1], ![0, 1, Complex.I],
      ![0, 0, 1], ![0, 1, 0], ![1, 0, 0], ![1, 0, 0]]
  let c : Fin 8 → ℝ :=
    ![1 / 40, 1 / 40, 1 / 40, 1 / 40, 1 / 10, 1 / 10, 1 / 5, 1 / 5]
  refine ⟨8, fun i => c i • vecMulVec (a i) (star (a i)),
    fun i => vecMulVec (b i) (star (b i)), ?_, ?_⟩
  · intro i
    refine ⟨(posSemidef_vecMulVec_self_star _).smul ?_,
      posSemidef_vecMulVec_self_star _⟩
    fin_cases i <;> norm_num [c]
  · ext ⟨u, v⟩ ⟨w, z⟩
    fin_cases u <;> fin_cases v <;> fin_cases w <;> fin_cases z <;>
      norm_num [a, b, c, rho, Fin.sum_univ_succ, Matrix.sum_apply,
        Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
        Pi.star_apply, Complex.real_smul, Complex.ext_iff]

set_option maxHeartbeats 2000000 in
private lemma base_two_separable : separableCone (rho 0 1) := by
  let a : Fin 8 → Fin 2 → ℂ :=
    ![![1, 1], ![1, Complex.I], ![1, -1], ![1, -Complex.I],
      ![1, 0], ![0, 1], ![1, 0], ![0, 1]]
  let b : Fin 8 → Fin 3 → ℂ :=
    ![![1, -1, 0], ![1, -Complex.I, 0], ![1, 1, 0], ![1, Complex.I, 0],
      ![0, 1, 0], ![1, 0, 0], ![0, 0, 1], ![0, 0, 1]]
  let c : Fin 8 → ℝ :=
    ![1 / 40, 1 / 40, 1 / 40, 1 / 40, 1 / 10, 1 / 10, 1 / 5, 1 / 5]
  refine ⟨8, fun i => c i • vecMulVec (a i) (star (a i)),
    fun i => vecMulVec (b i) (star (b i)), ?_, ?_⟩
  · intro i
    refine ⟨(posSemidef_vecMulVec_self_star _).smul ?_,
      posSemidef_vecMulVec_self_star _⟩
    fin_cases i <;> norm_num [c]
  · ext ⟨u, v⟩ ⟨w, z⟩
    fin_cases u <;> fin_cases v <;> fin_cases w <;> fin_cases z <;>
      norm_num [a, b, c, rho, Fin.sum_univ_succ, Matrix.sum_apply,
        Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
        Pi.star_apply, Complex.real_smul, Complex.ext_iff]

private lemma rho_separable {x y : ℝ} (hx : |x| ≤ 1 / 4) (hy : |y| ≤ 1 / 4)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) : separableCone (rho x y) := by
  rw [rho_affine]
  exact separableCone_add
    (separableCone_add
      (separableCone_smul (by linarith [abs_le.mp hx, abs_le.mp hy]) base_zero_separable)
      (separableCone_smul hx0 base_one_separable))
    (separableCone_smul hy0 base_two_separable)

private lemma partialTranspose_quadratic_x (x y : ℝ) :
    (star (Pi.single (0, 0) 1 + Pi.single (1, 1) 1) ⬝ᵥ
      (partialTranspose (rho x y)) *ᵥ (Pi.single (0, 0) 1 + Pi.single (1, 1) 1)).re =
      2 * x / 5 := by
  norm_num [partialTranspose, rho, dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three, Pi.single_apply, Pi.star_apply,
    Complex.add_re]
  ring

private lemma partialTranspose_quadratic_y (x y : ℝ) :
    (star (Pi.single (0, 1) 1 + Pi.single (1, 2) 1) ⬝ᵥ
      (partialTranspose (rho x y)) *ᵥ (Pi.single (0, 1) 1 + Pi.single (1, 2) 1)).re =
      2 * y / 5 := by
  norm_num [partialTranspose, rho, dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_three, Pi.single_apply, Pi.star_apply,
    Complex.add_re]
  ring

private lemma rho_entangled {x y : ℝ} (h : x < 0 ∨ y < 0) :
    ¬ separableCone (rho x y) := by
  intro hs
  have hp : (partialTranspose (rho x y)).PosSemidef :=
    D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef hs
  rcases h with hx | hy
  · have hq := hp.re_dotProduct_nonneg (Pi.single (0, 0) 1 + Pi.single (1, 1) 1)
    change 0 ≤ (star (Pi.single (0, 0) 1 + Pi.single (1, 1) 1) ⬝ᵥ
      (partialTranspose (rho x y)) *ᵥ (Pi.single (0, 0) 1 + Pi.single (1, 1) 1)).re at hq
    rw [partialTranspose_quadratic_x] at hq
    linarith
  · have hq := hp.re_dotProduct_nonneg (Pi.single (0, 1) 1 + Pi.single (1, 2) 1)
    change 0 ≤ (star (Pi.single (0, 1) 1 + Pi.single (1, 2) 1) ⬝ᵥ
      (partialTranspose (rho x y)) *ᵥ (Pi.single (0, 1) 1 + Pi.single (1, 2) 1)).re at hq
    rw [partialTranspose_quadratic_y] at hq
    linarith

private lemma coords_affine (x y : ℝ)
    (i : (Fin 2 × Fin 3) × (Fin 2 × Fin 3) × Bool) :
    coords (rho x y) i = coords (rho 0 0) i +
      x * (coords (rho 1 0) i - coords (rho 0 0) i) +
      y * (coords (rho 0 1) i - coords (rho 0 0) i) := by
  rcases i with ⟨p, q, t⟩
  cases t
  · change (rho x y p q).re = (rho 0 0 p q).re +
      x * ((rho 1 0 p q).re - (rho 0 0 p q).re) +
      y * ((rho 0 1 p q).re - (rho 0 0 p q).re)
    rw [rho_affine x y]
    simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul,
      Complex.add_re, Complex.re_ofReal_mul]
    ring
  · change (rho x y p q).im = (rho 0 0 p q).im +
      x * ((rho 1 0 p q).im - (rho 0 0 p q).im) +
      y * ((rho 0 1 p q).im - (rho 0 0 p q).im)
    rw [rho_affine x y]
    simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul,
      Complex.add_im, Complex.im_ofReal_mul]
    ring

private def restriction
    (f : MvPolynomial ((Fin 2 × Fin 3) × (Fin 2 × Fin 3) × Bool) ℝ) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (coords (rho 0 0) i) +
      Polynomial.X * Polynomial.C (coords (rho 0 1) i - coords (rho 0 0) i)) f

private lemma restriction_eval
    (f : MvPolynomial ((Fin 2 × Fin 3) × (Fin 2 × Fin 3) × Bool) ℝ) (y : ℝ) :
    Polynomial.eval y (restriction f) = MvPolynomial.eval (coords (rho 0 y)) f := by
  unfold restriction
  rw [MvPolynomial.polynomial_eval_eval₂]
  have hc : (Polynomial.evalRingHom y).comp Polynomial.C = RingHom.id ℝ := by
    ext r
    exact Polynomial.eval_C
  rw [hc]
  change MvPolynomial.eval _ f = MvPolynomial.eval _ f
  apply congrArg (fun v => MvPolynomial.eval v f)
  funext i
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  rw [coords_affine 0 y i]
  ring

private lemma evaluation_continuous
    (f : MvPolynomial ((Fin 2 × Fin 3) × (Fin 2 × Fin 3) × Bool) ℝ) (y : ℝ) :
    Continuous (fun x : ℝ => MvPolynomial.eval (coords (rho x y)) f) := by
  apply (MvPolynomial.continuous_eval f).comp
  apply continuous_pi
  intro i
  have hi : (fun x : ℝ => coords (rho x y) i) = fun x =>
      coords (rho 0 0) i + x * (coords (rho 1 0) i - coords (rho 0 0) i) +
        y * (coords (rho 0 1) i - coords (rho 0 0) i) :=
    funext fun x => coords_affine x y i
  rw [hi]
  fun_prop

private lemma boundary_zero
    (f : MvPolynomial ((Fin 2 × Fin 3) × (Fin 2 × Fin 3) × Bool) ℝ)
    (hf : ∀ ρ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ,
      IsDensity ρ → (0 ≤ MvPolynomial.eval (coords ρ) f ↔ separableCone ρ))
    {y : ℝ} (hy : 0 < y) (hy' : y < 1 / 4) :
    Polynomial.eval y (restriction f) = 0 := by
  rw [restriction_eval]
  have hyabs : |y| ≤ 1 / 4 := abs_le.mpr ⟨by linarith, hy'.le⟩
  have hzero : |(0 : ℝ)| ≤ 1 / 4 := by norm_num
  apply le_antisymm
  · have hlim : Filter.Tendsto (fun x : ℝ => MvPolynomial.eval (coords (rho x y)) f)
        (nhdsWithin (0 : ℝ) (Set.Iio 0))
        (nhds (MvPolynomial.eval (coords (rho 0 y)) f)) :=
      ((evaluation_continuous f y).continuousAt (x := 0)).tendsto.mono_left
        nhdsWithin_le_nhds
    apply le_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsLT (show (-1 / 4 : ℝ) < 0 by norm_num)] with x hx
    have hd := rho_density (x := x) (y := y)
      (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩) hyabs
    exact (lt_of_not_ge (fun hv => rho_entangled (Or.inl hx.2) ((hf _ hd).mp hv))).le
  · exact (hf _ (rho_density hzero hyabs)).mpr
      (rho_separable hzero hyabs le_rfl hy.le)

/-- Qubit–qutrit states refute the dimension-dependent single-polynomial criterion. -/
theorem result : ¬ claim := by
  intro hc
  obtain ⟨f, _, hf⟩ := hc 2 3 (by norm_num) (by norm_num)
  have hg : restriction f = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.Ioo_infinite (show (0 : ℝ) < 1 / 4 by norm_num)).mono
    intro y hy
    exact boundary_zero f hf hy.1 hy.2
  have hd : IsDensity (rho 0 (-1 / 8)) := rho_density (by norm_num) (by norm_num)
  have he : MvPolynomial.eval (coords (rho 0 (-1 / 8))) f = 0 := by
    rw [← restriction_eval, hg, Polynomial.eval_zero]
  exact rho_entangled (x := 0) (y := -1 / 8) (Or.inr (by norm_num))
    ((hf _ hd).mp (by rw [he]))

end

end D5.S3.Quantum.Information.SeparabilitySinglePolynomialRefutation
