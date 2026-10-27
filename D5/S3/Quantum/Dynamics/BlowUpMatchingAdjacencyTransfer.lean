/- GID: D5/S3/Quantum/Dynamics/BlowUpMatchingAdjacencyTransfer
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/BlowUpMatchingAdjacencyTransfer
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Perfect matchings in every clone set induce adjacency transfer at pi/2. -/

import D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Adjacency transfer from integral eigenvalue support and uniform clone matchings. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Dynamics.BlowUpMatchingAdjacencyTransfer

open Matrix Complex Finset
open D5.S3.Quantum.Dynamics.RationalWeightPathTransfer
open scoped BigOperators Matrix.Norms.Operator

/-- The adjacency eigenvalue support at `v` is integral: every complex eigenvector for a real
 eigenvalue with a nonzero `v` coordinate has an integer eigenvalue. -/
def IntegralSupport {m : ℕ} (g : SimpleGraph (Fin m)) [DecidableRel g.Adj] (v : Fin m) :
    Prop :=
  ∀ (l : ℝ) (x : Fin m → ℂ), g.adjMatrix ℂ *ᵥ x = (l : ℂ) • x →
    x v ≠ 0 → ∃ z : ℤ, l = z

/-- A perfect matching of clone indices is a fixed-point-free involutive permutation. -/
def IsPerfectMatching {n : ℕ} (ρ : Equiv.Perm (Fin n)) : Prop :=
  ρ * ρ = 1 ∧ ∀ j, ρ j ≠ j

/-- Adjacency of the blow-up with a matching in every clone set. Indices are `(vertex, clone)`;
`permMatrix` sends a basis vector to its inverse image, equal to its image for an involution. -/
def blowUpMatching {m : ℕ} (g : SimpleGraph (Fin m)) [DecidableRel g.Adj]
    (n : ℕ) (ρ : Equiv.Perm (Fin n)) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  Matrix.kroneckerMap (· * ·) (g.adjMatrix ℂ) (Matrix.of fun _ _ => 1) +
    Matrix.kroneckerMap (· * ·) 1 (ρ.permMatrix ℂ)

private theorem integral_phase (n : ℕ) (hn : 4 ∣ n) (z : ℤ) :
    Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * I * n * z) = 1 := by
  rcases hn with ⟨q, rfl⟩
  convert Complex.exp_int_mul_two_pi_mul_I ((q : ℤ) * z) using 1
  congr 1
  push_cast
  ring

private theorem base_periodic {m n : ℕ} (g : SimpleGraph (Fin m))
    [DecidableRel g.Adj] (v : Fin m) (hv : IntegralSupport g v) (hn : 4 ∣ n) :
    NormedSpace.exp (((((Real.pi / 2 : ℝ) : ℂ) * I) * n) • g.adjMatrix ℂ) *ᵥ
      Pi.single v 1 = Pi.single v 1 := by
  let h := g.isHermitian_adjMatrix ℂ
  have hphase (k : Fin m) :
      Complex.exp (((((Real.pi / 2 : ℝ) : ℂ) * I) * n) * h.eigenvalues k) *
        star ((h.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) v k) =
        star ((h.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) v k) := by
    by_cases hk : h.eigenvectorBasis k v = 0
    · simp only [Matrix.IsHermitian.eigenvectorUnitary_apply, hk, star_zero, mul_zero]
    · have heig : g.adjMatrix ℂ *ᵥ ⇑(h.eigenvectorBasis k) =
          (h.eigenvalues k : ℂ) • ⇑(h.eigenvectorBasis k) := by
        ext i
        have he := congrFun (h.mulVec_eigenvectorBasis k) i
        simpa only [Pi.smul_apply, Complex.real_smul, smul_eq_mul] using he
      obtain ⟨z, hz⟩ := hv (h.eigenvalues k) ⇑(h.eigenvectorBasis k) heig hk
      rw [hz, Complex.ofReal_intCast, integral_phase n hn z, one_mul]
  ext w
  rw [Matrix.mulVec_single_one, spectral_exp h]
  change ((h.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) *
    diagonal (fun k => Complex.exp (((((Real.pi / 2 : ℝ) : ℂ) * I) * n) *
      h.eigenvalues k)) * star (h.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)) w v = _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply]
  calc
    _ = ∑ k, (h.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) w k *
        star ((h.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) v k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_assoc, hphase]
    _ = _ := by
      have hu : (h.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) *
          star (h.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) = 1 := by
        simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self h.eigenvectorUnitary
      have he := congrArg (fun b : Matrix (Fin m) (Fin m) ℂ => b w v) hu
      simpa only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply,
        Pi.single_apply, Function.update_apply] using he

private theorem blowup_commute {m n : ℕ} (g : SimpleGraph (Fin m))
    [DecidableRel g.Adj] (ρ : Equiv.Perm (Fin n)) :
    Commute (Matrix.kroneckerMap (· * ·) (g.adjMatrix ℂ)
      (Matrix.of fun _ _ : Fin n => (1 : ℂ)))
      (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin m) (Fin m) ℂ) (ρ.permMatrix ℂ)) := by
  have hjp : (Matrix.of fun _ _ : Fin n => (1 : ℂ)) * ρ.permMatrix ℂ =
      Matrix.of fun _ _ : Fin n => (1 : ℂ) := by
    ext i j
    have h := congrFun (Matrix.vecMul_permMatrix (R := ℂ) ρ (v := fun _ => 1)) j
    change (∑ k, 1 * ρ.permMatrix ℂ k j) = 1 at h
    exact h
  have hpj : ρ.permMatrix ℂ * (Matrix.of fun _ _ : Fin n => (1 : ℂ)) =
      Matrix.of fun _ _ : Fin n => (1 : ℂ) := by
    ext i j
    have h := congrFun (Matrix.permMatrix_mulVec (R := ℂ) ρ (v := fun _ => 1)) i
    change (∑ k, ρ.permMatrix ℂ i k * 1) = 1 at h
    exact h
  change Matrix.kronecker (g.adjMatrix ℂ) (Matrix.of fun _ _ => 1) *
    Matrix.kronecker 1 (ρ.permMatrix ℂ) = Matrix.kronecker 1 (ρ.permMatrix ℂ) *
      Matrix.kronecker (g.adjMatrix ℂ) (Matrix.of fun _ _ => 1)
  unfold Matrix.kronecker
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.one_mul, hjp, hpj]

private theorem exp_involution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Matrix ι ι ℂ) (hb : b * b = 1) :
    NormedSpace.exp ((((Real.pi / 2 : ℝ) : ℂ) * I) • b) = I • b := by
  let φ : (ℂ × ℂ) →ₐ[ℂ] Matrix ι ι ℂ :=
    { toFun := fun z => ((z.1 + z.2) / 2) • 1 + ((z.1 - z.2) / 2) • b
      map_zero' := by simp
      map_one' := by norm_num
      map_add' := by
        rintro ⟨a, d⟩ ⟨e, f⟩
        dsimp
        module
      map_mul' := by
        rintro ⟨a, d⟩ ⟨e, f⟩
        dsimp
        simp only [add_mul, mul_add, smul_mul_smul, one_mul, mul_one, hb]
        module
      commutes' := by
        intro c
        change ((c + c) / 2) • 1 + ((c - c) / 2) • b = algebraMap ℂ _ c
        rw [Algebra.algebraMap_eq_smul_one]
        module }
  let c : ℂ := ((Real.pi / 2 : ℝ) : ℂ) * I
  have he := NormedSpace.map_exp φ φ.toLinearMap.continuous_of_finiteDimensional (c, -c)
  have hi : φ (c, -c) = c • b := by dsimp [φ]; module
  rw [hi] at he
  change NormedSpace.exp (c • b) = I • b
  rw [← he]
  change (((NormedSpace.exp (c, -c)).1 + (NormedSpace.exp (c, -c)).2) / 2) •
    (1 : Matrix ι ι ℂ) +
    (((NormedSpace.exp (c, -c)).1 - (NormedSpace.exp (c, -c)).2) / 2) • b = I • b
  rw [Prod.fst_exp, Prod.snd_exp, ← Complex.exp_eq_exp_ℂ]
  have hp : Complex.exp c = I := by
    dsimp [c]
    rw [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
  have hm : Complex.exp (-c) = -I := by
    dsimp [c]
    rw [Complex.ofReal_div, Complex.ofReal_ofNat]
    convert Complex.exp_neg_pi_div_two_mul_I using 1
    congr 1
    ring
  rw [hp, hm]
  module

private theorem matching_exp {m n : ℕ} (ρ : Equiv.Perm (Fin n))
    (hρ : IsPerfectMatching ρ) :
    NormedSpace.exp ((((Real.pi / 2 : ℝ) : ℂ) * I) •
      Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin m) (Fin m) ℂ) (ρ.permMatrix ℂ)) =
      I • Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin m) (Fin m) ℂ)
        (ρ.permMatrix ℂ) := by
  apply exp_involution
  change Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℂ) (ρ.permMatrix ℂ) *
    Matrix.kronecker 1 (ρ.permMatrix ℂ) = 1
  unfold Matrix.kronecker
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Matrix.permMatrix_mul, hρ.1,
    Matrix.permMatrix_one, Matrix.one_kronecker_one]

private theorem blowup_pow_succ {m n : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) (r : ℕ) :
    (Matrix.kroneckerMap (· * ·) a (Matrix.of fun _ _ : Fin n => (1 : ℂ))) ^ (r + 1) =
      (n : ℂ) ^ r • Matrix.kroneckerMap (· * ·) (a ^ (r + 1))
        (Matrix.of fun _ _ : Fin n => (1 : ℂ)) := by
  let j : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun _ _ => 1
  have hj : j * j = (n : ℂ) • j := by
    ext k l
    change (∑ _ : Fin n, (1 : ℂ) * 1) = (n : ℂ) * 1
    simp
  change (Matrix.kronecker a j) ^ (r + 1) =
    (n : ℂ) ^ r • Matrix.kronecker (a ^ (r + 1)) j
  unfold Matrix.kronecker
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ih, Matrix.smul_mul, ← Matrix.mul_kronecker_mul,
      hj, Matrix.kronecker_smul, smul_smul, ← pow_succ, ← pow_succ]

private theorem blowup_exp_column {m n : ℕ} (a : Matrix (Fin m) (Fin m) ℂ)
    (c : ℂ) (hn : n ≠ 0) (v : Fin m) (k : Fin n) :
    NormedSpace.exp (c • Matrix.kroneckerMap (· * ·) a
      (Matrix.of fun _ _ : Fin n => (1 : ℂ))) *ᵥ Pi.single (v, k) 1 =
      Pi.single (v, k) 1 + fun p => (n : ℂ)⁻¹ *
        ((NormedSpace.exp ((c * n) • a) *ᵥ Pi.single v 1) p.1 -
          (Pi.single v 1 : Fin m → ℂ) p.1) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  ext p
  rw [Matrix.mulVec_single_one]
  change NormedSpace.exp (c • Matrix.kroneckerMap (· * ·) a
    (Matrix.of fun _ _ : Fin n => (1 : ℂ))) p (v, k) = _
  let l : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →L[ℂ] ℂ :=
    { toLinearMap :=
        { toFun := fun b => b p (v, k)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      cont := (continuous_apply (v, k)).comp (continuous_apply p) }
  let q : Matrix (Fin m) (Fin m) ℂ →L[ℂ] ℂ :=
    { toLinearMap :=
        { toFun := fun b => b p.1 v
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      cont := (continuous_apply v).comp (continuous_apply p.1) }
  have hb := l.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ)
    (c • Matrix.kroneckerMap (· * ·) a (Matrix.of fun _ _ : Fin n => (1 : ℂ))))
  have ha := q.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((c * n) • a))
  have hp (r : ℕ) :
      l ((r.factorial : ℂ)⁻¹ • (c • Matrix.kroneckerMap (· * ·) a
        (Matrix.of fun _ _ : Fin n => (1 : ℂ))) ^ r) =
        (n : ℂ)⁻¹ * q ((r.factorial : ℂ)⁻¹ • ((c * n) • a) ^ r) +
          (if r = 0 then (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) p (v, k) -
            (n : ℂ)⁻¹ * (1 : Matrix (Fin m) (Fin m) ℂ) p.1 v else 0) := by
    cases r with
    | zero =>
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
        ite_true]
      change (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) p (v, k) =
        (n : ℂ)⁻¹ * (1 : Matrix (Fin m) (Fin m) ℂ) p.1 v + _
      ring
    | succ r =>
      change ((r + 1).factorial : ℂ)⁻¹ *
        ((c • Matrix.kroneckerMap (· * ·) a
          (Matrix.of fun _ _ : Fin n => (1 : ℂ))) ^ (r + 1)) p (v, k) = _
      rw [smul_pow, blowup_pow_succ, smul_pow]
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply,
        Matrix.of_apply, mul_one, Nat.succ_ne_zero, ite_false, add_zero]
      change _ = (n : ℂ)⁻¹ * (((r + 1).factorial : ℂ)⁻¹ *
        ((c * n) ^ (r + 1) * (a ^ (r + 1)) p.1 v))
      rw [mul_pow, pow_succ (n : ℂ)]
      calc
        _ = ((n : ℂ)⁻¹ * n) * (((r + 1).factorial : ℂ)⁻¹ *
            (c ^ (r + 1) * ((n : ℂ) ^ r * (a ^ (r + 1)) p.1 v))) := by
          rw [inv_mul_cancel₀ hn0, one_mul]
        _ = _ := by ring
  have hs := (ha.mul_left (n : ℂ)⁻¹).add (hasSum_ite_eq 0
    ((1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) p (v, k) -
      (n : ℂ)⁻¹ * (1 : Matrix (Fin m) (Fin m) ℂ) p.1 v))
  have he := (hb.congr_fun (fun r => (hp r).symm)).unique hs
  change NormedSpace.exp (c • Matrix.kroneckerMap (· * ·) a
    (Matrix.of fun _ _ : Fin n => (1 : ℂ))) p (v, k) =
    (n : ℂ)⁻¹ * NormedSpace.exp ((c * n) • a) p.1 v +
      ((1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) p (v, k) -
        (n : ℂ)⁻¹ * (1 : Matrix (Fin m) (Fin m) ℂ) p.1 v) at he
  rw [he, Matrix.mulVec_single_one]
  simp only [Pi.add_apply, Matrix.col_apply]
  have hbig : (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) p (v, k) =
      (Pi.single (v, k) 1 : Fin m × Fin n → ℂ) p := by
    simp [Matrix.one_apply, Pi.single_apply]
  have hsmall : (1 : Matrix (Fin m) (Fin m) ℂ) p.1 v =
      (Pi.single v 1 : Fin m → ℂ) p.1 := by
    simp [Matrix.one_apply, Pi.single_apply]
  rw [hbig, hsmall]
  ring

private theorem matching_column {m n : ℕ} (ρ : Equiv.Perm (Fin n))
    (hρ : IsPerfectMatching ρ) (v : Fin m) (j : Fin n) :
    Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin m) (Fin m) ℂ)
      (ρ.permMatrix ℂ) *ᵥ Pi.single (v, j) 1 = Pi.single (v, ρ j) 1 := by
  have hinv (k : Fin n) : ρ (ρ k) = k :=
    congrArg (fun p : Equiv.Perm (Fin n) => p k) hρ.1
  have hp : ρ.permMatrix ℂ *ᵥ Pi.single j 1 = Pi.single (ρ j) 1 := by
    rw [Matrix.permMatrix_mulVec]
    ext k
    change (Pi.single j 1 : Fin n → ℂ) (ρ k) = (Pi.single (ρ j) 1 : Fin n → ℂ) k
    by_cases hk : k = ρ j
    · subst k
      rw [hinv]
      simp
    · have hkj : ρ k ≠ j := fun h => hk (by rw [← hinv k, h])
      simp [hkj, hk]
  rw [Matrix.mulVec_single_one] at hp ⊢
  ext ⟨w, k⟩
  change (1 : Matrix (Fin m) (Fin m) ℂ) w v * ρ.permMatrix ℂ k j = _
  have hpk := congrFun hp k
  change ρ.permMatrix ℂ k j = _ at hpk
  rw [hpk]
  by_cases hw : w = v
  · subst w
    by_cases hk : k = ρ j <;> simp [hk]
  · simp [Matrix.one_apply_ne hw, hw, Prod.mk.injEq]

private theorem transfer_column {m n : ℕ} (g : SimpleGraph (Fin m))
    [DecidableRel g.Adj] (v : Fin m) (ρ : Equiv.Perm (Fin n))
    (hv : IntegralSupport g v) (hn : 4 ∣ n) (hρ : IsPerfectMatching ρ) (j : Fin n) :
    NormedSpace.exp ((((Real.pi / 2 : ℝ) : ℂ) * I) • blowUpMatching g n ρ) *ᵥ
      Pi.single (v, j) 1 = I • Pi.single (v, ρ j) 1 := by
  have hn0 : n ≠ 0 := by have := j.isLt; omega
  have hfix : NormedSpace.exp ((((Real.pi / 2 : ℝ) : ℂ) * I) •
      Matrix.kroneckerMap (· * ·) (g.adjMatrix ℂ)
        (Matrix.of fun _ _ : Fin n => (1 : ℂ))) *ᵥ Pi.single (v, ρ j) 1 =
      Pi.single (v, ρ j) 1 := by
    rw [blowup_exp_column _ _ hn0, base_periodic g v hv hn]
    ext p
    simp
  unfold blowUpMatching
  rw [smul_add, Matrix.exp_add_of_commute _ _
    ((blowup_commute g ρ).smul_left _ |>.smul_right _), matching_exp ρ hρ,
    ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, matching_column ρ hρ,
    Matrix.mulVec_smul, hfix]

/-- Integral adjacency support and a clone multiplicity divisible by four give adjacency
perfect state transfer across every inserted matching edge in the clone set of `v`. -/
theorem result (m n : ℕ) (g : SimpleGraph (Fin m)) [DecidableRel g.Adj]
    (v : Fin m) (ρ : Equiv.Perm (Fin n)) (hv : IntegralSupport g v)
    (hn : 4 ∣ n) (hρ : IsPerfectMatching ρ) (j : Fin n) :
    HasPST (blowUpMatching g n ρ) (Real.pi / 2) (v, j) (v, ρ j) := by
  have h := congrFun (transfer_column g v ρ hv hn hρ (ρ j)) (v, j)
  have hinv : ρ (ρ j) = j := congrArg (fun p : Equiv.Perm (Fin n) => p j) hρ.1
  rw [hinv] at h
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, Pi.single_eq_same,
    smul_eq_mul, mul_one] at h
  unfold HasPST
  rw [hamiltonianPropagator_neg, h]
  exact Complex.normSq_I

end D5.S3.Quantum.Dynamics.BlowUpMatchingAdjacencyTransfer
