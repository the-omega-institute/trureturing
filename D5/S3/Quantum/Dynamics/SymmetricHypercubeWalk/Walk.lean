/- GID: D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Walk
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Walk
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The origin-started continuous and complex coined walks in Walsh coordinates. -/

import D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.CoinAverages
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-! Real Walsh characters and their normalized position vectors. -/

section

open Filter
open scoped BigOperators Matrix Topology

set_option autoImplicit false

namespace HypercubeWalsh

abbrev Cube (d : ℕ) := Fin d → Bool

def origin {d : ℕ} : Cube d := fun _ => false

def xor {d : ℕ} (a b : Cube d) : Cube d := fun i => a i ^^ b i

private theorem xor_comm {d : ℕ} (a b : Cube d) : xor a b = xor b a := by
  ext i
  exact Bool.xor_comm _ _

@[simp] private theorem xor_origin {d : ℕ} (a : Cube d) : xor a origin = a := by
  ext i
  change (a i ^^ false) = a i
  cases a i <;> rfl

@[simp] private theorem origin_xor {d : ℕ} (a : Cube d) : xor origin a = a := by
  rw [xor_comm, xor_origin]

@[simp] private theorem xor_self {d : ℕ} (a : Cube d) : xor a a = origin := by
  ext i
  change (a i ^^ a i) = false
  cases a i <;> rfl

@[simp] private theorem xor_xor_cancel {d : ℕ} (a b : Cube d) : xor (xor a b) b = a := by
  ext i
  change ((a i ^^ b i) ^^ b i) = a i
  cases a i <;> cases b i <;> rfl

def xorEquiv {d : ℕ} (b : Cube d) : Cube d ≃ Cube d where
  toFun a := xor a b
  invFun a := xor a b
  left_inv a := xor_xor_cancel a b
  right_inv a := xor_xor_cancel a b

private theorem xor_eq_origin_iff {d : ℕ} (a b : Cube d) : xor a b = origin ↔ a = b := by
  constructor
  · intro h
    have hh := congrArg (fun x => xor x b) h
    simpa using hh
  · rintro rfl
    exact xor_self a

def character {d : ℕ} (a x : Cube d) : ℝ :=
  ∏ i, sign (a i && x i)

theorem character_comm {d : ℕ} (a x : Cube d) : character a x = character x a := by
  simp only [character, Bool.and_comm]

@[simp] private theorem character_origin {d : ℕ} (a : Cube d) : character a origin = 1 := by
  simp [character, origin]

@[simp] private theorem origin_character {d : ℕ} (a : Cube d) : character origin a = 1 := by
  rw [character_comm, character_origin]

private theorem character_mul {d : ℕ} (a b x : Cube d) :
    character (xor a b) x = character a x * character b x := by
  rw [character, character, character, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  unfold xor
  cases a i <;> cases b i <;> cases x i <;> norm_num

private theorem character_xor {d : ℕ} (a x y : Cube d) :
    character a (xor x y) = character a x * character a y := by
  rw [character_comm, character_mul, character_comm x, character_comm y]

@[simp] private theorem character_sq {d : ℕ} (a x : Cube d) : character a x ^ 2 = 1 := by
  rw [pow_two, ← character_mul, xor_self, origin_character]

noncomputable def characterBit {d : ℕ} (a x : Cube d) : Bool :=
  if character a x = -1 then true else false

@[simp] private theorem sign_characterBit {d : ℕ} (a x : Cube d) :
    sign (characterBit a x) = character a x := by
  rcases sq_eq_one_iff.mp (character_sq a x) with h | h <;> norm_num [characterBit, h]

private theorem sign_injective : Function.Injective sign := by
  intro x y
  cases x <;> cases y <;> norm_num

theorem characterBit_xor {d : ℕ} (a b : Cube d) :
    characterBit (xor a b) = fun x => characterBit a x ^^ characterBit b x := by
  funext x
  apply sign_injective
  rw [sign_characterBit, sign_mul, sign_characterBit, sign_characterBit, character_mul]

theorem cube_card (d : ℕ) : Fintype.card (Cube d) = 2 ^ d := by simp [Cube]

private theorem character_sum {d : ℕ} (a : Cube d) :
    ∑ x, character a x = if a = origin then (2 : ℝ) ^ d else 0 := by
  by_cases ha : a = origin
  · subst a
    simp
  · have hex : ∃ i, a i = true := by
      by_contra! h
      apply ha
      ext i
      cases hi : a i with
      | false => rfl
      | true => exact (h i hi).elim
    obtain ⟨i, hi⟩ := hex
    let e : Cube d := fun j => decide (j = i)
    have he : character a e = -1 := by
      rw [character, Fintype.prod_eq_single i]
      · simp [hi, e]
      · intro j hj
        simp [e, hj]
    have hshift : (∑ x, character a (xor x e)) = ∑ x, character a x :=
      Equiv.sum_comp (xorEquiv e) _
    rw [ite_eq_right ha]
    simp only [character_xor, he, mul_neg_one, Finset.sum_neg_distrib] at hshift
    linarith

private theorem character_orthogonal {d : ℕ} (a b : Cube d) :
    ∑ x, character a x * character b x = if a = b then (2 : ℝ) ^ d else 0 := by
  simp only [← character_mul, character_sum, xor_eq_origin_iff]

noncomputable def scale (d : ℕ) : ℝ := (Real.sqrt ((2 : ℝ) ^ d))⁻¹

theorem scale_sq (d : ℕ) : scale d ^ 2 = ((2 : ℝ) ^ d)⁻¹ := by
  rw [scale, inv_pow, Real.sq_sqrt (by positivity)]

noncomputable def basis {d : ℕ} (a x : Cube d) : ℝ := scale d * character a x

private theorem basis_comm {d : ℕ} (a x : Cube d) : basis a x = basis x a := by
  rw [basis, basis, character_comm]

@[simp] private theorem basis_origin {d : ℕ} (a : Cube d) : basis a origin = scale d := by
  simp [basis]

theorem basis_orthonormal {d : ℕ} (a b : Cube d) :
    ∑ x, basis a x * basis b x = if a = b then 1 else 0 := by
  calc
    _ = scale d ^ 2 * ∑ x, character a x * character b x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      unfold basis
      ring
    _ = _ := by
      rw [character_orthogonal, scale_sq]
      by_cases h : a = b <;> simp [h]

private theorem basis_delta {d : ℕ} (x : Cube d) :
    (scale d * ∑ a, basis a x) = if x = origin then 1 else 0 := by
  rw [Finset.mul_sum]
  calc
    _ = ∑ a, basis origin a * basis x a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [basis_comm origin a, basis_origin, basis_comm x a]
    _ = _ := by simp [basis_orthonormal, eq_comm]

theorem basis_character_mul {d : ℕ} (a c x : Cube d) :
    basis a x * character c x = basis (xor a c) x := by
  rw [basis, basis, character_mul, mul_assoc]

private theorem basis_translate {d : ℕ} (a x y : Cube d) :
    basis a (xor x y) = basis a x * character a y := by
  rw [basis, basis, character_xor, mul_assoc]

variable {d : ℕ} (K : Kernel (Cube d))

noncomputable def eigen (a : Cube d) : ℝ := K.eigenvalue (characterBit a)

theorem eigen_eq (a : Cube d) : eigen K a = ∑ y, K.p y * character a y := by
  simp [eigen, Kernel.eigenvalue]

noncomputable def gap (a c : Cube d) : ℝ :=
  if eigen K a = eigen K (xor a c) ∧ |eigen K a| < 1 then
    (1 - eigen K c) / (2 * (1 - eigen K a ^ 2))
  else 0

theorem pairGap_eq (a c : Cube d) :
    K.pairGap (characterBit a) (characterBit (xor a c)) = gap K a c := by
  have hx : xor a (xor a c) = c := by rw [xor_comm a, xor_comm a c, xor_xor_cancel]
  unfold gap Kernel.pairGap
  rw [← characterBit_xor, hx]
  rfl

end HypercubeWalsh

end

section

/-! Coordinate models of the two walks with initial position at the origin. -/

open scoped BigOperators Matrix

set_option autoImplicit false

namespace HypercubeWalsh

variable {d : ℕ} (K : Kernel (Cube d))

noncomputable def walshMatrix (d : ℕ) : Matrix (Cube d) (Cube d) ℂ :=
  fun x a => (basis a x : ℂ)

private theorem walshMatrix_sq (d : ℕ) : walshMatrix d * walshMatrix d = 1 := by
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply]
  change (∑ a, (basis a x : ℂ) * (basis y a : ℂ)) = _
  simp_rw [basis_comm _ x]
  simp_rw [← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum, basis_orthonormal]
  split <;> simp

noncomputable def transition : Matrix (Cube d) (Cube d) ℂ :=
  fun x z => (K.p (xor x z) : ℂ)

private theorem transition_mul_walshMatrix :
    transition K * walshMatrix d = walshMatrix d * Matrix.diagonal (fun a => (eigen K a : ℂ)) := by
  ext x a
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  change (∑ z, (K.p (xor x z) : ℂ) * (basis a z : ℂ)) = (basis a x : ℂ) * (eigen K a : ℂ)
  rw [← Equiv.sum_comp (xorEquiv x)]
  change (∑ z, (K.p (xor x (xor z x)) : ℂ) * (basis a (xor z x) : ℂ)) = _
  have hx (z : Cube d) : xor x (xor z x) = z := by rw [xor_comm x, xor_xor_cancel]
  simp only [hx, basis_translate, Complex.ofReal_mul, eigen_eq, Complex.ofReal_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  simp only [basis, Complex.ofReal_mul]
  ring

noncomputable def generator (t : ℝ) : Matrix (Cube d) (Cube d) ℂ :=
  ((-Complex.I) * (t : ℂ)) • (1 - transition K)

noncomputable def continuousState (t : ℝ) (x : Cube d) : ℂ :=
  NormedSpace.exp (generator K t) x origin

private theorem generator_diagonalization (t : ℝ) :
    generator K t = walshMatrix d *
      Matrix.diagonal (fun a => ((((eigen K a - 1) * t : ℝ) : ℂ) * Complex.I)) *
      walshMatrix d := by
  have h : generator K t * walshMatrix d =
      walshMatrix d * Matrix.diagonal (fun a => ((((eigen K a - 1) * t : ℝ) : ℂ) * Complex.I)) := by
    rw [generator, Matrix.smul_mul, sub_mul, one_mul, transition_mul_walshMatrix]
    ext x a
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_diagonal, smul_eq_mul,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [← h, Matrix.mul_assoc, walshMatrix_sq, mul_one]

theorem continuousState_fourier (t : ℝ) (x : Cube d) :
    continuousState K t x =
      (scale d : ℂ) * ∑ a, (basis a x : ℂ) * continuousBlock (eigen K a) t := by
  let W : Matrix (Cube d) (Cube d) ℂ := walshMatrix d
  let U : (Matrix (Cube d) (Cube d) ℂ)ˣ := ⟨W, W, walshMatrix_sq d, walshMatrix_sq d⟩
  have hi : W⁻¹ = W := Matrix.inv_eq_left_inv (walshMatrix_sq d)
  have hu : IsUnit W := ⟨U, rfl⟩
  unfold continuousState
  rw [generator_diagonalization]
  have hex := Matrix.exp_conj W
    (Matrix.diagonal (fun a => ((((eigen K a - 1) * t : ℝ) : ℂ) * Complex.I))) hu
  rw [hi] at hex
  change (NormedSpace.exp (W * Matrix.diagonal _ * W) : Matrix (Cube d) (Cube d) ℂ) x origin = _
  rw [hex, Matrix.exp_diagonal, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Pi.coe_exp]
  change (∑ a, (basis a x : ℂ) *
    NormedSpace.exp ((((eigen K a - 1) * t : ℝ) : ℂ) * Complex.I) * (basis origin a : ℂ)) = _
  simp only [← Complex.exp_eq_exp_ℂ]
  change (∑ a, (basis a x : ℂ) * continuousBlock (eigen K a) t * (basis origin a : ℂ)) = _
  simp only [basis_comm origin, basis_origin, ← Finset.sum_mul]
  exact mul_comm _ _

noncomputable def discreteInitial (y x : Cube d) : ℝ :=
  if x = origin then K.coin y else 0

noncomputable def discreteStep : (Cube d → Cube d → ℝ) →ₗ[ℝ] (Cube d → Cube d → ℝ) where
  toFun ψ y x := K.reflection (fun z => ψ z (xor x y)) y
  map_add' ψ φ := by
    ext y x
    simp only [Kernel.reflection, Pi.add_apply, ← Pi.add_def, dotProduct_add]
    ring
  map_smul' r ψ := by
    ext y x
    change K.reflection (fun z => (r • ψ) z (xor x y)) y =
      r * K.reflection (fun z => ψ z (xor x y)) y
    have hs : (fun z => (r • ψ) z (xor x y)) = r • (fun z => ψ z (xor x y)) := rfl
    rw [hs]
    simp only [Kernel.reflection, dotProduct_smul, Pi.smul_apply, smul_eq_mul]
    ring

noncomputable def discreteState (n : ℕ) : Cube d → Cube d → ℝ :=
  (discreteStep K)^[n] (discreteInitial K)

private theorem discreteStep_fourier (a : Cube d) (f : Cube d → ℝ) :
    discreteStep K (fun y x => basis a x * f y) =
      fun y x => basis a x * K.step (characterBit a) f y := by
  ext y x
  change 2 * (K.coin ⬝ᵥ (fun z => basis a (xor x y) * f z)) * K.coin y -
      basis a (xor x y) * f y = basis a x * K.step (characterBit a) f y
  change 2 * (K.coin ⬝ᵥ (basis a (xor x y) • f)) * K.coin y -
      basis a (xor x y) * f y = _
  simp only [dotProduct_smul, smul_eq_mul, Kernel.step, Kernel.reflection,
    basis_translate, sign_characterBit]
  ring

theorem discreteState_fourier (n : ℕ) (y x : Cube d) :
    discreteState K n y x =
      scale d * ∑ a, basis a x * K.orbit (characterBit a) n y := by
  induction n generalizing y x with
  | zero =>
    simp only [discreteState, Kernel.orbit, Function.iterate_zero, id_eq]
    rw [← Finset.sum_mul, ← mul_assoc, basis_delta]
    by_cases h : x = origin <;> simp [discreteInitial, h]
  | succ n ih =>
    have hs : discreteState K n =
        scale d • ∑ a, (fun z w => basis a w * K.orbit (characterBit a) n z) := by
      ext z w
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact ih z w
    rw [discreteState, Function.iterate_succ_apply', ← discreteState, hs, map_smul, map_sum]
    simp only [discreteStep_fourier, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Kernel.orbit, Function.iterate_succ_apply']

/-- Coin matrix of §4.2, before the position shift. -/
noncomputable def coinEntry (y z : Cube d) : ℝ :=
  2 * Real.sqrt (K.p y * K.p z) - if y = z then 1 else 0

private theorem discreteStep_entry (ψ : Cube d → Cube d → ℝ) (y x : Cube d) :
    discreteStep K ψ y x = ∑ z, coinEntry K y z * ψ z (xor x y) := by
  change 2 * (K.coin ⬝ᵥ fun z => ψ z (xor x y)) * K.coin y - ψ y (xor x y) = _
  unfold coinEntry
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  simp only [dotProduct, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Real.sqrt_mul (K.nonneg y)]
  unfold Kernel.coin
  ring

/-- Complex position/coin evolution with the shift applied after the coin. -/
noncomputable def discreteComplexStep (ψ : Cube d → Cube d → ℂ) (y x : Cube d) : ℂ :=
  ∑ z, (coinEntry K y z : ℂ) * ψ z (xor x y)

noncomputable def discreteComplexInitial (y x : Cube d) : ℂ :=
  if x = origin then (K.coin y : ℂ) else 0

noncomputable def discreteComplexState (n : ℕ) : Cube d → Cube d → ℂ :=
  (discreteComplexStep K)^[n] (discreteComplexInitial K)

theorem discreteComplexState_eq_ofReal (n : ℕ) (y x : Cube d) :
    discreteComplexState K n y x = (discreteState K n y x : ℂ) := by
  induction n generalizing y x with
  | zero =>
    simp only [discreteComplexState, discreteState, Function.iterate_zero, id_eq]
    unfold discreteComplexInitial discreteInitial
    split <;> simp
  | succ n ih =>
    rw [discreteComplexState, Function.iterate_succ_apply', ← discreteComplexState,
      discreteState, Function.iterate_succ_apply', ← discreteState, discreteComplexStep,
      discreteStep_entry]
    simp only [ih, Complex.ofReal_sum, Complex.ofReal_mul]

end HypercubeWalsh

end
