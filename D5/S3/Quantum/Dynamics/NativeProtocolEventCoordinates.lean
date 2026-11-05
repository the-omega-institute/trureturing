/- GID: D5/S3/Quantum/Dynamics/NativeProtocolEventCoordinates
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/NativeProtocolEventCoordinates
   mirror-E: none(waiver:content-registration-pending)
   anchors: []
   utility: none
   digest: Computed native coefficients bound the signed conjugate energy of the complete tree. -/

import D5.S3.Quantum.Dynamics.NativeProtocolGraft

noncomputable section
open scoped BigOperators Matrix
namespace D5.S3.Quantum.Dynamics.NativeProtocolGraft
open Tree

namespace Coeff
open scoped QuadraticAlgebra
private theorem mod_two : (2 : ZMod 2) = 0 := by decide

/-- Integer coordinates in the original inverse-golden basis. -/
abbrev O := QuadraticAlgebra ℤ 1 (-1)
def tau : O := QuadraticAlgebra.omega
/-- The two cyclotomic coordinates, each itself an integer pair. -/
abbrev S := QuadraticAlgebra O (-1) (-tau)
def eta : S := QuadraticAlgebra.omega
def inc : O →+* S := algebraMap O S

theorem t_sq : t ^ 2 = 1 - t := by
  have ht : (phi⁻¹ : ℝ) ^ 2 = 1 - phi⁻¹ := by
    change Real.goldenRatio⁻¹ ^ 2 = 1 - Real.goldenRatio⁻¹
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  unfold t
  exact_mod_cast ht

theorem beta_sq : beta ^ 2 = t := by
  dsimp [beta, t]
  rw [← Complex.ofReal_pow, Real.sq_sqrt]
  exact inv_nonneg.mpr (by dsimp [phi]; positivity)

private theorem zeta_sum : zeta + star zeta = -t := by
  have hcos : 2 * Real.cos (3 * Real.pi / 5) = -phi⁻¹ := by
    rw [show 3 * Real.pi / 5 = Real.pi - 2 * (Real.pi / 5) by ring,
      Real.cos_pi_sub, Real.cos_two_mul, Real.cos_pi_div_five]
    change _ = -Real.goldenRatio⁻¹
    rw [Real.inv_goldenRatio]
    dsimp [Real.goldenConj]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)]
  have hz : zeta.re = Real.cos (3 * Real.pi / 5) := by
    simp [zeta, Complex.exp_re]
  apply Complex.ext
  · simpa [t, hz, two_mul] using hcos
  · simp [t]

theorem zeta_norm : zeta * star zeta = 1 := by
  change zeta * (starRingEnd ℂ) zeta = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp [zeta, Complex.norm_exp]

theorem zeta_sq : zeta ^ 2 = -1 - t * zeta := by
  have h := congrArg (fun x : ℂ => zeta * x) zeta_sum
  rw [mul_add, zeta_norm] at h
  linear_combination h

/-- Evaluation laws follow from the two defining quadratic equations. -/
def evalO {R : Type*} [CommRing R] (u : R) (hu : u ^ 2 = 1 - u) : O →+* R where
  toFun x := (x.re : R) + (x.im : R) * u
  map_zero' := by simp
  map_one' := by
    simp only [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, Int.cast_one,
      Int.cast_zero, zero_mul, add_zero]
  map_add' x y := by
    change (((x+y).re : R) + ((x+y).im : R) * u) = _
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, Int.cast_add]
    ring
  map_mul' x y := by
    change (((x*y).re : R) + ((x*y).im : R) * u) = _
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    push_cast
    linear_combination -(x.im : R) * (y.im : R) * hu

@[simp] theorem evalO_tau {R : Type*} [CommRing R] (u : R) (hu : u ^ 2 = 1 - u) :
    evalO u hu tau = u := by simp [evalO, tau, QuadraticAlgebra.omega]

def evalS (u v : ℂ) (hu : u ^ 2 = 1 - u) (hv : v ^ 2 = -1 - u*v) : S →+* ℂ where
  toFun x := evalO u hu x.re + evalO u hu x.im * v
  map_zero' := by simp
  map_one' := by change evalO u hu 1 + evalO u hu 0 * v = 1; simp
  map_add' x y := by
    change evalO u hu (x+y).re + evalO u hu (x+y).im * v = _
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]
    ring
  map_mul' x y := by
    change evalO u hu (x*y).re + evalO u hu (x*y).im * v = _
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      map_add, map_mul, map_neg, map_one, evalO_tau]
    linear_combination -(evalO u hu x.im) * (evalO u hu y.im) * hv

def physical : S →+* ℂ := evalS t zeta t_sq zeta_sq

@[simp] private theorem evalS_inc (u v : ℂ) (hu hv) (x : O) :
    evalS u v hu hv (inc x) = evalO u hu x := by
  simp [evalS, inc]
@[simp] private theorem evalS_eta (u v : ℂ) (hu hv) :
    evalS u v hu hv eta = v := by simp [evalS, eta, QuadraticAlgebra.omega]

/-- Relative bit parity on the entire sixteen-bit carrier. -/
def parity (b : Basis) : ZMod 2 :=
  (∑ i : Fin 16, if b i then 1 else 0) -
    ∑ i : Fin 16, if rootWord i then 1 else 0

def exponent (b : Basis) : ℕ := if parity b = 0 then 0 else 1

private theorem parity_root : parity rootWord = 0 := by simp [parity]
theorem flip_flip (i : Fin 16) (b : Basis) : flip i (flip i b) = b := by
  funext k
  by_cases hk : k = i
  · subst k; simp [flip]
  · simp [flip, Function.update_of_ne hk, hk]

private theorem parity_flip (i : Fin 16) (b : Basis) :
    parity (flip i b) = parity b + 1 := by
  classical
  have hsplit (f : Fin 16 → ZMod 2) :
      ∑ k, f k = (∑ k ∈ Finset.univ.erase i, f k) + f i :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  unfold parity
  rw [hsplit (fun k => if flip i b k then 1 else 0),
    hsplit (fun k => if b k then 1 else 0)]
  have he : (∑ k ∈ Finset.univ.erase i, if flip i b k then (1:ZMod 2) else 0) =
      ∑ k ∈ Finset.univ.erase i, if b k then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [flip, Function.update_of_ne (Finset.mem_erase.mp hk).1]
  rw [he]
  cases hb : b i <;> simp [flip, hb] <;> ring_nf <;> simp only [mod_two, zero_add]

private theorem exponent_flip (i : Fin 16) (b : Basis) :
    exponent (flip i b) = 1 - exponent b := by
  have hcases : parity b = 0 ∨ parity b = 1 := by
    have hv := (parity b).val_lt
    have hr := ZMod.natCast_zmod_val (parity b)
    interval_cases (parity b).val <;> simp_all
  rcases hcases with h | h <;> norm_num [exponent, parity_flip, h] <;> exact mod_two


private theorem number_action (i : Fin 16) (w : Basis → ℂ) (z : Basis) :
    (number i).mulVec w z = if z i then w z else 0 := by
  classical
  simp [number, Matrix.mulVec_diagonal]

private theorem complement_action (i : Fin 16) (w : Basis → ℂ) (z : Basis) :
    (1 - number i : Mat).mulVec w z = if z i then 0 else w z := by
  rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec, number_action]
  cases z i <;> simp

private theorem flip_action (i : Fin 16) (w : Basis → ℂ) (z : Basis) :
    (bitX i).mulVec w z = w (flip i z) := by
  classical
  have he (b : Basis) : z = flip i b ↔ b = flip i z := by
    constructor
    · intro h; rw [h, flip_flip]
    · intro h; rw [h, flip_flip]
  simp [Matrix.mulVec, dotProduct, bitX, he]

private theorem q_action (j : Address) (w : Basis → ℂ) (z : Basis) :
    (goldenQ j).mulVec w z =
      (if z (center j) then t^2 else t) * w z + beta^3 * w (flip (center j) z) := by
  simp only [goldenQ, Matrix.add_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, number_action, complement_action]
  rw [flip_action]
  cases z (center j) <;> simp

def diagonal (j : Address) (z : Basis) : O :=
  if z (left j) then (if z (right j) then 1 else 0)
  else if z (right j) then 0 else if z (center j) then tau^2 else tau

def active (j : Address) (z : Basis) : Bool := !(z (left j)) && !(z (right j))

def diagStep (j : Address) (z : Basis) : S :=
  eta * (1 + (eta - 1) * inc (diagonal j z))
def offStep (j : Address) (z : Basis) : S :=
  if active j z then inc tau * eta * (eta - 1) else 0

/-- A forward call transports four integer coefficients per basis word. -/
def step (j : Address) (h : Basis → S) (z : Basis) : S :=
  diagStep j z * h z +
    offStep j z * inc (tau ^ (1 - exponent z)) * h (flip (center j) z)

def amplitude (h : Basis → S) (z : Basis) : ℂ :=
  beta ^ exponent z * physical (h z)

theorem p_action (j : Address) (w : Basis → ℂ) (z : Basis) :
    (goldenP j).mulVec w z = evalO t t_sq (diagonal j z) * w z +
      (if active j z then beta^3 * w (flip (center j) z) else 0) := by
  simp only [goldenP, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Pi.add_apply]
  rw [number_action, complement_action]
  cases hl : z (left j) <;> cases hr : z (right j) <;>
    simp [diagonal, active, hl, hr, number_action, complement_action, q_action]
  cases z (center j) <;> simp

private theorem step_physical (j : Address) (h : Basis → S) :
    amplitude (step j h) = (gate j).mulVec (amplitude h) := by
  funext z
  have he : exponent z = 0 ∨ exponent z = 1 := by
    unfold exponent; split_ifs <;> simp
  have hpow := exponent_flip (center j) z
  simp only [gate, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul, p_action]
  unfold amplitude step diagStep offStep physical
  simp only [map_add, map_mul, map_sub, map_one, evalS_eta, evalS_inc, map_pow,
    evalO_tau, map_zero]
  rw [hpow]
  rcases he with he | he <;> rw [he] <;>
    cases ha : active j z <;> simp [ha, beta_sq] <;> ring_nf <;>
    try simp only [show beta^4 = t^2 by rw [show beta^4 = (beta^2)^2 by ring, beta_sq],
      show beta^3 = beta*t by rw [pow_succ, beta_sq]; ring]
  all_goals ring

/-- Complete finite branch transport, with nine steps at inverse syntax. -/
def branch {L : Type} : (T : Tree L) → Path T → (Basis → S) → Basis → S
  | .leaf _, _, h => h
  | .call j d U, p, h => branch U p ((step j)^[callCost d] h)
  | .measure _ select U, p, h =>
      branch (U p.1) p.2 (fun z => if select z = p.1 then h z else 0)

def initial : Basis → S := fun z => if z = rootWord then 1 else 0

private theorem initial_physical : amplitude initial = omega0 := by
  funext z
  by_cases hz : z = rootWord
  · subst z
    simp [amplitude, initial, omega0, exponent, parity_root]
  · simp [amplitude, initial, omega0, hz]

private theorem iterate_physical (j : Address) (n : ℕ) (h : Basis → S) :
    amplitude ((step j)^[n] h) = (gate j ^ n).mulVec (amplitude h) := by
  induction n generalizing h with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, step_physical,
      Matrix.mulVec_mulVec, ← pow_succ]

private theorem branch_physical {L : Type} (T : Tree L) (p : Path T) (h : Basis → S) :
    amplitude (branch T p h) = (operator T p).mulVec (amplitude h) := by
  induction T generalizing h with
  | leaf l => simp [branch, operator]
  | call j d U ih =>
    change amplitude (branch U p ((step j)^[callCost d] h)) =
      (operator U p * callMatrix j d).mulVec (amplitude h)
    rw [ih p, iterate_physical, Matrix.mulVec_mulVec]
    cases d <;> simp [operator, callMatrix, callCost]
  | measure n select U ih =>
    change amplitude (branch (U p.1) p.2 _) =
      (operator (U p.1) p.2 * projector select p.1).mulVec (amplitude h)
    rw [ih p.1 p.2]
    simp only [← Matrix.mulVec_mulVec]
    congr 1
    funext z
    simp [amplitude, projector, Matrix.mulVec_diagonal]
    split_ifs <;> simp


private theorem real_t_sq : (phi⁻¹ : ℝ)^2 = 1 - phi⁻¹ := by
  change Real.goldenRatio⁻¹ ^ 2 = 1 - Real.goldenRatio⁻¹
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

private theorem neg_phi_sq : (-phi)^2 = 1 - (-phi) := by
  change (-Real.goldenRatio)^2 = 1 - (-Real.goldenRatio)
  nlinarith [Real.goldenRatio_sq]

private theorem complex_neg_phi_sq : (-(phi : ℂ))^2 = 1 - (-(phi : ℂ)) := by
  exact_mod_cast neg_phi_sq

def realPhysical : O →+* ℝ := evalO phi⁻¹ real_t_sq
def realConjugate : O →+* ℝ := evalO (-phi) neg_phi_sq

def conjugateZeta : ℂ := Complex.exp ((Real.pi / 5 : ℝ) * Complex.I)
def conjugateBeta : ℂ := (Real.sqrt phi : ℂ) * Complex.I

private theorem conjugateZeta_re : 2 * conjugateZeta.re = phi := by
  simp [conjugateZeta, Complex.exp_re, Real.cos_pi_div_five, phi]
  ring

private theorem conjugateZeta_norm : Complex.normSq conjugateZeta = 1 := by
  rw [Complex.normSq_eq_norm_sq]
  simp [conjugateZeta, Complex.norm_exp]

private theorem conjugateZeta_sq : conjugateZeta^2 = -1 - (-(phi : ℂ))*conjugateZeta := by
  have hs : conjugateZeta + star conjugateZeta = (phi : ℂ) := by
    apply Complex.ext
    · simpa [two_mul] using conjugateZeta_re
    · simp
  have hn : conjugateZeta * star conjugateZeta = 1 := by
    change conjugateZeta * (starRingEnd ℂ) conjugateZeta = 1
    rw [Complex.mul_conj, conjugateZeta_norm]; rfl
  have h := congrArg (fun x : ℂ => conjugateZeta*x) hs
  rw [mul_add, hn] at h
  linear_combination h

private theorem conjugateBeta_sq : conjugateBeta^2 = -(phi : ℂ) := by
  have hp : 0 ≤ phi := by dsimp [phi]; positivity
  simp [conjugateBeta, mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt hp]

private theorem conjugateBeta_norm : Complex.normSq conjugateBeta = phi := by
  have hp : 0 ≤ phi := by dsimp [phi]; positivity
  simp only [conjugateBeta, map_mul, Complex.normSq_I, Complex.normSq_ofReal]
  rw [← pow_two, Real.sq_sqrt hp, mul_one]

def nonphysical : S →+* ℂ :=
  evalS (-(phi : ℂ)) conjugateZeta complex_neg_phi_sq conjugateZeta_sq

def conjugateAmplitude (h : Basis → S) (z : Basis) : ℂ :=
  conjugateBeta ^ exponent z * nonphysical (h z)

private theorem evalO_real (u : ℝ) (hu : u^2 = 1-u) (x : O) :
    evalO (u : ℂ) (by exact_mod_cast hu) x = (evalO u hu x : ℂ) := by
  simp [evalO]

private theorem norm_evaluation (u : ℝ) (v : ℂ) (hu : u^2 = 1-u)
    (hv : v^2 = -1 - (u : ℂ)*v) (hr : 2*v.re = -u)
    (hn : Complex.normSq v = 1) (x : S) :
    evalO u hu (QuadraticAlgebra.norm x) =
      Complex.normSq (evalS (u : ℂ) v (by exact_mod_cast hu) hv x) := by
  simp only [QuadraticAlgebra.norm_def, map_sub, map_add, map_mul, map_neg,
    map_one, evalO_tau]
  change _ = Complex.normSq ((evalO (u : ℂ) _ x.re) +
    (evalO (u : ℂ) _ x.im)*v)
  rw [evalO_real u hu x.re, evalO_real u hu x.im]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    zero_add, add_zero]
  rw [Complex.normSq_apply] at hn
  linear_combination -(evalO u hu x.im)^2 * hn -
    evalO u hu x.re * evalO u hu x.im * hr

/-- Integer coordinates of the raw event, computed from the same branch products. -/
def coordinates {L : Type} (T : Tree L) (event : Path T → Basis → Bool) : O :=
  ∑ p, ∑ z, if event p z then
    tau ^ exponent z * QuadraticAlgebra.norm (branch T p initial z) else 0

private theorem physical_coordinate (h : Basis → S) (z : Basis) :
    realPhysical (tau^exponent z * QuadraticAlgebra.norm (h z)) =
      Complex.normSq (amplitude h z) := by
  have hr : 2*zeta.re = -phi⁻¹ := by
    have hh := congrArg Complex.re zeta_sum
    simpa [t, two_mul] using hh
  have hn : Complex.normSq zeta = 1 := by
    have hh := zeta_norm
    change zeta * (starRingEnd ℂ) zeta = 1 at hh
    rw [Complex.mul_conj] at hh
    exact_mod_cast hh
  have hb : Complex.normSq beta = phi⁻¹ := by
    simp only [beta, Complex.normSq_ofReal]
    rw [← pow_two, Real.sq_sqrt]
    exact inv_nonneg.mpr (by dsimp [phi]; positivity)
  simp only [realPhysical, map_mul, map_pow, evalO_tau, amplitude,
    map_mul, map_pow, hb, physical]
  rw [norm_evaluation phi⁻¹ zeta real_t_sq (by simpa [t] using zeta_sq) hr hn]
  rfl

private theorem conjugate_coordinate (h : Basis → S) (z : Basis) :
    realConjugate (tau^exponent z * QuadraticAlgebra.norm (h z)) =
      (-1 : ℝ)^exponent z * Complex.normSq (conjugateAmplitude h z) := by
  simp only [realConjugate, map_mul, map_pow, evalO_tau, conjugateAmplitude,
    map_mul, map_pow, conjugateBeta_norm, nonphysical]
  rw [norm_evaluation (-phi) conjugateZeta neg_phi_sq
    (by simpa using conjugateZeta_sq) (by simpa using conjugateZeta_re) conjugateZeta_norm]
  by_cases he : exponent z = 0
  · simp [he]
  · have he' : exponent z = 1 := by simpa [exponent] using he
    simp [he', mul_assoc]

private theorem coordinates_physical {L : Type} (T : Tree L)
    (event : Path T → Basis → Bool) :
    realPhysical (coordinates T event) = eventMass T event := by
  classical
  simp only [coordinates, map_sum, eventMass]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro z _
  split_ifs with h
  · rw [physical_coordinate, branch_physical, initial_physical]
    rfl
  · exact map_zero _

private theorem coordinates_conjugate {L : Type} (T : Tree L)
    (event : Path T → Basis → Bool) :
    realConjugate (coordinates T event) = ∑ p, ∑ z, if event p z then
      (-1 : ℝ)^exponent z * Complex.normSq (conjugateAmplitude (branch T p initial) z)
      else 0 := by
  classical
  simp only [coordinates, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro z _
  split_ifs
  · exact conjugate_coordinate _ _
  · exact map_zero _


/-- The actual embedded projection row, derived from the same coefficient transport. -/
def conjugateP (j : Address) (w : Basis → ℂ) (z : Basis) : ℂ :=
  (realConjugate (diagonal j z) : ℂ) * w z +
    if active j z then conjugateBeta^3 * w (flip (center j) z) else 0

private theorem conjugate_step (j : Address) (h : Basis → S) (z : Basis) :
    conjugateAmplitude (step j h) z = conjugateZeta *
      (conjugateAmplitude h z + (conjugateZeta - 1) *
        conjugateP j (conjugateAmplitude h) z) := by
  have he : exponent z = 0 ∨ exponent z = 1 := by
    unfold exponent; split_ifs <;> simp
  have hpow := exponent_flip (center j) z
  unfold conjugateAmplitude step diagStep offStep nonphysical conjugateP
  simp only [map_add, map_mul, map_sub, map_one, evalS_eta, evalS_inc, map_pow,
    evalO_tau]
  rw [hpow]
  have hd : evalO (-(phi : ℂ)) complex_neg_phi_sq (diagonal j z) =
      (realConjugate (diagonal j z) : ℂ) := by
    simpa [realConjugate] using evalO_real (-phi) neg_phi_sq (diagonal j z)
  rw [hd]
  rcases he with he | he <;> rw [he] <;>
    cases ha : active j z <;> simp [ha] <;> ring_nf <;>
    try simp only [show conjugateBeta^4 = (-(phi : ℂ))^2 by
      rw [show conjugateBeta^4 = (conjugateBeta^2)^2 by ring, conjugateBeta_sq],
      show conjugateBeta^3 = conjugateBeta * (-(phi : ℂ)) by
        rw [pow_succ, conjugateBeta_sq]; ring]
  all_goals ring

def energy (w : Basis → ℂ) : ℝ := ∑ z, Complex.normSq (w z)
def l2 (w : Basis → ℂ) : EuclideanSpace ℂ Basis := WithLp.toLp 2 w

private theorem energy_nonneg (w : Basis → ℂ) : 0 ≤ energy w :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

private theorem energy_norm (w : Basis → ℂ) : energy w = ‖l2 w‖^2 := by
  simp [energy, l2, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]

private theorem cauchy_two (a b x y : ℂ) :
    Complex.normSq (a*x+b*y) ≤
      (Complex.normSq a+Complex.normSq b)*(Complex.normSq x+Complex.normSq y) := by
  have h := norm_add_le (a*x) (b*y)
  rw [norm_mul, norm_mul] at h
  have hs := sq_nonneg (‖a‖*‖y‖ - ‖b‖*‖x‖)
  simp only [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (a*x+b*y), norm_nonneg a, norm_nonneg b,
    norm_nonneg x, norm_nonneg y]

theorem flip_sum (i : Fin 16) (f : Basis → ℝ) :
    ∑ z, f (flip i z) = ∑ z, f z := by
  let e : Basis ≃ Basis := ⟨flip i, flip i, flip_flip i, flip_flip i⟩
  exact e.sum_comp f

theorem phi_positive : 0 < phi := by dsimp [phi]; positivity
private theorem phi_cubic : phi^3 = phi + phi^2 := by
  have h : phi^2 = phi+1 := Real.goldenRatio_sq
  nlinarith

theorem active_flip (j : Address) (z : Basis) :
    active j (flip (center j) z) = active j z := by
  have hl : left j ≠ center j := by
    intro h; have hh := congrArg Fin.val h; simp [left, center] at hh
  have hr : right j ≠ center j := by
    intro h; have hh := congrArg Fin.val h; simp [right, center] at hh
  simp [active, flip, Function.update_of_ne hl, Function.update_of_ne hr, hl, hr]

/-- Squared row weight on a nonphysical active two-dimensional block. -/
def rowWeight (j : Address) (z : Basis) : ℝ :=
  if z (center j) then phi^2 else phi

private theorem rowWeight_pair (j : Address) (z : Basis) :
    rowWeight j z + rowWeight j (flip (center j) z) = phi^3 := by
  cases hc : z (center j) <;> simp [rowWeight, flip, hc, phi_cubic] <;> ring

private theorem active_row_bound (j : Address) (w : Basis → ℂ) (z : Basis)
    (ha : active j z = true) :
    Complex.normSq (conjugateP j w z) ≤
      phi^3 * rowWeight j z *
        (Complex.normSq (w z) + Complex.normSq (w (flip (center j) z))) := by
  have hd : realConjugate (diagonal j z) =
      if z (center j) then phi^2 else -phi := by
    unfold active at ha
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha
    cases hz : z (center j) <;> simp [diagonal, ha.1, ha.2, realConjugate, hz]
  have hc := cauchy_two (realConjugate (diagonal j z) : ℂ)
    (conjugateBeta^3) (w z) (w (flip (center j) z))
  simp only [conjugateP, ha, if_true]
  refine le_trans hc ?_
  apply mul_le_mul_of_nonneg_right _ (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
  rw [hd]
  simp only [map_pow, conjugateBeta_norm, Complex.normSq_ofReal]
  have hp : phi^2 = phi+1 := Real.goldenRatio_sq
  apply le_of_eq
  cases hz : z (center j) <;> simp only [rowWeight, hz, Bool.false_eq_true,
    ite_false, ite_true, neg_mul_neg, neg_pow, even_two, Even.neg_pow]
  · linear_combination -phi^2 * hp
  · linear_combination -phi^3 * hp

private theorem projection_energy (j : Address) (w : Basis → ℂ) :
    energy (conjugateP j w) ≤ (phi^3)^2 * energy w := by
  classical
  let a : Basis → ℝ := fun z => if active j z then Complex.normSq (w z) else 0
  let b : Basis → ℝ := fun z =>
    if z (left j) && z (right j) then Complex.normSq (w z) else 0
  have hpoint (z : Basis) : Complex.normSq (conjugateP j w z) ≤
      phi^3 * rowWeight j z * (a z + a (flip (center j) z)) + b z := by
    by_cases ha : active j z = true
    · have hh : z (left j) = false ∧ z (right j) = false := by
        simpa [active] using ha
      have hb : b z = 0 := by simp [b, hh.1, hh.2]
      simpa only [a, ha, active_flip, ite_true, hb, add_zero] using
        active_row_bound j w z ha
    · have hzero : active j z = false := Bool.eq_false_iff.mpr ha
      simp only [a, active_flip, hzero, ite_false, add_zero, zero_add, mul_zero]
      cases hl : z (left j) <;> cases hr : z (right j) <;>
        simp [active, hl, hr] at ha
      all_goals simp [b, conjugateP, hzero, diagonal, realConjugate, hl, hr]
  have hreindex :
      (∑ z, rowWeight j z * a (flip (center j) z)) =
        ∑ z, rowWeight j (flip (center j) z) * a z := by
    simpa only [flip_flip] using
      flip_sum (center j) (fun z => rowWeight j (flip (center j) z) * a z)
  have hsum : (∑ z, rowWeight j z * (a z + a (flip (center j) z))) =
      phi^3 * ∑ z, a z := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, hreindex, ← Finset.sum_add_distrib]
    simp_rw [← add_mul, rowWeight_pair]
    rw [Finset.mul_sum]
  have htotal := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset Basis)) => hpoint z)
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at htotal
  rw [hsum] at htotal
  refine le_trans htotal ?_
  rw [← mul_assoc, ← pow_two]
  have hphi : 1 ≤ (phi^3)^2 := by
    have hp : 1 ≤ phi := by
      change 1 ≤ Real.goldenRatio
      exact Real.one_lt_goldenRatio.le
    exact one_le_pow₀ (one_le_pow₀ hp)
  have hbn : 0 ≤ ∑ z, b z := by
    apply Finset.sum_nonneg
    intro z _; dsimp [b]; split_ifs
    · exact Complex.normSq_nonneg _
    · norm_num
  have hmass : (∑ z, a z) + (∑ z, b z) ≤ energy w := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z _
    cases hl : z (left j) <;> cases hr : z (right j) <;>
      simp [a, b, active, hl, hr, Complex.normSq_nonneg]
  nlinarith [mul_le_mul_of_nonneg_left hmass (sq_nonneg (phi^3)),
    mul_le_mul_of_nonneg_right hphi hbn]


def kappa : ℝ := 1 + 2*phi^3

theorem kappa_one : 1 ≤ kappa := by
  have hp := pow_nonneg phi_positive.le 3
  dsimp [kappa]
  linarith

private theorem step_energy (j : Address) (h : Basis → S) :
    energy (conjugateAmplitude (step j h)) ≤
      kappa^2 * energy (conjugateAmplitude h) := by
  let w := conjugateAmplitude h
  have hp : ‖l2 (conjugateP j w)‖ ≤ phi^3 * ‖l2 w‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (pow_nonneg phi_positive.le _) (norm_nonneg _))).mp
    have hb := projection_energy j w
    rw [energy_norm, energy_norm] at hb
    nlinarith [hb]
  have hv : l2 (conjugateAmplitude (step j h)) =
      conjugateZeta • (l2 w + (conjugateZeta-1) • l2 (conjugateP j w)) := by
    ext z
    exact conjugate_step j h z
  have hz : ‖conjugateZeta‖ = 1 := by
    have hn := conjugateZeta_norm
    rw [Complex.normSq_eq_norm_sq] at hn
    nlinarith [norm_nonneg conjugateZeta]
  have hd : ‖conjugateZeta-1‖ ≤ 2 := by
    have hn := norm_sub_le conjugateZeta (1 : ℂ)
    norm_num only [hz, norm_one] at hn
    exact hn
  have htri := norm_add_le (l2 w) ((conjugateZeta-1) • l2 (conjugateP j w))
  rw [norm_smul] at htri
  have hm := mul_le_mul hd hp (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  have hnorm : ‖l2 (conjugateAmplitude (step j h))‖ ≤ kappa * ‖l2 w‖ := by
    rw [hv, norm_smul, hz, one_mul]
    dsimp [kappa]
    nlinarith [hm]
  rw [energy_norm, energy_norm]
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (le_trans zero_le_one kappa_one) (norm_nonneg _))).mpr hnorm
  simpa [mul_pow] using hs

private theorem iterate_energy (j : Address) (n : ℕ) (h : Basis → S) :
    energy (conjugateAmplitude ((step j)^[n] h)) ≤
      kappa^(2*n) * energy (conjugateAmplitude h) := by
  induction n generalizing h with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have h1 := ih (step j h)
    have h2 := mul_le_mul_of_nonneg_left (step_energy j h)
      (pow_nonneg (le_trans zero_le_one kappa_one) (2*n))
    refine le_trans h1 (le_trans h2 (le_of_eq ?_))
    rw [← mul_assoc, ← pow_add]
    congr 2 <;> omega

def masked {n : ℕ} (select : Basis → Fin n) (o : Fin n) (h : Basis → S) : Basis → S :=
  fun z => if select z = o then h z else 0

private theorem measurement_energy {n : ℕ} (select : Basis → Fin n) (h : Basis → S) :
    (∑ o, energy (conjugateAmplitude (masked select o h))) =
      energy (conjugateAmplitude h) := by
  classical
  unfold energy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp [masked, conjugateAmplitude, apply_ite]

private theorem call_max {L : Type} (j : Address) (d : Direction) (U : Tree L) :
    callCost d + maxCalls U ≤ maxCalls (.call j d U) := by
  classical
  obtain ⟨p,_,hp⟩ := Finset.exists_mem_eq_sup Finset.univ
    (Finset.univ_nonempty : (Finset.univ : Finset (Path U)).Nonempty) (calls U)
  change callCost d + (Finset.univ.sup (calls U)) ≤ _
  rw [hp]
  exact Finset.le_sup (f := calls (.call j d U)) (Finset.mem_univ p)

private theorem measure_max {L : Type} {n : ℕ} (select : Basis → Fin n)
    (U : Fin n → Tree L) (o : Fin n) :
    maxCalls (U o) ≤ maxCalls (.measure n select U) := by
  classical
  apply Finset.sup_le
  intro p _
  exact Finset.le_sup (f := calls (.measure n select U)) (Finset.mem_univ (⟨o,p⟩))

/-- Sum over all syntactic paths, without pruning unused outcomes. -/
def treeEnergy {L : Type} (T : Tree L) (h : Basis → S) : ℝ :=
  ∑ p : Path T, energy (conjugateAmplitude (branch T p h))

private theorem whole_tree_energy {L : Type} (T : Tree L) (h : Basis → S) :
    treeEnergy T h ≤ kappa^(2*maxCalls T) * energy (conjugateAmplitude h) := by
  classical
  induction T generalizing h with
  | leaf l =>
    change (∑ _p : Unit, energy (conjugateAmplitude h)) ≤
      kappa^(2 * ((Finset.univ : Finset Unit).sup (fun _ => 0))) *
        energy (conjugateAmplitude h)
    simp
  | call j d U ih =>
    change treeEnergy U ((step j)^[callCost d] h) ≤ _
    have h1 := ih ((step j)^[callCost d] h)
    have h2 := mul_le_mul_of_nonneg_left (iterate_energy j (callCost d) h)
      (pow_nonneg (le_trans zero_le_one kappa_one) (2*maxCalls U))
    refine le_trans h1 (le_trans h2 ?_)
    rw [← mul_assoc, ← pow_add]
    apply mul_le_mul_of_nonneg_right _ (energy_nonneg _)
    apply pow_le_pow_right₀ kappa_one
    have hm := call_max j d U
    omega
  | measure n select U ih =>
    change (∑ p : (o : Fin n) × Path (U o),
      energy (conjugateAmplitude (branch (U p.1) p.2 (masked select p.1 h)))) ≤ _
    rw [Fintype.sum_sigma]
    calc
      _ ≤ ∑ o, kappa^(2*maxCalls (U o)) *
          energy (conjugateAmplitude (masked select o h)) :=
        Finset.sum_le_sum (fun o _ => ih o (masked select o h))
      _ ≤ ∑ o, kappa^(2*maxCalls (.measure n select U)) *
          energy (conjugateAmplitude (masked select o h)) := by
        apply Finset.sum_le_sum
        intro o _
        apply mul_le_mul_of_nonneg_right _ (energy_nonneg _)
        exact pow_le_pow_right₀ kappa_one (Nat.mul_le_mul_left 2 (measure_max select U o))
      _ = _ := by rw [← Finset.mul_sum, measurement_energy]

private theorem initial_energy : energy (conjugateAmplitude initial) = 1 := by
  classical
  simp [energy, conjugateAmplitude, initial, exponent, parity_root, apply_ite]

private theorem event_conjugate_bound {L : Type} (T : Tree L)
    (event : Path T → Basis → Bool) :
    |realConjugate (coordinates T event)| ≤ kappa^(2*maxCalls T) := by
  rw [coordinates_conjugate]
  calc
    _ ≤ ∑ p : Path T, ∑ z : Basis, |if event p z then
        (-1 : ℝ)^exponent z * Complex.normSq (conjugateAmplitude (branch T p initial) z)
        else 0| := le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum
          (fun p _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ treeEnergy T initial := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro z _
      split_ifs <;> simp [abs_mul, abs_pow, abs_of_nonneg (Complex.normSq_nonneg _),
        Complex.normSq_nonneg]
    _ ≤ _ := by simpa [initial_energy] using whole_tree_energy T initial



end Coeff

/-- Recursively computed integer coordinates of the actual original event,
its parity-signed nonphysical evaluation and its whole-tree resource bound. -/
theorem original_event_coordinates_and_bound {L : Type} (T : Tree L)
    (event : Path T → Basis → Bool) :
    eventMass T event = Coeff.realPhysical (Coeff.coordinates T event) ∧
    Coeff.realConjugate (Coeff.coordinates T event) =
      (∑ p, ∑ z, if event p z then (-1 : ℝ)^Coeff.exponent z *
        Complex.normSq (Coeff.conjugateAmplitude (Coeff.branch T p Coeff.initial) z)
        else 0) ∧
    |Coeff.realConjugate (Coeff.coordinates T event)| ≤
      Coeff.kappa^(2*maxCalls T) :=
  ⟨(Coeff.coordinates_physical T event).symm, Coeff.coordinates_conjugate T event,
    Coeff.event_conjugate_bound T event⟩

#print axioms original_event_coordinates_and_bound

end D5.S3.Quantum.Dynamics.NativeProtocolGraft
