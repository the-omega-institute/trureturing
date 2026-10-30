/- GID: D5/S3/Quantum/Tomography/PauliFisherGHZRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Tomography/PauliFisherGHZRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.claim; result=D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.result; claim=D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.claim
   digest: GHZ phase tangents refute a uniform lower bound for mean Pauli Fisher information. -/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
The GHZ phase family refutes the uniform Pauli Fisher lower bound in
Acharya–Kypraios–Guţă, arXiv:1510.03229v2, under the tangent formulation
preregistered in https://github.com/the-omega-institute/trureturing/issues/24270.
Settings use 0, 1, 2 for x, y, z; outcomes use 0, 1 for +, −.
-/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Tomography.PauliFisherGHZRefutation

open scoped BigOperators Matrix.Norms.Elementwise ComplexOrder
open Matrix

def IsDensity {n : ℕ} (ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

def pauliEigen (s : Fin 3) (o b : Fin 2) : ℂ :=
  if s = 2 then if b = o then 1 else 0
  else (if b = 0 then 1 else (-1 : ℂ) ^ (o : ℕ) * (if s = 0 then 1 else Complex.I)) /
    (Real.sqrt 2 : ℂ)

def productVector {n : ℕ} (s : Fin n → Fin 3) (o : Fin n → Fin 2)
    (b : Fin n → Fin 2) : ℂ := ∏ j, pauliEigen (s j) (o j) (b j)

def outcomeProb {n : ℕ} (ρ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (s : Fin n → Fin 3) (o : Fin n → Fin 2) : ℝ :=
  (star (productVector s o) ⬝ᵥ (ρ *ᵥ productVector s o)).re

def settingFisher {n : ℕ} (ρ v : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (s : Fin n → Fin 3) : ℝ :=
  ∑ o, (star (productVector s o) ⬝ᵥ (v *ᵥ productVector s o)).re ^ 2 /
    outcomeProb ρ s o

def averageFisher {n : ℕ} (ρ v : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : ℝ :=
  (∑ s, settingFisher ρ v s) / 3 ^ n

def IsRankTangent {n : ℕ} (r : ℕ)
    (ρ v : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : Prop :=
  ∃ γ : ℝ → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ,
    γ 0 = ρ ∧ HasDerivAt γ v 0 ∧ ∀ t, IsDensity (γ t) ∧ (γ t).rank = r

def claim : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
    ∀ ρ v : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ,
      IsDensity ρ → ρ.rank = r → IsRankTangent r ρ v →
      c * (v * v).trace.re ≤ averageFisher ρ v

private def ghzKet (n : ℕ) (θ : ℝ) (b : Fin n → Fin 2) : ℂ :=
  ((if b = (fun _ => 0) then 1 else 0) +
    Complex.exp (θ * Complex.I) * (if b = (fun _ => 1) then 1 else 0)) /
    (Real.sqrt 2 : ℂ)

private def ghz (n : ℕ) (θ : ℝ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  vecMulVec (ghzKet n θ) (star (ghzKet n θ))

private def phaseDirection (n : ℕ) (θ : ℝ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := fun a b =>
  Complex.I / 2 *
    (Complex.exp (θ * Complex.I) *
      (if a = (fun _ => 1) ∧ b = (fun _ => 0) then 1 else 0) -
    star (Complex.exp (θ * Complex.I)) *
      (if a = (fun _ => 0) ∧ b = (fun _ => 1) then 1 else 0))

private def outcomePhase {n : ℕ} (s : Fin n → Fin 3) (o : Fin n → Fin 2) : ℂ :=
  ∏ j, (-1 : ℂ) ^ (o j : ℕ) * (if s j = 0 then 1 else -Complex.I)

private lemma branches_distinct (n : ℕ) (hn : 0 < n) :
    (fun _ : Fin n => (0 : Fin 2)) ≠ (fun _ => 1) := by
  intro h
  have hzero := congrFun h ⟨0, hn⟩
  exact Fin.zero_ne_one hzero

private lemma phase_unit (θ : ℝ) :
    Complex.exp (θ * Complex.I) * star (Complex.exp (θ * Complex.I)) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  norm_num

private lemma ghz_entry (n : ℕ) (hn : 0 < n) (θ : ℝ)
    (a b : Fin n → Fin 2) :
    ghz n θ a b =
      ((if a = (fun _ => 0) ∧ b = (fun _ => 0) then 1 else 0) +
       (if a = (fun _ => 1) ∧ b = (fun _ => 1) then 1 else 0) +
       Complex.exp (θ * Complex.I) *
         (if a = (fun _ => 1) ∧ b = (fun _ => 0) then 1 else 0) +
       star (Complex.exp (θ * Complex.I)) *
         (if a = (fun _ => 0) ∧ b = (fun _ => 1) then 1 else 0)) / 2 := by
  have hab := branches_distinct n hn
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hu := phase_unit θ
  simp only [Complex.star_def] at hu
  change ghzKet n θ a * star (ghzKet n θ b) = _
  change (((if a = (fun _ => 0) then 1 else 0) + Complex.exp (θ * Complex.I) *
      (if a = (fun _ => 1) then 1 else 0)) / (Real.sqrt 2 : ℂ)) *
    star (((if b = (fun _ => 0) then 1 else 0) + Complex.exp (θ * Complex.I) *
      (if b = (fun _ => 1) then 1 else 0)) / (Real.sqrt 2 : ℂ)) = _
  simp only [map_div₀, Complex.star_def, Complex.conj_ofReal]
  rw [div_mul_div_comm, ← pow_two, hs]
  by_cases ha : a = (fun _ => 0) <;> by_cases hb : b = (fun _ => 0) <;>
    by_cases hc : a = (fun _ => 1) <;> by_cases hd : b = (fun _ => 1) <;>
    simp_all

private lemma ghz_density_rank (n : ℕ) (hn : 0 < n) (θ : ℝ) :
    IsDensity (ghz n θ) ∧ (ghz n θ).rank = 1 := by
  have hab := branches_distinct n hn
  have hd (a : Fin n → Fin 2) : ghz n θ a a =
      ((if a = (fun _ => 0) then 1 else 0) +
       (if a = (fun _ => 1) then 1 else 0)) / 2 := by
    rw [ghz_entry n hn]
    by_cases ha : a = (fun _ => 0) <;> by_cases hb : a = (fun _ => 1) <;>
      simp_all
  have htrace : (ghz n θ).trace = 1 := by
    change (∑ a, ghz n θ a a) = 1
    simp_rw [hd, add_div]
    rw [Finset.sum_add_distrib]
    norm_num [← Finset.sum_div]
  refine ⟨⟨posSemidef_vecMulVec_self_star _, htrace⟩, ?_⟩
  apply le_antisymm (rank_vecMulVec_le _ _)
  have hdet : ((ghz n θ).submatrix
      (fun _ : Fin 1 => fun _ => 0) (fun _ : Fin 1 => fun _ => 0)).det ≠ 0 := by
    rw [Matrix.det_unique]
    change ghz n θ (fun _ => 0) (fun _ => 0) ≠ 0
    rw [hd]
    simp [hab]
  have hlow := rank_submatrix_le (ghz n θ)
    (fun _ : Fin 1 => fun _ => 0) (fun _ : Fin 1 => fun _ => 0)
  rw [rank_of_det_ne_zero hdet] at hlow
  change 1 ≤ (ghz n θ).rank
  simpa only [Fintype.card_fin] using hlow

private lemma ghz_derivative (n : ℕ) (hn : 0 < n) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => ghz n (θ + t)) (phaseDirection n θ) 0 := by
  have he : HasDerivAt (fun t : ℝ => Complex.exp ((θ + t) * Complex.I))
      (Complex.exp (θ * Complex.I) * Complex.I) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_add θ).ofReal_comp.mul_const Complex.I).cexp
  apply hasDerivAt_pi.2
  intro a
  apply hasDerivAt_pi.2
  intro b
  simp_rw [ghz_entry n hn]
  convert (((hasDerivAt_const (0 : ℝ)
      ((if a = (fun _ => 0) ∧ b = (fun _ => 0) then (1 : ℂ) else 0) +
       (if a = (fun _ => 1) ∧ b = (fun _ => 1) then 1 else 0))).add
      (he.mul_const (if a = (fun _ => 1) ∧ b = (fun _ => 0) then 1 else 0))).add
      (he.star.mul_const (if a = (fun _ => 0) ∧ b = (fun _ => 1) then 1 else 0))).div_const 2 using 1
  · funext t
    simp only [Complex.ofReal_add, Pi.add_apply]
  · change Complex.I / 2 * _ = _
    simp only [star_mul, Complex.star_def, Complex.conj_I, zero_add]
    ring

private lemma corner_expectation {α : Type} [Fintype α] [DecidableEq α]
    (a b : α) (aa bb ba ab : ℂ) (u : α → ℂ) :
    star u ⬝ᵥ ((fun i j =>
      (if i = a ∧ j = a then aa else 0) +
      (if i = b ∧ j = b then bb else 0) +
      (if i = b ∧ j = a then ba else 0) +
      (if i = a ∧ j = b then ab else 0)) *ᵥ u) =
      aa * star (u a) * u a + bb * star (u b) * u b +
      ba * star (u b) * u a + ab * star (u a) * u b := by
  change (∑ i, star (u i) * ∑ j,
    ((if i = a ∧ j = a then aa else 0) +
     (if i = b ∧ j = b then bb else 0) +
     (if i = b ∧ j = a then ba else 0) +
     (if i = a ∧ j = b then ab else 0)) * u j) = _
  simp [add_mul, mul_add,
    Finset.sum_add_distrib, ite_mul, mul_ite, ite_and, mul_comm, mul_left_comm,
    mul_assoc]

private lemma phase_expectation (n : ℕ) (θ : ℝ) (u : (Fin n → Fin 2) → ℂ) :
    star u ⬝ᵥ (phaseDirection n θ *ᵥ u) = Complex.I / 2 *
      (Complex.exp (θ * Complex.I) * star (u (fun _ => 1)) * u (fun _ => 0) -
       star (Complex.exp (θ * Complex.I)) * star (u (fun _ => 0)) * u (fun _ => 1)) := by
  have hm : phaseDirection n θ = fun a b =>
      (if a = (fun _ => 0) ∧ b = (fun _ => 0) then (0 : ℂ) else 0) +
      (if a = (fun _ => 1) ∧ b = (fun _ => 1) then 0 else 0) +
      (if a = (fun _ => 1) ∧ b = (fun _ => 0)
        then Complex.I / 2 * Complex.exp (θ * Complex.I) else 0) +
      (if a = (fun _ => 0) ∧ b = (fun _ => 1)
        then -(Complex.I / 2 * star (Complex.exp (θ * Complex.I))) else 0) := by
    ext a b
    change Complex.I / 2 * _ = _
    split_ifs <;> ring
  rw [hm, corner_expectation]
  ring

private lemma ghz_expectation (n : ℕ) (hn : 0 < n) (θ : ℝ)
    (u : (Fin n → Fin 2) → ℂ) :
    star u ⬝ᵥ (ghz n θ *ᵥ u) =
      (star (u (fun _ => 0)) * u (fun _ => 0) +
       star (u (fun _ => 1)) * u (fun _ => 1) +
       Complex.exp (θ * Complex.I) * star (u (fun _ => 1)) * u (fun _ => 0) +
       star (Complex.exp (θ * Complex.I)) * star (u (fun _ => 0)) * u (fun _ => 1)) / 2 := by
  have hm : ghz n θ = fun a b =>
      (if a = (fun _ => 0) ∧ b = (fun _ => 0) then (1 / 2 : ℂ) else 0) +
      (if a = (fun _ => 1) ∧ b = (fun _ => 1) then 1 / 2 else 0) +
      (if a = (fun _ => 1) ∧ b = (fun _ => 0)
        then Complex.exp (θ * Complex.I) / 2 else 0) +
      (if a = (fun _ => 0) ∧ b = (fun _ => 1)
        then star (Complex.exp (θ * Complex.I)) / 2 else 0) := by
    ext a b
    rw [ghz_entry n hn]
    split_ifs <;> ring
  rw [hm, corner_expectation]
  ring

private lemma phase_norm (n : ℕ) (hn : 0 < n) (θ : ℝ) :
    ((phaseDirection n θ * phaseDirection n θ).trace).re = 1 / 2 := by
  have hab := branches_distinct n hn
  have hu := phase_unit θ
  have hv (a b : Fin n → Fin 2) : phaseDirection n θ a b =
      Complex.I / 2 *
      (Complex.exp (θ * Complex.I) *
        (if a = (fun _ => 1) ∧ b = (fun _ => 0) then 1 else 0) -
       star (Complex.exp (θ * Complex.I)) *
        (if a = (fun _ => 0) ∧ b = (fun _ => 1) then 1 else 0)) := rfl
  have hd (a : Fin n → Fin 2) :
      (phaseDirection n θ * phaseDirection n θ) a a =
      (if a = (fun _ => 0) then (1 / 4 : ℂ) else 0) +
      (if a = (fun _ => 1) then 1 / 4 else 0) := by
    rw [Matrix.mul_apply]
    simp_rw [hv]
    by_cases ha : a = (fun _ => 0) <;> by_cases hb : a = (fun _ => 1) <;>
      simp_all [mul_ite, ite_and]
    all_goals ring_nf at hu ⊢
    all_goals try simp only [Complex.I_sq]
    all_goals linear_combination hu / 4
  have ht : (phaseDirection n θ * phaseDirection n θ).trace = 1 / 2 := by
    change (∑ a, (phaseDirection n θ * phaseDirection n θ) a a) = 1 / 2
    simp_rw [hd]
    rw [Finset.sum_add_distrib]
    simp
    norm_num
  rw [ht]
  norm_num

private lemma z_setting_zero (n : ℕ) (_hn : 0 < n) (θ : ℝ)
    (s : Fin n → Fin 3) (hs : ∃ j, s j = 2) :
    settingFisher (ghz n θ) (phaseDirection n θ) s = 0 := by
  change (∑ o, (star (productVector s o) ⬝ᵥ
    (phaseDirection n θ *ᵥ productVector s o)).re ^ 2 / outcomeProb (ghz n θ) s o) = 0
  apply Finset.sum_eq_zero
  intro o _
  have hp : productVector s o (fun _ => 0) = 0 ∨
      productVector s o (fun _ => 1) = 0 := by
    obtain ⟨j, hj⟩ := hs
    by_cases ho : o j = 0
    · right
      change (∏ k, pauliEigen (s k) (o k) 1) = 0
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [hj]
      change (if (1 : Fin 2) = o j then (1 : ℂ) else 0) = 0
      simp [ho]
    · left
      change (∏ k, pauliEigen (s k) (o k) 0) = 0
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [hj]
      change (if (0 : Fin 2) = o j then (1 : ℂ) else 0) = 0
      simp [Ne.symm ho]
  rw [phase_expectation]
  rcases hp with hp | hp <;> simp [hp]

private lemma pauli_xy_products (s : Fin 3) (hs : s ≠ 2) (o : Fin 2) :
    star (pauliEigen s o 0) * pauliEigen s o 0 = (1 / 2 : ℂ) ∧
    star (pauliEigen s o 1) * pauliEigen s o 1 = (1 / 2 : ℂ) ∧
    star (pauliEigen s o 1) * pauliEigen s o 0 =
      ((-1 : ℂ) ^ (o : ℕ) * (if s = 0 then 1 else -Complex.I)) / 2 := by
  have hvals : pauliEigen s o 0 = 1 / (Real.sqrt 2 : ℂ) ∧
      pauliEigen s o 1 = ((-1 : ℂ) ^ (o : ℕ) *
        (if s = 0 then 1 else Complex.I)) / (Real.sqrt 2 : ℂ) := by
    constructor
    · change (if s = 2 then (if (0 : Fin 2) = o then (1 : ℂ) else 0)
        else 1 / (Real.sqrt 2 : ℂ)) = _
      rw [ite_eq_right hs]
    · change (if s = 2 then (if (1 : Fin 2) = o then (1 : ℂ) else 0)
        else ((-1 : ℂ) ^ (o : ℕ) * (if s = 0 then 1 else Complex.I)) /
          (Real.sqrt 2 : ℂ)) = _
      rw [ite_eq_right hs]
  rw [hvals.1, hvals.2]
  fin_cases o <;> by_cases h : s = 0 <;> norm_num [h, Complex.star_def]
  all_goals repeat' constructor
  all_goals ring_nf
  all_goals try simp only [Complex.I_sq]
  all_goals norm_num
  all_goals first
    | rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    | rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  all_goals norm_num

private lemma xy_amplitudes (n : ℕ) (s : Fin n → Fin 3)
    (hs : ∀ j, s j ≠ 2) (o : Fin n → Fin 2) :
    star (productVector s o (fun _ => 0)) * productVector s o (fun _ => 0) =
      1 / (2 : ℂ) ^ n ∧
    star (productVector s o (fun _ => 1)) * productVector s o (fun _ => 1) =
      1 / (2 : ℂ) ^ n ∧
    star (productVector s o (fun _ => 1)) * productVector s o (fun _ => 0) =
      outcomePhase s o / (2 : ℂ) ^ n := by
  have hp := fun j => pauli_xy_products (s j) (hs j) (o j)
  have hzero : star (productVector s o (fun _ => 0)) * productVector s o (fun _ => 0) =
      ∏ j, star (pauliEigen (s j) (o j) 0) * pauliEigen (s j) (o j) 0 := by
    change star (∏ j, pauliEigen (s j) (o j) 0) * (∏ j, pauliEigen (s j) (o j) 0) = _
    rw [star_prod, Finset.prod_mul_distrib]
  have hone : star (productVector s o (fun _ => 1)) * productVector s o (fun _ => 1) =
      ∏ j, star (pauliEigen (s j) (o j) 1) * pauliEigen (s j) (o j) 1 := by
    change star (∏ j, pauliEigen (s j) (o j) 1) * (∏ j, pauliEigen (s j) (o j) 1) = _
    rw [star_prod, Finset.prod_mul_distrib]
  have hcross : star (productVector s o (fun _ => 1)) * productVector s o (fun _ => 0) =
      ∏ j, star (pauliEigen (s j) (o j) 1) * pauliEigen (s j) (o j) 0 := by
    change star (∏ j, pauliEigen (s j) (o j) 1) * (∏ j, pauliEigen (s j) (o j) 0) = _
    rw [star_prod, Finset.prod_mul_distrib]
  refine ⟨?_, ?_, ?_⟩
  · rw [hzero]
    simp_rw [(hp _).1]
    simp
  · rw [hone]
    simp_rw [(hp _).2.1]
    simp
  · rw [hcross]
    simp_rw [(hp _).2.2]
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl

private lemma xy_prob_direction (n : ℕ) (hn : 0 < n)
    (s : Fin n → Fin 3) (hs : ∀ j, s j ≠ 2) (o : Fin n → Fin 2) (θ : ℝ) :
    outcomeProb (ghz n θ) s o =
      (1 + (Complex.exp (θ * Complex.I) * outcomePhase s o).re) / 2 ^ n ∧
    (star (productVector s o) ⬝ᵥ (phaseDirection n θ *ᵥ productVector s o)).re =
      -(Complex.exp (θ * Complex.I) * outcomePhase s o).im / 2 ^ n := by
  obtain ⟨hz, ho, hcross⟩ := xy_amplitudes n s hs o
  have hcrossconj : star (productVector s o (fun _ => 0)) * productVector s o (fun _ => 1) =
      star (outcomePhase s o) / (2 : ℂ) ^ n := by
    have h := congrArg star hcross
    simpa only [star_mul, star_star, star_div₀, star_pow, star_ofNat, mul_comm] using h
  constructor
  · change (star (productVector s o) ⬝ᵥ (ghz n θ *ᵥ productVector s o)).re = _
    rw [ghz_expectation n hn]
    have hform : (star (productVector s o (fun _ => 0)) * productVector s o (fun _ => 0) +
        star (productVector s o (fun _ => 1)) * productVector s o (fun _ => 1) +
        Complex.exp (θ * Complex.I) * star (productVector s o (fun _ => 1)) *
          productVector s o (fun _ => 0) +
        star (Complex.exp (θ * Complex.I)) * star (productVector s o (fun _ => 0)) *
          productVector s o (fun _ => 1)) / 2 =
        (1 + (Complex.exp (θ * Complex.I) * outcomePhase s o +
          star (Complex.exp (θ * Complex.I) * outcomePhase s o)) / 2) / (2 : ℂ) ^ n := by
      simp only [mul_assoc]
      rw [hz, ho, hcross, hcrossconj]
      simp only [star_mul]
      ring
    rw [hform]
    simp only [Complex.star_def, Complex.add_conj, Complex.ofReal_mul,
      Complex.ofReal_ofNat, mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0)]
    rw [show (2 : ℂ) ^ n = Complex.ofReal ((2 : ℝ) ^ n) from
      (Complex.ofReal_pow 2 n).symm]
    simp only [Complex.div_ofReal_re, Complex.add_re, Complex.one_re,
      Complex.ofReal_re]
  · rw [phase_expectation]
    have hform : Complex.I / 2 *
        (Complex.exp (θ * Complex.I) * star (productVector s o (fun _ => 1)) *
          productVector s o (fun _ => 0) -
        star (Complex.exp (θ * Complex.I)) * star (productVector s o (fun _ => 0)) *
          productVector s o (fun _ => 1)) =
        Complex.I / 2 * (Complex.exp (θ * Complex.I) * outcomePhase s o -
          star (Complex.exp (θ * Complex.I) * outcomePhase s o)) / (2 : ℂ) ^ n := by
      simp only [mul_assoc]
      rw [hcross, hcrossconj]
      simp only [star_mul]
      ring
    rw [hform]
    simp only [Complex.star_def, Complex.sub_conj, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    have hnum (x : ℝ) : Complex.I / 2 * ((2 : ℂ) * x * Complex.I) = -x := by
      calc
        _ = (x : ℂ) * Complex.I ^ 2 := by ring
        _ = -x := by rw [Complex.I_sq]; ring
    rw [hnum, show (2 : ℂ) ^ n = Complex.ofReal ((2 : ℝ) ^ n) from
      (Complex.ofReal_pow 2 n).symm]
    simp only [Complex.div_ofReal_re, Complex.neg_re, Complex.ofReal_re]

private lemma outcome_phase_fourth (n : ℕ) (s : Fin n → Fin 3) (o : Fin n → Fin 2) :
    outcomePhase s o ^ 4 = 1 := by
  change (∏ j, (-1 : ℂ) ^ (o j : ℕ) * (if s j = 0 then 1 else -Complex.I)) ^ 4 = 1
  rw [← Finset.prod_pow]
  have h (j : Fin n) :
      ((-1 : ℂ) ^ (o j : ℕ) * (if s j = 0 then 1 else -Complex.I)) ^ 4 = 1 := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul]
    by_cases hj : s j = 0 <;> norm_num [hj, pow_succ, Complex.I_sq]
  simp_rw [h]
  simp

private lemma fourth_root_cases (q : ℂ) (hq : q ^ 4 = 1) :
    q = 1 ∨ q = -1 ∨ q = Complex.I ∨ q = -Complex.I := by
  have hf : (q - 1) * (q + 1) * (q - Complex.I) * (q + Complex.I) = 0 := by
    calc
      _ = (q ^ 2 - 1) * (q ^ 2 - Complex.I ^ 2) := by ring
      _ = q ^ 4 - 1 := by rw [Complex.I_sq]; ring
      _ = 0 := by rw [hq]; ring
  rcases mul_eq_zero.mp hf with hf | hf
  · rcases mul_eq_zero.mp hf with hf | hf
    · rcases mul_eq_zero.mp hf with hf | hf
      · exact Or.inl (sub_eq_zero.mp hf)
      · exact Or.inr (Or.inl (eq_neg_of_add_eq_zero_left hf))
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp hf)))
  · exact Or.inr (Or.inr (Or.inr (eq_neg_of_add_eq_zero_left hf)))

private lemma phase_coordinates (n : ℕ) (s : Fin n → Fin 3) (o : Fin n → Fin 2) :
    (Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) * outcomePhase s o).re ^ 2 = 1 / 2 ∧
    (Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) * outcomePhase s o).im ^ 2 = 1 / 2 := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rcases fourth_root_cases _ (outcome_phase_fourth n s o) with h | h | h | h <;>
    rw [h] <;>
    simp [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      -Complex.ofReal_div,
      Real.cos_pi_div_four, Real.sin_pi_div_four, Complex.mul_re, Complex.mul_im] <;>
    nlinarith

private lemma xy_prob_positive (n : ℕ) (hn : 0 < n)
    (s : Fin n → Fin 3) (hs : ∀ j, s j ≠ 2) (o : Fin n → Fin 2) :
    0 < outcomeProb (ghz n (Real.pi / 4)) s o := by
  rw [(xy_prob_direction n hn s hs o (Real.pi / 4)).1]
  apply div_pos _ (by positivity)
  have hsq := (phase_coordinates n s o).1
  have hnonneg := sq_nonneg
    ((Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) * outcomePhase s o).re + 1)
  nlinarith

private lemma outcome_phase_sum (n : ℕ) (hn : 0 < n) (s : Fin n → Fin 3) :
    ∑ o, outcomePhase s o = 0 := by
  change (∑ o : Fin n → Fin 2,
    ∏ j, (-1 : ℂ) ^ (o j : ℕ) * (if s j = 0 then 1 else -Complex.I)) = 0
  rw [← Fintype.prod_sum (fun j (o : Fin 2) =>
    (-1 : ℂ) ^ (o : ℕ) * (if s j = 0 then 1 else -Complex.I))]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, hn⟩ : Fin n))
  simp [Fin.sum_univ_two]

private lemma xy_setting_one (n : ℕ) (hn : 0 < n)
    (s : Fin n → Fin 3) (hs : ∀ j, s j ≠ 2) :
    settingFisher (ghz n (Real.pi / 4)) (phaseDirection n (Real.pi / 4)) s = 1 := by
  have hp := xy_prob_direction n hn s hs
  have hpos := xy_prob_positive n hn s hs
  have hsum := outcome_phase_sum n hn s
  have hterm (o : Fin n → Fin 2) :
      (star (productVector s o) ⬝ᵥ
        (phaseDirection n (Real.pi / 4) *ᵥ productVector s o)).re ^ 2 /
        outcomeProb (ghz n (Real.pi / 4)) s o =
      (1 - (Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) * outcomePhase s o).re) / 2 ^ n := by
    obtain ⟨hreal, himag⟩ := phase_coordinates n s o
    have hplus : 1 + (Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) *
        outcomePhase s o).re ≠ 0 := by
      have hd := hpos o
      rw [(hp o (Real.pi / 4)).1] at hd
      intro he
      rw [he, zero_div] at hd
      exact (lt_irrefl 0) hd
    rw [(hp o (Real.pi / 4)).1, (hp o (Real.pi / 4)).2]
    have hid : (Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) * outcomePhase s o).im ^ 2 =
        (1 - (Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) * outcomePhase s o).re) *
        (1 + (Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) * outcomePhase s o).re) := by
      nlinarith
    field_simp
    nlinarith [hid]
  have hrez : (∑ o : Fin n → Fin 2,
      (Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) * outcomePhase s o).re) = 0 := by
    rw [← Complex.re_sum, ← Finset.mul_sum, hsum, mul_zero]
    rfl
  change (∑ o, _) = 1
  simp_rw [hterm]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hrez]
  simp [Nat.cast_pow]

private lemma xy_setting_count (n : ℕ) :
    (∑ s : Fin n → Fin 3, if ∀ j, s j ≠ 2 then (1 : ℝ) else 0) = 2 ^ n := by
  have h (s : Fin n → Fin 3) :
      (if ∀ j, s j ≠ 2 then (1 : ℝ) else 0) = ∏ j, if s j ≠ 2 then 1 else 0 := by
    classical
    by_cases hs : ∀ j, s j ≠ 2
    · simp [hs]
    · obtain ⟨j, hj⟩ := not_forall.mp hs
      rw [ite_eq_right hs]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)
  simp_rw [h]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (a : Fin 3) =>
    if a ≠ 2 then (1 : ℝ) else 0)]
  norm_num [Fin.sum_univ_three]

private lemma average_exact (n : ℕ) (hn : 0 < n) :
    averageFisher (ghz n (Real.pi / 4)) (phaseDirection n (Real.pi / 4)) =
      (2 / 3 : ℝ) ^ n := by
  have hz := z_setting_zero n hn (Real.pi / 4)
  have hxy := xy_setting_one n hn
  have hcount := xy_setting_count n
  change (∑ s, settingFisher (ghz n (Real.pi / 4))
    (phaseDirection n (Real.pi / 4)) s) / 3 ^ n = (2 / 3 : ℝ) ^ n
  rw [div_pow, ← hcount]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : ∀ j, s j ≠ 2
  · rw [ite_eq_left hs, hxy s hs]
  · rw [ite_eq_right hs, hz s]
    simpa only [not_forall, not_not] using hs

private lemma small_ratio (c : ℝ) (hc : 0 < c) :
    ∃ n : ℕ, 0 < n ∧ 2 * (2 / 3 : ℝ) ^ n < c := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (half_pos hc)
    (by norm_num : (2 / 3 : ℝ) < 1)
  refine ⟨k + 1, Nat.succ_pos k, ?_⟩
  have hnonneg : 0 ≤ (2 / 3 : ℝ) ^ k := by positivity
  rw [pow_succ]
  nlinarith

theorem result : ¬ claim := by
  intro h
  obtain ⟨c, hc, hbound⟩ := h 1 le_rfl
  obtain ⟨n, hn, hsmall⟩ := small_ratio c hc
  obtain ⟨hρ, hrank⟩ := ghz_density_rank n hn (Real.pi / 4)
  have ht : IsRankTangent 1 (ghz n (Real.pi / 4))
      (phaseDirection n (Real.pi / 4)) :=
    ⟨fun t => ghz n (Real.pi / 4 + t), by simp,
      ghz_derivative n hn (Real.pi / 4), fun t => ghz_density_rank n hn _⟩
  have hb := hbound n _ _ hρ hrank ht
  rw [phase_norm n hn, average_exact n hn] at hb
  linarith

end D5.S3.Quantum.Tomography.PauliFisherGHZRefutation
