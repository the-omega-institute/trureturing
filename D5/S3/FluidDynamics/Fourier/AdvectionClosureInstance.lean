/- GID: D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Fourier/AdvectionClosureInstance
   mirror-E: none(waiver:exact-symbolic-Fourier-family)
   anchors: []
   utility: none
   digest: The Fourier witness violates the mixed-term condition of the quadratic closure criterion in a five-mode Galerkin state space. -/

import D5.S3.FluidDynamics.Fourier.LowModeReversalWitness
import D5.S3.Observer.Reversal.QuadraticObservationClosure
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.BilinearMap

/-!
The four input modes are augmented by the generated transverse mode (0,1).
Keeping only the four inputs would discard the acceleration being observed.
The state space is a real vector space of complex amplitudes. The operator
uses every interaction of the five retained modes, followed by Leray projection.
On the embedded original family the fifth input is zero, so these expressions
agree with the original four-input convolution at every retained output.
This is a Galerkin instance, not an invariant subspace or a full PDE closure.
The coefficient predictor on the witness family has a smaller domain of
obligations than an exact vector closure on all states.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.FluidDynamics.Fourier.AdvectionClosureInstance

open scoped BigOperators
open LowModeReversalWitness
open D5.S3.Observer.Reversal.QuadraticObservationClosure

/-- Five retained complex velocity amplitudes, regarded as a real vector space. -/
abbrev State := Fin 5 → Amplitude

/-- The generated transverse mode followed by the original four input modes. -/
def mode : Fin 5 → Mode := Fin.cases (0, 1) frequency

/-- Linear zero extension of the four input amplitudes to the five retained modes. -/
def embed : (Fin 4 → Amplitude) →ₗ[ℝ] State where
  toFun x := Fin.cases 0 x
  map_add' x y := by funext j c; refine Fin.cases ?_ (fun i => ?_) j <;> simp
  map_smul' r x := by funext j c; refine Fin.cases ?_ (fun i => ?_) j <;> simp

/-- The original two-amplitude family in the enlarged state space. -/
def family (alpha beta : ℝ) : State := embed (inputAmplitude alpha beta)

private def convolution (x y : State) (k : Mode) (c : Fin 3) : ℂ :=
  Complex.I * ∑ i : Fin 5, ∑ j : Fin 5,
    if mode i + mode j = k then
      (((mode j).1 : ℂ) * x i 0 + ((mode j).2 : ℂ) * x i 1) * y j c
    else 0

private theorem convolution_add_left (x y z : State) (k : Mode) (c : Fin 3) :
    convolution (x + y) z k c = convolution x z k c + convolution y z k c := by
  simp only [convolution, Pi.add_apply, mul_add, add_mul]
  simp only [← Finset.sum_add_distrib, ← mul_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

private theorem convolution_add_right (x y z : State) (k : Mode) (c : Fin 3) :
    convolution x (y + z) k c = convolution x y k c + convolution x z k c := by
  simp only [convolution, Pi.add_apply, mul_add]
  simp only [← Finset.sum_add_distrib, ← mul_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

private theorem convolution_smul_left (r : ℝ) (x y : State) (k : Mode) (c : Fin 3) :
    convolution (r • x) y k c = r • convolution x y k c := by
  simp only [convolution, Pi.smul_apply, Complex.real_smul]
  rw [mul_left_comm (r : ℂ)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

private theorem convolution_smul_right (r : ℝ) (x y : State) (k : Mode) (c : Fin 3) :
    convolution x (r • y) k c = r • convolution x y k c := by
  simp only [convolution, Pi.smul_apply, Complex.real_smul]
  rw [mul_left_comm (r : ℂ)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

private def lerayLinear (k : Mode) : Amplitude →ₗ[ℝ] Amplitude where
  toFun := leray k
  map_add' x y := by funext c; simp only [leray, Pi.add_apply]; ring
  map_smul' r x := by
    funext c
    simp only [leray, Pi.smul_apply, Complex.real_smul, RingHom.id_apply]
    ring

/-- The full retained convolution followed by Leray projection, bundled bilinearly over the reals. -/
def B : State →ₗ[ℝ] State →ₗ[ℝ] State :=
  LinearMap.mk₂ ℝ (fun x y k => lerayLinear (mode k) (convolution x y (mode k)))
    (by
      intro x y z
      funext k
      rw [show convolution (x + y) z (mode k) =
        convolution x z (mode k) + convolution y z (mode k) from
          funext (convolution_add_left x y z (mode k)), map_add]
      rfl)
    (by
      intro r x y
      funext k
      rw [show convolution (r • x) y (mode k) = r • convolution x y (mode k) from
        funext (convolution_smul_left r x y (mode k)), map_smul]
      rfl)
    (by
      intro x y z
      funext k
      rw [show convolution x (y + z) (mode k) =
        convolution x y (mode k) + convolution x z (mode k) from
          funext (convolution_add_right x y z (mode k)), map_add]
      rfl)
    (by
      intro r x y
      funext k
      rw [show convolution x (r • y) (mode k) = r • convolution x y (mode k) from
        funext (convolution_smul_right r x y (mode k)), map_smul]
      rfl)

/-- The viscous Fourier multiplier on every retained mode. -/
def L (nu : ℝ) : State →ₗ[ℝ] State where
  toFun x k c := -(nu : ℂ) * (frequencySquared (mode k) : ℂ) * x k c
  map_add' x y := by funext k c; simp only [Pi.add_apply]; ring
  map_smul' r x := by
    funext k c
    simp only [Pi.smul_apply, Complex.real_smul, RingHom.id_apply]
    ring

/-- The squared-frequency cutoff at one on the retained state. -/
def P : State →ₗ[ℝ] State where
  toFun x k c := if frequencySquared (mode k) ≤ 1 then x k c else 0
  map_add' x y := by funext k c; dsimp; split_ifs <;> simp
  map_smul' r x := by funext k c; dsimp; split_ifs <;> simp

/-- The low-mode cutoff is an idempotent linear projection. -/
theorem projection_idempotent (x : State) : P (P x) = P x := by
  funext k c
  change (if frequencySquared (mode k) ≤ 1 then
    (if frequencySquared (mode k) ≤ 1 then x k c else 0) else 0) = (if frequencySquared (mode k) ≤ 1 then x k c else 0)
  split_ifs <;> rfl

private theorem family_coefficient (alpha beta : ℝ) (j : Fin 5) (c : Fin 3) :
    family alpha beta j c = coefficient alpha beta (mode j) c := by
  refine Fin.cases ?_ (fun i => ?_) j
  · change 0 = coefficient alpha beta (0, 1) c
    have hf : ∀ i : Fin 4, frequency i ≠ (0, 1) := by decide
    simp only [coefficient, hf, if_false, Finset.sum_const_zero]
  · change inputAmplitude alpha beta i c = coefficient alpha beta (frequency i) c
    have hf : Function.Injective frequency := by decide
    simp only [coefficient, hf.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem family_convolution (alpha beta : ℝ) (k : Mode) :
    convolution (family alpha beta) (family alpha beta) k = advection alpha beta k := by
  funext c
  simp only [convolution, family, embed, LinearMap.coe_mk, AddHom.coe_mk,
    mode, advection, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
    Pi.zero_apply, mul_zero, add_zero, zero_mul, ite_self, Finset.sum_const_zero, zero_add]
  rfl

/-- The projected family is exactly the original complete low observation sampled at retained modes. -/
theorem family_observation (alpha beta : ℝ) (j : Fin 5) (c : Fin 3) :
    P (family alpha beta) j c = lowObservation alpha beta (mode j) c := by
  change (if frequencySquared (mode j) ≤ 1 then family alpha beta j c else 0) = _
  rw [family_coefficient]
  rfl

/-- The Galerkin vector field agrees with the fluid acceleration at every retained output on the family. -/
theorem family_acceleration (nu alpha beta : ℝ) (j : Fin 5) (c : Fin 3) :
    vectorField (L nu) B (family alpha beta) j c =
      acceleration nu alpha beta (mode j) c := by
  change -(nu : ℂ) * (frequencySquared (mode j) : ℂ) * family alpha beta j c -
    leray (mode j) (convolution (family alpha beta) (family alpha beta) (mode j)) c = _
  rw [family_coefficient, family_convolution]
  rfl

private theorem family_add (a b a' b' : ℝ) :
    family a b + family a' b' = family (a + a') (b + b') := by
  rw [family, family, ← map_add]
  congr 1
  funext j c
  simp only [Pi.add_apply, inputAmplitude, Complex.ofReal_add]
  split_ifs <;> ring

private theorem visible_family : P (family 1 0) = family 1 0 := by
  funext j c
  refine Fin.cases ?_ (fun i => ?_) j
  · change (if frequencySquared (0, 1) ≤ 1 then (0 : ℂ) else 0) = 0
    simp
  · change (if frequencySquared (frequency i) ≤ 1 then inputAmplitude 1 0 i c else 0) =
      inputAmplitude 1 0 i c
    fin_cases i <;> norm_num [frequencySquared, frequency, inputAmplitude, Fin.ext_iff]

private theorem hidden_family : P (family 0 1) = 0 := by
  funext j c
  rw [family_observation, lowObservation_independent 0 1 0]
  simp [lowObservation, coefficient, inputAmplitude]

private theorem diagonal_transverse (alpha beta : ℝ) :
    B (family alpha beta) (family alpha beta) 0 0 =
      Complex.I * (alpha : ℂ) * (beta : ℂ) / 4 := by
  have h := family_acceleration 0 alpha beta 0 0
  rw [show mode 0 = (0, 1) from rfl, transverse_acceleration] at h
  change -(0 : ℂ) * (frequencySquared (mode 0) : ℂ) * family alpha beta 0 0 -
    B (family alpha beta) (family alpha beta) 0 0 = _ at h
  simp only [neg_zero, zero_mul, zero_sub] at h
  calc
    _ = -(-Complex.I * (alpha : ℂ) * (beta : ℂ) / 4) := neg_eq_iff_eq_neg.mp h
    _ = _ := by ring

/-- A visible wave and a hidden wave have a nonzero observed mixed interaction. -/
theorem mixed_witness :
    P (family 1 0) = family 1 0 ∧ P (family 0 1) = 0 ∧
      P (B (family 1 0) (family 0 1) + B (family 0 1) (family 1 0)) 0 0 =
        Complex.I / 4 := by
  refine ⟨visible_family, hidden_family, ?_⟩
  have h := diagonal_transverse 1 1
  have hs : family (1 : ℝ) 1 = family 1 0 + family 0 1 := by
    simpa using (family_add 1 0 0 1).symm
  rw [hs] at h
  simp only [map_add, LinearMap.add_apply, Pi.add_apply] at h
  have ha := diagonal_transverse 1 0
  have hb := diagonal_transverse 0 1
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_zero,
    zero_div, mul_one] at h ha hb
  rw [ha, hb] at h
  change (if frequencySquared (mode 0) ≤ 1 then
    (B (family 1 0) (family 0 1) + B (family 0 1) (family 1 0)) 0 0 else 0) = _
  rw [if_pos (by norm_num [mode, frequencySquared])]
  simpa only [Pi.add_apply, zero_add, add_zero, add_comm] using h

/-- Viscosity preserves the kernel of the low-mode projection. -/
theorem hidden_linear (nu : ℝ) (b : State) (hb : P b = 0) : P (L nu b) = 0 := by
  funext j c
  have h := congrFun (congrFun hb j) c
  change (if frequencySquared (mode j) ≤ 1 then b j c else 0) = 0 at h
  change (if frequencySquared (mode j) ≤ 1 then
    -(nu : ℂ) * (frequencySquared (mode j) : ℂ) * b j c else 0) = 0
  split_ifs with hj
  · rw [if_pos hj] at h
    rw [h, mul_zero]
  · rfl

/-- The third condition of the general quadratic closure criterion fails. -/
theorem mixed_condition_fails :
    ¬ (∀ a b : State, P a = a → P b = 0 → P (B a b + B b a) = 0) := by
  intro h
  have hz := congrFun (congrFun (h _ _ mixed_witness.1 mixed_witness.2.1) 0) 0
  rw [mixed_witness.2.2] at hz
  have him := congrArg Complex.im hz
  norm_num at him

/-- This concrete Galerkin instance has no exact closure, by the general quadratic criterion. -/
theorem no_exact_closure (nu : ℝ) :
    ¬ ∃ f : State → State, ∀ x, P (vectorField (L nu) B x) = f (P x) := by
  intro h
  exact mixed_condition_fails
    ((quadratic_closure_iff P (L nu) B projection_idempotent).mp h).2.2

/-- Any global exact vector closure would predict the original transverse fluid coefficient on the family. -/
theorem exact_closure_implies_fluid_predictor (nu : ℝ)
    (h : ∃ f : State → State, ∀ x, P (vectorField (L nu) B x) = f (P x)) :
    ∃ predict : (Mode → Amplitude) → ℂ, ∀ alpha beta : ℝ,
      predict (lowObservation alpha beta) = acceleration nu alpha beta (0, 1) 0 := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun obs => f (fun j => obs (mode j)) 0 0, ?_⟩
  intro alpha beta
  have hp : (fun j => lowObservation alpha beta (mode j)) = P (family alpha beta) := by
    funext j c
    exact (family_observation alpha beta j c).symm
  change f (fun j => lowObservation alpha beta (mode j)) 0 0 = _
  rw [hp, ← hf]
  change (if frequencySquared (mode 0) ≤ 1 then
    vectorField (L nu) B (family alpha beta) 0 0 else 0) = _
  rw [if_pos (by norm_num [mode, frequencySquared]), family_acceleration]
  rfl

private theorem transverse_projection (x : State) : P x 0 0 = x 0 0 := rfl

/-- The same mixed obstruction gives a fluid acceleration gap through the general observed-increment identity. -/
theorem fluid_gap_from_mixed (nu : ℝ) :
    acceleration nu 1 1 (0, 1) 0 - acceleration nu 1 0 (0, 1) 0 =
      -Complex.I / 4 := by
  have h := observed_increment P (L nu) B (family 1 0) (family 0 1)
  rw [hidden_linear nu _ hidden_family] at h
  have ht := congrFun (congrFun h 0) 0
  simp only [Pi.sub_apply, Pi.zero_apply] at ht
  rw [mixed_witness.2.2, transverse_projection, transverse_projection,
    transverse_projection] at ht
  have hs : family (1 : ℝ) 0 + family 0 1 = family 1 1 := by
    simpa only [add_zero, zero_add] using family_add 1 0 0 1
  rw [hs, family_acceleration, family_acceleration, diagonal_transverse] at ht
  simpa only [mode, Fin.cases_zero, Complex.ofReal_zero, mul_zero, zero_mul,
    zero_div, sub_zero, zero_sub, neg_div] using ht

/-- The mixed obstruction re-derives exactly the original scalar predictor impossibility on the whole family. -/
theorem no_fluid_predictor_from_mixed (nu : ℝ) :
    ¬ ∃ predict : (Mode → Amplitude) → ℂ,
      ∀ alpha beta : ℝ,
        predict (lowObservation alpha beta) = acceleration nu alpha beta (0, 1) 0 := by
  rintro ⟨predict, hp⟩
  have heq : acceleration nu 1 1 (0, 1) 0 = acceleration nu 1 0 (0, 1) 0 := by
    rw [← hp 1 1, ← hp 1 0, lowObservation_independent 1 1 0]
  have h := fluid_gap_from_mixed nu
  rw [heq, sub_self] at h
  have him := congrArg Complex.im h
  norm_num at him

#print axioms State
#print axioms mode
#print axioms embed
#print axioms family
#print axioms B
#print axioms L
#print axioms P
#print axioms projection_idempotent
#print axioms family_observation
#print axioms family_acceleration
#print axioms mixed_witness
#print axioms hidden_linear
#print axioms mixed_condition_fails
#print axioms no_exact_closure
#print axioms exact_closure_implies_fluid_predictor
#print axioms fluid_gap_from_mixed
#print axioms no_fluid_predictor_from_mixed

end D5.S3.FluidDynamics.Fourier.AdvectionClosureInstance
