/- GID: D5/S3/Quantum/KineticMoments/OddMoment
   generality: G
   mirror-B: D5/B/S3/Quantum/KineticMoments/OddMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prove the Tolias-Dornheim-Vorberger kinetic odd-moment conjecture. -/

/-
result:
  proof_shape: content
  escape_witness: IsotropicAverage.weighted_recurrence (in the live transitive proof path)
  admission_basis: open-problem-resolution (#13703; Proved)
Direct frozen dependencies: D5/S3/Quantum/ObserverCommutator.observer_read_update_commutator_formula; statement_id=sha256:64adf72ef394f71ee3b349cfaac0f75e831d9009d6ca5ef3ad4f9085b1a6212f
Direct unfrozen prerequisite: IsotropicAverage in this delivery.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

/- All statements are universal algebraic or integral identities; no finite certificate,
   enumeration, checker, or numerical reduction is delivered. -/

import D5.S3.Quantum.ObserverCommutator
import D5.S3.Quantum.KineticMoments.IsotropicAverage

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace D5.S3.Quantum.KineticMoments.OddMoment

noncomputable def shift {N : ℕ} (j : Fin N) (v : EuclideanSpace ℝ (Fin 3)) :
    Module.End ℂ ((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun P => Function.update P j (P j + v))

noncomputable def rho {N : ℕ} (hbar : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) : Module.End ℂ ((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ) :=
  ∑ j : Fin N, shift j (hbar • q)

noncomputable def rhoDag {N : ℕ} (hbar : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) : Module.End ℂ ((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ) :=
  ∑ j : Fin N, shift j (-(hbar • q))

noncomputable def energy {N : ℕ} (m : ℝ) (P : (Fin N → EuclideanSpace ℝ (Fin 3))) : ℝ :=
  ∑ j : Fin N, ‖P j‖ ^ 2 / (2 * m)

noncomputable def kinetic {N : ℕ} (m : ℝ) : Module.End ℂ ((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ) :=
  LinearMap.mulLeft ℂ (fun P => (energy m P : ℂ))

noncomputable def delta {N : ℕ} (m : ℝ) (X : Module.End ℂ ((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ)) : Module.End ℂ ((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ) :=
  X * kinetic m - kinetic m * X

noncomputable def C {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (k ell : ℕ) : Module.End ℂ ((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ) :=
  Bracket.bracket ((delta m)^[2*k+1-ell] (rho (N := N) hbar q))
    ((delta m)^[ell] (rhoDag (N := N) hbar q))

noncomputable def a (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) : ℝ := hbar^2 * ‖q‖^2 / (2*m)

noncomputable def b {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (j : Fin N)
    (P : (Fin N → EuclideanSpace ℝ (Fin 3))) : ℝ := (hbar/m) * ⟪q, P j⟫

noncomputable def F {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (k ell : ℕ)
    (P : (Fin N → EuclideanSpace ℝ (Fin 3))) : ℝ :=
  (-1 : ℝ)^ell * ∑ j : Fin N,
    ((b hbar m q j P + a hbar m q)^(2*k+1) -
      (b hbar m q j P - a hbar m q)^(2*k+1))

private noncomputable def translate {N : ℕ} (j : Fin N) (v : (EuclideanSpace ℝ (Fin 3)))
    (P : (Fin N → EuclideanSpace ℝ (Fin 3))) : (Fin N → EuclideanSpace ℝ (Fin 3)) := Function.update P j (P j + v)

private theorem shift_multiplication_commutator {N : ℕ} (j : Fin N) (v : (EuclideanSpace ℝ (Fin 3)))
    (f : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ) (ψ : ((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ)) (P : (Fin N → EuclideanSpace ℝ (Fin 3))) :
    (shift j v * LinearMap.mulLeft ℂ f - LinearMap.mulLeft ℂ f * shift j v) ψ P =
      (f (translate j v P) - f P) * ψ (translate j v P) := by
  have ht (P : (Fin N → EuclideanSpace ℝ (Fin 3))) : P + Pi.single j v = translate j v P := by
    ext i
    by_cases hi : i = j
    · subst i; simp [translate]
    · simp [translate, hi]
  have hs := congrFun
    (D5.S3.Quantum.ObserverCommutator.observer_read_update_commutator_formula
      (Equiv.addRight (Pi.single j v)).symm f ψ) P
  simpa [D5.S3.Quantum.ObserverAlgebra.observerUpdate,
    D5.S3.Quantum.ObserverAlgebra.readObservable, ht, shift, translate] using hs

private theorem energy_translate {N : ℕ} (m : ℝ) (j : Fin N) (v : (EuclideanSpace ℝ (Fin 3)))
    (P : (Fin N → EuclideanSpace ℝ (Fin 3))) :
    energy m (translate j v P) - energy m P =
      (2 * ⟪P j, v⟫ + ‖v‖^2) / (2*m) := by
  classical
  have hs : energy m (translate j v P) =
      energy m P - ‖P j‖^2/(2*m) + ‖P j + v‖^2/(2*m) := by
    unfold energy
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    have ht : ∑ i ∈ Finset.univ.erase j, ‖translate j v P i‖^2/(2*m) =
        ∑ i ∈ Finset.univ.erase j, ‖P i‖^2/(2*m) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [translate, (Finset.mem_erase.mp hi).1]
    rw [ht]
    simp [translate]
  rw [hs, norm_add_sq_real]
  ring

private theorem energy_shift_plus {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (j : Fin N)
    (P : (Fin N → EuclideanSpace ℝ (Fin 3))) :
    energy m (translate j (hbar • q) P) - energy m P = b hbar m q j P + a hbar m q := by
  rw [energy_translate]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  unfold b a
  rw [real_inner_comm (P j) q]
  ring

private theorem energy_shift_minus {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (j : Fin N)
    (P : (Fin N → EuclideanSpace ℝ (Fin 3))) :
    energy m (translate j (-(hbar • q)) P) - energy m P = a hbar m q - b hbar m q j P := by
  rw [energy_translate]
  simp only [inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  unfold b a
  rw [real_inner_comm (P j) q]
  ring

private theorem delta_weighted_shift {N : ℕ} (m : ℝ) (j : Fin N) (v : (EuclideanSpace ℝ (Fin 3)))
    (f : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ) :
    delta m (LinearMap.mulLeft ℂ f * shift j v) =
      LinearMap.mulLeft ℂ (fun P => f P * (energy m (translate j v P) - energy m P : ℝ)) *
        shift j v := by
  ext ψ P
  calc
    (delta m (LinearMap.mulLeft ℂ f * shift j v)) ψ P = f P * (delta m (shift j v) ψ P) := by
      simp [delta, kinetic, LinearMap.mulLeft, Module.End.mul_apply, shift, translate]
      ring
    _ = _ := by
      unfold delta kinetic
      rw [shift_multiplication_commutator]
      simp [LinearMap.mulLeft_apply, Pi.mul_apply, Module.End.mul_apply, shift, translate,
        ← Complex.ofReal_sub, mul_assoc]

private theorem iterate_delta_shift {N : ℕ} (m : ℝ) (j : Fin N) (v : (EuclideanSpace ℝ (Fin 3))) (r : ℕ) :
    (delta m)^[r] (shift j v) =
      LinearMap.mulLeft ℂ (fun P => ((energy m (translate j v P) - energy m P : ℝ) : ℂ)^r) *
        shift j v := by
  let d : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ :=
    fun P => (energy m (translate j v P) - energy m P : ℝ)
  let T : (((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ)) →
      Module.End ℂ ((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ) :=
    fun f => LinearMap.mulLeft ℂ f * shift j v
  have hs : Function.Semiconj T (fun f => f * d) (delta m) := by
    intro f
    exact (delta_weighted_shift m j v f).symm
  have hi := hs.iterate_right r (1 : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ)
  simp only [mul_right_iterate, one_mul] at hi
  have hT : T 1 = shift j v := by
    ext ψ P
    simp [T, Module.End.mul_apply, LinearMap.mulLeft_apply]
  rw [hT] at hi
  exact hi.symm

private theorem iterate_delta_shift_plus {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (j : Fin N) (r : ℕ) :
    (delta m)^[r] (shift j (hbar • q)) =
      LinearMap.mulLeft ℂ (fun P => ((b hbar m q j P + a hbar m q : ℝ) : ℂ)^r) *
        shift j (hbar • q) := by
  simpa [energy_shift_plus] using iterate_delta_shift m j (hbar • q) r

private theorem iterate_delta_shift_minus {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (j : Fin N) (r : ℕ) :
    (delta m)^[r] (shift j (-(hbar • q))) =
      LinearMap.mulLeft ℂ (fun P => ((a hbar m q - b hbar m q j P : ℝ) : ℂ)^r) *
        shift j (-(hbar • q)) := by
  simpa [energy_shift_minus] using iterate_delta_shift m j (-(hbar • q)) r

private theorem iterate_delta_sum {N : ℕ} {ι : Type*} (m : ℝ) (s : Finset ι)
    (f : ι → Module.End ℂ ((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ)) (r : ℕ) :
    (delta m)^[r] (∑ j ∈ s, f j) = ∑ j ∈ s, (delta m)^[r] (f j) := by
  let d : Module.End ℂ (Module.End ℂ ((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ)) :=
    LinearMap.mulRight ℂ (kinetic m) - LinearMap.mulLeft ℂ (kinetic m)
  have hd : (d : Module.End ℂ ((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ) →
      Module.End ℂ ((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ)) = delta m := rfl
  rw [← hd]
  simpa only [Module.End.pow_apply] using map_sum (d ^ r) f s

private theorem translate_commute {N : ℕ} (j l : Fin N) (v w : (EuclideanSpace ℝ (Fin 3)))
    (P : (Fin N → EuclideanSpace ℝ (Fin 3))) : translate l w (translate j v P) = translate j v (translate l w P) := by
  ext i
  by_cases hj : i = j
  · subst i
    by_cases hl : j = l
    · subst l; simp [translate, add_comm, add_left_comm]
    · simp [translate, hl, Ne.symm hl]
  · by_cases hl : i = l
    · subst i; simp [translate, hj, Ne.symm hj]
    · simp [translate, hj, hl]

private theorem b_translate_same {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (j : Fin N)
    (P : (Fin N → EuclideanSpace ℝ (Fin 3))) :
    b hbar m q j (translate j (hbar • q) P) = b hbar m q j P + 2 * a hbar m q := by
  simp [b, a, translate, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  ring

private theorem b_translate_same_minus {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (j : Fin N)
    (P : (Fin N → EuclideanSpace ℝ (Fin 3))) :
    b hbar m q j (translate j (-(hbar • q)) P) = b hbar m q j P - 2 * a hbar m q := by
  simp [b, a, translate, inner_add_right, inner_neg_right, inner_smul_right,
    real_inner_self_eq_norm_sq]
  ring

@[simp] private theorem b_translate_other {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (j l : Fin N)
    (h : j ≠ l) (v : (EuclideanSpace ℝ (Fin 3))) (P : (Fin N → EuclideanSpace ℝ (Fin 3))) :
    b hbar m q j (translate l v P) = b hbar m q j P := by
  simp [b, translate, h]

@[simp] private theorem translate_cancel {N : ℕ} (j : Fin N) (v : (EuclideanSpace ℝ (Fin 3)))
    (P : (Fin N → EuclideanSpace ℝ (Fin 3))) : translate j (-v) (translate j v P) = P := by
  ext i
  by_cases h : i = j
  · subst i; simp [translate]
  · simp [translate, h]

@[simp] private theorem translate_cancel' {N : ℕ} (j : Fin N) (v : (EuclideanSpace ℝ (Fin 3)))
    (P : (Fin N → EuclideanSpace ℝ (Fin 3))) : translate j v (translate j (-v) P) = P := by
  ext i
  by_cases h : i = j
  · subst i; simp [translate]
  · simp [translate, h]

private noncomputable def weightedPlus {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (j : Fin N) (r : ℕ) :
    Module.End ℂ ((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ) :=
  LinearMap.mulLeft ℂ (fun P => ((b hbar m q j P + a hbar m q : ℝ) : ℂ)^r) * shift j (hbar • q)

private noncomputable def weightedMinus {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (j : Fin N) (t : ℕ) :
    Module.End ℂ ((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ) :=
  LinearMap.mulLeft ℂ (fun P => ((a hbar m q - b hbar m q j P : ℝ) : ℂ)^t) * shift j (-(hbar • q))

private theorem scalar_cancellation (x y : ℂ) (r t : ℕ) :
    x^r * (-x)^t - (-y)^t * y^r = (-1 : ℂ)^t * (x^(r+t)-y^(r+t)) := by
  rw [neg_pow x t, neg_pow y t, pow_add, pow_add]
  ring

private theorem weighted_same_commutator {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3)))
    (j : Fin N) (r t : ℕ) :
    Bracket.bracket (weightedPlus hbar m q j r) (weightedMinus hbar m q j t) =
      LinearMap.mulLeft ℂ (fun P => (-1 : ℂ)^t *
        (((b hbar m q j P + a hbar m q : ℝ) : ℂ)^(r+t) -
         ((b hbar m q j P - a hbar m q : ℝ) : ℂ)^(r+t))) := by
  ext ψ P
  have hs (j : Fin N) (v : EuclideanSpace ℝ (Fin 3)) (ψ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ)
      (P : Fin N → EuclideanSpace ℝ (Fin 3)) : shift j v ψ P = ψ (translate j v P) := rfl
  simp only [Ring.lie_def, weightedPlus, weightedMinus, LinearMap.sub_apply, Pi.sub_apply,
    Module.End.mul_apply, LinearMap.mulLeft_apply, Pi.mul_apply, hs, translate_cancel,
    translate_cancel', b_translate_same, b_translate_same_minus]
  push_cast
  have h1 : (a hbar m q : ℂ) - ((b hbar m q j P : ℂ) + 2 * a hbar m q) =
      -((b hbar m q j P : ℂ) + a hbar m q) := by ring
  have h2 : (b hbar m q j P : ℂ) - 2 * a hbar m q + a hbar m q =
      (b hbar m q j P : ℂ) - a hbar m q := by ring
  rw [h1, h2]
  rw [show (a hbar m q : ℂ) - b hbar m q j P =
      -((b hbar m q j P : ℂ) - a hbar m q) by ring]
  rw [← mul_assoc, ← mul_assoc, ← sub_mul, scalar_cancellation]

private theorem weighted_other_commutator {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3)))
    (j l : Fin N) (h : j ≠ l) (r t : ℕ) :
    Bracket.bracket (weightedPlus hbar m q j r) (weightedMinus hbar m q l t) = 0 := by
  ext ψ P
  have hs (j : Fin N) (v : EuclideanSpace ℝ (Fin 3)) (ψ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ)
      (P : Fin N → EuclideanSpace ℝ (Fin 3)) : shift j v ψ P = ψ (translate j v P) := rfl
  simp only [Ring.lie_def, weightedPlus, weightedMinus, LinearMap.sub_apply, Pi.sub_apply,
    Module.End.mul_apply, LinearMap.mulLeft_apply, Pi.mul_apply, hs, LinearMap.zero_apply, Pi.zero_apply,
    b_translate_other hbar m q j l h, b_translate_other hbar m q l j (Ne.symm h)]
  rw [translate_commute]
  ring

private theorem iterate_rho {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (r : ℕ) :
    (delta m)^[r] (rho (N := N) hbar q) = ∑ j : Fin N, weightedPlus hbar m q j r := by
  rw [rho, iterate_delta_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact iterate_delta_shift_plus hbar m q j r

private theorem iterate_rhoDag {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (t : ℕ) :
    (delta m)^[t] (rhoDag (N := N) hbar q) = ∑ j : Fin N, weightedMinus hbar m q j t := by
  rw [rhoDag, iterate_delta_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact iterate_delta_shift_minus hbar m q j t

private theorem commutator_sums {N : ℕ} (X Y : Fin N → Module.End ℂ ((Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ)) :
    Bracket.bracket (∑ j, X j) (∑ l, Y l) = ∑ j, ∑ l, Bracket.bracket (X j) (Y l) := by
  simp only [Ring.lie_def, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]

private theorem nested_commutator_identity {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3)))
    (r t : ℕ) :
    Bracket.bracket ((delta m)^[r] (rho (N := N) hbar q)) ((delta m)^[t] (rhoDag (N := N) hbar q)) =
      LinearMap.mulLeft ℂ (fun P => (-1 : ℂ)^t * ∑ j : Fin N,
        (((b hbar m q j P + a hbar m q : ℝ) : ℂ)^(r+t) -
          ((b hbar m q j P - a hbar m q : ℝ) : ℂ)^(r+t))) := by
  classical
  rw [iterate_rho, iterate_rhoDag, commutator_sums]
  have hd (j : Fin N) : ∑ l : Fin N,
      Bracket.bracket (weightedPlus hbar m q j r) (weightedMinus hbar m q l t) =
      Bracket.bracket (weightedPlus hbar m q j r) (weightedMinus hbar m q j t) := by
    apply Finset.sum_eq_single j
    · intro l _ hl
      exact weighted_other_commutator hbar m q j l (Ne.symm hl) r t
    · simp
  simp_rw [hd, weighted_same_commutator]
  ext ψ P
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.mulLeft_apply, Pi.mul_apply]
  rw [Finset.mul_sum, Finset.sum_mul]

private theorem operator_identity {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (k ell : ℕ)
    (h : ell ≤ 2*k+1) :
    C (N := N) hbar m q k ell = LinearMap.mulLeft ℂ (fun P => (F hbar m q k ell P : ℂ)) := by
  unfold C
  rw [nested_commutator_identity, Nat.sub_add_cancel h]
  congr 1
  funext P
  simp [F]



open D5.S3.Quantum.KineticMoments.IsotropicAverage
private def FiniteMoments {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3)))) (k : ℕ) : Prop :=
  ∀ i ≤ k, ∀ j : Fin N, Integrable (fun P => ‖P j‖^(2*i)) ν

def FiniteTopMoment {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3)))) (k : ℕ) : Prop :=
  ∀ j : Fin N, Integrable (fun P => ‖P j‖^(2*k)) ν

noncomputable def momentumMoment {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3)))) (i : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j : Fin N, ∫ P, ‖P j‖^(2*i) ∂ν

noncomputable def prefactor (N k ell : ℕ) (hbar : ℝ) : ℂ :=
  (-1 : ℂ)^(k+ell+1) * (hbar / (2 * N) : ℂ) * (Complex.I / hbar)^(2*k+2)

noncomputable def target {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3)))
    (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3)))) (k : ℕ) : ℝ :=
  (hbar * ‖q‖^2 / (2*m))^(2*k+1) / (2*k+2) *
    ∑ i ∈ Finset.range (k+1),
      ((2*k+2).choose (2*i+1) : ℝ) * (2 / (hbar * ‖q‖))^(2*i) * momentumMoment ν i

def claim : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ (hbar m : ℝ), 0 < hbar → 0 < m →
  ∀ (q : (EuclideanSpace ℝ (Fin 3))), q ≠ 0 → ∀ (k ell : ℕ), ell ≤ 2*k+1 →
    C (N := N) hbar m q k ell = LinearMap.mulLeft ℂ (fun P => (F hbar m q k ell P : ℂ)) ∧
    ∀ (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3)))), IsProbabilityMeasure ν → IsIsotropic ν →
      FiniteTopMoment ν k →
      prefactor N k ell hbar * (∫ P, F hbar m q k ell P ∂ν : ℝ) =
        (target hbar m q ν k : ℂ)

private theorem pow_le_one_add_pow (x : ℝ) (hx : 0 ≤ x) (a b : ℕ) (hab : a ≤ b) :
    x^a ≤ 1+x^b := by
  by_cases h : x ≤ 1
  · exact (pow_le_one₀ hx h).trans (le_add_of_nonneg_right (pow_nonneg hx b))
  · have h1 : 1 ≤ x := (lt_of_not_ge h).le
    exact (pow_le_pow_right₀ h1 hab).trans (le_add_of_nonneg_left (by norm_num))

private theorem finiteMoments_of_top {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3))))
    [IsProbabilityMeasure ν] (k : ℕ) (hm : FiniteTopMoment ν k) : FiniteMoments ν k := by
  intro i hi j
  apply ((integrable_const (1 : ℝ)).add (hm j)).mono'
  · exact (by fun_prop : Continuous (fun P : (Fin N → EuclideanSpace ℝ (Fin 3)) => ‖P j‖^(2*i))).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro P
    simpa [norm_pow] using pow_le_one_add_pow ‖P j‖ (norm_nonneg _) (2*i) (2*k)
      (Nat.mul_le_mul_left 2 hi)

private theorem sum_pairs (f : ℕ → ℝ) (k : ℕ) :
    ∑ j ∈ Finset.range (2*k), f j =
      ∑ i ∈ Finset.range k, (f (2*i) + f (2*i+1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1) = (2*k+1)+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

private theorem odd_binomial (a b : ℝ) (k : ℕ) :
    (b+a)^(2*k+1) - (b-a)^(2*k+1) =
      2 * ∑ i ∈ Finset.range (k+1),
        ((2*k+1).choose (2*i) : ℝ) * a^(2*k+1-2*i) * b^(2*i) := by
  rw [sub_eq_add_neg b a, add_pow, add_pow, ← Finset.sum_sub_distrib,
    show 2*k+1+1 = 2*(k+1) by omega, sum_pairs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by simpa using (Finset.mem_range.mp hi)
  have he : 2*k+1-2*i = 2*(k-i)+1 := by omega
  have ho : 2*k+1-(2*i+1) = 2*(k-i) := by omega
  simp only [neg_pow a (2*k+1-2*i), neg_pow a (2*k+1-(2*i+1)), he, ho]
  simp [pow_add, pow_mul]
  ring

private theorem binomial_ratio (k i : ℕ) :
    ((2*k+1).choose (2*i) : ℝ) / (2*i+1) =
      ((2*k+2).choose (2*i+1) : ℝ) / (2*k+2) := by
  have h := Nat.add_one_mul_choose_eq (2*k+1) (2*i)
  have hcast : (2*k+2 : ℝ) * ((2*k+1).choose (2*i) : ℝ) =
      ((2*k+2).choose (2*i+1) : ℝ) * (2*i+1) := by exact_mod_cast h
  have hi : (2*i+1 : ℝ) ≠ 0 := by positivity
  have hk : (2*k+2 : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith [hcast]

private theorem prefactor_sign (k ell : ℕ) :
    (-1 : ℂ)^(k+ell+1) * (-1 : ℂ)^(k+1) * (-1 : ℂ)^ell = 1 := by
  rw [← pow_add, ← pow_add, show (k+ell+1)+(k+1)+ell = 2*(k+ell+1) by omega]
  simp [pow_mul]

private theorem prefactor_cancel (N k ell : ℕ) (hbar : ℝ) (hh : hbar ≠ 0) :
    prefactor N k ell hbar * (-1 : ℂ)^ell = 1 / (2*N*(hbar : ℂ)^(2*k+1)) := by
  have hhC : (hbar : ℂ) ≠ 0 := by exact_mod_cast hh
  have hI : Complex.I^(2*k+2) = (-1 : ℂ)^(k+1) := by
    rw [show 2*k+2 = 2*(k+1) by omega, pow_mul, Complex.I_sq]
  have hhP : (hbar : ℂ)^(2*k+2) = (hbar : ℂ)^(2*k+1) * hbar := by
    rw [show 2*k+2 = (2*k+1)+1 by omega, pow_succ]
  unfold prefactor
  rw [div_pow, hI, hhP]
  calc
    (-1 : ℂ)^(k+ell+1) * ((hbar : ℂ)/(2*N)) *
        ((-1 : ℂ)^(k+1) / ((hbar : ℂ)^(2*k+1) * hbar)) * (-1 : ℂ)^ell =
      ((-1 : ℂ)^(k+ell+1) * (-1 : ℂ)^(k+1) * (-1 : ℂ)^ell) *
        ((hbar : ℂ)/(2*N) / ((hbar : ℂ)^(2*k+1) * hbar)) := by ring
    _ = 1 / (2*N*(hbar : ℂ)^(2*k+1)) := by
      rw [prefactor_sign, one_mul]
      simp [div_eq_mul_inv, hhC, mul_assoc, mul_left_comm, mul_comm]

private theorem kinematic_scaling (h m t : ℝ) (hh : h ≠ 0) (hm : m ≠ 0) (ht : t ≠ 0)
    (s r : ℕ) :
    (h^2*t^2/(2*m))^s * (h/m)^r * t^r =
      h^(s+r) * (h*t^2/(2*m))^(s+r) * (2/(h*t))^r := by
  have h1 : h^2*t^2/(2*m) = h*(h*t^2/(2*m)) := by ring
  have h2 : h*(h*t^2/(2*m))*(2/(h*t)) = (h/m)*t := by
    field_simp
  calc
    _ = (h*(h*t^2/(2*m)))^s * (h*(h*t^2/(2*m))*(2/(h*t)))^r := by
      rw [h1, h2, mul_pow]
      ring
    _ = _ := by simp only [pow_add, mul_pow]; ring

private theorem coefficient_scaling (h m t : ℝ) (hh : h ≠ 0) (hm : m ≠ 0) (ht : t ≠ 0)
    (k i : ℕ) (hi : i ≤ k) :
    ((2*k+1).choose (2*i) : ℝ) * (h^2*t^2/(2*m))^(2*k+1-2*i) * (h/m)^(2*i) *
      (t^(2*i)/(2*i+1 : ℝ)) =
      h^(2*k+1) * ((h*t^2/(2*m))^(2*k+1)/(2*k+2 : ℝ) *
        ((2*k+2).choose (2*i+1) : ℝ) * (2/(h*t))^(2*i)) := by
  have hn : (2*k+1-2*i)+(2*i) = 2*k+1 := by omega
  have hp := kinematic_scaling h m t hh hm ht (2*k+1-2*i) (2*i)
  rw [hn] at hp
  calc
    _ = (((2*k+1).choose (2*i) : ℝ)/(2*i+1 : ℝ)) *
        ((h^2*t^2/(2*m))^(2*k+1-2*i)*(h/m)^(2*i)*t^(2*i)) := by ring
    _ = _ := by rw [hp, binomial_ratio]; ring

private noncomputable def rawCoefficient (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (k i : ℕ) : ℝ :=
  ((2*k+1).choose (2*i) : ℝ) * (a hbar m q)^(2*k+1-2*i) * (hbar/m)^(2*i)

private theorem multiplier_expansion {N : ℕ} (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (k ell : ℕ)
    (P : (Fin N → EuclideanSpace ℝ (Fin 3))) :
    F hbar m q k ell P = (-1 : ℝ)^ell * 2 *
      ∑ i ∈ Finset.range (k+1), rawCoefficient hbar m q k i *
        ∑ j : Fin N, ⟪q, P j⟫^(2*i) := by
  unfold F
  simp_rw [odd_binomial]
  rw [← Finset.mul_sum, ← mul_assoc]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [rawCoefficient, b, mul_pow]
  ring

private theorem multiplier_integral {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3))))
    (k : ℕ) (hm : FiniteMoments ν k) (hν : IsIsotropic ν)
    (hbar m : ℝ) (q : (EuclideanSpace ℝ (Fin 3))) (ell : ℕ) :
    (∫ P, F hbar m q k ell P ∂ν) = (-1 : ℝ)^ell * 2 *
      ∑ i ∈ Finset.range (k+1), rawCoefficient hbar m q k i *
        (‖q‖^(2*i)/(2*i+1 : ℝ)) * ∑ j : Fin N, ∫ P, ‖P j‖^(2*i) ∂ν := by
  have hI i (hi : i ∈ Finset.range (k+1)) (j : Fin N) :=
    integrable_directional ν j i q (hm i (by simpa using Finset.mem_range.mp hi) j)
  simp_rw [multiplier_expansion]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul, integral_finsetSum]
    · simp_rw [isotropic_average ν hν _ i q (hm i (by simpa using Finset.mem_range.mp hi) _)]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · intro j _
      exact hI i hi j
  · intro i hi
    apply Integrable.const_mul
    exact integrable_finsetSum Finset.univ (fun j _ => hI i hi j)

private theorem momentumMoment_sum {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3)))) (hN : N ≠ 0)
    (i : ℕ) : (∑ j : Fin N, ∫ P, ‖P j‖^(2*i) ∂ν) = (N : ℝ)*momentumMoment ν i := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  simp [momentumMoment, hn]

private theorem integral_normalized {N : ℕ} (ν : Measure ((Fin N → EuclideanSpace ℝ (Fin 3)))) (hN : N ≠ 0)
    (k : ℕ) (hmom : FiniteMoments ν k) (hν : IsIsotropic ν)
    (hbar m : ℝ) (hh : hbar ≠ 0) (hm : m ≠ 0) (q : (EuclideanSpace ℝ (Fin 3))) (hq : q ≠ 0)
    (ell : ℕ) :
    (∫ P, F hbar m q k ell P ∂ν) =
      (-1 : ℝ)^ell * 2 * N * hbar^(2*k+1) * target hbar m q ν k := by
  rw [multiplier_integral ν k hmom hν]
  simp_rw [momentumMoment_sum ν hN]
  unfold target
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hscale := coefficient_scaling hbar m ‖q‖ hh hm (norm_ne_zero_iff.mpr hq)
    k i (by simpa using Finset.mem_range.mp hi)
  unfold rawCoefficient a
  linear_combination ((-1 : ℝ)^ell * 2 * (N : ℝ) * momentumMoment ν i) * hscale

theorem result : claim := by
  intro N hN hbar m hh hm q hq k ell hell
  constructor
  · exact operator_identity hbar m q k ell hell
  · intro ν hprob hν hmom
    letI : IsProbabilityMeasure ν := hprob
    have hmom := finiteMoments_of_top ν k hmom
    have hn : N ≠ 0 := by omega
    have hnC : (N : ℂ) ≠ 0 := by exact_mod_cast hn
    have hhC : (hbar : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    rw [integral_normalized ν hn k hmom hν hbar m hh.ne' hm.ne' q hq ell]
    push_cast
    calc
      prefactor N k ell hbar * ((-1 : ℂ)^ell * 2 * N * (hbar : ℂ)^(2*k+1) *
          (target hbar m q ν k : ℂ)) =
        (prefactor N k ell hbar * (-1 : ℂ)^ell) *
          (2 * N * (hbar : ℂ)^(2*k+1) * (target hbar m q ν k : ℂ)) := by ring
      _ = _ := by
        rw [prefactor_cancel N k ell hbar hh.ne']
        field_simp


end D5.S3.Quantum.KineticMoments.OddMoment

#print axioms D5.S3.Quantum.KineticMoments.OddMoment.result
