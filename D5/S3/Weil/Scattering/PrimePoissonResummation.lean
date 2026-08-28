/- GID: D5/S3/Weil/Scattering/PrimePoissonResummation
   generality: G
   mirror-B: D5/B/S3/Weil/Scattering/PrimePoissonResummation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime-power translation histories resum exactly to a unitary Poisson resolvent. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-! # Prime Poisson resummation

The translation and Poisson operator below are the source constructions: translation acts on
the real-line `L2` carrier, while the Poisson operator is formed from the two actual resolvents.
The proof supplies the missing local bridge from those resolvents to the bilateral orbit series.

Library-search audit trail (2026-08-29):
* D5 body-shape searches for real-line `Lp` translation, unitary Poisson resolvents, and weighted
  bilateral orbit sums found no existing owner.
* Pinned Mathlib provides `Lp.compMeasurePreservingₗᵢ`, `NormedRing.inverse_one_sub`, and
  `summable_geometric_of_norm_lt_one`; these primitives are applied below.
* No convolution or resolvent-summation theorem matching the public statement was found. -/

open scoped ComplexConjugate

noncomputable section

namespace D5.S3.Weil.Scattering.PrimePoissonResummation

open MeasureTheory

/-- Translation by `a` on complex square-integrable functions over the real line. -/
noncomputable def realTranslation (a : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) := by
  let fMinus : ℝ → ℝ := fun x => x + (-a)
  let fPlus : ℝ → ℝ := fun x => x + a
  have hMinus : MeasurePreserving fMinus volume volume :=
    measurePreserving_add_right volume (-a)
  have hPlus : MeasurePreserving fPlus volume volume :=
    measurePreserving_add_right volume a
  apply LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ fMinus hMinus)
  intro g
  refine ⟨Lp.compMeasurePreservingₗᵢ ℂ fPlus hPlus g, ?_⟩
  change Lp.compMeasurePreserving fMinus hMinus
    (Lp.compMeasurePreserving fPlus hPlus g) = g
  rw [← Lp.compMeasurePreserving_comp_apply g hPlus hMinus]
  have hcomp : fPlus ∘ fMinus = id := by
    funext x
    simp [fMinus, fPlus]
  simpa only [hcomp] using Lp.compMeasurePreserving_id_apply g

/-- The translation equivalence has the source computation rule almost everywhere. -/
theorem realTranslation_ae_eq (a : ℝ) (ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    ⇑(realTranslation a ψ) =ᵐ[volume] fun x => ψ (x - a) := by
  change ⇑(Lp.compMeasurePreserving (fun x : ℝ => x + -a)
    (measurePreserving_add_right volume (-a)) ψ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_compMeasurePreserving ψ
    (measurePreserving_add_right volume (-a))] with x hx
  simpa [sub_eq_add_neg] using hx

/-- The unitary Poisson operator built from the two source resolvents. -/
noncomputable def unitaryPoissonOperator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (r : ℝ) (U : H →L[ℂ] H) : H →L[ℂ] H :=
  ((1 - r ^ 2 : ℝ) : ℂ) •
    (Ring.inverse (1 - (r : ℂ) • U) * Ring.inverse (1 - (r : ℂ) • star U))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma norm_real_smul_unitary_lt_one
    (u : unitary (H →L[ℂ] H)) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖(r : ℂ) • (u : H →L[ℂ] H)‖ < 1 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hnorm : ‖(u : H →L[ℂ] H)‖ ≤ 1 := by
    rw [← Unitary.coe_linearIsometryEquiv_apply u]
    exact (Unitary.linearIsometryEquiv u).toLinearIsometry.norm_toContinuousLinearMap_le
  exact (mul_le_mul_of_nonneg_left hnorm hr0).trans_lt (by simpa using hr1)

private lemma poisson_resolvent_eq_sum
    (u : unitary (H →L[ℂ] H)) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    let U : H →L[ℂ] H := u
    let x : H →L[ℂ] H := (r : ℂ) • U
    let y : H →L[ℂ] H := (r : ℂ) • star U
    let A : H →L[ℂ] H := Ring.inverse (1 - x)
    let B : H →L[ℂ] H := Ring.inverse (1 - y)
    ((1 - r ^ 2 : ℝ) : ℂ) • (A * B) = A + B - 1 := by
  dsimp only
  let U : H →L[ℂ] H := u
  let x : H →L[ℂ] H := (r : ℂ) • U
  let y : H →L[ℂ] H := (r : ℂ) • star U
  let A : H →L[ℂ] H := Ring.inverse (1 - x)
  let B : H →L[ℂ] H := Ring.inverse (1 - y)
  have hUstar : U * star U = 1 := by
    exact u.property.2
  have hxnorm : ‖x‖ < 1 := by
    simpa only [x, U] using norm_real_smul_unitary_lt_one u r hr0 hr1
  have hynorm : ‖y‖ < 1 := by
    simpa only [y, U, Unitary.coe_star] using
      norm_real_smul_unitary_lt_one (star u) r hr0 hr1
  have hxleft : A * (1 - x) = 1 := by
    simp only [A, NormedRing.inverse_one_sub x hxnorm]
    exact (summable_geometric_of_norm_lt_one hxnorm).tsum_pow_mul_one_sub
  have hxright : (1 - x) * A = 1 := by
    simp only [A, NormedRing.inverse_one_sub x hxnorm]
    exact (summable_geometric_of_norm_lt_one hxnorm).one_sub_mul_tsum_pow
  have hyleft : B * (1 - y) = 1 := by
    simp only [B, NormedRing.inverse_one_sub y hynorm]
    exact (summable_geometric_of_norm_lt_one hynorm).tsum_pow_mul_one_sub
  have hyright : (1 - y) * B = 1 := by
    simp only [B, NormedRing.inverse_one_sub y hynorm]
    exact (summable_geometric_of_norm_lt_one hynorm).one_sub_mul_tsum_pow
  have hxy : x * y = ((r ^ 2 : ℝ) : ℂ) • (1 : H →L[ℂ] H) := by
    simp only [x, y, smul_mul_smul, hUstar]
    congr 1
    norm_cast
    ring
  have hmiddle :
      (1 - y) + (1 - x) - (1 - x) * (1 - y) = 1 - x * y := by
    noncomm_ring
  rw [Algebra.smul_def]
  rw [show algebraMap ℂ (H →L[ℂ] H) ((1 - r ^ 2 : ℝ) : ℂ) =
      1 - ((r ^ 2 : ℝ) : ℂ) • (1 : H →L[ℂ] H) by
    simp [map_sub, Algebra.smul_def]]
  calc
    (1 - ((r ^ 2 : ℝ) : ℂ) • (1 : H →L[ℂ] H)) * (A * B) =
        A * ((1 - y) + (1 - x) - (1 - x) * (1 - y)) * B := by
          rw [hmiddle, hxy]
          simp only [Algebra.smul_def]
          simp only [mul_one]
          have hc : Commute
              (1 - algebraMap ℂ (H →L[ℂ] H) ((r ^ 2 : ℝ) : ℂ)) A :=
            (Commute.one_left A).sub_left (Algebra.commutes _ A)
          calc
            (1 - algebraMap ℂ (H →L[ℂ] H) ((r ^ 2 : ℝ) : ℂ)) * (A * B) =
                ((1 - algebraMap ℂ (H →L[ℂ] H) ((r ^ 2 : ℝ) : ℂ)) * A) * B :=
              (mul_assoc _ _ _).symm
            _ = (A * (1 - algebraMap ℂ (H →L[ℂ] H) ((r ^ 2 : ℝ) : ℂ))) * B := by
              rw [hc.eq]
            _ = A * ((1 - algebraMap ℂ (H →L[ℂ] H) ((r ^ 2 : ℝ) : ℂ)) * B) :=
              mul_assoc _ _ _
    _ = A + B - 1 := by
      calc
        A * ((1 - y) + (1 - x) - (1 - x) * (1 - y)) * B =
            A * (1 - y) * B + A * (1 - x) * B -
              A * (1 - x) * (1 - y) * B := by noncomm_ring
        _ = A + B - 1 := by
          simp only [mul_assoc, hxleft, hyright, one_mul, mul_one]

private lemma poisson_resolvent_sub_eq_tsum
    (u : unitary (H →L[ℂ] H)) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    let U : H →L[ℂ] H := u
    let x : H →L[ℂ] H := (r : ℂ) • U
    let y : H →L[ℂ] H := (r : ℂ) • star U
    let A : H →L[ℂ] H := Ring.inverse (1 - x)
    let B : H →L[ℂ] H := Ring.inverse (1 - y)
    ((1 - r ^ 2 : ℝ) : ℂ) • (A * B) - 1 =
      ∑' n : ℕ, (x ^ (n + 1) + y ^ (n + 1)) := by
  dsimp only
  let U : H →L[ℂ] H := u
  let x : H →L[ℂ] H := (r : ℂ) • U
  let y : H →L[ℂ] H := (r : ℂ) • star U
  let A : H →L[ℂ] H := Ring.inverse (1 - x)
  let B : H →L[ℂ] H := Ring.inverse (1 - y)
  have hxnorm : ‖x‖ < 1 := by
    simpa only [x, U] using norm_real_smul_unitary_lt_one u r hr0 hr1
  have hynorm : ‖y‖ < 1 := by
    simpa only [y, U, Unitary.coe_star] using
      norm_real_smul_unitary_lt_one (star u) r hr0 hr1
  have hsx : Summable (fun n : ℕ => x ^ n) :=
    summable_geometric_of_norm_lt_one hxnorm
  have hsy : Summable (fun n : ℕ => y ^ n) :=
    summable_geometric_of_norm_lt_one hynorm
  have hA : A = 1 + ∑' n : ℕ, x ^ (n + 1) := by
    simp only [A]
    rw [NormedRing.inverse_one_sub x hxnorm]
    change (∑' n : ℕ, x ^ n) = 1 + ∑' n : ℕ, x ^ (n + 1)
    rw [← hsx.sum_add_tsum_nat_add 1]
    simp
  have hB : B = 1 + ∑' n : ℕ, y ^ (n + 1) := by
    simp only [B]
    rw [NormedRing.inverse_one_sub y hynorm]
    change (∑' n : ℕ, y ^ n) = 1 + ∑' n : ℕ, y ^ (n + 1)
    rw [← hsy.sum_add_tsum_nat_add 1]
    simp
  have hsxTail : Summable (fun n : ℕ => x ^ (n + 1)) :=
    hsx.comp_injective (i := fun n => n + 1) (by
      intro a b h
      exact Nat.add_right_cancel h)
  have hsyTail : Summable (fun n : ℕ => y ^ (n + 1)) :=
    hsy.comp_injective (i := fun n => n + 1) (by
      intro a b h
      exact Nat.add_right_cancel h)
  have hsum :
      (∑' n : ℕ, (x ^ (n + 1) + y ^ (n + 1))) =
        (∑' n : ℕ, x ^ (n + 1)) + ∑' n : ℕ, y ^ (n + 1) :=
    hsxTail.tsum_add hsyTail
  rw [poisson_resolvent_eq_sum u r hr0 hr1]
  change A + B - 1 - 1 = ∑' n : ℕ, (x ^ (n + 1) + y ^ (n + 1))
  rw [hA, hB]
  rw [hsum]
  abel

private lemma poisson_inner_resummation
    (u : unitary (H →L[ℂ] H)) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ψ : H) :
    let U : H →L[ℂ] H := u
    let A : H →L[ℂ] H := Ring.inverse (1 - (r : ℂ) • U)
    let B : H →L[ℂ] H := Ring.inverse (1 - (r : ℂ) • star U)
    (∑' n : ℕ, (r : ℂ) ^ (n + 1) *
      (inner ℂ ψ ((U ^ (n + 1)) ψ) + inner ℂ ψ (((star U) ^ (n + 1)) ψ))) =
      inner ℂ ψ (((((1 - r ^ 2 : ℝ) : ℂ) • (A * B)) - 1) ψ) := by
  dsimp only
  let U : H →L[ℂ] H := u
  let x : H →L[ℂ] H := (r : ℂ) • U
  let y : H →L[ℂ] H := (r : ℂ) • star U
  let A : H →L[ℂ] H := Ring.inverse (1 - x)
  let B : H →L[ℂ] H := Ring.inverse (1 - y)
  have hxnorm : ‖x‖ < 1 := by
    simpa only [x, U] using norm_real_smul_unitary_lt_one u r hr0 hr1
  have hynorm : ‖y‖ < 1 := by
    simpa only [y, U, Unitary.coe_star] using
      norm_real_smul_unitary_lt_one (star u) r hr0 hr1
  have hsx : Summable (fun n : ℕ => x ^ n) :=
    summable_geometric_of_norm_lt_one hxnorm
  have hsy : Summable (fun n : ℕ => y ^ n) :=
    summable_geometric_of_norm_lt_one hynorm
  have hsxTail : Summable (fun n : ℕ => x ^ (n + 1)) :=
    hsx.comp_injective (i := fun n => n + 1) (by
      intro a b h
      exact Nat.add_right_cancel h)
  have hsyTail : Summable (fun n : ℕ => y ^ (n + 1)) :=
    hsy.comp_injective (i := fun n => n + 1) (by
      intro a b h
      exact Nat.add_right_cancel h)
  have hsum : Summable (fun n : ℕ => x ^ (n + 1) + y ^ (n + 1)) :=
    hsxTail.add hsyTail
  let evalInner : (H →L[ℂ] H) →L[ℂ] ℂ :=
    (innerSL ℂ ψ).comp ((ContinuousLinearMap.apply ℂ H) ψ)
  have hop := poisson_resolvent_sub_eq_tsum u r hr0 hr1
  change ((1 - r ^ 2 : ℝ) : ℂ) • (A * B) - 1 =
    ∑' n : ℕ, (x ^ (n + 1) + y ^ (n + 1)) at hop
  calc
    (∑' n : ℕ, (r : ℂ) ^ (n + 1) *
        (inner ℂ ψ ((U ^ (n + 1)) ψ) + inner ℂ ψ (((star U) ^ (n + 1)) ψ))) =
        ∑' n : ℕ, evalInner (x ^ (n + 1) + y ^ (n + 1)) := by
      apply tsum_congr
      intro n
      simp only [evalInner, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply, map_add,
        x, y, smul_pow, smul_apply, innerSL_apply_apply, inner_smul_right]
      ring
    _ = evalInner (∑' n : ℕ, (x ^ (n + 1) + y ^ (n + 1))) :=
      (evalInner.map_tsum hsum).symm
    _ = evalInner (((1 - r ^ 2 : ℝ) : ℂ) • (A * B) - 1) := by rw [hop]
    _ = inner ℂ ψ (((((1 - r ^ 2 : ℝ) : ℂ) • (A * B)) - 1) ψ) := rfl

/-- The full prime-power translation history is exactly the centered unitary Poisson resolvent. -/
theorem prime_poisson_resummation
    (p : ℕ) (hp : p.Prime) (ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    let r : ℝ := 1 / Real.sqrt p
    let U : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
      realTranslation (Real.log p)
    (-Real.log p : ℂ) *
        (∑' n : ℕ, (r : ℂ) ^ (n + 1) *
          (inner ℂ ψ ((U ^ (n + 1)) ψ) +
            inner ℂ ψ (((star U) ^ (n + 1)) ψ))) =
      (-Real.log p : ℂ) *
        inner ℂ ψ ((unitaryPoissonOperator r U - 1) ψ) := by
  dsimp only
  let r : ℝ := 1 / Real.sqrt p
  let e := realTranslation (Real.log p)
  let u : unitary
      (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) :=
    Unitary.linearIsometryEquiv.symm e
  have hpReal : (1 : ℝ) < p := by
    exact_mod_cast lt_of_lt_of_le (by omega : 1 < 2) hp.two_le
  have hsqrt : (1 : ℝ) < Real.sqrt p :=
    (Real.lt_sqrt zero_le_one).2 (by simpa using hpReal)
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hr1 : r < 1 := by
    dsimp only [r]
    exact (div_lt_one (lt_trans zero_lt_one hsqrt)).2 hsqrt
  have h := poisson_inner_resummation u r hr0 hr1 ψ
  have hU :
      (u : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) = e := rfl
  rw [hU] at h
  change (∑' n : ℕ, (r : ℂ) ^ (n + 1) *
      (inner ℂ ψ (((e : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ]
          Lp ℂ 2 (volume : Measure ℝ)) ^ (n + 1)) ψ) +
        inner ℂ ψ (((star (e : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ]
          Lp ℂ 2 (volume : Measure ℝ))) ^ (n + 1)) ψ))) =
    inner ℂ ψ ((unitaryPoissonOperator r
      (e : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ]
        Lp ℂ 2 (volume : Measure ℝ)) - 1) ψ) at h
  exact congrArg (fun z : ℂ => (-Real.log p : ℂ) * z) h

#print axioms realTranslation_ae_eq
#print axioms prime_poisson_resummation

end D5.S3.Weil.Scattering.PrimePoissonResummation
