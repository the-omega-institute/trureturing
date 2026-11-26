module

public import OmegaBuild.Commands
public import Mathlib.MeasureTheory.Integral.Pi

compile_only_with_mathlib

/-!
Omega original.

The integral of a finite product of measurable coordinate functions under a
product of sigma-finite measures is the product of their integrals.
-/

@[expose] public section

open MeasureTheory Finset Function
open scoped BigOperators ENNReal Classical

noncomputable section
set_option autoImplicit false

namespace Omega.MeasureTheory

set_option backward.isDefEq.respectTransparency false in
lemma lintegral_fin_prod {n : ℕ} {E : Fin n → Type*} {mE : ∀ i, MeasurableSpace (E i)} (μ : (i : Fin n) → Measure (E i)) [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)), f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i) ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) :=
        by
        rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]; simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂μ i.succ := by
        rw [lintegral_prod_mul (μ := μ 0) (ν := Measure.pi (fun i : Fin n => μ i.succ)) (f := f 0) (g := fun (x : (i : Fin n) → E i.succ) => ∏ i : Fin n, f i.succ (x i)) (hf 0).aemeasurable
            (by exact (Finset.measurable_prod _ (fun i _ => (hf i.succ).comp (measurable_pi_apply i))).aemeasurable),
          ih _ _ (fun i => hf i.succ)]
      _ = _ := by exact Eq.symm (Fin.prod_univ_succAbove (fun i => ∫⁻ (x : E i), f i x ∂μ i) 0)


end Omega.MeasureTheory
