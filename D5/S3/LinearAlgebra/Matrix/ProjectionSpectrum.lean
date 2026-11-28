/- GID: D5/S3/LinearAlgebra/Matrix/ProjectionSpectrum
   generality: G
   mirror-B: none(waiver:covered-by-hyperfinite-type-ii1-factor-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite complex projection spectra and their coordinate cutoff classification. -/

import OmegaBuild.Commands
import D5.S3.LinearAlgebra.Matrix.TensorIdentity
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-! Omega original.
Finite complex projection spectra and their coordinate cutoff classification. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.MatrixProjectionSpectrum

open Matrix
open Omega.MatrixTensorIdentity (Mat)

/-- A diagonal projection on the first `k` coordinates. -/
def rankProjection (d k : ℕ) : Mat d :=
  diagonal (fun i => if (i : ℕ) < k then 1 else 0)

theorem rankProjection_trace {d k : ℕ} (hk : k ≤ d) :
    trace (rankProjection d k) = (k : ℂ) := by
  have hfilter :
      Finset.univ.filter (fun i : Fin d => (i : ℕ) < k) =
        Finset.univ.map (Fin.castLEEmb hk) := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    exact ⟨fun hi => ⟨⟨i, hi⟩, Fin.ext rfl⟩,
      fun ⟨j, hj⟩ => hj ▸ j.isLt⟩
  simp only [rankProjection, trace, diag_apply, diagonal_apply_eq]
  rw [← Finset.sum_filter, hfilter]
  simp

private theorem projection_eigenvalue {d : ℕ} {p : Mat d} (hp : IsStarProjection p)
    (i : Fin d) : (show p.IsHermitian from hp.isSelfAdjoint).eigenvalues i = 0 ∨ (show p.IsHermitian from hp.isSelfAdjoint).eigenvalues i = 1 := by
  let hP : p.IsHermitian := hp.isSelfAdjoint
  let e := Unitary.conjStarAlgAut ℂ (Mat d) (star hP.eigenvectorUnitary)
  have hdiag : e p = diagonal (RCLike.ofReal ∘ hP.eigenvalues) :=
    hP.conjStarAlgAut_star_eigenvectorUnitary
  have hm : e p * e p = e p := by rw [← map_mul, hp.isIdempotentElem.eq]
  rw [hdiag, diagonal_mul_diagonal] at hm
  have hi := congrArg (fun a : Mat d => a i i) hm
  simp only [diagonal_apply_eq, Function.comp_apply] at hi
  change (hP.eigenvalues i : ℂ) * (hP.eigenvalues i : ℂ) = (hP.eigenvalues i : ℂ) at hi
  have hr : hP.eigenvalues i * hP.eigenvalues i = hP.eigenvalues i := by
    exact_mod_cast hi
  rcases mul_eq_zero.mp (show hP.eigenvalues i * (hP.eigenvalues i - 1) = 0 by
    rw [mul_sub, mul_one, hr, sub_self]) with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

private theorem binaryAntitone_cutoff {d : ℕ} (f : Fin d → ℝ) (hm : Antitone f)
    (hb : ∀ i, f i = 0 ∨ f i = 1) :
    ∃ k ≤ d, ∀ i, f i = if (i : ℕ) < k then 1 else 0 := by
  let s := Finset.univ.filter fun i => f i = 1
  refine ⟨s.card, (Finset.card_filter_le ..).trans_eq (Fintype.card_fin d), fun i => ?_⟩
  rcases hb i with hi | hi
  · have hs : s ⊆ Finset.Iio i := by
      intro j hj
      have hj' : f j = 1 := (Finset.mem_filter.mp hj).2
      apply Finset.mem_Iio.mpr
      by_contra! hn
      linarith [hm hn, hi, hj']
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iio] at hc
    simp [hi, not_lt_of_ge hc]
  · have hs : Finset.Iic i ⊆ s := by
      intro j hj
      have hj' := hm (Finset.mem_Iic.mp hj)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hb j).resolve_left ?_⟩
      linarith
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iic] at hc
    simp [hi, show (i : ℕ) < s.card by omega]

theorem projection_cutoff {d : ℕ} {p : Mat d} (hp : IsStarProjection p) :
    ∃ k ≤ d, (∀ i, (show p.IsHermitian from hp.isSelfAdjoint).eigenvalues i =
      if ((finCongr (Fintype.card_fin d) ((Fintype.equivOfCardEq
        (Fintype.card_fin (Fintype.card (Fin d)))).symm i)) : ℕ) < k then 1 else 0) ∧ trace p = (k : ℂ) := by
  let hP : p.IsHermitian := hp.isSelfAdjoint
  let e := finCongr (Fintype.card_fin d)
  let E : Fin (Fintype.card (Fin d)) ≃ Fin d := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d)))
  let f : Fin d → ℝ := hP.eigenvalues₀ ∘ e.symm
  have hf (i : Fin d) : f i = hP.eigenvalues (E (e.symm i)) := by
    simp [f, IsHermitian.eigenvalues, E]
  obtain ⟨k, hk, h⟩ := binaryAntitone_cutoff f
    (fun i j hij => hP.eigenvalues₀_antitone (show e.symm i ≤ e.symm j from hij))
    (fun i => hf i ▸ projection_eigenvalue hp (E (e.symm i)))
  have H (i : Fin d) : hP.eigenvalues i = if ((e (E.symm i)) : ℕ) < k then 1 else 0 := by
    simpa [hf] using h (e (E.symm i))
  refine ⟨k, hk, H, ?_⟩
  rw [hP.trace_eq_sum_eigenvalues]
  change (∑ i, (hP.eigenvalues i : ℂ)) = _
  simp_rw [H, apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero]
  trans ∑ i : Fin d, if (i : ℕ) < k then (1 : ℂ) else 0
  · exact (E.symm.trans e).sum_comp (fun i => if (i : ℕ) < k then (1 : ℂ) else 0)
  · simpa [rankProjection, trace] using rankProjection_trace (d := d) hk

end Omega.MatrixProjectionSpectrum
