/- GID: D5/S3/Analytic/NullSets/AnalyticZeroSetNull
   generality: G
   mirror-B: D5/B/S3/Analytic/NullSets/AnalyticZeroSetNull
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A nontrivial real analytic function has a Lebesgue null zero set. -/
/- admission_basis: escape-witness
   Direct frozen dependencies: none; all imports are pinned Mathlib.
   ae_ne_zero_of_analytic: proof_shape: content; escape_witness: ae_ne_zero_of_analytic;
   consumers: GenericLieLength.ae_mvPolynomial_ne_zero, PauliRotationCriticalValues.full_rank_ae.
   The dimension induction combines the one-dimensional isolated-zero theorem with Fubini.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16180
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

namespace D5.S3.Analytic.NullSets.AnalyticZeroSetNull

theorem ae_ne_zero_of_analytic {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : AnalyticOnNhd ℝ f Set.univ) {a : Fin n → ℝ} (ha : f a ≠ 0) :
    ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), f x ≠ 0 := by
  classical
  have hR (u : ℝ → ℝ) (hu : AnalyticOnNhd ℝ u Set.univ)
      (b : ℝ) (hb : u b ≠ 0) : ∀ᵐ t ∂volume, u t ≠ 0 := by
    simp -implicitDefEqProofs only [ae_iff, ne_eq, not_not]
    by_contra hz
    obtain ⟨z, hz⟩ := exists_accPt_of_nullSingletonClass (pos_iff_ne_zero.mpr hz)
    exact hb (hu.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ z)
      (accPt_iff_frequently_nhdsNE.mp hz) (Set.mem_univ b))
  induction n with
  | zero =>
    exact Filter.Eventually.of_forall fun x => by
      rw [Subsingleton.elim x a]; exact ha
  | succ n ih =>
    have hc (z : ℝ × (Fin n → ℝ)) :
        AnalyticAt ℝ (fun y : ℝ × (Fin n → ℝ) =>
          (Fin.insertNth 0 y.1 y.2 : Fin (n + 1) → ℝ)) z := by
      apply AnalyticAt.pi
      intro j
      cases j using Fin.cases with
      | zero => simpa -implicitDefEqProofs only [Fin.insertNth_zero', Fin.cons_zero] using
          (analyticAt_fst (𝕜 := ℝ) (p := z))
      | succ j => simpa -implicitDefEqProofs only [Fin.insertNth_zero', Fin.cons_succ, Function.comp_def,
          ContinuousLinearMap.proj_apply] using
          ((ContinuousLinearMap.proj (R := ℝ) j).analyticAt z.2).comp analyticAt_snd
    have hF : AnalyticOnNhd ℝ
        (fun z : ℝ × (Fin n → ℝ) => f (Fin.insertNth 0 z.1 z.2)) Set.univ :=
      fun z _ => (hf _ (Set.mem_univ _)).comp (hc z)
    have hi : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
        f (Fin.insertNth 0 (a 0) x) ≠ 0 :=
      ih (fun x _ => (hF (a 0, x) (Set.mem_univ _)).comp
        (f := fun y : Fin n → ℝ => (a 0, y))
        (analyticAt_const.prod analyticAt_id))
        (a := Fin.removeNth 0 a) (by simpa -implicitDefEqProofs only [Fin.insertNth_self_removeNth] using ha)
    have hi' : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
        ∀ᵐ t ∂volume, f (Fin.insertNth 0 t x) ≠ 0 := by
      filter_upwards [hi] with x hx
      exact hR _ (fun t _ => (hF (t, x) (Set.mem_univ _)).comp
        (f := fun s : ℝ => (s, x))
        (analyticAt_id.prod analyticAt_const)) (a 0) hx
    have hm : MeasurableSet {z : ℝ × (Fin n → ℝ) |
        f (Fin.insertNth 0 z.1 z.2) ≠ 0} :=
      hF.continuous.measurable ((measurableSet_singleton (0 : ℝ)).compl)
    have hp := (Measure.ae_prod_iff_ae_ae hm).2 ((Measure.ae_ae_comm hm).2 hi')
    have ht := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).quasiMeasurePreserving.ae hp
    dsimp only [MeasurableEquiv.piFinSuccAbove] at ht
    simpa -implicitDefEqProofs [Fin.insertNthEquiv, Fin.insertNth_self_removeNth] using ht


end D5.S3.Analytic.NullSets.AnalyticZeroSetNull
