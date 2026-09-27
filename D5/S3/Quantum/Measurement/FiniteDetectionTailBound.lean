/- GID: D5/S3/Quantum/Measurement/FiniteDetectionTailBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/FiniteDetectionTailBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Survival beyond the dark weight has a geometric operator tail and finite mean. -/
import D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.Measurement.FiniteDetectionTailBound
open Filter Matrix Metric
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder Topology
open D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit
theorem finite_detection_tail_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℂ) (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1) :
    ∃ g : ℝ, 0 < g ∧ g ≤ 1 ∧
      (∀ m : ℕ, 0 ≤ (Qᴴ) ^ (m * d) * Q ^ (m * d) - darkProjection Q L ∧
        (Qᴴ) ^ (m * d) * Q ^ (m * d) - darkProjection Q L ≤
          (1 - g) ^ m • (1 - darkProjection Q L)) ∧
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
        ρ.PosSemidef → ρ.trace = 1 → darkProjection Q L * ρ = 0 →
          Summable (fun N : ℕ => (ρ * ((Qᴴ) ^ N * Q ^ N)).trace.re) ∧
          ∑' N : ℕ, (ρ * ((Qᴴ) ^ N * Q ^ N)).trace.re ≤ (d : ℝ) / g := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨1, zero_lt_one, le_rfl, ?_, ?_⟩
    · intro m
      exact ⟨le_of_eq (Subsingleton.elim _ _), le_of_eq (Subsingleton.elim _ _)⟩
    · intro ρ _ htrace _
      have : False := by simpa [Matrix.trace] using htrace
      exact this.elim
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
  letI : NeZero d := ⟨hd⟩
  let P := darkProjection Q L
  let Pc := 1 - P
  obtain ⟨g, _c, hgpos, hgle, _hc_nonneg, _hc_le_one, _hc_step, hP_le, _hfactor,
    _hPc_nonneg, _hcontraction, _hsurvival_norm, _hgap, _hblock, _hc_iter, _hc_bound,
    _hiterated, hquotient⟩ :=
    dark_block_contraction Q L hcomp hd
  change ∀ N, P ≤ (Qᴴ) ^ N * Q ^ N at hP_le
  change ∀ N, (Qᴴ) ^ N * Q ^ N - P ≤ (1 - g) ^ (N / d) • Pc at hquotient
  let a : ℝ := 1 - g
  have ha_nonneg : 0 ≤ a := by
    exact sub_nonneg.mpr hgle
  have ha_lt : a < 1 := by
    exact sub_lt_self 1 hgpos
  have htail : ∀ N, 0 ≤ (Qᴴ) ^ N * Q ^ N - P ∧
      (Qᴴ) ^ N * Q ^ N - P ≤ a ^ (N / d) • Pc := by
    intro N
    let z := (Qᴴ) ^ N * Q ^ N - P
    have hHpos : z.PosSemidef := by
      exact (sub_nonneg.mpr (hP_le N)).posSemidef
    constructor
    · exact hHpos.nonneg
    · simpa only [a] using hquotient N
  refine ⟨g, hgpos, hgle, ?_, ?_⟩
  · intro m
    have hm := htail (m * d)
    have hmd : m * d / d = m := by rw [Nat.mul_comm, Nat.mul_div_right m (Nat.pos_of_ne_zero hd)]
    rw [hmd] at hm
    simpa only [P, Pc, a] using hm
  · intro ρ hρ htrace hsupp
    have hρP : (ρ * P).trace = 0 := by rw [Matrix.trace_mul_comm, hsupp, Matrix.trace_zero]
    have hρPc : (ρ * Pc).trace.re = 1 := by
      simp only [Pc, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re,
        htrace, hρP, Complex.one_re, Complex.zero_re, sub_zero]
    have hterm_nonneg : ∀ N, 0 ≤ (ρ * ((Qᴴ) ^ N * Q ^ N)).trace.re := by
      intro N
      have hH := RHLinalg.trace_mul_nonneg_of_posSemidef hρ (htail N).1.posSemidef
      have heq : (ρ * ((Qᴴ) ^ N * Q ^ N)).trace.re =
          (ρ * ((Qᴴ) ^ N * Q ^ N - P)).trace.re := by
        simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hρP, sub_zero]
      rwa [heq]
    have hterm_le : ∀ N,
        (ρ * ((Qᴴ) ^ N * Q ^ N)).trace.re ≤ a ^ (N / d) := by
      intro N
      have hdiff := RHLinalg.trace_mul_nonneg_of_posSemidef hρ
        (Matrix.le_iff.mp (htail N).2)
      have heq : (ρ * ((Qᴴ) ^ N * Q ^ N)).trace.re =
          (ρ * ((Qᴴ) ^ N * Q ^ N - P)).trace.re := by
        simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hρP, sub_zero]
      rw [heq]
      simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul] at hdiff
      change 0 ≤ (a ^ (N / d) • (ρ * Pc).trace -
        ((ρ * ((Qᴴ) ^ N * Q ^ N)).trace - (ρ * P).trace)).re at hdiff
      simp only [Complex.sub_re, Complex.smul_re, hρPc, hρP, Complex.zero_re,
        smul_eq_mul, mul_one, sub_zero] at hdiff
      linarith
    have hgeom : Summable (fun m : ℕ => a ^ m) := summable_geometric_of_lt_one ha_nonneg ha_lt
    have hprod : Summable (fun p : ℕ × Fin d => a ^ p.1) := by
      rw [summable_prod_of_nonneg (fun p => pow_nonneg ha_nonneg p.1)]
      constructor
      · exact fun _ => (hasSum_fintype _).summable
      · simpa only [tsum_fintype, Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using
          hgeom.mul_left (d : ℝ)
    have hmajor : Summable (fun N : ℕ => a ^ (N / d)) := by
      change Summable (fun N : ℕ => a ^ ((Nat.divModEquiv d N).1))
      exact hprod.comp_injective (Nat.divModEquiv d).injective
    have hseries : Summable (fun N : ℕ => (ρ * ((Qᴴ) ^ N * Q ^ N)).trace.re) :=
      Summable.of_nonneg_of_le hterm_nonneg hterm_le hmajor
    have hsum_le := hseries.tsum_le_tsum hterm_le hmajor
    refine ⟨hseries, hsum_le.trans_eq ?_⟩
    calc
      ∑' N : ℕ, a ^ (N / d) = ∑' p : ℕ × Fin d, a ^ p.1 := by
        change (∑' N : ℕ, a ^ (Nat.divModEquiv d N).1) = _
        exact (Nat.divModEquiv d).tsum_eq (fun p : ℕ × Fin d => a ^ p.1)
      _ = ∑' m : ℕ, ∑' _i : Fin d, a ^ m := hprod.tsum_prod
      _ = ∑' m : ℕ, (d : ℝ) * a ^ m := by simp
      _ = (d : ℝ) * ∑' m : ℕ, a ^ m := tsum_mul_left
      _ = (d : ℝ) * (1 - a)⁻¹ := by rw [tsum_geometric_of_lt_one ha_nonneg ha_lt]
      _ = (d : ℝ) / g := by simp only [a, sub_sub_cancel, div_eq_mul_inv]
#print axioms finite_detection_tail_bound
end D5.S3.Quantum.Measurement.FiniteDetectionTailBound
