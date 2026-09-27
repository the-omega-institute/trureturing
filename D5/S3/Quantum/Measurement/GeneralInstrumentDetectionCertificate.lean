/- GID: D5/S3/Quantum/Measurement/GeneralInstrumentDetectionCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/GeneralInstrumentDetectionCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Without a definite dark direction the survival effects of a general instrument decay geometrically in blocks of d rounds. -/

import D5.S3.Quantum.Measurement.GeneralInstrumentNoDarkDirection
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.GeneralInstrumentDetectionCertificate

open Matrix Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit
open D5.S3.Quantum.Measurement.GeneralInstrumentNoDarkDirection

variable {d : ℕ} {α ι : Type} [Fintype α] [Fintype ι]

/-- **Uniform detection certificate.** For no-click Kraus operators `Q_a` and click Kraus operators
`L_i` with `∑ₐ Q_aᴴ Q_a + ∑ᵢ L_iᴴ L_i = I` on `ℂᵈ`: if the stable dark layer `D_d` is zero, some
`g > 0` satisfies `g I ≤ I - S_d`; and for every such `g`, `S_{md} ≤ (1 - g)ᵐ I` for all `m`, and
for every density matrix `ρ` the survival probabilities `Tr(ρ S_N)` are summable with
`∑_N Tr(ρ S_N) ≤ d / g`. -/
theorem detection_certificate (Q : α → Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ) (hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ i, (L i)ᴴ * L i = 1) :
    (darkLayer Q L d = ⊥ →
      ∃ g : ℝ, 0 < g ∧ (g : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ 1 - survival Q d) ∧
    ∀ g : ℝ, 0 < g → (g : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ 1 - survival Q d →
      (∀ m, survival Q (m * d) ≤ (((1 - g) ^ m : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) ∧
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → ρ.trace = 1 →
        Summable (fun N => (ρ * survival Q N).trace.re) ∧
          ∑' N, (ρ * survival Q N).trace.re ≤ d / g := by
  classical
  obtain ⟨F, hF, hchain, -⟩ := survival_tendsto_maximal_fixed_effect Q L hcomp
  have htfae := no_dark_direction_tfae Q L hcomp F hF
  -- degenerate dimension: every Loewner inequality holds
  have htriv : d = 0 → ∀ A B : Matrix (Fin d) (Fin d) ℂ, A ≤ B := by
    rintro rfl A B
    exact le_of_subsingleton
  -- the dual map is positive, monotone and homogeneous, and so are its iterates
  have hpos : ∀ X : Matrix (Fin d) (Fin d) ℂ, X.PosSemidef → (noClickDual Q X).PosSemidef :=
    fun X hX => posSemidef_sum _ fun a _ => hX.conjTranspose_mul_mul_same (Q a)
  have hsub : ∀ X Y, noClickDual Q (X - Y) = noClickDual Q X - noClickDual Q Y := by
    intro X Y
    simp only [noClickDual, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]
  have hsmulA : ∀ (c : ℂ) X, noClickDual Q (c • X) = c • noClickDual Q X := by
    intro c X
    simp only [noClickDual, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  have hmono : Monotone (noClickDual Q) := by
    intro X Y h
    rw [Matrix.le_iff, ← hsub]
    exact hpos _ (Matrix.le_iff.mp h)
  have hmonoIt : ∀ k, Monotone (noClickDual Q)^[k] := fun k => hmono.iterate k
  have hsmulIt : ∀ k (c : ℂ) X, (noClickDual Q)^[k] (c • X) = c • (noClickDual Q)^[k] X := by
    intro k c X
    exact ((show Function.Semiconj (fun Y => c • Y) (noClickDual Q) (noClickDual Q) from
      fun Y => (hsmulA c Y).symm).iterate_right k X).symm
  have hshift : ∀ n k, survival Q (n + k) = (noClickDual Q)^[k] (survival Q n) := by
    intro n k
    induction k with
    | zero => rfl
    | succ k ih => rw [← add_assoc, Function.iterate_succ_apply', ← ih]; rfl
  have hsmul_mono : ∀ (c : ℝ), 0 ≤ c → ∀ X Y : Matrix (Fin d) (Fin d) ℂ, X ≤ Y →
      (c : ℂ) • X ≤ (c : ℂ) • Y := by
    intro c hc X Y h
    exact smul_le_smul_of_nonneg_left h (Complex.zero_le_real.mpr hc)
  refine ⟨fun hD => ?_, fun g hg hgle => ?_⟩
  · -- (i) a positive lower bound for the quadratic form of `I - S_d`
    have hPD : (1 - survival Q d).PosDef := (htfae.out 0 2).mp hD
    by_cases hd0 : d = 0
    · exact ⟨1, one_pos, htriv hd0 _ _⟩
    · -- a strictly positive element dominates a positive multiple of the identity
      haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd0⟩⟩
      have hsp : IsStrictlyPositive (1 - survival Q d) := hPD.isStrictlyPositive
      obtain ⟨r, hr, hle⟩ :=
        (CFC.exists_pos_algebraMap_le_iff hsp.isSelfAdjoint).2 fun x hx => hsp.spectrum_pos hx
      refine ⟨r, hr, ?_⟩
      rwa [Algebra.algebraMap_eq_smul_one, RCLike.real_smul_eq_coe_smul (K := ℂ)] at hle
  · -- (ii) block decay of the survival effects
    have hSd : survival Q d ≤ (((1 - g : ℝ)) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      rw [Matrix.le_iff]
      have h := Matrix.le_iff.mp hgle
      have heq : (((1 - g : ℝ)) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - survival Q d =
          1 - survival Q d - (g : ℂ) • 1 := by
        push_cast
        rw [sub_smul, one_smul]
        abel
      rw [heq]
      exact h
    have hdecay : ∀ m, survival Q (m * d) ≤ (((1 - g) ^ m : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      by_cases hd0 : d = 0
      · exact fun m => htriv hd0 _ _
      have hg1 : 0 ≤ 1 - g := by
        have h := Matrix.le_iff.mp (le_trans (hchain d).1 hSd)
        have hd : 0 < d := Nat.pos_of_ne_zero hd0
        have hdiag := h.diag_nonneg (i := ⟨0, hd⟩)
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
          Matrix.zero_apply, smul_eq_mul, mul_one, sub_zero] at hdiag
        exact Complex.zero_le_real.mp hdiag
      intro m
      induction m with
      | zero => simp [survival]
      | succ m ih =>
          rw [Nat.succ_mul, hshift]
          calc (noClickDual Q)^[d] (survival Q (m * d))
              ≤ (noClickDual Q)^[d] ((((1 - g) ^ m : ℝ) : ℂ) • 1) := hmonoIt d ih
            _ = (((1 - g) ^ m : ℝ) : ℂ) • survival Q d := by
                have h0 := hshift 0 d
                rw [zero_add] at h0
                rw [hsmulIt, h0]
                rfl
            _ ≤ (((1 - g) ^ m : ℝ) : ℂ) • ((((1 - g : ℝ)) : ℂ) • 1) :=
                hsmul_mono _ (pow_nonneg hg1 m) _ _ hSd
            _ = (((1 - g) ^ (m + 1) : ℝ) : ℂ) • 1 := by
                rw [smul_smul]; push_cast; ring_nf
    refine ⟨hdecay, fun ρ hρ hρtr => ?_⟩
    -- (iii) summation of the survival probabilities
    have htr_nonneg : ∀ Y : Matrix (Fin d) (Fin d) ℂ, Y.PosSemidef → 0 ≤ (ρ * Y).trace.re :=
      fun Y hY => RHLinalg.trace_mul_nonneg_of_posSemidef hρ hY
    let s : ℕ → ℝ := fun N => (ρ * survival Q N).trace.re
    have hs_nonneg : ∀ N, 0 ≤ s N := fun N =>
      htr_nonneg _ (Matrix.nonneg_iff_posSemidef.mp (hchain N).1)
    have hs_anti : Antitone s := by
      refine antitone_nat_of_succ_le fun N => ?_
      have h := htr_nonneg _ (Matrix.le_iff.mp (hchain N).2.1)
      rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at h
      change s (N + 1) ≤ s N
      linarith
    have hs_block : ∀ m, s (m * d) ≤ (1 - g) ^ m := by
      intro m
      have h := htr_nonneg _ (Matrix.le_iff.mp (hdecay m))
      rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
        hρtr, smul_eq_mul, mul_one] at h
      simp only [Complex.sub_re, Complex.ofReal_re] at h
      change s (m * d) ≤ (1 - g) ^ m
      linarith
    by_cases hd0 : d = 0
    · have hs0 : ∀ N, s N = 0 := fun N => by
        subst hd0
        simp [s, Matrix.trace]
      have hsum : ∀ n, ∑ i ∈ Finset.range n, s i ≤ (d : ℝ) / g := fun n => by
        simp [hs0, hd0]
      exact ⟨summable_of_sum_range_le hs_nonneg hsum, Real.tsum_le_of_sum_range_le hs_nonneg hsum⟩
    have hg1 : 0 ≤ 1 - g := by
      have := le_trans (hs_nonneg (1 * d)) (hs_block 1)
      simpa using this
    have hblocks : ∀ M, ∑ i ∈ Finset.range (M * d), s i ≤ d * ∑ m ∈ Finset.range M, (1 - g) ^ m := by
      intro M
      induction M with
      | zero => simp
      | succ M ih =>
          rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, mul_add]
          refine add_le_add ih ?_
          calc ∑ r ∈ Finset.range d, s (M * d + r)
              ≤ ∑ r ∈ Finset.range d, (1 - g) ^ M :=
                Finset.sum_le_sum fun r _ => le_trans (hs_anti (Nat.le_add_right _ _)) (hs_block M)
            _ = d * (1 - g) ^ M := by simp
    have hgeom : ∀ M, ∑ m ∈ Finset.range M, (1 - g) ^ m ≤ 1 / g := by
      intro M
      have hne : (1 - g) ≠ 1 := by linarith
      rw [geom_sum_eq hne]
      rw [show (1 - g - 1) = -g by ring, div_neg, ← neg_div, neg_sub]
      exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hg1 M]) hg.le
    have hsum : ∀ n, ∑ i ∈ Finset.range n, s i ≤ (d : ℝ) / g := by
      intro n
      have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
      calc ∑ i ∈ Finset.range n, s i ≤ ∑ i ∈ Finset.range (n * d), s i :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_mul_of_pos_right n hd))
              fun i _ _ => hs_nonneg i
        _ ≤ d * ∑ m ∈ Finset.range n, (1 - g) ^ m := hblocks n
        _ ≤ d * (1 / g) := mul_le_mul_of_nonneg_left (hgeom n) (Nat.cast_nonneg d)
        _ = d / g := by ring
    exact ⟨summable_of_sum_range_le hs_nonneg hsum, Real.tsum_le_of_sum_range_le hs_nonneg hsum⟩

#print axioms detection_certificate

end D5.S3.Quantum.Measurement.GeneralInstrumentDetectionCertificate
