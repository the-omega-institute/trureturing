/- GID: D5/S3/Quantum/Measurement/GeneralInstrumentResidualTailContraction
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/GeneralInstrumentResidualTailContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Residual survival effects contract geometrically and have a unique dominated sum. -/

import D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction

open Matrix Filter Topology
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit

variable {d : ℕ} {α ι : Type} [Fintype α] [Fintype ι]

/-- Subtracting the maximal fixed survival effect leaves a geometrically contracting positive tail.
Its sum solves the residual Poisson equation and is the unique solution dominated by the residual
effect. -/
theorem residual_tail_contraction (Q : α → Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ i, (L i)ᴴ * L i = 1)
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : Tendsto (survival Q) atTop (𝓝 F)) :
    (∀ n, survival Q n - F = (noClickDual Q)^[n] (1 - F) ∧
      0 ≤ survival Q n - F ∧ survival Q n - F ≤ 1 - F) ∧
    (1 - F ≠ 0 → ∃ M : ℕ, 1 ≤ M ∧ ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      survival Q M - F ≤ q • (1 - F) ∧
      (∀ n, survival Q n - F ≤ q ^ (n / M) • (1 - F)) ∧
      Summable (fun n => survival Q n - F) ∧
      let T := ∑' n, (survival Q n - F)
      0 ≤ T ∧ T ≤ ((M : ℝ) / (1 - q)) • (1 - F) ∧
        T - noClickDual Q T = 1 - F ∧
        (∀ k, 0 ≤ T - ∑ n ∈ Finset.range (k * M), (survival Q n - F) ∧
          T - ∑ n ∈ Finset.range (k * M), (survival Q n - F) ≤
            ((M : ℝ) * q ^ k / (1 - q)) • (1 - F)) ∧
        ∀ (X : Matrix (Fin d) (Fin d) ℂ) (c : ℝ),
          X - noClickDual Q X = 1 - F → 0 ≤ X → X ≤ c • (1 - F) → X = T) := by
  classical
  obtain ⟨F', hF', hchain, hF'0, hF'1, hfix, -⟩ :=
    survival_tendsto_maximal_fixed_effect Q L hcomp
  have hF'eq : F' = F := tendsto_nhds_unique hF' hF
  subst F'
  let R : Matrix (Fin d) (Fin d) ℂ := 1 - F
  let Rn : ℕ → Matrix (Fin d) (Fin d) ℂ := fun n => survival Q n - F
  have hsub : ∀ X Y, noClickDual Q (X - Y) = noClickDual Q X - noClickDual Q Y := by
    intro X Y
    simp only [noClickDual, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]
  have hresidual : ∀ n, Rn n = (noClickDual Q)^[n] R := by
    intro n
    induction n with
    | zero => simp [Rn, R, survival]
    | succ n ih =>
        rw [Function.iterate_succ_apply', ← ih]
        change noClickDual Q (survival Q n) - F = noClickDual Q (survival Q n - F)
        rw [hsub, hfix]
  have hRn0 : ∀ n, 0 ≤ Rn n := fun n => sub_nonneg.mpr (hchain n).2.2.2
  have hRnR : ∀ n, Rn n ≤ R := fun n => by
    exact sub_le_sub_right (hchain n).2.2.1 F
  refine ⟨fun n => ⟨hresidual n, hRn0 n, hRnR n⟩, fun hRne => ?_⟩
  have hR0 : 0 ≤ R := sub_nonneg.mpr hF'1
  have hRpsd : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hR0
  have hfinite : (spectrum ℝ R ∩ Set.Ioi 0).Finite :=
    R.finite_real_spectrum.subset Set.inter_subset_left
  let _ : Nontrivial (Matrix (Fin d) (Fin d) ℂ) := nontrivial_of_ne R 0 hRne
  have hnorm_mem : ‖R‖ ∈ spectrum ℝ R := CStarAlgebra.norm_mem_spectrum_of_nonneg hR0
  have hpositive_nonempty : (spectrum ℝ R ∩ Set.Ioi 0).Nonempty :=
    ⟨‖R‖, hnorm_mem, norm_pos_iff.mpr hRne⟩
  obtain ⟨r₀, hr₀mem, hr₀min⟩ :=
    hfinite.isCompact.exists_isMinOn hpositive_nonempty continuousOn_id
  have hr₀ : 0 < r₀ := hr₀mem.2
  let P := cfc (fun x : ℝ => if 0 < x then (1 : ℝ) else 0) R
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ R) :=
    R.finite_real_spectrum.continuousOn f
  have hr₀P : r₀ • P ≤ R := by
    rw [Matrix.le_iff]
    have hcalc : R - r₀ • P =
        cfc (fun x : ℝ => x - r₀ * (if 0 < x then (1 : ℝ) else 0)) R := by
      rw [cfc_sub _ _ R (hcont _) (hcont _), cfc_id' ℝ R hRpsd.isHermitian.isSelfAdjoint,
        cfc_const_mul r₀ _ R (hcont _)]
    rw [hcalc, ← Matrix.nonneg_iff_posSemidef]
    apply cfc_nonneg
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hR0 hx
    by_cases hxp : 0 < x
    · simp only [if_pos hxp, mul_one]
      exact sub_nonneg.mpr (hr₀min ⟨hx, hxp⟩)
    · simp only [if_neg hxp, mul_zero, sub_zero]
      exact hx0
  have hRP : R * P = R := by
    calc
      R * P = cfc (fun x : ℝ => x) R *
          cfc (fun x : ℝ => if 0 < x then (1 : ℝ) else 0) R := by
            rw [cfc_id' ℝ R hRpsd.isHermitian.isSelfAdjoint]
      _ = cfc (fun x : ℝ => x * (if 0 < x then (1 : ℝ) else 0)) R :=
        (cfc_mul _ _ R (hcont _) (hcont _)).symm
      _ = cfc (fun x : ℝ => x) R := by
        apply cfc_congr
        intro x hx
        have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hR0 hx
        by_cases hxp : 0 < x
        · simp [hxp]
        · have hxz : x = 0 := le_antisymm (not_lt.mp hxp) hx0
          simp [hxz]
      _ = R := cfc_id' ℝ R hRpsd.isHermitian.isSelfAdjoint
  have hRcomp : R * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hRP, sub_self]
  have hPstar : Pᴴ = P := (cfc_predicate _ R : IsSelfAdjoint P).star_eq
  have hPP : P * P = P := by
    calc
      P * P = cfc ((fun x : ℝ => if 0 < x then (1 : ℝ) else 0) *
          (fun x : ℝ => if 0 < x then (1 : ℝ) else 0)) R :=
        (cfc_mul _ _ R (hcont _) (hcont _)).symm
      _ = P := by
        apply cfc_congr
        intro x _
        by_cases hxp : 0 < x <;> simp [hxp]
  have hsupport : ∀ X : Matrix (Fin d) (Fin d) ℂ, 0 ≤ X → X ≤ R → X = P * X * P := by
    intro X hX0 hXR
    have hX : X.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hX0
    have hkernel : ∀ w : Fin d → ℂ, R *ᵥ w = 0 → X *ᵥ w = 0 := by
      intro w hRw
      apply (hX.dotProduct_mulVec_zero_iff w).mp
      have hdiff : (R - X).PosSemidef := Matrix.le_iff.mp hXR
      have hXquad : 0 ≤ star w ⬝ᵥ (X *ᵥ w) := hX.dotProduct_mulVec_nonneg w
      have hdiffquad : 0 ≤ star w ⬝ᵥ ((R - X) *ᵥ w) :=
        hdiff.dotProduct_mulVec_nonneg w
      have hsum : star w ⬝ᵥ (X *ᵥ w) + star w ⬝ᵥ ((R - X) *ᵥ w) = 0 := by
        rw [Matrix.sub_mulVec, dotProduct_sub, hRw, dotProduct_zero]
        abel
      exact (add_eq_zero_iff_of_nonneg hXquad hdiffquad).mp hsum |>.1
    have hright : X * (1 - P) = 0 := by
      rw [Matrix.ext_iff_mulVec]
      intro v
      rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
      apply hkernel
      rw [Matrix.mulVec_mulVec, hRcomp, Matrix.zero_mulVec]
    have hleft : (1 - P) * X = 0 := by
      have hstar := congrArg star hright
      simpa only [star_eq_conjTranspose, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPstar,
        hX.isHermitian.eq, Matrix.conjTranspose_zero] using hstar
    have hXP : X * P = X :=
      (sub_eq_zero.mp (by simpa only [Matrix.mul_sub, Matrix.mul_one] using hright)).symm
    have hPX : P * X = X :=
      (sub_eq_zero.mp (by simpa only [Matrix.sub_mul, Matrix.one_mul] using hleft)).symm
    calc
      X = P * X := hPX.symm
      _ = P * (X * P) := by rw [hXP]
      _ = P * X * P := (Matrix.mul_assoc _ _ _).symm
  have hcompare : ∀ X : Matrix (Fin d) (Fin d) ℂ, 0 ≤ X → X ≤ R →
      X ≤ (‖X‖ / r₀) • R := by
    intro X hX0 hXR
    have hX : X.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hX0
    have hXnorm : X ≤ ‖X‖ • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        hX.isHermitian.isSelfAdjoint.le_algebraMap_norm_self
    have hXPnorm : X ≤ ‖X‖ • P := by
      calc
        X = P * X * P := hsupport X hX0 hXR
        _ ≤ P * (‖X‖ • (1 : Matrix (Fin d) (Fin d) ℂ)) * P :=
          (show IsSelfAdjoint P from hPstar).conjugate_le_conjugate hXnorm
        _ = ‖X‖ • P := by
          rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hPP]
    calc
      X ≤ ‖X‖ • P := hXPnorm
      _ = (‖X‖ / r₀) • (r₀ • P) := by
        rw [smul_smul, div_mul_cancel₀ _ hr₀.ne']
      _ ≤ (‖X‖ / r₀) • R :=
        smul_le_smul_of_nonneg_left hr₀P (div_nonneg (norm_nonneg X) hr₀.le)
  have hRnlim : Tendsto Rn atTop (𝓝 0) := by
    simpa only [Rn, sub_self] using hF.sub_const F
  have hnormlim : Tendsto (fun n => ‖Rn n‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hRnlim
  have hevent : ∀ᶠ n in atTop, ‖Rn n‖ < r₀ / 2 :=
    (tendsto_order.1 hnormlim).2 _ (half_pos hr₀)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  let M := max 1 N
  have hM1 : 1 ≤ M := le_max_left _ _
  have hNM : N ≤ M := le_max_right _ _
  have hnormM : ‖Rn M‖ / r₀ ≤ (1 / 2 : ℝ) := by
    have hle : ‖Rn M‖ ≤ r₀ / 2 := (hN M hNM).le
    apply (div_le_iff₀ hr₀).2
    nlinarith
  have hcontract : Rn M ≤ (1 / 2 : ℝ) • R := by
    calc
      Rn M ≤ (‖Rn M‖ / r₀) • R := hcompare (Rn M) (hRn0 M) (hRnR M)
      _ ≤ (1 / 2 : ℝ) • R := smul_le_smul_of_nonneg_right hnormM hR0
  let q : ℝ := 1 / 2
  have hq0 : 0 < q := by simp [q]
  have hq1 : q < 1 := by norm_num [q]
  have hcontractq : Rn M ≤ q • R := by simpa only [q] using hcontract
  have hpos : ∀ X : Matrix (Fin d) (Fin d) ℂ, X.PosSemidef →
      (noClickDual Q X).PosSemidef :=
    fun X hX => posSemidef_sum _ fun a _ => hX.conjTranspose_mul_mul_same (Q a)
  have hmono : Monotone (noClickDual Q) := by
    intro X Y hXY
    rw [Matrix.le_iff, ← hsub]
    exact hpos _ (Matrix.le_iff.mp hXY)
  have hmonoIt : ∀ k, Monotone (noClickDual Q)^[k] := fun k => hmono.iterate k
  have hsmulA : ∀ (c : ℝ) X, noClickDual Q (c • X) = c • noClickDual Q X := by
    intro c X
    simp only [noClickDual, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  have hsmulIt : ∀ k (c : ℝ) X,
      (noClickDual Q)^[k] (c • X) = c • (noClickDual Q)^[k] X := by
    intro k c X
    exact ((show Function.Semiconj (fun Y => c • Y) (noClickDual Q) (noClickDual Q) from
      fun Y => (hsmulA c Y).symm).iterate_right k X).symm
  have hRnSucc : ∀ n, Rn (n + 1) = noClickDual Q (Rn n) := by
    intro n
    rw [hresidual, hresidual, Function.iterate_succ_apply']
  have hRnShift : ∀ n k, Rn (n + k) = (noClickDual Q)^[k] (Rn n) := by
    intro n k
    rw [hresidual, hresidual, Nat.add_comm, Function.iterate_add_apply]
  have hRnAnti : Antitone Rn := by
    apply antitone_nat_of_succ_le
    intro n
    exact sub_le_sub_right (hchain n).2.1 F
  have hsmulMono : ∀ (c : ℝ), 0 ≤ c →
      ∀ X Y : Matrix (Fin d) (Fin d) ℂ, X ≤ Y → c • X ≤ c • Y := by
    intro c hc X Y hXY
    exact smul_le_smul_of_nonneg_left hXY hc
  have hblock : ∀ k, Rn (k * M) ≤ q ^ k • R := by
    intro k
    induction k with
    | zero => simp [Rn, R, survival]
    | succ k ih =>
        rw [Nat.succ_mul, hRnShift]
        calc
          (noClickDual Q)^[M] (Rn (k * M)) ≤
              (noClickDual Q)^[M] (q ^ k • R) := hmonoIt M ih
          _ = q ^ k • (noClickDual Q)^[M] R := by
            exact hsmulIt M (q ^ k) R
          _ = q ^ k • Rn M := by rw [← hresidual M]
          _ ≤ q ^ k • (q • R) := hsmulMono _ (pow_nonneg hq0.le k) _ _ hcontractq
          _ = q ^ (k + 1) • R := by rw [smul_smul, pow_succ]
  have hbound : ∀ n, Rn n ≤ q ^ (n / M) • R := by
    intro n
    exact (hRnAnti (Nat.div_mul_le_self n M)).trans (hblock (n / M))
  let _ : NeZero M := ⟨Nat.ne_of_gt hM1⟩
  have hqprod : Summable (fun p : ℕ × Fin M => q ^ p.1) := by
    refine (summable_prod_of_nonneg (fun _ => pow_nonneg hq0.le _)).2 ⟨?_, ?_⟩
    · intro n
      exact Summable.of_finite
    · simpa using (summable_geometric_of_lt_one hq0.le hq1).mul_left (M : ℝ)
  have hqfloor : Summable (fun n : ℕ => q ^ (n / M)) := by
    have h := (Nat.divModEquiv M).summable_iff.mpr hqprod
    change Summable (fun n : ℕ => q ^ (n / M)) at h
    exact h
  have hsum : Summable Rn := by
    apply Summable.of_norm_bounded (hqfloor.mul_right ‖R‖)
    intro n
    calc
      ‖Rn n‖ ≤ ‖q ^ (n / M) • R‖ :=
        CStarAlgebra.norm_le_norm_of_nonneg_of_le (hRn0 n) (hbound n)
      _ = q ^ (n / M) * ‖R‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0.le _)]
  have hqfloorSum : ∑' n : ℕ, q ^ (n / M) = (M : ℝ) / (1 - q) := by
    calc
      ∑' n : ℕ, q ^ (n / M) = ∑' p : ℕ × Fin M, q ^ p.1 :=
        (Nat.divModEquiv M).tsum_eq (fun p : ℕ × Fin M => q ^ p.1)
      _ = ∑' n : ℕ, ∑' _ : Fin M, q ^ n := hqprod.tsum_prod
      _ = ∑' n : ℕ, (M : ℝ) * q ^ n := by
        apply tsum_congr
        intro n
        simp
      _ = (M : ℝ) * ∑' n : ℕ, q ^ n := tsum_mul_left
      _ = (M : ℝ) / (1 - q) := by
        rw [tsum_geometric_of_lt_one hq0.le hq1]
        ring
  have hpartialUpper : ∀ N, ∑ n ∈ Finset.range N, Rn n ≤
      ((M : ℝ) / (1 - q)) • R := by
    intro N
    calc
      ∑ n ∈ Finset.range N, Rn n ≤
          ∑ n ∈ Finset.range N, q ^ (n / M) • R :=
        Finset.sum_le_sum fun n _ => hbound n
      _ = (∑ n ∈ Finset.range N, q ^ (n / M)) • R :=
        (Finset.sum_smul).symm
      _ ≤ ((M : ℝ) / (1 - q)) • R := by
        apply smul_le_smul_of_nonneg_right _ hR0
        rw [← hqfloorSum]
        exact hqfloor.sum_le_tsum (Finset.range N) fun n _ => pow_nonneg hq0.le _
  let T : Matrix (Fin d) (Fin d) ℂ := ∑' n, Rn n
  have hpartialTend : Tendsto (fun N => ∑ n ∈ Finset.range N, Rn n) atTop (𝓝 T) :=
    hsum.hasSum.tendsto_sum_nat
  have hT0 : 0 ≤ T := by
    simpa only [T] using tsum_nonneg hRn0
  have hTupper : T ≤ ((M : ℝ) / (1 - q)) • R := by
    apply le_of_tendsto hpartialTend
    exact Eventually.of_forall hpartialUpper
  let Alinear : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
    { toFun := noClickDual Q
      map_add' := by
        intro X Y
        simp only [noClickDual, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c X
        change noClickDual Q (c • X) = c • noClickDual Q X
        simp only [noClickDual, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum] }
  let Acont := Alinear.toContinuousLinearMap
  have hAT : noClickDual Q T = ∑' n, Rn (n + 1) := by
    calc
      noClickDual Q T = Acont T := rfl
      _ = ∑' n, Acont (Rn n) := Acont.map_tsum hsum
      _ = ∑' n, Rn (n + 1) := by
        apply tsum_congr
        intro n
        exact (hRnSucc n).symm
  have hTeq : T - noClickDual Q T = R := by
    have hsplit : T = R + noClickDual Q T := by
      calc
        T = Rn 0 + ∑' n, Rn (n + 1) := hsum.tsum_eq_zero_add
        _ = R + noClickDual Q T := by rw [hresidual 0, hAT]; rfl
    exact sub_eq_iff_eq_add.mpr hsplit
  have hgeomPartial : ∀ K, ∑ j ∈ Finset.range K, q ^ j ≤ 1 / (1 - q) := by
    intro K
    norm_num [q]
    exact sum_geometric_two_le K
  have hblockSegment : ∀ k K, ∑ n ∈ Finset.range (K * M), Rn (n + k * M) ≤
      ((M : ℝ) * q ^ k * ∑ j ∈ Finset.range K, q ^ j) • R := by
    intro k K
    induction K with
    | zero => simp
    | succ K ih =>
        have hnew : ∑ r ∈ Finset.range M, Rn (K * M + r + k * M) ≤
            ((M : ℝ) * (q ^ k * q ^ K)) • R := by
          calc
            ∑ r ∈ Finset.range M, Rn (K * M + r + k * M) ≤
                ∑ _r ∈ Finset.range M, q ^ (k + K) • R := by
              apply Finset.sum_le_sum
              intro r hr
              have hrM : r < M := Finset.mem_range.mp hr
              have hindex : (k + K) * M ≤ K * M + r + k * M := by
                calc
                  (k + K) * M = k * M + K * M := Nat.add_mul _ _ _
                  _ = K * M + k * M := Nat.add_comm _ _
                  _ ≤ K * M + r + k * M := by omega
              exact (hRnAnti hindex).trans (hblock (k + K))
            _ = ((M : ℝ) * (q ^ k * q ^ K)) • R := by
              simp only [Finset.sum_const, Finset.card_range,
                ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, pow_add]
        calc
          ∑ n ∈ Finset.range (Nat.succ K * M), Rn (n + k * M) =
              (∑ n ∈ Finset.range (K * M), Rn (n + k * M)) +
                ∑ r ∈ Finset.range M, Rn (K * M + r + k * M) := by
            rw [Nat.succ_mul, Finset.sum_range_add]
          _ ≤ ((M : ℝ) * q ^ k * ∑ j ∈ Finset.range K, q ^ j) • R +
              ((M : ℝ) * (q ^ k * q ^ K)) • R := add_le_add ih hnew
          _ = ((M : ℝ) * q ^ k * ∑ j ∈ Finset.range (Nat.succ K), q ^ j) • R := by
            rw [← add_smul, Finset.sum_range_succ]
            congr 1
            ring
  have htailPartial : ∀ k N, ∑ n ∈ Finset.range N, Rn (n + k * M) ≤
      ((M : ℝ) * q ^ k / (1 - q)) • R := by
    intro k N
    have hN : N ≤ N * M := Nat.le_mul_of_pos_right N (Nat.pos_of_ne_zero (NeZero.ne M))
    calc
      ∑ n ∈ Finset.range N, Rn (n + k * M) ≤
          ∑ n ∈ Finset.range (N * M), Rn (n + k * M) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN)
          fun n _ _ => hRn0 (n + k * M)
      _ ≤ ((M : ℝ) * q ^ k * ∑ j ∈ Finset.range N, q ^ j) • R :=
        hblockSegment k N
      _ ≤ ((M : ℝ) * q ^ k / (1 - q)) • R := by
        apply smul_le_smul_of_nonneg_right _ hR0
        calc
          (M : ℝ) * q ^ k * ∑ j ∈ Finset.range N, q ^ j ≤
              (M : ℝ) * q ^ k * (1 / (1 - q)) :=
            mul_le_mul_of_nonneg_left (hgeomPartial N)
              (mul_nonneg (Nat.cast_nonneg M) (pow_nonneg hq0.le k))
          _ = (M : ℝ) * q ^ k / (1 - q) := by ring
  have htail : ∀ k, 0 ≤ T - ∑ n ∈ Finset.range (k * M), Rn n ∧
      T - ∑ n ∈ Finset.range (k * M), Rn n ≤
        ((M : ℝ) * q ^ k / (1 - q)) • R := by
    intro k
    have htailsum : Summable (fun n => Rn (n + k * M)) :=
      (summable_nat_add_iff (k * M)).2 hsum
    have htailTend : Tendsto (fun N => ∑ n ∈ Finset.range N, Rn (n + k * M))
        atTop (𝓝 (∑' n, Rn (n + k * M))) := htailsum.hasSum.tendsto_sum_nat
    have htail0 : 0 ≤ ∑' n, Rn (n + k * M) := by
      exact tsum_nonneg fun n => hRn0 (n + k * M)
    have htailUpper : (∑' n, Rn (n + k * M)) ≤
        ((M : ℝ) * q ^ k / (1 - q)) • R := by
      apply le_of_tendsto htailTend
      exact Eventually.of_forall fun N => htailPartial k N
    have htailEq : T - ∑ n ∈ Finset.range (k * M), Rn n =
        ∑' n, Rn (n + k * M) := by
      change (∑' n, Rn n) - ∑ n ∈ Finset.range (k * M), Rn n =
        ∑' n, Rn (n + k * M)
      rw [← hsum.sum_add_tsum_nat_add (k * M)]
      abel
    rw [htailEq]
    exact ⟨htail0, htailUpper⟩
  have hunique : ∀ (X : Matrix (Fin d) (Fin d) ℂ) (c : ℝ),
      X - noClickDual Q X = R → 0 ≤ X → X ≤ c • R → X = T := by
    intro X c hXeq hX0 hXR
    have hXdecomp : X = R + noClickDual Q X := sub_eq_iff_eq_add.mp hXeq
    have hiterateStep : ∀ k, (noClickDual Q)^[k] X =
        Rn k + (noClickDual Q)^[k + 1] X := by
      intro k
      calc
        (noClickDual Q)^[k] X = (noClickDual Q)^[k] (R + noClickDual Q X) := by
          rw [← hXdecomp]
        _ = (noClickDual Q)^[k] R + (noClickDual Q)^[k] (noClickDual Q X) :=
          iterate_map_add Alinear.toAddMonoidHom k R (noClickDual Q X)
        _ = Rn k + (noClickDual Q)^[k + 1] X := by
          rw [← hresidual k, ← Function.iterate_succ_apply]
    have hiterateX : ∀ k, X = ∑ n ∈ Finset.range k, Rn n +
        (noClickDual Q)^[k] X := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          calc
            X = ∑ n ∈ Finset.range k, Rn n + (noClickDual Q)^[k] X := ih
            _ = ∑ n ∈ Finset.range k, Rn n +
                (Rn k + (noClickDual Q)^[k + 1] X) := by rw [hiterateStep]
            _ = ∑ n ∈ Finset.range (k + 1), Rn n +
                (noClickDual Q)^[k + 1] X := by
              rw [Finset.sum_range_succ]
              abel
    have hrem0 : ∀ k, 0 ≤ (noClickDual Q)^[k] X := by
      intro k
      rw [← iterate_map_zero Alinear.toAddMonoidHom k]
      exact hmonoIt k hX0
    have hremUpper : ∀ k, (noClickDual Q)^[k] X ≤ c • Rn k := by
      intro k
      calc
        (noClickDual Q)^[k] X ≤ (noClickDual Q)^[k] (c • R) := hmonoIt k hXR
        _ = c • (noClickDual Q)^[k] R := hsmulIt k c R
        _ = c • Rn k := by rw [hresidual]
    have hscaledLim : Tendsto (fun k => c • Rn k) atTop (𝓝 0) := by
      simpa using hRnlim.const_smul c
    have hscaledNormLim : Tendsto (fun k => ‖c • Rn k‖) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mp hscaledLim
    have hremLim : Tendsto (fun k => (noClickDual Q)^[k] X) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      apply squeeze_zero (fun k => norm_nonneg ((noClickDual Q)^[k] X)) _ hscaledNormLim
      intro k
      exact CStarAlgebra.norm_le_norm_of_nonneg_of_le (hrem0 k) (hremUpper k)
    have hconstT : Tendsto (fun _ : ℕ => X) atTop (𝓝 (T + 0)) :=
      (hpartialTend.add hremLim).congr'
        (Eventually.of_forall fun k => (hiterateX k).symm)
    simpa using hconstT
  exact ⟨M, hM1, q, hq0, hq1, hcontractq, hbound, by simpa [Rn] using hsum,
    by simpa only [T, R, Rn] using
      And.intro hT0 (And.intro hTupper (And.intro hTeq (And.intro htail hunique)))⟩

#print axioms residual_tail_contraction

end D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction
