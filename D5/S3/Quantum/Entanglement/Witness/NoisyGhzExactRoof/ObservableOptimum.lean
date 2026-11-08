/- GID: D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof/ObservableOptimum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Actual noisy-GHZ ObservableOptimum in the original finite-ensemble semantics. -/


import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.Foundations
import D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof.TwoMeanBound


open scoped BigOperators ComplexOrder MatrixOrder
open _root_.Matrix
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.OccupancyWordSectors (Word)
open D5.S3.Quantum.Information.MultiEntropyPositivityRefutation (IsUnitState)
open D5.S3.Quantum.Recovery.ProductPrefixRigidity (readout)
open D5.S3.Quantum.Entanglement.Witness.NoisyGhzWitnessBoundGap

namespace D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof

noncomputable section

/-- A vector supported on constant computational words, with specified amplitudes. -/
def constantVector {n d : ℕ} (hn : 0 < n) (c : Fin d → ℂ) : Word (Fin d) n → ℂ := by
  classical
  exact fun x => if ∀ i, x i = x ⟨0, hn⟩ then c (x ⟨0, hn⟩) else 0

lemma constantVector_apply {n d : ℕ} (hn : 0 < n) (c : Fin d → ℂ)
    (j : Fin d) : constantVector hn c (fun _ => j) = c j := by
  simp [constantVector]

lemma constantVector_off {n d : ℕ} (hn : 0 < n) (c : Fin d → ℂ)
    (x : Word (Fin d) n) (hx : ¬ ∃ j : Fin d, ∀ i, x i = j) : constantVector hn c x = 0 := by
  have h : ¬ ∀ i, x i = x ⟨0, hn⟩ := by
    intro h; exact hx ⟨_, h⟩
  simp [constantVector, h]

private lemma constantVector_norm {n d : ℕ} (hn : 0 < n) (c : Fin d → ℂ) :
    ∑ x, Complex.normSq (constantVector hn c x) = ∑ j, Complex.normSq (c j) := by
  rw [sum_supported_constants hn _ (by
    intro x hx; rw [constantVector_off hn c x hx]; exact Complex.normSq_zero)]
  simp only [constantVector_apply]

private lemma constantVector_support {n d : ℕ} (hn : 0 < n) (c : Fin d → ℂ) :
    readout (supportProjector n d) (constantVector hn c) = ∑ j, Complex.normSq (c j) := by
  rw [support_expectation, Finset.sum_filter]
  rw [sum_supported_constants hn _ (by
    intro x hx; rw [constantVector_off hn c x hx]; simp)]
  apply Finset.sum_congr rfl
  intro j hj
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simp [constantVector_apply, Finset.image_const]

private lemma basis_overlap {n d : ℕ} (x : Word (Fin d) n) (ψ : Word (Fin d) n → ℂ) :
    Complex.normSq (star (Pi.single x (1 : ℂ)) ⬝ᵥ ψ) = Complex.normSq (ψ x) := by
  classical
  simp [dotProduct, Pi.single_apply, Pi.star_apply]

private lemma constantVector_ghz {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (c : Fin d → ℂ) :
    readout (rankOneDensity (ghz n d)) (constantVector hn c) =
      Complex.normSq (∑ j, c j) / d := by
  have h := ghz_expectation hn hd (constantVector hn c)
  simp only [constantVector_apply] at h
  exact (eq_div_iff (by exact_mod_cast hd.ne')).mpr (by linarith)

/-- The distinguished source vector has one amplitude `α` and `d-1` amplitudes `β`. -/
def chiVector {n d : ℕ} (hn : 0 < n) (j : Fin d) (α β : ℝ) : Word (Fin d) n → ℂ :=
  constantVector hn (fun i => if i = j then (α : ℂ) else (β : ℂ))

private lemma chi_norm {n d : ℕ} (hn : 0 < n) (j : Fin d) (α β : ℝ) :
    ∑ x, Complex.normSq (chiVector hn j α β x) = α^2 + (d - 1 : ℝ) * β^2 := by
  classical
  rw [chiVector, constantVector_norm]
  simp only [apply_ite Complex.normSq, Complex.normSq_ofReal, ← pow_two]
  calc
    (∑ i : Fin d, if i = j then α^2 else β^2) =
        ∑ i : Fin d, (β^2 + if i = j then α^2 - β^2 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> ring
    _ = α^2 + (d - 1 : ℝ) * β^2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring

/-- Source amplitudes, expressed with a single nonnegative cross radical. -/
def optimalAlpha (d : ℕ) (F : ℝ) : ℝ :=
  (Real.sqrt F + Real.sqrt ((d - 1 : ℝ) * (1 - F))) / Real.sqrt d

def optimalBeta (d : ℕ) (F : ℝ) : ℝ :=
  (Real.sqrt F - Real.sqrt ((d - 1 : ℝ) * (1 - F)) / (d - 1 : ℝ)) / Real.sqrt d

lemma optimal_amplitudes {d : ℕ} (hd : 2 ≤ d) {F : ℝ}
    (hF : 1 / (d : ℝ) ≤ F) (hF1 : F ≤ 1) :
    0 ≤ optimalBeta d F ∧ optimalBeta d F ≤ optimalAlpha d F ∧
      (optimalAlpha d F)^2 + (d - 1 : ℝ) * (optimalBeta d F)^2 = 1 ∧
      (optimalAlpha d F + (d - 1 : ℝ) * optimalBeta d F)^2 / d = F ∧
      twoMeanValue d F 1 = 1 - (optimalAlpha d F)^2 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hd1 : 0 < (d - 1 : ℝ) := by linarith
  have hf0 : 0 ≤ F := (one_div_nonneg.mpr hdpos.le).trans hF
  have hcross : 0 ≤ (d - 1 : ℝ) * (1 - F) := mul_nonneg hd1.le (sub_nonneg.mpr hF1)
  have hS := Real.sq_sqrt hf0
  have hC := Real.sq_sqrt hcross
  have hD := Real.sq_sqrt hdpos.le
  have hDpos := Real.sqrt_pos.mpr hdpos
  have hbeta : Real.sqrt ((d - 1 : ℝ) * (1 - F)) / (d - 1 : ℝ) ≤ Real.sqrt F := by
    apply (div_le_iff₀ hd1).mpr
    have hm : 1 ≤ (d : ℝ) * F := by simpa only [mul_comm] using (div_le_iff₀ hdpos).mp hF
    have hs0 := Real.sqrt_nonneg F
    have hc0 := Real.sqrt_nonneg ((d - 1 : ℝ) * (1 - F))
    have hsquare : (Real.sqrt F * (d - 1 : ℝ))^2 -
        (Real.sqrt ((d - 1 : ℝ) * (1 - F)))^2 = (d - 1 : ℝ) * ((d : ℝ) * F - 1) := by
      rw [mul_pow, hS, hC]
      ring
    apply (sq_le_sq₀ hc0 (mul_nonneg hs0 hd1.le)).mp
    apply sub_nonneg.mp
    rw [hsquare]
    exact mul_nonneg hd1.le (sub_nonneg.mpr hm)
  refine ⟨div_nonneg (sub_nonneg.mpr hbeta) hDpos.le, ?_, ?_, ?_, ?_⟩
  · unfold optimalBeta optimalAlpha
    apply div_le_div_of_nonneg_right _ hDpos.le
    have hc := Real.sqrt_nonneg ((d - 1 : ℝ) * (1 - F))
    have hq := div_nonneg hc hd1.le
    linarith
  · unfold optimalAlpha optimalBeta
    field_simp [hdpos.ne', hd1.ne', hDpos.ne']
    linear_combination (d : ℝ) * (d - 1) * hS + (d : ℝ) * hC - (d - 1 : ℝ) * hD
  · unfold optimalAlpha optimalBeta
    field_simp [hdpos.ne', hd1.ne', hDpos.ne']
    linear_combination (d : ℝ)^2 * hS - (d : ℝ) * F * hD
  · unfold twoMeanValue optimalAlpha
    have hmul : Real.sqrt ((d - 1 : ℝ) * F * (1 - F)) =
        Real.sqrt F * Real.sqrt ((d - 1 : ℝ) * (1 - F)) := by
      rw [← Real.sqrt_mul hf0]
      congr 1
      ring
    rw [hmul]
    field_simp [hdpos.ne', hd1.ne', hDpos.ne']
    <;> nlinarith

/-- The original single-witness conjugate with an arbitrary feasible mean. -/
def epsilonWitness (n d : ℕ) (w : ℝ) : ℝ :=
  sSup {t : ℝ | ∃ r : ℝ, t = r * w - hatE n d r}

lemma epsilonO_bridge (n d : ℕ) (p : ℝ) :
    epsilonO n d p = epsilonWitness n d (witnessValue n d p) := rfl

private lemma witness_pure_bounds {n d : ℕ} (hn : 0 < n) (hd : 1 ≤ d)
    (ψ : Word (Fin d) n → ℂ) (hψ : IsUnitState ψ) :
    -(1 : ℝ) ≤ readout (witnessOp n d) ψ ∧ readout (witnessOp n d) ψ ≤ 1 := by
  obtain ⟨hf, hfy, hy⟩ := pure_means_triangle hn (by omega) ψ hψ
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 ≤ 1 / (d : ℝ) := one_div_nonneg.mpr (by linarith)
  have hden1 : 1 / (d : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hdR
  simp only [witnessOp, expectation_sub, expectation_smul]
  have hprod := mul_le_mul_of_nonneg_left hy hden
  have hy0 : 0 ≤ readout (supportProjector n d) ψ := hf.trans hfy
  have hz := mul_nonneg hden hy0
  constructor <;> nlinarith

private lemma hat_values_nonempty {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) (r : ℝ) :
    {t : ℝ | ∃ ψ φ, IsUnitState ψ ∧ IsBiseparable φ ∧
      t = readout (r • witnessOp n d + rankOneDensity φ) ψ - 1}.Nonempty := by
  let φ : Word (Fin d) n → ℂ := Pi.single (fun _ => (⟨0, hd⟩ : Fin d)) (1 : ℂ)
  exact ⟨_, φ, φ, basis_unit _, computational_biseparable hn _, rfl⟩

private lemma hat_values_bdd {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) (r : ℝ) :
    BddAbove {t : ℝ | ∃ ψ φ, IsUnitState ψ ∧ IsBiseparable φ ∧
      t = readout (r • witnessOp n d + rankOneDensity φ) ψ - 1} := by
  refine ⟨|r|, ?_⟩
  rintro t ⟨ψ, φ, hψ, hφ, rfl⟩
  obtain ⟨hw0, hw1⟩ := witness_pure_bounds (by omega : 0 < n) (by omega : 1 ≤ d) ψ hψ
  have habs : |readout (witnessOp n d) ψ| ≤ 1 := abs_le.mpr ⟨hw0, hw1⟩
  have hmul : r * readout (witnessOp n d) ψ ≤ |r| := by
    calc
      _ ≤ |r * readout (witnessOp n d) ψ| := le_abs_self _
      _ = |r| * |readout (witnessOp n d) ψ| := abs_mul _ _
      _ ≤ |r| := by nlinarith [mul_le_mul_of_nonneg_left habs (abs_nonneg r)]
  have hov := cs φ ψ
  rw [hφ.1, hψ, mul_one] at hov
  simp only [expectation_add, expectation_smul, expectation_rank_one]
  linarith

private lemma pure_conjugate_bound {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    (r : ℝ) (ψ : Word (Fin d) n → ℂ) (hψ : IsUnitState ψ) :
    r * readout (witnessOp n d) ψ - hatE n d r ≤ geometricMeasurePure ψ := by
  have hs : sSup {t : ℝ | ∃ φ, IsBiseparable φ ∧
      t = Complex.normSq (star φ ⬝ᵥ ψ)} ≤ 1 + hatE n d r - r * readout (witnessOp n d) ψ := by
    apply csSup_le (overlap_values_nonempty hn hd ψ)
    rintro t ⟨φ, hφ, rfl⟩
    have h := le_csSup (hat_values_bdd hn hd r)
      (show readout (r • witnessOp n d + rankOneDensity φ) ψ - 1 ∈
        {t : ℝ | ∃ ψ φ, IsUnitState ψ ∧ IsBiseparable φ ∧
          t = readout (r • witnessOp n d + rankOneDensity φ) ψ - 1} from
        ⟨ψ, φ, hψ, hφ, rfl⟩)
    change _ ≤ hatE n d r at h
    simp only [expectation_add, expectation_smul, expectation_rank_one] at h
    linarith
  unfold geometricMeasurePure
  linarith

private lemma hat_zero {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d) : hatE n d 0 = 0 := by
  apply le_antisymm
  · apply csSup_le (hat_values_nonempty hn hd 0)
    rintro t ⟨ψ, φ, hψ, hφ, rfl⟩
    have hov := cs φ ψ
    rw [hφ.1, hψ, mul_one] at hov
    simp only [zero_smul, zero_add, expectation_rank_one]
    linarith
  · let φ : Word (Fin d) n → ℂ := Pi.single (fun _ => (⟨0, hd⟩ : Fin d)) (1 : ℂ)
    have hφ := computational_biseparable hn (fun _ => (⟨0, hd⟩ : Fin d))
    have hu : star φ ⬝ᵥ φ = 1 :=
      (D5.S3.Quantum.Information.MultiEntropyPositivityRefutation.unit_norm_iff φ).mpr hφ.1
    apply le_csSup (hat_values_bdd hn hd 0)
    refine ⟨φ, φ, hφ.1, hφ, ?_⟩
    simp [zero_smul, expectation_rank_one, hu]

private lemma conjugate_ensemble_bound {n d : ℕ} (hn : 2 ≤ n) (hd : 0 < d)
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (ψ : ι → Word (Fin d) n → ℂ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (hu : ∀ i, IsUnitState (ψ i)) (r : ℝ) :
    r * (∑ i, p i * readout (witnessOp n d) (ψ i)) - hatE n d r ≤
      ∑ i, p i * geometricMeasurePure (ψ i) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (pure_conjugate_bound hn hd r (ψ i) (hu i)) (hp i))
  convert h using 1
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hs]
  simp only [one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma sum_distinguished {d : ℕ} {R : Type*} [CommRing R]
    (j : Fin d) (a b : R) : (∑ i : Fin d, if i = j then a else b) = a + (d - 1 : R) * b := by
  classical
  calc
    _ = ∑ i : Fin d, (b + if i = j then a - b else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring

/-- The canonical source pure vector really has the stated norm, two means,
and all-cut entanglement, including F=1/d and F=1. -/
theorem chi_attainment {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    (j : Fin d) {F : ℝ} (hF : 1 / (d : ℝ) ≤ F) (hF1 : F ≤ 1) :
    IsUnitState (chiVector (by omega : 0 < n) j (optimalAlpha d F) (optimalBeta d F)) ∧
      readout (supportProjector n d)
        (chiVector (by omega : 0 < n) j (optimalAlpha d F) (optimalBeta d F)) = 1 ∧
      readout (rankOneDensity (ghz n d))
        (chiVector (by omega : 0 < n) j (optimalAlpha d F) (optimalBeta d F)) = F ∧
      geometricMeasurePure (chiVector (by omega : 0 < n) j (optimalAlpha d F) (optimalBeta d F)) =
        twoMeanOptimum d F 1 := by
  classical
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hb, hba, hnorm, hmean, hvalue⟩ := optimal_amplitudes (by omega : 2 ≤ d) hF hF1
  let ψ := chiVector (by omega : 0 < n) j (optimalAlpha d F) (optimalBeta d F)
  have hψ : IsUnitState ψ := by
    change ∑ x, Complex.normSq (chiVector _ _ _ _ x) = 1
    rw [chi_norm, hnorm]
  have hy : readout (supportProjector n d) ψ = 1 := by
    change readout (supportProjector n d) (constantVector _ _) = 1
    rw [constantVector_support]
    have hnorm' := chi_norm (by omega : 0 < n) j (optimalAlpha d F) (optimalBeta d F)
    rw [chiVector, constantVector_norm] at hnorm'
    exact hnorm'.trans hnorm
  have hf : readout (rankOneDensity (ghz n d)) ψ = F := by
    change readout (rankOneDensity (ghz n d)) (constantVector _ _) = F
    rw [constantVector_ghz (by omega) (by omega), sum_distinguished]
    have he : (optimalAlpha d F : ℂ) + (d - 1 : ℂ) * optimalBeta d F =
        ((optimalAlpha d F + (d - 1 : ℝ) * optimalBeta d F : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.normSq_ofReal]
    simpa only [pow_two] using hmean
  have hl := pure_two_mean_lower hn hd ψ hψ
  rw [hf, hy] at hl
  have hβ : twoMeanOptimum d F 1 = 1 - (optimalAlpha d F)^2 := by
    unfold twoMeanOptimum
    split_ifs with h
    · have hF' : 1 ≤ (d : ℝ) * F := by
        simpa only [mul_comm] using (div_le_iff₀ (by positivity : (0 : ℝ) < d)).mp hF
      have hFeq : F = 1 / (d : ℝ) := by
        apply (eq_div_iff (by positivity : (d : ℝ) ≠ 0)).mpr
        nlinarith
      have hh : twoMeanValue d F 1 = 0 := by
        unfold twoMeanValue
        have he : (d - 1 : ℝ) * F * (1 - F) = ((d - 1 : ℝ) / d)^2 := by
          rw [hFeq]
          field_simp
          <;> ring
        rw [he, Real.sqrt_sq (div_nonneg (by linarith) (by linarith))]
        rw [hFeq]
        field_simp
        <;> ring
      linarith
    · exact hvalue
  have hupper : geometricMeasurePure ψ ≤ 1 - (optimalAlpha d F)^2 := by
    have hs := le_csSup (overlap_values_bdd ψ hψ)
      (show Complex.normSq (star (Pi.single (fun _ => j) (1 : ℂ)) ⬝ᵥ ψ) ∈
        {t : ℝ | ∃ φ, IsBiseparable φ ∧ t = Complex.normSq (star φ ⬝ᵥ ψ)} from
        ⟨_, computational_biseparable (by omega) _, rfl⟩)
    rw [basis_overlap] at hs
    have hc : ψ (fun _ => j) = (optimalAlpha d F : ℂ) := by
      simp [ψ, chiVector, constantVector_apply]
    rw [hc, Complex.normSq_ofReal] at hs
    unfold geometricMeasurePure
    nlinarith
  exact ⟨hψ, hy, hf, le_antisymm (hupper.trans_eq hβ.symm) hl⟩

private lemma basis_readout {n d : ℕ} (x : Word (Fin d) n)
    (A : Matrix (Word (Fin d) n) (Word (Fin d) n) ℂ) :
    readout A (Pi.single x 1) = (A x x).re := by
  classical
  simp [readout, dotProduct, mulVec, Pi.single_apply, Pi.star_apply]

private lemma basis_support_mean {n d : ℕ} (x : Word (Fin d) n) :
    readout (supportProjector n d) (Pi.single x 1) =
      if (Finset.univ.image x).card ≤ 2 then 1 else 0 := by
  classical
  rw [basis_readout]
  by_cases h : (Finset.univ.image x).card ≤ 2 <;> simp [supportProjector, h]

private lemma basis_ghz_mean {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (x : Word (Fin d) n) :
    readout (rankOneDensity (ghz n d)) (Pi.single x 1) =
      if ∃ j : Fin d, ∀ i, x i = j then 1 / (d : ℝ) else 0 := by
  classical
  rw [expectation_rank_one,
    D5.S3.Quantum.Entanglement.GHZ.OddGhzTenSettingWitness.normSq_overlap_comm,
    basis_overlap]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  split_ifs with h
  · simp [ghz, h, Complex.normSq_ofReal, Real.sq_sqrt (Nat.cast_nonneg d), hdR]
  · simp [ghz, h]

/-- The source computational Q-vector |0,1,2,0,...>. -/
def qWord {n d : ℕ} (hd : 3 ≤ d) : Word (Fin d) n :=
  fun k => if k.val = 1 then ⟨1, by omega⟩ else if k.val = 2 then ⟨2, by omega⟩ else ⟨0, by omega⟩

/-- A nonconstant two-symbol computational product word. -/
def twoSymbolWord {n d : ℕ} (hd : 2 ≤ d) : Word (Fin d) n :=
  fun k => if k.val = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩

lemma qWord_outside {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    ¬ (Finset.univ.image (qWord (n := n) hd)).card ≤ 2 := by
  classical
  let s : Finset (Fin d) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}
  have hs : s.card = 3 := by simp [s, Fin.ext_iff]
  have hsub : s ⊆ Finset.univ.image (qWord (n := n) hd) := by
    intro x hx
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, by simp [qWord]⟩
    · exact Finset.mem_image.mpr ⟨⟨1, by omega⟩, Finset.mem_univ _, by simp [qWord]⟩
    · exact Finset.mem_image.mpr ⟨⟨2, by omega⟩, Finset.mem_univ _, by simp [qWord]⟩
  have h := Finset.card_le_card hsub
  omega

private lemma qWord_nonconstant {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    ¬ ∃ j : Fin d, ∀ i, qWord (n := n) hd i = j := by
  rintro ⟨j, hj⟩
  have h := (hj ⟨0, by omega⟩).trans (hj ⟨1, by omega⟩).symm
  have hh := congrArg Fin.val h
  norm_num [qWord] at hh

private lemma twoSymbolWord_data {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d) :
    (Finset.univ.image (twoSymbolWord (n := n) hd)).card ≤ 2 ∧
      ¬ ∃ j : Fin d, ∀ i, twoSymbolWord (n := n) hd i = j := by
  classical
  constructor
  · have hsub : Finset.univ.image (twoSymbolWord (n := n) hd) ⊆
        {⟨0, by omega⟩, ⟨1, by omega⟩} := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      simp only [twoSymbolWord]
      split_ifs <;> simp
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · rintro ⟨j, hj⟩
    have h := (hj ⟨0, by omega⟩).trans (hj ⟨1, by omega⟩).symm
    have hh := congrArg Fin.val h
    norm_num [twoSymbolWord] at hh

lemma twoMean_scaling {d : ℕ} {f y : ℝ} (hy : 0 < y) :
    twoMeanOptimum d f y = y * twoMeanOptimum d (f / y) 1 := by
  have he : (d : ℝ) * (f / y) ≤ 1 ↔ (d : ℝ) * f ≤ y := by
    rw [← mul_div_assoc, div_le_one hy]
  unfold twoMeanOptimum
  simp only [he]
  by_cases h : (d : ℝ) * f ≤ y
  · simp [h]
  · simp only [h, ite_false]
    unfold twoMeanValue
    have hrad : (d - 1 : ℝ) * f * (y - f) =
        y^2 * ((d - 1 : ℝ) * (f / y) * (1 - f / y)) := by
      field_simp
      <;> ring
    rw [hrad, Real.sqrt_mul (sq_nonneg y), Real.sqrt_sq hy.le]
    field_simp
    <;> ring

/-- The means W,Q and the means G,P determine one another on every density state. -/
theorem observable_correspondence {n d : ℕ}
    (ρ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n)) :
    observableMean (CStarMatrix.ofMatrix.symm ρ.1) (supportProjector n d) =
      1 - observableMean (CStarMatrix.ofMatrix.symm ρ.1) (complementProjector n d) ∧
    observableMean (CStarMatrix.ofMatrix.symm ρ.1) (rankOneDensity (ghz n d)) =
      (1 - observableMean (CStarMatrix.ofMatrix.symm ρ.1) (complementProjector n d)) / d -
        observableMean (CStarMatrix.ofMatrix.symm ρ.1) (witnessOp n d) := by
  simp only [complementProjector, witnessOp, mean_sub, mean_smul, mean_one]
  constructor <;> ring

/-- The three weights of a concrete optimizer for every feasible pair of means. -/
def twoMeanWeights (d : ℕ) (f y : ℝ) : Fin 3 → ℝ := by
  classical
  exact if (d : ℝ) * f ≤ y then ![(d : ℝ) * f, y - (d : ℝ) * f, 1 - y] else ![y, 1 - y, 0]

/-- The actual computational or constant-sector vectors in the optimizer. -/
def twoMeanStates {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) (f y : ℝ) :
    Fin 3 → Word (Fin d) n → ℂ := by
  classical
  exact if (d : ℝ) * f ≤ y then
    ![Pi.single (fun _ => (⟨0, by omega⟩ : Fin d)) 1,
      Pi.single (twoSymbolWord (show 2 ≤ d by omega)) 1, Pi.single (qWord hd) 1]
  else ![chiVector (show 0 < n by omega) ⟨0, by omega⟩ (optimalAlpha d (f / y)) (optimalBeta d (f / y)),
    Pi.single (qWord hd) 1, Pi.single (qWord hd) 1]

private lemma two_mean_ensemble_data {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {f y : ℝ} (hf : 0 ≤ f) (hfy : f ≤ y) (hy : y ≤ 1) :
    (∀ i, 0 ≤ twoMeanWeights d f y i) ∧ (∑ i, twoMeanWeights d f y i) = 1 ∧
      (∀ i, IsUnitState (twoMeanStates hn hd f y i)) ∧
      (∑ i, twoMeanWeights d f y i * readout (rankOneDensity (ghz n d))
        (twoMeanStates hn hd f y i)) = f ∧
      (∑ i, twoMeanWeights d f y i * readout (supportProjector n d)
        (twoMeanStates hn hd f y i)) = y ∧
      (∑ i, twoMeanWeights d f y i * geometricMeasurePure (twoMeanStates hn hd f y i)) =
        twoMeanOptimum d f y := by
  classical
  have hn0 : 0 < n := by omega
  have hd0 : 0 < d := by omega
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  let j : Fin d := ⟨0, by omega⟩
  have hcG : readout (rankOneDensity (ghz n d)) (Pi.single (fun _ => j) 1) = 1 / d := by
    rw [basis_ghz_mean hn0 hd0]
    exact if_pos ⟨j, fun _ => rfl⟩
  have hcP : readout (supportProjector n d) (Pi.single (fun _ => j) 1) = 1 := by
    rw [basis_support_mean]
    haveI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
    simp [Finset.image_const]
  obtain ⟨h2P, h2c⟩ := twoSymbolWord_data (by omega : 2 ≤ n) (by omega : 2 ≤ d)
  have h2G : readout (rankOneDensity (ghz n d))
      (Pi.single (twoSymbolWord (n := n) (show 2 ≤ d by omega)) 1) = 0 := by
    rw [basis_ghz_mean hn0 hd0]
    simp [h2c]
  have h2P' : readout (supportProjector n d)
      (Pi.single (twoSymbolWord (n := n) (show 2 ≤ d by omega)) 1) = 1 := by
    rw [basis_support_mean]; simp [h2P]
  have hqG : readout (rankOneDensity (ghz n d)) (Pi.single (qWord (n := n) hd) 1) = 0 := by
    rw [basis_ghz_mean hn0 hd0]; simp [qWord_nonconstant hn hd]
  have hqP : readout (supportProjector n d) (Pi.single (qWord (n := n) hd) 1) = 0 := by
    rw [basis_support_mean]; simp [qWord_outside hn hd]
  have hzero (w : Word (Fin d) n) : geometricMeasurePure (Pi.single w 1) = 0 :=
    biseparable_measure_zero (by omega) hd0 _ (computational_biseparable (by omega) w)
  dsimp [j] at hcG hcP
  by_cases hlow : (d : ℝ) * f ≤ y
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> norm_num [twoMeanWeights, hlow] <;> nlinarith
    · simp [twoMeanWeights, hlow, Fin.sum_univ_succ] <;> ring
    · intro i; fin_cases i <;> simp only [twoMeanStates, hlow, ite_true, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one] <;> apply basis_unit
    · simp only [twoMeanWeights, twoMeanStates, hlow, ite_true, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.sum_univ_zero,
        add_zero, hcG, h2G, hqG, mul_zero]
      field_simp
    · simp [twoMeanWeights, twoMeanStates, hlow, Fin.sum_univ_succ, hcP, h2P', hqP]
    · simp [twoMeanWeights, twoMeanStates, hlow, Fin.sum_univ_succ, hzero, twoMeanOptimum]
  · have hy0 : 0 < y := by nlinarith
    have hF0 : 1 / (d : ℝ) ≤ f / y := by
      apply (div_le_div_iff₀ (by linarith) hy0).mpr
      nlinarith
    have hF1 : f / y ≤ 1 := (div_le_one hy0).mpr hfy
    obtain ⟨hunit, hP, hG, hE⟩ := chi_attainment hn hd j hF0 hF1
    dsimp [j] at hunit hP hG hE
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp [twoMeanWeights, hlow] <;> linarith
    · simp [twoMeanWeights, hlow, Fin.sum_univ_succ]
    · intro i; fin_cases i
      · simpa [twoMeanStates, hlow] using hunit
      · simp only [twoMeanStates, hlow, ite_false, Matrix.cons_val_one]; apply basis_unit
      · simp only [twoMeanStates, hlow, ite_false, Matrix.cons_val_fin_one]; apply basis_unit
    · simp only [twoMeanWeights, twoMeanStates, hlow, ite_false, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.sum_univ_zero,
        add_zero, hG, hqG, mul_zero, zero_mul]
      field_simp
    · simp [twoMeanWeights, twoMeanStates, hlow, Fin.sum_univ_succ, hP, hqP]
    · simp only [twoMeanWeights, twoMeanStates, hlow, ite_false, Fin.sum_univ_succ,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.sum_univ_zero,
        add_zero, hE, hzero, mul_zero, zero_mul]
      exact (twoMean_scaling hy0).symm

/-- Every feasible pair of means is realized by an actual density operator
and the explicit finite normalized ensemble above, with roof equal to the
universal lower bound. This is an attained all-state minimum. -/
theorem two_mean_attainment {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d)
    {f y : ℝ} (hf : 0 ≤ f) (hfy : f ≤ y) (hy : y ≤ 1) :
    ∃ σ : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Word (Fin d) n),
      CStarMatrix.ofMatrix.symm σ.1 = ∑ i, twoMeanWeights d f y i •
        rankOneDensity (twoMeanStates hn hd f y i) ∧
      observableMean (CStarMatrix.ofMatrix.symm σ.1) (rankOneDensity (ghz n d)) = f ∧
      observableMean (CStarMatrix.ofMatrix.symm σ.1) (supportProjector n d) = y ∧
      geometricMeasure (CStarMatrix.ofMatrix.symm σ.1) = twoMeanOptimum d f y ∧
      (∀ i, 0 ≤ twoMeanWeights d f y i) ∧ (∑ i, twoMeanWeights d f y i) = 1 ∧
      (∀ i, IsUnitState (twoMeanStates hn hd f y i)) ∧
      (∑ i, twoMeanWeights d f y i * geometricMeasurePure (twoMeanStates hn hd f y i)) =
        twoMeanOptimum d f y := by
  obtain ⟨hp, hs, hu, hG, hP, hE⟩ := two_mean_ensemble_data hn hd hf hfy hy
  let σ := ensembleDensity (twoMeanWeights d f y) (twoMeanStates hn hd f y) hp hs hu
  have he : CStarMatrix.ofMatrix.symm σ.1 = ∑ i, twoMeanWeights d f y i •
      rankOneDensity (twoMeanStates hn hd f y i) := rfl
  have hfσ : observableMean (CStarMatrix.ofMatrix.symm σ.1) (rankOneDensity (ghz n d)) = f := by
    rw [he, trace_average]; exact hG
  have hyσ : observableMean (CStarMatrix.ofMatrix.symm σ.1) (supportProjector n d) = y := by
    rw [he, trace_average]; exact hP
  refine ⟨σ, he, hfσ, hyσ, ?_, hp, hs, hu, hE⟩
  apply le_antisymm
  · rw [he]
    exact (finite_ensemble_upper (by omega) (by omega) _ _ hp hs hu).trans_eq hE
  · have h := two_mean_lower hn hd σ
    rwa [hfσ, hyσ] at h

private lemma metric_intercept_nonpos {d : ℕ} (hd : 2 ≤ d) {t : ℝ} (ht : 1 ≤ t) :
    1 - metricB d t + (metricB d t - metricA d t) / d ≤ 0 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have ht0 : 0 < t := by linarith
  have he : 1 - metricB d t + (metricB d t - metricA d t) / d =
      -((d - 1 : ℝ) * (t - 1)^2) / ((d : ℝ)^2 * t) := by
    unfold metricA metricB
    field_simp
    <;> ring
  rw [he]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (mul_nonneg (by linarith) (sq_nonneg _))
  · positivity

private lemma hat_supporting {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d)
    {t : ℝ} (ht : 1 ≤ t) :
    hatE n d (metricA d t - metricB d t) ≤
      -(1 - metricB d t + (metricB d t - metricA d t) / d) := by
  obtain ⟨ha, ha1, hab, he⟩ := metric_parameters hd ht
  apply csSup_le (hat_values_nonempty hn (by omega) _)
  rintro v ⟨ψ, φ, hψ, hφ, rfl⟩
  have hm := pure_metric_lower hn (by omega) ha ha1 hab he ψ hψ
  obtain ⟨_, _, hy⟩ := pure_means_triangle (by omega : 0 < n) (by omega : 0 < d) ψ hψ
  have hc := metric_intercept_nonpos hd ht
  have hcy := mul_le_mul_of_nonpos_left hy hc
  have hov := le_csSup (overlap_values_bdd ψ hψ)
    (show Complex.normSq (star φ ⬝ᵥ ψ) ∈ {v : ℝ | ∃ φ, IsBiseparable φ ∧
      v = Complex.normSq (star φ ⬝ᵥ ψ)} from ⟨φ, hφ, rfl⟩)
  have hov' : Complex.normSq (star φ ⬝ᵥ ψ) ≤ 1 - geometricMeasurePure ψ := by
    unfold geometricMeasurePure
    linarith only [hov]
  simp only [expectation_add, expectation_smul, expectation_rank_one,
    witnessOp, expectation_sub]
  rw [expectation_rank_one] at hm
  have hh :
      (metricA d t - metricB d t) *
          (1 / (d : ℝ) * readout (supportProjector n d) ψ -
            Complex.normSq (star (ghz n d) ⬝ᵥ ψ)) +
        (1 - metricB d t + (metricB d t - metricA d t) / d) ≤ geometricMeasurePure ψ := by
    calc
      _ ≤ (metricA d t - metricB d t) *
          (1 / (d : ℝ) * readout (supportProjector n d) ψ -
            Complex.normSq (star (ghz n d) ⬝ᵥ ψ)) +
        (1 - metricB d t + (metricB d t - metricA d t) / d) *
          readout (supportProjector n d) ψ :=
        by linarith only [hcy]
      _ = (1 - metricB d t) * readout (supportProjector n d) ψ +
          (metricB d t - metricA d t) * Complex.normSq (star (ghz n d) ⬝ᵥ ψ) := by ring
      _ ≤ _ := hm
  linarith only [hh, hov']

/-- The complete optimum for the original two-vector single-witness
conjugate on the entire feasible interval. No all-real-slope supplier formula
is assumed, and all limiting endpoints follow from finite supporting lines. -/
theorem witness_optimum {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) {w : ℝ}
    (hw0 : -(d - 1 : ℝ) / d ≤ w) (hw1 : w ≤ 1 / (d : ℝ)) :
    epsilonWitness n d w = twoMeanOptimum d (1 / (d : ℝ) - w) 1 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  let F : ℝ := 1 / (d : ℝ) - w
  have hf : 0 ≤ F := sub_nonneg.mpr hw1
  have hf1 : F ≤ 1 := by
    have he : -(d - 1 : ℝ) / d = 1 / (d : ℝ) - 1 := by field_simp <;> ring
    rw [he] at hw0
    dsimp [F]; linarith
  obtain ⟨hp, hs, hu, hG, hP, hE⟩ := two_mean_ensemble_data hn hd hf hf1 (le_refl 1)
  let p := twoMeanWeights d F 1
  let ψ := twoMeanStates hn hd F 1
  have hw : (∑ i, p i * readout (witnessOp n d) (ψ i)) = w := by
    simp only [witnessOp, expectation_sub, expectation_smul]
    have hterm (i : Fin 3) : p i * ((1 / (d : ℝ)) * readout (supportProjector n d) (ψ i) -
        readout (rankOneDensity (ghz n d)) (ψ i)) =
        (1 / (d : ℝ)) * (p i * readout (supportProjector n d) (ψ i)) -
          p i * readout (rankOneDensity (ghz n d)) (ψ i) := by ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hP, hG]
    dsimp [F]
    ring
  have hb : BddAbove {v : ℝ | ∃ r : ℝ, v = r * w - hatE n d r} := by
    refine ⟨twoMeanOptimum d F 1, ?_⟩
    rintro v ⟨r, rfl⟩
    have h := conjugate_ensemble_bound (by omega : 2 ≤ n) (by omega : 0 < d) p ψ hp hs hu r
    rw [hw] at h
    exact h.trans_eq hE
  have hs0 : {v : ℝ | ∃ r : ℝ, v = r * w - hatE n d r}.Nonempty := ⟨_, 0, rfl⟩
  have hnonneg : 0 ≤ epsilonWitness n d w := by
    apply le_csSup hb
    refine ⟨0, ?_⟩
    rw [zero_mul, hat_zero (by omega : 2 ≤ n) (by omega : 0 < d), sub_self]
  apply le_antisymm
  · apply csSup_le hs0
    rintro v ⟨r, rfl⟩
    have h := conjugate_ensemble_bound (by omega : 2 ≤ n) (by omega : 0 < d) p ψ hp hs hu r
    rw [hw] at h
    exact h.trans_eq hE
  · apply supporting_envelope (by omega : 2 ≤ d) hf hf1 hnonneg
    intro t ht
    have hhat := hat_supporting (by omega : 2 ≤ n) (by omega : 2 ≤ d) ht
    have hslope := le_csSup hb
      (show (metricA d t - metricB d t) * w - hatE n d (metricA d t - metricB d t) ∈
        {v : ℝ | ∃ r : ℝ, v = r * w - hatE n d r} from ⟨_, rfl⟩)
    change _ ≤ epsilonWitness n d w at hslope
    have he :
        (1 + (d - 2 : ℝ) * F - t * (1 - F) - (d - 1 : ℝ) * F / t) / d =
        (metricA d t - metricB d t) * w +
          (1 - metricB d t + (metricB d t - metricA d t) / d) := by
      dsimp [F, metricA, metricB]
      field_simp
      <;> ring
    rw [he]
    linarith

end
end D5.S3.Quantum.Entanglement.Witness.NoisyGhzExactRoof
