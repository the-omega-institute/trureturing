/- GID: D5/S3/Quantum/Analysis/TraceClass/ContinuousEnergyHamiltonian
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/ContinuousEnergyHamiltonian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full-space thermal Hamiltonians from continuous singular spectral energy. -/

import D5.S3.Quantum.Analysis.DiagonalEnergy
import D5.S3.Quantum.Analysis.OrliczCommonEnergy
import D5.S3.Quantum.Analysis.TraceClass.KernelEnergy
import D5.S3.Quantum.Analysis.TraceClass.CompactCommonReference
import D5.S3.Quantum.Analysis.TraceClass.EntropyMaximizer
import D5.S3.Observer.HilbertGeometry.HilbertPathFundamentalTheorem
import Mathlib.Topology.UniformSpace.Dini

noncomputable section
open Filter Set
open scoped ComplexOrder InnerProductSpace ENNReal NNReal Topology BigOperators

namespace QuantumLogEnergy
open D5.S3.Quantum.Analysis
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem basis_countable {ι : Type*} [TopologicalSpace.SeparableSpace H]
    (b : HilbertBasis ι ℂ H) : Countable ι := by
  have hs := D5.S3.Observer.HilbertGeometry.HilbertPathFundamentalTheorem.CountableBasisPort.countable_of_orthonormal
    b.orthonormal.toSubtypeRange
  letI : Countable (Set.range b) := hs.to_subtype
  exact Function.Injective.countable (f := Set.rangeFactorization b)
    (fun _ _ h => b.orthonormal.linearIndependent.injective (congrArg Subtype.val h))

private theorem continuous_diagonal {w : Set H} (b : HilbertBasis w ℂ H) (i : w) :
    Continuous (fun rho : TraceClass H => diagonal b rho i) := by
  exact Complex.continuous_re.comp (continuous_const.inner
    ((ContinuousLinearMap.apply ℂ H (b i)).continuous.comp operatorCLM.continuous))

/-- Finite logarithmic levels on every full-basis fiber, including the reference kernel. -/
def thermalBaseLevel {T : Reference H} (r : SpectralResolution T)
    (code : r.index → ℕ) (i : r.index) : ℝ :=
  if r.values i = 0 then (code i + 1 : ℝ) * Real.log 2 else -Real.log (r.values i)

private theorem thermalBaseLevel_nonneg {T : Reference H} (r : SpectralResolution T)
    (code : r.index → ℕ) (i : r.index) : 0 ≤ thermalBaseLevel r code i := by
  dsimp [thermalBaseLevel]
  split_ifs
  · positivity
  · exact neg_nonneg.mpr (Real.log_nonpos (r.nonneg i)
      (spectral_value_le_one T r.basis r.values r.eigen i))

private theorem encoded_energy {T : Reference H} (r : SpectralResolution T)
    (code : r.index → ℕ) (rho : TraceClass H) (hp : 0 ≤ rho.1)
    (hf : spectralEnergy T rho < ∞) :
    (∑' i, ENNReal.ofReal (thermalBaseLevel r code i * diagonal r.basis rho i)) =
      spectralEnergy T rho := by
  rw [← spectralSeries_eq_spectralEnergy T r.basis r.values r.nonneg r.eigen rho hp]
  apply tsum_congr
  intro i
  by_cases hz : r.values i = 0
  · have hk : r.basis i ∈ T.1.1.ker := by
      change T.1.1 (r.basis i) = 0
      rw [r.eigen i, hz, Complex.ofReal_zero, zero_smul]
    have hr : rho.1 (r.basis i) = 0 := ker_le_ker_of_spectralEnergy_lt_top T rho hp hf hk
    simp [spectralSeries, diagonal, hr]
  · simp only [spectralSeries, thermalBaseLevel, hz, ↓reduceIte, singularLog]
    have hn : 0 ≤ -Real.log (r.values i) := by
      simpa only [thermalBaseLevel, hz, ↓reduceIte] using thermalBaseLevel_nonneg r code i
    rw [ENNReal.ofReal_mul hn]
    exact mul_comm _ _

private theorem reference_values_hasSum (T : Reference H) (r : SpectralResolution T)
    (ht : (trace T.1.1 (TraceClass.isTraceClass_coe T.1)).re = 1) : HasSum r.values 1 := by
  convert (diagonal_hasSum r.basis T.1) using 1
  · ext i
    simp only [diagonal, r.eigen, inner_smul_right_eq_smul, inner_self_eq_norm_sq_to_K,
      r.basis.orthonormal.1 i, smul_eq_mul]
    norm_num
  · exact ht.symm

private theorem encoded_heat_summable {T : Reference H} (r : SpectralResolution T)
    (code : r.index → ℕ) (hc : Function.Injective code)
    (ht : (trace T.1.1 (TraceClass.isTraceClass_coe T.1)).re = 1) :
    Summable (fun i => Real.exp (-thermalBaseLevel r code i)) := by
  have hg := (summable_geometric_two.comp_injective hc).mul_right (1 / 2 : ℝ)
  apply ((reference_values_hasSum T r ht).summable.add hg).of_norm_bounded
  intro i
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  by_cases hz : r.values i = 0
  · dsimp [thermalBaseLevel]
    rw [if_pos hz]
    have he : Real.exp (-((code i + 1 : ℝ) * Real.log 2)) = (1 / 2 : ℝ) ^ (code i + 1) := by
      calc
        _ = Real.exp (((code i + 1 : ℕ) : ℝ) * (-Real.log 2)) := by
          congr 1; push_cast; ring
        _ = Real.exp (-Real.log 2) ^ (code i + 1) := by rw [Real.exp_nat_mul]
        _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
    rw [he, pow_succ, hz, zero_add]
  · simp only [thermalBaseLevel, hz, ↓reduceIte, neg_neg,
      Real.exp_log (lt_of_le_of_ne (r.nonneg i) (Ne.symm hz))]
    change r.values i ≤ r.values i + (1 / 2 : ℝ) ^ code i * (1 / 2)
    exact le_add_of_nonneg_right (by positivity)

private theorem encoded_all_temperature {ι : Type*} (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable (fun i => Real.exp (-a i)))
    (code : ι → ℕ) (hc : Function.Injective code) (w : ℕ → ℕ)
    (hw : Tendsto w atTop atTop) {β : ℝ} (hβ : 0 < β) :
    Summable (fun i => Real.exp (-β * (1 + (w (code i) : ℝ) * a i))) := by
  have hwR : Tendsto (fun i => (w (code i) : ℝ)) cofinite atTop :=
    (tendsto_natCast_atTop_atTop.comp hw).comp
      (show Tendsto code cofinite atTop from Nat.cofinite_eq_atTop ▸ hc.tendsto_cofinite)
  apply hs.of_norm_bounded_eventually
  filter_upwards [hwR.eventually (eventually_ge_atTop β⁻¹)] with i hi
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  have hβw : 1 ≤ β * (w (code i) : ℝ) := by
    simpa only [mul_inv_cancel₀ hβ.ne'] using mul_le_mul_of_nonneg_left hi hβ.le
  nlinarith [mul_le_mul_of_nonneg_right hβw (ha i)]

private theorem extend_nonneg {ι : Type*} (code : ι → ℕ) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (n : ℕ) : 0 ≤ Function.extend code f 0 n := by
  classical
  rw [Function.extend_def]
  split_ifs
  · exact hf _
  · exact le_rfl

private theorem continuous_extend {ι X : Type*} [TopologicalSpace X]
    (code : ι → ℕ) (hc : Function.Injective code) (f : X → ι → ℝ)
    (hf : ∀ i, Continuous (fun x => f x i)) (n : ℕ) :
    Continuous (fun x => Function.extend code (f x) 0 n) := by
  classical
  by_cases hn : ∃ i, code i = n
  · obtain ⟨i, rfl⟩ := hn
    simpa only [hc.extend_apply] using hf i
  · simpa only [Function.extend_apply' _ _ _ hn, Pi.zero_apply] using
      (continuous_const : Continuous (fun _ : X => (0 : ℝ)))

private theorem ofReal_extend_tsum {ι : Type*} (code : ι → ℕ)
    (hc : Function.Injective code) (f : ι → ℝ) (v : ℕ → ℝ) :
    (∑' n, ENNReal.ofReal (v n * Function.extend code f 0 n)) =
      ∑' i, ENNReal.ofReal (v (code i) * f i) := by
  classical
  have he : (fun n => ENNReal.ofReal (v n * Function.extend code f 0 n)) =
      Function.extend code (fun i => ENNReal.ofReal (v (code i) * f i)) 0 := by
    funext n
    by_cases hn : ∃ i, code i = n
    · obtain ⟨i, rfl⟩ := hn
      simp only [hc.extend_apply]
    · simp [Function.extend_apply' _ _ _ hn]
  rw [he, tsum_extend_zero hc]

private theorem uniform_tails_of_continuous_total {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (f : X → ℕ → ℝ) (hf : ∀ x n, 0 ≤ f x n)
    (hc : ∀ n, Continuous (fun x => f x n)) (hs : ∀ x, Summable (f x))
    (ht : Continuous (fun x => ∑' n, f x n)) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ x,
      (∑' k, ENNReal.ofReal (f x (N + k))) ≤ (ε : ℝ≥0∞) := by
  classical
  let F : ℕ → X → ℝ := fun N x => ∑ n ∈ Finset.range N, f x n
  have hF (N) : Continuous (F N) := continuous_finsetSum _ (fun n _ => hc n)
  have hm : Monotone F := by
    apply monotone_nat_of_le_succ
    intro N x
    simp only [F, Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hf x N)
  have hu := Monotone.tendstoUniformly_of_forall_tendsto hF hm ht
    (fun x => (hs x).hasSum.tendsto_sum_nat)
  intro ε hε
  have he : 0 < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨N, hN⟩ := (hu _ (Metric.dist_mem_uniformity he)).exists
  refine ⟨N, fun x => ?_⟩
  have htail : Summable (fun k => f x (N + k)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff N).2 (hs x)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => hf x _) htail,
    ← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  have heq : (∑' n, f x n) - F N x = ∑' k, f x (N + k) := by
    have hh := (hs x).sum_add_tsum_nat_add N
    dsimp [F]
    rw [← hh]
    simp only [add_sub_cancel_left, Nat.add_comm]
  have hn := hN x
  change dist (∑' n, f x n) (F N x) < (ε : ℝ) at hn
  rw [Real.dist_eq, heq, abs_of_nonneg (tsum_nonneg (fun k => hf x _))] at hn
  exact hn.le

/-- Joint properties of the literal full-space Hamiltonian, its heat, generator and state energy. -/
def ThermalOn {ι : Type*} (b : HilbertBasis ι ℂ H) (h : ι → ℝ)
    (hh : ∀ i, 0 ≤ h i) (A : Set (TraceClass H)) : Prop :=
  (∀ i, 1 ≤ h i) ∧
  (∀ β : ℝ, 0 < β → Summable (fun i => Real.exp (-β * h i))) ∧
  IsSelfAdjoint (DiagonalHeat.hamiltonian b h) ∧
  Dense ((DiagonalHeat.hamiltonian b h).domain : Set H) ∧
  (∀ x y, (x,y) ∈ (DiagonalHeat.hamiltonian b h).graph ↔
    ∀ i, b.repr y i = (h i : ℂ) * b.repr x i) ∧
  (∀ x, x ∈ (DiagonalHeat.hamiltonian b h).domain ↔
    Memℓp (fun i => (h i : ℂ) * b.repr x i) 2) ∧
  (∀ t x i, b.repr (DiagonalHeat.heat b h hh t x) i =
    (Real.exp (-(t : ℝ)*h i) : ℂ)*b.repr x i) ∧
  (∀ t, (DiagonalHeat.heat b h hh t).IsPositive) ∧
  (∃ S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H,
    (∀ t, S t = (DiagonalHeat.heat b h hh t).restrictScalars ℝ) ∧
    (∀ x v : H, Tendsto (fun t : ℝ≥0 =>
      (t : ℝ)⁻¹ • (DiagonalHeat.heat b h hh t x-x)) (𝓝[>] 0) (𝓝 v) ↔
      (x,-v) ∈ (DiagonalHeat.hamiltonian b h).graph) ∧
    (∀ R : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup H,
      (∀ x v, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (R t x-x))
        (𝓝[>] 0) (𝓝 v) ↔ (x,-v) ∈ (DiagonalHeat.hamiltonian b h).graph) → R = S)) ∧
  (∀ x : (DiagonalHeat.hamiltonian b h).domain,
    ‖(x : H)‖^2 ≤ (⟪(x : H),(DiagonalHeat.hamiltonian b h) x⟫_ℂ).re) ∧
  (∀ β : ℝ≥0, 0 < β → ∃ ht : IsTraceClass (DiagonalHeat.heat b h hh β),
    HasSum (fun i => (Real.exp (-(β : ℝ)*h i) : ℂ))
      (trace (DiagonalHeat.heat b h hh β) ht) ∧
    HasSum (fun i => Real.exp (-(β : ℝ)*h i))
      (trace (DiagonalHeat.heat b h hh β) ht).re) ∧
  (∀ rho ∈ A, DiagonalEnergy.stateEnergy b h hh rho.1
    (TraceClass.isTraceClass_coe rho) < ∞) ∧
  ContinuousOn (fun rho : TraceClass H => DiagonalEnergy.stateEnergy b h hh rho.1
    (TraceClass.isTraceClass_coe rho)) A ∧
  ContinuousOn (fun rho : TraceClass H => (DiagonalEnergy.stateEnergy b h hh rho.1
    (TraceClass.isTraceClass_coe rho)).toReal) A

set_option maxHeartbeats 1600000 in
-- The construction transfers scalar series twice and assembles the full operator conclusions.
/-- A continuous finite singular energy on a compact state family yields one thermal Hamiltonian
on the original full spectral basis, at arbitrarily small additional energy cost. -/
theorem exists_thermalHamiltonian_of_continuous_spectralEnergy
    [TopologicalSpace.SeparableSpace H] (sigma : Reference H)
    (htrace : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1)
    (r : SpectralResolution sigma) {A : Set (TraceClass H)}
    (hne : A.Nonempty) (hA : IsCompact A)
    (hp : ∀ rho ∈ A, 0 ≤ rho.1)
    (ht : ∀ rho ∈ A, (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1)
    (hf : ∀ rho ∈ A, spectralEnergy sigma rho < ∞)
    (hc : ContinuousOn (fun rho => (spectralEnergy sigma rho).toReal) A)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ code : r.index → ℕ, Function.Injective code ∧
      ∃ w : ℕ → ℕ, (∀ n, 1 ≤ w n) ∧ Monotone w ∧ Tendsto w atTop atTop ∧
      ∃ (h : r.index → ℝ) (hh : ∀ i, 0 ≤ h i),
        (∀ i, h i = 1 + (w (code i) : ℝ) * thermalBaseLevel r code i) ∧
        ThermalOn r.basis h hh A ∧
        ∀ rho ∈ A,
          DiagonalEnergy.stateEnergy r.basis h hh rho.1 (TraceClass.isTraceClass_coe rho) =
            1 + ∑' i, ENNReal.ofReal
              ((w (code i) : ℝ) * thermalBaseLevel r code i * diagonal r.basis rho i) ∧
          DiagonalEnergy.stateEnergy r.basis h hh rho.1 (TraceClass.isTraceClass_coe rho) ≤
            1 + spectralEnergy sigma rho + (δ : ℝ≥0∞) ∧
          (DiagonalEnergy.stateEnergy r.basis h hh rho.1
            (TraceClass.isTraceClass_coe rho)).toReal ≤
            1 + (spectralEnergy sigma rho).toReal + (δ : ℝ) := by
  classical
  letI : Countable r.index := basis_countable r.basis
  letI : Encodable r.index := Encodable.ofCountable r.index
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let code : r.index → ℕ := Encodable.encode
  have hinj : Function.Injective code := Encodable.encode_injective
  let a := thermalBaseLevel r code
  have ha : ∀ i, 0 ≤ a i := thermalBaseLevel_nonneg r code
  let f : A → ℕ → ℝ := fun rho =>
    Function.extend code (fun i => a i * diagonal r.basis rho.1 i) 0
  have hd (rho : A) (i : r.index) : 0 ≤ diagonal r.basis rho.1 i :=
    (rho.1.1.nonneg_iff_isPositive.mp (hp rho.1 rho.2)).re_inner_nonneg_right _
  have hf0 : ∀ rho n, 0 ≤ f rho n := fun rho =>
    extend_nonneg code _ (fun i => mul_nonneg (ha i) (hd rho i))
  have hfc : ∀ n, Continuous (fun rho => f rho n) :=
    continuous_extend code hinj _ (fun i =>
      continuous_const.mul ((continuous_diagonal r.basis i).comp continuous_subtype_val))
  have htotal (rho : A) : (∑' n, ENNReal.ofReal (f rho n)) = spectralEnergy sigma rho.1 := by
    calc
      _ = ∑' i, ENNReal.ofReal (a i * diagonal r.basis rho.1 i) := by
        simpa only [one_mul] using
          ofReal_extend_tsum code hinj (fun i => a i * diagonal r.basis rho.1 i) (fun _ => 1)
      _ = _ := encoded_energy r code rho.1 (hp rho.1 rho.2) (hf rho.1 rho.2)
  have hfs : ∀ rho, Summable (f rho) := by
    intro rho
    have hn : (∑' n, ENNReal.ofReal (f rho n)) ≠ ∞ := by
      rw [htotal]; exact (hf rho.1 rho.2).ne
    simpa only [ENNReal.toReal_ofReal (hf0 rho _)] using ENNReal.summable_toReal hn
  have hreal (rho : A) : (∑' n, f rho n) = (spectralEnergy sigma rho.1).toReal := by
    rw [← htotal, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal (hf0 rho _)]
  have hft : Continuous (fun rho : A => ∑' n, f rho n) := by
    simp_rw [hreal]
    exact continuousOn_iff_continuous_domRestrict.mp hc
  have hUT := uniform_tails_of_continuous_total f hf0 hfc hfs hft
  obtain ⟨w, hw1, hwm, hwlim, hwcost, hwUT⟩ :=
    D5.S3.Analytic.SeriesInequalities.UniformTailAmplification.exists_uniform_tail_amplification
      (fun rho n => ENNReal.ofReal (f rho n)) δ hδ hUT
  let g : A → ℕ → ℝ := fun rho n => (w n : ℝ) * f rho n
  have hg0 : ∀ rho n, 0 ≤ g rho n := fun rho n => mul_nonneg (by positivity) (hf0 rho n)
  have hgc : ∀ n, Continuous (fun rho => g rho n) := fun n => continuous_const.mul (hfc n)
  have hge (rho : A) (n : ℕ) : ENNReal.ofReal (g rho n) =
      (w n : ℝ≥0∞) * ENNReal.ofReal (f rho n) := by
    change ENNReal.ofReal ((w n : ℝ) * f rho n) = _
    rw [ENNReal.ofReal_mul (by positivity)]
    simp
  have hgUT : ∀ ε : ℝ≥0, 0 < ε → ∃ N : ℕ, ∀ rho,
      (∑' k, ENNReal.ofReal (g rho (N+k))) ≤ (ε : ℝ≥0∞) := by
    simpa only [hge] using hwUT
  have hgs := OrliczCommonEnergy.summable_of_uniform_ennreal_tails g hg0 hgUT
  have hgcont := OrliczCommonEnergy.continuous_of_uniform_ennreal_tails g hg0 hgc hgUT
  have hweighted (rho : A) :
      (∑' i, ENNReal.ofReal ((w (code i) : ℝ) * a i * diagonal r.basis rho.1 i)) =
        ENNReal.ofReal (∑' n, g rho n) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (hg0 rho) (hgs rho)]
    symm
    simpa only [g, f, mul_assoc] using
      ofReal_extend_tsum code hinj (fun i => a i * diagonal r.basis rho.1 i)
        (fun n => (w n : ℝ))
  let h : r.index → ℝ := fun i => 1 + (w (code i) : ℝ) * a i
  have h1 : ∀ i, 1 ≤ h i := fun i => le_add_of_nonneg_right (mul_nonneg (by positivity) (ha i))
  have hh : ∀ i, 0 ≤ h i := fun i => zero_le_one.trans (h1 i)
  have hsum : ∀ β : ℝ, 0 < β → Summable (fun i => Real.exp (-β*h i)) :=
    fun _ hβ => encoded_all_temperature a ha (encoded_heat_summable r code hinj htrace)
      code hinj w hwlim hβ
  have he (rho : A) : DiagonalEnergy.stateEnergy r.basis h hh rho.1.1
      (TraceClass.isTraceClass_coe rho.1) = 1 + ENNReal.ofReal (∑' n, g rho n) := by
    have hmass : (∑' i, ENNReal.ofReal (diagonal r.basis rho.1 i)) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (hd rho) (diagonal_hasSum r.basis rho.1).summable,
        (diagonal_hasSum r.basis rho.1).tsum_eq, ht rho.1 rho.2]
      norm_num
    have hid := (DiagonalEnergy.diagonal_resolvent_energy r.basis h hh hsum rho.1.1
      (TraceClass.isTraceClass_coe rho.1)
      (rho.1.1.nonneg_iff_isPositive.mp (hp rho.1 rho.2))).2.2.2.1
    rw [hid, ← hweighted rho, ← hmass, ← ENNReal.tsum_add]
    apply tsum_congr
    intro i
    have halg : h i * diagonal r.basis rho.1 i = diagonal r.basis rho.1 i +
        (w (code i) : ℝ) * a i * diagonal r.basis rho.1 i := by dsimp [h]; ring
    change ENNReal.ofReal (h i * diagonal r.basis rho.1 i) = _
    rw [halg, ENNReal.ofReal_add (hd rho i)
      (mul_nonneg (mul_nonneg (by positivity) (ha i)) (hd rho i))]
  have her (rho : A) : (DiagonalEnergy.stateEnergy r.basis h hh rho.1.1
      (TraceClass.isTraceClass_coe rho.1)).toReal = 1 + ∑' n, g rho n := by
    rw [he, ENNReal.toReal_add (by norm_num) ENNReal.ofReal_ne_top,
      ENNReal.toReal_one, ENNReal.toReal_ofReal (tsum_nonneg (hg0 rho))]
  have hefin (rho : A) : DiagonalEnergy.stateEnergy r.basis h hh rho.1.1
      (TraceClass.isTraceClass_coe rho.1) < ∞ := by
    rw [he]
    exact ENNReal.add_lt_top.mpr ⟨by norm_num, ENNReal.ofReal_lt_top⟩
  have hecont : ContinuousOn (fun rho : TraceClass H => DiagonalEnergy.stateEnergy
      r.basis h hh rho.1 (TraceClass.isTraceClass_coe rho)) A := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_const.add (ENNReal.continuous_ofReal.comp hgcont) using 1
    funext rho
    exact he rho
  have hercont : ContinuousOn (fun rho : TraceClass H => (DiagonalEnergy.stateEnergy
      r.basis h hh rho.1 (TraceClass.isTraceClass_coe rho)).toReal) A := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_const.add hgcont using 1
    funext rho
    exact her rho
  have hdiag := DiagonalHeat.diagonal_heat r.basis h hh
  obtain ⟨rho0, hrho0⟩ := hne
  have hbound := (DiagonalEnergy.diagonal_resolvent_energy r.basis h hh hsum rho0.1
    (TraceClass.isTraceClass_coe rho0) (rho0.1.nonneg_iff_isPositive.mp (hp rho0 hrho0))).2.2.2.2 h1
  refine ⟨code, hinj, w, hw1, hwm, hwlim, h, hh, fun _ => rfl,
    ⟨h1, hsum, hdiag.1, hdiag.2.1, hdiag.2.2.1, hdiag.2.2.2.1,
      hdiag.2.2.2.2.1, hdiag.2.2.2.2.2.1, hdiag.2.2.2.2.2.2,
      hbound, fun β hβ => DiagonalEnergy.heat_trace r.basis h hh hsum β hβ,
      fun rho hrho => hefin ⟨rho,hrho⟩, hecont, hercont⟩, ?_⟩
  intro rho hrho
  let x : A := ⟨rho, hrho⟩
  have hcost : ENNReal.ofReal (∑' n, g x n) ≤ spectralEnergy sigma rho + (δ : ℝ≥0∞) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (hg0 x) (hgs x)]
    simpa only [hge, htotal] using hwcost x
  have hcostR : (∑' n, g x n) ≤ (spectralEnergy sigma rho).toReal + (δ : ℝ) := by
    have hz := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨(hf rho hrho).ne, ENNReal.coe_ne_top⟩) hcost
    simpa only [ENNReal.toReal_ofReal (tsum_nonneg (hg0 x)),
      ENNReal.toReal_add (hf rho hrho).ne ENNReal.coe_ne_top, ENNReal.coe_toReal] using hz
  refine ⟨?_, ?_, ?_⟩
  · exact (he x).trans (congrArg (fun z : ℝ≥0∞ => 1+z) (hweighted x).symm)
  · rw [he x]
    simpa only [add_assoc] using (add_le_add (le_rfl : (1 : ℝ≥0∞) ≤ 1) hcost)
  · rw [her x]
    linarith

/-- The original closed convex finite-continuous-entropy premises yield a full-space
all-temperature Hamiltonian with a strictly positive finite uniform energy bound. -/
theorem exists_thermalHamiltonian_of_continuous_entropy
    [TopologicalSpace.SeparableSpace H] {A : Set (TraceClass H)}
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hp : ∀ rho ∈ A, 0 ≤ rho.1)
    (ht : ∀ rho ∈ A, (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1)
    (hf : ∀ (rho) (hr : rho ∈ A), spectralEntropy
      (⟨rho, hp rho hr, density_le_one rho (hp rho hr) (ht rho hr)⟩ : Reference H) ≠ ∞)
    (hc : ContinuousOn realEntropy A) :
    ∃ gamma ∈ A, IsMaxOn realEntropy A gamma ∧
      ∃ sigma : Reference H, sigma.1 ∈ A ∧
      (∀ rho ∈ A, spectralEnergy sigma rho ≠ ∞ ∧
        spectralEnergy sigma rho ≤ ENNReal.ofReal (realEntropy gamma + Real.log 2) ∧
        (spectralEnergy sigma rho).toReal ≤ realEntropy gamma + Real.log 2) ∧
      ContinuousOn (spectralEnergy sigma) A ∧
      ContinuousOn (fun rho => (spectralEnergy sigma rho).toReal) A ∧
      ∃ (h : (nativeResolution sigma).index → ℝ) (hh : ∀ i, 0 ≤ h i),
        ThermalOn (nativeResolution sigma).basis h hh A ∧
        0 < 2 + realEntropy gamma + Real.log 2 ∧
        ∀ rho ∈ A,
          DiagonalEnergy.stateEnergy (nativeResolution sigma).basis h hh rho.1
            (TraceClass.isTraceClass_coe rho) ≤
              ENNReal.ofReal (2 + realEntropy gamma + Real.log 2) ∧
          (DiagonalEnergy.stateEnergy (nativeResolution sigma).basis h hh rho.1
            (TraceClass.isTraceClass_coe rho)).toReal ≤
              2 + realEntropy gamma + Real.log 2 := by
  classical
  obtain ⟨_, gamma0, hg0, hmax0, _, _⟩ :=
    exists_unique_entropy_maximizer hne hclosed hconv hp ht hf hc
  let g0 : Reference H := ⟨gamma0, hp gamma0 hg0,
    density_le_one gamma0 (hp gamma0 hg0) (ht gamma0 hg0)⟩
  have hreal0 : realEntropy gamma0 = (spectralEntropy g0).toReal := by
    change realEntropy g0.1 = _
    simp only [realEntropy, dif_pos g0.2]
  have hM0 : 0 ≤ realEntropy gamma0 := by rw [hreal0]; exact ENNReal.toReal_nonneg
  have he0 : spectralEntropy g0 = ENNReal.ofReal (realEntropy gamma0) := by
    rw [hreal0, ENNReal.ofReal_toReal (hf gamma0 hg0)]
  have hsub : A ⊆ energySublevel g0 (realEntropy gamma0) := by
    intro rho hrho
    refine ⟨hp rho hrho, ht rho hrho, ?_⟩
    exact (spectralEnergy_le_entropy_of_isMaxOn hconv hp ht hf g0 hg0 hmax0 rho hrho).trans_eq he0
  have hcompact : IsCompact A :=
    (isCompact_energySublevel g0 (realEntropy gamma0) hM0).of_isClosed_subset hclosed hsub
  obtain ⟨gamma, hgamma, hmax, sigma, hsigma, henergy, henergycontENN, henergycont⟩ :=
    fullCompactCommonReference hcompact hne hconv hp ht hf hc
  obtain ⟨code, hcode, w, hw1, hwm, hwlim, h, hh, hdef, hthermal, hcost⟩ :=
    exists_thermalHamiltonian_of_continuous_spectralEnergy sigma (ht sigma.1 hsigma)
      (nativeResolution sigma) hne hcompact hp ht
      (fun rho hrho => lt_top_iff_ne_top.mpr (henergy rho hrho).1) henergycont 1 (by norm_num)
  have hgn : 0 ≤ realEntropy gamma := by
    unfold realEntropy
    split_ifs
    · exact ENNReal.toReal_nonneg
    · exact le_rfl
  refine ⟨gamma, hgamma, hmax, sigma, hsigma, henergy, henergycontENN, henergycont,
    h, hh, hthermal, ?_, ?_⟩
  · have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · intro rho hrho
    have hR : (DiagonalEnergy.stateEnergy (nativeResolution sigma).basis h hh rho.1
        (TraceClass.isTraceClass_coe rho)).toReal ≤ 2 + realEntropy gamma + Real.log 2 := by
      have h1 := (hcost rho hrho).2.2
      have h2 := (henergy rho hrho).2.2
      norm_num only [NNReal.coe_one] at h1
      linarith
    have hfinite : DiagonalEnergy.stateEnergy (nativeResolution sigma).basis h hh rho.1
        (TraceClass.isTraceClass_coe rho) ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨by norm_num, (henergy rho hrho).1⟩, by norm_num⟩)
        (hcost rho hrho).2.1
    refine ⟨?_, hR⟩
    rw [← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal hR

#print axioms exists_thermalHamiltonian_of_continuous_spectralEnergy
#print axioms exists_thermalHamiltonian_of_continuous_entropy

end QuantumLogEnergy
