/- GID: D5/S3/Quantum/Analysis/TraceClass/FiniteEntropyRelativeEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/FiniteEntropyRelativeEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual normalized finite-entropy trace-log divergence and fixed-reference continuity. -/

import D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy
import D5.S3.Quantum.Analysis.TraceClass.KernelEnergy
import D5.S3.Quantum.Analysis.TraceClass.EntropyMaximizer
import D5.S3.Quantum.Analysis.TraceClass.CompactCommonReference
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open scoped ComplexOrder InnerProductSpace ENNReal
open Filter Topology
set_option backward.isDefEq.respectTransparency false
namespace QuantumLogEnergy
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The real trace pairing of the two bounded shifted CFC logarithms. -/
def traceLogGrid (rho sigma : Reference H) (n : ℕ) : ℝ :=
  (TraceClass.tracePairing
    (CFC.log (rho.1.1 + algebraMap ℝ (H →L[ℂ] H) ((n : ℝ) + 1)⁻¹) -
      CFC.log (sigma.1.1 + algebraMap ℝ (H →L[ℂ] H) ((n : ℝ) + 1)⁻¹)) rho.1).re

/-- Relative entropy on its actual normalized finite-entropy domain. The defining
quantity is the liminf of the bounded trace-log grid, also at infinite cross energy. -/
def finiteEntropyRelativeEntropy (rho sigma : Reference H)
    (_hr : (trace rho.1.1 (TraceClass.isTraceClass_coe rho.1)).re = 1)
    (_hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1)
    (_hS : spectralEntropy rho ≠ ∞) : ℝ≥0∞ :=
  liminf (fun n : ℕ => ENNReal.ofReal (traceLogGrid rho sigma n)) atTop

private theorem traceLogGrid_eq (rho sigma : Reference H) (n : ℕ) :
    traceLogGrid rho sigma n =
      regularizedEnergy ((n : ℝ) + 1)⁻¹ sigma.1.1 rho.1 -
        regularizedEnergy ((n : ℝ) + 1)⁻¹ rho.1.1 rho.1 := by
  have hop : logRegularization ((n : ℝ) + 1)⁻¹ sigma.1.1 -
      logRegularization ((n : ℝ) + 1)⁻¹ rho.1.1 =
      CFC.log (rho.1.1 + algebraMap ℝ (H →L[ℂ] H) ((n : ℝ) + 1)⁻¹) -
        CFC.log (sigma.1.1 + algebraMap ℝ (H →L[ℂ] H) ((n : ℝ) + 1)⁻¹) := by
    unfold logRegularization
    abel
  symm
  calc
    _ = (TraceClass.tracePairingContinuousLinearMap
        (logRegularization ((n : ℝ) + 1)⁻¹ sigma.1.1 -
          logRegularization ((n : ℝ) + 1)⁻¹ rho.1.1) rho.1).re := by
      rw [map_sub, ContinuousLinearMap.sub_apply, Complex.sub_re]
      rfl
    _ = _ := by rw [hop]; rfl

/-- Both shifted logarithms are bounded operators of strictly positive shifts.
Their literal products with rho are trace class, and cyclicity gives the rho-first
trace expression with exact cancellation of the common scalar logarithm. -/
theorem traceLogGrid_operators (rho sigma : Reference H) (n : ℕ) :
    let eps : ℝ := ((n : ℝ) + 1)⁻¹
    let Lr := CFC.log (rho.1.1 + algebraMap ℝ (H →L[ℂ] H) eps)
    let Ls := CFC.log (sigma.1.1 + algebraMap ℝ (H →L[ℂ] H) eps)
    IsStrictlyPositive (rho.1.1 + algebraMap ℝ (H →L[ℂ] H) eps) ∧
    IsStrictlyPositive (sigma.1.1 + algebraMap ℝ (H →L[ℂ] H) eps) ∧
    (∀ x, ‖Lr x‖ ≤ ‖Lr‖ * ‖x‖) ∧ (∀ x, ‖Ls x‖ ≤ ‖Ls‖ * ‖x‖) ∧
    IsTraceClass ((Lr - Ls) * rho.1.1) ∧ IsTraceClass (rho.1.1 * (Lr - Ls)) ∧
    traceLogGrid rho sigma n =
      (trace (rho.1.1 * (Lr - Ls))
        (by simpa using (isTraceClass_mul_mul (A := 1) (B := Lr - Ls)
          (TraceClass.isTraceClass_coe rho.1)))).re ∧
    traceLogGrid rho sigma n = regularizedEnergy eps sigma.1.1 rho.1 -
      regularizedEnergy eps rho.1.1 rho.1 := by
  dsimp only
  refine ⟨shift_strictlyPositive (by positivity) rho.2.1,
    shift_strictlyPositive (by positivity) sigma.2.1,
    fun x => ContinuousLinearMap.le_opNorm _ x, fun x => ContinuousLinearMap.le_opNorm _ x,
    TraceClass.isTraceClass_mul_coe _ rho.1, ?_, ?_, traceLogGrid_eq rho sigma n⟩
  · simpa using (isTraceClass_mul_mul (A := 1) (B :=
      CFC.log (rho.1.1 + algebraMap ℝ (H →L[ℂ] H) ((n : ℝ) + 1)⁻¹) -
        CFC.log (sigma.1.1 + algebraMap ℝ (H →L[ℂ] H) ((n : ℝ) + 1)⁻¹))
      (TraceClass.isTraceClass_coe rho.1))
  · unfold traceLogGrid
    rw [TraceClass.tracePairing_apply]
    exact congrArg Complex.re (trace_mul_cycle (TraceClass.isTraceClass_coe rho.1))

private theorem regularizedEnergy_limit (T : Reference H) (r : TraceClass H)
    (hr : 0 ≤ r.1) :
    Tendsto (fun n : ℕ => ENNReal.ofReal
      (regularizedEnergy ((n : ℝ) + 1)⁻¹ T.1.1 r)) atTop (𝓝 (spectralEnergy T r)) := by
  rw [spectralEnergy_eq_regularizedSupremum T r hr]
  exact tendsto_atTop_iSup (fun m n h =>
    ENNReal.ofReal_le_ofReal (monotone_regularizedEnergy T r hr h))

private theorem traceLogGrid_limit (rho sigma : Reference H)
    (hS : spectralEntropy rho ≠ ∞) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (traceLogGrid rho sigma n))
      atTop (𝓝 (spectralEnergy sigma rho.1 - spectralEntropy rho)) := by
  have hc := regularizedEnergy_limit sigma rho.1 rho.2.1
  have hs := regularizedEnergy_limit rho rho.1 rho.2.1
  rw [spectralEnergy_self] at hs
  have h := ENNReal.Tendsto.sub hc hs (Or.inr hS)
  convert h using 1
  funext n
  rw [(traceLogGrid_operators rho sigma n).2.2.2.2.2.2.2, ENNReal.ofReal_sub _
    (regularizedEnergy_nonneg (by positivity) rho rho.1 rho.2.1)]

/-- The actual liminf is spectral cross energy minus finite self entropy. -/
theorem finiteEntropyRelativeEntropy_eq_energy_tsub (rho sigma : Reference H)
    (hr : (trace rho.1.1 (TraceClass.isTraceClass_coe rho.1)).re = 1)
    (hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1)
    (hS : spectralEntropy rho ≠ ∞) :
    finiteEntropyRelativeEntropy rho sigma hr hs hS =
      spectralEnergy sigma rho.1 - spectralEntropy rho :=
  (traceLogGrid_limit rho sigma hS).liminf_eq

private theorem finiteRelative_eq (rho sigma : Reference H)
    (hr : (trace rho.1.1 (TraceClass.isTraceClass_coe rho.1)).re = 1)
    (hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1)
    (hS : spectralEntropy rho ≠ ∞) (hE : spectralEnergy sigma rho.1 ≠ ∞) :
    finiteEntropyRelativeEntropy rho sigma hr hs hS =
      ENNReal.ofReal ((spectralEnergy sigma rho.1).toReal - (spectralEntropy rho).toReal) := by
  rw [finiteEntropyRelativeEntropy_eq_energy_tsub, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hE, ENNReal.ofReal_toReal hS]

private theorem relative_lower (rho sigma : Reference H)
    (hr : (trace rho.1.1 (TraceClass.isTraceClass_coe rho.1)).re = 1)
    (hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1)
    (hS : spectralEntropy rho ≠ ∞) (hE : spectralEnergy sigma rho.1 ≠ ∞) :
    ‖rho.1 - sigma.1‖ ^ 2 / 4 ≤
      (spectralEnergy sigma rho.1).toReal - (spectralEntropy rho).toReal := by
  have h := ENNReal.toReal_mono hE (spectralEntropy_add_traceNorm_sq_le_energy rho sigma hr hs)
  rw [ENNReal.toReal_add hS ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)] at h
  linarith

/-- Finite energy gives the genuine unclamped real value and trace-norm separation;
infinite energy or failed kernel inclusion gives infinity. -/
theorem finiteEntropyRelativeEntropy_branches (rho sigma : Reference H)
    (hr : (trace rho.1.1 (TraceClass.isTraceClass_coe rho.1)).re = 1)
    (hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1)
    (hS : spectralEntropy rho ≠ ∞) :
    (∀ hE : spectralEnergy sigma rho.1 ≠ ∞,
      finiteEntropyRelativeEntropy rho sigma hr hs hS =
        ENNReal.ofReal ((spectralEnergy sigma rho.1).toReal - (spectralEntropy rho).toReal) ∧
      (finiteEntropyRelativeEntropy rho sigma hr hs hS).toReal =
        (spectralEnergy sigma rho.1).toReal - (spectralEntropy rho).toReal ∧
      ‖rho.1 - sigma.1‖ ^ 2 / 4 ≤
        (finiteEntropyRelativeEntropy rho sigma hr hs hS).toReal) ∧
    (spectralEnergy sigma rho.1 = ∞ → finiteEntropyRelativeEntropy rho sigma hr hs hS = ∞) ∧
    (¬ sigma.1.1.ker ≤ rho.1.1.ker → finiteEntropyRelativeEntropy rho sigma hr hs hS = ∞) := by
  have htop (hE : spectralEnergy sigma rho.1 = ∞) :
      finiteEntropyRelativeEntropy rho sigma hr hs hS = ∞ := by
    rw [finiteEntropyRelativeEntropy_eq_energy_tsub, hE, ENNReal.top_sub hS]
  refine ⟨?_, htop, ?_⟩
  · intro hE
    have heq := finiteRelative_eq rho sigma hr hs hS hE
    have hl := relative_lower rho sigma hr hs hS hE
    have hn : 0 ≤ (spectralEnergy sigma rho.1).toReal - (spectralEntropy rho).toReal :=
      (by positivity : 0 ≤ ‖rho.1 - sigma.1‖ ^ 2 / 4).trans hl
    exact ⟨heq, by rw [heq, ENNReal.toReal_ofReal hn], by rw [heq, ENNReal.toReal_ofReal hn]; exact hl⟩
  · intro hk
    apply htop
    by_contra hE
    exact hk (ker_le_ker_of_spectralEnergy_lt_top sigma rho.1 rho.2.1 (lt_top_iff_ne_top.mpr hE))

private theorem real_double_sums (rho sigma : Reference H)
    (d : SpectralResolution rho) (e : SpectralResolution sigma)
    (hS : spectralEntropy rho ≠ ∞) (hE : spectralEnergy sigma rho.1 ≠ ∞) :
    let a := fun p : d.index × e.index => d.values p.1 *
      ‖⟪e.basis p.2, d.basis p.1⟫_ℂ‖ ^ 2 * (-Real.log (e.values p.2))
    let b := fun p : d.index × e.index =>
      (-d.values p.1 * Real.log (d.values p.1)) * ‖⟪e.basis p.2, d.basis p.1⟫_ℂ‖ ^ 2
    (∀ p, 0 ≤ a p) ∧ (∀ p, 0 ≤ b p) ∧ Summable a ∧ Summable b ∧
      (∑' p, a p) = (spectralEnergy sigma rho.1).toReal ∧
      (∑' p, b p) = (spectralEntropy rho).toReal ∧
      (∀ i j, e.values j = 0 → d.values i * ‖⟪e.basis j, d.basis i⟫_ℂ‖ ^ 2 = 0) := by
  classical
  let c := fun (i : d.index) (j : e.index) => ‖⟪e.basis j, d.basis i⟫_ℂ‖ ^ 2
  let f := fun p : d.index × e.index =>
    (ENNReal.ofReal (d.values p.1) * singularLog (e.values p.2)) * ENNReal.ofReal (c p.1 p.2)
  have hsum : (∑' p, f p) = spectralEnergy sigma rho.1 := by
    rw [ENNReal.tsum_prod']
    exact resolution_cross_energy rho sigma d e
  have hf (p) : f p ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top (hsum ▸ hE) p
  have hz (i : d.index) (j : e.index) (hj : e.values j = 0) :
      d.values i * c i j = 0 := by
    have ht := hf (i,j)
    have heq : f (i,j) = ENNReal.ofReal (d.values i * c i j) * ∞ := by
      dsimp [f]
      rw [singularLog, if_pos hj, ENNReal.ofReal_mul (d.nonneg i)]
      ac_rfl
    rw [heq] at ht
    have hw : ENNReal.ofReal (d.values i * c i j) = 0 := by
      by_contra hw
      exact ht (ENNReal.mul_top hw)
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hw) (mul_nonneg (d.nonneg _) (sq_nonneg _))
  let a := fun p : d.index × e.index => d.values p.1 * c p.1 p.2 * (-Real.log (e.values p.2))
  let b := fun p : d.index × e.index => (-d.values p.1 * Real.log (d.values p.1)) * c p.1 p.2
  have ha (p) : 0 ≤ a p := mul_nonneg (mul_nonneg (d.nonneg _) (sq_nonneg _))
    (neg_nonneg.mpr (Real.log_nonpos (e.nonneg _) (spectral_value_le_one sigma e.basis e.values e.eigen _)))
  have hb (p) : 0 ≤ b p := mul_nonneg
    (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (d.nonneg _))
      (Real.log_nonpos (d.nonneg _) (spectral_value_le_one rho d.basis d.values d.eigen _)))
    (sq_nonneg _)
  have hfa (p) : ENNReal.ofReal (a p) = f p := by
    by_cases hj : e.values p.2 = 0
    · have hw := hz p.1 p.2 hj
      dsimp [a]
      rw [hw, zero_mul, ENNReal.ofReal_zero]
      dsimp [f]
      rw [singularLog, if_pos hj]
      have heq : (ENNReal.ofReal (d.values p.1) * ∞) * ENNReal.ofReal (c p.1 p.2) =
          ENNReal.ofReal (d.values p.1 * c p.1 p.2) * ∞ := by
        rw [ENNReal.ofReal_mul (d.nonneg _)]
        ac_rfl
      rw [heq, hw, ENNReal.ofReal_zero, zero_mul]
    · dsimp [a, f, c]
      rw [singularLog, if_neg hj, ENNReal.ofReal_mul (mul_nonneg (d.nonneg _) (sq_nonneg _)),
        ENNReal.ofReal_mul (d.nonneg _)]
      ac_rfl
  have hasum : (∑' p, ENNReal.ofReal (a p)) = spectralEnergy sigma rho.1 := by
    simp_rw [hfa]
    exact hsum
  have hbsum : (∑' p, ENNReal.ofReal (b p)) = spectralEntropy rho := by
    rw [ENNReal.tsum_prod']
    simp_rw [b, ENNReal.ofReal_mul (mul_nonneg_of_nonpos_of_nonpos
      (neg_nonpos.mpr (d.nonneg _)) (Real.log_nonpos (d.nonneg _)
        (spectral_value_le_one rho d.basis d.values d.eigen _))), ENNReal.tsum_mul_left]
    have hrow (i : d.index) : (∑' j, ENNReal.ofReal (c i j)) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _)
        (hasSum_norm_sq_inner_basis e.basis (d.basis i)).summable,
        (hasSum_norm_sq_inner_basis e.basis (d.basis i)).tsum_eq, d.basis.orthonormal.1 i]
      norm_num
    simp_rw [hrow, mul_one]
    exact resolution_entropy rho d
  have hsa : Summable a := by
    have h := ENNReal.summable_toReal (hasum ▸ hE)
    simpa only [ENNReal.toReal_ofReal (ha _)] using h
  have hsb : Summable b := by
    have h := ENNReal.summable_toReal (hbsum ▸ hS)
    simpa only [ENNReal.toReal_ofReal (hb _)] using h
  refine ⟨ha, hb, hsa, hsb, ?_, ?_, hz⟩
  · rw [← hasum, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal (ha _)]
    rfl
  · rw [← hbsum, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal (hb _)]
    rfl

/-- Full arbitrary spectral resolutions, including zero fibers, give an absolutely
summable signed logarithmic formula. The real sum is asserted only at finite energy. -/
theorem finiteEntropyRelativeEntropy_spectral (rho sigma : Reference H)
    (hr : (trace rho.1.1 (TraceClass.isTraceClass_coe rho.1)).re = 1)
    (hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1)
    (hS : spectralEntropy rho ≠ ∞) (hE : spectralEnergy sigma rho.1 ≠ ∞)
    (d : SpectralResolution rho) (e : SpectralResolution sigma) :
    let f := fun p : d.index × e.index => d.values p.1 *
      ‖⟪e.basis p.2, d.basis p.1⟫_ℂ‖ ^ 2 *
        (Real.log (d.values p.1) - Real.log (e.values p.2))
    Summable (fun p => |f p|) ∧
      (∑' p, f p) = (spectralEnergy sigma rho.1).toReal - (spectralEntropy rho).toReal ∧
      (∑' i, ∑' j, f (i,j)) = ∑' p, f p ∧
      finiteEntropyRelativeEntropy rho sigma hr hs hS = ENNReal.ofReal (∑' p, f p) ∧
      (finiteEntropyRelativeEntropy rho sigma hr hs hS).toReal = ∑' p, f p ∧
      (∀ i j, e.values j = 0 → d.values i * ‖⟪e.basis j, d.basis i⟫_ℂ‖ ^ 2 = 0) := by
  classical
  obtain ⟨ha, hb, hsa, hsb, hta, htb, hz⟩ := real_double_sums rho sigma d e hS hE
  let a := fun p : d.index × e.index => d.values p.1 *
    ‖⟪e.basis p.2, d.basis p.1⟫_ℂ‖ ^ 2 * (-Real.log (e.values p.2))
  let b := fun p : d.index × e.index =>
    (-d.values p.1 * Real.log (d.values p.1)) * ‖⟪e.basis p.2, d.basis p.1⟫_ℂ‖ ^ 2
  let f := fun p : d.index × e.index => d.values p.1 *
    ‖⟪e.basis p.2, d.basis p.1⟫_ℂ‖ ^ 2 *
      (Real.log (d.values p.1) - Real.log (e.values p.2))
  have heq : f = fun p => a p - b p := by funext p; dsimp [f, a, b]; ring
  have hsf : Summable f := by rw [heq]; exact hsa.sub hsb
  have htf : (∑' p, f p) =
      (spectralEnergy sigma rho.1).toReal - (spectralEntropy rho).toReal := by
    rw [heq, hsa.tsum_sub hsb, hta, htb]
  refine ⟨hsf.abs, htf, ?_, ?_, ?_, hz⟩
  · exact (hsf.tsum_prod' hsf.prod_factor).symm
  · rw [htf]
    exact finiteRelative_eq rho sigma hr hs hS hE
  · rw [htf]
    exact ((finiteEntropyRelativeEntropy_branches rho sigma hr hs hS).1 hE).2.1

/-- A fixed reference for the original closed convex finite continuous entropy
premises. Compactness is a consequence, and the functions are the actual trace-log
liminf divergence, in the original trace-norm topology. -/
theorem closedConvex_finiteEntropy_commonReference {A : Set (TraceClass H)}
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hp : ∀ r ∈ A, 0 ≤ r.1)
    (ht : ∀ r ∈ A, (trace r.1 (TraceClass.isTraceClass_coe r)).re = 1)
    (hf : ∀ (r) (h : r ∈ A), spectralEntropy
      (⟨r, hp r h, density_le_one r (hp r h) (ht r h)⟩ : Reference H) ≠ ∞)
    (hc : ContinuousOn realEntropy A) :
    let R : A → Reference H := fun r =>
      ⟨r.1, hp r.1 r.2, density_le_one r.1 (hp r.1 r.2) (ht r.1 r.2)⟩
    IsCompact A ∧ ∃ gamma ∈ A, IsMaxOn realEntropy A gamma ∧
      ∃ (sigma : Reference H)
        (hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1),
      sigma.1 ∈ A ∧
      (∀ r : A, finiteEntropyRelativeEntropy (R r) sigma (ht r.1 r.2) hs (hf r.1 r.2) ≠ ∞ ∧
        (finiteEntropyRelativeEntropy (R r) sigma (ht r.1 r.2) hs (hf r.1 r.2)).toReal ≤
          realEntropy gamma + Real.log 2 ∧
        ‖r.1 - sigma.1‖ ^ 2 / 4 ≤
          (finiteEntropyRelativeEntropy (R r) sigma (ht r.1 r.2) hs (hf r.1 r.2)).toReal) ∧
      Continuous (fun r : A =>
        finiteEntropyRelativeEntropy (R r) sigma (ht r.1 r.2) hs (hf r.1 r.2)) ∧
      Continuous (fun r : A =>
        (finiteEntropyRelativeEntropy (R r) sigma (ht r.1 r.2) hs (hf r.1 r.2)).toReal) := by
  classical
  let R : A → Reference H := fun r =>
    ⟨r.1, hp r.1 r.2, density_le_one r.1 (hp r.1 r.2) (ht r.1 r.2)⟩
  obtain ⟨_, g, hg, hmax, _, _⟩ :=
    exists_unique_entropy_maximizer hne hclosed hconv hp ht hf hc
  let G : Reference H := ⟨g, hp g hg, density_le_one g (hp g hg) (ht g hg)⟩
  have hsub : A ⊆ energySublevel G (realEntropy g) := by
    intro r hr
    refine ⟨hp r hr, ht r hr, ?_⟩
    have he := spectralEnergy_le_entropy_of_isMaxOn hconv hp ht hf G hg hmax r hr
    rwa [realEntropy_reference G, ENNReal.ofReal_toReal (hf g hg)]
  have hcompact : IsCompact A :=
    (isCompact_energySublevel G (realEntropy g)
      (by rw [realEntropy_reference G]; exact ENNReal.toReal_nonneg)).of_isClosed_subset hclosed hsub
  obtain ⟨gamma, hgamma, hgmax, sigma, hsmem, hbound, _, hecont⟩ :=
    fullCompactCommonReference hcompact hne hconv hp ht hf hc
  have hs : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1 := ht sigma.1 hsmem
  have hval (r : A) :
      (finiteEntropyRelativeEntropy (R r) sigma (ht r.1 r.2) hs (hf r.1 r.2)).toReal =
        (spectralEnergy sigma r.1).toReal - realEntropy r.1 := by
    rw [realEntropy_reference (R r)]
    exact ((finiteEntropyRelativeEntropy_branches (R r) sigma (ht r.1 r.2) hs
      (hf r.1 r.2)).1 (hbound r.1 r.2).1).2.1
  have hfinite (r : A) :
      finiteEntropyRelativeEntropy (R r) sigma (ht r.1 r.2) hs (hf r.1 r.2) ≠ ∞ := by
    rw [finiteRelative_eq (R r) sigma (ht r.1 r.2) hs (hf r.1 r.2) (hbound r.1 r.2).1]
    exact ENNReal.ofReal_ne_top
  have hreal : Continuous (fun r : A =>
      (finiteEntropyRelativeEntropy (R r) sigma (ht r.1 r.2) hs (hf r.1 r.2)).toReal) := by
    simp_rw [hval]
    exact (continuousOn_iff_continuous_domRestrict.mp hecont).sub
      (continuousOn_iff_continuous_domRestrict.mp hc)
  refine ⟨hcompact, gamma, hgamma, hgmax, sigma, hs, hsmem, ?_, ?_, hreal⟩
  · intro r
    refine ⟨hfinite r, ?_, ?_⟩
    · rw [hval]
      have hn : 0 ≤ realEntropy r.1 := by rw [realEntropy_reference (R r)]; exact ENNReal.toReal_nonneg
      exact (sub_le_self _ hn).trans (hbound r.1 r.2).2.2
    · exact ((finiteEntropyRelativeEntropy_branches (R r) sigma (ht r.1 r.2) hs
        (hf r.1 r.2)).1 (hbound r.1 r.2).1).2.2
  · convert ENNReal.continuous_ofReal.comp hreal using 1
    funext r
    exact (ENNReal.ofReal_toReal (hfinite r)).symm

#print axioms finiteEntropyRelativeEntropy_eq_energy_tsub
#print axioms finiteEntropyRelativeEntropy_branches
#print axioms finiteEntropyRelativeEntropy_spectral
#print axioms closedConvex_finiteEntropy_commonReference
end QuantumLogEnergy
