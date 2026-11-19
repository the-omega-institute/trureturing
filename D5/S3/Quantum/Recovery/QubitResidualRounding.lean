/- GID: D5/S3/Quantum/Recovery/QubitResidualRounding
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/QubitResidualRounding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dimension-independent fifth-root repair from the actual recovered residual. -/

import D5.S3.Quantum.Recovery.QubitPhysicalRepair


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Recovery.QubitResidualRounding

open _root_.Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.StrongSubadditivity
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator Kronecker

local notation "traceNorm" => D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm

variable {Q : Type*} [Fintype Q]

section MarginalCoherence

variable {A C E : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype E] [DecidableEq E]

private theorem qubit_density_entries (b : DensityState (Fin 2)) :
    ‖b.1 0 0 - b.1 1 1‖ ≤ 1 ∧ ‖b.1 1 0‖ ≤ 1 := by
  have hp := density_posSemidef b
  have h0 := Complex.nonneg_iff.mp (hp.diag_nonneg (i := 0))
  have h1 := Complex.nonneg_iff.mp (hp.diag_nonneg (i := 1))
  change 0 ≤ (b.1 0 0).re ∧ 0 = (b.1 0 0).im at h0
  change 0 ≤ (b.1 1 1).re ∧ 0 = (b.1 1 1).im at h1
  have ht : (b.1 0 0).re + (b.1 1 1).re = 1 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using congrArg Complex.re b.2.2
  have hr : b.1 0 0 - b.1 1 1 = ((b.1 0 0).re - (b.1 1 1).re : ℝ) := by
    apply Complex.ext
    · simp
    · simp only [Complex.sub_im, Complex.ofReal_im]
      linarith [h0.2, h1.2]
  constructor
  · rw [hr, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · have he := D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound hp 1 0
    rw [Complex.normSq_eq_norm_sq] at he
    change ‖b.1 1 0‖ ^ 2 ≤ (b.1 1 1).re * (b.1 0 0).re at he
    nlinarith [norm_nonneg (b.1 1 0),sq_nonneg ((b.1 0 0).re-(b.1 1 1).re)]

/-- The actual B-marginal equation controls its coherence through the same
phase-sensitive gap and the two actual flip columns. -/
theorem marginal_coherence_gap_bound
    (W : Matrix (Fin 2 × (C × E)) (Fin 2) ℂ) (hW : Wᴴ * W = 1)
    (b : DensityState (Fin 2)) (r f d : ℝ)
    (he : traceNorm (reduced W (CStarMatrix.ofMatrix.symm b.1) -
      CStarMatrix.ofMatrix.symm b.1) ≤ 2*r)
    (hf : ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 ≤ f)
    (hd : ‖inner ℂ (column W 1 0) (column W 0 0) -
      inner ℂ (column W 1 1) (column W 0 1)‖ ≤ d) :
    ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖ * ‖b.1 0 1‖ ≤
      r + Real.sqrt (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2) *
        Real.sqrt ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖ + d/2 + f/2 := by
  let M := CStarMatrix.ofMatrix.symm b.1
  let u := inner ℂ (column W 1 0) (column W 0 0)
  let v := inner ℂ (column W 1 1) (column W 0 1)
  let kap := inner ℂ (column W 1 0) (column W 0 1)
  have hm : M.IsHermitian := (density_posSemidef b).isHermitian
  have ht : M 0 0 + M 1 1 = 1 := by
    change b.1 0 0 + b.1 1 1 = 1
    simpa [Matrix.trace,Fin.sum_univ_two] using b.2.2
  have hres := (traceless_qubit_entry_bounds (reduced W M-M)
    ((reduced_hermitian W M hm).sub hm)
    (by rw [Matrix.trace_sub,reduced_trace W hW,sub_self])).2
  have hres' : ‖(reduced W M-M) 0 1‖ ≤ r := by linarith
  obtain ⟨hentry,hkap,hsum⟩ := isometry_coefficient_geometry W hW
  have heq : (1-inner ℂ (column W 1 1) (column W 0 0))*M 0 1 =
      -(reduced W M-M) 0 1 + (u+v)/2 + (u-v)*(M 0 0-M 1 1)/2 + kap*M 1 0 := by
    have h := hentry M
    change reduced W M 0 1 = _ + u*M 0 0 + v*M 1 1 + kap*M 1 0 at h
    simp only [Matrix.sub_apply]
    linear_combination h + (u+v)*ht/2
  obtain ⟨hdiag,h10⟩ := qubit_density_entries b
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  have hf0 : 0 ≤ f := (by positivity : 0 ≤ ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2).trans hf
  have hsum' : ‖(u+v)/2‖ ≤
      Real.sqrt (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2) *
      Real.sqrt ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖ := by
    rw [norm_div]; norm_num
    dsimp only [u,v] at ⊢
    linarith
  have hdiff : ‖(u-v)*(M 0 0-M 1 1)/2‖ ≤ d/2 := by
    rw [norm_div,norm_mul]; norm_num
    have h := mul_le_mul hd hdiag (norm_nonneg _) hd0
    change ‖u-v‖ * ‖M 0 0-M 1 1‖ ≤ d*1 at h
    linarith
  have hk : ‖kap*M 1 0‖ ≤ f/2 := by
    rw [norm_mul]
    have h := mul_le_mul (hkap.trans (by linarith)) h10 (norm_nonneg _) (by positivity : 0 ≤ f/2)
    change ‖kap‖ * ‖b.1 1 0‖ ≤ _
    simpa only [mul_one] using h
  change ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖ * ‖M 0 1‖ ≤ _
  rw [← norm_mul,heq]
  exact ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (by simpa only [norm_neg] using hres') hsum'))
      hdiff)) hk)).trans (by ring_nf; rfl)

end MarginalCoherence


section ActualOffDiagonal

variable {A : Type*} [Fintype A] [DecidableEq A]

private theorem density_smul_traceNorm_le (a : DensityState A) (z : ℂ) :
    traceNorm (z • CStarMatrix.ofMatrix.symm a.1) ≤ ‖z‖ := by
  obtain ⟨U,hU⟩ := (traceNorm_eq_max_re_tr_U (z • CStarMatrix.ofMatrix.symm a.1)).1
  have ht : traceNorm (CStarMatrix.ofMatrix.symm a.1) = 1 :=
    (congrArg Complex.re (traceNorm_of_posSemidef (density_posSemidef a))).trans
      (congrArg Complex.re a.2.2)
  have he : U.val * (z • CStarMatrix.ofMatrix.symm a.1) =
      (z • U.val) * CStarMatrix.ofMatrix.symm a.1 := by
    rw [Matrix.mul_smul,Matrix.smul_mul]
  rw [← hU,he]
  have h := D5.S3.Quantum.Matrix.UniformVarianceTraceBound.re_trace_mul_le
    (z • U.val) (CStarMatrix.ofMatrix.symm a.1)
  rw [ht,mul_one,norm_smul] at h
  exact h.trans (by
    have hu := isometry_operatorNorm_le U.val (Unitary.coe_star_mul_self U)
    nlinarith [norm_nonneg z])

private theorem actual_offDiagonal_le (P : DensityState (A × Fin 2)) :
    traceNorm (block (CStarMatrix.ofMatrix.symm P.1) 0 1) ≤
      traceNorm (block (centered P) 0 1) + ‖(marginalLeft P).1 0 1‖ := by
  have he : block (CStarMatrix.ofMatrix.symm P.1) 0 1 = block (centered P) 0 1 +
      (marginalLeft P).1 0 1 • CStarMatrix.ofMatrix.symm (marginalRight P).1 := by
    ext a b
    simp [block,centered,productState,Matrix.kronecker_apply,smul_eq_mul]
    ring
  rw [he]
  exact (D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_add_le _ _).trans
    (add_le_add le_rfl
    (density_smul_traceNorm_le (marginalRight P) _))

end ActualOffDiagonal


section ScaleAlgebra

private theorem fifth_scale_basic (delta r x f : ℝ)
    (hdelta : 0 < delta) (hsmall : delta ≤ 1/6) (hr : r = delta^5)
    (hx : delta < x) (hf0 : 0 ≤ f) (hf : f ≤ 2*r/x) :
    2*r/x ≤ 2*delta^4 ∧ Real.sqrt f ≤ (3/2)*delta^2 ∧ f < 1 ∧
      r ≤ delta ∧ delta^2 ≤ delta/6 ∧ delta^3 ≤ delta/36 := by
  have hd0 := hdelta.le
  have hd1 : delta ≤ 1 := by linarith
  have hx0 : 0 < x := hdelta.trans hx
  have hq : 2*r/x ≤ 2*delta^4 := by
    apply (div_le_iff₀ hx0).mpr
    rw [hr]
    have h := mul_le_mul_of_nonneg_left hx.le (pow_nonneg hd0 4)
    nlinarith
  have hsq := Real.sq_sqrt hf0
  have hs0 := Real.sqrt_nonneg f
  have hs : Real.sqrt f ≤ (3/2)*delta^2 := by
    nlinarith [hf.trans hq,sq_nonneg (delta^2)]
  have hd2 : delta^2 ≤ delta/6 := by nlinarith
  have hd3 : delta^3 ≤ delta/36 := by
    have h := mul_le_mul_of_nonneg_left hd2 hd0
    nlinarith
  have hr1 : r ≤ delta := by
    rw [hr]
    exact pow_le_of_le_one hd0 hd1 (by decide : (5 : ℕ) ≠ 0)
  have hf1 : f < 1 := by
    have h4 := pow_le_pow_left₀ hd0 hsmall 4
    nlinarith [hf.trans hq]
  exact ⟨hq,hs,hf1,hr1,hd2,hd3⟩

private theorem fifth_scale_small_gap (delta r s g : ℝ)
    (hd : 0 ≤ delta) (hr : r ≤ delta) (hd2 : delta^2 ≤ delta/6)
    (hs : s ≤ (3/2)*delta^2) (hg0 : 0 ≤ g) (hg : g ≤ delta^2) :
    r+2*s+Real.sqrt (2*g) ≤ 6*delta := by
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2*g)
  have hn := Real.sqrt_nonneg (2*g)
  have hb : Real.sqrt (2*g) ≤ (3/2)*delta := by nlinarith [sq_nonneg delta]
  linarith

private theorem fifth_scale_classical (delta r s g z b : ℝ)
    (hd : 0 < delta) (hrpow : r = delta^5) (hr : r ≤ delta)
    (hd2 : delta^2 ≤ delta/6) (hd3 : delta^3 ≤ delta/36)
    (hs : s ≤ (3/2)*delta^2) (hg : delta^2 < g)
    (hz : z ≤ 16*r/g+b) (hb : b ≤ delta) :
    r+z+2*s ≤ 6*delta := by
  have hg0 : 0 < g := lt_of_le_of_lt (sq_nonneg delta) hg
  have hdiv : 16*r/g ≤ 16*delta^3 := by
    apply (div_le_iff₀ hg0).mpr
    rw [hrpow]
    have h := mul_le_mul_of_nonneg_left hg.le (pow_nonneg hd.le 3)
    nlinarith
  linarith

private theorem fifth_scale_large_coherence (delta r x f g b : ℝ)
    (hd : 0 < delta) (hdsmall : delta ≤ 1/6) (hrpow : r = delta^5)
    (hx : delta < x) (hf0 : 0 ≤ f) (hf : f ≤ 2*r/x)
    (hg0 : 0 ≤ g) (hb : delta < b)
    (he : g*b ≤ r+Real.sqrt f*Real.sqrt g+2*r/x) :
    r+2*Real.sqrt f+Real.sqrt (2*g) ≤ 6*delta := by
  obtain ⟨hq,hs,hf1,hr,hd2,hd3⟩ := fifth_scale_basic delta r x f hd hdsmall hrpow hx hf0 hf
  have hy0 := Real.sqrt_nonneg g
  have hyy := Real.sq_sqrt hg0
  have hr4 : r ≤ delta^4 := by
    rw [hrpow]
    exact pow_le_pow_of_le_one hd.le (by linarith) (by decide : (4 : ℕ) ≤ 5)
  have hsy := mul_le_mul_of_nonneg_right hs hy0
  have hbg := mul_le_mul_of_nonneg_left hb.le hg0
  have hy : (Real.sqrt g)^2 ≤ 3*delta^3+(3/2)*delta*Real.sqrt g := by
    apply (mul_le_mul_iff_right₀ hd).mp
    nlinarith
  have hy3 : Real.sqrt g ≤ 3*delta := by
    by_contra hn
    have hgt : 3*delta < Real.sqrt g := lt_of_not_ge hn
    have hp := mul_pos (sub_pos.mpr hgt) (lt_trans (by positivity : 0 < 3*delta) hgt)
    have hp' := mul_lt_mul_of_pos_left hgt hd
    have hd32 : delta^3 ≤ delta^2 :=
      pow_le_pow_of_le_one hd.le (by linarith) (by decide : (2 : ℕ) ≤ 3)
    nlinarith
  have hdg : Real.sqrt (2*g) ≤ (3/2)*Real.sqrt g := by
    have heq := Real.sq_sqrt (by positivity : 0 ≤ 2*g)
    nlinarith [Real.sqrt_nonneg (2*g)]
  linarith

end ScaleAlgebra


section WholeRepair

variable {A C : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C]

private theorem dilation_reduced {E : Type*} [Fintype E] [DecidableEq E]
    (T : QuantumChannel (Fin 2) (Fin 2 × C))
    (W : Matrix (Fin 2 × (C × E)) (Fin 2) ℂ)
    (hT : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (j k : Fin 2) (c d : C),
      (∑ e : E, (W*M*Wᴴ) (j,(c,e)) (k,(d,e))) =
        CStarMatrix.ofMatrix.symm (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix M))
          (j,c) (k,d)) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    reduced W M = CStarMatrix.ofMatrix.symm (reducedAction T (CStarMatrix.ofMatrix M)) := by
  ext j k
  change (∑ p : C × E, (W*M*Wᴴ) (j,p) (k,p)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [hT]
  rfl

private theorem actual_dilation_marginal_residual {E : Type*} [Fintype E] [DecidableEq E]
    (rho : DensityState (A × (Fin 2 × C)))
    (T : QuantumChannel (Fin 2) (Fin 2 × C))
    (W : Matrix (Fin 2 × (C × E)) (Fin 2) ℂ)
    (hT : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (j k : Fin 2) (c d : C),
      (∑ e : E, (W*M*Wᴴ) (j,(c,e)) (k,(d,e))) =
        CStarMatrix.ofMatrix.symm (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix M))
          (j,c) (k,d)) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
    let b := marginalLeft P
    traceNorm (reduced W (CStarMatrix.ofMatrix.symm b.1)-CStarMatrix.ofMatrix.symm b.1) ≤
      2*traceDistance rho (referenceState T P) := by
  dsimp only
  rw [dilation_reduced T W hT]
  have h := actual_B_residual rho T
  rw [← neg_sub, D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm_neg]
  exact h

private theorem repair_back (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (rho : DensityState (A × (Fin 2 × C)))
    (T : QuantumChannel (Fin 2) (Fin 2 × C)) (bound : ℝ)
    (h : ∃ sigma : DensityState (A × (Fin 2 × C)),
      qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState sigma) = 0 ∧
      traceDistance (localBState U rho) sigma ≤ bound) :
    ∃ sigma : DensityState (A × (Fin 2 × C)),
      qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState sigma) = 0 ∧
      traceDistance rho sigma ≤ bound := by
  obtain ⟨sigma,hq,hd⟩ := h
  obtain ⟨_,_,_,_,_,_,hback⟩ := actual_B_unitary_transport U rho T
  obtain ⟨hd',hq'⟩ := hback sigma
  exact ⟨localBState (star U) sigma,hq'.trans hq,hd'.trans_le hd⟩

private theorem repair_positive_small_scale
    (rho : DensityState (A × (Fin 2 × C)))
    (T : QuantumChannel (Fin 2) (Fin 2 × C)) (delta : ℝ)
    (hd : 0 < delta) (hdsmall : delta ≤ 1/6)
    (hrpow : traceDistance rho (referenceState T
      (marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho))) = delta^5) :
    ∃ sigma : DensityState (A × (Fin 2 × C)),
      qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState sigma) = 0 ∧
      traceDistance rho sigma ≤ 6*delta := by
  let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
  let r := traceDistance rho (referenceState T P)
  obtain ⟨F,hF,hFn,hmax,sigma,hq,hsmall⟩ := product_repair_of_centered_correlation rho T
  let x := ‖sliceLinear (centered P) F‖
  have hr : r ≤ delta := by
    rw [show r = delta^5 from hrpow]
    exact pow_le_of_le_one hd.le (by linarith) (by decide : (5 : ℕ) ≠ 0)
  by_cases hx : x ≤ delta
  · exact ⟨sigma,hq,hsmall.trans (by change r+3*x ≤ _; linarith)⟩
  have hx' : delta < x := lt_of_not_ge hx
  obtain ⟨U,W,hW,hT,hm,he,hflip,hdiff,hblock⟩ :=
    actual_diagonal_geometry rho T F hF hFn hmax (hd.trans hx')
  let rhoU := localBState U rho
  let TU := localBChannel U T
  let PU := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rhoU)
  let f := ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2
  let g := ‖1-inner ℂ (column W 1 1) (column W 0 0)‖
  let b := ‖(marginalLeft PU).1 0 1‖
  let z := traceNorm (block (CStarMatrix.ofMatrix.symm PU.1) 0 1)
  have hf0 : 0 ≤ f := by positivity
  obtain ⟨hquot,hs,hf1,_,hd2,hd3⟩ :=
    fifth_scale_basic delta r x f hd hdsmall hrpow hx' hf0 hflip
  have hru : traceDistance rhoU (referenceState TU PU) = r := by
    dsimp only [rhoU,TU,PU]
    rw [localBState_AB,localBChannel_reference]
    exact traceDistance_conjugateState _ _ _
  apply repair_back U rho T
  by_cases hg : g ≤ delta^2
  · obtain ⟨sigma,hq,ht⟩ := common_environment_product_repair rhoU TU W hW hT hf1
    refine ⟨sigma,hq,ht.trans ?_⟩
    rw [hru]
    exact fifth_scale_small_gap delta r (Real.sqrt f) g hd.le hr hd2 hs (norm_nonneg _) hg
  have hg' : delta^2 < g := lt_of_not_ge hg
  have hg0 : 0 < g := lt_of_le_of_lt (sq_nonneg delta) hg'
  by_cases hb : b ≤ delta
  · obtain ⟨sigma,hq,ht⟩ := classical_pointer_repair rhoU TU W hW hT hf1
    have hz : z ≤ 16*r/g+b :=
      (actual_offDiagonal_le PU).trans (add_le_add (hblock hg0) le_rfl)
    refine ⟨sigma,hq,ht.trans ?_⟩
    rw [hru]
    exact fifth_scale_classical delta r (Real.sqrt f) g z b hd hrpow hr hd2 hd3 hs hg' hz hb
  have hres := actual_dilation_marginal_residual rhoU TU W hT
  change traceNorm (reduced W (CStarMatrix.ofMatrix.symm (marginalLeft PU).1) -
    CStarMatrix.ofMatrix.symm (marginalLeft PU).1) ≤
    2*traceDistance rhoU (referenceState TU PU) at hres
  rw [hru] at hres
  have hcoh := marginal_coherence_gap_bound W hW (marginalLeft PU) r (2*r/x) (2*r/x)
    hres hflip hdiff
  have hcoh' : g*b ≤ r+Real.sqrt f*Real.sqrt g+2*r/x := by
    change g*b ≤ _ at hcoh
    linarith
  obtain ⟨sigma,hq,ht⟩ := common_environment_product_repair rhoU TU W hW hT hf1
  refine ⟨sigma,hq,ht.trans ?_⟩
  rw [hru]
  exact fifth_scale_large_coherence delta r x f g b hd hdsmall hrpow hx' hf0 hflip
    (norm_nonneg _) (lt_of_not_ge hb) hcoh'


private theorem repair_zero_residual
    (rho : DensityState (A × (Fin 2 × C)))
    (T : QuantumChannel (Fin 2) (Fin 2 × C))
    (hr0 : traceDistance rho (referenceState T
      (marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho))) = 0) :
    ∃ sigma : DensityState (A × (Fin 2 × C)),
      qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState sigma) = 0 ∧
      traceDistance rho sigma ≤ 0 := by
  let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
  obtain ⟨F,hF,hFn,hmax,sigma,hq,hsmall⟩ := product_repair_of_centered_correlation rho T
  let x := ‖sliceLinear (centered P) F‖
  by_cases hx : x = 0
  · refine ⟨sigma,hq,?_⟩
    change traceDistance rho sigma ≤ traceDistance rho (referenceState T P)+3*x at hsmall
    have hrP : traceDistance rho (referenceState T P) = 0 := hr0
    simpa only [hrP,hx,mul_zero,add_zero] using hsmall
  have hx0 : 0 < x := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
  obtain ⟨U,W,hW,hT,hm,he,hflip,hdiff,hblock⟩ :=
    actual_diagonal_geometry rho T F hF hFn hmax hx0
  let rhoU := localBState U rho
  let TU := localBChannel U T
  let PU := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rhoU)
  let f := ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2
  let g := ‖1-inner ℂ (column W 1 1) (column W 0 0)‖
  have hf0 : f = 0 := by
    have hf : 0 ≤ f := by positivity
    change f ≤ 2*traceDistance rho (referenceState T P)/x at hflip
    rw [hr0, mul_zero, zero_div] at hflip
    exact le_antisymm hflip hf
  have hf1 : f < 1 := by rw [hf0]; norm_num
  have hru : traceDistance rhoU (referenceState TU PU) = 0 := by
    dsimp only [rhoU,TU,PU]
    rw [localBState_AB,localBChannel_reference]
    exact (traceDistance_conjugateState _ _ _).trans hr0
  apply repair_back U rho T
  by_cases hg : g = 0
  · obtain ⟨sigma,hq,ht⟩ := common_environment_product_repair rhoU TU W hW hT hf1
    refine ⟨sigma,hq,?_⟩
    change traceDistance rhoU sigma ≤ traceDistance rhoU (referenceState TU PU)+
      2*Real.sqrt f+Real.sqrt (2*g) at ht
    simpa only [hru,hf0,hg,Real.sqrt_zero,mul_zero,add_zero] using ht
  have hg0 : 0 < g := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg)
  have hres := actual_dilation_marginal_residual rhoU TU W hT
  change traceNorm (reduced W (CStarMatrix.ofMatrix.symm (marginalLeft PU).1)-
      CStarMatrix.ofMatrix.symm (marginalLeft PU).1) ≤
      2*traceDistance rhoU (referenceState TU PU) at hres
  rw [hru,mul_zero] at hres
  have hd0 : ‖inner ℂ (column W 1 0) (column W 0 0)-
      inner ℂ (column W 1 1) (column W 0 1)‖ ≤ 0 := by
    simpa only [hr0,mul_zero,zero_div] using hdiff
  have hcoh := marginal_coherence_gap_bound W hW (marginalLeft PU) 0 0 0
    (by simpa only [mul_zero] using hres) (by change f ≤ 0; rw [hf0]) hd0
  have hb0 : ‖(marginalLeft PU).1 0 1‖ = 0 := by
    change g * ‖(marginalLeft PU).1 0 1‖ ≤
      0+Real.sqrt f*Real.sqrt g+0/2+0/2 at hcoh
    rw [hf0,Real.sqrt_zero,zero_mul] at hcoh
    have hb : ‖(marginalLeft PU).1 0 1‖ ≤ 0 := by nlinarith
    exact le_antisymm hb (norm_nonneg _)
  have hz : traceNorm (block (CStarMatrix.ofMatrix.symm PU.1) 0 1) ≤ 0 := by
    have hh := hblock hg0
    rw [hr0,mul_zero,zero_div] at hh
    have ha := actual_offDiagonal_le PU
    rw [hb0,add_zero] at ha
    exact ha.trans hh
  obtain ⟨sigma,hq,ht⟩ := classical_pointer_repair rhoU TU W hW hT hf1
  refine ⟨sigma,hq,?_⟩
  change traceDistance rhoU sigma ≤ traceDistance rhoU (referenceState TU PU)+
    traceNorm (block (CStarMatrix.ofMatrix.symm PU.1) 0 1)+2*Real.sqrt f at ht
  rw [hru,hf0,Real.sqrt_zero,mul_zero,add_zero,zero_add] at ht
  exact ht.trans hz

/-- Every actual qubit recovery residual admits a Markov repair on the same
physical system with the uniform fifth-root modulus and half trace distance. -/
theorem qubit_residual_fifth_root_repair
    (rho : DensityState (A × (Fin 2 × C)))
    (T : QuantumChannel (Fin 2) (Fin 2 × C)) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
    let r := traceDistance rho (referenceState T P)
    ∃ sigma : DensityState (A × (Fin 2 × C)),
      qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState sigma) = 0 ∧
      traceDistance rho sigma ≤ min 1 (6*Real.rpow r (1/5 : ℝ)) := by
  dsimp only
  let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
  let r := traceDistance rho (referenceState T P)
  have hr0 : 0 ≤ r := traceDistance_nonneg _ _
  by_cases hz : r = 0
  · obtain ⟨sigma,hq,ht⟩ := repair_zero_residual rho T hz
    refine ⟨sigma,hq,le_min (traceDistance_le_one _ _) ?_⟩
    change traceDistance rho sigma ≤ 6*Real.rpow r (1/5 : ℝ)
    rw [hz]
    norm_num [Real.zero_rpow] at ⊢
    exact ht
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hz)
  let delta := Real.rpow r (1/5 : ℝ)
  have hd : 0 < delta := Real.rpow_pos_of_pos hrpos _
  have hpow : r = delta^5 := by
    have h := Real.rpow_inv_natCast_pow hr0 (by decide : (5 : ℕ) ≠ 0)
    change r = (Real.rpow r (1/5 : ℝ))^5
    convert h.symm using 1 <;> norm_num
  by_cases hlarge : 1/6 ≤ delta
  · obtain ⟨F,hF,hFn,hmax,sigma,hq,ht⟩ := product_repair_of_centered_correlation rho T
    refine ⟨sigma,hq,le_min (traceDistance_le_one _ _) ?_⟩
    change traceDistance rho sigma ≤ 6*delta
    exact (traceDistance_le_one _ _).trans (by linarith)
  obtain ⟨sigma,hq,ht⟩ := repair_positive_small_scale rho T delta hd (le_of_lt (lt_of_not_ge hlarge)) hpow
  exact ⟨sigma,hq,le_min (traceDistance_le_one _ _) ht⟩

end WholeRepair

end D5.S3.Quantum.Recovery.QubitResidualRounding
