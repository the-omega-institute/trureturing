/- GID: D5/S3/Quantum/Recovery/PhaseBoundarySecondOrderExpansion
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PhaseBoundarySecondOrderExpansion
   mirror-E: none(waiver:research-interface)
   anchors: []
   utility: none
   digest: Uniform all-decoder second-order expansion and current Choi-moment rates. -/
import D5.S3.Quantum.Recovery.PhaseBoundaryCurrentMomentDefect
import D5.S3.Quantum.Recovery.PhaseBoundaryUniformFeasibleRecovery

noncomputable section
namespace D5.S3.Quantum.Recovery.PhaseBoundarySecondOrderExpansion
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Recovery.PhaseBoundarySourceModel
open D5.S3.Quantum.Recovery.PhaseBoundaryReferenceReduction
open D5.S3.Quantum.Recovery.PhaseBoundaryFlagInstrument
open D5.S3.Quantum.Recovery.PhaseBoundarySpectralReduction
open D5.S3.Quantum.Recovery.PhaseBoundaryDiagonalReferenceReduction
open D5.S3.Quantum.Recovery.PhaseBoundaryCurrentMomentDefect
open D5.S3.Quantum.Recovery.PhaseBoundaryUniformFeasibleRecovery
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

private theorem diamond_symm {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (G H : QuantumChannel a b) :
    diamondDistance G H = diamondDistance H G := by
  have he (n : ℕ) (rho : DensityState (Fin n × a)) :
      referenceError G H rho = referenceError H G rho := by
    unfold referenceError
    rw [← neg_sub (CStarMatrix.ofMatrix.symm (referenceState H rho).1)
      (CStarMatrix.ofMatrix.symm (referenceState G rho).1), traceNorm_neg]
  simp only [diamondDistance, he]

private theorem realization_eq_decoder (Γ : Instrument) :
    instrumentRealization Γ = Γ.decoder := by
  have hmap : (instrumentRealization Γ).toCompletelyPositiveMap =
      Γ.decoder.toCompletelyPositiveMap := by
    apply DFunLike.ext
    intro X
    have h := (common_flag_instrument_complete.{0,0,0,0,0,0}.1 Γ).choose_spec.2 Unit
      (CStarMatrix.ofMatrix fun p q => X p.2 q.2)
    rw [← decoder_reference] at h
    ext a b
    exact congrArg (fun Y => Y ((),a) ((),b)) h
  cases hG : instrumentRealization Γ
  cases hH : Γ.decoder
  simp only [hG,hH] at hmap
  cases hmap
  rfl

/-- Both averages act only on the receiver's flag and output registers. -/
private theorem reduced_error_le (p : Parameters) (x : CoupledPoint p)
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit)) :
    x.error (FlagInstrument.extract D) ≤ decoderError p x D := by
  have hlabel := output_label_symmetrization (x.h*x.eps) p.beta p.gamma x.weights
    (mul_nonneg x.h_nonneg x.eps_pos.le) x.ell_le p.beta_pos
    x.weights_nonneg x.weights_legal D
  have hflag := (flag_z_symmetrization (x.h*x.eps) p.beta p.gamma x.weights
    (mul_nonneg x.h_nonneg x.eps_pos.le) x.ell_le p.beta_pos
    x.weights_nonneg x.weights_legal (FlagInstrument.extract D).decoder).2
  rw [diamond_symm, diamond_symm _ (targetChannel _ _ _)] at hlabel hflag
  unfold CoupledPoint.error actualError decoderError
  rw [realization_eq_decoder]
  exact div_le_div_of_nonneg_right (hflag.trans hlabel) (by norm_num)

private theorem lawful_domain (p : Parameters) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ eps h : ℝ, 0 < eps → eps < e0 →
      0 ≤ h → h ≤ p.H →
      ∃ x : CoupledPoint p, x.eps = eps ∧ x.h = h ∧ h*eps < 1/2 := by
  have hR : 0 < p.R := lt_trans (by norm_num) p.R_gt_one
  have hb := p.beta_pos
  have hHpos := p.H_pos
  have hden : 0 < p.beta^2+p.gamma^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos p.beta_pos) (sq_nonneg _)
  let e0 := min (1/(2*(p.H+1))) ((p.beta/(p.beta^2+p.gamma^2))/p.R)
  have he0 : 0 < e0 := by
    dsimp [e0]
    exact lt_min (by positivity) (by positivity)
  refine ⟨e0,he0,?_⟩
  intro eps h he hs hh hH
  have hr : h*eps < 1/2 := by
    have he' := hs.trans_le (min_le_left _ _)
    have ht := (lt_div_iff₀ (by positivity : 0 < 2*(p.H+1))).mp he'
    nlinarith [mul_le_mul_of_nonneg_right hH he.le]
  have hi : p.R*eps ≤ p.beta/(p.beta^2+p.gamma^2) := by
    have he' := hs.trans_le (min_le_right _ _)
    have ht := (lt_div_iff₀ hR).mp he'
    nlinarith
  exact ⟨⟨eps,h,he,hh,hH,by linarith,hi⟩,rfl,rfl,hr⟩

/-- The lower bound includes decoders outside the near-optimal class. -/
private theorem all_decoder_lower_bound (p : Parameters) :
    ∃ C e0 : ℝ, 0 < C ∧ 0 < e0 ∧
      ∀ (x : CoupledPoint p), x.eps < e0 →
        (∀ D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit),
          3/4+x.eps*Phi p x.h-C*x.eps^2 ≤ decoderError p x D) ∧
        3/4+x.eps*Phi p x.h-C*x.eps^2 ≤ optimalError p x := by
  obtain ⟨_,_,_,_,hPhi,_⟩ := uniform_optimal_upper_bound p
  let K := p.beta*(p.R+1)/8+1
  have hK : 0 ≤ K := by
    have hb := p.beta_pos
    have hR := p.R_gt_one
    dsimp [K]
    positivity
  obtain ⟨b,hb,e0,he0,hdef⟩ := current_moment_defect_lower_bound p K hK
  refine ⟨6*b^2+b,e0,by positivity,he0,?_⟩
  intro x he
  have hall (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit)) :
      3/4+x.eps*Phi p x.h-(6*b^2+b)*x.eps^2 ≤ decoderError p x D := by
    have hred := reduced_error_le p x D
    by_cases hnear : x.error (FlagInstrument.extract D) ≤ 3/4+K*x.eps
    · exact ((hdef x (FlagInstrument.extract D) he hnear).2).trans hred
    · have hhigh := lt_of_not_ge hnear
      have hphi := mul_le_mul_of_nonneg_left (hPhi x.h) x.eps_pos.le
      have hcost : 0 ≤ (6*b^2+b)*x.eps^2 := by positivity
      dsimp [K] at hhigh
      nlinarith [x.eps_pos]
  refine ⟨hall,?_⟩
  apply le_csInf
  · exact ⟨_,Set.mem_range_self
      (instrumentRealization (feasibleInstrument ⟨0,0,by norm_num,by norm_num⟩))⟩
  · rintro _ ⟨D,rfl⟩
    exact hall D

private theorem coupled_expansion (p : Parameters) :
    ∃ C e0 : ℝ, 0 < C ∧ 0 < e0 ∧
      ∀ x : CoupledPoint p, x.eps < e0 →
        |optimalError p x-3/4-x.eps*Phi p x.h| ≤ C*x.eps^2 := by
  obtain ⟨Cu,eu,hCu,heu,_,hupper⟩ := uniform_optimal_upper_bound p
  obtain ⟨Cl,el,hCl,hel,hlower⟩ := all_decoder_lower_bound p
  refine ⟨Cu+Cl,min eu el,by positivity,lt_min heu hel,?_⟩
  intro x he
  have hu := hupper x (he.trans_le (min_le_left _ _))
  have hl := (hlower x (he.trans_le (min_le_right _ _))).2
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg x.eps]

/-- Uniform second-order expansion of the infimum over all receiver CPTP maps.
The lawful source is constructed for every raw pair in the stated rectangle;
its rare weight is strictly below one half, including the boundary h = 0. -/
theorem uniform_second_order_expansion (p : Parameters) :
    ∃ C eps0 : ℝ, 0 < C ∧ 0 < eps0 ∧
      ∀ eps h : ℝ, 0 < eps → eps < eps0 → 0 ≤ h → h ≤ p.H →
        ∃ x : CoupledPoint p, x.eps = eps ∧ x.h = h ∧ h*eps < 1/2 ∧
          p.R*eps ≤ p.beta/(p.beta^2+p.gamma^2) ∧
          |optimalError p x-3/4-eps*Phi p h| ≤ C*eps^2 := by
  obtain ⟨C,ec,hC,hec,herr⟩ := coupled_expansion p
  obtain ⟨el,hel,hlaw⟩ := lawful_domain p
  refine ⟨C,min ec el,hC,lt_min hec hel,?_⟩
  intro eps h he he0 hh hH
  obtain ⟨x,hxe,hxh,hr⟩ := hlaw eps h he (he0.trans_le (min_le_right _ _)) hh hH
  refine ⟨x,hxe,hxh,hr,by simpa only [hxe] using x.input_le,?_⟩
  have hxsmall : x.eps < ec := by rw [hxe]; exact he0.trans_le (min_le_left _ _)
  simpa [hxe,hxh] using herr x hxsmall

set_option maxHeartbeats 2000000 in
-- The simultaneous square estimates retain all parameter-dependent coefficients.
private theorem near_optimal_rates (p : Parameters) (K0 : ℝ) (hK0 : 0 ≤ K0) :
    ∃ C e0 : ℝ, 0 < C ∧ 0 < e0 ∧
      ∀ (x : CoupledPoint p) (Γ : Instrument), x.eps < e0 →
        x.error Γ ≤ optimalError p x+K0*x.eps^2 →
        x.c Γ ≤ C*x.eps^2 ∧ |x.d Γ| ≤ C*x.eps ∧
          ∀ j : Qubit, |A (symInstrument Γ) j-1/2| ≤ C*x.eps := by
  obtain ⟨Cu,eu,hCu,heu,hPhi,hupper⟩ := uniform_optimal_upper_bound p
  let K := p.beta*(p.R+1)/8+Cu+K0+1
  have hK : 0 ≤ K := by
    have hb := p.beta_pos
    have hR := p.R_gt_one
    dsimp [K]
    positivity
  obtain ⟨b,hb,ed,hed,hdef⟩ := current_moment_defect_lower_bound p K hK
  let V := 12*b^2+b+Cu+K0
  have hV : 0 < V := by dsimp [V]; positivity
  let L := 32*V+1
  have hL : 0 < L := by dsimp [L]; positivity
  have hLb : 0 ≤ Lbar p := by
    have hb := p.beta_pos
    have hR := p.R_gt_one
    dsimp [Lbar]
    positivity
  let C := 16*V+L+Lbar p+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,min eu (min ed 1),hC,lt_min heu (lt_min hed (by norm_num)),?_⟩
  intro x Γ he hnear
  have he0 := x.eps_pos.le
  have he1 : x.eps ≤ 1 := (he.trans_le (le_trans (min_le_right _ _) (min_le_right _ _))).le
  have hesq : x.eps^2 ≤ x.eps := by nlinarith
  have hu := hupper x (he.trans_le (min_le_left _ _))
  have hne : x.error Γ ≤ 3/4+K*x.eps := by
    have hp := mul_le_mul_of_nonneg_left (hPhi x.h) he0
    have hs := mul_le_mul_of_nonneg_left hesq (show 0 ≤ Cu+K0 by positivity)
    dsimp [K]
    nlinarith
  have hw := (hdef x Γ
    (he.trans_le (le_trans (min_le_right _ _) (min_le_left _ _))) hne).1
  have hc0 : 0 ≤ x.c Γ := add_nonneg
    (diagonal_bounds (symInstrument Γ) 0 (0,1)).1
    (diagonal_bounds (symInstrument Γ) 1 (0,1)).1
  have hsqrt := Real.sq_sqrt hc0
  have habs : |x.d Γ|^2 = (x.d Γ)^2 := sq_abs _
  have hyu := sq_nonneg (Real.sqrt (x.c Γ)-8*b*x.eps)
  have hyv := sq_nonneg (|x.d Γ|-16*b*x.eps)
  have henergy : x.c Γ/16+(x.d Γ)^2/32 ≤ V*x.eps^2 := by
    dsimp [V]
    nlinarith
  have hc : x.c Γ ≤ 16*V*x.eps^2 := by nlinarith [sq_nonneg (x.d Γ)]
  have hd2 : (x.d Γ)^2 ≤ 32*V*x.eps^2 := by nlinarith
  have hLsq : 32*V ≤ L^2 := by dsimp [L]; nlinarith [sq_nonneg (32*V)]
  have hd : |x.d Γ| ≤ L*x.eps := by
    apply abs_le_of_sq_le_sq _ (mul_nonneg hL.le he0)
    have ht := mul_le_mul_of_nonneg_right hLsq (sq_nonneg x.eps)
    nlinarith
  have hC1 : 16*V ≤ C := by dsimp [C]; linarith
  have hC2 : L ≤ C := by dsimp [C]; linarith
  refine ⟨hc.trans (mul_le_mul_of_nonneg_right hC1 (sq_nonneg x.eps)),
    hd.trans (mul_le_mul_of_nonneg_right hC2 he0),?_⟩
  intro j
  have ha := current_A_bound p x Γ j
  have hce : x.c Γ ≤ 16*V*x.eps := hc.trans
    (mul_le_mul_of_nonneg_left hesq (by positivity))
  have hcoef : (16*V+L+Lbar p)/2 ≤ C := by dsimp [C]; linarith
  have ht := mul_le_mul_of_nonneg_right hcoef he0
  nlinarith

/-- Every second-order near-optimal receiver admits the specified lawful
output-label and flag average, with uniform rates for its current Choi moments.
The moments are defined by the channel action; no Kraus representation or rank
bound enters either the hypothesis or the conclusion. -/
theorem near_optimal_decoder_moments (p : Parameters) (K0 : ℝ) (hK0 : 0 ≤ K0) :
    ∃ CK epsK : ℝ, 0 < CK ∧ 0 < epsK ∧
      ∀ eps h : ℝ, 0 < eps → eps < epsK → 0 ≤ h → h ≤ p.H →
        ∃ x : CoupledPoint p, x.eps = eps ∧ x.h = h ∧ h*eps < 1/2 ∧
          p.R*eps ≤ p.beta/(p.beta^2+p.gamma^2) ∧
          ∀ D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit),
            decoderError p x D ≤ optimalError p x+K0*eps^2 →
            ∃ Gamma : QuantumChannel (Qubit × Qubit) (Qubit × Qubit),
              Gamma = flagSymmetrizedDecoder (FlagInstrument.extract D).decoder ∧
              decoderError p x Gamma ≤ decoderError p x D ∧
              C (FlagInstrument.extract Gamma) 0+C (FlagInstrument.extract Gamma) 1 ≤ CK*eps^2 ∧
              |F (FlagInstrument.extract Gamma) p.beta p.gamma eps 0-
                F (FlagInstrument.extract Gamma) p.beta p.gamma (p.R*eps) 1| ≤ CK*eps ∧
              ∀ j : Qubit, |A (FlagInstrument.extract Gamma) j-1/2| ≤ CK*eps := by
  obtain ⟨CK,er,hCK,her,hrates⟩ := near_optimal_rates p K0 hK0
  obtain ⟨el,hel,hlaw⟩ := lawful_domain p
  refine ⟨CK,min er el,hCK,lt_min her hel,?_⟩
  intro eps h he he0 hh hH
  obtain ⟨x,hxe,hxh,hr⟩ := hlaw eps h he (he0.trans_le (min_le_right _ _)) hh hH
  refine ⟨x,hxe,hxh,hr,by simpa only [hxe] using x.input_le,?_⟩
  intro D hD
  let Γ := FlagInstrument.extract D
  let Gamma := flagSymmetrizedDecoder (instrumentRealization Γ)
  have hred := reduced_error_le p x D
  have hnear : x.error Γ ≤ optimalError p x+K0*x.eps^2 := by
    rw [hxe]
    exact hred.trans hD
  have hes : x.eps < er := by rw [hxe]; exact he0.trans_le (min_le_left _ _)
  obtain ⟨hc,hd,ha⟩ := hrates x Γ hes hnear
  refine ⟨Gamma,?_,hred,?_,?_,?_⟩
  · exact congrArg flagSymmetrizedDecoder (realization_eq_decoder Γ)
  · simpa only [CoupledPoint.c,hxe,Gamma,symInstrument] using hc
  · simpa only [CoupledPoint.d,CoupledPoint.f,CoupledPoint.weights,rate,
      show (0 : Qubit) = 0 from rfl, if_true,
      show (1 : Qubit) ≠ 0 from by decide, if_false, one_mul,hxe,Gamma,symInstrument] using hd
  · intro j
    simpa only [hxe,Gamma,symInstrument] using ha j

end D5.S3.Quantum.Recovery.PhaseBoundarySecondOrderExpansion
