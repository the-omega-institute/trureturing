/- GID: D5/S3/Quantum/Information/PureStateECQCFamily
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/PureStateECQCFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.LegendreSymbol.Basic]
   utility: none
   digest: Pure-state ECQC fails in every prime dimension congruent to one modulo four. -/

import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Information.InputInformationBalance
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
import D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
import D5.S3.Entropy.MutualInformationEntropy
import D5.S3.Entropy.MutualInformation
import D5.S3.Entropy.MaxEntropy
import D5.S3.Divergence.ChainRule
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-
proof_shape: bases: definition; jointLaw: definition; claim: definition; result: content.
escape_witness: The uniform-in-p same-basis amplitude calculation cancels the
  quadratic phase using u^2 = -1 and produces a bijection-graph law for every basis.
admission_basis: escape-witness
computational_content: none; the result quantifies over unbounded prime dimensions
  and evaluates the literal Born law by character orthogonality, not enumeration.
-/

open Matrix Polynomial
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.InputInformationBalance
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationEntropy
open D5.S3.Entropy.MaxEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Information.PureStateECQCFamily

def bases (p : ℕ) [NeZero p] (i : Option (ZMod p)) (b x : ZMod p) : ℂ :=
  match i with
  | none => (Pi.single b (1 : ℂ) : ZMod p → ℂ) x
  | some a => ZMod.stdAddChar (a*x^2+b*x) / (Real.sqrt p : ℂ)

def jointLaw (p : ℕ) [NeZero p] (i : Option (ZMod p))
    (ψ : ZMod p × ZMod p → ℂ) (bc : ZMod p × ZMod p) : ℝ :=
  Complex.normSq (∑ xy, star (bases p i bc.1 xy.1) * star (bases p i bc.2 xy.2) * ψ xy)

def claim (p : ℕ) [NeZero p] : Prop :=
  ∀ (ψ : ZMod p × ZMod p → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1),
    sInf {r : ℝ | ∃ S : Finset (Option (ZMod p)), S.card = p ∧
      r = ∑ i ∈ S, mutualInformation (jointLaw p i ψ)} ≤
    quantumMutualInformation (pureDensityState ψ hψ)

theorem result (p : ℕ) [Fact (Nat.Prime p)] (hp : p % 4 = 1) :
    (∃ u : ZMod p, u^2 = -1) ∧
    ∀ u : ZMod p, u^2 = -1 →
      let ψ : ZMod p × ZMod p → ℂ :=
        fun xy => if xy.2 = u*xy.1 then (Real.sqrt p : ℂ)⁻¹ else 0
      ∃ hψ : star ψ ⬝ᵥ ψ = 1,
        (∀ i bc, jointLaw p i ψ bc = if bc.2 = u*bc.1 then (p : ℝ)⁻¹ else 0) ∧
        (∀ i, D5.S3.Divergence.ChainRule.marginal (jointLaw p i ψ) = fun _ => (p : ℝ)⁻¹) ∧
        (∀ i, D5.S3.Divergence.ChainRule.marginal
          (fun bc : ZMod p × ZMod p => jointLaw p i ψ (bc.2,bc.1)) = fun _ => (p : ℝ)⁻¹) ∧
        (∀ i, mutualInformation (jointLaw p i ψ) = Real.log p) ∧
        quantumMutualInformation (pureDensityState ψ hψ) = 2*Real.log p ∧
        sInf {r : ℝ | ∃ S : Finset (Option (ZMod p)), S.card = p ∧
          r = ∑ i ∈ S, mutualInformation (jointLaw p i ψ)} -
          quantumMutualInformation (pureDensityState ψ hψ) = ((p : ℝ)-2)*Real.log p ∧
        0 < ((p : ℝ)-2)*Real.log p ∧ ¬ claim p := by
  classical
  have hp2 := (Fact.out : Nat.Prime p).two_le
  have hp5 : 5 ≤ p := by omega
  have hppos : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpR : (p : ℝ) ≠ 0 := ne_of_gt hppos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  constructor
  · obtain ⟨u, hu⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 (by omega)
    exact ⟨u, by simpa only [pow_two] using hu.symm⟩
  intro u hu
  dsimp only
  let c : ℂ := (Real.sqrt p : ℂ)⁻¹
  have hcs : (starRingEnd ℂ) c = c := by simp [c]
  have hc : c*c = (p : ℂ)⁻¹ := by
    dsimp [c]
    have hs : (Real.sqrt p : ℂ)*(Real.sqrt p : ℂ) = p := by
      exact_mod_cast Real.mul_self_sqrt hppos.le
    rw [← _root_.mul_inv_rev, hs]
  have hc3 : c*c*c*(p : ℂ) = c := by
    rw [hc]
    calc (p : ℂ)⁻¹*c*(p : ℂ) = c*((p : ℂ)⁻¹*(p : ℂ)) := by ring
         _ = c := by rw [inv_mul_cancel₀ hpC, mul_one]
  have hcn : Complex.normSq c = (p : ℝ)⁻¹ := by
    simp only [c, Complex.normSq_inv, Complex.normSq_ofReal, Real.mul_self_sqrt hppos.le]
  let ψ : ZMod p × ZMod p → ℂ := fun xy => if xy.2 = u*xy.1 then c else 0
  have hψ : star ψ ⬝ᵥ ψ = 1 := by
    simp [dotProduct, ψ, Fintype.sum_prod_type, hcs, hc, ZMod.card, hpC]
  have hstar (z : ZMod p) : (starRingEnd ℂ) (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
    simpa only [Complex.star_def, AddChar.inv_apply', AddChar.map_neg_eq_inv] using
      (AddChar.starComp_apply (R := ZMod p) (φ := ZMod.stdAddChar)
        (by simpa only [ZMod.ringChar_zmod_n] using (by omega : 0 < p)) z)
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hu
    exact one_ne_zero (neg_eq_zero.mp hu.symm)
  have hum : u*u = -1 := by simpa only [pow_two] using hu
  have hinj : Function.Injective (fun x : ZMod p => u*x) := by
    intro x y h
    exact mul_left_cancel₀ hu0 h
  have he (a x : ZMod p) : a = u*x ↔ x = -u*a := by
    constructor
    · intro h
      rw [h]
      calc x = -(u*u)*x := by rw [hum]; ring
           _ = -u*(u*x) := by ring
    · intro h
      rw [h]
      calc a = -(u*u)*a := by rw [hum]; ring
           _ = u*(-u*a) := by ring
  have hcond (b d : ZMod p) : -(b+u*d) = 0 ↔ d = u*b := by
    constructor
    · intro h
      have hh : b+u*d = 0 := neg_eq_zero.mp h
      calc d = -(u*(b+u*d))+u*b := by
                 calc _ = -(u*u)*d := by rw [hum]; ring
                      _ = _ := by ring
           _ = u*b := by rw [hh]; ring
    · intro h
      rw [h]
      calc -(b+u*(u*b)) = -(b+(u*u)*b) := by ring
           _ = 0 := by rw [hum]; ring
  have hamp (i : Option (ZMod p)) (b d : ZMod p) :
      (∑ xy, star (bases p i b xy.1) * star (bases p i d xy.2) * ψ xy) =
        if d = u*b then c else 0 := by
    rw [Fintype.sum_prod_type]
    simp only [ψ, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    cases i with
    | none =>
      calc _ = ∑ x : ZMod p, if x=b then (if d=u*b then c else 0) else 0 := by
               apply Finset.sum_congr rfl
               intro x _
               by_cases hx : x=b <;> simp [bases, Pi.single_apply, hx, eq_comm]
           _ = _ := by simp
    | some a =>
      have hb (b x : ZMod p) : bases p (some a) b x = ZMod.stdAddChar (a*x^2+b*x)*c := rfl
      simp only [hb, star_mul, Complex.star_def, hstar, hcs]
      have phase (x : ZMod p) :
          -(a*x^2+b*x)+-(a*(u*x)^2+d*(u*x)) = x*(-(b+u*d)) := by
        calc _ = -(a*(1+u^2)*x^2)+x*(-(b+u*d)) := by ring
             _ = _ := by rw [hu]; ring
      calc _ = c*c*c * ∑ x : ZMod p, ZMod.stdAddChar (x*(-(b+u*d))) := by
               rw [Finset.mul_sum]
               apply Finset.sum_congr rfl
               intro x _
               rw [← phase, AddChar.map_add_eq_mul]
               ring
           _ = _ := by
               rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p), ZMod.card]
               simp only [hcond]
               split_ifs <;> simp [hc3]
  have hlaw (i : Option (ZMod p)) :
      jointLaw p i ψ = fun bc => if bc.2 = u*bc.1 then (p : ℝ)⁻¹ else 0 := by
    funext bc
    rw [jointLaw, hamp]
    split_ifs <;> simp [hcn]
  have hmarg (i : Option (ZMod p)) :
      D5.S3.Divergence.ChainRule.marginal (jointLaw p i ψ) = fun _ => (p : ℝ)⁻¹ := by
    funext b
    simp [D5.S3.Divergence.ChainRule.marginal, hlaw]
  have hmarg' (i : Option (ZMod p)) :
      D5.S3.Divergence.ChainRule.marginal
        (fun bc : ZMod p × ZMod p => jointLaw p i ψ (bc.2,bc.1)) = fun _ => (p : ℝ)⁻¹ := by
    funext d
    simp [D5.S3.Divergence.ChainRule.marginal, hlaw, he]
  have hlog : Real.negMulLog (p : ℝ)⁻¹ = Real.log p / p := by
    simp only [Real.negMulLog, Real.log_inv]
    ring
  have hcancel : (p : ℝ)*(Real.log p / p) = Real.log p := mul_div_cancel₀ _ hpR
  have hmi (i : Option (ZMod p)) : mutualInformation (jointLaw p i ψ) = Real.log p := by
    rw [mutual_information_eq_entropy_sub (jointLaw p i ψ)
      (fun bc => show 0 ≤ jointLaw p i ψ bc from Complex.normSq_nonneg _), hmarg, hmarg']
    simp [shannonEntropy, hlaw, Fintype.sum_prod_type, ZMod.card, apply_ite, hlog, hcancel]
  let ρ := pureDensityState ψ hψ
  have hR : CStarMatrix.ofMatrix.symm (marginalRight ρ).1 =
      diagonal (fun _ : ZMod p => (p : ℂ)⁻¹) := by
    ext b d
    change (∑ y : ZMod p, ψ (b,y) * star (ψ (d,y))) = _
    by_cases h : b = d
    · subst d
      simp [ψ, hcs, hc]
    · have hn : u*b ≠ u*d := fun hh => h (hinj hh)
      simp [ψ, h, hn]
  have hL : CStarMatrix.ofMatrix.symm (marginalLeft ρ).1 =
      diagonal (fun _ : ZMod p => (p : ℂ)⁻¹) := by
    ext b d
    change (∑ x : ZMod p, ψ (x,b) * star (ψ (x,d))) = _
    have hv (a x : ZMod p) : ψ (x,a) = if x = -u*a then c else 0 := by
      dsimp only [ψ]
      simp only [he a x]
    simp only [hv]
    by_cases h : b = d
    · subst d
      simp [hcs, hc]
    · simp [h, hu0]
  have hentropy (σ : DensityState (ZMod p))
      (hd : CStarMatrix.ofMatrix.symm σ.1 = diagonal (fun _ : ZMod p => (p : ℂ)⁻¹)) :
      vonNeumannEntropy σ = Real.log p := by
    rw [entropy_eq_sum]
    rw [spectral_sum_eq_of_charpoly_prod _ (fun _ : ZMod p => (p : ℝ)⁻¹) Real.negMulLog (by
      rw [hd, charpoly_diagonal]
      simp)]
    simp [ZMod.card, hlog, hcancel]
  have hpure : vonNeumannEntropy ρ = 0 := by
    have hid : IsIdempotentElem (rankOneDensity ψ) :=
      (pure_state_handshake ψ hψ (1 : Matrix _ _ ℂ)).1
    have hM := (Matrix.posSemidef_vecMulVec_self_star ψ).isHermitian
    rw [entropy_eq_sum]
    change ∑ i, Real.negMulLog (hM.eigenvalues i) = 0
    apply Finset.sum_eq_zero
    intro i _
    have hh := hid.spectrum_subset ℝ (hM.eigenvalues_mem_spectrum_real i)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with h | h <;> rw [h] <;> simp
  have hqmi : quantumMutualInformation ρ = 2*Real.log p := by
    rw [quantumMutualInformation, hentropy _ hR, hentropy _ hL, hpure]
    ring
  have hset : {r : ℝ | ∃ S : Finset (Option (ZMod p)), S.card = p ∧
      r = ∑ i ∈ S, mutualInformation (jointLaw p i ψ)} = {(p : ℝ)*Real.log p} := by
    ext r
    constructor
    · rintro ⟨S, hS, rfl⟩
      simp [hmi, hS]
    · intro hr
      have hh : r = (p : ℝ)*Real.log p := hr
      subst r
      refine ⟨Finset.univ.erase none, ?_, ?_⟩ <;> simp [hmi, ZMod.card]
  have hmin : sInf {r : ℝ | ∃ S : Finset (Option (ZMod p)), S.card = p ∧
      r = ∑ i ∈ S, mutualInformation (jointLaw p i ψ)} = (p : ℝ)*Real.log p := by
    rw [hset, csInf_singleton]
  have hpositive : 0 < ((p : ℝ)-2)*Real.log p := by
    have hpR5 : 5 ≤ (p : ℝ) := by exact_mod_cast hp5
    exact mul_pos (by linarith) (Real.log_pos (by linarith))
  have hnot : ¬ claim p := by
    intro hclaim
    have hh := hclaim ψ hψ
    rw [hmin] at hh
    change (p : ℝ)*Real.log p ≤ quantumMutualInformation ρ at hh
    rw [hqmi] at hh
    nlinarith
  refine ⟨hψ, ?_, hmarg, hmarg', hmi, hqmi, ?_, hpositive, hnot⟩
  · intro i bc
    exact congrFun (hlaw i) bc
  · rw [hmin]
    change (p : ℝ)*Real.log p - quantumMutualInformation ρ = _
    rw [hqmi]
    ring

#print axioms result
end D5.S3.Quantum.Information.PureStateECQCFamily
