/- GID: D5/S3/Quantum/Information/PureStateECQCRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/PureStateECQCRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/PureStateECQCRefutation.claim; result=D5/S3/Quantum/Information/PureStateECQCRefutation.result; claim=D5/S3/Quantum/Information/PureStateECQCRefutation.claim
   digest: A maximally entangled five-dimensional pure state refutes ECQC. -/

/-
proof_shape: bases: definition; jointLaw: definition; claim: definition;
  result: bind-only (primitive-character orthogonality, existing entropy identities,
  a constructed finite witness, spectral projection and normalization).
escape_witness: none
admission_basis: open-problem-resolution (#12896; Refuted)
Registration is paused under CLAUDE.md §3.9 (information-escape registration pause).
Direct frozen dependencies:
  D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.pureDensityState
  module statement_id: sha256:d5563afe7bd312f16b4e6f7c9f441317f7de6d07a379a2a024ddcd34ddbbc1f7
  D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity
  D5/S3/Quantum/PureState/PureStateHandshake.pure_state_handshake
  module statement_id: sha256:d0b30bfdc4f51dc80a7b7acc6ecc28c8aca99f8eaa4a9d48683e3e57908a6639
  D5/S3/Quantum/Information/InputInformationBalance.entropy_eq_sum
  module statement_id: sha256:7cd0b5a8cd046746c5faf724b7790ecb11fe9f5b9ad6dd4a404dc684ab703d4b
  D5/S3/Quantum/Information/PartialTraceMutualInformation.quantumMutualInformation
  D5/S3/Quantum/Information/PartialTraceMutualInformation.marginalRight
  D5/S3/Quantum/Information/PartialTraceMutualInformation.marginalLeft
  D5/S3/Quantum/Information/PartialTraceMutualInformation.spectral_sum_eq_of_charpoly_prod
  module statement_id: sha256:a9412bc39f47c48d0206a946c9781d89d5e3a19963de2c334eda8ba43e136130
  D5/S3/Quantum/Divergence/VonNeumannEntropyPinching.vonNeumannEntropy
  module statement_id: sha256:7e20a9a8027e14e93fe22cd7900dc1a94b48a57dcb9f97b27d4815f8e9b61a00
  D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition.DensityState
  module statement_id: sha256:445d28204f4c839e9d5711f568c7f8a3259e36bcff54986168a827333cbdbb5d
  D5/S3/Entropy/MutualInformationEntropy.mutual_information_eq_entropy_sub
  module statement_id: sha256:fd4c9c2007919097105dc62c2d903be56e62d3a65af4aad219bb6b12c2e67f7c
  D5/S3/Entropy/MutualInformation.mutualInformation
  module statement_id: sha256:e4f40b94b8aa512f99b49f609881dc0261233103899f9e11e86c073cd1929ae8
  D5/S3/Entropy/MaxEntropy.shannonEntropy
  module statement_id: sha256:bb7656cc403aa1afcb3a8d1187c3c2e09f60c923721b2fdc47e373755b413610
  D5/S3/Divergence/ChainRule.marginal
  module statement_id: sha256:6f8bf8f41874d30941bd6d1392205943b8151971d5ce71ef7e893ef882058b16
-/

import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
import D5.S3.Quantum.Information.InputInformationBalance
import D5.S3.Entropy.MutualInformationEntropy

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
open D5.S3.Divergence.ChainRule
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Information.PureStateECQCRefutation

def bases (i : Fin 6) (a x : ZMod 5) : ℂ :=
  if i = 1 then (Pi.single a (1 : ℂ) : ZMod 5 → ℂ) x else
    ZMod.stdAddChar (((if i = 0 then 0 else (i.val - 1 : ℕ)) : ZMod 5) * x^2 + a*x) /
      (Real.sqrt 5 : ℂ)

def jointLaw (i : Fin 6) (ψ : ZMod 5 × ZMod 5 → ℂ) (ab : ZMod 5 × ZMod 5) : ℝ :=
  Complex.normSq (∑ xy, star (bases i ab.1 xy.1) * star (bases i ab.2 xy.2) * ψ xy)

def claim : Prop :=
  ∀ (ψ : ZMod 5 × ZMod 5 → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1),
    sInf {r : ℝ | ∃ S : Finset (Fin 6), S.card = 5 ∧
      r = ∑ i ∈ S, mutualInformation (jointLaw i ψ) / Real.log 2} ≤
    quantumMutualInformation (pureDensityState ψ hψ) / Real.log 2

theorem result : ¬ claim := by
  classical
  intro hclaim
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let c : ℂ := (Real.sqrt 5 : ℂ)⁻¹
  have hcs : (starRingEnd ℂ) c = c := by simp [c]
  have hc : c * c = (1/5 : ℂ) := by
    dsimp [c]
    have hs : (Real.sqrt 5 : ℂ) * (Real.sqrt 5 : ℂ) = 5 := by
      exact_mod_cast Real.mul_self_sqrt (show (0:ℝ) ≤ 5 by norm_num)
    rw [← _root_.mul_inv_rev, hs]
    norm_num
  have hc3 : c * c * c * 5 = c := by rw [hc]; ring
  have hcn : Complex.normSq c = 1/5 := by
    simp [c, Complex.normSq]
  let ψ : ZMod 5 × ZMod 5 → ℂ := fun xy => if xy.2 = 2 * xy.1 then c else 0
  have hψ : star ψ ⬝ᵥ ψ = 1 := by
    simp [dotProduct, ψ, Fintype.sum_prod_type, hcs, hc, ZMod.card]
  have hstar (z : ZMod 5) : (starRingEnd ℂ) (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
    simpa only [Complex.star_def, AddChar.inv_apply', AddChar.map_neg_eq_inv] using
      (AddChar.starComp_apply (R := ZMod 5) (φ := ZMod.stdAddChar)
        (by norm_num [ZMod.ringChar_zmod_n]) z)
  have hinj : Function.Injective (fun x : ZMod 5 => 2*x) := by
    intro x y h
    have h2 : (2 : ZMod 5) ≠ 0 := by decide
    exact mul_left_cancel₀ h2 h
  have hcond (a b : ZMod 5) : -(a+2*b) = 0 ↔ b = 2*a := by
    have hf : (4 : ZMod 5) = -1 := by decide
    constructor
    · intro h
      have hh : a+2*b = 0 := neg_eq_zero.mp h
      calc b = -(2*(a+2*b)) + 2*a := by ring_nf; rw [hf]; ring
           _ = 2*a := by rw [hh]; ring
    · intro h
      rw [h]
      ring_nf
      rw [show (5 : ZMod 5) = 0 by decide]
      simp
  have hamp (i : Fin 6) (a b : ZMod 5) :
      (∑ xy, star (bases i a xy.1) * star (bases i b xy.2) * ψ xy) =
        if b = 2*a then c else 0 := by
    rw [Fintype.sum_prod_type]
    simp only [ψ, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hi : i = 1
    · calc _ = ∑ x : ZMod 5, if x=a then (if b=2*a then c else 0) else 0 := by
             apply Finset.sum_congr rfl
             intro x _
             by_cases hx : x=a <;> simp [bases, hi, Pi.single_apply, hx, eq_comm]
           _ = _ := by simp
    · let k : ZMod 5 := ((if i = 0 then 0 else (i.val - 1 : ℕ)) : ZMod 5)
      have hb (a x : ZMod 5) : bases i a x = ZMod.stdAddChar (k*x^2+a*x) * c := by
        simp only [bases, if_neg hi]
        rfl
      simp only [hb, star_mul, Complex.star_def, hstar, hcs]
      have phase (x : ZMod 5) : -(k*x^2+a*x) + -(k*(2*x)^2+b*(2*x)) = x * (-(a+2*b)) := by
        have hf : (5 : ZMod 5) = 0 := by decide
        calc _ = -(5*k*x^2) + x * (-(a+2*b)) := by ring
             _ = _ := by rw [hf]; ring
      calc _ = c*c*c * ∑ x : ZMod 5, ZMod.stdAddChar (x * (-(a+2*b))) := by
             rw [Finset.mul_sum]
             apply Finset.sum_congr rfl
             intro x _
             rw [← phase, AddChar.map_add_eq_mul]
             ring
           _ = _ := by
             rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar 5), ZMod.card]
             simp only [hcond]
             split_ifs <;> simp [hc3]
  have hlaw (i : Fin 6) : jointLaw i ψ = fun ab => if ab.2 = 2*ab.1 then 1/5 else 0 := by
    funext ab
    rw [jointLaw, hamp]
    split_ifs <;> simp [hcn]
  have hmarg (i : Fin 6) : D5.S3.Divergence.ChainRule.marginal (jointLaw i ψ) = fun _ => 1/5 := by
    funext a
    simp [D5.S3.Divergence.ChainRule.marginal, hlaw]
  have hmarg' (i : Fin 6) :
      D5.S3.Divergence.ChainRule.marginal (fun ab : ZMod 5 × ZMod 5 => jointLaw i ψ (ab.2,ab.1)) = fun _ => 1/5 := by
    funext b
    have he (a : ZMod 5) : b = 2*a ↔ a = 3*b := by
      constructor <;> intro h
      · rw [h]; ring_nf; rw [show (6 : ZMod 5) = 1 by decide]; simp
      · rw [h]; ring_nf; rw [show (6 : ZMod 5) = 1 by decide]; simp
    simp [D5.S3.Divergence.ChainRule.marginal, hlaw, he]
  have hlog : Real.negMulLog (5:ℝ)⁻¹ = Real.log 5 / 5 := by
    simp only [Real.negMulLog, Real.log_inv]
    ring
  have hmi (i : Fin 6) : mutualInformation (jointLaw i ψ) = Real.log 5 := by
    rw [mutual_information_eq_entropy_sub (jointLaw i ψ) (fun ab => show 0 ≤ jointLaw i ψ ab from Complex.normSq_nonneg _), hmarg, hmarg']
    simp [shannonEntropy, hlaw, Fintype.sum_prod_type, ZMod.card, apply_ite, hlog]
    ring
  let ρ := pureDensityState ψ hψ
  have hR : CStarMatrix.ofMatrix.symm (marginalRight ρ).1 = diagonal (fun _ : ZMod 5 => (1/5 : ℂ)) := by
    ext a b
    change (∑ y : ZMod 5, ψ (a,y) * star (ψ (b,y))) = _
    by_cases h : a = b
    · subst b
      simp [ψ, hcs, hc]
    · have hn : 2*a ≠ 2*b := fun hh => h (hinj hh)
      simp [ψ, h, hn]
  have hL : CStarMatrix.ofMatrix.symm (marginalLeft ρ).1 = diagonal (fun _ : ZMod 5 => (1/5 : ℂ)) := by
    ext a b
    change (∑ x : ZMod 5, ψ (x,a) * star (ψ (x,b))) = _
    have he (a x : ZMod 5) : a = 2*x ↔ x = 3*a := by
      constructor <;> intro h
      · rw [h]; ring_nf; rw [show (6 : ZMod 5) = 1 by decide]; simp
      · rw [h]; ring_nf; rw [show (6 : ZMod 5) = 1 by decide]; simp
    by_cases h : a = b
    · subst b
      simp [ψ, he, hcs, hc]
    · have hn : 3*a ≠ 3*b := by
        intro hh
        have h3 : (3 : ZMod 5) ≠ 0 := by decide
        exact h (mul_left_cancel₀ h3 hh)
      simp [ψ, he, h, hn]
  have hentropy (σ : DensityState (ZMod 5))
      (hd : CStarMatrix.ofMatrix.symm σ.1 = diagonal (fun _ : ZMod 5 => (1/5 : ℂ))) :
      vonNeumannEntropy σ = Real.log 5 := by
    rw [entropy_eq_sum]
    rw [spectral_sum_eq_of_charpoly_prod _ (fun _ : ZMod 5 => (1/5 : ℝ)) Real.negMulLog (by
      rw [hd, charpoly_diagonal]
      norm_num)]
    simp [ZMod.card, hlog]
    ring
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
  have hqmi : quantumMutualInformation ρ = 2*Real.log 5 := by
    rw [quantumMutualInformation, hentropy _ hR, hentropy _ hL, hpure]
    ring
  have hset : {r : ℝ | ∃ S : Finset (Fin 6), S.card = 5 ∧
      r = ∑ i ∈ S, mutualInformation (jointLaw i ψ) / Real.log 2} =
      {5*(Real.log 5 / Real.log 2)} := by
    ext r
    constructor
    · rintro ⟨S, hS, rfl⟩
      simp [hmi, hS]
    · intro hr
      have hh : r = 5*(Real.log 5 / Real.log 2) := hr
      subst r
      refine ⟨Finset.univ.erase 0, by decide, ?_⟩
      simp [hmi]
  have hh := hclaim ψ hψ
  rw [hset, csInf_singleton] at hh
  change 5*(Real.log 5 / Real.log 2) ≤ quantumMutualInformation ρ / Real.log 2 at hh
  rw [hqmi] at hh
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have ht : 0 < Real.log 5 / Real.log 2 := div_pos h5 h2
  rw [mul_div_assoc] at hh
  linarith

#print axioms result
end D5.S3.Quantum.Information.PureStateECQCRefutation
