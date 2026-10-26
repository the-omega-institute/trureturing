/- GID: D5/S3/QuantumBounds/EnergyConstrainedDeterministicViolation
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/EnergyConstrainedDeterministicViolation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Deterministic entangled devices strictly violate the separable energy bound. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)

namespace D5.S3.QuantumBounds.EnergyConstrainedDeterministicViolation

/-- Born probabilities for a local channel and a joint binary measurement. -/
def probability {dp ds dm : ℕ}
    (sigma : Matrix (Fin dp × Fin dm) (Fin dp × Fin dm) ℂ)
    (lam : Fin 2 → MatrixMap (Fin dp) (Fin ds) ℂ)
    (povm : Fin 2 → Matrix (Fin ds × Fin dm) (Fin ds × Fin dm) ℂ)
    (b x : Fin 2) : ℝ :=
  (Matrix.trace (povm b * MatrixMap.kron (lam x) LinearMap.id sigma)).re

/-- Every positive energy budget below one half admits a deterministic-input violation. -/
def claim : Prop :=
  ∀ ω : ℝ, 0 < ω → ω < 1 / 2 →
    ∃ (dp ds dm : ℕ) (sigma : Matrix (Fin dp × Fin dm) (Fin dp × Fin dm) ℂ)
      (lam : Fin 2 → MatrixMap (Fin dp) (Fin ds) ℂ)
      (ham : Matrix (Fin ds) (Fin ds) ℂ) (g : Fin ds → ℂ)
      (povm : Fin 2 → Matrix (Fin ds × Fin dm) (Fin ds × Fin dm) ℂ),
      sigma.PosSemidef ∧ sigma.trace = 1 ∧
      (∀ x, (lam x).IsCompletelyPositive ∧ ∀ rho, (lam x rho).trace = rho.trace) ∧
      ham.IsHermitian ∧ star g ⬝ᵥ g = 1 ∧ ham *ᵥ g = 0 ∧
      (ham - (1 - Matrix.vecMulVec g (star g))).PosSemidef ∧
      (∀ b, (povm b).PosSemidef) ∧ povm 0 + povm 1 = 1 ∧
      (∀ x, (Matrix.trace (ham * lam x (partialTraceRight sigma))).re ≤ ω) ∧
      probability sigma lam povm 0 0 = 1 ∧
      probability sigma lam povm 0 1 - probability sigma lam povm 1 1 <
        2 * (1 - 2 * ω) ^ 2 - 1

private def psi (s r q : ℝ) (i : Fin 2 × Fin 2) : ℂ :=
  if i.1 = 0 then if i.2 = 0 then s else 0 else if i.2 = 0 then r else q

private def sigma (s r q : ℝ) := Matrix.vecMulVec (psi s r q) (star (psi s r q))

private def kraus (s r q a h : ℝ) (x k : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if x = 0 then if k = 0 then 1 else 0 else
    if k = 0 then !![-(a : ℂ) / s, 0; (h : ℂ)^2 / (s*q), (r : ℂ) / q]
    else !![-(h : ℂ)*r / (s*q), (h : ℂ) / q; 0, 0]

private def channel (s r q a h : ℝ) (x : Fin 2) :=
  MatrixMap.of_kraus (kraus s r q a h x) (kraus s r q a h x)

private def measurement (s r q : ℝ) (b : Fin 2) :=
  if b = 0 then sigma s r q else 1 - sigma s r q

private def hamiltonian : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

private def ground : Fin 2 → ℂ := ![1, 0]

private lemma parameters (ω : ℝ) (hω : 0 < ω) (hω' : ω < 1/2) :
    ∃ s r q a h : ℝ, 0 < s ∧ 0 < r ∧ 0 < q ∧ 0 < a ∧ 0 < h ∧
      s^2 = 1-ω ∧ r^2 + q^2 = ω ∧ q^2-r^2 = h^2 ∧
      a^2 + h^2 = s^2 ∧ (s*a-2*r*q)^2 < (1-2*ω)^2 := by
  sorry

private lemma state_measurement (s r q : ℝ) (hs : s^2+r^2+q^2=1) :
    (sigma s r q).PosSemidef ∧ (sigma s r q).trace = 1 ∧
      (∀ b, (measurement s r q b).PosSemidef) ∧
      measurement s r q 0 + measurement s r q 1 = 1 := by
  sorry

private lemma kraus_complete (s r q a h : ℝ) (hs : s ≠ 0) (hq : q ≠ 0)
    (hqr : q^2-r^2=h^2) (ha : a^2+h^2=s^2) (x : Fin 2) :
    (∑ k, (kraus s r q a h x k).conjTranspose * kraus s r q a h x k) = 1 := by
  sorry

private lemma channels (s r q a h : ℝ) (hs : s ≠ 0) (hq : q ≠ 0)
    (hqr : q^2-r^2=h^2) (ha : a^2+h^2=s^2) (x : Fin 2) :
    (channel s r q a h x).IsCompletelyPositive ∧
      ∀ rho, (channel s r q a h x rho).trace = rho.trace := by
  sorry

private lemma ground_energy : hamiltonian.IsHermitian ∧ star ground ⬝ᵥ ground = 1 ∧
    hamiltonian *ᵥ ground = 0 ∧
    (hamiltonian - (1 - Matrix.vecMulVec ground (star ground))).PosSemidef := by
  sorry

private lemma energies (s r q a h : ℝ) (hs : s ≠ 0) (hq : q ≠ 0)
    (hqr : q^2-r^2=h^2) (x : Fin 2) :
    (Matrix.trace (hamiltonian * channel s r q a h x
      (partialTraceRight (sigma s r q)))).re = r^2+q^2 := by
  sorry

private lemma probabilities (s r q a h : ℝ) (hs : s ≠ 0) (hq : q ≠ 0)
    (hn : s^2+r^2+q^2=1) (hqr : q^2-r^2=h^2) (ha : a^2+h^2=s^2) :
    probability (sigma s r q) (channel s r q a h) (measurement s r q) 0 0 = 1 ∧
    probability (sigma s r q) (channel s r q a h) (measurement s r q) 0 1 =
      (s*a-2*r*q)^2 ∧
    probability (sigma s r q) (channel s r q a h) (measurement s r q) 1 1 =
      1-(s*a-2*r*q)^2 := by
  sorry

/-- Qubit channels attain the strict violation for every energy budget in the open interval. -/
theorem result : claim := by
  intro ω hω hω'
  obtain ⟨s, r, q, a, h, hs, hr, hq, ha, hh, hs2, hrq, hqr, has, hv⟩ :=
    parameters ω hω hω'
  have hn : s^2+r^2+q^2=1 := by linarith
  obtain ⟨hd, ht, hp, hm⟩ := state_measurement s r q hn
  obtain ⟨he, hg, hzero, hgap⟩ := ground_energy
  obtain ⟨hp0, hp1, hp2⟩ := probabilities s r q a h hs.ne' hq.ne' hn hqr has
  refine ⟨2, 2, 2, sigma s r q, channel s r q a h, hamiltonian, ground,
    measurement s r q, hd, ht, channels s r q a h hs.ne' hq.ne' hqr has,
    he, hg, hzero, hgap, hp, hm, ?_, hp0, ?_⟩
  · intro x
    rw [energies s r q a h hs.ne' hq.ne' hqr x, hrq]
  · rw [hp1, hp2]
    linarith

end D5.S3.QuantumBounds.EnergyConstrainedDeterministicViolation
