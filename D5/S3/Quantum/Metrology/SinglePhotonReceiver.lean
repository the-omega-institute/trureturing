/- GID: D5/S3/Quantum/Metrology/SinglePhotonReceiver
   generality: I
   mirror-B: D5/B/S3/Quantum/Metrology/SinglePhotonReceiver
   mirror-E: none(waiver:analytic-single-photon-model)
   anchors: []
   utility: none
   digest: Derive the local probability and tangent of a literal two-mode single-photon Born readout and construct every extremal tangent. -/

import D5.S3.Quantum.FiniteDimensional

/-!
# A physical single-photon probability/tangent domain

The basis is |10>, |01>, so every normalized state has exactly one photon.
The receiver is an arbitrary rank-one projective two-port measurement. The
existing QubitMatrix and bornProbability own the matrix carrier and trace law.
Bloch coordinates here parametrize the actual matrices, rather than postulating
the desired Fisher-information constraint. Normalized complex amplitudes map
to these matrices explicitly. The phase is diag(1, exp(i*phi)).

The consumer is AsymmetricDetectorOptimum. It needs the derived inequality
(d p/d phi)^2 <= p(1-p) and an attaining probe/receiver for every interior p.
No loss channel before encoding, ancillary photons, dark counts, arbitrary
POVM implementation, or unknown-phase global optimization is claimed.

Library-first: dev b89d56d0c9a433f9b714821d2bb1779066c59ede provides
FiniteDimensional.bornProbability. Searches for Fisher, fisherInformation,
Bloch and Pauli found no corresponding single-photon receiver jet owner.
The existing amplitude-damping profiles and reference-channel fidelity are
other observables, not substitutes for an actual acquired Born probability.

References: Qin and Liu, PRResearch 8,023125 (2026), arXiv:2604.07828v1,
section VI; Len et al., Nat.Commun.13,6971 (2022), DOI
10.1038/s41467-022-33563-8. The physical representation is classical; no
priority is asserted. This is a specified one-photon receiver class, not the
whole finite-dimensional detector-inefficiency problem in Qin and Liu.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Metrology.SinglePhotonReceiver

open D5.S3.Quantum.FiniteDimensional
open scoped ComplexConjugate ComplexOrder Matrix

/-- Three real coordinates, with the sphere condition stated at each use. -/
abbrev Direction := Fin 3 → ℝ

/-- Squared Euclidean length of the three physical Bloch coordinates. -/
def radiusSq (r : Direction) : ℝ := r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2

/-- The actual two-by-two trace-one Bloch matrix. -/
def blochMatrix (r : Direction) : QubitMatrix :=
  !![((1 + r 2) / 2 : ℝ), (r 0 / 2 : ℝ) - (r 1 / 2 : ℝ) * Complex.I;
     (r 0 / 2 : ℝ) + (r 1 / 2 : ℝ) * Complex.I, ((1 - r 2) / 2 : ℝ)]

private theorem bloch_hermitian (r : Direction) : (blochMatrix r)ᴴ = blochMatrix r := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blochMatrix]

/-- Sphere points are genuine positive trace-one projectors. -/
theorem bloch_projector_valid (r : Direction) (hr : radiusSq r = 1) :
    (blochMatrix r).PosSemidef ∧ Matrix.trace (blochMatrix r) = 1 ∧
      blochMatrix r * blochMatrix r = blochMatrix r := by
  change r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1 at hr
  have hsq : blochMatrix r * blochMatrix r = blochMatrix r := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [blochMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        Complex.mul_re, Complex.mul_im] <;>
      nlinarith [hr]
  have hp := Matrix.posSemidef_conjTranspose_mul_self (blochMatrix r)
  rw [bloch_hermitian, hsq] at hp
  refine ⟨hp, ?_, hsq⟩
  norm_num [Matrix.trace, blochMatrix, Fin.sum_univ_two] <;> push_cast <;> ring

/-- Coordinates of an arbitrary normalized pair of complex amplitudes. -/
def amplitudeDirection (a b : ℂ) : Direction :=
  ![2 * (a * conj b).re, -(2 * (a * conj b).im),
    Complex.normSq a - Complex.normSq b]

/-- The parametrization includes every normalized pure single-photon state
and every normalized rank-one receiver vector, not merely real amplitudes. -/
theorem normalized_amplitudes_realized (a b : ℂ)
    (h : Complex.normSq a + Complex.normSq b = 1) :
    radiusSq (amplitudeDirection a b) = 1 ∧
      blochMatrix (amplitudeDirection a b) =
        Matrix.vecMulVec (![a,b] : Fin 2 → ℂ) (fun j => conj ((![a,b] : Fin 2 → ℂ) j)) := by
  have hid : radiusSq (amplitudeDirection a b) =
      (Complex.normSq a + Complex.normSq b) ^ 2 := by
    simp [radiusSq, amplitudeDirection, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im] <;> ring
  refine ⟨by rw [hid, h]; norm_num, ?_⟩
  have hh := h
  simp only [Complex.normSq_apply] at hh
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [blochMatrix, amplitudeDirection, Matrix.vecMulVec,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> nlinarith [hh]

/-- Relative-phase rotation, with the second mode acquiring exp(i*phi). -/
def rotate (r : Direction) (phi : ℝ) : Direction :=
  ![r 0 * Real.cos phi - r 1 * Real.sin phi,
    r 0 * Real.sin phi + r 1 * Real.cos phi, r 2]

/-- The literal phase-encoding matrix in the one-photon sector. -/
def phaseMatrix (phi : ℝ) : QubitMatrix :=
  !![1, 0; 0, Complex.exp ((phi : ℂ) * Complex.I)]

/-- The relative-phase encoder is unitary on the actual two-mode sector. -/
theorem phase_matrix_unitary (phi : ℝ) : (phaseMatrix phi)ᴴ * phaseMatrix phi = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [phaseMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im] <;> nlinarith [Real.sin_sq_add_cos_sq phi]

/-- The coordinate rotation equals conjugation by the physical phase encoder. -/
theorem rotation_is_phase_encoding (r : Direction) (phi : ℝ) :
    blochMatrix (rotate r phi) =
      phaseMatrix phi * blochMatrix r * (phaseMatrix phi)ᴴ := by
  have hs : ((1 - r 2) / 2) * (Real.cos phi ^ 2 + Real.sin phi ^ 2) =
      (1 - r 2) / 2 := by
    rw [add_comm, Real.sin_sq_add_cos_sq]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [blochMatrix, rotate, phaseMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im] <;> nlinarith [hs]

/-- The acquired ideal port probability uses the existing trace Born rule. -/
def bornPort (r n : Direction) (phi : ℝ) : ℝ :=
  (bornProbability (blochMatrix (rotate r phi)) (blochMatrix n)).re

/-- The probability at the fixed, known design phase zero. -/
def portAt (r n : Direction) : ℝ :=
  (1 + r 0 * n 0 + r 1 * n 1 + r 2 * n 2) / 2

/-- The actual phase derivative at that design point. -/
def tangentAt (r n : Direction) : ℝ := (r 0 * n 1 - r 1 * n 0) / 2

/-- Explicit Born curve; no sensitivity is supplied as a hypothesis. -/
theorem born_port_formula (r n : Direction) (phi : ℝ) :
    bornPort r n phi =
      (1 + (r 0 * Real.cos phi - r 1 * Real.sin phi) * n 0 +
        (r 0 * Real.sin phi + r 1 * Real.cos phi) * n 1 + r 2 * n 2) / 2 := by
  norm_num [bornPort, bornProbability, blochMatrix, rotate,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- The recorded local probability is the actual Born value at the design point. -/
theorem born_port_at_zero (r n : Direction) : bornPort r n 0 = portAt r n := by
  simp [born_port_formula, portAt]

/-- The tangent is differentiated from the encoded Born probability. -/
theorem born_port_hasDerivAt (r n : Direction) :
    HasDerivAt (bornPort r n) (tangentAt r n) 0 := by
  have h := ((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
    ((((Real.hasDerivAt_cos 0).const_mul (r 0)).sub
       ((Real.hasDerivAt_sin 0).const_mul (r 1))).mul_const (n 0))).add
    ((((Real.hasDerivAt_sin 0).const_mul (r 0)).add
       ((Real.hasDerivAt_cos 0).const_mul (r 1))).mul_const (n 1))).add_const
    (r 2 * n 2)).div_const 2
  have hf : bornPort r n = fun phi =>
      (1 + (r 0 * Real.cos phi - r 1 * Real.sin phi) * n 0 +
        (r 0 * Real.sin phi + r 1 * Real.cos phi) * n 1 + r 2 * n 2) / 2 :=
    funext (born_port_formula r n)
  rw [hf]
  convert h using 1 <;> simp [tangentAt] <;> ring

/-- The local Born jet lies in the sharp probability-tangent disk. -/
theorem born_jet_bound (r n : Direction) (hr : radiusSq r = 1) (hn : radiusSq n = 1) :
    0 ≤ portAt r n ∧ portAt r n ≤ 1 ∧
      tangentAt r n ^ 2 ≤ portAt r n * (1 - portAt r n) := by
  have hid :
      (r 0*n 0+r 1*n 1+r 2*n 2)^2 + (r 0*n 1-r 1*n 0)^2 +
        (r 1*n 2-r 2*n 1)^2 + (r 2*n 0-r 0*n 2)^2 = radiusSq r * radiusSq n := by
    unfold radiusSq
    ring
  rw [hr, hn, one_mul] at hid
  have hdot : (r 0*n 0+r 1*n 1+r 2*n 2)^2 ≤ 1 := by
    nlinarith [sq_nonneg (r 0*n 1-r 1*n 0), sq_nonneg (r 1*n 2-r 2*n 1),
      sq_nonneg (r 2*n 0-r 0*n 2)]
  have hlo : -1 ≤ r 0*n 0+r 1*n 1+r 2*n 2 := by nlinarith
  have hhi : r 0*n 0+r 1*n 1+r 2*n 2 ≤ 1 := by nlinarith
  unfold portAt tangentAt
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith [sq_nonneg (r 1*n 2-r 2*n 1), sq_nonneg (r 2*n 0-r 0*n 2)]

/-- A balanced pure probe; the receiver alone moves the design point. -/
def balancedProbe : Direction := ![1,0,0]

/-- A realizable unit projective receiver attaining the tangent envelope. -/
def attainingReceiver (p : ℝ) : Direction := ![2*p-1, 2*Real.sqrt (p*(1-p)), 0]

/-- Every probability in [0,1] is attained together with the largest allowed
squared tangent. This is the witness used by the detector optimization. -/
theorem receiver_attains_jet (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    radiusSq balancedProbe = 1 ∧ radiusSq (attainingReceiver p) = 1 ∧
      portAt balancedProbe (attainingReceiver p) = p ∧
      tangentAt balancedProbe (attainingReceiver p) ^ 2 = p*(1-p) := by
  have hsq := Real.sq_sqrt (mul_nonneg hp0 (sub_nonneg.mpr hp1))
  refine ⟨by norm_num [radiusSq, balancedProbe], ?_, ?_, ?_⟩
  · norm_num [radiusSq, attainingReceiver] <;> nlinarith [hsq]
  · norm_num [portAt, balancedProbe, attainingReceiver] <;> ring
  · norm_num [tangentAt, balancedProbe, attainingReceiver] <;> nlinarith [hsq]

#print axioms normalized_amplitudes_realized
#print axioms rotation_is_phase_encoding
#print axioms born_port_hasDerivAt
#print axioms born_jet_bound
#print axioms receiver_attains_jet

end D5.S3.Quantum.Metrology.SinglePhotonReceiver
end
