/- GID: D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation.claim; result=D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation.result; claim=D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation.claim
   digest: A full-public-flag rational witness obstructs exact error-state erasure. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#24328; Refuted).
Private proof_shape: bind-only for ket_trace (consumer sigma), rho_psd and
rho_trace (consumer flagged), distance_of_square (consumers correct_distance and
perturbation_distance), correct_distance and perturbation_distance (consumer
disturbance_bound), and disturbance_bound (consumer result).
Direct frozen dependencies (declaration GID and statement_id):
rhoET:
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
  sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
ErasesErrorsPreservingCorrect:
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
  sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
  D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel
  sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05
  D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap
  sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc
claim:
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
  sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
  D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel
  sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05
  D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap
  sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc
ket:
  none.
ket_trace:
  none.
sigma:
  none.
rho_psd:
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
  sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
rho_trace:
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
  sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
flagged:
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
  sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
distance_of_square:
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
  sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance
  sha256:a951383b42658bc45458c21e07d0f1306eb2d0af3f5709cef4338a96b4a21c20
correct_distance:
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
  sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance
  sha256:a951383b42658bc45458c21e07d0f1306eb2d0af3f5709cef4338a96b4a21c20
perturbation_distance:
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
  sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance
  sha256:a951383b42658bc45458c21e07d0f1306eb2d0af3f5709cef4338a96b4a21c20
disturbance_bound:
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
  sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
  D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel
  sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05
  D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel.mapState
  sha256:85f38416b2caa15929825cb7cf7f1b334998a7ccc859cdb9374b371763e208d9
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance
  sha256:a951383b42658bc45458c21e07d0f1306eb2d0af3f5709cef4338a96b4a21c20
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_contract
  sha256:d1ce433ffc536086a361916e97950143175007f261f83b5618dc580022734f56
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_symm
  sha256:37f643301bff9cc278091610e4429102318a6ae601d6a720ccf135650252061c
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_triangle
  sha256:3e39bbc546c4f2f84227266629b13852790c1a317807dc15bbc188b953fee079
result:
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
  sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
  D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel
  sha256:b7b2554d55122b11b177ecdf92367d243e4d35ec1e3897c844deba5df1285d05
  D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel.mapState
  sha256:85f38416b2caa15929825cb7cf7f1b334998a7ccc859cdb9374b371763e208d9
  D5/S3/Quantum/Foundation/FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap
  sha256:7e2eefba0a4c0a6af6a4d36e7168066ad5899f2ba2622c43f082056bec8fb7dc
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance
  sha256:a951383b42658bc45458c21e07d0f1306eb2d0af3f5709cef4338a96b4a21c20
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance._proof_1
  sha256:786a0c12941226388043cfbd6d2fe1a86d4e3cf8b6be93df8b354b845e23f6e7
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_contract
  sha256:d1ce433ffc536086a361916e97950143175007f261f83b5618dc580022734f56
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_symm
  sha256:37f643301bff9cc278091610e4429102318a6ae601d6a720ccf135650252061c
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceDistance_triangle
  sha256:3e39bbc546c4f2f84227266629b13852790c1a317807dc15bbc188b953fee079
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm
  sha256:12ad034b5758446e6d628c75121b3ad5f0c80bb305937e8c9ff87e82076bc059
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm._proof_1
  sha256:b1586fdd8f90368f29693bf2d79bbde6eef95de7877836ce053c092745767dcb
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm._proof_2
  sha256:2c4ba5b5c99b826fb97b25dec25e9c500d187206dfe78430a0de7fd11c71bb2b
  D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm._proof_7
  sha256:5f854fd7eee62349e53f46e6718cdea507d64df8d2f6b1e2ba8e1da15cd9898c
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
The public definitions retain equation (6) and the operational assertion literally;
proofs use Matrix.vecMulVec and Pi.single directly, without forwarding definitions.
The rational two-dimensional witness retains the full public Bool flag; the channel
may act jointly on ET. The physical preparation, Bell violation and Chernoff
computations are separate evidence, not Lean statements of this module.
-/

import D5.S3.Quantum.Foundation.FiniteTraceDistance

import D5.S3.Quantum.Foundation.FiniteStateChannel

/-! A rational ensemble obstructs exact erasure by an arbitrary joint ET channel. -/



namespace D5.S3.Quantum.Foundation.StasiukLutkenhausTanErrorStateErasureRefutation

open D5.S3.Quantum.Foundation.FiniteStateChannel

/-- Equation (6), with row (e,t) and column (f,u), including the full public flag.
The entrywise form of |t><t| is the Kronecker delta on the two flag indices. -/
noncomputable def rhoET {d : ℕ}
    (sigma : Bool → Bool → DensityState (Fin d)) (a b : Bool) :
    Matrix (Fin d × Bool) (Fin d × Bool) ℂ :=
  fun i j =>
    if i.2 = j.2 then
      (1 / 2 : ℂ) *
        (if i.2 then (sigma (!a) (!b)).val i.1 j.1 else (sigma a b).val i.1 j.1)
    else 0

/-- The one CPTP operation acts on all of ET, including coherent operations on T. -/
def ErasesErrorsPreservingCorrect {d : ℕ}
    (sigma : Bool → Bool → DensityState (Fin d))
    (channel : QuantumChannel (Fin d × Bool) (Fin d × Bool)) : Prop :=
  channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (rhoET sigma false false)) =
      CStarMatrix.ofMatrix (rhoET sigma false false) ∧
  channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (rhoET sigma true true)) =
      CStarMatrix.ofMatrix (rhoET sigma true true) ∧
  channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (rhoET sigma false true)) =
      channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (rhoET sigma true false))

/-- The source's universal local-operation assertion, not replacement of the attack.
All four normalized pre-symmetrization conditional states and every finite Eve
system are universally quantified. A single channel must satisfy all three
requirements simultaneously. -/
def claim : Prop :=
  ∀ (d : ℕ) (sigma : Bool → Bool → DensityState (Fin d)),
    ∃ channel : QuantumChannel (Fin d × Bool) (Fin d × Bool),
      ErasesErrorsPreservingCorrect sigma channel

end D5.S3.Quantum.Foundation.StasiukLutkenhausTanErrorStateErasureRefutation

set_option maxRecDepth 4096

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
namespace D5.S3.Quantum.Foundation.StasiukLutkenhausTanErrorStateErasureRefutation

private def ket : Bool → Bool → Fin 2 → ℂ
  | false, false => ![1, 0]
  | true, true => ![3/5, 4/5]
  | false, true => ![9999/10001, 200/10001]
  | true, false => ![29197/50005, 40596/50005]

set_option maxHeartbeats 4000000 in
private theorem ket_trace (a b : Bool) : trace (vecMulVec (ket a b) (star (ket a b))) = 1 := by
  cases a <;> cases b <;>
    norm_num [ket, trace, Fin.sum_univ_two, vecMulVec, star_div₀, map_ofNat]

private def sigma (a b : Bool) : DensityState (Fin 2) :=
  ⟨CStarMatrix.ofMatrix (vecMulVec (ket a b) (star (ket a b))),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (posSemidef_vecMulVec_self_star _).nonneg,
    ket_trace a b⟩

set_option maxHeartbeats 4000000 in
private theorem rho_psd (a b : Bool) : (rhoET sigma a b).PosSemidef := by
  have heq : rhoET sigma a b = (1/2 : ℝ) •
      (vecMulVec (fun i : Fin 2 × Bool => (Pi.single false (ket a b i.1) : Bool → ℂ) i.2) (star (fun i : Fin 2 × Bool => (Pi.single false (ket a b i.1) : Bool → ℂ) i.2)) +
       vecMulVec (fun i : Fin 2 × Bool => (Pi.single true (ket (!a) (!b) i.1) : Bool → ℂ) i.2) (star (fun i : Fin 2 × Bool => (Pi.single true (ket (!a) (!b) i.1) : Bool → ℂ) i.2))) := by
    ext ⟨i,t⟩ ⟨j,u⟩
    cases t <;> cases u <;>
      simp [rhoET, sigma, Pi.single_apply, vecMulVec, Complex.real_smul]
  rw [heq]
  exact ((posSemidef_vecMulVec_self_star _).add
    (posSemidef_vecMulVec_self_star _)).smul (by norm_num : (0:ℝ) ≤ 1/2)

set_option maxHeartbeats 4000000 in
private theorem rho_trace (a b : Bool) : trace (rhoET sigma a b) = 1 := by
  cases a <;> cases b <;>
    norm_num [rhoET, sigma, ket, trace, Fintype.sum_prod_type,
      Fin.sum_univ_two, vecMulVec, star_div₀, map_ofNat]

private def flagged (a b : Bool) : DensityState (Fin 2 × Bool) :=
  ⟨CStarMatrix.ofMatrix (rhoET sigma a b),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (rho_psd a b).nonneg,
    rho_trace a b⟩


set_option maxHeartbeats 4000000 in
private theorem distance_of_square (a b c d : Bool) (r : ℝ) (hr : 0 ≤ r)
    (hs : (diagonal (fun _ : Fin 2 × Bool => (r : ℂ))) *
        (diagonal (fun _ : Fin 2 × Bool => (r : ℂ))) =
        (rhoET sigma a b - rhoET sigma c d)ᴴ *
        (rhoET sigma a b - rhoET sigma c d)) :
    traceDistance (flagged a b) (flagged c d) = 2 * r := by
  have hp : (diagonal (fun _ : Fin 2 × Bool => (r : ℂ))).PosSemidef :=
    posSemidef_diagonal_iff.mpr (fun _ => by exact_mod_cast hr)
  change (CFC.sqrt ((rhoET sigma a b - rhoET sigma c d)ᴴ *
    (rhoET sigma a b - rhoET sigma c d))).trace.re / 2 = 2 * r
  rw [CFC.sqrt_unique hs hp.nonneg]
  simp [trace_diagonal]
  ring

set_option maxHeartbeats 4000000 in
private theorem correct_distance :
    traceDistance (flagged false false) (flagged true true) = 4/5 := by
  have hs : diagonal (fun _ : Fin 2 × Bool => (2/5 : ℂ)) *
      diagonal (fun _ : Fin 2 × Bool => (2/5 : ℂ)) =
      (rhoET sigma false false - rhoET sigma true true)ᴴ *
      (rhoET sigma false false - rhoET sigma true true) := by
    ext ⟨i,t⟩ ⟨j,u⟩
    fin_cases i <;> fin_cases j <;> cases t <;> cases u <;>
      norm_num [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        rhoET, sigma, ket, vecMulVec, Matrix.conjTranspose_apply,
        Matrix.diagonal_apply, star_div₀, map_ofNat]
  convert distance_of_square false false true true (2/5) (by norm_num)
    (by simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hs) using 1; norm_num

set_option maxHeartbeats 4000000 in
private theorem perturbation_distance (a : Bool) :
    traceDistance (flagged a a) (flagged a (!a)) = 200/10001 := by
  have hs : diagonal (fun _ : Fin 2 × Bool => (100/10001 : ℂ)) *
      diagonal (fun _ : Fin 2 × Bool => (100/10001 : ℂ)) =
      (rhoET sigma a a - rhoET sigma a (!a))ᴴ *
      (rhoET sigma a a - rhoET sigma a (!a)) := by
    cases a <;> ext ⟨i,t⟩ ⟨j,u⟩ <;>
    fin_cases i <;> fin_cases j <;> cases t <;> cases u <;>
      norm_num [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        rhoET, sigma, ket, vecMulVec, Matrix.conjTranspose_apply,
        Matrix.diagonal_apply, star_div₀, map_ofNat]
  convert distance_of_square a a a (!a) (100/10001) (by norm_num)
    (by simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hs) using 1; norm_num


set_option maxHeartbeats 4000000 in
private theorem disturbance_bound
    (channel : QuantumChannel (Fin 2 × Bool) (Fin 2 × Bool)) :
    (38004/50005 : ℝ) ≤
      traceDistance (flagged false false) (channel.mapState (flagged false false)) +
      traceDistance (flagged true true) (channel.mapState (flagged true true)) +
      traceDistance (channel.mapState (flagged false true))
        (channel.mapState (flagged true false)) := by
  have h0 := traceDistance_triangle (flagged false false)
    (channel.mapState (flagged false false)) (channel.mapState (flagged false true))
  have h1 := traceDistance_triangle (flagged false false)
    (channel.mapState (flagged false true)) (channel.mapState (flagged true false))
  have h2 := traceDistance_triangle (flagged false false)
    (channel.mapState (flagged true false)) (channel.mapState (flagged true true))
  have h3 := traceDistance_triangle (flagged false false)
    (channel.mapState (flagged true true)) (flagged true true)
  have c0 := traceDistance_contract channel (flagged false false) (flagged false true)
  have c1 := traceDistance_contract channel (flagged true true) (flagged true false)
  rw [correct_distance] at h3
  rw [traceDistance_symm (channel.mapState (flagged true false))] at h2
  rw [traceDistance_symm (channel.mapState (flagged true true))] at h3
  have p0 := perturbation_distance false
  have p1 := perturbation_distance true
  simp only [Bool.not_false, Bool.not_true] at p0 p1
  linarith

set_option maxHeartbeats 4000000 in
theorem result : ¬ claim := by
  intro h
  obtain ⟨channel, h00, h11, h01⟩ := h 2 sigma
  have m00 : channel.mapState (flagged false false) = flagged false false :=
    Subtype.ext h00
  have m11 : channel.mapState (flagged true true) = flagged true true :=
    Subtype.ext h11
  have m01 : channel.mapState (flagged false true) = channel.mapState (flagged true false) :=
    Subtype.ext h01
  have hb := disturbance_bound channel
  rw [m00, m11, m01] at hb
  norm_num [traceDistance, sub_self, traceNorm, Matrix.conjTranspose_zero,
    Matrix.mul_zero, CFC.sqrt_zero] at hb

end D5.S3.Quantum.Foundation.StasiukLutkenhausTanErrorStateErasureRefutation
