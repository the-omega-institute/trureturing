/- GID: D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/SwitchUselessConcatenationRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.claim; result=D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.result; claim=D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.claim
   digest: Two useless qubit channels have a non-EB concatenation switch branch. -/

/-
result
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#16400; Refuted)
Direct frozen dependencies use the declaration identities listed below.
The identities are from the origin/dev base report; published owners retain
their baseline private declaration identities here and require a new scoped
report and canonical re-pin for the public names.
F1 = D5/S3/Quantum/FiniteDimensional.QubitMatrix sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30
F2 = D5/S3/Quantum/FiniteDimensional.qubitX sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
F3 = D5/S3/Quantum/FiniteDimensional.qubitZ sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
F4 = D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
F5 = D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.kron sha256:6bbbe42180d7cde8ee171b8a1aeeb16449194862345f2042d95ec7c0b2055471
F6 = D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
F7 = D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.I sha256:194b87c5757c4209245572dae83ba02c7d0b8bc34b3603b0077d1f7bef8d5086
F8 = D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.X sha256:c5a0ae88d76c4eaaa4b6fe8a43d173573dc140906b88c1033f4a61033ac6288e
F9 = D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Y sha256:35dc0190894fc92420f9611604a3030c3f0caed3c92ee732a2224b7a3343e92a
F10 = D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.Pauli.Z sha256:13af366bc311e9f007d266b48686e5771e4117ded2ded1aa5085eff8b4b2ff69
F11 = D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix sha256:7f853eaeda888a9eccbab5fe25474fc62b519a3229013530986887de25cb28d7
F12 = D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.octVec sha256:0883e8ea081c41485fd4913c1aecd1ad10ae2bfa025d5db81607b4903e4e94aa
F13 = D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsEB sha256:77b643493753433b52c77050ea4728e1e1d7de02484e1d7caca6286c250a7729
F14 = D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.SEP sha256:db2b2ea52566ceb8270adf10aebd0001b69c464ab6d78615550f23ba2afa40f4
F15 = D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.prepare_eb sha256:95c9c6b584631812eeb1791ab9ab72bd181efbd19b0cb08f6e18b03cd29fc50c
F16 = D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.ptFirst sha256:1830213b78378f17a20579ffdd4aa8b9f71017075b34de9d3ab9e2dd27634755
F17 = D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.sigma sha256:8d32b4e3e5803524e6569b40c43fffbb84b46699655ec967674ed337624d369d
Per-declaration classification (definitions encode the stated constructions;
proofs use those constructions, existing positivity results and normalization):
IsKrausChannel: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: channel_A, channel_B, claim.
switchPlus: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F4, F6; consumers: CompletelyUseless, eb_plus_A, eb_plus_B, plus_A_prepare, plus_B_prepare, result, useless_A, useless_B.
switchMinus: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F4, F6; consumers: CompletelyUseless, eb_minus_A, eb_minus_B, minus_A_prepare, minus_B_prepare, result, useless_A, useless_B, witness_sum, witness_value.
CompletelyUseless: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F4, F6, F13; consumers: claim, result, useless_A, useless_B.
composeKraus: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: claim, compositeG_eq, minusG_eq, minusK, result, witness_sum, witness_value.
claim: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F4, F6, F13; consumers: result.
tilted: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F17; consumers: B, base_B_prepare, channel_B, compositeG_eq, minus_B_prepare, plus_B_prepare, tiltedTable.
weight: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: A, B, channel_A, channel_B, compositeG_eq.
A: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F17; consumers: base_A_prepare, channel_A, compositeG_eq, eb_base_A, eb_minus_A, eb_plus_A, minusG_eq, minusK, minus_A_prepare, plus_A_prepare, result, useless_A, witness_sum, witness_value.
B: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F17; consumers: base_B_prepare, channel_B, compositeG_eq, eb_base_B, eb_minus_B, eb_plus_B, minusG_eq, minusK, minus_B_prepare, plus_B_prepare, result, useless_B, witness_sum, witness_value.
frameB: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: base_B_prepare, eb_base_B, eb_minus_B, eb_plus_B, measures_B_pos, minus_B_prepare, plus_B_prepare.
normsA: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: base_A_prepare, eb_base_A, eb_minus_A, eb_plus_A, measures_A_pos, minus_A_prepare, plus_A_prepare.
normsB: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: base_B_prepare, eb_base_B, eb_minus_B, eb_plus_B, measures_B_pos, minus_B_prepare, plus_B_prepare.
coeffBase: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: base_A_prepare, base_B_prepare, eb_base_A, eb_base_B, eb_minus_A, eb_minus_B, eb_plus_A, eb_plus_B, measures_A_pos, measures_B_pos.
coeffPlus: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: eb_base_A, eb_base_B, eb_minus_A, eb_minus_B, eb_plus_A, eb_plus_B, measures_A_pos, measures_B_pos, plus_A_prepare, plus_B_prepare.
coeffMinus: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: eb_base_A, eb_base_B, eb_minus_A, eb_minus_B, eb_plus_A, eb_plus_B, measures_A_pos, measures_B_pos, minus_A_prepare, minus_B_prepare.
measure: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: base_A_prepare, base_B_prepare, eb_base_A, eb_base_B, eb_minus_A, eb_minus_B, eb_plus_A, eb_plus_B, measure_pos, measures_A_pos, measures_B_pos, minus_A_prepare, minus_B_prepare, plus_A_prepare, plus_B_prepare.
prepare: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: base_A_prepare, base_B_prepare, eb_base_A, eb_base_B, eb_minus_A, eb_minus_B, eb_plus_A, eb_plus_B, minus_A_prepare, minus_B_prepare, plus_A_prepare, plus_B_prepare, prepare_pos.
sigmaTable: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F7, F8, F9, F10, F11, F17; consumers: base_A_prepare, base_B_prepare, channel_A, compositeG_eq, minus_A_prepare, minus_B_prepare, plus_A_prepare, plus_B_prepare, tiltedTable.
tiltedTable: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F7, F8, F9, F10, F11, F17; consumers: channel_B, compositeG_eq.
octFrameTable: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F12; consumers: base_A_prepare, minus_A_prepare, plus_A_prepare.
ofKrausApply: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F4, F6; consumers: base_A_prepare, base_B_prepare, minus_A_prepare, minus_B_prepare, plus_A_prepare, plus_B_prepare.
channel_A: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F7, F8, F9, F10, F11, F17; consumers: result.
channel_B: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F7, F8, F9, F10, F11, F17; consumers: result.
base_A_prepare: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F6, F7, F8, F9, F10, F11, F12, F17; consumers: eb_base_A.
base_B_prepare: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F6, F7, F8, F9, F10, F11, F17; consumers: eb_base_B.
plus_A_prepare: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F6, F7, F8, F9, F10, F11, F12, F17; consumers: eb_plus_A.
plus_B_prepare: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F6, F7, F8, F9, F10, F11, F17; consumers: eb_plus_B.
minus_A_prepare: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F6, F7, F8, F9, F10, F11, F12, F17; consumers: eb_minus_A.
minus_B_prepare: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F6, F7, F8, F9, F10, F11, F17; consumers: eb_minus_B.
prepare_pos: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: eb_base_A, eb_base_B, eb_minus_A, eb_minus_B, eb_plus_A, eb_plus_B.
measure_pos: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: measures_A_pos, measures_B_pos.
measures_A_pos: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F12; consumers: eb_base_A, eb_minus_A, eb_plus_A.
measures_B_pos: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: eb_base_B, eb_minus_B, eb_plus_B.
eb_base_A: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F6, F7, F8, F9, F10, F11, F12, F13, F15, F17; consumers: useless_A.
eb_base_B: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F6, F7, F8, F9, F10, F11, F13, F15, F17; consumers: useless_B.
eb_plus_A: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F6, F7, F8, F9, F10, F11, F12, F13, F15, F17; consumers: useless_A.
eb_plus_B: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F6, F7, F8, F9, F10, F11, F13, F15, F17; consumers: useless_B.
eb_minus_A: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F6, F7, F8, F9, F10, F11, F12, F13, F15, F17; consumers: useless_A.
eb_minus_B: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F6, F7, F8, F9, F10, F11, F13, F15, F17; consumers: useless_B.
useless_A: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F6, F7, F8, F9, F10, F11, F12, F13, F15, F17; consumers: result.
useless_B: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F6, F7, F8, F9, F10, F11, F13, F15, F17; consumers: result.
sep_pt_psd: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F14, F16; consumers: notEB_of_witness.
notEB_of_witness: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F4, F5, F13, F14, F16; consumers: result.
wG: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: qG, qval, qval_mapG, qval_smul, result, witness_sum, witness_value.
minusK: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F17; consumers: minusG_eq, witness_sum, witness_value.
qval: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F16; consumers: qval_mapG, qval_smul, witness_sum, witness_value.
witness_sum: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F4, F6, F16, F17; consumers: witness_value.
compositeG: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: compositeG_eq, minusG, minusG_eq.
compositeG_eq: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F7, F8, F9, F10, F11, F17; consumers: minusG_eq.
minusG: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: minusG_eq, totalG, totalG_complex, witness_value.
minusG_eq: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F7, F8, F9, F10, F11, F17; consumers: witness_value.
qG: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: qval_mapG, totalG, totalG_complex, witness_value.
qval_mapG: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F16; consumers: witness_value.
qval_smul: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F16; consumers: witness_value.
totalG: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: totalG_complex.
totalG_complex: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: none; consumers: witness_value.
witness_value: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F6, F7, F8, F9, F10, F11, F16, F17; consumers: result.
result: proof_shape: bind-only; escape_witness: none;
  Direct frozen dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17; consumers: none.
The Kraus-map expression uses MatrixMap.of_kraus K K directly.
The unfrozen closed FiniteKrausRepresentation import supplies Choi operations;
its declarations are not counted as frozen dependencies.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
Escape audit unfinished for the published owner prepare_eb: https://github.com/the-omega-institute/trureturing/issues/16693
Only eta = 24/25 is settled here. Family-wide and common-axis questions remain open.
-/

import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
import D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsEB SEP ptFirst)
namespace D5.S3.QuantumChannels.SwitchUselessConcatenationRefutation
universe u v
variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
def IsKrausChannel (K : ι → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∑ i, (K i)ᴴ * K i = 1

def switchPlus (K : ι → Matrix (Fin 2) (Fin 2) ℂ) : MatrixMap (Fin 2) (Fin 2) ℂ :=
  MatrixMap.of_kraus
    (fun p : ι × ι => (1 / 2 : ℂ) • (K p.1 * K p.2 + K p.2 * K p.1))
    (fun p : ι × ι => (1 / 2 : ℂ) • (K p.1 * K p.2 + K p.2 * K p.1))

def switchMinus (K : ι → Matrix (Fin 2) (Fin 2) ℂ) : MatrixMap (Fin 2) (Fin 2) ℂ :=
  MatrixMap.of_kraus
    (fun p : ι × ι => (1 / 2 : ℂ) • (K p.1 * K p.2 - K p.2 * K p.1))
    (fun p : ι × ι => (1 / 2 : ℂ) • (K p.1 * K p.2 - K p.2 * K p.1))

def CompletelyUseless (K : ι → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  IsEB (MatrixMap.of_kraus K K) ∧ IsEB (switchPlus K) ∧ IsEB (switchMinus K)

def composeKraus (L : κ → Matrix (Fin 2) (Fin 2) ℂ)
    (K : ι → Matrix (Fin 2) (Fin 2) ℂ) : ι × κ → Matrix (Fin 2) (Fin 2) ℂ :=
  fun p => L p.2 * K p.1

def claim : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
    (K : ι → Matrix (Fin 2) (Fin 2) ℂ) (L : κ → Matrix (Fin 2) (Fin 2) ℂ),
    IsKrausChannel K → IsKrausChannel L → CompletelyUseless K → CompletelyUseless L →
    CompletelyUseless (composeKraus L K)


set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

private def tilted (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  match i.val with
  | 0 => D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma 0
  | 1 => (3/5 : ℂ) • D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma 1 -
      (4/5 : ℂ) • D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma 3
  | 2 => D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma 2
  | _ => (4/5 : ℂ) • D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma 1 +
      (3/5 : ℂ) • D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma 3
private def weight (i : Fin 4) : ℂ :=
  match i.val with | 0 => 7/10 | 1 => 1/10 | 2 => 1/10 | _ => 7/10
private def A (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ := weight i • D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma i
private def B (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ := weight i • tilted i

private def frameB (i : Fin 6) : Fin 2 → ℂ :=
  match i.val with
  | 0 => ![1,3] | 1 => ![3,-1] | 2 => ![2-Complex.I,1+2*Complex.I]
  | 3 => ![2+Complex.I,1-2*Complex.I] | 4 => ![2,1] | _ => ![-1,2]
private def normsA (i : Fin 3) : ℂ := match i.val with | 0 => 2 | 1 => 2 | _ => 1
private def normsB (i : Fin 3) : ℂ := match i.val with | 0 => 10 | 1 => 10 | _ => 5
private def coeffBase (i : Fin 4) : ℂ :=
  match i.val with | 0 => 0 | 1 => 0 | 2 => 24/25 | _ => 1/25
private def coeffPlus (i : Fin 4) : ℂ :=
  match i.val with | 0 => 1/5000 | 1 => 1/5000 | 2 => 941/1000 | _ => 97/2500
private def coeffMinus (i : Fin 4) : ℂ :=
  match i.val with | 0 => 1/5000 | 1 => 1/5000 | 2 => 97/5000 | _ => 0

private def measure (f : Fin 6 → Fin 2 → ℂ) (n : Fin 3 → ℂ) (c : Fin 4 → ℂ)
    (j : Fin 8) : Matrix (Fin 2) (Fin 2) ℂ :=
  match j.val with
  | 0 => (c 0 / (n 0)^2) • (fun x => Matrix.vecMulVec x (star x)) (f 0)
  | 1 => (c 0 / (n 0)^2) • (fun x => Matrix.vecMulVec x (star x)) (f 1)
  | 2 => (c 1 / (n 1)^2) • (fun x => Matrix.vecMulVec x (star x)) (f 2)
  | 3 => (c 1 / (n 1)^2) • (fun x => Matrix.vecMulVec x (star x)) (f 3)
  | 4 => (c 2 / (n 2)^2) • (fun x => Matrix.vecMulVec x (star x)) (f 4)
  | 5 => (c 2 / (n 2)^2) • (fun x => Matrix.vecMulVec x (star x)) (f 5)
  | _ => (c 3 / 2) • 1
private def prepare (f : Fin 6 → Fin 2 → ℂ) (neg : Bool)
    (j : Fin 8) : Matrix (Fin 2) (Fin 2) ℂ :=
  match j.val with
  | 0 => (fun x => Matrix.vecMulVec x (star x)) (f (if neg then 1 else 0))
  | 1 => (fun x => Matrix.vecMulVec x (star x)) (f (if neg then 0 else 1))
  | 2 => (fun x => Matrix.vecMulVec x (star x)) (f (if neg then 3 else 2))
  | 3 => (fun x => Matrix.vecMulVec x (star x)) (f (if neg then 2 else 3))
  | 4 => (fun x => Matrix.vecMulVec x (star x)) (f (if neg then 5 else 4))
  | 5 => (fun x => Matrix.vecMulVec x (star x)) (f (if neg then 4 else 5))
  | 6 => (fun x => Matrix.vecMulVec x (star x)) ![1,0]
  | _ => (fun x => Matrix.vecMulVec x (star x)) ![0,1]

private lemma sigmaTable (i : Fin 4) :
    D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma i =
      match i.val with
      | 0 => !![1,0;0,1]
      | 1 => !![0,1;1,0]
      | 2 => !![0,-Complex.I;Complex.I,0]
      | _ => !![1,0;0,-1] := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness.sigma,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
      Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_succ]
private lemma tiltedTable (i : Fin 4) :
    tilted i = match i.val with
      | 0 => !![1,0;0,1]
      | 1 => !![-(4/5),3/5;3/5,4/5]
      | 2 => !![0,-Complex.I;Complex.I,0]
      | _ => !![3/5,4/5;4/5,-(3/5)] := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [tilted, sigmaTable, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply]

private lemma octFrameTable (i : Fin 6) :
    D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2) =
      match i.val with
      | 0 => ![1,1] | 1 => ![1,-1] | 2 => ![1,Complex.I]
      | 3 => ![1,-Complex.I] | 4 => ![1,0] | _ => ![0,1] := by
  fin_cases i <;> rfl

private lemma ofKrausApply (K : ι → Matrix (Fin 2) (Fin 2) ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    MatrixMap.of_kraus K K X = ∑ i, K i * X * (K i)ᴴ := by
  simp [MatrixMap.of_kraus, LinearMap.sum_apply]

private lemma channel_A : IsKrausChannel A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [IsKrausChannel, A, weight, sigmaTable, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.sum_apply, Matrix.smul_apply, Fin.sum_univ_succ, Matrix.one_apply, Complex.ext_iff,
      map_ofNat, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
private lemma channel_B : IsKrausChannel B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [IsKrausChannel, B, weight, tiltedTable, sigmaTable, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.sum_apply, Matrix.smul_apply, Fin.sum_univ_succ, Matrix.one_apply, Complex.ext_iff,
      map_ofNat, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

private lemma base_A_prepare (X : Matrix (Fin 2) (Fin 2) ℂ) :
    MatrixMap.of_kraus A A X = ∑ j, (measure (fun i : Fin 6 => D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2)) normsA coeffBase j * X).trace • prepare (fun i : Fin 6 => D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2)) false j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [switchPlus, switchMinus, ofKrausApply, Fintype.sum_prod_type, A, B, weight, sigmaTable, tilted, measure, prepare, octFrameTable, normsA, coeffBase,
       Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Matrix.trace, Matrix.diag, Matrix.add_apply, Matrix.sub_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.one_apply, Pi.star_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_succ',
      Matrix.of_apply, map_div₀, map_mul, map_neg, map_ofNat, map_one, map_zero,
      Complex.conj_I] <;>
    norm_num [Complex.ext_iff, map_ofNat] <;> ring_nf <;> simp <;> norm_num <;> ring

private lemma base_B_prepare (X : Matrix (Fin 2) (Fin 2) ℂ) :
    MatrixMap.of_kraus B B X = ∑ j, (measure frameB normsB coeffBase j * X).trace • prepare frameB false j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [switchPlus, switchMinus, ofKrausApply, Fintype.sum_prod_type, A, B, weight, sigmaTable, tilted, measure, prepare, frameB, normsB, coeffBase,
       Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Matrix.trace, Matrix.diag, Matrix.add_apply, Matrix.sub_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.one_apply, Pi.star_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_succ',
      Matrix.of_apply, map_div₀, map_mul, map_neg, map_ofNat, map_one, map_zero,
      Complex.conj_I] <;>
    norm_num [Complex.ext_iff, map_ofNat] <;> ring_nf <;> simp <;> norm_num <;> ring

private lemma plus_A_prepare (X : Matrix (Fin 2) (Fin 2) ℂ) :
    switchPlus A X = ∑ j, (measure (fun i : Fin 6 => D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2)) normsA coeffPlus j * X).trace • prepare (fun i : Fin 6 => D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2)) false j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [switchPlus, switchMinus, ofKrausApply, Fintype.sum_prod_type, A, B, weight, sigmaTable, tilted, measure, prepare, octFrameTable, normsA, coeffPlus,
       Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Matrix.trace, Matrix.diag, Matrix.add_apply, Matrix.sub_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.one_apply, Pi.star_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_succ',
      Matrix.of_apply, map_div₀, map_mul, map_neg, map_ofNat, map_one, map_zero,
      Complex.conj_I] <;>
    norm_num [Complex.ext_iff, map_ofNat] <;> ring_nf <;> simp <;> norm_num <;> ring

private lemma plus_B_prepare (X : Matrix (Fin 2) (Fin 2) ℂ) :
    switchPlus B X = ∑ j, (measure frameB normsB coeffPlus j * X).trace • prepare frameB false j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [switchPlus, switchMinus, ofKrausApply, Fintype.sum_prod_type, A, B, weight, sigmaTable, tilted, measure, prepare, frameB, normsB, coeffPlus,
       Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Matrix.trace, Matrix.diag, Matrix.add_apply, Matrix.sub_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.one_apply, Pi.star_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_succ',
      Matrix.of_apply, map_div₀, map_mul, map_neg, map_ofNat, map_one, map_zero,
      Complex.conj_I] <;>
    norm_num [Complex.ext_iff, map_ofNat] <;> ring_nf <;> simp <;> norm_num <;> ring

private lemma minus_A_prepare (X : Matrix (Fin 2) (Fin 2) ℂ) :
    switchMinus A X = ∑ j, (measure (fun i : Fin 6 => D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2)) normsA coeffMinus j * X).trace • prepare (fun i : Fin 6 => D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2)) true j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [switchPlus, switchMinus, ofKrausApply, Fintype.sum_prod_type, A, B, weight, sigmaTable, tilted, measure, prepare, octFrameTable, normsA, coeffMinus,
       Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Matrix.trace, Matrix.diag, Matrix.add_apply, Matrix.sub_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.one_apply, Pi.star_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_succ',
      Matrix.of_apply, map_div₀, map_mul, map_neg, map_ofNat, map_one, map_zero,
      Complex.conj_I] <;>
    norm_num [Complex.ext_iff, map_ofNat] <;> ring_nf <;> simp <;> norm_num <;> ring

private lemma minus_B_prepare (X : Matrix (Fin 2) (Fin 2) ℂ) :
    switchMinus B X = ∑ j, (measure frameB normsB coeffMinus j * X).trace • prepare frameB true j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [switchPlus, switchMinus, ofKrausApply, Fintype.sum_prod_type, A, B, weight, sigmaTable, tilted, measure, prepare, frameB, normsB, coeffMinus,
       Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Matrix.trace, Matrix.diag, Matrix.add_apply, Matrix.sub_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.one_apply, Pi.star_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_succ',
      Matrix.of_apply, map_div₀, map_mul, map_neg, map_ofNat, map_one, map_zero,
      Complex.conj_I] <;>
    norm_num [Complex.ext_iff, map_ofNat] <;> ring_nf <;> simp <;> norm_num <;> ring

private lemma prepare_pos (f : Fin 6 → Fin 2 → ℂ) (neg : Bool) (j : Fin 8) :
    (prepare f neg j).PosSemidef := by
  cases neg <;> fin_cases j <;>
    change (Matrix.vecMulVec _ (star _)).PosSemidef <;>
    exact Matrix.posSemidef_vecMulVec_self_star _
private lemma measure_pos (f : Fin 6 → Fin 2 → ℂ) (n : Fin 3 → ℂ) (c : Fin 4 → ℂ)
    (hc : ∀ i : Fin 3, 0 ≤ c i.castSucc / (n i)^2) (hr : 0 ≤ c 3 / 2) (j : Fin 8) :
    (measure f n c j).PosSemidef := by
  fin_cases j
  all_goals first
    | exact (Matrix.posSemidef_vecMulVec_self_star _).smul (hc 0)
    | exact (Matrix.posSemidef_vecMulVec_self_star _).smul (hc 1)
    | exact (Matrix.posSemidef_vecMulVec_self_star _).smul (hc 2)
    | exact Matrix.PosSemidef.one.smul hr

private lemma measures_A_pos (c : Fin 4 → ℂ)
    (hc : c = coeffBase ∨ c = coeffPlus ∨ c = coeffMinus) (j : Fin 8) :
    (measure (fun i : Fin 6 => D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2)) normsA c j).PosSemidef := by
  apply measure_pos
  · intro i
    rcases hc with rfl | rfl | rfl <;> fin_cases i <;>
      norm_num [coeffBase, coeffPlus, coeffMinus, normsA, map_ofNat,
        Matrix.cons_val_two, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Complex.le_def]
  · rcases hc with rfl | rfl | rfl <;>
      norm_num [coeffBase, coeffPlus, coeffMinus, map_ofNat,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Complex.le_def]
private lemma measures_B_pos (c : Fin 4 → ℂ)
    (hc : c = coeffBase ∨ c = coeffPlus ∨ c = coeffMinus) (j : Fin 8) :
    (measure frameB normsB c j).PosSemidef := by
  apply measure_pos
  · intro i
    rcases hc with rfl | rfl | rfl <;> fin_cases i <;>
      norm_num [coeffBase, coeffPlus, coeffMinus, normsB, map_ofNat,
        Matrix.cons_val_two, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Complex.le_def]
  · rcases hc with rfl | rfl | rfl <;>
      norm_num [coeffBase, coeffPlus, coeffMinus, map_ofNat,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Complex.le_def]

private lemma eb_base_A : IsEB (MatrixMap.of_kraus A A) := by
  apply D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.prepare_eb
  exact ⟨8, measure (fun i : Fin 6 => D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2)) normsA coeffBase, prepare (fun i : Fin 6 => D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2)) false,
    (fun j => ⟨measures_A_pos coeffBase (by simp) j,
      prepare_pos (fun i : Fin 6 => D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2)) false j⟩), base_A_prepare⟩

private lemma eb_base_B : IsEB (MatrixMap.of_kraus B B) := by
  apply D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.prepare_eb
  exact ⟨8, measure frameB normsB coeffBase, prepare frameB false,
    (fun j => ⟨measures_B_pos coeffBase (by simp) j,
      prepare_pos frameB false j⟩), base_B_prepare⟩

private lemma eb_plus_A : IsEB (switchPlus A) := by
  apply D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.prepare_eb
  exact ⟨8, measure (fun i : Fin 6 => D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2)) normsA coeffPlus, prepare (fun i : Fin 6 => D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2)) false,
    (fun j => ⟨measures_A_pos coeffPlus (by exact Or.inr (Or.inl rfl)) j,
      prepare_pos (fun i : Fin 6 => D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2)) false j⟩), plus_A_prepare⟩

private lemma eb_plus_B : IsEB (switchPlus B) := by
  apply D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.prepare_eb
  exact ⟨8, measure frameB normsB coeffPlus, prepare frameB false,
    (fun j => ⟨measures_B_pos coeffPlus (by exact Or.inr (Or.inl rfl)) j,
      prepare_pos frameB false j⟩), plus_B_prepare⟩

private lemma eb_minus_A : IsEB (switchMinus A) := by
  apply D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.prepare_eb
  exact ⟨8, measure (fun i : Fin 6 => D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2)) normsA coeffMinus, prepare (fun i : Fin 6 => D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2)) true,
    (fun j => ⟨measures_A_pos coeffMinus (by exact Or.inr (Or.inr rfl)) j,
      prepare_pos (fun i : Fin 6 => D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation.octVec (i + 2)) true j⟩), minus_A_prepare⟩

private lemma eb_minus_B : IsEB (switchMinus B) := by
  apply D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.prepare_eb
  exact ⟨8, measure frameB normsB coeffMinus, prepare frameB true,
    (fun j => ⟨measures_B_pos coeffMinus (by exact Or.inr (Or.inr rfl)) j,
      prepare_pos frameB true j⟩), minus_B_prepare⟩

private lemma useless_A : CompletelyUseless A := ⟨eb_base_A, eb_plus_A, eb_minus_A⟩
private lemma useless_B : CompletelyUseless B := ⟨eb_base_B, eb_plus_B, eb_minus_B⟩
private lemma sep_pt_psd {m r : ℕ} {X : Matrix (Fin m × Fin r) (Fin m × Fin r) ℂ}
    (hX : X ∈ SEP ℂ m r) : (ptFirst X).PosSemidef := by
  obtain ⟨k, x, y, rfl⟩ := hX
  have he : ptFirst (∑ j, Matrix.kroneckerMap (· * ·)
        (Matrix.vecMulVec (x j) (star (x j))) (Matrix.vecMulVec (y j) (star (y j)))) =
      ∑ j, Matrix.kroneckerMap (· * ·)
        (Matrix.vecMulVec (x j) (star (x j)))ᵀ (Matrix.vecMulVec (y j) (star (y j))) := by
    ext a b
    simp only [ptFirst, Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  rw [he]
  apply Matrix.posSemidef_sum
  intro j _
  exact (Matrix.posSemidef_vecMulVec_self_star (x j)).transpose.kronecker
    (Matrix.posSemidef_vecMulVec_self_star (y j))

private lemma notEB_of_witness (Phi : MatrixMap (Fin 2) (Fin 2) ℂ)
    (w : Fin 2 × Fin 2 → ℂ)
    (hv : star w ⬝ᵥ (ptFirst Phi.choi_matrix *ᵥ w) = (-2185891/39062500 : ℂ)) :
    ¬ IsEB Phi := by
  intro h
  have hs := h 2
    (Matrix.vecMulVec (fun a : Fin 2 × Fin 2 => if a.1 = a.2 then (1 : ℂ) else 0)
      (star (fun a : Fin 2 × Fin 2 => if a.1 = a.2 then (1 : ℂ) else 0)))
    (Matrix.posSemidef_vecMulVec_self_star _)
  change MatrixMap.kron Phi (MatrixMap.id (Fin 2) ℂ)
    (Matrix.vecMulVec (fun a : Fin 2 × Fin 2 => if a.1 = a.2 then (1 : ℂ) else 0)
      (fun a => star (if a.1 = a.2 then (1 : ℂ) else 0))) ∈ SEP ℂ 2 2 at hs
  rw [← MatrixMap.choi_matrix_eq_map_proj] at hs
  have hp := (sep_pt_psd hs).dotProduct_mulVec_nonneg w
  rw [hv] at hp
  norm_num [Complex.le_def] at hp
private def wG : Fin 2 × Fin 2 → GaussianInt := fun a => !![-2,-1;-1,2] a.1 a.2
private def minusK (p q : Fin 4 × Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • (composeKraus B A p * composeKraus B A q -
    composeKraus B A q * composeKraus B A p)
private def qval (K : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  star (fun a => (wG a : ℂ)) ⬝ᵥ (ptFirst (vecMulVec (fun a : Fin 2 × Fin 2 => K a.1 a.2)
    (star (fun a : Fin 2 × Fin 2 => K a.1 a.2))) *ᵥ (fun a => (wG a : ℂ)))
private lemma witness_sum :
    star (fun a => (wG a : ℂ)) ⬝ᵥ (ptFirst ((switchMinus (composeKraus B A)).choi_matrix) *ᵥ (fun a => (wG a : ℂ))) =
      ∑ p, ∑ q, qval (minusK p q) := by
  unfold switchMinus
  rw [MatrixMap.choi_of_kraus]
  have hs {α : Type} [Fintype α]
      (M : α → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
      ptFirst (∑ a, M a) = ∑ a, ptFirst (M a) := by
    ext a b
    simp only [ptFirst, Matrix.sum_apply]
  rw [hs, Matrix.sum_mulVec, dotProduct_sum, Fintype.sum_prod_type]
  rfl


private def compositeG (p : Fin 4 × Fin 4) : Matrix (Fin 2) (Fin 2) GaussianInt :=
  match p.1.val, p.2.val with
  | 0, 0 => !![(⟨245, 0⟩ : GaussianInt),(⟨0, 0⟩ : GaussianInt);(⟨0, 0⟩ : GaussianInt),(⟨245, 0⟩ : GaussianInt)]
  | 0, 1 => !![(⟨-28, 0⟩ : GaussianInt),(⟨21, 0⟩ : GaussianInt);(⟨21, 0⟩ : GaussianInt),(⟨28, 0⟩ : GaussianInt)]
  | 0, 2 => !![(⟨0, 0⟩ : GaussianInt),(⟨0, -35⟩ : GaussianInt);(⟨0, 35⟩ : GaussianInt),(⟨0, 0⟩ : GaussianInt)]
  | 0, 3 => !![(⟨147, 0⟩ : GaussianInt),(⟨196, 0⟩ : GaussianInt);(⟨196, 0⟩ : GaussianInt),(⟨-147, 0⟩ : GaussianInt)]
  | 1, 0 => !![(⟨0, 0⟩ : GaussianInt),(⟨35, 0⟩ : GaussianInt);(⟨35, 0⟩ : GaussianInt),(⟨0, 0⟩ : GaussianInt)]
  | 1, 1 => !![(⟨3, 0⟩ : GaussianInt),(⟨-4, 0⟩ : GaussianInt);(⟨4, 0⟩ : GaussianInt),(⟨3, 0⟩ : GaussianInt)]
  | 1, 2 => !![(⟨0, -5⟩ : GaussianInt),(⟨0, 0⟩ : GaussianInt);(⟨0, 0⟩ : GaussianInt),(⟨0, 5⟩ : GaussianInt)]
  | 1, 3 => !![(⟨28, 0⟩ : GaussianInt),(⟨21, 0⟩ : GaussianInt);(⟨-21, 0⟩ : GaussianInt),(⟨28, 0⟩ : GaussianInt)]
  | 2, 0 => !![(⟨0, 0⟩ : GaussianInt),(⟨0, -35⟩ : GaussianInt);(⟨0, 35⟩ : GaussianInt),(⟨0, 0⟩ : GaussianInt)]
  | 2, 1 => !![(⟨0, 3⟩ : GaussianInt),(⟨0, 4⟩ : GaussianInt);(⟨0, 4⟩ : GaussianInt),(⟨0, -3⟩ : GaussianInt)]
  | 2, 2 => !![(⟨5, 0⟩ : GaussianInt),(⟨0, 0⟩ : GaussianInt);(⟨0, 0⟩ : GaussianInt),(⟨5, 0⟩ : GaussianInt)]
  | 2, 3 => !![(⟨0, 28⟩ : GaussianInt),(⟨0, -21⟩ : GaussianInt);(⟨0, -21⟩ : GaussianInt),(⟨0, -28⟩ : GaussianInt)]
  | 3, 0 => !![(⟨245, 0⟩ : GaussianInt),(⟨0, 0⟩ : GaussianInt);(⟨0, 0⟩ : GaussianInt),(⟨-245, 0⟩ : GaussianInt)]
  | 3, 1 => !![(⟨-28, 0⟩ : GaussianInt),(⟨-21, 0⟩ : GaussianInt);(⟨21, 0⟩ : GaussianInt),(⟨-28, 0⟩ : GaussianInt)]
  | 3, 2 => !![(⟨0, 0⟩ : GaussianInt),(⟨0, 35⟩ : GaussianInt);(⟨0, 35⟩ : GaussianInt),(⟨0, 0⟩ : GaussianInt)]
  | 3, 3 => !![(⟨147, 0⟩ : GaussianInt),(⟨-196, 0⟩ : GaussianInt);(⟨196, 0⟩ : GaussianInt),(⟨147, 0⟩ : GaussianInt)]
  | _, _ => 0

private lemma compositeG_eq (p : Fin 4 × Fin 4) :
    composeKraus B A p = (1/500 : ℂ) • (compositeG p).map GaussianInt.toComplex := by
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [composeKraus, A, B, weight, sigmaTable, tiltedTable, compositeG,
      GaussianInt.toComplex_def, Matrix.mul_apply, Matrix.map_apply,
      Matrix.smul_apply, Fin.sum_univ_succ, Complex.ext_iff, map_ofNat]
private def minusG (p q : Fin 4 × Fin 4) : Matrix (Fin 2) (Fin 2) GaussianInt :=
  compositeG p * compositeG q - compositeG q * compositeG p
private lemma minusG_eq (p q : Fin 4 × Fin 4) :
    minusK p q = (1/500000 : ℂ) • (minusG p q).map GaussianInt.toComplex := by
  unfold minusK
  rw [compositeG_eq p, compositeG_eq q]
  ext a b
  simp only [minusG, Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.mul_apply, smul_eq_mul, map_sub, map_sum, map_add, map_mul, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  ring

private def qG (K : Matrix (Fin 2) (Fin 2) GaussianInt) : GaussianInt :=
  ∑ a : Fin 2 × Fin 2, ∑ b : Fin 2 × Fin 2,
    star (wG a) * (K b.1 a.2 * star (K a.1 b.2)) * wG b
private lemma qval_mapG (K : Matrix (Fin 2) (Fin 2) GaussianInt) :
    qval (K.map GaussianInt.toComplex) = ((qG K : GaussianInt) : ℂ) := by
  simp [qval, qG, ptFirst, dotProduct, Matrix.mulVec, Matrix.map_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, map_sum, map_mul,
    GaussianInt.toComplex_star, mul_assoc, Finset.mul_sum]
private lemma qval_smul (c : ℂ) (K : Matrix (Fin 2) (Fin 2) ℂ) :
    qval (c • K) = c * star c * qval K := by
  simp only [qval, ptFirst, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply,
    Pi.star_apply, Matrix.smul_apply, smul_eq_mul, map_mul, star_mul,
    Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.sum_univ_zero]
  ring
private lemma totalG : ∑ p : Fin 4 × Fin 4, ∑ q : Fin 4 × Fin 4,
    qG (minusG p q) = (-13989702400 : GaussianInt) := by
  decide
private lemma totalG_complex : ∑ p : Fin 4 × Fin 4, ∑ q : Fin 4 × Fin 4,
    ((qG (minusG p q) : GaussianInt) : ℂ) = (-13989702400 : ℂ) := by
  simp_rw [← map_sum]
  rw [totalG]
  norm_num [GaussianInt.toComplex_def]
private lemma witness_value :
    star (fun a => (wG a : ℂ)) ⬝ᵥ (ptFirst ((switchMinus (composeKraus B A)).choi_matrix) *ᵥ (fun a => (wG a : ℂ))) =
      (-2185891 / 39062500 : ℂ) := by
  rw [witness_sum]
  simp_rw [minusG_eq, qval_smul, qval_mapG]
  simp only [← Finset.mul_sum]
  rw [totalG_complex]
  norm_num [map_ofNat]

theorem result : ¬ claim := by
  intro h
  have hc := h (Fin 4) (Fin 4) A B channel_A channel_B useless_A useless_B
  exact (notEB_of_witness _ (fun a => (wG a : ℂ)) witness_value) hc.2.2

end D5.S3.QuantumChannels.SwitchUselessConcatenationRefutation
