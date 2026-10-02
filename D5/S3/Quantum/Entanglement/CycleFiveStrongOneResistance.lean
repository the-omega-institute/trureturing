/- GID: D5/S3/Quantum/Entanglement/CycleFiveStrongOneResistance
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/CycleFiveStrongOneResistance
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The five-cycle graph state is strongly 1-resistant. -/
/-
proof_shape: result: content
escape_witness: form (2): exact graph-basis Gram decompositions of all oriented
  partial-transpose witnesses, the cut-product trace reindexing establishing
  nonnegative expectation on biseparable mixtures, and explicit Pauli-product
  decompositions of every two-qubit-loss marginal, on the live path of result.
admission_basis: open-problem-resolution (#11551; Proved)
Direct frozen dependencies:
  D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.IsStrongResistant
  statement_id: sha256:652539ae14c83cea38d31f6001cf88fa7c874591bdf5a9fc87184264bb6f53ea
  D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.IsGME
  statement_id: sha256:3aecc9a6c9c3071ef9bc867eb7146c6b6da2b949fc77e770c8bfbc902f221c18
  D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.IsBiseparable
  statement_id: sha256:856898119021743b7a433ef7c807b0bbc1bcba63a6c8dc09c4add29ded9e5c66
  D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.IsFullySeparable
  statement_id: sha256:77cad917d81d04680e631a40172d6e0891432871af6bb5b2d0fe8c309d2fa739
  D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.partialTrace
  statement_id: sha256:7fe960e0659d09a74ae584594d2d6e40d7a1065dec77a37a848cb9bb2e59b0b7
  D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.joinBits
  statement_id: sha256:9105c314396c5e642ad966a7b6520756c047f814bbe847d0eef0d39f29a07e06
  D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation.cycleGraphState
  statement_id: sha256:bb7cc3a76eb4eddfec4b3618917175a262faa0076965b927bd1e0870b623437b
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
  statement_id: sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
-/
import D5.S3.Quantum.Entanglement.CycleSixStrongTwoResistanceRefutation
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace D5.S3.Quantum.Entanglement.CycleFiveStrongOneResistance
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Entanglement.CycleSixStrongTwoResistanceRefutation
open scoped BigOperators ComplexOrder MatrixOrder
def claim : Prop := IsStrongResistant 1 (cycleGraphState 5)
variable {V : Type} [Fintype V] [DecidableEq V]
private def transposePart (A : Finset V) (W : Matrix (V → Bool) (V → Bool) ℂ) :
    Matrix (V → Bool) (V → Bool) ℂ :=
  fun x y => W (A.piecewise y x) (A.piecewise x y)
private def pairing (W ρ : Matrix (V → Bool) (V → Bool) ℂ) : ℂ :=
  ∑ x, ∑ y, W x y * ρ y x
namespace Numeric
open scoped BigOperators
private def coefNode0 (s : Nat) : Int := if s.testBit 4 then 2 else (-2)
private def coefNode1 (s : Nat) : Int := if s.testBit 3 then 2 else coefNode0 s
private def coefNode2 (s : Nat) : Int := if s.testBit 2 then 2 else coefNode1 s
private def coefNode3 (s : Nat) : Int := if s.testBit 1 then 2 else coefNode2 s
private def coefNode4 (s : Nat) : Int := if s.testBit 0 then 2 else coefNode3 s
private def coefNode5 (s : Nat) : Int := if s.testBit 3 then 2 else 0
private def coefNode6 (s : Nat) : Int := if s.testBit 2 then 2 else coefNode5 s
private def coefNode7 (s : Nat) : Int := if s.testBit 1 then 2 else coefNode6 s
private def coefNode8 (s : Nat) : Int := if s.testBit 4 then 4 else 0
private def coefNode9 (s : Nat) : Int := if s.testBit 3 then coefNode8 s else 2
private def coefNode10 (s : Nat) : Int := if s.testBit 2 then 2 else coefNode9 s
private def coefNode11 (s : Nat) : Int := if s.testBit 1 then 2 else coefNode10 s
private def coefNode12 (s : Nat) : Int := if s.testBit 0 then coefNode11 s else coefNode7 s
private def coefNode13 (A s : Nat) : Int := if A.testBit 4 then coefNode12 s else coefNode4 s
private def coefNode14 (s : Nat) : Int := if s.testBit 4 then 2 else 0
private def coefNode15 (s : Nat) : Int := if s.testBit 4 then 0 else 2
private def coefNode16 (s : Nat) : Int := if s.testBit 4 then 4 else 2
private def coefNode17 (s : Nat) : Int := if s.testBit 3 then coefNode16 s else coefNode15 s
private def coefNode18 (s : Nat) : Int := if s.testBit 2 then coefNode17 s else coefNode14 s
private def coefNode19 (s : Nat) : Int := if s.testBit 1 then 2 else coefNode18 s
private def coefNode20 (s : Nat) : Int := if s.testBit 0 then 2 else coefNode19 s
private def coefNode21 (s : Nat) : Int := if s.testBit 3 then 3 else 1
private def coefNode22 (s : Nat) : Int := if s.testBit 2 then coefNode21 s else 1
private def coefNode23 (s : Nat) : Int := if s.testBit 1 then 2 else coefNode22 s
private def coefNode24 (s : Nat) : Int := if s.testBit 4 then 3 else 1
private def coefNode25 (s : Nat) : Int := if s.testBit 4 then 1 else 3
private def coefNode26 (s : Nat) : Int := if s.testBit 3 then coefNode25 s else coefNode24 s
private def coefNode27 (s : Nat) : Int := if s.testBit 2 then coefNode26 s else coefNode24 s
private def coefNode28 (s : Nat) : Int := if s.testBit 1 then 2 else coefNode27 s
private def coefNode29 (s : Nat) : Int := if s.testBit 0 then coefNode28 s else coefNode23 s
private def coefNode30 (A s : Nat) : Int := if A.testBit 4 then coefNode29 s else coefNode20 s
private def coefNode31 (A s : Nat) : Int := if A.testBit 3 then coefNode30 A s else coefNode13 A s
private def coefNode32 (s : Nat) : Int := if s.testBit 3 then 2 else coefNode14 s
private def coefNode33 (s : Nat) : Int := if s.testBit 3 then coefNode14 s else 2
private def coefNode34 (s : Nat) : Int := if s.testBit 4 then 2 else 4
private def coefNode35 (s : Nat) : Int := if s.testBit 3 then coefNode34 s else 2
private def coefNode36 (s : Nat) : Int := if s.testBit 2 then coefNode35 s else coefNode33 s
private def coefNode37 (s : Nat) : Int := if s.testBit 1 then coefNode36 s else coefNode32 s
private def coefNode38 (s : Nat) : Int := if s.testBit 0 then 2 else coefNode37 s
private def coefNode39 (s : Nat) : Int := if s.testBit 3 then 2 else 1
private def coefNode40 (s : Nat) : Int := if s.testBit 3 then 1 else 2
private def coefNode41 (s : Nat) : Int := if s.testBit 3 then 3 else 2
private def coefNode42 (s : Nat) : Int := if s.testBit 2 then coefNode41 s else coefNode40 s
private def coefNode43 (s : Nat) : Int := if s.testBit 1 then coefNode42 s else coefNode39 s
private def coefNode44 (s : Nat) : Int := if s.testBit 3 then coefNode24 s else 2
private def coefNode45 (s : Nat) : Int := if s.testBit 3 then 2 else coefNode24 s
private def coefNode46 (s : Nat) : Int := if s.testBit 3 then 2 else coefNode25 s
private def coefNode47 (s : Nat) : Int := if s.testBit 2 then coefNode46 s else coefNode45 s
private def coefNode48 (s : Nat) : Int := if s.testBit 1 then coefNode47 s else coefNode44 s
private def coefNode49 (s : Nat) : Int := if s.testBit 0 then coefNode48 s else coefNode43 s
private def coefNode50 (A s : Nat) : Int := if A.testBit 4 then coefNode49 s else coefNode38 s
private def coefNode51 (s : Nat) : Int := if s.testBit 3 then coefNode24 s else 1
private def coefNode52 (s : Nat) : Int := if s.testBit 3 then coefNode25 s else 3
private def coefNode53 (s : Nat) : Int := if s.testBit 2 then coefNode52 s else coefNode51 s
private def coefNode54 (s : Nat) : Int := if s.testBit 1 then coefNode53 s else coefNode51 s
private def coefNode55 (s : Nat) : Int := if s.testBit 0 then 2 else coefNode54 s
private def coefNode56 (s : Nat) : Int := if s.testBit 3 then 2 else 3
private def coefNode57 (s : Nat) : Int := if s.testBit 2 then coefNode56 s else coefNode39 s
private def coefNode58 (s : Nat) : Int := if s.testBit 1 then coefNode57 s else coefNode39 s
private def coefNode59 (s : Nat) : Int := if s.testBit 1 then coefNode47 s else coefNode45 s
private def coefNode60 (s : Nat) : Int := if s.testBit 0 then coefNode59 s else coefNode58 s
private def coefNode61 (A s : Nat) : Int := if A.testBit 4 then coefNode60 s else coefNode55 s
private def coefNode62 (A s : Nat) : Int := if A.testBit 3 then coefNode61 A s else coefNode50 A s
private def coefNode63 (A s : Nat) : Int := if A.testBit 2 then coefNode62 A s else coefNode31 A s
private def coefNode64 (s : Nat) : Int := if s.testBit 2 then 2 else coefNode32 s
private def coefNode65 (s : Nat) : Int := if s.testBit 2 then coefNode32 s else 2
private def coefNode66 (s : Nat) : Int := if s.testBit 3 then 2 else coefNode34 s
private def coefNode67 (s : Nat) : Int := if s.testBit 2 then coefNode66 s else 2
private def coefNode68 (s : Nat) : Int := if s.testBit 1 then coefNode67 s else coefNode65 s
private def coefNode69 (s : Nat) : Int := if s.testBit 0 then coefNode68 s else coefNode64 s
private def coefNode70 (s : Nat) : Int := if s.testBit 2 then coefNode44 s else coefNode39 s
private def coefNode71 (s : Nat) : Int := if s.testBit 3 then coefNode25 s else 2
private def coefNode72 (s : Nat) : Int := if s.testBit 2 then coefNode71 s else coefNode39 s
private def coefNode73 (s : Nat) : Int := if s.testBit 1 then coefNode72 s else coefNode70 s
private def coefNode74 (s : Nat) : Int := if s.testBit 2 then coefNode39 s else coefNode44 s
private def coefNode75 (s : Nat) : Int := if s.testBit 2 then coefNode56 s else coefNode44 s
private def coefNode76 (s : Nat) : Int := if s.testBit 1 then coefNode75 s else coefNode74 s
private def coefNode77 (s : Nat) : Int := if s.testBit 0 then coefNode76 s else coefNode73 s
private def coefNode78 (A s : Nat) : Int := if A.testBit 4 then coefNode77 s else coefNode69 s
private def coefNode79 (s : Nat) : Int := if s.testBit 4 then 2 else 1
private def coefNode80 (s : Nat) : Int := if s.testBit 4 then 1 else 2
private def coefNode81 (s : Nat) : Int := if s.testBit 4 then 3 else 2
private def coefNode82 (s : Nat) : Int := if s.testBit 3 then coefNode81 s else coefNode80 s
private def coefNode83 (s : Nat) : Int := if s.testBit 2 then coefNode82 s else coefNode79 s
private def coefNode84 (s : Nat) : Int := if s.testBit 2 then coefNode79 s else coefNode82 s
private def coefNode85 (s : Nat) : Int := if s.testBit 3 then coefNode80 s else coefNode81 s
private def coefNode86 (s : Nat) : Int := if s.testBit 4 then 2 else 3
private def coefNode87 (s : Nat) : Int := if s.testBit 2 then coefNode86 s else coefNode85 s
private def coefNode88 (s : Nat) : Int := if s.testBit 1 then coefNode87 s else coefNode84 s
private def coefNode89 (s : Nat) : Int := if s.testBit 0 then coefNode88 s else coefNode83 s
private def coefNode90 (s : Nat) : Int := if s.testBit 3 then coefNode80 s else coefNode79 s
private def coefNode91 (s : Nat) : Int := if s.testBit 3 then coefNode81 s else coefNode79 s
private def coefNode92 (s : Nat) : Int := if s.testBit 2 then coefNode91 s else coefNode90 s
private def coefNode93 (s : Nat) : Int := if s.testBit 3 then coefNode79 s else coefNode80 s
private def coefNode94 (s : Nat) : Int := if s.testBit 3 then coefNode86 s else coefNode80 s
private def coefNode95 (s : Nat) : Int := if s.testBit 2 then coefNode94 s else coefNode93 s
private def coefNode96 (s : Nat) : Int := if s.testBit 1 then coefNode95 s else coefNode92 s
private def coefNode97 (s : Nat) : Int := if s.testBit 2 then coefNode90 s else coefNode91 s
private def coefNode98 (s : Nat) : Int := if s.testBit 3 then coefNode79 s else coefNode81 s
private def coefNode99 (s : Nat) : Int := if s.testBit 3 then coefNode86 s else coefNode81 s
private def coefNode100 (s : Nat) : Int := if s.testBit 2 then coefNode99 s else coefNode98 s
private def coefNode101 (s : Nat) : Int := if s.testBit 1 then coefNode100 s else coefNode97 s
private def coefNode102 (s : Nat) : Int := if s.testBit 0 then coefNode101 s else coefNode96 s
private def coefNode103 (A s : Nat) : Int := if A.testBit 4 then coefNode102 s else coefNode89 s
private def coefNode104 (A s : Nat) : Int := if A.testBit 3 then coefNode103 A s else coefNode78 A s
private def coefNode105 (s : Nat) : Int := if s.testBit 3 then coefNode86 s else coefNode79 s
private def coefNode106 (s : Nat) : Int := if s.testBit 2 then coefNode105 s else coefNode79 s
private def coefNode107 (s : Nat) : Int := if s.testBit 3 then coefNode79 s else coefNode86 s
private def coefNode108 (s : Nat) : Int := if s.testBit 2 then coefNode107 s else coefNode86 s
private def coefNode109 (s : Nat) : Int := if s.testBit 1 then coefNode108 s else coefNode106 s
private def coefNode110 (s : Nat) : Int := if s.testBit 0 then coefNode109 s else coefNode106 s
private def coefNode111 (s : Nat) : Int := if s.testBit 2 then coefNode105 s else coefNode80 s
private def coefNode112 (s : Nat) : Int := if s.testBit 1 then coefNode111 s else coefNode83 s
private def coefNode113 (s : Nat) : Int := if s.testBit 2 then coefNode107 s else coefNode81 s
private def coefNode114 (s : Nat) : Int := if s.testBit 1 then coefNode113 s else coefNode83 s
private def coefNode115 (s : Nat) : Int := if s.testBit 0 then coefNode114 s else coefNode112 s
private def coefNode116 (A s : Nat) : Int := if A.testBit 4 then coefNode115 s else coefNode110 s
private def coefNode117 (s : Nat) : Int := if s.testBit 2 then 2 else coefNode51 s
private def coefNode118 (s : Nat) : Int := if s.testBit 2 then 2 else coefNode52 s
private def coefNode119 (s : Nat) : Int := if s.testBit 1 then coefNode118 s else coefNode117 s
private def coefNode120 (s : Nat) : Int := if s.testBit 0 then coefNode119 s else coefNode117 s
private def coefNode121 (s : Nat) : Int := if s.testBit 3 then 2 else coefNode15 s
private def coefNode122 (s : Nat) : Int := if s.testBit 2 then 2 else coefNode121 s
private def coefNode123 (s : Nat) : Int := if s.testBit 1 then coefNode122 s else coefNode64 s
private def coefNode124 (s : Nat) : Int := if s.testBit 3 then 2 else coefNode16 s
private def coefNode125 (s : Nat) : Int := if s.testBit 2 then 2 else coefNode124 s
private def coefNode126 (s : Nat) : Int := if s.testBit 1 then coefNode125 s else coefNode64 s
private def coefNode127 (s : Nat) : Int := if s.testBit 0 then coefNode126 s else coefNode123 s
private def coefNode128 (A s : Nat) : Int := if A.testBit 4 then coefNode127 s else coefNode120 s
private def coefNode129 (A s : Nat) : Int := if A.testBit 3 then coefNode128 A s else coefNode116 A s
private def coefNode130 (A s : Nat) : Int := if A.testBit 2 then coefNode129 A s else coefNode104 A s
private def coefNode131 (A s : Nat) : Int := if A.testBit 1 then coefNode130 A s else coefNode63 A s
private def coefNode132 (A s : Nat) : Int := if A.testBit 4 then coefNode120 s else coefNode127 s
private def coefNode133 (A s : Nat) : Int := if A.testBit 4 then coefNode110 s else coefNode115 s
private def coefNode134 (A s : Nat) : Int := if A.testBit 3 then coefNode133 A s else coefNode132 A s
private def coefNode135 (A s : Nat) : Int := if A.testBit 4 then coefNode89 s else coefNode102 s
private def coefNode136 (A s : Nat) : Int := if A.testBit 4 then coefNode69 s else coefNode77 s
private def coefNode137 (A s : Nat) : Int := if A.testBit 3 then coefNode136 A s else coefNode135 A s
private def coefNode138 (A s : Nat) : Int := if A.testBit 2 then coefNode137 A s else coefNode134 A s
private def coefNode139 (A s : Nat) : Int := if A.testBit 4 then coefNode55 s else coefNode60 s
private def coefNode140 (A s : Nat) : Int := if A.testBit 4 then coefNode38 s else coefNode49 s
private def coefNode141 (A s : Nat) : Int := if A.testBit 3 then coefNode140 A s else coefNode139 A s
private def coefNode142 (A s : Nat) : Int := if A.testBit 4 then coefNode20 s else coefNode29 s
private def coefNode143 (A s : Nat) : Int := if A.testBit 4 then coefNode4 s else coefNode12 s
private def coefNode144 (A s : Nat) : Int := if A.testBit 3 then coefNode143 A s else coefNode142 A s
private def coefNode145 (A s : Nat) : Int := if A.testBit 2 then coefNode144 A s else coefNode141 A s
private def coefNode146 (A s : Nat) : Int := if A.testBit 1 then coefNode145 A s else coefNode138 A s
private def coefNode147 (A s : Nat) : Int := if A.testBit 0 then coefNode146 A s else coefNode131 A s
private def coefNode148 (s : Nat) : Int := if s.testBit 4 then 1 else (-1)
private def coefNode149 (s : Nat) : Int := if s.testBit 3 then 1 else coefNode148 s
private def coefNode150 (s : Nat) : Int := if s.testBit 2 then 1 else coefNode149 s
private def coefNode151 (s : Nat) : Int := if s.testBit 4 then (-1) else 1
private def coefNode152 (s : Nat) : Int := if s.testBit 3 then 1 else coefNode151 s
private def coefNode153 (s : Nat) : Int := if s.testBit 2 then 1 else coefNode152 s
private def coefNode154 (s : Nat) : Int := if s.testBit 1 then coefNode153 s else coefNode150 s
private def coefNode155 (s : Nat) : Int := if s.testBit 0 then 0 else coefNode154 s
private def coefNode156 (s : Nat) : Int := if s.testBit 3 then coefNode14 s else 0
private def coefNode157 (s : Nat) : Int := if s.testBit 2 then 1 else coefNode156 s
private def coefNode158 (s : Nat) : Int := if s.testBit 3 then coefNode15 s else 0
private def coefNode159 (s : Nat) : Int := if s.testBit 2 then 1 else coefNode158 s
private def coefNode160 (s : Nat) : Int := if s.testBit 1 then coefNode159 s else coefNode157 s
private def coefNode161 (s : Nat) : Int := if s.testBit 0 then 0 else coefNode160 s
private def coefNode162 (A s : Nat) : Int := if A.testBit 4 then coefNode161 s else coefNode155 s
private def coefNode163 (s : Nat) : Int := if s.testBit 4 then 1 else 0
private def coefNode164 (s : Nat) : Int := if s.testBit 4 then 0 else 1
private def coefNode165 (s : Nat) : Int := if s.testBit 3 then coefNode79 s else coefNode164 s
private def coefNode166 (s : Nat) : Int := if s.testBit 2 then coefNode165 s else coefNode163 s
private def coefNode167 (s : Nat) : Int := if s.testBit 3 then coefNode80 s else coefNode163 s
private def coefNode168 (s : Nat) : Int := if s.testBit 2 then coefNode167 s else coefNode164 s
private def coefNode169 (s : Nat) : Int := if s.testBit 1 then coefNode168 s else coefNode166 s
private def coefNode170 (s : Nat) : Int := if s.testBit 0 then 0 else coefNode169 s
private def coefNode171 (s : Nat) : Int := if s.testBit 2 then coefNode167 s else coefNode163 s
private def coefNode172 (s : Nat) : Int := if s.testBit 2 then coefNode165 s else coefNode164 s
private def coefNode173 (s : Nat) : Int := if s.testBit 1 then coefNode172 s else coefNode171 s
private def coefNode174 (s : Nat) : Int := if s.testBit 0 then 0 else coefNode173 s
private def coefNode175 (A s : Nat) : Int := if A.testBit 4 then coefNode174 s else coefNode170 s
private def coefNode176 (A s : Nat) : Int := if A.testBit 3 then coefNode175 A s else coefNode162 A s
private def coefNode177 (s : Nat) : Int := if s.testBit 3 then coefNode164 s else coefNode163 s
private def coefNode178 (s : Nat) : Int := if s.testBit 3 then coefNode79 s else coefNode163 s
private def coefNode179 (s : Nat) : Int := if s.testBit 2 then coefNode178 s else coefNode177 s
private def coefNode180 (s : Nat) : Int := if s.testBit 3 then coefNode163 s else coefNode164 s
private def coefNode181 (s : Nat) : Int := if s.testBit 3 then coefNode80 s else coefNode164 s
private def coefNode182 (s : Nat) : Int := if s.testBit 2 then coefNode181 s else coefNode180 s
private def coefNode183 (s : Nat) : Int := if s.testBit 1 then coefNode182 s else coefNode179 s
private def coefNode184 (s : Nat) : Int := if s.testBit 0 then 0 else coefNode183 s
private def coefNode185 (s : Nat) : Int := if s.testBit 2 then coefNode178 s else coefNode180 s
private def coefNode186 (s : Nat) : Int := if s.testBit 2 then coefNode181 s else coefNode177 s
private def coefNode187 (s : Nat) : Int := if s.testBit 1 then coefNode186 s else coefNode185 s
private def coefNode188 (s : Nat) : Int := if s.testBit 0 then 0 else coefNode187 s
private def coefNode189 (A s : Nat) : Int := if A.testBit 4 then coefNode188 s else coefNode184 s
private def coefNode190 (s : Nat) : Int := if s.testBit 3 then 1 else 0
private def coefNode191 (s : Nat) : Int := if s.testBit 3 then coefNode14 s else 1
private def coefNode192 (s : Nat) : Int := if s.testBit 2 then coefNode191 s else coefNode190 s
private def coefNode193 (s : Nat) : Int := if s.testBit 3 then coefNode15 s else 1
private def coefNode194 (s : Nat) : Int := if s.testBit 2 then coefNode193 s else coefNode190 s
private def coefNode195 (s : Nat) : Int := if s.testBit 1 then coefNode194 s else coefNode192 s
private def coefNode196 (s : Nat) : Int := if s.testBit 0 then 0 else coefNode195 s
private def coefNode197 (s : Nat) : Int := if s.testBit 3 then 1 else coefNode14 s
private def coefNode198 (s : Nat) : Int := if s.testBit 2 then coefNode197 s else coefNode190 s
private def coefNode199 (s : Nat) : Int := if s.testBit 3 then 1 else coefNode15 s
private def coefNode200 (s : Nat) : Int := if s.testBit 2 then coefNode199 s else coefNode190 s
private def coefNode201 (s : Nat) : Int := if s.testBit 1 then coefNode200 s else coefNode198 s
private def coefNode202 (s : Nat) : Int := if s.testBit 0 then 0 else coefNode201 s
private def coefNode203 (A s : Nat) : Int := if A.testBit 4 then coefNode202 s else coefNode196 s
private def coefNode204 (A s : Nat) : Int := if A.testBit 3 then coefNode203 A s else coefNode189 A s
private def coefNode205 (A s : Nat) : Int := if A.testBit 2 then coefNode204 A s else coefNode176 A s
private def coefNode206 (A s : Nat) : Int := if A.testBit 4 then coefNode196 s else coefNode202 s
private def coefNode207 (A s : Nat) : Int := if A.testBit 4 then coefNode184 s else coefNode188 s
private def coefNode208 (A s : Nat) : Int := if A.testBit 3 then coefNode207 A s else coefNode206 A s
private def coefNode209 (A s : Nat) : Int := if A.testBit 4 then coefNode170 s else coefNode174 s
private def coefNode210 (A s : Nat) : Int := if A.testBit 4 then coefNode155 s else coefNode161 s
private def coefNode211 (A s : Nat) : Int := if A.testBit 3 then coefNode210 A s else coefNode209 A s
private def coefNode212 (A s : Nat) : Int := if A.testBit 2 then coefNode211 A s else coefNode208 A s
private def coefNode213 (A s : Nat) : Int := if A.testBit 1 then coefNode212 A s else coefNode205 A s
private def coefNode214 (s : Nat) : Int := if s.testBit 1 then 0 else coefNode150 s
private def coefNode215 (s : Nat) : Int := if s.testBit 2 then coefNode149 s else 1
private def coefNode216 (s : Nat) : Int := if s.testBit 1 then 0 else coefNode215 s
private def coefNode217 (s : Nat) : Int := if s.testBit 0 then coefNode216 s else coefNode214 s
private def coefNode218 (s : Nat) : Int := if s.testBit 1 then 0 else coefNode192 s
private def coefNode219 (s : Nat) : Int := if s.testBit 2 then coefNode190 s else coefNode191 s
private def coefNode220 (s : Nat) : Int := if s.testBit 1 then 0 else coefNode219 s
private def coefNode221 (s : Nat) : Int := if s.testBit 0 then coefNode220 s else coefNode218 s
private def coefNode222 (A s : Nat) : Int := if A.testBit 4 then coefNode221 s else coefNode217 s
private def coefNode223 (s : Nat) : Int := if s.testBit 1 then 0 else coefNode166 s
private def coefNode224 (s : Nat) : Int := if s.testBit 2 then coefNode163 s else coefNode165 s
private def coefNode225 (s : Nat) : Int := if s.testBit 1 then 0 else coefNode224 s
private def coefNode226 (s : Nat) : Int := if s.testBit 0 then coefNode225 s else coefNode223 s
private def coefNode227 (s : Nat) : Int := if s.testBit 1 then 0 else coefNode179 s
private def coefNode228 (s : Nat) : Int := if s.testBit 2 then coefNode177 s else coefNode178 s
private def coefNode229 (s : Nat) : Int := if s.testBit 1 then 0 else coefNode228 s
private def coefNode230 (s : Nat) : Int := if s.testBit 0 then coefNode229 s else coefNode227 s
private def coefNode231 (A s : Nat) : Int := if A.testBit 4 then coefNode230 s else coefNode226 s
private def coefNode232 (A s : Nat) : Int := if A.testBit 3 then coefNode231 A s else coefNode222 A s
private def coefNode233 (s : Nat) : Int := if s.testBit 1 then 0 else coefNode171 s
private def coefNode234 (s : Nat) : Int := if s.testBit 2 then coefNode163 s else coefNode167 s
private def coefNode235 (s : Nat) : Int := if s.testBit 1 then 0 else coefNode234 s
private def coefNode236 (s : Nat) : Int := if s.testBit 0 then coefNode235 s else coefNode233 s
private def coefNode237 (s : Nat) : Int := if s.testBit 1 then 0 else coefNode185 s
private def coefNode238 (s : Nat) : Int := if s.testBit 2 then coefNode180 s else coefNode178 s
private def coefNode239 (s : Nat) : Int := if s.testBit 1 then 0 else coefNode238 s
private def coefNode240 (s : Nat) : Int := if s.testBit 0 then coefNode239 s else coefNode237 s
private def coefNode241 (A s : Nat) : Int := if A.testBit 4 then coefNode240 s else coefNode236 s
private def coefNode242 (s : Nat) : Int := if s.testBit 1 then 0 else coefNode157 s
private def coefNode243 (s : Nat) : Int := if s.testBit 2 then coefNode156 s else 1
private def coefNode244 (s : Nat) : Int := if s.testBit 1 then 0 else coefNode243 s
private def coefNode245 (s : Nat) : Int := if s.testBit 0 then coefNode244 s else coefNode242 s
private def coefNode246 (s : Nat) : Int := if s.testBit 1 then 0 else coefNode198 s
private def coefNode247 (s : Nat) : Int := if s.testBit 2 then coefNode190 s else coefNode197 s
private def coefNode248 (s : Nat) : Int := if s.testBit 1 then 0 else coefNode247 s
private def coefNode249 (s : Nat) : Int := if s.testBit 0 then coefNode248 s else coefNode246 s
private def coefNode250 (A s : Nat) : Int := if A.testBit 4 then coefNode249 s else coefNode245 s
private def coefNode251 (A s : Nat) : Int := if A.testBit 3 then coefNode250 A s else coefNode241 A s
private def coefNode252 (A s : Nat) : Int := if A.testBit 2 then coefNode251 A s else coefNode232 A s
private def coefNode253 (A s : Nat) : Int := if A.testBit 4 then coefNode245 s else coefNode249 s
private def coefNode254 (A s : Nat) : Int := if A.testBit 4 then coefNode236 s else coefNode240 s
private def coefNode255 (A s : Nat) : Int := if A.testBit 3 then coefNode254 A s else coefNode253 A s
private def coefNode256 (A s : Nat) : Int := if A.testBit 4 then coefNode226 s else coefNode230 s
private def coefNode257 (A s : Nat) : Int := if A.testBit 4 then coefNode217 s else coefNode221 s
private def coefNode258 (A s : Nat) : Int := if A.testBit 3 then coefNode257 A s else coefNode256 A s
private def coefNode259 (A s : Nat) : Int := if A.testBit 2 then coefNode258 A s else coefNode255 A s
private def coefNode260 (A s : Nat) : Int := if A.testBit 0 then coefNode259 A s else coefNode252 A s
private def coefNode261 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode149 s
private def coefNode262 (s : Nat) : Int := if s.testBit 3 then coefNode148 s else 1
private def coefNode263 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode262 s
private def coefNode264 (s : Nat) : Int := if s.testBit 1 then coefNode263 s else coefNode261 s
private def coefNode265 (s : Nat) : Int := if s.testBit 2 then 0 else 1
private def coefNode266 (s : Nat) : Int := if s.testBit 0 then coefNode265 s else coefNode264 s
private def coefNode267 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode190 s
private def coefNode268 (s : Nat) : Int := if s.testBit 3 then 0 else 1
private def coefNode269 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode268 s
private def coefNode270 (s : Nat) : Int := if s.testBit 1 then coefNode269 s else coefNode267 s
private def coefNode271 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode191 s
private def coefNode272 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode197 s
private def coefNode273 (s : Nat) : Int := if s.testBit 1 then coefNode272 s else coefNode271 s
private def coefNode274 (s : Nat) : Int := if s.testBit 0 then coefNode273 s else coefNode270 s
private def coefNode275 (A s : Nat) : Int := if A.testBit 4 then coefNode274 s else coefNode266 s
private def coefNode276 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode156 s
private def coefNode277 (s : Nat) : Int := if s.testBit 3 then 0 else coefNode14 s
private def coefNode278 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode277 s
private def coefNode279 (s : Nat) : Int := if s.testBit 1 then coefNode278 s else coefNode276 s
private def coefNode280 (s : Nat) : Int := if s.testBit 0 then coefNode265 s else coefNode279 s
private def coefNode281 (s : Nat) : Int := if s.testBit 1 then coefNode271 s else coefNode272 s
private def coefNode282 (s : Nat) : Int := if s.testBit 0 then coefNode281 s else coefNode270 s
private def coefNode283 (A s : Nat) : Int := if A.testBit 4 then coefNode282 s else coefNode280 s
private def coefNode284 (A s : Nat) : Int := if A.testBit 3 then coefNode283 A s else coefNode275 A s
private def coefNode285 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode163 s
private def coefNode286 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode167 s
private def coefNode287 (s : Nat) : Int := if s.testBit 3 then coefNode163 s else coefNode80 s
private def coefNode288 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode287 s
private def coefNode289 (s : Nat) : Int := if s.testBit 1 then coefNode288 s else coefNode286 s
private def coefNode290 (s : Nat) : Int := if s.testBit 0 then coefNode289 s else coefNode285 s
private def coefNode291 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode180 s
private def coefNode292 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode177 s
private def coefNode293 (s : Nat) : Int := if s.testBit 1 then coefNode292 s else coefNode291 s
private def coefNode294 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode178 s
private def coefNode295 (s : Nat) : Int := if s.testBit 3 then coefNode163 s else coefNode79 s
private def coefNode296 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode295 s
private def coefNode297 (s : Nat) : Int := if s.testBit 1 then coefNode296 s else coefNode294 s
private def coefNode298 (s : Nat) : Int := if s.testBit 0 then coefNode297 s else coefNode293 s
private def coefNode299 (A s : Nat) : Int := if A.testBit 4 then coefNode298 s else coefNode290 s
private def coefNode300 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode165 s
private def coefNode301 (s : Nat) : Int := if s.testBit 3 then coefNode164 s else coefNode79 s
private def coefNode302 (s : Nat) : Int := if s.testBit 2 then 0 else coefNode301 s
private def coefNode303 (s : Nat) : Int := if s.testBit 1 then coefNode302 s else coefNode300 s
private def coefNode304 (s : Nat) : Int := if s.testBit 0 then coefNode303 s else coefNode285 s
private def coefNode305 (s : Nat) : Int := if s.testBit 1 then coefNode291 s else coefNode292 s
private def coefNode306 (s : Nat) : Int := if s.testBit 0 then coefNode297 s else coefNode305 s
private def coefNode307 (A s : Nat) : Int := if A.testBit 4 then coefNode306 s else coefNode304 s
private def coefNode308 (A s : Nat) : Int := if A.testBit 3 then coefNode307 A s else coefNode299 A s
private def coefNode309 (A s : Nat) : Int := if A.testBit 1 then coefNode308 A s else coefNode284 A s
private def coefNode310 (A s : Nat) : Int := if A.testBit 4 then coefNode304 s else coefNode306 s
private def coefNode311 (A s : Nat) : Int := if A.testBit 4 then coefNode290 s else coefNode298 s
private def coefNode312 (A s : Nat) : Int := if A.testBit 3 then coefNode311 A s else coefNode310 A s
private def coefNode313 (A s : Nat) : Int := if A.testBit 4 then coefNode280 s else coefNode282 s
private def coefNode314 (A s : Nat) : Int := if A.testBit 4 then coefNode266 s else coefNode274 s
private def coefNode315 (A s : Nat) : Int := if A.testBit 3 then coefNode314 A s else coefNode313 A s
private def coefNode316 (A s : Nat) : Int := if A.testBit 1 then coefNode315 A s else coefNode312 A s
private def coefNode317 (A s : Nat) : Int := if A.testBit 0 then coefNode316 A s else coefNode309 A s
private def coefNode318 (s : Nat) : Int := if s.testBit 3 then 0 else coefNode148 s
private def coefNode319 (s : Nat) : Int := if s.testBit 3 then 0 else coefNode151 s
private def coefNode320 (s : Nat) : Int := if s.testBit 2 then coefNode319 s else coefNode318 s
private def coefNode321 (s : Nat) : Int := if s.testBit 1 then coefNode268 s else coefNode320 s
private def coefNode322 (s : Nat) : Int := if s.testBit 0 then coefNode268 s else coefNode321 s
private def coefNode323 (s : Nat) : Int := if s.testBit 1 then coefNode268 s else 0
private def coefNode324 (s : Nat) : Int := if s.testBit 3 then 0 else coefNode15 s
private def coefNode325 (s : Nat) : Int := if s.testBit 2 then coefNode324 s else coefNode277 s
private def coefNode326 (s : Nat) : Int := if s.testBit 1 then coefNode268 s else coefNode325 s
private def coefNode327 (s : Nat) : Int := if s.testBit 0 then coefNode326 s else coefNode323 s
private def coefNode328 (A s : Nat) : Int := if A.testBit 4 then coefNode327 s else coefNode322 s
private def coefNode329 (s : Nat) : Int := if s.testBit 1 then coefNode325 s else 0
private def coefNode330 (s : Nat) : Int := if s.testBit 0 then coefNode268 s else coefNode329 s
private def coefNode331 (s : Nat) : Int := if s.testBit 1 then coefNode325 s else coefNode268 s
private def coefNode332 (s : Nat) : Int := if s.testBit 0 then coefNode331 s else coefNode323 s
private def coefNode333 (A s : Nat) : Int := if A.testBit 4 then coefNode332 s else coefNode330 s
private def coefNode334 (A s : Nat) : Int := if A.testBit 2 then coefNode333 A s else coefNode328 A s
private def coefNode335 (s : Nat) : Int := if s.testBit 3 then 0 else coefNode163 s
private def coefNode336 (s : Nat) : Int := if s.testBit 3 then 0 else coefNode164 s
private def coefNode337 (s : Nat) : Int := if s.testBit 2 then coefNode336 s else coefNode335 s
private def coefNode338 (s : Nat) : Int := if s.testBit 2 then coefNode335 s else coefNode336 s
private def coefNode339 (s : Nat) : Int := if s.testBit 3 then 0 else coefNode79 s
private def coefNode340 (s : Nat) : Int := if s.testBit 3 then 0 else coefNode80 s
private def coefNode341 (s : Nat) : Int := if s.testBit 2 then coefNode340 s else coefNode339 s
private def coefNode342 (s : Nat) : Int := if s.testBit 1 then coefNode341 s else coefNode338 s
private def coefNode343 (s : Nat) : Int := if s.testBit 0 then coefNode342 s else coefNode337 s
private def coefNode344 (s : Nat) : Int := if s.testBit 1 then coefNode337 s else coefNode338 s
private def coefNode345 (s : Nat) : Int := if s.testBit 1 then coefNode341 s else coefNode337 s
private def coefNode346 (s : Nat) : Int := if s.testBit 0 then coefNode345 s else coefNode344 s
private def coefNode347 (A s : Nat) : Int := if A.testBit 4 then coefNode346 s else coefNode343 s
private def coefNode348 (s : Nat) : Int := if s.testBit 2 then coefNode339 s else coefNode340 s
private def coefNode349 (s : Nat) : Int := if s.testBit 1 then coefNode348 s else coefNode337 s
private def coefNode350 (s : Nat) : Int := if s.testBit 0 then coefNode349 s else coefNode337 s
private def coefNode351 (s : Nat) : Int := if s.testBit 1 then coefNode338 s else coefNode337 s
private def coefNode352 (s : Nat) : Int := if s.testBit 0 then coefNode345 s else coefNode351 s
private def coefNode353 (A s : Nat) : Int := if A.testBit 4 then coefNode352 s else coefNode350 s
private def coefNode354 (A s : Nat) : Int := if A.testBit 2 then coefNode353 A s else coefNode347 A s
private def coefNode364 (s : Nat) : Int := if s.testBit 4 then 0 else (-1)
private def coefNode371 (s : Nat) : Int := if s.testBit 0 then (if s.testBit 1 then coefNode164 s else (if s.testBit 2 then coefNode164 s else (if s.testBit 3 then coefNode364 s else coefNode164 s))) else (if s.testBit 1 then coefNode164 s else (if s.testBit 2 then coefNode164 s else (if s.testBit 3 then coefNode164 s else coefNode364 s)))
private def coefNode376 (s : Nat) : Int := if s.testBit 0 then (if s.testBit 1 then coefNode164 s else (if s.testBit 2 then coefNode324 s else 0)) else (if s.testBit 1 then coefNode164 s else (if s.testBit 2 then coefNode158 s else 0))
private def coefNode378 (s : Nat) : Int := if s.testBit 3 then coefNode164 s else 0
private def coefNode379 (s : Nat) : Int := if s.testBit 3 then coefNode15 s else coefNode164 s
private def coefNode380 (s : Nat) : Int := if s.testBit 2 then coefNode379 s else coefNode336 s
private def coefNode382 (s : Nat) : Int := if s.testBit 3 then coefNode164 s else coefNode15 s
private def coefNode383 (s : Nat) : Int := if s.testBit 2 then coefNode382 s else coefNode378 s
private def coefNode385 (s : Nat) : Int := if s.testBit 0 then (if s.testBit 1 then coefNode383 s else coefNode336 s) else (if s.testBit 1 then coefNode380 s else coefNode378 s)
private def coefNode388 (s : Nat) : Int := if s.testBit 0 then (if s.testBit 1 then coefNode380 s else coefNode336 s) else (if s.testBit 1 then coefNode383 s else coefNode378 s)
private def coefNode391 (s : Nat) : Int := if s.testBit 2 then coefNode336 s else coefNode378 s
private def coefNode392 (s : Nat) : Int := if s.testBit 2 then coefNode379 s else coefNode378 s
private def coefNode394 (s : Nat) : Int := if s.testBit 2 then coefNode378 s else coefNode336 s
private def coefNode395 (s : Nat) : Int := if s.testBit 2 then coefNode382 s else coefNode336 s
private def coefNode397 (s : Nat) : Int := if s.testBit 0 then (if s.testBit 1 then coefNode395 s else coefNode394 s) else (if s.testBit 1 then coefNode392 s else coefNode391 s)
private def coefNode400 (s : Nat) : Int := if s.testBit 0 then (if s.testBit 1 then coefNode395 s else coefNode391 s) else (if s.testBit 1 then coefNode392 s else coefNode394 s)
private def coefNode402 (s : Nat) : Int := if s.testBit 2 then coefNode164 s else 0
private def coefNode407 (s : Nat) : Int := if s.testBit 0 then (if s.testBit 1 then (if s.testBit 2 then coefNode324 s else coefNode164 s) else coefNode402 s) else (if s.testBit 1 then (if s.testBit 2 then coefNode158 s else coefNode164 s) else coefNode402 s)
private def coefNode412 (s : Nat) : Int := if s.testBit 0 then (if s.testBit 1 then (if s.testBit 2 then coefNode164 s else coefNode324 s) else coefNode402 s) else (if s.testBit 1 then (if s.testBit 2 then coefNode164 s else coefNode158 s) else coefNode402 s)
private def lossMask (l : Fin 6) : Nat := if l.val = 0 then 0 else 2 ^ (l.val - 1)
private def cnum (l : Fin 6) (A s : Nat) : Int :=
  match l.val with
  | 0 => coefNode147 A s
  | 1 => coefNode213 A s
  | 2 => coefNode260 A s
  | 3 => coefNode317 A s
  | 4 => (if A.testBit 0 then (if A.testBit 1 then (if A.testBit 2 then (if A.testBit 4 then coefNode322 s else coefNode327 s) else (if A.testBit 4 then coefNode330 s else coefNode332 s)) else (if A.testBit 2 then (if A.testBit 4 then coefNode343 s else coefNode346 s) else (if A.testBit 4 then coefNode350 s else coefNode352 s))) else (if A.testBit 1 then coefNode354 A s else coefNode334 A s))
  | _ => (if A.testBit 0 then (if A.testBit 1 then (if A.testBit 2 then (if A.testBit 3 then coefNode371 s else coefNode376 s) else (if A.testBit 3 then coefNode385 s else coefNode388 s)) else (if A.testBit 2 then (if A.testBit 3 then coefNode397 s else coefNode400 s) else (if A.testBit 3 then coefNode407 s else coefNode412 s))) else (if A.testBit 1 then (if A.testBit 2 then (if A.testBit 3 then coefNode412 s else coefNode407 s) else (if A.testBit 3 then coefNode400 s else coefNode397 s)) else (if A.testBit 2 then (if A.testBit 3 then coefNode388 s else coefNode385 s) else (if A.testBit 3 then coefNode376 s else coefNode371 s))))
private def phase (x : Nat) : Int :=
  if ((x.testBit 0 && x.testBit 1) ^^ (x.testBit 1 && x.testBit 2) ^^
      (x.testBit 2 && x.testBit 3) ^^ (x.testBit 3 && x.testBit 4) ^^ (x.testBit 4 && x.testBit 0)) then -1 else 1
private def character (s x : Nat) : Int :=
  (if s.testBit 0 && x.testBit 0 then -1 else 1) * (if s.testBit 1 && x.testBit 1 then -1 else 1) *
  (if s.testBit 2 && x.testBit 2 then -1 else 1) * (if s.testBit 3 && x.testBit 3 then -1 else 1) *
  (if s.testBit 4 && x.testBit 4 then -1 else 1)
private def bnum (s x : Nat) : Int := phase x * character s x
private def rhoNum (l : Fin 6) (x y : Nat) : Int :=
  phase x * phase y + if l.val = 0 then 0 else
    phase (Nat.lor x (lossMask l)) * phase (Nat.lor y (lossMask l))
private def sp (A x y : Nat) : Nat := Nat.lor (Nat.land A x) (Nat.land (31 - A) y)
private def allowedCut (l : Fin 6) (A : Fin 32) : Prop :=
  Nat.land (lossMask l) A.val = 0 ∧ A.val ≠ 0 ∧ Nat.lor (lossMask l) A.val ≠ 31
private instance decision1 (l : Fin 6) (A : Fin 32) : Decidable (allowedCut l A) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
private def allowedState (l : Fin 6) (x : Fin 32) : Prop := Nat.land (lossMask l) x.val = 0
private instance decision2 (l : Fin 6) (x : Fin 32) : Decidable (allowedState l x) := inferInstanceAs (Decidable (_ = _))
private def scale (l : Fin 6) : Int := if l.val = 0 then 128 else 32
private def factor (l : Fin 6) : Int := if l.val = 0 then 4 else 2
private def qnum (l : Fin 6) (A x y : Nat) : Int :=
  (if x = y then scale l / 2 else 0) - factor l * rhoNum l (sp A y x) (sp A x y)
end Numeric
private def lossSet (l : Fin 6) : Finset (Fin 5) :=
  if h : l.val = 0 then ∅ else {⟨l.val - 1, by omega⟩}
private abbrev Retained (l : Fin 6) := {v : Fin 5 // v ∉ lossSet l}
private def code (l : Fin 6) (x : Retained l → Bool) : Nat :=
  ∑ v, 2 ^ v.val.val * (x v).toNat
private def cutCode (l : Fin 6) (A : Finset (Retained l)) : Nat :=
  ∑ v ∈ A, 2 ^ v.val.val
private def phaseConfig (x : Fin 5 → Bool) : Int :=
  (-1) ^ (∑ i : Fin 5, (x i).toNat * (x ⟨(i.val+1)%5, by omega⟩).toNat)
private def wnum (l : Fin 6) (x y : Nat) : Int :=
  (if x = y then Numeric.scale l / 2 else 0) - Numeric.factor l * Numeric.rhoNum l x y
private def densityFamily (l : Fin 6) : Matrix (Retained l → Bool) (Retained l → Bool) ℂ :=
  partialTrace (Matrix.vecMulVec (cycleGraphState 5) (star (cycleGraphState 5))) (lossSet l)
private def witness (l : Fin 6) : Matrix (Retained l → Bool) (Retained l → Bool) ℂ :=
  fun x y => (wnum l (code l x) (code l y) : ℂ) / (Numeric.scale l : ℂ)
private def fullCode (x : Fin 5 → Bool) : Nat := ∑ v, 2 ^ v.val * (x v).toNat
private def fullCutCode (A : Finset (Fin 5)) : Nat := ∑ v ∈ A, 2 ^ v.val
private def pauliVector (a : Fin 3) (e x : Bool) : ℂ :=
  if a.val = 2 then if x = e then 1 else 0
  else if x then (if e then -1 else 1) * (if a.val = 1 then Complex.I else 1)
  else 1
private def pauliState (a : Fin 3) (e : Bool) : DensityState Bool :=
  ⟨CStarMatrix.ofMatrix ((if a.val = 2 then (1 : ℝ) else 1/2) •
    Matrix.vecMulVec (pauliVector a e) (star (pauliVector a e))),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((Matrix.posSemidef_vecMulVec_self_star (pauliVector a e)).smul (by split <;> norm_num)).nonneg,
    by
      change Matrix.trace ((if a.val = 2 then (1 : ℝ) else 1/2) •
        Matrix.vecMulVec (pauliVector a e) (star (pauliVector a e))) = 1
      fin_cases a <;> cases e <;>
        norm_num [Matrix.trace, Matrix.diag_apply, Matrix.smul_apply,
          Matrix.vecMulVec_apply, pauliVector, Fintype.sum_bool, Complex.real_smul]
  ⟩
private def pauliNumerator (a : Fin 3) (e x y : Bool) : GaussianInt :=
  if a.val = 2 then if x = e ∧ y = e then 2 else 0
  else if x = y then 1
  else if a.val = 0 then if e then -1 else 1
  else if x then (if e then -1 else 1) * (⟨0,1⟩ : GaussianInt)
  else (if e then 1 else -1) * (⟨0,1⟩ : GaussianInt)
private def sepMask (J : Finset (Fin 5)) : Nat := ∑ v ∈ J, 2 ^ v.val
private abbrev SepRetained (J : Finset (Fin 5)) := {v : Fin 5 // v ∉ J}
private def localAxis (J : Finset (Fin 5)) (v : SepRetained J) : Fin 3 :=
  match sepMask J with
  | 3 => if v.val.val = 2 then 2 else if v.val.val = 3 then 0 else 2
  | 5 => if v.val.val = 1 then 0 else if v.val.val = 3 then 1 else 1
  | 9 => if v.val.val = 1 then 1 else if v.val.val = 2 then 1 else 0
  | 17 => if v.val.val = 1 then 2 else if v.val.val = 2 then 0 else 2
  | 6 => if v.val.val = 0 then 2 else if v.val.val = 3 then 2 else 0
  | 10 => if v.val.val = 0 then 1 else if v.val.val = 2 then 0 else 1
  | 18 => if v.val.val = 0 then 0 else if v.val.val = 2 then 1 else 1
  | 12 => if v.val.val = 0 then 0 else if v.val.val = 1 then 2 else 2
  | 20 => if v.val.val = 0 then 1 else if v.val.val = 1 then 1 else 0
  | 24 => if v.val.val = 0 then 2 else if v.val.val = 1 then 0 else 2
  | _ => 0
private def localRank (J : Finset (Fin 5)) (v : SepRetained J) : Nat :=
  (Finset.univ.filter (fun u : SepRetained J => u.val.val < v.val.val)).card
private def localEigen (J : Finset (Fin 5)) (e : Fin 8) (v : SepRetained J) : Bool :=
  e.val.testBit (localRank J v)
private def evenEigen (e : Fin 8) : Prop := e.val = 0 ∨ e.val = 3 ∨ e.val = 5 ∨ e.val = 6
private instance decision3 (e : Fin 8) : Decidable (evenEigen e) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
open Numeric
/-- The five-cycle graph state is strongly 1-resistant. -/
theorem result : claim := by
  have product_witness_nonneg {V : Type} [Fintype V] [DecidableEq V] (W : Matrix (V → Bool) (V → Bool) ℂ)
      (A : Finset V) (σ : DensityState (A → Bool))
      (τ : DensityState (↥(Aᶜ) → Bool))
      (hW : (transposePart A W).PosSemidef) :
      0 ≤ pairing W (fun x y =>
        σ.val (fun v => x v.val) (fun v => y v.val) *
        τ.val (fun v => x v.val) (fun v => y v.val)) := by
    classical
    let e : ((V → Bool) × (V → Bool)) ≃ ((V → Bool) × (V → Bool)) :=
      { toFun := fun p => (A.piecewise p.2 p.1, A.piecewise p.1 p.2)
        invFun := fun p => (A.piecewise p.2 p.1, A.piecewise p.1 p.2)
        left_inv := by intro p; ext v <;> simp [Finset.piecewise] <;> split <;> simp_all
        right_inv := by intro p; ext v <;> simp [Finset.piecewise] <;> split <;> simp_all }
    have hσ : (CStarMatrix.ofMatrix.symm σ.val).PosSemidef := by
      exact Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.property.1)
    have hτ : (CStarMatrix.ofMatrix.symm τ.val).PosSemidef := by
      exact Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm τ.property.1)
    let K : Matrix (V → Bool) (V → Bool) ℂ := fun x y =>
      σ.val (fun v => y v.val) (fun v => x v.val) *
      τ.val (fun v => x v.val) (fun v => y v.val)
    have hK : K.PosSemidef := by
      exact (hσ.transpose.kronecker hτ).submatrix
        (fun x : V → Bool => (fun v : A => x v.val, fun v : ↥(Aᶜ) => x v.val))
    have heq : pairing W (fun x y =>
        σ.val (fun v => x v.val) (fun v => y v.val) *
        τ.val (fun v => x v.val) (fun v => y v.val)) =
        Matrix.trace (transposePart A W * K) := by
      unfold pairing
      change (∑ x, ∑ y, W x y *
        (σ.val (fun v => y v.val) (fun v => x v.val) *
         τ.val (fun v => y v.val) (fun v => x v.val))) = _
      let f : ((V → Bool) × (V → Bool)) → ℂ := fun p => W p.1 p.2 *
        (σ.val (fun v => p.2 v.val) (fun v => p.1 v.val) *
         τ.val (fun v => p.2 v.val) (fun v => p.1 v.val))
      change (∑ x, ∑ y, f (x,y)) = _
      rw [← Fintype.sum_prod_type f, ← e.sum_comp f]
      dsimp only [f]
      simp only [e, Equiv.coe_fn_mk, transposePart, Matrix.trace, Matrix.diag_apply,
        Matrix.mul_apply, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x hx; apply Finset.sum_congr rfl
      intro y hy
      have ha : ∀ (v : A), A.piecewise x y v.val = x v.val := by
        intro v; simp [Finset.piecewise, v.property]
      have hb : ∀ (v : ↥(Aᶜ)), A.piecewise x y v.val = y v.val := by
        intro v; simp [Finset.piecewise, Finset.mem_compl.mp v.property]
      have ha' : ∀ (v : A), A.piecewise y x v.val = y v.val := by
        intro v; simp [Finset.piecewise, v.property]
      have hb' : ∀ (v : ↥(Aᶜ)), A.piecewise y x v.val = x v.val := by
        intro v; simp [Finset.piecewise, Finset.mem_compl.mp v.property]
      simp [K, ha, hb, ha', hb']
    rw [heq]
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hW.nonneg
    rw [hB, Matrix.star_eq_conjTranspose, Matrix.mul_assoc, Matrix.trace_mul_comm]
    exact (hK.mul_mul_conjTranspose_same B).trace_nonneg
  have witness_gme {V : Type} [Fintype V] [DecidableEq V]
      (W ρ : Matrix (V → Bool) (V → Bool) ℂ)
      (hW : ∀ A : Finset V, A.Nonempty → Aᶜ.Nonempty →
        (transposePart A W).PosSemidef)
      (hρ : (pairing W ρ).re < 0) : IsGME ρ := by
    classical
    rintro ⟨k, p, A, σ, τ, hp, hsum, hA, hdecomp⟩
    have heq : pairing W ρ = ∑ j, (p j : ℂ) * pairing W (fun x y =>
        (σ j).val (fun v => x v.val) (fun v => y v.val) *
        (τ j).val (fun v => x v.val) (fun v => y v.val)) := by
      unfold pairing
      simp_rw [hdecomp, Finset.mul_sum]
      calc
        _ = ∑ x, ∑ j, ∑ y, W x y *
            ((p j : ℂ) * (σ j).val (fun v => y v.val) (fun v => x v.val) *
              (τ j).val (fun v => y v.val) (fun v => x v.val)) := by
          apply Finset.sum_congr rfl
          intro x hx; exact Finset.sum_comm
        _ = ∑ j, ∑ x, ∑ y, W x y *
            ((p j : ℂ) * (σ j).val (fun v => y v.val) (fun v => x v.val) *
              (τ j).val (fun v => y v.val) (fun v => x v.val)) := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj; apply Finset.sum_congr rfl
          intro x hx; apply Finset.sum_congr rfl
          intro y hy; ring
    have hnonneg : 0 ≤ pairing W ρ := by
      rw [heq]
      apply Finset.sum_nonneg
      intro j hj; exact mul_nonneg (by exact_mod_cast hp j)
        (product_witness_nonneg W (A j) (σ j) (τ j) (hW _ (hA j).1 (hA j).2))
    exact (not_lt_of_ge (Complex.nonneg_iff.mp hnonneg).1) hρ
  have hψ : ∀ x y : Fin 5 → Bool,
      Matrix.vecMulVec (cycleGraphState 5) (star (cycleGraphState 5)) x y =
      ((phaseConfig x * phaseConfig y : Int) : ℂ) / 32 := by
    intro x y
    have hsqrt : (Real.sqrt (32 : ℝ) : ℂ) * (Real.sqrt (32 : ℝ) : ℂ) = 32 := by
      norm_cast
      norm_num [Real.mul_self_sqrt]
    simp only [Matrix.vecMulVec_apply, Pi.star_apply, cycleGraphState,
      star_div₀, star_pow, star_neg, star_one, Complex.star_def, Complex.conj_ofReal]
    norm_num only [show (2 ^ 5 : ℝ) = 32 by norm_num]
    rw [div_mul_div_comm, hsqrt]
    simp only [phaseConfig, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  have spectral_certificates :
      (∀ (l : Fin 6) (A : Fin 32), allowedCut l A → ∀ s : Fin 32, 0 ≤ cnum l A.val s.val) ∧
      (∀ (l : Fin 6) (A : Fin 32), allowedCut l A → ∀ (x y : Fin 32),
        allowedState l x → allowedState l y →
        qnum l A.val x.val y.val = ∑ s : Fin 32, cnum l A.val s.val * bnum s.val x.val * bnum s.val y.val) := by
    constructor
    · intro l A
      fin_cases l <;> fin_cases A <;> decide +kernel
    · have hrow : ∀ (l : Fin 6) (A : Fin 32), allowedCut l A → ∀ (d : Fin 32), allowedState l d →
          qnum l A.val 0 d.val = ∑ s : Fin 32, cnum l A.val s.val * bnum s.val 0 * bnum s.val d.val := by
        intro l A
        fin_cases l <;> fin_cases A <;> decide +kernel
      have hbound : ∀ (x y : Fin 32), Nat.xor x.val y.val < 32 := by decide +kernel
      have hsupport : ∀ (l : Fin 6) (x y : Fin 32), allowedState l x → allowedState l y →
          Nat.land (lossMask l) (Nat.xor x.val y.val) = 0 := by decide +kernel
      have hcharacter : ∀ (s x y : Fin 32),
          bnum s.val x.val * bnum s.val y.val =
            (phase x.val * phase y.val * phase (Nat.xor x.val y.val)) *
              bnum s.val 0 * bnum s.val (Nat.xor x.val y.val) := by
        have hsign (a b c : Bool) :
            (if a && b then (-1 : Int) else 1) * (if a && c then -1 else 1) =
              (if a && (b ^^ c) then -1 else 1) := by
          cases a <;> cases b <;> cases c <;> decide +kernel
        have hχ (s x y : Nat) : character s x * character s y = character s (Nat.xor x y) := by
          unfold character
          rw [Nat.xor_eq]
          simp only [Nat.testBit_xor]
          calc
            _ = ((if s.testBit 0 && x.testBit 0 then (-1 : Int) else 1) * (if s.testBit 0 && y.testBit 0 then -1 else 1)) *
                ((if s.testBit 1 && x.testBit 1 then -1 else 1) * (if s.testBit 1 && y.testBit 1 then -1 else 1)) *
                ((if s.testBit 2 && x.testBit 2 then -1 else 1) * (if s.testBit 2 && y.testBit 2 then -1 else 1)) *
                ((if s.testBit 3 && x.testBit 3 then -1 else 1) * (if s.testBit 3 && y.testBit 3 then -1 else 1)) *
                ((if s.testBit 4 && x.testBit 4 then -1 else 1) * (if s.testBit 4 && y.testBit 4 then -1 else 1)) := by ring
            _ = _ := by rw [hsign, hsign, hsign, hsign, hsign]
        intro s x y
        have hzero : phase 0 = 1 := by decide +kernel
        have hχzero : character s.val 0 = 1 := by simp only [character, Nat.zero_testBit, Bool.and_false, Bool.false_eq_true, ↓reduceIte, mul_one]
        have hsq : phase (Nat.xor x.val y.val) * phase (Nat.xor x.val y.val) = 1 := by
          unfold phase; split <;> norm_num
        unfold bnum
        rw [hzero, hχzero, mul_one]
        calc
          _ = (phase x.val * phase y.val) * (character s.val x.val * character s.val y.val) := by ring
          _ = (phase x.val * phase y.val) * character s.val (Nat.xor x.val y.val) := by rw [hχ]
          _ = (phase x.val * phase y.val) * (phase (Nat.xor x.val y.val) * phase (Nat.xor x.val y.val)) * character s.val (Nat.xor x.val y.val) := by rw [hsq]; ring
          _ = _ := by ring
      have htransfer : ∀ (l : Fin 6) (A : Fin 32), allowedCut l A → ∀ (x y : Fin 32),
          allowedState l x → allowedState l y →
          qnum l A.val x.val y.val =
            (phase x.val * phase y.val * phase (Nat.xor x.val y.val)) *
              qnum l A.val 0 (Nat.xor x.val y.val) := by
        intro l A
        fin_cases l <;> fin_cases A <;> decide +kernel
      intro l A hA x y hx hy
      let d : Fin 32 := ⟨Nat.xor x.val y.val, hbound x y⟩
      have hd : allowedState l d := hsupport l x y hx hy
      rw [htransfer l A hA x y hx hy, hrow l A hA d hd, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      have hc := congrArg (fun z : Int => cnum l A.val s.val * z) (hcharacter s x y)
      convert hc.symm using 1 <;> ring
  have gme_family (l : Fin 6) : IsGME (densityFamily l) := by
    have hb : ∀ (l : Fin 6) (x : Retained l → Bool), code l x < 32 := by decide +kernel
    have hAb : ∀ (l : Fin 6) (A : Finset (Retained l)), cutCode l A < 32 := by decide +kernel
    have hstate : ∀ (l : Fin 6) (x : Retained l → Bool),
        Nat.land (Numeric.lossMask l) (code l x) = 0 := by decide +kernel
    have hcut : ∀ (l : Fin 6) (A : Finset (Retained l)), A.Nonempty → Aᶜ.Nonempty →
        Nat.land (Numeric.lossMask l) (cutCode l A) = 0 ∧ cutCode l A ≠ 0 ∧
          Nat.lor (Numeric.lossMask l) (cutCode l A) ≠ 31 := by decide +kernel
    have hbits : ∀ (a b : Fin 32),
        (∀ i : Fin 5, a.val.testBit i.val = b.val.testBit i.val) → a = b := by
      intro a
      fin_cases a <;> decide +kernel
    have hspb : ∀ (a x y : Fin 32), Numeric.sp a.val x.val y.val < 32 := by
      intro a
      fin_cases a <;> decide +kernel
    have hcomplement : ∀ (a : Fin 32) (i : Fin 5),
        (31 - a.val).testBit i.val = !(a.val.testBit i.val) := by decide +kernel
    have hcodebit : ∀ (l : Fin 6) (x : Retained l → Bool) (i : Fin 5),
        (code l x).testBit i.val = if h : i ∉ lossSet l then x ⟨i,h⟩ else false := by decide +kernel
    have hcutbit : ∀ (l : Fin 6) (A : Finset (Retained l)) (i : Fin 5),
        (cutCode l A).testBit i.val = if h : i ∉ lossSet l then decide ((⟨i,h⟩ : Retained l) ∈ A) else false := by decide +kernel
    have hcodeeq : ∀ (l : Fin 6) (x y : Retained l → Bool), code l x = code l y ↔ x = y := by
      intro l
      fin_cases l <;> decide +kernel
    have hsplice : ∀ (l : Fin 6) (A : Finset (Retained l)) (x y : Retained l → Bool),
        code l (A.piecewise x y) = Numeric.sp (cutCode l A) (code l x) (code l y) := by
      intro l A x y
      have hf := hbits ⟨code l (A.piecewise x y), hb l _⟩
        ⟨Numeric.sp (cutCode l A) (code l x) (code l y), hspb ⟨cutCode l A,hAb l A⟩ ⟨code l x,hb l x⟩ ⟨code l y,hb l y⟩⟩
      apply congrArg Fin.val (hf ?_)
      intro i
      change (code l (A.piecewise x y)).testBit i.val =
        (Numeric.sp (cutCode l A) (code l x) (code l y)).testBit i.val
      rw [hcodebit]
      simp only [Numeric.sp, Nat.lor_eq, Nat.land_eq, Nat.testBit_lor, Nat.testBit_land]
      rw [hcomplement ⟨cutCode l A,hAb l A⟩ i]
      simp only [hcutbit, hcodebit]
      by_cases hr : i ∉ lossSet l
      · by_cases ha : (⟨i,hr⟩ : Retained l) ∈ A <;> simp [hr, ha, Finset.piecewise]
      · simp [hr]
    have hq : ∀ (l : Fin 6) (A : Finset (Retained l)) (x y : Retained l → Bool),
        wnum l (code l (A.piecewise y x)) (code l (A.piecewise x y)) =
          Numeric.qnum l (cutCode l A) (code l x) (code l y) := by
      intro l A x y
      have hsame : A.piecewise y x = A.piecewise x y ↔ x = y := by
        constructor
        · intro h; funext v
          have hv := congrFun h v
          by_cases ha : v ∈ A
          · simpa [Finset.piecewise, ha] using hv.symm
          · simpa [Finset.piecewise, ha] using hv
        · rintro rfl; rfl
      have he : (code l (A.piecewise y x) = code l (A.piecewise x y)) ↔ code l x = code l y := by
        rw [hcodeeq, hcodeeq, hsame]
      unfold wnum Numeric.qnum
      simp only [he]
      rw [hsplice, hsplice]
    have hphase : ∀ (l : Fin 6) (x y : Retained l → Bool),
        (∑ z : lossSet l → Bool, phaseConfig (joinBits (lossSet l) z x) *
          phaseConfig (joinBits (lossSet l) z y)) = Numeric.rhoNum l (code l x) (code l y) := by
      intro l
      fin_cases l <;> decide +kernel
    have hnegative : ∀ (l : Fin 6),
        (∑ x : Retained l → Bool, ∑ y : Retained l → Bool,
          wnum l (code l x) (code l y) * Numeric.rhoNum l (code l y) (code l x)) =
          -(Numeric.scale l * 16) := by
      intro l
      fin_cases l <;> decide +kernel
    have hρ : ∀ (l : Fin 6) (x y : Retained l → Bool),
        densityFamily l x y = (Numeric.rhoNum l (code l x) (code l y) : ℂ) / 32 := by
      intro l x y
      change (∑ z : lossSet l → Bool,
        Matrix.vecMulVec (cycleGraphState 5) (star (cycleGraphState 5))
          (joinBits (lossSet l) z x) (joinBits (lossSet l) z y)) = _
      simp_rw [hψ]
      rw [← Finset.sum_div, ← Int.cast_sum, hphase]
    classical
    apply witness_gme (witness l) (densityFamily l)
    · intro A ha hbA
      let a : Fin 32 := ⟨cutCode l A, hAb l A⟩
      have ha' : Numeric.allowedCut l a := hcut l A ha hbA
      have hs : (0 : ℝ) < (Numeric.scale l : ℝ) := by
        by_cases h : l.val = 0 <;> norm_num [Numeric.scale, h]
      have hc : ∀ s : Fin 32, 0 ≤ (Numeric.cnum l a.val s.val : ℝ) := by
        intro s; exact_mod_cast spectral_certificates.1 l a ha' s
      have hGram : transposePart A (witness l) =
          ∑ s : Fin 32, ((Numeric.cnum l a.val s.val : ℝ) / (Numeric.scale l : ℝ)) •
            Matrix.vecMulVec (fun x => (Numeric.bnum s.val (code l x) : ℂ))
              (star (fun x => (Numeric.bnum s.val (code l x) : ℂ))) := by
        ext x y
        change (wnum l (code l (A.piecewise y x)) (code l (A.piecewise x y)) : ℂ) /
          (Numeric.scale l : ℂ) = _
        rw [hq]
        have hi := spectral_certificates.2 l a ha'
          ⟨code l x, hb l x⟩ ⟨code l y, hb l y⟩ (hstate l x) (hstate l y)
        calc
          _ = ((∑ s : Fin 32, Numeric.cnum l a.val s.val *
              Numeric.bnum s.val (code l x) * Numeric.bnum s.val (code l y) : Int) : ℂ) /
              (Numeric.scale l : ℂ) := by rw [hi]
          _ = _ := by
            simp only [Int.cast_sum, Int.cast_mul, Finset.sum_div, Matrix.sum_apply,
              Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
              Complex.real_smul, Complex.ofReal_div, Complex.ofReal_intCast, star_intCast]
            apply Finset.sum_congr rfl
            intro s hs'; ring
      rw [hGram]
      exact Matrix.posSemidef_sum _ (fun s _ =>
        (Matrix.posSemidef_vecMulVec_self_star _).smul (div_nonneg (hc s) hs.le))
    · have he : pairing (witness l) (densityFamily l) = (-1/2 : ℂ) := by
        unfold pairing
        simp_rw [hρ]
        change (∑ x : Retained l → Bool, ∑ y : Retained l → Bool,
          (wnum l (code l x) (code l y) : ℂ) / (Numeric.scale l : ℂ) *
            ((Numeric.rhoNum l (code l y) (code l x) : ℂ) / 32)) = _
        calc
          _ = ((∑ x : Retained l → Bool, ∑ y : Retained l → Bool,
              wnum l (code l x) (code l y) * Numeric.rhoNum l (code l y) (code l x) : Int) : ℂ) /
              ((Numeric.scale l : ℂ) * 32) := by
            simp only [Int.cast_sum, Int.cast_mul, Finset.sum_div]
            apply Finset.sum_congr rfl
            intro x hx; apply Finset.sum_congr rfl
            intro y hy; ring
          _ = _ := by
            rw [hnegative]
            by_cases h : l.val = 0 <;> norm_num [Numeric.scale, h]
      rw [he]
      norm_num
  have initial_gme : IsGME (Matrix.vecMulVec (cycleGraphState 5) (star (cycleGraphState 5))) := by
    have hb : ∀ x : Fin 5 → Bool, fullCode x < 32 := by decide +kernel
    have hAb : ∀ A : Finset (Fin 5), fullCutCode A < 32 := by decide +kernel
    have hstate : ∀ x : Fin 5 → Bool, Nat.land (Numeric.lossMask 0) (fullCode x) = 0 := by decide +kernel
    have hcut : ∀ A : Finset (Fin 5), A.Nonempty → Aᶜ.Nonempty →
        Nat.land (Numeric.lossMask 0) (fullCutCode A) = 0 ∧ fullCutCode A ≠ 0 ∧
          Nat.lor (Numeric.lossMask 0) (fullCutCode A) ≠ 31 := by decide +kernel
    have hbits : ∀ (a b : Fin 32),
        (∀ i : Fin 5, a.val.testBit i.val = b.val.testBit i.val) → a = b := by
      intro a
      fin_cases a <;> decide +kernel
    have hspb : ∀ (a x y : Fin 32), Numeric.sp a.val x.val y.val < 32 := by
      intro a
      fin_cases a <;> decide +kernel
    have hcomplement : ∀ (a : Fin 32) (i : Fin 5),
        (31 - a.val).testBit i.val = !(a.val.testBit i.val) := by decide +kernel
    have hcodebit : ∀ (x : Fin 5 → Bool) (i : Fin 5),
        (fullCode x).testBit i.val = x i := by decide +kernel
    have hcutbit : ∀ (A : Finset (Fin 5)) (i : Fin 5),
        (fullCutCode A).testBit i.val = decide (i ∈ A) := by decide +kernel
    have hcodeeq : ∀ (x y : Fin 5 → Bool), fullCode x = fullCode y ↔ x = y := by decide +kernel
    have hsplice : ∀ (A : Finset (Fin 5)) (x y : Fin 5 → Bool),
        fullCode (A.piecewise x y) = Numeric.sp (fullCutCode A) (fullCode x) (fullCode y) := by
      intro A x y
      have hf := hbits ⟨fullCode (A.piecewise x y), hb _⟩
        ⟨Numeric.sp (fullCutCode A) (fullCode x) (fullCode y), hspb ⟨fullCutCode A,hAb A⟩ ⟨fullCode x,hb x⟩ ⟨fullCode y,hb y⟩⟩
      apply congrArg Fin.val (hf ?_)
      intro i
      change (fullCode (A.piecewise x y)).testBit i.val =
        (Numeric.sp (fullCutCode A) (fullCode x) (fullCode y)).testBit i.val
      rw [hcodebit]
      simp only [Numeric.sp, Nat.lor_eq, Nat.land_eq, Nat.testBit_lor, Nat.testBit_land]
      rw [hcomplement ⟨fullCutCode A,hAb A⟩ i]
      simp only [hcutbit, hcodebit]
      by_cases ha : i ∈ A <;> simp [ha, Finset.piecewise]
    have hq : ∀ (A : Finset (Fin 5)) (x y : Fin 5 → Bool),
        wnum 0 (fullCode (A.piecewise y x)) (fullCode (A.piecewise x y)) =
          Numeric.qnum 0 (fullCutCode A) (fullCode x) (fullCode y) := by
      intro A x y
      have hsame : A.piecewise y x = A.piecewise x y ↔ x = y := by
        constructor
        · intro h; funext v
          have hv := congrFun h v
          by_cases ha : v ∈ A
          · simpa [Finset.piecewise, ha] using hv.symm
          · simpa [Finset.piecewise, ha] using hv
        · rintro rfl; rfl
      have he : (fullCode (A.piecewise y x) = fullCode (A.piecewise x y)) ↔ fullCode x = fullCode y := by
        rw [hcodeeq, hcodeeq, hsame]
      unfold wnum Numeric.qnum
      simp only [he]
      rw [hsplice, hsplice]
    have hnegative : (∑ x : Fin 5 → Bool, ∑ y : Fin 5 → Bool,
          wnum 0 (fullCode x) (fullCode y) * Numeric.rhoNum 0 (fullCode y) (fullCode x)) =
          -(Numeric.scale 0 * 16) := by decide +kernel
    have hphase : ∀ x y : Fin 5 → Bool,
        phaseConfig x * phaseConfig y = Numeric.rhoNum 0 (fullCode x) (fullCode y) := by decide +kernel
    let ρ := Matrix.vecMulVec (cycleGraphState 5) (star (cycleGraphState 5))
    let W : Matrix (Fin 5 → Bool) (Fin 5 → Bool) ℂ :=
      fun x y => (wnum 0 (fullCode x) (fullCode y) : ℂ) / (Numeric.scale 0 : ℂ)
    have hρ : ∀ x y : Fin 5 → Bool, ρ x y = (Numeric.rhoNum 0 (fullCode x) (fullCode y) : ℂ) / 32 := by
      intro x y
      change Matrix.vecMulVec (cycleGraphState 5) (star (cycleGraphState 5)) x y = _
      rw [hψ, hphase]
    classical
    apply witness_gme W ρ
    · intro A ha hbA
      let a : Fin 32 := ⟨fullCutCode A, hAb A⟩
      have ha' : Numeric.allowedCut 0 a := hcut A ha hbA
      have hs : (0 : ℝ) < (Numeric.scale 0 : ℝ) := by
        norm_num [Numeric.scale]
      have hc : ∀ s : Fin 32, 0 ≤ (Numeric.cnum 0 a.val s.val : ℝ) := by
        intro s; exact_mod_cast spectral_certificates.1 0 a ha' s
      have hGram : transposePart A (W) =
          ∑ s : Fin 32, ((Numeric.cnum 0 a.val s.val : ℝ) / (Numeric.scale 0 : ℝ)) •
            Matrix.vecMulVec (fun x => (Numeric.bnum s.val (fullCode x) : ℂ))
              (star (fun x => (Numeric.bnum s.val (fullCode x) : ℂ))) := by
        ext x y
        change (wnum 0 (fullCode (A.piecewise y x)) (fullCode (A.piecewise x y)) : ℂ) /
          (Numeric.scale 0 : ℂ) = _
        rw [hq]
        have hi := spectral_certificates.2 0 a ha'
          ⟨fullCode x, hb x⟩ ⟨fullCode y, hb y⟩ (hstate x) (hstate y)
        calc
          _ = ((∑ s : Fin 32, Numeric.cnum 0 a.val s.val *
              Numeric.bnum s.val (fullCode x) * Numeric.bnum s.val (fullCode y) : Int) : ℂ) /
              (Numeric.scale 0 : ℂ) := by rw [hi]
          _ = _ := by
            simp only [Int.cast_sum, Int.cast_mul, Finset.sum_div, Matrix.sum_apply,
              Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
              Complex.real_smul, Complex.ofReal_div, Complex.ofReal_intCast, star_intCast]
            apply Finset.sum_congr rfl
            intro s hs'; ring
      rw [hGram]
      exact Matrix.posSemidef_sum _ (fun s _ =>
        (Matrix.posSemidef_vecMulVec_self_star _).smul (div_nonneg (hc s) hs.le))
    · have he : pairing W ρ = (-1/2 : ℂ) := by
        unfold pairing
        simp_rw [hρ]
        change (∑ x : Fin 5 → Bool, ∑ y : Fin 5 → Bool,
          (wnum 0 (fullCode x) (fullCode y) : ℂ) / (Numeric.scale 0 : ℂ) *
            ((Numeric.rhoNum 0 (fullCode y) (fullCode x) : ℂ) / 32)) = _
        calc
          _ = ((∑ x : Fin 5 → Bool, ∑ y : Fin 5 → Bool,
              wnum 0 (fullCode x) (fullCode y) * Numeric.rhoNum 0 (fullCode y) (fullCode x) : Int) : ℂ) /
              ((Numeric.scale 0 : ℂ) * 32) := by
            simp only [Int.cast_sum, Int.cast_mul, Finset.sum_div]
            apply Finset.sum_congr rfl
            intro x hx; apply Finset.sum_congr rfl
            intro y hy; ring
          _ = _ := by
            rw [hnegative]
            norm_num [Numeric.scale]
      rw [he]
      norm_num
  have separable_family (J : Finset (Fin 5)) (hJ : J.card = 2) :
      IsFullySeparable (partialTrace (Matrix.vecMulVec (cycleGraphState 5)
        (star (cycleGraphState 5))) J) := by
    have hcertificate : ∀ (J : Finset (Fin 5)), J.card = 2 → ∀ (x y : SepRetained J → Bool),
        ((∑ z : J → Bool, phaseConfig (joinBits J z x) * phaseConfig (joinBits J z y) : Int) : GaussianInt) =
          ∑ e : Fin 8, if evenEigen e then
            ∏ v : SepRetained J, pauliNumerator (localAxis J v) (localEigen J e v) (x v) (y v)
          else 0 := by
      intro J
      fin_cases J <;> decide +kernel
    have hcard : Fintype.card (SepRetained J) = 3 := by
      rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin, hJ]
    have hpauli : ∀ (a : Fin 3) (e x y : Bool),
        (pauliState a e).val x y = (pauliNumerator a e x y : ℂ) / 2 := by
      intro a e x y
      fin_cases a <;> cases e <;> cases x <;> cases y <;>
        norm_num [pauliState, pauliVector, pauliNumerator, CStarMatrix.ofMatrix_apply,
          Matrix.smul_apply, Matrix.vecMulVec_apply, Complex.real_smul,
          GaussianInt.toComplex_def', map_ofNat] <;> ring
    refine ⟨8, (fun e => if evenEigen e then 1/4 else 0),
      (fun e v => pauliState (localAxis J v) (localEigen J e v)), ?_, ?_, ?_⟩
    · intro e; change 0 ≤ if evenEigen e then (1/4 : ℝ) else 0
      by_cases he : evenEigen e <;> simp [he]
    · norm_num [Fin.sum_univ_succ, evenEigen]
    · intro x y
      change (∑ z : J → Bool, Matrix.vecMulVec (cycleGraphState 5) (star (cycleGraphState 5))
        (joinBits J z x) (joinBits J z y)) = _
      simp_rw [hψ, hpauli]
      simp only [← Finset.sum_div, Finset.prod_div_distrib, Finset.prod_const,
        Finset.card_univ, hcard]
      norm_num only [show (2 ^ 3 : ℂ) = 8 by norm_num]
      have hi := congrArg GaussianInt.toComplex (hcertificate J hJ x y)
      simp only [map_sum, map_prod, map_intCast, apply_ite, map_zero] at hi
      rw [← Int.cast_sum]
      rw [hi]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e he
      by_cases h : evenEigen e <;> simp [h] <;> ring
  change IsStrongResistant 1 (cycleGraphState 5)
  refine ⟨initial_gme, ?_, ?_⟩
  · intro J hJ
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hJ
    let l : Fin 6 := ⟨j.val + 1, by omega⟩
    have hg := gme_family l
    dsimp [densityFamily, Retained, lossSet, l] at hg
    exact hg
  · intro J hJ
    exact separable_family J hJ
#print axioms result
end D5.S3.Quantum.Entanglement.CycleFiveStrongOneResistance
