/- GID: D5/S3/Quantum/Entanglement/EJM/EJMOriginalGlobalDAGData
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMOriginalGlobalDAGData
   mirror-E: none(waiver:actual-complete-original-dag-input)
   anchors: []
   utility: none
   digest: The complete original DAG decodes its actual action pivots and natural split Nodes with fuel checks. -/

/- Untrusted exact certificate input. Source generation and native binding do
not assert Lean acceptance. Actual bound and symmetry predicates must be
checked at every reached partial context of the complete original domain. -/
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock00
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock01
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock02
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock03
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock04
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock05
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock06
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock07
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock08
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock09
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock10
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock11
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock12
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock13
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock14
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock15
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock16
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock17
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock18
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock19
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock20
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock21
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock22
import D5.S3.Quantum.Entanglement.EJM.Encoding.EJMOriginalDAGBlock23
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalScoreSymmetry
import D5.S0.Certificates.FiniteSymmetryDAGNode
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Quantum.Entanglement.EJM.EJMOriginalGlobalDAGData
open D5.S0.Certificates.FiniteSymmetryDAGNode (Node)
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalScoreSymmetry

abbrev Size := 1558777

private def packedChunk (index : ℕ) : ℕ :=
  if index < 512 then EJMOriginalDAGBlock00.chunks.get index else
  if index < 1024 then EJMOriginalDAGBlock01.chunks.get index else
  if index < 1536 then EJMOriginalDAGBlock02.chunks.get index else
  if index < 2048 then EJMOriginalDAGBlock03.chunks.get index else
  if index < 2560 then EJMOriginalDAGBlock04.chunks.get index else
  if index < 3072 then EJMOriginalDAGBlock05.chunks.get index else
  if index < 3584 then EJMOriginalDAGBlock06.chunks.get index else
  if index < 4096 then EJMOriginalDAGBlock07.chunks.get index else
  if index < 4608 then EJMOriginalDAGBlock08.chunks.get index else
  if index < 5120 then EJMOriginalDAGBlock09.chunks.get index else
  if index < 5632 then EJMOriginalDAGBlock10.chunks.get index else
  if index < 6144 then EJMOriginalDAGBlock11.chunks.get index else
  if index < 6656 then EJMOriginalDAGBlock12.chunks.get index else
  if index < 7168 then EJMOriginalDAGBlock13.chunks.get index else
  if index < 7680 then EJMOriginalDAGBlock14.chunks.get index else
  if index < 8192 then EJMOriginalDAGBlock15.chunks.get index else
  if index < 8704 then EJMOriginalDAGBlock16.chunks.get index else
  if index < 9216 then EJMOriginalDAGBlock17.chunks.get index else
  if index < 9728 then EJMOriginalDAGBlock18.chunks.get index else
  if index < 10240 then EJMOriginalDAGBlock19.chunks.get index else
  if index < 10752 then EJMOriginalDAGBlock20.chunks.get index else
  if index < 11264 then EJMOriginalDAGBlock21.chunks.get index else
  if index < 11776 then EJMOriginalDAGBlock22.chunks.get index else
  EJMOriginalDAGBlock23.chunks.get index

def word (index : ℕ) : ℕ :=
  packedChunk (index / 128) / 2 ^ (103 * (index % 128)) % 2 ^ 103

/-- A mismatching fuel/record is rejected by the identity cut. Valid splits
use the literal original Node, and never infer a different variable ordering. -/
def nodes (fuel : ℕ) (index : Fin Size) :
    Node Size (Fin 20) (Fin 4) Cut :=
  let w := word index.val
  if w % 4 = 0 then .bound
  else if w % 4 = 1 then
    let payload := w / 4 % 131072
    .symmetry (cutOfTag ⟨payload / 20 % 4608, Nat.mod_lt _ (by decide)⟩
      ⟨payload % 20, Nat.mod_lt _ (by decide)⟩)
  else if w / 4 % 131072 = (21 - fuel) % 20 then
    .split ⟨w / 4 % 131072 % 20, Nat.mod_lt _ (by decide)⟩
      (fun a => ⟨(w / 2 ^ (19 + 21 * a.val) % 2 ^ 21) % Size,
        Nat.mod_lt _ (by decide)⟩)
  else .symmetry (cutOfTag 0 0)

def root : Fin Size := ⟨1558776, by decide⟩

end D5.S3.Quantum.Entanglement.EJM.EJMOriginalGlobalDAGData
