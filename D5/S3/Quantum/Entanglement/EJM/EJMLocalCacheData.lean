/- GID: D5/S3/Quantum/Entanglement/EJM/EJMLocalCacheData
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMLocalCacheData
   mirror-E: none(waiver:actual-exact-certificate-cache)
   anchors: []
   utility: none
   digest: Compact row mirrors, exact action composition and literal original-block incidence provide executable cache data. -/

/- Prepared source: not yet compiled. Part of the same complete actual EJM
certificate, not a standalone conditional or numerical delivery. All literal
mirrors, actions and transition receipts require kernel acceptance before use.
The original score, scale, all actual assignments and four value branches are
preserved. Producer checks below are not mathematical premises. -/

import D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport
import D5.S0.Certificates.FiniteLocalRowCache
import D5.S3.Quantum.Entanglement.EJMInflationScore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMLocalCacheData
open D5.S0.Certificates.FiniteLocalRowCache (State)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym action)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (trianglePerm singletonPerm triangleMul singletonMul)

/-- Small literal hash and scaled lower; transitions are packed only within this row. -/
structure MirrorRow where
  hash : ℕ
  lower : ℤ
  slots : ℕ
  edges : ℕ

/-- Comparing the encoded assignment once preserves the whole original
assignment, and avoids decoding that original row separately at every coordinate. -/
def checkRawMirror (mirror : MirrorRow)
    (raw : D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData.RawRow) : Bool :=
  match raw with
  | .terminal hash lower | .branch hash lower _ _ _ =>
    decide (mirror.hash = hash ∧ mirror.lower =
      lower * D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData.scale)

theorem checked_raw_mirror_eq {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    (mirror : MirrorRow)
    (raw : D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData.RawRow)
    (accepted : checkRawMirror mirror raw = true) :
    D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData.partialEvent
      (n := n) mirror.hash =
        (D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData.row hn hN raw).assignment ∧
    mirror.lower =
      (D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData.row hn hN raw).lower := by
  cases raw with
  | terminal hash lower =>
    have h := of_decide_eq_true accepted
    exact ⟨congrArg (D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData.partialEvent
      (n := n)) h.1, h.2⟩
  | branch hash lower coordinate children actions =>
    have h := of_decide_eq_true accepted
    exact ⟨congrArg (D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData.partialEvent
      (n := n)) h.1, h.2⟩

inductive MirrorTree where
  | empty
  | node (index : ℕ) (row : MirrorRow) (left right : MirrorTree)

def MirrorTree.get : MirrorTree → ℕ → MirrorRow
  | .empty, _ => ⟨0, 0, 0, 0⟩
  | .node index row left right, j =>
    if j = index then row else if j < index then left.get j else right.get j

/-- Each unknown coordinate has four consecutive 25-bit next-row/action words.
Four-bit slots are proposals only; full transition receipts check their use. -/
def readTransition {N : ℕ} (hN : 0 < N) (row : MirrorRow) (coordinate : ℕ)
    (a : Fin 4) : State N LocalSym :=
  let slot := row.slots / 16 ^ coordinate % 16
  let word := row.edges / 2 ^ (25 * (4 * slot + a.val)) % 2 ^ 25
  (⟨word % 65536 % N, Nat.mod_lt _ hN⟩, action (word / 65536 % 512))

def coordinateInverse : Fin 12 → Fin 12 := ![0,1,2,4,3,5,6,7,8,10,9,11]
def trianglePreimage (s : LocalSym) := trianglePerm (coordinateInverse s.1)
def singletonPreimage (s : LocalSym) := singletonPerm (coordinateInverse s.1)

def outcomeMul : Fin 24 → Fin 24 → Fin 24 :=
  ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],
    ![1,0,4,5,2,3,7,6,10,11,8,9,18,19,20,21,22,23,12,13,14,15,16,17],
    ![2,3,0,1,5,4,12,13,14,15,16,17,6,7,8,9,10,11,19,18,22,23,20,21],
    ![3,2,5,4,0,1,13,12,16,17,14,15,19,18,22,23,20,21,6,7,8,9,10,11],
    ![4,5,1,0,3,2,18,19,20,21,22,23,7,6,10,11,8,9,13,12,16,17,14,15],
    ![5,4,3,2,1,0,19,18,22,23,20,21,13,12,16,17,14,15,7,6,10,11,8,9],
    ![6,7,8,9,10,11,0,1,2,3,4,5,14,15,12,13,17,16,20,21,18,19,23,22],
    ![7,6,10,11,8,9,1,0,4,5,2,3,20,21,18,19,23,22,14,15,12,13,17,16],
    ![8,9,6,7,11,10,14,15,12,13,17,16,0,1,2,3,4,5,21,20,23,22,18,19],
    ![9,8,11,10,6,7,15,14,17,16,12,13,21,20,23,22,18,19,0,1,2,3,4,5],
    ![10,11,7,6,9,8,20,21,18,19,23,22,1,0,4,5,2,3,15,14,17,16,12,13],
    ![11,10,9,8,7,6,21,20,23,22,18,19,15,14,17,16,12,13,1,0,4,5,2,3],
    ![12,13,14,15,16,17,2,3,0,1,5,4,8,9,6,7,11,10,22,23,19,18,21,20],
    ![13,12,16,17,14,15,3,2,5,4,0,1,22,23,19,18,21,20,8,9,6,7,11,10],
    ![14,15,12,13,17,16,8,9,6,7,11,10,2,3,0,1,5,4,23,22,21,20,19,18],
    ![15,14,17,16,12,13,9,8,11,10,6,7,23,22,21,20,19,18,2,3,0,1,5,4],
    ![16,17,13,12,15,14,22,23,19,18,21,20,3,2,5,4,0,1,9,8,11,10,6,7],
    ![17,16,15,14,13,12,23,22,21,20,19,18,9,8,11,10,6,7,3,2,5,4,0,1],
    ![18,19,20,21,22,23,4,5,1,0,3,2,10,11,7,6,9,8,16,17,13,12,15,14],
    ![19,18,22,23,20,21,5,4,3,2,1,0,16,17,13,12,15,14,10,11,7,6,9,8],
    ![20,21,18,19,23,22,10,11,7,6,9,8,4,5,1,0,3,2,17,16,15,14,13,12],
    ![21,20,23,22,18,19,11,10,9,8,7,6,17,16,15,14,13,12,4,5,1,0,3,2],
    ![22,23,19,18,21,20,16,17,13,12,15,14,5,4,3,2,1,0,11,10,9,8,7,6],
    ![23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0]]

/-- A_t after A_s uses coordinate π_s ∘ π_t and outcome o_t ∘ o_s. -/
def triangleCompose (t s : LocalSym) : LocalSym :=
  (triangleMul s.1 t.1, outcomeMul t.2 s.2)
def singletonCompose (t s : LocalSym) : LocalSym :=
  (singletonMul s.1 t.1, outcomeMul t.2 s.2)

def triangleIncidence : Fin 20 → Fin 16 → Option (Fin 10) :=
  ![![some 0,some 0,none,none,none,none,some 6,some 3,none,none,some 6,some 3,none,none,some 6,some 3],
    ![some 1,none,some 0,none,none,some 6,none,some 6,none,some 6,none,some 6,none,some 6,none,some 6],
    ![some 2,none,none,some 9,some 2,none,none,some 9,some 2,none,none,some 9,some 2,none,none,some 9],
    ![none,some 1,none,some 0,some 6,none,some 3,none,some 6,none,some 3,none,some 6,none,some 3,none],
    ![none,some 2,some 9,none,none,some 2,some 9,none,none,some 2,some 9,none,none,some 2,some 9,none],
    ![none,none,some 1,some 1,some 3,some 3,none,none,some 3,some 3,none,none,some 3,some 3,none,none],
    ![none,some 9,some 2,none,none,some 9,some 2,none,none,some 9,some 2,none,none,some 9,some 2,none],
    ![some 9,none,none,some 2,some 9,none,none,some 2,some 9,none,none,some 2,some 9,none,none,some 2],
    ![none,none,some 6,some 6,some 0,some 0,none,none,none,none,some 7,some 4,none,none,some 7,some 4],
    ![none,some 6,none,some 3,some 1,none,some 0,none,none,some 7,none,some 7,none,some 7,none,some 7],
    ![some 3,some 3,none,none,none,none,some 1,some 0,some 4,some 4,none,none,some 4,some 4,none,none],
    ![some 6,none,some 3,none,none,some 1,none,some 1,some 7,none,some 4,none,some 7,none,some 4,none],
    ![none,none,some 7,some 7,none,none,some 7,some 4,some 0,some 0,none,none,none,none,some 8,some 5],
    ![none,some 7,none,some 4,none,some 7,none,some 7,some 1,none,some 0,none,none,some 8,none,some 8],
    ![some 4,some 4,none,none,some 4,some 4,none,none,none,none,some 1,some 0,some 5,some 5,none,none],
    ![some 7,none,some 4,none,some 7,none,some 4,none,none,some 1,none,some 1,some 8,none,some 5,none],
    ![none,none,some 8,some 8,none,none,some 8,some 5,none,none,some 8,some 5,some 0,some 0,none,none],
    ![none,some 8,none,some 5,none,some 8,none,some 8,none,some 8,none,some 8,some 1,none,some 0,none],
    ![some 5,some 5,none,none,some 5,some 5,none,none,some 5,some 5,none,none,none,none,some 1,some 0],
    ![some 8,none,some 5,none,some 8,none,some 5,none,some 8,none,some 5,none,none,some 1,none,some 1]]

def singletonIncidence : Fin 20 → Fin 16 → Option (Fin 9) :=
  ![![some 0,none,none,none,none,some 1,none,some 1,none,some 1,none,some 1,none,some 1,none,some 1],
    ![none,some 0,none,none,some 1,none,some 1,none,some 1,none,some 1,none,some 1,none,some 1,none],
    ![none,none,some 7,some 7,none,none,some 7,some 7,none,none,some 7,some 7,none,none,some 7,some 7],
    ![none,none,some 0,none,some 2,none,some 2,none,some 2,none,some 2,none,some 2,none,some 2,none],
    ![none,some 7,none,some 8,none,some 7,some 8,none,none,some 7,some 8,none,none,some 7,some 8,none],
    ![none,none,none,some 0,none,some 2,none,some 2,none,some 2,none,some 2,none,some 2,none,some 2],
    ![some 7,none,some 8,none,some 7,none,none,some 8,some 7,none,none,some 8,some 7,none,none,some 8],
    ![some 8,some 8,none,none,some 8,some 8,none,none,some 8,some 8,none,none,some 8,some 8,none,none],
    ![none,some 1,some 1,none,some 0,none,none,none,none,some 3,none,some 3,none,some 3,none,some 3],
    ![some 1,none,none,some 1,none,some 0,none,none,some 3,none,some 3,none,some 3,none,some 3,none],
    ![none,some 2,some 2,none,none,none,some 0,none,none,some 4,none,some 4,none,some 4,none,some 4],
    ![some 2,none,none,some 2,none,none,none,some 0,some 4,none,some 4,none,some 4,none,some 4,none],
    ![none,some 3,some 3,none,none,some 3,none,some 3,some 0,none,none,none,none,some 5,none,some 5],
    ![some 3,none,none,some 3,some 3,none,some 3,none,none,some 0,none,none,some 5,none,some 5,none],
    ![none,some 4,some 4,none,none,some 4,none,some 4,none,none,some 0,none,none,some 6,none,some 6],
    ![some 4,none,none,some 4,some 4,none,some 4,none,none,none,none,some 0,some 6,none,some 6,none],
    ![none,some 5,some 5,none,none,some 5,none,some 5,none,some 5,none,some 5,some 0,none,none,none],
    ![some 5,none,none,some 5,some 5,none,some 5,none,some 5,none,some 5,none,none,some 0,none,none],
    ![none,some 6,some 6,none,none,some 6,none,some 6,none,some 6,none,some 6,none,none,some 0,none],
    ![some 6,none,none,some 6,some 6,none,some 6,none,some 6,none,some 6,none,none,none,none,some 0]]

end D5.S3.Quantum.Entanglement.EJM.EJMLocalCacheData
