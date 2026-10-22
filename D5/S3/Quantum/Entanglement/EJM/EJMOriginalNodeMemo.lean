/- GID: D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo
   mirror-E: none(waiver:exact-original-decoder-equations-and-checker-transport)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/PreparedEJMCompleteFrontierRaw029.raw_cut_03712; premises=D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_2_0,D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_1_0,D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_3_442,D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_3_0,D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_3_112,D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_4_295,D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_2_57,D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_2_33
   digest: Eight certified original DAG nodes give an exact fuel-indexed memo decoder and preserve the full actual-context checker. -/

/- The concrete decoder, node size, actions and eight keys belong to the original
EJM instance. ExactMemo quantifies over arbitrary key and output types, including
function-valued outputs. The complete key is checked before a literal is reused;
all other calls use the original decoder. Full-checker equality retains every
actual cache, partial event, lower bound, scale and exhaustive value branch.

The computational use is numeric reduction in the original Raw029 suffix
consumer. Its eight full-node equalities supply the exact numerical decoder
outputs. Sharing these outputs supplies no context's acceptance: every suffix
still checks its complete original cache, partial assignment and predicates. -/

import D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.EJMOriginalNodeMemo

namespace ExactMemo

universe u v
variable {Key : Type u} {Output : Type v}

/-- A transparent input/output pair carries a kernel proof for that exact input.
The proof can be opaque while the output remains a reducible literal. -/
structure Receipt (actual : Key → Output) where
  input : Key
  output : Output
  correct : output = actual input

/-- Any selector may propose a certified entry, including a hash bucket, trie,
dictionary or a selector returning the wrong entry. Reuse requires complete Key
equality. A missing or mismatched entry evaluates the original function. -/
def memoStep [DecidableEq Key] (actual : Key → Output)
    (lookup : Key → Option (Receipt actual)) (input : Key) : Output :=
  match lookup input with
  | none => actual input
  | some receipt =>
    if receipt.input = input then receipt.output else actual input

/-- No completeness, injectivity, ordering or honesty premise on lookup. -/
theorem memoStep_eq [DecidableEq Key] (actual : Key → Output)
    (lookup : Key → Option (Receipt actual)) (input : Key) :
    memoStep actual lookup input = actual input := by
  cases selected : lookup input with
  | none => simp only [memoStep, selected]
  | some receipt =>
    by_cases same : receipt.input = input
    · simpa only [memoStep, selected, if_pos same] using
        receipt.correct.trans (congrArg actual same)
    · simp only [memoStep, selected, if_neg same]

/-- Function equality transports any existing consumer without changing it. -/
theorem memoStep_fun_eq [DecidableEq Key] (actual : Key → Output)
    (lookup : Key → Option (Receipt actual)) : memoStep actual lookup = actual :=
  funext (memoStep_eq actual lookup)


end ExactMemo

open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGNode (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
  (check checkSplit checked_split_node)
open EJMCacheState (Cache step lower)
open EJMPartialBoundData (scale)
open EJMGlobalScoreSymmetry (Cut)
open ExactMemo (Receipt memoStep memoStep_eq)

abbrev ReplayNode :=
  Node EJMOriginalGlobalDAGData.Size (Fin 20) (Fin 4) Cut

abbrev Key := Nat × Fin EJMOriginalGlobalDAGData.Size

def actual (key : Key) : ReplayNode :=
  EJMOriginalGlobalDAGData.nodes key.1 key.2

def zeroIndex : Fin EJMOriginalGlobalDAGData.Size := ⟨0, by decide⟩

def zeroChildren : Fin 4 → Fin EJMOriginalGlobalDAGData.Size :=
  fun _ => zeroIndex

def boundNode : ReplayNode := .bound

def split18Node : ReplayNode :=
  .split ⟨18, by decide⟩ zeroChildren

def split19Node : ReplayNode :=
  .split ⟨19, by decide⟩ zeroChildren

def symmetry12 : Cut := EJMGlobalScoreSymmetry.cutOfTag 24 12
def symmetry13 : Cut := EJMGlobalScoreSymmetry.cutOfTag 24 13
def symmetry14 : Cut := EJMGlobalScoreSymmetry.cutOfTag 24 14

def symmetry12Node : ReplayNode := .symmetry symmetry12
def symmetry13Node : ReplayNode := .symmetry symmetry13
def symmetry14Node : ReplayNode := .symmetry symmetry14

private def isBound : ReplayNode → Bool
  | .bound => true
  | _ => false

private theorem bound_of_isBound (node : ReplayNode)
    (accepted : isBound node = true) : node = .bound := by
  cases node with
  | bound => rfl
  | symmetry s => simp only [isBound, Bool.false_eq_true] at accepted
  | split i children => simp only [isBound, Bool.false_eq_true] at accepted


/-- The entire symmetry action and pivot are compared. -/
private def checkSymmetry (node : ReplayNode) (proposed : Cut) : Bool :=
  match node with
  | .symmetry actual => decide (actual = proposed)
  | _ => false

private theorem symmetry_of_checked (node : ReplayNode) (proposed : Cut)
    (accepted : checkSymmetry node proposed = true) :
    node = .symmetry proposed := by
  cases node with
  | bound => simp only [checkSymmetry, Bool.false_eq_true] at accepted
  | symmetry actual =>
    change decide (actual = proposed) = true at accepted
    exact congrArg Node.symmetry (of_decide_eq_true accepted)
  | split i children =>
    simp only [checkSymmetry, Bool.false_eq_true] at accepted

/- Each ground Boolean below still requires real Lean/kernel validation.
The decoded literals were read from the current original packed source. -/
private theorem node_2_0_receipt :
    isBound (EJMOriginalGlobalDAGData.nodes 2 zeroIndex) = true := by
  decide +kernel

theorem node_2_0 :
    EJMOriginalGlobalDAGData.nodes 2 zeroIndex = boundNode :=
  bound_of_isBound _ node_2_0_receipt

private theorem node_1_0_receipt :
    isBound (EJMOriginalGlobalDAGData.nodes 1 zeroIndex) = true := by
  decide +kernel

theorem node_1_0 :
    EJMOriginalGlobalDAGData.nodes 1 zeroIndex = boundNode :=
  bound_of_isBound _ node_1_0_receipt

private theorem node_3_442_receipt :
    checkSplit (EJMOriginalGlobalDAGData.nodes 3 ⟨442, by decide⟩)
      (⟨18, by decide⟩ : Fin 20) zeroChildren = true := by
  decide +kernel

theorem node_3_442 :
    EJMOriginalGlobalDAGData.nodes 3 ⟨442, by decide⟩ = split18Node :=
  checked_split_node _ _ _ node_3_442_receipt

private theorem node_3_0_receipt :
    isBound (EJMOriginalGlobalDAGData.nodes 3 zeroIndex) = true := by
  decide +kernel

theorem node_3_0 :
    EJMOriginalGlobalDAGData.nodes 3 zeroIndex = boundNode :=
  bound_of_isBound _ node_3_0_receipt

private theorem node_3_112_receipt :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 3 ⟨112, by decide⟩)
      symmetry13 = true := by
  decide +kernel

theorem node_3_112 :
    EJMOriginalGlobalDAGData.nodes 3 ⟨112, by decide⟩ = symmetry13Node :=
  symmetry_of_checked _ _ node_3_112_receipt

private theorem node_4_295_receipt :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 4 ⟨295, by decide⟩)
      symmetry12 = true := by
  decide +kernel

theorem node_4_295 :
    EJMOriginalGlobalDAGData.nodes 4 ⟨295, by decide⟩ = symmetry12Node :=
  symmetry_of_checked _ _ node_4_295_receipt

private theorem node_2_57_receipt :
    checkSymmetry (EJMOriginalGlobalDAGData.nodes 2 ⟨57, by decide⟩)
      symmetry14 = true := by
  decide +kernel

theorem node_2_57 :
    EJMOriginalGlobalDAGData.nodes 2 ⟨57, by decide⟩ = symmetry14Node :=
  symmetry_of_checked _ _ node_2_57_receipt

private theorem node_2_33_receipt :
    checkSplit (EJMOriginalGlobalDAGData.nodes 2 ⟨33, by decide⟩)
      (⟨19, by decide⟩ : Fin 20) zeroChildren = true := by
  decide +kernel

theorem node_2_33 :
    EJMOriginalGlobalDAGData.nodes 2 ⟨33, by decide⟩ = split19Node :=
  checked_split_node _ _ _ node_2_33_receipt

/- Receipt definitions remain transparent; their correctness proofs may be
opaque. Projecting output does not unfold the correctness theorem. -/
def receipt_2_0 : Receipt actual where
  input := (2, zeroIndex)
  output := boundNode
  correct := node_2_0.symm

def receipt_1_0 : Receipt actual where
  input := (1, zeroIndex)
  output := boundNode
  correct := node_1_0.symm

def receipt_3_442 : Receipt actual where
  input := (3, ⟨442, by decide⟩)
  output := split18Node
  correct := node_3_442.symm

def receipt_3_0 : Receipt actual where
  input := (3, zeroIndex)
  output := boundNode
  correct := node_3_0.symm

def receipt_3_112 : Receipt actual where
  input := (3, ⟨112, by decide⟩)
  output := symmetry13Node
  correct := node_3_112.symm

def receipt_4_295 : Receipt actual where
  input := (4, ⟨295, by decide⟩)
  output := symmetry12Node
  correct := node_4_295.symm

def receipt_2_57 : Receipt actual where
  input := (2, ⟨57, by decide⟩)
  output := symmetry14Node
  correct := node_2_57.symm

def receipt_2_33 : Receipt actual where
  input := (2, ⟨33, by decide⟩)
  output := split19Node
  correct := node_2_33.symm

/-- Selection has no correctness premise: memoStep checks the complete Key.
Every absent or mismatched entry calls the original fuel-indexed decoder. -/
def lookup (key : Key) : Option (Receipt actual) :=
  match key.1, key.2.val with
  | 2, 0 => some receipt_2_0
  | 1, 0 => some receipt_1_0
  | 3, 442 => some receipt_3_442
  | 3, 0 => some receipt_3_0
  | 3, 112 => some receipt_3_112
  | 4, 295 => some receipt_4_295
  | 2, 57 => some receipt_2_57
  | 2, 33 => some receipt_2_33
  | _, _ => none

def memoNodes (fuel : Nat) (index : Fin EJMOriginalGlobalDAGData.Size) :
    ReplayNode :=
  memoStep actual lookup (fuel, index)

theorem memoNodes_eq (fuel : Nat) (index : Fin EJMOriginalGlobalDAGData.Size) :
    memoNodes fuel index = EJMOriginalGlobalDAGData.nodes fuel index :=
  memoStep_eq actual lookup (fuel, index)

theorem nodes_fun_eq : memoNodes = EJMOriginalGlobalDAGData.nodes :=
  funext fun fuel => funext fun index => memoNodes_eq fuel index

/-- Function congruence transports the complete original checker without
unfolding its decoder, cache steps, partial event or recursion. -/
theorem check_eq_original
    (fuel : Nat) (index : Fin EJMOriginalGlobalDAGData.Size) (cache : Cache)
    (p : Partial (Fin 20) (Fin 4)) :
    check memoNodes step lower EJMGlobalScoreSymmetry.dominates scale
      fuel index cache p =
    check EJMOriginalGlobalDAGData.nodes step lower
      EJMGlobalScoreSymmetry.dominates scale fuel index cache p :=
  congrArg
    (fun ns : Nat → Fin EJMOriginalGlobalDAGData.Size → ReplayNode =>
      check ns step lower EJMGlobalScoreSymmetry.dominates scale fuel index cache p)
    nodes_fun_eq

#print axioms ExactMemo.memoStep_eq
#print axioms ExactMemo.memoStep_fun_eq
#print axioms bound_of_isBound
#print axioms symmetry_of_checked
#print axioms node_2_0
#print axioms node_1_0
#print axioms node_3_442
#print axioms node_3_0
#print axioms node_3_112
#print axioms node_4_295
#print axioms node_2_57
#print axioms node_2_33
#print axioms memoNodes_eq
#print axioms nodes_fun_eq
#print axioms check_eq_original

end D5.S3.Quantum.Entanglement.EJM.EJMOriginalNodeMemo
