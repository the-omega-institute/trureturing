import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
universe u v w z

abbrev natSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def eqActual : Realization natSignature :=
  realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e)
def leActual : Realization natSignature :=
  realize natSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e)
def ltActual : Realization natSignature :=
  realize natSignature (fun _ _ a b => a < b) (fun e => nomatch e)
def natRejected : Realization natSignature :=
  realize natSignature (fun _ _ _ _ => False) (fun e => nomatch e)

theorem eqDependence : ObservationalDependence natSignature eqActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℕ) = 0) = ((1 : ℕ) = 0) at he
  have hn : (1 : ℕ) = 0 := he ▸ rfl
  omega

theorem leDependence : ObservationalDependence natSignature leActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℕ) ≤ 0) = ((1 : ℕ) ≤ 0) at he
  have hn : (1 : ℕ) ≤ 0 := he ▸ (Nat.le_refl 0)
  omega

theorem ltDependence : ObservationalDependence natSignature ltActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 1
  change ((0 : ℕ) < 1) = ((1 : ℕ) < 1) at he
  have hn : (1 : ℕ) < 1 := he ▸ (by omega : (0 : ℕ) < 1)
  omega

@[reducible] def attainedArena : Arena where
  signature := natSignature
  Law R := ∀ a b c d : ℕ,
    ∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ),
      R.readout () () (flow M N).rank (QMaxFlow a b c d)
theorem attainedPositive : attainedArena.Law eqActual := QMaxFlow_attained
theorem attainedNegative : ¬ attainedArena.Law natRejected := by
  intro h
  obtain ⟨M, N, hf⟩ := h 0 0 0 0
  exact hf

@[reducible] def rankArena : Arena where
  signature := natSignature
  Law R := ∀ {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ),
    R.readout () () (flow M N).rank (QMaxFlow a b c d)
theorem rankPositive : rankArena.Law leActual := @rank_le_QMaxFlow
theorem rankNegative : ¬ rankArena.Law natRejected := by
  intro h
  exact h (a := 0) (b := 0) (c := 0) (d := 0) (fun _ => 0) (fun _ => 0)

@[reducible] def cutArena : Arena where
  signature := natSignature
  Law R := ∀ a b c d : ℕ, R.readout () () (QMaxFlow a b c d) (QMinCut a b c d)
theorem cutPositive : cutArena.Law leActual := QMaxFlow_le_QMinCut
theorem cutNegative : ¬ cutArena.Law natRejected := by
  intro h
  exact h 0 0 0 0

@[reducible] def coneArena : Arena where
  signature := natSignature
  Law R := ∀ {a b : ℕ} (ha : 0 < a)
    (h : a * a + b * b ≤ 3 * a * b), R.readout () () b (3 * a)
theorem conePositive : coneArena.Law ltActual := @cone_bounds
theorem coneNegative : ¬ coneArena.Law natRejected := by
  intro h
  exact h (a := 1) (b := 1) (by norm_num) (by norm_num)

@[reducible] def coneCutArena : Arena where
  signature := natSignature
  Law R := ∀ {a b c d : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hab : a * a + b * b ≤ 3 * a * b)
    (hcd : c * c + d * d ≤ 3 * c * d),
    R.readout () () (QMinCut a b c d) (min (a * d) (b * c))
theorem coneCutPositive : coneCutArena.Law eqActual := @cone_QMinCut
theorem coneCutNegative : ¬ coneCutArena.Law natRejected := by
  intro h
  exact h (a := 1) (b := 1) (c := 1) (d := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

@[reducible] def rationalArena : Arena where
  signature := natSignature
  Law R := ∀ {a b c d : ℕ} (h : RationalWitness a b c d),
    R.readout () () (QMaxFlow a b c d) (min (a * d) (b * c))
theorem rationalPositive : rationalArena.Law eqActual := @rationalWitness_full_rank

theorem zeroWitness (b c d : ℕ) : RationalWitness 0 b c d := by
  refine ⟨(fun _ => 0), (fun _ => 0), ?_⟩
  simp [flow]

theorem obstructedWitness : ¬ RationalWitness 1 4 1 4 := by
  intro h
  have he := rationalWitness_full_rank h
  have hl := QMaxFlow_le_QMinCut 1 4 1 4
  norm_num [QMinCut] at he hl
  omega

theorem rationalNegative : ¬ rationalArena.Law natRejected := by
  intro h
  exact h (zeroWitness 0 0 0)

/-- The four independent carrier universes are retained without finiteness assumptions. -/
structure Carriers where
  I : Type u
  J : Type v
  K : Type w
  L : Type z

abbrev matrixSignature : Signature where
  Params := Carriers.{u,v,w,z}
  State p := Matrix (p.I × p.L) (p.J × p.K) ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (p.I × p.L) (p.J × p.K) ℚ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def matrixActual : Realization matrixSignature.{u,v,w,z} :=
  realize matrixSignature (fun _ _ A B => A = B) (fun e => nomatch e)
def matrixRejected : Realization matrixSignature.{u,v,w,z} :=
  realize matrixSignature (fun _ _ _ _ => False) (fun e => nomatch e)
@[reducible] def slicesArena : Arena where
  signature := matrixSignature.{u,v,w,z}
  Law R := ∀ {I : Type u} {J : Type v} {K : Type w} {L : Type z}
    (A B C : Matrix I J ℚ) (D E F : Matrix L K ℚ),
    R.readout () ⟨I,J,K,L⟩
      (∑ r : Fin 3, Matrix.kronecker (threeSlices A B C r) (threeSlices D E F r))
      (Matrix.kronecker A D + Matrix.kronecker B E + Matrix.kronecker C F)
theorem slicesPositive : slicesArena.{u,v,w,z}.Law matrixActual := @typed_three_slice_flow

theorem slicesNegative : ¬ slicesArena.{u,v,w,z}.Law matrixRejected := by
  intro h
  exact h (I := ULift.{u} Unit) (J := ULift.{v} Unit)
    (K := ULift.{w} Unit) (L := ULift.{z} Unit) 0 0 0 0 0 0

theorem matrixDependence : ObservationalDependence matrixSignature.{u,v,w,z} matrixActual := by
  intro i
  let p : Carriers.{u,v,w,z} := ⟨ULift.{u} Unit, ULift.{v} Unit, ULift.{w} Unit, ULift.{z} Unit⟩
  let x : matrixSignature.State p := 0
  let y : matrixSignature.State p := fun _ _ => 1
  refine ⟨p, x, y, ?_⟩
  intro h
  have he := congrFun h x
  change (x = x) = (y = x) at he
  have hy : y = x := he ▸ rfl
  have hh := congrArg (fun A : matrixSignature.State p => A (⟨()⟩,⟨()⟩) (⟨()⟩,⟨()⟩)) hy
  change (1 : ℚ) = 0 at hh
  norm_num at hh

abbrev witnessSignature : Signature where
  Params := ℕ × ℕ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def witnessActual : Realization witnessSignature :=
  realize witnessSignature (fun _ p a => RationalWitness a p.1 p.2.1 p.2.2) (fun e => nomatch e)
def swapActual : Realization witnessSignature :=
  realize witnessSignature (fun _ p c => RationalWitness c p.2.2 p.1 p.2.1) (fun e => nomatch e)
def witnessRejected : Realization witnessSignature :=
  realize witnessSignature (fun _ _ _ => False) (fun e => nomatch e)

@[reducible] def swapArena : Arena where
  signature := witnessSignature
  Law R := ∀ {a b c d : ℕ} (h : RationalWitness a b c d), R.readout () (a,b,d) c
theorem swapPositive : swapArena.Law swapActual := @witness_swap
theorem swapNegative : ¬ swapArena.Law witnessRejected := by
  intro h
  exact h (zeroWitness 0 0 0)
theorem swapDependence : ObservationalDependence witnessSignature swapActual := by
  intro i
  refine ⟨(1,4,4), 0, 1, ?_⟩
  intro h
  change RationalWitness 0 4 1 4 = RationalWitness 1 4 1 4 at h
  exact obstructedWitness (h ▸ zeroWitness 4 1 4)

@[reducible] def widthArena : Arena where
  signature := witnessSignature
  Law R := ∀ a b c d : ℕ, 0 < a → a ≤ b → 0 < c → c ≤ d →
    (a = b ∨ c = d ∨ (2 * a ≤ b ∧ d ≤ 2 * c) ∨
      (b ≤ 2 * a ∧ 2 * c ≤ d)) → R.readout () (b,c,d) a
theorem widthPositive : widthArena.Law witnessActual := widthTwo_proved
theorem widthNegative : ¬ widthArena.Law witnessRejected := by
  intro h
  exact h 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Or.inl rfl)
theorem witnessDependence : ObservationalDependence witnessSignature witnessActual := by
  intro i
  refine ⟨(4,1,4), 0, 1, ?_⟩
  intro h
  change RationalWitness 0 4 1 4 = RationalWitness 1 4 1 4 at h
  exact obstructedWitness (h ▸ zeroWitness 4 1 4)

def attainedEvidence : Registration attainedArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.QMaxFlow_attained)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨attainedPositive, natRejected, attainedNegative⟩
  sensitivity := ⟨fun i => ⟨natRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, attainedNegative⟩,
    fun i => nomatch i⟩
  dependence := eqDependence

noncomputable def attainedRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.QMaxFlow_attained)
    (type_of% (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.QMaxFlow_attained
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.attainedArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.attainedEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨attainedArena⟩,
  objectArena := .source ⟨attainedArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source attainedArena ⟨attainedEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.QMaxFlow_attained
#print axioms attainedPositive
#print axioms attainedNegative
#print axioms attainedEvidence
#print axioms attainedRegistration

def rankEvidence : Registration rankArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rank_le_QMaxFlow)) where
  actual := leActual
  bridge := Iff.rfl
  variation := ⟨rankPositive, natRejected, rankNegative⟩
  sensitivity := ⟨fun i => ⟨natRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rankNegative⟩,
    fun i => nomatch i⟩
  dependence := leDependence

noncomputable def rankRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rank_le_QMaxFlow)
    (type_of% (realize natSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rank_le_QMaxFlow
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rankArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rankEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨rankArena⟩,
  objectArena := .source ⟨rankArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source rankArena ⟨rankEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize natSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rank_le_QMaxFlow
#print axioms rankPositive
#print axioms rankNegative
#print axioms rankEvidence
#print axioms rankRegistration

def cutEvidence : Registration cutArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.QMaxFlow_le_QMinCut)) where
  actual := leActual
  bridge := Iff.rfl
  variation := ⟨cutPositive, natRejected, cutNegative⟩
  sensitivity := ⟨fun i => ⟨natRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, cutNegative⟩,
    fun i => nomatch i⟩
  dependence := leDependence

noncomputable def cutRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.QMaxFlow_le_QMinCut)
    (type_of% (realize natSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.QMaxFlow_le_QMinCut
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.cutArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.cutEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨cutArena⟩,
  objectArena := .source ⟨cutArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source cutArena ⟨cutEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize natSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.QMaxFlow_le_QMinCut
#print axioms cutPositive
#print axioms cutNegative
#print axioms cutEvidence
#print axioms cutRegistration

def coneEvidence : Registration coneArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.cone_bounds)) where
  actual := ltActual
  bridge := Iff.rfl
  variation := ⟨conePositive, natRejected, coneNegative⟩
  sensitivity := ⟨fun i => ⟨natRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, coneNegative⟩,
    fun i => nomatch i⟩
  dependence := ltDependence

noncomputable def coneRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.cone_bounds)
    (type_of% (realize natSignature (fun _ _ a b => a < b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.cone_bounds
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.coneArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.coneEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨coneArena⟩,
  objectArena := .source ⟨coneArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source coneArena ⟨coneEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize natSignature (fun _ _ a b => a < b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.cone_bounds
#print axioms conePositive
#print axioms coneNegative
#print axioms coneEvidence
#print axioms coneRegistration

def coneCutEvidence : Registration coneCutArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.cone_QMinCut)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨coneCutPositive, natRejected, coneCutNegative⟩
  sensitivity := ⟨fun i => ⟨natRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, coneCutNegative⟩,
    fun i => nomatch i⟩
  dependence := eqDependence

noncomputable def coneCutRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.cone_QMinCut)
    (type_of% (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.cone_QMinCut
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.coneCutArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.coneCutEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨coneCutArena⟩,
  objectArena := .source ⟨coneCutArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source coneCutArena ⟨coneCutEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.cone_QMinCut
#print axioms coneCutPositive
#print axioms coneCutNegative
#print axioms coneCutEvidence
#print axioms coneCutRegistration

def rationalEvidence : Registration rationalArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rationalWitness_full_rank)) where
  actual := eqActual
  bridge := Iff.rfl
  variation := ⟨rationalPositive, natRejected, rationalNegative⟩
  sensitivity := ⟨fun i => ⟨natRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rationalNegative⟩,
    fun i => nomatch i⟩
  dependence := eqDependence

noncomputable def rationalRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rationalWitness_full_rank)
    (type_of% (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rationalWitness_full_rank
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rationalArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rationalEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨rationalArena⟩,
  objectArena := .source ⟨rationalArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source rationalArena ⟨rationalEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize natSignature (fun _ _ a b => a = b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.rationalWitness_full_rank
#print axioms rationalPositive
#print axioms rationalNegative
#print axioms rationalEvidence
#print axioms rationalRegistration

def slicesEvidence : Registration slicesArena.{u,v,w,z}
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.typed_three_slice_flow.{u,v,w,z})) where
  actual := matrixActual
  bridge := Iff.rfl
  variation := ⟨slicesPositive, matrixRejected, slicesNegative⟩
  sensitivity := ⟨fun i => ⟨matrixRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, slicesNegative⟩,
    fun i => nomatch i⟩
  dependence := matrixDependence

noncomputable def slicesRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.typed_three_slice_flow.{u,v,w,z})
    (type_of% (realize matrixSignature.{u,v,w,z} (fun _ _ A B => A = B) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.typed_three_slice_flow
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.slicesArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.slicesEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨slicesArena.{u,v,w,z}⟩,
  objectArena := .source ⟨slicesArena.{u,v,w,z}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source slicesArena.{u,v,w,z} ⟨slicesEvidence.{u,v,w,z}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize matrixSignature.{u,v,w,z} (fun _ _ A B => A = B) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound, definition := none,
    coordinates := #[0, 1, 2, 3], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.typed_three_slice_flow
#print axioms slicesPositive
#print axioms slicesNegative
#print axioms slicesEvidence
#print axioms slicesRegistration

def swapEvidence : Registration swapArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.witness_swap)) where
  actual := swapActual
  bridge := Iff.rfl
  variation := ⟨swapPositive, witnessRejected, swapNegative⟩
  sensitivity := ⟨fun i => ⟨witnessRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, swapNegative⟩,
    fun i => nomatch i⟩
  dependence := swapDependence

noncomputable def swapRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.witness_swap)
    (type_of% (realize witnessSignature (fun _ p c => RationalWitness c p.2.2 p.1 p.2.1) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.witness_swap
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.swapArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.swapEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨swapArena⟩,
  objectArena := .source ⟨swapArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source swapArena ⟨swapEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize witnessSignature (fun _ p c => RationalWitness c p.2.2 p.1 p.2.1) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound, definition := none,
    coordinates := #[0, 1, 3], readouts := #[{
      path := #["body", "body", "body", "body", "body"],
      stateBinder := 2, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.witness_swap
#print axioms swapPositive
#print axioms swapNegative
#print axioms swapEvidence
#print axioms swapRegistration

def widthEvidence : Registration widthArena
    (type_of% (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.widthTwo_proved)) where
  actual := witnessActual
  bridge := Iff.rfl
  variation := ⟨widthPositive, witnessRejected, widthNegative⟩
  sensitivity := ⟨fun i => ⟨witnessRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, widthNegative⟩,
    fun i => nomatch i⟩
  dependence := witnessDependence

noncomputable def widthRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.widthTwo_proved)
    (type_of% (realize witnessSignature (fun _ p a => RationalWitness a p.1 p.2.1 p.2.2) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.widthTwo_proved
    "Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound/Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.widthArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.widthEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨widthArena⟩,
  objectArena := .source ⟨widthArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source widthArena ⟨widthEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize witnessSignature (fun _ p a => RationalWitness a p.1 p.2.1 p.2.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound, definition := some {
      owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound,
      name := `D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.WidthTwo,
      path := #[] },
    coordinates := #[1, 2, 3], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body"],
      stateBinder := 0, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound.widthTwo_proved
#print axioms widthPositive
#print axioms widthNegative
#print axioms widthEvidence
#print axioms widthRegistration

end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
