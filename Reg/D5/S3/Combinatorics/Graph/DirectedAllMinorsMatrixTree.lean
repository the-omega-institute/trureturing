import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree
open _root_.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

structure Parameters where
  R : Type u
  ring : CommRing R
  n : ℕ
  k : ℕ
  U : Finset (Fin n)
  W : Finset (Fin n)
  hU : U.card = k
  hW : W.card = k
  hk : 1 ≤ k

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Matrix (Fin p.n) (Fin p.n) p.R
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.R
  Anchor := Empty
  finiteAnchor := inferInstance

def minorValue (p : Parameters.{u}) (M : signature.State p) : p.R :=
  letI := p.ring
  let row : Fin (p.n - p.k) ↪o Fin p.n :=
    p.Wᶜ.orderEmbOfFin (by simp [Finset.card_compl, p.hW])
  let col : Fin (p.n - p.k) ↪o Fin p.n :=
    p.Uᶜ.orderEmbOfFin (by simp [Finset.card_compl, p.hU])
  (M.submatrix row col).det

def actual : Realization signature.{u} :=
  realize signature (fun _ p M => minorValue p M) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.ring; 0) (fun e => nomatch e)

open Classical in
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ p : Parameters.{u}, letI := p.ring
    ∀ M : signature.State p, (∀ j, ∑ i, M i j = 0) →
    let graph := fun F : Finset (Fin p.n × Fin p.n) =>
      SimpleGraph.fromRel (fun i j => (i, j) ∈ F)
    let Forest := {F : Finset (Fin p.n × Fin p.n) //
      (∀ edge ∈ F, edge.1 ≠ edge.2) ∧
      (graph F).IsAcyclic ∧
      (∀ v, ∃! root, root ∈ p.U ∧ (graph F).Reachable v root) ∧
      (∀ v, ∃! mark, mark ∈ p.W ∧ (graph F).Reachable v mark) ∧
      (∀ i j, (i, j) ∈ F → ∀ root ∈ p.U, (graph F).Reachable root i →
        (graph F).dist root i < (graph F).dist root j)}
    ∃ matching : Forest → Equiv.Perm (Fin p.k),
      (∀ F a, (graph F.val).Reachable (p.U.orderEmbOfFin p.hU a)
        (p.W.orderEmbOfFin p.hW (matching F a))) ∧
      r.readout () p M =
        ∑ F : Forest,
          (((-1 : ℤ) ^ (p.n + p.k + (∑ root ∈ p.U, root.val) +
            (∑ mark ∈ p.W, mark.val)) * (Equiv.Perm.sign (matching F) : ℤ) : ℤ) : p.R) *
            ∏ edge ∈ F.val, M edge.1 edge.2

def rejectedLaw : ¬arena.{u}.Law rejected.{u} := by
  classical
  intro h
  let p : Parameters.{u} :=
    ⟨ULift.{u} ℤ, inferInstance, 1, 1, Finset.univ, Finset.univ, by simp, by simp, by omega⟩
  letI := p.ring
  obtain ⟨matching, hmatching, hcorrect⟩ := directed_all_minors_matrix_tree
    (0 : Matrix (Fin p.n) (Fin p.n) p.R) p.U p.W p.hU p.hW p.hk (by simp)
  obtain ⟨otherMatching, hother, hwrong⟩ := h p 0 (by simp; intro j; rfl)
  have hperm : otherMatching = matching := funext fun F => Subsingleton.elim _ _
  rw [hperm] at hwrong
  simp only [rejected, realize] at hwrong
  simp only [Matrix.det_isEmpty] at hcorrect
  have hbad : (1 : p.R) = 0 := hcorrect.trans hwrong.symm
  exact one_ne_zero hbad

def dependence : ObservationalDependence signature.{u} actual.{u} := by
  classical
  intro role
  let p : Parameters.{u} :=
    ⟨ULift.{u} ℤ, inferInstance, 2, 1, {0}, {0}, by simp, by simp, by omega⟩
  letI := p.ring
  refine ⟨p, 0, 1, ?_⟩
  intro h
  have hzero : minorValue p 0 = 0 := by
    simp [minorValue, p, Matrix.det_fin_one]
  have hone : minorValue p 1 = 1 := by
    simp [minorValue, p, Matrix.det_fin_one, Matrix.one_apply]
    rfl
  change minorValue p 0 = minorValue p 1 at h
  rw [hzero, hone] at h
  exact zero_ne_one h

open Classical in
abbrev SourceClaim : Prop :=
  ∀ {R : Type u} [CommRing R] {n k : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (U W : Finset (Fin n))
    (hU : U.card = k) (hW : W.card = k) (hk : 1 ≤ k)
    (hcol : ∀ j, ∑ i, M i j = 0),
    let graph := fun F : Finset (Fin n × Fin n) =>
      SimpleGraph.fromRel (fun i j => (i, j) ∈ F)
    let Forest := {F : Finset (Fin n × Fin n) //
      (∀ edge ∈ F, edge.1 ≠ edge.2) ∧
      (graph F).IsAcyclic ∧
      (∀ v, ∃! root, root ∈ U ∧ (graph F).Reachable v root) ∧
      (∀ v, ∃! mark, mark ∈ W ∧ (graph F).Reachable v mark) ∧
      (∀ i j, (i, j) ∈ F → ∀ root ∈ U, (graph F).Reachable root i →
        (graph F).dist root i < (graph F).dist root j)}
    let row : Fin (n - k) ↪o Fin n :=
      Wᶜ.orderEmbOfFin (by simp [Finset.card_compl, hW])
    let col : Fin (n - k) ↪o Fin n :=
      Uᶜ.orderEmbOfFin (by simp [Finset.card_compl, hU])
    ∃ matching : Forest → Equiv.Perm (Fin k),
      (∀ F a, (graph F.val).Reachable (U.orderEmbOfFin hU a)
        (W.orderEmbOfFin hW (matching F a))) ∧
      (M.submatrix row col).det =
        ∑ F : Forest,
          (((-1 : ℤ) ^ (n + k + (∑ root ∈ U, root.val) + (∑ mark ∈ W, mark.val)) *
            (Equiv.Perm.sign (matching F) : ℤ) : ℤ) : R) *
            ∏ edge ∈ F.val, M edge.1 edge.2

def registration : Registration arena.{u} SourceClaim.{u} where
  actual := actual
  bridge := by
    constructor
    · intro h p
      letI := p.ring
      intro M hcol
      exact h M p.U p.W p.hU p.hW p.hk hcol
    · intro h R inst n k M U W hU hW hk hcol
      let p : Parameters.{u} := ⟨R, inst, n, k, U, W, hU, hW, hk⟩
      exact h p M hcol
  variation := ⟨by
    intro p
    letI := p.ring
    intro M hcol
    exact directed_all_minors_matrix_tree M p.U p.W p.hU p.hW p.hk hcol,
    rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro anchor
      exact nomatch anchor
  dependence := dependence

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.directed_all_minors_matrix_tree.{u_1}) (type_of% (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ p M => minorValue.{u_1} p M) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "Graph") "DirectedAllMinorsMatrixTree") "directed_all_minors_matrix_tree") "Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree/Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ p M => minorValue.{u_1} p M) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree, definition := none, coordinates := #[0, 1, 2, 3, 5, 6, 7, 8, 9], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree, declaration := `D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.directed_all_minors_matrix_tree, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree, declaration := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree, declaration := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree, declaration := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree, declaration := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.canonicalArenaFact, `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.sourceBridgeFact, `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.anchorEnumeration }


end Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree


noncomputable def Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.arena.{u_1}
noncomputable def Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"DirectedAllMinorsMatrixTree\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"DirectedAllMinorsMatrixTree\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree, declaration := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree, declaration := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.arena.{u_1}
noncomputable def Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"DirectedAllMinorsMatrixTree\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"DirectedAllMinorsMatrixTree\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree, declaration := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree, declaration := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0}
  Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.arena.{u_1}
    Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.SourceClaim.{u_1}
    Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration.{u_1})

noncomputable def Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"DirectedAllMinorsMatrixTree\",\"directed_all_minors_matrix_tree\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"DirectedAllMinorsMatrixTree\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree, declaration := `D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.directed_all_minors_matrix_tree, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree, declaration := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{u_1 + 1, u_1, 0, u_1, 0}
  Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.arena.{u_1}
  Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.SourceClaim.{u_1}
  Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration.{u_1})

noncomputable def Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"DirectedAllMinorsMatrixTree\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"DirectedAllMinorsMatrixTree\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"DirectedAllMinorsMatrixTree\",\"directed_all_minors_matrix_tree\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree, declaration := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree, declaration := `D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.directed_all_minors_matrix_tree, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration.{u_1}).actual (Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration.{u_1}).variation.2.choose (Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration.{u_1}).variation.1 (Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"DirectedAllMinorsMatrixTree\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"DirectedAllMinorsMatrixTree\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree, declaration := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree, declaration := `Reg.D5.S3.Combinatorics.Graph.DirectedAllMinorsMatrixTree.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
