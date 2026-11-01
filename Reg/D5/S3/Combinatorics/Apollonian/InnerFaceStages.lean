import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Apollonian.InnerFaceStages
import Reg.Support.SingleDependentReadout

/-! Source-bound family registrations for the finite inner-face constructor laws. -/

namespace Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages
open _root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section

abbrev stageSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ Vertex (fun _ => ℕ)
abbrev cutoffSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ × ℕ) (fun p => Vertex p.1) (fun _ => ℕ)
abbrev seedSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => Fin 4) (fun _ => ℕ)
abbrev sizeSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
structure OldParameters where
  n : ℕ
  t : ℕ
  u : Vertex n
abbrev adjacencySignature : Signature :=
  Reg.Support.SingleDependentReadout.signature OldParameters (fun p => Vertex p.n) (fun _ => Prop)
abbrev oldSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ × ℕ) (fun p => Vertex (p.1 + p.2)) (fun _ => ℕ)
abbrev faceSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ n, Face n) (fun p => Vertex p.1) (fun _ => Prop)
abbrev diagonalSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ × ℕ) (fun p => Vertex p.1) (fun _ => ℝ)
abbrev gramSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature OldParameters (fun p => Vertex p.n) (fun _ => ℝ)
private def firstFace : (n : ℕ) → Face n
  | 0 => 0
  | n + 1 => (firstFace n, 0)

abbrev degreeCount_inner_actual : Realization stageSignature :=
  realize stageSignature (fun _ n v => degreeCount n v) (fun e => nomatch e)
abbrev degreeCount_inner_arena : Arena where
  signature := stageSignature
  Law R := ∀ n (v : Vertex n), 0 < birth n v → R.readout () n v = 3 * 2 ^ (n - birth n v)
private def degreeCount_inner_rejected : Realization stageSignature :=
  realize stageSignature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem degreeCount_inner_reject : ¬ degreeCount_inner_arena.Law degreeCount_inner_rejected := by
  intro h
  have hh : (0 : ℕ) = 3 := h 1 (Sum.inr (0 : Face 0)) (by decide)
  omega
def degreeCount_inner_family : Registration degreeCount_inner_arena (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_inner)) where
  actual := degreeCount_inner_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_inner, degreeCount_inner_rejected, degreeCount_inner_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ degreeCount_inner_actual degreeCount_inner_rejected degreeCount_inner_reject
  dependence := by
    intro i
    cases i
    refine ⟨1, Sum.inl (0 : Vertex 0), Sum.inl (3 : Vertex 0), ?_⟩
    decide
def registration_degreeCount_inner : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_inner)
    (Realization stageSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_inner_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_inner_family
  realizationSource := none
  generated := false
  arena := .source ⟨degreeCount_inner_arena⟩
  objectArena := .source ⟨degreeCount_inner_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source degreeCount_inner_arena ⟨degreeCount_inner_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize stageSignature (fun _ n v => degreeCount n v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body","body","body","fn","arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev degreeCount_late_le_actual : Realization cutoffSignature :=
  realize cutoffSignature (fun _ p v => degreeCount p.1 v) (fun e => nomatch e)
abbrev degreeCount_late_le_arena : Arena where
  signature := cutoffSignature
  Law R := ∀ n k (v : Vertex n), k < birth n v → R.readout () (n,k) v ≤ 3 * 2 ^ (n-k-1)
private def degreeCount_late_le_rejected : Realization cutoffSignature :=
  realize cutoffSignature (fun _ _ _ => 4) (fun e => nomatch e)
private theorem degreeCount_late_le_reject : ¬ degreeCount_late_le_arena.Law degreeCount_late_le_rejected := by
  intro h
  have hh : (4 : ℕ) ≤ 3 := h 1 0 (Sum.inr (0 : Face 0)) (by decide)
  omega
def degreeCount_late_le_family : Registration degreeCount_late_le_arena (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_late_le)) where
  actual := degreeCount_late_le_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_late_le, degreeCount_late_le_rejected, degreeCount_late_le_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ degreeCount_late_le_actual degreeCount_late_le_rejected degreeCount_late_le_reject
  dependence := by
    intro i
    cases i
    refine ⟨(1,0), Sum.inl (0 : Vertex 0), Sum.inl (3 : Vertex 0), ?_⟩
    decide
def registration_degreeCount_late_le : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_late_le)
    (Realization cutoffSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_late_le_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_late_le_family
  realizationSource := none
  generated := false
  arena := .source ⟨degreeCount_late_le_arena⟩
  objectArena := .source ⟨degreeCount_late_le_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source degreeCount_late_le_arena ⟨degreeCount_late_le_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cutoffSignature (fun _ p v => degreeCount p.1 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[0,1]
    readouts := #[{ path := #["body","body","body","body","fn","arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev seed_degrees_actual : Realization seedSignature :=
  realize seedSignature (fun _ n v => degreeCount n (seed n v)) (fun e => nomatch e)
abbrev seed_degrees_arena : Arena where
  signature := seedSignature
  Law R := ∀ n (v : Fin 4), R.readout () n v = if v = 3 then 3 * 2 ^ n else 2 ^ (n+1)+1
private def seed_degrees_rejected : Realization seedSignature :=
  realize seedSignature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem seed_degrees_reject : ¬ seed_degrees_arena.Law seed_degrees_rejected := by
  intro h
  have hh : (0 : ℕ) = 3 := h 0 0
  omega
def seed_degrees_family : Registration seed_degrees_arena (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.seed_degrees)) where
  actual := seed_degrees_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.seed_degrees, seed_degrees_rejected, seed_degrees_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ seed_degrees_actual seed_degrees_rejected seed_degrees_reject
  dependence := by
    intro i
    cases i
    refine ⟨1, 0, 3, ?_⟩
    decide
def registration_seed_degrees : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.seed_degrees)
    (Realization seedSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.seed_degrees_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.seed_degrees_family
  realizationSource := none
  generated := false
  arena := .source ⟨seed_degrees_arena⟩
  objectArena := .source ⟨seed_degrees_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source seed_degrees_arena ⟨seed_degrees_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize seedSignature (fun _ n v => degreeCount n (seed n v)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body","body","fn","arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev degreeCount_eq_degree_actual : Realization stageSignature :=
  realize stageSignature (fun _ n v => degreeCount n v) (fun e => nomatch e)
abbrev degreeCount_eq_degree_arena : Arena where
  signature := stageSignature
  Law R := ∀ n (v : Vertex n), R.readout () n v = (graph n).degree v
private def degreeCount_eq_degree_rejected : Realization stageSignature :=
  realize stageSignature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem degreeCount_eq_degree_reject : ¬ degreeCount_eq_degree_arena.Law degreeCount_eq_degree_rejected := by
  intro h
  have hh := h 0 (0 : Vertex 0)
  rw [← degreeCount_eq_degree] at hh
  change (0 : ℕ) = 3 at hh
  omega
def degreeCount_eq_degree_family : Registration degreeCount_eq_degree_arena (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_eq_degree)) where
  actual := degreeCount_eq_degree_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_eq_degree, degreeCount_eq_degree_rejected, degreeCount_eq_degree_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ degreeCount_eq_degree_actual degreeCount_eq_degree_rejected degreeCount_eq_degree_reject
  dependence := by
    intro i
    cases i
    refine ⟨1, Sum.inl (0 : Vertex 0), Sum.inl (3 : Vertex 0), ?_⟩
    decide
def registration_degreeCount_eq_degree : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_eq_degree)
    (Realization stageSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_eq_degree_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_eq_degree_family
  realizationSource := none
  generated := false
  arena := .source ⟨degreeCount_eq_degree_arena⟩
  objectArena := .source ⟨degreeCount_eq_degree_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source degreeCount_eq_degree_arena ⟨degreeCount_eq_degree_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize stageSignature (fun _ n v => degreeCount n v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body","body","fn","arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev card_vertex_ge_four_actual : Realization sizeSignature :=
  realize sizeSignature (fun _ _ n => Fintype.card (Vertex n)) (fun e => nomatch e)
abbrev card_vertex_ge_four_arena : Arena where
  signature := sizeSignature
  Law R := ∀ n, 4 ≤ R.readout () () n
private def card_vertex_ge_four_rejected : Realization sizeSignature :=
  realize sizeSignature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem card_vertex_ge_four_reject : ¬ card_vertex_ge_four_arena.Law card_vertex_ge_four_rejected := by
  intro h
  have hh : (4 : ℕ) ≤ 0 := h 0
  omega
def card_vertex_ge_four_family : Registration card_vertex_ge_four_arena (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.card_vertex_ge_four)) where
  actual := card_vertex_ge_four_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.card_vertex_ge_four, card_vertex_ge_four_rejected, card_vertex_ge_four_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ card_vertex_ge_four_actual card_vertex_ge_four_rejected card_vertex_ge_four_reject
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    decide
def registration_card_vertex_ge_four : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.card_vertex_ge_four)
    (Realization sizeSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.card_vertex_ge_four_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.card_vertex_ge_four_family
  realizationSource := none
  generated := false
  arena := .source ⟨card_vertex_ge_four_arena⟩
  objectArena := .source ⟨card_vertex_ge_four_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source card_vertex_ge_four_arena ⟨card_vertex_ge_four_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sizeSignature (fun _ _ n => Fintype.card (Vertex n)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev oriented_outdegree_le_three_actual : Realization stageSignature :=
  realize stageSignature (fun _ n u => ∑ v : Vertex n, if Oriented n u v then 1 else 0) (fun e => nomatch e)
abbrev oriented_outdegree_le_three_arena : Arena where
  signature := stageSignature
  Law R := ∀ n (u : Vertex n), R.readout () n u ≤ 3
private def oriented_outdegree_le_three_rejected : Realization stageSignature :=
  realize stageSignature (fun _ _ _ => 4) (fun e => nomatch e)
private theorem oriented_outdegree_le_three_reject : ¬ oriented_outdegree_le_three_arena.Law oriented_outdegree_le_three_rejected := by
  intro h
  have hh : (4 : ℕ) ≤ 3 := h 0 (0 : Vertex 0)
  omega
def oriented_outdegree_le_three_family : Registration oriented_outdegree_le_three_arena (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.oriented_outdegree_le_three)) where
  actual := oriented_outdegree_le_three_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.oriented_outdegree_le_three, oriented_outdegree_le_three_rejected, oriented_outdegree_le_three_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ oriented_outdegree_le_three_actual oriented_outdegree_le_three_rejected oriented_outdegree_le_three_reject
  dependence := by
    intro i
    cases i
    refine ⟨1, Sum.inl (0 : Vertex 0), Sum.inr (0 : Face 0), ?_⟩
    decide
def registration_oriented_outdegree_le_three : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.oriented_outdegree_le_three)
    (Realization stageSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.oriented_outdegree_le_three_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.oriented_outdegree_le_three_family
  realizationSource := none
  generated := false
  arena := .source ⟨oriented_outdegree_le_three_arena⟩
  objectArena := .source ⟨oriented_outdegree_le_three_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source oriented_outdegree_le_three_arena ⟨oriented_outdegree_le_three_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize stageSignature (fun _ n u => ∑ v : Vertex n, if Oriented n u v then 1 else 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body","body","fn","arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev late_oriented_indegree_le_actual : Realization cutoffSignature :=
  realize cutoffSignature (fun _ p u => ∑ v : Vertex p.1, if p.2 < birth p.1 v ∧ Oriented p.1 v u then 1 else 0) (fun e => nomatch e)
abbrev late_oriented_indegree_le_arena : Arena where
  signature := cutoffSignature
  Law R := ∀ n k (u : Vertex n), k < birth n u → R.readout () (n,k) u ≤ 3 * 2 ^ (n-k-1)
private def late_oriented_indegree_le_rejected : Realization cutoffSignature :=
  realize cutoffSignature (fun _ _ _ => 4) (fun e => nomatch e)
private theorem late_oriented_indegree_le_reject : ¬ late_oriented_indegree_le_arena.Law late_oriented_indegree_le_rejected := by
  intro h
  have hh : (4 : ℕ) ≤ 3 := h 1 0 (Sum.inr (0 : Face 0)) (by decide)
  omega
def late_oriented_indegree_le_family : Registration late_oriented_indegree_le_arena (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.late_oriented_indegree_le)) where
  actual := late_oriented_indegree_le_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.late_oriented_indegree_le, late_oriented_indegree_le_rejected, late_oriented_indegree_le_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ late_oriented_indegree_le_actual late_oriented_indegree_le_rejected late_oriented_indegree_le_reject
  dependence := by
    intro i
    cases i
    refine ⟨(1,0), Sum.inl (0 : Vertex 0), Sum.inl (3 : Vertex 0), ?_⟩
    decide
def registration_late_oriented_indegree_le : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.late_oriented_indegree_le)
    (Realization cutoffSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.late_oriented_indegree_le_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.late_oriented_indegree_le_family
  realizationSource := none
  generated := false
  arena := .source ⟨late_oriented_indegree_le_arena⟩
  objectArena := .source ⟨late_oriented_indegree_le_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source late_oriented_indegree_le_arena ⟨late_oriented_indegree_le_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cutoffSignature (fun _ p u => ∑ v : Vertex p.1, if p.2 < birth p.1 v ∧ Oriented p.1 v u then 1 else 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[0,1]
    readouts := #[{ path := #["body","body","body","body","fn","arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev adjacent_embed_actual : Realization adjacencySignature :=
  realize adjacencySignature (fun _ p v => adjacent (p.n+p.t) (embed p.n p.t p.u) (embed p.n p.t v)) (fun e => nomatch e)
abbrev adjacent_embed_arena : Arena where
  signature := adjacencySignature
  Law R := ∀ n t (u v : Vertex n), R.readout () ⟨n,t,u⟩ v ↔ adjacent n u v
private def adjacent_embed_rejected : Realization adjacencySignature :=
  realize adjacencySignature (fun _ _ _ => False) (fun e => nomatch e)
private theorem adjacent_embed_reject : ¬ adjacent_embed_arena.Law adjacent_embed_rejected := by
  intro h
  exact (h 0 0 (0 : Vertex 0) (1 : Vertex 0)).mpr (by decide)
def adjacent_embed_family : Registration adjacent_embed_arena (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.adjacent_embed)) where
  actual := adjacent_embed_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.adjacent_embed, adjacent_embed_rejected, adjacent_embed_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ adjacent_embed_actual adjacent_embed_rejected adjacent_embed_reject
  dependence := by
    intro i
    cases i
    refine ⟨⟨0,0,(0 : Vertex 0)⟩, (0 : Vertex 0), (1 : Vertex 0), ?_⟩
    intro he
    have ht : (adjacent (0+0) (embed 0 0 (0 : Vertex 0)) (embed 0 0 (1 : Vertex 0))) := by decide
    exact (Eq.mp he.symm ht) rfl
def registration_adjacent_embed : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.adjacent_embed)
    (Realization adjacencySignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.adjacent_embed_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.adjacent_embed_family
  realizationSource := none
  generated := false
  arena := .source ⟨adjacent_embed_arena⟩
  objectArena := .source ⟨adjacent_embed_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source adjacent_embed_arena ⟨adjacent_embed_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize adjacencySignature (fun _ p v => adjacent (p.n+p.t) (embed p.n p.t p.u) (embed p.n p.t v)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{ path := #["body","body","body","body","fn","arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev old_vertices_iff_actual : Realization oldSignature :=
  realize oldSignature (fun _ p w => birth (p.1+p.2) w) (fun e => nomatch e)
abbrev old_vertices_iff_arena : Arena where
  signature := oldSignature
  Law R := ∀ k t (w : Vertex (k+t)), R.readout () (k,t) w ≤ k ↔ ∃ u : Vertex k, embed k t u = w
private def old_vertices_iff_rejected : Realization oldSignature :=
  realize oldSignature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem old_vertices_iff_reject : ¬ old_vertices_iff_arena.Law old_vertices_iff_rejected := by
  intro h
  obtain ⟨u, hu⟩ := (h 0 1 (Sum.inr (0 : Face 0))).mp (by decide)
  simp [embed] at hu
def old_vertices_iff_family : Registration old_vertices_iff_arena (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.old_vertices_iff)) where
  actual := old_vertices_iff_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.old_vertices_iff, old_vertices_iff_rejected, old_vertices_iff_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ old_vertices_iff_actual old_vertices_iff_rejected old_vertices_iff_reject
  dependence := by
    intro i
    cases i
    refine ⟨(0,1), Sum.inl (0 : Vertex 0), Sum.inr (0 : Face 0), ?_⟩
    decide
def registration_old_vertices_iff : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.old_vertices_iff)
    (Realization oldSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.old_vertices_iff_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.old_vertices_iff_family
  realizationSource := none
  generated := false
  arena := .source ⟨old_vertices_iff_arena⟩
  objectArena := .source ⟨old_vertices_iff_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source old_vertices_iff_arena ⟨old_vertices_iff_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize oldSignature (fun _ p w => birth (p.1+p.2) w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[0,1]
    readouts := #[{ path := #["body","body","body","fn","arg","fn","arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev late_edge_oriented_actual : Realization adjacencySignature :=
  realize adjacencySignature (fun _ p v => Oriented p.n p.u v) (fun e => nomatch e)
abbrev late_edge_oriented_arena : Arena where
  signature := adjacencySignature
  Law R := ∀ n k (u v : Vertex n), k < birth n u → k < birth n v → adjacent n u v → R.readout () ⟨n,k,u⟩ v ∨ Oriented n v u
private def late_edge_oriented_rejected : Realization adjacencySignature :=
  realize adjacencySignature (fun _ _ _ => False) (fun e => nomatch e)
private theorem late_edge_oriented_reject : ¬ late_edge_oriented_arena.Law late_edge_oriented_rejected := by
  intro h
  have hh := h 2 0 (Sum.inr ((0 : Face 0), (0 : Fin 3)))
    (Sum.inl (Sum.inr (0 : Face 0))) (by decide) (by decide) (by decide)
  rcases hh with hh | hh
  · exact hh
  · exact (by decide : ¬ Oriented 2 (Sum.inl (Sum.inr (0 : Face 0)))
      (Sum.inr ((0 : Face 0), (0 : Fin 3)))) hh
def late_edge_oriented_family : Registration late_edge_oriented_arena (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.late_edge_oriented)) where
  actual := late_edge_oriented_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.late_edge_oriented, late_edge_oriented_rejected, late_edge_oriented_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ late_edge_oriented_actual late_edge_oriented_rejected late_edge_oriented_reject
  dependence := by
    intro i
    cases i
    refine ⟨⟨1,0,Sum.inr (0 : Face 0)⟩, Sum.inl (0 : Vertex 0), Sum.inr (0 : Face 0), ?_⟩
    intro he
    have ht : Oriented 1 (Sum.inr (0 : Face 0)) (Sum.inl (0 : Vertex 0)) := by decide
    have hf : ¬ Oriented 1 (Sum.inr (0 : Face 0)) (Sum.inr (0 : Face 0)) := by decide
    exact hf (Eq.mp he ht)
def registration_late_edge_oriented : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.late_edge_oriented)
    (Realization adjacencySignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.late_edge_oriented_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.late_edge_oriented_family
  realizationSource := none
  generated := false
  arena := .source ⟨late_edge_oriented_arena⟩
  objectArena := .source ⟨late_edge_oriented_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source late_edge_oriented_arena ⟨late_edge_oriented_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize adjacencySignature (fun _ p v => Oriented p.n p.u v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{ path := #["body","body","body","body","body","body","body","fn","arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev inner_faces_distinct_actual : Realization faceSignature :=
  realize faceSignature (fun _ p v => Incident p.1 p.2 v) (fun e => nomatch e)
abbrev inner_faces_distinct_arena : Arena where
  signature := faceSignature
  Law R := ∀ n (f g : Face n), (∀ v, R.readout () ⟨n,f⟩ v ↔ Incident n g v) → f = g
private def inner_faces_distinct_rejected : Realization faceSignature :=
  realize faceSignature (fun _ p v => Incident p.1 (firstFace p.1) v) (fun e => nomatch e)
private theorem inner_faces_distinct_reject : ¬ inner_faces_distinct_arena.Law inner_faces_distinct_rejected := by
  intro h
  have hh : (1 : Face 0) = 0 := h 0 1 0 (by intro v; rfl)
  exact (by decide : (1 : Face 0) ≠ 0) hh
def inner_faces_distinct_family : Registration inner_faces_distinct_arena (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.inner_faces_distinct)) where
  actual := inner_faces_distinct_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.inner_faces_distinct, inner_faces_distinct_rejected, inner_faces_distinct_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ inner_faces_distinct_actual inner_faces_distinct_rejected inner_faces_distinct_reject
  dependence := by
    intro i
    cases i
    refine ⟨⟨0,(0 : Face 0)⟩, (3 : Vertex 0), (2 : Vertex 0), ?_⟩
    intro he
    have ht : Incident 0 (0 : Face 0) (3 : Vertex 0) := by decide
    have hf : ¬ Incident 0 (0 : Face 0) (2 : Vertex 0) := by decide
    exact hf (Eq.mp he ht)
def registration_inner_faces_distinct : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.inner_faces_distinct)
    (Realization faceSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.inner_faces_distinct_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.inner_faces_distinct_family
  realizationSource := none
  generated := false
  arena := .source ⟨inner_faces_distinct_arena⟩
  objectArena := .source ⟨inner_faces_distinct_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source inner_faces_distinct_arena ⟨inner_faces_distinct_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize faceSignature (fun _ p v => Incident p.1 p.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[0,1]
    readouts := #[{ path := #["body","body","body","domain","body","fn","arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev cutoff_gram_diag_actual : Realization diagonalSignature :=
  realize diagonalSignature (fun _ p u => (cutoffBlock p.1 p.2 * (cutoffBlock p.1 p.2).transpose) u u) (fun e => nomatch e)
abbrev cutoff_gram_diag_arena : Arena where
  signature := diagonalSignature
  Law R := ∀ k t (u : Vertex k), R.readout () (k,t) u = (((graph (k+t)).degree (embed k t u) - (graph k).degree u : ℕ) : ℝ)
private def cutoff_gram_diag_rejected : Realization diagonalSignature :=
  realize diagonalSignature (fun _ _ _ => -1) (fun e => nomatch e)
private theorem cutoff_gram_diag_reject : ¬ cutoff_gram_diag_arena.Law cutoff_gram_diag_rejected := by
  intro h
  have hh := h 0 0 (0 : Vertex 0)
  have hn : (0 : ℝ) ≤ (((graph (0+0)).degree (embed 0 0 (0 : Vertex 0)) -
    (graph 0).degree (0 : Vertex 0) : ℕ) : ℝ) := Nat.cast_nonneg _
  change (-1 : ℝ) = _ at hh
  rw [← hh] at hn
  norm_num at hn
def cutoff_gram_diag_family : Registration cutoff_gram_diag_arena (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.cutoff_gram_diag)) where
  actual := cutoff_gram_diag_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.cutoff_gram_diag, cutoff_gram_diag_rejected, cutoff_gram_diag_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ cutoff_gram_diag_actual cutoff_gram_diag_rejected cutoff_gram_diag_reject
  dependence := by
    intro i
    cases i
    refine ⟨(0,1), (0 : Vertex 0), (3 : Vertex 0), ?_⟩
    change (cutoffBlock 0 1 * (cutoffBlock 0 1).transpose) 0 0 ≠
      (cutoffBlock 0 1 * (cutoffBlock 0 1).transpose) 3 3
    rw [cutoff_gram_diag, cutoff_gram_diag]
    rw [← degreeCount_eq_degree, ← degreeCount_eq_degree,
      ← degreeCount_eq_degree, ← degreeCount_eq_degree]
    change (2 : ℝ) ≠ 3
    norm_num
def registration_cutoff_gram_diag : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.cutoff_gram_diag)
    (Realization diagonalSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.cutoff_gram_diag_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.cutoff_gram_diag_family
  realizationSource := none
  generated := false
  arena := .source ⟨cutoff_gram_diag_arena⟩
  objectArena := .source ⟨cutoff_gram_diag_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source cutoff_gram_diag_arena ⟨cutoff_gram_diag_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize diagonalSignature (fun _ p u => (cutoffBlock p.1 p.2 * (cutoffBlock p.1 p.2).transpose) u u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[0,1]
    readouts := #[{ path := #["body","body","body","fn","arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev cutoff_gram_offdiag_actual : Realization gramSignature :=
  realize gramSignature (fun _ p v => (cutoffBlock p.n p.t * (cutoffBlock p.n p.t).transpose) p.u v) (fun e => nomatch e)
abbrev cutoff_gram_offdiag_arena : Arena where
  signature := gramSignature
  Law R := ∀ k t (u v : Vertex k), u ≠ v → 0 ≤ R.readout () ⟨k,t,u⟩ v ∧ R.readout () ⟨k,t,u⟩ v ≤ 2 * (t : ℝ) ∧ (¬ adjacent k u v → R.readout () ⟨k,t,u⟩ v = 0)
private def cutoff_gram_offdiag_rejected : Realization gramSignature :=
  realize gramSignature (fun _ _ _ => -1) (fun e => nomatch e)
private theorem cutoff_gram_offdiag_reject : ¬ cutoff_gram_offdiag_arena.Law cutoff_gram_offdiag_rejected := by
  intro h
  have hh : (0 : ℝ) ≤ -1 := (h 0 0 (0 : Vertex 0) (1 : Vertex 0) (by decide)).1
  norm_num at hh
def cutoff_gram_offdiag_family : Registration cutoff_gram_offdiag_arena (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.cutoff_gram_offdiag)) where
  actual := cutoff_gram_offdiag_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.cutoff_gram_offdiag, cutoff_gram_offdiag_rejected, cutoff_gram_offdiag_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ cutoff_gram_offdiag_actual cutoff_gram_offdiag_rejected cutoff_gram_offdiag_reject
  dependence := by
    intro i
    cases i
    let u : Vertex 1 := Sum.inr (0 : Face 0)
    let v : Vertex 1 := Sum.inr (1 : Face 0)
    refine ⟨⟨1,1,u⟩, u, v, ?_⟩
    change (cutoffBlock 1 1 * (cutoffBlock 1 1).transpose) u u ≠
      (cutoffBlock 1 1 * (cutoffBlock 1 1).transpose) u v
    have hz := (cutoff_gram_offdiag 1 1 u v (by decide)).2.2 (by decide)
    rw [hz, cutoff_gram_diag]
    have hd1 : (graph 1).degree u = 3 :=
      (degreeCount_eq_degree 1 u).symm.trans (by
        simpa [u, birth] using degreeCount_inner 1 u (by decide))
    have hd2 : (graph 2).degree (Sum.inl u) = 6 :=
      (degreeCount_eq_degree 2 (Sum.inl u)).symm.trans (by
        simpa [u, birth] using degreeCount_inner 2 (Sum.inl u) (by decide))
    change (((graph 2).degree (Sum.inl u) - (graph 1).degree u : ℕ) : ℝ) ≠ 0
    rw [hd1, hd2]
    norm_num

def registration_cutoff_gram_offdiag : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.cutoff_gram_offdiag)
    (Realization gramSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.cutoff_gram_offdiag_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.cutoff_gram_offdiag_family
  realizationSource := none
  generated := false
  arena := .source ⟨cutoff_gram_offdiag_arena⟩
  objectArena := .source ⟨cutoff_gram_offdiag_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source cutoff_gram_offdiag_arena ⟨cutoff_gram_offdiag_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gramSignature (fun _ p v => (cutoffBlock p.n p.t * (cutoffBlock p.n p.t).transpose) p.u v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{ path := #["body","body","body","body","body","fn","arg","arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false },{ path := #["body","body","body","body","body","arg","fn","arg","fn","arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false },{ path := #["body","body","body","body","body","arg","arg","body","fn","arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

structure CutoffParameters where
  k : ℕ
  t : ℕ
  u : Vertex k ⊕ LateVertex k t
abbrev cutoffAdjacencySignature : Signature :=
  Reg.Support.SingleDependentReadout.signature CutoffParameters
    (fun p => Vertex p.k ⊕ LateVertex p.k p.t) (fun _ => ℝ)
abbrev cutoff_adjacency_actual : Realization cutoffAdjacencySignature :=
  realize cutoffAdjacencySignature
    (fun _ p v => adjacency (p.k + p.t) (cutoffEquiv p.k p.t p.u) (cutoffEquiv p.k p.t v))
    (fun e => nomatch e)
abbrev cutoff_adjacency_arena : Arena where
  signature := cutoffAdjacencySignature
  Law R := ∀ k t (u v : Vertex k ⊕ LateVertex k t), R.readout () ⟨k,t,u⟩ v =
    Matrix.fromBlocks (adjacency k) (cutoffBlock k t) (cutoffBlock k t).transpose
      (lateAdjacency k t) u v
private def cutoff_adjacency_rejected : Realization cutoffAdjacencySignature :=
  realize cutoffAdjacencySignature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem cutoff_adjacency_reject :
    ¬ cutoff_adjacency_arena.Law cutoff_adjacency_rejected := by
  intro h
  have hh : (0 : ℝ) = 1 := h 0 0 (Sum.inl (0 : Vertex 0)) (Sum.inl (1 : Vertex 0))
  norm_num at hh
def cutoff_adjacency_family : Registration cutoff_adjacency_arena
    (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.cutoff_adjacency)) where
  actual := cutoff_adjacency_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.cutoff_adjacency,
    cutoff_adjacency_rejected, cutoff_adjacency_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _
    cutoff_adjacency_actual cutoff_adjacency_rejected cutoff_adjacency_reject
  dependence := by
    intro i
    cases i
    refine ⟨⟨0,0,Sum.inl (0 : Vertex 0)⟩, Sum.inl (0 : Vertex 0),
      Sum.inl (1 : Vertex 0), ?_⟩
    change (0 : ℝ) ≠ 1
    norm_num
def registration_cutoff_adjacency : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.cutoff_adjacency)
    (Realization cutoffAdjacencySignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.cutoff_adjacency_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.cutoff_adjacency_family
  realizationSource := none
  generated := false
  arena := .source ⟨cutoff_adjacency_arena⟩
  objectArena := .source ⟨cutoff_adjacency_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source cutoff_adjacency_arena ⟨cutoff_adjacency_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cutoffAdjacencySignature
    (fun _ p v => adjacency (p.k + p.t) (cutoffEquiv p.k p.t p.u) (cutoffEquiv p.k p.t v))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","fn","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev seedMapSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => Fin 4) Vertex

abbrev faceCount_old_actual : Realization stageSignature :=
  realize stageSignature (fun _ n v => faceCount (n+1) (Sum.inl v)) (fun e => nomatch e)
abbrev faceCount_old_arena : Arena where
  signature := stageSignature
  Law R := ∀ n (v : Vertex n), R.readout () n v = 2 * faceCount n v
private def faceCount_old_rejected : Realization stageSignature :=
  realize stageSignature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem faceCount_old_reject : ¬ faceCount_old_arena.Law faceCount_old_rejected := by
  intro h
  have hh : (0 : ℕ) = 4 := h 0 0
  omega
def faceCount_old_family : Registration faceCount_old_arena
    (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.faceCount_old)) where
  actual := faceCount_old_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.faceCount_old,
    faceCount_old_rejected, faceCount_old_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ faceCount_old_reject
  dependence := by
    intro i
    cases i
    refine ⟨0, 0, 3, ?_⟩
    decide
def registration_faceCount_old : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.faceCount_old)
    (Realization stageSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.faceCount_old_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.faceCount_old_family
  realizationSource := none
  generated := false
  arena := .source ⟨faceCount_old_arena⟩
  objectArena := .source ⟨faceCount_old_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source faceCount_old_arena ⟨faceCount_old_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize stageSignature (fun _ n v => faceCount (n+1) (Sum.inl v)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body","body","fn","arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev degreeCount_old_actual : Realization stageSignature :=
  realize stageSignature (fun _ n v => degreeCount (n+1) (Sum.inl v)) (fun e => nomatch e)
abbrev degreeCount_old_arena : Arena where
  signature := stageSignature
  Law R := ∀ n (v : Vertex n), R.readout () n v = degreeCount n v + faceCount n v
private def degreeCount_old_rejected : Realization stageSignature :=
  realize stageSignature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem degreeCount_old_reject : ¬ degreeCount_old_arena.Law degreeCount_old_rejected := by
  intro h
  have hh : (0 : ℕ) = 5 := h 0 0
  omega
def degreeCount_old_family : Registration degreeCount_old_arena
    (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_old)) where
  actual := degreeCount_old_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_old,
    degreeCount_old_rejected, degreeCount_old_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ degreeCount_old_reject
  dependence := by
    intro i
    cases i
    refine ⟨0, 0, 3, ?_⟩
    decide
def registration_degreeCount_old : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_old)
    (Realization stageSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_old_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.degreeCount_old_family
  realizationSource := none
  generated := false
  arena := .source ⟨degreeCount_old_arena⟩
  objectArena := .source ⟨degreeCount_old_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source degreeCount_old_arena ⟨degreeCount_old_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize stageSignature (fun _ n v => degreeCount (n+1) (Sum.inl v)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body","body","fn","arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev seed_injective_actual : Realization seedMapSignature :=
  realize seedMapSignature (fun _ n v => seed n v) (fun e => nomatch e)
abbrev seed_injective_arena : Arena where
  signature := seedMapSignature
  Law R := ∀ n, Function.Injective (R.readout () n)
private def seed_injective_rejected : Realization seedMapSignature :=
  realize seedMapSignature (fun _ n _ => seed n 0) (fun e => nomatch e)
private theorem seed_injective_reject : ¬ seed_injective_arena.Law seed_injective_rejected := by
  intro h
  have hh : (0 : Fin 4) = 1 := h 0 (show seed 0 0 = seed 0 0 from rfl)
  exact (by decide : (0 : Fin 4) ≠ 1) hh
def seed_injective_family : Registration seed_injective_arena
    (type_of% (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.seed_injective)) where
  actual := seed_injective_actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.seed_injective,
    seed_injective_rejected, seed_injective_reject⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ seed_injective_reject
  dependence := by
    intro i
    cases i
    refine ⟨0, 0, 1, ?_⟩
    decide
def registration_seed_injective : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Apollonian.InnerFaceStages.seed_injective)
    (Realization seedMapSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.seed_injective_unit
  realizationName := `Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages.seed_injective_family
  realizationSource := none
  generated := false
  arena := .source ⟨seed_injective_arena⟩
  objectArena := .source ⟨seed_injective_arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source seed_injective_arena ⟨seed_injective_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize seedMapSignature (fun _ n v => seed n v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Apollonian.InnerFaceStages
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body","arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Apollonian.InnerFaceStages
