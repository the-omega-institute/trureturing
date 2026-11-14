import D5.S3.Combinatorics.TraceAvoidingArrays.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact readout families for arbitrary bond-defect transfers. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.DefectTransfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.DefectTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section

namespace Relabel
structure Params where
  q k : ℕ
  H V : Finset (Fin k × Fin k)
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Params
    (fun p => List (Row p.q p.k)) (fun _ => ℕ)
def readout : Realization signature :=
  realize signature (fun _ p rs => defects p.H p.V rs) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p rs => defects p.H p.V rs +
    (rs.map fun r => ∑ i, (r i).val).sum) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Params) (e : Equiv.Perm (Fin p.q)) (rs : List (Row p.q p.k)),
    R.readout () p (rs.map fun r => e ∘ r) = R.readout () p rs
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h ⟨2, 1, ∅, ∅⟩ (Equiv.swap 0 1) [fun _ => 0]
  norm_num [rejected, realize, defects, tailDefects, bondDefects, Fin.sum_univ_one] at hh
def family : Registration arena (type_of% @relabel_defects) where
  actual := readout
  bridge := by
    constructor
    · intro h p e rs; exact h p.H p.V e rs
    · intro h q k H V e rs; exact h ⟨q, k, H, V⟩ e rs
  variation := ⟨fun p e rs => relabel_defects p.H p.V e rs, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨1, 1, {(0, 0)}, ∅⟩, [], [fun _ => 0], ?_⟩
    decide +kernel


def audit : Contract.Registration.{_, _, _, _, _, _, _, _, _, _, _, _}
    (@relabel_defects) (Realization signature) Type Unit where
  unitName := `Reg.ADefectTransfer.Relabel.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some readout
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.DefectTransfer
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Relabel

namespace Constant
structure Params where
  q k : ℕ
  H V : Finset (Fin k × Fin k)
  c : Fin q
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Params (fun _ => ℕ) (fun _ => ℕ)
def readout : Realization signature :=
  realize signature (fun _ p n => defects p.H p.V (List.replicate (n + 1) (fun _ => p.c)))
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p n => defects p.H p.V (List.replicate (n + 1) (fun _ => p.c)) + 1)
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Params) (n : ℕ),
    R.readout () p n = p.H.card + n * (p.V.card + p.H.card)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h ⟨1, 1, ∅, ∅, 0⟩ 0
  norm_num [rejected, realize, defects, tailDefects, bondDefects] at hh
def family : Registration arena (type_of% @constant_defects) where
  actual := readout
  bridge := by
    constructor
    · intro h p n; exact h p.H p.V p.c n
    · intro h q k H V c n; exact h ⟨q, k, H, V, c⟩ n
  variation := ⟨fun p n => constant_defects p.H p.V p.c n, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨1, 1, {(0, 0)}, ∅, 0⟩, 0, 1, ?_⟩
    decide +kernel


def audit : Contract.Registration.{_, _, _, _, _, _, _, _, _, _, _, _}
    (@constant_defects) (Realization signature) Type Unit where
  unitName := `Reg.ADefectTransfer.Constant.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some readout
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.DefectTransfer
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Constant

universe u v

namespace Lumped
structure Params where
  q k : ℕ
  B : Type u
  S : Type v
  finite : Fintype S
  equality : DecidableEq S
  H V : Finset (Fin k × Fin k)
  P : Row q k → B
  C : B → Row q k → ℕ
  Valid : B → ℕ → Prop
  cl : B → ℕ → S
  T : Matrix S S ℤ
  initial terminal : S → ℤ
  D : ℕ
abbrev signature : Signature where
  Params := Params.{u,v}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance
def readout : Realization signature :=
  realize signature (fun _ p n => (literalCount (q := p.q) p.H p.V p.D (n + 1) : ℤ))
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p n => (literalCount (q := p.q) p.H p.V p.D (n + 1) : ℤ) + 1)
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p : Params,
    letI := p.finite
    letI := p.equality
    (∀ r t, bondDefects p.V r t = p.C (p.P r) t) →
    (∀ z d, p.Valid z d → p.terminal (p.cl z d) = if d = 0 then 1 else 0) →
    (∀ z d, p.Valid z d → ∀ r, p.C z r + bondDefects p.H r r ≤ d →
      p.Valid (p.P r) (d - (p.C z r + bondDefects p.H r r))) →
    (∀ z d, p.Valid z d → ∀ s,
      (∑ r : Row p.q p.k, if p.C z r + bondDefects p.H r r ≤ d ∧
        p.cl (p.P r) (d - (p.C z r + bondDefects p.H r r)) = s then (1 : ℤ) else 0) =
        p.T (p.cl z d) s) →
    (∀ r, bondDefects p.H r r ≤ p.D → p.Valid (p.P r) (p.D - bondDefects p.H r r)) →
    (∀ s, (∑ r : Row p.q p.k, if bondDefects p.H r r ≤ p.D ∧
      p.cl (p.P r) (p.D - bondDefects p.H r r) = s then (1 : ℤ) else 0) = p.initial s) →
    ∀ n, R.readout () p n = dotProduct p.initial ((p.T ^ n).mulVec p.terminal)
def sample : Params.{u,v} where
  q := 2
  k := 1
  B := ULift Unit
  S := ULift (Fin 1)
  finite := inferInstance
  equality := inferInstance
  H := ∅
  V := ∅
  P _ := ⟨()⟩
  C _ _ := 0
  Valid _ d := d = 0
  cl _ _ := ⟨0⟩
  T _ _ := 2
  initial _ := 2
  terminal _ := 1
  D := 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h sample
    (by intro r t; rfl)
    (by intro p d hd; simp_all [sample])
    (by intro p d hd r hr; simpa [sample] using hd)
    (by intro p d hd s; subst d; simp [sample, bondDefects, Fin.sum_univ_succ])
    (by intro r hr; rfl)
    (by intro s; simp [sample, bondDefects, Fin.sum_univ_succ]) 0
  norm_num [rejected, realize, sample, literalCount, defects, tailDefects,
    bondDefects, Matrix.mulVec, dotProduct] at hh
def family : Registration arena (type_of% @lumped_count.{u,v}) where
  actual := readout
  bridge := by
    constructor
    · intro h p edge hz hn ht hi hv n
      exact @h p.q p.k p.B p.H p.V p.P p.C p.S p.finite p.equality
        p.Valid p.cl p.T p.initial p.terminal p.D edge hz hn ht hi hv n
    · intro h q k B H V P C S fs ds valid cl T ini term D edge hz hn ht hi hv n
      exact h ⟨q, k, B, S, fs, ds, H, V, P, C, valid, cl, T, ini, term, D⟩
        edge hz hn ht hi hv n
  variation := ⟨fun p edge hz hn ht hi hv n =>
    @lumped_count p.q p.k p.B p.H p.V p.P p.C p.S p.finite p.equality
      p.Valid p.cl p.T p.initial p.terminal p.D edge hz hn ht hi hv n,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨sample, 0, 1, ?_⟩
    change (literalCount (q := 2) ∅ ∅ 0 1 : ℤ) ≠ literalCount (q := 2) ∅ ∅ 0 2
    decide +kernel

def audit : Contract.Registration.{_, _, _, _, _, _, _, _, _, _, _, _}
    (@lumped_count) (Realization signature) Type Unit where
  unitName := `Reg.ADefectTransfer.Lumped.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some readout
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.DefectTransfer
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 23
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Lumped

namespace Shift
structure Params where
  S : Type u
  finite : Fintype S
  equality : DecidableEq S
  T : Matrix S S ℤ
  initial terminal : S → ℤ
  d b : ℕ
  c : Fin d → ℤ
abbrev signature : Signature where
  Params := Params.{u}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance
def readout : Realization signature :=
  realize signature (fun _ p n => letI := p.finite
    dotProduct p.initial ((p.T ^ n).mulVec p.terminal)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p n => letI := p.finite
    dotProduct p.initial ((p.T ^ n).mulVec p.terminal) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p : Params,
    letI := p.finite
    letI := p.equality
    forward p.T p.initial (p.b + p.d) =
      ∑ j : Fin p.d, p.c j • forward p.T p.initial (p.b + j.val) →
    ∀ n, R.readout () p (n + p.b + p.d) =
      ∑ j : Fin p.d, p.c j * R.readout () p (n + p.b + j.val)
def sample : Params.{u} where
  S := ULift (Fin 1)
  finite := inferInstance
  equality := inferInstance
  T _ _ := 2
  initial _ := 1
  terminal _ := 1
  d := 1
  b := 0
  c _ := 2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h sample
    (by ext s; simp [sample, forward, Matrix.vecMul, dotProduct]) 0
  norm_num [sample, rejected, realize, Matrix.mulVec, dotProduct, Fin.sum_univ_one] at hh
def family : Registration arena (type_of% @forward_shift.{u}) where
  actual := readout
  bridge := by
    constructor
    · intro h p hp n
      exact @h p.S p.finite p.equality p.T p.initial p.terminal p.d p.b p.c hp n
    · intro h S fs ds T ini term d b c hp n
      exact h ⟨S, fs, ds, T, ini, term, d, b, c⟩ hp n
  variation := ⟨fun p hp n =>
    @forward_shift p.S p.finite p.equality p.T p.initial p.terminal p.d p.b p.c hp n,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨sample, 0, 1, ?_⟩
    simp [sample, readout, realize, Matrix.mulVec, dotProduct]

def audit : Contract.Registration.{_, _, _, _, _, _, _, _, _, _, _, _}
    (@forward_shift) (Realization signature) Type Unit where
  unitName := `Reg.ADefectTransfer.Shift.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some readout
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.DefectTransfer
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Shift

end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.DefectTransfer
