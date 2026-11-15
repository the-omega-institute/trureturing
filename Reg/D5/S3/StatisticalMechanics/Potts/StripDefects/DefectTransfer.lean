import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact readout families for arbitrary bond-defect transfers. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section

namespace Relabel
structure Params where
  q : ℕ
  k : ℕ
  H : Finset (Fin k × Fin k)
  V : Finset (Fin k × Fin k)
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
    intro ⟨⟩
    refine ⟨⟨1, 1, {(0, 0)}, ∅⟩, [], [fun _ => 0], ?_⟩
    decide +kernel


def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
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
  q : ℕ
  k : ℕ
  H : Finset (Fin k × Fin k)
  V : Finset (Fin k × Fin k)
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
    intro ⟨⟩
    refine ⟨⟨1, 1, {(0, 0)}, ∅, 0⟩, 0, 1, ?_⟩
    decide +kernel


def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
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
  q : ℕ
  k : ℕ
  B : Type u
  S : Type v
  finite : Fintype S
  equality : DecidableEq S
  H : Finset (Fin k × Fin k)
  V : Finset (Fin k × Fin k)
  P : Row q k → B
  C : B → Row q k → ℕ
  Valid : B → ℕ → Prop
  cl : B → ℕ → S
  T : Matrix S S ℤ
  initial : S → ℤ
  terminal : S → ℤ
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
private theorem actual_law : arena.Law readout := by
  intro p edge hz hn ht hi hv n
  exact @lumped_count p.q p.k p.B p.H p.V p.P p.C p.S p.finite p.equality
    p.Valid p.cl p.T p.initial p.terminal p.D edge hz hn ht hi hv n
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
  have check (R : Realization signature) (hR : arena.Law R) := hR sample
    (by intro r t; rfl)
    (by intro p d hd; simp_all [sample])
    (by
      intro p d hd r hr
      change d = 0 at hd
      change d - _ = 0
      rw [hd, Nat.zero_sub])
    (by
      intro p d hd s
      subst d
      have hs : s = ⟨0⟩ := by
        apply ULift.ext
        exact Fin.eq_zero _
      subst s
      change (∑ _ : Fin 1 → Fin 2, (1 : ℤ)) = 2
      norm_num)
    (by intro r hr; rfl)
    (by
      intro s
      have hs : s = ⟨0⟩ := by
        apply ULift.ext
        exact Fin.eq_zero _
      subst s
      change (∑ _ : Fin 1 → Fin 2, (1 : ℤ)) = 2
      norm_num) 0
  have hb := check rejected h
  have ha := check readout actual_law
  simp only [rejected, readout, realize] at hb ha
  linarith

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
    intro ⟨⟩
    refine ⟨sample, 0, 1, ?_⟩
    change (literalCount (q := 2) ∅ ∅ 0 1 : ℤ) ≠ literalCount (q := 2) ∅ ∅ 0 2
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@lumped_count.{u,v}) (Realization signature.{u,v}) Type Unit where
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 22
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
  initial : S → ℤ
  terminal : S → ℤ
  d : ℕ
  b : ℕ
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
    letI := p.equality
    dotProduct p.initial ((p.T ^ n).mulVec p.terminal)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p n => letI := p.finite
    letI := p.equality
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
private theorem actual_law : arena.Law readout := by
  intro p hp n
  exact @forward_shift p.S p.finite p.equality p.T p.initial p.terminal p.d p.b p.c hp n
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
private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  letI := sample.{u}.finite
  letI := sample.{u}.equality
  have hp : forward sample.{u}.T sample.{u}.initial (sample.{u}.b + sample.{u}.d) =
      ∑ j : Fin sample.{u}.d, sample.{u}.c j • forward sample.{u}.T sample.{u}.initial (sample.{u}.b + j.val) := by
    ext s
    change (∑ _ : ULift (Fin 1), (1 : ℤ) * 2) = (2 : ℤ) * 1
    norm_num
  have hb := h sample.{u} hp 0
  have ha := actual_law sample.{u} hp 0
  simp only [rejected, readout, realize] at hb ha
  have hc : (∑ j : Fin sample.{u}.d, sample.{u}.c j) = 2 := by decide +kernel
  simp_rw [mul_add, mul_one] at hb
  rw [Finset.sum_add_distrib, hc] at hb
  linarith

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
    intro ⟨⟩
    refine ⟨sample, 0, 1, ?_⟩
    letI := sample.finite
    letI := sample.equality
    change (∑ _ : ULift.{u} (Fin 1), (1 : ℤ)) ≠ ∑ _ : ULift.{u} (Fin 1), (2 : ℤ)
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@forward_shift.{u}) (Realization signature.{u}) Type Unit where
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Shift

namespace ForwardEq
structure Params where
  S : Type u
  finite : Fintype S
  equality : DecidableEq S
  T : Matrix S S ℤ
  initial : S → ℤ
abbrev signature : Signature where
  Params := Params.{u}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.S → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance
def readout : Realization signature :=
  realize signature (fun _ p n => letI := p.finite; forward p.T p.initial n)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p n s => letI := p.finite; forward p.T p.initial n s + 1)
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Params) (n : ℕ),
    letI := p.finite
    letI := p.equality
    R.readout () p n = Matrix.vecMul p.initial (p.T ^ n)
def sample : Params.{u} where
  S := ULift (Fin 1)
  finite := inferInstance
  equality := inferInstance
  T _ _ := 2
  initial _ := 1
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI := sample.finite
  letI := sample.equality
  have hh := h sample 0
  change (fun s => forward sample.T sample.initial 0 s + 1) = _ at hh
  rw [← forward_eq] at hh
  have hh' := congrFun hh ⟨0⟩
  linarith
def family : Registration arena (type_of% @forward_eq.{u}) where
  actual := readout
  bridge := by
    constructor
    · intro h p n; exact @h p.S p.finite p.equality p.T p.initial n
    · intro h S fs ds T ini n; exact h ⟨S, fs, ds, T, ini⟩ n
  variation := ⟨fun p n => @forward_eq p.S p.finite p.equality p.T p.initial n,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h; exact (h (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro ⟨⟩
    refine ⟨sample, 0, 1, ?_⟩
    letI := sample.finite
    intro h
    have hh := congrFun h ⟨0⟩
    change (1 : ℤ) = ∑ _ : ULift (Fin 1), (1 : ℤ) * 2 at hh
    norm_num at hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@forward_eq.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.ADefectTransfer.ForwardEq.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
    definition := none
    coordinates := #[0,1,2,3,4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ForwardEq

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
