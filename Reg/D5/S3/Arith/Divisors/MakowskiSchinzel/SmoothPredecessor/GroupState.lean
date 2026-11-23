import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.GroupState
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit families for exact product and prefix statements. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.GroupState

open _root_.D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace step

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ × List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => fixedProduct x.1 x.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ts : List (ℕ × ℕ × ℕ)} {es : List ℕ}
    {st st' : List (ℕ × ℕ)} {i p j L : ℕ} {t : ℕ × ℕ × ℕ},
    stepTable ts es st = some st' → oddPrimes[i]? = some p →
    st[i]? = some (j, L) → ts[i]? = some t →
    st'[i]? = some (j + (groupValues i es).length,
      R.readout () () (L, groupValues i es)) ∧
    ∀ k < (groupValues i es).length,
      prefixOk p (j + k) (R.readout () () (L, (groupValues i es).take k)) t = true

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hh := (h (ts := [(0, 1, 0)]) (es := []) (st := [(0, 0)])
    (st' := [(0, 0)]) (i := 0) (p := 3) (j := 0) (L := 0) (t := (0, 1, 0))
    rfl (by decide) rfl rfl).1
  norm_num [rejected, realize, groupValues] at hh

def family : Registration arena (type_of% @stepTable_group) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@stepTable_group, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨(), (0, []), (1, []), ?_⟩
    norm_num [actual, realize, fixedProduct]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stepTable_group) (Realization signature) (ℕ → List ℕ → ℕ) Unit where
  unitName :=
    `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.stepTable_group.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.GroupState.step.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => fixedProduct x.1 x.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.GroupState
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end step

namespace rounding

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ × List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => fixedProduct x.1 x.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (L : ℕ) (qs : List ℕ),
    (R.readout () () (L, qs) : ℚ) ≤
      L * (qs.map (fun q : ℕ => ((q : ℚ) - 1) / q)).prod

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hh := h 0 []
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% @fixedProduct_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fixedProduct_le, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨(), (0, []), (1, []), ?_⟩
    norm_num [actual, realize, fixedProduct]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fixedProduct_le) (Realization signature) (ℕ → List ℕ → ℕ) Unit where
  unitName :=
    `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.fixedProduct_le.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.GroupState.rounding.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => fixedProduct x.1 x.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.GroupState
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end rounding

namespace prefixes

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ × ℕ × ℕ × (ℕ × ℕ × ℕ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => prefixOk x.1 x.2.1 x.2.2.1 x.2.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => x.2.1 != 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ts : List (ℕ × ℕ × ℕ)} {es : List ℕ}
    {st st' : List (ℕ × ℕ)} {i p j L : ℕ} {t : ℕ × ℕ × ℕ},
    stepTable ts es st = some st' → oddPrimes[i]? = some p →
    st[i]? = some (j, L) → ts[i]? = some t →
    ((∀ k ≤ (groupValues i es).length,
      R.readout () () (p, j + k, fixedProduct L ((groupValues i es).take k), t) = true) ↔
      R.readout () () (p, j + (groupValues i es).length,
        fixedProduct L (groupValues i es), t) = true)

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hr : stepTable [(0, 1, 0)] [1792] [(0, scale)] =
      some [(1, scale * 6 / 7)] := by decide +kernel
  have hh := h hr (i := 0) (p := 3) (j := 0) (L := scale) (t := (0, 1, 0))
    (by decide) rfl rfl
  have hall := hh.mpr (by decide)
  have hz := hall 0 (by decide)
  exact Bool.false_ne_true hz

def family : Registration arena (type_of% @stepTable_all_prefixes) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@stepTable_all_prefixes, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨(), (3, 0, scale, (0, 1, 0)), (3, 1, 0, (0, 1, 0)), ?_⟩
    decide +kernel

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stepTable_all_prefixes) (Realization signature) (ℕ → ℕ → ℕ → ℕ × ℕ × ℕ → Bool) Unit where
  unitName :=
    `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.stepTable_all_prefixes.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.GroupState.prefixes.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => prefixOk x.1 x.2.1 x.2.2.1 x.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.GroupState
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end prefixes

end Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.GroupState
