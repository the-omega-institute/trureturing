import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.CertificateState
import Reg.Support.DependentFamily

/-! Source-bound audit of the increasing-list checker. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.CertificateState

open _root_.D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ prev xs => increasingFrom prev xs) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {prev : ℕ} {xs : List ℕ}, R.readout () prev xs = true ↔
    xs.Pairwise (· < ·) ∧ ∀ x ∈ xs, prev < x

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hb := ((h (prev := 0) (xs := [1, 0])).mp rfl).1
  simpa using hb

def evidence : Registration arena (type_of% @increasingFrom_sound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@increasingFrom_sound, rejected, rejected_law⟩
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
    refine ⟨0, [], [0], ?_⟩
    norm_num [actual, realize, increasingFrom]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@increasingFrom_sound) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.increasingFrom_sound.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.CertificateState.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ prev xs => increasingFrom prev xs) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.CertificateState
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace stepTable_head

abbrev signature : Signature where
  Params := List (ℕ × ℕ × ℕ)
  State _ := List ℕ × List (ℕ × ℕ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option (List (ℕ × ℕ))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ ts x => stepTable ts x.1 x.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => some []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ts : List (ℕ × ℕ × ℕ)} {e : ℕ} {es : List ℕ}
    {st st' : List (ℕ × ℕ)},
    R.readout () ts (e :: es, st) = some st' ↔
      ∃ p j L t, oddPrimes[entryLabel e]? = some p ∧
        st[entryLabel e]? = some (j, L) ∧ ts[entryLabel e]? = some t ∧
        prefixOk p j L t = true ∧
        R.readout () ts (es, st.set (entryLabel e)
          (j + 1, L * (entryValue e - 1) / entryValue e)) = some st'

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  obtain ⟨p, j, L, t, _, hs, _⟩ :=
    (h (ts := []) (e := 0) (es := []) (st := []) (st' := [])).mp rfl
  simp at hs

def family : Registration arena (type_of% (@stepTable_head)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨stepTable_head, rejected, rejected_law⟩
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
    refine ⟨[], ([], []), ([0], []), ?_⟩
    change (some [] : Option (List (ℕ × ℕ))) ≠ none
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stepTable_head) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.stepTable_head)
      |>.str "__information_unit"
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ts x => stepTable ts x.1 x.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end stepTable_head

namespace stepTable_append

abbrev signature : Signature where
  Params := List (ℕ × ℕ × ℕ)
  State _ := List ℕ × List (ℕ × ℕ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option (List (ℕ × ℕ))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ ts x => stepTable ts x.1 x.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => if x.1 = [] then none else some []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ts : List (ℕ × ℕ × ℕ)) (as bs : List ℕ) (st : List (ℕ × ℕ)),
    R.readout () ts (as ++ bs, st) =
      (R.readout () ts (as, st)).bind (fun st => R.readout () ts (bs, st))

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hh := h [] [] [0] []
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% (@stepTable_append)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨stepTable_append, rejected, rejected_law⟩
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
    refine ⟨[], ([], []), ([0], []), ?_⟩
    change (some [] : Option (List (ℕ × ℕ))) ≠ none
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@stepTable_append) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.stepTable_append)
      |>.str "__information_unit"
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ts x => stepTable ts x.1 x.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end stepTable_append

namespace finalOk_sound

abbrev signature : Signature where
  Params := List (ℕ × ℕ × ℕ)
  State _ := List (ℕ × ℕ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ ts st => finalOk ts st) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ts : List (ℕ × ℕ × ℕ)} {st : List (ℕ × ℕ)},
    R.readout () ts st = true ↔
      ∀ (i p j L : ℕ) (t : ℕ × ℕ × ℕ), oddPrimes[i]? = some p →
        st[i]? = some (j, L) → ts[i]? = some t → prefixOk p j L t = true

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hb := (h (ts := []) (st := [])).mpr (by
    intro i p j L t hp hs ht
    simp at hs)
  exact Bool.false_ne_true hb

def family : Registration arena (type_of% (@finalOk_sound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finalOk_sound, rejected, rejected_law⟩
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
    refine ⟨[(1, 1, 0)], [], [(0, 0)], ?_⟩
    change finalOk [(1, 1, 0)] [] ≠ finalOk [(1, 1, 0)] [(0, 0)]
    decide +kernel

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finalOk_sound) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.finalOk_sound)
      |>.str "__information_unit"
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ts st => finalOk ts st) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.CertificateState
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end finalOk_sound

namespace increasingFrom_append

abbrev signature : Signature where
  Params := ℕ
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ prev xs => increasingFrom prev xs) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ xs => decide (xs.length = 1)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (prev : ℕ) (as bs : List ℕ), R.readout () prev (as ++ bs) =
    (R.readout () prev as && R.readout () (as.getLastD prev) bs)

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hh := h 0 [] [1]
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% (@increasingFrom_append)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨increasingFrom_append, rejected, rejected_law⟩
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
    refine ⟨0, [], [0], ?_⟩
    change increasingFrom 0 [] ≠ increasingFrom 0 [0]
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@increasingFrom_append) (Realization signature) Type Unit where
  unitName :=
    (`D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.increasingFrom_append)
      |>.str "__information_unit"
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ prev xs => increasingFrom prev xs) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.CertificateState
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end increasingFrom_append

end
end Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.CertificateState
