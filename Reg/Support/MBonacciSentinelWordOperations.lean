import D5.S1.Words.MBonacciParikhStarConverse
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.MBonacciSentinelDesubstitution
import Reg.Support.DependentFamily

open _root_.D5.S1.Words.MBonacciSentinelDesubstitution
open _root_.D5.S1.Words.RankOneMorphismIterationBound (subst image)
open _root_.D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs (factor)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S1.Words.MBonacciSentinelDesubstitution
open _root_.D5.S1.Words.MBonacciReversedPrefixFRS
open _root_.D5.S1.Words.MBonacciMinimumParikhDescent
open _root_.D5.S1.Words.MBonacciMinimumGreedy
open _root_.D5.S1.Words.MBonacciParikhStarConverse
open _root_.D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs (factor letterCount)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S1.Words.MBonacciSentinelDesubstitution

abbrev ConverseOrder := {m : ℕ // 2 ≤ m}
abbrev ConverseFive := {m : ℕ // 2 ≤ m ∧ 5 ≤ m}

namespace boundary_window

abbrev signature : Signature where
  Params := ConverseOrder × ℕ
  State p := ℕ → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  ∃ i : ℕ, x i ≤ p.2 ∧ p.2 < x (i + 1)

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (q : ℕ),
      R.readout () ⟨⟨m, hm⟩, q⟩ (boundary hm)

private theorem actual_law : arena.Law actual := by
  intro m hm q
  exact _root_.D5.S1.Words.MBonacciSentinelDesubstitution.boundary_window hm q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) 0

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, 0⟩ (fun _ => 0) := by
  simp [observed]

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.boundary_window)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law, ⟨rejected, rejected_law⟩⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨⟨2, by omega⟩, 0⟩, (boundary (by omega : 2 ≤ 2)), (fun _ => 0), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) 0))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.boundary_window) (type_of% actual)
    (type_of% (@boundary)) Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.boundary_window.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.boundary_window.family,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (@boundary),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end boundary_window

namespace t_head

abbrev signature : Signature where
  Params := Σ p : ConverseOrder, List (Fin p.val)
  State p := List (Fin p.1.val)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  ∃ v : List (Fin p.1.val), x = zero p.1.property :: v

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (s : List (Fin m)),
      R.readout () ⟨⟨m, hm⟩, s⟩ (T hm s)

private theorem actual_law : arena.Law actual := by
  intro m hm s
  exact _root_.D5.S1.Words.MBonacciSentinelDesubstitution.t_head hm s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) []

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, []⟩ ([]) := by
  simp [observed]

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.t_head)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law, ⟨rejected, rejected_law⟩⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨⟨2, by omega⟩, []⟩, (T (by omega : 2 ≤ 2) []), ([]), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) []))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.t_head) (type_of% actual)
    (type_of% (@T)) Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.t_head.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.t_head.family,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (@T),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end t_head

namespace occ_cons

abbrev signature : Signature where
  Params := Σ p : ConverseOrder, Fin p.val × (List (Fin p.val) × ℕ)
  State p := (List (Fin p.1.val) → ℕ → Prop) × (ℕ → Fin p.1.val)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  x.1 (p.2.1 :: p.2.2.1) p.2.2.2 ↔
    x.2 p.2.2.2 = p.2.1 ∧ x.1 p.2.2.1 (p.2.2.2 + 1)

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (a : Fin m) (s : List (Fin m)) (q : ℕ),
      R.readout () ⟨⟨m, hm⟩, a, s, q⟩ (Occ hm, word hm)

private theorem actual_law : arena.Law actual := by
  intro m hm a s q
  exact _root_.D5.S1.Words.MBonacciSentinelDesubstitution.occ_cons hm a s q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (by omega : 2 ≤ 2) 0 [] 0

private theorem bad_observation : ¬ observed ⟨⟨2, by omega⟩, 0, [], 0⟩ ((fun _ _ => True, fun _ => 1)) := by
  simp [observed]

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.occ_cons)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law, ⟨rejected, rejected_law⟩⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨⟨2, by omega⟩, 0, [], 0⟩, ((Occ (by omega : 2 ≤ 2), word (by omega : 2 ≤ 2))), ((fun _ _ => True, fun _ => 1)), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (by omega : 2 ≤ 2) 0 [] 0))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.occ_cons) (type_of% actual)
    (type_of% (@Occ)) Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.occ_cons.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.occ_cons.family,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (@Occ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end occ_cons

namespace factor_add

abbrev signature : Signature where
  Params := Σ m : ℕ, (ℕ → Fin m) × (ℕ × (ℕ × ℕ))
  State p := ℕ → ℕ → List (Fin p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (p : signature.Params) (x : signature.State p) : Prop :=
  x p.2.2.1 (p.2.2.2.1 + p.2.2.2.2) =
    x p.2.2.1 p.2.2.2.1 ++ x (p.2.2.1 + p.2.2.2.1) p.2.2.2.2

def actual : Realization signature :=
  realize signature (fun _ p x => observed p x) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (x : ℕ → Fin m) (i n t : ℕ),
      R.readout () ⟨m, x, i, n, t⟩ (factor x)

private theorem actual_law : arena.Law actual := by
  intro m x i n t
  exact _root_.D5.S1.Words.MBonacciSentinelDesubstitution.factor_add x i n t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (m := 2) (fun _ => 0) 0 0 0

private theorem bad_observation : ¬ observed ⟨2, (fun _ => 0), 0, 0, 0⟩ (fun _ _ => [0]) := by
  simp [observed]

def family : Registration arena (type_of% (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.factor_add)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law, ⟨rejected, rejected_law⟩⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨2, (fun _ => 0), 0, 0, 0⟩, (factor (fun _ => (0 : Fin 2))), (fun _ _ => [0]), ?_⟩
    intro he
    exact bad_observation (Eq.mp he (by
      exact actual_law (m := 2) (fun _ => 0) 0 0 0))

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.MBonacciSentinelDesubstitution.factor_add) (type_of% actual)
    (type_of% (@factor)) Unit := {
  unitName := `D5.S1.Words.MBonacciSentinelDesubstitution.factor_add.__information_unit,
  realizationName := `Reg.D5.S1.Words.MBonacciSentinelDesubstitution.factor_add.family,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature actual.readout actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (@factor),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end factor_add

end Reg.D5.S1.Words.MBonacciSentinelDesubstitution

#print axioms Reg.D5.S1.Words.MBonacciSentinelDesubstitution.boundary_window.family
#print axioms Reg.D5.S1.Words.MBonacciSentinelDesubstitution.boundary_window.audit
#print axioms Reg.D5.S1.Words.MBonacciSentinelDesubstitution.t_head.family
#print axioms Reg.D5.S1.Words.MBonacciSentinelDesubstitution.t_head.audit
#print axioms Reg.D5.S1.Words.MBonacciSentinelDesubstitution.occ_cons.family
#print axioms Reg.D5.S1.Words.MBonacciSentinelDesubstitution.occ_cons.audit
#print axioms Reg.D5.S1.Words.MBonacciSentinelDesubstitution.factor_add.family
#print axioms Reg.D5.S1.Words.MBonacciSentinelDesubstitution.factor_add.audit
