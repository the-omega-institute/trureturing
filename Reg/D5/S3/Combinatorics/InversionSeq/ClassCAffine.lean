import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.InversionSeq.ClassCAffine
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.InversionSeq ClassCSites ClassCPaths ClassCAffine
open scoped BigOperators

namespace Reg.D5.S3.Combinatorics.InversionSeq.ClassCAffine

private theorem phi_one (q : State) : phi 1 q = q.p.length + q.s := by
  classical
  simp [phi, Path, Nat.card_sigma, Nat.card_eq_fintype_card,
    Fintype.card_sum, Fintype.card_fin]

namespace continuation_affine

abbrev signature : Signature where
  Params := State
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ q r => (phi r q : ℤ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law x := ∀ q : State, ∀ r : ℕ, x.readout () q r = (a r q.s 0 q.hs : ℤ) +
      (if q.h then (b r q.s q.hs : ℤ) - (a r q.s 1 q.hs : ℤ) else 0) +
      ∑ i : Fin q.p.length,
        ((a r q.s (((q.p.drop (i.val + 1)).count .U) + 1) q.hs : ℤ) -
          (a r q.s ((q.p.drop (i.val + 1)).count .U) q.hs : ℤ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx := h (lowerState 0 1 (by omega)) 0
  simpa [rejected, realize, a, phi, Path, lowerState] using hx

noncomputable def registration : Registration arena
    (∀ r : ℕ, ∀ q : State, (phi r q : ℤ) = (a r q.s 0 q.hs : ℤ) +
      (if q.h then (b r q.s q.hs : ℤ) - (a r q.s 1 q.hs : ℤ) else 0) +
      ∑ i : Fin q.p.length,
        ((a r q.s (((q.p.drop (i.val + 1)).count .U) + 1) q.hs : ℤ) -
          (a r q.s ((q.p.drop (i.val + 1)).count .U) q.hs : ℤ))) where
  actual := actual
  bridge := by
    constructor
    · intro h q r; exact h r q
    · intro h r q; exact h q r
  variation := ⟨by
    intro q r
    exact _root_.D5.S3.Combinatorics.InversionSeq.ClassCAffine.continuation_affine r q,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro ⟨⟩
    refine ⟨repeatState 1 (by omega), 0, 1, ?_⟩
    change (phi 0 (repeatState 1 (by omega)) : ℤ) ≠ (phi 1 (repeatState 1 (by omega)) : ℤ)
    simp [phi_one, repeatState, phi, Path]

noncomputable def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.InversionSeq.ClassCAffine.continuation_affine)
    (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Combinatorics.InversionSeq.ClassCAffine.continuation_affine.information_unit
  realizationName := `Reg.D5.S3.Combinatorics.InversionSeq.ClassCAffine.continuation_affine.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end continuation_affine

namespace a_recurrence

abbrev signature : Signature where
  Params := {s : ℕ // 1 ≤ s} × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ q r => a r q.1.val q.2 q.1.property) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law x := ∀ q : {s : ℕ // 1 ≤ s} × ℕ, ∀ r : ℕ, x.readout () q (r + 1) = (∑ i : Fin q.2, a r (q.1.val + 1) i.val (by omega)) +
      ∑ j : ↥(Finset.Icc 1 q.1.val),
        (a r (q.1.val - j.val + 1) (q.2 + j.val - 1)
          (by have := Finset.mem_Icc.mp j.property; omega) +
        b r (q.1.val - j.val + 1) (by have := Finset.mem_Icc.mp j.property; omega) -
        a r (q.1.val - j.val + 1) 0 (by have := Finset.mem_Icc.mp j.property; omega))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx := h (⟨1, by omega⟩, 0) 0
  simpa [rejected, realize, a, b, phi, Path, Finset.Icc_self] using hx

noncomputable def registration : Registration arena
    (∀ r s k : ℕ, ∀ hs : 1 ≤ s,
    a (r + 1) s k hs = (∑ i : Fin k, a r (s + 1) i.val (by omega)) +
      ∑ j : ↥(Finset.Icc 1 s),
        (a r (s - j.val + 1) (k + j.val - 1)
          (by have := Finset.mem_Icc.mp j.property; omega) +
        b r (s - j.val + 1) (by have := Finset.mem_Icc.mp j.property; omega) -
        a r (s - j.val + 1) 0 (by have := Finset.mem_Icc.mp j.property; omega))) where
  actual := actual
  bridge := by
    constructor
    · intro h q r; exact h r q.1.val q.2 q.1.property
    · intro h r s k hs; exact h (⟨s, hs⟩, k) r
  variation := ⟨by
    intro q r
    exact _root_.D5.S3.Combinatorics.InversionSeq.ClassCAffine.a_recurrence r q.1.val q.2 q.1.property,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro ⟨⟩
    refine ⟨(⟨1, by omega⟩, 1), 0, 1, ?_⟩
    change a 0 1 1 (by omega) ≠ a 1 1 1 (by omega)
    simp [a, phi_one, lowerState, phi, Path]

noncomputable def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.InversionSeq.ClassCAffine.a_recurrence)
    (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Combinatorics.InversionSeq.ClassCAffine.a_recurrence.information_unit
  realizationName := `Reg.D5.S3.Combinatorics.InversionSeq.ClassCAffine.a_recurrence.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end a_recurrence

namespace b_recurrence

abbrev signature : Signature where
  Params := {s : ℕ // 1 ≤ s}
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ q r => b r q.val q.property) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law x := ∀ q : {s : ℕ // 1 ≤ s}, ∀ r : ℕ, x.readout () q (r + 1) = b r (q.val + 1) (by omega) +
      ∑ j : ↥(Finset.Icc 1 q.val),
        (a r (q.val - j.val + 1) j.val
          (by have := Finset.mem_Icc.mp j.property; omega) +
        b r (q.val - j.val + 1) (by have := Finset.mem_Icc.mp j.property; omega) -
        a r (q.val - j.val + 1) 0 (by have := Finset.mem_Icc.mp j.property; omega))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx := h ⟨1, by omega⟩ 0
  simpa [rejected, realize, a, b, phi, Path, Finset.Icc_self] using hx

noncomputable def registration : Registration arena
    (∀ r s : ℕ, ∀ hs : 1 ≤ s,
    b (r + 1) s hs = b r (s + 1) (by omega) +
      ∑ j : ↥(Finset.Icc 1 s),
        (a r (s - j.val + 1) j.val
          (by have := Finset.mem_Icc.mp j.property; omega) +
        b r (s - j.val + 1) (by have := Finset.mem_Icc.mp j.property; omega) -
        a r (s - j.val + 1) 0 (by have := Finset.mem_Icc.mp j.property; omega))) where
  actual := actual
  bridge := by
    constructor
    · intro h q r; exact h r q.val q.property
    · intro h r s hs; exact h ⟨s, hs⟩ r
  variation := ⟨by
    intro q r
    exact _root_.D5.S3.Combinatorics.InversionSeq.ClassCAffine.b_recurrence r q.val q.property,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro ⟨⟩
    refine ⟨⟨1, by omega⟩, 0, 1, ?_⟩
    change b 0 1 (by omega) ≠ b 1 1 (by omega)
    simp [b, phi_one, repeatState, phi, Path]

noncomputable def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.InversionSeq.ClassCAffine.b_recurrence)
    (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Combinatorics.InversionSeq.ClassCAffine.b_recurrence.information_unit
  realizationName := `Reg.D5.S3.Combinatorics.InversionSeq.ClassCAffine.b_recurrence.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end b_recurrence

end Reg.D5.S3.Combinatorics.InversionSeq.ClassCAffine
