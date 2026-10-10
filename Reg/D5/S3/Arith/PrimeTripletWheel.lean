import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.PrimeTripletWheel
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.Arith.PrimeTripletWheel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.PrimeTripletWheel

abbrev NonzeroMod := {W : ℕ // W ≠ 0}

abbrev signature : Signature where
  Params := NonzeroMod
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ p n =>
    letI : NeZero p.1 := ⟨p.2⟩
    letI : Fintype (PlusResidue p.1) :=
      Fintype.ofFinite {a : ZMod p.1 // plusAdmissible p.1 a}
    if n = 0 then Fintype.card (PlusResidue p.1)
    else Fintype.card (PlusResidue p.1) + n) (fun e => nomatch e)

noncomputable def rejected : Realization signature :=
  realize signature (fun _ p _ =>
    letI : NeZero p.1 := ⟨p.2⟩
    letI : Fintype (MinusResidue p.1) :=
      Fintype.ofFinite {a : ZMod p.1 // minusAdmissible p.1 a}
    Fintype.card (MinusResidue p.1) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ p : NonzeroMod,
    letI : NeZero p.1 := ⟨p.2⟩
    letI : Fintype (PlusResidue p.1) :=
      Fintype.ofFinite {a : ZMod p.1 // plusAdmissible p.1 a}
    letI : Fintype (MinusResidue p.1) :=
      Fintype.ofFinite {a : ZMod p.1 // minusAdmissible p.1 a}
    r.readout () p 0 = Fintype.card (MinusResidue p.1)

abbrev statement : Prop := ∀ (W : ℕ) [NeZero W],
  letI : Fintype (PlusResidue W) :=
    Fintype.ofFinite {a : ZMod W // plusAdmissible W a}
  letI : Fintype (MinusResidue W) :=
    Fintype.ofFinite {a : ZMod W // minusAdmissible W a}
  Fintype.card (PlusResidue W) = Fintype.card (MinusResidue W)

theorem bridge : statement ↔ arena.Law actual := by
  constructor
  · intro h p
    letI : NeZero p.1 := ⟨p.2⟩
    letI : Fintype (PlusResidue p.1) :=
      Fintype.ofFinite {a : ZMod p.1 // plusAdmissible p.1 a}
    letI : Fintype (MinusResidue p.1) :=
      Fintype.ofFinite {a : ZMod p.1 // minusAdmissible p.1 a}
    have hcard := h p.1
    change Fintype.card (PlusResidue p.1) = Fintype.card (MinusResidue p.1)
    exact hcard
  · intro h W inst
    letI : NeZero W := inst
    letI : Fintype (PlusResidue W) :=
      Fintype.ofFinite {a : ZMod W // plusAdmissible W a}
    letI : Fintype (MinusResidue W) :=
      Fintype.ofFinite {a : ZMod W // minusAdmissible W a}
    let p : NonzeroMod := ⟨W, NeZero.ne W⟩
    have hp := h p
    change Fintype.card (PlusResidue W) = Fintype.card (MinusResidue W) at hp
    exact hp

theorem actual_law : arena.Law actual := by
  intro p
  letI : NeZero p.1 := ⟨p.2⟩
  letI : Fintype (PlusResidue p.1) :=
    Fintype.ofFinite {a : ZMod p.1 // plusAdmissible p.1 a}
  letI : Fintype (MinusResidue p.1) :=
    Fintype.ofFinite {a : ZMod p.1 // minusAdmissible p.1 a}
  have hcard := candidate_space_card_eq p.1
  change Fintype.card (PlusResidue p.1) = Fintype.card (MinusResidue p.1)
  exact hcard

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : NeZero (1 : ℕ) := ⟨by decide⟩
  letI : Fintype (MinusResidue 1) :=
    Fintype.ofFinite {a : ZMod 1 // minusAdmissible 1 a}
  have hp := h ⟨1, by decide⟩
  have hne : ¬ Fintype.card (MinusResidue 1) + 1 = Fintype.card (MinusResidue 1) := by
    omega
  change Fintype.card (MinusResidue 1) + 1 = Fintype.card (MinusResidue 1) at hp
  exact hne hp

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, by decide⟩, 0, 1, ?_⟩
  letI : NeZero (1 : ℕ) := ⟨by decide⟩
  letI : Fintype (PlusResidue 1) :=
    Fintype.ofFinite {a : ZMod 1 // plusAdmissible 1 a}
  change Fintype.card (PlusResidue 1) ≠ Fintype.card (PlusResidue 1) + 1
  omega

noncomputable def registration : Registration arena statement where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Arith.PrimeTripletWheel.candidate_space_card_eq)
      (type_of% (realize signature
        (fun _ p n =>
          letI : NeZero p.1 := ⟨p.2⟩
          letI : Fintype (PlusResidue p.1) :=
            Fintype.ofFinite {a : ZMod p.1 // plusAdmissible p.1 a}
          if n = 0 then Fintype.card (PlusResidue p.1)
          else Fintype.card (PlusResidue p.1) + n)
        (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.Arith.PrimeTripletWheel.candidate_space_card_eq.__information_unit,
  realizationName := `Reg.D5.S3.Arith.PrimeTripletWheel.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ p n =>
      letI : NeZero p.1 := ⟨p.2⟩
      letI : Fintype (PlusResidue p.1) :=
        Fintype.ofFinite {a : ZMod p.1 // plusAdmissible p.1 a}
      if n = 0 then Fintype.card (PlusResidue p.1)
      else Fintype.card (PlusResidue p.1) + n)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimeTripletWheel,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Arith.PrimeTripletWheel
