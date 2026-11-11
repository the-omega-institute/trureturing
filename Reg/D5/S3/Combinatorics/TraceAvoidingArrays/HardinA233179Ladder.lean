import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179Ladder
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact sequence readouts for the literal ladder count and its pair-label transfer. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179Ladder
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179Ladder
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer (L initial_values)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
attribute [local irreducible] a L

namespace Bridge
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 2 ≤ n → 48 * R.readout () () n =
      (64 : ℤ)^n * ((L n : ℤ) + 6)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := counting_bridge (n := 2) (by decide)
  have hb := h (n := 2) (by decide)
  change 48 * ((a 2 : ℤ) + 1) = (64 : ℤ)^2 * ((L 2 : ℤ) + 6) at hb
  linarith only [ha, hb]
private theorem actual_dependence :
    actual.readout () () 2 ≠ actual.readout () () 3 := by
  have h2 := counting_bridge (n := 2) (by decide)
  have h3 := counting_bridge (n := 3) (by decide)
  have hL2 : (L 2 : ℤ) = 1458 := initial_values 0
  have hL3 : (L 3 : ℤ) = 23346 := initial_values 1
  rw [hL2] at h2
  rw [hL3] at h3
  norm_num at h2 h3
  change (a 2 : ℤ) ≠ (a 3 : ℤ)
  omega
def family : Registration arena (type_of% @counting_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@counting_bridge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 3, actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@counting_bridge) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179Ladder.Bridge.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179Ladder.Bridge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179Ladder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Bridge

namespace Base
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () 26 =
    448 * R.readout () () 25 + 421888 * R.readout () () 24 - 95682560 * R.readout () () 23 -
      48586817536 * R.readout () () 22 + 7696581394432 * R.readout () () 21 + 2219020623282176 *
      R.readout () () 20 - 331924968239529984 * R.readout () () 19 - 45544058606667694080 *
      R.readout () () 18 + 7676565708838105251840 * R.readout () () 17 + 384720682715267981115392 *
      R.readout () () 16 - 90389119748153097756606464 * R.readout () () 15 -
      732939612340266155036901376 * R.readout () () 14 + 559176850836005482125888323584 * R.readout
      () () 13 - 7028965514623047698676841447424 * R.readout () () 12 -
      1887473560557987165955670813966336 * R.readout () () 11 + 44169859058027396737075939400220672
      * R.readout () () 10 + 3500683050361467360162023730212503552 * R.readout () () 9 -
      101555160700421718306247628235154128896 * R.readout () () 8 -
      3466958920006006825501354764976208740352 * R.readout () () 7 +
      108207134224866861549607317549181730553856 * R.readout () () 6 +
      1701156622829501613469275506203267231121408 * R.readout () () 5 -
      52659376845749069097884147249280994259238912 * R.readout () () 4 -
      315694924216699133847365011797178367569035264 * R.readout () () 3 +
      9366312983382861719445001674512311832511774720 * R.readout () () 2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := finite_certificate
  change ((a 26 : ℤ) + 1) =
    448 * ((a (25) : ℤ) + 1) + 421888 * ((a (24) : ℤ) + 1) - 95682560 * ((a (23) : ℤ) + 1) -
      48586817536 * ((a (22) : ℤ) + 1) + 7696581394432 * ((a (21) : ℤ) + 1) + 2219020623282176 * ((a
      (20) : ℤ) + 1) - 331924968239529984 * ((a (19) : ℤ) + 1) - 45544058606667694080 * ((a (18) :
      ℤ) + 1) + 7676565708838105251840 * ((a (17) : ℤ) + 1) + 384720682715267981115392 * ((a (16) :
      ℤ) + 1) - 90389119748153097756606464 * ((a (15) : ℤ) + 1) - 732939612340266155036901376 * ((a
      (14) : ℤ) + 1) + 559176850836005482125888323584 * ((a (13) : ℤ) + 1) -
      7028965514623047698676841447424 * ((a (12) : ℤ) + 1) - 1887473560557987165955670813966336 *
      ((a (11) : ℤ) + 1) + 44169859058027396737075939400220672 * ((a (10) : ℤ) + 1) +
      3500683050361467360162023730212503552 * ((a (9) : ℤ) + 1) -
      101555160700421718306247628235154128896 * ((a (8) : ℤ) + 1) -
      3466958920006006825501354764976208740352 * ((a (7) : ℤ) + 1) +
      108207134224866861549607317549181730553856 * ((a (6) : ℤ) + 1) +
      1701156622829501613469275506203267231121408 * ((a (5) : ℤ) + 1) -
      52659376845749069097884147249280994259238912 * ((a (4) : ℤ) + 1) -
      315694924216699133847365011797178367569035264 * ((a (3) : ℤ) + 1) +
      9366312983382861719445001674512311832511774720 * ((a (2) : ℤ) + 1) at h
  linarith only [ha, h]
private theorem actual_dependence :
    actual.readout () () 2 ≠ actual.readout () () 3 := by
  have h2 := counting_bridge (n := 2) (by decide)
  have h3 := counting_bridge (n := 3) (by decide)
  have hL2 : (L 2 : ℤ) = 1458 := initial_values 0
  have hL3 : (L 3 : ℤ) = 23346 := initial_values 1
  rw [hL2] at h2
  rw [hL3] at h3
  norm_num at h2 h3
  change (a 2 : ℤ) ≠ (a 3 : ℤ)
  omega
def family : Registration arena (type_of% @finite_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 3, actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179Ladder.Base.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179Ladder.Base.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179Ladder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Base

namespace Recurrence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+26) =
    448 * R.readout () () (n+25) + 421888 * R.readout () () (n+24) - 95682560 * R.readout () ()
      (n+23) - 48586817536 * R.readout () () (n+22) + 7696581394432 * R.readout () () (n+21) +
      2219020623282176 * R.readout () () (n+20) - 331924968239529984 * R.readout () () (n+19) -
      45544058606667694080 * R.readout () () (n+18) + 7676565708838105251840 * R.readout () ()
      (n+17) + 384720682715267981115392 * R.readout () () (n+16) - 90389119748153097756606464 *
      R.readout () () (n+15) - 732939612340266155036901376 * R.readout () () (n+14) +
      559176850836005482125888323584 * R.readout () () (n+13) - 7028965514623047698676841447424 *
      R.readout () () (n+12) - 1887473560557987165955670813966336 * R.readout () () (n+11) +
      44169859058027396737075939400220672 * R.readout () () (n+10) +
      3500683050361467360162023730212503552 * R.readout () () (n+9) -
      101555160700421718306247628235154128896 * R.readout () () (n+8) -
      3466958920006006825501354764976208740352 * R.readout () () (n+7) +
      108207134224866861549607317549181730553856 * R.readout () () (n+6) +
      1701156622829501613469275506203267231121408 * R.readout () () (n+5) -
      52659376845749069097884147249280994259238912 * R.readout () () (n+4) -
      315694924216699133847365011797178367569035264 * R.readout () () (n+3) +
      9366312983382861719445001674512311832511774720 * R.readout () () (n+2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := result 0
  have hb := h 0
  change ((a (0+26) : ℤ) + 1) =
    448 * ((a (0+25) : ℤ) + 1) + 421888 * ((a (0+24) : ℤ) + 1) - 95682560 * ((a (0+23) : ℤ) + 1) -
      48586817536 * ((a (0+22) : ℤ) + 1) + 7696581394432 * ((a (0+21) : ℤ) + 1) + 2219020623282176 *
      ((a (0+20) : ℤ) + 1) - 331924968239529984 * ((a (0+19) : ℤ) + 1) - 45544058606667694080 * ((a
      (0+18) : ℤ) + 1) + 7676565708838105251840 * ((a (0+17) : ℤ) + 1) + 384720682715267981115392 *
      ((a (0+16) : ℤ) + 1) - 90389119748153097756606464 * ((a (0+15) : ℤ) + 1) -
      732939612340266155036901376 * ((a (0+14) : ℤ) + 1) + 559176850836005482125888323584 * ((a
      (0+13) : ℤ) + 1) - 7028965514623047698676841447424 * ((a (0+12) : ℤ) + 1) -
      1887473560557987165955670813966336 * ((a (0+11) : ℤ) + 1) +
      44169859058027396737075939400220672 * ((a (0+10) : ℤ) + 1) +
      3500683050361467360162023730212503552 * ((a (0+9) : ℤ) + 1) -
      101555160700421718306247628235154128896 * ((a (0+8) : ℤ) + 1) -
      3466958920006006825501354764976208740352 * ((a (0+7) : ℤ) + 1) +
      108207134224866861549607317549181730553856 * ((a (0+6) : ℤ) + 1) +
      1701156622829501613469275506203267231121408 * ((a (0+5) : ℤ) + 1) -
      52659376845749069097884147249280994259238912 * ((a (0+4) : ℤ) + 1) -
      315694924216699133847365011797178367569035264 * ((a (0+3) : ℤ) + 1) +
      9366312983382861719445001674512311832511774720 * ((a (0+2) : ℤ) + 1) at hb
  norm_num only [Nat.reduceAdd] at hb
  linarith only [ha, hb]
private theorem actual_dependence :
    actual.readout () () 2 ≠ actual.readout () () 3 := by
  have h2 := counting_bridge (n := 2) (by decide)
  have h3 := counting_bridge (n := 3) (by decide)
  have hL2 : (L 2 : ℤ) = 1458 := initial_values 0
  have hL3 : (L 3 : ℤ) = 23346 := initial_values 1
  rw [hL2] at h2
  rw [hL3] at h3
  norm_num at h2 h3
  change (a 2 : ℤ) ≠ (a 3 : ℤ)
  omega
def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 3, actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179Ladder.Recurrence.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179Ladder.Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179Ladder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Recurrence
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179Ladder
