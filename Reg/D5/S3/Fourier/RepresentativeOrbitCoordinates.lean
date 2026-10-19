import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.RepresentativeOrbitCoordinates
import Reg.Support.DependentFamily
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Field.ULift

namespace Reg.D5.S3.Fourier.RepresentativeOrbitCoordinates
open _root_.D5.S3.Fourier.RepresentativeOrbitCoordinates
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
universe u

abbrev Parameters := Σ n : ℕ, Σ d : ℕ, (Fin d → ZMod n) → ZMod 2

abbrev signature : Signature where
  Params := Parameters
  State p := Fin p.2.1 → ZMod p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p r => p.2.2 r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n d : ℕ) (hn : 3 ≤ n) (ho : Odd n) (_hd : 1 ≤ d)
    (F : Type u) [Field F] [Finite F] [CharP F 2]
    (ζ : F) (hζ : IsPrimitiveRoot ζ n),
    let : NeZero n := ⟨by omega⟩
    let : Algebra (ZMod 2) F := ZMod.algebra F 2
    let G := Fin d → ZMod n
    let p : Equiv.Perm G := Equiv.piCongrRight
      (fun _ => (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr ho)).mulLeft)
    let O := Quotient (Equiv.Perm.SameCycle.setoid p)
    ∀ sec : O → G, (∀ q, Quotient.mk (Equiv.Perm.SameCycle.setoid p) (sec q) = q) →
    ∃ e : (G → ZMod 2) ≃ₗ[ZMod 2]
        ((q : O) → IntermediateField.adjoin (ZMod 2)
          (Set.range (fun j : Fin d => ζ ^ (sec q j).val))),
      ∀ a q, (e a q : F) =
        ∑ r : G, algebraMap (ZMod 2) F (R.readout () ⟨n,d,a⟩ r) *
          ∏ j : Fin d, ζ ^ (sec q j * r j).val

def registration : Registration arena.{u} (type_of% (@representative_fourier_coordinates.{u})) := by
  have rejected_law : ¬ arena.{u}.Law rejected := by
    classical
    let K := GaloisField 2 2
    letI : Fintype K := Fintype.ofFinite K
    obtain ⟨z,hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
    have hz3 : IsPrimitiveRoot (z : K) 3 := by
      apply IsPrimitiveRoot.iff_orderOf.mpr
      rw [orderOf_units, hz, Nat.card_units, GaloisField.card 2 2 (by decide : 2 ≠ 0)]
      norm_num
    let F := ULift.{u} K
    letI : Field F := inferInstanceAs (Field (ULift.{u} (GaloisField 2 2)))
    letI : Finite F := inferInstanceAs (Finite (ULift.{u} (GaloisField 2 2)))
    letI : CharP F 2 := inferInstanceAs (CharP (ULift.{u} (GaloisField 2 2)) 2)
    have hζ : IsPrimitiveRoot (ULift.up (z : K) : F) 3 :=
      hz3.map_of_injective ULift.ringEquiv.symm.injective
    intro h
    let p : Equiv.Perm (Fin 1 → ZMod 3) := Equiv.piCongrRight
      (fun _ => (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 3)).mulLeft)
    let O := Quotient (Equiv.Perm.SameCycle.setoid p)
    let sec : O → (Fin 1 → ZMod 3) := Quotient.out
    obtain ⟨e,he⟩ := h 3 1 (by omega) (by decide) (by omega) F (ULift.up (z : K)) hζ
      sec (fun q => Quotient.out_eq' q)
    have ez (a : (Fin 1 → ZMod 3) → ZMod 2) : e a=0 := by
      funext q
      apply Subtype.ext
      simpa [rejected, realize] using he a q
    have heq : (fun _ : Fin 1 → ZMod 3 => (1 : ZMod 2)) = (fun _ => 0) :=
      e.injective ((ez _).trans (ez _).symm)
    have hh := congrFun heq 0
    norm_num at hh
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@representative_fourier_coordinates.{u}, rejected, rejected_law⟩
    sensitivity := ⟨fun i => ⟨rejected,
      fun j h => (h (show j=i from @Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
      fun i => nomatch i⟩
    dependence := ?_ }
  classical
  change ObservationalDependence signature actual
  intro i
  refine ⟨⟨3,1,fun r => if r=0 then 1 else 0⟩, 0, 1, ?_⟩
  norm_num [actual, realize, Pi.one_apply, Pi.zero_apply, funext_iff]

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@representative_fourier_coordinates.{u})
    (type_of% (realize signature (fun (_ : Unit) (p : Parameters) r => p.2.2 r)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Fourier.RepresentativeOrbitCoordinates.representative_fourier_coordinates.information_unit,
  realizationName := `Reg.D5.S3.Fourier.RepresentativeOrbitCoordinates.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨registration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun (_ : Unit) (p : Parameters) r => p.2.2 r)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.RepresentativeOrbitCoordinates,
    definition := none,
    coordinates := #[0, 1, 19],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","body","arg","body","body","body","arg","arg","body","fn","arg","arg"],
      stateBinder := 21,
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

end
end Reg.D5.S3.Fourier.RepresentativeOrbitCoordinates
