import Reg.D5.S3.Geometry.Rauzy.Interior
import D5.S3.Geometry.Rauzy.TribonacciRegularClosure

/-! Regular-interior observations retain the original two root hypotheses. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Geometry.Rauzy.TribonacciRegularClosure

open _root_.D5.S0.Tower.Tribonacci
open _root_.D5.S3.Geometry.Rauzy.TribonacciRegularClosure
open _root_.D5.S3.Constants.Irrationality.TribonacciTraceLattice
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set

abbrev signature : Signature where
  Params := Unit
  State _ := Set ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => closure (interior s)) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {z : ℂ}, z ∈ Binet.tribonacciCharacteristicPolynomial.roots →
    z ≠ (Values.tribonacciConstant : ℂ) →
      R.readout () () (RauzyFractal.rauzyFractal z) = RauzyFractal.rauzyFractal z

abbrev sourceScope := type_of% (@rauzyFractal_closure_interior)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have he := h Reg.D5.S3.Geometry.Rauzy.Interior.root_mem
    tribonacciSecondaryRoot.2.2.1
  have hn := RauzyFractal.rauzyFractal_nonempty tribonacciSecondaryRoot.1
  change (∅ : Set ℂ) = RauzyFractal.rauzyFractal tribonacciSecondaryRoot.1 at he
  rw [← he] at hn
  exact not_nonempty_empty hn

def family : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨@rauzyFractal_closure_interior, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), ∅, univ, ?_⟩
    change closure (interior (∅ : Set ℂ)) ≠ closure (interior (univ : Set ℂ))
    simpa using (Set.empty_ne_univ : (∅ : Set ℂ) ≠ univ)

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@rauzyFractal_closure_interior) (Realization signature) Unit Unit where
  unitName := `D5.S3.Geometry.Rauzy.TribonacciRegularClosure.rauzyFractal_closure_interior.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Rauzy.TribonacciRegularClosure.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => closure (interior s)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Rauzy.TribonacciRegularClosure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace PrefixCover

open _root_.D5.S0.Tower.Tribonacci.RauzyFractal
open _root_.D5.S0.Tower.Tribonacci.Binet
open _root_.D5.S0.Tower.Tribonacci.Values

abbrev geometricSignature : Signature where
  Params := Complex
  State _ := Set Complex
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def geometricActual : Realization geometricSignature :=
  realize geometricSignature (fun _ z s =>
    zeroPrefixMap z '' rauzyFractal z ∪ oneZeroPrefixMap z '' rauzyFractal z ∪
      oneOneZeroPrefixMap z '' rauzyFractal z = s) (fun e => nomatch e)

def geometricErased : Realization geometricSignature :=
  realize geometricSignature (fun _ _ _ => False) (fun e => nomatch e)

abbrev geometricArena : Arena where
  signature := geometricSignature
  Law R := ∀ {z : Complex}, z ∈ tribonacciCharacteristicPolynomial.roots →
    z ≠ (tribonacciConstant : Complex) → R.readout () z (rauzyFractal z)

abbrev sourceScope := type_of% (@rauzyFractal_prefix_cover)

theorem geometric_bridge : sourceScope ↔ geometricArena.Law geometricActual := Iff.rfl

theorem geometric_erased_fails : ¬ geometricArena.Law geometricErased := by
  intro h
  exact h Reg.D5.S3.Geometry.Rauzy.Interior.root_mem
    _root_.D5.S3.Constants.Irrationality.TribonacciTraceLattice.tribonacciSecondaryRoot.2.2.1

private theorem images_nonempty (z : Complex) :
    (zeroPrefixMap z '' rauzyFractal z ∪ oneZeroPrefixMap z '' rauzyFractal z ∪
      oneOneZeroPrefixMap z '' rauzyFractal z).Nonempty :=
  ((rauzyFractal_nonempty z).image (zeroPrefixMap z)).mono
    (fun _ h => Or.inl (Or.inl h))

def geometricFamily : Registration geometricArena sourceScope where
  actual := geometricActual
  bridge := geometric_bridge
  variation := ⟨@rauzyFractal_prefix_cover, geometricErased, geometric_erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨geometricErased, ?_, rfl, geometric_erased_fails⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨0, zeroPrefixMap 0 '' rauzyFractal 0 ∪ oneZeroPrefixMap 0 '' rauzyFractal 0 ∪
      oneOneZeroPrefixMap 0 '' rauzyFractal 0, ∅, ?_⟩
    change (_ = _) ≠ (_ = (∅ : Set Complex))
    intro he
    have hempty := he ▸ (rfl :
      (zeroPrefixMap 0 '' rauzyFractal 0 ∪ oneZeroPrefixMap 0 '' rauzyFractal 0 ∪
      oneOneZeroPrefixMap 0 '' rauzyFractal 0) = _)
    exact (images_nonempty 0).ne_empty hempty

def geometricRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@rauzyFractal_prefix_cover) (Realization geometricSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Rauzy.TribonacciRegularClosure.rauzyFractal_prefix_cover.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Rauzy.TribonacciRegularClosure.PrefixCover.geometricFamily
  realizationSource := none
  generated := false
  arena := .source ⟨geometricArena⟩
  objectArena := .source ⟨geometricArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source geometricArena ⟨geometricFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize geometricSignature (fun _ z s =>
    zeroPrefixMap z '' rauzyFractal z ∪ oneZeroPrefixMap z '' rauzyFractal z ∪
      oneOneZeroPrefixMap z '' rauzyFractal z = s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Rauzy.TribonacciRegularClosure
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PrefixCover

end Reg.D5.S3.Geometry.Rauzy.TribonacciRegularClosure
