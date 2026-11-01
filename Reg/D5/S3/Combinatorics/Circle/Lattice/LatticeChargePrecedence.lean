import D5.S3.Combinatorics.Circle.Lattice.LatticeChargePrecedence
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact physical-position observation for the full lattice/suffix implication. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Circle.Lattice.LatticeChargePrecedence
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.RunFirstEarTransport
open _root_.D5.S3.Combinatorics.Circle.Lattice.LatticeChargePrecedence

abbrev signature : Signature where
  Params := Σ m : ℕ, List (Fin m)
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p i => p.2.idxOf i) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀
    (m : ℕ) (sigma : List (Fin m)) (j : ℕ)
    (hperm : sigma.Perm (List.finRange m)) (hj : j ≤ m)
    (f q : Fin m → ℤ) (g : Fin (m + 1) → ℤ) (G C N A H : ℤ)
    (hG : 0 < G) (hA : 0 < A)
    (hgrid : ∀ i, G ∣ f i) (hq : ∀ i, 0 ≤ q i)
    (hcharge : (sigma.map q).sum = A)
    (hpair : ∀ i, g i.castSucc = 2 * f i - q i)
    (hfresh : g (Fin.last m) = A)
    (holdsum : (sigma.map f).sum = 0)
    (hnewsum : ((earWord m sigma j).map g).sum = 0)
    (hold : ∀ r, ((sigma.take r).map f).sum ∈ Set.Icc (0 : ℤ) C)
    (hnew : ∀ r, (((earWord m sigma j).take r).map g).sum ∈ Set.Icc (0 : ℤ) N)
    (nu : Fin m) (hnu : f nu = -H) (hH : 0 < H)
    (hHgrid : G ∣ H) (hHC : H ≤ C) (hsat : C < H + G) (hqnu : 0 < q nu),
    let p := R.readout () ⟨m, sigma⟩ nu
    ((sigma.take p).map f).sum = H ∧
    ((sigma.take (p + 1)).map f).sum = 0 ∧
    j ≤ p ∧
    ((sigma.drop p).map q).sum ≤ N - 2 * H ∧
    ∀ delta : Fin m, delta ≠ nu → N - 2 * H < q delta + q nu →
      sigma.idxOf delta < p

private def f (i : Fin 2) : ℤ := if i.val = 0 then 2 else -2
private def q (i : Fin 2) : ℤ := if i.val = 0 then 0 else 1
private def g (i : Fin 3) : ℤ := if i.val = 0 then 4 else if i.val = 1 then -5 else 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hold : ∀ r : ℕ, (([0,1].take r).map f).sum ∈ Set.Icc (0 : ℤ) 2 := by
    intro r
    simpa using inStrip_prefix (f := f) (B := 2) (h := 0) (l := [0,1])
      (by norm_num [InStrip, f]) r
  have hnew : ∀ r : ℕ, (((earWord 2 [0,1] 1).take r).map g).sum ∈ Set.Icc (0 : ℤ) 5 := by
    intro r
    simpa using inStrip_prefix (f := g) (B := 5) (h := 0) (l := earWord 2 [0,1] 1)
      (by norm_num [earWord, InStrip, g]) r
  have hh := h 2 [0,1] 1 (by decide) (by decide) f q g 2 2 5 1 2
    (by decide) (by decide)
    (by intro i; fin_cases i <;> norm_num [f])
    (by intro i; fin_cases i <;> norm_num [q])
    (by norm_num [q]) (by intro i; fin_cases i <;> norm_num [f,q,g])
    (by norm_num [g]) (by norm_num [f]) (by norm_num [earWord,g])
    hold hnew 1 (by norm_num [f]) (by decide) (by decide) (by decide) (by decide) (by norm_num [q])
  norm_num [rejected,realize] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2,[0,1]⟩, 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% (@lattice_saturation_suffix_precedence)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨lattice_saturation_suffix_precedence, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e; exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.Lattice.LatticeChargePrecedence.lattice_saturation_suffix_precedence)
    (type_of% (realize signature actual.readout actual.anchor)) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.Lattice.LatticeChargePrecedence.lattice_saturation_suffix_precedence.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.Lattice.LatticeChargePrecedence.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Lattice.LatticeChargePrecedence
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #[
      "body", "body", "body", "body", "body", "body", "body", "body",
      "body", "body", "body", "body", "body", "body", "body", "body",
      "body", "body", "body", "body", "body", "body", "body", "body",
      "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms source_registration
#print axioms audit
end Reg.D5.S3.Combinatorics.Circle.Lattice.LatticeChargePrecedence
