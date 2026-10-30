import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.LooseRootRepair
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.LooseRootRepair

namespace Reg.D5.S3.Combinatorics.Circle.LooseRootRepair
universe u
noncomputable section

/-- Only the first-slot strip's actual weight operand is varied. -/
abbrev signature : Signature where
  Params := Σ α : Type u, α → ℤ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => p.2 x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -100) (fun e => nomatch e)

/-- All source geometry, label inventories, positivity, sums and endpoints
retain the original f. The readout changes only InStrip's function operand. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [DecidableEq α]
    (f : α → ℤ) (Y : Finset α) (r s n m : α) (N Q C p B M h : ℤ)
    (hlabels : (r :: s :: n :: m :: Y.toList).Nodup)
    (hQ : 1 ≤ Q) (hN : N = 4 * Q - 1) (hC : C = (N - 1) / 2)
    (hB : B = N - 2 * p) (hp : Q ≤ p) (hpR : p ≤ f r)
    (hR : 3 * f r ≤ N) (hsQ : Q ≤ f s)
    (hs : f s = 4 * p - N) (hstrict : f s < p)
    (hn : f n = -B) (hm : f m < 0)
    (hf : ∀ x ∈ Y, 0 < f x ∧ f x ≤ M) (hsmall : 2 * M ≤ B)
    (hh : 0 ≤ h) (hbudget : h + f s ≤ C)
    (hover : C < h + f r + Y.sum f),
    ∃ P Q' : List α,
      (P ++ Q').Perm (r :: s :: Y.toList) ∧
      (P ++ Q').Nodup ∧ List.Disjoint P Q' ∧
      P.toFinset ∪ Q'.toFinset = insert r (insert s Y) ∧
      ((P.head? = some r ∧ Q'.head? = some s) ∨
        (P.head? = some s ∧ Q'.head? = some r)) ∧
      (∀ x ∈ P ++ Q', 0 < f x) ∧
      InStrip (R.readout () ⟨α, f⟩) C h (P ++ [n]) ∧
      (0 ≤ h + (P.map f).sum - B ∧ h + (P.map f).sum - B ≤ C - B) ∧
      (P.map f).sum + (Q'.map f).sum = f r + f s + Y.sum f ∧
      ((P ++ [n]) ++ (Q' ++ [m])).Perm ((r :: s :: Y.toList) ++ [n, m]) ∧
      h + (((P ++ [n]) ++ (Q' ++ [m])).map f).sum =
        h + f r + f s + (Y.sum f) + f n + f m

private def sampleWeight (i : ULift.{u} (Fin 4)) : ℤ :=
  ![10, 9, -11, -1] i.down

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro law
  obtain ⟨P, Q, _, _, _, _, hheads, _, hstrip, _⟩ := law sampleWeight ∅
    (ULift.up 0) (ULift.up 1) (ULift.up 2) (ULift.up 3) 31 8 15 10 11 0 6
    (by simp) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [sampleWeight]) (by norm_num [sampleWeight])
    (by norm_num [sampleWeight]) (by norm_num [sampleWeight])
    (by norm_num [sampleWeight]) (by norm_num [sampleWeight])
    (by norm_num [sampleWeight]) (by simp) (by norm_num) (by norm_num)
    (by norm_num [sampleWeight]) (by norm_num [sampleWeight])
  change InStrip (fun _ => (-100 : ℤ)) 15 6 (P ++ [ULift.up 2]) at hstrip
  cases P with
  | nil => simpa using hheads
  | cons a tail =>
    have hlo := (inStrip_prefix hstrip 1).1
    norm_num at hlo

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} (Fin 4), sampleWeight⟩, ULift.up 0, ULift.up 1, ?_⟩
  norm_num [actual, realize, sampleWeight]

def source_registration : Registration arena.{u}
    (type_of% (@source_cut_root_repair.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@source_cut_root_repair.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit.{u_1} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Circle.LooseRootRepair.source_cut_root_repair.{u_1})
    (type_of% (realize signature.{u_1} (fun _ p x => p.2 x) (fun e => nomatch e)))
    Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.LooseRootRepair.source_cut_root_repair.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.LooseRootRepair.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1}⟩
  objectArena := .source ⟨arena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1} ⟨source_registration.{u_1}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u_1} (fun _ p x => p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.LooseRootRepair
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg",
        "fn", "arg", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration

end
end Reg.D5.S3.Combinatorics.Circle.LooseRootRepair
