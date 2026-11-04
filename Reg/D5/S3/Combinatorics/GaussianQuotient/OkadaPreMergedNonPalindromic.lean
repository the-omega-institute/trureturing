import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic
import Reg.Support.DependentFamily

/-! Source-bound audit of Okada's pre-merged determinant non-palindromicity. -/

namespace Reg.D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic

open _root_.D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic
open _root_.D5.S3.Combinatorics.CylindricPartition.LiUncuDefs (gauss)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the pre-merged polynomial while varying its upper index sequence. -/
abbrev signature : Signature where
  Params := Σ μ : ℕ, Fin μ → ℕ
  State p := Fin p.1 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Polynomial ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p b => preMerged p.2 b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Keep the full width, monotonicity, and crossing hypotheses of the source claim. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (μ : ℕ) (a b : Fin μ → ℕ),
    3 ≤ μ → StrictMono a → StrictMono b → (∀ i j, a i ≤ b j) →
      ¬ IsAlmostPalindromic (r.readout () ⟨μ, a⟩ b)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 3 (fun i => i.val) (fun i => i.val + 2) (by omega)
    (fun _ _ hij => hij) (fun _ _ hij => by simpa using hij)
    (fun i j => by omega)
  apply hbad
  change IsAlmostPalindromic 0
  simpa [IsAlmostPalindromic] using (List.Palindrome.nil : ([] : List ℤ).Palindrome)

theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨2, fun i => i.val⟩, (fun _ => 0), (fun i => i.val + 1), ?_⟩
  change preMerged (fun i : Fin 2 => i.val) (fun _ => 0) ≠
    preMerged (fun i : Fin 2 => i.val) (fun i => i.val + 1)
  norm_num [preMerged, Fin.prod_univ_two, gauss, Fin.rev]
  exact Polynomial.X_ne_zero.symm

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ p b => preMerged p.2 b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic
    definition := some {
      owner := `D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic
      name := `D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic.claim
      path := #[] }
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic.result
#print _root_.D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic.claim
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.GaussianQuotient.OkadaPreMergedNonPalindromic
