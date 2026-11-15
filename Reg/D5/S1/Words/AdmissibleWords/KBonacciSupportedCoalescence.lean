import D5.S1.Words.AdmissibleWords.KBonacciSupportedCoalescence
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option autoImplicit false
noncomputable section

namespace Reg.D5.S1.Words.AdmissibleWords.KBonacciSupportedCoalescence

abbrev signature : Signature where
  Params := Σ n : ℕ, Σ sites : List (Fin n), Fin sites.length
  State p := (Fin p.1 → Bool) × (Fin p.1 → Bool)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => w.1 (p.2.1.get p.2.2)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k n : ℕ} (hk : 0 < k)
    (sites : List (Fin n)) (hn : sites.Nodup)
    (horder : sites.Pairwise (fun i j => i.val < j.val))
    (fixed : Finset (Fin n)) (hfree : ∀ i ∈ sites, i ∉ fixed)
    (hcover : ∀ i : Fin n, i ∉ fixed → i ∈ sites)
    (x y : Fin n → Bool) (hx : (completions k n fixed x).Nonempty)
    (hy : (completions k n fixed y).Nonempty)
    (hfar : ∀ i ∈ sites, ∀ j ∈ fixed, i.val < j.val → x j = y j),
    ∀ w : (Fin n → Bool) × (Fin n → Bool),
      prefixCoupling sites fixed x y hx hy w ≠ 0 →
      ∀ r q : Fin sites.length, r ≤ q →
        w.1 (sites.get r) = false → w.2 (sites.get r) = false →
        R.readout () ⟨n, sites, q⟩ w = w.2 (sites.get q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let x : Fin 1 → Bool := fun _ => false
  have hx : (completions 1 1 ∅ x).Nonempty := completion_nonempty ∅ x (by decide)
  let p := prefixCoupling [(0 : Fin 1)] ∅ x x hx hx
  obtain ⟨w, hw⟩ := p.support_nonempty
  have hm := prefix_coupling_marginals (by decide : 0 < 1) [(0 : Fin 1)]
    (by simp) ∅ (by simp) x x hx hx
  have hxw : w.1 ∈ completions 1 1 ∅ x := by
    have hs : w.1 ∈ (p.map Prod.fst).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨w, hw, rfl⟩
    change p.map Prod.fst w.1 ≠ 0 at hs
    rw [hm.1, completionLaw_apply] at hs
    by_contra he
    simp [he] at hs
  have hyw : w.2 ∈ completions 1 1 ∅ x := by
    have hs : w.2 ∈ (p.map Prod.snd).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨w, hw, rfl⟩
    change p.map Prod.snd w.2 ≠ 0 at hs
    rw [hm.2, completionLaw_apply] at hs
    by_contra he
    simp [he] at hs
  have hall : ∀ v ∈ completions 1 1 ∅ x, v (0 : Fin 1) = false := by decide
  have hbad := law (by decide : 0 < 1) [(0 : Fin 1)] (by simp)
    (by simp) ∅ (by simp) (by intro i hi; exact List.mem_singleton.mpr (Subsingleton.elim i 0))
    x x hx hx (by simp) w hw 0 0 le_rfl (by simpa using hall _ hxw) (by simpa using hall _ hyw)
  change true = w.2 (0 : Fin 1) at hbad
  rw [hall _ hyw] at hbad
  cases hbad

def proof_record : Registration arena (type_of% @prefix_coupling_supported_coalescence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prefix_coupling_supported_coalescence, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨⟨1, [(0 : Fin 1)], 0⟩,
      ((fun _ => false), (fun _ => false)),
      ((fun _ => true), (fun _ => false)), ?_⟩
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prefix_coupling_supported_coalescence) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.KBonacciConditionalBlockCoupling.prefix_coupling_supported_coalescence.__information_unit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.KBonacciSupportedCoalescence.proof_record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof_record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.KBonacciSupportedCoalescence
    definition := none
    coordinates := #[1, 3, 17]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof_record
end Reg.D5.S1.Words.AdmissibleWords.KBonacciSupportedCoalescence
