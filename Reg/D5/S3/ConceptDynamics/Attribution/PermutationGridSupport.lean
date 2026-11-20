import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.PermutationGridSupport
import Reg.Support.SingleDependentReadout

/-! The sharp grid budget observes the number of available occupancy codes. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.PermutationGridSupport

open _root_.D5.S3.ConceptDynamics.Attribution.PermutationGridSupport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset
open scoped Nat

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ k n => (k + 1)^n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k q : ℕ}, 2 ≤ k → 0 < q →
    (∀ d : ℕ, 0 < d → d ≤ k → d ∣ k * (k - 1) * q) → ∀ n : ℕ,
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction (Equiv.Perm (Fin k)) S)
      (w : S → ℝ) (f : {p : Fin k → ℕ // ∑ i, p i = k * (k - 1) * q} → S → Fin k),
      CalibratingLaw S w f ∧ Fintype.card S ≤ k ! * n) ↔
      k * q + 1 ≤ R.readout () k n

private theorem smallDivisible : ∀ d : ℕ, 0 < d → d ≤ 2 → d ∣ 2 * (2 - 1) * 1 := by
  intro d positive bound
  have h : d = 1 ∨ d = 2 := by omega
  rcases h with rfl | rfl <;> decide

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have existsLaw :=
    (grid_support_budget_iff (k := 2) (q := 1) (by decide) (by decide) smallDivisible 1).mpr
      (by decide)
  exact (by decide : ¬ (2 : ℕ) * 1 + 1 ≤ 0)
    ((h (k := 2) (q := 1) (by decide) (by decide) smallDivisible 1).mp existsLaw)

def family : Registration arena (type_of% (@grid_support_budget_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨grid_support_budget_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    exact (by decide : (1 : ℕ) ≠ 3)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@grid_support_budget_iff) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.PermutationGridSupport.information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.PermutationGridSupport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k n => (k + 1)^n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.PermutationGridSupport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


private abbrev Profile (I : Type*) [Fintype I] (m : ℕ) :=
  {p : I → ℕ // ∑ i, p i = m}

private abbrev relabel {I : Type*} [Fintype I] {m : ℕ} (g : Equiv.Perm I) (p : Profile I m) :
    Profile I m :=
  ⟨fun i => p.val (g⁻¹ i), (Equiv.sum_comp (g⁻¹ : Equiv.Perm I) p.val).trans p.property⟩

universe u v

abbrev spectrumSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def spectrumActual : Realization spectrumSignature :=
  realize spectrumSignature (fun _ _ m => m) (fun e => nomatch e)

def spectrumRejected : Realization spectrumSignature :=
  realize spectrumSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev spectrumArena : Arena where
  signature := spectrumSignature
  Law R := ∀ {I : Type u} {S : Type v} [Fintype I] [DecidableEq I] [Fintype S]
    [MulAction (Equiv.Perm I) S] (_two : 2 ≤ Fintype.card I)
    {m : ℕ} (_free : ∀ s : S, MulAction.stabilizer (Equiv.Perm I) s = ⊥)
    (w : S → ℝ) (_invariant : ∀ (g : Equiv.Perm I) s, w (g • s) = w s)
    (f : Profile I m → S → I)
    (_calibrated : ∀ p i, ∑ s, (if f p s = i then w s else 0) = (p.val i : ℝ))
    (_covariant : ∀ g p s, f (relabel g p) (g • s) = g (f p s)),
    ∃ (r : ℕ) (weights : Fin r → ℝ),
      Fintype.card S = (Fintype.card I)! * r ∧
      ((Fintype.card I)! : ℝ) * (∑ j, weights j) =
        ((Fintype.card I - 2)! : ℝ) * ∑ s, w s ∧
      ∀ l : Fin (R.readout () () m / (Fintype.card I - 1) + 1),
        ∃ d : Fin r → Fin (Fintype.card I + 1),
          ∑ j, (d j).val * weights j = (l.val : ℝ)

private theorem spectrum_rejected_law : ¬ spectrumArena.{u,v}.Law spectrumRejected := by
  classical
  intro h
  let I := ULift.{u} (Fin 2)
  let S := ULift.{v} Empty
  letI : MulAction (Equiv.Perm I) S :=
    { smul := fun _ s => s, one_smul := fun _ => rfl, mul_smul := fun _ _ _ => rfl }
  let f (_p : Profile I 0) (s : S) : I := isEmptyElim s
  let w (s : S) : ℝ := isEmptyElim s
  have cardI : Fintype.card I = 2 := by simp [I]
  have cardS : Fintype.card S = 0 := by simp [S]
  have calibrated (p : Profile I 0) (i : I) :
      (∑ s : S, if f p s = i then w s else 0) = (p.val i : ℝ) := by
    have le : p.val i ≤ ∑ j, p.val j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (p.val j)) (Finset.mem_univ i)
    rw [p.property] at le
    simp [Nat.eq_zero_of_le_zero le]
  obtain ⟨r, weights, support, _, cover⟩ :=
    h (I := I) (S := S) (by rw [cardI]) (m := 0) (fun s => isEmptyElim s)
      w (fun _ s => isEmptyElim s) f calibrated (fun _ _ s => isEmptyElim s)
  have zero : r = 0 := by
    norm_num [cardI, cardS, Nat.factorial] at support
    omega
  subst r
  have level : Fin (spectrumRejected.readout () () 0 / (Fintype.card I - 1) + 1) :=
    ⟨1, by rw [cardI]; decide⟩
  obtain ⟨digits, eq⟩ := cover level
  norm_num [level] at eq

def spectrumFamily : Registration spectrumArena (type_of% (@weighted_orbit_spectrum)) where
  actual := spectrumActual
  bridge := Iff.rfl
  variation := ⟨weighted_orbit_spectrum, spectrumRejected, spectrum_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    spectrumArena.Law spectrumActual spectrumRejected spectrum_rejected_law
  dependence := by
    intro role
    exact ⟨(), 0, 1, (by decide : (0 : ℕ) ≠ 1)⟩

def spectrumRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@weighted_orbit_spectrum) (Realization spectrumSignature) Type Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.PermutationGridSupport.weighted_spectrum_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.PermutationGridSupport.spectrumFamily
  realizationSource := none
  generated := false
  arena := .source ⟨spectrumArena⟩
  objectArena := .source ⟨spectrumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source spectrumArena ⟨spectrumFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize spectrumSignature (fun _ _ m => m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.PermutationGridSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "body", "arg", "arg", "domain", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.PermutationGridSupport
