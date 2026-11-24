import Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
import D5.S3.Combinatorics.Matroids.SteinerFixedPivotCountRange
import Mathlib.Algebra.Module.PUnit

/-! Source registration for the range of counts at fixed Steiner pivots. -/

namespace Reg.D5.S3.Combinatorics.Matroids.SteinerFixedPivotCountRange

open LeanInformationAudit SimpleGraph
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Matroids
open _root_.D5.S3.Combinatorics.Matroids.SteinerFixedPivotCountRange
open SteinerSchreierExtension (extensionMul)
open SteinerSchreierSwitchCount (realizeLabelledSwitchCount squareFixed)
open SteinerAlternatingSwitches (SuccessfulStart Matchings)
open PointDeletedSteinerSwitch (pointDeletedFamily)
open RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open RankThreeSaturatedTopGap (Covered Uncovered)
open SteinerMatchingTranslations (translate)
open _root_.Reg.D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
  (sig actual rejected)
open _root_.Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
  (AffineLoop affineIdentity affine_unit affine_comm affine_invol affine_centreless affine_noncommuting)
open _root_.Reg.Support.UniverseSingleReadout (sensitivity)

universe u v

noncomputable section

def law (R : Realization sig.{v}) : Prop :=
  ∀ {L : Type u} {A : Type v} [Finite L] [Mul L]
    [Finite A] [AddCommGroup A] [Module (ZMod 2) A]
    (G : SimpleGraph L) (e p q : L)
    (one : ∀ x : L, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) (centreless : Set.center L = {e})
    (different : p ≠ q)
    (edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v)
    (count : ℕ),
    let b := ({x : L | p * (q * (p * (q * x))) ≠ x} : Set L).ncard
    let s := ({C : G.ConnectedComponent | C ≠ G.connectedComponentMk e ∧ C.supp.ncard = 4} :
      Set G.ConnectedComponent).ncard
    (∃ (labels : Set L → A) (r : ℕ) (label : Option (Fin (r + 1)) ≃ L × A)
      (S : Set (Set (Fin (r + 1)))) (valid : IsPartialSteiner S)
      (cover : ∀ a b : Fin (r + 1), a ≠ b → Covered S a b)
      (i : Fin (r + 1)) (v : Fin r) (m : Fin r → Fin r),
      letI := extensionMul e labels
      label none = (e, 0) ∧ label (some i) = (p, 0) ∧
      label (some (i.succAbove v)) = (q, 0) ∧
      (∀ j a, label (translate valid cover j a) = label (some j) * label a) ∧
      (∀ a b, Uncovered (pointDeletedFamily S i) a b ↔ m a = b) ∧
      ({a | SuccessfulStart (pointDeletedFamily S i) m v a} : Set (Fin r)).ncard = count) ↔
      ∃ k ≤ s, (k = 0 ∨ Nontrivial A) ∧ count = R.readout () () A * (b + 4 * k)

abbrev arena : Arena := ⟨sig, law.{u,v}⟩

private theorem rejected_law : ¬ law.{u,v} rejected := by
  intro bound
  let L := AffineLoop.{u}
  let A := PUnit.{v+1}
  let e : L := affineIdentity
  obtain ⟨p, q, x, noncommuting⟩ := affine_noncommuting.{u}
  have hp : p ≠ e := by
    intro eq
    exact noncommuting (by rw [eq, affine_unit, affine_unit])
  have hq : q ≠ e := by
    intro eq
    exact noncommuting (by rw [eq, affine_unit, affine_unit])
  have different : p ≠ q := fun eq => noncommuting (by rw [eq])
  have injectRight (x : L) : Function.Injective (· * x) := by
    intro y z eq
    apply (show Function.Involutive (x * ·) from affine_invol x).injective
    change x * y = x * z
    simpa only [affine_comm x y, affine_comm x z] using eq
  let M : Matchings L := {
    first := (p * ·)
    second := (q * ·)
    first_involutive := affine_invol p
    second_involutive := affine_invol q
    first_ne_self := fun x eq => hp (injectRight x (eq.trans (affine_unit x).symm))
    second_ne_self := fun x eq => hq (injectRight x (eq.trans (affine_unit x).symm))
    partners_ne := fun x eq => different (injectRight x eq)
  }
  let zeroReturn : {C : M.graph.ConnectedComponent // C ≠ M.graph.connectedComponentMk e} → A :=
    fun _ => 0
  obtain ⟨labels, r, label, i, w, S, valid, cover, matching, zero, atP, atQ, _, transport, leave, _,
    measured⟩ :=
    realizeLabelledSwitchCount M.graph e p q affine_unit affine_comm affine_invol
      (fun _ => Subsingleton.elim _ _) affine_centreless different (fun _ _ => Iff.rfl) zeroReturn
  have positive :
      0 < ({a | SuccessfulStart (pointDeletedFamily S i) matching w a} : Set (Fin r)).ncard := by
    rw [measured]
    apply Nat.mul_pos Nat.card_pos
    apply (Set.ncard_pos (Set.toFinite _)).mpr
    refine ⟨x, Or.inl ?_⟩
    exact fun closes => noncommuting ((squareFixed (affine_invol p) (affine_invol q) x).mpr closes)
  obtain ⟨_, _, _, impossible⟩ :=
    (bound (L := L) (A := A) M.graph e p q affine_unit affine_comm affine_invol
      affine_centreless different (fun _ _ => Iff.rfl)
      ({a | SuccessfulStart (pointDeletedFamily S i) matching w a} : Set (Fin r)).ncard).mp
        ⟨labels, r, label, S, valid, cover, i, w, matching, zero, atP, atQ, transport, leave, rfl⟩
  simp only [rejected, realize, zero_mul] at impossible
  exact (Nat.ne_of_gt positive) impossible

def source : Registration arena.{u,v} (type_of% (@labelledFixedPivotCountRange.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@labelledFixedPivotCountRange, rejected, rejected_law⟩
  sensitivity := sensitivity law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), PUnit.{v+1}, ULift.{v} Bool, ?_⟩
    change Nat.card (PUnit.{v+1}) ≠ Nat.card (ULift.{v} Bool)
    simp [Nat.card_eq_fintype_card]

def fixedCountRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@labelledFixedPivotCountRange.{u,v}) (Realization sig.{v}) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Matroids.SteinerFixedPivotCountRange.labelledFixedPivotCountRange.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SteinerFixedPivotCountRange.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.SteinerFixedPivotCountRange
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "arg", "body", "arg", "arg",
        "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end
end Reg.D5.S3.Combinatorics.Matroids.SteinerFixedPivotCountRange
