import Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
import D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns
import D5.S3.Combinatorics.Matroids.SteinerPaschSwitchCount

/-! Source registration for the opposite-pivot Pasch predicate. -/
namespace Reg.D5.S3.Combinatorics.Matroids.SteinerPaschSwitchCount

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Matroids
open _root_.D5.S3.Combinatorics.Matroids.SteinerPaschSwitchCount
open SteinerSchreierExtension (extensionMul)
open SteinerAlternatingSwitches (SuccessfulStart)
open PointDeletedSteinerSwitch (pointDeletedFamily)
open RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open RankThreeSaturatedTopGap (Covered Uncovered)
open SteinerMatchingTranslations (translate)
open _root_.Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
  (AffineLoop affineIdentity affine_unit affine_comm affine_invol affine_centreless)
open _root_.Reg.Support.UniverseSingleReadout (signature sensitivity)

universe u v

noncomputable section

abbrev Params := Σ L : Type u, Σ _ : Mul L, Σ _ : L, L

abbrev sig : Signature :=
  signature Params.{u} (fun P => P.1) (fun _ => Bool)

def actual : Realization sig.{u} :=
  realize sig (fun _ P q =>
    letI := P.2.1
    @decide (HasOppositePasch P.2.2.1 P.2.2.2 q) (Classical.propDecidable _))
    (fun a => nomatch a)

def rejected : Realization sig.{u} :=
  realize sig (fun _ _ _ => false) (fun a => nomatch a)

def law (R : Realization sig.{u}) : Prop :=
  ∀ {L : Type u} {A : Type v} [Finite L] [Mul L]
    [Finite A] [AddCommGroup A] [Module (ZMod 2) A] [Nontrivial A]
    (G : SimpleGraph L) (e p q : L)
    (_one : ∀ x, e * x = x) (_comm : ∀ x y : L, x * y = y * x)
    (_invol : ∀ x y : L, x * (x * y) = y) (_centreless : Set.center L = {e})
    (_different : p ≠ q) (_edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v),
    let attainable (count : ℕ) := ∃ (labels : Set L → A) (r : ℕ)
      (label : Option (Fin (r + 1)) ≃ L × A)
      (S : Set (Set (Fin (r + 1)))) (valid : IsPartialSteiner S)
      (cover : ∀ a b : Fin (r + 1), a ≠ b → Covered S a b)
      (i : Fin (r + 1)) (v : Fin r) (m : Fin r → Fin r),
      letI := extensionMul e labels
      label none = (e, 0) ∧ label (some i) = (p, 0) ∧
      label (some (i.succAbove v)) = (q, 0) ∧
      (∀ j a, label (translate valid cover j a) = label (some j) * label a) ∧
      (∀ a b, Uncovered (pointDeletedFamily S i) a b ↔ m a = b) ∧
      ({a | SuccessfulStart (pointDeletedFamily S i) m v a} : Set (Fin r)).ncard = count
    (∃ n₁ n₂, attainable n₁ ∧ attainable n₂ ∧ n₁ ≠ n₂) ↔
      R.readout () ⟨L, inferInstance, e, p⟩ q = true

abbrev arena : Arena := ⟨sig, law.{u,v}⟩

private abbrev Cube := AffineLoop.{u} × AffineLoop.{u} × AffineLoop.{u}

private def unitPoint : Cube.{u} := (affineIdentity, affineIdentity, affineIdentity)

private theorem paschWitness :
    ∃ p q : Cube.{u}, Set.center Cube.{u} = {unitPoint} ∧
      p ≠ unitPoint ∧ q ≠ unitPoint ∧ p ≠ q ∧ HasOppositePasch unitPoint p q := by
  let point : AffineLoop.{u} := ULift.up (some 0)
  have nonidentity : point ≠ affineIdentity := by
    intro h
    cases congrArg ULift.down h
  obtain ⟨b, identity, centre, product⟩ :=
    SteinerMultipivotReturns.existsCentrelessBooleanCube affineIdentity point affine_unit affine_comm
      affine_invol affine_centreless nonidentity
  change b 0 = unitPoint at identity
  have distinct : [b 0, b 1, b 2, b 4, b 6, b 7, b 5].Nodup :=
    List.Nodup.map b.injective
      (by decide : ([0, 1, 2, 4, 6, 7, 5] : List (BitVec 3)).Nodup)
  refine ⟨b 1, b 2, centre.trans (congrArg (fun x => ({x} : Set Cube)) identity),
    ?_, ?_, ?_, b 4, b 6, b 7, b 5, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← identity]
    exact b.injective.ne (by decide : (1 : BitVec 3) ≠ 0)
  · rw [← identity]
    exact b.injective.ne (by decide : (2 : BitVec 3) ≠ 0)
  · exact b.injective.ne (by decide : (1 : BitVec 3) ≠ 2)
  · rwa [← identity]
  · exact (product 2 4).symm
  · exact (product 1 6).symm
  · exact (product 2 7).symm
  · exact (product 1 5).symm

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro bad
  classical
  let L := Cube.{u}
  let A := ULift.{v} (ZMod 2)
  let e : L := unitPoint
  obtain ⟨p, q, centre, hp, hq, different, pasch⟩ := paschWitness.{u}
  have one (x : L) : e * x = x :=
    Prod.ext (affine_unit _) (Prod.ext (affine_unit _) (affine_unit _))
  have comm (x y : L) : x * y = y * x :=
    Prod.ext (affine_comm _ _) (Prod.ext (affine_comm _ _) (affine_comm _ _))
  have invol (x y : L) : x * (x * y) = y :=
    Prod.ext (affine_invol _ _) (Prod.ext (affine_invol _ _) (affine_invol _ _))
  let G := (loopPivotMatchings e p q one comm invol hp hq different).graph
  have existsCounts := (variableLabelledSwitchCount_iff (L := L) (A := A) G e p q
    one comm invol centre different (fun _ _ => Iff.rfl)).mpr pasch
  exact Bool.false_ne_true ((bad (L := L) (A := A) G e p q one comm invol centre different
    (fun _ _ => Iff.rfl)).mp existsCounts)

private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro i
  obtain ⟨p, q, _, _, _, _, hasPasch⟩ := paschWitness.{u}
  let e := unitPoint.{u}
  change HasOppositePasch e p q at hasPasch
  let P : Params.{u} := ⟨_, inferInstance, e, p⟩
  have same : ¬ HasOppositePasch e p p := by
    rintro ⟨a, b, c, d, distinct, _⟩
    simp at distinct
  refine ⟨P, q, p, ?_⟩
  simp [actual, realize, P, hasPasch, same]

private theorem actual_bridge :
    (type_of% (@variableLabelledSwitchCount_iff.{u,v})) ↔ law.{u,v} actual := by
  unfold law
  simp only [actual, realize, decide_eq_true_eq]

def source : Registration arena.{u,v} (type_of% (@variableLabelledSwitchCount_iff.{u,v})) where
  actual := actual
  bridge := actual_bridge
  variation := ⟨actual_bridge.mp @variableLabelledSwitchCount_iff.{u,v}, rejected, rejected_law⟩
  sensitivity := sensitivity law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@variableLabelledSwitchCount_iff.{u,v}) (Realization sig.{u}) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Matroids.SteinerPaschSwitchCount.variableLabelledSwitchCount_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SteinerPaschSwitchCount.source
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
    owner := `D5.S3.Combinatorics.Matroids.SteinerPaschSwitchCount
    definition := none
    coordinates := #[0, 9, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Matroids.SteinerPaschSwitchCount
