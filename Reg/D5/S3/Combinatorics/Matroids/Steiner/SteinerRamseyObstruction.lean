import Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
import D5.S3.Combinatorics.Matroids.Steiner.SteinerRamseyObstruction

namespace Reg.D5.S3.Combinatorics.Matroids.Steiner.SteinerRamseyObstruction

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Matroids.Steiner.SteinerRamseyObstruction
open _root_.D5.S3.Combinatorics.Matroids.SteinerSchreierExtension (extensionMul)
open _root_.Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
  (AffineLoop affineIdentity affine_unit affine_comm affine_invol affine_centreless)
open _root_.Reg.Support.UniverseSingleReadout (signature sensitivity)

universe u v

noncomputable section

abbrev Params := Σ L : Type u, Σ A : Type v, Σ _ : Mul L, Σ _ : AddCommGroup A,
  Σ _ : L, Σ n : ℕ, Σ _ : Fin n → L, Fin n → L

abbrev sig : Signature :=
  signature Params.{u,v} (fun ⟨L, A, _, _, _, n, _, _⟩ => Set (Fin n → L) → A)
    (fun _ => ℕ)

def actual : Realization sig.{u,v} :=
  realize sig (fun _ ⟨_, _, multiply, add, e, _, p, q⟩ labels =>
    letI := multiply
    letI := add
    switchCount (fun _ => e) p q labels) (fun a => nomatch a)

def rejected : Realization sig.{u,v} :=
  realize sig (fun _ ⟨L, A, _, _, _, n, _, _⟩ _ => Nat.card ((Fin n → L) × A))
    (fun a => nomatch a)

def law (R : Realization sig.{u,v}) : Prop :=
  ∀ {L : Type u} {A : Type v} [Finite L] [Finite A] [Mul L]
    [AddCommGroup A] [Module (ZMod 2) A] [Nontrivial A]
    (e t : L) (_different : t ≠ e) (_unit : ∀ x, e * x = x)
    (_comm : ∀ x y : L, x * y = y * x) (_invol : ∀ x y : L, x * (x * y) = y)
    (_centre : Set.center L = {e}),
    ∃ n : ℕ, 0 < n ∧ ∀ labels : Set (Fin n → L) → A,
      ∃ p q : Fin n → L, p ≠ (fun _ => e) ∧ q ≠ (fun _ => e) ∧ p ≠ q ∧
        ∃ better : Set (Fin n → L) → A,
          R.readout () ⟨L, A, inferInstance, inferInstance, e, n, p, q⟩ labels <
            switchCount (fun _ => e) p q better

abbrev arena : Arena := ⟨sig, law.{u,v}⟩

private def point : AffineLoop.{u} := ULift.up (some 0)

private theorem point_ne : point.{u} ≠ affineIdentity := by
  intro same
  cases congrArg ULift.down same

private theorem rejected_law : ¬ law.{u,v} rejected := by
  intro impossible
  let L := AffineLoop.{u}
  let A := ULift.{v} (ZMod 2)
  obtain ⟨n, _, all⟩ := impossible (L := L) (A := A) affineIdentity point point_ne
    affine_unit affine_comm affine_invol affine_centreless
  obtain ⟨p, q, _, _, _, better, tooLarge⟩ := all (fun _ => 0)
  let _ := extensionMul (fun _ : Fin n => (affineIdentity : L)) better
  change Nat.card ((Fin n → L) × A) <
      ({x : (Fin n → L) × A | (q, 0) * ((p, 0) * x) ≠
        (p, 0) * ((q, 0) * x)} : Set ((Fin n → L) × A)).ncard at tooLarge
  exact (Nat.not_lt_of_ge (Set.ncard_le_card _)) tooLarge

private theorem dependence : ObservationalDependence sig.{u,v} actual := by
  intro role
  let L := AffineLoop.{u}
  let A := ULift.{v} (ZMod 2)
  obtain ⟨n, _, all⟩ := noCommonMaximumInSomePower (L := L) (A := A)
    affineIdentity point point_ne affine_unit affine_comm affine_invol affine_centreless
  obtain ⟨p, q, _, _, _, better, larger⟩ := all (fun _ => 0)
  refine ⟨⟨L, A, inferInstance, inferInstance, affineIdentity, n, p, q⟩,
    (fun _ => 0), better, ?_⟩
  exact Nat.ne_of_lt larger

def source : Registration arena.{u,v} (type_of% (@noCommonMaximumInSomePower.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@noCommonMaximumInSomePower, rejected, rejected_law⟩
  sensitivity := sensitivity law actual rejected rejected_law
  dependence := dependence


def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@noCommonMaximumInSomePower.{u,v}) (Realization sig.{u,v}) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Matroids.Steiner.SteinerRamseyObstruction.noCommonMaximumInSomePower.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.Steiner.SteinerRamseyObstruction.source
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
    owner := `D5.S3.Combinatorics.Matroids.Steiner.SteinerRamseyObstruction
    definition := none
    coordinates := #[0, 1, 8, 15, 17, 18]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Matroids.Steiner.SteinerRamseyObstruction
