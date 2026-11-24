import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns
import Mathlib.Algebra.Group.ULift

/-! # Registration of the simultaneous return range and the centreless obstruction -/

namespace Reg.D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns

open Function LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns
open _root_.D5.S3.Combinatorics.Matroids.SteinerSchreierExtension (extensionMul)
open _root_.Reg.Support.UniverseSingleReadout (signature sensitivity)

universe u v

noncomputable section

namespace ReturnRange

abbrev sig := signature (Type u) (fun A => A) (fun A => A)

def actual : Realization sig.{u} :=
  realize sig (fun _ _ w => w) (fun anchor => nomatch anchor)

def rejected : Realization sig.{u} := by
  classical
  exact realize sig (fun _ A w => if h : ∃ a : A, a ≠ w then Classical.choose h else w)
    (fun anchor => nomatch anchor)

def law (R : Realization sig.{u}) : Prop :=
  ∀ {A : Type u} {L : Type v} [AddCommGroup A] [Mul L]
    (b : BitVec 3 ↪ L) (_mul : ∀ x y, b (x ^^^ y) = b x * b y)
    (_twice : ∀ x : A, x + x = 0) (u v w : A),
    (∃ labels : Set L → A,
      letI := extensionMul (b 0) labels
      ∀ i : Fin 4, ∀ a : A,
        let x := b (BitVec.ofNat 3 (4 + i.val))
        (pairLift (b 1) (b 2))^[2] (x, a) = (x, a + u) ∧
        (pairLift (b 1) (b 3))^[2] (x, a) = (x, a + v) ∧
        (pairLift (b 2) (b 3))^[2] (x, a) = (x, a + w)) ↔ (u + v) + R.readout () A w = 0

abbrev arena : Arena := ⟨sig, law.{u,v}⟩

private theorem rejected_law : ¬ law.{u,v} rejected := by
  intro rule
  obtain ⟨B, mulB, b, _, _, _, _, _, hmul, _⟩ := existsCentrelessObstruction
  let _ := mulB
  let A := ULift.{u} (ZMod 2)
  let L := ULift.{v} B
  let cube : BitVec 3 ↪ L :=
    ⟨fun x => ULift.up (b x), fun h => b.injective (congrArg ULift.down h)⟩
  have mul (x y : BitVec 3) : cube (x ^^^ y) = cube x * cube y := ULift.ext (hmul x y)
  have twice (a : A) : a + a = 0 :=
    ULift.ext ((show ∀ j : ZMod 2, j + j = 0 by decide) a.down)
  have altered : rejected.readout () A (0 : A) ≠ 0 := by
    classical
    have hn : ∃ a : A, a ≠ 0 := ⟨ULift.up 1, by decide⟩
    change (if h : ∃ a : A, a ≠ 0 then Classical.choose h else 0) ≠ 0
    rw [dif_pos hn]
    exact Classical.choose_spec hn
  have zeroReturn := (simultaneousReturns cube mul twice (0 : A) 0 0).mpr (by simp)
  have incompatible := (rule cube mul twice (0 : A) 0 0).mp zeroReturn
  exact altered (by simpa only [zero_add] using incompatible)

private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro role
  refine ⟨ULift.{u} Bool, ULift.up false, ULift.up true, ?_⟩
  intro h
  exact Bool.noConfusion (congrArg ULift.down h)

def source : Registration arena.{u,v} (type_of% (@simultaneousReturns.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@simultaneousReturns, rejected, rejected_law⟩
  sensitivity := sensitivity law actual rejected rejected_law
  dependence := dependence

end ReturnRange

namespace CentrelessModel

abbrev sig := signature Unit (fun _ => Type) (fun _ => ℕ)

def actual : Realization sig := realize sig (fun _ _ L => Nat.card L) (fun anchor => nomatch anchor)

def rejected : Realization sig := realize sig (fun _ _ _ => 0) (fun anchor => nomatch anchor)

def law (R : Realization sig) : Prop :=
    ∃ (L : Type) (mul : Mul L) (b : BitVec 3 ↪ L),
      letI := mul
      R.readout () () L = 1000 ∧
      (∀ x : L, b 0 * x = x) ∧ (∀ x y : L, x * y = y * x) ∧
      (∀ x y : L, x * (x * y) = y) ∧ Set.center L = {b 0} ∧
      (∀ x y : BitVec 3, b (x ^^^ y) = b x * b y) ∧
      ¬ (∃ labels : Set L → ZMod 2,
        letI := extensionMul (b 0) labels
        ∀ i : Fin 4, ∀ a : ZMod 2,
          let x := b (BitVec.ofNat 3 (4 + i.val))
          (pairLift (b 1) (b 2))^[2] (x, a) = (x, a + 1) ∧
          (pairLift (b 1) (b 3))^[2] (x, a) = (x, a + 0) ∧
          (pairLift (b 2) (b 3))^[2] (x, a) = (x, a + 0))

abbrev arena : Arena := ⟨sig, law⟩

private theorem rejected_law : ¬ law rejected := by
  rintro ⟨L, mul, b, impossible, _⟩
  exact (by decide : (0 : ℕ) ≠ 1000) impossible

private theorem dependence : ObservationalDependence sig actual := by
  intro role
  refine ⟨(), PUnit, Bool, ?_⟩
  change Nat.card PUnit ≠ Nat.card Bool
  simp [Nat.card_eq_fintype_card]

def source : Registration arena (type_of% existsCentrelessObstruction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨existsCentrelessObstruction, rejected, rejected_law⟩
  sensitivity := sensitivity law actual rejected rejected_law
  dependence := dependence

end CentrelessModel

end
end Reg.D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns
