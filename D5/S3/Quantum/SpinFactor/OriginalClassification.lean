/- GID: D5/S3/Quantum/SpinFactor/OriginalClassification
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinFactor/OriginalClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.CrossProduct,
     D5/S3/Quantum/SpinFactor/OriginalDContract,
     D5/S3/Quantum/SpinFactor/OriginalPureRigidity,
     D5/S3/Quantum/SpinFactor/OriginalResidual,
     D5/S3/Geometry/TwoAxisFiniteRotation,
     D5/S3/Quantum/Information/Pauli/OriginalSpinConsumers]
   utility: none
   digest: Complete original-D H2 classification and same-D consequences. -/

import D5.S3.Quantum.SpinFactor.OriginalPureRigidity
import D5.S3.Quantum.SpinFactor.OriginalResidual
import D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers

noncomputable section

namespace D5.S3.Quantum.SpinFactor.OriginalClassification

open OriginalDContract
open OriginalPureRigidity (global_pure)
open OriginalResidual (all_inputs_of_pure)
open _root_.D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers
  (Consequences MatrixInterfaces same_D_consequences)

abbrev Relation := E → E → E

/- The Bool flag is only the consumer's presentation of the original two
   orientations; `crossD` remains the source-level endpoint. -/
def orientationBool : Orientation → Bool
  | .plus => true
  | .minus => false

private theorem all_input_sign (D : Relation) (hP : P2 D) (hPB : PB D) :
    ∃ e : ℝ, (e = 1 ∨ e = -1) ∧
      ∀ (s t : ℝ) (x y : Vec), D (s, x) (t, y) = (0, e • cross x y) := by
  obtain ⟨e, he, hpure⟩ := global_pure D hP hPB
  exact all_inputs_of_pure D hP hPB ⟨e, he, hpure⟩

/-- The complete original Theorem 93.1 endpoint on every original input. -/
theorem complete_classification (D : Relation) :
    P2 D ∧ PB D ↔
      ∃ ε : Orientation, ∀ a b : E, D a b = crossD ε a b := by
  constructor
  · rintro ⟨hP, hPB⟩
    obtain ⟨e, he, hD⟩ := all_input_sign D hP hPB
    rcases he with rfl | rfl
    · refine ⟨.plus, ?_⟩
      intro a b
      simpa [crossD] using hD a.1 b.1 a.2 b.2
    · refine ⟨.minus, ?_⟩
      intro a b
      simpa [crossD] using hD a.1 b.1 a.2 b.2
  · rintro ⟨ε, hε⟩
    cases ε with
    | plus =>
        have hc := same_D_consequences true D (by
          intro a b
          simpa [crossD] using hε a b)
        exact ⟨hc.1.p2, hc.1.pb⟩
    | minus =>
        have hc := same_D_consequences false D (by
          intro a b
          simpa [crossD] using hε a b)
        exact ⟨hc.1.p2, hc.1.pb⟩

/-- The classified sign also supplies every required same-D consequence.

The returned `Consequences` keeps the original unit, translation, real
bilinearity, original-norm bounds and continuity, finite complex Gram tables,
and the original reassociation identity.  `MatrixInterfaces` retains every
positive mass (including zero, subnormalized and unequal mass), the original
cone and `|s| + norm(x)` order-unit norm, and the fixed product realization.
The finite-word and moving-axis obligations are consumed transitively by the
all-input residual theorem; no continuity or density argument for unknown D is
introduced here.
-/
theorem complete_consequences (D : Relation) (hP : P2 D) (hPB : PB D) :
    ∃ ε : Orientation,
      (ε = .plus ∨ ε = .minus) ∧
      (∀ a b : E, D a b = crossD ε a b) ∧
      (Consequences D ∧ MatrixInterfaces (orientationBool ε) D) := by
  have hc := (complete_classification D).mp ⟨hP, hPB⟩
  rcases hc with ⟨ε, hε⟩
  cases ε with
  | plus =>
      have hconsumer := same_D_consequences true D (by
        intro a b
        simpa [crossD] using hε a b)
      exact ⟨.plus, Or.inl rfl, hε, hconsumer⟩
  | minus =>
      have hconsumer := same_D_consequences false D (by
        intro a b
        simpa [crossD] using hε a b)
      exact ⟨.minus, Or.inr rfl, hε, hconsumer⟩

end D5.S3.Quantum.SpinFactor.OriginalClassification
