/- GID: D5/S3/Quantum/Entanglement/FiniteSectorChannelModel
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/FiniteSectorChannelModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact finite sector channel model, operations, and optimality claims. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Entanglement.SectorSchmidtEncoding
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Matrix.Composition

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open SectorSchmidtEncoding
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker InnerProductSpace

/-- The exact finite spectral data of the source and flat target encodings. -/
structure Model (Sector : Type*) [Fintype Sector] (spectralSize : ℕ) where
  d : Sector → ℕ
  positiveRank : ∀ s, 0 < d s
  spectrum : Sector → Fin spectralSize → ℝ
  spectrumNonneg : ∀ s j, 0 ≤ spectrum s j
  spectrumSum : ∀ s, ∑ j, spectrum s j = 1
  spectrumAntitone : ∀ s, Antitone (spectrum s)

variable {Sector : Type u} [Fintype Sector] [DecidableEq Sector]
  {spectralSize : ℕ}

/-- The Gram kernel of the common residual spectra. -/
def kernel (M : Model Sector spectralSize) (s t : Sector) : ℝ :=
  ∑ j, Real.sqrt (M.spectrum s j) * Real.sqrt (M.spectrum t j)

/-- The minimum common spectral quadratic form. -/
def spectralMinimum (M : Model Sector spectralSize) : ℝ :=
  sInf {q : ℝ | ∃ p ∈ stdSimplex ℝ Sector,
    q = ∑ s, ∑ t, p s * p t * kernel M s t}

/-- Actual channels realizing the two prescribed isometric matrix encodings. -/
structure EncodingChannels (M : Model Sector spectralSize) where
  source : QuantumChannel Sector
    (SourceLocal (Coord := Fin spectralSize) M.d × SourceLocal (Coord := Fin spectralSize) M.d)
  target : QuantumChannel Sector (TargetLocal M.d × TargetLocal M.d)
  sourceAction : ∀ X : Matrix Sector Sector ℂ,
    CStarMatrix.ofMatrix.symm
      (source.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      sourceEncoding M.d M.spectrum * X * (sourceEncoding M.d M.spectrum)ᴴ
  targetAction : ∀ X : Matrix Sector Sector ℂ,
    CStarMatrix.ofMatrix.symm
      (target.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      targetEncoding M.d * X * (targetEncoding M.d)ᴴ

/-- The tensor action of arbitrary local channels, expanded in input matrix units. -/
def tensorRawAction {ax ay bx oy : Type*}
    [Fintype ax] [DecidableEq ax] [Fintype ay] [DecidableEq ay]
    [Fintype bx] [DecidableEq bx] [Fintype oy] [DecidableEq oy]
    (left : QuantumChannel ax bx) (right : QuantumChannel ay oy)
    (X : Matrix (ax × ay) (ax × ay) ℂ) : Matrix (bx × oy) (bx × oy) ℂ :=
  fun p q => ∑ i : ax, ∑ j : ax, ∑ u : ay, ∑ v : ay,
    X (i, u) (j, v) *
      CStarMatrix.ofMatrix.symm
        (left.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single i j 1))) p.1 q.1 *
      CStarMatrix.ofMatrix.symm
        (right.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single u v 1))) p.2 q.2

/-- Complete matrix reconstruction ties a joint channel to the two local maps. -/
def TensorRealization {ax ay bx oy : Type*}
    [Fintype ax] [DecidableEq ax] [Fintype ay] [DecidableEq ay]
    [Fintype bx] [DecidableEq bx] [Fintype oy] [DecidableEq oy]
    (left : QuantumChannel ax bx) (right : QuantumChannel ay oy)
    (joint : QuantumChannel (ax × ay) (bx × oy)) : Prop :=
  ∀ X : Matrix (ax × ay) (ax × ay) ℂ,
    CStarMatrix.ofMatrix.symm (joint.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      tensorRawAction left right X

/-- A finite shared classical choice mixes product actions on every input matrix. -/
def MixtureRealization {ax ay bx oy : Type*}
    [Fintype ax] [DecidableEq ax] [Fintype ay] [DecidableEq ay]
    [Fintype bx] [DecidableEq bx] [Fintype oy] [DecidableEq oy]
    {m : ℕ} (weight : Fin m → ℝ)
    (left : Fin m → QuantumChannel ax bx) (right : Fin m → QuantumChannel ay oy)
    (joint : QuantumChannel (ax × ay) (bx × oy)) : Prop :=
  ∀ X : Matrix (ax × ay) (ax × ay) ℂ,
    CStarMatrix.ofMatrix.symm (joint.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      ∑ i, (weight i : ℂ) • tensorRawAction (left i) (right i) X

def productErrors (M : Model Sector spectralSize) (encoding : EncodingChannels M) : Set ℝ :=
  {x | ∃ left : QuantumChannel (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d),
    ∃ right : QuantumChannel (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d),
    ∃ joint : QuantumChannel
      (SourceLocal (Coord := Fin spectralSize) M.d × SourceLocal (Coord := Fin spectralSize) M.d)
      (TargetLocal M.d × TargetLocal M.d),
    TensorRealization left right joint ∧
      x = diamondDistance (joint.comp encoding.source) encoding.target}

def mixtureErrors (M : Model Sector spectralSize) (encoding : EncodingChannels M) : Set ℝ :=
  {x | ∃ m : ℕ, ∃ weight ∈ stdSimplex ℝ (Fin m),
    ∃ left : Fin m → QuantumChannel
      (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d),
    ∃ right : Fin m → QuantumChannel
      (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d),
    ∃ joint : QuantumChannel
      (SourceLocal (Coord := Fin spectralSize) M.d × SourceLocal (Coord := Fin spectralSize) M.d)
      (TargetLocal M.d × TargetLocal M.d),
    MixtureRealization weight left right joint ∧
      x = diamondDistance (joint.comp encoding.source) encoding.target}

/-- The full model asks for actual encoding channels, all admissible operations,
both equal infima, and a product construction attaining their common value. -/
def FullOptimalityClaim [Nonempty Sector] (M : Model Sector spectralSize) : Prop :=
  ∃ encoding : EncodingChannels M,
    (∀ left : QuantumChannel (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d),
      ∀ right : QuantumChannel (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d),
      ∃ joint : QuantumChannel
        (SourceLocal (Coord := Fin spectralSize) M.d × SourceLocal (Coord := Fin spectralSize) M.d)
        (TargetLocal M.d × TargetLocal M.d), TensorRealization left right joint) ∧
    (∀ m : ℕ, ∀ weight ∈ stdSimplex ℝ (Fin m),
      ∀ left : Fin m → QuantumChannel
        (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d),
      ∀ right : Fin m → QuantumChannel
        (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d),
      ∃ joint : QuantumChannel
        (SourceLocal (Coord := Fin spectralSize) M.d × SourceLocal (Coord := Fin spectralSize) M.d)
        (TargetLocal M.d × TargetLocal M.d), MixtureRealization weight left right joint) ∧
    sInf (productErrors M encoding) = 2 * (1 - spectralMinimum M) ∧
    sInf (mixtureErrors M encoding) = 2 * (1 - spectralMinimum M) ∧
    2 * (1 - spectralMinimum M) ∈ productErrors M encoding



def ConstructiveOptimalityClaim [Nonempty Sector] (M : Model Sector spectralSize) : Prop :=
  ∃ encoding : EncodingChannels M,
  ∃ splitting : QuantumChannel (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d),
  ∃ joint : QuantumChannel
      (SourceLocal (Coord := Fin spectralSize) M.d × SourceLocal (Coord := Fin spectralSize) M.d)
      (TargetLocal M.d × TargetLocal M.d),
    TensorRealization splitting splitting joint ∧
    (∀ X : Matrix (SourceLocal (Coord := Fin spectralSize) M.d)
        (SourceLocal (Coord := Fin spectralSize) M.d) ℂ,
      CStarMatrix.ofMatrix.symm
        (splitting.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      (fun b c => ∑ j : Fin spectralSize,
        X ⟨b.1, (b.2, j)⟩ ⟨c.1, (c.2, j)⟩)) ∧
    (∀ X : Matrix Sector Sector ℂ,
      CStarMatrix.ofMatrix.symm
        ((joint.comp encoding.source).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      targetEncoding M.d * (Matrix.of fun s t => (kernel M s t : ℂ) * X s t) *
        (targetEncoding M.d)ᴴ) ∧
    (∀ s : Sector,
      (joint.comp encoding.source).toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (Matrix.single s s 1)) =
      encoding.target.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (Matrix.single s s 1))) ∧
    diamondDistance (joint.comp encoding.source) encoding.target =
      2 * (1 - spectralMinimum M) ∧
    sInf (productErrors M encoding) = 2 * (1 - spectralMinimum M) ∧
    sInf (mixtureErrors M encoding) = 2 * (1 - spectralMinimum M)


def FlatFeasibilityClaim : Prop :=
  ∀ (r d : Sector → ℕ), (∀ s, 0 < r s) → (∀ s, 0 < d s) →
    ((∃ left : QuantumChannel (TargetLocal r) (TargetLocal d),
      ∃ right : QuantumChannel (TargetLocal r) (TargetLocal d),
      ∀ s : Sector,
        tensorRawAction left right
          (Matrix.vecMulVec (fun xy => targetEncoding r xy s)
            (star (fun xy => targetEncoding r xy s))) =
        Matrix.vecMulVec (fun xy => targetEncoding d xy s)
          (star (fun xy => targetEncoding d xy s))) ↔
      ∀ s : Sector, ∃ m : ℕ, 0 < m ∧ r s = d s * m)


end D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
