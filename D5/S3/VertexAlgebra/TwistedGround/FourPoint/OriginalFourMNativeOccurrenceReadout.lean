/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccurrenceReadout
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccurrenceReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native four-slot occupation and factorial readout of a surviving word. -/

import D5.S3.VertexAlgebra.TwistedGround.AffineOccurrenceWick
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction

/-! Collisions of surviving native labels give the literal four factorial
Fock weights of the external occupation. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMNativeOccurrenceReadout

open LatticeGeneratingFieldLocality LatticeHalfFock
open OriginalGaussianSourceRestriction (CompactExternal externalOccupation)
open OriginalNormalRowSource (supportLabel restricted embedded_weight)
open NativeAffineExternalCoefficient (jetOccupation)
open AffineOccurrenceWick (affineMoment_pullback)
open OriginalChargedRowSource (affineMoment affineMoment_coefficient affineCoefficient)
open FactorialFockMetric (weight)

private theorem occupation_sum {I J : Type*} (l : List (I ⊕ J)) :
    jetOccupation l = (jetOccupation (l.filterMap Sum.getLeft?)).sumElim
      (jetOccupation (l.filterMap Sum.getRight?)) := by
  classical
  induction l with
  | nil => ext (x | x) <;> simp [jetOccupation]
  | cons a l ih =>
    cases a <;> ext (x | x) <;>
      simp [jetOccupation, ih, List.filterMap_cons, Sum.getLeft?, Sum.getRight?] <;>
      simp only [Finsupp.single_apply, Sum.inl.injEq, Sum.inr.injEq]

private theorem restricted_embDomain (D : LatticeData) (F : Finset (Index D))
    (d : {b // b ∈ F} →₀ ℕ) :
    restricted D F (d.embDomain (supportLabel D F)) = d := by
  ext i
  change d.embDomain (supportLabel D F) (supportLabel D F i) = d i
  simp

private theorem weight_sumElim {I J : Type*} (d : I →₀ ℕ) (h : J →₀ ℕ) :
    weight (d.sumElim h) = weight d * weight h := by
  simp only [weight, Finsupp.prod_sumElim, Function.comp_def]

/-- Count each surviving native letter in its own input or output slot,
then forget the proof that its oscillator index belongs to the finite support. -/
def slotOccupation (D : LatticeData) (F : Finset (Index D))
    (l : List {b // b ∈ F}) : Index D →₀ ℕ :=
  (jetOccupation l).embDomain (supportLabel D F)

/-- The original two tagged legs each retain two independent occupations.
The readout multiplies the literal affine coefficient by the four factorial
Fock weights, even when the projection identifies several occurrences. -/
theorem native_occurrence_readout {X : Type*} [Fintype X] (D : LatticeData)
    (F : Finset (Index D))
    (K : Matrix (CompactExternal D F ⊕ CompactExternal D F)
      (CompactExternal D F ⊕ CompactExternal D F) ℂ)
    (μ : CompactExternal D F ⊕ CompactExternal D F → ℂ)
    (hs : ∀ i j, K i j = K j i)
    (label : X → CompactExternal D F ⊕ CompactExternal D F) (l : List X) :
    let left := (l.map label).filterMap Sum.getLeft?
    let right := (l.map label).filterMap Sum.getRight?
    let b := slotOccupation D F (left.filterMap Sum.getLeft?)
    let g := slotOccupation D F (left.filterMap Sum.getRight?)
    let d := slotOccupation D F (right.filterMap Sum.getLeft?)
    let e := slotOccupation D F (right.filterMap Sum.getRight?)
    affineMoment (K.submatrix label label) (μ ∘ label) (jetOccupation l) =
      (weight b : ℂ) * (weight g : ℂ) * ((weight d : ℂ) * (weight e : ℂ)) *
        affineCoefficient K μ (externalOccupation D F b g d e) := by
  dsimp only
  rw [affineMoment_pullback K μ hs label l, affineMoment_coefficient]
  let L := (l.map label).filterMap Sum.getLeft?
  let R := (l.map label).filterMap Sum.getRight?
  have ho : jetOccupation (l.map label) =
      externalOccupation D F (slotOccupation D F (L.filterMap Sum.getLeft?))
        (slotOccupation D F (L.filterMap Sum.getRight?))
        (slotOccupation D F (R.filterMap Sum.getLeft?))
        (slotOccupation D F (R.filterMap Sum.getRight?)) := by
    rw [externalOccupation]
    simp only [slotOccupation, restricted_embDomain]
    rw [occupation_sum (l.map label)]
    change (jetOccupation L).sumElim (jetOccupation R) = _
    rw [occupation_sum L, occupation_sum R]
  change _ = (weight (slotOccupation D F (L.filterMap Sum.getLeft?)) : ℂ) *
    (weight (slotOccupation D F (L.filterMap Sum.getRight?)) : ℂ) *
    ((weight (slotOccupation D F (R.filterMap Sum.getLeft?)) : ℂ) *
      (weight (slotOccupation D F (R.filterMap Sum.getRight?)) : ℂ)) * _
  rw [ho]
  simp only [externalOccupation, weight_sumElim, Nat.cast_mul, slotOccupation,
    restricted_embDomain, embedded_weight]
  rfl

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMNativeOccurrenceReadout
