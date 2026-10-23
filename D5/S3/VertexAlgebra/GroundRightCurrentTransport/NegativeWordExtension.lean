/- GID: D5/S3/VertexAlgebra/GroundRightCurrentTransport/NegativeWordExtension
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GroundRightCurrentTransport/NegativeWordExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First-source compatibility propagated through every finite negative-current word. -/

import D5.S3.VertexAlgebra.GroundRightCurrentTransport.LeftCurrentStep

/-! The conditional native current insertion is consumed here by induction on
    the actual negative-current word.  The ground-pair family remains an
    explicit premise, so this file does not hide the remaining charged-base
    obligation behind an axiom or an unprojected compatibility assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators VertexOperator
namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
open LatticeGeneratingFieldLocality LatticeAllStateReconstruction
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockPhysicalRescaling LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeHalfFockLeftCurrentTransport

/-! A finite negative word on the first source is the same actual word
    constructor used by the existing oscillator expansion on the second
    source.  Its source lift increases once per letter because
    `left_current_step` consumes one current insertion. -/
theorem projectedGround_left_current_word
    (D : LatticeData) (hu : IsUnit D.G.det)
    (groundPair : SectorGroundPair D hu)
    (word : List (Index D))
    (alpha : Charge D) (epsilon : Bool) (gamma : ℤ)
    (hgamma : sectorSign epsilon = (-1 : ℂ) ^ gamma) :
    ∀ (b : Carrier D) (delta : ℤ),
      OriginalCompatible D hu (rightCurrentWord D word
        (projectedGround D alpha epsilon)) b
        (gamma + (word.length : ℤ)) delta := by
  induction word generalizing gamma with
  | nil =>
      intro b delta
      simpa only [rightCurrentWord, List.length_nil, Nat.cast_zero, add_zero] using
        projectedGround_arbitrary_second D hu groundPair alpha epsilon
          gamma delta b hgamma
  | cons j w ih =>
      intro b delta
      have tail : ∀ (b' : Carrier D) (delta' : ℤ),
          OriginalCompatible D hu (rightCurrentWord D w
            (projectedGround D alpha epsilon)) b'
            (gamma + (w.length : ℤ)) delta' :=
        ih gamma hgamma
      have step := left_current_step D hu j.1
        (rightCurrentWord D w (projectedGround D alpha epsilon))
        (gamma + (w.length : ℤ)) (-((j.2 + 1 : ℕ) : ℤ)) tail b delta
      simpa [rightCurrentWord, List.length_cons, add_assoc] using step

end D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
