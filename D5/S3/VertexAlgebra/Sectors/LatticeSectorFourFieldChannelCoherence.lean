/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldChannelCoherence
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldChannelCoherence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite middle-channel readout transported across four-field
   FullIO reassociation.
-/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorFourFieldFullIOReadout

/-!
This module consumes the actual four-variable numerator readout rather than
reproving the abstract linear-equivalence equality.  The source channel is
right-associated, while the finite readout is taken after the middle charge
transport used by the alternate channel.  The returned coefficient identity
is the finite `middleCoefficient` contraction, including its support bound;
the same witness is therefore available at the crossing path itself by the
explicit FullIO path equality.

This is the first finite-target crossing consumer.  It does not assert a
sewing, convergence, positivity, or physical realization principle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSectorFourFieldChannelCoherence

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticeSectorIntertwiner LatticeSectorIntertwiner.FiniteSectorObject
open LatticeSectorChannelTransport LatticeSectorFourFieldCommonSeries
open LatticeSectorFourFieldInnerIterate LatticeSectorFourFieldMiddleSpectator
open LatticeSectorFourFieldRawMiddleCoefficients
open D5.S3.VertexAlgebra.LatticeSectorFourFieldFullIOReadout
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedChannelSeries
open FourFieldInnerPolynomial FourFieldMiddlePolynomial SupportedFourFieldMiddleCollision
open FourFieldMiddleLaurentFiber
open StateFieldResidueReconstruction (integerBinomial)
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators
noncomputable section

private def incomingChargeAssoc (D : LatticeData)
    (M : FiniteSectorObject D) {p q : Charge D} (h : p = q) :
    Incoming D p M ≃ₗ[ℂ] Incoming D q M where
  toFun f := ⟨f.val, by
    intro a n x
    have e := congrArg (fun δ : Charge D => action D δ a n x) h
    exact (congrArg f.val e).symm.trans (f.property a n x)⟩
  invFun f := ⟨f.val, by
    intro a n x
    have e := congrArg (fun δ : Charge D => action D δ a n x) h
    exact (congrArg f.val e).trans (f.property a n x)⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv f := by apply Subtype.ext; rfl
  map_add' f g := rfl
  map_smul' c f := rfl

private def middleChargeAssoc (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ δ : Charge D) (M : FiniteSectorObject D) :
    FullIO D α (β + (γ + δ)) M ≃ₗ[ℂ] FullIO D α ((β + γ) + δ) M :=
  (fullUniversal D H hHG hGH α (β + (γ + δ)) M).symm.trans
    ((incomingChargeAssoc D M (by rw [add_assoc β γ δ])).trans
      (fullUniversal D H hHG hGH α ((β + γ) + δ) M))

/--
For a right-associated source field, the actual four-variable numerator gives
the finite middle-channel readout after the charge reassociation used by the
alternate path.  The final conjunct records the equality with the short path,
so the readout is a crossing witness rather than an abstract path statement.
-/
theorem actual_four_field_channel_readout_transport
    (D : LatticeData) (α β γ η δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ)
    (q : Sector D η) (w : Sector D δ)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (M : FiniteSectorObject D)
    (F : FullIO D α (β + (γ + (η + δ))) M)
    (b y r s : ℤ) (ι : Fin M.size) :
    ∃ k : ℕ, ∃ a : Fin 4 → ℕ,
      ∃ P : MvPowerSeries (Fin 4) (Oscillator D),
      ∃ N A B : ℕ, ∃ Q : MvPowerSeries (Fin 2) (M.States D),
        (∀ x z : ℤ,
          clear N
              (fun x z =>
                ((middleChargeAssoc D H hHG hGH α β γ (η + δ) M F).val u (-x - 1))
                  (canonical D (β + γ) (η + δ)
                    (canonical D β γ v (-b - 1) t) (-z - 1)
                    (canonical D η δ q (-y - 1) w)))
              (x - A) (z - B) = extend Q x z) ∧
        (∀ r s : ℤ,
          (clearIterate N A B
            (fun r s : ℤ =>
              (fullChannel D H hHG hGH α (β + γ) (η + δ) M
                (middleChargeAssoc D H hHG hGH α β γ (η + δ) M F)).val
                (canonical D α (β + γ) u (-r - 1)
                  (canonical D β γ v (-b - 1) t)) (-s - 1)
                  (canonical D η δ q (-y - 1) w)) r s) ι =
            ∑ i ∈ Finset.range
                ((s - B + b + y + a 1 + a 2 + a 3 + 3 * k).toNat + 1),
              ∑ h ∈ middleFiber k a
                ![r - A - N + i, b, s - B - i, y],
                (((-1 : ℂ) ^ i) *
                    integerBinomial ((N : ℤ) - r - 1) i) •
                  (middleWeight k a h •
                    (((fullUniversal D H hHG hGH α ((β + γ) + (η + δ)) M).symm
                      (middleChargeAssoc D H hHG hGH α β γ (η + δ) M F)).val
                        (signedExtend
                          (MvPowerSeries.subst
                            (middleFourArguments (Oscillator D)) P)
                          (middleInput k a
                            ![r - A - N + i, b, s - B - i, y] h)) ι))) ∧
        (fourFieldShortPath D H hHG hGH α β γ (η + δ) M =
          fourFieldAlternatePath D H hHG hGH α β γ (η + δ) M) := by
  classical
  obtain ⟨k, _locality, rest⟩ :=
    actual_four_field_fullIO_middle_readout D α β γ η u v t q
  obtain ⟨a, P, _truncation, _allOrders, _inner, _middle, _raw, readout⟩ :=
    rest δ w
  let Fmid := middleChargeAssoc D H hHG hGH α β γ (η + δ) M F
  obtain ⟨N, A, B, Q, common, finiteReadout⟩ :=
    readout H hHG hGH M Fmid b y
  refine ⟨k, a, P, N, A, B, Q, ?_, ?_, ?_⟩
  · intro x z
    exact (common x z).1
  · intro r s
    simpa [Fmid] using finiteReadout r s ι
  · exact fourField_reassociation_path_eq D H hHG hGH α β γ (η + δ) M

#print axioms actual_four_field_channel_readout_transport

end
end D5.S3.VertexAlgebra.LatticeSectorFourFieldChannelCoherence
