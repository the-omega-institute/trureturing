/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldChannelCrossing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldChannelCrossing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite four-field channel crossing readout built on the frozen coherence transport. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorFourFieldChannelCoherence

/-!
This module keeps the finite channel-crossing consumer separate from the
frozen four-field readout transport module.  It reuses the common numerator,
support bounds, and reassociation path equality, and records the same finite
coefficient readout on both channels.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSectorFourFieldChannelCrossing

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

private def finalChargeAssoc (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ δ : Charge D) (M : FiniteSectorObject D) :
    FullIO D ((α + β) + γ) δ M ≃ₗ[ℂ] FullIO D (α + (β + γ)) δ M :=
  ((fullUniversal D H hHG hGH (α + (β + γ)) δ M).symm.trans
    ((incomingChargeAssoc D M
      (congrArg (fun p : Charge D => p + δ) (add_assoc α β γ).symm)).trans
      (fullUniversal D H hHG hGH ((α + β) + γ) δ M))).symm

/-- The common cleared four-field numerator and its support data give the
same finite coefficient readout for the middle channel and the short path,
after transporting the latter's final charge association. -/
theorem actual_four_field_channel_crossing
    (D : LatticeData) (α β γ η δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ)
    (q : Sector D η) (w : Sector D δ)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (M : FiniteSectorObject D)
    (F : FullIO D α (β + (γ + (η + δ))) M)
    (b y : ℤ) (ι : Fin M.size) :
    let c : Fin 4 → Charge D := ![α, β, γ, η]
    let states : Fin 4 → Oscillator D := ![u, v, t, q]
    let Fmid := middleChargeAssoc D H hHG hGH α β γ (η + δ) M F
    let Jmid := fullChannel D H hHG hGH α (β + γ) (η + δ) M Fmid
    let Jshort := finalChargeAssoc D H hHG hGH α β γ (η + δ) M
      (fourFieldShortPath D H hHG hGH α β γ (η + δ) M F)
    ∃ k : ℕ, ∃ a : Fin 4 → ℕ,
      ∃ P : MvPowerSeries (Fin 4) (Oscillator D),
        (∀ (i : Fin 4) (n : ℤ), (a i : ℤ) ≤ n →
          canonical D (c i) δ (states i) n w = 0) ∧
        (∀ (i j l m : Fin 4), ([0, 1, 2, 3] : List (Fin 4)).Perm [i, j, l, m] →
          ∀ e : Exponent 4,
            polynomialAction (clearingPolynomial 4 k)
              (nestedCanonical D c states δ w i j l m)
              (fun n => e n - a n) = signedExtend P e) ∧
        (∀ e : Exponent 4,
          middleIterate D α β γ η δ u v t q w (e 0) (e 1) (e 2) (e 3) =
            middleCoefficient
              (MvPowerSeries.subst (middleFourArguments (Oscillator D)) P) k a e) ∧
        ∃ N A B : ℕ, ∃ Q : MvPowerSeries (Fin 2) (M.States D),
          (∀ x z : ℤ,
            clear N
                (fun x z => Fmid.val u (-x - 1)
                  (canonical D (β + γ) (η + δ)
                    (canonical D β γ v (-b - 1) t) (-z - 1)
                    (canonical D η δ q (-y - 1) w)))
                (x - A) (z - B) = extend Q x z ∧
            clearIterate N A B
                (fun r s => Jmid.val
                  (canonical D α (β + γ) u (-r - 1)
                    (canonical D β γ v (-b - 1) t)) (-s - 1)
                    (canonical D η δ q (-y - 1) w)) x z =
              extend (collision Q) x z) ∧
          (∀ r s : ℤ,
            let readout :=
              ∑ i ∈ Finset.range
                  ((s - B + b + y + a 1 + a 2 + a 3 + 3 * k).toNat + 1),
                ∑ h ∈ middleFiber k a ![r - A - N + i, b, s - B - i, y],
                  (((-1 : ℂ) ^ i) * integerBinomial ((N : ℤ) - r - 1) i) •
                    (middleWeight k a h •
                      (((fullUniversal D H hHG hGH α ((β + γ) + (η + δ)) M).symm
                        Fmid).val
                          (signedExtend
                            (MvPowerSeries.subst (middleFourArguments (Oscillator D)) P)
                            (middleInput k a ![r - A - N + i, b, s - B - i, y] h)) ι))
            (clearIterate N A B
              (fun r s => Jmid.val
                (canonical D α (β + γ) u (-r - 1)
                  (canonical D β γ v (-b - 1) t)) (-s - 1)
                  (canonical D η δ q (-y - 1) w)) r s) ι = readout ∧
            (clearIterate N A B
              (fun r s => Jshort.val
                (canonical D α (β + γ) u (-r - 1)
                  (canonical D β γ v (-b - 1) t)) (-s - 1)
                  (canonical D η δ q (-y - 1) w)) r s) ι = readout) := by
  classical
  dsimp only
  let Fmid := middleChargeAssoc D H hHG hGH α β γ (η + δ) M F
  let Jmid := fullChannel D H hHG hGH α (β + γ) (η + δ) M Fmid
  let Jshort := finalChargeAssoc D H hHG hGH α β γ (η + δ) M
    (fourFieldShortPath D H hHG hGH α β γ (η + δ) M F)
  have crossing : Jshort = Jmid := by
    change finalChargeAssoc D H hHG hGH α β γ (η + δ) M
      (fourFieldShortPath D H hHG hGH α β γ (η + δ) M F) = Jmid
    rw [fourField_reassociation_path_eq D H hHG hGH α β γ (η + δ) M]
    change finalChargeAssoc D H hHG hGH α β γ (η + δ) M
      ((finalChargeAssoc D H hHG hGH α β γ (η + δ) M).symm Jmid) = Jmid
    exact (finalChargeAssoc D H hHG hGH α β γ (η + δ) M).apply_symm_apply Jmid
  obtain ⟨k, _locality, rest⟩ :=
    actual_four_field_fullIO_middle_readout D α β γ η u v t q
  obtain ⟨a, P, truncation, allOrders, _inner, _middle, raw, readout⟩ := rest δ w
  obtain ⟨N, A, B, Q, common, finiteReadout⟩ := readout H hHG hGH M Fmid b y
  refine ⟨k, a, P, truncation, allOrders, raw, N, A, B, Q, common, ?_⟩
  intro r s
  change (clearIterate N A B
      (fun r s => Jmid.val
        (canonical D α (β + γ) u (-r - 1) (canonical D β γ v (-b - 1) t))
        (-s - 1) (canonical D η δ q (-y - 1) w)) r s) ι = _ ∧
    (clearIterate N A B
      (fun r s => Jshort.val
        (canonical D α (β + γ) u (-r - 1) (canonical D β γ v (-b - 1) t))
        (-s - 1) (canonical D η δ q (-y - 1) w)) r s) ι = _
  rw [crossing]
  exact ⟨finiteReadout r s ι, finiteReadout r s ι⟩

#print axioms actual_four_field_channel_crossing


end
end D5.S3.VertexAlgebra.LatticeSectorFourFieldChannelCrossing
