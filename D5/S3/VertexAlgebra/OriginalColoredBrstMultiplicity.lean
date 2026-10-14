/- GID: D5/S3/VertexAlgebra/OriginalColoredBrstMultiplicity
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/OriginalColoredBrstMultiplicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original nonzero-charge on-shell ghost multiplicities are independent colored partition coefficients. -/

import D5.S3.VertexAlgebra.ColoredFockCharacter
import D5.S3.VertexAlgebra.OriginalAbsoluteGradedSector
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.OriginalColoredBrstMultiplicity

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  OriginalQQuartetSource OriginalQEnergyInclusionPairing OriginalBrstReassembly
  OriginalAbsoluteGradedSector LatticeOscillatorFockMetric
  RelativePairing.AbsolutePhysicalNoGhost
open scoped BigOperators

noncomputable section

variable (D : LatticeData) (xAxis yAxis : Fin D.rank)

abbrev TransverseColors := {axis : Fin D.rank // axis ≠ xAxis ∧ axis ≠ yAxis}

def transverseEmbedding : TransverseColors D xAxis yAxis × ℕ ↪ Index D where
  toFun index := (index.1.val, index.2)
  inj' := by
    intro first second equality
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun index : Index D => index.1) equality)
    · exact congrArg (fun index : Index D => index.2) equality

private theorem transverseColors_card (distinct : xAxis ≠ yAxis) :
    Fintype.card (TransverseColors D xAxis yAxis) = D.rank - 2 := by
  classical
  change Fintype.card {axis : Fin D.rank // axis ≠ xAxis ∧ axis ≠ yAxis} = _
  calc
    _ = Fintype.card ↥(({xAxis, yAxis} : Finset (Fin D.rank))ᶜ) := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (fun axis => by simp)
    _ = D.rank - 2 := by
      rw [Fintype.card_coe, Finset.card_compl]
      simp [distinct]

private theorem lift_nativeLevel (powers : ColoredFockCharacter.Occupation
    (TransverseColors D xAxis yAxis)) :
    nativeLevel D (Finsupp.embDomain (transverseEmbedding D xAxis yAxis) powers) ∅ =
      (ColoredFockCharacter.energy (TransverseColors D xAxis yAxis) powers : ℤ) := by
  simp only [nativeLevel, polarizedLevel, Finset.sum_empty, add_zero,
    Finsupp.weight_apply, Finsupp.sum_embDomain, frequencyWeight, smul_eq_mul]
  congr 1
  exact Finsupp.sum_congr (fun _ _ => Nat.mul_comm _ _)

private theorem down_support (level : ℤ) (powers : TransverseDownIndex D xAxis yAxis level) :
    ↑powers.val.support ⊆ Set.range (transverseEmbedding D xAxis yAxis) := by
  intro index member
  have nonzero := Finsupp.mem_support_iff.mp member
  have xAbsent : index.1 ≠ xAxis := by
    intro same
    exact nonzero (by simpa [← same] using powers.property.1 index.2)
  have yAbsent : index.1 ≠ yAxis := by
    intro same
    exact nonzero (by simpa [← same] using powers.property.2.1 index.2)
  exact ⟨(⟨index.1, xAbsent, yAbsent⟩, index.2), rfl⟩

def downOccupationEquiv (level : ℕ) :
    TransverseDownIndex D xAxis yAxis (level : ℤ) ≃
      ColoredFockCharacter.EnergyFiber (TransverseColors D xAxis yAxis) level where
  toFun powers :=
    ⟨Finsupp.comapDomain (transverseEmbedding D xAxis yAxis) powers.val
      (transverseEmbedding D xAxis yAxis).injective.injOn, by
      have equality := lift_nativeLevel D xAxis yAxis
        (Finsupp.comapDomain (transverseEmbedding D xAxis yAxis) powers.val
          (transverseEmbedding D xAxis yAxis).injective.injOn)
      rw [Finsupp.embDomain_comapDomain (down_support D xAxis yAxis _ powers),
        powers.property.2.2] at equality
      exact_mod_cast equality.symm⟩
  invFun powers :=
    ⟨Finsupp.embDomain (transverseEmbedding D xAxis yAxis) powers.val,
      (by
        intro frequency
        apply Finsupp.embDomain_of_notMem_range
        rintro ⟨index, equality⟩
        exact index.1.property.1 (congrArg Prod.fst equality)),
      (by
        intro frequency
        apply Finsupp.embDomain_of_notMem_range
        rintro ⟨index, equality⟩
        exact index.1.property.2 (congrArg Prod.fst equality)),
      by rw [lift_nativeLevel, powers.property]⟩
  left_inv powers := Subtype.ext
    (Finsupp.embDomain_comapDomain (down_support D xAxis yAxis _ powers))
  right_inv powers := Subtype.ext (Finsupp.comapDomain_embDomain _ _)

private theorem downIndex_negative (level : ℤ) (negative : level < 0) :
    IsEmpty (TransverseDownIndex D xAxis yAxis level) := by
  constructor
  intro powers
  have bound := nativeLevel_nonnegative D xAxis yAxis powers.val ∅
  rw [powers.property.2.2] at bound
  omega

instance downIndex_finite (level : ℤ) : Finite (TransverseDownIndex D xAxis yAxis level) := by
  by_cases negative : level < 0
  · letI := downIndex_negative D xAxis yAxis level negative
    infer_instance
  · have equality : (level.toNat : ℤ) = level := Int.toNat_of_nonneg (by omega)
    rw [← equality]
    exact Finite.of_equiv
      (ColoredFockCharacter.EnergyFiber (TransverseColors D xAxis yAxis) level.toNat)
      (downOccupationEquiv D xAxis yAxis level.toNat).symm

def coloredMultiplicity (colors : ℕ) (level : ℤ) : ℕ :=
  if level < 0 then 0 else PowerSeries.coeff level.toNat
    ((Nat.Partition.genFun (fun _ _ => (1 : ℕ))) ^ colors)

abbrev p24 (level : ℤ) : ℕ := coloredMultiplicity 24 level

theorem downIndex_card (distinct : xAxis ≠ yAxis) (level : ℤ) :
    Nat.card (TransverseDownIndex D xAxis yAxis level) =
      coloredMultiplicity (D.rank - 2) level := by
  classical
  by_cases negative : level < 0
  · letI := downIndex_negative D xAxis yAxis level negative
    simp [coloredMultiplicity, negative]
  · have equality : (level.toNat : ℤ) = level := Int.toNat_of_nonneg (by omega)
    conv_lhs => rw [← equality]
    rw [Nat.card_congr (downOccupationEquiv D xAxis yAxis level.toNat),
      ColoredFockCharacter.energyFiber_card]
    simp only [ColoredFockCharacter.partitionCoefficient, transverseColors_card D xAxis yAxis distinct,
      coloredMultiplicity, if_neg negative]

variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (leftGram : H * gramComplex D = 1) (rightGram : gramComplex D * H = 1)
variable (beta : Charge D) (level : ℤ) (critical : D.rank = 26)
variable (shell : chosenH D beta + (level : ℂ) - 1 = 0) (chargeNonzero : beta ≠ 0)
variable (lorentzian : QuadraticForms.ActualSignature.signature (gramReal D).toQuadraticForm' =
  (D.rank : ℤ) - 2)

local notation "sector" => originalEnergySector D H beta level
local notation "stable" => energyStable D H leftGram rightGram beta level
local notation "degreeCohomology" => ghostCohomology D H leftGram rightGram critical sector stable

include shell chargeNonzero lorentzian in
theorem original_brst_multiplicities :
    Module.finrank ℂ (degreeCohomology 1) = p24 level ∧
    Module.finrank ℂ (degreeCohomology 2) = p24 level ∧
    Module.finrank ℂ (Cohomology D H leftGram rightGram critical sector stable) =
      2 * p24 level := by
  classical
  let native := choice D H leftGram rightGram beta critical chargeNonzero lorentzian
  let indices := TransverseDownIndex D native.xAxis native.yAxis level
  letI : Fintype indices := Fintype.ofFinite indices
  have count : Module.finrank ℂ (indices →₀ ℂ) = p24 level := by
    rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card]
    simpa only [critical, Nat.reduceSub] using
      downIndex_card D native.xAxis native.yAxis native.distinct level
  refine ⟨?_, ?_, ?_⟩
  · rw [← (downEquiv D H leftGram rightGram beta level critical shell chargeNonzero
      lorentzian).finrank_eq]
    exact count
  · rw [← (upEquiv D H leftGram rightGram beta level critical shell chargeNonzero
      lorentzian).finrank_eq]
    exact count
  · rw [(ungradedEquiv D H leftGram rightGram beta level critical shell chargeNonzero
      lorentzian).finrank_eq, Module.finrank_prod, count]
    omega

end

end D5.S3.VertexAlgebra.OriginalColoredBrstMultiplicity
