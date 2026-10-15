/- GID: D5/S3/VertexAlgebra/OriginalZeroChargeEnergySector
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/OriginalZeroChargeEnergySector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete native zero-charge zero-energy support without a signature assumption. -/

import D5.S3.VertexAlgebra.BcGhostLZeroSpectrum
import D5.S3.VertexAlgebra.BcGhostNumber
import D5.S3.VertexAlgebra.LatticePositiveEnergy
import D5.S3.VertexAlgebra.LatticeSugawaraConformal
import D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.Supported

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalZeroChargeEnergySector

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraConformal
  LatticeBcGhostBrstCharge BcGhostFockSupport LatticePositiveEnergy
open scoped BigOperators TensorProduct

noncomputable section

private theorem weight_nonnegative (site : ℕ) (different : site ≠ 1) :
    0 ≤ BcGhostLZeroSpectrum.siteWeight site := by
  unfold BcGhostLZeroSpectrum.siteWeight
  split_ifs <;> omega

private theorem weight_large (site : ℕ) (large : 5 < site) :
    2 ≤ BcGhostLZeroSpectrum.siteWeight site := by
  unfold BcGhostLZeroSpectrum.siteWeight
  split_ifs <;> omega

private theorem energy_without_one_nonnegative (subset : Finset ℕ) :
    0 ≤ BcGhostLZeroSpectrum.energy (subset.erase 1) := by
  apply Finset.sum_nonneg
  intro site member
  exact weight_nonnegative site (Finset.mem_erase.mp member).1

private theorem energy_erase_one (subset : Finset ℕ) :
    BcGhostLZeroSpectrum.energy (subset.erase 1) =
      BcGhostLZeroSpectrum.energy subset + if 1 ∈ subset then 1 else 0 := by
  by_cases present : 1 ∈ subset
  · have split := Finset.sum_erase_add subset BcGhostLZeroSpectrum.siteWeight present
    have weight : BcGhostLZeroSpectrum.siteWeight 1 = -1 := by decide
    change BcGhostLZeroSpectrum.energy (subset.erase 1) +
      BcGhostLZeroSpectrum.siteWeight 1 = BcGhostLZeroSpectrum.energy subset at split
    rw [weight] at split
    rw [if_pos present]
    omega
  · simp [present]

theorem ghost_energy_lower_bound (subset : Finset ℕ) :
    -1 ≤ BcGhostLZeroSpectrum.energy subset := by
  have nonnegative := energy_without_one_nonnegative subset
  rw [energy_erase_one] at nonnegative
  split_ifs at nonnegative <;> omega

theorem ghost_nonpositive_support (subset : Finset ℕ)
    (nonpositive : BcGhostLZeroSpectrum.energy subset ≤ 0) :
    subset ⊆ Finset.range 6 := by
  intro site member
  rw [Finset.mem_range]
  by_contra notSmall
  have large : 5 < site := by omega
  have erasedMember : site ∈ subset.erase 1 := Finset.mem_erase.mpr ⟨by omega, member⟩
  have termBound := Finset.single_le_sum
    (fun other otherMember => weight_nonnegative other (Finset.mem_erase.mp otherMember).1)
    erasedMember
  change BcGhostLZeroSpectrum.siteWeight site ≤
    BcGhostLZeroSpectrum.energy (subset.erase 1) at termBound
  have high := weight_large site large
  rw [energy_erase_one] at termBound
  split_ifs at termBound <;> omega

private theorem finite_ghost_classification :
    ∀ subset ∈ (Finset.range 6).powerset,
      BcGhostLZeroSpectrum.energy subset ≤ 0 →
        subset = ∅ ∨ subset = {3} ∨ subset = {1} ∨ subset = {1, 3} ∨
          subset = {1, 5} ∨ subset = {1, 3, 5} := by
  decide

theorem ghost_nonpositive_classification (subset : Finset ℕ) :
    BcGhostLZeroSpectrum.energy subset ≤ 0 ↔
      subset = ∅ ∨ subset = {3} ∨ subset = {1} ∨ subset = {1, 3} ∨
        subset = {1, 5} ∨ subset = {1, 3, 5} := by
  constructor
  · intro nonpositive
    exact finite_ghost_classification subset
      (Finset.mem_powerset.mpr (ghost_nonpositive_support subset nonpositive)) nonpositive
  · intro alternatives
    rcases alternatives with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem oscillator_one_classification (D : LatticeData) (powers : Exponent D)
    (level : oscillatorEnergy powers = 1) :
    ∃ axis : Fin D.rank, powers = Finsupp.single (axis, 0) 1 := by
  classical
  have nonzero : powers ≠ 0 := by
    intro zero
    simp [zero, oscillatorEnergy] at level
  obtain ⟨site, occupied⟩ := Finsupp.ne_iff.mp nonzero
  simp only [Finsupp.zero_apply] at occupied
  have frequencyBound := Finsupp.le_weight_of_ne_zero'
    (fun index : Index D => index.2 + 1) occupied
  change site.2 + 1 ≤ oscillatorEnergy powers at frequencyBound
  have frequency : site.2 = 0 := by omega
  have countBound := Finsupp.le_weight (fun index : Index D => index.2 + 1)
    (s := site) (by omega) powers
  change powers site ≤ oscillatorEnergy powers at countBound
  have count : powers site = 1 := by omega
  have decomposition : powers = powers.erase site + Finsupp.single site 1 := by
    ext other
    by_cases same : other = site
    · simp [same, count]
    · simp [same]
  have erasedLevel : oscillatorEnergy (powers.erase site) = 0 := by
    have split := congrArg oscillatorEnergy decomposition
    simp only [oscillatorEnergy, map_add, Finsupp.weight_single, frequency,
      zero_add, one_nsmul] at split
    change oscillatorEnergy powers = oscillatorEnergy (powers.erase site) + 1 at split
    omega
  have erased : powers.erase site = 0 :=
    (oscillatorEnergy_eq_zero_iff D _).mp erasedLevel
  refine ⟨site.1, ?_⟩
  rw [erased, zero_add] at decomposition
  have siteZero : site = (site.1, 0) := Prod.ext rfl frequency
  exact decomposition.trans (congrArg (fun source : Index D => Finsupp.single source 1) siteZero)

theorem zero_energy_labels (D : LatticeData) (powers : Exponent D) (subset : Finset ℕ) :
    (oscillatorEnergy powers : ℤ) + BcGhostLZeroSpectrum.energy subset = 0 ↔
      (powers = 0 ∧ (subset = ∅ ∨ subset = {3} ∨
        subset = {1, 5} ∨ subset = {1, 3, 5})) ∨
      ((∃ axis : Fin D.rank, powers = Finsupp.single (axis, 0) 1) ∧
        (subset = {1} ∨ subset = {1, 3})) := by
  constructor
  · intro total
    have nonpositive : BcGhostLZeroSpectrum.energy subset ≤ 0 := by omega
    have bound := ghost_energy_lower_bound subset
    have levelBound : oscillatorEnergy powers ≤ 1 := by omega
    have alternatives := (ghost_nonpositive_classification subset).mp nonpositive
    rcases alternatives with rfl | rfl | rfl | rfl | rfl | rfl
    · left
      refine ⟨?_, Or.inl rfl⟩
      norm_num [BcGhostLZeroSpectrum.energy, BcGhostLZeroSpectrum.siteWeight] at total
      exact total
    · left
      refine ⟨?_, Or.inr (Or.inl rfl)⟩
      norm_num [BcGhostLZeroSpectrum.energy, BcGhostLZeroSpectrum.siteWeight] at total
      exact total
    · right
      refine ⟨oscillator_one_classification D powers ?_, Or.inl rfl⟩
      norm_num [BcGhostLZeroSpectrum.energy, BcGhostLZeroSpectrum.siteWeight] at total
      omega
    · right
      refine ⟨oscillator_one_classification D powers ?_, Or.inr rfl⟩
      norm_num [BcGhostLZeroSpectrum.energy, BcGhostLZeroSpectrum.siteWeight] at total
      omega
    · left
      refine ⟨?_, Or.inr (Or.inr (Or.inl rfl))⟩
      norm_num [BcGhostLZeroSpectrum.energy, BcGhostLZeroSpectrum.siteWeight] at total
      exact total
    · left
      refine ⟨?_, Or.inr (Or.inr (Or.inr rfl))⟩
      norm_num [BcGhostLZeroSpectrum.energy, BcGhostLZeroSpectrum.siteWeight] at total
      exact total
  · rintro (⟨rfl, alternatives⟩ | ⟨⟨axis, rfl⟩, alternatives⟩)
    · rcases alternatives with rfl | rfl | rfl | rfl <;>
        norm_num [oscillatorEnergy, BcGhostLZeroSpectrum.energy,
          BcGhostLZeroSpectrum.siteWeight]
    · rcases alternatives with rfl | rfl <;>
        norm_num [oscillatorEnergy, Finsupp.weight_single,
          BcGhostLZeroSpectrum.energy, BcGhostLZeroSpectrum.siteWeight]

#print axioms ghost_nonpositive_support
#print axioms zero_energy_labels

end
end D5.S3.VertexAlgebra.OriginalZeroChargeEnergySector
