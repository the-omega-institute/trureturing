/- GID: D5/S3/Combinatorics/Partitions/ColouredOddOccupation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/ColouredOddOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.Glaisher, mathlib/module/Mathlib.Data.Finsupp.Multiset, mathlib/module/Mathlib.RingTheory.PowerSeries.Basic]
   utility: none
   digest: Odd occupation fibres correspond to dependent finite-colour partition convolutions and their formal Euler product. -/



import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# Coloured odd occupation and formal Euler products

An occupation at mode n has weight 2*n+1. The odd-part inverse sends a part j
to mode j/2. For any finite colour type, the full weighted fibre is a dependent
sum of odd partitions over all energy allocations, with no occupation cutoff.

The multiset construction follows the architecture of
`PolynomialFockCharacter.energyFiberEquivPartition`; the odd inverse and
restricted membership are proved here. Mathlib supplies Finsupp multiset and
curry equivalences, subtype/sigma transport, finite antidiagonals and
`PowerSeries.coeff_prod`. Its restricted-partition HasProd (Weiyi Wang,
Apache 2.0) supplies the one-colour product. The finite-colour result uses the
new fibre/convolution equality. Only the product theorems use the formal
coefficient topology `PowerSeries.WithPiTopology`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.Partitions.ColouredOddOccupation

open scoped BigOperators PowerSeries.WithPiTopology

noncomputable section

/-- The actual native odd mode weight, without a second energy shift. -/
def oddWeight (n : ℕ) : ℕ := 2 * n + 1

/-- One colour's twice-oscillator energy. -/
def singleEnergy (d : ℕ →₀ ℕ) : ℕ := Finsupp.weight oddWeight d

abbrev SingleOddFiber (N : ℕ) := {d : ℕ →₀ ℕ // singleEnergy d = N}

/-- `odds N` is a finset of partitions; this is its element type. -/
abbrev OddPartition (N : ℕ) := ↥(Nat.Partition.odds N)

/-- Content: all odd occupation numbers are exactly the odd-part partitions.
The inverse replaces an odd part j by its unique mode index j / 2.
The multiset architecture reuses the public pinned source
PolynomialFockCharacter.energyFiberEquivPartition; odd weights and the restricted
partition codomain require the new inverse and membership arguments below. -/
def singleOddFiberEquivPartition (N : ℕ) : SingleOddFiber N ≃ OddPartition N := by
  classical
  have hinjWeight : Function.Injective oddWeight := by
    intro a b h
    dsimp [oddWeight] at h
    omega
  have hsum (d : ℕ →₀ ℕ) :
      (d.toMultiset.map oddWeight).sum = singleEnergy d := by
    rw [Finsupp.toMultiset_apply, Finsupp.multiset_map_sum,
      Finsupp.multiset_sum_sum]
    simp only [Multiset.map_nsmul, Multiset.sum_nsmul,
      Multiset.map_singleton, Multiset.sum_singleton]
    simp [singleEnergy, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  let toOdd (d : SingleOddFiber N) : OddPartition N :=
    ⟨{ parts := d.1.toMultiset.map oddWeight
       parts_pos := by
         intro j hj
         obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hj
         dsimp [oddWeight]
         omega
       parts_sum := (hsum d.1).trans d.2 }, by
      simp only [Nat.Partition.odds, Nat.Partition.restricted,
        Finset.mem_filter, Finset.mem_univ, true_and]
      intro j hj
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hj
      apply Nat.not_even_iff.mpr
      dsimp [oddWeight]
      omega⟩
  have hinj : Function.Injective toOdd := by
    intro d e h
    apply Subtype.ext
    have hm := congrArg (fun p : OddPartition N => p.1.parts) h
    change d.1.toMultiset.map oddWeight = e.1.toMultiset.map oddWeight at hm
    have hraw := Multiset.map_injective hinjWeight hm
    simpa using congrArg Multiset.toFinsupp hraw
  have hsurj : Function.Surjective toOdd := by
    intro p
    have hpodd : ∀ j ∈ p.1.parts, ¬ Even j := by
      simpa only [Nat.Partition.odds, Nat.Partition.restricted,
        Finset.mem_filter, Finset.mem_univ, true_and] using p.2
    let d : ℕ →₀ ℕ := (p.1.parts.map (fun j => j / 2)).toFinsupp
    have hparts : d.toMultiset.map oddWeight = p.1.parts := by
      rw [Multiset.toFinsupp_toMultiset, Multiset.map_map]
      exact (Multiset.map_congr rfl (by
        intro j hj
        have hmod := Nat.not_even_iff.mp (hpodd j hj)
        dsimp [oddWeight]
        omega)).trans p.1.parts.map_id'
    have henergy : singleEnergy d = N := by
      rw [← hsum d, hparts, p.1.parts_sum]
    exact ⟨⟨d, henergy⟩, Subtype.ext (Nat.Partition.ext hparts)⟩
  exact Equiv.ofBijective toOdd ⟨hinj, hsurj⟩

section Colours

variable (ι : Type*) [Fintype ι]

/-- Generic form of the original exponent energy for an arbitrary finite colour type. -/
def colouredEnergy (d : (ι × ℕ) →₀ ℕ) : ℕ :=
  Finsupp.weight (fun x : ι × ℕ => oddWeight x.2) d

abbrev ColouredOddFiber (N : ℕ) :=
  {d : (ι × ℕ) →₀ ℕ // colouredEnergy ι d = N}

/-- Reuse: the library's curry and finite-domain Finsupp/function equivalences. -/
def colourEquiv : ((ι × ℕ) →₀ ℕ) ≃ (ι → ℕ →₀ ℕ) :=
  Finsupp.curryEquiv.trans Finsupp.equivFunOnFinite

/-- Reuse/normalization: existing Finsupp currying splits the weight sum. -/
theorem colouredEnergy_eq_sum (d : (ι × ℕ) →₀ ℕ) :
    colouredEnergy ι d = ∑ i, singleEnergy (colourEquiv ι d i) := by
  classical
  calc
    colouredEnergy ι d =
        d.sum (fun x c => c • oddWeight x.2) := rfl
    _ = d.curry.sum (fun (_ : ι) f => f.sum (fun n c => c • oddWeight n)) :=
      (Finsupp.sum_curry_index d (fun (_ : ι) n c => c • oddWeight n)).symm
    _ = ∑ i, (d.curry i).sum (fun n c => c • oddWeight n) :=
      Finsupp.sum_fintype _ _ (by intro i; simp)
    _ = ∑ i, singleEnergy (colourEquiv ι d i) := rfl

abbrev EnergyAllocation (N : ℕ) := {e : ι → ℕ // ∑ i, e i = N}

/-- The dependent sigma requested by the original coloured-fibre problem. -/
abbrev OddPartitionSigma (N : ℕ) :=
  Σ e : EnergyAllocation ι N, (i : ι) → OddPartition (e.1 i)

/-- Reuse: a fibre of the pointwise energy map is a Pi of individual fibres. -/
def pointwiseEnergyFiberEquiv (e : ι → ℕ) :
    {f : ι → ℕ →₀ ℕ // (fun i => singleEnergy (f i)) = e} ≃
      ((i : ι) → SingleOddFiber (e i)) :=
  (Equiv.subtypeEquivRight
    (p := fun f : ι → ℕ →₀ ℕ => (fun i => singleEnergy (f i)) = e)
    (q := fun f : ι → ℕ →₀ ℕ => ∀ i, singleEnergy (f i) = e i)
    (fun _ => funext_iff)).trans
      (Equiv.subtypePiEquivPi (p := fun i d => singleEnergy d = e i))

/-- Content: the genuine coloured odd-weight fibre is exactly a tuple of odd
partitions with dependent colour energies summing to N. The grouping itself
uses the public sigmaSubtypeFiberEquivSubtype supplier. -/
def colouredOddFiberEquivSigma (N : ℕ) :
    ColouredOddFiber ι N ≃ OddPartitionSigma ι N := by
  let split : ColouredOddFiber ι N ≃
      {f : ι → ℕ →₀ ℕ // ∑ i, singleEnergy (f i) = N} :=
    (colourEquiv ι).subtypeEquiv (fun d => by rw [colouredEnergy_eq_sum])
  let group :
      (Σ e : EnergyAllocation ι N,
        {f : ι → ℕ →₀ ℕ // (fun i => singleEnergy (f i)) = e.1}) ≃
      {f : ι → ℕ →₀ ℕ // ∑ i, singleEnergy (f i) = N} :=
    Equiv.sigmaSubtypeFiberEquivSubtype
      (fun f : ι → ℕ →₀ ℕ => fun i => singleEnergy (f i)) (fun _ => Iff.rfl)
  exact split.trans (group.symm.trans (Equiv.sigmaCongrRight (fun e =>
    (pointwiseEnergyFiberEquiv ι e.1).trans
      (Equiv.piCongrRight (fun i => singleOddFiberEquivPartition (e.1 i))))))

variable [DecidableEq ι]

/-- Reuse/normalization: the same energy allocations are precisely the public
finite antidiagonal used by PowerSeries.coeff_prod. -/
def energyAllocationEquivAntidiag (N : ℕ) :
    EnergyAllocation ι N ≃ ↥((Finset.univ : Finset ι).finsuppAntidiag N) := by
  classical
  exact
    { toFun := fun e => ⟨Finsupp.equivFunOnFinite.symm e.1,
        Finset.mem_finsuppAntidiag.mpr ⟨e.2, Finset.subset_univ _⟩⟩
      invFun := fun l => ⟨fun i => l.1 i, (Finset.mem_finsuppAntidiag.mp l.2).1⟩
      left_inv := fun e => Subtype.ext rfl
      right_inv := fun l => Subtype.ext (by ext i; rfl) }

/-- Content consumer: match the actual fibre to the exact finite convolution index. -/
def colouredOddFiberEquivAntidiag (N : ℕ) :
    ColouredOddFiber ι N ≃
      Σ e : ↥((Finset.univ : Finset ι).finsuppAntidiag N),
        (i : ι) → OddPartition (e.1 i) := by
  classical
  exact (colouredOddFiberEquivSigma ι N).trans
    (Equiv.sigmaCongr (energyAllocationEquivAntidiag ι N) (fun _ => Equiv.refl _))


/-- All-degree exact counting/convolution bridge; no occupation cutoff. -/
theorem card_colouredOddFiber (N : ℕ) :
    Nat.card (ColouredOddFiber ι N) =
      ∑ e ∈ (Finset.univ : Finset ι).finsuppAntidiag N,
        ∏ i : ι, (Nat.Partition.odds (e i)).card := by
  classical
  rw [Nat.card_congr (colouredOddFiberEquivAntidiag ι N),
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_pi, Fintype.card_coe]
  exact Finset.sum_coe_sort ((Finset.univ : Finset ι).finsuppAntidiag N)
    (fun e : ι →₀ ℕ => ∏ i : ι, (Nat.Partition.odds (e i)).card)

end Colours

section Series

variable (R : Type*) [CommSemiring R]

/-- The library's single-colour restricted-partition coefficient series. -/
def oddPartitionSeries : PowerSeries R :=
  PowerSeries.mk (fun N => ((Nat.Partition.odds N).card : R))

/-- Counting series of the actual generic coloured occupation fibre. -/
def colouredFiberSeries (ι : Type*) [Fintype ι] : PowerSeries R :=
  PowerSeries.mk (fun N => (Nat.card (ColouredOddFiber ι N) : R))

/-- Content consumer: exact finite coefficient convolution identifies the series. -/
theorem colouredFiberSeries_eq_prod (ι : Type*) [Fintype ι] :
    colouredFiberSeries R ι = ∏ _ : ι, oddPartitionSeries R := by
  classical
  apply PowerSeries.ext
  intro N
  rw [colouredFiberSeries, PowerSeries.coeff_mk, card_colouredOddFiber,
    PowerSeries.coeff_prod]
  simp only [Nat.cast_sum, Nat.cast_prod, oddPartitionSeries, PowerSeries.coeff_mk]

/-- Reuse: identical colour factors turn the finite product into a power. -/
theorem colouredFiberSeries_eq_pow (ι : Type*) [Fintype ι] :
    colouredFiberSeries R ι = oddPartitionSeries R ^ Fintype.card ι := by
  rw [colouredFiberSeries_eq_prod]
  simp




end Series

section Product

variable (K : Type*) [Field K] [TopologicalSpace K] [T2Space K] [IsTopologicalRing K]

/-- Formal geometric inverse. PowerSeries has its coefficient-field inverse,
not a field structure on all power series; the constant term is checked. -/
theorem odd_geometric_eq_inverse (n : ℕ) :
    (∑' j : ℕ, (PowerSeries.X : PowerSeries K) ^ (oddWeight n * j)) =
      ((1 : PowerSeries K) - PowerSeries.X ^ oddWeight n)⁻¹ := by
  have hzero : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries K) ^ oddWeight n) = 0 := by
    simp [oddWeight]
  simp_rw [pow_mul]
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp [hzero])).2
  exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hzero

/-- Reuse: Glaisher's public restricted-partition HasProd, restricted to the
odd positive parts and reindexed by n ↦ 2*n. No analytic convergence is used. -/
theorem hasProd_oddPartitionSeries :
    HasProd (fun n : ℕ =>
      ((1 : PowerSeries K) - PowerSeries.X ^ oddWeight n)⁻¹)
      (oddPartitionSeries K) := by
  classical
  let F : ℕ → PowerSeries K := fun i =>
    if ¬ Even (i + 1) then ∑' j : ℕ, PowerSeries.X ^ ((i + 1) * j) else 1
  have hF : HasProd F (oddPartitionSeries K) := by
    simpa only [F, oddPartitionSeries, Nat.Partition.odds] using
      Nat.Partition.hasProd_powerSeriesMk_card_restricted K (fun j => ¬ Even j)
  have hinj : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b h
    change 2 * a = 2 * b at h
    omega
  have houtside : ∀ i : ℕ, i ∉ Set.range (fun n : ℕ => 2 * n) → F i = 1 := by
    intro i hi
    have hnot : ¬ Even i := by
      rintro ⟨j, hj⟩
      exact hi ⟨j, by dsimp; omega⟩
    have hmod := Nat.not_even_iff.mp hnot
    have heven : Even (i + 1) := Nat.even_iff.mpr (by omega)
    simp [F, heven]
  have hsub : HasProd (F ∘ (fun n : ℕ => 2 * n)) (oddPartitionSeries K) :=
    (hinj.hasProd_iff houtside).2 hF
  apply hsub.congr_fun
  intro n
  have hodd : ¬ Even (2 * n + 1) := Nat.not_even_iff.mpr (by omega)
  simpa only [Function.comp_apply, F, if_pos hodd, oddWeight] using
    (odd_geometric_eq_inverse K n).symm

/-- Full formal Euler HasProd for arbitrary finite colours, including rank zero. -/
theorem hasProd_colouredFiberSeries (ι : Type*) [Fintype ι] :
    HasProd (fun n : ℕ =>
      (((1 : PowerSeries K) - PowerSeries.X ^ (2 * n + 1))⁻¹) ^ Fintype.card ι)
      (colouredFiberSeries K ι) := by
  rw [colouredFiberSeries_eq_pow]
  simpa only [oddWeight] using (hasProd_oddPartitionSeries K).pow (Fintype.card ι)



end Product

end
end D5.S3.Combinatorics.Partitions.ColouredOddOccupation
