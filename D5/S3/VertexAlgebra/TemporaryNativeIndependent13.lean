import D5.S3.VertexAlgebra.TemporaryOriginalQuartet06
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic


set_option autoImplicit false

open scoped Classical

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

theorem etaSite_injective : Function.Injective etaSite := by
  intro first second equality
  unfold etaSite at equality
  split_ifs at equality <;> omega

theorem thetaSite_injective : Function.Injective thetaSite := by
  intro first second equality
  unfold thetaSite at equality
  omega

theorem etaSite_range (site : ℕ) :
    site ∈ Set.range etaSite ↔ site = 1 ∨ site % 2 = 0 := by
  constructor
  · rintro ⟨frequency, rfl⟩
    unfold etaSite
    split_ifs <;> omega
  · rintro (one | even)
    · exact ⟨0, by simp [etaSite, one]⟩
    · refine ⟨site / 2 + 1, ?_⟩
      simp only [etaSite, if_neg (by omega : site / 2 + 1 ≠ 0)]
      omega

theorem thetaSite_range (site : ℕ) :
    site ∈ Set.range thetaSite ↔ site % 2 = 1 ∧ site ≠ 1 ∧ site ≠ 3 := by
  constructor
  · rintro ⟨frequency, rfl⟩
    unfold thetaSite
    omega
  · rintro ⟨odd, notOne, notThree⟩
    refine ⟨(site - 5) / 2, ?_⟩
    unfold thetaSite
    omega

theorem site_indicator_finite (subset : Finset ℕ) :
    Function.HasFiniteSupport (fun site : ℕ => (if site ∈ subset then 1 else 0 : ℕ)) := by
  classical
  apply subset.finite_toSet.subset
  intro site nonzero
  change site ∈ subset
  by_contra absent
  exact nonzero (by simp [absent])

theorem site_frequency_count (siteMap : ℕ → ℕ) (injective : Function.Injective siteMap)
    (subset : Finset ℕ) :
    (∑ᶠ frequency : ℕ, if siteMap frequency ∈ subset then 1 else 0 : ℕ) =
      (subset.filter (fun site => site ∈ Set.range siteMap)).card := by
  classical
  rw [← finsum_mem_range (f := fun site : ℕ => if site ∈ subset then 1 else 0) injective]
  rw [finsum_mem_eq_sum_of_subset
    (fun site : ℕ => if site ∈ subset then 1 else 0)
    (s := Set.range siteMap) (t := subset.filter (fun site => site ∈ Set.range siteMap))]
  · calc
      _ = ∑ site ∈ subset.filter (fun site => site ∈ Set.range siteMap), (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro site member
        simp [(Finset.mem_filter.mp member).1]
      _ = _ := by simp
  · intro site member
    have present : site ∈ subset := by
      by_contra absent
      exact member.2 (by simp [absent])
    exact Finset.mem_filter.mpr ⟨present, member.1⟩
  · intro site member
    exact (Finset.mem_filter.mp member).2

theorem axis_frequency_finite (D : LatticeData) (axis : Fin D.rank)
    (powers : Index D →₀ ℕ) :
    Function.HasFiniteSupport (fun frequency : ℕ => powers (axis, frequency)) := by
  have finite : Function.HasFiniteSupport (fun index : Index D => powers index) :=
    powers.hasFiniteSupport
  exact finite.comp_of_injective (fun first second equality => (Prod.mk.inj equality).2)

theorem eta_frequency_count (subset : Finset ℕ) :
    (∑ᶠ frequency : ℕ, if etaSite frequency ∈ subset then 1 else 0 : ℕ) = etaCount subset := by
  rw [site_frequency_count etaSite etaSite_injective]
  simp only [etaCount, etaSite_range]

theorem theta_frequency_count (subset : Finset ℕ) :
    (∑ᶠ frequency : ℕ, if thetaSite frequency ∈ subset then 1 else 0 : ℕ) = thetaCount subset := by
  rw [site_frequency_count thetaSite thetaSite_injective]
  simp only [thetaCount, thetaSite_range]

theorem occupation_frequency_finite (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (powers : Index D →₀ ℕ) (subset : Finset ℕ) :
    Function.HasFiniteSupport (fun frequency : ℕ =>
      powers (xAxis, frequency) + powers (yAxis, frequency) +
        (if thetaSite frequency ∈ subset then 1 else 0) +
        (if etaSite frequency ∈ subset then 1 else 0)) := by
  exact (((axis_frequency_finite D xAxis powers).add (axis_frequency_finite D yAxis powers)).add
    ((site_indicator_finite subset).comp_of_injective thetaSite_injective)).add
    ((site_indicator_finite subset).comp_of_injective etaSite_injective)

theorem signed_frequency_finsum (D : LatticeData) (family : ℤ → State D)
    (finite : Function.HasFiniteSupport family) (atZero : family 0 = 0) :
    (∑ᶠ mode : ℤ, family mode) =
      ∑ᶠ frequency : ℕ, (family ((frequency : ℤ) + 1) + family (-((frequency : ℤ) + 1))) := by
  classical
  let positive : ℕ → ℤ := fun frequency => (frequency : ℤ) + 1
  let negative : ℕ → ℤ := fun frequency => -((frequency : ℤ) + 1)
  have positiveInjective : Function.Injective positive := by
    intro first second equality
    dsimp [positive] at equality
    omega
  have negativeInjective : Function.Injective negative := by
    intro first second equality
    dsimp [negative] at equality
    omega
  have disjoint : Disjoint (Set.range positive) (Set.range negative) := by
    apply Set.disjoint_left.mpr
    rintro mode ⟨first, rfl⟩ ⟨second, equality⟩
    dsimp [positive, negative] at equality
    omega
  have cover : (Set.range positive ∪ Set.range negative) ∩ Function.support family =
      Set.univ ∩ Function.support family := by
    ext mode
    constructor
    · exact fun member => ⟨Set.mem_univ mode, member.2⟩
    · intro member
      have nonzero : mode ≠ 0 := by
        intro equality
        subst mode
        exact member.2 atZero
      refine ⟨?_, member.2⟩
      by_cases above : 0 < mode
      · left
        exact ⟨(mode - 1).toNat, by dsimp [positive]; omega⟩
      · right
        exact ⟨(-mode - 1).toNat, by dsimp [negative]; omega⟩
  calc
    _ = ∑ᶠ mode ∈ Set.range positive ∪ Set.range negative, family mode := by
      rw [← finsum_mem_univ family]
      exact (finsum_mem_inter_support_eq family _ _ cover).symm
    _ = (∑ᶠ frequency : ℕ, family (positive frequency)) +
        (∑ᶠ frequency : ℕ, family (negative frequency)) := by
      rw [finsum_mem_union' disjoint (finite.subset Set.inter_subset_right)
        (finite.subset Set.inter_subset_right), finsum_mem_range positiveInjective,
        finsum_mem_range negativeInjective]
    _ = _ := (finsum_add_distrib (finite.comp_of_injective positiveInjective)
      (finite.comp_of_injective negativeInjective)).symm


theorem ghost_occupation_zero_iff (subset : Finset ℕ) :
    etaCount subset = 0 ∧ thetaCount subset = 0 ↔ subset ⊆ {3} := by
  classical
  simp only [etaCount, thetaCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · rintro ⟨noEta, noTheta⟩ site member
    have first := noEta member
    have second := noTheta member
    simp only [Finset.mem_singleton]
    omega
  · intro onlyEpsilon
    constructor <;> intro site member <;>
      have equality := Finset.mem_singleton.mp (onlyEpsilon member)
    · subst site
      norm_num
    · subst site
      norm_num


end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
