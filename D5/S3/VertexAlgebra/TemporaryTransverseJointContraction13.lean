import D5.S3.VertexAlgebra.TemporaryTransverseJointAuxiliary12
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

def kappa (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (powers : Index D →₀ ℕ) (subset : Finset ℕ) : ℕ :=
  axisExponentCount D xAxis powers + axisExponentCount D yAxis powers +
    etaCount subset + thetaCount subset

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

theorem axis_frequency_count (D : LatticeData) (axis : Fin D.rank)
    (powers : Index D →₀ ℕ) :
    (∑ᶠ frequency : ℕ, powers (axis, frequency)) = axisExponentCount D axis powers := by
  classical
  have injective : Function.Injective (fun frequency : ℕ => (axis, frequency)) :=
    fun first second equality => (Prod.mk.inj equality).2
  rw [← finsum_mem_range injective]
  rw [finsum_mem_eq_sum_of_subset (fun index : Index D => powers index)
    (s := Set.range (fun frequency : ℕ => (axis, frequency)))
    (t := powers.support.filter (fun index => index.1 = axis))]
  · simp only [axisExponentCount, Finsupp.sum, Finset.sum_filter]
  · rintro index ⟨⟨frequency, rfl⟩, nonzero⟩
    exact Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr nonzero, rfl⟩
  · intro index member
    refine ⟨index.2, ?_⟩
    exact Prod.ext (Finset.mem_filter.mp member).2.symm rfl

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

theorem occupation_frequency_sum (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (powers : Index D →₀ ℕ) (subset : Finset ℕ) :
    (∑ᶠ frequency : ℕ,
      (powers (xAxis, frequency) + powers (yAxis, frequency) +
        (if thetaSite frequency ∈ subset then 1 else 0) +
        (if etaSite frequency ∈ subset then 1 else 0) : ℕ)) =
      kappa D xAxis yAxis powers subset := by
  have xFinite := axis_frequency_finite D xAxis powers
  have yFinite := axis_frequency_finite D yAxis powers
  have thetaFinite := (site_indicator_finite subset).comp_of_injective thetaSite_injective
  have etaFinite := (site_indicator_finite subset).comp_of_injective etaSite_injective
  have sumEta := finsum_add_distrib ((xFinite.add yFinite).add thetaFinite) etaFinite
  have sumTheta := finsum_add_distrib (xFinite.add yFinite) thetaFinite
  have sumAxes := finsum_add_distrib xFinite yFinite
  simp only [Pi.add_apply, Function.comp_apply] at sumEta sumTheta sumAxes
  rw [sumEta, sumTheta, sumAxes, axis_frequency_count, axis_frequency_count,
    theta_frequency_count, eta_frequency_count]
  simp only [kappa]
  omega

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


theorem original_K_all_frequency_count (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (charge : Charge D) (powers : Index D →₀ ℕ) (scalar : ℂ) (subset : Finset ℕ) :
    K D (frame xAxis) (frame yAxis) (by simpa using xDual xAxis)
      (Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar))
        ⊗ₜ[ℂ] downWord subset down) =
      (kappa D xAxis yAxis powers subset : ℂ) •
      (Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar))
        ⊗ₜ[ℂ] downWord subset down) := by
  let state := Finsupp.single charge (coordinateSub D frame (MvPolynomial.monomial powers scalar))
    ⊗ₜ[ℂ] downWord subset down
  have dual : gramPair D (frame yAxis) (frame xAxis) = 1 := by simpa using xDual xAxis
  have opposite : gramPair D (frame xAxis) (frame yAxis) = 1 := by simpa using yDual yAxis
  have finite : Function.HasFiniteSupport
      (fun mode : ℤ => normalKAtom D (frame xAxis) (frame yAxis) mode state) := by
    simpa only [rawKAtom_eq_normal D (frame xAxis) (frame yAxis) opposite] using
      rawKAtom_finite D (frame xAxis) (frame yAxis) dual state
  have zeroAtom : normalKAtom D (frame xAxis) (frame yAxis) 0 state = 0 := by
    simp [normalKAtom]
  have decomposed := signed_frequency_finsum D
    (fun mode : ℤ => normalKAtom D (frame xAxis) (frame yAxis) mode state) finite zeroAtom
  have countFinite := occupation_frequency_finite D xAxis yAxis powers subset
  have castFinite := countFinite.fun_comp (g := fun count : ℕ => (count : ℂ)) (by simp)
  have castSum := (Nat.castAddMonoidHom ℂ).map_finsum countFinite
  simp only [Nat.castAddMonoidHom, occupation_frequency_sum] at castSum
  change K D (frame xAxis) (frame yAxis) dual state = _
  calc
    _ = ∑ᶠ mode : ℤ, normalKAtom D (frame xAxis) (frame yAxis) mode state :=
      K_normal_ordered D (frame xAxis) (frame yAxis) dual state
    _ = ∑ᶠ frequency : ℕ,
        (normalKAtom D (frame xAxis) (frame yAxis) ((frequency : ℤ) + 1) state +
          normalKAtom D (frame xAxis) (frame yAxis) (-((frequency : ℤ) + 1)) state) := decomposed
    _ = ∑ᶠ frequency : ℕ,
        ((powers (xAxis, frequency) + powers (yAxis, frequency) +
          (if thetaSite frequency ∈ subset then 1 else 0) +
          (if etaSite frequency ∈ subset then 1 else 0) : ℕ) : ℂ) • state := by
      apply finsum_congr
      intro frequency
      exact original_K_block_count D frame xAxis yAxis xDual yDual charge powers scalar subset frequency
    _ = _ := by
      rw [← finsum_smul' castFinite]
      exact congrArg (fun count : ℂ => count • state) castSum.symm

theorem axisExponentCount_zero_iff (D : LatticeData) (axis : Fin D.rank)
    (powers : Index D →₀ ℕ) :
    axisExponentCount D axis powers = 0 ↔ ∀ frequency : ℕ, powers (axis, frequency) = 0 := by
  classical
  simp only [axisExponentCount, Finsupp.sum, Finset.sum_eq_zero_iff]
  constructor
  · intro allZero frequency
    by_cases present : (axis, frequency) ∈ powers.support
    · simpa using allZero (axis, frequency) present
    · exact Finsupp.notMem_support_iff.mp present
  · intro allZero index member
    by_cases onAxis : index.1 = axis
    · rcases index with ⟨row, frequency⟩
      dsimp only at onAxis
      subst row
      simpa using allZero frequency
    · simp [onAxis]

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


theorem kappa_zero_iff (D : LatticeData) (xAxis yAxis : Fin D.rank)
    (powers : Index D →₀ ℕ) (subset : Finset ℕ) :
    kappa D xAxis yAxis powers subset = 0 ↔
      (∀ frequency : ℕ, powers (xAxis, frequency) = 0) ∧
      (∀ frequency : ℕ, powers (yAxis, frequency) = 0) ∧ subset ⊆ {3} := by
  rw [kappa, Nat.add_eq_zero_iff, Nat.add_eq_zero_iff, Nat.add_eq_zero_iff,
    axisExponentCount_zero_iff, axisExponentCount_zero_iff]
  exact ⟨fun ⟨⟨⟨xZero, yZero⟩, etaZero⟩, thetaZero⟩ =>
    ⟨xZero, yZero, (ghost_occupation_zero_iff subset).mp ⟨etaZero, thetaZero⟩⟩,
    fun ⟨xZero, yZero, onlyEpsilon⟩ =>
    let ghostZero := (ghost_occupation_zero_iff subset).mpr onlyEpsilon
    ⟨⟨⟨xZero, yZero⟩, ghostZero.1⟩, ghostZero.2⟩⟩

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
