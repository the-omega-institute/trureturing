/- GID: D5/S3/Combinatorics/Partitions/AnalyticOddOccupation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/AnalyticOddOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Group.Tannery, mathlib/module/Mathlib.Analysis.Normed.Ring.InfiniteSum]
   utility: none
   digest: Absolute convergence and ordinary complex Euler products for unbounded coloured odd occupations. -/

import D5.S3.Combinatorics.Partitions.ColouredOddOccupation
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators
open Filter Topology

namespace D5.S3.Combinatorics.Partitions.AnalyticOddOccupation

open D5.S3.Combinatorics.Partitions.ColouredOddOccupation

/- The graph comparison reuses the finite-subset summability supplier.
A graph contains one pair (a,d a) for each nonzero occupation.
All finite subsets of pairs form a larger, already summable family. -/
private theorem summable_finsuppProd_of_graph_test {α : Type*}
    (f : α → ℕ → ℝ) (hf : ∀ a k, 0 ≤ f a k)
    (hs : Summable (fun p : α × ℕ => if p.2 = 0 then 0 else f p.1 p.2)) :
    Summable (fun d : α →₀ ℕ => d.prod f) := by
  classical
  let g : α × ℕ → ℝ := fun p => if p.2 = 0 then 0 else f p.1 p.2
  have hg : ∀ p, 0 ≤ g p := by
    intro p
    dsimp [g]
    split_ifs
    · exact le_rfl
    · exact hf _ _
  have hsets : Summable (fun s : Finset (α × ℕ) => ∏ p ∈ s, g p) :=
    summable_finsetProd_of_summable_nonneg hg hs
  have hgraphs := hsets.comp_injective (Finsupp.graph_injective α ℕ)
  apply hgraphs.congr
  intro d
  change (∏ p ∈ d.graph, g p) = d.prod f
  rw [Finsupp.graph, Finset.prod_map]
  change (∏ a ∈ d.support, g (a, d a)) = ∏ a ∈ d.support, f a (d a)
  apply Finset.prod_congr rfl
  intro a ha
  exact if_neg (Finsupp.mem_support_iff.mp ha)

/-- Absolute occupation majorant for all finite colour types, including empty.
The comparison uses (2*n+1)*k ≥ n+k for k≥1, so the pair family is bounded
by the product of two ordinary geometric sequences. No r>0 is used. -/
theorem summable_real_odd_occupations (ι : Type*) [Fintype ι]
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun d : (ι × ℕ) →₀ ℕ => r ^ colouredEnergy ι d) := by
  classical
  have hgeom : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_lt_one hr0 hr1
  have hcol : Summable (fun a : ι × ℕ => r ^ a.2) :=
    (summable_prod_of_nonneg (fun a : ι × ℕ => pow_nonneg hr0 a.2)).2
      ⟨fun _ => hgeom, Summable.of_finite⟩
  have hbound : Summable (fun p : (ι × ℕ) × ℕ => r ^ p.1.2 * r ^ p.2) :=
    hcol.mul_of_nonneg hgeom (fun _ => pow_nonneg hr0 _) (fun _ => pow_nonneg hr0 _)
  have hpairs : Summable (fun p : (ι × ℕ) × ℕ =>
      if p.2 = 0 then 0 else r ^ (oddWeight p.1.2 * p.2)) := by
    refine hbound.of_nonneg_of_le ?_ ?_
    · intro p
      split_ifs
      · exact le_rfl
      · exact pow_nonneg hr0 _
    · intro p
      by_cases hk : p.2 = 0
      · rw [if_pos hk]
        exact mul_nonneg (pow_nonneg hr0 _) (pow_nonneg hr0 _)
      · rw [if_neg hk, ← pow_add]
        apply pow_le_pow_of_le_one hr0 hr1.le
        have hk1 : 1 ≤ p.2 := by omega
        have hm := Nat.mul_le_mul_left p.1.2 hk1
        dsimp [oddWeight]
        nlinarith
  have hocc := summable_finsuppProd_of_graph_test
    (fun a : ι × ℕ => fun k => r ^ (oddWeight a.2 * k))
    (fun _ _ => pow_nonneg hr0 _) hpairs
  apply hocc.congr
  intro d
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum]
  congr 1
  simp only [colouredEnergy, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => Nat.mul_comm _ _)

def monomial {α : Type*} (z : α → ℂ) (d : α →₀ ℕ) : ℂ :=
  d.prod (fun a k => z a ^ k)

private theorem monomial_odd_eq (ι : Type*) (q : ℂ) (d : (ι × ℕ) →₀ ℕ) :
    monomial (fun a : ι × ℕ => q ^ oddWeight a.2) d = q ^ colouredEnergy ι d := by
  classical
  unfold monomial Finsupp.prod
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simp only [colouredEnergy, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => Nat.mul_comm _ _)

private theorem summable_norm_odd_occupations (ι : Type*) [Fintype ι]
    {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun d : (ι × ℕ) →₀ ℕ => ‖q ^ colouredEnergy ι d‖) := by
  simpa only [Complex.norm_pow] using
    summable_real_odd_occupations ι (norm_nonneg q) hq

/- Finite product evaluation via exact finite boxes. The finite algebraic
step is Finset.prod_univ_sum, also used in the immutable repository's
FiniteOccupationPartitionFunctions.bosonic_trunc_eq_product_geometric_sums.
This lemma adds the actual absolute-convergence/limit passage. -/
private theorem hasSum_finite_prod_of_summable_norm {β : Type*} [Fintype β]
    (f : β → ℕ → ℂ) (b : β → ℂ)
    (hnorm : Summable (fun d : β → ℕ => ‖∏ i, f i (d i)‖))
    (hf : ∀ i, HasSum (f i) (b i)) :
    HasSum (fun d : β → ℕ => ∏ i, f i (d i)) (∏ i, b i) := by
  classical
  let box : ℕ → Finset (β → ℕ) :=
    fun N => Fintype.piFinset (fun _ : β => Finset.range N)
  have hmono : Monotone box := by
    intro m n hmn
    exact Fintype.piFinset_subset _ _ (fun _ => Finset.range_mono hmn)
  have hexhaust : ∀ d : β → ℕ, ∃ N, d ∈ box N := by
    intro d
    refine ⟨Finset.univ.sup d + 1, Fintype.mem_piFinset.mpr ?_⟩
    intro i
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
  have hbox : Tendsto box atTop atTop := hmono.tendsto_atTop_finset hexhaust
  apply hasSum_of_subseq_of_summable hnorm hbox
  have ht := tendsto_finsetProd (Finset.univ : Finset β)
    (fun i _ => (hf i).tendsto_sum_nat)
  simpa only [box, Finset.prod_univ_sum] using ht

/-- Ordinary complex evaluation of the sum over all occupations supported in
a fixed finite set. This is the only finite-mode evaluation needed below. -/
private theorem hasSum_supported_monomials {α : Type*} (z : α → ℂ)
    (hnorm : Summable (fun d : α →₀ ℕ => ‖monomial z d‖))
    (hz : ∀ a, ‖z a‖ < 1) (s : Finset α) :
    HasSum
      (fun d : {d : α →₀ ℕ // ↑d.support ⊆ (s : Set α)} => monomial z d.1)
      (∏ a ∈ s, (1 - z a)⁻¹) := by
  classical
  let A := {d : α →₀ ℕ // ↑d.support ⊆ (s : Set α)}
  let e : A ≃ (s → ℕ) :=
    (Finsupp.restrictSupportEquiv (s : Set α) ℕ).trans Finsupp.equivFunOnFinite
  have hprod (d : A) : monomial z d.1 = ∏ a : s, z a ^ (e d a) := by
    change d.1.prod (fun a k => z a ^ k) = _
    rw [← Finsupp.prod_subtypeDomain_index
      (p := fun a => a ∈ (s : Set α)) (v := d.1)
      (h := fun a k => z a ^ k) (fun a ha => d.2 ha)]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  have hsub : Summable (fun d : A => ‖monomial z d.1‖) :=
    hnorm.subtype (fun d => ↑d.support ⊆ (s : Set α))
  have hpif : Summable (fun d : s → ℕ => ‖∏ a : s, z a ^ d a‖) := by
    have he : Summable (fun d : s → ℕ => ‖monomial z (e.symm d).1‖) :=
      hsub.comp_injective e.symm.injective
    apply he.congr
    intro d
    simpa only [e.apply_symm_apply] using congrArg norm (hprod (e.symm d))
  have hpi := hasSum_finite_prod_of_summable_norm
    (fun a : s => fun k => z a ^ k) (fun a : s => (1 - z a)⁻¹) hpif
    (fun a => hasSum_geometric_of_norm_lt_one (hz a))
  have hA : HasSum (fun d : A => ∏ a : s, z a ^ (e d a))
      (∏ a : s, (1 - z a)⁻¹) :=
    (e.hasSum_iff (f := fun d : s → ℕ => ∏ a : s, z a ^ d a)).mpr hpi
  have hout := hA.congr_fun hprod
  rw [← Finset.prod_coe_sort s (fun a => (1 - z a)⁻¹)]
  exact hout

/-- A genuine analytic Euler expansion. The hypothesis is absolute summability
of actual occupation monomials; no formal-series topology is involved. -/
theorem hasProd_inverse_eq_occupation_sum {α : Type*} (z : α → ℂ)
    (hnorm : Summable (fun d : α →₀ ℕ => ‖monomial z d‖))
    (hz : ∀ a, ‖z a‖ < 1) :
    HasProd (fun a => (1 - z a)⁻¹) (∑' d : α →₀ ℕ, monomial z d) := by
  classical
  let cut : Finset α → (α →₀ ℕ) → ℂ := fun s d =>
    if ↑d.support ⊆ (s : Set α) then monomial z d else 0
  have hfinite (s : Finset α) :
      (∑' d : α →₀ ℕ, cut s d) = ∏ a ∈ s, (1 - z a)⁻¹ := by
    have hS := hasSum_supported_monomials z hnorm hz s
    have hind := (hasSum_subtype_iff_indicator
      (f := monomial z)
      (s := {d : α →₀ ℕ | ↑d.support ⊆ (s : Set α)})).mp (by simpa only [Function.comp_def, Set.coe_ofPred] using hS)
    simpa only [cut, Set.indicator, Set.mem_ofPred_eq] using hind.tsum_eq
  have hpoint (d : α →₀ ℕ) :
      Tendsto (fun s : Finset α => cut s d) atTop (𝓝 (monomial z d)) := by
    have heq : (fun _ : Finset α => monomial z d) =ᶠ[atTop]
        (fun s : Finset α => cut s d) := by
      filter_upwards [eventually_ge_atTop d.support] with s hs
      dsimp [cut]
      rw [if_pos (show ↑d.support ⊆ (s : Set α) from hs)]
    exact tendsto_const_nhds.congr' heq
  have hdom : ∀ᶠ s : Finset α in atTop,
      ∀ d : α →₀ ℕ, ‖cut s d‖ ≤ ‖monomial z d‖ := by
    apply Filter.Eventually.of_forall
    intro s d
    dsimp [cut]
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (monomial z d)
  have ht := tendsto_tsum_of_dominated_convergence hnorm hpoint hdom
  change Tendsto (fun s : Finset α => ∏ a ∈ s, (1 - z a)⁻¹)
    atTop (𝓝 (∑' d : α →₀ ℕ, monomial z d))
  exact ht.congr hfinite

/- Finite energy-fibre sums: all finiteness is explicit. In the application,
the canonical dependent antidiagonal equivalence supplies this finiteness;
Nat.card's default value on infinite types is never used. -/
private theorem finite_fiber_power_sum {α R : Type*} [Semiring R]
    [TopologicalSpace R] [T2Space R]
    (e : α → ℕ) (hfinite : ∀ N, Finite {a : α // e a = N}) (z : R) (N : ℕ) :
    (∑' a : e ⁻¹' {N}, z ^ e a.1) =
      (Nat.card {a : α // e a = N} : R) * z ^ N := by
  classical
  letI : Finite {a : α // e a = N} := hfinite N
  letI : Fintype {a : α // e a = N} := Fintype.ofFinite _
  change (∑' a : {a : α // e a = N}, z ^ e a.1) = _
  calc
    _ = ∑' _a : {a : α // e a = N}, z ^ N :=
      tsum_congr (fun a => congrArg (fun n => z ^ n) a.2)
    _ = _ := by
      simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem summable_norm_odd_coefficients (ι : Type*) [Fintype ι]
    {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun N : ℕ => ‖(Nat.card (ColouredOddFiber ι N) : ℂ) * q ^ N‖) := by
  classical
  have hocc := summable_real_odd_occupations ι (norm_nonneg q) hq
  have hgroup := hocc.hasSum.tsum_fiberwise (colouredEnergy ι)
  have hcoeff : Summable (fun N : ℕ =>
      (Nat.card (ColouredOddFiber ι N) : ℝ) * ‖q‖ ^ N) := by
    apply HasSum.summable (hgroup.congr_fun ?_)
    intro N
    exact (finite_fiber_power_sum (colouredEnergy ι)
      (fun N => Finite.of_injective (colouredOddFiberEquivAntidiag ι N)
        (colouredOddFiberEquivAntidiag ι N).injective) ‖q‖ N).symm
  simpa only [norm_mul, Complex.norm_natCast, Complex.norm_pow] using hcoeff

private theorem hasSum_odd_coefficients (ι : Type*) [Fintype ι]
    {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun N : ℕ => (Nat.card (ColouredOddFiber ι N) : ℂ) * q ^ N)
      (∑' d : (ι × ℕ) →₀ ℕ, q ^ colouredEnergy ι d) := by
  classical
  have hocc := (summable_norm_odd_occupations ι hq).of_norm
  have hgroup := hocc.hasSum.tsum_fiberwise (colouredEnergy ι)
  apply hgroup.congr_fun
  intro N
  exact (finite_fiber_power_sum (colouredEnergy ι)
    (fun N => Finite.of_injective (colouredOddFiberEquivAntidiag ι N)
        (colouredOddFiberEquivAntidiag ι N).injective) q N).symm

/-- Full analytic Euler HasProd in the original odd weights. All complex q
with norm<1, all finite colours, and the empty colour type are included. -/
theorem hasProd_odd_character (ι : Type*) [Fintype ι]
    {q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => ((1 - q ^ (2 * n + 1))⁻¹) ^ Fintype.card ι)
      (∑' N : ℕ, (Nat.card (ColouredOddFiber ι N) : ℂ) * q ^ N) := by
  classical
  let z : ι × ℕ → ℂ := fun a => q ^ oddWeight a.2
  have hm : Summable (fun d : (ι × ℕ) →₀ ℕ => ‖monomial z d‖) := by
    apply (summable_norm_odd_occupations ι hq).congr
    intro d
    exact (congrArg norm (monomial_odd_eq ι q d)).symm
  have hz (a : ι × ℕ) : ‖z a‖ < 1 := by
    dsimp [z]
    rw [Complex.norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by dsimp [oddWeight]; omega)
  have hp := hasProd_inverse_eq_occupation_sum z hm hz
  have hswap : HasProd (fun p : ℕ × ι => (1 - q ^ oddWeight p.1)⁻¹)
      (∑' d : (ι × ℕ) →₀ ℕ, monomial z d) :=
    (Equiv.prodComm ℕ ι).hasProd_iff.mpr hp
  have hgroup : HasProd
      (fun n : ℕ => ((1 - q ^ oddWeight n)⁻¹) ^ Fintype.card ι)
      (∑' d : (ι × ℕ) →₀ ℕ, monomial z d) := by
    apply hswap.prod_fiberwise
    intro n
    simpa only [Finset.prod_const, Finset.card_univ] using
      hasProd_fintype (fun _ : ι => (1 - q ^ oddWeight n)⁻¹)
  have hocc_eq : (∑' d : (ι × ℕ) →₀ ℕ, monomial z d) =
      ∑' d : (ι × ℕ) →₀ ℕ, q ^ colouredEnergy ι d :=
    tsum_congr (monomial_odd_eq ι q)
  rw [hocc_eq, ← (hasSum_odd_coefficients ι hq).tsum_eq] at hgroup
  simpa only [oddWeight] using hgroup


end D5.S3.Combinatorics.Partitions.AnalyticOddOccupation
