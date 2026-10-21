/- GID: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyOccurrence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyOccurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Partition.Finpartition]
   utility: none
   digest: Erased occurrence coefficients of the literal power-sum operator. -/
import D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2
import D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow
import D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRealization

/-! Literal derivative coefficients counted by erased positive occurrences. -/

noncomputable section
namespace D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyOccurrence
open scoped BigOperators
open MvPolynomial
open D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyC2
open D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow

/-- The same exponent encoding on arbitrary residual multisets. -/
def residualExponent (s : Multiset ℕ) : Exponent := (s.map Nat.pred).toFinsupp

private theorem residualExponent_cons (r : ℕ) (s : Multiset ℕ) :
    residualExponent (r ::ₘ s) = Finsupp.single (r-1) 1 + residualExponent s := by
  ext i
  simp [residualExponent, Multiset.count_cons, Finsupp.single_apply, add_comm, eq_comm]

private theorem residualExponent_singleton (r : ℕ) :
    residualExponent {r} = Finsupp.single (r-1) 1 := by
  simp only [residualExponent, Multiset.map_singleton, Multiset.toFinsupp_singleton,
    Nat.pred_eq_sub_one]

theorem residualExponent_erase {s : Multiset ℕ} {r : ℕ} (hr : r ∈ s) :
    residualExponent (s.erase r) = residualExponent s - Finsupp.single (r - 1) 1 := by
  have h := congrArg residualExponent (Multiset.cons_erase hr)
  rw [residualExponent_cons] at h
  rw [← h, add_tsub_cancel_left]

theorem residualExponent_add (s t : Multiset ℕ) :
    residualExponent (s + t) = residualExponent s + residualExponent t := by
  simp [residualExponent]

theorem residualExponent_apply {s : Multiset ℕ} (hs : ∀ r ∈ s, 0 < r) (i : ℕ) :
    residualExponent s i = s.count (i+1) := by
  induction s using Multiset.induction_on with
  | empty => simp [residualExponent]
  | @cons r s ih =>
      have hr := hs r (Multiset.mem_cons_self r s)
      have ht : ∀ t ∈ s, 0 < t := fun t ht => hs t (Multiset.mem_cons_of_mem ht)
      have he : r - 1 = i ↔ r = i+1 := by omega
      simp only [residualExponent, Multiset.map_cons, Multiset.toFinsupp_apply,
        Multiset.count_cons, Nat.pred_eq_sub_one]
      change residualExponent s i + (if i = r-1 then 1 else 0) = _
      rw [ih ht]
      by_cases h : i = r-1
      · have hri : i+1 = r := by omega
        have hpred : r-1+1 = r := by omega
        simp only [h, hpred, ite_true]
      · have hri : i+1 ≠ r := by omega
        simp only [h, hri, ite_false]

private theorem residual_derivative {K : Type*} [Field K] [CharZero K]
    {s : Multiset ℕ} (hs : ∀ r ∈ s, 0 < r) (i : ℕ) :
    pderiv i (monomial (residualExponent s) (1 : K)) =
      (s.count (i+1) : K) • monomial (residualExponent (s.erase (i+1))) 1 := by
  rw [pderiv_monomial, residualExponent_apply hs]
  by_cases hc : s.count (i+1) = 0
  · simp [hc]
  · have hm := Multiset.count_pos.mp (Nat.pos_of_ne_zero hc)
    rw [residualExponent_erase hm]
    simp only [Nat.add_sub_cancel, one_mul, smul_monomial, smul_eq_mul, mul_one]

private theorem occurrence_sum {K : Type*} [AddCommMonoid K]
    (s : Multiset ℕ) (f : ℕ → K) (N : ℕ) (hs : ∀ r ∈ s, r < N) :
    (s.map f).sum = ∑ r ∈ Finset.range N, s.count r • f r := by
  rw [Finset.sum_multiset_map_count]
  apply Finset.sum_subset
  · intro r hr
    exact Finset.mem_range.mpr (hs r (Multiset.mem_toFinset.mp hr))
  · intro r _ hr
    simp only [Multiset.mem_toFinset] at hr
    simp [Multiset.count_eq_zero.mpr hr]

/-- A finite derivative sum is a sum over the original erased occurrences.
The target of the linear maps may be any module. -/
theorem derivative_occurrence_sum {K M : Type*} [Field K] [CharZero K]
    [AddCommGroup M] [Module K M] (N : ℕ) (s : Multiset ℕ)
    (hs : ∀ r ∈ s, 0 < r ∧ r ≤ N)
    (F : ℕ → PowerSum K →ₗ[K] M) :
    (∑ i ∈ Finset.range N, F i (pderiv i (monomial (residualExponent s) 1))) =
      (s.map fun r => F (r-1) (monomial (residualExponent (s.erase r)) 1)).sum := by
  classical
  have hp : ∀ r ∈ s, 0 < r := fun r hr => (hs r hr).1
  have hmap : (s.map fun r => F (r-1) (monomial (residualExponent (s.erase r)) 1)) =
      ((s.map Nat.pred).map fun i =>
        F i (monomial (residualExponent (s.erase (i+1))) 1)) := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro r hr
    have he : r-1+1 = r := by have := hp r hr; omega
    simp only [Function.comp_apply, Nat.pred_eq_sub_one, he]
  rw [hmap, occurrence_sum (s.map Nat.pred) _ N (by
    intro i hi
    obtain ⟨r,hr,rfl⟩ := Multiset.mem_map.mp hi
    have := hs r hr
    simp only [Nat.pred_eq_sub_one]
    omega)]
  apply Finset.sum_congr rfl
  intro i _
  rw [residual_derivative hp, map_smul]
  have hc : (s.map Nat.pred).count i = s.count (i+1) := residualExponent_apply hp i
  rw [hc, ← Nat.cast_smul_eq_nsmul K]

theorem double_derivative_occurrence_sum {K M : Type*} [Field K] [CharZero K]
    [AddCommGroup M] [Module K M] (N : ℕ) (s : Multiset ℕ)
    (hs : ∀ r ∈ s, 0 < r ∧ r ≤ N)
    (F : ℕ → ℕ → PowerSum K →ₗ[K] M) :
    (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N,
      F i j (pderiv i (pderiv j (monomial (residualExponent s) 1)))) =
      (s.map fun r => ((s.erase r).map fun t =>
        F (t-1) (r-1) (monomial (residualExponent ((s.erase r).erase t)) 1)).sum).sum := by
  classical
  have h := derivative_occurrence_sum N s hs (fun j =>
    ∑ i ∈ Finset.range N, (F i j).comp (pderiv i).toLinearMap)
  simp only [LinearMap.sum_apply, LinearMap.comp_apply] at h
  refine h.trans ?_
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro r hr
  exact derivative_occurrence_sum N (s.erase r)
    (fun t ht => hs t (Multiset.mem_of_mem_erase ht)) (fun i => F i (r-1))

/-- Ordered positive cuts, including equal halves, are in bijection with the
two derivative indices. No division by a symmetry factor occurs here. -/
theorem positive_cut_reindex {M : Type*} [AddCommMonoid M] (N r : ℕ)
    (hr : r ≤ N) (f : ℕ → ℕ → M) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      if r = i+j+2 then f i j else 0) =
      ∑ d ∈ Finset.Ioo 0 r, f (d-1) (r-d-1) := by
  classical
  rw [← Finset.sum_product' (f := fun i j => if r=i+j+2 then f i j else 0)]
  change (∑ z ∈ Finset.product (Finset.range N) (Finset.range N),
    if r = z.1+z.2+2 then f z.1 z.2 else 0) = _
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun z _ => z.1+1) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hz
    exact Finset.mem_Ioo.mpr (by omega)
  · intro z hz w hw he
    simp only [Finset.mem_filter] at hz hw
    apply Prod.ext <;> omega
  · intro d hd
    have hd := Finset.mem_Ioo.mp hd
    refine ⟨(d-1,r-d-1), ?_, by omega⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩
    · dsimp only
      omega
  · intro z hz
    have hz := (Finset.mem_filter.mp hz).2
    have he : r - (z.1+1) - 1 = z.2 := by omega
    simp only [Nat.add_sub_cancel, he]

theorem residualExponent_parts {s : Multiset ℕ} (hs : ∀ r ∈ s, 0 < r) :
    exponentParts (residualExponent s) = s := by
  simp only [exponentParts, residualExponent, Multiset.toFinsupp_toMultiset,
    Multiset.map_map]
  simpa [Function.comp_def] using
    Multiset.map_congr rfl (fun r hr => Nat.succ_pred_eq_of_pos (hs r hr))

private theorem residual_coeff {K : Type*} [Field K] [CharZero K]
    {k : ℕ} (σ : Nat.Partition k) (s : Multiset ℕ) (hs : ∀ r ∈ s, 0 < r) :
    (monomial (residualExponent s) (1 : K)).coeff (partitionExponent σ) =
      if σ.parts = s then 1 else 0 := by
  have he : residualExponent s = partitionExponent σ ↔ σ.parts = s := by
    constructor
    · intro h
      have := congrArg exponentParts h
      simpa only [residualExponent_parts hs, exponentParts_partitionExponent] using this.symm
    · intro h
      rw [← h]
      rfl
  simp only [coeff_monomial, he]

private theorem partition_part_bounds {k : ℕ} (ρ : Nat.Partition k) :
    ∀ r ∈ ρ.parts, 0 < r ∧ r ≤ k := by
  intro r hr
  exact ⟨ρ.parts_pos hr, ρ.parts_sum ▸ Multiset.le_sum_of_mem hr⟩

theorem join_derivative_coefficient {K : Type*} [Field K] [CharZero K]
    {k : ℕ} (ρ σ : Nat.Partition k) :
    (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
      ((i+1 : ℕ) * (j+1) : K) *
        (X (i+j+1) * pderiv i (pderiv j (powerSumMonomial (K := K) ρ))).coeff
          (partitionExponent σ)) =
      (ρ.parts.map fun (r : ℕ) => ((ρ.parts.erase r).map fun (s : ℕ) =>
        (r : K) * (s : K) *
          if σ.parts = (ρ.parts.erase r).erase s + {r+s} then 1 else 0).sum).sum := by
  classical
  let F : ℕ → ℕ → PowerSum K →ₗ[K] K := fun i j =>
    ((i+1 : ℕ) * (j+1) : K) •
      ((lcoeff K (partitionExponent σ)).comp (LinearMap.mulLeft K (X (i+j+1))))
  have h := double_derivative_occurrence_sum k ρ.parts (partition_part_bounds ρ) F
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    lcoeff_apply, smul_eq_mul, F] at h
  rw [Finset.sum_comm]
  change (∑ j ∈ Finset.range k, ∑ i ∈ Finset.range k,
    ((i+1 : ℕ) * (j+1) : K) *
      (X (i+j+1) * pderiv i (pderiv j
        (monomial (residualExponent ρ.parts) (1 : K)))).coeff (partitionExponent σ)) = _
  rw [h]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro r hr
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro s hs
  have hp := ρ.parts_pos hr
  have hq := ρ.parts_pos (Multiset.mem_of_mem_erase hs)
  have hi : s-1+1 = s := by omega
  have hj : r-1+1 = r := by omega
  have hjK : ((r-1 : ℕ) : K) + 1 = (r : K) := by exact_mod_cast hj
  have hij : s-1+(r-1)+1 = r+s-1 := by omega
  rw [hi,hjK,hij]
  have he : Finsupp.single (r+s-1) 1 +
      residualExponent ((ρ.parts.erase r).erase s) =
      residualExponent ((ρ.parts.erase r).erase s + {r+s}) := by
    rw [residualExponent_add, residualExponent_singleton, add_comm]
  rw [X, monomial_mul_monomial, one_mul, he,
    residual_coeff σ _ (by
      intro t ht
      rcases Multiset.mem_add.mp ht with ht | ht
      · exact ρ.parts_pos (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase ht))
      · have ht := Multiset.mem_singleton.mp ht; omega)]
  push_cast
  ring

private theorem sum_ite_occurrences {M : Type*} [AddCommMonoid M]
    (s : Multiset ℕ) (t : ℕ) (a : M) :
    (s.map fun r => if r=t then a else 0).sum = s.count t • a := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons r s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.count_cons, ih]
      by_cases h : r=t
      · simp [h, add_nsmul, add_comm]
      · simp [h, Ne.symm h]

private theorem derivative_occurrences {K : Type*} [Field K] [CharZero K]
    (s : Multiset ℕ) (hs : ∀ r ∈ s, 0 < r) (i : ℕ) :
    pderiv i (monomial (residualExponent s) (1 : K)) =
      (s.map fun r => if r=i+1 then
        monomial (residualExponent (s.erase r)) 1 else 0).sum := by
  rw [residual_derivative hs]
  have hm : (s.map fun r => if r=i+1 then
      monomial (residualExponent (s.erase r)) (1 : K) else 0) =
      (s.map fun r => if r=i+1 then
        monomial (residualExponent (s.erase (i+1))) 1 else 0) := by
    apply Multiset.map_congr rfl
    intro r _
    by_cases h : r=i+1 <;> simp [h]
  rw [hm, sum_ite_occurrences, Nat.cast_smul_eq_nsmul]

private theorem multiset_finset_sum {A I M : Type*} [AddCommMonoid M]
    (s : Multiset A) (T : Finset I) (f : A → I → M) :
    (∑ i ∈ T, (s.map fun a => f a i).sum) =
      (s.map fun a => ∑ i ∈ T, f a i).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp only [Multiset.map_cons, Multiset.sum_cons,
      Finset.sum_add_distrib, ih]

theorem cut_derivative_coefficient {K : Type*} [Field K] [CharZero K]
    {k : ℕ} (ρ σ : Nat.Partition k) :
    (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
      ((i+j+2 : ℕ) : K) *
        (X i * X j * pderiv (i+j+1) (powerSumMonomial (K := K) ρ)).coeff
          (partitionExponent σ)) =
      (ρ.parts.map fun (r : ℕ) => (r : K) * ∑ d ∈ Finset.Ioo 0 r,
        if σ.parts = ρ.parts.erase r + {d,r-d} then 1 else 0).sum := by
  classical
  have hmap (i j : ℕ) : ((i+j+2 : ℕ) : K) *
      (X i * X j * pderiv (i+j+1) (powerSumMonomial ρ) : PowerSum K).coeff
        (partitionExponent σ) =
      (ρ.parts.map fun (r : ℕ) => if r=i+j+2 then (r : K) *
        (X i * X j * monomial (residualExponent (ρ.parts.erase r)) (1 : K)).coeff
          (partitionExponent σ) else 0).sum := by
    let L : PowerSum K →ₗ[K] K := ((i+j+2 : ℕ) : K) •
      ((lcoeff K (partitionExponent σ)).comp (LinearMap.mulLeft K (X i * X j)))
    have h := congrArg L (derivative_occurrences (K := K) ρ.parts
      (fun r hr => ρ.parts_pos hr) (i+j+1))
    simp only [map_multiset_sum, Multiset.map_map, Function.comp_def] at h
    change L (pderiv (i+j+1) (monomial (residualExponent ρ.parts) 1)) = _ at h
    change L (pderiv (i+j+1) (monomial (residualExponent ρ.parts) 1)) = _
    rw [h]
    apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro r _
    by_cases he : r=i+j+2
    · simp only [show i+j+1+1=i+j+2 by omega, he, ite_true, L,
        LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        lcoeff_apply, smul_eq_mul]
    · simp [show i+j+1+1=i+j+2 by omega, he]
  simp_rw [hmap, multiset_finset_sum]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro r hr
  rw [positive_cut_reindex k r ((partition_part_bounds ρ r hr).2), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd := Finset.mem_Ioo.mp hd
  congr 1
  have hp : ∀ t ∈ ρ.parts.erase r + {d,r-d}, 0 < t := by
    intro t ht
    rcases Multiset.mem_add.mp ht with ht | ht
    · exact ρ.parts_pos (Multiset.mem_of_mem_erase ht)
    · have ht' : t=d ∨ t=r-d := by simpa using ht
      rcases ht' with rfl | rfl <;> omega
  have he : X (d-1) * X (r-d-1) *
      monomial (residualExponent (ρ.parts.erase r)) (1 : K) =
      monomial (residualExponent (ρ.parts.erase r + {d,r-d})) 1 := by
    have hexp : Finsupp.single (d-1) 1 + Finsupp.single (r-d-1) 1 +
        residualExponent (ρ.parts.erase r) =
        residualExponent (ρ.parts.erase r + {d,r-d}) := by
      rw [residualExponent_add]
      change _ = residualExponent (ρ.parts.erase r) + residualExponent (d ::ₘ {r-d})
      rw [residualExponent_cons, residualExponent_singleton]
      ac_rfl
    rw [X, X, monomial_mul_monomial, monomial_mul_monomial, one_mul, one_mul, hexp]
  rw [he, residual_coeff σ _ hp]

theorem diagonal_occurrence {K : Type*} [Field K] [CharZero K]
    {k : ℕ} (ρ : Nat.Partition k) :
    ((ρ.parts.map fun r => (Nat.choose r 2 : K)).sum) =
      (2 : K)⁻¹ * ∑ i ∈ Finset.range k,
        ((i + 1 : ℕ) * i : K) * (partitionExponent ρ i : K) := by
  classical
  have hsum := occurrence_sum (ρ.parts.map Nat.pred)
    (fun i => (Nat.choose (i+1) 2 : K)) k (by
      intro i hi
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hi
      have hp := ρ.parts_pos hr
      have hb := Multiset.le_sum_of_mem hr
      rw [ρ.parts_sum] at hb
      simp only [Nat.pred_eq_sub_one]
      omega)
  have hparts : ((ρ.parts.map Nat.pred).map Nat.succ) = ρ.parts := by
    rw [Multiset.map_map]
    simpa [Function.comp_def] using
      Multiset.map_congr rfl (fun r hr => Nat.succ_pred_eq_of_pos (ρ.parts_pos hr))
  have hleft : ((ρ.parts.map Nat.pred).map fun i => (Nat.choose (i+1) 2 : K)).sum =
      (ρ.parts.map fun r => (Nat.choose r 2 : K)).sum := by
    simpa only [Multiset.map_map, Function.comp_def] using
      congrArg (fun s : Multiset ℕ => (s.map fun r => (Nat.choose r 2 : K)).sum) hparts
  rw [hleft] at hsum
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc : (ρ.parts.map Nat.pred).count i = partitionExponent ρ i := rfl
  rw [hc, nsmul_eq_mul]
  have hchoose : (Nat.choose (i+1) 2 : K) = (i+1 : ℕ) * (i : K) / 2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  rw [hchoose]
  push_cast
  ring

theorem diagonal_derivative_coefficient {K : Type*} [Field K] [CharZero K]
    {k : ℕ} (ρ σ : Nat.Partition k) :
    (∑ i ∈ Finset.range k, ((i+1 : ℕ) * i : K) *
      (X i * pderiv i (powerSumMonomial (K := K) ρ)).coeff (partitionExponent σ)) =
      (∑ i ∈ Finset.range k, ((i+1 : ℕ) * i : K) *
        (partitionExponent ρ i : K)) * (if σ = ρ then 1 else 0) := by
  classical
  unfold powerSumMonomial
  simp_rw [X_mul_pderiv_monomial, ← Nat.cast_smul_eq_nsmul K]
  simp only [coeff_smul, coeff_monomial, smul_eq_mul]
  by_cases h : σ = ρ
  · subst σ
    simp
  · have he : partitionExponent ρ ≠ partitionExponent σ :=
      fun he => h ((partitionExponent_injective k) he).symm
    simp [he, h]

/-- Equality of literal differential coefficients and the single canonical
native occurrence coefficient. Empty residuals and all zero branches remain. -/
theorem operatorCoefficient_eq_rowCoefficient {K : Type*} [Field K] [CharZero K]
    (b : K) {k : ℕ} (ρ σ : Nat.Partition k) :
    operatorCoefficient b ρ σ = rowCoefficient b ρ σ := by
  classical
  unfold operatorCoefficient
  rw [differentialOperator_on_homogeneous b (powerSumMonomial_homogeneous ρ)]
  change lcoeff K (partitionExponent σ) (boundedOperator b k (powerSumMonomial ρ)) = _
  rw [boundedOperator_apply]
  simp only [map_smul, map_add, map_sum, smul_eq_mul, lcoeff_apply]
  rw [join_derivative_coefficient, cut_derivative_coefficient,
    diagonal_derivative_coefficient]
  have hcut : (ρ.parts.map fun (r : ℕ) => (r : K) / 2 *
      ∑ d ∈ Finset.Ioo 0 r,
        if σ.parts = ρ.parts.erase r + {d,r-d} then (1 : K) else 0).sum =
      (2 : K)⁻¹ * (ρ.parts.map fun (r : ℕ) => (r : K) *
        ∑ d ∈ Finset.Ioo 0 r,
          if σ.parts = ρ.parts.erase r + {d,r-d} then (1 : K) else 0).sum := by
    rw [← Multiset.sum_map_mul_left]
    apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro r _
    rw [div_eq_mul_inv]
    ring
  rw [rowCoefficient, hcut, diagonal_occurrence]
  ring

/-- Original normalized C2, with the same coefficient as native C1. -/
theorem same_coefficient_C2 {k : ℕ} (lam : Nat.Partition k) :
    (∑ μ : Nat.Partition k,
      (rowCoefficient (RatFunc.X : CoefficientField) μ lam / normalization μ) •
        powerSumMonomial μ) =
      differentialOperator (RatFunc.X : CoefficientField)
        ((normalization lam)⁻¹ • powerSumMonomial lam) := by
  simpa only [operatorCoefficient_eq_rowCoefficient] using normalized_operatorCoefficient_C2 lam

/-- The original native C1 and literal polynomial C2 share one coefficient
function. Actual matching realization also proves that function is unique. -/
theorem conjecture58 (k : ℕ) (_hk : 1 ≤ k) (lam : Nat.Partition k) :
    ∃! c : Nat.Partition k → CoefficientField,
      S (RatFunc.X : CoefficientField) k (indicator lam) = (fun p => c (ct p)) ∧
      (∑ μ : Nat.Partition k, (c μ / normalization μ) • powerSumMonomial μ) =
        differentialOperator (RatFunc.X : CoefficientField)
          ((normalization lam)⁻¹ • powerSumMonomial lam) := by
  refine ⟨fun μ => rowCoefficient (RatFunc.X : CoefficientField) μ lam,
    ⟨native_C1 k lam, same_coefficient_C2 lam⟩, ?_⟩
  intro c hc
  funext μ
  obtain ⟨p,hp⟩ :=
    D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRealization.matching_realization μ
  have h := congrFun hc.1 p
  have hn := native_row (RatFunc.X : CoefficientField) lam p
  rw [hp] at h hn
  exact h.symm.trans hn

#print axioms operatorCoefficient_eq_rowCoefficient
#print axioms same_coefficient_C2
#print axioms conjecture58

end D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyOccurrence
