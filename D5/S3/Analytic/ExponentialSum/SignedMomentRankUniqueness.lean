import D5.S3.Analytic.ExponentialSum.ExponentialMomentNonnegativeSelector
import D5.S3.Weil.ZetaLinear.HermitianPosPart
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Rank

/-! A nonzero family of signed Hermitian residues with small positive and negative
rank budgets and vanishing exponential moments has a nonzero common kernel. -/

noncomputable section

open Matrix RHLinalg
open scoped BigOperators ComplexOrder
open D5.S3.Analytic.ExponentialSum.DescartesRule

namespace SignedMomentRankUniqueness

variable {d : Type*} [Fintype d]

/-- Every positively weighted PSD summand annihilates a vector in the kernel
of the weighted sum. Zero weights are allowed at the other indices. -/
theorem mulVec_eq_zero_of_weighted_psd_sum {ι : Type*}
    (s : Finset ι) (A : ι → Matrix d d ℂ) (w : ι → ℝ)
    (hA : ∀ i ∈ s, (A i).PosSemidef) (hw : ∀ i ∈ s, 0 ≤ w i)
    {v : d → ℂ} (hv : (∑ i ∈ s, w i • A i) *ᵥ v = 0)
    {i : ι} (hi : i ∈ s) (hwi : 0 < w i) : A i *ᵥ v = 0 := by
  let q : ι → ℂ := fun j => star v ⬝ᵥ (A j *ᵥ v)
  have hq (j : ι) (hj : j ∈ s) : 0 ≤ q j :=
    (hA j hj).dotProduct_mulVec_nonneg v
  have hsum : ∑ j ∈ s, w j • q j = 0 := by
    have h := congrArg (fun z : d → ℂ => star v ⬝ᵥ z) hv
    simpa only [q, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
      dotProduct_zero] using h
  have hreal : ∑ j ∈ s, w j * (q j).re = 0 := by
    change ∑ j ∈ s, w j * Complex.reLm (q j) = 0
    simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using
      congrArg Complex.reLm hsum
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun j hj =>
    mul_nonneg (hw j hj) (Complex.nonneg_iff.mp (hq j hj)).1).mp hreal i hi
  have hre : (q i).re = 0 := (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hwi)
  have him : (q i).im = 0 := (Complex.nonneg_iff.mp (hq i hi)).2.symm
  apply (hA i hi).dotProduct_mulVec_zero_iff.mp
  exact Complex.ext (by simpa using hre) (by simpa using him)

private theorem signVariations_le {k : ℕ} (a : Fin k → ℝ) :
    (List.ofFn a).signVariations ≤ k - 1 := by
  let signs := (List.ofFn a).map SignType.sign
  have hlength : ((signs.filter (· ≠ 0)).destutter (· ≠ ·)).length ≤ k := by
    calc
      _ ≤ (signs.filter (· ≠ 0)).length := (List.destutter_sublist _ _).length_le
      _ ≤ signs.length := List.length_filter_le _ _
      _ = k := by simp [signs]
  exact Nat.sub_le_sub_right hlength 1

private theorem exponentialSum_coeff_eq_zero {k : ℕ} (a μ : Fin k → ℝ)
    (hμ : StrictAnti μ) (times : Finset ℝ) (hcard : k ≤ times.card)
    (hzero : ∀ t ∈ times, exponentialSum a μ t = 0) : a = 0 := by
  by_contra h
  have hne : ∃ i, a i ≠ 0 := by
    by_contra! hall
    exact h (funext hall)
  have hk : 0 < k := by
    obtain ⟨i, _⟩ := hne
    exact i.isLt.pos
  have hbound := (zero_bound a μ hμ hne times hzero).trans (signVariations_le a)
  omega

/-- The exponential evaluation matrix with entries `exp(-x * t)`.
Rows are sample times and columns are selected rates. -/
def selectedExponentialVandermonde (times selected : Finset ℝ) : Matrix times selected ℂ :=
  Matrix.of fun t x => (Real.exp (-(x : ℝ) * (t : ℝ)) : ℂ)

/-- As many distinct sample times as selected rates suffice for column injectivity. -/
theorem selectedExponentialVandermonde_injective (times selected : Finset ℝ)
    (hcard : selected.card ≤ times.card) :
    Function.Injective (selectedExponentialVandermonde times selected).mulVec := by
  classical
  change Function.Injective (selectedExponentialVandermonde times selected).mulVecLin
  rw [← LinearMap.ker_eq_bot]
  apply Matrix.ker_mulVecLin_eq_bot_iff.mpr
  intro c hc
  let e : Fin selected.card ≃o selected := selected.orderIsoOfFin rfl
  let μ : Fin selected.card → ℝ := fun i => -((e i : selected) : ℝ)
  have hμ : StrictAnti μ := fun i j hij => neg_lt_neg (e.strictMono hij)
  have hsum (t : ℝ) (ht : t ∈ times) :
      ∑ i, Real.exp (μ i * t) • c (e i) = 0 := by
    have h := congrFun hc (⟨t, ht⟩ : times)
    calc
      _ = ∑ x : selected, Real.exp (-(x : ℝ) * t) • c x :=
        Equiv.sum_comp e.toEquiv (fun x : selected => Real.exp (-(x : ℝ) * t) • c x)
      _ = 0 := by
        simpa only [selectedExponentialVandermonde, Matrix.mulVec, Matrix.of_apply,
          dotProduct, Pi.zero_apply, Complex.real_smul] using h
  have hpart (L : ℂ →ₗ[ℝ] ℝ) : (fun i => L (c (e i))) = 0 := by
    apply exponentialSum_coeff_eq_zero _ μ hμ times hcard
    intro t ht
    simpa only [exponentialSum, map_sum, map_smul, map_zero, smul_eq_mul, mul_comm] using
      congrArg L (hsum t ht)
  funext x
  obtain ⟨i, rfl⟩ := e.surjective x
  apply Complex.ext
  · exact congrFun (hpart Complex.reLm) i
  · exact congrFun (hpart Complex.imLm) i

private theorem rank_pos_of_ne_zero [DecidableEq d] {A : Matrix d d ℂ} (hA : A ≠ 0) :
    0 < A.rank := by
  by_contra! h
  have hrange : LinearMap.range A.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero h)
  apply hA
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [Matrix.zero_mulVec]
  exact LinearMap.congr_fun (LinearMap.range_eq_bot.mp hrange) (Pi.single i 1)

private theorem weighted_sum_rank_le {ι : Type*} [DecidableEq d]
    (s : Finset ι) (P : ι → Matrix d d ℂ) (w : ι → ℝ) :
    (∑ x ∈ s, w x • P x).rank ≤ ∑ x ∈ s, (P x).rank := by
  classical
  have h := LinearMap.rank_finsetSum_le s (fun x => Matrix.toLin' (w x • P x))
  rw [← map_sum] at h
  have hsum : (∑ x ∈ s, w x • P x).rank ≤ ∑ x ∈ s, (w x • P x).rank := by
    have hcast : ((∑ x ∈ s, w x • P x).rank : Cardinal) ≤
        ∑ x ∈ s, ((w x • P x).rank : Cardinal) := by
      dsimp only [Matrix.rank]
      simpa only [Matrix.toLin'_apply', ← Module.finrank_eq_rank] using h
    exact_mod_cast hcast
  refine hsum.trans (Finset.sum_le_sum fun x _ => ?_)
  by_cases hx : w x = 0
  · simp [hx]
  have heq : w x • P x = (w x : ℂ) • P x := by
    ext i j
    exact Complex.real_smul
  rw [heq, Matrix.rank_smul_of_mem_nonZeroDivisors _]
  exact mem_nonZeroDivisors_of_ne_zero (Complex.ofReal_ne_zero.mpr hx)

private theorem exists_nonzero_mulVec_eq_zero_of_rank_lt
    {A : Matrix d d ℂ} (hA : A.rank < Fintype.card d) :
    ∃ v : d → ℂ, v ≠ 0 ∧ A *ᵥ v = 0 := by
  have hdim := A.mulVecLin.finrank_range_add_finrank_ker
  rw [← Matrix.rank, Module.finrank_fintype_fun_eq_card] at hdim
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ :=
    Submodule.one_le_finrank_iff.mp (by omega)
  obtain ⟨v, hv, hne⟩ := (LinearMap.ker A.mulVecLin).ne_bot_iff.mp hker
  exact ⟨v, hne, LinearMap.mem_ker.mp hv⟩

private theorem exists_selection (positive : Finset ℝ) {xMin : ℝ}
    (hmin : xMin ∈ positive) (r : ℕ) :
    ∃ selected ⊆ positive, xMin ∈ selected ∧ selected.card = min (r + 1) positive.card := by
  classical
  let k := min (r + 1) positive.card
  have hk : 0 < k := lt_min (Nat.succ_pos _) (Finset.card_pos.mpr ⟨_, hmin⟩)
  have hcount : k - 1 ≤ (positive.erase xMin).card := by
    rw [Finset.card_erase_of_mem hmin]
    exact Nat.sub_le_sub_right (min_le_right _ _) _
  obtain ⟨rest, hrest, hcard⟩ := Finset.exists_subset_card_eq hcount
  have hnot : xMin ∉ rest := fun h => Finset.notMem_erase xMin positive (hrest h)
  refine ⟨insert xMin rest, ?_, Finset.mem_insert_self _ _, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hmin
    · exact (Finset.mem_erase.mp (hrest hx)).2
  · rw [Finset.card_insert_of_notMem hnot, hcard]
    omega

private theorem exists_common_kernel_of_oriented_parts [DecidableEq d]
    (active times : Finset ℝ) (r : ℕ) (htimes : 2 * r + 2 ≤ times.card)
    (P N : ℝ → Matrix d d ℂ)
    (hP : ∀ x ∈ active, (P x).PosSemidef) (hN : ∀ x ∈ active, (N x).PosSemidef)
    (hbudget : ∑ x ∈ active, (P x).rank ≤ Fintype.card d + r)
    (xMin : ℝ) (hmin : xMin ∈ active) (hmin_le : ∀ x ∈ active, xMin ≤ x)
    (hPmin : P xMin ≠ 0)
    (hmoment : ∀ t ∈ times, ∑ x ∈ active, Real.exp (-t * x) • (P x - N x) = 0) :
    ∃ v : d → ℂ, v ≠ 0 ∧ ∀ x ∈ active, (P x - N x) *ᵥ v = 0 := by
  classical
  let positive := active.filter fun x => P x ≠ 0
  have hminPos : xMin ∈ positive := Finset.mem_filter.mpr ⟨hmin, hPmin⟩
  obtain ⟨selected, hselected, hminSel, hcard⟩ := exists_selection positive hminPos r
  have hsub : selected ⊆ active := hselected.trans (Finset.filter_subset _ _)
  let k := selected.card
  have hk : 1 ≤ k := Finset.card_pos.mpr ⟨xMin, hminSel⟩
  have hkr : k ≤ r + 1 := hcard.le.trans (min_le_left _ _)
  have h2k : 2 * k ≤ times.card := by omega
  have hn : 0 < Fintype.card d := (rank_pos_of_ne_zero hPmin).trans_le
    (Matrix.rank_le_card_width _)
  let sample := times.orderEmbOfCardLe h2k
  let μ : Fin (2 * k) → ℝ := fun j => -sample j
  have hμ : StrictAnti μ := fun _ _ hij => neg_lt_neg (sample.strictMono hij)
  obtain ⟨a, _, hzero, hpos, _⟩ :=
    ExponentialMomentNonnegativeSelector.exists_selector_pos_off_selected
      hk active selected hsub rfl xMin hminSel hmin_le μ (Or.inl hμ)
  let w := exponentialSum a μ
  have hw (x : ℝ) (hx : x ∈ active) : 0 ≤ w x := by
    by_cases hxs : x ∈ selected
    · rw [show w x = 0 from hzero x hxs]
    · exact (hpos x hx hxs).le

  have hweighted : ∑ x ∈ active, w x • (P x - N x) = 0 := by
    calc
      _ = ∑ x ∈ active, ∑ j, (a j * Real.exp (μ j * x)) • (P x - N x) := by
        simp only [w, exponentialSum, Finset.sum_smul]
      _ = ∑ j, ∑ x ∈ active, (a j * Real.exp (μ j * x)) • (P x - N x) :=
        Finset.sum_comm
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [show (∑ x ∈ active, (a j * Real.exp (μ j * x)) • (P x - N x)) =
            a j • ∑ x ∈ active, Real.exp (μ j * x) • (P x - N x) by
          simp only [Finset.smul_sum, mul_smul]]
        rw [hmoment (sample j) (Finset.orderEmbOfCardLe_mem _ _ _), smul_zero]
  have hequal : (∑ x ∈ active, w x • P x) = ∑ x ∈ active, w x • N x := by
    simpa only [smul_sub, Finset.sum_sub_distrib, sub_eq_zero] using hweighted

  have hremaining : (∑ x ∈ active \ selected, w x • P x) =
      ∑ x ∈ active, w x • P x :=
    Finset.sum_subset Finset.sdiff_subset fun x hx hnot => by
      have hxs : x ∈ selected := by
        by_contra h
        exact hnot (Finset.mem_sdiff.mpr ⟨hx, h⟩)
      rw [show w x = 0 from hzero x hxs, zero_smul]
  have hrank : (∑ x ∈ active, w x • P x).rank ≤ Fintype.card d - 1 := by
    rw [← hremaining]
    by_cases hkfull : k = r + 1
    · have hremoved : k ≤ ∑ x ∈ selected, (P x).rank := by
        calc
          k = ∑ _x ∈ selected, (1 : ℕ) := by simp [k]
          _ ≤ ∑ x ∈ selected, (P x).rank :=
            Finset.sum_le_sum fun x hx =>
              rank_pos_of_ne_zero (Finset.mem_filter.mp (hselected hx)).2
      have hsplit := Finset.sum_sdiff (f := fun x => (P x).rank) hsub
      have hrest : ∑ x ∈ active \ selected, (P x).rank ≤ Fintype.card d - 1 := by
        omega
      exact (weighted_sum_rank_le _ P w).trans hrest
    · have hposcard : positive.card ≤ k := by omega
      have hall : selected = positive := Finset.eq_of_subset_of_card_le hselected hposcard
      have hsum : ∑ x ∈ active \ selected, w x • P x = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        obtain ⟨hxActive, hxNot⟩ := Finset.mem_sdiff.mp hx
        have hPx : P x = 0 := by
          by_contra h
          exact hxNot (hall.symm ▸ Finset.mem_filter.mpr ⟨hxActive, h⟩)
        rw [hPx, smul_zero]
      rw [hsum, Matrix.rank_zero]
      exact Nat.zero_le _
  obtain ⟨v, hv, hvP⟩ := exists_nonzero_mulVec_eq_zero_of_rank_lt (hrank.trans_lt (by omega))
  have hvN : (∑ x ∈ active, w x • N x) *ᵥ v = 0 := hequal ▸ hvP
  have hoff (x : ℝ) (hx : x ∈ active) (hxs : x ∉ selected) : (P x - N x) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec,
      mulVec_eq_zero_of_weighted_psd_sum active P w hP hw hvP hx (hpos x hx hxs),
      mulVec_eq_zero_of_weighted_psd_sum active N w hN hw hvN hx (hpos x hx hxs), sub_zero]

  have hsamples (t : ℝ) (ht : t ∈ times) :
      ∑ x ∈ selected, Real.exp (-t * x) • ((P x - N x) *ᵥ v) = 0 := by
    have h := congrArg (fun M : Matrix d d ℂ => M *ᵥ v) (hmoment t ht)
    rw [Matrix.sum_mulVec, Matrix.zero_mulVec] at h
    simp only [Matrix.smul_mulVec] at h
    rw [← h]
    exact Finset.sum_subset hsub fun x hx hxs => by rw [hoff x hx hxs, smul_zero]

  have hselectedZero (i : d) :
      (fun x : selected => ((P x - N x) *ᵥ v) i) = 0 := by
    apply selectedExponentialVandermonde_injective times selected (by omega)
    rw [Matrix.mulVec_zero]
    funext t
    have ht := congrFun (hsamples t t.property) i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at ht
    rw [Finset.sum_subtype selected (fun _ => Iff.rfl)] at ht
    have harg (x : selected) : -(t : ℝ) * (x : ℝ) = -(x : ℝ) * (t : ℝ) := by ring
    simp_rw [harg] at ht
    simpa only [selectedExponentialVandermonde, Matrix.mulVec, Matrix.of_apply, dotProduct,
      Pi.zero_apply, Complex.real_smul] using ht

  refine ⟨v, hv, fun x hx => ?_⟩
  by_cases hxs : x ∈ selected
  · funext i
    exact congrFun (hselectedZero i) ⟨x, hxs⟩
  · exact hoff x hx hxs

/-- A nonzero family with the two signed-part rank budgets and at least
`2 * r + 2` distinct exponential moment zeros has a nonzero common kernel. -/
theorem exists_common_kernel_of_nonzero_signed_residue [DecidableEq d]
    (carrier times : Finset ℝ) (r : ℕ) (htimes : 2 * r + 2 ≤ times.card)
    (D : ℝ → Matrix d d ℂ) (hD : ∀ x, (D x).IsHermitian)
    (hbudgetPos : ∑ x ∈ carrier, (hermPosPart (hD x)).rank ≤ Fintype.card d + r)
    (hbudgetNeg : ∑ x ∈ carrier, (hermNegPart (hD x)).rank ≤ Fintype.card d + r)
    (hmoment : ∀ t ∈ times, ∑ x ∈ carrier, Real.exp (-t * x) • D x = 0)
    (hne : ∃ x ∈ carrier, D x ≠ 0) :
    ∃ v : d → ℂ, v ≠ 0 ∧ ∀ x ∈ carrier, D x *ᵥ v = 0 := by
  classical
  let active := carrier.filter fun x => D x ≠ 0
  have hactive : active.Nonempty := by
    obtain ⟨x, hx, hn⟩ := hne
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hn⟩⟩
  let xMin := active.min' hactive
  have hmin : xMin ∈ active := active.min'_mem hactive
  have hmin_le (x : ℝ) (hx : x ∈ active) : xMin ≤ x := active.min'_le x hx
  have hvanish {x : ℝ} (hx : x ∈ carrier) (hnot : x ∉ active) : D x = 0 := by
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨hx, h⟩)
  have hactiveMoment (t : ℝ) (ht : t ∈ times) :
      ∑ x ∈ active, Real.exp (-t * x) • D x = 0 :=
    (Finset.sum_subset (Finset.filter_subset _ _) fun x hx hnot => by
      rw [hvanish hx hnot, smul_zero]).trans (hmoment t ht)

  let P := fun x => hermPosPart (hD x)
  let N := fun x => hermNegPart (hD x)
  have hsplit (x : ℝ) : P x - N x = D x := hermPosPart_sub_hermNegPart (hD x)
  have hP (x : ℝ) (_ : x ∈ active) : (P x).PosSemidef := hermPosPart_posSemidef (hD x)
  have hN (x : ℝ) (_ : x ∈ active) : (N x).PosSemidef := hermNegPart_posSemidef (hD x)

  have hkernel : ∃ v : d → ℂ, v ≠ 0 ∧ ∀ x ∈ active, D x *ᵥ v = 0 := by
    by_cases hPmin : P xMin ≠ 0
    · have hbudget : ∑ x ∈ active, (P x).rank ≤ Fintype.card d + r :=
        (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hbudgetPos
      simpa only [hsplit] using
        exists_common_kernel_of_oriented_parts active times r htimes P N hP hN hbudget
          xMin hmin hmin_le hPmin (by simpa only [hsplit] using hactiveMoment)
    · have hNmin : N xMin ≠ 0 := by
        intro h
        have hneMin := (Finset.mem_filter.mp hmin).2
        apply hneMin
        rw [← hsplit, not_not.mp hPmin, h, sub_zero]
      have hreverse (x : ℝ) : N x - P x = -D x := by rw [← neg_sub, hsplit]
      have hmoment' (t : ℝ) (ht : t ∈ times) :
          ∑ x ∈ active, Real.exp (-t * x) • (N x - P x) = 0 := by
        simp only [hreverse, smul_neg, Finset.sum_neg_distrib, hactiveMoment t ht, neg_zero]
      have hbudget : ∑ x ∈ active, (N x).rank ≤ Fintype.card d + r :=
        (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hbudgetNeg
      obtain ⟨v, hv, hvAll⟩ := exists_common_kernel_of_oriented_parts active times r htimes
        N P hN hP hbudget xMin hmin hmin_le hNmin hmoment'
      exact ⟨v, hv, by simpa only [hreverse, Matrix.neg_mulVec, neg_eq_zero] using hvAll⟩
  obtain ⟨v, hv, hvAll⟩ := hkernel
  refine ⟨v, hv, fun x hx => ?_⟩
  by_cases ha : x ∈ active
  · exact hvAll x ha
  · rw [hvanish hx ha, Matrix.zero_mulVec]

/-- A trivial common kernel rules out any nonzero signed residue under the two
rank budgets and the stated number of exponential moment equalities. -/
theorem signed_residue_eq_zero_of_trivial_common_kernel [DecidableEq d]
    (carrier times : Finset ℝ) (r : ℕ) (htimes : 2 * r + 2 ≤ times.card)
    (D : ℝ → Matrix d d ℂ) (hD : ∀ x, (D x).IsHermitian)
    (hbudgetPos : ∑ x ∈ carrier, (hermPosPart (hD x)).rank ≤ Fintype.card d + r)
    (hbudgetNeg : ∑ x ∈ carrier, (hermNegPart (hD x)).rank ≤ Fintype.card d + r)
    (hmoment : ∀ t ∈ times, ∑ x ∈ carrier, Real.exp (-t * x) • D x = 0)
    (hkernel : ∀ v : d → ℂ, (∀ x ∈ carrier, D x *ᵥ v = 0) → v = 0) :
    ∀ x ∈ carrier, D x = 0 := by
  intro x hx
  by_contra h
  obtain ⟨v, hv, hvAll⟩ := exists_common_kernel_of_nonzero_signed_residue carrier times r
    htimes D hD hbudgetPos hbudgetNeg hmoment ⟨x, hx, h⟩
  exact hv (hkernel v hvAll)

end SignedMomentRankUniqueness
