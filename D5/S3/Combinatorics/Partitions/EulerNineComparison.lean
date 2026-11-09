/- GID: D5/S3/Combinatorics/Partitions/EulerNineComparison
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/EulerNineComparison
   mirror-E: none(waiver:restricted-partition-nine-block-comparison)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.Glaisher]
   utility: none
   digest: Multiplicity-free cancellation and telescoping for the Euler nine-block products. -/

import D5.S3.Combinatorics.Partitions.RestrictedEulerCancellation

/-! Coefficient comparisons for three genuine restricted partition products.
The infinite products are represented by partition counting series. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.Partitions.EulerNineComparison

open RestrictedEulerCancellation
open OrdinaryEulerProduct
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable def S : PowerSeries ℚ := restrictedSeries (fun m => m % 9 ≠ 0)

noncomputable def block (r i : ℕ) : PowerSeries ℚ :=
  (1 - PowerSeries.X ^ (9 * i + r)) *
    (1 - PowerSeries.X ^ (9 * i + 9 - r))

def pairWeight (r : ℕ → ℕ) (a : ℕ × Bool) : ℕ :=
  9 * a.1 + if a.2 then r a.1 else 9 - r a.1

private theorem pairWeight_bounds (r : ℕ → ℕ) (a : ℕ × Bool)
    (hr : r a.1 = 1 ∨ r a.1 = 2 ∨ r a.1 = 4) :
    9 * a.1 < pairWeight r a ∧ pairWeight r a < 9 * (a.1 + 1) := by
  rcases a with ⟨i, b⟩
  change r i = 1 ∨ r i = 2 ∨ r i = 4 at hr
  cases b
  · change 9 * i < 9 * i + (9 - r i) ∧ 9 * i + (9 - r i) < 9 * (i + 1)
    omega
  · change 9 * i < 9 * i + r i ∧ 9 * i + r i < 9 * (i + 1)
    omega

private theorem pairWeight_injective (r : ℕ → ℕ) (I : Finset ℕ)
    (hr : ∀ i ∈ I, r i = 1 ∨ r i = 2 ∨ r i = 4) :
    Set.InjOn (pairWeight r) (↑(I.product (Finset.univ : Finset Bool))) := by
  intro a ha b hb hab
  have hai := (Finset.mem_product.mp ha).1
  have hbi := (Finset.mem_product.mp hb).1
  have habounds := pairWeight_bounds r a (hr _ hai)
  have hbbounds := pairWeight_bounds r b (hr _ hbi)
  have hi : a.1 = b.1 := by omega
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  dsimp only at hi
  subst j
  congr 1
  cases a <;> cases b <;> dsimp [pairWeight] at hab ⊢ <;> try rfl
  all_goals have := hr i hai; omega

/-- Every factor cancels a different allowed reciprocal.  The extra two
small factors must be absent from the chosen blocks. -/
theorem coeff_cancel_blocks (r : ℕ → ℕ) (I : Finset ℕ) (u v : ℕ)
    (hr : ∀ i ∈ I, r i = 1 ∨ r i = 2 ∨ r i = 4)
    (hu : 0 < u ∧ u < 9) (hv : 0 < v ∧ v < 9) (huv : u ≠ v)
    (havoid : ∀ i ∈ I, ∀ b : Bool, pairWeight r (i, b) ≠ u ∧
      pairWeight r (i, b) ≠ v) (n : ℕ) :
    0 ≤ PowerSeries.coeff n
      (S * ((1 - PowerSeries.X ^ u) * (1 - PowerSeries.X ^ v)) *
        ∏ i ∈ I, block (r i) i) := by
  classical
  let J := (I.product (Finset.univ : Finset Bool)).disjSum
    (Finset.univ : Finset Bool)
  let w : (ℕ × Bool) ⊕ Bool → ℕ := Sum.elim (pairWeight r) (fun b => if b then u else v)
  have hinj : Set.InjOn w J := by
    intro a ha b hb hab
    cases a with
    | inl a =>
      have ha' : a ∈ I.product Finset.univ := by simpa [J] using ha
      cases b with
      | inl b =>
        have hb' : b ∈ I.product Finset.univ := by simpa [J] using hb
        exact congrArg Sum.inl (pairWeight_injective r I hr ha' hb' hab)
      | inr b =>
        have hav := havoid a.1 (Finset.mem_product.mp ha').1 a.2
        cases b <;> simp_all [w]
    | inr a =>
      cases b with
      | inl b =>
        have hb' : b ∈ I.product Finset.univ := by simpa [J] using hb
        have hbv := havoid b.1 (Finset.mem_product.mp hb').1 b.2
        cases a <;> simp_all [w]
      | inr b =>
        cases a <;> cases b <;> simp_all [w]
  have hw : ∀ a ∈ J, 0 < w a ∧ w a % 9 ≠ 0 := by
    intro a ha
    cases a with
    | inl a =>
      have ha' : a.1 ∈ I := by simpa [J] using ha
      have hh := hr a.1 ha'
      rcases a with ⟨i, b⟩
      cases b <;> dsimp [w, pairWeight]
      all_goals rcases hh with hh | hh | hh <;> simp [hh] <;> omega
    | inr b =>
      cases b <;> dsimp [w] <;> omega
  have h := coeff_cancelled_indexed_product_nonnegative
    (fun m => m % 9 ≠ 0) J w hinj hw n
  simp only [J, Finset.prod_disjSum, w, Sum.elim_inl, Sum.elim_inr] at h
  rw [Finset.product_eq_sprod, Finset.prod_product] at h
  simp only [Fintype.prod_bool, pairWeight, ite_true, Bool.false_eq_true, ite_false] at h
  have he : (∏ i ∈ I, (1 - PowerSeries.X ^ (9 * i + r i)) *
      (1 - PowerSeries.X ^ (9 * i + (9 - r i))) : PowerSeries ℚ) =
      ∏ i ∈ I, block (r i) i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hh := hr i hi
    dsimp only [block]
    rw [show 9 * i + 9 - r i = 9 * i + (9 - r i) by omega]
  rw [he] at h
  simpa only [S, mul_assoc, mul_left_comm, mul_comm] using h

noncomputable def mixed (N k r s : ℕ) : PowerSeries ℚ :=
  ∏ i ∈ Finset.range N, block (if i < k then r else s) i

private theorem mixed_step (N k r s : ℕ) (hk : k < N) :
    mixed N (k + 1) r s - mixed N k r s =
      (block r k - block s k) *
        ∏ i ∈ (Finset.range N).erase k, block (if i < k then r else s) i := by
  have hkm : k ∈ Finset.range N := by simpa using hk
  rw [mixed, mixed, ← Finset.mul_prod_erase _ _ hkm,
    ← Finset.mul_prod_erase _ _ hkm]
  simp only [Nat.lt_succ_self, ite_true, Nat.lt_irrefl, ite_false]
  have he : (∏ i ∈ (Finset.range N).erase k, block (if i < k + 1 then r else s) i) =
      ∏ i ∈ (Finset.range N).erase k, block (if i < k then r else s) i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hne := (Finset.mem_erase.mp hi).1
    have hh : (i < k + 1) = (i < k) := propext (by omega)
    simp only [hh]
  rw [he]
  ring

private theorem block_difference_42 (k : ℕ) :
    block 4 k - block 2 k =
      PowerSeries.X ^ (9 * k + 2) *
        ((1 - PowerSeries.X ^ 2) * (1 - PowerSeries.X ^ 3)) := by
  simp only [block]
  rw [show 9 * k + 9 - 4 = 9 * k + 5 by omega,
    show 9 * k + 9 - 2 = 9 * k + 7 by omega]
  simp only [pow_add]
  ring

private theorem block_difference_21 (k : ℕ) :
    block 2 k - block 1 k =
      PowerSeries.X ^ (9 * k + 1) *
        ((1 - PowerSeries.X) * (1 - PowerSeries.X ^ 6)) := by
  simp only [block]
  rw [show 9 * k + 9 - 2 = 9 * k + 7 by omega,
    show 9 * k + 9 - 1 = 9 * k + 8 by omega]
  simp only [pow_add]
  ring

/-- Finite telescoping uses positivity only after all signed Euler factors
in a summand have been cancelled; no signed factor multiplies an inequality. -/
theorem coeff_finite_comparison (r s u v t : ℕ)
    (hr : r = 1 ∨ r = 2 ∨ r = 4) (hs : s = 1 ∨ s = 2 ∨ s = 4)
    (hu : 0 < u ∧ u < 9) (hv : 0 < v ∧ v < 9) (huv : u ≠ v)
    (hdiff : ∀ k, block r k - block s k = PowerSeries.X ^ (9 * k + t) *
      ((1 - PowerSeries.X ^ u) * (1 - PowerSeries.X ^ v)))
    (havoid : ∀ k i, i ≠ k → ∀ b : Bool,
      pairWeight (fun j => if j < k then r else s) (i, b) ≠ u ∧
      pairWeight (fun j => if j < k then r else s) (i, b) ≠ v)
    (N n : ℕ) :
    PowerSeries.coeff n (S * ∏ i ∈ Finset.range N, block s i) ≤
      PowerSeries.coeff n (S * ∏ i ∈ Finset.range N, block r i) := by
  have hstep (k : ℕ) (hk : k < N) :
      PowerSeries.coeff n (S * mixed N k r s) ≤
        PowerSeries.coeff n (S * mixed N (k + 1) r s) := by
    have hp := coeff_cancel_blocks (fun j => if j < k then r else s)
      ((Finset.range N).erase k) u v
      (by intro i _; split_ifs <;> assumption) hu hv huv
      (by intro i hi; exact havoid k i (Finset.mem_erase.mp hi).1)
    have he : S * mixed N (k + 1) r s - S * mixed N k r s =
        PowerSeries.X ^ (9 * k + t) *
          (S * ((1 - PowerSeries.X ^ u) * (1 - PowerSeries.X ^ v)) *
            ∏ i ∈ (Finset.range N).erase k, block (if i < k then r else s) i) := by
      rw [← mul_sub, mixed_step N k r s hk, hdiff]
      ring
    have hn : 0 ≤ PowerSeries.coeff n
        (S * mixed N (k + 1) r s - S * mixed N k r s) := by
      rw [he, PowerSeries.coeff_X_pow_mul']
      split_ifs
      · exact hp _
      · exact le_rfl
    simpa only [map_sub, sub_nonneg] using hn
  have hind : ∀ k, k ≤ N → PowerSeries.coeff n (S * mixed N 0 r s) ≤
      PowerSeries.coeff n (S * mixed N k r s) := by
    intro k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih =>
      intro hk
      exact (ih (by omega)).trans (hstep k (by omega))
  have h := hind N le_rfl
  have he : mixed N N r s = ∏ i ∈ Finset.range N, block r i := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_range.mp hi, ite_true]
  rw [he] at h
  simpa only [mixed, Nat.not_lt_zero, ite_false] using h

theorem coeff_finite_42 (N n : ℕ) :
    PowerSeries.coeff n (S * ∏ i ∈ Finset.range N, block 2 i) ≤
      PowerSeries.coeff n (S * ∏ i ∈ Finset.range N, block 4 i) := by
  apply coeff_finite_comparison 4 2 2 3 2 (by omega) (by omega)
    (by omega) (by omega) (by omega) block_difference_42 ?_ N n
  intro k i hne b
  cases b <;> dsimp [pairWeight]
  all_goals split_ifs <;> omega

theorem coeff_finite_21 (N n : ℕ) :
    PowerSeries.coeff n (S * ∏ i ∈ Finset.range N, block 1 i) ≤
      PowerSeries.coeff n (S * ∏ i ∈ Finset.range N, block 2 i) := by
  apply coeff_finite_comparison 2 1 1 6 1 (by omega) (by omega)
    (by omega) (by omega) (by omega) (by simpa using block_difference_21) ?_ N n
  intro k i hne b
  cases b <;> dsimp [pairWeight]
  all_goals split_ifs <;> omega

/-- The two forbidden nonzero residue classes are removed from the genuine
unrestricted-by-nine partition product.  In the source, A=Q 4, B=Q 2, C=Q 1. -/
noncomputable def Q (r : ℕ) : PowerSeries ℚ :=
  restrictedSeries (fun m => m % 9 ≠ 0 ∧ m % 9 ≠ r ∧ m % 9 ≠ 9 - r)

private theorem prod_pairWeight (r : ℕ → ℕ) (I : Finset ℕ)
    (hr : ∀ i ∈ I, r i = 1 ∨ r i = 2 ∨ r i = 4) :
    (∏ a ∈ I.product (Finset.univ : Finset Bool),
      (1 - PowerSeries.X ^ pairWeight r a) : PowerSeries ℚ) =
      ∏ i ∈ I, block (r i) i := by
  rw [Finset.product_eq_sprod, Finset.prod_product]
  simp only [Fintype.prod_bool, pairWeight, ite_true, Bool.false_eq_true, ite_false]
  apply Finset.prod_congr rfl
  intro i hi
  have hh := hr i hi
  dsimp only [block]
  rw [show 9 * i + 9 - r i = 9 * i + (9 - r i) by omega]

/-- Exact stabilization, quantified over every degree, connects the finite
cancellation proof to the actual infinite counting series. -/
theorem coeff_Q_finite (r n N : ℕ) (hr : r = 1 ∨ r = 2 ∨ r = 4)
    (hN : n < 9 * N) :
    PowerSeries.coeff n (Q r) =
      PowerSeries.coeff n (S * ∏ i ∈ Finset.range N, block r i) := by
  classical
  let I := (Finset.range N).product (Finset.univ : Finset Bool)
  let w := pairWeight (fun _ => r)
  have hinj : Set.InjOn w I := pairWeight_injective (fun _ => r) (Finset.range N)
    (fun _ _ => hr)
  have hw : ∀ a ∈ I, 0 < w a ∧ w a % 9 ≠ 0 := by
    rintro ⟨i, b⟩ _
    cases b <;> dsimp [w, pairWeight]
    all_goals rcases hr with hr | hr | hr <;> simp [hr] <;> omega
  have he := restricted_mul_indexed_euler (fun m => m % 9 ≠ 0) I w hinj hw
  have hp : (∏ a ∈ I, (1 - PowerSeries.X ^ w a) : PowerSeries ℚ) =
      ∏ i ∈ Finset.range N, block r i :=
    prod_pairWeight (fun _ => r) (Finset.range N) (fun _ _ => hr)
  rw [hp] at he
  change S * _ = _ at he
  rw [he]
  apply coeff_restricted_congr
  intro m hm hmn
  have hmN : m < 9 * N := by omega
  have hmem : m ∈ I.image w ↔ m % 9 = r ∨ m % 9 = 9 - r := by
    constructor
    · intro h
      obtain ⟨⟨i, b⟩, _, hb⟩ := Finset.mem_image.mp h
      subst m
      cases b <;> dsimp [w, pairWeight]
      all_goals rcases hr with hr | hr | hr <;> simp [hr]
    · intro h
      have hi : m / 9 < N := by omega
      rcases h with h | h
      · apply Finset.mem_image.mpr
        refine ⟨(m / 9, true), ?_, ?_⟩
        · simp [I, hi]
        · dsimp [w, pairWeight]
          omega
      · apply Finset.mem_image.mpr
        refine ⟨(m / 9, false), ?_, ?_⟩
        · simp [I, hi]
        · dsimp [w, pairWeight]
          omega
  change (m % 9 ≠ 0 ∧ m % 9 ≠ r ∧ m % 9 ≠ 9 - r) ↔
    (m % 9 ≠ 0 ∧ m ∉ I.image w)
  rw [hmem]
  tauto

/-- All-index coefficientwise ordering A ≥ B ≥ C, for the actual allowed-part
products, not series with assumed signs. -/
theorem coefficient_order (n : ℕ) :
    PowerSeries.coeff n (Q 1) ≤ PowerSeries.coeff n (Q 2) ∧
      PowerSeries.coeff n (Q 2) ≤ PowerSeries.coeff n (Q 4) := by
  rw [coeff_Q_finite 1 n (n + 1) (by omega) (by omega),
    coeff_Q_finite 2 n (n + 1) (by omega) (by omega),
    coeff_Q_finite 4 n (n + 1) (by omega) (by omega)]
  exact ⟨coeff_finite_21 (n + 1) n, coeff_finite_42 (n + 1) n⟩

/-- The extra factors are coloured partition factors, not division of an
inequality by A.  Multiplicity two occurs at residues four and five. -/
noncomputable def D : PowerSeries ℚ :=
  restrictedSeries (fun m => m % 9 = 3 ∨ m % 9 = 6) *
    restrictedSeries (fun m => m % 9 = 4 ∨ m % 9 = 5) ^ 2

/-- Exact multiplicity comparison of the four actual reciprocal products. -/
theorem multiplicity_relation : Q 4 * D = Q 2 * Q 1 := by
  classical
  letI : TopologicalSpace ℚ := ⊥
  letI : DiscreteTopology ℚ := ⟨rfl⟩
  let f (p : ℕ → Prop) (i : ℕ) : PowerSeries ℚ :=
    if p (i + 1) then ∑' j : ℕ, PowerSeries.X ^ ((i + 1) * j) else 1
  have hprod (p : ℕ → Prop) : HasProd (f p) (restrictedSeries p) := by
    simpa only [f, restrictedSeries, Nat.Partition.restricted,
      Finset.filter_congr_decidable] using
      Nat.Partition.hasProd_powerSeriesMk_card_restricted ℚ p
  have hA := hprod (fun m => m % 9 ≠ 0 ∧ m % 9 ≠ 4 ∧ m % 9 ≠ 9 - 4)
  have hB := hprod (fun m => m % 9 ≠ 0 ∧ m % 9 ≠ 2 ∧ m % 9 ≠ 9 - 2)
  have hC := hprod (fun m => m % 9 ≠ 0 ∧ m % 9 ≠ 1 ∧ m % 9 ≠ 9 - 1)
  have h36 := hprod (fun m => m % 9 = 3 ∨ m % 9 = 6)
  have h45 := hprod (fun m => m % 9 = 4 ∨ m % 9 = 5)
  have hl := hA.mul (h36.mul (h45.pow 2))
  have hr := hB.mul hC
  change HasProd _ (Q 4 * D) at hl
  change HasProd _ (Q 2 * Q 1) at hr
  apply (hl.congr_fun ?_).unique hr
  intro i
  have hm : (i + 1) % 9 < 9 := Nat.mod_lt _ (by omega)
  have hh : (i + 1) % 9 = 0 ∨ (i + 1) % 9 = 1 ∨ (i + 1) % 9 = 2 ∨
      (i + 1) % 9 = 3 ∨ (i + 1) % 9 = 4 ∨ (i + 1) % 9 = 5 ∨
      (i + 1) % 9 = 6 ∨ (i + 1) % 9 = 7 ∨ (i + 1) % 9 = 8 := by omega
  rcases hh with hh | hh | hh | hh | hh | hh | hh | hh | hh
  all_goals norm_num [f, hh] <;> ring

/-- The difference AC-CD is positive coefficientwise by the paid identity
AD=BC and the proved comparisons, without sign inference under division. -/
theorem coeff_delta_nonnegative (n : ℕ) :
    0 ≤ PowerSeries.coeff n (Q 4 * Q 1 - Q 1 * D) := by
  have he : Q 4 * Q 1 - Q 1 * D =
      Q 1 * (Q 4 - Q 2) + D * (Q 4 - Q 1) := by
    linear_combination -multiplicity_relation
  rw [he, map_add]
  apply add_nonneg
  · apply coeff_mul_nonnegative (coeff_restricted_nonnegative _) _ n
    intro k
    rw [map_sub, sub_nonneg]
    exact (coefficient_order k).2
  · apply coeff_mul_nonnegative _ _ n
    · exact coeff_mul_nonnegative (coeff_restricted_nonnegative _)
        (coeff_pow_nonnegative (coeff_restricted_nonnegative _) 2)
    · intro k
      rw [map_sub, sub_nonneg]
      exact (coefficient_order k).1.trans (coefficient_order k).2

/-- Removing the sole unrestricted part one from AC leaves a genuine
nonnegative product with unrestricted parts two and three. -/
noncomputable def lowerProduct : PowerSeries ℚ :=
  (1 - PowerSeries.X) * (Q 4 * Q 1)

private theorem lowerProduct_eq : lowerProduct =
    Q 1 * restrictedSeries (fun m =>
      (m % 9 ≠ 0 ∧ m % 9 ≠ 4 ∧ m % 9 ≠ 9 - 4) ∧ m ≠ 1) := by
  have h := restricted_mul_one_sub
    (fun m => m % 9 ≠ 0 ∧ m % 9 ≠ 4 ∧ m % 9 ≠ 9 - 4) 1
    (by omega) (by norm_num)
  change Q 4 * (1 - PowerSeries.X ^ 1) = _ at h
  rw [pow_one] at h
  rw [← h]
  dsimp only [lowerProduct]
  ring

/-- This is the exact nonnegative lower product in the W decomposition. -/
theorem coeff_lowerProduct_nonnegative (n : ℕ) :
    0 ≤ PowerSeries.coeff n lowerProduct := by
  rw [lowerProduct_eq]
  exact coeff_mul_nonnegative (coeff_restricted_nonnegative _)
    (coeff_restricted_nonnegative _) n

theorem coeff_lowerProduct_ge_one (n : ℕ) (hn : n = 0 ∨ 2 ≤ n) :
    1 ≤ PowerSeries.coeff n lowerProduct := by
  rw [lowerProduct_eq]
  exact (coeff_restricted_ge_one_of_two_three _ (by norm_num) (by norm_num) n hn).trans
    (coeff_mul_ge_right (coeff_restricted_nonnegative _)
      (coeff_restricted_nonnegative _) (restricted_constant_one _) n)

/-- The lower product has precisely the auxiliary degree-one hole. -/
theorem lowerProduct_initial :
    PowerSeries.constantCoeff lowerProduct = 1 ∧
      PowerSeries.coeff 1 lowerProduct = 0 := by
  have hzero (p : ℕ → Prop) (hp : ¬ p 1) :
      PowerSeries.coeff 1 (restrictedSeries p) = 0 := by
    classical
    have he : Nat.Partition.restricted 1 p = ∅ := by
      ext a
      simp [Nat.Partition.restricted, hp]
    simp only [restrictedSeries, PowerSeries.coeff_mk]
    rw [he]
    norm_num
  rw [lowerProduct_eq]
  constructor
  · rw [map_mul, restricted_constant_one, show PowerSeries.constantCoeff (Q 1) = 1 from
      restricted_constant_one _, one_mul]
  · rw [PowerSeries.coeff_one_mul, hzero _ (by norm_num),
      show PowerSeries.coeff 1 (Q 1) = 0 from hzero _ (by norm_num), zero_mul,
      zero_mul, zero_add]

end D5.S3.Combinatorics.Partitions.EulerNineComparison
