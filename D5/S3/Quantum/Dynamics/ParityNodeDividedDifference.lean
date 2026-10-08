/- GID: D5/S3/Quantum/Dynamics/ParityNodeDividedDifference
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/ParityNodeDividedDifference
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Divided differences over even and odd integer nodes with an odd binomial are 2-adic units. -/

/-
proof_shape: evenOdd_dividedDifference_twoAdicUnit: content; escape_witness: the public
conclusion itself (form 2): the partial divided difference over the even nodes is a 2-adic
unit, produced by a truncated 2-adic geometric expansion of the odd-node factors, integrality
of divided differences of monomials, and a mod-2 coefficient computation; no Mathlib or frozen
declaration states it.
Private helpers:
proof_shape: coeff_geomSum_pow: bind-only; consumer: evenOdd_dividedDifference_twoAdicUnit.
proof_shape: exists_prod_one_sub_mul: content (finite induction); consumer:
evenOdd_dividedDifference_twoAdicUnit.
proof_shape: sum_pow_div_nodal_eq_coeff: content (Lagrange.coeff_eq_sum applied to a remainder
modulo the integer nodal polynomial); consumer: evenOdd_dividedDifference_twoAdicUnit.
proof_shape: norm_odd_int: bind-only; consumer: evenOdd_dividedDifference_twoAdicUnit.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only).
utility: none; no declaration is a bounded enumeration, checker, numeric reduction or certified
instance: every statement quantifies over arbitrary finite node families.
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.WellKnown

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.ParityNodeDividedDifference

open Polynomial Finset

/-- Below the truncation order, the `(d + 1)`-st power of `1 + X + ⋯ + X ^ (N - 1)` has the
binomial coefficients `C(d + n, d)`. -/
private theorem coeff_geomSum_pow {R : Type*} [CommRing R] (N d n : ℕ) (hn : n < N) :
    ((∑ i ∈ range N, (X : R[X]) ^ i) ^ (d + 1)).coeff n = ((d + n).choose d : R) := by
  have htr : (∑ i ∈ range N, (X : R[X]) ^ i) = PowerSeries.trunc N (PowerSeries.mk 1) := by
    ext m
    rw [PowerSeries.coeff_trunc, finsetSum_coeff]
    simp [coeff_X_pow, Finset.mem_range]
  have key := congrArg (fun p : R[X] => p.coeff n)
    (PowerSeries.trunc_trunc_pow (PowerSeries.mk (1 : ℕ → R)) N (d + 1))
  simp only [PowerSeries.coeff_trunc, if_pos hn] at key
  rw [htr, ← Polynomial.coeff_coe, Polynomial.coe_pow, key,
    PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_mk]

/-- A product of factors `1 - t * f j` is again of the form `1 - t * c`. -/
private theorem exists_prod_one_sub_mul {ι R : Type*} [CommRing R] (t : R) (s : Finset ι)
    (f : ι → R) : ∃ c : R, ∏ j ∈ s, (1 - t * f j) = 1 - t * c := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨f a + c - t * f a * c, by rw [prod_insert ha, hc]; ring⟩

/-- The divided difference of `x ^ i` over integer nodes is the coefficient of degree
`#A - 1` of the remainder of `X ^ i` modulo the monic nodal polynomial; in particular it is an
integer. -/
private theorem sum_pow_div_nodal_eq_coeff {ι K : Type*} [DecidableEq ι] [Field K] [CharZero K]
    (μ : ι → ℤ) (A : Finset ι) (hμ : Set.InjOn μ A) (i : ℕ) :
    ∑ k ∈ A, ((μ k : K) ^ i / ∏ l ∈ A.erase k, ((μ k : K) - μ l)) =
      ((((X : ℤ[X]) ^ i %ₘ ∏ l ∈ A, (X - C (μ l))).coeff (A.card - 1) : ℤ) : K) := by
  set Ω : ℤ[X] := ∏ l ∈ A, (X - C (μ l)) with hΩdef
  have hΩ : Ω.Monic := monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _
  have hinj : Set.InjOn (fun k => (μ k : K)) A := fun a ha b hb h =>
    hμ ha hb (Int.cast_injective h)
  have hdeg : (((X : ℤ[X]) ^ i %ₘ Ω).map (Int.castRingHom K)).degree < A.card := by
    calc _ ≤ ((X : ℤ[X]) ^ i %ₘ Ω).degree := degree_map_le
      _ < Ω.degree := degree_modByMonic_lt _ hΩ
      _ = A.card := by
        rw [degree_eq_natDegree hΩ.ne_zero,
          natDegree_prod_of_monic _ _ fun l _ => monic_X_sub_C _,
          Finset.sum_congr rfl fun l _ => natDegree_X_sub_C (μ l)]
        simp
  have h := Lagrange.coeff_eq_sum hinj hdeg
  rw [coeff_map, eq_intCast] at h
  rw [h]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hev : eval (μ k) Ω = 0 := by
    rw [hΩdef, eval_prod]
    exact Finset.prod_eq_zero hk (by simp)
  have hrem := congrArg (eval (μ k)) (modByMonic_add_div ((X : ℤ[X]) ^ i) Ω)
  rw [eval_add, eval_mul, hev, zero_mul, add_zero, eval_pow, eval_X] at hrem
  have hcast := eval_intCast_map (Int.castRingHom K) ((X : ℤ[X]) ^ i %ₘ Ω) (μ k)
  simp only [Int.cast_id, eq_intCast] at hcast
  simp only [hcast, hrem, Int.cast_pow]

/-- Odd integers have norm one in `ℤ_[2]`. -/
private theorem norm_odd_int (n : ℤ) (hn : Odd n) : ‖(n : ℤ_[2])‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)
  rw [PadicInt.norm_int_lt_one_iff_dvd] at h
  exact (Int.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr (by exact_mod_cast h))

/-- **Even/odd node divided differences are 2-adic units.** Let `z` be injective integer nodes,
even on `A` and odd off `A`, with `C(#ι - 2, #A - 1)` odd. Then
`Σ_{i ∈ A} 1 / ∏_{j ≠ i} (z i - z j)` is a nonzero rational of `2`-adic valuation `0`. -/
theorem evenOdd_dividedDifference_twoAdicUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → ℤ) (hz : Function.Injective z) (A : Finset ι) (hA : A.Nonempty)
    (heven : ∀ i ∈ A, Even (z i)) (hodd : ∀ i, i ∉ A → Odd (z i))
    (hchoose : Odd ((Fintype.card ι - 2).choose (A.card - 1))) :
    (∑ i ∈ A, (∏ j ∈ univ.erase i, ((z i - z j : ℤ) : ℚ))⁻¹) ≠ 0 ∧
      padicValRat 2 (∑ i ∈ A, (∏ j ∈ univ.erase i, ((z i - z j : ℤ) : ℚ))⁻¹) = 0 := by
  set T : ℚ := ∑ i ∈ A, (∏ j ∈ univ.erase i, ((z i - z j : ℤ) : ℚ))⁻¹ with hTdef
  suffices hnorm : ‖(T : ℚ_[2])‖ = 1 by
    rw [Padic.eq_padicNorm] at hnorm
    have h1 : padicNorm 2 T = 1 := by exact_mod_cast hnorm
    have hT : T ≠ 0 := by
      rintro h0
      rw [h0, padicNorm.zero] at h1
      exact zero_ne_one h1
    refine ⟨hT, ?_⟩
    rw [padicNorm.eq_zpow_of_nonzero hT] at h1
    have h2 := (zpow_eq_one_iff_right₀ (by norm_num : (0 : ℚ) ≤ ((2 : ℕ) : ℚ))
      (by norm_num)).mp h1
    omega
  set α := A.card with hαdef
  have hα : 1 ≤ α := Finset.card_pos.mpr hA
  have hcard : α + (Aᶜ).card = Fintype.card ι := Finset.card_add_card_compl A
  let μ : ι → ℤ := fun i => z i / 2
  have hzμ : ∀ i ∈ A, z i = 2 * μ i := fun i hi =>
    (Int.two_mul_ediv_two_of_even (heven i hi)).symm
  have hμinj : Set.InjOn μ A := fun i hi j hj h => hz (by rw [hzμ i hi, hzμ j hj, h])
  let Pk : ι → ℤ := fun i => ∏ l ∈ A.erase i, (μ i - μ l)
  let Y : ι → ℤ := fun i => ∏ l ∈ Aᶜ, (z i - z l)
  have hPk : ∀ i ∈ A, Pk i ≠ 0 := by
    intro i hi
    refine Finset.prod_ne_zero_iff.mpr fun l hl => sub_ne_zero.mpr fun h => ?_
    obtain ⟨hne, hlA⟩ := Finset.mem_erase.mp hl
    exact hne (hμinj hlA hi h.symm)
  have hY : ∀ i ∈ A, Odd (Y i) := by
    intro i hi
    refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun l hl => ?_
    exact (heven i hi).sub_odd (hodd l (Finset.mem_compl.mp hl))
  have hfac : ∀ i ∈ A, ∏ j ∈ univ.erase i, ((z i - z j : ℤ) : ℚ) =
      (2 : ℚ) ^ (α - 1) * (Pk i : ℚ) * (Y i : ℚ) := by
    intro i hi
    have hsplit : univ.erase i = A.erase i ∪ Aᶜ := by
      ext l
      by_cases h : l = i
      · subst h; simp [hi]
      · simp [h, em]
    have hdisj : Disjoint (A.erase i) Aᶜ := Finset.disjoint_left.mpr fun l h1 h2 =>
      (Finset.mem_compl.mp h2) (Finset.mem_of_mem_erase h1)
    rw [hsplit, Finset.prod_union hdisj,
      Finset.prod_congr rfl fun l hl => show ((z i - z l : ℤ) : ℚ) = 2 * ((μ i - μ l : ℤ) : ℚ)
        by rw [hzμ i hi, hzμ l (Finset.mem_of_mem_erase hl)]; push_cast; ring,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem hi]
    simp only [Pk, Y]
    push_cast
    ring
  -- the truncation order
  have hPnorm : ∀ i ∈ A, 0 < ‖((Pk i : ℤ) : ℚ_[2])‖ := fun i hi =>
    norm_pos_iff.mpr (by exact_mod_cast hPk i hi)
  obtain ⟨N', hN'⟩ : ∃ N' : ℕ, ((1 : ℝ) / 2) ^ N' < ∏ i ∈ A, ‖((Pk i : ℤ) : ℚ_[2])‖ :=
    exists_pow_lt_of_lt_one (Finset.prod_pos hPnorm) (by norm_num)
  have hle : ∀ i ∈ A, ((1 : ℝ) / 2) ^ N' ≤ ‖((Pk i : ℤ) : ℚ_[2])‖ := by
    intro i hi
    refine hN'.le.trans ?_
    rw [← Finset.mul_prod_erase A _ hi]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => Padic.norm_int_le_one _)
  have h2norm : ‖(2 : ℚ_[2])‖ = 1 / 2 := by
    have h := Padic.norm_p (p := 2)
    norm_num at h ⊢
    exact h
  have hδ : ∀ i, ∃ d : ℤ_[2], i ∈ A → (d : ℚ_[2]) = (2 : ℚ_[2]) ^ N' / (Pk i : ℚ_[2]) := by
    intro i
    by_cases hi : i ∈ A
    · refine ⟨⟨(2 : ℚ_[2]) ^ N' / (Pk i : ℚ_[2]), ?_⟩, fun _ => rfl⟩
      rw [norm_div, norm_pow, h2norm]
      exact div_le_one_of_le₀ (hle i hi) (norm_nonneg _)
    · exact ⟨0, fun h => absurd h hi⟩
  choose δ hδ using hδ
  -- inverses of the odd factors
  let u : ι → ℤ_[2] := fun j => Ring.inverse (z j : ℤ_[2])
  have hu : ∀ j, j ∉ A → (z j : ℤ_[2]) * u j = 1 := fun j hj =>
    Ring.mul_inverse_cancel _ (PadicInt.isUnit_iff.mpr (norm_odd_int _ (hodd j hj)))
  let v : ι → ℤ_[2] := fun i => Ring.inverse (Y i : ℤ_[2])
  have hv : ∀ i ∈ A, (Y i : ℤ_[2]) * v i = 1 := fun i hi =>
    Ring.mul_inverse_cancel _ (PadicInt.isUnit_iff.mpr (norm_odd_int _ (hY i hi)))
  -- the truncated expansion of `1 / ∏_{j ∉ A} (x - z j)`
  set N := α + N' with hN
  set Q : ℤ_[2][X] := ∏ j ∈ Aᶜ, (-C (u j) * ∑ t ∈ range N, (C (u j) * X) ^ t) with hQ
  have happrox : ∀ k, ∃ c : ℤ_[2], k ∈ A →
      (Y k : ℤ_[2]) * Q.eval (z k : ℤ_[2]) = 1 - 2 ^ N * c := by
    intro k
    by_cases hk : k ∈ A
    · have hprod : (Y k : ℤ_[2]) * Q.eval (z k : ℤ_[2]) =
          ∏ j ∈ Aᶜ, (1 - 2 ^ N * (u j * μ k) ^ N) := by
        simp only [hQ, eval_prod, Y]
        push_cast
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j hj => ?_
        simp only [eval_mul, eval_neg, eval_C, eval_finsetSum, eval_pow, eval_X]
        have h1 : ((z k : ℤ_[2]) - z j) * -u j = 1 - u j * z k := by
          linear_combination hu j (Finset.mem_compl.mp hj)
        rw [← mul_assoc, h1, mul_neg_geom_sum, hzμ k hk]
        push_cast
        ring
      obtain ⟨c, hc⟩ := exists_prod_one_sub_mul (2 ^ N : ℤ_[2]) Aᶜ fun j => (u j * μ k) ^ N
      exact ⟨c, fun _ => hprod.trans hc⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose c hc using happrox
  -- integral moments of the nodes `μ`
  set Ω : ℤ[X] := ∏ l ∈ A, (X - C (μ l)) with hΩ
  let m : ℕ → ℤ := fun i => ((X : ℤ[X]) ^ i %ₘ Ω).coeff (α - 1)
  have hm : ∀ i, ∑ k ∈ A, ((μ k : ℚ_[2]) ^ i / ∏ l ∈ A.erase k, ((μ k : ℚ_[2]) - μ l)) =
      (m i : ℚ_[2]) := fun i => sum_pow_div_nodal_eq_coeff μ A hμinj i
  have hmlow : ∀ i < α, m i = if i = α - 1 then 1 else 0 := by
    intro i hi
    have hΩm : Ω.Monic := monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _
    have hdeg : ((X : ℤ[X]) ^ i).degree < Ω.degree := by
      rw [degree_X_pow, degree_eq_natDegree hΩm.ne_zero,
        natDegree_prod_of_monic _ _ fun l _ => monic_X_sub_C _,
        Finset.sum_congr rfl fun l _ => natDegree_X_sub_C (μ l)]
      simp only [Finset.sum_const, smul_eq_mul, mul_one]
      exact_mod_cast hi
    simp only [m, (modByMonic_eq_self_iff hΩm).mpr hdeg, coeff_X_pow]
    by_cases h : i = α - 1
    · simp [h]
    · simp [h, Ne.symm h]
  -- the coefficient of degree `α - 1` is odd
  set q := Q.coeff (α - 1) with hq
  have hqmod : PadicInt.toZMod q = 1 := by
    have hu1 : ∀ j, j ∉ A → PadicInt.toZMod (u j) = 1 := by
      intro j hj
      have h := congrArg PadicInt.toZMod (hu j hj)
      rw [map_mul, map_one, map_intCast, (ZMod.intCast_eq_one_iff_odd).mpr (hodd j hj),
        one_mul] at h
      exact h
    have hmap : Q.map PadicInt.toZMod = (∑ t ∈ range N, (X : (ZMod 2)[X]) ^ t) ^ (Aᶜ).card := by
      rw [hQ, Polynomial.map_prod, ← Finset.prod_const]
      refine Finset.prod_congr rfl fun j hj => ?_
      simp only [Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_C, Polynomial.map_sum,
        Polynomial.map_pow, Polynomial.map_X, hu1 j (Finset.mem_compl.mp hj), map_one, one_mul,
        CharTwo.neg_eq]
    rw [hq, ← Polynomial.coeff_map, hmap]
    rcases Nat.eq_zero_or_pos (Aᶜ).card with hβ | hβ
    · rw [hβ, pow_zero, coeff_one]
      have hα1 : α = 1 := by
        by_contra hne
        rw [← hcard, hβ, add_zero, Nat.choose_eq_zero_of_lt (by omega)] at hchoose
        exact Nat.not_odd_zero hchoose
      simp [hα1]
    · obtain ⟨d, hd⟩ : ∃ d, (Aᶜ).card = d + 1 := ⟨(Aᶜ).card - 1, by omega⟩
      rw [hd, coeff_geomSum_pow N d (α - 1) (by omega), ZMod.natCast_eq_one_iff_odd,
        Nat.choose_symm_add]
      have h' : Fintype.card ι - 2 = d + (α - 1) := by omega
      rw [h'] at hchoose
      exact hchoose
  have hqnorm : ∀ s : ℤ_[2], ‖q + 2 * s‖ = 1 := by
    intro s
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)
    obtain ⟨r, hr⟩ := (PadicInt.norm_lt_one_iff_dvd _).mp h
    have h' := congrArg PadicInt.toZMod hr
    simp only [map_add, map_mul, hqmod, map_natCast, map_ofNat] at h'
    revert h'
    generalize PadicInt.toZMod s = a
    generalize PadicInt.toZMod r = b
    decide +revert
  have hcoe2 : ((2 : ℤ_[2]) : ℚ_[2]) = 2 := by simpa using PadicInt.coe_natCast (p := 2) 2
  -- the polynomial part of the divided difference
  set D := Q.natDegree + α with hD
  have hevalsum : ∀ x : ℤ_[2], Q.eval x = ∑ i ∈ range D, Q.coeff i * x ^ i :=
    fun x => eval_eq_sum_range' (by omega) x
  set w : ℤ_[2] := ∑ i ∈ range D,
    (if α ≤ i then 2 ^ (i - α) * Q.coeff i * (m i : ℤ_[2]) else 0) with hw
  have hpoly : ∑ i ∈ range D, Q.coeff i * 2 ^ i * (m i : ℤ_[2]) =
      2 ^ (α - 1) * (q + 2 * w) := by
    have hterm : ∀ i ∈ range D, Q.coeff i * 2 ^ i * (m i : ℤ_[2]) =
        (if i = α - 1 then 2 ^ (α - 1) * q else 0) +
          2 ^ α * (if α ≤ i then 2 ^ (i - α) * Q.coeff i * (m i : ℤ_[2]) else 0) := by
      intro i _
      by_cases h1 : i < α
      · rw [hmlow i h1, if_neg (by omega : ¬ α ≤ i)]
        by_cases h2 : i = α - 1
        · rw [if_pos h2, if_pos h2, h2, ← hq]
          push_cast
          ring
        · rw [if_neg h2, if_neg h2]
          push_cast
          ring
      · rw [if_neg (by omega : i ≠ α - 1), if_pos (by omega : α ≤ i),
          show (2 : ℤ_[2]) ^ i = 2 ^ α * 2 ^ (i - α) by rw [← pow_add]; congr 1; omega]
        ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_range.mpr (by omega)), ← Finset.mul_sum, ← hw,
      show (2 : ℤ_[2]) ^ α = 2 ^ (α - 1) * 2 by rw [← pow_succ]; congr 1; omega]
    ring
  have hE : ∑ k ∈ A, ((Q.eval (z k : ℤ_[2]) : ℤ_[2]) : ℚ_[2]) / ((Pk k : ℤ) : ℚ_[2]) =
      (2 : ℚ_[2]) ^ (α - 1) * ((q + 2 * w : ℤ_[2]) : ℚ_[2]) := by
    have hk' : ∀ k ∈ A, ((Q.eval (z k : ℤ_[2]) : ℤ_[2]) : ℚ_[2]) / ((Pk k : ℤ) : ℚ_[2]) =
        ∑ i ∈ range D, (Q.coeff i : ℚ_[2]) * 2 ^ i *
          ((μ k : ℚ_[2]) ^ i / ∏ l ∈ A.erase k, ((μ k : ℚ_[2]) - μ l)) := by
      intro k hk
      rw [hevalsum, PadicInt.coe_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pk]
      rw [hzμ k hk]
      push_cast
      simp only [hcoe2]
      ring
    rw [Finset.sum_congr rfl hk', Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hm]
    have h := congrArg (fun x : ℤ_[2] => (x : ℚ_[2])) hpoly
    simp only [PadicInt.coe_sum, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_intCast,
      PadicInt.coe_add, hcoe2] at h ⊢
    exact h
  set t : ℤ_[2] := w + ∑ k ∈ A, δ k * c k * v k with ht
  have hTsum : (T : ℚ_[2]) =
      ∑ k ∈ A, ((2 : ℚ_[2]) ^ (α - 1) * ((Pk k : ℤ) : ℚ_[2]) * ((Y k : ℤ) : ℚ_[2]))⁻¹ := by
    rw [hTdef, Rat.cast_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Rat.cast_inv, hfac i hi]
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_intCast]
  have hterm : ∀ k ∈ A,
      ((2 : ℚ_[2]) ^ (α - 1) * ((Pk k : ℤ) : ℚ_[2]) * ((Y k : ℤ) : ℚ_[2]))⁻¹ =
        ((2 : ℚ_[2]) ^ (α - 1))⁻¹ *
            (((Q.eval (z k : ℤ_[2]) : ℤ_[2]) : ℚ_[2]) / ((Pk k : ℤ) : ℚ_[2])) +
          2 * ((δ k * c k * v k : ℤ_[2]) : ℚ_[2]) := by
    intro k hk
    have hPk' : ((Pk k : ℤ) : ℚ_[2]) ≠ 0 := by exact_mod_cast hPk k hk
    have hc' : ((Y k : ℤ) : ℚ_[2]) * ((Q.eval (z k : ℤ_[2]) : ℤ_[2]) : ℚ_[2]) =
        1 - 2 ^ N * (c k : ℚ_[2]) := by
      have h := congrArg (fun x : ℤ_[2] => (x : ℚ_[2])) (hc k hk)
      simpa [hcoe2] using h
    have hv' : ((Y k : ℤ) : ℚ_[2]) * (v k : ℚ_[2]) = 1 := by
      have h := congrArg (fun x : ℤ_[2] => (x : ℚ_[2])) (hv k hk)
      simpa using h
    have hYinv : ((Y k : ℤ) : ℚ_[2])⁻¹ = (v k : ℚ_[2]) := inv_eq_of_mul_eq_one_right hv'
    have he : ((Q.eval (z k : ℤ_[2]) : ℤ_[2]) : ℚ_[2]) =
        (1 - 2 ^ N * (c k : ℚ_[2])) * (v k : ℚ_[2]) := by
      rw [← hc']
      linear_combination -(((Q.eval (z k : ℤ_[2]) : ℤ_[2]) : ℚ_[2])) * hv'
    rw [PadicInt.coe_mul, PadicInt.coe_mul, hδ k hk, mul_inv, mul_inv, hYinv, he,
      show (2 : ℚ_[2]) ^ N = 2 ^ (α - 1) * 2 * 2 ^ N' by
        rw [← pow_succ, ← pow_add]; congr 1; omega]
    field_simp
    ring
  have hT2 : (T : ℚ_[2]) = ((q + 2 * t : ℤ_[2]) : ℚ_[2]) := by
    rw [hTsum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hE, ht]
    simp only [PadicInt.coe_sum, PadicInt.coe_mul, PadicInt.coe_add, hcoe2]
    field_simp
    ring
  rw [hT2, ← PadicInt.norm_def]
  exact hqnorm t

end D5.S3.Quantum.Dynamics.ParityNodeDividedDifference
