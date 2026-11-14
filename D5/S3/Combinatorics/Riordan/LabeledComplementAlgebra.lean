/- GID: D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Riordan/LabeledComplementAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite binary Riordan complement algebra. -/

/-
admission_basis: escape-witness
escape_witness: image_square_annihilator
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27284
monicModulus: proof_shape: bind-only; consumers: coefficientEquiv, truncatedCoeff, canonicalSeries.
modulusDegree: proof_shape: bind-only; consumers: coefficientEquiv, coefficientEquiv_apply.
The labels i : Fin n represent the source labels i.val + 1.
The parity expressions use the disclosed products 10 * 8^(k-1) and 3 * 8^k.
Coefficients lie in ZMod 2; truncations use AdjoinRoot of a power of Polynomial.X.
three_column_extension: proof_shape: bind-only; consumers: columns_of_annihilator.
columns_of_annihilator: proof_shape: bind-only; consumers: columns_iff_annihilator, unit_parameter_criterion.
square_discrepancy: proof_shape: bind-only; consumers: columns_iff_annihilator.
columns_iff_annihilator: proof_shape: bind-only; consumers: unit_parameter_criterion.
all_graphs_one: proof_shape: bind-only; consumers: count_one.
count_one: proof_shape: bind-only; consumers: claim_of_sum, count_sum.
prefix_succ: proof_shape: bind-only; consumers: prefix_two_step, difference_of_sum.
weight_two_step: proof_shape: bind-only; consumers: prefix_two_step.
prefix_two_step: proof_shape: bind-only; consumers: prefix_even, prefix_odd, recurrence_of_sum.
prefix_even: proof_shape: bind-only; consumers: odd_of_sum.
prefix_odd: proof_shape: bind-only; consumers: even_of_sum.
truncatedCoeff_truncateMap: proof_shape: bind-only; consumers: truncateMap_eq_iff, truncateMap_canonicalSeries, unitParametersToGraph_surjective, canonical_constant_truncateMap.
truncateMap_eq_iff: proof_shape: bind-only; consumers: truncateMap_eq_zero_iff, truncateMap_canonicalSeries, image_square_annihilator, graph_eq_iff_columns, column_equation_coeff, unitParametersToGraph_injective.
truncateMap_eq_zero_iff: proof_shape: bind-only; consumers: image_square_annihilator, graph_complement_factor_criterion.
complement_orientation_card: proof_shape: bind-only; consumers: count_all.
unit_parameter_criterion: proof_shape: bind-only; consumers: graph_complement_criterion.
truncateMap_surjective: proof_shape: bind-only; consumers: truncateMap_canonicalSeries.
truncateMap_isUnit: proof_shape: bind-only; consumers: unitParametersToGraph_injective, graph_complement_criterion.
allOnes_constant: proof_shape: bind-only; consumers: graph_complement_criterion, class_complement, classToUnitParams, classToUnitParams_surjective.
square_divisibility: proof_shape: bind-only; consumers: shifted_square_divisibility.
shifted_square_divisibility: proof_shape: bind-only; consumers: image_square_annihilator, graph_complement_factor_criterion.
zero_prefix_card: proof_shape: bind-only; consumers: classified_card.
truncateMap_canonicalSeries: proof_shape: bind-only; consumers: unitParametersToGraph_injective, unitParametersToGraph_surjective, canonicalGraph_eq, classToUnitParams_injective, classToUnitParams_surjective.
coefficientEquiv_apply: proof_shape: bind-only; consumers: seriesOfVector_coeff, classToUnitParams_surjective.
image_square_annihilator: proof_shape: content; consumers: graph_complement_factor_criterion.
recurrence_of_sum: proof_shape: bind-only; consumers: claim_of_sum.
difference_of_sum: proof_shape: bind-only; consumers: claim_of_sum.
a113836_eq_prefix: proof_shape: bind-only; consumers: claim_of_sum.
even_of_sum: proof_shape: bind-only; consumers: claim_of_sum.
odd_of_sum: proof_shape: bind-only; consumers: claim_of_sum.
ogf_of_recurrence: proof_shape: bind-only; consumers: claim_of_sum.
claim_of_sum: proof_shape: bind-only; consumers: result.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.LinearRecurrence
import Mathlib.RingTheory.PowerSeries.Expand

set_option linter.unusedTactic false
set_option maxHeartbeats 1000000

namespace D5.S3.Combinatorics.Riordan.LabeledComplementAlgebra

open scoped BigOperators

noncomputable def riordanGraph (n : ℕ) (g f : (PowerSeries (ZMod 2))) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j =>
    j.val < i.val ∧ PowerSeries.coeff (i.val - 1) (g * f ^ j.val) = 1

def IsLabeledRiordan {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ g f : (PowerSeries (ZMod 2)), PowerSeries.constantCoeff f = 0 ∧ G = riordanGraph n g f

def ComplementCompatible (n : ℕ) :=
  {G : SimpleGraph (Fin n) // IsLabeledRiordan G ∧ IsLabeledRiordan Gᶜ}

noncomputable def a (n : ℕ) : ℕ := Nat.card (ComplementCompatible n)

def a001651 (i : ℕ) : ℕ := i + i / 2 + 1

def a113836 (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, 2 ^ (a001651 i - 1)

noncomputable def ogf : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

noncomputable def conjecturedOGF : PowerSeries ℚ :=
  let X : PowerSeries ℚ := PowerSeries.X
  X * (1 - 2 * X) * (1 + 3 * X) *
    PowerSeries.invOfUnit ((1 - X) * (1 - 8 * X ^ 2)) 1

def claim : Prop :=
  a 1 = 1 ∧ a 2 = 2 ∧
  (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 8 * (a (n - 2) : ℤ) - 4) ∧
  (∀ n : ℕ, 1 ≤ n →
    (a (n + 1) : ℤ) - (a n : ℤ) = (2 : ℤ) ^ (3 * (n - 1) / 2)) ∧
  (∀ n : ℕ, 1 ≤ n →
    a n = 1 + ∑ k ∈ Finset.range (n - 1), 2 ^ (3 * k / 2)) ∧
  (∀ n : ℕ, 2 ≤ n → a n = a113836 (n - 1) + 1) ∧
  (∀ k : ℕ, 1 ≤ k →
    (a (2 * k) : ℚ) = (10 * (8 : ℚ) ^ (k - 1) + 4) / 7) ∧
  (∀ k : ℕ, (a (2 * k + 1) : ℚ) = (3 * (8 : ℚ) ^ k + 4) / 7) ∧
  ogf = conjecturedOGF

private theorem three_column_extension {R : Type*} [CommRing R] (g r h f u t : R)
    (h0 : g + r = h)
    (h1 : g * f + r * u = h * t)
    (h2 : g * f ^ 2 + r * u ^ 2 = h * t ^ 2) :
    ∀ j : ℕ, g * f ^ j + r * u ^ j = h * t ^ j := by
  let E : LinearRecurrence R :=
    ⟨3, ![f * u * t, -(f * u + f * t + u * t), f + u + t]⟩
  let s : ℕ → R := fun j => g * f ^ j + r * u ^ j - h * t ^ j
  have hs : E.IsSolution s := by
    intro n
    simp [E, s, Fin.sum_univ_succ, pow_add]
    ring
  have hz : E.IsSolution (fun _ => 0) := E.solSpace.zero_mem
  have heq : s = fun _ => 0 := (E.eq_iff_eqOn_range_order s _ hs hz).mpr (by
    intro n hn
    have hn3 : n < 3 := Finset.mem_range.mp hn
    interval_cases n <;> simp_all [s])
  intro j
  exact sub_eq_zero.mp (congrFun heq j)

private theorem columns_of_annihilator {R : Type*} [CommRing R] [CharP R 2]
    (g r h t alpha delta : R) (h0 : g + r = h) (ha : g * alpha = r)
    (hnil : r * delta ^ 2 = 0) :
    ∀ j : ℕ, g * (t + alpha * delta) ^ j + r * (t + delta) ^ j = h * t ^ j := by
  apply three_column_extension g r h (t + alpha * delta) (t + delta) t h0
  · calc
      g * (t + alpha * delta) + r * (t + delta) =
          (g + r) * t + (g * alpha + r) * delta := by ring
      _ = h * t := by rw [h0, ha, CharTwo.add_self_eq_zero, zero_mul, add_zero]
  · rw [CharTwo.add_sq, CharTwo.add_sq, mul_pow]
    calc
      g * (t ^ 2 + alpha ^ 2 * delta ^ 2) + r * (t ^ 2 + delta ^ 2) =
          (g + r) * t ^ 2 + alpha * (r * delta ^ 2) + r * delta ^ 2 := by
        rw [← ha]
        ring
      _ = h * t ^ 2 := by rw [h0, hnil]; ring

private theorem square_discrepancy {R : Type*} [CommRing R] [CharP R 2]
    (g r h t alpha delta : R) (h0 : g + r = h) (ha : g * alpha = r) :
    g * (t + alpha * delta) ^ 2 + r * (t + delta) ^ 2 + h * t ^ 2 =
      (1 + alpha) * (r * delta ^ 2) := by
  rw [CharTwo.add_sq, CharTwo.add_sq, mul_pow]
  calc
    g * (t ^ 2 + alpha ^ 2 * delta ^ 2) + r * (t ^ 2 + delta ^ 2) + h * t ^ 2 =
        (g + r + h) * t ^ 2 + (g * alpha ^ 2 + r) * delta ^ 2 := by ring
    _ = (g * alpha ^ 2 + r) * delta ^ 2 := by
      rw [h0, CharTwo.add_self_eq_zero, zero_mul, zero_add]
    _ = (1 + alpha) * (r * delta ^ 2) := by rw [← ha]; ring

private theorem columns_iff_annihilator {R : Type*} [CommRing R] [CharP R 2]
    (g r h t alpha delta : R) (h0 : g + r = h) (ha : g * alpha = r)
    (hunit : IsUnit (1 + alpha)) :
    (∀ j : ℕ, g * (t + alpha * delta) ^ j + r * (t + delta) ^ j = h * t ^ j) ↔
      r * delta ^ 2 = 0 := by
  constructor
  · intro hc
    have hz : (1 + alpha) * (r * delta ^ 2) = 0 := by
      rw [← square_discrepancy g r h t alpha delta h0 ha]
      exact CharTwo.add_eq_zero.mpr (hc 2)
    rcases hunit with ⟨v, hv⟩
    rw [← hv] at hz
    exact v.mul_right_eq_zero.mp hz
  · exact columns_of_annihilator g r h t alpha delta h0 ha

private theorem all_graphs_one (G : SimpleGraph (Fin 1)) : IsLabeledRiordan G := by
  exact ⟨0, 0, by simp, Subsingleton.elim _ _⟩

theorem count_one : a 1 = 1 := by
  letI : Nonempty (ComplementCompatible 1) :=
    ⟨⟨⊥, all_graphs_one _, all_graphs_one _⟩⟩
  letI : Subsingleton (ComplementCompatible 1) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim x.val y.val)⟩
  exact Nat.card_unique

noncomputable def prefixCount (n : ℕ) : ℕ :=
  1 + ∑ k ∈ Finset.range n, 2 ^ (3 * k / 2)

private theorem prefix_succ (n : ℕ) : prefixCount (n + 1) = prefixCount n + 2 ^ (3 * n / 2) := by
  simp only [prefixCount, Finset.sum_range_succ]
  omega

private theorem weight_two_step (n : ℕ) :
    (2 : ℕ) ^ (3 * (n + 2) / 2) = 8 * 2 ^ (3 * n / 2) := by
  rw [show 3 * (n + 2) / 2 = 3 * n / 2 + 3 by omega, pow_add]
  ring

private theorem prefix_two_step (n : ℕ) : prefixCount (n + 2) + 4 = 8 * prefixCount n := by
  induction n with
  | zero => norm_num [prefixCount, Finset.sum_range_succ]
  | succ n ih =>
    have hs : prefixCount (n + 1 + 2) = prefixCount (n + 2) + 2 ^ (3 * (n + 2) / 2) := by
      exact prefix_succ (n + 2)
    have hs' := prefix_succ n
    rw [weight_two_step n] at hs
    omega

private theorem prefix_even (k : ℕ) : 7 * prefixCount (2 * k) = 3 * 8 ^ k + 4 := by
  induction k with
  | zero => norm_num [prefixCount]
  | succ k ih =>
    have hr := prefix_two_step (2 * k)
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_succ]
    omega

private theorem prefix_odd (k : ℕ) : 7 * prefixCount (2 * k + 1) = 10 * 8 ^ k + 4 := by
  induction k with
  | zero => norm_num [prefixCount]
  | succ k ih =>
    have hr := prefix_two_step (2 * k + 1)
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_succ]
    omega

noncomputable def truncateMap (N : ℕ) : PowerSeries (ZMod 2) →+* (AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1))) where
  toFun f := AdjoinRoot.mk _ (PowerSeries.trunc (N + 1) f)
  map_zero' := by simp
  map_one' := by simp
  map_add' f g := by simp
  map_mul' f g := by
    rw [← map_mul]
    apply AdjoinRoot.mk_eq_mk.mpr
    apply Polynomial.X_pow_dvd_iff.mpr
    intro d hd
    rw [Polynomial.coeff_sub, sub_eq_zero, PowerSeries.coeff_trunc, if_pos hd]
    have hc := PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc f g hd
    rwa [← Polynomial.coe_mul, Polynomial.coeff_coe] at hc

theorem monicModulus (N : ℕ) :
    ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)).Monic :=
  Polynomial.monic_X_pow _

theorem modulusDegree (N : ℕ) :
    ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)).natDegree = N + 1 :=
  Polynomial.natDegree_X_pow _

noncomputable def coefficientEquiv (N : ℕ) : (AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1))) ≃ₗ[(ZMod 2)] (Fin (N + 1) → (ZMod 2)) := by
  have hd := modulusDegree N
  exact (AdjoinRoot.powerBasisAux' (monicModulus N)).equivFun.trans
    (LinearEquiv.piCongrLeft' (ZMod 2) (fun _ => (ZMod 2)) (finCongr hd))

noncomputable def truncatedCoeff (N : ℕ) (i : ℕ) (f : (AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)))) : (ZMod 2) :=
  (AdjoinRoot.modByMonicHom (monicModulus N) f).coeff i

theorem truncatedCoeff_truncateMap (N : ℕ) (f : PowerSeries (ZMod 2)) (i : ℕ) (hi : i < N + 1) :
    truncatedCoeff N i (truncateMap N f) = PowerSeries.coeff i f := by
  change (PowerSeries.trunc (N + 1) f %ₘ ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1))).coeff i = _
  rw [(Polynomial.modByMonic_eq_self_iff (monicModulus N)).mpr]
  · exact (PowerSeries.coeff_trunc i (N + 1) f).trans (if_pos hi)
  · simpa using PowerSeries.degree_trunc_lt f (N + 1)

theorem truncateMap_eq_iff (N : ℕ) (f g : PowerSeries (ZMod 2)) :
    truncateMap N f = truncateMap N g ↔
      ∀ i < N + 1, PowerSeries.coeff i f = PowerSeries.coeff i g := by
  constructor
  · intro h i hi
    rw [← truncatedCoeff_truncateMap N f i hi, ← truncatedCoeff_truncateMap N g i hi, h]
  · intro h
    apply AdjoinRoot.mk_eq_mk.mpr
    apply Polynomial.X_pow_dvd_iff.mpr
    intro i hi
    simp only [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hi, h i hi, sub_self]

theorem truncateMap_eq_zero_iff (N : ℕ) (f : PowerSeries (ZMod 2)) :
    truncateMap N f = 0 ↔ (PowerSeries.X : PowerSeries (ZMod 2)) ^ (N + 1) ∣ f := by
  rw [← map_zero (truncateMap N), truncateMap_eq_iff, PowerSeries.X_pow_dvd_iff]
  simp

theorem complement_orientation_card {V : Type*} (P : SimpleGraph V → Prop)
    (v w : V) (hvw : v ≠ w) :
    Nat.card {G : SimpleGraph V // P G ∧ P Gᶜ} =
      2 * Nat.card {G : SimpleGraph V // P G ∧ P Gᶜ ∧ G.Adj v w} := by
  classical
  let A := {G : SimpleGraph V // P G ∧ P Gᶜ}
  let B := {G : SimpleGraph V // P G ∧ P Gᶜ ∧ G.Adj v w}
  let e : A ≃ Bool × B :=
    { toFun := fun G =>
        if h : G.val.Adj v w then (true, ⟨G.val, G.property.1, G.property.2, h⟩)
        else (false, ⟨G.valᶜ, G.property.2, by simpa using G.property.1,
          by simpa [hvw] using h⟩)
      invFun := fun x =>
        if x.1 then ⟨x.2.val, x.2.property.1, x.2.property.2.1⟩
        else ⟨x.2.valᶜ, x.2.property.2.1, by simpa using x.2.property.1⟩
      left_inv := by
        intro G
        by_cases h : G.val.Adj v w <;> simp [h]
      right_inv := by
        rintro ⟨b, G⟩
        cases b <;> simp [G.property.2.2, hvw] }
  calc
    Nat.card A = Nat.card (Bool × B) := Nat.card_congr e
    _ = 2 * Nat.card B := by rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_bool]

theorem unit_parameter_criterion {R : Type*} [CommRing R] [CharP R 2]
    (g H : Rˣ) (f u t : R) :
    (∀ j : ℕ, (g : R) * f ^ j + ((H : R) + g) * u ^ j = (H : R) * t ^ j) ↔
      f = t + (((H : R) + g) * (↑g⁻¹ : R)) * (u + t) ∧
        ((H : R) + g) * (u + t) ^ 2 = 0 := by
  let r : R := (H : R) + g
  let alpha : R := r * (↑g⁻¹ : R)
  have h0 : (g : R) + r = H := by
    dsimp [r]
    rw [add_comm (H : R) (g : R), CharTwo.add_cancel_left]
  have ha : (g : R) * alpha = r := by
    dsimp [alpha]
    calc
      (g : R) * (r * ↑g⁻¹) = r * ((g : R) * ↑g⁻¹) := by ring
      _ = r := by simp
  have he : 1 + alpha = (H : R) * (↑g⁻¹ : R) := by
    dsimp [alpha, r]
    rw [add_mul, g.mul_inv]
    rw [add_comm ((H : R) * (↑g⁻¹ : R)) 1, CharTwo.add_cancel_left]
  have hunit : IsUnit (1 + alpha) := by
    rw [he]
    exact H.isUnit.mul (g⁻¹).isUnit
  have hud : t + (u + t) = u := by
    rw [add_comm u t, CharTwo.add_cancel_left]
  constructor
  · intro hc
    have hfirst := hc 1
    simp only [pow_one] at hfirst
    have hgf : (g : R) * f = (H : R) * t + r * u :=
      CharTwo.add_eq_iff_eq_add.mp hfirst
    have hf : f = t + alpha * (u + t) := by
      apply g.isUnit.mul_left_cancel
      rw [hgf]
      symm
      calc
        (g : R) * (t + alpha * (u + t)) =
            (g : R) * t + ((g : R) * alpha) * (u + t) := by ring
        _ = (H : R) * t + r * u := by rw [ha, ← h0]; ring
    refine ⟨hf, ?_⟩
    apply (columns_iff_annihilator (g : R) r (H : R) t alpha (u + t) h0 ha hunit).mp
    simpa only [← hf, hud] using hc
  · rintro ⟨hf, hnil⟩
    have hc := columns_of_annihilator (g : R) r (H : R) t alpha (u + t) h0 ha hnil
    simpa only [hf, hud] using hc

private instance truncated_nontrivial (N : ℕ) : Nontrivial ((AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)))) :=
  AdjoinRoot.nontrivial ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)) (by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast Nat.succ_ne_zero N)

private instance truncated_charP (N : ℕ) : CharP ((AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)))) 2 := by
  apply CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
  have h : (2 : (ZMod 2)) = 0 := by exact (ZMod.val_eq_zero 2).mp rfl
  have hh := congrArg (AdjoinRoot.of ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1))) h
  simpa only [map_ofNat, map_zero] using hh

private theorem truncateMap_surjective (N : ℕ) : Function.Surjective (truncateMap N) := by
  intro x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨(p : PowerSeries (ZMod 2)), ?_⟩
  apply AdjoinRoot.mk_eq_mk.mpr
  apply Polynomial.X_pow_dvd_iff.mpr
  intro i hi
  simp only [Polynomial.coeff_sub, PowerSeries.coeff_trunc, ite_eq_left hi,
    Polynomial.coeff_coe, sub_self]

theorem truncateMap_isUnit (N : ℕ) (f : (PowerSeries (ZMod 2)))
    (hf : PowerSeries.constantCoeff f = 1) : IsUnit (truncateMap N f) := by
  apply IsUnit.map (truncateMap N)
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [hf]
  exact isUnit_one

noncomputable def allOnes : (PowerSeries (ZMod 2)) := PowerSeries.mk (Function.const ℕ 1)

theorem allOnes_constant : PowerSeries.constantCoeff allOnes = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact PowerSeries.coeff_mk _ _

private theorem square_divisibility (f : (PowerSeries (ZMod 2))) (N : ℕ) :
    (PowerSeries.X : (PowerSeries (ZMod 2))) ^ N ∣ f ^ 2 ↔
      (PowerSeries.X : (PowerSeries (ZMod 2))) ^ ((N + 1) / 2) ∣ f := by
  have hs : PowerSeries.expand 2 (by decide) f = f ^ 2 := by
    simpa only [ZMod.card] using FiniteField.PowerSeries.expand_card f
  rw [← hs, PowerSeries.X_pow_dvd_iff, PowerSeries.X_pow_dvd_iff]
  constructor
  · intro h i hi
    have hz := h (2 * i) (by omega)
    rwa [PowerSeries.coeff_expand_mul] at hz
  · intro h i hi
    rw [PowerSeries.coeff_expand]
    split_ifs with hd
    · exact h (i / 2) (by omega)
    · rfl

theorem shifted_square_divisibility (f : (PowerSeries (ZMod 2))) (N k : ℕ) :
    (PowerSeries.X : (PowerSeries (ZMod 2))) ^ N ∣ PowerSeries.X ^ k * f ^ 2 ↔
      (PowerSeries.X : (PowerSeries (ZMod 2))) ^ ((N - k + 1) / 2) ∣ f := by
  by_cases hk : k ≤ N
  · have he : (PowerSeries.X : (PowerSeries (ZMod 2))) ^ N =
        PowerSeries.X ^ k * PowerSeries.X ^ (N - k) := by exact Eq.symm (pow_mul_pow_sub PowerSeries.X hk)
    rw [he, mul_dvd_mul_iff_left (pow_ne_zero k PowerSeries.X_ne_zero), square_divisibility]
  · have hNk : N ≤ k := by exact Nat.le_of_not_ge hk
    have hz : N - k = 0 := by exact Nat.sub_eq_zero_of_le hNk
    rw [hz]
    simp only [Nat.reduceAdd, Nat.reduceDiv, pow_zero, one_dvd, iff_true]
    exact dvd_mul_of_dvd_left (pow_dvd_pow _ hNk) _

private noncomputable def zeroPrefixEquiv (N q : ℕ) (hq : q ≤ N) :
    {f : Fin N → (ZMod 2) // ∀ i : Fin N, i.val < q → f i = 0} ≃ (Fin (N - q) → (ZMod 2)) where
  toFun f i := f.val ⟨q + i.val, by omega⟩
  invFun f := ⟨fun i => if h : i.val < q then 0 else f ⟨i.val - q, by omega⟩,
    by intro i hi; simp [hi]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    dsimp
    split_ifs with hi
    · exact (f.property i hi).symm
    · have he : (⟨q + (i.val - q), by omega⟩ : Fin N) = i := by
        apply Fin.ext
        dsimp
        omega
      exact congrArg f.val he
  right_inv f := by
    funext i
    dsimp
    simp only [show ¬q + i.val < q by omega, ↓reduceDIte]
    congr 1
    apply Fin.ext
    dsimp
    omega

theorem zero_prefix_card (N q : ℕ) (hq : q ≤ N) :
    Nat.card {f : Fin N → (ZMod 2) // ∀ i : Fin N, i.val < q → f i = 0} = 2 ^ (N - q) := by
  rw [Nat.card_congr (zeroPrefixEquiv N q hq), Nat.card_fun, Nat.card_fin]
  congr 1
  rw [Nat.card_eq_fintype_card, ZMod.card]

noncomputable def canonicalSeries (N : ℕ) (x : (AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)))) : (PowerSeries (ZMod 2)) :=
  (AdjoinRoot.modByMonicHom (monicModulus N) x : Polynomial (ZMod 2))

theorem truncateMap_canonicalSeries (N : ℕ) (x : (AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)))) :
    truncateMap N (canonicalSeries N x) = x := by
  obtain ⟨f, rfl⟩ := truncateMap_surjective N x
  apply (truncateMap_eq_iff N _ _).mpr
  intro i hi
  simpa only [canonicalSeries, Polynomial.coeff_coe, truncatedCoeff] using
    truncatedCoeff_truncateMap N f i hi

@[simp] theorem coefficientEquiv_apply (N : ℕ) (x : (AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)))) (i : Fin (N + 1)) :
    coefficientEquiv N x i = PowerSeries.coeff i.val (canonicalSeries N x) := by
  change (AdjoinRoot.powerBasisAux' (monicModulus N)).equivFun x
    ((finCongr (modulusDegree N)).symm i) = _
  rw [Module.Basis.equivFun_apply, AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  simp only [canonicalSeries, Polynomial.coeff_coe]
  rfl

theorem image_square_annihilator (N k : ℕ) (hk : k ≤ N + 1)
    (v w : (PowerSeries (ZMod 2))ˣ) (s : (PowerSeries (ZMod 2))) :
    (∃ delta : (PowerSeries (ZMod 2)),
      truncateMap N (PowerSeries.X ^ k * (v : (PowerSeries (ZMod 2))) * delta ^ 2) = 0 ∧
      truncateMap N (PowerSeries.X ^ k * (v : (PowerSeries (ZMod 2))) * (w : (PowerSeries (ZMod 2))) * delta) =
        truncateMap N s) ↔
      (PowerSeries.X : (PowerSeries (ZMod 2))) ^ (k + (N + 1 - k + 1) / 2) ∣ s := by
  let q := (N + 1 - k + 1) / 2
  have hq : k + q ≤ N + 1 := by dsimp [q]; omega
  have nil_iff : ∀ delta : (PowerSeries (ZMod 2)),
      truncateMap N (PowerSeries.X ^ k * (v : (PowerSeries (ZMod 2))) * delta ^ 2) = 0 ↔
        (PowerSeries.X : (PowerSeries (ZMod 2))) ^ q ∣ delta := by
    intro delta
    rw [truncateMap_eq_zero_iff,
      show PowerSeries.X ^ k * (v : (PowerSeries (ZMod 2))) * delta ^ 2 =
        (v : (PowerSeries (ZMod 2))) * (PowerSeries.X ^ k * delta ^ 2) by ring,
      v.isUnit.dvd_mul_left, shifted_square_divisibility]
  constructor
  · rintro ⟨delta, hn, he⟩
    have hd := (nil_iff delta).mp hn
    have hp : (PowerSeries.X : (PowerSeries (ZMod 2))) ^ (k + q) ∣
        PowerSeries.X ^ k * (v : (PowerSeries (ZMod 2))) * (w : (PowerSeries (ZMod 2))) * delta := by
      rw [pow_add]
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        (mul_dvd_mul (dvd_refl ((PowerSeries.X : (PowerSeries (ZMod 2))) ^ k))
          (dvd_mul_of_dvd_right hd ((v : (PowerSeries (ZMod 2))) * w)))
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro i hi
    rw [← (truncateMap_eq_iff N _ _).mp he i (by omega)]
    exact (PowerSeries.X_pow_dvd_iff.mp hp) i hi
  · rintro ⟨z, hz⟩
    let delta : (PowerSeries (ZMod 2)) := PowerSeries.X ^ q * (↑(v * w)⁻¹ : (PowerSeries (ZMod 2))) * z
    refine ⟨delta, (nil_iff delta).mpr ?_, ?_⟩
    · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    · apply congrArg (truncateMap N)
      rw [hz]
      dsimp [delta]
      calc
        PowerSeries.X ^ k * (v : (PowerSeries (ZMod 2))) * (w : (PowerSeries (ZMod 2))) *
            (PowerSeries.X ^ q * ↑(v * w)⁻¹ * z) =
            PowerSeries.X ^ k * PowerSeries.X ^ q *
              ((↑(v * w) : (PowerSeries (ZMod 2))) * ↑(v * w)⁻¹) * z := by
                rw [Units.val_mul]; ring
        _ = PowerSeries.X ^ (k + q) * z := by rw [Units.mul_inv, mul_one, ← pow_add]

private theorem recurrence_of_sum (hs : ∀ n, 1 ≤ n → a n = prefixCount (n - 1)) :
    ∀ n, 3 ≤ n → (a n : ℤ) = 8 * (a (n - 2) : ℤ) - 4 := by
  intro n hn
  have hr := prefix_two_step (n - 3)
  have heq : a n + 4 = 8 * a (n - 2) := by
    rw [hs n (by omega), hs (n - 2) (by omega)]
    convert hr using 1 <;> congr 2 <;> omega
  have hz : (a n : ℤ) + 4 = 8 * (a (n - 2) : ℤ) := by exact_mod_cast heq
  omega

private theorem difference_of_sum (hs : ∀ n, 1 ≤ n → a n = prefixCount (n - 1)) :
    ∀ n, 1 ≤ n → (a (n + 1) : ℤ) - (a n : ℤ) = (2 : ℤ) ^ (3 * (n - 1) / 2) := by
  intro n hn
  have hr := prefix_succ (n - 1)
  have heq : a (n + 1) = a n + 2 ^ (3 * (n - 1) / 2) := by
    rw [hs (n + 1) (by omega), hs n hn]
    simpa [show n - 1 + 1 = n by omega] using hr
  have hz : (a (n + 1) : ℤ) = (a n : ℤ) + (2 : ℤ) ^ (3 * (n - 1) / 2) := by
    exact_mod_cast heq
  omega

private theorem a113836_eq_prefix (m : ℕ) : a113836 m + 1 = prefixCount m := by
  unfold a113836 prefixCount
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  unfold a001651
  omega

private theorem even_of_sum (hs : ∀ n, 1 ≤ n → a n = prefixCount (n - 1)) :
    ∀ k, 1 ≤ k → (a (2 * k) : ℚ) = (10 * (8 : ℚ) ^ (k - 1) + 4) / 7 := by
  intro k hk
  have hr := prefix_odd (k - 1)
  have heq : 7 * a (2 * k) = 10 * 8 ^ (k - 1) + 4 := by
    rw [hs (2 * k) (by omega)]
    convert hr using 1 <;> congr 2 <;> omega
  have hq : 7 * (a (2 * k) : ℚ) = 10 * (8 : ℚ) ^ (k - 1) + 4 := by exact_mod_cast heq
  linarith

private theorem odd_of_sum (hs : ∀ n, 1 ≤ n → a n = prefixCount (n - 1)) :
    ∀ k, (a (2 * k + 1) : ℚ) = (3 * (8 : ℚ) ^ k + 4) / 7 := by
  intro k
  have hr := prefix_even k
  have heq : 7 * a (2 * k + 1) = 3 * 8 ^ k + 4 := by
    rw [hs (2 * k + 1) (by omega)]
    simpa using hr
  have hq : 7 * (a (2 * k + 1) : ℚ) = 3 * (8 : ℚ) ^ k + 4 := by exact_mod_cast heq
  linarith

private theorem ogf_of_recurrence (h1 : a 1 = 1) (h2 : a 2 = 2)
    (hr : ∀ n, 3 ≤ n → (a n : ℤ) = 8 * (a (n - 2) : ℤ) - 4) :
    ogf = conjecturedOGF := by
  have h3 : a 3 = 4 := by
    have h := hr 3 (by decide)
    norm_num [h1] at h
    exact_mod_cast h
  have hq : ∀ n, 3 ≤ n → (a n : ℚ) = 8 * (a (n - 2) : ℚ) - 4 := by
    intro n hn
    exact_mod_cast hr n hn
  let X : PowerSeries ℚ := PowerSeries.X
  let D : PowerSeries ℚ := (1 - X) * (1 - 8 * X ^ 2)
  have he : D * ogf = ogf - X * ogf - 8 * (X ^ 2 * ogf) + 8 * (X ^ 3 * ogf) := by
    dsimp [D]
    ring
  have hD : D * ogf = X + X ^ 2 - 6 * X ^ 3 := by
    rw [he]
    have hx : ∀ n : ℕ, PowerSeries.coeff n (PowerSeries.X * ogf) =
        if 1 ≤ n then PowerSeries.coeff (n - 1) ogf else 0 := by
      intro n
      simpa only [pow_one] using PowerSeries.coeff_X_pow_mul' ogf 1 n
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul]
    simp only [X, PowerSeries.coeff_X, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X_pow_mul']
    simp only [hx]
    simp only [ogf, PowerSeries.coeff_mk]
    rcases n with _ | n
    · norm_num
    rcases n with _ | n
    · norm_num [h1]
    rcases n with _ | n
    · norm_num [h1, h2]
    rcases n with _ | n
    · norm_num [h1, h2, h3]
    have hn := hq (n + 4) (by omega)
    have hn' := hq (n + 3) (by omega)
    simp only [show n + 4 - 2 = n + 2 by omega] at hn
    simp only [show n + 3 - 2 = n + 1 by omega] at hn'
    simp only [show n + 1 + 1 + 1 + 1 = n + 4 by omega]
    simp (disch := omega) only [show n + 4 - 1 = n + 3 by omega,
      show n + 4 - 2 = n + 2 by omega, show n + 4 - 3 = n + 1 by omega,
      ite_eq_left (by omega : 1 ≤ n + 4), ite_eq_left (by omega : 2 ≤ n + 4),
      ite_eq_left (by omega : 3 ≤ n + 4),
      ite_eq_right (by omega : n + 4 ≠ 0), ite_eq_right (by omega : n + 3 ≠ 0),
      ite_eq_right (by omega : n + 2 ≠ 0), ite_eq_right (by omega : n + 1 ≠ 0),
      ite_eq_right (by omega : n + 4 ≠ 1), ite_eq_right (by omega : n + 4 ≠ 2),
      ite_eq_right (by omega : n + 4 ≠ 3)]
    linarith
  have hi : D * PowerSeries.invOfUnit D 1 = 1 :=
    PowerSeries.mul_invOfUnit D 1 (by simp [D, X])
  calc
    ogf = (D * ogf) * PowerSeries.invOfUnit D 1 := by rw [mul_right_comm, hi, one_mul]
    _ = (X + X ^ 2 - 6 * X ^ 3) * PowerSeries.invOfUnit D 1 := by rw [hD]
    _ = conjecturedOGF := by
      change (X + X ^ 2 - 6 * X ^ 3) * PowerSeries.invOfUnit D 1 =
        X * (1 - 2 * X) * (1 + 3 * X) * PowerSeries.invOfUnit D 1
      congr 1
      ring

theorem claim_of_sum (hs : ∀ n, 1 ≤ n → a n = prefixCount (n - 1)) : claim := by
  have h1 : a 1 = 1 := by exact count_one
  have h2 : a 2 = 2 := by simpa [prefixCount] using hs 2 (by decide)
  refine ⟨h1, h2, recurrence_of_sum hs, difference_of_sum hs, ?_, ?_,
    even_of_sum hs, odd_of_sum hs, ogf_of_recurrence h1 h2 (recurrence_of_sum hs)⟩
  · intro n hn
    exact hs n hn
  · intro n hn
    rw [hs n (by omega), ← a113836_eq_prefix]

end D5.S3.Combinatorics.Riordan.LabeledComplementAlgebra
