/- GID: D5/S3/Combinatorics/Riordan/LabeledComplementClassification
   generality: G
   mirror-B: Blueprint/D5/S3/Combinatorics/Riordan/LabeledComplementClassification.md
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite binary Riordan complement classification. -/

/-
admission_basis: escape-witness
escape_witness: graph_complement_factor_criterion
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27284
The labels i : Fin n represent the source labels i.val + 1.
The parity expressions use the disclosed products 10 * 8^(k-1) and 3 * 8^k.
Coefficients lie in ZMod 2; truncations use AdjoinRoot of a power of Polynomial.X.
riordan_adj_lower: proof_shape: bind-only; consumers: graph_eq_iff_columns, graph_complement_iff_columns, unitParametersToGraph, unitParametersToGraph_surjective.
column_coeff_zero: proof_shape: bind-only; consumers: graph_eq_iff_columns, graph_complement_iff_columns.
graph_eq_iff_columns: proof_shape: content; consumers: unitParametersToGraph_injective, unitParametersToGraph_surjective, canonicalGraph_eq, classToUnitParams_surjective.
column_equation_coeff: proof_shape: bind-only; consumers: graph_complement_iff_columns.
graph_complement_iff_columns: proof_shape: content; consumers: graph_complement_criterion.
unitParametersToGraph_injective: proof_shape: content; consumers: count_all.
unitParametersToGraph_surjective: proof_shape: content; consumers: count_all.
graph_complement_criterion: proof_shape: content; consumers: graph_complement_factor_criterion, class_complement, classToUnitParams_surjective.
graph_complement_factor_criterion: proof_shape: content; consumers: class_complement, classToUnitParams_surjective.
canonical_constant_truncateMap: proof_shape: bind-only; consumers: classToUnitParams, classToUnitParams_surjective.
canonicalSeries_zero: proof_shape: bind-only; consumers: classToUnitParams_surjective.
canonicalGraph_eq: proof_shape: content; consumers: classToUnitParams.
first_degree_factor: proof_shape: bind-only; consumers: class_complement, classToUnitParams_surjective.
seriesOfVector_coeff: proof_shape: bind-only; consumers: class_complement, classToUnitParams.
-/

import D5.S3.Combinatorics.Riordan.LabeledComplementAlgebra

set_option linter.unusedTactic false
set_option maxHeartbeats 1000000

namespace D5.S3.Combinatorics.Riordan.LabeledComplementClassification

open D5.S3.Combinatorics.Riordan.LabeledComplementAlgebra

open scoped BigOperators

theorem riordan_adj_lower {n : ℕ} (g f : (PowerSeries (ZMod 2))) {i j : Fin n}
    (hji : j.val < i.val) :
    (riordanGraph n g f).Adj i j ↔ PowerSeries.coeff (i.val - 1) (g * f ^ j.val) = 1 := by
  have hne : i ≠ j := by exact Ne.symm (Fin.ne_of_lt hji)
  have hnlt : ¬i.val < j.val := by exact Nat.not_lt_of_gt hji
  simp only [riordanGraph, SimpleGraph.fromRel_adj, hne, hji, hnlt,
    not_false_eq_true, true_and, false_and, or_false]
  exact and_iff_right hne

private theorem column_coeff_zero (g f : (PowerSeries (ZMod 2)))
    (hf : PowerSeries.constantCoeff f = 0) (i j : ℕ) (hij : i < j) :
    PowerSeries.coeff i (g * f ^ j) = 0 := by
  apply (PowerSeries.X_pow_dvd_iff.mp ?_) i hij
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr hf) j) g

theorem graph_eq_iff_columns (N : ℕ) (g f g' f' : (PowerSeries (ZMod 2)))
    (hf : PowerSeries.constantCoeff f = 0) (hf' : PowerSeries.constantCoeff f' = 0) :
    riordanGraph (N + 2) g f = riordanGraph (N + 2) g' f' ↔
      ∀ j < N + 1, truncateMap N (g * f ^ j) = truncateMap N (g' * f' ^ j) := by
  constructor
  · intro hg j hj
    apply (truncateMap_eq_iff N _ _).mpr
    intro i hi
    by_cases hji : j ≤ i
    · let v : Fin (N + 2) := ⟨i + 1, by omega⟩
      let w : Fin (N + 2) := ⟨j, by omega⟩
      have hvw : w.val < v.val := by exact Order.lt_add_one_iff.mpr hji
      have hc : PowerSeries.coeff i (g * f ^ j) = 1 ↔
          PowerSeries.coeff i (g' * f' ^ j) = 1 := by
        simpa [v, w] using (riordan_adj_lower g f hvw).symm.trans
          ((congrArg (fun G : SimpleGraph (Fin (N + 2)) => G.Adj v w) hg).to_iff.trans
            (riordan_adj_lower g' f' hvw))
      have bit : ∀ a b : (ZMod 2), (a = 1 ↔ b = 1) → a = b := by decide
      exact bit _ _ hc
    · rw [column_coeff_zero g f hf i j (by omega),
        column_coeff_zero g' f' hf' i j (by omega)]
  · intro h
    have lower : ∀ i j : Fin (N + 2), j.val < i.val →
        ((riordanGraph (N + 2) g f).Adj i j ↔ (riordanGraph (N + 2) g' f').Adj i j) := by
      intro i j hji
      rw [riordan_adj_lower g f hji, riordan_adj_lower g' f' hji]
      have hc := (truncateMap_eq_iff N _ _).mp (h j.val (by omega)) (i.val - 1) (by omega)
      rw [hc]
    ext i j
    by_cases hji : j.val < i.val
    · exact lower i j hji
    · by_cases hij : i.val < j.val
      · simpa only [SimpleGraph.adj_comm] using lower j i hij
      · have heq : i = j := Fin.ext (by omega)
        subst j
        simp

private theorem column_equation_coeff (N j : ℕ) (g f r u : (PowerSeries (ZMod 2))) :
    (truncateMap N g * (truncateMap N f) ^ j +
      truncateMap N r * (truncateMap N u) ^ j =
      truncateMap N allOnes * (truncateMap N PowerSeries.X) ^ j) ↔
    ∀ i < N + 1, PowerSeries.coeff i (g * f ^ j) +
      PowerSeries.coeff i (r * u ^ j) = if j ≤ i then 1 else 0 := by
  have h := truncateMap_eq_iff N (g * f ^ j + r * u ^ j) (allOnes * PowerSeries.X ^ j)
  rw [map_add, map_mul, map_pow, map_mul, map_pow, map_mul, map_pow] at h
  have hh : ∀ i : ℕ, PowerSeries.coeff i (allOnes * PowerSeries.X ^ j) =
      if j ≤ i then (1 : (ZMod 2)) else 0 := by
    intro i
    rw [PowerSeries.coeff_mul_X_pow']
    simp only [allOnes, PowerSeries.coeff_mk, Function.const_apply]
  simpa only [map_add, hh] using h

private theorem graph_complement_iff_columns (N : ℕ) (g f r u : (PowerSeries (ZMod 2)))
    (hf : PowerSeries.constantCoeff f = 0) (hu : PowerSeries.constantCoeff u = 0) :
    riordanGraph (N + 2) g f = (riordanGraph (N + 2) r u)ᶜ ↔
      ∀ j : ℕ, truncateMap N g * (truncateMap N f) ^ j +
        truncateMap N r * (truncateMap N u) ^ j =
        truncateMap N allOnes * (truncateMap N PowerSeries.X) ^ j := by
  have bit : ∀ a b : (ZMod 2), (a = 1 ↔ ¬b = 1) ↔ a + b = 1 := by decide
  constructor
  · intro hg j
    apply (column_equation_coeff N j g f r u).mpr
    intro i hi
    by_cases hji : j ≤ i
    · let v : Fin (N + 2) := ⟨i + 1, by omega⟩
      let w : Fin (N + 2) := ⟨j, by omega⟩
      have hvw : w.val < v.val := by exact Order.lt_add_one_iff.mpr hji
      have hne : v ≠ w := by exact Ne.symm (Fin.ne_of_lt hvw)
      rw [ite_eq_left hji]
      apply (bit _ _).mp
      have hc : (riordanGraph (N + 2) g f).Adj v w ↔
          ¬(riordanGraph (N + 2) r u).Adj v w := by
        constructor
        · intro ha
          rw [hg] at ha
          exact ((SimpleGraph.compl_adj _ _ _).mp ha).2
        · intro hn
          rw [hg]
          exact (SimpleGraph.compl_adj _ _ _).mpr ⟨hne, hn⟩
      simpa [v, w] using (riordan_adj_lower g f hvw).symm.trans
        (hc.trans (not_congr (riordan_adj_lower r u hvw)))
    · rw [ite_eq_right hji, column_coeff_zero g f hf i j (by omega),
        column_coeff_zero r u hu i j (by omega), zero_add]
  · intro h
    have lower : ∀ i j : Fin (N + 2), j.val < i.val →
        ((riordanGraph (N + 2) g f).Adj i j ↔ (riordanGraph (N + 2) r u)ᶜ.Adj i j) := by
      intro i j hji
      have hne : i ≠ j := by exact Ne.symm (Fin.ne_of_lt hji)
      rw [riordan_adj_lower g f hji, SimpleGraph.compl_adj,
        riordan_adj_lower r u hji]
      have hc := (column_equation_coeff N j.val g f r u).mp (h j.val) (i.val - 1) (by omega)
      have hb : PowerSeries.coeff (i.val - 1) (g * f ^ j.val) = 1 ↔
          ¬PowerSeries.coeff (i.val - 1) (r * u ^ j.val) = 1 := by
        apply (bit _ _).mpr
        simpa only [ite_eq_left (by omega : j.val ≤ i.val - 1)] using hc
      exact hb.trans (and_iff_right hne).symm
    ext i j
    by_cases hji : j.val < i.val
    · exact lower i j hji
    · by_cases hij : i.val < j.val
      · simpa only [SimpleGraph.adj_comm] using lower j i hij
      · have heq : i = j := Fin.ext (by omega)
        subst j
        simp

def Oriented (N : ℕ) := {G : SimpleGraph (Fin (N + 2)) //
  IsLabeledRiordan G ∧ IsLabeledRiordan Gᶜ ∧ G.Adj ⟨1, by omega⟩ 0}

def UnitParameters (N : ℕ) := {p : (AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1))) × (AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1))) //
  PowerSeries.constantCoeff (canonicalSeries N p.1) = 1 ∧
  PowerSeries.constantCoeff (canonicalSeries N p.2) = 0 ∧
  IsLabeledRiordan (riordanGraph (N + 2)
    (canonicalSeries N p.1) (canonicalSeries N p.2))ᶜ}

noncomputable def unitParametersToGraph (N : ℕ) (p : UnitParameters N) : Oriented N :=
  ⟨riordanGraph (N + 2) (canonicalSeries N p.val.1) (canonicalSeries N p.val.2),
    ⟨⟨_, _, p.property.2.1, rfl⟩, p.property.2.2, by
      rw [riordan_adj_lower _ _ (by simp)]
      simpa only [Fin.val_zero, pow_zero, mul_one, Nat.reduceSub, PowerSeries.coeff_zero_eq_constantCoeff_apply]
        using p.property.1⟩⟩

theorem unitParametersToGraph_injective (N : ℕ) :
    Function.Injective (unitParametersToGraph N) := by
  intro p q he
  have hg := congrArg Subtype.val he
  have hc := (graph_eq_iff_columns N _ _ _ _ p.property.2.1 q.property.2.1).mp hg
  have h0 := hc 0 (by omega)
  simp only [pow_zero, mul_one, truncateMap_canonicalSeries] at h0
  have h1 : p.val.2 = q.val.2 := by
    by_cases hN : N = 0
    · subst N
      calc
        p.val.2 = truncateMap 0 (canonicalSeries 0 p.val.2) :=
          (truncateMap_canonicalSeries 0 p.val.2).symm
        _ = truncateMap 0 (canonicalSeries 0 q.val.2) := by
          apply (truncateMap_eq_iff 0 _ _).mpr
          intro i hi
          have hi0 : i = 0 := by exact Nat.lt_one_iff.mp hi
          subst i
          simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
            p.property.2.1.trans q.property.2.1.symm
        _ = q.val.2 := truncateMap_canonicalSeries 0 q.val.2
    · have h1 := hc 1 (by omega)
      simp only [pow_one, map_mul, truncateMap_canonicalSeries, h0] at h1
      have hu := truncateMap_isUnit N (canonicalSeries N q.val.1) q.property.1
      rw [truncateMap_canonicalSeries] at hu
      exact hu.mul_left_cancel h1
  apply Subtype.ext
  exact Prod.ext h0 h1

@[simp] theorem canonical_constant_truncateMap (N : ℕ) (f : (PowerSeries (ZMod 2))) :
    PowerSeries.constantCoeff (canonicalSeries N (truncateMap N f)) =
      PowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, canonicalSeries, Polynomial.coeff_coe]
  simpa only [truncatedCoeff, PowerSeries.coeff_zero_eq_constantCoeff_apply] using
    truncatedCoeff_truncateMap N f 0 (by omega)

@[simp] theorem canonicalSeries_zero (N : ℕ) : canonicalSeries N 0 = 0 := by
  simp only [canonicalSeries, map_zero, Polynomial.coe_zero]

theorem canonicalGraph_eq (N : ℕ) (g f : (PowerSeries (ZMod 2)))
    (hf : PowerSeries.constantCoeff f = 0) :
    riordanGraph (N + 2) (canonicalSeries N (truncateMap N g))
      (canonicalSeries N (truncateMap N f)) = riordanGraph (N + 2) g f := by
  apply (graph_eq_iff_columns N _ _ _ _ (by simpa using hf) hf).mpr
  intro j hj
  simp only [map_mul, map_pow, truncateMap_canonicalSeries]

theorem unitParametersToGraph_surjective (N : ℕ) :
    Function.Surjective (unitParametersToGraph N) := by
  intro G
  obtain ⟨g, f, hf, hg⟩ := G.property.1
  have hconst : PowerSeries.constantCoeff g = 1 := by
    have he := G.property.2.2
    rw [hg, riordan_adj_lower _ _ (by simp)] at he
    simpa only [Fin.val_zero, pow_zero, mul_one, Nat.reduceSub, PowerSeries.coeff_zero_eq_constantCoeff_apply] using he
  have hgraph : riordanGraph (N + 2)
      (canonicalSeries N (truncateMap N g)) (canonicalSeries N (truncateMap N f)) = G.val :=
    (canonicalGraph_eq N g f hf).trans hg.symm
  refine ⟨⟨(truncateMap N g, truncateMap N f),
    by rw [canonical_constant_truncateMap, canonical_constant_truncateMap]; exact ⟨hconst, hf, by rw [hgraph]; exact G.property.2.1⟩⟩, ?_⟩
  exact Subtype.ext hgraph

theorem graph_complement_criterion (N : ℕ) (g : (PowerSeries (ZMod 2))ˣ) (f : (PowerSeries (ZMod 2)))
    (hg : PowerSeries.constantCoeff (g : (PowerSeries (ZMod 2))) = 1)
    (hf : PowerSeries.constantCoeff f = 0) :
    IsLabeledRiordan (riordanGraph (N + 2) (g : (PowerSeries (ZMod 2))) f)ᶜ ↔
      ∃ delta : (PowerSeries (ZMod 2)), PowerSeries.constantCoeff delta = 0 ∧
        truncateMap N f = truncateMap N PowerSeries.X +
          (truncateMap N (allOnes + (g : (PowerSeries (ZMod 2)))) * truncateMap N (↑g⁻¹ : (PowerSeries (ZMod 2)))) *
            truncateMap N delta ∧
        truncateMap N ((allOnes + (g : (PowerSeries (ZMod 2)))) * delta ^ 2) = 0 := by
  let gg : ((AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1))))ˣ := Units.map (truncateMap N).toMonoidHom g
  obtain ⟨HH, hHH⟩ := truncateMap_isUnit N allOnes allOnes_constant
  have hgg : (gg : (AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)))) = truncateMap N (g : (PowerSeries (ZMod 2))) := rfl
  have hggi : (↑gg⁻¹ : (AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)))) = truncateMap N (↑g⁻¹ : (PowerSeries (ZMod 2))) := rfl
  constructor
  · rintro ⟨r, u, hu, he⟩
    have hc := (graph_complement_iff_columns N (g : (PowerSeries (ZMod 2))) f r u hf hu).mp
      (by rw [← he]; simp)
    have hr := hc 0
    simp only [pow_zero, mul_one] at hr
    have hr' : truncateMap N r = truncateMap N (allOnes + (g : (PowerSeries (ZMod 2)))) := by
      rw [map_add]
      apply CharTwo.add_eq_iff_eq_add.mp
      simpa only [add_comm] using hr
    have hcols : ∀ j : ℕ, (gg : (AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)))) * (truncateMap N f) ^ j +
        ((HH : (AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)))) + gg) * (truncateMap N u) ^ j =
        (HH : (AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)))) * (truncateMap N PowerSeries.X) ^ j := by
      intro j
      rw [hgg, hHH]
      have hj := hc j
      rw [hr', map_add] at hj
      exact hj
    have hcrit := (unit_parameter_criterion gg HH (truncateMap N f)
      (truncateMap N u) (truncateMap N PowerSeries.X)).mp hcols
    refine ⟨u + PowerSeries.X, by simp [hu], ?_, ?_⟩
    · simpa only [map_add, hgg, hggi, hHH] using hcrit.1
    · simpa only [map_mul, map_pow, map_add, hgg, hHH] using hcrit.2
  · rintro ⟨delta, hd, he, hn⟩
    let u := delta + PowerSeries.X
    have hu : PowerSeries.constantCoeff u = 0 := by simp [u, hd]
    have hc : ∀ j : ℕ, (gg : (AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)))) * (truncateMap N f) ^ j +
        ((HH : (AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)))) + gg) * (truncateMap N u) ^ j =
        (HH : (AdjoinRoot ((Polynomial.X : Polynomial (ZMod 2)) ^ (N + 1)))) * (truncateMap N PowerSeries.X) ^ j := by
      apply (unit_parameter_criterion gg HH _ _ _).mpr
      have hud : truncateMap N u + truncateMap N PowerSeries.X = truncateMap N delta := by
        simp only [u, map_add, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [hud]
      constructor
      · simpa only [hgg, hggi, hHH, map_add] using he
      · simpa only [hgg, hHH, map_mul, map_add, map_pow] using hn
    have hgraph : riordanGraph (N + 2) (g : (PowerSeries (ZMod 2))) f =
        (riordanGraph (N + 2) (allOnes + (g : (PowerSeries (ZMod 2)))) u)ᶜ := by
      apply (graph_complement_iff_columns N _ _ _ _ hf hu).mpr
      simpa only [hgg, hHH, map_add] using hc
    refine ⟨allOnes + (g : (PowerSeries (ZMod 2))), u, hu, ?_⟩
    rw [hgraph]
    simp

theorem graph_complement_factor_criterion (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N + 1)
    (g v : (PowerSeries (ZMod 2))ˣ) (f : (PowerSeries (ZMod 2)))
    (hg : PowerSeries.constantCoeff (g : (PowerSeries (ZMod 2))) = 1)
    (hf : PowerSeries.constantCoeff f = 0)
    (hr : allOnes + (g : (PowerSeries (ZMod 2))) = PowerSeries.X ^ k * (v : (PowerSeries (ZMod 2)))) :
    IsLabeledRiordan (riordanGraph (N + 2) (g : (PowerSeries (ZMod 2))) f)ᶜ ↔
      (PowerSeries.X : (PowerSeries (ZMod 2))) ^ (k + (N + 1 - k + 1) / 2) ∣ (f + PowerSeries.X) := by
  have heq : ∀ delta : (PowerSeries (ZMod 2)),
      truncateMap N f = truncateMap N PowerSeries.X +
        (truncateMap N (allOnes + (g : (PowerSeries (ZMod 2)))) * truncateMap N (↑g⁻¹ : (PowerSeries (ZMod 2)))) *
          truncateMap N delta ↔
      truncateMap N (PowerSeries.X ^ k * (v : (PowerSeries (ZMod 2))) * (↑g⁻¹ : (PowerSeries (ZMod 2))) * delta) =
        truncateMap N (f + PowerSeries.X) := by
    intro delta
    simp only [← hr, map_add, map_mul]
    constructor
    · intro h
      apply CharTwo.add_eq_iff_eq_add.mp
      simpa only [add_comm] using h.symm
    · intro h
      have hh := CharTwo.add_eq_iff_eq_add.mpr h
      simpa only [add_comm] using hh.symm
  rw [graph_complement_criterion N g f hg hf]
  constructor
  · rintro ⟨delta, hd, he, hn⟩
    apply (image_square_annihilator N k (by omega) v g⁻¹ (f + PowerSeries.X)).mp
    refine ⟨delta, ?_, (heq delta).mp he⟩
    simpa only [hr] using hn
  · intro hs
    obtain ⟨delta, hn, he⟩ :=
      (image_square_annihilator N k (by omega) v g⁻¹ (f + PowerSeries.X)).mpr hs
    have hdelta : (PowerSeries.X : (PowerSeries (ZMod 2))) ^ ((N + 1 - k + 1) / 2) ∣ delta := by
      rw [truncateMap_eq_zero_iff,
        show PowerSeries.X ^ k * (v : (PowerSeries (ZMod 2))) * delta ^ 2 =
          (v : (PowerSeries (ZMod 2))) * (PowerSeries.X ^ k * delta ^ 2) by ring,
        v.isUnit.dvd_mul_left, shifted_square_divisibility] at hn
      exact hn
    have hd : PowerSeries.constantCoeff delta = 0 := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
        (PowerSeries.X_pow_dvd_iff.mp hdelta) 0 (by omega)
    exact ⟨delta, hd, (heq delta).mpr he, by simpa only [hr] using hn⟩

theorem first_degree_factor (r : (PowerSeries (ZMod 2))) (k : ℕ)
    (hzero : ∀ i < k, PowerSeries.coeff i r = 0) (hone : PowerSeries.coeff k r = 1) :
    ∃ v : (PowerSeries (ZMod 2))ˣ, r = PowerSeries.X ^ k * (v : (PowerSeries (ZMod 2))) := by
  have hr : r ≠ 0 := by
    intro hz
    exact zero_ne_one (by simpa only [hz, map_zero] using hone)
  have ho : r.order = k := PowerSeries.order_eq_nat.mpr ⟨by rw [hone]; exact one_ne_zero, hzero⟩
  refine ⟨PowerSeries.Unit_of_divided_by_X_pow_order r, ?_⟩
  rw [PowerSeries.Unit_of_divided_by_X_pow_order_nonzero hr]
  simpa only [ho, ENat.toNat_natCast] using (PowerSeries.X_pow_order_mul_divXPowOrder (f := r)).symm

noncomputable def seriesOfVector (N : ℕ) (v : Fin (N + 1) → (ZMod 2)) : (PowerSeries (ZMod 2)) :=
  canonicalSeries N ((coefficientEquiv N).symm v)

@[simp] theorem seriesOfVector_coeff (N : ℕ) (v : Fin (N + 1) → (ZMod 2)) (i : Fin (N + 1)) :
    PowerSeries.coeff i.val (seriesOfVector N v) = v i := by
  rw [seriesOfVector, ← coefficientEquiv_apply, LinearEquiv.apply_symm_apply]

end D5.S3.Combinatorics.Riordan.LabeledComplementClassification
