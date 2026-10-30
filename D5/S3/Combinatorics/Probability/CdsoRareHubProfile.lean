/- GID: D5/S3/Combinatorics/Probability/CdsoRareHubProfile
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/CdsoRareHubProfile
   mirror-E: none(waiver:symbolic-finite-probability-law)
   anchors: []
   utility: none
   digest: Actual rare-hub incidence laws and their reciprocal-marginal energy. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open scoped BigOperators
open Filter Topology
noncomputable section
set_option autoImplicit false

namespace D5.S3.Combinatorics.Probability.CdsoRareHubProfile

/-- A law on all subsets, with zero mass at the empty subset. All its observables
are computed from this one law. -/
structure Profile (V : Type*) [Fintype V] [DecidableEq V] where
  mass : Finset V → ℝ
  nonneg : ∀ T, 0 ≤ mass T
  total : ∑ T, mass T = 1
  empty : mass ∅ = 0
  positive : ∀ i, 0 < ∑ T, if i ∈ T then mass T else 0

def marginal {V : Type*} [Fintype V] [DecidableEq V]
    (x : Finset V → ℝ) (i : V) : ℝ := ∑ T, if i ∈ T then x T else 0

def moment {V : Type*} [Fintype V] [DecidableEq V]
    (x : Finset V → ℝ) (i : V) : ℝ :=
  ∑ T, x T * (if i ∈ T then (T.card : ℝ)^2 else 0)

def mean {V : Type*} [Fintype V] [DecidableEq V] (x : Finset V → ℝ) : ℝ :=
  ∑ T, x T * T.card

def energy {V : Type*} [Fintype V] [DecidableEq V] (x : Finset V → ℝ) : ℝ :=
  (∑ i, moment x i / marginal x i ^ 2) / 2

def benchmark (r : ℕ) (q : ℝ) : ℝ :=
  (r : ℝ)^2 * ((3 * ((r : ℝ)-1)^2 + 3*((r : ℝ)-1)+1)*q -
    ((r : ℝ)-1)*(r : ℝ)*(2*((r : ℝ)-1)+1)) / (2*q^2)

def extra (a : ℕ) : Fin (a + 2) := Fin.last (a + 1)

def core (a : ℕ) : Finset (Fin (a + 2)) := Finset.univ.erase (extra a)

def rareLaw (a : ℕ) (ε : ℝ) (T : Finset (Fin (a + 2))) : ℝ :=
  (if T = {extra a} then ε else 0) +
  (if T = core a then ((a : ℝ)-1)*ε else 0) +
  ∑ j ∈ core a, if T = (core a).erase j then (1-(a : ℝ)*ε)/((a : ℝ)+1) else 0

private lemma core_card (a : ℕ) : (core a).card = a+1 := by
  simp [core, extra]

private lemma extra_not_core (a : ℕ) : extra a ∉ core a := by simp [core]

private lemma core_mem (a : ℕ) (i : Fin (a + 2)) : i ∈ core a ↔ i ≠ extra a := by
  simp [core, ne_comm]

private lemma erased_card (a : ℕ) (j : Fin (a + 2)) (hj : j ∈ core a) :
    ((core a).erase j).card = a := by
  rw [Finset.card_erase_of_mem hj, core_card]
  omega

private lemma expectation (a : ℕ) (ε : ℝ) (f : Finset (Fin (a + 2)) → ℝ) :
    (∑ T, rareLaw a ε T * f T) =
      ε * f {extra a} + ((a : ℝ)-1)*ε*f (core a) +
      ((1-(a : ℝ)*ε)/((a : ℝ)+1)) * ∑ j ∈ core a, f ((core a).erase j) := by
  classical
  simp only [rareLaw, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp [ite_mul]
  · simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [ite_mul, Finset.mul_sum]

private lemma scalar_bounds {a : ℕ} (ha : 4 ≤ a) {ε : ℝ}
    (hε : 0 < ε) (hεa : ε ≤ 1/(a : ℝ)) :
    0 < (a : ℝ) ∧ ε ≤ 1 ∧ (a : ℝ)*ε ≤ 1 ∧ 0 < (a : ℝ)-ε := by
  have h4 : (4 : ℝ) ≤ a := by exact_mod_cast ha
  have hap : (0 : ℝ) < a := by linarith
  have hprod : (a : ℝ)*ε ≤ 1 := by
    have h := (le_div_iff₀ hap).mp hεa
    nlinarith
  have he1 : ε ≤ 1 := by nlinarith
  exact ⟨hap, he1, hprod, by linarith⟩

private lemma total_mean (a : ℕ) (ε : ℝ) :
    (∑ T, rareLaw a ε T) = 1 ∧ mean (rareLaw a ε) = a := by
  have hp : (a : ℝ)+1 ≠ 0 := by positivity
  constructor
  · have h := expectation a ε (fun _ => 1)
    simpa [core_card] using (show (∑ T, rareLaw a ε T * 1) = 1 by
      rw [h]
      simp only [mul_one, Finset.sum_const, nsmul_eq_mul, core_card, Nat.cast_add,
        Nat.cast_one]
      field_simp
      <;> ring)
  · unfold mean
    rw [expectation]
    simp only [Finset.card_singleton, Nat.cast_one, mul_one, core_card, Nat.cast_add,
      Finset.sum_congr rfl (fun j hj => congrArg (fun n : ℕ => (n : ℝ)) (erased_card a j hj))]
    simp only [Finset.sum_const, nsmul_eq_mul, core_card, Nat.cast_add, Nat.cast_one]
    field_simp
    <;> ring

private lemma marginal_extra (a : ℕ) (ε : ℝ) :
    marginal (rareLaw a ε) (extra a) = ε := by
  unfold marginal
  have he : (∑ T, if extra a ∈ T then rareLaw a ε T else 0) =
      ∑ T, rareLaw a ε T * (if extra a ∈ T then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro T _
    split_ifs <;> simp
  rw [he]
  rw [expectation]
  simp [extra_not_core, Finset.mem_erase]

private lemma marginal_core (a : ℕ) (ε : ℝ) (i : Fin (a + 2)) (hi : i ∈ core a) :
    marginal (rareLaw a ε) i = ((a : ℝ)-ε)/((a : ℝ)+1) := by
  have hie : i ≠ extra a := (core_mem a i).mp hi
  have hp : (a : ℝ)+1 ≠ 0 := by positivity
  have hs : (∑ j ∈ core a, if i ∈ (core a).erase j then (1 : ℝ) else 0) = a := by
    have hf : (core a).filter (fun j => i ∈ (core a).erase j) = (core a).erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, hi, and_true]
      tauto
    rw [← Finset.sum_filter, hf]
    simp [erased_card a i hi]
  unfold marginal
  have he : (∑ T, if i ∈ T then rareLaw a ε T else 0) =
      ∑ T, rareLaw a ε T * (if i ∈ T then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro T _
    split_ifs <;> simp
  rw [he, expectation, hs]
  simp only [Finset.mem_singleton, hie, ↓reduceIte, mul_zero, hi, mul_one, zero_add]
  field_simp
  <;> ring

private lemma moment_extra (a : ℕ) (ε : ℝ) :
    moment (rareLaw a ε) (extra a) = ε := by
  unfold moment
  rw [expectation]
  simp [extra_not_core, Finset.mem_erase]

private lemma moment_core (a : ℕ) (ε : ℝ) (i : Fin (a + 2)) (hi : i ∈ core a) :
    moment (rareLaw a ε) i =
      ((a : ℝ)^3 + ε*(2*(a : ℝ)^3-2*(a : ℝ)-1))/((a : ℝ)+1) := by
  have hie : i ≠ extra a := (core_mem a i).mp hi
  have hp : (a : ℝ)+1 ≠ 0 := by positivity
  have hs : (∑ j ∈ core a,
      if i ∈ (core a).erase j then (((core a).erase j).card : ℝ)^2 else 0) =
      (a : ℝ)^3 := by
    have hf : (core a).filter (fun j => i ∈ (core a).erase j) = (core a).erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, hi, and_true]
      tauto
    rw [← Finset.sum_filter]
    have hc : ∀ j ∈ (core a).filter (fun j => i ∈ (core a).erase j),
        (((core a).erase j).card : ℝ)^2 = (a : ℝ)^2 := by
      intro j hj
      rw [erased_card a j (Finset.mem_filter.mp hj).1]
    rw [Finset.sum_congr rfl hc, hf]
    simp only [Finset.sum_const, nsmul_eq_mul, erased_card a i hi]
    ring
  unfold moment
  rw [expectation, hs]
  simp only [Finset.mem_singleton, hie, ↓reduceIte, mul_zero, hi, core_card,
    Nat.cast_add, Nat.cast_one, zero_add]
  field_simp
  <;> ring

private lemma shape_separation {a : ℕ} (ha : 4 ≤ a) :
    core a ≠ {extra a} ∧ ∀ j ∈ core a,
      (core a).erase j ≠ {extra a} ∧ (core a).erase j ≠ core a := by
  constructor
  · intro h
    have hc := congrArg Finset.card h
    simp only [core_card, Finset.card_singleton] at hc
    omega
  · intro j hj
    constructor
    · intro h
      have hc := congrArg Finset.card h
      rw [erased_card a j hj, Finset.card_singleton] at hc
      omega
    · exact Finset.erase_ne_self.mpr hj

private lemma displayed_masses {a : ℕ} (ha : 4 ≤ a) (ε : ℝ) :
    rareLaw a ε {extra a} = ε ∧
    rareLaw a ε (core a) = ((a : ℝ)-1)*ε ∧
    ∀ j ∈ core a, rareLaw a ε ((core a).erase j) =
      (1-(a : ℝ)*ε)/((a : ℝ)+1) := by
  obtain ⟨hc, hd⟩ := shape_separation ha
  refine ⟨?_, ?_, ?_⟩
  · simp only [rareLaw, ite_true, Ne.symm hc, ↓reduceIte, add_zero]
    have hz : (∑ j ∈ core a, if {extra a} = (core a).erase j then
        (1-(a : ℝ)*ε)/((a : ℝ)+1) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [(hd j hj).1.symm]
    rw [hz, add_zero]
  · simp only [rareLaw, hc, ↓reduceIte, ite_true, zero_add]
    have hz : (∑ j ∈ core a, if core a = (core a).erase j then
        (1-(a : ℝ)*ε)/((a : ℝ)+1) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [(hd j hj).2.symm]
    rw [hz, add_zero]
  · intro j hj
    simp only [rareLaw, (hd j hj).1, (hd j hj).2, ↓reduceIte, zero_add]
    have he : ∀ k ∈ core a, ((core a).erase j = (core a).erase k) ↔ j = k := by
      intro k _
      exact Finset.erase_inj (core a) hj
    simp_rw [Finset.sum_congr rfl (fun k hk => if_congr (he k hk) rfl rfl)]
    simp [hj]

private lemma lawful {a : ℕ} (ha : 4 ≤ a) {ε : ℝ}
    (hε : 0 < ε) (hεa : ε ≤ 1/(a : ℝ)) :
    (∀ T, 0 ≤ rareLaw a ε T) ∧ rareLaw a ε ∅ = 0 ∧
      ∀ i, 0 < marginal (rareLaw a ε) i := by
  obtain ⟨hap, he1, hprod, hdiff⟩ := scalar_bounds ha hε hεa
  have h4 : (4 : ℝ) ≤ a := by exact_mod_cast ha
  have hc : 0 ≤ (1-(a : ℝ)*ε)/((a : ℝ)+1) := div_nonneg (by linarith) (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · intro T
    unfold rareLaw
    apply add_nonneg (add_nonneg ?_ ?_) (Finset.sum_nonneg fun j _ => ?_)
    · split_ifs <;> positivity
    · split_ifs
      · exact mul_nonneg (by linarith) hε.le
      · exact le_rfl
    · split_ifs
      · exact hc
      · exact le_rfl
  · have hn : (∅ : Finset (Fin (a + 2))) ≠ core a := by
      intro h
      have := congrArg Finset.card h
      simp only [Finset.card_empty, core_card] at this
      omega
    have hd : ∀ j ∈ core a, (∅ : Finset (Fin (a + 2))) ≠ (core a).erase j := by
      intro j hj h
      have := congrArg Finset.card h
      rw [Finset.card_empty, erased_card a j hj] at this
      omega
    simp only [rareLaw, Finset.empty_ne_singleton, ↓reduceIte, hn, zero_add]
    exact Finset.sum_eq_zero fun j hj => if_neg (hd j hj)
  · intro i
    by_cases hi : i = extra a
    · subst i
      simpa [marginal_extra] using hε
    · rw [marginal_core a ε i ((core_mem a i).mpr hi)]
      exact div_pos hdiff (by positivity)

private lemma energy_formula {a : ℕ} (ha : 4 ≤ a) {ε : ℝ}
    (hε : 0 < ε) (hεa : ε ≤ 1/(a : ℝ)) :
    2 * energy (rareLaw a ε) =
      ((a : ℝ)+1)^2*((a : ℝ)^3+ε*(2*(a : ℝ)^3-2*(a : ℝ)-1))/
        ((a : ℝ)-ε)^2 + 1/ε := by
  have hp : (a : ℝ)+1 ≠ 0 := by positivity
  have hd := (scalar_bounds ha hε hεa).2.2.2.ne'
  have he := hε.ne'
  have hs : (∑ i ∈ core a, moment (rareLaw a ε) i / marginal (rareLaw a ε) i ^ 2) =
      ((a : ℝ)+1)^2*((a : ℝ)^3+ε*(2*(a : ℝ)^3-2*(a : ℝ)-1))/
        ((a : ℝ)-ε)^2 := by
    calc
      _ = ∑ i ∈ core a,
          (((a : ℝ)^3 + ε*(2*(a : ℝ)^3-2*(a : ℝ)-1))/((a : ℝ)+1)) /
            (((a : ℝ)-ε)/((a : ℝ)+1))^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [moment_core a ε i hi, marginal_core a ε i hi]
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, core_card, Nat.cast_add, Nat.cast_one]
        field_simp
        <;> ring
  unfold energy
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin (a + 2)))
    (fun i => moment (rareLaw a ε) i / marginal (rareLaw a ε) i ^ 2)
    (Finset.mem_univ (extra a))
  rw [show (∑ i, moment (rareLaw a ε) i / marginal (rareLaw a ε) i ^ 2) =
      (∑ i ∈ core a, moment (rareLaw a ε) i / marginal (rareLaw a ε) i ^ 2) +
        moment (rareLaw a ε) (extra a) / marginal (rareLaw a ε) (extra a)^2 from hsplit.symm]
  rw [hs, moment_extra, marginal_extra]
  field_simp
  <;> ring

private lemma gap_formula {a : ℕ} (ha : 4 ≤ a) {ε : ℝ}
    (hε : 0 < ε) (hεa : ε ≤ 1/(a : ℝ)) :
    2 * (energy (rareLaw a ε) - benchmark (a+1) a) =
      1/ε + ((a : ℝ)+1)^2*ε*
        (2*(a : ℝ)^3+2*(a : ℝ)^2-2*(a : ℝ)-1-(a : ℝ)*ε)/((a : ℝ)-ε)^2 := by
  obtain ⟨hap, _, _, hdiff⟩ := scalar_bounds ha hε hεa
  have he := hε.ne'
  have hd := hdiff.ne'
  have hab := hap.ne'
  rw [mul_sub, energy_formula ha hε hεa]
  unfold benchmark
  push_cast
  field_simp
  <;> ring

/-- Two vertices are linked when a positive-mass type contains both. -/
def supportLink {V : Type*} [Fintype V] [DecidableEq V]
    (x : Finset V → ℝ) (u v : V) : Prop :=
  ∃ T, 0 < x T ∧ u ∈ T ∧ v ∈ T

/-- Incidence-hypergraph connectivity, including paths of length zero. -/
def supportConnected {V : Type*} [Fintype V] [DecidableEq V]
    (x : Finset V → ℝ) (u v : V) : Prop :=
  Relation.ReflTransGen (supportLink x) u v

private lemma support_shapes (a : ℕ) (ε : ℝ) (T : Finset (Fin (a + 2)))
    (hT : 0 < rareLaw a ε T) :
    T = {extra a} ∨ T = core a ∨ ∃ j ∈ core a, T = (core a).erase j := by
  by_contra h
  push_neg at h
  have hz : rareLaw a ε T = 0 := by
    simp only [rareLaw, h.1, h.2.1, ↓reduceIte, zero_add]
    exact Finset.sum_eq_zero fun j hj => if_neg (h.2.2 j hj)
  linarith

private lemma support_components {a : ℕ} (ha : 4 ≤ a) {ε : ℝ}
    (hε : 0 < ε) (u v : Fin (a + 2)) :
    supportConnected (rareLaw a ε) u v ↔ (u = extra a ↔ v = extra a) := by
  have hcore : 0 < rareLaw a ε (core a) := by
    rw [(displayed_masses ha ε).2.1]
    have h4 : (4 : ℝ) ≤ a := by exact_mod_cast ha
    exact mul_pos (by linarith) hε
  have invariant : ∀ u v : Fin (a + 2), supportLink (rareLaw a ε) u v →
      (u = extra a ↔ v = extra a) := by
    intro i j ⟨T, hT, hi, hj⟩
    rcases support_shapes a ε T hT with ht | ht | ⟨k, hk, ht⟩
    · subst T
      simpa only [Finset.mem_singleton] using (show i = extra a ↔ j = extra a by
        simp_all)
    · subst T
      have hi' := (core_mem a i).mp hi
      have hj' := (core_mem a j).mp hj
      simp [hi', hj']
    · subst T
      have hi' := (core_mem a i).mp (Finset.mem_of_mem_erase hi)
      have hj' := (core_mem a j).mp (Finset.mem_of_mem_erase hj)
      simp [hi', hj']
  constructor
  · intro h
    induction h with
    | refl => rfl
    | @tail b c _ hbc ih => exact ih.trans (invariant b c hbc)
  · intro h
    by_cases hu : u = extra a
    · have hv := h.mp hu
      subst u
      subst v
      exact .refl
    · have hv : v ≠ extra a := fun hv => hu (h.mpr hv)
      exact Relation.ReflTransGen.single ⟨core a, hcore,
        (core_mem a u).mpr hu, (core_mem a v).mpr hv⟩

private lemma gap_positive {a : ℕ} (ha : 4 ≤ a) {ε : ℝ}
    (hε : 0 < ε) (hεa : ε ≤ 1/(a : ℝ)) :
    0 < energy (rareLaw a ε) - benchmark (a+1) a := by
  obtain ⟨hap, _, hprod, hdiff⟩ := scalar_bounds ha hε hεa
  have h4 : (4 : ℝ) ≤ a := by exact_mod_cast ha
  have hc : 0 < 2*(a : ℝ)^3+2*(a : ℝ)^2-2*(a : ℝ)-1-(a : ℝ)*ε := by
    have hs : (a : ℝ)^2 ≥ 16 := by nlinarith
    have ht : (a : ℝ)^3 ≥ 16*(a : ℝ) := by nlinarith
    nlinarith
  have hpos : 0 < 1/ε + ((a : ℝ)+1)^2*ε*
      (2*(a : ℝ)^3+2*(a : ℝ)^2-2*(a : ℝ)-1-(a : ℝ)*ε)/((a : ℝ)-ε)^2 := by
    positivity
  rw [← gap_formula ha hε hεa] at hpos
  linarith

def scale (a : ℕ) : ℝ := (a : ℝ) ^ (3 / 2 : ℝ)

def epsilon (a : ℕ) : ℝ := 1 / (Real.sqrt 2 * scale a)

private lemma scale_square (a : ℕ) : scale a ^ 2 = (a : ℝ)^3 := by
  unfold scale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg a)]
  norm_num

private lemma epsilon_admissible {a : ℕ} (ha : 4 ≤ a) :
    0 < epsilon a ∧ epsilon a ≤ 1/(a : ℝ) := by
  have h4 : (4 : ℝ) ≤ a := by exact_mod_cast ha
  have hp : 0 < scale a := Real.rpow_pos_of_pos (by linarith) _
  have hs : 1 ≤ Real.sqrt 2 := by
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  have hscale : (a : ℝ) ≤ scale a :=
    Real.self_le_rpow_of_one_le (by linarith) (by norm_num)
  constructor
  · unfold epsilon
    positivity
  · apply one_div_le_one_div_of_le (by linarith : (0 : ℝ) < a)
    change (a : ℝ) ≤ Real.sqrt 2 * scale a
    nlinarith

private lemma epsilon_zero : Tendsto epsilon atTop (𝓝 0) := by
  have hn : Tendsto (fun a : ℕ => (a : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3/2)).comp hn
  have he : epsilon = fun a : ℕ => (1 / Real.sqrt 2) * (a : ℝ)^(-(3/2 : ℝ)) := by
    funext a
    simp [epsilon, scale, Real.rpow_neg (Nat.cast_nonneg a), div_eq_mul_inv, mul_comm]
  rw [he]
  simpa using tendsto_const_nhds.mul ht

private lemma normalized_gap {a : ℕ} (ha : 4 ≤ a) :
    (energy (rareLaw a (epsilon a)) - benchmark (a+1) a) / scale a =
      1 / Real.sqrt 2 +
      (1 + 1/(a : ℝ))^2 *
        (2 + 2/(a : ℝ) - 2/(a : ℝ)^2 - 1/(a : ℝ)^3 - epsilon a/(a : ℝ)^2) /
        (2 * Real.sqrt 2 * (1 - epsilon a/(a : ℝ))^2) := by
  obtain ⟨hepos, heub⟩ := epsilon_admissible ha
  have hap := (scalar_bounds ha hepos heub).1
  have hd := (scalar_bounds ha hepos heub).2.2.2.ne'
  have hpa : scale a ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hap _)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hss : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hps := scale_square a
  have hg := gap_formula ha hepos heub
  have hz : 1 - epsilon a/(a : ℝ) ≠ 0 := by
    have heq : 1 - epsilon a/(a : ℝ) = ((a : ℝ)-epsilon a)/(a : ℝ) := by
      field_simp
    rw [heq]
    exact div_ne_zero hd hap.ne'
  have hequot : epsilon a / scale a = 1/(Real.sqrt 2*(a : ℝ)^3) := by
    unfold epsilon
    rw [div_div, mul_assoc, ← pow_two, hps]
  have hfirst : (1/epsilon a)/scale a = Real.sqrt 2 := by
    unfold epsilon
    field_simp
  have hn1 : (1+1/(a : ℝ))^2 = ((a : ℝ)+1)^2/(a : ℝ)^2 := by
    field_simp
    <;> ring
  have hn2 : 2+2/(a : ℝ)-2/(a : ℝ)^2-1/(a : ℝ)^3-epsilon a/(a : ℝ)^2 =
      (2*(a : ℝ)^3+2*(a : ℝ)^2-2*(a : ℝ)-1-(a : ℝ)*epsilon a)/(a : ℝ)^3 := by
    field_simp
    <;> ring
  have hn3 : (1-epsilon a/(a : ℝ))^2 = ((a : ℝ)-epsilon a)^2/(a : ℝ)^2 := by
    field_simp
    <;> ring
  apply (mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num))
  rw [← mul_div_assoc, hg, add_div, hfirst, hn1, hn2, hn3]
  calc
    _ = Real.sqrt 2 + ((a : ℝ)+1)^2 *
        (2*(a : ℝ)^3+2*(a : ℝ)^2-2*(a : ℝ)-1-(a : ℝ)*epsilon a)/
          ((a : ℝ)-epsilon a)^2 * (epsilon a / scale a) := by ring
    _ = _ := by
      rw [hequot]
      field_simp
      ring_nf
      rw [hss]
      ring

private lemma first_limit :
    Tendsto (fun a : ℕ =>
      (energy (rareLaw a (epsilon a)) - benchmark (a+1) a) / scale a)
      atTop (𝓝 (Real.sqrt 2)) := by
  have hn : Tendsto (fun a : ℕ => (a : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun a : ℕ => 1/(a : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hn
  have hi2 : Tendsto (fun a : ℕ => 1/(a : ℝ)^2) atTop (𝓝 0) := by
    simpa using hi.pow 2
  have hi3 : Tendsto (fun a : ℕ => 1/(a : ℝ)^3) atTop (𝓝 0) := by
    simpa using hi.pow 3
  have he2 : Tendsto (fun a : ℕ => epsilon a/(a : ℝ)^2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using epsilon_zero.mul hi2
  have he1 : Tendsto (fun a : ℕ => epsilon a/(a : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using epsilon_zero.mul hi
  have hnum : Tendsto (fun a : ℕ =>
      (1+1/(a : ℝ))^2 *
        (2+2/(a : ℝ)-2/(a : ℝ)^2-1/(a : ℝ)^3-epsilon a/(a : ℝ)^2))
      atTop (𝓝 2) := by
    have h1 := ((tendsto_const_nhds (x := (1 : ℝ))).add hi).pow 2
    have h2 := ((((tendsto_const_nhds (x := (2 : ℝ))).add (hi.const_mul 2)).sub
      (hi2.const_mul 2)).sub hi3).sub he2
    simpa [div_eq_mul_inv] using h1.mul h2
  have hden : Tendsto (fun a : ℕ =>
      2*Real.sqrt 2*(1-epsilon a/(a : ℝ))^2) atTop (𝓝 (2*Real.sqrt 2)) := by
    convert ((tendsto_const_nhds.sub he1).pow 2).const_mul (2*Real.sqrt 2)
      using 1 <;> simp
  have h := (tendsto_const_nhds (x := 1/Real.sqrt 2)).add (hnum.div hden (by positivity))
  have hs : 1/Real.sqrt 2 + 2/(2*Real.sqrt 2) = Real.sqrt 2 := by
    have hss := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hsp : 0 < Real.sqrt 2 := by positivity
    field_simp
    nlinarith
  rw [hs] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with a ha
  exact (normalized_gap ha).symm

private lemma second_limit :
    Tendsto (fun a : ℕ =>
      (energy (rareLaw a (epsilon a)) - benchmark (a+1) a) / scale (a+1))
      atTop (𝓝 (Real.sqrt 2)) := by
  have hr : Tendsto (fun a : ℕ => scale a / scale (a+1)) atTop (𝓝 1) := by
    have h := (tendsto_natCast_div_add_atTop (1 : ℝ)).rpow_const
      (p := (3/2 : ℝ)) (Or.inr (by norm_num))
    have heq : (fun a : ℕ => ((a : ℝ)/((a : ℝ)+1))^(3/2 : ℝ)) =
        fun a : ℕ => scale a/scale (a+1) := by
      funext a
      rw [Real.div_rpow (Nat.cast_nonneg a) (by positivity)]
      simp only [scale, Nat.cast_add, Nat.cast_one]
    rw [heq] at h
    simpa only [Real.one_rpow] using h
  have h := first_limit.mul hr
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with a ha
  have hap := (scalar_bounds ha (epsilon_admissible ha).1 (epsilon_admissible ha).2).1
  have hp : scale a ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hap _)
  have hp1 : scale (a+1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  field_simp

private lemma quadratic_limit :
    Tendsto (fun a : ℕ =>
      (energy (rareLaw a (epsilon a)) - benchmark (a+1) a) / ((a : ℝ)+1)^2)
      atTop (𝓝 0) := by
  have hn : Tendsto (fun a : ℕ => (a : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hi := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp hn
  have h := second_limit.mul hi
  simp only [mul_zero] at h
  apply h.congr'
  apply Eventually.of_forall
  intro a
  dsimp only [Function.comp_def]
  have hz : (0 : ℝ) < (a : ℝ)+1 := by positivity
  have he : scale (a+1) * (((a : ℝ)+1)^(1/2 : ℝ)) = ((a : ℝ)+1)^2 := by
    unfold scale
    push_cast
    rw [← Real.rpow_add hz]
    norm_num
  rw [Real.rpow_neg hz.le]
  rw [div_eq_mul_inv, mul_assoc, ← mul_inv, he]
  rfl

private lemma rational_epsilon {b : ℕ} (hb : 2 ≤ b) :
    epsilon (2*b^2) = 1/(4*(b : ℝ)^3) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hap : (0 : ℝ) < (2*b^2 : ℕ) := by positivity
  have hs : Real.sqrt (2*b^2 : ℕ) = Real.sqrt 2 * (b : ℝ) := by
    push_cast
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (Nat.cast_nonneg b)]
  have hp : scale (2*b^2) = (2*b^2 : ℕ) * Real.sqrt (2*b^2 : ℕ) := by
    unfold scale
    rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hap,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  unfold epsilon
  rw [hp, hs]
  push_cast
  have hss : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  ring_nf
  rw [hss]
  ring

/-- The proposed bound quantifies over the actual subset law, at every finite
hub number and every mean in the complete adjacent-cardinality interval. -/
def UniformQuadraticGap : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (r s : ℕ), 5 ≤ r → r+1 ≤ s →
    ∀ x : Profile (Fin s),
      (r : ℝ)-1 ≤ mean x.mass → mean x.mass ≤ r →
        c*(r : ℝ)^2 ≤ energy x.mass - benchmark r (mean x.mass)

private lemma no_uniform : ¬ UniformQuadraticGap := by
  rintro ⟨c, hc, hbound⟩
  have hevent : ∀ᶠ a : ℕ in atTop,
      (energy (rareLaw a (epsilon a)) - benchmark (a+1) a) / ((a : ℝ)+1)^2 < c :=
    quadratic_limit.eventually (gt_mem_nhds hc)
  obtain ⟨a, hsmall, ha⟩ := (hevent.and (eventually_ge_atTop (4 : ℕ))).exists
  obtain ⟨hepos, heub⟩ := epsilon_admissible ha
  obtain ⟨hnonneg, hempty, hpositive⟩ := lawful ha hepos heub
  let x : Profile (Fin (a+2)) :=
    ⟨rareLaw a (epsilon a), hnonneg, (total_mean a (epsilon a)).1, hempty, hpositive⟩
  have hm : mean x.mass = a := (total_mean a (epsilon a)).2
  have hb := hbound (a+1) (a+2) (by omega) (by omega) x
    (by rw [hm]; push_cast; linarith) (by rw [hm]; push_cast; linarith)
  rw [hm] at hb
  have hsq : 0 < ((a : ℝ)+1)^2 := by positivity
  have hsmall' := (div_lt_iff₀ hsq).mp hsmall
  push_cast at hb
  linarith

/-- All finite conclusions concern one array on all subsets of the source labels.
Zero mass at the empty subset identifies it with the law on nonempty subsets. -/
structure FiniteFacts (a : ℕ) (ε : ℝ) (x : Finset (Fin (a+2)) → ℝ) : Prop where
  nonneg : ∀ T, 0 ≤ x T
  total : ∑ T, x T = 1
  empty : x ∅ = 0
  positive : ∀ i, 0 < marginal x i
  mean_eq : mean x = a
  masses : x {extra a} = ε ∧ x (core a) = ((a : ℝ)-1)*ε ∧
    ∀ j ∈ core a, x ((core a).erase j) = (1-(a : ℝ)*ε)/((a : ℝ)+1)
  other_zero : ∀ T, T ≠ {extra a} → T ≠ core a →
    (∀ j ∈ core a, T ≠ (core a).erase j) → x T = 0
  y_extra : marginal x (extra a) = ε
  y_core : ∀ i ∈ core a, marginal x i = ((a : ℝ)-ε)/((a : ℝ)+1)
  w_extra : moment x (extra a) = ε
  w_core : ∀ i ∈ core a, moment x i =
    ((a : ℝ)^3+ε*(2*(a : ℝ)^3-2*(a : ℝ)-1))/((a : ℝ)+1)
  components : ∀ u v, supportConnected x u v ↔ (u = extra a ↔ v = extra a)
  core_nonempty : (core a).Nonempty
  energy_eq : 2*energy x =
    ((a : ℝ)+1)^2*((a : ℝ)^3+ε*(2*(a : ℝ)^3-2*(a : ℝ)-1))/((a : ℝ)-ε)^2+1/ε
  gap_eq : 2*(energy x-benchmark (a+1) a) =
    1/ε+((a : ℝ)+1)^2*ε*
      (2*(a : ℝ)^3+2*(a : ℝ)^2-2*(a : ℝ)-1-(a : ℝ)*ε)/((a : ℝ)-ε)^2
  gap_pos : 0 < energy x-benchmark (a+1) a
  endpoint : ε = 1/(a : ℝ) → ∀ j ∈ core a, x ((core a).erase j) = 0
  native_expectation : ∀ f : Finset (Fin (a+2)) → ℝ,
    (∑ T : {T : Finset (Fin (a+2)) // T.Nonempty}, x T.val * f T.val) =
      ∑ T, x T * f T

private lemma finite_facts {a : ℕ} (ha : 4 ≤ a) {ε : ℝ}
    (hε : 0 < ε) (hεa : ε ≤ 1/(a : ℝ)) : FiniteFacts a ε (rareLaw a ε) := by
  obtain ⟨hn, he, hp⟩ := lawful ha hε hεa
  refine ⟨hn, (total_mean a ε).1, he, hp, (total_mean a ε).2,
    displayed_masses ha ε, ?_, marginal_extra a ε, marginal_core a ε,
    moment_extra a ε, moment_core a ε, support_components ha hε, ?_,
    energy_formula ha hε hεa, gap_formula ha hε hεa, gap_positive ha hε hεa, ?_, ?_⟩
  · intro T h1 h2 h3
    simp only [rareLaw, h1, h2, ↓reduceIte, zero_add]
    exact Finset.sum_eq_zero fun j hj => if_neg (h3 j hj)
  · exact Finset.card_pos.mp (by rw [core_card]; omega)
  · intro he j hj
    rw [(displayed_masses ha ε).2.2 j hj, he]
    have hap := (scalar_bounds ha hε hεa).1.ne'
    field_simp
    <;> ring
  · intro f
    have hs := Fintype.sum_subtype_add_sum_subtype
      (fun T : Finset (Fin (a+2)) => T.Nonempty) (fun T => rareLaw a ε T * f T)
    have hz : (∑ T : {T : Finset (Fin (a+2)) // ¬T.Nonempty},
        rareLaw a ε T.val * f T.val) = 0 := by
      apply Finset.sum_eq_zero
      intro T _
      have ht : T.val = ∅ := Finset.not_nonempty_iff_eq_empty.mp T.property
      rw [ht, he, zero_mul]
    rw [hz, add_zero] at hs
    exact hs

/-- The complete family assertion, including both natural-index asymptotics and
the quantified obstruction for actual laws. -/
def TheoremClaims (F : (a : ℕ) → ℝ → Finset (Fin (a+2)) → ℝ) : Prop :=
  (∀ (a : ℕ), 4 ≤ a → ∀ ε : ℝ, 0 < ε → ε ≤ 1/(a : ℝ) → FiniteFacts a ε (F a ε)) ∧
  (∀ (a : ℕ), 4 ≤ a → 0 < epsilon a ∧ epsilon a ≤ 1/(a : ℝ)) ∧
  Tendsto (fun a : ℕ => (energy (F a (epsilon a))-benchmark (a+1) a)/scale a)
    atTop (𝓝 (Real.sqrt 2)) ∧
  Tendsto (fun a : ℕ => (energy (F a (epsilon a))-benchmark (a+1) a)/scale (a+1))
    atTop (𝓝 (Real.sqrt 2)) ∧
  (∀ b : ℕ, 2 ≤ b → epsilon (2*b^2) = 1/(4*(b : ℝ)^3)) ∧
  ¬ UniformQuadraticGap

/-- The full genuine-profile family: all admissible real parameters, exact
formulas, both components and limits, and failure of a uniform quadratic gap. -/
theorem result : TheoremClaims rareLaw := by
  exact ⟨fun _ ha _ he heub => finite_facts ha he heub,
    fun _ ha => epsilon_admissible ha, first_limit, second_limit,
    fun _ hb => rational_epsilon hb, no_uniform⟩

end D5.S3.Combinatorics.Probability.CdsoRareHubProfile
