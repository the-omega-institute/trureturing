/- GID: D5/S3/Zeros/LeeYang/TreePairSource
   generality: G
   mirror-B: D5/B/S3/Zeros/LeeYang/TreePairSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Zeros/LeeYang/TreePairSource.exact_source_coefficient; premises=D5/S3/Zeros/LeeYang/TreePairSource.endpoint_factor_one,D5/S3/Zeros/LeeYang/TreePairSource.endpoint_factor_two,D5/S3/Zeros/LeeYang/TreePairSource.edge_factor_two,D5/S3/Zeros/LeeYang/TreePairSource.edge_factor_three
   digest: Formal generator coefficient extraction and the exact physical scalar. -/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import D5.S3.Zeros.LeeYang.TreePairStability
import Mathlib.Algebra.Polynomial.Homogenize

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace FiolArbitraryTreePair

def totalKey {E : Type*} [Fintype E] (n : E → ℕ) : ℕ →₀ ℕ :=
  ∑ e, Finsupp.single (2 * n e - 1) 1

def pairKey (e : ℕ) : ℕ →₀ ℕ := Finsupp.single 5 2 + Finsupp.single 3 (e - 2)

def selectedEdges {E : Type*} [Fintype E] (n : E → ℕ) : Finset E :=
  univ.filter fun e => n e = 3

def selectedTotals {E : Type*} [DecidableEq E] (A : Finset E) (e : E) : ℕ :=
  if e ∈ A then 3 else 2

theorem totalKey_apply {E : Type*} [Fintype E] (n : E → ℕ) (j : ℕ) :
    totalKey n j = ∑ e, if 2 * n e - 1 = j then 1 else 0 := by
  classical
  simp [totalKey, Finsupp.single_apply]

theorem key_forces_pair_totals {E : Type*} [Fintype E] (n : E → ℕ)
    (hn : ∀ e, 2 ≤ n e) (hk : totalKey n = pairKey (Fintype.card E)) :
    (∀ e, n e = 2 ∨ n e = 3) ∧ (selectedEdges n).card = 2 := by
  classical
  have hallowed (e : E) : n e = 2 ∨ n e = 3 := by
    by_contra he
    have h3 : 2 * n e - 1 ≠ 3 := by have := hn e; omega
    have h5 : 2 * n e - 1 ≠ 5 := by have := hn e; omega
    have hz : totalKey n (2 * n e - 1) = 0 := by
      rw [hk]
      simp [pairKey, Finsupp.single_apply, h3, h5, Ne.symm h3, Ne.symm h5]
    have hle : 1 ≤ totalKey n (2 * n e - 1) := by
      rw [totalKey_apply]
      have h := Finset.single_le_sum
        (f := fun i : E => if 2 * n i - 1 = 2 * n e - 1 then 1 else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
      simpa using h
    omega
  refine ⟨hallowed, ?_⟩
  have h5 := congrArg (fun k : ℕ →₀ ℕ => k 5) hk
  rw [totalKey_apply] at h5
  have he : (∑ e, if 2 * n e - 1 = 5 then 1 else 0) = (selectedEdges n).card := by
    simp only [selectedEdges, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro e _
    have : (2 * n e - 1 = 5) ↔ n e = 3 := by have := hn e; omega
    simp [this]
  rw [he] at h5
  simpa [pairKey] using h5

theorem selected_totals_key {E : Type*} [Fintype E] [DecidableEq E]
    (A : Finset E) (hA : A.card = 2) :
    totalKey (selectedTotals A) = pairKey (Fintype.card E) := by
  classical
  ext j
  rw [totalKey_apply]
  by_cases h5 : j = 5
  · subst j
    simp [selectedTotals, pairKey, Finsupp.single_apply, ← Finset.card_filter, hA]
  · by_cases h3 : j = 3
    · subst j
      have hc : (univ.filter fun e : E => e ∉ A).card = Fintype.card E - 2 := by
        have hc := Finset.card_sdiff_of_subset (show A ⊆ (univ : Finset E) by simp)
        simpa [Finset.sdiff_eq_filter, hA] using hc
      have ht (e : E) : (if 2 * selectedTotals A e - 1 = 3 then 1 else 0) =
          (if e ∈ A then 0 else 1) := by
        by_cases he : e ∈ A <;> simp [selectedTotals, he]
      simp only [ht, pairKey, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by norm_num : (3 : ℕ) ≠ 5), zero_add]
      simpa only [Finset.card_filter, ite_not] using hc
    · have hterm (e : E) : (if 2 * selectedTotals A e - 1 = j then 1 else 0) = 0 := by
        unfold selectedTotals
        split_ifs <;> simp_all
      simp [hterm, pairKey, Finsupp.single_apply, h5, h3, Ne.symm h5, Ne.symm h3]

theorem selected_totals_inverse {E : Type*} [Fintype E] [DecidableEq E]
    (n : E → ℕ) (hn : ∀ e, n e = 2 ∨ n e = 3) :
    selectedTotals (selectedEdges n) = n := by
  funext e
  rcases hn e with h | h <;> simp [selectedTotals, selectedEdges, h]

/- The coefficient is extracted from the actual formal-generator monomials.
   The split/vertex polynomial is a coefficient payload, not a premise about roots. -/
def boundedTotals {E : Type*} [Fintype E] [DecidableEq E] (M : ℕ) : Finset (E → ℕ) :=
  Fintype.piFinset fun _ => Finset.Icc 2 M

def formalSource {E R : Type*} [Fintype E] [DecidableEq E] [CommSemiring R]
    (M : ℕ) (payload : (E → ℕ) → R) :
    MvPolynomial ℕ R :=
  ∑ n ∈ boundedTotals M, MvPolynomial.monomial (totalKey n) (payload n)

theorem formal_coefficient_support {E R : Type*} [Fintype E] [DecidableEq E] [CommSemiring R]
    (M : ℕ) (payload : (E → ℕ) → R) :
    (formalSource M payload).coeff (pairKey (Fintype.card E)) =
      ∑ n ∈ (boundedTotals M).filter (fun n => totalKey n = pairKey (Fintype.card E)), payload n := by
  classical
  simp [formalSource, MvPolynomial.coeff_monomial, Finset.sum_filter,
    eq_comm (a := pairKey (Fintype.card E))]

theorem formal_pair_coefficient {E R : Type*} [Fintype E] [DecidableEq E] [CommSemiring R]
    (M : ℕ) (hM : 3 ≤ M) (payload : (E → ℕ) → R) :
    (formalSource M payload).coeff (pairKey (Fintype.card E)) =
      ∑ A ∈ (univ : Finset E).powersetCard 2, payload (selectedTotals A) := by
  classical
  rw [formal_coefficient_support]
  have hb (n : E → ℕ) (hn : n ∈ (boundedTotals M).filter
      (fun n => totalKey n = pairKey (Fintype.card E))) :
      (∀ e, n e = 2 ∨ n e = 3) ∧ (selectedEdges n).card = 2 := by
    apply key_forces_pair_totals n _ (Finset.mem_filter.mp hn).2
    have hm := (Finset.mem_filter.mp hn).1
    simp only [boundedTotals, Fintype.mem_piFinset, Finset.mem_Icc] at hm
    exact fun e => (hm e).1
  apply Finset.sum_bij (fun n _ => selectedEdges n)
  · intro n hn
    exact Finset.mem_powersetCard.mpr ⟨by simp, (hb n hn).2⟩
  · intro n hn m hm hnm
    rw [← selected_totals_inverse n (hb n hn).1,
      ← selected_totals_inverse m (hb m hm).1, hnm]
  · intro A hA
    have hcard := (Finset.mem_powersetCard.mp hA).2
    refine ⟨selectedTotals A, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨?_, selected_totals_key A hcard⟩
      simp only [boundedTotals, Fintype.mem_piFinset, Finset.mem_Icc]
      intro e
      unfold selectedTotals
      split_ifs <;> omega
    · ext e
      simp [selectedEdges, selectedTotals]
  · intro n hn
    rw [selected_totals_inverse n (hb n hn).1]

def endpointFactor (k : ℕ) : ℝ :=
  (Nat.factorial (2 * k) : ℝ) /
    ((Nat.factorial (k - 1) : ℝ) * (Nat.factorial k : ℝ))

def vertexRatio (d r : ℕ) : ℝ :=
  if r = 0 then 1 else if r = 1 then d / 3 else (d : ℝ) * (d + 1) / 12

theorem endpoint_factor_one : endpointFactor 1 = 2 := by norm_num [endpointFactor]
theorem endpoint_factor_two : endpointFactor 2 = 12 := by norm_num [endpointFactor]
theorem edge_factor_two : (Nat.choose 4 2 : ℝ) * endpointFactor 1 * endpointFactor 1 = 24 := by
  rw [endpoint_factor_one]
  norm_num [Nat.choose]
theorem edge_factor_three : (Nat.choose 6 2 : ℝ) * endpointFactor 1 * endpointFactor 2 = 360 := by
  rw [endpoint_factor_one,endpoint_factor_two]
  norm_num [Nat.choose]

theorem vertex_factorial_ratio (d r : ℕ) (hd : 1 ≤ d) (hr : r ≤ 2) :
    (Nat.factorial (d + r - 1) : ℝ) / (Nat.factorial (r + 2) : ℝ) =
      (Nat.factorial (d - 1) : ℝ) / 2 * vertexRatio d r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  interval_cases r <;> simp [vertexRatio, Nat.factorial_succ] <;> push_cast <;> ring

theorem source_scalar (e aut : ℕ) (D : ℝ) (he : 2 ≤ e) (haut : aut ≠ 0) :
    ((-2 : ℝ) ^ e * (-1 : ℝ) ^ (2 * e + 2) /
      (9 * 2 ^ (e - 2) * aut)) *
      (24 ^ (e - 2) * 360 ^ 2 * D / 2 ^ (e + 1)) =
      50 * (-1 : ℝ) ^ e * 12 ^ e * D / aut := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
  have h24 : (24 : ℝ) ^ k = 2 ^ k * 12 ^ k := by rw [← mul_pow]; norm_num
  have hn2 : (-2 : ℝ) ^ k = (-1 : ℝ) ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
  have hs : (-1 : ℝ) ^ (2 * (2 + k) + 2) = 1 := by
    rw [show 2 * (2 + k) + 2 = 2 * (k + 3) by omega, pow_mul]
    norm_num
  simp only [show 2 + k - 2 = k by omega, hs]
  rw [show 2 + k + 1 = k + 3 by omega, pow_add, show 2 + k = k + 2 by omega,
    pow_add, pow_add]
  rw [h24, hn2]
  have h2 : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have ha : (aut : ℝ) ≠ 0 := by exact_mod_cast haut
  field_simp
  <;> ring

def sourceSplits {E : Type*} [Fintype E] [DecidableEq E] (n : E → ℕ) : Finset (E → ℕ) :=
  Fintype.piFinset fun e => Finset.Icc 1 (n e - 1)

def sourceMass {V E : Type*} [Fintype E] [DecidableEq V]
    (src tgt : E → V) (n k : E → ℕ) (v : V) : ℕ :=
  (∑ e, if src e = v then k e else 0) +
  (∑ e, if tgt e = v then n e - k e else 0)

def sourceDegree {V E : Type*} [Fintype E] [DecidableEq V]
    (src tgt : E → V) (v : V) : ℕ :=
  (∑ e, if src e = v then 1 else 0) + (∑ e, if tgt e = v then 1 else 0)

def sourceVertex {V E : Type*} [Fintype E] [DecidableEq V]
    (src tgt : E → V) (n k : E → ℕ) (v : V) : Polynomial ℝ :=
  Polynomial.C ((Nat.factorial (sourceMass src tgt n k v - 1) : ℝ) /
    (Nat.factorial (sourceMass src tgt n k v - sourceDegree src tgt v + 2) : ℝ)) *
  Polynomial.C ((∏ e, if src e = v then endpointFactor (k e) else 1) *
    (∏ e, if tgt e = v then endpointFactor (n e - k e) else 1)) *
  (1 + Polynomial.C ((-1 : ℝ) ^ sourceDegree src tgt v) *
    Polynomial.X ^ sourceMass src tgt n k v)

def rawSourcePayload {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (src tgt : E → V) (aut : ℕ) (n : E → ℕ) : Polynomial ℝ :=
  Polynomial.C (((-2 : ℝ) ^ Fintype.card E / aut) *
    ∏ e, (-1 : ℝ) ^ n e / n e) *
  ∑ k ∈ sourceSplits n,
    Polynomial.C (∏ e, (Nat.choose (2 * n e) (2 * k e) : ℝ)) *
      ∏ v, sourceVertex src tgt n k v

/- Literal all-vertex equation (2.19), with a finite cutoff only on edge totals.
   Stabilization of the requested coefficient must be proved for every cutoff >=3. -/
def allVertexSource {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (src tgt : E → V) (aut M : ℕ) :
    MvPolynomial ℕ (Polynomial ℝ) := formalSource M (rawSourcePayload src tgt aut)

theorem allVertexSource_coefficient {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (src tgt : E → V) (aut M : ℕ) (hM : 3 ≤ M) :
    (allVertexSource src tgt aut M).coeff (pairKey (Fintype.card E)) =
      ∑ A ∈ (univ : Finset E).powersetCard 2,
        rawSourcePayload src tgt aut (selectedTotals A) :=
  formal_pair_coefficient M hM _

theorem vertexRatio_pos (d r : ℕ) (hd : 1 ≤ d) (hr : r ≤ 2) :
    0 < vertexRatio d r := by
  interval_cases r <;> simp [vertexRatio] <;> positivity

theorem selected_product {E R : Type*} [Fintype E] [DecidableEq E] [CommMonoid R]
    (A : Finset E) (hA : A.card = 2) (f : ℕ → R) :
    (∏ e, f (selectedTotals A e)) = f 3 ^ 2 * f 2 ^ (Fintype.card E - 2) := by
  have hc : (univ.filter fun e : E => e ∉ A).card = Fintype.card E - 2 := by
    have hc := Finset.card_sdiff_of_subset (show A ⊆ (univ : Finset E) by simp)
    simpa [Finset.sdiff_eq_filter, hA] using hc
  simp only [selectedTotals, apply_ite, Finset.prod_ite, Finset.prod_const]
  simpa [hA, hc]

theorem selected_edge_factor (n k : ℕ) (hn : n = 2 ∨ n = 3)
    (hk : k ∈ Finset.Icc 1 (n - 1)) :
    (Nat.choose (2 * n) (2 * k) : ℝ) * endpointFactor k * endpointFactor (n - k) =
      if n = 3 then 360 else 24 := by
  rcases hn with rfl | rfl
  · have : k = 1 := by simp only [Finset.mem_Icc] at hk; omega
    subst k
    simpa using edge_factor_two
  · have : k = 1 ∨ k = 2 := by simp only [Finset.mem_Icc] at hk; omega
    rcases this with rfl | rfl
    · simpa using edge_factor_three
    · have hs : (Nat.choose 6 4 : ℝ) * endpointFactor 2 * endpointFactor 1 =
          (Nat.choose 6 2 : ℝ) * endpointFactor 1 * endpointFactor 2 := by
        norm_num [Nat.choose]
        ring
      simpa using hs.trans edge_factor_three

theorem selected_split_edge_product {E : Type*} [Fintype E] [DecidableEq E]
    (A : Finset E) (hA : A.card = 2) (k : E → ℕ)
    (hk : k ∈ sourceSplits (selectedTotals A)) :
    (∏ e, (Nat.choose (2 * selectedTotals A e) (2 * k e) : ℝ) *
      endpointFactor (k e) * endpointFactor (selectedTotals A e - k e)) =
        24 ^ (Fintype.card E - 2) * 360 ^ 2 := by
  have hm : ∀ e, k e ∈ Finset.Icc 1 (selectedTotals A e - 1) := by
    simpa only [sourceSplits, Fintype.mem_piFinset] using hk
  have he (e : E) := selected_edge_factor (selectedTotals A e) (k e)
    (by unfold selectedTotals; split_ifs <;> simp) (hm e)
  simp_rw [he]
  have hp := selected_product A hA (fun n => if n = 3 then (360 : ℝ) else 24)
  simpa [mul_comm] using hp

theorem vertex_endpoints_product {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] (src tgt : E → V) (f g : E → ℝ) :
    (∏ v, (∏ e, if src e = v then f e else 1) *
      (∏ e, if tgt e = v then g e else 1)) = ∏ e, f e * g e := by
  rw [Finset.prod_mul_distrib, Finset.prod_comm, Finset.prod_comm (f := fun v e =>
    if tgt e = v then g e else 1)]
  simp [eq_comm, Finset.prod_mul_distrib]

theorem selected_totals_sum {E : Type*} [Fintype E] [DecidableEq E]
    (A : Finset E) (hA : A.card = 2) :
    (∑ e, selectedTotals A e) = 2 * Fintype.card E + 2 := by
  have he (e : E) : selectedTotals A e = 2 + (if e ∈ A then 1 else 0) := by
    unfold selectedTotals
    split_ifs <;> rfl
  simp_rw [he, Finset.sum_add_distrib]
  have hc : (∑ e : E, if e ∈ A then 1 else 0) = A.card := by simp
  rw [hc, hA]
  simp [mul_comm]

theorem sourceMass_total {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (src tgt : E → V) (n k : E → ℕ) (hk : ∀ e, k e ≤ n e) :
    (∑ v, sourceMass src tgt n k v) = ∑ e, n e := by
  unfold sourceMass
  rw [Finset.sum_add_distrib, Finset.sum_comm,
    Finset.sum_comm (f := fun v e => if tgt e = v then n e - k e else 0)]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  exact Nat.add_sub_of_le (hk e)

end FiolArbitraryTreePair

open scoped BigOperators
open Finset

namespace FiolArbitraryTreePair

private theorem ordered_pair_fibre {E : Type*} [Fintype E] [DecidableEq E]
    (u v : E) (huv : u ≠ v) :
    ((univ : Finset E).offDiag.filter fun p => ({p.1,p.2} : Finset E) = {u,v}) =
      {(u,v),(v,u)} := by
  ext ⟨a,b⟩
  simp only [mem_filter, mem_offDiag, mem_univ, true_and, mem_insert, mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hab, he⟩
    have ha : a = u ∨ a = v := by
      have h : a ∈ ({a,b} : Finset E) := by simp
      rw [he] at h
      simpa using h
    have hb : b = u ∨ b = v := by
      have h : b ∈ ({a,b} : Finset E) := by simp
      rw [he] at h
      simpa using h
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> simp [huv, Ne.symm huv, Finset.pair_comm]

/- Each unordered pair is visited exactly twice by the ordered distinct-pair sum. -/
theorem sum_ordered_distinct_twice {E R : Type*} [Fintype E] [DecidableEq E]
    [CommRing R] (F : Finset E → R) :
    (∑ p ∈ (univ : Finset E).offDiag, F {p.1,p.2}) =
      2 * ∑ A ∈ (univ : Finset E).powersetCard 2, F A := by
  have hm (p : E × E) (hp : p ∈ (univ : Finset E).offDiag) :
      ({p.1,p.2} : Finset E) ∈ (univ : Finset E).powersetCard 2 := by
    refine Finset.mem_powersetCard.mpr ⟨by simp, ?_⟩
    exact Finset.card_pair (Finset.mem_offDiag.mp hp).2.2
  have hs := Finset.sum_fiberwise_of_maps_to' hm F
  have hf (A : Finset E) (hA : A ∈ (univ : Finset E).powersetCard 2) :
      (∑ p ∈ (univ : Finset E).offDiag with ({p.1,p.2} : Finset E) = A, F A) =
        2 * F A := by
    obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hA).2
    rw [ordered_pair_fibre u v huv]
    simp [huv, Ne.symm huv, two_mul]
  rw [Finset.sum_congr rfl hf, ← Finset.mul_sum] at hs
  exact hs.symm

end FiolArbitraryTreePair

open scoped BigOperators
open Finset Polynomial

namespace FiolArbitraryTreePair

section Choices
variable {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]

def edgeChoices (A : Finset E) : Finset (E → Bool) :=
  Fintype.piFinset fun e => if e ∈ A then univ else {false}

def choiceSplit (A : Finset E) (b : E → Bool) (e : E) : ℕ :=
  if e ∈ A ∧ b e = true then 2 else 1

def splitChoice (k : E → ℕ) (e : E) : Bool := decide (k e = 2)

def receiver (src tgt : E → V) (b : E → Bool) (e : E) : V :=
  if b e then src e else tgt e

def receivedCount (src tgt : E → V) (A : Finset E) (b : E → Bool) (v : V) : ℕ :=
  (A.filter fun e => receiver src tgt b e = v).card

theorem choice_mem_split (A : Finset E) (b : E → Bool) :
    choiceSplit A b ∈ sourceSplits (selectedTotals A) := by
  simp only [sourceSplits, Fintype.mem_piFinset, Finset.mem_Icc]
  intro e
  by_cases he : e ∈ A <;> cases hb : b e <;>
    simp [choiceSplit, selectedTotals, he, hb]

theorem split_range (A : Finset E) (k : E → ℕ)
    (hk : k ∈ sourceSplits (selectedTotals A)) (e : E) :
    (e ∈ A → k e = 1 ∨ k e = 2) ∧ (e ∉ A → k e = 1) := by
  have hm : k e ∈ Finset.Icc 1 (selectedTotals A e - 1) := by
    exact (Fintype.mem_piFinset.mp hk) e
  simp only [Finset.mem_Icc] at hm
  constructor
  · intro he
    simp [selectedTotals, he] at hm
    omega
  · intro he
    simp [selectedTotals, he] at hm
    omega

theorem splitChoice_mem (A : Finset E) (k : E → ℕ)
    (hk : k ∈ sourceSplits (selectedTotals A)) : splitChoice k ∈ edgeChoices A := by
  simp only [edgeChoices, Fintype.mem_piFinset]
  intro e
  by_cases he : e ∈ A
  · simp [he]
  · simp [he, splitChoice, (split_range A k hk e).2 he]

theorem choiceSplit_inverse (A : Finset E) (k : E → ℕ)
    (hk : k ∈ sourceSplits (selectedTotals A)) : choiceSplit A (splitChoice k) = k := by
  funext e
  by_cases he : e ∈ A
  · rcases (split_range A k hk e).1 he with h | h <;>
      simp [choiceSplit, splitChoice, he, h]
  · simp [choiceSplit, he, (split_range A k hk e).2 he]

theorem splitChoice_inverse (A : Finset E) (b : E → Bool) (hb : b ∈ edgeChoices A) :
    splitChoice (choiceSplit A b) = b := by
  funext e
  have hm := (Fintype.mem_piFinset.mp hb) e
  by_cases he : e ∈ A
  · cases h : b e <;> simp [choiceSplit, splitChoice, he, h]
  · have h : b e = false := by simpa [he] using hm
    simp [choiceSplit, splitChoice, he, h]

theorem sum_sourceSplits {R : Type*} [AddCommMonoid R]
    (A : Finset E) (f : (E → ℕ) → R) :
    (∑ k ∈ sourceSplits (selectedTotals A), f k) =
      ∑ b ∈ edgeChoices A, f (choiceSplit A b) := by
  apply Finset.sum_bij (fun k _ => splitChoice k)
  · exact fun k hk => splitChoice_mem A k hk
  · intro k hk l hl hkl
    rw [← choiceSplit_inverse A k hk, ← choiceSplit_inverse A l hl, hkl]
  · intro b hb
    exact ⟨choiceSplit A b, choice_mem_split A b, splitChoice_inverse A b hb⟩
  · intro k hk
    rw [choiceSplit_inverse A k hk]

def pairChoice (e f : E) (p q : Bool) (a : E) : Bool :=
  if a = e then p else if a = f then q else false

theorem pairChoice_mem (e f : E) (p q : Bool) :
    pairChoice e f p q ∈ edgeChoices {e,f} := by
  simp only [edgeChoices, Fintype.mem_piFinset]
  intro a
  by_cases h : a ∈ ({e,f} : Finset E)
  · simp [h]
  · have he : a ≠ e := by intro he; subst a; simp at h
    have hf : a ≠ f := by intro hf; subst a; simp at h
    simp [h, pairChoice, he, hf]

theorem pairChoice_inverse (e f : E) (b : E → Bool) (hb : b ∈ edgeChoices {e,f}) :
    pairChoice e f (b e) (b f) = b := by
  funext a
  unfold pairChoice
  split_ifs with he hf
  · exact congrArg b he.symm
  · exact congrArg b hf.symm
  · have hm := (Fintype.mem_piFinset.mp hb) a
    have h : b a = false := by simpa [he, hf] using hm
    exact h.symm

theorem pair_choice_sum {R : Type*} [AddCommMonoid R]
    (e f : E) (hef : e ≠ f) (F : (E → Bool) → R) :
    (∑ b ∈ edgeChoices {e,f}, F b) =
      ∑ p : Bool, ∑ q : Bool, F (pairChoice e f p q) := by
  have hprod : (∑ p : Bool × Bool, F (pairChoice e f p.1 p.2)) =
      ∑ p : Bool, ∑ q : Bool, F (pairChoice e f p q) := Fintype.sum_prod_type _
  rw [← hprod]
  apply Finset.sum_bij (fun b _ => (b e, b f))
  · exact fun _ _ => Finset.mem_univ _
  · intro b hb c hc hbc
    have he : b e = c e := congrArg Prod.fst hbc
    have hf : b f = c f := congrArg Prod.snd hbc
    rw [← pairChoice_inverse e f b hb, ← pairChoice_inverse e f c hc, he, hf]
  · intro p _
    refine ⟨pairChoice e f p.1 p.2, pairChoice_mem e f p.1 p.2, ?_⟩
    simp [pairChoice, hef, Ne.symm hef]
  · intro b hb
    rw [pairChoice_inverse e f b hb]

theorem receivedCount_le (src tgt : E → V) (A : Finset E) (b : E → Bool) (v : V) :
    receivedCount src tgt A b v ≤ A.card :=
  Finset.card_filter_le _ _

theorem sourceMass_choice (src tgt : E → V) (A : Finset E) (b : E → Bool) (v : V) :
    sourceMass src tgt (selectedTotals A) (choiceSplit A b) v =
      sourceDegree src tgt v + receivedCount src tgt A b v := by
  have he (e : E) :
      (if src e = v then choiceSplit A b e else 0) +
        (if tgt e = v then selectedTotals A e - choiceSplit A b e else 0) =
      (if src e = v then 1 else 0) + (if tgt e = v then 1 else 0) +
        (if e ∈ A ∧ receiver src tgt b e = v then 1 else 0) := by
    by_cases ha : e ∈ A <;> cases hb : b e <;>
      by_cases hs : src e = v <;> by_cases ht : tgt e = v <;>
      simp [choiceSplit, selectedTotals, receiver, ha, hb, hs, ht]
  have hs := congrArg (fun f : E → ℕ => ∑ e, f e) (funext he)
  simp only [Finset.sum_add_distrib] at hs
  unfold sourceMass sourceDegree receivedCount
  rw [hs]
  simp [Finset.card_filter, Finset.sum_filter, Finset.sum_ite_mem, ite_and, -Finset.sum_boole]

theorem sum_receivedCount [Fintype V] (src tgt : E → V) (A : Finset E) (b : E → Bool) :
    (∑ v, receivedCount src tgt A b v) = A.card := by
  simp only [receivedCount, Finset.card_filter]
  rw [Finset.sum_comm]
  simp [eq_comm]

def allocationWeight [Fintype V] (d : V → ℕ) (src tgt : E → V) (A : Finset E) (b : E → Bool) : ℝ :=
  ∏ v : V, vertexRatio (d v) (receivedCount src tgt A b v)

theorem receivedCount_pairChoice (src tgt : E → V) (e f : E) (hef : e ≠ f)
    (p q : Bool) (v : V) :
    receivedCount src tgt {e,f} (pairChoice e f p q) v =
      (if (if p then src e else tgt e) = v then 1 else 0) +
      (if (if q then src f else tgt f) = v then 1 else 0) := by
  simp [receivedCount, Finset.card_filter, receiver, pairChoice, hef, Ne.symm hef,
    -Finset.sum_boole]

theorem sourceVertex_choice (src tgt : E → V) (A : Finset E) (hA : A.card = 2)
    (b : E → Bool) (v : V) (hd : 1 ≤ sourceDegree src tgt v) :
    sourceVertex src tgt (selectedTotals A) (choiceSplit A b) v =
      C ((Nat.factorial (sourceDegree src tgt v - 1) : ℝ) / 2) *
      C (vertexRatio (sourceDegree src tgt v) (receivedCount src tgt A b v)) *
      C ((∏ e, if src e = v then endpointFactor (choiceSplit A b e) else 1) *
        (∏ e, if tgt e = v then
          endpointFactor (selectedTotals A e - choiceSplit A b e) else 1)) *
      vertexFactor (sourceDegree src tgt v) (receivedCount src tgt A b v) := by
  have hr : receivedCount src tgt A b v ≤ 2 := by
    simpa [hA] using receivedCount_le src tgt A b v
  unfold sourceVertex
  rw [sourceMass_choice]
  have hs : sourceDegree src tgt v + receivedCount src tgt A b v -
      sourceDegree src tgt v + 2 = receivedCount src tgt A b v + 2 := by omega
  rw [hs, vertex_factorial_ratio _ _ hd hr, map_mul]
  rfl

end Choices

abbrev PairPlacement (E : Type*) [Fintype E] [DecidableEq E] :=
  {A : Finset E // A ∈ (Finset.univ : Finset E).powersetCard 2}

abbrev PairAllocation (E : Type*) [Fintype E] [DecidableEq E] :=
  Σ A : PairPlacement E, {b : E → Bool // b ∈ edgeChoices A.val}

section Allocation
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def allocationIncrements (src tgt : E → V) (c : PairAllocation E) (v : V) : ℕ :=
  receivedCount src tgt c.1.val c.2.val v

def treeAllocationPolynomial (d : V → ℕ) (src tgt : E → V) : ℝ[X] :=
  allocationPolynomial d (allocationIncrements src tgt)
    (fun c => allocationWeight d src tgt c.1.val c.2.val)

theorem allocationIncrements_le_two (src tgt : E → V) (c : PairAllocation E) (v : V) :
    allocationIncrements src tgt c v ≤ 2 := by
  have hcard := (Finset.mem_powersetCard.mp c.1.property).2
  simpa only [allocationIncrements, hcard] using
    receivedCount_le src tgt c.1.val c.2.val v

theorem allocationIncrements_sum (src tgt : E → V) (c : PairAllocation E) :
    (∑ v, allocationIncrements src tgt c v) = 2 := by
  simp only [allocationIncrements]
  rw [sum_receivedCount]
  exact (Finset.mem_powersetCard.mp c.1.property).2

theorem allocationWeight_pos (d : V → ℕ) (src tgt : E → V)
    (hd : ∀ v, 1 ≤ d v) (c : PairAllocation E) :
    0 < allocationWeight d src tgt c.1.val c.2.val := by
  apply Finset.prod_pos
  intro v _
  exact vertexRatio_pos (d v) _ (hd v) (allocationIncrements_le_two src tgt c v)

def pairReceivedPolynomial (d : V → ℕ) (u v : V) : ℝ[X] :=
  ∏ w, C (vertexRatio (d w) ((if u = w then 1 else 0) + (if v = w then 1 else 0))) *
    vertexFactor (d w) ((if u = w then 1 else 0) + (if v = w then 1 else 0))

theorem sourceSplit_choice_polynomial (src tgt : E → V)
    (A : Finset E) (hA : A.card = 2) (b : E → Bool)
    (hd : ∀ v, 1 ≤ sourceDegree src tgt v) :
    C (∏ e, (Nat.choose (2 * selectedTotals A e) (2 * choiceSplit A b e) : ℝ)) *
      (∏ v, sourceVertex src tgt (selectedTotals A) (choiceSplit A b) v) =
    C (24 ^ (Fintype.card E - 2) * 360 ^ 2 *
      (∏ v, (Nat.factorial (sourceDegree src tgt v - 1) : ℝ)) / 2 ^ Fintype.card V) *
    (∏ v, C (vertexRatio (sourceDegree src tgt v) (receivedCount src tgt A b v)) *
      vertexFactor (sourceDegree src tgt v) (receivedCount src tgt A b v)) := by
  let base (v : V) : ℝ := (Nat.factorial (sourceDegree src tgt v - 1) : ℝ) / 2
  let endpoint (v : V) : ℝ :=
    (∏ e, if src e = v then endpointFactor (choiceSplit A b e) else 1) *
    (∏ e, if tgt e = v then endpointFactor (selectedTotals A e - choiceSplit A b e) else 1)
  have hb : (∏ v, base v) =
      (∏ v, (Nat.factorial (sourceDegree src tgt v - 1) : ℝ)) / 2 ^ Fintype.card V := by
    simp only [base, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  have hend : (∏ v, endpoint v) =
      (∏ e, endpointFactor (choiceSplit A b e)) *
        (∏ e, endpointFactor (selectedTotals A e - choiceSplit A b e)) := by
    rw [show (∏ v, endpoint v) =
      ∏ e, endpointFactor (choiceSplit A b e) *
        endpointFactor (selectedTotals A e - choiceSplit A b e) from
      vertex_endpoints_product src tgt _ _, Finset.prod_mul_distrib]
  have he := selected_split_edge_product A hA (choiceSplit A b) (choice_mem_split A b)
  simp only [Finset.prod_mul_distrib] at he
  have hc : (∏ e, (Nat.choose (2 * selectedTotals A e) (2 * choiceSplit A b e) : ℝ)) *
      (∏ v, base v) * (∏ v, endpoint v) =
      24 ^ (Fintype.card E - 2) * 360 ^ 2 *
        (∏ v, (Nat.factorial (sourceDegree src tgt v - 1) : ℝ)) / 2 ^ Fintype.card V := by
    rw [hb, hend, ← he]
    ring
  simp_rw [sourceVertex_choice src tgt A hA b _ (hd _)]
  change (C _ * ∏ v, C (base v) * C (vertexRatio (sourceDegree src tgt v)
      (receivedCount src tgt A b v)) * C (endpoint v) *
      vertexFactor (sourceDegree src tgt v) (receivedCount src tgt A b v)) = _
  calc
    _ = C ((∏ e, (Nat.choose (2 * selectedTotals A e) (2 * choiceSplit A b e) : ℝ)) *
        (∏ v, base v) * (∏ v, endpoint v)) *
      (∏ v, C (vertexRatio (sourceDegree src tgt v) (receivedCount src tgt A b v)) *
        vertexFactor (sourceDegree src tgt v) (receivedCount src tgt A b v)) := by
      simp only [map_mul, map_prod, Finset.prod_mul_distrib]
      ring
    _ = _ := by rw [hc]


theorem rawSourcePayload_choice (src tgt : E → V) (aut : ℕ) (haut : aut ≠ 0)
    (A : Finset E) (hA : A.card = 2) (he : 2 ≤ Fintype.card E)
    (hvertices : Fintype.card V = Fintype.card E + 1)
    (hd : ∀ v, 1 ≤ sourceDegree src tgt v) :
    rawSourcePayload src tgt aut (selectedTotals A) =
      C (50 * (-1 : ℝ) ^ Fintype.card E * 12 ^ Fintype.card E *
        (∏ v, (Nat.factorial (sourceDegree src tgt v - 1) : ℝ)) / aut) *
      ∑ b ∈ edgeChoices A,
        ∏ v, C (vertexRatio (sourceDegree src tgt v) (receivedCount src tgt A b v)) *
          vertexFactor (sourceDegree src tgt v) (receivedCount src tgt A b v) := by
  have hprod := selected_product A hA (fun n => (-1 : ℝ) ^ n / n)
  norm_num [div_pow] at hprod
  have hsign : (-1 : ℝ) ^ (2 * Fintype.card E + 2) = 1 := by
    rw [show 2 * Fintype.card E + 2 = 2 * (Fintype.card E + 1) by omega, pow_mul]
    norm_num
  have h2 : (2 : ℝ) ^ (Fintype.card E - 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  have ha : (aut : ℝ) ≠ 0 := by exact_mod_cast haut
  have hpref : ((-2 : ℝ) ^ Fintype.card E / aut) *
      (∏ e, (-1 : ℝ) ^ selectedTotals A e / selectedTotals A e) =
      (-2 : ℝ) ^ Fintype.card E * (-1 : ℝ) ^ (2 * Fintype.card E + 2) /
        (9 * 2 ^ (Fintype.card E - 2) * aut) := by
    rw [Finset.prod_div_distrib, hprod, hsign]
    field_simp
    <;> ring
  unfold rawSourcePayload
  rw [hpref, sum_sourceSplits]
  simp_rw [sourceSplit_choice_polynomial src tgt A hA _ hd]
  rw [← Finset.mul_sum, ← mul_assoc, ← map_mul, hvertices,
    source_scalar (Fintype.card E) aut _ he haut]


theorem treeAllocationPolynomial_sum (d : V → ℕ) (src tgt : E → V) :
    treeAllocationPolynomial d src tgt =
      ∑ A ∈ (univ : Finset E).powersetCard 2,
        ∑ b ∈ edgeChoices A,
          ∏ v, C (vertexRatio (d v) (receivedCount src tgt A b v)) *
            vertexFactor (d v) (receivedCount src tgt A b v) := by
  let G (A : Finset E) (b : E → Bool) : ℝ[X] :=
    ∏ v, C (vertexRatio (d v) (receivedCount src tgt A b v)) *
      vertexFactor (d v) (receivedCount src tgt A b v)
  simp only [treeAllocationPolynomial, allocationPolynomial, Fintype.sum_sigma,
    allocationWeight, allocationIncrements, map_prod, ← Finset.prod_mul_distrib]
  change (∑ A : PairPlacement E, ∑ b : {b : E → Bool // b ∈ edgeChoices A.val}, G A.val b.val) =
    ∑ A ∈ (univ : Finset E).powersetCard 2, ∑ b ∈ edgeChoices A, G A b
  calc
    _ = ∑ A : PairPlacement E, ∑ b ∈ edgeChoices A.val, G A.val b := by
      apply Finset.sum_congr rfl
      intro A _
      exact (Finset.sum_subtype (edgeChoices A.val) (fun _ => Iff.rfl) (G A.val)).symm
    _ = _ := (Finset.sum_subtype ((univ : Finset E).powersetCard 2)
      (fun _ => Iff.rfl) (fun A => ∑ b ∈ edgeChoices A, G A b)).symm

theorem treeAllocation_twice (d : V → ℕ) (src tgt : E → V) :
    2 * treeAllocationPolynomial d src tgt =
      ∑ p ∈ (univ : Finset E).offDiag,
        ∑ b : Bool, ∑ c : Bool,
          pairReceivedPolynomial d (if b then src p.1 else tgt p.1)
            (if c then src p.2 else tgt p.2) := by
  rw [treeAllocationPolynomial_sum]
  rw [← sum_ordered_distinct_twice]
  apply Finset.sum_congr rfl
  intro p hp
  have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
  rw [pair_choice_sum p.1 p.2 hne]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  simp only [pairReceivedPolynomial, receivedCount_pairChoice src tgt p.1 p.2 hne b c]



theorem exact_source_coefficient (src tgt : E → V) (aut M : ℕ) (haut : aut ≠ 0)
    (hM : 3 ≤ M) (he : 2 ≤ Fintype.card E)
    (hvertices : Fintype.card V = Fintype.card E + 1)
    (hd : ∀ v, 1 ≤ sourceDegree src tgt v) :
    (allVertexSource src tgt aut M).coeff (pairKey (Fintype.card E)) =
      C (50 * (-1 : ℝ) ^ Fintype.card E * 12 ^ Fintype.card E *
        (∏ v, (Nat.factorial (sourceDegree src tgt v - 1) : ℝ)) / aut) *
        treeAllocationPolynomial (sourceDegree src tgt) src tgt := by
  rw [allVertexSource_coefficient src tgt aut M hM, treeAllocationPolynomial_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  exact rawSourcePayload_choice src tgt aut haut A
    (Finset.mem_powersetCard.mp hA).2 he hvertices hd


theorem pairAllocation_nonempty (he : 2 ≤ Fintype.card E) : Nonempty (PairAllocation E) := by
  let e : E := (Fintype.equivFin E).symm ⟨0, by omega⟩
  let f : E := (Fintype.equivFin E).symm ⟨1, by omega⟩
  have hef : e ≠ f := by
    intro h
    have h' := congrArg (Fintype.equivFin E) h
    simp [e, f] at h'
  have hcard : ({e,f} : Finset E).card = 2 := Finset.card_pair hef
  have hmem : ({e,f} : Finset E) ∈ (univ : Finset E).powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨by simp, hcard⟩
  have hb : (fun _ : E => false) ∈ edgeChoices {e,f} := by
    simp only [edgeChoices, Fintype.mem_piFinset]
    intro a
    split_ifs <;> simp
  exact ⟨⟨⟨{e,f},hmem⟩,⟨fun _ => false,hb⟩⟩⟩

theorem treeAllocation_degree_multiplicity (d : V → ℕ) (src tgt : E → V)
    (he : 2 ≤ Fintype.card E) (hd : ∀ v, 1 ≤ d v)
    (hsum : (∑ v, d v) = 2 * Fintype.card E) :
    (treeAllocationPolynomial d src tgt).natDegree = 2 * Fintype.card E + 2 ∧
    treeAllocationPolynomial d src tgt ≠ 0 ∧
    (treeAllocationPolynomial d src tgt).leadingCoeff = (treeAllocationPolynomial d src tgt).coeff 0 ∧
    (treeAllocationPolynomial d src tgt).rootMultiplicity 1 = oddCount d ∧
    0 < (treeAllocationPolynomial d src tgt).coeff 0 := by
  letI : Nonempty (PairAllocation E) := pairAllocation_nonempty he
  let r := allocationIncrements src tgt
  let w (c : PairAllocation E) := allocationWeight d src tgt c.1.val c.2.val
  have hdp : ∀ v, 0 < d v := fun v => by have := hd v; omega
  have hw : ∀ c, 0 < w c := allocationWeight_pos d src tgt hd
  have hm (c : PairAllocation E) : (∑ v, (d v + r c v)) = 2 * Fintype.card E + 2 := by
    simp only [Finset.sum_add_distrib, r, allocationIncrements_sum, hsum]
  have hparity : Even (∑ v, d v) := ⟨Fintype.card E, by omega⟩
  have hp := allocation_degree_and_leading d r w (2 * Fintype.card E + 2) hdp hw hm hparity
  refine ⟨hp.1, hp.2.2, ?_, allocation_multiplicity_one d r w hdp hw, ?_⟩
  · change (allocationPolynomial d r w).leadingCoeff = (allocationPolynomial d r w).coeff 0
    rw [hp.2.1, allocation_constant d r w hdp]
  · rw [show treeAllocationPolynomial d src tgt = allocationPolynomial d r w from rfl,
      allocation_constant d r w hdp]
    exact Finset.sum_pos (fun c _ => hw c) Finset.univ_nonempty

end Allocation

end FiolArbitraryTreePair

open scoped BigOperators
open Finset Polynomial

namespace FiolArbitraryTreePair

section FullSource
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/- Index 0 is the second coupling and index 1 is the first coupling. -/
def sourceBinaryVertex (src tgt : E → V) (n k : E → ℕ) (v : V) :
    MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C ((Nat.factorial (sourceMass src tgt n k v - 1) : ℝ) /
    (Nat.factorial (sourceMass src tgt n k v - sourceDegree src tgt v + 2) : ℝ)) *
  MvPolynomial.C ((∏ e, if src e = v then endpointFactor (k e) else 1) *
    (∏ e, if tgt e = v then endpointFactor (n e - k e) else 1)) *
  (MvPolynomial.X 1 ^ sourceMass src tgt n k v +
    MvPolynomial.C ((-1 : ℝ) ^ sourceDegree src tgt v) *
      MvPolynomial.X 0 ^ sourceMass src tgt n k v)

def sourceBinaryPayload (src tgt : E → V) (aut : ℕ) (n : E → ℕ) :
    MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C (((-2 : ℝ) ^ Fintype.card E / aut) *
    ∏ e, (-1 : ℝ) ^ n e / n e) *
  ∑ k ∈ sourceSplits n,
    MvPolynomial.C (∏ e, (Nat.choose (2 * n e) (2 * k e) : ℝ)) *
      ∏ v, sourceBinaryVertex src tgt n k v

def fullVertexSource (src tgt : E → V) (aut M : ℕ) :
    MvPolynomial ℕ (MvPolynomial (Fin 2) ℝ) :=
  formalSource M (sourceBinaryPayload src tgt aut)

theorem sourceVertex_degree_le (src tgt : E → V) (n k : E → ℕ) (v : V) :
    (sourceVertex src tgt n k v).natDegree ≤ sourceMass src tgt n k v := by
  have hc (c : ℝ) (p : ℝ[X]) : (C c * p).natDegree ≤ p.natDegree := by
    exact (natDegree_mul_le).trans (by simp)
  have hx (c : ℝ) (m : ℕ) : (1 + C c * X ^ m : ℝ[X]).natDegree ≤ m := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · simp
    · exact (hc c _).trans (by simp)
  unfold sourceVertex
  rw [mul_assoc]
  exact (hc _ _).trans ((hc _ _).trans (hx _ _))

theorem sourceVertex_homogenize (src tgt : E → V) (n k : E → ℕ) (v : V) :
    (sourceVertex src tgt n k v).homogenize (sourceMass src tgt n k v) =
      sourceBinaryVertex src tgt n k v := by
  unfold sourceVertex sourceBinaryVertex
  rw [mul_assoc, homogenize_C_mul, homogenize_C_mul, homogenize_add,
    homogenize_one, homogenize_C_mul,
    homogenize_X_pow (le_refl (sourceMass src tgt n k v))]
  simp only [Nat.sub_self,pow_zero,mul_one,one_mul]
  ring

theorem selectedSourcePayload_homogenize (src tgt : E → V) (aut : ℕ)
    (A : Finset E) (hA : A.card = 2) :
    (rawSourcePayload src tgt aut (selectedTotals A)).homogenize (2 * Fintype.card E + 2) =
      sourceBinaryPayload src tgt aut (selectedTotals A) := by
  simp only [rawSourcePayload, sourceBinaryPayload, homogenize_C_mul, homogenize_finsetSum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkn (e : E) : k e ≤ selectedTotals A e := by
    have h := (Fintype.mem_piFinset.mp hk) e
    simp only [Finset.mem_Icc] at h
    omega
  have hm : (∑ v, sourceMass src tgt (selectedTotals A) k v) = 2 * Fintype.card E + 2 :=
    (sourceMass_total src tgt _ k hkn).trans (selected_totals_sum A hA)
  congr 1
  rw [← hm, homogenize_finsetProd (fun v _ => sourceVertex_degree_le src tgt _ k v)]
  simp only [sourceVertex_homogenize]

theorem full_source_coefficient_homogenize (src tgt : E → V) (aut M : ℕ) (hM : 3 ≤ M) :
    (fullVertexSource src tgt aut M).coeff (pairKey (Fintype.card E)) =
      ((allVertexSource src tgt aut M).coeff (pairKey (Fintype.card E))).homogenize
        (2 * Fintype.card E + 2) := by
  unfold fullVertexSource allVertexSource
  rw [formal_pair_coefficient M hM, formal_pair_coefficient M hM, homogenize_finsetSum]
  apply Finset.sum_congr rfl
  intro A hA
  exact (selectedSourcePayload_homogenize src tgt aut A
    (Finset.mem_powersetCard.mp hA).2).symm

theorem exact_full_source_coefficient (src tgt : E → V) (aut M : ℕ) (haut : aut ≠ 0)
    (hM : 3 ≤ M) (he : 2 ≤ Fintype.card E)
    (hvertices : Fintype.card V = Fintype.card E + 1)
    (hd : ∀ v, 1 ≤ sourceDegree src tgt v) :
    (fullVertexSource src tgt aut M).coeff (pairKey (Fintype.card E)) =
      MvPolynomial.C (50 * (-1 : ℝ) ^ Fintype.card E * 12 ^ Fintype.card E *
        (∏ v, (Nat.factorial (sourceDegree src tgt v - 1) : ℝ)) / aut) *
        (treeAllocationPolynomial (sourceDegree src tgt) src tgt).homogenize
          (2 * Fintype.card E + 2) := by
  rw [full_source_coefficient_homogenize src tgt aut M hM,
    exact_source_coefficient src tgt aut M haut hM he hvertices hd, homogenize_C_mul]

end FullSource
end FiolArbitraryTreePair
