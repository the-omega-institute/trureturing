/- GID: D5/S3/Combinatorics/Probability/ScalarOverlapObstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/ScalarOverlapObstruction
   mirror-E: none(waiver:symbolic-unbounded-family)
   anchors: []
   utility: none
   digest: A self-consistent scalar overlap law below the incidence benchmark has no joint array realization. -/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Finite scalar laws and their common-array incidence constraints. -/

open scoped BigOperators
noncomputable section
set_option autoImplicit false

namespace D5.S3.Combinatorics.Probability.ScalarOverlapObstruction

/-- All nonempty types, including those assigned zero mass. -/
abbrev Types (s : ℕ) := {T : Finset (Fin s) // T.Nonempty}

def marginal {s : ℕ} (p : Types s → ℝ) (i : Fin s) : ℝ :=
  ∑ T, if i ∈ T.val then p T else 0

structure NativeArray (s : ℕ) where
  mass : Types s → ℝ
  nonneg : ∀ T, 0 ≤ mass T
  normalized : ∑ T, mass T = 1
  positive : ∀ i, 0 < marginal mass i

def nativeK {s : ℕ} (T : Types s) : ℕ := T.val.card

def nativeU {s : ℕ} (x : NativeArray s) (T : Types s) : ℝ :=
  ∑ i ∈ T.val, 1 / marginal x.mass i

def nativeQ {s : ℕ} (x : NativeArray s) : ℝ :=
  ∑ T, x.mass T * (nativeK T : ℝ)

def nativeW {s : ℕ} (x : NativeArray s) (i : Fin s) : ℝ :=
  ∑ T, if i ∈ T.val then x.mass T * (nativeK T : ℝ)^2 else 0

def twoJ {s : ℕ} (x : NativeArray s) : ℝ :=
  ∑ i, nativeW x i / (marginal x.mass i)^2

def meanMin {ι : Type*} [Fintype ι] (p : ι → ℝ) (K : ι → ℕ) (k : ℕ) : ℝ :=
  ∑ i, p i * (min k (K i) : ℝ)

/-- Every truncated mean is computed from the one supplied finite law. -/
def Relaxed {ι : Type*} [Fintype ι] (s : ℕ) (q : ℝ)
    (p : ι → ℝ) (K : ι → ℕ) (U : ι → ℝ) : Prop :=
  0 < s ∧ (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
  (∀ i, 0 < p i → 1 ≤ K i ∧ K i ≤ s) ∧
  (∑ i, p i * (K i : ℝ) = q) ∧ (∑ i, p i * U i = (s : ℝ)) ∧
  ∀ i, 0 < p i → max (K i : ℝ) ((K i : ℝ)^2 / meanMin p K (K i)) ≤ U i

/-- Equality of joint finite pushforwards, tested against every real function of both coordinates. -/
def Induces {s : ℕ} {ι : Type*} [Fintype ι] (x : NativeArray s)
    (p : ι → ℝ) (K : ι → ℕ) (U : ι → ℝ) : Prop :=
  ∀ f : ℕ → ℝ → ℝ,
    (∑ T, x.mass T * f (nativeK T) (nativeU x T)) = ∑ i, p i * f (K i) (U i)

private lemma incidence {s : ℕ} (p : Types s → ℝ) (f : Fin s → ℝ) :
    (∑ T, p T * ∑ i ∈ T.val, f i) = ∑ i, marginal p i * f i := by
  classical
  calc
    _ = ∑ T, ∑ i : Fin s, (if i ∈ T.val then p T else 0) * f i := by
      apply Finset.sum_congr rfl
      intro T _
      simp [ite_mul, Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [marginal, Finset.sum_mul]

private lemma marginal_le_one {s : ℕ} (x : NativeArray s) (i : Fin s) :
    marginal x.mass i ≤ 1 := by
  classical
  rw [marginal, ← x.normalized]
  apply Finset.sum_le_sum
  intro T _
  split_ifs <;> simp_all [x.nonneg]

private lemma marginal_total {s : ℕ} (x : NativeArray s) :
    (∑ i, marginal x.mass i) = nativeQ x := by
  have h := incidence x.mass (fun _ => 1)
  simpa [nativeQ, nativeK] using h.symm

private lemma native_mean_u {s : ℕ} (x : NativeArray s) :
    (∑ T, x.mass T * nativeU x T) = (s : ℝ) := by
  rw [show (∑ T, x.mass T * nativeU x T) =
      ∑ i, marginal x.mass i * (1 / marginal x.mass i) from incidence _ _]
  simp [(x.positive _).ne']

private lemma overlap_budget {s : ℕ} (x : NativeArray s) (T : Types s) :
    (∑ i ∈ T.val, marginal x.mass i) ≤ meanMin x.mass nativeK (nativeK T) := by
  classical
  calc
    _ = ∑ i : Fin s, marginal x.mass i * (if i ∈ T.val then 1 else 0) := by simp
    _ = ∑ S, x.mass S * ∑ i ∈ S.val, (if i ∈ T.val then (1 : ℝ) else 0) :=
      (incidence x.mass _).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro S _
      apply mul_le_mul_of_nonneg_left _ (x.nonneg S)
      have h : (S.val ∩ T.val).card ≤ min T.val.card S.val.card :=
        le_min (Finset.card_le_card Finset.inter_subset_right)
          (Finset.card_le_card Finset.inter_subset_left)
      simpa [nativeK, ← Finset.sum_filter, Finset.filter_mem_eq_inter] using
        (Nat.cast_le (α := ℝ)).mpr h

private lemma reciprocal_bounds {s : ℕ} (x : NativeArray s) (T : Types s) :
    max (nativeK T : ℝ)
      ((nativeK T : ℝ)^2 / meanMin x.mass nativeK (nativeK T)) ≤ nativeU x T := by
  classical
  have hb : 0 < ∑ i ∈ T.val, marginal x.mass i :=
    Finset.sum_pos (fun i _ => x.positive i) T.property
  have hm := overlap_budget x T
  have hc := Finset.sq_sum_div_le_sum_sq_div T.val (fun _ => (1 : ℝ))
    (fun i _ => x.positive i)
  have hc' : (nativeK T : ℝ)^2 / (∑ i ∈ T.val, marginal x.mass i) ≤
      nativeU x T := by simpa [nativeK, nativeU] using hc
  apply max_le
  · calc
      _ = ∑ i ∈ T.val, (1 : ℝ) := by simp [nativeK]
      _ ≤ nativeU x T := by
        apply Finset.sum_le_sum
        intro i _
        exact (le_div_iff₀ (x.positive i)).2 (by simpa using marginal_le_one x i)
  · exact (div_le_div_of_nonneg_left (sq_nonneg _) hb hm).trans hc'

private lemma native_objective {s : ℕ} (x : NativeArray s) :
    (∑ T, x.mass T * ((nativeK T : ℝ) * nativeU x T ^ 2)) ≤ twoJ x := by
  classical
  have hj : twoJ x = ∑ T, x.mass T * ((nativeK T : ℝ)^2 *
      ∑ i ∈ T.val, (1 / marginal x.mass i)^2) := by
    unfold twoJ nativeW
    simp_rw [Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T _
    rw [Finset.mul_sum, Finset.mul_sum]
    simp [ite_div, div_pow, div_eq_mul_inv, mul_assoc]
  rw [hj]
  apply Finset.sum_le_sum
  intro T _
  apply mul_le_mul_of_nonneg_left _ (x.nonneg T)
  have h := Finset.sum_mul_sq_le_sq_mul_sq T.val (fun _ => (1 : ℝ))
    (fun i => 1 / marginal x.mass i)
  simp only [one_mul, one_pow, Finset.sum_const, smul_eq_mul, mul_one] at h
  have hk : 0 ≤ (nativeK T : ℝ) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left h hk
  simpa [nativeK, nativeU, pow_two, mul_assoc] using hh

private lemma native_bridge {s : ℕ} (hs : 0 < s) (x : NativeArray s) :
    Relaxed s (nativeQ x) x.mass nativeK (nativeU x) ∧
    (∑ i, marginal x.mass i) = nativeQ x ∧
    (∑ T, x.mass T * ((nativeK T : ℝ) * nativeU x T ^ 2)) ≤ twoJ x := by
  refine ⟨⟨hs, x.nonneg, x.normalized, ?_, rfl, native_mean_u x, ?_⟩,
    marginal_total x, native_objective x⟩
  · intro T _
    exact ⟨T.property.card_pos, le_trans (Finset.card_le_univ T.val) (by simp)⟩
  · intro T _
    exact reciprocal_bounds x T


def denominator (a : ℝ) : ℝ := 5*a^2-a+1

def weights (a : ℝ) : Fin 3 → ℝ := ![1/(5*a), 4/5, (a-1)/(5*a)]
def lawK (a : ℕ) : Fin 3 → ℕ := ![1, a, a+1]
def lawU (a : ℝ) : Fin 3 → ℝ :=
  ![(41*a^4+13*a^2+1)/(a*denominator a), 5*a^3/denominator a, (a+1)^2/a]

def objective {ι : Type*} [Fintype ι] (p : ι → ℝ) (K : ι → ℕ) (U : ι → ℝ) : ℝ :=
  ∑ i, p i * ((K i : ℝ)*U i^2)

def obstructionPolynomial (a : ℝ) : ℝ :=
  110*a^8-1697*a^7+58*a^6-949*a^5+56*a^4-211*a^3+24*a^2-18*a+2

def benchmark (a q : ℝ) : ℝ :=
  (a+1)^2*((3*a^2+3*a+1)*q-a*(a+1)*(2*a+1))/(2*q^2)

private lemma sum_three (f : Fin 3 → ℝ) : (∑ i, f i) = f 0 + f 1 + f 2 := by
  simp [Fin.sum_univ_succ]
  ring

private lemma law_data (a : ℕ) (ha : 16 ≤ a) :
    (∀ i, 0 < weights (a : ℝ) i) ∧
    (∑ i, weights (a : ℝ) i = 1) ∧
    (∑ i, weights (a : ℝ) i * (lawK a i : ℝ) = (a : ℝ)) ∧
    (∑ i, weights (a : ℝ) i * lawU (a : ℝ) i = (a+2 : ℕ)) ∧
    meanMin (weights (a : ℝ)) (lawK a) 1 = 1 ∧
    meanMin (weights (a : ℝ)) (lawK a) a = denominator (a : ℝ)/(5*a) ∧
    meanMin (weights (a : ℝ)) (lawK a) (a+1) = (a : ℝ) := by
  have ha1 : 1 ≤ a := by omega
  have hA : (16 : ℝ) ≤ a := by exact_mod_cast ha
  have hpos : 0 < (a : ℝ) := by linarith
  have hA1 : (1 : ℝ) ≤ a := by linarith
  have hn : (a : ℝ) ≠ 0 := ne_of_gt hpos
  have hM : 0 < denominator (a : ℝ) := by
    dsimp [denominator]
    nlinarith [sq_nonneg ((a : ℝ)-1)]
  have hMn := ne_of_gt hM
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> dsimp [weights]
    · positivity
    · norm_num
    · apply div_pos <;> linarith
  · rw [sum_three]
    dsimp [weights]
    field_simp
    <;> ring
  · rw [sum_three]
    simp only [weights, lawK, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.head_cons, Nat.cast_one, Nat.cast_add]
    field_simp
    <;> ring
  · rw [sum_three]
    norm_num only [weights, lawU, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.head_cons, Nat.cast_add, Nat.cast_ofNat]
    field_simp
    <;> dsimp [denominator] at * <;> ring
  · unfold meanMin
    rw [sum_three]
    simp [weights, lawK, min_eq_left hA1]
    field_simp
    <;> ring
  · unfold meanMin
    rw [sum_three]
    simp [weights, lawK, min_eq_right hA1]
    field_simp
    <;> dsimp [denominator] <;> ring
  · unfold meanMin
    rw [sum_three]
    simp [weights, lawK, min_eq_right (show 1 ≤ a+1 by omega),
      min_eq_right (show a ≤ a+1 by omega), Nat.cast_add]
    field_simp
    <;> ring


private lemma law_feasible (a : ℕ) (ha : 16 ≤ a) :
    Relaxed (a+2) (a : ℝ) (weights (a : ℝ)) (lawK a) (lawU (a : ℝ)) := by
  obtain ⟨hp, hn, hk, hu, hm1, hma, hmap⟩ := law_data a ha
  have hA : (16 : ℝ) ≤ a := by exact_mod_cast ha
  have hpos : 0 < (a : ℝ) := by linarith
  have hM : 0 < denominator (a : ℝ) := by
    dsimp [denominator]
    nlinarith [sq_nonneg ((a : ℝ)-1)]
  have hma_pos : 0 < denominator (a : ℝ)/(5*a) := by positivity
  have hma_le : denominator (a : ℝ)/(5*a) ≤ a := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 5*a)).2
    dsimp [denominator]
    nlinarith
  refine ⟨by omega, fun i => (hp i).le, hn, ?_, hk, hu, ?_⟩
  · intro i _
    fin_cases i <;> simp [lawK] <;> omega
  · intro i _
    fin_cases i
    · change max (1 : ℝ) (1^2 / meanMin (weights (a : ℝ)) (lawK a) 1) ≤
        (41*(a : ℝ)^4+13*(a : ℝ)^2+1)/((a : ℝ)*denominator (a : ℝ))
      rw [hm1]
      norm_num only [one_pow, div_one, max_self]
      apply (le_div_iff₀ (mul_pos hpos hM)).2
      have h1 : 0 < (a : ℝ)^3*(41*a-5) :=
        mul_pos (by positivity) (by linarith)
      have h2 : 0 < (a : ℝ)*(14*a-1) := mul_pos hpos (by linarith)
      dsimp [denominator]
      nlinarith
    · change max (a : ℝ) ((a : ℝ)^2 / meanMin (weights (a : ℝ)) (lawK a) a) ≤
        5*(a : ℝ)^3/denominator (a : ℝ)
      rw [hma]
      apply max_le
      · apply (le_div_iff₀ hM).2
        dsimp [denominator]
        nlinarith
      · apply le_of_eq
        field_simp
        <;> ring
    · change max ((a : ℝ)+1)
        (((a : ℝ)+1)^2 / meanMin (weights (a : ℝ)) (lawK a) (a+1)) ≤
          ((a : ℝ)+1)^2/(a : ℝ)
      rw [hmap]
      apply max_le
      · apply (le_div_iff₀ hpos).2
        nlinarith
      · exact le_rfl

private lemma polynomial_positive (a : ℝ) (ha : 16 ≤ a) :
    0 < obstructionPolynomial a := by
  have hpos : 0 < a := by linarith
  have h5 : 0 < a^5 := by positivity
  have h3 : 0 < a^3 := by positivity
  have hgroup : 0 < a^5*((110*a-1697)*a^2+(58*a-949)) := by
    have hfirst : 0 ≤ (110*a-1760)*a^2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have hsecond : 0 ≤ 58*a-928 := by linarith
    have hsq : 256 ≤ a^2 := by nlinarith
    apply mul_pos h5
    nlinarith
  have hthird : 0 < a^3*(56*a-211) := mul_pos h3 (by linarith)
  have hlast : 0 < 24*a^2-18*a+2 := by nlinarith [sq_nonneg (a-1)]
  dsimp [obstructionPolynomial]
  nlinarith [hgroup]

private lemma objective_formula (a : ℕ) (ha : 16 ≤ a) :
    objective (weights (a : ℝ)) (lawK a) (lawU (a : ℝ)) =
      (41*(a : ℝ)^4+13*(a : ℝ)^2+1)^2/(5*(a : ℝ)^3*denominator (a : ℝ)^2) +
      20*(a : ℝ)^7/denominator (a : ℝ)^2 +
      ((a : ℝ)-1)*((a : ℝ)+1)^5/(5*(a : ℝ)^3) ∧
    objective (weights (a : ℝ)) (lawK a) (lawU (a : ℝ)) - (a : ℝ)*(a+1)^2 =
      -obstructionPolynomial (a : ℝ)/(5*(a : ℝ)^2*denominator (a : ℝ)^2) := by
  have hA : (16 : ℝ) ≤ a := by exact_mod_cast ha
  have hpos : 0 < (a : ℝ) := by linarith
  have hM : 0 < denominator (a : ℝ) := by
    dsimp [denominator]
    nlinarith [sq_nonneg ((a : ℝ)-1)]
  have hn := ne_of_gt hpos
  have hm := ne_of_gt hM
  constructor <;> unfold objective <;> rw [sum_three] <;>
    simp only [weights, lawK, lawU, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.head_cons, Nat.cast_one, Nat.cast_add] <;>
    field_simp <;> dsimp [denominator, obstructionPolynomial] <;> ring


private lemma strict_reciprocal {s : ℕ} (x : NativeArray s) (T : Types s)
    (hproper : nativeK T < s) :
    (nativeK T : ℝ)^2 / nativeQ x < nativeU x T := by
  classical
  obtain ⟨i, hi, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show T.val.card < (Finset.univ : Finset (Fin s)).card by simpa using hproper)
  have hb : 0 < ∑ j ∈ T.val, marginal x.mass j :=
    Finset.sum_pos (fun j _ => x.positive j) T.property
  have hbudget : (∑ j ∈ T.val, marginal x.mass j) < nativeQ x := by
    rw [← marginal_total x]
    exact Finset.sum_lt_sum_of_subset (Finset.subset_univ T.val) hi hnot
      (x.positive i) (fun j _ _ => (x.positive j).le)
  have hk : 0 < (nativeK T : ℝ) := by
    exact_mod_cast T.property.card_pos
  have hc := Finset.sq_sum_div_le_sum_sq_div T.val (fun _ => (1 : ℝ))
    (fun j _ => x.positive j)
  have hc' : (nativeK T : ℝ)^2 / (∑ j ∈ T.val, marginal x.mass j) ≤ nativeU x T :=
    by simpa [nativeK, nativeU] using hc
  exact (div_lt_div_of_pos_left (sq_pos_of_pos hk) hb hbudget).trans_le hc'

private lemma nonrealizable (a : ℕ) (ha : 16 ≤ a) :
    ¬ ∃ x : NativeArray (a+2),
      Induces x (weights (a : ℝ)) (lawK a) (lawU (a : ℝ)) := by
  classical
  rintro ⟨x, hx⟩
  obtain ⟨hp, hn, hk, hu, hm1, hma, hmap⟩ := law_data a ha
  have hq : nativeQ x = (a : ℝ) := (hx (fun k _ => (k : ℝ))).trans hk
  let u : ℝ := ((a : ℝ)+1)^2/(a : ℝ)
  let f : ℕ → ℝ → ℝ := fun k v => if k = a+1 ∧ v = u then 1 else 0
  have hright : (∑ j, weights (a : ℝ) j * f (lawK a j) (lawU (a : ℝ) j)) =
      weights (a : ℝ) 2 := by
    rw [sum_three]
    have h1 : (1 : ℕ) ≠ a+1 := by omega
    have h2 : a ≠ a+1 := by omega
    simp [f, lawK, lawU, u, h1, h2]
  have hsum : 0 < ∑ T, x.mass T * f (nativeK T) (nativeU x T) := by
    rw [hx f, hright]
    exact hp 2
  have hex : ∃ T, 0 < x.mass T * f (nativeK T) (nativeU x T) := by
    by_contra h
    push_neg at h
    have hle : (∑ T, x.mass T * f (nativeK T) (nativeU x T)) ≤ 0 :=
      Finset.sum_nonpos (fun T _ => h T)
    linarith
  obtain ⟨T, hT⟩ := hex
  have hpair : nativeK T = a+1 ∧ nativeU x T = u := by
    by_contra h
    simp only [f, if_neg h, mul_zero] at hT
    exact (lt_irrefl 0 hT)
  have hstrict := strict_reciprocal x T (by rw [hpair.1]; omega)
  rw [hq, hpair.1, hpair.2] at hstrict
  norm_num only [Nat.cast_add, Nat.cast_one] at hstrict
  exact (lt_irrefl u hstrict)

private lemma mean_min_upper {s : ℕ} (x : NativeArray s) (k : ℕ) :
    meanMin x.mass nativeK k ≤ min (k : ℝ) (nativeQ x) := by
  apply le_min
  · calc
      _ ≤ ∑ T, x.mass T * (k : ℝ) := by
        apply Finset.sum_le_sum
        intro T _
        exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.min_le_left _ _))
          (x.nonneg T)
      _ = _ := by rw [← Finset.sum_mul, x.normalized, one_mul]
  · apply Finset.sum_le_sum
    intro T _
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.min_le_right _ _))
      (x.nonneg T)

/-- The native bridge includes the typewise overlap bounds, with no marginal floor. -/
def NativeBridge : Prop := ∀ (s : ℕ), 0 < s → ∀ x : NativeArray s,
  Relaxed s (nativeQ x) x.mass nativeK (nativeU x) ∧
  (∑ i, marginal x.mass i) = nativeQ x ∧
  objective x.mass nativeK (nativeU x) ≤ twoJ x ∧
  ∀ T : Types s,
    0 < (∑ i ∈ T.val, marginal x.mass i) ∧
    (∑ i ∈ T.val, marginal x.mass i) ≤ meanMin x.mass nativeK (nativeK T) ∧
    meanMin x.mass nativeK (nativeK T) ≤ min (nativeK T : ℝ) (nativeQ x) ∧
    (nativeK T : ℝ)^2/(∑ i ∈ T.val, marginal x.mass i) ≤ nativeU x T

private lemma native_bridge_full : NativeBridge := by
  intro s hs x
  obtain ⟨hf, hq, hv⟩ := native_bridge hs x
  refine ⟨hf, hq, hv, ?_⟩
  intro T
  have hc := Finset.sq_sum_div_le_sum_sq_div T.val (fun _ => (1 : ℝ))
    (fun i _ => x.positive i)
  exact ⟨Finset.sum_pos (fun i _ => x.positive i) T.property,
    overlap_budget x T, mean_min_upper x (nativeK T),
    by simpa [nativeK, nativeU] using hc⟩

/-- All clauses of the rational law, including its full joint native nonrealizability. -/
def Obstruction (a : ℕ) (U : Fin 3 → ℝ) : Prop :=
  (∀ i, 0 < weights (a : ℝ) i) ∧
  Relaxed (a+2) (a : ℝ) (weights (a : ℝ)) (lawK a) U ∧
  meanMin (weights (a : ℝ)) (lawK a) 1 = 1 ∧
  meanMin (weights (a : ℝ)) (lawK a) a = denominator (a : ℝ)/(5*a) ∧
  meanMin (weights (a : ℝ)) (lawK a) (a+1) = (a : ℝ) ∧
  objective (weights (a : ℝ)) (lawK a) U =
    (41*(a : ℝ)^4+13*(a : ℝ)^2+1)^2/(5*(a : ℝ)^3*denominator (a : ℝ)^2) +
    20*(a : ℝ)^7/denominator (a : ℝ)^2 +
    ((a : ℝ)-1)*((a : ℝ)+1)^5/(5*(a : ℝ)^3) ∧
  objective (weights (a : ℝ)) (lawK a) U - (a : ℝ)*(a+1)^2 =
    -obstructionPolynomial (a : ℝ)/(5*(a : ℝ)^2*denominator (a : ℝ)^2) ∧
  0 < obstructionPolynomial (a : ℝ) ∧
  objective (weights (a : ℝ)) (lawK a) U < (a : ℝ)*(a+1)^2 ∧
  (¬ ∃ x : NativeArray (a+2), Induces x (weights (a : ℝ)) (lawK a) U) ∧
  2*benchmark (a : ℝ) (a : ℝ) = (a : ℝ)*(a+1)^2

/-- The scalar constraints are feasible below the benchmark for every a at least sixteen,
while the full induced joint law has no native common-array realization. -/
theorem complete_theorem (a : ℕ) (ha : 16 ≤ a) :
    NativeBridge ∧ Obstruction a (lawU (a : ℝ)) := by
  have hA : (16 : ℝ) ≤ a := by exact_mod_cast ha
  have hpos : 0 < (a : ℝ) := by linarith
  have hM : 0 < denominator (a : ℝ) := by
    dsimp [denominator]
    nlinarith [sq_nonneg ((a : ℝ)-1)]
  obtain ⟨hp, hn, hk, hu, hm1, hma, hmap⟩ := law_data a ha
  obtain ⟨hv, hgap⟩ := objective_formula a ha
  have hpoly := polynomial_positive (a : ℝ) hA
  refine ⟨native_bridge_full, hp, law_feasible a ha, hm1, hma, hmap, hv, hgap,
    hpoly, ?_, nonrealizable a ha, ?_⟩
  · have hneg : -obstructionPolynomial (a : ℝ)/
        (5*(a : ℝ)^2*denominator (a : ℝ)^2) < 0 := by
      apply div_neg_of_neg_of_pos (neg_neg_of_pos hpoly)
      positivity
    linarith
  · dsimp [benchmark]
    field_simp
    <;> ring

#print axioms complete_theorem

end D5.S3.Combinatorics.Probability.ScalarOverlapObstruction
