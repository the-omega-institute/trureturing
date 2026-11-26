/- GID: D5/S3/Combinatorics/Graph/Incidence/FixedSizeCutVariance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Incidence/FixedSizeCutVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform fixed-size cut variance decomposes by unsigned vertex-edge incidence. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-! # Uniform fixed-size cut variance -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Incidence.FixedSizeCutVariance

namespace FixedCutCount

open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The indexed edges are the two-element subsets of the vertex population. -/
abbrev Edge (A : Type*) [Fintype A] [DecidableEq A] :=
  ↥((Finset.univ : Finset A).powersetCard 2)

/-- An edge crosses a cut if exactly one endpoint belongs to the selected side. -/
abbrev crossed (e : Edge A) (S : Finset A) : Prop :=
  (e.val ∩ S).card = 1

/-- The two crossing events are evaluated on the same uniform size-`m` cut. -/
noncomputable def jointProbability (m : ℕ) (e f : Edge A) : ℝ :=
  (((univ : Finset A).powersetCard m).filter (fun S => crossed e S ∧ crossed f S)).card /
    (((univ : Finset A).powersetCard m).card : ℝ)

/-- The population crossing probability for a single edge. -/
noncomputable def q (n m : ℕ) : ℝ :=
  2 * (m : ℝ) * ((n : ℝ) - m) / ((n : ℝ) * ((n : ℝ) - 1))

variable (m : ℕ)

private abbrev fits (inside outside S : Finset A) : Prop :=
  inside ⊆ S ∧ Disjoint S outside

-- First exclude the forced-out vertices, then count subsets containing the forced-in vertices.
private theorem card_pattern (inside outside : Finset A) (h : Disjoint inside outside)
    (hm : inside.card ≤ m) :
    (((univ : Finset A).powersetCard m).filter (fits inside outside)).card =
      (Fintype.card A - (inside.card + outside.card)).choose (m - inside.card) := by
  have hfilter :
      ((univ : Finset A).powersetCard m).filter (fits inside outside) =
        ((univ \ outside).powersetCard m).filter (inside ⊆ ·) := by
    ext S
    simp only [mem_filter, mem_powersetCard, subset_sdiff, subset_univ, true_and, fits]
    tauto
  rw [hfilter, card_filter_powersetCard_subset _ _ _ (subset_sdiff.mpr ⟨subset_univ _, h⟩) hm,
    card_sdiff_of_subset (subset_univ outside), card_univ, Nat.sub_sub, add_comm outside.card]

omit [Fintype A] [DecidableEq A] in
private theorem card_filter_or {s : Finset A} {p r : A → Prop}
    [DecidablePred p] [DecidablePred r] (h : ∀ a, p a → r a → False) :
    (s.filter (fun a => p a ∨ r a)).card = (s.filter p).card + (s.filter r).card := by
  classical
  rw [Finset.filter_or, card_union_of_disjoint]
  exact disjoint_left.mpr fun a hp hr => h a (mem_filter.mp hp).2 (mem_filter.mp hr).2

omit [Fintype A] in
private theorem pair_crosses_iff {a b : A} (hab : a ≠ b) (S : Finset A) :
    (({a, b} : Finset A) ∩ S).card = 1 ↔
      (a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S) := by
  rw [← filter_mem_eq_inter, filter_insert, filter_singleton]
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb, card_pair hab]

private theorem edge_card (e : Edge A) : e.val.card = 2 :=
  (mem_powersetCard.mp e.property).2

omit [Fintype A] in
private theorem edge_eq_pair_of_mem (s : Finset A) (hs : s.card = 2) (a : A) (ha : a ∈ s) :
    ∃ b, a ≠ b ∧ s = {a, b} := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hs
  simp only [mem_insert, mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨y, hxy, rfl⟩
  · exact ⟨x, hxy.symm, by ext z; simp [or_comm]⟩

/-- Equal edges have two crossing orientations. -/
private theorem card_joint_eq (e : Edge A) (hm : 1 ≤ m) :
    (((univ : Finset A).powersetCard m).filter
      (fun S => crossed e S ∧ crossed e S)).card =
      2 * (Fintype.card A - 2).choose (m - 1) := by
  obtain ⟨a, b, hab, he⟩ := card_eq_two.mp (edge_card e)
  have hfilter :
      ((univ : Finset A).powersetCard m).filter (fun S => crossed e S ∧ crossed e S) =
        ((univ : Finset A).powersetCard m).filter
          (fun S => fits {a} {b} S ∨ fits {b} {a} S) := by
    ext S
    simp [crossed, he, pair_crosses_iff hab, fits]
  rw [hfilter, card_filter_or (by simp [fits]; tauto),
    card_pattern m _ _ (by simp [hab]) (by simpa using hm),
    card_pattern m _ _ (by simp [hab.symm]) (by simpa using hm)]
  simp [two_mul]

/-- With a single common endpoint, either it alone or both other endpoints are selected. -/
private theorem card_joint_inter_one (e f : Edge A) (h : (e.val ∩ f.val).card = 1) (hm : 2 ≤ m) :
    (((univ : Finset A).powersetCard m).filter
      (fun S => crossed e S ∧ crossed f S)).card =
      (Fintype.card A - 2).choose (m - 1) := by
  obtain ⟨a, ha⟩ := card_eq_one.mp h
  have ham : a ∈ e.val ∩ f.val := by simp [ha]
  obtain ⟨b, hab, he⟩ := edge_eq_pair_of_mem e.val (edge_card e) a (mem_inter.mp ham).1
  obtain ⟨c, hac, hf⟩ := edge_eq_pair_of_mem f.val (edge_card f) a (mem_inter.mp ham).2
  have hbc : b ≠ c := by
    intro h
    subst c
    have hb : b ∈ e.val ∩ f.val := by simp [he, hf]
    exact hab (mem_singleton.mp (ha ▸ hb)).symm
  have hfilter :
      ((univ : Finset A).powersetCard m).filter (fun S => crossed e S ∧ crossed f S) =
        ((univ : Finset A).powersetCard m).filter
          (fun S => fits {a} {b, c} S ∨ fits {b, c} {a} S) := by
    ext S
    simp only [mem_filter, crossed, he, hf, pair_crosses_iff hab, pair_crosses_iff hac, fits,
      singleton_subset_iff, insert_subset_iff, disjoint_insert_right, disjoint_singleton_right]
    tauto
  rw [hfilter, card_filter_or (by simp [fits, insert_subset_iff]; tauto),
    card_pattern m _ _ (by simp [hab, hac]) (by simp; omega),
    card_pattern m _ _ (by simp [hab, hac]) (by simpa [card_pair hbc] using hm)]
  simp only [card_singleton, card_pair hbc, Nat.reduceAdd]
  have hn : 3 ≤ Fintype.card A := by
    have hcard : ({a, b, c} : Finset A).card = 3 :=
      card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
    rw [← hcard, ← card_univ]
    exact card_mono (subset_univ _)
  rw [show Fintype.card A - 2 = Fintype.card A - 3 + 1 by omega,
    show m - 1 = m - 2 + 1 by omega, Nat.choose_succ_succ']
  exact Nat.add_comm _ _

omit [Fintype A] in
private theorem disjoint_pairs_iff {a b c d : A} :
    Disjoint ({a, b} : Finset A) {c, d} ↔ (a ≠ c ∧ a ≠ d) ∧ (b ≠ c ∧ b ≠ d) := by
  simp only [disjoint_insert_left, disjoint_singleton_left, mem_insert, mem_singleton, not_or]

/-- Disjoint edges have four crossing orientations, each forcing two vertices to each side. -/
private theorem card_joint_disjoint (e f : Edge A) (h : Disjoint e.val f.val) (hm : 2 ≤ m) :
    (((univ : Finset A).powersetCard m).filter
      (fun S => crossed e S ∧ crossed f S)).card =
      4 * (Fintype.card A - 4).choose (m - 2) := by
  obtain ⟨a, b, hab, he⟩ := card_eq_two.mp (edge_card e)
  obtain ⟨c, d, hcd, hf⟩ := card_eq_two.mp (edge_card f)
  rw [he, hf, disjoint_pairs_iff] at h
  obtain ⟨⟨hac, had⟩, hbc, hbd⟩ := h
  have hfilter :
      ((univ : Finset A).powersetCard m).filter (fun S => crossed e S ∧ crossed f S) =
        ((univ : Finset A).powersetCard m).filter
          (fun S => (fits {a, c} {b, d} S ∨ fits {a, d} {b, c} S) ∨
                    (fits {b, c} {a, d} S ∨ fits {b, d} {a, c} S)) := by
    ext S
    simp only [mem_filter, crossed, he, hf, pair_crosses_iff hab, pair_crosses_iff hcd, fits,
      singleton_subset_iff, insert_subset_iff, disjoint_insert_right, disjoint_singleton_right]
    by_cases ha : a ∈ S <;> by_cases hc : c ∈ S <;>
      simp [ha, hc, and_comm]
  rw [hfilter, card_filter_or (by
      intro S
      by_cases ha : a ∈ S <;> simp [fits, insert_subset_iff, ha]),
    card_filter_or (by
      intro S
      by_cases hc : c ∈ S <;> simp [fits, insert_subset_iff, hc]),
    card_filter_or (by
      intro S
      by_cases hc : c ∈ S <;> simp [fits, insert_subset_iff, hc])]
  rw [card_pattern m _ _ (disjoint_pairs_iff.mpr ⟨⟨hab, had⟩, hbc.symm, hcd⟩)
        (by simpa [card_pair hac] using hm),
    card_pattern m _ _ (disjoint_pairs_iff.mpr ⟨⟨hab, hac⟩, hbd.symm, hcd.symm⟩)
        (by simpa [card_pair had] using hm),
    card_pattern m _ _ (disjoint_pairs_iff.mpr ⟨⟨hab.symm, hbd⟩, hac.symm, hcd⟩)
        (by simpa [card_pair hbc] using hm),
    card_pattern m _ _ (disjoint_pairs_iff.mpr ⟨⟨hab.symm, hbc⟩, had.symm, hcd.symm⟩)
        (by simpa [card_pair hbd] using hm)]
  simp only [card_pair hac, card_pair had, card_pair hbc, card_pair hbd, Nat.reduceAdd]
  omega

-- Force one vertex in and one out, then cancel the two one-vertex binomial steps.
private theorem choose_ratio_step (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    ((n - 2).choose (k - 1) : ℝ) / (n.choose k : ℝ) =
      (k : ℝ) * ((n : ℝ) - k) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hiNat := Nat.add_one_mul_choose_eq (n - 2) (k - 1)
  rw [show n - 2 + 1 = n - 1 by omega, show k - 1 + 1 = k by omega] at hiNat
  have hoNat := Nat.choose_mul_succ_eq (n - 1) k
  rw [show n - 1 + 1 = n by omega] at hoNat
  have hi := congrArg (fun x : ℕ => (x : ℝ)) hiNat
  have ho := congrArg (fun x : ℕ => (x : ℝ)) hoNat
  push_cast [Nat.cast_sub (show 1 ≤ n by omega)] at hi
  push_cast [Nat.cast_sub hkn.le] at ho
  have hn : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn₀ : (n : ℝ) ≠ 0 := by linarith
  have hn₁ : (n : ℝ) - 1 ≠ 0 := by linarith
  have hc : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkn.le).ne'
  apply (div_eq_div_iff hc (mul_ne_zero hn₀ hn₁)).mpr
  calc
    _ = (n : ℝ) * (((n : ℝ) - 1) * ((n - 2).choose (k - 1) : ℝ)) := by ring
    _ = (k : ℝ) * (((n - 1).choose k : ℝ) * n) := by rw [hi]; ring
    _ = _ := by rw [ho]; ring

private theorem choose_ratio_two (n k : ℕ) (hk : 2 ≤ k) (hkn : k + 2 ≤ n) :
    ((n - 4).choose (k - 2) : ℝ) / (n.choose k : ℝ) =
      (k : ℝ) * ((k : ℝ) - 1) * ((n : ℝ) - k) * ((n : ℝ) - k - 1) /
        ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3)) := by
  have hc : ((n - 2).choose (k - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show k - 1 ≤ n - 2 by omega)).ne'
  have hn : (3 : ℝ) < n := by exact_mod_cast (show 3 < n by omega)
  have hn₀ : (n : ℝ) ≠ 0 := by linarith
  have hn₁ : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn₂ : (n : ℝ) - 2 ≠ 0 := by linarith
  have hn₃ : (n : ℝ) - 3 ≠ 0 := by linarith
  have hstep := choose_ratio_step (n - 2) (k - 1) (by omega) (by omega)
  rw [show n - 2 - 2 = n - 4 by omega, show k - 1 - 1 = k - 2 by omega,
    Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 1 ≤ k by omega)] at hstep
  calc
    _ = (((n - 4).choose (k - 2) : ℝ) / ((n - 2).choose (k - 1) : ℝ)) *
        (((n - 2).choose (k - 1) : ℝ) / (n.choose k : ℝ)) := by
          rw [div_mul_div_comm, mul_comm ((n - 4).choose (k - 2) : ℝ), mul_div_mul_left _ _ hc]
    _ = _ := by
      rw [hstep, choose_ratio_step n k (by omega) (by omega)]
      have hn₃' : (n : ℝ) - 2 - 1 ≠ 0 := by linarith
      field_simp [hn₀, hn₁, hn₂, hn₃, hn₃']
      ring

/-- The joint probability for an edge paired with itself is `q`. -/
private theorem jointProbability_eq (e : Edge A) (hn : 4 ≤ Fintype.card A)
    (hm : 2 ≤ m) (hmn : m ≤ Fintype.card A - 2) :
    jointProbability m e e = q (Fintype.card A) m := by
  rw [jointProbability, card_joint_eq m e (by omega), card_powersetCard, card_univ,
    Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc, choose_ratio_step _ _ (by omega) (by omega)]
  unfold q
  ring

/-- The joint probability for edges sharing exactly one endpoint is `q / 2`. -/
private theorem jointProbability_inter_one (e f : Edge A) (h : (e.val ∩ f.val).card = 1)
    (hn : 4 ≤ Fintype.card A) (hm : 2 ≤ m) (hmn : m ≤ Fintype.card A - 2) :
    jointProbability m e f = q (Fintype.card A) m / 2 := by
  rw [jointProbability, card_joint_inter_one m e f h hm, card_powersetCard, card_univ,
    choose_ratio_step _ _ (by omega) (by omega)]
  unfold q
  ring

/-- The joint probability for disjoint edges comes from four orientations. -/
private theorem jointProbability_disjoint (e f : Edge A) (h : Disjoint e.val f.val)
    (hn : 4 ≤ Fintype.card A) (hm : 2 ≤ m) (hmn : m ≤ Fintype.card A - 2) :
    jointProbability m e f =
      4 * (m : ℝ) * ((m : ℝ) - 1) * ((Fintype.card A : ℝ) - m) *
          ((Fintype.card A : ℝ) - m - 1) /
        ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) - 1) *
          ((Fintype.card A : ℝ) - 2) * ((Fintype.card A : ℝ) - 3)) := by
  rw [jointProbability, card_joint_disjoint m e f h hm, card_powersetCard, card_univ,
    Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc, choose_ratio_two _ _ hm (by omega)]
  ring

end FixedCutCount

open scoped BigOperators

noncomputable section
namespace FixedCutAlgebra

variable {A E J : Type*} [Fintype A] [Fintype E] [Fintype J]

def starWeights (incident : A → E → ℝ) (u : A → ℝ) (e : E) : ℝ :=
  ∑ a, u a * incident a e

def degrees (incident : A → E → ℝ) (w : E → ℝ) (a : A) : ℝ :=
  ∑ e, w e * incident a e

def average (mass : J → ℝ) (x : J → ℝ) : ℝ :=
  ∑ s, mass s * x s

def cut (crosses : J → E → ℝ) (w : E → ℝ) (s : J) : ℝ :=
  ∑ e, w e * crosses s e

def variance (mass : J → ℝ) (x : J → ℝ) : ℝ :=
  average mass (fun s => x s ^ 2) - average mass x ^ 2

def pairCovariance (mass : J → ℝ) (crosses : J → E → ℝ) (e f : E) : ℝ :=
  average mass (fun s => crosses s e * crosses s f) -
    average mass (fun s => crosses s e) * average mass (fun s => crosses s f)

private theorem star_dot (incident : A → E → ℝ) (u : A → ℝ) (z : E → ℝ) :
    (∑ e, starWeights incident u e * z e) = ∑ a, u a * degrees incident z a := by
  simp only [starWeights, degrees, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro e _
  ring

private theorem degrees_star (incident : A → E → ℝ) (u : A → ℝ) (h : ℝ) [DecidableEq A]
    (hoverlap : ∀ a b, (∑ e, incident a e * incident b e) = (if a = b then h else 0) + 1) :
    ∀ a, degrees incident (starWeights incident u) a = h * u a + ∑ b, u b := by
  intro a
  calc
    _ = ∑ b, u b * (∑ e, incident b e * incident a e) := by
      simp only [degrees, starWeights, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = _ := by
      simp only [hoverlap, mul_add, mul_one, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single a]
      · simp [mul_comm]
      · intro b _ hb
        simp [hb]
      · simp

private theorem weighted_first_moment (mass : J → ℝ) (crosses : J → E → ℝ) (w : E → ℝ) :
    average mass (cut crosses w) = ∑ e, w e * average mass (fun s => crosses s e) := by
  simp only [average, cut, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem weighted_second_moment (mass : J → ℝ) (crosses : J → E → ℝ) (w : E → ℝ) :
    average mass (fun s => cut crosses w s ^ 2) =
      ∑ e, ∑ f, w e * w f * average mass (fun s => crosses s e * crosses s f) := by
  simp only [average, cut, pow_two, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem cut_variance_of_covariance (mass : J → ℝ) (crosses : J → E → ℝ) (w : E → ℝ) :
    variance mass (cut crosses w) = ∑ e, ∑ f, w e * w f * pairCovariance mass crosses e f := by
  rw [variance, weighted_first_moment, weighted_second_moment]
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, pairCovariance, mul_sub,
    Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  ring

private theorem covariance_form (mass : J → ℝ) (crosses : J → E → ℝ) (incident : A → E → ℝ)
    (w : E → ℝ) (alpha beta gamma : ℝ) [DecidableEq E]
    (hcov : ∀ e f, pairCovariance mass crosses e f =
      (if e = f then alpha else 0) + beta * (∑ a, incident a e * incident a f) + gamma) :
    variance mass (cut crosses w) =
      alpha * (∑ e, w e ^ 2) + beta * (∑ a, degrees incident w a ^ 2) +
        gamma * (∑ e, w e) ^ 2 := by
  rw [cut_variance_of_covariance]
  simp_rw [hcov, mul_add, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_eq_single e]
      · simp
        ring
      · intro f _ hf
        simp [Ne.symm hf]
      · simp
    · simp only [degrees, pow_two, Finset.sum_mul, Finset.mul_sum]
      calc
        (∑ e, ∑ f, ∑ a, w e * w f * (beta * (incident a e * incident a f))) =
            ∑ a, ∑ e, ∑ f, w e * w f * (beta * (incident a e * incident a f)) := by
          simp_rw [Finset.sum_comm (s := (Finset.univ : Finset E))
            (t := (Finset.univ : Finset A))]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro e _
          apply Finset.sum_congr rfl
          intro f _
          ring
  · simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    ring

private theorem degrees_sum (incident : A → E → ℝ) (w : E → ℝ) (k : ℝ)
    (hcard : ∀ e, (∑ a, incident a e) = k) :
    (∑ a, degrees incident w a) = k * ∑ e, w e := by
  simp only [degrees]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hcard, mul_comm _ k, ← Finset.mul_sum]

private theorem variance_centered_of_covariance (mass : J → ℝ) (crosses : J → E → ℝ)
    (incident : A → E → ℝ) [DecidableEq A] [DecidableEq E]
    (w : E → ℝ) (t alpha beta gamma : ℝ)
    (ht : t ≠ 0) (hw : (∑ e, w e) = 0)
    (hcard : ∀ e, (∑ a, incident a e) = 2)
    (hoverlap : ∀ a b, (∑ e, incident a e * incident b e) = (if a = b then t else 0) + 1)
    (hcov : ∀ e f, pairCovariance mass crosses e f =
      (if e = f then alpha else 0) + beta * (∑ a, incident a e * incident a f) + gamma) :
    let u : A → ℝ := fun a => degrees incident w a / t
    let z : E → ℝ := fun e => w e - starWeights incident u e
    variance mass (cut crosses w) =
      (alpha + t * beta) * (∑ e, starWeights incident u e ^ 2) +
        alpha * (∑ e, z e ^ 2) := by
  intro u z
  have hsum : (∑ a, u a) = 0 := by
    simp [u, ← Finset.sum_div, degrees_sum incident w 2 hcard, hw]
  have hdegree (a : A) : degrees incident w a = t * u a := by
    dsimp [u]
    field_simp
  have hstarDegree (a : A) : degrees incident (starWeights incident u) a = t * u a := by
    rw [degrees_star incident u t hoverlap, hsum, add_zero]
  have hdegzero (a : A) : degrees incident z a = 0 := by
    rw [show degrees incident z a = degrees incident w a -
      degrees incident (starWeights incident u) a by
        simp only [degrees, z, sub_mul, Finset.sum_sub_distrib]]
    rw [hdegree, hstarDegree, sub_self]
  have hcross : (∑ e, starWeights incident u e * z e) = 0 := by
    simp [star_dot, hdegzero]
  have hstarSq : (∑ e, starWeights incident u e ^ 2) = t * ∑ a, u a ^ 2 := by
    simp only [pow_two, star_dot, hstarDegree, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hdegreesSq :
      (∑ a, degrees incident w a ^ 2) = t * (∑ e, starWeights incident u e ^ 2) := by
    simp only [hdegree, hstarSq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hsquared :
      (∑ e, w e ^ 2) = (∑ e, starWeights incident u e ^ 2) + ∑ e, z e ^ 2 := by
    calc
      _ = ∑ e, (starWeights incident u e ^ 2 + z e ^ 2 + 2 * (starWeights incident u e * z e)) := by
        apply Finset.sum_congr rfl
        intro e _
        dsimp [z]
        ring
      _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum, hcross]
  rw [covariance_form mass crosses incident w alpha beta gamma hcov, hsquared, hdegreesSq, hw]
  ring

private theorem variance_add_const (mass : J → ℝ) (x : J → ℝ) (c : ℝ)
    (hMass : (∑ s, mass s) = 1) :
    variance mass (fun s => x s + c) = variance mass x := by
  have hFirst : average mass (fun s => x s + c) = average mass x + c := by
    simp [average, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hMass]
  have hSecond : average mass (fun s => (x s + c)^2) =
      average mass (fun s => x s^2) + 2 * average mass x * c + c^2 := by
    calc
      _ = average mass (fun s => x s^2 + (2 * (mass s * x s) * c) / mass s + c^2) := by
        unfold average
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : mass s = 0
        · simp [hs]
        · field_simp
          ring
      _ = _ := by
        unfold average
        simp_rw [mul_add, Finset.sum_add_distrib]
        have hmid (s : J) :
            mass s * (2 * (mass s * x s) * c / mass s) = 2 * (mass s * x s) * c := by
          by_cases hs : mass s = 0
          · simp [hs]
          · field_simp
        simp_rw [hmid, ← Finset.sum_mul, ← Finset.mul_sum, hMass, one_mul]
  simp only [variance, hFirst, hSecond]
  ring

end FixedCutAlgebra

end

open Finset FixedCutAlgebra
open scoped BigOperators

noncomputable section
variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev Slice (A : Type*) [Fintype A] (m : ℕ) := ↥((univ : Finset A).powersetCard m)
abbrev Edge (A : Type*) [Fintype A] := Slice A 2

def incidence (a : A) (e : Edge A) : ℝ := if a ∈ e.val then 1 else 0

def crossing (m : ℕ) (S : Slice A m) (e : Edge A) : ℝ :=
  if (e.val ∩ S.val).card = 1 then 1 else 0

def mass (m : ℕ) (_ : Slice A m) : ℝ := ((Fintype.card A).choose m : ℝ)⁻¹

private theorem incidence_size (e : Edge A) :
    (∑ a, incidence a e) = 2 := by
  have h : e.val.card = 2 := (Finset.mem_powersetCard.mp e.property).2
  simp [incidence, h]

private theorem edge_overlap (e f : Edge A) :
    (∑ a, incidence a e * incidence a f) = ((e.val ∩ f.val).card : ℝ) := by
  calc
    _ = ∑ a : A, if a ∈ e.val ∩ f.val then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases he : a ∈ e.val <;> by_cases hf : a ∈ f.val <;> simp [incidence, he, hf]
    _ = _ := by
      rw [Finset.sum_boole]
      have hfilter : (univ.filter fun a => a ∈ e.val ∩ f.val) = e.val ∩ f.val := by
        ext a
        simp
      rw [hfilter]

private theorem vertex_overlap (a b : A) (hn : 4 ≤ Fintype.card A) :
    (∑ e : Edge A, incidence a e * incidence b e) =
      (if a = b then ((Fintype.card A : ℝ) - 2) else 0) + 1 := by
  unfold incidence
  rw [Finset.sum_coe_sort ((univ : Finset A).powersetCard 2)
    (fun e => (if a ∈ e then (1 : ℝ) else 0) * (if b ∈ e then 1 else 0))]
  let inside : Finset A := {a, b}
  have hc : inside.card ≤ 2 := by
    by_cases hab : a = b
    · simp [inside, hab]
    · simp [inside, hab]
  have hfilter : ((univ : Finset A).powersetCard 2).filter (fun e => a ∈ e ∧ b ∈ e) =
      ((univ : Finset A).powersetCard 2).filter (inside ⊆ ·) := by
    ext s
    simp [inside, Finset.insert_subset_iff, and_comm]
  calc
    _ = ∑ e ∈ (univ : Finset A).powersetCard 2, if a ∈ e ∧ b ∈ e then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases ha : a ∈ e <;> by_cases hb : b ∈ e <;> simp [ha, hb]
    _ = _ := by
      rw [Finset.sum_boole, hfilter,
        Finset.card_filter_powersetCard_subset inside univ 2 (Finset.subset_univ _) hc,
        Finset.card_univ]
      by_cases hab : a = b
      · subst b
        simp [inside, Nat.cast_sub (by omega : 1 ≤ Fintype.card A)]
        ring
      · simp [inside, hab]

omit [Fintype A] in
private theorem crossing_iff (S : Finset A) {a b : A} (hab : a ≠ b) :
    (({a, b} : Finset A) ∩ S).card = 1 ↔ (a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S) := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
    simp [Finset.insert_inter_of_mem, Finset.insert_inter_of_notMem, Finset.singleton_inter_of_mem,
      Finset.singleton_inter_of_notMem, hab, ha, hb]

private theorem constant_unit_cut {m : ℕ} (S : Slice A m) :
    (∑ e, crossing m S e) = (m : ℝ) * ((Fintype.card A : ℝ) - m) := by
  let T : Finset A := univ \ S.val
  let pairs : Finset (A × A) := S.val.product T
  let toEdge : A × A → Finset A := fun p => {p.1, p.2}
  have disj {a b : A} (ha : a ∈ S.val) (hb : b ∈ T) : a ≠ b := by
    intro h
    exact (Finset.mem_sdiff.mp hb).2 (h ▸ ha)
  have hsubset : pairs.image toEdge =
      ((univ : Finset A).powersetCard 2).filter (fun e => (e ∩ S.val).card = 1) := by
    ext e
    constructor
    · intro h
      obtain ⟨⟨a, b⟩, hp, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
      have hab := disj ha hb
      simp [toEdge, Finset.mem_filter, Finset.mem_powersetCard, hab,
        ha, (Finset.mem_sdiff.mp hb).2]
    · intro he
      obtain ⟨he, hint⟩ := Finset.mem_filter.mp he
      have he2 := (Finset.mem_powersetCard.mp he).2
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he2
      rcases (crossing_iff S.val hab).mp hint with ⟨ha,hb⟩ | ⟨hb,ha⟩
      · exact Finset.mem_image.mpr ⟨(a,b), Finset.mem_product.mpr ⟨ha, by simp [T, hb]⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨(b,a), Finset.mem_product.mpr ⟨hb, by simp [T, ha]⟩,
          by simp [toEdge, Finset.pair_comm]⟩
  have hinj : Set.InjOn toEdge pairs := by
    rintro ⟨a,b⟩ h₁ ⟨a',b'⟩ h₂ heq
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp h₁
    obtain ⟨ha',hb'⟩ := Finset.mem_product.mp h₂
    have haeq : a = a' := by
      have hm : a ∈ toEdge (a',b') := heq ▸ (by simp [toEdge] : a ∈ toEdge (a,b))
      simp only [toEdge, Finset.mem_insert, Finset.mem_singleton] at hm
      exact hm.resolve_right (disj ha hb')
    subst a'
    have hbeq : b = b' := by
      have hm : b ∈ toEdge (a,b') := heq ▸ (by simp [toEdge] : b ∈ toEdge (a,b))
      simp only [toEdge, Finset.mem_insert, Finset.mem_singleton] at hm
      exact hm.resolve_left (disj ha hb).symm
    subst b'
    rfl
  have hS : S.val.card = m := (Finset.mem_powersetCard.mp S.property).2
  have hm : m ≤ Fintype.card A := by
    simpa [hS] using Finset.card_le_univ S.val
  have hT : T.card = Fintype.card A - m := by
    simp [T, Finset.card_sdiff_of_subset (Finset.subset_univ S.val), hS]
  have hcount :
      (((univ : Finset A).powersetCard 2).filter (fun e => (e ∩ S.val).card = 1)).card =
        m * (Fintype.card A - m) := by
    rw [← hsubset, Finset.card_image_of_injOn hinj]
    dsimp only [pairs]
    calc
      _ = S.val.card * T.card := Finset.card_product S.val T
      _ = _ := by rw [hS, hT]
  unfold crossing
  rw [Finset.sum_coe_sort ((univ : Finset A).powersetCard 2)
    (fun e => if (e ∩ S.val).card = 1 then (1 : ℝ) else 0), Finset.sum_boole, hcount]
  push_cast [Nat.cast_sub hm]
  rfl

def separationProbability (n m : ℕ) : ℝ :=
  2 * (m : ℝ) * ((n : ℝ) - m) / ((n : ℝ) * ((n : ℝ) - 1))

def disjointProbability (n m : ℕ) : ℝ :=
  4 * (m : ℝ) * ((m : ℝ) - 1) * ((n : ℝ) - m) * ((n : ℝ) - m - 1) /
    ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3))

def degreeCoefficient (n m : ℕ) : ℝ :=
  (m : ℝ) * ((n : ℝ) - m) * ((n : ℝ) - 2 * m)^2 /
    ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2))

private theorem covariance_entry (m : ℕ)
    (hmean : ∀ e : Edge A, average (mass m) (fun S => crossing m S e) =
      separationProbability (Fintype.card A) m)
    (hjoint : ∀ e f : Edge A, average (mass m) (fun S => crossing m S e * crossing m S f) =
      if e = f then separationProbability (Fintype.card A) m
      else if (e.val ∩ f.val).card = 1 then separationProbability (Fintype.card A) m / 2
      else disjointProbability (Fintype.card A) m) :
    ∀ e f : Edge A, pairCovariance (mass m) (crossing m) e f =
      (if e = f then disjointProbability (Fintype.card A) m else 0) +
      (separationProbability (Fintype.card A) m / 2 - disjointProbability (Fintype.card A) m) *
        (∑ a, incidence a e * incidence a f) +
      (disjointProbability (Fintype.card A) m - separationProbability (Fintype.card A) m ^ 2) := by
  intro e f
  rw [pairCovariance, hmean, hmean, hjoint, edge_overlap]
  have he : e.val.card = 2 := (Finset.mem_powersetCard.mp e.property).2
  have hf : f.val.card = 2 := (Finset.mem_powersetCard.mp f.property).2
  by_cases hd : e = f
  · subst f
    simp [he]
    ring
  have hlt : (e.val ∩ f.val).card < 2 := by
    have hle := Finset.card_le_card (Finset.inter_subset_left (s₁ := e.val) (s₂ := f.val))
    rw [he] at hle
    apply lt_of_le_of_ne hle
    intro heq
    have hLeft : e.val ∩ f.val = e.val :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hRight : e.val ∩ f.val = f.val :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hd (Subtype.ext (hLeft.symm.trans hRight))
  by_cases hi : (e.val ∩ f.val).card = 1
  · simp [hd, hi]
    ring
  · have hzero : (e.val ∩ f.val).card = 0 := by omega
    simp [hd, hzero]
    ring

private theorem variance_split_from_counts (m : ℕ) (hn : 4 ≤ Fintype.card A)
    (hm : m ≤ Fintype.card A) (w : Edge A → ℝ)
    (hmean : ∀ e : Edge A, average (mass m) (fun S => crossing m S e) =
      separationProbability (Fintype.card A) m)
    (hjoint : ∀ e f : Edge A, average (mass m) (fun S => crossing m S e * crossing m S f) =
      if e = f then separationProbability (Fintype.card A) m
      else if (e.val ∩ f.val).card = 1 then separationProbability (Fintype.card A) m / 2
      else disjointProbability (Fintype.card A) m) :
    let n := Fintype.card A
    let b := (∑ e, w e) / (n.choose 2 : ℝ)
    let v : Edge A → ℝ := fun e => w e - b
    let u : A → ℝ := fun a => degrees incidence v a / ((n : ℝ) - 2)
    let z : Edge A → ℝ := fun e => v e - starWeights incidence u e
    variance (mass m) (cut (crossing m) w) =
      degreeCoefficient n m * (∑ e, starWeights incidence u e ^ 2) +
        disjointProbability n m * (∑ e, z e ^ 2) := by
  intro n b v u z
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have hnCard : Fintype.card (Edge A) = n.choose 2 := by
    simp [n, Edge, Slice]
  have hp : (n.choose 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ n)).ne'
  have hw : (∑ e, v e) = 0 := by
    simp only [v, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      hnCard, nsmul_eq_mul, b]
    field_simp
    ring
  have hMass : (∑ S : Slice A m, mass m S) = 1 := by
    have hpos : ((n.choose m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hm).ne'
    have hcard : Fintype.card (Slice A m) = n.choose m := by
      simp [n, Slice]
    simp only [mass, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    change (n.choose m : ℝ) * (n.choose m : ℝ)⁻¹ = 1
    exact mul_inv_cancel₀ hpos
  have hcut : cut (crossing m) w =
      fun S => cut (crossing m) v S + b * ((m : ℝ) * ((n : ℝ) - m)) := by
    funext S
    rw [← constant_unit_cut S, Finset.mul_sum, cut, cut, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    dsimp [v]
    ring
  have hcoeff :
      disjointProbability n m + ((n : ℝ) - 2) *
        (separationProbability n m / 2 - disjointProbability n m) = degreeCoefficient n m := by
    have h0 : (n : ℝ) ≠ 0 := by linarith
    have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have h3 : (n : ℝ) - 3 ≠ 0 := by linarith
    unfold disjointProbability separationProbability degreeCoefficient
    field_simp
    ring
  rw [hcut, variance_add_const _ _ _ hMass]
  have h := variance_centered_of_covariance (mass m) (crossing m) incidence v
    ((n : ℝ) - 2) (disjointProbability n m)
    (separationProbability n m / 2 - disjointProbability n m)
    (disjointProbability n m - separationProbability n m ^ 2) hn2 hw
    incidence_size (fun a b => vertex_overlap a b hn) (covariance_entry m hmean hjoint)
  dsimp only at h
  rw [hcoeff] at h
  exact h

private theorem joint_from_average (m : ℕ) (e f : Edge A) :
    average (mass m) (fun S => crossing m S e * crossing m S f) =
      FixedCutCount.jointProbability m e f := by
  let population := (univ : Finset A).powersetCard m
  simp only [average, mass]
  rw [← Finset.mul_sum]
  have hprod (S : Slice A m) : crossing m S e * crossing m S f =
      if FixedCutCount.crossed e S.val ∧ FixedCutCount.crossed f S.val then 1 else 0 := by
    by_cases he : FixedCutCount.crossed e S.val <;> by_cases hf : FixedCutCount.crossed f S.val <;>
      simp [crossing, FixedCutCount.crossed] at he hf ⊢ <;> simp [he, hf]
  simp_rw [hprod]
  rw [Finset.sum_coe_sort population
    (fun S => if FixedCutCount.crossed e S ∧ FixedCutCount.crossed f S then (1 : ℝ) else 0),
    Finset.sum_boole]
  simp only [FixedCutCount.jointProbability, Finset.card_powersetCard, Finset.card_univ, population,
    div_eq_mul_inv, mul_comm]

/-- A uniform fixed-size cut has separate degree and zero-degree variance contributions. -/
theorem fixed_size_cut_variance (m : ℕ) (hn : 4 ≤ Fintype.card A)
    (hm : 2 ≤ m) (hmn : m ≤ Fintype.card A - 2) (w : Edge A → ℝ) :
    let n := Fintype.card A
    let b := (∑ e, w e) / (n.choose 2 : ℝ)
    let v : Edge A → ℝ := fun e => w e - b
    let u : A → ℝ := fun a => degrees incidence v a / ((n : ℝ) - 2)
    let z : Edge A → ℝ := fun e => v e - starWeights incidence u e
    variance (mass m) (cut (crossing m) w) =
      degreeCoefficient n m * (∑ e, starWeights incidence u e ^ 2) +
        disjointProbability n m * (∑ e, z e ^ 2) := by
  have hmean (e : Edge A) :
      average (mass m) (fun S => crossing m S e) =
        separationProbability (Fintype.card A) m := by
    have he (S : Slice A m) : crossing m S e = crossing m S e * crossing m S e := by
      unfold crossing
      split <;> simp
    rw [show (fun S : Slice A m => crossing m S e) =
      (fun S : Slice A m => crossing m S e * crossing m S e) from funext he]
    rw [joint_from_average]
    exact FixedCutCount.jointProbability_eq m e hn hm hmn
  apply variance_split_from_counts m hn (by omega) w hmean
  intro e f
  rw [joint_from_average]
  by_cases hd : e = f
  · subst f
    rw [ite_eq_left rfl]
    exact FixedCutCount.jointProbability_eq m e hn hm hmn
  rw [ite_eq_right hd]
  by_cases hi : (e.val ∩ f.val).card = 1
  · rw [ite_eq_left hi]
    exact FixedCutCount.jointProbability_inter_one m e f hi hn hm hmn
  rw [ite_eq_right hi]
  have he : e.val.card = 2 := (Finset.mem_powersetCard.mp e.property).2
  have hf : f.val.card = 2 := (Finset.mem_powersetCard.mp f.property).2
  have hle := Finset.card_le_card (Finset.inter_subset_left (s₁ := e.val) (s₂ := f.val))
  have hne : (e.val ∩ f.val).card ≠ 2 := by
    intro heq
    have hLeft : e.val ∩ f.val = e.val :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hRight : e.val ∩ f.val = f.val :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hd (Subtype.ext (hLeft.symm.trans hRight))
  have hzero : (e.val ∩ f.val).card = 0 := by omega
  have hdisj : Disjoint e.val f.val :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hzero)
  exact FixedCutCount.jointProbability_disjoint m e f hdisj hn hm hmn

end

end D5.S3.Combinatorics.Graph.Incidence.FixedSizeCutVariance
