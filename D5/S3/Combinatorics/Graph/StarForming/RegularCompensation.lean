/- GID: D5/S3/Combinatorics/Graph/StarForming/RegularCompensation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/RegularCompensation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual augmented exchanges give graph-wide sharp regular compensation. -/

import D5.S3.Combinatorics.Graph.StarForming.BipartiteExchange

/-! The augmented exchanges from the received isolate-compensation proof are
combined with the actual finite degree-capacity sum. The numerical regular-gap
proof body below is reused from formal/StarForming/RegularCompensation.lean at
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69 (Apache-2.0).
No conditional numerical premise substitutes for a graph invariant. -/

namespace D5.S3.Combinatorics.Graph.StarForming.RegularCompensation
open StarFormingDissociationRefutation
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The degree-weighted compensation inequality includes irregular, empty and
zero-degree cases. It is stronger than the stated maximum-degree-at-least-three
source restriction, using the later augmented exchanges. -/
theorem weighted_selection_bound (hG : G.Colorable 2) (S : Finset V)
    (hS : IsMinimalStarForming G 2 S) (D : ℕ)
    (hD : ∀ v, DegreeCapacity.degree G v ≤ D) :
    (∑ v ∈ S, DegreeCapacity.degree G v) + (D + 1) * S.card ≤
      D * Fintype.card V + 2 * beta G 2 := by
  have hc := DegreeCapacity.degree_capacity G S hS D hD
  have he := BipartiteExchange.selection_compensation G hG S hS
  have ht : (Finset.univ \ S).card + S.card = Fintype.card V := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  nlinarith

/-- Both actual minimum and maximum ambient degrees enter the irregular bound. -/
theorem min_max_selection_bound (hG : G.Colorable 2) (S : Finset V)
    (hS : IsMinimalStarForming G 2 S) (delta D : ℕ)
    (hmin : ∀ v, delta ≤ DegreeCapacity.degree G v)
    (hmax : ∀ v, DegreeCapacity.degree G v ≤ D) :
    (delta + D + 1) * S.card ≤ D * Fintype.card V + 2 * beta G 2 := by
  have hc := weighted_selection_bound G hG S hS D hmax
  have hl : delta * S.card ≤ ∑ v ∈ S, DegreeCapacity.degree G v := by
    calc
      _ = ∑ _v ∈ S, delta := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hmin v)
  nlinarith

/-- Actual finite attainment transports the selection bound to SF. -/
theorem sf_min_max_bound (hG : G.Colorable 2) (delta D : ℕ)
    (hmin : ∀ v, delta ≤ DegreeCapacity.degree G v)
    (hmax : ∀ v, DegreeCapacity.degree G v ≤ D) :
    (delta + D + 1) * SF G 2 ≤ D * Fintype.card V + 2 * beta G 2 := by
  classical
  obtain ⟨S,hS,he⟩ := sf_attained G 2
  rw [← he]
  exact min_max_selection_bound G hG S hS delta D hmin hmax

/-- Sharp linear compensation for every regular bipartite graph. -/
theorem sf_regular_bound (hG : G.Colorable 2) (d : ℕ)
    (hregular : ∀ v, DegreeCapacity.degree G v = d) :
    (2 * d + 1) * SF G 2 ≤ d * Fintype.card V + 2 * beta G 2 := by
  have h := sf_min_max_bound G hG d d (fun v => (hregular v).ge)
    (fun v => (hregular v).le)
  simpa only [two_mul] using h

private theorem regular_gap_bound
    (degree order size beta : Int)
    (hdegree : 1 ≤ degree)
    (hregular : (2 * degree + 1) * size ≤ degree * order + 2 * beta)
    (hbalanced : order ≤ 2 * beta) :
    (4 * degree + 2) * (size - beta) ≤ order := by
  have hpositive : 0 ≤ 2 * degree - 1 := by omega
  have hscaled := Int.mul_le_mul_of_nonneg_left hbalanced hpositive
  simp only [Int.sub_mul, Int.add_mul, Int.mul_sub,
    Int.one_mul] at hregular hscaled ⊢
  simp only [Int.mul_assoc, Int.mul_left_comm degree 2] at hregular hscaled ⊢
  omega

/-- The graph-wide regular gap is bounded at every finite order. -/
theorem sf_sub_beta_bound (hG : G.Colorable 2) (d : ℕ) (hd : 1 ≤ d)
    (hregular : ∀ v, DegreeCapacity.degree G v = d) :
    (4 * d + 2) * (SF G 2 - beta G 2) ≤ Fintype.card V := by
  have hr := sf_regular_bound G hG d hregular
  have hb := BipartiteBounds.card_le_two_beta G hG
  have hs := beta_le_sf G
  have hh := regular_gap_bound (d : ℤ) (Fintype.card V) (SF G 2) (beta G 2)
    (by exact_mod_cast hd) (by exact_mod_cast hr) (by exact_mod_cast hb)
  exact_mod_cast hh

/-- The floor formulation is the exact natural-number source gap bound. -/
theorem sf_sub_beta_floor (hG : G.Colorable 2) (d : ℕ) (hd : 1 ≤ d)
    (hregular : ∀ v, DegreeCapacity.degree G v = d) :
    SF G 2 - beta G 2 ≤ Fintype.card V / (4 * d + 2) := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 4 * d + 2)).mpr
  simpa only [Nat.mul_comm] using sf_sub_beta_bound G hG d hd hregular

/-- The augmented regular remainder is an exact sum of two actual exchange
maximality deficits and the nonnegative isolate capacity remainder. -/
theorem regular_remainder (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (S : Finset V) (hS : IsMinimalStarForming G 2 S) (d : ℕ) :
    (d : ℤ) * Fintype.card V + 2 * beta G 2 - (2 * d + 1) * S.card =
      ((beta G 2 : ℤ) - (BipartiteExchange.exchange G S hS color false).card) +
      ((beta G 2 : ℤ) - (BipartiteExchange.exchange G S hS color true).card) +
      ((d : ℤ) * Fintype.card V - (2 * d - 1) * S.card -
        (DegreeCapacity.isolates G S).card) := by
  have hs := BipartiteExchange.exchange_card_sum G S color hcolor hS
  have hs' : ((BipartiteExchange.exchange G S hS color false).card : ℤ) +
      (BipartiteExchange.exchange G S hS color true).card +
      (DegreeCapacity.isolates G S).card = 2 * S.card := by exact_mod_cast hs
  nlinarith

/-- Linear equality is equivalent to tight isolate capacity and both actual
augmented exchanges attaining beta. This applies in degree three as well as
higher degree; no separate maximum-exchange premise is silently inferred from
an accounting partition. -/
theorem linear_equality_iff (color : V → Bool)
    (hcolor : ∀ v w, G.Adj v w → color v ≠ color w)
    (S : Finset V) (hS : IsMinimalStarForming G 2 S) (d : ℕ)
    (hd : 1 ≤ d) (hregular : ∀ v, DegreeCapacity.degree G v = d) :
    d * Fintype.card V + 2 * beta G 2 = (2 * d + 1) * S.card ↔
      ((2 * d - 1) * S.card + (DegreeCapacity.isolates G S).card = d * Fintype.card V) ∧
      (BipartiteExchange.exchange G S hS color false).card = beta G 2 ∧
      (BipartiteExchange.exchange G S hS color true).card = beta G 2 := by
  classical
  have h0 : (BipartiteExchange.exchange G S hS color false).card ≤ beta G 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,
      BipartiteExchange.exchange_dissociation G S color hcolor hS false⟩)
  have h1 : (BipartiteExchange.exchange G S hS color true).card ≤ beta G 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,
      BipartiteExchange.exchange_dissociation G S color hcolor hS true⟩)
  have hc := DegreeCapacity.regular_selection_bound G S hS d hd hregular
  have hs := BipartiteExchange.exchange_card_sum G S color hcolor hS
  have hd' : (2 * d - 1) + 1 = 2 * d := by omega
  constructor
  · intro he
    have hcap : (2 * d - 1) * S.card + (DegreeCapacity.isolates G S).card =
        d * Fintype.card V := by nlinarith
    refine ⟨hcap,?_,?_⟩ <;> nlinarith
  · rintro ⟨hcap,he0,he1⟩
    nlinarith

end D5.S3.Combinatorics.Graph.StarForming.RegularCompensation

