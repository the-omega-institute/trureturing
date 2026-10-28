/- GID: D5/S3/Combinatorics/Graph/Domination/TotalDominationSeeds
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/TotalDominationSeeds
   mirror-E: none(waiver:unbounded-constructive-proof)
   anchors: []
   utility: none
   digest: Actual total-domination graph families and right-hand seed estimates. -/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
Total domination always uses an open neighbourhood, including at selected vertices.
The seed family is the cone over the disjoint union of m copies of C5 and K3.
Cycle, clique, disjoint-union and cone polynomial identities are known ingredients
(arXiv:1605.02222 and the H-join framework of Subramanian--Selvakumar, Filomat 2025).
The quantitative right-hand seed argument is an ingredient of the direct route to
Shao--Zhao arXiv:2609.06569v5, section 5.2, Open Problem 2, registered as issue 23313.
This module does not assert whole-plane density.
-/

set_option autoImplicit false
set_option maxRecDepth 2000

namespace D5.S3.Combinatorics.Graph.Domination.TotalDominationSeeds

open Finset Polynomial

variable {V W : Type}

/-- Every vertex, whether selected or not, has a selected neighbour. -/
def IsTotal (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v, ∃ u ∈ S, G.Adj v u

/-- The polynomial of the actual subsets, without minimality or independence. -/
noncomputable def totalPolynomial [Fintype V] (G : SimpleGraph V) : ℝ[X] := by
  classical
  exact ∑ S : Finset V, if IsTotal G S then X ^ S.card else 0

/-- Disjoint union on the actual disjoint sum of vertex types. -/
def unionGraph (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) where
  Adj a b := match a, b with
    | .inl v, .inl w => G.Adj v w
    | .inr v, .inr w => H.Adj v w
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> simp_all [G.adj_comm, H.adj_comm]⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

private theorem union_total (G : SimpleGraph V) (H : SimpleGraph W)
    (A : Finset V) (B : Finset W) :
    IsTotal (unionGraph G H) (A.disjSum B) ↔ IsTotal G A ∧ IsTotal H B := by
  simp only [IsTotal, Sum.forall, Sum.exists, mem_disjSum, unionGraph]
  simp

private theorem union_polynomial [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    totalPolynomial (unionGraph G H) = totalPolynomial G * totalPolynomial H := by
  classical
  unfold totalPolynomial
  have hs : (∑ S : Finset (V ⊕ W), if IsTotal (unionGraph G H) S then
      (X : ℝ[X]) ^ S.card else 0) =
      ∑ p : Finset V × Finset W, if IsTotal (unionGraph G H) (p.1.disjSum p.2)
        then X ^ (p.1.disjSum p.2).card else 0 := by
    exact (Fintype.sum_equiv Finset.sumEquiv.toEquiv.symm _ _ (fun p => rfl)).symm
  rw [hs, Fintype.sum_prod_type]
  simp_rw [union_total, card_disjSum, pow_add]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  by_cases ha : IsTotal G A <;> by_cases hb : IsTotal H B <;> simp [ha, hb]

/-- The cone adds one genuine universal vertex, with no loop. -/
def coneGraph (G : SimpleGraph V) : SimpleGraph (Unit ⊕ V) where
  Adj a b := match a, b with
    | .inl _, .inl _ => False
    | .inr v, .inr w => G.Adj v w
    | _, _ => True
  symm := ⟨by intro a b; cases a <;> cases b <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

private theorem all_subsets [Fintype V] :
    (∑ S : Finset V, (X : ℝ[X]) ^ S.card) = (1 + X) ^ Fintype.card V := by
  classical
  have h := Finset.prod_add (fun _ : V => (X : ℝ[X])) (fun _ => (1 : ℝ[X])) univ
  simpa [add_comm] using h.symm


private theorem total_nonempty [Nonempty V] (G : SimpleGraph V) (B : Finset V)
    (h : IsTotal G B) : B.Nonempty := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨u, hu, _⟩ := h v
  exact ⟨u, hu⟩

private theorem cone_without_hub [Nonempty V] (G : SimpleGraph V) (B : Finset V) :
    IsTotal (coneGraph G) ((∅ : Finset Unit).disjSum B) ↔ IsTotal G B := by
  constructor
  · intro h v
    obtain ⟨u, hu, hadj⟩ := h (.inr v)
    cases u with
    | inl u => simp at hu
    | inr u => exact ⟨u, by simpa using hu, hadj⟩
  · intro h v
    cases v with
    | inl v =>
      obtain ⟨u, hu⟩ := total_nonempty G B h
      exact ⟨.inr u, by simpa using hu, trivial⟩
    | inr v =>
      obtain ⟨u, hu, hadj⟩ := h v
      exact ⟨.inr u, by simpa using hu, hadj⟩

private theorem cone_with_hub (G : SimpleGraph V) (B : Finset V) :
    IsTotal (coneGraph G) (({()} : Finset Unit).disjSum B) ↔ B.Nonempty := by
  constructor
  · intro h
    obtain ⟨u, hu, hadj⟩ := h (.inl ())
    cases u with
    | inl u => exact False.elim hadj
    | inr u => exact ⟨u, by simpa using hu⟩
  · rintro ⟨u, hu⟩ v
    cases v with
    | inl v => exact ⟨.inr u, by simpa using hu, trivial⟩
    | inr v => exact ⟨.inl (), by simp, trivial⟩

private theorem cone_polynomial [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    totalPolynomial (coneGraph G) =
      X * ((1 + X) ^ Fintype.card V - 1) + totalPolynomial G := by
  classical
  unfold totalPolynomial
  have hs : (∑ S : Finset (Unit ⊕ V), if IsTotal (coneGraph G) S then
      (X : ℝ[X]) ^ S.card else 0) =
      ∑ p : Finset Unit × Finset V, if IsTotal (coneGraph G) (p.1.disjSum p.2)
        then X ^ (p.1.disjSum p.2).card else 0 := by
    exact (Fintype.sum_equiv Finset.sumEquiv.toEquiv.symm _ _ (fun p => rfl)).symm
  rw [hs, Fintype.sum_prod_type]
  have hu : (univ : Finset (Finset Unit)) = {∅, {()}} := by decide +kernel
  rw [hu]
  simp only [Finset.sum_insert, Finset.sum_singleton, show (∅ : Finset Unit) ∉ ({ {()} } : Finset (Finset Unit)) by decide,
    not_false_eq_true, cone_without_hub, cone_with_hub, card_disjSum, card_empty,
    card_singleton, zero_add]
  have hB : (∑ B : Finset V, if B.Nonempty then (X : ℝ[X]) ^ (1 + B.card) else 0) =
      X * ((1 + X) ^ Fintype.card V - 1) := by
    have hsum : (∑ B : Finset V, if B.Nonempty then (X : ℝ[X]) ^ B.card else 0) =
        (1 + X) ^ Fintype.card V - 1 := by
      rw [← all_subsets]
      have he := Finset.sum_erase_add (univ : Finset (Finset V))
        (fun B => (X : ℝ[X]) ^ B.card) (by simp : (∅ : Finset V) ∈ univ)
      have hfilter : (∑ B : Finset V, if B.Nonempty then (X : ℝ[X]) ^ B.card else 0) =
          ∑ B ∈ (univ : Finset (Finset V)).erase ∅, (X : ℝ[X]) ^ B.card := by
        rw [← Finset.sum_filter]
        congr 1
        ext B
        simp [Finset.nonempty_iff_ne_empty]
      rw [hfilter]
      simpa using eq_sub_iff_add_eq.mpr he
    rw [← hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B _
    by_cases hb : B.Nonempty <;> simp [hb, pow_add]
  rw [hB]
  ring

instance totalDecidable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Decidable (IsTotal G S) := by
  unfold IsTotal
  infer_instance

private theorem cycle_five_polynomial : totalPolynomial (SimpleGraph.cycleGraph 5) =
    5 * X ^ 3 + 5 * X ^ 4 + X ^ 5 := by
  let C : Finset (Finset (Fin 5)) :=
    {{0,1,2}, {0,1,4}, {0,3,4}, {1,2,3}, {2,3,4},
     {0,1,2,3}, {0,1,2,4}, {0,1,3,4}, {0,2,3,4}, {1,2,3,4}, {0,1,2,3,4}}
  have hc : ∀ S : Finset (Fin 5), IsTotal (SimpleGraph.cycleGraph 5) S ↔ S ∈ C := by
    decide +kernel
  classical
  unfold totalPolynomial
  simp_rw [hc]
  rw [← Finset.sum_filter]
  have he : univ.filter (fun S => S ∈ C) = C := by ext S; simp
  rw [he]
  dsimp [C]
  simp (disch := decide +kernel) only [Finset.sum_insert, Finset.sum_singleton]
  norm_num [Finset.card_insert_of_notMem, Finset.card_singleton]
  ring

private theorem clique_three_polynomial : totalPolynomial (⊤ : SimpleGraph (Fin 3)) =
    3 * X ^ 2 + X ^ 3 := by
  let C : Finset (Finset (Fin 3)) := {{0,1}, {0,2}, {1,2}, {0,1,2}}
  have hc : ∀ S : Finset (Fin 3), IsTotal (⊤ : SimpleGraph (Fin 3)) S ↔ S ∈ C := by
    decide +kernel
  classical
  unfold totalPolynomial
  simp_rw [hc]
  rw [← Finset.sum_filter]
  have he : univ.filter (fun S => S ∈ C) = C := by ext S; simp
  rw [he]
  dsimp [C]
  simp (disch := decide +kernel) only [Finset.sum_insert, Finset.sum_singleton]
  norm_num [Finset.card_insert_of_notMem, Finset.card_singleton]
  ring

/-- The actual vertices of m disjoint five-cycles and one triangle. -/
def SeedBase : ℕ → Type
  | 0 => Fin 3
  | m + 1 => Fin 5 ⊕ SeedBase m

instance seedBaseFintype : (m : ℕ) → Fintype (SeedBase m)
  | 0 => inferInstanceAs (Fintype (Fin 3))
  | m + 1 => @instFintypeSum (Fin 5) (SeedBase m) _ (seedBaseFintype m)

instance seedBaseNonempty (m : ℕ) : Nonempty (SeedBase m) := by
  cases m with
  | zero => exact inferInstanceAs (Nonempty (Fin 3))
  | succ m => exact ⟨Sum.inl 0⟩

/-- No polynomial is hypothesized: these are the actual disjoint-union graphs. -/
def seedBaseGraph : (m : ℕ) → SimpleGraph (SeedBase m)
  | 0 => ⊤
  | m + 1 => unionGraph (SimpleGraph.cycleGraph 5) (seedBaseGraph m)

/-- The actual seed graph, with its universal vertex. -/
def seedGraph (m : ℕ) : SimpleGraph (Unit ⊕ SeedBase m) := coneGraph (seedBaseGraph m)

private theorem seed_base_card (m : ℕ) : Fintype.card (SeedBase m) = 5 * m + 3 := by
  induction m with
  | zero => norm_num [SeedBase]
  | succ m ih =>
    change Fintype.card (Fin 5 ⊕ SeedBase m) = _
    rw [Fintype.card_sum, ih]
    norm_num
    omega

private theorem seed_base_polynomial (m : ℕ) : totalPolynomial (seedBaseGraph m) =
    (5 * X ^ 3 + 5 * X ^ 4 + X ^ 5) ^ m * (3 * X ^ 2 + X ^ 3) := by
  induction m with
  | zero => simpa [seedBaseGraph] using clique_three_polynomial
  | succ m ih =>
    change totalPolynomial (unionGraph (SimpleGraph.cycleGraph 5) (seedBaseGraph m)) = _
    rw [union_polynomial, cycle_five_polynomial, ih, pow_succ]
    ring

/-- The explicit algebraic seed polynomial; graph realization is kept separate. -/
noncomputable def seedPolynomial (m : ℕ) : ℝ[X] :=
  X * ((1 + X) ^ (5 * m + 3) - 1) +
    (5 * X ^ 3 + 5 * X ^ 4 + X ^ 5) ^ m * (3 * X ^ 2 + X ^ 3)

private theorem seed_graph_polynomial (m : ℕ) :
    totalPolynomial (seedGraph m) = seedPolynomial m := by
  rw [seedGraph, cone_polynomial, seed_base_card, seed_base_polynomial]
  rfl

private theorem seed_at_minus_one (m : ℕ) (hm : Odd m) :
    (seedPolynomial m).eval (-1) = -1 := by
  simp only [seedPolynomial, eval_add, eval_mul, eval_sub, eval_pow, eval_ofNat,
    eval_X, eval_one]
  norm_num
  rw [hm.neg_one_pow]
  ring

/-- Bernoulli gives a finite, uniform upper bound on a shrinking base power. -/
private theorem shrinking_power_bound (a u : ℝ) (m : ℕ)
    (ha : 0 ≤ a) (hu : 0 ≤ u) (hua : a ≤ 1 - u) (hm : 3 ≤ (m : ℝ) * u) :
    a ^ m ≤ 1 / 4 := by
  have hmul : a * (1 + u) ≤ 1 := by nlinarith
  have hp := pow_le_pow_left₀ (mul_nonneg ha (by linarith : 0 ≤ 1 + u)) hmul m
  rw [mul_pow, one_pow] at hp
  have hb := one_add_mul_le_pow (by linarith : -2 ≤ u) m
  have hfour : 4 ≤ (1 + u) ^ m := by linarith
  have hnon := pow_nonneg ha m
  nlinarith

private theorem seed_upper_positive (s : ℕ) (hs : 3 ≤ s) (ho : Odd s) :
    0 < (seedPolynomial (s ^ 2)).eval (-1 + 1 / (s : ℝ)) := by
  let t : ℝ := 1 / (s : ℝ)
  let a : ℝ := (1 - t) ^ 3 * (1 + 3 * t + t ^ 2)
  let g : ℝ := 2 - 3 * t + t ^ 3
  have hsR : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hsp : (0 : ℝ) < s := by linarith
  have ht : 0 < t := one_div_pos.mpr hsp
  have ht3 : t ≤ 1 / 3 := by dsimp [t]; exact one_div_le_one_div_of_le (by norm_num) hsR
  have ht1 : t < 1 := by linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have haq : a ≤ 1 - 3 * t ^ 2 := by
    have hb : 0 ≤ 2 - 5 * t + t ^ 3 := by nlinarith [pow_nonneg ht.le 3]
    have hc := mul_nonneg (sq_nonneg t) hb
    dsimp [a]
    nlinarith [hc]
  have hmu : 3 ≤ ((s ^ 2 : ℕ) : ℝ) * (3 * t ^ 2) := by
    dsimp [t]
    push_cast
    field_simp
    nlinarith
  have hp : a ^ (s ^ 2) ≤ 1 / 4 :=
    shrinking_power_bound a (3 * t ^ 2) (s ^ 2) ha (by positivity) haq hmu
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
  have ht3t : t ^ 3 ≤ t := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht2)]
  have hg0 : 0 ≤ g := by dsimp [g]; nlinarith [pow_nonneg ht.le 3]
  have hg2 : g ≤ 2 := by dsimp [g]; nlinarith
  have hN : 3 ≤ 5 * s ^ 2 + 3 := by omega
  have htN : t ^ (5 * s ^ 2 + 3) ≤ t ^ 3 :=
    pow_le_pow_of_le_one ht.le ht1.le hN
  have ht33 : t ^ 3 ≤ (1 / 3 : ℝ) ^ 3 := pow_le_pow_left₀ ht.le ht3 3
  have hhub : 52 / 81 ≤ (1 - t) * (1 - t ^ (5 * s ^ 2 + 3)) := by
    have hn : 0 ≤ t ^ (5 * s ^ 2 + 3) := pow_nonneg ht.le _
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 3 - t)
      (by nlinarith : 0 ≤ 1 / 27 - t ^ (5 * s ^ 2 + 3))]
  have hneg : a ^ (s ^ 2) * g ≤ 1 / 2 := by
    nlinarith [pow_nonneg ha (s ^ 2), mul_nonneg
      (by linarith : 0 ≤ 1 / 4 - a ^ (s ^ 2)) (by linarith : 0 ≤ 2 - g)]
  have hodd : Odd (s ^ 2) := ho.pow
  have heval : (seedPolynomial (s ^ 2)).eval (-1 + t) =
      (1 - t) * (1 - t ^ (5 * s ^ 2 + 3)) - a ^ (s ^ 2) * g := by
    simp only [seedPolynomial, eval_add, eval_mul, eval_sub, eval_pow, eval_ofNat,
      eval_X, eval_one]
    have hf : 5 * (-1 + t) ^ 3 + 5 * (-1 + t) ^ 4 + (-1 + t) ^ 5 = -a := by
      dsimp [a]; ring
    have hg : 3 * (-1 + t) ^ 2 + (-1 + t) ^ 3 = g := by dsimp [g]; ring
    rw [hf, hg, hodd.neg_pow]
    ring
  change 0 < (seedPolynomial (s ^ 2)).eval (-1 + t)
  rw [heval]
  linarith

/-- A seed exists in each shrinking right-hand interval; this is not density. -/
theorem seed_root_right (s : ℕ) (hs : 3 ≤ s) (ho : Odd s) :
    ∃ r : ℝ, -1 < r ∧ r < -1 + 1 / (s : ℝ) ∧
      (seedPolynomial (s ^ 2)).IsRoot r := by
  have hsp : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hleft := seed_at_minus_one (s ^ 2) ho.pow
  have hright := seed_upper_positive s hs ho
  obtain ⟨r, hr, hzero⟩ := intermediate_value_Ioo
    (by linarith [one_div_pos.mpr hsp] : (-1 : ℝ) ≤ -1 + 1 / (s : ℝ))
    (seedPolynomial (s ^ 2)).continuous.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo ((seedPolynomial (s ^ 2)).eval (-1))
      ((seedPolynomial (s ^ 2)).eval (-1 + 1 / (s : ℝ))) by
      constructor <;> linarith)
  exact ⟨r, hr.1, hr.2, hzero⟩

/-- Genuine graph roots, with the same finite graphs satisfying every total condition. -/
theorem actual_seed_root_right (s : ℕ) (hs : 3 ≤ s) (ho : Odd s) :
    ∃ r : ℝ, -1 < r ∧ r < -1 + 1 / (s : ℝ) ∧
      (totalPolynomial (seedGraph (s ^ 2))).IsRoot r ∧
      totalPolynomial (seedGraph (s ^ 2)) ≠ 0 ∧
      (∀ v, ∃ u, (seedGraph (s ^ 2)).Adj v u) := by
  obtain ⟨r, hl, hr, hz⟩ := seed_root_right s hs ho
  refine ⟨r, hl, hr, ?_, ?_, ?_⟩
  · simpa [seed_graph_polynomial] using hz
  · intro he
    have hm := seed_at_minus_one (s ^ 2) ho.pow
    rw [← seed_graph_polynomial, he] at hm
    norm_num at hm
  · intro v
    cases v with
    | inl v =>
      obtain ⟨u⟩ := seedBaseNonempty (s ^ 2)
      exact ⟨.inr u, trivial⟩
    | inr v => exact ⟨.inl (), trivial⟩

#print axioms actual_seed_root_right

#print axioms seed_root_right

end D5.S3.Combinatorics.Graph.Domination.TotalDominationSeeds
