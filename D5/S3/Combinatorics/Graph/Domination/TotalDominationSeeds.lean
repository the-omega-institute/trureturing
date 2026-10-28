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
import Mathlib.Analysis.Complex.Basic
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
  simp only [Finset.sum_insert, Finset.sum_singleton, show (∅ : Finset Unit) ∉
      ({ {()} } : Finset (Finset Unit)) by decide,
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
      simpa only [card_empty, pow_zero] using eq_sub_iff_add_eq.mpr he
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
  | zero => change Fintype.card (Fin 3) = 3; norm_num
  | succ m ih =>
    change Fintype.card (Fin 5 ⊕ SeedBase m) = _
    rw [Fintype.card_sum, ih]
    norm_num
    omega

private theorem seed_base_polynomial (m : ℕ) : totalPolynomial (seedBaseGraph m) =
    (5 * X ^ 3 + 5 * X ^ 4 + X ^ 5) ^ m * (3 * X ^ 2 + X ^ 3) := by
  induction m with
  | zero =>
    simp only [pow_zero, one_mul]
    convert clique_three_polynomial using 1
    rfl
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

private theorem total_equiv (G : SimpleGraph V) (e : W ≃ V) (S : Finset W) :
    IsTotal (G.comap e) S ↔ IsTotal G (S.map e.toEmbedding) := by
  constructor
  · intro h v
    obtain ⟨u, hu, hadj⟩ := h (e.symm v)
    exact ⟨e u, mem_map.mpr ⟨u, hu, rfl⟩, by simpa using hadj⟩
  · intro h w
    obtain ⟨v, hv, hadj⟩ := h (e w)
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hv
    exact ⟨u, hu, hadj⟩

private theorem polynomial_equiv [Fintype V] [Fintype W]
    (G : SimpleGraph V) (e : W ≃ V) :
    totalPolynomial (G.comap e) = totalPolynomial G := by
  classical
  unfold totalPolynomial
  exact Fintype.sum_equiv e.finsetCongr _ _ (fun S => by
    simp [Equiv.finsetCongr_apply, total_equiv G e S])

/-- Finite labelled witnesses to the right-hand accumulation at minus one. -/
theorem labelled_seed_root (s : ℕ) (hs : 3 ≤ s) (ho : Odd s) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℝ),
      n = 5 * s ^ 2 + 4 ∧ 2 ≤ n ∧ -1 < r ∧ r < -1 + 1 / (s : ℝ) ∧
      (totalPolynomial G).IsRoot r ∧ totalPolynomial G ≠ 0 ∧
      (∀ v, ∃ u, G.Adj v u) := by
  classical
  obtain ⟨r, hl, hr, hz, hnz, hni⟩ := actual_seed_root_right s hs ho
  let V := Unit ⊕ SeedBase (s ^ 2)
  let n := Fintype.card V
  let e : Fin n ≃ V := (Fintype.equivFin V).symm
  let G := (seedGraph (s ^ 2)).comap e
  have hp : totalPolynomial G = totalPolynomial (seedGraph (s ^ 2)) :=
    polynomial_equiv _ e
  have hn : n = 5 * s ^ 2 + 4 := by
    dsimp [n, V]
    rw [Fintype.card_sum, seed_base_card]
    simp
    omega
  refine ⟨n, G, r, hn, by omega, hl, hr, ?_, ?_, ?_⟩
  · rwa [hp]
  · rwa [hp]
  · intro v
    obtain ⟨u, hu⟩ := hni (e v)
    exact ⟨e.symm u, by simpa [G] using hu⟩

/-- Arbitrarily small positive shifts are realized by nonzero actual graph polynomials. -/
theorem arbitrarily_small_positive_shift (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℝ),
      2 ≤ n ∧ 0 < 1 + r ∧ 1 + r < ε ∧
      (totalPolynomial G).IsRoot r ∧ totalPolynomial G ≠ 0 ∧
      (∀ v, ∃ u, G.Adj v u) := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  let s := 2 * k + 3
  have hs : 3 ≤ s := by dsimp [s]; omega
  have ho : Odd s := ⟨k + 1, by dsimp [s]; omega⟩
  obtain ⟨n, G, r, hn, hn2, hl, hr, hz, hnz, hni⟩ := labelled_seed_root s hs ho
  have hks : (k : ℝ) + 1 ≤ s := by dsimp [s]; push_cast; linarith
  have hsmall : 1 / (s : ℝ) < ε :=
    lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) hks) hk
  exact ⟨n, G, r, hn2, by linarith, by linarith, hz, hnz, hni⟩

/-- The same actual-subset definition with complex coefficients. -/
noncomputable def complexPolynomial [Fintype V] (G : SimpleGraph V) : ℂ[X] := by
  classical
  exact ∑ S : Finset V, if IsTotal G S then X ^ S.card else 0

private theorem complex_polynomial_map [Fintype V] (G : SimpleGraph V) :
    complexPolynomial G = (totalPolynomial G).map Complex.ofRealHom := by
  classical
  unfold complexPolynomial totalPolynomial
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp

/-- The exact original whole-plane target. No theorem asserting this is supplied here. -/
def WholePlaneDensity : Prop :=
  ∀ (z : ℂ) (ε : ℝ), 0 < ε →
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℂ),
      2 ≤ n ∧ (∀ v, ∃ u, G.Adj v u) ∧ complexPolynomial G ≠ 0 ∧
      (complexPolynomial G).IsRoot w ∧ ‖w - z‖ < ε

/-- Genuine complex graph roots accumulate at minus one from the real right side. -/
theorem complex_seed_accumulation (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℝ),
      2 ≤ n ∧ (∀ v, ∃ u, G.Adj v u) ∧ complexPolynomial G ≠ 0 ∧
      (complexPolynomial G).IsRoot (r : ℂ) ∧
      0 < 1 + r ∧ ‖(r : ℂ) - (-1 : ℂ)‖ < ε := by
  obtain ⟨n, G, r, hn, hl, hr, hz, hnz, hni⟩ := arbitrarily_small_positive_shift ε hε
  refine ⟨n, G, r, hn, hni, ?_, ?_, hl, ?_⟩
  · rw [complex_polynomial_map]
    exact (Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr hnz
  · rw [complex_polynomial_map]
    exact hz.map
  · have he : (r : ℂ) - (-1 : ℂ) = ((1 + r : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl]
    exact hr


/-- The base consists of m+1 disjoint actual edges. -/
def EdgeBase : ℕ → Type
  | 0 => Fin 2
  | m + 1 => Fin 2 ⊕ EdgeBase m

instance edgeBaseFintype : (m : ℕ) → Fintype (EdgeBase m)
  | 0 => inferInstanceAs (Fintype (Fin 2))
  | m + 1 => @instFintypeSum (Fin 2) (EdgeBase m) _ (edgeBaseFintype m)

instance edgeBaseNonempty (m : ℕ) : Nonempty (EdgeBase m) := by
  cases m with
  | zero => exact inferInstanceAs (Nonempty (Fin 2))
  | succ m => exact ⟨Sum.inl 0⟩

/-- A disjoint matching, whose cone is the friendship graph. -/
def edgeBaseGraph : (m : ℕ) → SimpleGraph (EdgeBase m)
  | 0 => ⊤
  | m + 1 => unionGraph (⊤ : SimpleGraph (Fin 2)) (edgeBaseGraph m)

/-- Each triangle has the same hub and a separate pair of outer vertices. -/
def friendshipGraph (m : ℕ) : SimpleGraph (Unit ⊕ EdgeBase m) :=
  coneGraph (edgeBaseGraph m)

private theorem edge_polynomial : totalPolynomial (⊤ : SimpleGraph (Fin 2)) = X ^ 2 := by
  have ht : ∀ S : Finset (Fin 2), IsTotal (⊤ : SimpleGraph (Fin 2)) S ↔ S = univ := by
    decide +kernel
  classical
  unfold totalPolynomial
  simp_rw [ht]
  simp

private theorem edge_base_card (m : ℕ) : Fintype.card (EdgeBase m) = 2 * (m + 1) := by
  induction m with
  | zero => change Fintype.card (Fin 2) = _; simp
  | succ m ih =>
    change Fintype.card (Fin 2 ⊕ EdgeBase m) = _
    rw [Fintype.card_sum, ih]
    simp
    omega

private theorem edge_base_polynomial (m : ℕ) :
    totalPolynomial (edgeBaseGraph m) = X ^ (2 * (m + 1)) := by
  induction m with
  | zero =>
    convert edge_polynomial using 1
    rfl
  | succ m ih =>
    change totalPolynomial (unionGraph (⊤ : SimpleGraph (Fin 2)) (edgeBaseGraph m)) = _
    rw [union_polynomial, edge_polynomial, ih, ← pow_add]
    congr 1
    omega

/-- The known friendship formula, used here to construct unbounded actual roots. -/
noncomputable def friendshipPolynomial (m : ℕ) : ℝ[X] :=
  X * ((1 + X) ^ (2 * (m + 1)) - 1) + X ^ (2 * (m + 1))

private theorem friendship_graph_polynomial (m : ℕ) :
    totalPolynomial (friendshipGraph m) = friendshipPolynomial m := by
  rw [friendshipGraph, cone_polynomial, edge_base_card, edge_base_polynomial]
  rfl

private theorem friendship_eval_negative (m : ℕ) (q : ℝ) :
    (friendshipPolynomial m).eval (-q) =
      q ^ (2 * (m + 1)) + q - q * (q - 1) ^ (2 * (m + 1)) := by
  simp only [friendshipPolynomial, eval_add, eval_mul, eval_sub, eval_pow, eval_X,
    eval_one]
  have he : Even (2 * (m + 1)) := even_two_mul _
  have hn : 1 + -q = -(q - 1) := by ring
  rw [hn, he.neg_pow, he.neg_pow]
  ring

private theorem friendship_far_negative (m : ℕ) :
    (friendshipPolynomial m).eval (-(2 * (m + 1) + 2 : ℝ)) < 0 := by
  let e : ℕ := 2 * (m + 1)
  let q : ℝ := e + 2
  have he : 2 ≤ e := by dsimp [e]; omega
  have heR : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hq : 4 ≤ q := by dsimp [q]; linarith
  have hqp : 0 < q := by linarith
  have hi : 0 < 1 / q := one_div_pos.mpr hqp
  have hi1 : 1 / q ≤ 1 := (div_le_one hqp).mpr (by linarith)
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(1 / q) by linarith) e
  have hnorm : (q - 1) ^ e = q ^ e * (1 - 1 / q) ^ e := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hB : 2 ≤ q * (1 - 1 / q) ^ e := by
    have hmul := mul_le_mul_of_nonneg_left hb hqp.le
    have heq : q * (1 + (e : ℝ) * -(1 / q)) = 2 := by
      dsimp [q]
      field_simp
      ring
    simpa only [heq, sub_eq_add_neg] using hmul
  have hpow : q < q ^ e := by
    have hh : q ^ 2 ≤ q ^ e := pow_le_pow_right₀ (by linarith : 1 ≤ q) he
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hB (pow_nonneg hqp.le e)
  have hval := friendship_eval_negative m q
  have hqdef : (2 * ((m : ℝ) + 1) + 2) = q := by dsimp [q, e]; push_cast; ring
  rw [hqdef, hval]
  change q ^ e + q - q * (q - 1) ^ e < 0
  rw [hnorm]
  nlinarith

/-- An actual friendship root lies to the left of any prescribed negative bound. -/
theorem friendship_root_unbounded (R : ℝ) (hR : 2 < R) :
    ∃ (m : ℕ) (r : ℝ), r < -R ∧
      (totalPolynomial (friendshipGraph m)).IsRoot r ∧
      totalPolynomial (friendshipGraph m) ≠ 0 ∧
      (∀ v, ∃ u, (friendshipGraph m).Adj v u) := by
  have hRp : 0 < R := by linarith
  let a : ℝ := (1 - 1 / R) ^ 2
  have hi : 0 < 1 / R := one_div_pos.mpr hRp
  have hi1 : 1 / R < 1 := (div_lt_one hRp).mpr (by linarith)
  have ha : 0 ≤ a := sq_nonneg _
  have ha1 : a < 1 := by dsimp [a]; nlinarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hRp) ha1
  have hmp : a ^ (m + 1) < 1 / R :=
    lt_of_le_of_lt (pow_le_pow_of_le_one ha ha1.le (by omega : m ≤ m + 1)) hm
  have hval : 0 < (friendshipPolynomial m).eval (-R) := by
    rw [friendship_eval_negative]
    have hnorm : (R - 1) ^ (2 * (m + 1)) =
        R ^ (2 * (m + 1)) * a ^ (m + 1) := by
      dsimp [a]
      rw [← pow_mul, ← mul_pow]
      have heq : R * (1 - 1 / R) = R - 1 := by field_simp
      rw [heq]
    rw [hnorm]
    have hlt : R * a ^ (m + 1) < 1 := by simpa [mul_comm] using (lt_div_iff₀ hRp).mp hmp
    have hpos := mul_pos (pow_pos hRp (2 * (m + 1))) (sub_pos.mpr hlt)
    nlinarith
  have hfar := friendship_far_negative m
  have horder : -(2 * (m + 1) + 2 : ℝ) ≤ -R := by
    by_contra h
    have hRlarge : (2 * (m + 1) + 2 : ℝ) < R := by linarith
    have he : 1 ≤ (m + 1 : ℕ) := by omega
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(1 / R) by linarith) (2 * (m + 1))
    have hnorm : (1 - 1 / R) ^ (2 * (m + 1)) = a ^ (m + 1) := by
      dsimp [a]; rw [pow_mul]
    rw [show 1 + -(1 / R) = 1 - 1 / R by ring, hnorm] at hb
    have hmul := mul_le_mul_of_nonneg_left hb hRp.le
    have hcancel : R * (1 + (2 * (m + 1) : ℕ) * -(1 / R)) = R - 2 * (m + 1) := by
      push_cast
      field_simp
      ring
    rw [hcancel] at hmul
    have hlt : R * a ^ (m + 1) < 1 := by simpa [mul_comm] using (lt_div_iff₀ hRp).mp hmp
    push_cast at hmul
    linarith
  obtain ⟨r, hr, hz⟩ := intermediate_value_Ioo horder
    (friendshipPolynomial m).continuous.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo
      ((friendshipPolynomial m).eval (-(2 * (m + 1) + 2 : ℝ)))
      ((friendshipPolynomial m).eval (-R)) from ⟨hfar, hval⟩)
  refine ⟨m, r, hr.2, ?_, ?_, ?_⟩
  · simpa [friendship_graph_polynomial] using hz
  · intro hzero
    rw [← friendship_graph_polynomial, hzero] at hval
    simpa using hval
  · intro v
    cases v with
    | inl v =>
      obtain ⟨u⟩ := edgeBaseNonempty m
      exact ⟨.inr u, trivial⟩
    | inr v => exact ⟨.inl (), trivial⟩


/-- The unbounded negative roots have the exact finite labels of the original target. -/
theorem labelled_unbounded_negative_roots (R : ℝ) (hR : 2 < R) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℝ),
      2 ≤ n ∧ r < -R ∧ (∀ v, ∃ u, G.Adj v u) ∧
      complexPolynomial G ≠ 0 ∧ (complexPolynomial G).IsRoot (r : ℂ) := by
  classical
  obtain ⟨m, r, hr, hz, hnz, hni⟩ := friendship_root_unbounded R hR
  let V := Unit ⊕ EdgeBase m
  let n := Fintype.card V
  let e : Fin n ≃ V := (Fintype.equivFin V).symm
  let G := (friendshipGraph m).comap e
  have hp : totalPolynomial G = totalPolynomial (friendshipGraph m) :=
    polynomial_equiv _ e
  have hn : 2 ≤ n := by
    dsimp [n, V]
    rw [Fintype.card_sum, edge_base_card]
    simp
    omega
  refine ⟨n, G, r, hn, hr, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨u, hu⟩ := hni (e v)
    exact ⟨e.symm u, by simpa [G] using hu⟩
  · rw [complex_polynomial_map, hp]
    exact (Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr hnz
  · rw [complex_polynomial_map, hp]
    exact hz.map

#print axioms labelled_unbounded_negative_roots

#print axioms friendship_root_unbounded

#print axioms complex_seed_accumulation

#print axioms arbitrarily_small_positive_shift

#print axioms actual_seed_root_right

#print axioms seed_root_right

end D5.S3.Combinatorics.Graph.Domination.TotalDominationSeeds
