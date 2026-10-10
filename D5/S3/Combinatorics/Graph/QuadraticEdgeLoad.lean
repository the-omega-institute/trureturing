/- GID: D5/S3/Combinatorics/Graph/QuadraticEdgeLoad
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/QuadraticEdgeLoad
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric]
   utility: none
   digest: Geometric edge shares characterize the maximum-degree quadratic load equality. -/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace D5.S3.Combinatorics.Graph.QuadraticEdgeLoad

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Coordinates outside the oriented edge set are harmless bounded extensions. -/
def Feasible (a : V → V → ℝ) : Prop :=
  (∀ b c, 0 ≤ a b c ∧ a b c ≤ 1) ∧
    ∀ b c, G.Adj b c → a b c + a c b = 1

/-- The first argument is the vertex paying the squared share. -/
def load (a : V → V → ℝ) (b : V) : ℝ :=
  ∑ c ∈ G.neighborFinset b, (a b c) ^ 2

variable [Nonempty V]

noncomputable def maxLoad (a : V → V → ℝ) : ℝ :=
  univ.sup' univ_nonempty (load G a)

/-- The infimum is over actual feasible shares, with no duality assumption. -/
noncomputable def kappa : ℝ :=
  sInf (maxLoad G '' {a | Feasible G a})

omit [Fintype V] [DecidableRel G.Adj] [Nonempty V] in
private theorem half_feasible : Feasible G (fun _ _ => 1 / 2) := by
  constructor
  · intro b c; norm_num
  · intro b c h; norm_num

private theorem load_le_maxLoad (a : V → V → ℝ) (b : V) :
    load G a b ≤ maxLoad G a := le_sup' _ (mem_univ b)

private theorem kappa_le (a : V → V → ℝ) (ha : Feasible G a) :
    kappa G ≤ maxLoad G a := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨a, ha, rfl⟩
    exact le_trans (sum_nonneg fun c _ => sq_nonneg (a (Classical.arbitrary V) c))
      (load_le_maxLoad G a (Classical.arbitrary V))
  · exact ⟨a, ha, rfl⟩

private theorem continuous_maxLoad : Continuous (maxLoad G) := by
  unfold maxLoad
  apply Continuous.finset_sup'_apply
  intro b hb
  unfold load
  fun_prop

/-- The optimization defining kappa has an actual feasible minimizer. -/
theorem minimum_attained :
    ∃ a, Feasible G a ∧ maxLoad G a = kappa G := by
  have hc : IsCompact ({a | Feasible G a} : Set (V → V → ℝ)) := by
    have he : IsClosed {a : V → V → ℝ |
        ∀ b c, G.Adj b c → a b c + a c b = 1} := by
      simp_rw [Set.ofPred_forall]
      apply isClosed_iInter
      intro b
      apply isClosed_iInter
      intro c
      apply isClosed_iInter
      intro h
      exact isClosed_eq (by fun_prop) continuous_const
    have hi := (isCompact_Icc : IsCompact
      (Set.Icc (fun _ _ : V => (0 : ℝ)) (fun _ _ : V => (1 : ℝ))))
    convert hi.inter_right he using 1
    ext a
    simp only [Set.mem_inter_iff, Set.mem_Icc, Pi.le_def, Set.mem_ofPred_eq, Feasible]
    aesop
  obtain ⟨a, ha, hm⟩ := hc.exists_isMinOn ⟨_, half_feasible G⟩
    (continuous_maxLoad G).continuousOn
  refine ⟨a, ha, le_antisymm ?_ (kappa_le G a ha)⟩
  apply le_csInf
  · exact ⟨maxLoad G a, a, ha, rfl⟩
  · rintro r ⟨b, hb, rfl⟩
    exact hm hb

omit [Nonempty V] in
private theorem half_load (b : V) :
    load G (fun _ _ => 1 / 2) b = (G.degree b : ℝ) / 4 := by
  simp [load, SimpleGraph.card_neighborFinset_eq_degree]
  ring

private theorem kappa_le_maxDegree : kappa G ≤ (G.maxDegree : ℝ) / 4 := by
  apply le_trans (kappa_le G _ (half_feasible G))
  apply sup'_le
  intro b hb
  rw [half_load]
  exact div_le_div_of_nonneg_right (by exact_mod_cast G.degree_le_maxDegree b) (by norm_num)

omit [Nonempty V] in
private theorem deficiency_reachable
    (h : ¬ ∃ C : G.ConnectedComponent, ∀ b ∈ C.supp, G.degree b = G.maxDegree)
    (b : V) : ∃ c, G.Reachable b c ∧ G.degree c < G.maxDegree := by
  by_contra! hn
  apply h
  refine ⟨G.connectedComponentMk b, ?_⟩
  intro c hc
  have hr : G.Reachable b c := by
    apply SimpleGraph.ConnectedComponent.exact
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hc |>.symm
  exact le_antisymm (G.degree_le_maxDegree c) (hn c hr)

omit [Nonempty V] in
private theorem exists_deficiency_layers
    (h : ¬ ∃ C : G.ConnectedComponent, ∀ b ∈ C.supp, G.degree b = G.maxDegree) :
    ∃ l : V → ℕ,
      (∀ b, l b = 0 ↔ G.degree b < G.maxDegree) ∧
      (∀ b c, G.Adj b c → l b ≤ l c + 1) ∧
      (∀ b, 0 < l b → ∃ c, G.Adj b c ∧ l b = l c + 1) := by
  classical
  have hex (b : V) : ∃ n : ℕ, ∃ c, G.degree c < G.maxDegree ∧
      ∃ p : G.Walk b c, p.length = n := by
    obtain ⟨c, hr, hc⟩ := deficiency_reachable G h b
    obtain ⟨p⟩ := hr
    exact ⟨p.length, c, hc, p, rfl⟩
  let l : V → ℕ := fun b => Nat.find (hex b)
  have witness (b : V) : ∃ c, G.degree c < G.maxDegree ∧
      ∃ p : G.Walk b c, p.length = l b := Nat.find_spec (hex b)
  have minimal (b c : V) (hc : G.degree c < G.maxDegree) (p : G.Walk b c) :
      l b ≤ p.length := Nat.find_min' (hex b) ⟨c, hc, p, rfl⟩
  refine ⟨l, ?_, ?_, ?_⟩
  · intro b
    constructor
    · intro hb
      obtain ⟨c, hc, p, hp⟩ := witness b
      have hbc : b = c := SimpleGraph.Walk.eq_of_length_eq_zero (hp.trans hb)
      exact hbc ▸ hc
    · intro hb
      exact Nat.eq_zero_of_le_zero (minimal b b hb SimpleGraph.Walk.nil)
  · intro b c hbc
    obtain ⟨d, hd, p, hp⟩ := witness c
    simpa [hp] using minimal b d hd (p.cons hbc)
  · intro b hb
    obtain ⟨d, hd, p, hp⟩ := witness b
    cases p with
    | nil => simp at hp; omega
    | @cons b c d hbc p =>
      refine ⟨c, hbc, ?_⟩
      have hl := minimal c d hd p
      obtain ⟨e, he, q, hq⟩ := witness c
      have hu := minimal b e he (q.cons hbc)
      simp only [SimpleGraph.Walk.length_cons] at hp hu
      omega

private noncomputable def epsilon (D j : ℕ) : ℝ :=
  (1 / 2) * (1 / (8 * (D : ℝ))) ^ j

private theorem epsilon_bounds {D : ℕ} (hD : 0 < D) (j : ℕ) :
    0 < epsilon D j ∧ epsilon D j ≤ 1 / 2 := by
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hp : 0 < (1 : ℝ) / (8 * D) := by positivity
  have hu : (1 : ℝ) / (8 * D) ≤ 1 := by
    apply (div_le_one (by positivity)).2; linarith
  constructor
  · unfold epsilon; positivity
  · unfold epsilon
    have := pow_le_one₀ hp.le hu (n := j)
    nlinarith

private theorem epsilon_step {D : ℕ} (hD : 0 < D) (j : ℕ) :
    2 * (D : ℝ) * epsilon D (j + 1) = epsilon D j / 4 := by
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  unfold epsilon
  rw [pow_succ]
  field_simp
  ring

private noncomputable def layerShare (D : ℕ) (l : V → ℕ) (b c : V) : ℝ :=
  if l c < l b then 1 / 2 - epsilon D (l b)
  else if l b < l c then 1 / 2 + epsilon D (l c)
  else 1 / 2

omit [Fintype V] [DecidableRel G.Adj] [Nonempty V] in
private theorem layerShare_feasible {D : ℕ} (hD : 0 < D) (l : V → ℕ) :
    Feasible G (layerShare D l) := by
  constructor
  · intro b c
    have hb := epsilon_bounds hD (l b)
    have hc := epsilon_bounds hD (l c)
    unfold layerShare
    split_ifs <;> constructor <;> linarith
  · intro b c hbc
    unfold layerShare
    split_ifs <;> first | omega | linarith

omit [Fintype V] [DecidableRel G.Adj] [Nonempty V] in
private theorem layerShare_sq_le {D : ℕ} (hD : 0 < D) (l : V → ℕ)
    (hl : ∀ b c, G.Adj b c → l b ≤ l c + 1)
    (b c : V) (hbc : G.Adj b c) :
    (layerShare D l b c) ^ 2 ≤ 1 / 4 + 2 * epsilon D (l b + 1) := by
  have hb := epsilon_bounds hD (l b)
  have hn := epsilon_bounds hD (l b + 1)
  unfold layerShare
  split_ifs with hc hcb
  · nlinarith [mul_nonneg hb.1.le (sub_nonneg.mpr hb.2)]
  · have he : l c = l b + 1 := by have := hl c b hbc.symm; omega
    rw [he]
    nlinarith [mul_nonneg hn.1.le (sub_nonneg.mpr hn.2)]
  · nlinarith

omit [Nonempty V] in
private theorem strict_layer_load {D : ℕ} (hD : 0 < D) (l : V → ℕ)
    (hdeg : ∀ b, G.degree b ≤ D)
    (hz : ∀ b, l b = 0 → G.degree b < D)
    (hl : ∀ b c, G.Adj b c → l b ≤ l c + 1)
    (hp : ∀ b, 0 < l b → ∃ c, G.Adj b c ∧ l b = l c + 1) (b : V) :
    load G (layerShare D l) b < (D : ℝ) / 4 := by
  classical
  have hdn : (G.degree b : ℝ) ≤ D := by exact_mod_cast hdeg b
  have he := epsilon_bounds hD (l b)
  have hn := epsilon_bounds hD (l b + 1)
  have hs := epsilon_step hD (l b)
  by_cases hb : l b = 0
  · have hd : (G.degree b : ℝ) + 1 ≤ D := by exact_mod_cast hz b hb
    have hsum : load G (layerShare D l) b ≤
        (G.degree b : ℝ) * (1 / 4 + 2 * epsilon D (0 + 1)) := by
      unfold load
      calc
        _ ≤ ∑ _c ∈ G.neighborFinset b, (1 / 4 + 2 * epsilon D (0 + 1)) := by
          apply sum_le_sum
          intro c hc
          simpa only [hb] using layerShare_sq_le G hD l hl b c
            ((G.mem_neighborFinset b c).mp hc)
        _ = _ := by simp [SimpleGraph.card_neighborFinset_eq_degree]; ring
    have hs0 := epsilon_step hD 0
    have he0 : epsilon D 0 = 1 / 2 := by simp [epsilon]
    rw [he0] at hs0
    have hm : (G.degree b : ℝ) * epsilon D (0 + 1) ≤
        D * epsilon D (0 + 1) := mul_le_mul_of_nonneg_right hdn (epsilon_bounds hD 1).1.le
    nlinarith
  · obtain ⟨p, hbp, hlp⟩ := hp b (Nat.pos_of_ne_zero hb)
    have hpmem : p ∈ G.neighborFinset b := (G.mem_neighborFinset b p).mpr hbp
    have hpred : (layerShare D l b p) ^ 2 ≤ 1 / 4 - epsilon D (l b) / 2 := by
      have hlt : l p < l b := by omega
      simp only [layerShare, if_pos hlt]
      nlinarith [mul_nonneg he.1.le (sub_nonneg.mpr he.2)]
    have hsum : load G (layerShare D l) b ≤
        (G.degree b : ℝ) * (1 / 4 + 2 * epsilon D (l b + 1)) - epsilon D (l b) / 2 := by
      unfold load
      calc
        _ ≤ ∑ c ∈ G.neighborFinset b,
            ((1 / 4 + 2 * epsilon D (l b + 1)) - if c = p then epsilon D (l b) / 2 else 0) := by
          apply sum_le_sum
          intro c hc
          by_cases hcp : c = p
          · subst c
            simp only [ite_true]
            simp
            linarith
          · simp only [if_neg hcp, sub_zero]
            exact layerShare_sq_le G hD l hl b c ((G.mem_neighborFinset b c).mp hc)
        _ = _ := by
          rw [sum_sub_distrib]
          simp [SimpleGraph.card_neighborFinset_eq_degree, hpmem]
          ring
    have hm : (G.degree b : ℝ) * epsilon D (l b + 1) ≤
        D * epsilon D (l b + 1) := mul_le_mul_of_nonneg_right hdn hn.1.le
    nlinarith

/-- Without a maximum-degree regular component, actual shares beat the degree bound. -/
theorem strict_allocation_of_no_regular_component
    (h : ¬ ∃ C : G.ConnectedComponent, ∀ b ∈ C.supp, G.degree b = G.maxDegree) :
    ∃ a, Feasible G a ∧ ∀ b, load G a b < (G.maxDegree : ℝ) / 4 := by
  have hD : 0 < G.maxDegree := by
    obtain ⟨c, hr, hc⟩ := deficiency_reachable G h (Classical.arbitrary V)
    omega
  obtain ⟨l, hz, hl, hp⟩ := exists_deficiency_layers G h
  refine ⟨layerShare G.maxDegree l, layerShare_feasible G hD l, ?_⟩
  exact strict_layer_load G hD l (G.degree_le_maxDegree) (fun b hb => (hz b).mp hb) hl hp

omit [Nonempty V] in
private theorem reverse_sum (S : Finset V)
    (hS : ∀ b c, G.Adj b c → (b ∈ S ↔ c ∈ S)) (f : V → V → ℝ) :
    (∑ b ∈ S, ∑ c ∈ G.neighborFinset b, f c b) =
      ∑ b ∈ S, ∑ c ∈ G.neighborFinset b, f b c := by
  classical
  have expand (f : V → V → ℝ) :
      (∑ b ∈ S, ∑ c ∈ G.neighborFinset b, f b c) =
        ∑ b : V, ∑ c : V, if b ∈ S ∧ G.Adj b c then f b c else 0 := by
    simp only [SimpleGraph.neighborFinset_eq_filter, sum_filter, ite_and]
    simp only [sum_ite_irrel, sum_const_zero, sum_ite_mem, univ_inter]
  rw [expand (fun b c => f c b), expand f, sum_comm]
  apply sum_congr rfl
  intro b hb
  apply sum_congr rfl
  intro c hc
  have he : (c ∈ S ∧ G.Adj c b) ↔ (b ∈ S ∧ G.Adj b c) := by
    constructor
    · rintro ⟨hc, hcb⟩
      exact ⟨(hS c b hcb).mp hc, hcb.symm⟩
    · rintro ⟨hb, hbc⟩
      exact ⟨(hS b c hbc).mp hb, hbc.symm⟩
  simp only [he]

private theorem component_lower_bound (C : G.ConnectedComponent)
    (hC : ∀ b ∈ C.supp, G.degree b = G.maxDegree)
    (a : V → V → ℝ) (ha : Feasible G a) :
    (G.maxDegree : ℝ) / 4 ≤ maxLoad G a := by
  classical
  let S := C.supp.toFinset
  have hS (b c : V) (hbc : G.Adj b c) : b ∈ S ↔ c ∈ S := by
    simpa [S] using C.mem_supp_congr_adj hbc
  have hne : S.Nonempty := by simpa [S] using C.nonempty_supp
  have hd (b : V) (hb : b ∈ S) : G.degree b = G.maxDegree :=
    hC b (by simpa [S] using hb)
  have rev := reverse_sum G S hS (fun b c => (a b c) ^ 2)
  have hpair : (S.card : ℝ) * (G.maxDegree : ℝ) / 2 ≤
      2 * ∑ b ∈ S, load G a b := by
    calc
      _ = ∑ b ∈ S, ∑ _c ∈ G.neighborFinset b, (1 / 2 : ℝ) := by
        symm
        calc
          _ = ∑ b ∈ S, (G.degree b : ℝ) * (1 / 2) := by
            simp [SimpleGraph.card_neighborFinset_eq_degree]
          _ = ∑ _b ∈ S, (G.maxDegree : ℝ) * (1 / 2) := by
            apply sum_congr rfl
            intro b hb
            rw [hd b hb]
          _ = _ := by simp; ring
      _ ≤ ∑ b ∈ S, ∑ c ∈ G.neighborFinset b, ((a b c)^2 + (a c b)^2) := by
        apply sum_le_sum
        intro b hb
        apply sum_le_sum
        intro c hc
        have he := ha.2 b c ((G.mem_neighborFinset b c).mp hc)
        nlinarith [sq_nonneg (a b c - a c b)]
      _ = 2 * ∑ b ∈ S, load G a b := by
        simp only [sum_add_distrib]
        rw [rev]
        unfold load
        ring
  have hu : (∑ b ∈ S, load G a b) ≤ S.card * maxLoad G a := by
    calc
      _ ≤ ∑ _b ∈ S, maxLoad G a := sum_le_sum fun b _ => load_le_maxLoad G a b
      _ = _ := by simp
  have hn : (0 : ℝ) < S.card := by exact_mod_cast card_pos.mpr hne
  nlinarith

/-- Equality holds precisely when one actual connected component is maximum-degree regular. -/
theorem maximum_degree_equality_iff :
    kappa G = (G.maxDegree : ℝ) / 4 ↔
      ∃ C : G.ConnectedComponent, ∀ b ∈ C.supp, G.degree b = G.maxDegree := by
  constructor
  · intro he
    by_contra hn
    obtain ⟨a, ha, hl⟩ := strict_allocation_of_no_regular_component G hn
    have hm : maxLoad G a < (G.maxDegree : ℝ) / 4 := by
      exact (sup'_lt_iff univ_nonempty).mpr (fun b _ => hl b)
    have := kappa_le G a ha
    linarith
  · rintro ⟨C, hC⟩
    obtain ⟨a, ha, hk⟩ := minimum_attained G
    apply le_antisymm (kappa_le_maxDegree G)
    rw [← hk]
    exact component_lower_bound G C hC a ha

end D5.S3.Combinatorics.Graph.QuadraticEdgeLoad
