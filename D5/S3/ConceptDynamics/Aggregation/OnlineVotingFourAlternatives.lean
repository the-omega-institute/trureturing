/- GID: D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.claim; result=D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.result; claim=D5/S3/ConceptDynamics/Aggregation/OnlineVotingFourAlternatives.claim
   digest: Four labeled arrivals obstruct the deterministic square-root-of-thirteen guarantee. -/

/- proof_shape: content
   escape_witness: leaf_strict, used by counterexample at the selected fixed election.
   admission_basis: open-problem-resolution (#32348; Refuted) -/

module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Deterministic online voting with four alternatives

The model and threshold are from Ghasemi, Seddighin and Seddighin,
*Distortion in Online Voting*, [arXiv:2611.25709v1](https://arxiv.org/abs/2611.25709v1),
§§3 and 6. The finite certificate is the four-alternative construction in
[trureturing issue #32348](https://github.com/the-omega-institute/trureturing/issues/32348).
-/

set_option autoImplicit false

public section

namespace D5.S3.ConceptDynamics.Aggregation.OnlineVotingFourAlternatives

abbrev Alternative := Fin 4
abbrev Label (n : ℕ) := Fin n ⊕ Alternative
/-- A full strict ballot for each voter, encoded by the four distinct ordinal positions. -/
abbrev Profile (n : ℕ) :=
  Fin n → {rank : Alternative → Alternative // Function.Injective rank}
abbrev Arrival := Fin 4 ≃ Alternative

/-- The order of arrivals and each labeled voter's pairwise comparisons on the prefix. -/
structure Observation (n : ℕ) where
  arrived : List Alternative
  prefers : Fin n → Alternative → Alternative → Bool

def observe {n : ℕ} (arrival : Arrival) (profile : Profile n) (round : ℕ) : Observation n where
  arrived := (List.ofFn arrival).take round
  prefers v a b := decide
    ((arrival.symm a).val < round ∧ (arrival.symm b).val < round ∧
      (profile v).val a < (profile v).val b)

/-- A deterministic rule receives all observations through the current round and its own
earlier decisions, in chronological order. True switches to the latest arrival. -/
abbrev Rule (n : ℕ) := List (Observation n) → List Bool → Bool

private def choose (switch : Bool) (incumbent latest : Alternative) : Alternative :=
  if switch then latest else incumbent

private def run {n : ℕ} (rule : Rule n) (arrival : Arrival) (o : ℕ → Observation n) :
    Alternative :=
  let d₂ := rule [o 1, o 2] []
  let d₃ := rule [o 1, o 2, o 3] [d₂]
  let d₄ := rule [o 1, o 2, o 3, o 4] [d₂, d₃]
  choose d₄ (choose d₃ (choose d₂ (arrival 0) (arrival 1)) (arrival 2)) (arrival 3)

def finalWinner {n : ℕ} (rule : Rule n) (arrival : Arrival) (profile : Profile n) : Alternative :=
  run rule arrival (observe arrival profile)

/-- Voters and alternatives lie in a single real-valued metric space. A full ballot
orders any ties once, and all observations inherit that order. -/
structure Election (n : ℕ) where
  Space : Type
  metric : MetricSpace Space
  location : Label n → Space
  arrival : Arrival
  profile : Profile n
  compatible : ∀ v a b,
    @dist Space metric.toDist (location (.inr a)) (location (.inl v)) <
      @dist Space metric.toDist (location (.inr b)) (location (.inl v)) →
    (profile v).val a < (profile v).val b

noncomputable def socialCost {n : ℕ} (election : Election n) (a : Alternative) : ℝ :=
  ∑ v : Fin n, @dist election.Space election.metric.toDist
    (election.location (.inr a)) (election.location (.inl v))

/-- At the positive threshold, bounding the cost against every alternative is
equivalent to bounding it against the minimum over the full election. -/
def claim : Prop :=
  ∃ rule : Rule 12, ∀ election : Election 12, ∀ a : Alternative,
    socialCost election (finalWinner rule election.arrival election.profile) ≤
      Real.sqrt 13 * socialCost election a

/-- The eight table positions are A, B, C, D and the four voter groups, in that order.
Entries are exact shortest-path distances from the four graphs in the certificate.
Positions may share a graph vertex. -/
private def graphTable (switchThree switchFour : Bool) : Fin 8 → Fin 8 → ℕ :=
  match switchThree, switchFour with
  | true, false => ![
      ![0, 2, 2, 0, 0, 1, 1, 1],
      ![2, 0, 2, 2, 2, 1, 1, 1],
      ![2, 2, 0, 2, 2, 3, 3, 1],
      ![0, 2, 2, 0, 0, 1, 1, 1],
      ![0, 2, 2, 0, 0, 1, 1, 1],
      ![1, 1, 3, 1, 1, 0, 0, 2],
      ![1, 1, 3, 1, 1, 0, 0, 2],
      ![1, 1, 1, 1, 1, 2, 2, 0]]
  | true, true => ![
      ![0, 2, 2, 2, 0, 1, 1, 1],
      ![2, 0, 0, 2, 2, 1, 1, 1],
      ![2, 0, 0, 2, 2, 1, 1, 1],
      ![2, 2, 2, 0, 2, 1, 1, 3],
      ![0, 2, 2, 2, 0, 1, 1, 1],
      ![1, 1, 1, 1, 1, 0, 0, 2],
      ![1, 1, 1, 1, 1, 0, 0, 2],
      ![1, 1, 1, 3, 1, 2, 2, 0]]
  | false, false => ![
      ![0, 4, 2, 2, 1, 3, 2, 3],
      ![4, 0, 4, 4, 5, 3, 2, 3],
      ![2, 4, 0, 2, 1, 3, 2, 1],
      ![2, 4, 2, 0, 1, 1, 2, 1],
      ![1, 5, 1, 1, 0, 2, 3, 2],
      ![3, 3, 3, 1, 2, 0, 1, 2],
      ![2, 2, 2, 2, 3, 1, 0, 1],
      ![3, 3, 1, 1, 2, 2, 1, 0]]
  | false, true => ![
      ![0, 2, 2, 2, 1, 1, 1, 2],
      ![2, 0, 2, 2, 3, 1, 1, 2],
      ![2, 2, 0, 2, 1, 1, 1, 0],
      ![2, 2, 2, 0, 3, 1, 3, 2],
      ![1, 3, 1, 3, 0, 2, 2, 1],
      ![1, 1, 1, 1, 2, 0, 2, 1],
      ![1, 1, 1, 3, 2, 2, 0, 1],
      ![2, 2, 0, 2, 1, 1, 1, 0]]

private theorem graph_self : ∀ (t u : Bool) (x : Fin 8), graphTable t u x x = 0 := by decide

private theorem graph_comm :
    ∀ (t u : Bool) (x y : Fin 8), graphTable t u x y = graphTable t u y x := by decide

private theorem graph_triangle : ∀ (t u : Bool) (x y z : Fin 8),
    graphTable t u x z ≤ graphTable t u x y + graphTable t u y z := by
  decide

/-- The actual labels 0 and 1 play the discarded and retained roles A and B.
The third and fourth labels always play C and D. -/
private def role (switchTwo : Bool) (a : Alternative) : Fin 4 :=
  if switchTwo ∨ 2 ≤ a.val then a else if a = 0 then 1 else 0

/-- The first six voter labels prefer label 0 at round two. Use the half that
prefers role A as group 0, and split the other half into groups of sizes 1, 1, 4. -/
private def voterGroup (switchTwo : Bool) (v : Fin 12) : Fin 4 :=
  let index := if switchTwo then v.val else (v.val + 6) % 12
  if index < 6 then 0 else if index = 6 then 1 else if index = 7 then 2 else 3

private def tablePosition (switchTwo : Bool) : Label 12 → Fin 8
  | .inl v => (voterGroup switchTwo v).natAdd 4
  | .inr a => (role switchTwo a).castAdd 4

private def separation (x y : Label 12) : ℕ := if x = y then 0 else 1

private theorem separation_triangle (x y z : Label 12) :
    separation x z ≤ separation x y + separation y z := by
  by_cases hxy : x = y
  · subst y
    simp [separation]
  · by_cases hxz : x = z <;> simp [separation, hxy, hxz]

private def leafDistance (s t u : Bool) (x y : Label 12) : ℕ :=
  1000 * graphTable t u (tablePosition s x) (tablePosition s y) + separation x y

@[instance_reducible]
private noncomputable def leafMetric (s t u : Bool) : MetricSpace (Label 12) where
  dist x y := leafDistance s t u x y
  dist_self x := by simp [leafDistance, graph_self, separation]
  dist_comm x y := by
    simp only [leafDistance, graph_comm t u (tablePosition s x) (tablePosition s y),
      separation, eq_comm (a := x) (b := y)]
  dist_triangle x y z := by
    have main := Nat.mul_le_mul_left 1000
      (graph_triangle t u (tablePosition s x) (tablePosition s y) (tablePosition s z))
    have discrete := separation_triangle x y z
    have bound : leafDistance s t u x z ≤ leafDistance s t u x y + leafDistance s t u y z := by
      unfold leafDistance
      rw [Nat.mul_add] at main
      omega
    exact_mod_cast bound
  eq_of_dist_eq_zero {x y} h := by
    have hzero : leafDistance s t u x y = 0 := by exact_mod_cast h
    by_contra hne
    simp [leafDistance, separation, hne] at hzero

/-- Inverse ballots, indexed by role A, B, C, D. The rows are in voter-group order. -/
private def rankTable (switchThree : Bool) : Fin 4 → Fin 4 → Fin 4 :=
  if switchThree then ![![0, 3, 2, 1], ![2, 1, 3, 0], ![2, 1, 3, 0], ![2, 1, 0, 3]]
  else ![![0, 3, 1, 2], ![2, 1, 3, 0], ![1, 0, 2, 3], ![3, 2, 0, 1]]

private def leafRank (s t : Bool) (v : Fin 12) (a : Alternative) : Fin 4 :=
  rankTable t (voterGroup s v) (role s a)

private theorem leaf_rank_injective :
    ∀ (s t : Bool) (v : Fin 12) (a b : Alternative),
      leafRank s t v a = leafRank s t v b → a = b := by decide

private def leafProfile (s t : Bool) : Profile 12 :=
  fun v => ⟨leafRank s t v, leaf_rank_injective s t v⟩

private def fixedArrival : Arrival := Equiv.refl _

private theorem leaf_compatible :
    ∀ (s t u : Bool) (v : Fin 12) (a b : Alternative),
      leafDistance s t u (.inr a) (.inl v) < leafDistance s t u (.inr b) (.inl v) →
      leafRank s t v a < leafRank s t v b := by
  decide

private noncomputable def leafElection (s t u : Bool) : Election 12 where
  Space := Label 12
  metric := leafMetric s t u
  location := id
  arrival := fixedArrival
  profile := leafProfile s t
  compatible v a b h := by
    change (leafDistance s t u (.inr a) (.inl v) : ℝ) <
      (leafDistance s t u (.inr b) (.inl v) : ℝ) at h
    exact leaf_compatible s t u v a b (by exact_mod_cast h)

private def leafObservation (s t : Bool) (round : ℕ) : Observation 12 :=
  observe fixedArrival (leafProfile s t) round

/-- The first two arrivals present the same labeled six-to-six split in every leaf. -/
private def opening (round : ℕ) : Observation 12 where
  arrived := (List.ofFn fixedArrival).take round
  prefers v a b := decide (2 ≤ round ∧
    ((a = 0 ∧ b = 1 ∧ v.val < 6) ∨ (a = 1 ∧ b = 0 ∧ 6 ≤ v.val)))

private theorem shared_early_comparisons :
    ∀ (s t : Bool) (r : Fin 2) (v : Fin 12) (a b : Alternative),
      (leafObservation s t (r.val + 1)).prefers v a b =
        (opening (r.val + 1)).prefers v a b := by
  decide

private theorem shared_early (s t : Bool) (r : Fin 2) :
    leafObservation s t (r.val + 1) = opening (r.val + 1) := by
  apply congrArg (Observation.mk ((List.ofFn fixedArrival).take (r.val + 1)))
  funext v a b
  exact shared_early_comparisons s t r v a b

private theorem shared_third_comparisons :
    ∀ (s t : Bool) (v : Fin 12) (a b : Alternative),
      (leafObservation s t 3).prefers v a b = (leafObservation s true 3).prefers v a b := by
  decide

private theorem shared_third (s t : Bool) :
    leafObservation s t 3 = leafObservation s true 3 := by
  apply congrArg (Observation.mk ((List.ofFn fixedArrival).take 3))
  funext v a b
  exact shared_third_comparisons s t v a b

private def natCost (s t u : Bool) (a : Alternative) : ℕ :=
  ∑ v : Fin 12, leafDistance s t u (.inr a) (.inl v)

private def expectedCost (switchThree switchFour : Bool) : Fin 4 → ℕ :=
  match switchThree, switchFour with
  | true, false => ![6012, 18012, 22012, 6012]
  | true, true => ![6012, 18012, 18012, 26012]
  | false, false => ![23012, 47012, 15012, 13012]
  | false, true => ![16012, 28012, 8012, 30012]

private theorem cost_table : ∀ (s t u : Bool) (a : Alternative),
    natCost s t u a = expectedCost t u (role s a) := by
  decide

private theorem real_cost (s t u : Bool) (a : Alternative) :
    socialCost (leafElection s t u) a = (natCost s t u a : ℝ) := by
  exact (Nat.cast_sum ..).symm

private def leafBest (s t u : Bool) : Alternative :=
  if t then role s 0 else if u then 2 else 3

private def leafWinner (s t u : Bool) : Alternative :=
  choose u (choose t (choose s 0 1) 2) 3

private theorem leaf_optimal : ∀ (s t u : Bool) (a : Alternative),
    expectedCost t u (role s (leafBest s t u)) ≤ expectedCost t u (role s a) := by decide

private theorem leaf_positive : ∀ (s t u : Bool),
    0 < expectedCost t u (role s (leafBest s t u)) := by decide

private theorem leaf_strict : ∀ (s t u : Bool),
    13 * expectedCost t u (role s (leafBest s t u)) ^ 2 <
      expectedCost t u (role s (leafWinner s t u)) ^ 2 := by decide

private theorem leaf_outcome (rule : Rule 12) :
    ∃ s t u : Bool,
      finalWinner rule (leafElection s t u).arrival (leafElection s t u).profile =
        leafWinner s t u := by
  let first := opening 1
  let second := opening 2
  let s := rule [first, second] []
  let third := leafObservation s true 3
  let t := rule [first, second, third] [s]
  let fourth := leafObservation s t 4
  let u := rule [first, second, third, fourth] [s, t]
  refine ⟨s, t, u, ?_⟩
  have h₁ : leafObservation s t 1 = first := shared_early s t 0
  have h₂ : leafObservation s t 2 = second := shared_early s t 1
  have h₃ : leafObservation s t 3 = third := shared_third s t
  change run rule fixedArrival (leafObservation s t) = leafWinner s t u
  simp only [run, h₁, h₂, h₃]
  rfl

/-- For each deterministic rule, one compatible fixed election has positive minimum
social cost and forces a final cost strictly above the threshold times that minimum. -/
private theorem counterexample (rule : Rule 12) :
    ∃ (election : Election 12) (best : Alternative),
      (∀ a, socialCost election best ≤ socialCost election a) ∧
      0 < socialCost election best ∧
      Real.sqrt 13 * socialCost election best <
        socialCost election (finalWinner rule election.arrival election.profile) := by
  obtain ⟨s, t, u, outcome⟩ := leaf_outcome rule
  refine ⟨leafElection s t u, leafBest s t u, ?_, ?_, ?_⟩
  · intro a
    simp only [real_cost, cost_table]
    exact_mod_cast leaf_optimal s t u a
  · simp only [real_cost, cost_table]
    exact_mod_cast leaf_positive s t u
  · simp only [outcome, real_cost, cost_table]
    have h : 13 * (expectedCost t u (role s (leafBest s t u)) : ℝ) ^ 2 <
        (expectedCost t u (role s (leafWinner s t u)) : ℝ) ^ 2 := by
      exact_mod_cast leaf_strict s t u
    rw [← Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13), ← mul_pow] at h
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.cast_nonneg _) h

/-- The four-alternative guarantee already fails with twelve labeled voters. -/
theorem result : ¬ claim := by
  rintro ⟨rule, guarantee⟩
  obtain ⟨election, best, _, _, violation⟩ := counterexample rule
  exact (not_lt_of_ge (guarantee election best)) violation

#print axioms result

end D5.S3.ConceptDynamics.Aggregation.OnlineVotingFourAlternatives
