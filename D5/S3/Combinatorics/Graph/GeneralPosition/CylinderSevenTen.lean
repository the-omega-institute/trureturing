/- GID: D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Rigidity of five robots settles the seven- and ten-cycle cylinder conjecture. -/

/-
proof_shape: result: content (covering construction and column invariant, with helpers inlined)
escape_witness: none
admission_basis: open-problem-resolution (#17705; Proved)
Direct frozen dependencies: F1--F3 below, after inlining this delivery's helpers.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17763
The seven public definitions retain the preregistered expressions.
The angular triple condition uses List.Triplewise; cycle distance uses its existing owner.
Utility none: the result is uniform in the path height; the finite tables are proof certificates.
Frozen declaration identities from the merged baseline report:
F1 = WellCoveredPowerCliqueProduct.cycleMetric @ sha256:2160035b11169ee3a321eb5e42afe29ca2c60867c1e9c2e1bd5ef671da66c9ff
F2 = WellCoveredPowerCliqueProduct.distance_certificate @ sha256:2ed868feac517a64060ab1dc1f05d5c4edfaf7f3ee530ce3f1d4d0d67b9d7684
F3 = _private.D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle.0.MatchingCliqueCycle.base_adj_values @ sha256:5618609b359d9e0051d2f314c7cc78c6a100dbeafc3818a053cb84f8fd5e5826
Columns: declaration | proof_shape | frozen dependencies | escape_witness | consumers.
The shared admission basis above applies to every row. Definitions and instances are auxiliary.
OnGeodesic | bind-only | none | none | IsGeneralPosition,geodesic_ordered,gp_turn,equal_row_geodesic,labelled_gp,geodesic_split,separated_gp
IsGeneralPosition | bind-only | none | none | LegalMove,IsMobile,gp_mono,gp_turn,gp_good5,five_strict_rows,gp_card_le_five,labelled_move,legal_card,legal_symm,reach_gp,reach_symm,mobile_of_reaches,no_horizontal,legal_columns,no_five_mobile,mobile_card_le_four
LegalMove | bind-only | none | none | IsMobile,legal_card,legal_symm,reach_gp,reach_symm,trace_extend,mobile_of_reaches,legal_columns,no_five_mobile,mobile_card_le_four,pair_rotate,pair_all_rotations,row_shift,all_row_pairs,four_mobile
IsMobile | bind-only | none | none | mobGP,mobile_of_reaches,no_five_mobile,mobile_card_le_four,mobGP_eq,four_mobile,result
mobGP | bind-only | none | none | claim,mobGP_eq,result
cylinder | bind-only | none | none | claim,cylinder_dist,geodesic_ordered,gp_turn,gp_good5,equal_row_geodesic,five_strict_rows,gp_card_le_five,geodesic_split,separated_gp,no_horizontal,legal_columns,no_five_mobile,mobile_card_le_four,pair_step,pair_rotate,pair_all_rotations,shift_step,row_shift,all_row_pairs,four_mobile,result
claim | bind-only | none | none | result
cycle_dist | bind-only | F1,F2,F3 | none | cylinder_dist,delta_triangle
path_dist | bind-only | F2 | none | cylinder_dist
cylinder_dist | bind-only | F1,F2,F3 | none | geodesic_ordered,equal_row_geodesic,geodesic_split
Turn | bind-only | F1 | none | goodFiveDecidable,rigidity7,rigidity10,rigidity,word_six7,word_six10,six_obstruction,gp_good5,gp_card_le_five
turnDecidable | bind-only | F1 | none | goodFiveDecidable,word_six7,word_six10
goodFiveDecidable | bind-only | F1 | none | rigidity7,rigidity10,word_six7,word_six10
Regular5 | bind-only | none | none | regularFiveDecidable,rigidity7,rigidity10,rigidity,regular_tie_obstruction,six_obstruction,regular_one_change,five_strict_rows,no_horizontal
regularFiveDecidable | bind-only | none | none | rigidity7,rigidity10
rigidity7 | bind-only | F1 | none | rigidity
rigidity10 | bind-only | F1 | none | rigidity
Supported | bind-only | none | none | rigidity,regular_tie_obstruction,six_obstruction,regular_one_change,five_strict_rows,gp_card_le_five,patterns,no_horizontal,legal_columns,no_five_mobile,mobile_card_le_four,pair_gp,pair_injective,pair_step,pair_rotate,pair_all_rotations,shift_gp,shift_injective,shift_step,row_shift,all_row_pairs,four_mobile
rigidity | bind-only | F1 | none | six_obstruction,five_strict_rows,no_horizontal
WeakRowTriple | bind-only | F1 | none | weakRowTripleDecidable,word_tie7,word_tie10,regular_tie_obstruction,five_strict_rows
weakRowTripleDecidable | bind-only | F1 | none | word_tie7,word_tie10
word7p | bind-only | none | none | word_tie7,word_six7,word_change7,regular_tie_obstruction,six_obstruction,regular_one_change
word7m | bind-only | none | none | word_tie7,word_six7,word_change7,regular_tie_obstruction,six_obstruction,regular_one_change
word_tie7 | bind-only | F1 | none | regular_tie_obstruction
word_six7 | bind-only | F1 | none | six_obstruction
word_change7 | bind-only | none | none | regular_one_change
word10p | bind-only | none | none | word_tie10,word_six10,word_change10,regular_tie_obstruction,six_obstruction,regular_one_change
word10m | bind-only | none | none | word_tie10,word_six10,word_change10,regular_tie_obstruction,six_obstruction,regular_one_change
word_tie10 | bind-only | F1 | none | regular_tie_obstruction
word_six10 | bind-only | F1 | none | six_obstruction
word_change10 | bind-only | none | none | regular_one_change
regular_tie_obstruction | bind-only | F1 | none | five_strict_rows
six_obstruction | bind-only | F1 | none | gp_card_le_five
regular_one_change | bind-only | none | none | no_horizontal
ordered_enumeration | bind-only | none | none | gp_card_le_five,no_horizontal
geodesic_ordered | bind-only | F1,F2,F3 | none | gp_turn
gp_mono | bind-only | none | none | gp_card_le_five
gp_turn | bind-only | F1,F2,F3 | none | gp_good5,gp_card_le_five
gp_good5 | bind-only | F1,F2,F3 | none | five_strict_rows,gp_card_le_five,no_horizontal
equal_row_geodesic | bind-only | F1,F2,F3 | none | five_strict_rows
five_strict_rows | bind-only | F1,F2,F3 | none | no_horizontal
gp_card_le_five | bind-only | F1,F2,F3 | none | mobile_card_le_four
mem_configuration | bind-only | none | none | labelled_gp,labelled_move,four_mobile
configuration_card | bind-only | none | none | four_mobile
labelled_gp | bind-only | none | none | separated_gp
labelled_move | bind-only | none | none | pair_step,shift_step
legal_card | bind-only | none | none | no_five_mobile
legal_symm | bind-only | none | none | reach_symm
reach_gp | bind-only | none | none | reach_symm
reach_symm | bind-only | none | none | mobile_of_reaches
trace_extend | bind-only | none | none | mobile_of_reaches
mobile_of_reaches | content | none | none | four_mobile
rowTag | bind-only | none | none | Safe,safeDecidable,separated_gp,tag_bound,row_certificates,pairRow,pair_gp,shiftRow,shift_gp,shift_step,four_mobile
Safe | bind-only | F1 | none | safeDecidable,separated_gp,pattern7,pattern10,patterns,pair_gp,pair_injective,pair_step,pair_rotate,shift_gp,shift_injective
safeDecidable | bind-only | F1 | none | pattern7,pattern10
delta_triangle | bind-only | F1,F2,F3 | none | geodesic_split
geodesic_split | bind-only | F1,F2,F3 | none | separated_gp
separated_gp | bind-only | F1,F2,F3 | none | pair_gp,shift_gp
pattern | bind-only | none | none | pattern7,pattern10,patterns,pairRobots,pair_gp,pair_injective,pair_step,pair_rotate,shiftRobots,shift_gp,shift_injective,four_mobile
movingIndex | bind-only | none | none | pattern7,pattern10,patterns,pair_gp,pair_injective,pair_step,pair_rotate,shift_gp,shift_injective
pattern7 | bind-only | F1 | none | patterns
pattern10 | bind-only | F1 | none | patterns
patterns | bind-only | F1 | none | pair_gp,pair_injective,pair_step,pair_rotate,shift_gp,shift_injective
shiftOffset | bind-only | none | none | row_certificates,shiftRow,shift_gp,shift_step
shiftIndex | bind-only | none | none | row_certificates,shiftRow,shift_gp,shift_step
tag_bound | bind-only | none | none | pairRow,four_mobile
row_certificates | bind-only | none | none | shiftRow,shift_gp,shift_step
no_horizontal | bind-only | F1,F2,F3 | none | legal_columns
legal_columns | bind-only | F1,F2,F3 | none | no_five_mobile
no_five_mobile | content | F1,F2,F3 | none | mobile_card_le_four
mobile_card_le_four | content | F1,F2,F3 | none | result
pairRow | bind-only | none | none | pairRobots,pair_gp,four_mobile
pairRobots | bind-only | none | none | pairConfig,pair_injective,pair_step,pair_rotate,four_mobile
pairConfig | bind-only | none | none | pair_rotate,pair_all_rotations,row_shift,all_row_pairs,four_mobile
pair_gp | bind-only | F1,F2,F3 | none | pair_step,four_mobile
pair_injective | bind-only | F1 | none | pair_step,four_mobile
pair_step | bind-only | F1,F2,F3 | none | pair_rotate
pair_rotate | bind-only | F1,F2,F3 | none | pair_all_rotations
pair_all_rotations | bind-only | F1,F2,F3 | none | four_mobile
shiftRow | bind-only | none | none | shiftRobots,shift_gp
shiftRobots | bind-only | none | none | shiftConfig,shift_injective,shift_step
shiftConfig | bind-only | none | none | row_shift
shift_gp | bind-only | F1,F2,F3 | none | shift_step
shift_injective | bind-only | F1 | none | shift_step
shift_step | bind-only | F1,F2,F3 | none | row_shift
row_shift | bind-only | F1,F2,F3 | none | all_row_pairs
all_row_pairs | content | F1,F2,F3 | none | four_mobile
mobGP_eq | bind-only | none | none | result
four_mobile | content | F1,F2,F3 | none | result
result | content | F1,F2,F3 | none | settling result
-/

import Mathlib.Data.Finset.Sort
import D5.S3.Combinatorics.Graph.Walks.MatchingCliqueCycle
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Triplewise

namespace D5.S3.Combinatorics.Graph.GeneralPosition.CylinderSevenTen

open MatchingCliqueCycle (cycle_distance)

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- `v` lies on a shortest `u`–`w` path of `G`. -/
def OnGeodesic (G : SimpleGraph V) (u v w : V) : Prop :=
  G.dist u v + G.dist v w = G.dist u w

/-- `S` is in general position: no vertex of `S` lies on a shortest path between two other
vertices of `S` (no three vertices of `S` lie on a common geodesic). -/
def IsGeneralPosition (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ∀ w ∈ S, u ≠ v → v ≠ w → u ≠ w → ¬ OnGeodesic G u v w

/-- A legal move (arXiv:2505.00535, Section 1.1): one robot moves from `u ∈ S` along an edge to an
unoccupied vertex `v`, and the new configuration is again in general position. -/
def LegalMove (G : SimpleGraph V) (S T : Finset V) : Prop :=
  ∃ u ∈ S, ∃ v, v ∉ S ∧ G.Adj u v ∧ T = insert v (S.erase u) ∧ IsGeneralPosition G T

/-- `S` is a mobile general position set: in general position, and some finite sequence of
legal moves starting from `S` visits every vertex at least once by some robot. -/
def IsMobile (G : SimpleGraph V) (S : Finset V) : Prop :=
  IsGeneralPosition G S ∧ ∃ (n : ℕ) (c : Fin (n + 1) → Finset V), c 0 = S ∧
    (∀ i : Fin n, LegalMove G (c i.castSucc) (c i.succ)) ∧ ∀ x : V, ∃ i, x ∈ c i

/-- The mobile general position number `Mob_gp(G)`: the largest number of robots in a mobile
general position set. -/
noncomputable def mobGP (G : SimpleGraph V) : ℕ :=
  sSup {k | ∃ S : Finset V, S.card = k ∧ IsMobile G S}

/-- The cylinder `C_r □ P_s`. -/
abbrev cylinder (r s : ℕ) : SimpleGraph (Fin r × Fin s) := cycleGraph r □ pathGraph s

/-- Klavžar–Krishnakumar–Kuziak–Shallcross–Tuite–Yero (arXiv:2505.00535v2, after Proposition 3.7):
`Mob_gp(C₇ □ P_s) = Mob_gp(C₁₀ □ P_s) = 4` for every `s ≥ 5`. -/
def claim : Prop := ∀ s : ℕ, 5 ≤ s → mobGP (cylinder 7 s) = 4 ∧ mobGP (cylinder 10 s) = 4

private theorem cycle_dist {r : ℕ} (hr : 3 ≤ r) (x z : Fin r) :
    (SimpleGraph.cycleGraph r).dist x z = WellCoveredPowerCliqueProduct.cycleMetric r x z := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 3 := ⟨r - 3, by omega⟩
  exact cycle_distance k x z

private theorem path_dist {s : ℕ} (y t : Fin s) :
    (SimpleGraph.pathGraph s).dist y t = Nat.dist y.val t.val := by
  have : NeZero s := Fin.neZero y
  apply (WellCoveredPowerCliqueProduct.distance_certificate
    (SimpleGraph.pathGraph s) (fun u v => Nat.dist u.val v.val) ?_ ?_ ?_).2
  · intro u v
    constructor
    · intro h; apply Fin.ext; exact Nat.eq_of_dist_eq_zero h
    · intro h; subst v; exact by simp [Nat.dist]
  · intro u v w h
    rw [SimpleGraph.pathGraph_adj] at h
    simp only [Nat.dist]
    omega
  · intro u v h
    have hu := u.isLt
    have hv := v.isLt
    by_cases huv : u.val < v.val
    · refine ⟨⟨u.val + 1, by omega⟩, ?_, ?_⟩
      · simp [SimpleGraph.pathGraph_adj]
      · simp only [Nat.dist]
        omega
    · refine ⟨⟨u.val - 1, by simp only [Nat.dist] at h; omega⟩, ?_, ?_⟩
      · simp only [SimpleGraph.pathGraph_adj]
        simp only [Nat.dist] at h
        omega
      · simp only [Nat.dist] at *
        omega

private theorem cylinder_dist {r s : ℕ} (hr : 3 ≤ r) (x z : Fin r) (y t : Fin s) :
    (cylinder r s).dist (x,y) (z,t) = WellCoveredPowerCliqueProduct.cycleMetric r x z + Nat.dist y.val t.val := by
  rw [SimpleGraph.dist, SimpleGraph.edist_boxProd,
    ENat.toNat_add
      (SimpleGraph.edist_ne_top_iff_reachable.mpr (SimpleGraph.cycleGraph_preconnected x z))
      (SimpleGraph.edist_ne_top_iff_reachable.mpr (SimpleGraph.pathGraph_preconnected s y t))]
  change (SimpleGraph.cycleGraph r).dist x z + (SimpleGraph.pathGraph s).dist y t = _
  rw [cycle_dist hr, path_dist]

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def Turn {r : ℕ} (x y z : Fin r) : Prop := WellCoveredPowerCliqueProduct.cycleMetric r x y + WellCoveredPowerCliqueProduct.cycleMetric r y z ≠ WellCoveredPowerCliqueProduct.cycleMetric r x z
private instance turnDecidable {r : ℕ} (x y z : Fin r) : Decidable (Turn x y z) := inferInstanceAs (Decidable (_ ≠ _))

private instance goodFiveDecidable {r : ℕ} (a b c d e : Fin r) :
    Decidable ([a,b,c,d,e].Triplewise Turn) :=
  decidable_of_iff
    (Turn a b c ∧ Turn a b d ∧ Turn a b e ∧
     Turn a c d ∧ Turn a c e ∧ Turn a d e ∧
     Turn b c d ∧ Turn b c e ∧ Turn b d e ∧
     Turn c d e)
    (by simp [List.triplewise_cons, List.pairwise_cons, and_assoc])

private def Regular5 {r : ℕ} [NeZero r] (a : Fin r) (x : Fin 5 → Fin r) : Prop :=
  x = ![x 0, x 0 + a, x 0 + 2*a, x 0 + 3*a, x 0 + 4*a] ∨
  x = ![x 0, x 0 - a, x 0 - 2*a, x 0 - 3*a, x 0 - 4*a]
private instance regularFiveDecidable {r : ℕ} [NeZero r] (a : Fin r) (x : Fin 5 → Fin r) : Decidable (Regular5 a x) := by
  unfold Regular5; infer_instance

private theorem rigidity7 (a b c d e : Fin 7) : ([a,b,c,d,e].Triplewise Turn) → Regular5 2 ![a,b,c,d,e] := by
  revert b c d e
  fin_cases a <;> decide +kernel

private theorem rigidity10 (a b c d e : Fin 10) : ([a,b,c,d,e].Triplewise Turn) → Regular5 3 ![a,b,c,d,e] := by
  revert b c d e
  fin_cases a <;> decide +kernel

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def Supported (r : ℕ) : Prop := r = 7 ∨ r = 10

private theorem rigidity {r : ℕ} [NeZero r] (hr : Supported r) (x : Fin 5 → Fin r)
    (h : ([x 0,x 1,x 2,x 3,x 4].Triplewise Turn)) : Regular5 (Fin.ofNat r (r / 3)) x := by
  have hx : x = ![x 0,x 1,x 2,x 3,x 4] := by exact List.ofFn_inj.mp rfl
  rw [hx] at h ⊢
  rcases hr with rfl | rfl
  · exact rigidity7 _ _ _ _ _ h
  · exact rigidity10 _ _ _ _ _ h

private def WeakRowTriple {r n : ℕ} (x : Fin n → Fin r) (i j : Fin n) : Prop :=
  ∃ k : Fin n, k ≠ i ∧ k ≠ j ∧
    (WellCoveredPowerCliqueProduct.cycleMetric r (x i) (x j) + WellCoveredPowerCliqueProduct.cycleMetric r (x j) (x k) = WellCoveredPowerCliqueProduct.cycleMetric r (x i) (x k) ∨
     WellCoveredPowerCliqueProduct.cycleMetric r (x j) (x i) + WellCoveredPowerCliqueProduct.cycleMetric r (x i) (x k) = WellCoveredPowerCliqueProduct.cycleMetric r (x j) (x k))

private instance weakRowTripleDecidable {r n : ℕ} (x : Fin n → Fin r) (i j : Fin n) : Decidable (WeakRowTriple x i j) := by
  unfold WeakRowTriple; infer_instance

private def word7p (b : Fin 7) : Fin 5 → Fin 7 := ![b,b + 2,b + 4,b + 6,b + 1]

private def word7m (b : Fin 7) : Fin 5 → Fin 7 := ![b,b - 2,b - 4,b - 6,b - 1]

private theorem word_tie7 : ∀ b : Fin 7, (∀ i : Fin 4, WeakRowTriple (word7p b) i.castSucc i.succ) ∧
    (∀ i : Fin 4, WeakRowTriple (word7m b) i.castSucc i.succ) := by
  decide +kernel

private theorem word_six7 : ∀ b f : Fin 7,
    ¬ (([(word7p b) 1,(word7p b) 2,(word7p b) 3,(word7p b) 4,f].Triplewise Turn) ∧ Turn b ((word7p b) 1) f) ∧
    ¬ (([(word7m b) 1,(word7m b) 2,(word7m b) 3,(word7m b) 4,f].Triplewise Turn) ∧ Turn b ((word7m b) 1) f) := by
  decide +kernel

private theorem word_change7 : ∀ a b : Fin 7, ∀ i : Fin 5,

    ((∀ j, j ≠ i → word7p a j = word7p b j) → word7p a = word7p b) ∧
    ((∀ j, j ≠ i → word7p a j = word7m b j) → word7p a = word7m b) ∧
    ((∀ j, j ≠ i → word7m a j = word7p b j) → word7m a = word7p b) ∧
    ((∀ j, j ≠ i → word7m a j = word7m b j) → word7m a = word7m b) := by
  decide +kernel

private def word10p (b : Fin 10) : Fin 5 → Fin 10 := ![b,b + 3,b + 6,b + 9,b + 2]

private def word10m (b : Fin 10) : Fin 5 → Fin 10 := ![b,b - 3,b - 6,b - 9,b - 2]

private theorem word_tie10 : ∀ b : Fin 10, (∀ i : Fin 4, WeakRowTriple (word10p b) i.castSucc i.succ) ∧
    (∀ i : Fin 4, WeakRowTriple (word10m b) i.castSucc i.succ) := by
  decide +kernel

private theorem word_six10 : ∀ b f : Fin 10,
    ¬ (([(word10p b) 1,(word10p b) 2,(word10p b) 3,(word10p b) 4,f].Triplewise Turn) ∧ Turn b ((word10p b) 1) f) ∧
    ¬ (([(word10m b) 1,(word10m b) 2,(word10m b) 3,(word10m b) 4,f].Triplewise Turn) ∧ Turn b ((word10m b) 1) f) := by
  decide +kernel

private theorem word_change10 : ∀ a b : Fin 10, ∀ i : Fin 5,

    ((∀ j, j ≠ i → word10p a j = word10p b j) → word10p a = word10p b) ∧
    ((∀ j, j ≠ i → word10p a j = word10m b j) → word10p a = word10m b) ∧
    ((∀ j, j ≠ i → word10m a j = word10p b j) → word10m a = word10p b) ∧
    ((∀ j, j ≠ i → word10m a j = word10m b j) → word10m a = word10m b) := by
  decide +kernel

private theorem regular_tie_obstruction {r : ℕ} [NeZero r] (hr : Supported r)
    (x : Fin 5 → Fin r) (h : Regular5 (Fin.ofNat r (r / 3)) x) :
    ∀ i : Fin 4, WeakRowTriple x i.castSucc i.succ := by
  rcases hr with rfl | rfl <;> rcases h with h | h <;> rw [h]
  · exact (word_tie7 (x 0)).1
  · exact (word_tie7 (x 0)).2
  · exact (word_tie10 (x 0)).1
  · exact (word_tie10 (x 0)).2

private theorem six_obstruction {r : ℕ} [NeZero r] (hr : Supported r)
    (a b c d e f : Fin r) (h : ([a,b,c,d,e].Triplewise Turn)) :
    ¬ (([b,c,d,e,f].Triplewise Turn) ∧ Turn a b f) := by
  have hn := rigidity hr ![a,b,c,d,e] h
  rcases hr with rfl | rfl <;> rcases hn with hn | hn
  all_goals
    have hb := congrFun hn 1
    have hc := congrFun hn 2
    have hd := congrFun hn 3
    have he := congrFun hn 4
    simp at hb hc hd he
    subst b; subst c; subst d; subst e
  · exact (word_six7 a f).1
  · exact (word_six7 a f).2
  · exact (word_six10 a f).1
  · exact (word_six10 a f).2

private theorem regular_one_change {r : ℕ} [NeZero r] (hr : Supported r)
    (x y : Fin 5 → Fin r) (hx : Regular5 (Fin.ofNat r (r / 3)) x)
    (hy : Regular5 (Fin.ofNat r (r / 3)) y) (i : Fin 5)
    (heq : ∀ j, j ≠ i → x j = y j) : x = y := by
  rcases hr with rfl | rfl <;> rcases hx with hx | hx <;> rcases hy with hy | hy
  all_goals rw [hx,hy] at heq ⊢
  · exact (word_change7 (x 0) (y 0) i).1 heq
  · exact (word_change7 (x 0) (y 0) i).2.1 heq
  · exact (word_change7 (x 0) (y 0) i).2.2.1 heq
  · exact (word_change7 (x 0) (y 0) i).2.2.2 heq
  · exact (word_change10 (x 0) (y 0) i).1 heq
  · exact (word_change10 (x 0) (y 0) i).2.1 heq
  · exact (word_change10 (x 0) (y 0) i).2.2.1 heq
  · exact (word_change10 (x 0) (y 0) i).2.2.2 heq

open SimpleGraph

private theorem ordered_enumeration {r s n : ℕ} (S : Finset (Fin r × Fin s)) (hc : S.card = n) :
    ∃ f : Fin n → Fin r × Fin s, Function.Injective f ∧
      (∀ i, f i ∈ S) ∧ (∀ v ∈ S, ∃ i, f i = v) ∧ Monotone (fun i => (f i).2) := by
  classical
  let e : (Fin r × Fin s) ≃ (Fin s ×ₗ Fin r) :=
    (Equiv.prodComm _ _).trans toLex
  let T := S.map e.toEmbedding
  have ht : T.card = n := by simpa [T] using hc
  let o := T.orderIsoOfFin ht
  let f : Fin n → Fin r × Fin s := fun i => e.symm (o i)
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro i j h
    apply o.injective
    apply Subtype.ext
    exact e.symm.injective h
  · intro i
    have h := (o i).2
    simpa [T] using h
  · intro v hv
    have hv' : e v ∈ T := Finset.mem_map_equiv.mpr hv
    refine ⟨o.symm ⟨e v,hv'⟩, ?_⟩
    simp [f]
  · intro i j hij
    have hh := o.monotone hij
    exact Prod.Lex.monotone_fst (o i).val (o j).val hh

private theorem geodesic_ordered {r s : ℕ} (hr : 3 ≤ r) (u v w : Fin r × Fin s)
    (huv : u.2 ≤ v.2) (hvw : v.2 ≤ w.2) :
    OnGeodesic (cylinder r s) u v w ↔ WellCoveredPowerCliqueProduct.cycleMetric r u.1 v.1 + WellCoveredPowerCliqueProduct.cycleMetric r v.1 w.1 = WellCoveredPowerCliqueProduct.cycleMetric r u.1 w.1 := by
  rcases u with ⟨x,y⟩; rcases v with ⟨z,t⟩; rcases w with ⟨a,b⟩
  dsimp at *
  simp only [OnGeodesic, cylinder_dist hr, Nat.dist]
  have h1 : y.val ≤ t.val := huv
  have h2 : t.val ≤ b.val := hvw
  omega

open SimpleGraph
set_option maxHeartbeats 1000000

private theorem gp_mono {V : Type*} [DecidableEq V] {G : SimpleGraph V} {S T : Finset V}
    (h : S ⊆ T) (hg : IsGeneralPosition G T) : IsGeneralPosition G S := by
  intro u hu v hv w hw
  exact hg u (h hu) v (h hv) w (h hw)

private theorem gp_turn {r s n : ℕ} (hr : 3 ≤ r) {S : Finset (Fin r × Fin s)}
    (hg : IsGeneralPosition (cylinder r s) S) (f : Fin n → Fin r × Fin s)
    (hf : ∀ i, f i ∈ S) (hi : Function.Injective f) (ho : Monotone (fun i => (f i).2))
    {i j k : Fin n} (hij : i < j) (hjk : j < k) : Turn (f i).1 (f j).1 (f k).1 := by
  intro he
  exact hg _ (hf i) _ (hf j) _ (hf k) (hi.ne hij.ne) (hi.ne hjk.ne)
    (hi.ne (hij.trans hjk).ne) ((geodesic_ordered hr _ _ _ (ho hij.le) (ho hjk.le)).mpr he)

private theorem gp_good5 {r s : ℕ} (hr : 3 ≤ r) {S : Finset (Fin r × Fin s)}
    (hg : IsGeneralPosition (cylinder r s) S) (f : Fin 5 → Fin r × Fin s)
    (hf : ∀ i, f i ∈ S) (hi : Function.Injective f) (ho : Monotone (fun i => (f i).2)) :
    ([(f 0).1,(f 1).1,(f 2).1,(f 3).1,(f 4).1].Triplewise Turn) := by
  change (List.ofFn (fun i : Fin 5 => (f i).1)).Triplewise Turn
  apply List.triplewise_iff_getElem.mpr
  intro i j k hij hjk hk
  simp only [List.length_ofFn] at hk
  have hjlt : j < 5 := Nat.lt_trans hjk hk
  have hilt : i < 5 := Nat.lt_trans hij hjlt
  simpa only [List.getElem_ofFn] using
    (gp_turn hr hg f hf hi ho (i := ⟨i,hilt⟩) (j := ⟨j,hjlt⟩) (k := ⟨k,hk⟩) hij hjk)

private theorem equal_row_geodesic {r s : ℕ} (hr : 3 ≤ r) (u v w : Fin r × Fin s)
    (hy : u.2 = v.2)
    (hx : WellCoveredPowerCliqueProduct.cycleMetric r u.1 v.1 + WellCoveredPowerCliqueProduct.cycleMetric r v.1 w.1 = WellCoveredPowerCliqueProduct.cycleMetric r u.1 w.1) :
    OnGeodesic (cylinder r s) u v w := by
  rcases u with ⟨x,y⟩; rcases v with ⟨z,t⟩; rcases w with ⟨a,b⟩
  dsimp at *
  subst t
  simp only [OnGeodesic, cylinder_dist hr, Nat.dist_self]
  omega

private theorem five_strict_rows {r s : ℕ} [NeZero r] (hr : Supported r)
    {S : Finset (Fin r × Fin s)} (hg : IsGeneralPosition (cylinder r s) S)
    (f : Fin 5 → Fin r × Fin s) (hf : ∀ i, f i ∈ S) (hi : Function.Injective f)
    (ho : Monotone (fun i => (f i).2)) : StrictMono (fun i => (f i).2) := by
  have hr3 : 3 ≤ r := by rcases hr with rfl | rfl <;> decide
  have reg := rigidity hr (fun i => (f i).1) (gp_good5 hr3 hg f hf hi ho)
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hle := ho (Fin.castSucc_le_succ i)
  apply lt_of_le_of_ne hle
  intro heq
  obtain ⟨k,hki,hkj,hx | hx⟩ := regular_tie_obstruction hr _ reg i
  · exact hg _ (hf _) _ (hf _) _ (hf k) (hi.ne (Fin.castSucc_lt_succ (i:=i)).ne)
      (hi.ne hkj.symm) (hi.ne hki.symm) (equal_row_geodesic hr3 _ _ _ heq hx)
  · exact hg _ (hf _) _ (hf _) _ (hf k) (hi.ne (Fin.castSucc_lt_succ (i:=i)).ne.symm)
      (hi.ne hki.symm) (hi.ne hkj.symm) (equal_row_geodesic hr3 _ _ _ heq.symm hx)

private theorem gp_card_le_five {r s : ℕ} [NeZero r] (hr : Supported r)
    {S : Finset (Fin r × Fin s)} (hg : IsGeneralPosition (cylinder r s) S) : S.card ≤ 5 := by
  by_contra hn
  obtain ⟨T,hTS,hTc⟩ := Finset.exists_subset_card_eq (show 6 ≤ S.card by omega)
  have hgT := gp_mono hTS hg
  obtain ⟨f,hi,hf,hs,ho⟩ := ordered_enumeration T hTc
  have hr3 : 3 ≤ r := by rcases hr with rfl | rfl <;> decide
  have h0 : ([(f 0).1,(f 1).1,(f 2).1,(f 3).1,(f 4).1].Triplewise Turn) := by
    have h := gp_good5 hr3 hgT (fun i : Fin 5 => f i.castSucc)
      (fun i => hf i.castSucc) (hi.comp (Fin.castSucc_injective 5))
      (ho.comp Fin.strictMono_castSucc.monotone)
    exact h
  have h1 : ([(f 1).1,(f 2).1,(f 3).1,(f 4).1,(f 5).1].Triplewise Turn) := by
    have h := gp_good5 hr3 hgT (fun i : Fin 5 => f i.succ)
      (fun i => hf i.succ) (hi.comp (Fin.succ_injective 5))
      (ho.comp Fin.strictMono_succ.monotone)
    exact h
  exact six_obstruction hr _ _ _ _ _ _ h0 ⟨h1,gp_turn hr3 hgT f hf hi ho (i:=0) (j:=1) (k:=5) (by decide) (by decide)⟩

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

@[simp] private theorem mem_configuration {n : ℕ} (f : Fin n → V) (v : V) :
    v ∈ (fun f => Finset.univ.image f) f ↔ ∃ i, f i = v := by
  simp

private theorem configuration_card {n : ℕ} (f : Fin n → V) (h : Function.Injective f) :
    ((fun f => Finset.univ.image f) f).card = n := by
  rw [Finset.card_image_of_injective _ h,Finset.card_univ,Fintype.card_fin]

private theorem labelled_gp {n : ℕ} (f : Fin n → V)
    (h : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ¬ OnGeodesic G (f i) (f j) (f k)) :
    IsGeneralPosition G ((fun f => Finset.univ.image f) f) := by
  intro u hu v hv w hw huv hvw huw
  obtain ⟨i,rfl⟩ := (mem_configuration _ _).mp hu
  obtain ⟨j,rfl⟩ := (mem_configuration _ _).mp hv
  obtain ⟨k,rfl⟩ := (mem_configuration _ _).mp hw
  exact h i j k (fun he => huv (congrArg f he)) (fun he => hvw (congrArg f he))
    (fun he => huw (congrArg f he))

private theorem labelled_move {n : ℕ} (f g : Fin n → V) (i : Fin n)
    (hf : Function.Injective f) (hg : Function.Injective g) (he : ∀ j, j ≠ i → f j = g j)
    (ha : G.Adj (f i) (g i)) (hgp : IsGeneralPosition G ((fun f => Finset.univ.image f) g)) :
    LegalMove G ((fun f => Finset.univ.image f) f) ((fun f => Finset.univ.image f) g) := by
  have hne : f i ≠ g i := G.ne_of_adj ha
  have hnew : g i ∉ (fun f => Finset.univ.image f) f := by
    rintro h
    obtain ⟨j,hj⟩ := (mem_configuration _ _).mp h
    by_cases hji : j = i
    · subst j; exact hne hj
    · have heq : g j = g i := (he j hji).symm.trans hj
      exact hji (hg heq)
  refine ⟨f i, by simp, g i,hnew,ha,?_,hgp⟩
  ext v
  simp only [mem_configuration, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨j,rfl⟩
    by_cases hji : j = i
    · exact Or.inl (congrArg g hji)
    · refine Or.inr ⟨?_,⟨j,he j hji⟩⟩
      intro h
      exact hji (hf ((he j hji).trans h))
  · rintro (rfl | ⟨hv, j,hj⟩)
    · exact ⟨i,rfl⟩
    · have hji : j ≠ i := fun h => hv (h ▸ hj).symm
      exact ⟨j,(he j hji).symm.trans hj⟩

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

private theorem legal_card {S T : Finset V} (h : LegalMove G S T) : T.card = S.card := by
  rcases h with ⟨u,hu,v,hv,ha,rfl,hg⟩
  have hv' : v ∉ S.erase u := fun h => hv (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hv', Finset.card_erase_of_mem hu]
  have := Finset.card_pos.mpr ⟨u,hu⟩
  omega

private theorem legal_symm {S T : Finset V} (hs : IsGeneralPosition G S)
    (h : LegalMove G S T) : LegalMove G T S := by
  rcases h with ⟨u,hu,v,hv,ha,rfl,hg⟩
  have hv' : v ∉ S.erase u := fun h => hv (Finset.mem_of_mem_erase h)
  have huv : u ≠ v := fun h => hv (h ▸ hu)
  refine ⟨v, by simp, u, ?_, ha.symm, ?_, hs⟩
  · simp [huv]
  · simp [hv', Finset.insert_erase hu]

private theorem reach_gp {S T : Finset V} (hs : IsGeneralPosition G S) (h : Relation.ReflTransGen (LegalMove G) S T) :
    IsGeneralPosition G T := by
  induction h with
  | refl => exact hs
  | tail h hm ih => rcases hm with ⟨u,hu,v,hv,ha,he,hg⟩; exact hg

private theorem reach_symm {S T : Finset V} (hs : IsGeneralPosition G S) (h : Relation.ReflTransGen (LegalMove G) S T) : Relation.ReflTransGen (LegalMove G) T S := by
  induction h with
  | refl => exact .refl
  | tail h hm ih => exact (Relation.ReflTransGen.single (legal_symm (reach_gp hs h) hm)).trans ih

private theorem trace_extend {S T U : Finset V} (h : Relation.ReflTransGen (LegalMove G) T U) (l : List (Finset V))
    (hc : (S :: l).IsChain (LegalMove G)) (ht : (S :: l).getLast (by simp) = T) :
    ∃ l', (S :: l').IsChain (LegalMove G) ∧ (S :: l').getLast (by simp) = U ∧
      ∀ X ∈ S :: l, X ∈ S :: l' := by
  obtain ⟨q,hq,hu⟩ := List.exists_isChain_cons_of_relationReflTransGen h
  have he : (S :: l).dropLast ++ [T] = S :: l := by
    rw [← ht]
    exact List.dropLast_concat_getLast (by simp)
  refine ⟨l ++ q, ?_, ?_, ?_⟩
  · have hc' : ((S :: l).dropLast ++ [T]).IsChain (LegalMove G) := by rw [he]; exact hc
    simpa only [he, List.cons_append] using hc'.append_overlap hq (by simp)
  · cases q with
    | nil => simpa using ht.trans hu
    | cons a q =>
      change ((S :: l) ++ a :: q).getLast _ = U
      rw [List.getLast_append_right (by simp)]
      exact hu
  · intro X hX
    exact List.mem_append_left q hX

private theorem mobile_of_reaches [Fintype V] {S : Finset V} (hs : IsGeneralPosition G S)
    (hvisit : ∀ v : V, ∃ T, Relation.ReflTransGen (LegalMove G) S T ∧ v ∈ T) : IsMobile G S := by
  classical
  have cover : ∀ A : Finset V, ∃ T, ∃ l : List (Finset V),
      (S :: l).IsChain (LegalMove G) ∧ (S :: l).getLast (by simp) = T ∧
      ∀ v ∈ A, ∃ X ∈ S :: l, v ∈ X := by
    intro A
    induction A using Finset.induction_on with
    | empty => exact ⟨S,[],.singleton _,rfl,by simp⟩
    | @insert v A hv ih =>
      obtain ⟨T,l,hc,ht,hA⟩ := ih
      have hST : Relation.ReflTransGen (LegalMove G) S T := by
        exact List.relationReflTransGen_of_exists_isChain_cons l hc ht
      obtain ⟨U,hSU,hvU⟩ := hvisit v
      obtain ⟨q,hq,hqU,hsub⟩ := trace_extend ((reach_symm hs hST).trans hSU) l hc ht
      refine ⟨U,q,hq,hqU,?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨U, hqU ▸ List.getLast_mem (by simp), hvU⟩
      · obtain ⟨X,hX,hwX⟩ := hA w hw
        exact ⟨X,hsub X hX,hwX⟩
  obtain ⟨T,l,hc,ht,hcover⟩ := cover Finset.univ
  refine ⟨hs,l.length,(fun i => (S :: l)[i.val]),rfl,?_,?_⟩
  · intro i
    exact List.isChain_iff_getElem.mp hc i.val (by simpa using i.isLt)
  · intro v
    obtain ⟨X,hX,hv⟩ := hcover v (Finset.mem_univ _)
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem hX
    exact ⟨⟨i,by simpa using hi⟩,he ▸ hv⟩

set_option maxHeartbeats 1000000

private def rowTag : Fin 4 → ℕ := ![0,0,1,1]
private def Safe {r : ℕ} (x : Fin 4 → Fin r) : Prop :=
  ∀ i j k : Fin 4, i ≠ j → j ≠ k → i ≠ k →
    WellCoveredPowerCliqueProduct.cycleMetric r (x i) (x j) + WellCoveredPowerCliqueProduct.cycleMetric r (x j) (x k) = WellCoveredPowerCliqueProduct.cycleMetric r (x i) (x k) →
    Nat.dist (rowTag i) (rowTag j) + Nat.dist (rowTag j) (rowTag k) ≠ Nat.dist (rowTag i) (rowTag k)
private instance safeDecidable {r : ℕ} (x : Fin 4 → Fin r) : Decidable (Safe x) := by unfold Safe; infer_instance

private theorem delta_triangle {r : ℕ} (hr : 3 ≤ r) (x y z : Fin r) :
    WellCoveredPowerCliqueProduct.cycleMetric r x z ≤ WellCoveredPowerCliqueProduct.cycleMetric r x y + WellCoveredPowerCliqueProduct.cycleMetric r y z := by
  have h := (SimpleGraph.cycleGraph_preconnected x y).dist_triangle_left z
  simpa only [cycle_dist hr] using h

private theorem geodesic_split {r s : ℕ} (hr : 3 ≤ r) (u v w : Fin r × Fin s)
    (h : OnGeodesic (cylinder r s) u v w) :
    WellCoveredPowerCliqueProduct.cycleMetric r u.1 v.1 + WellCoveredPowerCliqueProduct.cycleMetric r v.1 w.1 = WellCoveredPowerCliqueProduct.cycleMetric r u.1 w.1 ∧
    Nat.dist u.2.val v.2.val + Nat.dist v.2.val w.2.val = Nat.dist u.2.val w.2.val := by
  have hx := delta_triangle hr u.1 v.1 w.1
  have hy := Nat.dist.triangle_inequality u.2.val v.2.val w.2.val
  rcases u with ⟨x,y⟩; rcases v with ⟨z,t⟩; rcases w with ⟨a,b⟩
  simp only [OnGeodesic,cylinder_dist hr] at h
  dsimp at *
  omega

private theorem separated_gp {r s : ℕ} (hr : 3 ≤ r) (x : Fin 4 → Fin r) (y : Fin 4 → Fin s)
    (hx : Safe x) (hy : ∀ i j, rowTag i < rowTag j → y i < y j) :
    IsGeneralPosition (cylinder r s) ((fun f => Finset.univ.image f) (fun i => (x i,y i))) := by
  apply labelled_gp
  intro i j k hij hjk hik hg
  obtain ⟨ha,hb⟩ := geodesic_split hr _ _ _ hg
  have reflect : ∀ a b, (y a).val ≤ (y b).val → rowTag a ≤ rowTag b := by
    exact fun a b hab => le_imp_le_of_lt_imp_lt (hy b a) hab
  have hbt : ((y i).val ≤ (y j).val ∧ (y j).val ≤ (y k).val) ∨
      ((y k).val ≤ (y j).val ∧ (y j).val ≤ (y i).val) := by
    dsimp at hb
    simp only [Nat.dist] at hb
    omega
  apply hx i j k hij hjk hik ha
  rcases hbt with ⟨hij,hjk⟩ | ⟨hkj,hji⟩
  · have := reflect i j hij
    have := reflect j k hjk
    simp only [Nat.dist]; omega
  · have := reflect k j hkj
    have := reflect j i hji
    simp only [Nat.dist]; omega

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def pattern {r : ℕ} [NeZero r] (b : Fin r) (q : Fin 5) : Fin 4 → Fin r :=
  fun i => b + (if r = 7 then
    ![![0,4,1,5],![0,4,2,5],![1,4,2,5],![1,4,2,6],![1,5,2,6]]
    else ![![0,5,1,6],![0,5,2,6],![0,5,2,7],![1,5,2,7],![1,6,2,7]]) q i

private def movingIndex (r : ℕ) : Fin 4 → Fin 4 :=
  if r = 7 then ![2,0,3,1] else ![2,3,0,1]

private theorem pattern7 : ∀ b : Fin 7,
    (∀ q, Safe (pattern b q) ∧ Function.Injective (pattern b q)) ∧
    (∀ q : Fin 4,
      (∀ i, i ≠ movingIndex 7 q → pattern b q.castSucc i = pattern b q.succ i) ∧
      (SimpleGraph.cycleGraph 7).Adj (pattern b q.castSucc (movingIndex 7 q)) (pattern b q.succ (movingIndex 7 q))) ∧
    pattern b 4 = pattern (b+1) 0 := by
  decide +kernel

private theorem pattern10 : ∀ b : Fin 10,
    (∀ q, Safe (pattern b q) ∧ Function.Injective (pattern b q)) ∧
    (∀ q : Fin 4,
      (∀ i, i ≠ movingIndex 10 q → pattern b q.castSucc i = pattern b q.succ i) ∧
      (SimpleGraph.cycleGraph 10).Adj (pattern b q.castSucc (movingIndex 10 q)) (pattern b q.succ (movingIndex 10 q))) ∧
    pattern b 4 = pattern (b+1) 0 := by
  decide +kernel

private theorem patterns {r : ℕ} [NeZero r] (hr : Supported r) (b : Fin r) :
    (∀ q, Safe (pattern b q) ∧ Function.Injective (pattern b q)) ∧
    (∀ q : Fin 4,
      (∀ i, i ≠ movingIndex r q → pattern b q.castSucc i = pattern b q.succ i) ∧
      (SimpleGraph.cycleGraph r).Adj (pattern b q.castSucc (movingIndex r q)) (pattern b q.succ (movingIndex r q))) ∧
    pattern b 4 = pattern (b+1) 0 := by
  rcases hr with rfl | rfl
  · exact pattern7 b
  · exact pattern10 b

private def shiftOffset : Fin 5 → Fin 4 → ℕ :=
  ![![0,0,1,1],![0,0,2,1],![0,0,2,2],![1,0,2,2],![1,1,2,2]]
private def shiftIndex : Fin 4 → Fin 4 := ![2,3,0,1]

private theorem tag_bound : ∀ i, rowTag i ≤ 1 := by
  decide +kernel

private theorem row_certificates :
    (∀ q i, shiftOffset q i ≤ 2) ∧
    (∀ q i j, rowTag i < rowTag j → shiftOffset q i < shiftOffset q j) ∧
    (∀ q : Fin 4, (∀ i, i ≠ shiftIndex q → shiftOffset q.castSucc i = shiftOffset q.succ i) ∧
      shiftOffset q.castSucc (shiftIndex q) + 1 = shiftOffset q.succ (shiftIndex q)) ∧
    (∀ i, shiftOffset 0 i = rowTag i ∧ shiftOffset 4 i = rowTag i + 1) := by
  decide +kernel

open SimpleGraph
set_option maxHeartbeats 1000000

private theorem no_horizontal {r s : ℕ} [NeZero r] (hr : Supported r)
    {S : Finset (Fin r × Fin s)} (hc : S.card = 5) (hg : IsGeneralPosition (cylinder r s) S)
    (u v : Fin r × Fin s) (hu : u ∈ S) (hv : v ∉ S) (ha : (cylinder r s).Adj u v)
    (ht : IsGeneralPosition (cylinder r s) (insert v (S.erase u))) : u.2 ≠ v.2 := by
  intro hy
  obtain ⟨f,hi,hf,hs,ho⟩ := ordered_enumeration S hc
  obtain ⟨k,hku⟩ := hs u hu
  let g := Function.update f k v
  have hm := five_strict_rows hr hg f hf hi ho
  have hrows : ∀ i, (g i).2 = (f i).2 := by
    intro i
    by_cases h : i = k
    · subst i; simpa [g,hku] using hy.symm
    · simp [g,h]
  have hgi : Function.Injective g :=
    Function.Injective.of_comp (f := Prod.snd)
      (by change Function.Injective (fun i => (g i).2); simpa only [hrows] using hm.injective)
  have hgf : ∀ i, g i ∈ insert v (S.erase u) := by
    intro i
    by_cases h : i = k
    · subst i; simp [g]
    · have hfu : f i ≠ u := fun he => h (hi (he.trans hku.symm))
      simp [g,h,hfu,hf i]
  have hgo : Monotone (fun i => (g i).2) := by
    simpa only [hrows] using ho
  have hr3 : 3 ≤ r := by rcases hr with rfl | rfl <;> decide
  have hregf := rigidity hr (fun i => (f i).1) (gp_good5 hr3 hg f hf hi ho)
  have hregg := rigidity hr (fun i => (g i).1) (gp_good5 hr3 ht g hgf hgi hgo)
  have hx := regular_one_change hr _ _ hregf hregg k (by intro j hj; simp [g,hj])
  have he : u = v := by
    apply Prod.ext
    · have h := congrFun hx k
      simpa [g,hku] using h
    · exact hy
  exact (cylinder r s).ne_of_adj ha he

private theorem legal_columns {r s : ℕ} [NeZero r] (hr : Supported r)
    {S T : Finset (Fin r × Fin s)} (hc : S.card = 5)
    (hg : IsGeneralPosition (cylinder r s) S) (hm : LegalMove (cylinder r s) S T) :
    ∀ z ∈ T, z.1 ∈ S.image Prod.fst := by
  rcases hm with ⟨u,hu,v,hv,ha,rfl,ht⟩
  have hy := no_horizontal hr hc hg u v hu hv ha ht
  have hx : u.1 = v.1 := by
    rcases boxProd_adj.mp ha with h | h
    · exact False.elim (hy h.2)
    · exact h.2
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact Finset.mem_image.mpr ⟨u,hu,hx⟩
  · exact Finset.mem_image.mpr ⟨z,Finset.mem_of_mem_erase hz,rfl⟩

private theorem no_five_mobile {r s : ℕ} [NeZero r] (hr : Supported r)
    {S : Finset (Fin r × Fin s)} (hc : S.card = 5) : ¬ IsMobile (cylinder r s) S := by
  rintro ⟨hg,n,c,hc0,hm,hcover⟩
  have states : ∀ i : Fin (n+1), (c i).card = 5 ∧
      IsGeneralPosition (cylinder r s) (c i) ∧
      ∀ z ∈ c i, z.1 ∈ S.image Prod.fst := by
    intro i
    induction i using Fin.induction with
    | zero =>
      rw [hc0]
      exact ⟨hc,hg,fun z hz => Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
    | succ i ih =>
      have hi := hm i
      refine ⟨(legal_card hi).trans ih.1, ?_, ?_⟩
      · rcases hi with ⟨u,hu,v,hv,ha,he,hg⟩; exact hg
      · intro z hz
        obtain ⟨w,hw,he⟩ := Finset.mem_image.mp (legal_columns hr ih.1 ih.2.1 hi z hz)
        simpa [he] using ih.2.2 w hw
  have hcard : (S.image Prod.fst).card < (Finset.univ : Finset (Fin r)).card := by
    have hle := Finset.card_image_le (f:=Prod.fst) (s:=S)
    have hr5 : 5 < r := by rcases hr with rfl | rfl <;> decide
    simpa only [Finset.card_univ,Fintype.card_fin] using lt_of_le_of_lt hle (hc ▸ hr5)
  obtain ⟨x,hx,hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨i,hi⟩ := hcover (x,v.2)
  exact hnot ((states i).2.2 _ hi)

private theorem mobile_card_le_four {r s : ℕ} [NeZero r] (hr : Supported r)
    {S : Finset (Fin r × Fin s)} (hm : IsMobile (cylinder r s) S) : S.card ≤ 4 := by
  have hle := gp_card_le_five hr hm.1
  by_contra hn
  have he : S.card = 5 := by omega
  exact no_five_mobile hr he hm

open SimpleGraph
set_option maxHeartbeats 1000000

private def pairRow {s : ℕ} (j : ℕ) (hj : j + 1 < s) (i : Fin 4) : Fin s :=
  ⟨j + rowTag i, by have := tag_bound i; omega⟩
private def pairRobots {r s : ℕ} [NeZero r] (b : Fin r) (q : Fin 5) (j : ℕ) (hj : j+1<s) : Fin 4 → Fin r × Fin s :=
  Function.prod (pattern b q) (pairRow j hj)
private def pairConfig {r s : ℕ} [NeZero r] (b : Fin r) (q : Fin 5) (j : ℕ) (hj : j+1<s) : Finset (Fin r × Fin s) :=
  (fun f => Finset.univ.image f) (pairRobots b q j hj)

private theorem pair_gp {r s : ℕ} [NeZero r] (hr : Supported r) (b : Fin r) (q : Fin 5)
    (j : ℕ) (hj : j+1<s) : IsGeneralPosition (cylinder r s) (pairConfig b q j hj) := by
  have hr3 : 3 ≤ r := by rcases hr with rfl | rfl <;> decide
  apply separated_gp hr3 (pattern b q) (pairRow j hj) ((patterns hr b).1 q).1
  intro i k hik
  change j + rowTag i < j + rowTag k
  omega

private theorem pair_injective {r s : ℕ} [NeZero r] (hr : Supported r) (b : Fin r) (q : Fin 5)
    (j : ℕ) (hj : j+1<s) : Function.Injective (pairRobots b q j hj) := by
  exact Function.Injective.of_comp (f := Prod.fst) ((patterns hr b).1 q).2

private theorem pair_step {r s : ℕ} [NeZero r] (hr : Supported r) (b : Fin r) (q : Fin 4)
    (j : ℕ) (hj : j+1<s) :
    LegalMove (cylinder r s) (pairConfig b q.castSucc j hj) (pairConfig b q.succ j hj) := by
  apply labelled_move _ _ (movingIndex r q) (pair_injective hr _ _ _ _) (pair_injective hr _ _ _ _)
  · intro i hi
    apply Prod.ext
    · exact ((patterns hr b).2.1 q).1 i hi
    · rfl
  · apply boxProd_adj.mpr
    exact Or.inl ⟨((patterns hr b).2.1 q).2,rfl⟩
  · exact pair_gp hr _ _ _ _

private theorem pair_rotate {r s : ℕ} [NeZero r] (hr : Supported r) (b : Fin r)
    (j : ℕ) (hj : j+1<s) :
    Relation.ReflTransGen (LegalMove (cylinder r s)) (pairConfig b 0 j hj) (pairConfig (b+1) 0 j hj) := by
  have steps : ∀ q : Fin 5, Relation.ReflTransGen (LegalMove (cylinder r s)) (pairConfig b 0 j hj) (pairConfig b q j hj) := by
    intro q
    induction q using Fin.induction with
    | zero => exact .refl
    | succ i ih => exact ih.tail (pair_step hr b i j hj)
  have he : pairConfig b 4 j hj = pairConfig (b+1) 0 j hj := by
    apply congrArg (fun f => Finset.univ.image f)
    funext i
    apply Prod.ext
    · exact congrFun ((patterns hr b).2.2) i
    · rfl
  exact he ▸ steps 4

private theorem pair_all_rotations {r s : ℕ} [NeZero r] (hr : Supported r)
    (j : ℕ) (hj : j+1<s) (b : Fin r) :
    Relation.ReflTransGen (LegalMove (cylinder r s)) (pairConfig (0 : Fin r) 0 j hj) (pairConfig b 0 j hj) := by
  obtain ⟨n,rfl⟩ : ∃ n, r = n+1 := ⟨r-1, by have := NeZero.pos r; omega⟩
  induction b using Fin.induction with
  | zero => exact .refl
  | succ i ih =>
    have h := pair_rotate hr i.castSucc j hj
    have he : i.castSucc + 1 = i.succ := Fin.coeSucc_eq_succ
    rw [he] at h
    exact ih.trans h

open SimpleGraph
set_option maxHeartbeats 1000000

private def shiftRow {s : ℕ} (j : ℕ) (hj : j+2<s) (q : Fin 5) (i : Fin 4) : Fin s :=
  ⟨j+shiftOffset q i,by have := row_certificates.1 q i; omega⟩
private def shiftRobots {r s : ℕ} [NeZero r] (b : Fin r) (j : ℕ) (hj : j+2<s) (q : Fin 5) : Fin 4 → Fin r × Fin s :=
  Function.prod (pattern b 0) (shiftRow j hj q)
private def shiftConfig {r s : ℕ} [NeZero r] (b : Fin r) (j : ℕ) (hj : j+2<s) (q : Fin 5) : Finset (Fin r × Fin s) :=
  (fun f => Finset.univ.image f) (shiftRobots b j hj q)

private theorem shift_gp {r s : ℕ} [NeZero r] (hr : Supported r) (b : Fin r)
    (j : ℕ) (hj : j+2<s) (q : Fin 5) : IsGeneralPosition (cylinder r s) (shiftConfig b j hj q) := by
  have hr3 : 3 ≤ r := by rcases hr with rfl | rfl <;> decide
  apply separated_gp hr3 (pattern b 0) (shiftRow j hj q) ((patterns hr b).1 0).1
  intro i k hik
  change j + shiftOffset q i < j + shiftOffset q k
  have := row_certificates.2.1 q i k hik
  omega

private theorem shift_injective {r s : ℕ} [NeZero r] (hr : Supported r) (b : Fin r)
    (j : ℕ) (hj : j+2<s) (q : Fin 5) : Function.Injective (shiftRobots b j hj q) := by
  exact Function.Injective.of_comp (f := Prod.fst) ((patterns hr b).1 0).2

private theorem shift_step {r s : ℕ} [NeZero r] (hr : Supported r) (b : Fin r)
    (j : ℕ) (hj : j+2<s) (q : Fin 4) :
    LegalMove (cylinder r s) (shiftConfig b j hj q.castSucc) (shiftConfig b j hj q.succ) := by
  apply labelled_move _ _ (shiftIndex q) (shift_injective hr _ _ _ _) (shift_injective hr _ _ _ _)
  · intro i hi
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change j+shiftOffset q.castSucc i = j+shiftOffset q.succ i
      rw [(row_certificates.2.2.1 q).1 i hi]
  · apply boxProd_adj.mpr
    apply Or.inr
    refine ⟨pathGraph_adj.mpr (Or.inl ?_),rfl⟩
    change j + shiftOffset q.castSucc (shiftIndex q) + 1 = j + shiftOffset q.succ (shiftIndex q)
    have := (row_certificates.2.2.1 q).2
    omega
  · exact shift_gp hr _ _ _ _

private theorem row_shift {r s : ℕ} [NeZero r] (hr : Supported r) (b : Fin r)
    (j : ℕ) (hj : j+2<s) :
    Relation.ReflTransGen (LegalMove (cylinder r s)) (pairConfig b 0 j (by omega)) (pairConfig b 0 (j+1) (by omega)) := by
  have steps : ∀ q : Fin 5, Relation.ReflTransGen (LegalMove (cylinder r s)) (shiftConfig b j hj 0) (shiftConfig b j hj q) := by
    intro q
    induction q using Fin.induction with
    | zero => exact .refl
    | succ i ih => exact ih.tail (shift_step hr b j hj i)
  exact steps 4

private theorem all_row_pairs {r s : ℕ} [NeZero r] (hr : Supported r) (hs : 2 ≤ s)
    (j : ℕ) (hj : j+1<s) :
    Relation.ReflTransGen (LegalMove (cylinder r s)) (pairConfig (0 : Fin r) 0 0 (by omega)) (pairConfig (0 : Fin r) 0 j hj) := by
  induction j with
  | zero => exact .refl
  | succ j ih =>
    have h := ih (by omega)
    exact h.trans (row_shift hr 0 j (by omega))

variable {V : Type*} [DecidableEq V]

private theorem mobGP_eq {G : SimpleGraph V} {k : ℕ}
    (hu : ∀ S, IsMobile G S → S.card ≤ k)
    (hl : ∃ S : Finset V, S.card = k ∧ IsMobile G S) : mobGP G = k := by
  rcases hl with ⟨S,hc,hm⟩
  apply le_antisymm
  · exact csSup_le ⟨k,S,hc,hm⟩ (by rintro b ⟨T,hT,hmT⟩; simpa [← hT] using hu T hmT)
  · exact le_csSup ⟨k, by rintro b ⟨T,hT,hmT⟩; simpa [← hT] using hu T hmT⟩ ⟨S,hc,hm⟩

set_option maxHeartbeats 1000000

private theorem four_mobile {r s : ℕ} [NeZero r] (hr : Supported r) (hs : 2 ≤ s) :
    ∃ S : Finset (Fin r × Fin s), S.card = 4 ∧ IsMobile (cylinder r s) S := by
  let S : Finset (Fin r × Fin s) := pairConfig 0 0 0 (by omega)
  refine ⟨S,configuration_card _ (pair_injective hr _ _ _ _),?_⟩
  apply mobile_of_reaches (pair_gp hr _ _ _ _)
  rintro ⟨x,y⟩
  by_cases hy : y.val+1 < s
  · refine ⟨pairConfig x 0 y.val hy, (all_row_pairs hr hs y.val hy).trans (pair_all_rotations hr y.val hy x),?_⟩
    apply (mem_configuration _ _).mpr
    refine ⟨0,?_⟩
    apply Prod.ext
    · change pattern x 0 0 = x
      simp only [pattern]
      split_ifs <;> simp
    · apply Fin.ext
      simp [pairRobots,pairRow,rowTag]
  · have hyv : 1 ≤ y.val := by have := y.isLt; omega
    have hj : y.val-1+1 < s := by have := y.isLt; omega
    refine ⟨pairConfig (x-1) 0 (y.val-1) hj,
      (all_row_pairs hr hs (y.val-1) hj).trans (pair_all_rotations hr (y.val-1) hj (x-1)),?_⟩
    apply (mem_configuration _ _).mpr
    refine ⟨2,?_⟩
    apply Prod.ext
    · change pattern (x-1) 0 2 = x
      simp only [pattern]
      split_ifs <;> simp
    · apply Fin.ext
      change y.val-1+rowTag 2 = y.val
      simp only [rowTag,Matrix.cons_val]
      omega

theorem result : claim := by
  intro s hs
  constructor
  · exact mobGP_eq (fun S hm => mobile_card_le_four (Or.inl rfl) hm)
      (four_mobile (Or.inl rfl) (by omega))
  · exact mobGP_eq (fun S hm => mobile_card_le_four (Or.inr rfl) hm)
      (four_mobile (Or.inr rfl) (by omega))


end D5.S3.Combinatorics.Graph.GeneralPosition.CylinderSevenTen
