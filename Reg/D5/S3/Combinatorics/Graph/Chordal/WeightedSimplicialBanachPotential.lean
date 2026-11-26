import D5.S3.Combinatorics.Graph.Chordal.WeightedSimplicialBanachPotential
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Numerical checks and source-bound registrations for weighted reconstruction. -/

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.WeightedSimplicialBanachPotential

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support
open LeanInformationAudit SimpleGraph
open scoped BigOperators

noncomputable section

universe u v w

private abbrev Pair := ULift.{u} (Fin 2)
private abbrev Root := ULift.{w} Unit
private def a : Pair.{u} := ⟨0⟩
private def b : Pair.{u} := ⟨1⟩
private def r : Root.{w} := ⟨()⟩
private def pairBag : Root.{w} → Set Pair.{u} := fun _ => Set.univ
private abbrev pairGraph : SimpleGraph Pair.{u} := ⊤

private theorem pair_adj : pairGraph.Adj a b := by
  change a ≠ b
  intro h
  exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down h)

private theorem pair_chordal : pairGraph.{u}.IsChordal := by
  have h : pairGraph.{u}.IsAcyclic := IsAcyclic.of_card_le_two (by simp)
  exact fun _ hp _ => (h _ hp).elim

private theorem pair_cliques : ∀ C : Set Pair.{u}, pairGraph.IsClique C → C.ncard ≤ 2 + 1 := by
  intro C _
  have h := C.ncard_le_card
  simpa using h.trans (by simp : Nat.card Pair.{u} ≤ 2 + 1)

private theorem one_bag : IsCliqueTree (⊥ : SimpleGraph Root.{w}) pairGraph.{u} pairBag where
  isTree := IsTree.of_subsingleton
  clique _ _ _ _ _ h := h
  cover _ := ⟨r, Set.mem_univ _⟩
  edge _ _ _ := ⟨r, Set.mem_univ _, Set.mem_univ _⟩
  running _ _ _ _ _ _ _ := Set.mem_univ _

private def pairProbability (_ : Root.{w}) (_ : Pair.{u}) : ℝ := 1 / 2

private theorem pairProbability_total (i : Root.{w}) : ∑ x, pairProbability i x = 1 := by
  norm_num [pairProbability, nsmul_eq_mul, Fintype.card_ulift, Finset.sum_const]

private def radius (k : ℕ) : ℝ :=
  max ((k : ℝ)-2) (((k : ℝ)-1 + Real.sqrt (((k : ℝ)+3)^2-16))/4)

private theorem sqrt_bound {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x < y^2) :
    Real.sqrt x < y := by
  by_contra! hn
  have h₁ := Real.sq_sqrt hx
  have h₂ := mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ Real.sqrt x + y by positivity)
  nlinarith

private theorem sqrt_nine : Real.sqrt 9 = 3 :=
  (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)

example : radius 2 = 1 := by norm_num [radius, sqrt_nine]

example : radius 3 = (1 + Real.sqrt 5)/2 ∧ (1 + Real.sqrt 5)/2 < 5/3 ∧ (5/3 : ℝ) < 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg 5
  have h₁ : 1 ≤ Real.sqrt 5 := by nlinarith
  have h₂ := sqrt_bound (x := 5) (y := 7/3) (by norm_num) (by norm_num) (by norm_num)
  have h20 : Real.sqrt (20 : ℝ) = 2 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)]
    nlinarith
  refine ⟨?_, by linarith, by norm_num⟩
  norm_num [radius, h20, max_eq_right (show (1 : ℝ) ≤ (1+2*Real.sqrt 5)/4 by linarith)]
  ring

example :
    radius 4 = (3 + Real.sqrt 33)/4 ∧ (3 + Real.sqrt 33)/4 < 7/3 ∧ (7/3 : ℝ) < 20/7 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 33 by norm_num)
  have hn := Real.sqrt_nonneg 33
  have h₁ : 5 ≤ Real.sqrt 33 := by nlinarith
  have h₂ := sqrt_bound (x := 33) (y := 19/3) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, by linarith, by norm_num⟩
  norm_num [radius, max_eq_right (show (2 : ℝ) ≤ (3+Real.sqrt 33)/4 by linarith)]

example : radius 5 = 3 ∧ (3 : ℝ) < 40/13 := by
  have hs := sqrt_bound (x := 48) (y := 8) (by norm_num) (by norm_num) (by norm_num)
  norm_num [radius, max_eq_left (show (4+Real.sqrt 48)/4 ≤ (3 : ℝ) by linarith)]

namespace Simplicial

abbrev signature := SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ k ε =>
    max ((k : ℝ)-2) (((k : ℝ)-1 + Real.sqrt (((k : ℝ)+3)^2-16))/4)*ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [Finite V] {G : SimpleGraph V} (_hG : G.IsChordal)
    (k : ℕ) (_hk : 2 ≤ k) (_hclique : ∀ C : Set V, G.IsClique C → C.ncard ≤ k+1)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (_hε : 0 ≤ ε) (_hskew : ∀ x y, g y x = -g x y)
    (_htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖g x y + g y z - g x z‖ ≤ ε),
    ∃ φ : V → E, ∀ x y, G.Adj x y → ‖g x y - (φ y - φ x)‖ ≤ R.readout () k ε

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  obtain ⟨φ, hf⟩ := h pair_chordal 2 le_rfl pair_cliques
    (E := ULift.{v} ℝ) (fun _ _ => 0) 0 le_rfl (by simp) (by simp)
  have hn := hf a b pair_adj
  change ‖(0 : ULift.{v} ℝ) - (φ b - φ a)‖ ≤ -1 at hn
  linarith [norm_nonneg ((0 : ULift.{v} ℝ) - (φ b - φ a))]

def family : Registration arena.{u,v}
    (type_of% (@IsChordal.exists_weighted_simplicial_banach_gain_potential.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@IsChordal.exists_weighted_simplicial_banach_gain_potential.{u,v}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨2, 0, 1, ?_⟩
    norm_num [actual, realize, sqrt_nine]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@IsChordal.exists_weighted_simplicial_banach_gain_potential.{u,v})
    (Realization signature) Unit Unit where
  unitName := `SimpleGraph.IsChordal.exists_weighted_simplicial_banach_gain_potential.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.WeightedSimplicialBanachPotential.Simplicial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.WeightedSimplicialBanachPotential
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Simplicial

namespace Occurrence

abbrev signature := SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, ℕ)
  (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p ε => (p.1 + 4 * (((p.2.2+1)/2 : ℕ) : ℝ) * p.2.1) * ε)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [Fintype V] {I : Type w} [Finite I]
    {T : SimpleGraph I} {G : SimpleGraph V} {K : I → Set V}
    (_hK : IsCliqueTree T G K) (_hsep : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty)
    (π : I → V → ℝ) (_hπ : ∀ a x, 0 ≤ π a x)
    (_hsupp : ∀ a x, x ∉ K a → π a x = 0) (_htotal : ∀ a, ∑ x, π a x = 1)
    (α d : ℝ) (_hα₀ : 0 ≤ α) (_hd₀ : 0 ≤ d)
    (_hα : ∀ a u v, u ∈ K a → v ∈ K a → G.Adj u v → 1 - π a u - π a v ≤ α)
    (_hd : ∀ a b, T.Adj a b →
      (1 - 1 / ((K a ∩ K b).ncard : ℝ)) *
        (1 - ∑ x ∈ (K a ∩ K b).toFinite.toFinset, min (π a x) (π b x)) ≤ d)
    (D : ℕ) (_hD : ∀ x a b, x ∈ K a → x ∈ K b → T.dist a b ≤ D)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (_hε : 0 ≤ ε) (_hskew : ∀ u v, g v u = -g u v)
    (_htri : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj u w → ‖g u v + g v w - g u w‖ ≤ ε),
    ∃ φ : V → E, ∀ u v, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ R.readout () ⟨α,d,D⟩ ε ∧
      (D ≤ 1 → ‖g u v - (φ v - φ u)‖ ≤ (α + 2*d) * ε)

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  obtain ⟨φ, hf⟩ := h one_bag (fun i j h => False.elim h)
    pairProbability (fun _ _ => by norm_num [pairProbability])
    (fun _ x h => (h (Set.mem_univ x)).elim) pairProbability_total
    1 0 (by norm_num) le_rfl (fun _ _ _ _ _ _ => by norm_num [pairProbability])
    (fun _ _ h => False.elim h) 0 (fun _ i j _ _ => by simp [Subsingleton.elim j i])
    (E := ULift.{v} ℝ) (fun _ _ => 0) 0 le_rfl (by simp) (by simp)
  have hn := (hf a b pair_adj).1
  change ‖(0 : ULift.{v} ℝ) - (φ b - φ a)‖ ≤ -1 at hn
  linarith [norm_nonneg ((0 : ULift.{v} ℝ) - (φ b - φ a))]

def family : Registration arena.{u,v,w}
    (type_of% (@cliqueTree_occurrenceCenter_banach_potential.{u,w,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cliqueTree_occurrenceCenter_banach_potential.{u,w,v}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨⟨1,0,0⟩, 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cliqueTree_occurrenceCenter_banach_potential.{u,w,v})
    (Realization signature) Unit Unit where
  unitName := `SimpleGraph.cliqueTree_occurrenceCenter_banach_potential.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.WeightedSimplicialBanachPotential.Occurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.WeightedSimplicialBanachPotential
    definition := none
    coordinates := #[13,14,19]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body",
        "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 25
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Occurrence

section OccurrenceExamples

variable {V I E : Type*} [Fintype V] [Fintype I]
variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable {T : SimpleGraph I} {G : SimpleGraph V} {K : I → Set V}

private noncomputable def uniform (S : Set V) (x : V) : ℝ :=
  open Classical in if x ∈ S then 1/(S.ncard : ℝ) else 0

private theorem uniform_nonneg (S : Set V) (x : V) : 0 ≤ uniform S x := by
  classical
  simp only [uniform]
  split_ifs <;> positivity

private theorem uniform_total {S : Set V} (hS : S.Nonempty) : ∑ x, uniform S x = 1 := by
  classical
  have hpos : (0 : ℝ) < S.ncard := by exact_mod_cast Set.ncard_pos.mpr hS
  have he : (Finset.univ.filter fun x => x ∈ S) = S.toFinite.toFinset := by ext x; simp
  simp only [uniform, ← Finset.sum_filter, he, Finset.sum_const, nsmul_eq_mul,
    ← Set.ncard_eq_toFinset_card]
  field_simp

private theorem separator_mass_uniform (hK₀ : ∀ a, (K a).Nonempty)
    (c : ℝ) (hc : 1 ≤ c) (a b : I)
    (hsize : (max (K a).ncard (K b).ncard : ℝ) ≤ c * ((K a ∩ K b).ncard : ℝ))
    (hs : (K a ∩ K b).Nonempty) :
    1/c ≤ ∑ x ∈ (K a ∩ K b).toFinite.toFinset, min (uniform (K a) x) (uniform (K b) x) := by
  classical
  let M : ℝ := max (K a).ncard (K b).ncard
  have hM : 0 < M := by
    have h : (0 : ℝ) < (K a).ncard := by exact_mod_cast Set.ncard_pos.mpr (hK₀ a)
    exact h.trans_le (by dsimp [M]; exact_mod_cast le_max_left (K a).ncard (K b).ncard)
  have hspos : (0 : ℝ) < (K a ∩ K b).ncard := by exact_mod_cast Set.ncard_pos.mpr hs
  calc
    1/c ≤ ((K a ∩ K b).ncard : ℝ) / M :=
      (div_le_div_iff₀ (by linarith) hM).2 (by simpa [M, mul_comm] using hsize)
    _ = ∑ x ∈ (K a ∩ K b).toFinite.toFinset, 1/M := by
      simp [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card, div_eq_mul_inv]
    _ ≤ _ := Finset.sum_le_sum fun x hx => by
      have hx' : x ∈ K a ∩ K b := by simpa using hx
      simp only [uniform, hx'.1, hx'.2, ite_true, le_min_iff]
      constructor
      · exact one_div_le_one_div_of_le (by exact_mod_cast Set.ncard_pos.mpr (hK₀ a))
          (by dsimp [M]; exact_mod_cast le_max_left (K a).ncard (K b).ncard)
      · exact one_div_le_one_div_of_le (by exact_mod_cast Set.ncard_pos.mpr (hK₀ b))
          (by dsimp [M]; exact_mod_cast le_max_right (K a).ncard (K b).ncard)

private theorem separator_coefficient {S : Set V} (hS : S.Nonempty)
    {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 1 - M ≤ δ) :
    (1 - 1 / (S.ncard : ℝ)) * (1 - M) ≤ (1 - 1 / (S.ncard : ℝ)) * δ := by
  have hpos : (1 : ℝ) ≤ S.ncard := by
    exact_mod_cast Nat.succ_le_of_lt (Set.ncard_pos.mpr hS)
  apply mul_le_mul_of_nonneg_left hM
  exact sub_nonneg.mpr ((div_le_iff₀ (by linarith : (0 : ℝ) < S.ncard)).2 (by linarith))

private theorem reconstruct_from_probabilities (hK : IsCliqueTree T G K)
    (hsep : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty)
    (π : I → V → ℝ) (hπ : ∀ a x, 0 ≤ π a x)
    (hsupp : ∀ a x, x ∉ K a → π a x = 0) (htotal : ∀ a, ∑ x, π a x = 1)
    (d : ℝ) (hd₀ : 0 ≤ d)
    (hd : ∀ a b, T.Adj a b → (1 - 1 / ((K a ∩ K b).ncard : ℝ)) *
      (1 - ∑ x ∈ (K a ∩ K b).toFinite.toFinset, min (π a x) (π b x)) ≤ d)
    (D : ℕ) (hD : ∀ x a b, x ∈ K a → x ∈ K b → T.dist a b ≤ D)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hskew : ∀ x y, g y x = -g x y)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖g x y + g y z - g x z‖ ≤ ε) :
    ∃ φ : V → E, ∀ x y, G.Adj x y →
      ‖g x y - (φ y - φ x)‖ ≤ (1 + 4*(((D+1)/2 : ℕ) : ℝ)*d)*ε ∧
      (D ≤ 1 → ‖g x y - (φ y - φ x)‖ ≤ (1+2*d)*ε) :=
  cliqueTree_occurrenceCenter_banach_potential hK hsep π hπ hsupp htotal 1 d zero_le_one hd₀
    (fun a x y _ _ _ => by linarith [hπ a x, hπ a y]) hd D hD g ε hε hskew htri

example (hK : IsCliqueTree T G K) (hsep : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty)
    (hK₀ : ∀ a, (K a).Nonempty)
    (c : ℝ) (hc : 1 ≤ c)
    (hsize : ∀ a b, T.Adj a b →
      (max (K a).ncard (K b).ncard : ℝ) ≤ c * ((K a ∩ K b).ncard : ℝ))
    (hD : ∀ x a b, x ∈ K a → x ∈ K b → T.dist a b ≤ 2)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hskew : ∀ x y, g y x = -g x y)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖g x y + g y z - g x z‖ ≤ ε) :
    ∃ φ : V → E, ∀ x y, G.Adj x y → ‖g x y - (φ y - φ x)‖ ≤ (5-4/c)*ε := by
  classical
  have hc₀ : 0 < c := by linarith
  have hδ : 0 ≤ 1-1/c := sub_nonneg.mpr ((div_le_iff₀ hc₀).2 (by linarith))
  have hd (a b : I) (hab : T.Adj a b) :
      (1 - 1 / ((K a ∩ K b).ncard : ℝ)) *
        (1 - ∑ x ∈ (K a ∩ K b).toFinite.toFinset,
          min (uniform (K a) x) (uniform (K b) x)) ≤ 1-1/c := by
    have hM := separator_mass_uniform hK₀ c hc a b (hsize a b hab) (hsep a b hab)
    refine (separator_coefficient (hsep a b hab) hδ (by linarith)).trans ?_
    exact mul_le_of_le_one_left hδ (sub_le_self _ (by positivity))
  obtain ⟨φ, hφ⟩ := reconstruct_from_probabilities hK hsep (fun a => uniform (K a))
    (fun a => uniform_nonneg (K a)) (fun a x hx => by simp [uniform, hx])
    (fun a => uniform_total (hK₀ a)) _ hδ hd 2 hD g ε hε hskew htri
  refine ⟨φ, fun x y hxy => ?_⟩
  convert (hφ x y hxy).1 using 1 <;> norm_num <;> ring

example : (5 : ℝ) - 4/2 = 3 ∧ (5 : ℝ) - 4/(4/3) = 2 := by norm_num

private theorem degree_probability (hsep : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty)
    (hK₀ : ∀ a, (K a).Nonempty) (b : ℕ) (hb : 2 ≤ b)
    (hdeg : ∀ a, (T.neighborSet a).ncard ≤ b) :
    ∃ π : I → V → ℝ,
      (∀ a x, 0 ≤ π a x) ∧ (∀ a x, x ∉ K a → π a x = 0) ∧
      (∀ a, ∑ x, π a x = 1) ∧
      ∀ a j, T.Adj a j → 1/(b : ℝ) ≤
        ∑ x ∈ (K a ∩ K j).toFinite.toFinset, min (π a x) (π j x) := by
  classical
  let N (a : I) := (T.neighborSet a).toFinite.toFinset
  let π (a : I) (x : V) :=
    if (N a).Nonempty then (∑ j ∈ N a, uniform (K a ∩ K j) x) / ((N a).card : ℝ)
    else uniform (K a) x
  have mem (a j : I) : j ∈ N a ↔ T.Adj a j := by simp [N]
  have pos {a : I} (h : (N a).Nonempty) : 0 < ((N a).card : ℝ) := by exact_mod_cast h.card_pos
  have hnon (a x) : 0 ≤ π a x := by
    simp only [π]
    split_ifs with h
    · exact div_nonneg (Finset.sum_nonneg fun i _ => uniform_nonneg _ _) (pos h).le
    · exact uniform_nonneg _ _
  have hsupp (a x) (h : x ∉ K a) : π a x = 0 := by
    simp [π, uniform, h]
  have htotal (a) : ∑ x, π a x = 1 := by
    by_cases h : (N a).Nonempty
    · simp only [π, h, if_true, ← Finset.sum_div]
      rw [Finset.sum_comm]
      have hsum : ∑ j ∈ N a, ∑ x, uniform (K a ∩ K j) x = (N a).card := by
        rw [← Finset.sum_const_one]
        exact Finset.sum_congr rfl fun j hj => uniform_total (hsep _ _ ((mem a j).1 hj))
      rw [hsum, div_self (pos h).ne']
    · simpa [π, h] using uniform_total (hK₀ a)
  refine ⟨π, hnon, hsupp, htotal, ?_⟩
  have lb (a j : I) (h : T.Adj a j) (x : V) (hx : x ∈ K a ∩ K j) :
      1 / ((b : ℝ) * ((K a ∩ K j).ncard : ℝ)) ≤ π a x := by
    have hj := (mem a j).2 h
    have hn : (N a).Nonempty := ⟨j, hj⟩
    have hb' : (N a).card ≤ b := by simp [N, ← Set.ncard_eq_toFinset_card, hdeg]
    have hsep' : (0 : ℝ) < (K a ∩ K j).ncard := by exact_mod_cast Set.ncard_pos.mpr ⟨x, hx⟩
    have hsum : uniform (K a ∩ K j) x ≤ ∑ i ∈ N a, uniform (K a ∩ K i) x :=
      Finset.single_le_sum (fun i _ => uniform_nonneg _ _) hj
    calc
      _ = (1 / ((K a ∩ K j).ncard : ℝ)) / (b : ℝ) := by ring
      _ ≤ (1 / ((K a ∩ K j).ncard : ℝ)) / ((N a).card : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (pos hn) (by exact_mod_cast hb')
      _ ≤ _ := by
        simp only [π, hn, if_true]
        exact div_le_div_of_nonneg_right (by simpa [uniform, hx] using hsum) (pos hn).le
  intro a j h
  have hsep' : ((K a ∩ K j).ncard : ℝ) ≠ 0 := by
    exact_mod_cast (Set.ncard_pos.mpr (hsep a j h)).ne'
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  calc
    _ = ∑ x ∈ (K a ∩ K j).toFinite.toFinset,
        1 / ((b : ℝ) * ((K a ∩ K j).ncard : ℝ)) := by
          simp only [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card]
          field_simp
    _ ≤ _ := Finset.sum_le_sum fun x hx => by
      have hx' : x ∈ K a ∩ K j := by simpa using hx
      exact le_min (lb a j h x hx') (by simpa [Set.inter_comm (K j) (K a)] using
        lb j a h.symm x (by simpa [Set.inter_comm (K j) (K a)] using hx'))

private theorem degree_fit (hK : IsCliqueTree T G K)
    (hsep : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty) (hK₀ : ∀ a, (K a).Nonempty)
    (b : ℕ) (hb : 2 ≤ b) (hdeg : ∀ a, (T.neighborSet a).ncard ≤ b)
    (D : ℕ) (hD : ∀ x a j, x ∈ K a → x ∈ K j → T.dist a j ≤ D)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hskew : ∀ x y, g y x = -g x y)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖g x y + g y z - g x z‖ ≤ ε) :
    ∃ d : ℝ, d < 1-1/(b : ℝ) ∧ ∃ φ : V → E, ∀ x y, G.Adj x y →
      ‖g x y - (φ y - φ x)‖ ≤ (1 + 4*(((D+1)/2 : ℕ) : ℝ)*d)*ε ∧
      (D ≤ 1 → ‖g x y - (φ y - φ x)‖ ≤ (1+2*d)*ε) := by
  classical
  obtain ⟨π, hπ, hsupp, htotal, hmass⟩ := degree_probability hsep hK₀ b hb hdeg
  let δ : ℝ := 1-1/(b : ℝ)
  have hδ : 0 < δ := by
    have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
    have := (div_lt_iff₀ (show (0 : ℝ) < b by linarith)).2 (show (1 : ℝ) < 1*b by linarith)
    dsimp [δ]; linarith
  let A := (Finset.univ : Finset (I × I)).filter fun p => T.Adj p.1 p.2
  let margin (p : I × I) := (1 - 1 / ((K p.1 ∩ K p.2).ncard : ℝ)) * δ
  let B := insert 0 (A.image margin)
  have hB : B.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  let d := B.max' hB
  have hd₀ : 0 ≤ d := Finset.le_max' B 0 (Finset.mem_insert_self _ _)
  have hdδ : d < δ := by
    apply (Finset.max'_lt_iff _).2
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hδ
    obtain ⟨⟨a,j⟩, ha, rfl⟩ := Finset.mem_image.mp hc
    have h := (Finset.mem_filter.mp ha).2
    have hpos : (0 : ℝ) < (K a ∩ K j).ncard := by exact_mod_cast Set.ncard_pos.mpr (hsep a j h)
    exact mul_lt_of_lt_one_left hδ (by linarith [one_div_pos.mpr hpos])
  have hd (a j : I) (h : T.Adj a j) :
      (1 - 1 / ((K a ∩ K j).ncard : ℝ)) *
        (1 - ∑ x ∈ (K a ∩ K j).toFinite.toFinset, min (π a x) (π j x)) ≤ d :=
    (separator_coefficient (hsep a j h) hδ.le (by dsimp [δ]; linarith [hmass a j h])).trans
      (Finset.le_max' B (margin (a,j)) (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨(a,j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩)))
  exact ⟨d, hdδ, reconstruct_from_probabilities hK hsep π hπ hsupp htotal d hd₀ hd D hD g ε hε hskew htri⟩

example (hK : IsCliqueTree T G K) (hsep : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty)
    (hK₀ : ∀ a, (K a).Nonempty) (hdeg : ∀ a, (T.neighborSet a).ncard ≤ 3)
    (hD : ∀ x a b, x ∈ K a → x ∈ K b → T.dist a b ≤ 2)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hskew : ∀ x y, g y x = -g x y)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖g x y + g y z - g x z‖ ≤ ε) :
    ∃ R : ℝ, R < 11/3 ∧ ∃ φ : V → E, ∀ x y, G.Adj x y →
      ‖g x y - (φ y - φ x)‖ ≤ R*ε := by
  obtain ⟨d, hd, φ, hf⟩ := degree_fit hK hsep hK₀ 3 (by decide) hdeg 2 hD g ε hε hskew htri
  exact ⟨1+4*d, by norm_num at hd ⊢; linarith, φ, fun x y h => by simpa using (hf x y h).1⟩

example (hK : IsCliqueTree T G K) (hsep : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty)
    (hK₀ : ∀ a, (K a).Nonempty) (hdeg : ∀ a, (T.neighborSet a).ncard ≤ 2)
    (hD : ∀ x a b, x ∈ K a → x ∈ K b → T.dist a b ≤ 1)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hskew : ∀ x y, g y x = -g x y)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z → ‖g x y + g y z - g x z‖ ≤ ε) :
    ∃ R : ℝ, R < 2 ∧ ∃ φ : V → E, ∀ x y, G.Adj x y →
      ‖g x y - (φ y - φ x)‖ ≤ R*ε := by
  obtain ⟨d, hd, φ, hf⟩ := degree_fit hK hsep hK₀ 2 (by decide) hdeg 1 hD g ε hε hskew htri
  exact ⟨1+2*d, by norm_num at hd; linarith, φ, fun x y h => (hf x y h).2 le_rfl⟩

end OccurrenceExamples

end Reg.D5.S3.Combinatorics.Graph.Chordal.WeightedSimplicialBanachPotential
