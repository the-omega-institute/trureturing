import D5.S3.Combinatorics.Graph.Chordal.CliqueTreeBanachPotential
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Numerical specializations and the dependent readouts of clique-tree residual bounds. -/

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.CliqueTreeBanachPotential

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support
open LeanInformationAudit SimpleGraph

noncomputable section

universe u v w

private theorem radius_step (m n : ℕ) :
    cliqueTreeRadius m 1 n ≤ cliqueTreeRadius m 1 (n + 1) :=
  (le_max_left _ _).trans (le_max_left _ _)

private theorem radius_mono (m : ℕ) : Monotone (cliqueTreeRadius m 1) :=
  monotone_nat_of_le_succ (radius_step m)

private theorem radius_small (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    cliqueTreeRadius m 1 n < (n : ℝ) + 1 ∨ n = 0 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlt : 1 - 1 / (m : ℝ) < 1 := by linarith [one_div_pos.mpr hm']
  have hR : ∀ i, 1 ≤ cliqueTreeRadius m 1 i := by
    intro i
    exact (show 1 ≤ cliqueTreeRadius m 1 0 by rfl).trans (radius_mono m (Nat.zero_le i))
  induction n with
  | zero => exact Or.inr rfl
  | succ n ih =>
    left
    have hi : cliqueTreeRadius m 1 n ≤ (n : ℝ) + 1 := by
      rcases ih with hi | rfl
      · exact hi.le
      · norm_num [cliqueTreeRadius]
    rw [cliqueTreeRadius, max_lt_iff, max_lt_iff]
    push_cast
    have hp : 0 < 1 + cliqueTreeRadius m 1 n := by linarith [hR n]
    have hprod := mul_lt_mul_of_pos_right hlt hp
    rw [one_mul] at hprod
    exact ⟨⟨by linarith, by linarith [Nat.cast_nonneg (α := ℝ) n]⟩, by linarith⟩

example (m D : ℕ) (hm : 1 ≤ m) (hD : D ≤ 5) :
    cliqueTreeRadius m 1 (D / 2) < 3 := by
  refine lt_of_le_of_lt (radius_mono m (show D / 2 ≤ 2 by omega)) ?_
  simpa only [Nat.cast_ofNat, show (2 : ℝ) + 1 = 3 by norm_num] using (radius_small m hm 2).resolve_right (by decide)

example (m D : ℕ) (hm : 1 ≤ m) (hD : D ≤ 7) :
    cliqueTreeRadius m 1 (D / 2) < 4 := by
  refine lt_of_le_of_lt (radius_mono m (show D / 2 ≤ 3 by omega)) ?_
  simpa only [Nat.cast_ofNat, show (3 : ℝ) + 1 = 4 by norm_num] using (radius_small m hm 3).resolve_right (by decide)

example (D : ℕ) (hD : D ≤ 19) :
    cliqueTreeRadius 4 1 (D / 2) ≤ 373533 / 131072 ∧ (373533 / 131072 : ℝ) < 20 / 7 := by
  refine ⟨(radius_mono 4 (show D / 2 ≤ 9 by omega)).trans ?_, by norm_num⟩
  norm_num [cliqueTreeRadius, max_def]

private abbrev Pair := ULift.{u} (Fin 2)
private abbrev Root := ULift.{w} Unit
private def a : Pair.{u} := ⟨0⟩
private def b : Pair.{u} := ⟨1⟩
private def r : Root.{w} := ⟨()⟩
private def pairBag : Root.{w} → Set Pair.{u} := fun _ => Set.univ

private theorem pair_adj : (⊤ : SimpleGraph Pair.{u}).Adj a b := by
  change a ≠ b
  intro h
  exact (by decide : (0 : Fin 2) ≠ 1) (congrArg ULift.down h)

private theorem one_bag : IsCliqueTree (⊥ : SimpleGraph Root.{w}) (⊤ : SimpleGraph Pair.{u})
    pairBag where
  isTree := IsTree.of_subsingleton
  clique _ _ _ _ _ h := h
  cover _ := ⟨r, Set.mem_univ _⟩
  edge _ _ _ := ⟨r, Set.mem_univ _, Set.mem_univ _⟩
  running _ _ _ _ _ _ _ := Set.mem_univ _

private theorem no_sep (i j : Root.{w}) (h : (⊥ : SimpleGraph Root.{w}).Adj i j) : False := h

namespace Center

abbrev signature := SingleDependentReadout.signature (ℕ × ℕ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p ε => cliqueTreeRadius p.1 1 (p.2 / 2) * ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [Finite V] {I : Type w} [Finite I]
    {T : SimpleGraph I} {G : SimpleGraph V} {K : I → Set V}
    (_hK : IsCliqueTree T G K) (_hs : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty)
    (m : ℕ) (_hm : 1 ≤ m) (_hsep : ∀ a b, T.Adj a b → (K a ∩ K b).ncard ≤ m)
    (D : ℕ) (_hD : ∀ a b, T.dist a b ≤ D)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (_hε : 0 ≤ ε) (_hrev : ∀ i j, g j i = -g i j)
    (_htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε),
    ∃ φ : V → E, ∀ u v, G.Adj u v → ‖g u v - (φ v - φ u)‖ ≤ R.readout () (m, D) ε

private theorem rejected_law : ¬ arena.{u, v, w}.Law rejected := by
  intro h
  obtain ⟨φ, hφ⟩ := h one_bag (fun i j h => (no_sep i j h).elim)
    1 le_rfl (fun i j h => (no_sep i j h).elim) 0 (fun i j => by
      simp [Subsingleton.elim j i, SimpleGraph.dist_self])
    (E := ULift.{v} ℝ) (fun _ _ => 0) 0 le_rfl (by simp) (by simp)
  have hn := hφ a b pair_adj
  change ‖(0 : ULift.{v} ℝ) - (φ b - φ a)‖ ≤ -1 at hn
  linarith [norm_nonneg ((0 : ULift.{v} ℝ) - (φ b - φ a))]

def family : Registration arena.{u, v, w}
    (type_of% (@cliqueTree_center_extension_banach_potential.{u, v, w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cliqueTree_center_extension_banach_potential.{u, v, w}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(1, 0), 0, 1, ?_⟩
    norm_num [actual, realize, cliqueTreeRadius]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cliqueTree_center_extension_banach_potential.{u, v, w})
    (Realization signature) Unit Unit where
  unitName := `SimpleGraph.cliqueTree_center_extension_banach_potential.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.CliqueTreeBanachPotential.Center.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.CliqueTreeBanachPotential
    definition := none
    coordinates := #[9, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 18
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Center

namespace Midpoint

structure Params where
  vertices : Type u
  bags : Type w
  finiteBags : Finite bags
  tree : SimpleGraph bags
  clique : bags → Set vertices

abbrev signature : Signature where
  Params := Params.{u, w}
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, w} :=
  realize signature (fun _ p ε => @cliqueTreeMidpointCoeff _ _ p.finiteBags p.tree p.clique * ε)
    (fun e => nomatch e)

def rejected : Realization signature.{u, w} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, w}
  Law R := ∀ {V : Type u} [Finite V] {I : Type w} [fI : Finite I]
    {T : SimpleGraph I} {G : SimpleGraph V} {K : I → Set V}
    (_hK : IsCliqueTree T G K) (_hs : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty)
    (_h₂ : ∀ x : V, {i : I | x ∈ K i}.ncard ≤ 2)
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (_hε : 0 ≤ ε) (_hrev : ∀ i j, g j i = -g i j)
    (_htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε),
    cliqueTreeMidpointCoeff T K < 3 ∧ ∃ φ : V → E, ∀ u v, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ R.readout () ⟨V, I, fI, T, K⟩ ε

private theorem at_most_two (x : Pair.{u}) : {i : Root.{w} | x ∈ pairBag i}.ncard ≤ 2 := by
  have hs : {i : Root.{w} | x ∈ pairBag i} = Set.univ := by ext i; simp [pairBag]
  rw [hs, Set.ncard_univ, Nat.card_eq_fintype_card]
  simp

private theorem rejected_law : ¬ arena.{u, v, w}.Law rejected := by
  intro h
  obtain ⟨_, φ, hφ⟩ := h one_bag (fun i j h => (no_sep i j h).elim) at_most_two
    (E := ULift.{v} ℝ) (fun _ _ => 0) 0 le_rfl (by simp) (by simp)
  have hn := hφ a b pair_adj
  change ‖(0 : ULift.{v} ℝ) - (φ b - φ a)‖ ≤ -1 at hn
  linarith [norm_nonneg ((0 : ULift.{v} ℝ) - (φ b - φ a))]

private theorem positive (T : SimpleGraph Root.{w}) :
    0 < cliqueTreeMidpointCoeff T (fun _ => (Set.univ : Set (ULift.{u} (Fin 3)))) := by
  classical
  let K : Root.{w} → Set (ULift.{u} (Fin 3)) := fun _ => Set.univ
  have hcard : (K r).ncard = 3 := by
    simp [K, Set.ncard_univ, Nat.card_eq_fintype_card]
  have hpad : 0 ≤ CliqueTreeBanach.twoShifts T K r := by
    unfold CliqueTreeBanach.twoShifts
    apply Finset.le_max'
    exact Finset.mem_insert_self ..
  have hle : 1 - 2 / ((K r).ncard : ℝ) + CliqueTreeBanach.twoShifts T K r ≤
      cliqueTreeMidpointCoeff T K := by
    unfold cliqueTreeMidpointCoeff
    apply Finset.le_max'
    apply Finset.mem_insert_of_mem
    refine Finset.mem_image.mpr ⟨r, ?_, rfl⟩
    change r ∈ ({a : Root.{w} | 2 ≤ (K a).ncard} : Set Root.{w}).toFinite.toFinset
    simp [K, Set.ncard_univ, Nat.card_eq_fintype_card]
  rw [hcard] at hle
  linarith

def family : Registration arena.{u, v, w}
    (type_of% (@cliqueTree_twoClique_midpoint_banach_potential.{u, v, w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cliqueTree_twoClique_midpoint_banach_potential.{u, v, w}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, ?_, rejected_law⟩
      funext e
      exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨⟨ULift.{u} (Fin 3), Root.{w}, inferInstance, ⊥, fun _ => Set.univ⟩, 0, 1, ?_⟩
    simp only [actual, realize, mul_zero, mul_one]
    exact (positive (⊥ : SimpleGraph Root.{w})).ne

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cliqueTree_twoClique_midpoint_banach_potential.{u, v, w})
    (Realization signature.{u, w}) Unit Unit where
  unitName := `SimpleGraph.cliqueTree_twoClique_midpoint_banach_potential.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.CliqueTreeBanachPotential.Midpoint.family
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
    owner := `D5.S3.Combinatorics.Graph.Chordal.CliqueTreeBanachPotential
    definition := none
    coordinates := #[0, 2, 3, 4, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Midpoint

end

end Reg.D5.S3.Combinatorics.Graph.Chordal.CliqueTreeBanachPotential
