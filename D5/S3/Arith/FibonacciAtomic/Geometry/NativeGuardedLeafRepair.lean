/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeGuardedLeafRepair
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact guarded original-leaf P/S cost frontiers with actual material trees. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.NativeMaterialRootRecognition
import D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open NativeMaterialRootRecognition (D material neighbors children)
open ActualImageAddressCertificate (replace)

abbrev Cell (t : Source) := {p : Address // p ∈ (material t).toFinset}

noncomputable instance cellFintype (t : Source) : Fintype (Cell t) := by
  classical exact Fintype.ofFinite _

def cellGraph (t : Source) : SimpleGraph (Cell t) :=
  SimpleGraph.fromRel (fun x y => y.1 ∈ neighbors t x.1)

abbrev NonrootCell (t : Source) := {p : Address // p ∈ (material t).toFinset.erase []}

noncomputable instance nonrootCellFintype (t : Source) : Fintype (NonrootCell t) := by
  classical exact Fintype.ofFinite _

def nonrootGraph (t : Source) : SimpleGraph (NonrootCell t) :=
  SimpleGraph.fromRel (fun x y => y.1 ∈ neighbors t x.1)

def StateF (t : Source) : Prop := ∃ M : (cellGraph t).Subgraph, M.IsPerfectMatching

def StateR (t : Source) : Prop :=
  ∃ M : (nonrootGraph t).Subgraph, M.IsPerfectMatching

inductive Call where
  | promote (p : Address)
  | split (p : Address)
  deriving DecidableEq

def run : Source → List Call → Option Source
  | t, [] => some t
  | t, .promote p :: w =>
      match subtree p t with
      | some (.of true) => run (replace t p (.of false)) w
      | _ => none
  | t, .split p :: w =>
      match subtree p t with
      | some (.of false) => run (replace t p (.mul (.of false) (.of true))) w
      | _ => none

def promotions : List Call → ℕ
  | [] => 0
  | .promote _ :: w => promotions w + 1
  | .split _ :: w => promotions w

def splits : List Call → ℕ
  | [] => 0
  | .promote _ :: w => splits w
  | .split _ :: w => splits w + 1

structure History (root : Source) where
  final : Source
  calls : List Call
  trace : run root calls = some final
  domain : D final

def pairCost {root : Source} (h : History root) : ℕ × ℕ :=
  (promotions h.calls, splits h.calls)

def reachesF {root : Source} (h : History root) : Prop := StateF h.final
def reachesR {root : Source} (h : History root) : Prop := StateR h.final

def dominates (x y : ℕ × ℕ) : Prop := x.1 ≤ y.1 ∧ x.2 ≤ y.2

def frontier (root : Source) (X : History root → Prop) : Set (ℕ × ℕ) :=
  {c | ∃ h, X h ∧ pairCost h = c ∧ ∀ h', X h' → dominates c (pairCost h')}

private theorem material_nodup' (t : Source) : (material t).Nodup := by
  induction t with
  | of b => cases b <;> simp [material]
  | mul l r il ir =>
    simp only [material, List.nodup_cons, List.mem_append, List.mem_map]
    constructor
    · simp
    · rw [List.nodup_append]
      refine ⟨il.map (fun _ _ he => (List.cons.inj he).2),
        ir.map (fun _ _ he => (List.cons.inj he).2), ?_⟩
      intro x hx y hy he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
      cases he

theorem material_card (t : Source) :
    (material t).toFinset.card = (material t).length := by
  exact List.toFinset_card_of_nodup (material_nodup' t)

private theorem promote_card (t : Source) (p : Address)
    (h : subtree p t = some (.of true)) :
    (material (replace t p (.of false))).toFinset.card =
      (material t).toFinset.card + 1 := by
  rw [material_card, material_card]
  induction p generalizing t with
  | nil =>
      cases t with
      | of b =>
          cases b
          · have hne : (FreeMagma.of false : Source) ≠ .of true := by decide
            have hs : (FreeMagma.of false : Source) = .of true := by simpa [subtree] using h
            exact (hne hs).elim
          · simp [subtree, replace, material]
      | mul l r => cases h
  | cons b p ih =>
      cases t with
      | of c => simp [subtree] at h
      | mul l r =>
          cases b with
          | false =>
              have hp : subtree p l = some (.of true) := by simpa [subtree] using h
              have := ih l hp
              simp [subtree, replace, material] at this ⊢
              omega
          | true =>
              have hp : subtree p r = some (.of true) := by simpa [subtree] using h
              have := ih r hp
              simp [subtree, replace, material] at this ⊢
              omega

private theorem split_card (t : Source) (p : Address)
    (h : subtree p t = some (.of false)) :
    (material (replace t p (.mul (.of false) (.of true)))).toFinset.card =
      (material t).toFinset.card + 2 := by
  rw [material_card, material_card]
  induction p generalizing t with
  | nil =>
      cases t with
      | of b =>
          cases b
          · simp [subtree, replace, material]
          · have hne : (FreeMagma.of true : Source) ≠ .of false := by decide
            have hs : (FreeMagma.of true : Source) = .of false := by simpa [subtree] using h
            exact (hne hs).elim
      | mul l r => cases h
  | cons b p ih =>
      cases t with
      | of c => simp [subtree] at h
      | mul l r =>
          cases b with
          | false =>
              have hp : subtree p l = some (.of false) := by simpa [subtree] using h
              have := ih l hp
              simp [subtree, replace, material] at this ⊢
              omega
          | true =>
              have hp : subtree p r = some (.of false) := by simpa [subtree] using h
              have := ih r hp
              simp [subtree, replace, material] at this ⊢
              omega

private theorem card_run {t : Source} {w : List Call} {u : Source}
    (h : run t w = some u) :
    (material u).toFinset.card = (material t).toFinset.card + promotions w + 2 * splits w := by
  induction w generalizing t with
  | nil =>
      unfold run at h
      cases h
      rfl
  | cons c w ih =>
      cases c with
      | promote p =>
          unfold run at h
          split at h <;> try simp at h
          next hsub =>
            have hr : run (replace t p (.of false)) w = some u := h
            have hc := ih hr
            have hp := promote_card t p hsub
            change _ = _ + (promotions w + 1) + 2 * splits w
            rw [hc, hp]
            omega
      | split p =>
          unfold run at h
          split at h <;> try simp at h
          next hsub =>
            have hr : run (replace t p (.mul (.of false) (.of true))) w = some u := h
            have hc := ih hr
            have hp := split_card t p hsub
            change _ = _ + promotions w + 2 * (splits w + 1)
            rw [hc, hp]
            omega

theorem history_card {root : Source} (h : History root) :
    (material h.final).toFinset.card = (material root).toFinset.card +
      (pairCost h).1 + 2 * (pairCost h).2 := by
  exact card_run h.trace

def preservesMaterial (t u : Source) : Prop :=
  ∀ p : Address, p ∈ material t → p ∈ material u

private theorem promote_material_preserves (t : Source) (p : Address)
    (h : subtree p t = some (.of true)) :
    preservesMaterial t (replace t p (.of false)) := by
  induction p generalizing t with
  | nil =>
      cases t with
      | of b =>
          cases b
          · have hne : (FreeMagma.of false : Source) ≠ .of true := by decide
            have hs : (FreeMagma.of false : Source) = .of true := by simpa [subtree] using h
            exact (hne hs).elim
          · simp [preservesMaterial, replace, material]
      | mul l r => cases h
  | cons b p ih =>
      cases t with
      | of c => simp [subtree] at h
      | mul l r =>
          cases b with
          | false =>
              have hp : subtree p l = some (.of true) := by simpa [subtree] using h
              intro q hq
              have ih' := ih l hp
              simp [material, replace, List.mem_map] at hq ⊢
              aesop
          | true =>
              have hp : subtree p r = some (.of true) := by simpa [subtree] using h
              intro q hq
              have ih' := ih r hp
              simp [material, replace, List.mem_map] at hq ⊢
              aesop

private theorem split_material_preserves (t : Source) (p : Address)
    (h : subtree p t = some (.of false)) :
    preservesMaterial t (replace t p (.mul (.of false) (.of true))) := by
  induction p generalizing t with
  | nil =>
      cases t with
      | of b =>
          cases b
          · simp [preservesMaterial, replace, material]
          · have hne : (FreeMagma.of true : Source) ≠ .of false := by decide
            have hs : (FreeMagma.of true : Source) = .of false := by simpa [subtree] using h
            exact (hne hs).elim
      | mul l r => cases h
  | cons b p ih =>
      cases t with
      | of c => simp [subtree] at h
      | mul l r =>
          cases b with
          | false =>
              have hp : subtree p l = some (.of false) := by simpa [subtree] using h
              intro q hq
              have ih' := ih l hp
              simp [material, replace, List.mem_map] at hq ⊢
              aesop
          | true =>
              have hp : subtree p r = some (.of false) := by simpa [subtree] using h
              intro q hq
              have ih' := ih r hp
              simp [material, replace, List.mem_map] at hq ⊢
              aesop

private theorem run_preserves_material {t u : Source} {w : List Call}
    (h : run t w = some u) : preservesMaterial t u := by
  induction w generalizing t with
  | nil => simp [run, preservesMaterial] at h ⊢; subst u; exact fun _ hp => hp
  | cons c w ih =>
      cases c with
      | promote p =>
          unfold run at h
          split at h <;> try simp at h
          next hsub =>
            intro q hq
            exact (ih h) q (promote_material_preserves t p hsub q hq)
      | split p =>
          unfold run at h
          split at h <;> try simp at h
          next hsub =>
            intro q hq
            exact (ih h) q (split_material_preserves t p hsub q hq)

theorem history_preserves_material {root : Source} (h : History root) :
    preservesMaterial root h.final :=
  run_preserves_material h.trace

abbrev Value := Address → ℚ

def zeroExtend (old current : Source) (x : Value) : Value :=
  fun p => if p ∈ material old then x p else 0

theorem history_preserves_values {root : Source} (h : History root) (x : Value) :
    (∀ p ∈ material root, zeroExtend root h.final x p = x p) ∧
    (∀ p ∈ material h.final, p ∉ material root →
      zeroExtend root h.final x p = 0) := by
  constructor
  · intro p hp
    simp [zeroExtend, hp]
  · intro p hp hnot
    simp [zeroExtend, hnot]

private theorem perfect_even {t : Source} (h : StateF t) :
    Even ((material t).toFinset.card) := by
  obtain ⟨M, hM⟩ := h
  simpa using hM.even_card

private theorem rootless_even {t : Source} (h : StateR t) :
    Even (((material t).toFinset.erase []).card) := by
  obtain ⟨M, hM⟩ := h
  simpa using hM.even_card

private theorem root_mem_finset (t : Source) : [] ∈ (material t).toFinset := by
  induction t with
  | of b => cases b <;> simp [material]
  | mul l r il ir => simp [material]

private theorem rootless_card (t : Source) :
    ((material t).toFinset.erase []).card = (material t).toFinset.card - 1 := by
  rw [Finset.card_erase_of_mem (root_mem_finset t)]

private theorem alpha_material_card :
    (material (.of true : Source)).toFinset.card = 1 := by decide

private theorem beta_material_card :
    (material (.of false : Source)).toFinset.card = 2 := by decide

private theorem leaf_tail_absent (b : Bool) (q : Address) :
    readout (q ++ [false]) (.of b) = .absent := by
  cases q <;> rfl

private theorem D_leaf (b : Bool) : D (.of b) := by
  intro p
  cases p <;> simp [readout]

private theorem D_false_false : D (.mul (.of false) (.of false)) := by
  intro p
  cases p with
  | nil => simp [readout]
  | cons b q =>
      cases b <;> simp [readout, leaf_tail_absent]

private theorem alpha_F_lower {h : History (.of true)} (hs : reachesF h) :
    1 ≤ (pairCost h).1 := by
  have hc := history_card h
  have he := perfect_even hs
  rw [alpha_material_card] at hc
  rcases he with ⟨k, hk⟩
  rw [hc] at hk
  omega

private theorem beta_R_lower {h : History (.of false)} (hs : reachesR h) :
    1 ≤ (pairCost h).1 ∧ 1 ≤ (pairCost h).2 := by
  have hc := history_card h
  have he := rootless_even hs
  have hr := rootless_card h.final
  rw [beta_material_card] at hc
  rw [hr] at he
  rw [hc] at he
  rcases he with ⟨k, hk⟩
  have hp : 1 ≤ (pairCost h).1 := by omega
  have hspl : 1 ≤ (pairCost h).2 := by
    by_contra hn
    have hz : (pairCost h).2 = 0 := by omega
    have hrun : run (.of false) h.calls = some h.final := h.trace
    have hno : h.calls = [] ∧ h.final = (.of false : Source) := by
      cases hc : h.calls with
      | nil =>
          have hrun' : run (.of false) [] = some h.final := by simpa [hc] using hrun
          have hfinal : (.of false : Source) = h.final := by simpa [run] using hrun'
          exact ⟨rfl, hfinal.symm⟩
      | cons c w =>
          cases c with
          | split p =>
              have hz' : splits (.split p :: w) = 0 := by simpa [hc, pairCost] using hz
              simp [splits] at hz'
          | promote p =>
              have hrun' : run (.of false) (.promote p :: w) = some h.final := by
                simpa [hc] using hrun
              cases p <;> simp only [run, subtree] at hrun' <;> cases hrun'
    have hnotR : ¬ StateR (.of false : Source) := by
      intro hr
      have he := rootless_even hr
      have hone : ((material (.of false : Source)).toFinset.erase []).card = 1 := by decide
      rw [hone] at he
      rcases he with ⟨k, hk⟩
      omega
    exact hnotR (hno.2 ▸ hs)
  exact ⟨hp, hspl⟩

def alphaRHistory : History (.of true) :=
  ⟨.of true, [], by simp [run], D_leaf true⟩

def alphaFHistory : History (.of true) :=
  ⟨.of false, [.promote []], by simp [run, subtree, replace], D_leaf false⟩

def betaFHistory : History (.of false) :=
  ⟨.of false, [], by simp [run], D_leaf false⟩

def betaRHistory : History (.of false) :=
  ⟨.mul (.of false) (.of false), [.split [], .promote [true]],
    by simp [run, subtree, replace], D_false_false⟩

private theorem alpha_R_witness : reachesR alphaRHistory := by
  change StateR (.of true)
  letI : IsEmpty (NonrootCell (.of true)) := ⟨fun x => by
    have : x.1 = [] := by simpa [material] using x.2
    simpa [this] using x.2⟩
  refine ⟨⊤, ?_⟩
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  exact isEmptyElim v

private theorem beta_F_witness : reachesF betaFHistory := by
  change StateF (.of false)
  let t : Source := .of false
  change ∃ M : (cellGraph t).Subgraph, M.IsPerfectMatching
  let x : Cell t := ⟨[], by simp [t, material]⟩
  let y : Cell t := ⟨[false], by simp [t, material]⟩
  have hxy : (cellGraph t).Adj x y := by
    simp only [cellGraph, SimpleGraph.fromRel_adj]
    constructor
    · intro h
      have h' : ([] : Address) = [false] := congrArg Subtype.val h
      cases h'
    · simp [x, y, t, neighbors, material, children, readout]
  exact ⟨(cellGraph t).subgraphOfAdj hxy, by
    rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
    intro v
    have hv : v = x ∨ v = y := by
      rcases v with ⟨p, hp⟩
      simp [t, material] at hp
      rcases hp with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hv with rfl | rfl
    · refine ⟨y, SimpleGraph.subgraphOfAdj_adj_self hxy, ?_⟩
      intro z hz
      have hzy : y = z := by simpa [x, y] using hz
      exact hzy.symm
    · refine ⟨x, (SimpleGraph.subgraphOfAdj_adj_self hxy).symm, ?_⟩
      intro z hz
      have hzx : x = z := by simpa [x, y] using hz
      exact hzx.symm
  ⟩

private theorem beta_R_witness : reachesR betaRHistory := by
  change StateR (.mul (.of false) (.of false))
  let t : Source := .mul (.of false) (.of false)
  change ∃ M : (nonrootGraph t).Subgraph, M.IsPerfectMatching
  let x : NonrootCell t := ⟨[false], by simp [t, material]⟩
  let y : NonrootCell t := ⟨[false, false], by simp [t, material]⟩
  let z : NonrootCell t := ⟨[true], by simp [t, material]⟩
  let w : NonrootCell t := ⟨[true, false], by simp [t, material]⟩
  let g := nonrootGraph t
  have hxy : g.Adj x y := by
    simp only [g, nonrootGraph, SimpleGraph.fromRel_adj]
    constructor
    · intro h
      have h' : ([false] : Address) = [false, false] := congrArg Subtype.val h
      cases h'
    · simp [x, y, t, neighbors, children, readout]
  have hzw : g.Adj z w := by
    simp only [g, nonrootGraph, SimpleGraph.fromRel_adj]
    constructor
    · intro h
      have h' : ([true] : Address) = [true, false] := congrArg Subtype.val h
      cases h'
    · simp [z, w, t, neighbors, children, readout]
  let M := (g.subgraphOfAdj hxy) ⊔ (g.subgraphOfAdj hzw)
  refine ⟨M, ?_⟩
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  have hv : v = x ∨ v = y ∨ v = z ∨ v = w := by
    rcases v with ⟨p, hp⟩
    simp [t, material] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse <;>
      try contradiction
    all_goals simp [x, y, z, w]
  rcases hv with rfl | rfl | rfl | rfl
  · refine ⟨y, ?_, ?_⟩
    · simp [M, SimpleGraph.Subgraph.sup_adj, x, y, z, w, hxy, hzw]
    · intro q hq
      have hyq : y = q := by
        simpa [M, SimpleGraph.Subgraph.sup_adj, x, y, z, w, hxy, hzw] using hq
      exact hyq.symm
  · refine ⟨x, ?_, ?_⟩
    · simp [M, SimpleGraph.Subgraph.sup_adj, x, y, z, w, hxy, hzw]
    · intro q hq
      have hxq : x = q := by
        simpa [M, SimpleGraph.Subgraph.sup_adj, x, y, z, w, hxy, hzw] using hq
      exact hxq.symm
  · refine ⟨w, ?_, ?_⟩
    · simp [M, SimpleGraph.Subgraph.sup_adj, x, y, z, w, hxy, hzw]
    · intro q hq
      have hwq : w = q := by
        simpa [M, SimpleGraph.Subgraph.sup_adj, x, y, z, w, hxy, hzw] using hq
      exact hwq.symm
  · refine ⟨z, ?_, ?_⟩
    · simp [M, SimpleGraph.Subgraph.sup_adj, x, y, z, w, hxy, hzw]
    · intro q hq
      have hzq : z = q := by
        simpa [M, SimpleGraph.Subgraph.sup_adj, x, y, z, w, hxy, hzw] using hq
      exact hzq.symm

theorem exact_frontiers :
    frontier (.of true) reachesF = {(1, 0)} ∧
    frontier (.of true) reachesR = {(0, 0)} ∧
    frontier (.of false) reachesF = {(0, 0)} ∧
    frontier (.of false) reachesR = {(1, 1)} := by
  have hαR := alpha_R_witness
  have hαF : reachesF alphaFHistory := by
    have := beta_F_witness
    exact this
  have hβF := beta_F_witness
  have hβR := beta_R_witness
  constructor
  · ext c
    constructor
    · rintro ⟨h, hs, rfl, hmin⟩
      have hle := hmin alphaFHistory hαF
      have hlo := alpha_F_lower hs
      have hcost : pairCost alphaFHistory = (1, 0) := rfl
      rw [hcost] at hle
      change (pairCost h).1 ≤ 1 ∧ (pairCost h).2 ≤ 0 at hle
      have hp : (pairCost h).1 = 1 := by omega
      have hs0 : (pairCost h).2 = 0 := by omega
      exact Prod.ext hp hs0
    · intro hc
      subst c
      refine ⟨alphaFHistory, hαF, rfl, ?_⟩
      intro h hs
      exact ⟨alpha_F_lower hs, Nat.zero_le _⟩
  · constructor
    · ext c
      constructor
      · rintro ⟨h, hs, rfl, hmin⟩
        have hle := hmin alphaRHistory hαR
        have hcost : pairCost alphaRHistory = (0, 0) := rfl
        rw [hcost] at hle
        change (pairCost h).1 ≤ 0 ∧ (pairCost h).2 ≤ 0 at hle
        have hp : (pairCost h).1 = 0 := by omega
        have hs0 : (pairCost h).2 = 0 := by omega
        exact Prod.ext hp hs0
      · intro hc
        subst c
        refine ⟨alphaRHistory, hαR, rfl, ?_⟩
        intro h hs
        exact ⟨Nat.zero_le _, Nat.zero_le _⟩
    · constructor
      · ext c
        constructor
        · rintro ⟨h, hs, rfl, hmin⟩
          have hle := hmin betaFHistory hβF
          have hcost : pairCost betaFHistory = (0, 0) := rfl
          rw [hcost] at hle
          change (pairCost h).1 ≤ 0 ∧ (pairCost h).2 ≤ 0 at hle
          have hp : (pairCost h).1 = 0 := by omega
          have hs0 : (pairCost h).2 = 0 := by omega
          exact Prod.ext hp hs0
        · intro hc
          subst c
          refine ⟨betaFHistory, hβF, rfl, ?_⟩
          intro h hs
          exact ⟨Nat.zero_le _, Nat.zero_le _⟩
      · ext c
        constructor
        · rintro ⟨h, hs, rfl, hmin⟩
          have hle := hmin betaRHistory hβR
          have hlo := beta_R_lower hs
          have hcost : pairCost betaRHistory = (1, 1) := rfl
          rw [hcost] at hle
          change (pairCost h).1 ≤ 1 ∧ (pairCost h).2 ≤ 1 at hle
          have hp : (pairCost h).1 = 1 := by omega
          have hs1 : (pairCost h).2 = 1 := by omega
          exact Prod.ext hp hs1
        · intro hc
          subst c
          refine ⟨betaRHistory, hβR, rfl, ?_⟩
          intro h hs
          have hlo := beta_R_lower hs
          exact hlo

theorem result :
    (∀ h : History (.of true), reachesF h → 1 ≤ (pairCost h).1) ∧
    (∀ h : History (.of false), reachesR h →
      1 ≤ (pairCost h).1 ∧ 1 ≤ (pairCost h).2) ∧
    (frontier (.of true) reachesF = {(1, 0)} ∧
      frontier (.of true) reachesR = {(0, 0)} ∧
      frontier (.of false) reachesF = {(0, 0)} ∧
      frontier (.of false) reachesR = {(1, 1)}) := by
  exact ⟨fun h hs => alpha_F_lower hs, fun h hs => beta_R_lower hs, exact_frontiers⟩

end D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair

#print axioms D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair.result
