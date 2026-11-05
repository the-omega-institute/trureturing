/- GID: D5/S0/Automata/TwoStateShortWordSampleBound
   generality: G
   mirror-B: D5/B/S0/Automata/TwoStateShortWordSampleBound
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Two-state Boolean output automata on words of length at most two have an alphabet-linear finite-sample bound. -/

import D5.S0.Automata.FiniteSampleRestriction
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S0.Automata.TwoStateShortWordSampleBound
open D5.S0.Automata.DFAOStateLowerBound
open D5.S0.Automata.FiniteSampleRestriction

def normalized {A : Type} (e : Bool) (x y : A → Bool) : DFAO A Bool Bool :=
  { start := e
    step := fun q a => if q = e then x a else y a
    output := id
    accept := ∅ }

private theorem eval_nil {A : Type} (e : Bool) (x y : A → Bool) :
    (normalized e x y).evalOutput [] = e := rfl

private theorem eval_single {A : Type} (e : Bool) (x y : A → Bool) (a : A) :
    (normalized e x y).evalOutput [a] = x a := by
  simp [DFAO.evalOutput, normalized, DFA.eval, DFA.evalFrom]

private theorem eval_pair {A : Type} (e : Bool) (x y : A → Bool) (a b : A) :
    (normalized e x y).evalOutput [a,b] =
      (if x a = e then x b else y b) := by
  simp [DFAO.evalOutput, normalized, DFA.eval, DFA.evalFrom]


private theorem normalize_injective {A S : Type}
    (M : DFAO A Bool S) (hi : Function.Injective M.output) :
    ∃ e : Bool, ∃ x y : A → Bool,
      ∀ w, (normalized e x y).evalOutput w = M.evalOutput w := by
  classical
  letI : Nonempty S := ⟨M.start⟩
  let r : Bool → S := Function.invFun M.output
  have hr : ∀ q, r (M.output q) = q := Function.leftInverse_invFun hi
  let e := M.output M.start
  let x : A → Bool := fun a => M.output (M.step M.start a)
  let y : A → Bool := fun a => M.output (M.step (r (!e)) a)
  have st : ∀ q a, (normalized e x y).step (M.output q) a = M.output (M.step q a) := by
    intro q a
    by_cases h : M.output q = e
    · have he : q = M.start := hi h
      subst q
      simp [normalized, e, x]
    · have he : M.output q = !e := by
        cases hq : M.output q <;> cases he : e <;> simp_all
      have hn : r (!e) = q := by rw [← he, hr]
      simp [normalized, h, y, hn]
  refine ⟨e, x, y, ?_⟩
  have run : ∀ w q, (normalized e x y).toDFA.evalFrom (M.output q) w =
      M.output (M.toDFA.evalFrom q w) := by
    intro w
    induction w with
    | nil => intro q; rfl
    | cons a tail ih =>
      intro q
      simp only [DFA.evalFrom_cons]
      rw [show (normalized e x y).toDFA.step (M.output q) a = M.output (M.step q a) from st q a]
      exact ih _
  intro w
  exact run w M.start

theorem normalize_two_states {A S : Type} [Fintype S]
    (M : DFAO A Bool S) (hc : Fintype.card S ≤ 2) :
    ∃ e : Bool, ∃ x y : A → Bool,
      ∀ w, (normalized e x y).evalOutput w = M.evalOutput w := by
  classical
  by_cases hconst : ∀ q, M.output q = M.output M.start
  · let e := M.output M.start
    refine ⟨e, (fun _ => e), (fun _ => e), ?_⟩
    have run : ∀ (w : List A) (q : Bool), (normalized e (fun _ : A => e) (fun _ : A => e)).toDFA.evalFrom q w =
        (if w = [] then q else e) := by
      intro w
      induction w with
      | nil => intro q; simp [DFA.evalFrom]
      | cons a tail ih =>
        intro q
        simp only [DFA.evalFrom_cons]
        change (normalized e (fun _ : A => e) (fun _ : A => e)).toDFA.evalFrom
          (if q = e then e else e) tail = _
        simp only [ite_self]
        rw [ih]
        simp
    intro w
    change (normalized e (fun _ => e) (fun _ => e)).toDFA.evalFrom e w = _
    rw [run]
    simp only [ite_self]
    exact (hconst _).symm
  · have hs : Function.Surjective M.output := by
      push Not at hconst
      obtain ⟨q, hq⟩ := hconst
      intro b
      by_cases hb : b = M.output M.start
      · exact ⟨M.start, hb.symm⟩
      · refine ⟨q, ?_⟩
        cases hp : M.output q <;> cases he : M.output M.start <;> cases b <;> simp_all
    have he : Fintype.card S = Fintype.card Bool := by
      have hl := Fintype.card_le_of_surjective _ hs
      simp only [Fintype.card_bool] at hl ⊢
      omega
    exact normalize_injective M ((Fintype.bijective_iff_surjective_and_card M.output).mpr ⟨hs, he⟩).1


open Relation

private def Edge {I V : Type} (r : I → V → V → Prop) (E : Finset I) (a b : V) : Prop :=
  ∃ i ∈ E, r i a b

private theorem sparse_reach {I V : Type} [Fintype V] (r : I → V → V → Prop) (a : V) :
    ∃ E : Finset I, E.card ≤ Fintype.card V ∧
      ∀ b, ReflTransGen (fun p q => ∃ i, r i p q) a b → ReflTransGen (Edge r E) a b := by
  classical
  have grow : ∀ n : ℕ, ∀ (T : Finset V) (E : Finset I),
      Fintype.card V - T.card = n → a ∈ T →
      (∀ b ∈ T, ReflTransGen (Edge r E) a b) →
      ∃ F : Finset I, F.card ≤ E.card + n ∧
        ∀ b, ReflTransGen (fun p q => ∃ i, r i p q) a b → ReflTransGen (Edge r F) a b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T E hn ha ht
      by_cases closed : ∀ p ∈ T, ∀ q, (∃ i, r i p q) → q ∈ T
      · refine ⟨E, by omega, ?_⟩
        intro b hb
        have mem : b ∈ T := by
          induction hb with
          | refl => exact ha
          | @tail b c path edge ih => exact closed b ih c edge
        exact ht b mem
      · push Not at closed
        obtain ⟨p,hp,q,⟨i,hi⟩,hq⟩ := closed
        let T' := insert q T
        let E' := insert i E
        have htcard : T'.card = T.card + 1 := Finset.card_insert_of_notMem hq
        have hle : T'.card ≤ Fintype.card V := Finset.card_le_univ _
        have less : Fintype.card V - T'.card < n := by omega
        have mono : ∀ {u v}, ReflTransGen (Edge r E) u v → ReflTransGen (Edge r E') u v := by
          apply ReflTransGen.mono
          rintro u v ⟨j,hj,hij⟩
          exact ⟨j,Finset.mem_insert_of_mem hj,hij⟩
        have ht' : ∀ b ∈ T', ReflTransGen (Edge r E') a b := by
          intro b hb
          rcases Finset.mem_insert.mp hb with rfl | hb
          · exact (mono (ht p hp)).tail ⟨i,Finset.mem_insert_self _ _,hi⟩
          · exact mono (ht b hb)
        obtain ⟨F,hF,hreach⟩ := ih _ less T' E' rfl (Finset.mem_insert_of_mem ha) ht'
        refine ⟨F,?_,hreach⟩
        have hecard : E'.card ≤ E.card + 1 := Finset.card_insert_le _ _
        omega
  obtain ⟨E,hE,hreach⟩ := grow (Fintype.card V - 1) {a} ∅ (by simp) (by simp)
    (by intro b hb; have he := Finset.mem_singleton.mp hb; subst b; exact ReflTransGen.refl)
  simp only [Finset.card_empty, zero_add] at hE
  exact ⟨E,le_trans hE (Nat.sub_le _ _),hreach⟩

/-
Faithful source port of the consumed 2-SAT supplier from
https://github.com/GregoryMorse/smcdynirredloops/tree/c06bdd83c782594d7f0bb3ad0d5b6c15e47c8134/lean/SmcIrred
(Spec/Graph, Spec/TwoSat, Graph/DfsInv, TwoSat/Reach, TwoSat/Implication,
TwoSat/APT). Names are private; executable reachability decision is replaced
by classical decision. The propositions and retained proof bodies are preserved, with a redundant
terminal tactic omitted where the current rewrite closes its goal.
Retire this fragment when the repository's pinned Mathlib supplies an equivalent
finite well-formed nonempty-clause twoSat_iff_scc interface: compile the finite
encoding below against that interface, then replace the port by its import.

MIT License

Copyright (c) 2026 Gregory Morse

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

namespace Supplier
noncomputable section

private structure Digraph where
  n : Nat
  succ : Nat → List Nat

/-- `a → b` is an edge: both ends are vertices and `b` is listed among the successors of `a`. -/
private def Digraph.edge (g : Digraph) (a b : Nat) : Prop := a < g.n ∧ b < g.n ∧ b ∈ g.succ a

/-- Reachability along edges (reflexive-transitive closure). -/
private inductive Digraph.Reach (g : Digraph) : Nat → Nat → Prop
  | refl (a : Nat) : Digraph.Reach g a a
  | step {a b c : Nat} : g.edge a b → Digraph.Reach g b c → Digraph.Reach g a c



private def Digraph.SameSCC (g : Digraph) (a b : Nat) : Prop := g.Reach a b ∧ g.Reach b a



private structure Lit where
  var : Nat
  pos : Bool
  deriving DecidableEq

private def Lit.neg (l : Lit) : Lit := ⟨l.var, !l.pos⟩

/-- The vertex of the implication graph of a literal: `2x` for `x`, `2x + 1` for `¬x`. -/
private def Lit.node (l : Lit) : Nat := 2 * l.var + (if l.pos then 0 else 1)

/-- The literal of a vertex of the implication graph. -/
private def Lit.ofNode (u : Nat) : Lit := ⟨u / 2, decide (u % 2 = 0)⟩

/-- A 2-SAT formula: `n` variables and `m` clauses of at most two literals each (`Wf`); the empty clause is allowed and
is unsatisfiable. -/
private structure TwoSat where
  n : Nat
  clauses : List (List Lit)

private def TwoSat.Wf (f : TwoSat) : Prop := ∀ c ∈ f.clauses, c.length ≤ 2 ∧ ∀ l ∈ c, l.var < f.n

/-- The literal is true under the assignment `a`. -/
private def Lit.Holds (a : Nat → Bool) (l : Lit) : Prop := a l.var = l.pos

/-- A clause is satisfied when one of its literals holds (the empty clause is never satisfied). -/
private def ClauseSat (a : Nat → Bool) (c : List Lit) : Prop := ∃ l ∈ c, l.Holds a

private def TwoSat.Sat (f : TwoSat) (a : Nat → Bool) : Prop := ∀ c ∈ f.clauses, ClauseSat a c

/-- The implications of a clause: `(p ∨ q)` gives `¬p → q` and `¬q → p`; a unit clause `(p)` gives `¬p → p`; the empty
clause gives none. -/
private def clauseImps : List Lit → List (Lit × Lit)
  | [a, b] => [(a.neg, b), (b.neg, a)]
  | [a] => [(a.neg, a)]
  | _ => []

private def TwoSat.imps (f : TwoSat) : List (Lit × Lit) := f.clauses.flatMap clauseImps

/-- The implication graph on the `2n` literal vertices (successor order: clause order). -/
private def TwoSat.graph (f : TwoSat) : Digraph where
  n := 2 * f.n
  succ u := (f.imps.filter fun e => e.1.node == u).map fun e => e.2.node



private theorem filter_len_le {p q : Nat → Bool} (h : ∀ x, p x = true → q x = true) (l : List Nat) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq] <;> first | omega | (have := h a hp; simp_all)

private theorem filter_len_lt {p q : Nat → Bool} (h : ∀ x, p x = true → q x = true) {v : Nat} {l : List Nat} (hv : v ∈ l)
    (hp : p v = false) (hq : q v = true) : (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => simp at hv
  | cons a l ih =>
    by_cases hav : a = v
    · subst hav
      have := filter_len_le h l
      simp [hp, hq]; omega
    · have hmem : v ∈ l := by simpa [Ne.symm hav] using hv
      have := ih hmem
      cases hpa : p a <;> cases hqa : q a <;> simp [hpa, hqa] <;> first | omega | (have := h a hpa; simp_all)



variable {g : Digraph}

private theorem Digraph.Reach.trans {a b c : Nat} (h1 : g.Reach a b) (h2 : g.Reach b c) : g.Reach a c := by
  induction h1 with
  | refl _ => exact h2
  | step he _ ih => exact .step he (ih h2)

private theorem Digraph.SameSCC.refl (a : Nat) : g.SameSCC a a := ⟨.refl a, .refl a⟩

private theorem Digraph.SameSCC.symm {a b : Nat} (h : g.SameSCC a b) : g.SameSCC b a := ⟨h.2, h.1⟩

private theorem Digraph.SameSCC.trans {a b c : Nat} (h1 : g.SameSCC a b) (h2 : g.SameSCC b c) : g.SameSCC a c :=
  ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩



local instance (g : Digraph) (a b : Nat) : Decidable (g.Reach a b) := Classical.propDecidable _

local instance (g : Digraph) (a b : Nat) : Decidable (g.SameSCC a b) := Classical.propDecidable _



/-- The least vertex of the strongly connected component of `u`. -/
private def sccRep (g : Digraph) (u : Nat) : Nat := ((List.range g.n).find? fun w => decide (g.SameSCC u w)).getD u

/-- A reverse-topological SCC label: the size of the reachable set, then the component representative. -/
private def sccLabel (g : Digraph) (u : Nat) : Nat :=
  ((List.range g.n).filter fun w => decide (g.Reach u w)).length * (g.n + 1) + sccRep g u

private theorem sccRep_spec {u : Nat} (hu : u < g.n) : sccRep g u < g.n ∧ g.SameSCC u (sccRep g u) := by
  unfold sccRep
  have : ((List.range g.n).find? fun w => decide (g.SameSCC u w)).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨u, List.mem_range.2 hu, by simpa using Digraph.SameSCC.refl u⟩
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 this
  rw [hw]
  have h1 := List.find?_some hw
  have h2 := List.mem_of_find?_eq_some hw
  exact ⟨List.mem_range.1 h2, by simpa using h1⟩

private theorem sccRep_congr {u w : Nat} (hu : u < g.n) (h : g.SameSCC u w) : sccRep g u = sccRep g w := by
  unfold sccRep
  have e : (fun x => decide (g.SameSCC u x)) = fun x => decide (g.SameSCC w x) := by
    funext x
    simp only [decide_eq_decide]
    exact ⟨fun h2 => h.symm.trans h2, fun h2 => h.trans h2⟩
  rw [e]
  have : ((List.range g.n).find? fun x => decide (g.SameSCC w x)).isSome = true := by
    rw [List.find?_isSome]
    refine ⟨u, List.mem_range.2 hu, ?_⟩
    simpa using h.symm
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 this
  rw [hx]; rfl

/-- A reverse-topological SCC labelling exists for every finite digraph: labels are equal exactly inside a strongly
connected component and never increase along an edge. -/
private theorem sccLabel_spec : (∀ u w, u < g.n → w < g.n → sccLabel g u = sccLabel g w → g.SameSCC u w) ∧
    ∀ u w, g.edge u w → sccLabel g w ≤ sccLabel g u := by
  constructor
  · intro u w hu hw h
    unfold sccLabel at h
    obtain ⟨hr1, hs1⟩ := sccRep_spec hu
    obtain ⟨hr2, hs2⟩ := sccRep_spec hw
    have hm : sccRep g u = sccRep g w := by
      have := congrArg (· % (g.n + 1)) h
      simp only [Nat.add_comm _ (sccRep g _), Nat.add_mul_mod_self_right] at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact hs1.trans (hm ▸ hs2.symm)
  · intro u w he
    have hu := he.1
    have hw := he.2.1
    by_cases hs : g.SameSCC u w
    · have hrep := sccRep_congr hu hs
      have hset : ((List.range g.n).filter fun x => decide (g.Reach w x)) =
          (List.range g.n).filter fun x => decide (g.Reach u x) := by
        apply List.filter_congr; intro x _
        simp only [decide_eq_decide]
        exact ⟨fun h => hs.1.trans h, fun h => hs.2.trans h⟩
      unfold sccLabel
      rw [hset, hrep]
    · have hnr : ¬ g.Reach w u := fun h => hs ⟨.step he (.refl _), h⟩
      have hlt : ((List.range g.n).filter fun x => decide (g.Reach w x)).length <
          ((List.range g.n).filter fun x => decide (g.Reach u x)).length := by
        refine filter_len_lt (v := u) ?_ (List.mem_range.2 hu) (by simpa using hnr) (by simpa using Digraph.Reach.refl (g := g) u)
        intro x hx
        simp only [decide_eq_true_eq] at hx ⊢
        exact (Digraph.Reach.step he (.refl _)).trans hx
      unfold sccLabel
      have hr := (sccRep_spec hw).1
      have := Nat.mul_le_mul_right (g.n + 1) hlt
      rw [Nat.succ_mul] at this
      omega



private theorem Lit.neg_neg (l : Lit) : l.neg.neg = l := by cases l; simp [Lit.neg]

private theorem Lit.holds_neg (a : Nat → Bool) (l : Lit) : l.neg.Holds a ↔ ¬ l.Holds a := by
  unfold Lit.Holds Lit.neg; simp only; cases a l.var <;> cases l.pos <;> simp

private theorem Lit.ofNode_node (l : Lit) : Lit.ofNode l.node = l := by
  cases l with
  | mk v p => cases p <;> simp [Lit.node, Lit.ofNode] <;> omega



private theorem Lit.node_inj {a b : Lit} (h : a.node = b.node) : a = b := by
  have := congrArg Lit.ofNode h
  rwa [Lit.ofNode_node, Lit.ofNode_node] at this

private theorem Lit.node_lt {n : Nat} {l : Lit} (h : l.var < n) : l.node < 2 * n := by
  unfold Lit.node; split <;> omega



/-- C24: `(p ∨ q)` is equivalent to `(¬p → q) ∧ (¬q → p)`. -/
private theorem or_iff_implications (p q : Prop) : (p ∨ q) ↔ ((¬ p → q) ∧ (¬ q → p)) := by
  constructor
  · rintro (hp | hq)
    · exact ⟨fun hn => absurd hp hn, fun _ => hp⟩
    · exact ⟨fun _ => hq, fun hn => absurd hq hn⟩
  · rintro ⟨h1, h2⟩
    exact Classical.byCases (fun hp : p => Or.inl hp) (fun hp => Or.inr (h1 hp))

/-- A clause of at most two literals is satisfied iff it is not empty and every implication it yields is respected. -/
private theorem clauseSat_iff {a : Nat → Bool} {c : List Lit} (hc : c.length ≤ 2) :
    ClauseSat a c ↔ c ≠ [] ∧ ∀ e ∈ clauseImps c, e.1.Holds a → e.2.Holds a := by
  match c, hc with
  | [], _ => simp [ClauseSat, clauseImps]
  | [p], _ =>
    simp only [ClauseSat, clauseImps, List.mem_singleton, forall_eq, ne_eq, List.cons_ne_nil, not_false_eq_true,
      true_and, List.mem_cons, exists_eq_or_imp, List.not_mem_nil, or_false, exists_eq_left]
    rw [Lit.holds_neg]
    exact ⟨fun h _ => h, fun h => Classical.byContradiction fun hn => hn (h hn)⟩
  | [p, q], _ =>
    simp only [ClauseSat, clauseImps, List.mem_cons, List.not_mem_nil, or_false, ne_eq, reduceCtorEq, not_false_eq_true,
      true_and, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left]
    rw [Lit.holds_neg, Lit.holds_neg]
    constructor
    · intro h; exact ⟨fun hn => (or_iff_implications _ _).1 h |>.1 hn, fun hn => (or_iff_implications _ _).1 h |>.2 hn⟩
    · intro h; exact (or_iff_implications _ _).2 h
  | _ :: _ :: _ :: _, h => exact absurd h (by simp)

/-- C24/C22: an assignment satisfies the formula iff no clause is empty and the assignment is closed under the
implications of the implication graph (no edge from a true to a false literal). -/
private theorem sat_iff_closed {f : TwoSat} (hw : f.Wf) {a : Nat → Bool} :
    f.Sat a ↔ (∀ c ∈ f.clauses, c ≠ []) ∧ ∀ e ∈ f.imps, e.1.Holds a → e.2.Holds a := by
  constructor
  · intro h
    refine ⟨fun c hc => ((clauseSat_iff (hw c hc).1).1 (h c hc)).1, fun e he => ?_⟩
    obtain ⟨c, hc, hec⟩ := List.mem_flatMap.1 he
    exact ((clauseSat_iff (hw c hc).1).1 (h c hc)).2 e hec
  · rintro ⟨hne, hcl⟩ c hc
    exact (clauseSat_iff (hw c hc).1).2 ⟨hne c hc, fun e he => hcl e (List.mem_flatMap.2 ⟨c, hc, he⟩)⟩

private theorem graph_edge_iff (f : TwoSat) (u w : Nat) :
    f.graph.edge u w ↔ u < 2 * f.n ∧ w < 2 * f.n ∧ ∃ e ∈ f.imps, e.1.node = u ∧ e.2.node = w := by
  unfold Digraph.edge
  simp only [TwoSat.graph, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2, e, ⟨he, hu⟩, hw⟩
    exact ⟨h1, h2, e, he, hu, hw⟩
  · rintro ⟨h1, h2, e, he, hu, hw⟩
    exact ⟨h1, h2, e, ⟨he, hu⟩, hw⟩

/-- The implications come in contrapositive pairs: `p → q` and `¬q → ¬p`. -/
private theorem imps_skew {f : TwoSat} {e : Lit × Lit} (he : e ∈ f.imps) : (e.2.neg, e.1.neg) ∈ f.imps := by
  obtain ⟨c, hc, hec⟩ := List.mem_flatMap.1 he
  refine List.mem_flatMap.2 ⟨c, hc, ?_⟩
  match c, hec with
  | [], h => simp [clauseImps] at h
  | [p], h =>
    simp only [clauseImps, List.mem_singleton] at h ⊢
    subst h; simp [Lit.neg_neg]
  | [p, q], h =>
    simp only [clauseImps, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with rfl | rfl <;> simp [Lit.neg_neg]
  | _ :: _ :: _ :: _, h => simp [clauseImps] at h

/-- An assignment closed under the implications is monotone along paths of the implication graph. -/
private theorem closed_reach {f : TwoSat} {a : Nat → Bool} (hcl : ∀ e ∈ f.imps, e.1.Holds a → e.2.Holds a) {u w : Nat}
    (h : f.graph.Reach u w) : (Lit.ofNode u).Holds a → (Lit.ofNode w).Holds a := by
  induction h with
  | refl _ => exact id
  | @step x y z he _ ih =>
    intro hu
    obtain ⟨-, -, e, hmem, hn1, hn2⟩ := (graph_edge_iff f _ _).1 he
    have e1 : e.1 = Lit.ofNode x := by rw [← hn1, Lit.ofNode_node]
    have e2 : e.2 = Lit.ofNode y := by rw [← hn2, Lit.ofNode_node]
    apply ih
    have := hcl e hmem
    rw [e1, e2] at this
    exact this hu



variable {f : TwoSat}

private theorem imps_var_lt (hw : f.Wf) {e : Lit × Lit} (he : e ∈ f.imps) : e.1.var < f.n ∧ e.2.var < f.n := by
  obtain ⟨c, hc, hec⟩ := List.mem_flatMap.1 he
  have hv := (hw c hc).2
  match c, hec with
  | [], h => simp [clauseImps] at h
  | [p], h =>
    simp only [clauseImps, List.mem_singleton] at h
    subst h
    have := hv p (by simp)
    exact ⟨this, this⟩
  | [p, q], h =>
    simp only [clauseImps, List.mem_cons, List.not_mem_nil, or_false] at h
    have h1 := hv p (by simp)
    have h2 := hv q (by simp)
    rcases h with rfl | rfl <;> exact ⟨by assumption, by assumption⟩
  | _ :: _ :: _ :: _, h => simp [clauseImps] at h

/-- The Aspvall–Plass–Tarjan assignment: `x` is true iff `label(x) < label(¬x)`. -/
private def aptAssign (lab : Nat → Nat) (x : Nat) : Bool :=
  decide (lab (Lit.node ⟨x, true⟩) < lab (Lit.node ⟨x, false⟩))

private theorem apt_holds {n : Nat} {lab : Nat → Nat} (hd : ∀ x, x < n → lab (Lit.node ⟨x, true⟩) ≠ lab (Lit.node ⟨x, false⟩))
    {l : Lit} (hl : l.var < n) : l.Holds (aptAssign lab) ↔ lab l.node < lab l.neg.node := by
  cases l with
  | mk x p =>
    cases p
    · have := hd x hl
      simp [Lit.Holds, aptAssign, Lit.neg]
      omega
    · simp [Lit.Holds, aptAssign, Lit.neg]

/-- C21 (APT): if the labels of the literals are in reverse topological order (never increase along an implication) and
no variable has the same label as its negation, then "x true iff label(x) < label(¬x)" satisfies the formula. -/
private theorem apt_sat (hw : f.Wf) (hne : ∀ c ∈ f.clauses, c ≠ []) {lab : Nat → Nat}
    (hmono : ∀ e ∈ f.imps, lab e.2.node ≤ lab e.1.node)
    (hd : ∀ x, x < f.n → lab (Lit.node ⟨x, true⟩) ≠ lab (Lit.node ⟨x, false⟩)) : f.Sat (aptAssign lab) := by
  refine (sat_iff_closed hw).2 ⟨hne, fun e he hp => ?_⟩
  obtain ⟨h1, h2⟩ := imps_var_lt hw he
  have hs := imps_skew he
  have m1 := hmono e he
  have m2 : lab e.1.neg.node ≤ lab e.2.neg.node := hmono _ hs
  rw [apt_holds hd h1] at hp
  rw [apt_holds hd h2]
  omega



/-- A variable in the same strongly connected component as its negation makes the formula unsatisfiable. -/
private theorem unsat_of_sameSCC (hw : f.Wf) (hne : ∀ c ∈ f.clauses, c ≠ []) {x : Nat}
    (h : f.graph.SameSCC (Lit.node ⟨x, true⟩) (Lit.node ⟨x, false⟩)) (a : Nat → Bool) : ¬ f.Sat a := by
  intro hs
  have hcl := ((sat_iff_closed hw).1 hs).2
  have h1 := closed_reach hcl h.1
  have h2 := closed_reach hcl h.2
  rw [Lit.ofNode_node, Lit.ofNode_node] at h1 h2
  unfold Lit.Holds at h1 h2
  by_cases hax : a x = true
  · have := h1 hax; simp_all
  · have hf : a x = false := by simpa using hax
    have := h2 hf; simp_all

/-- Aspvall–Plass–Tarjan (C21): a 2-SAT formula without empty clause is satisfiable iff no variable lies in the same
strongly connected component of the implication graph as its negation. -/
private theorem twoSat_iff_scc (hw : f.Wf) (hne : ∀ c ∈ f.clauses, c ≠ []) :
    (∃ a, f.Sat a) ↔ ∀ x, x < f.n → ¬ f.graph.SameSCC (Lit.node ⟨x, true⟩) (Lit.node ⟨x, false⟩) := by
  constructor
  · rintro ⟨a, ha⟩ x _ h
    exact unsat_of_sameSCC hw hne h a ha
  · intro hx
    refine ⟨aptAssign (sccLabel f.graph), apt_sat hw hne (fun e he => ?_) (fun x hxn hh => hx x hxn ?_)⟩
    · obtain ⟨h1, h2⟩ := imps_var_lt hw he
      have hedge : f.graph.edge e.1.node e.2.node :=
        (graph_edge_iff f _ _).2 ⟨Lit.node_lt h1, Lit.node_lt h2, e, he, rfl, rfl⟩
      exact sccLabel_spec.2 _ _ hedge
    · exact sccLabel_spec.1 _ _ (Lit.node_lt (l := ⟨x, true⟩) hxn) (Lit.node_lt (l := ⟨x, false⟩) hxn) hh


end
end Supplier

private def neg {V : Type} (l : V × Bool) : V × Bool := (l.1,!l.2)

private def Holds {V : Type} (v : V → Bool) (l : V × Bool) : Prop := v l.1 = l.2

private theorem neg_neg {V : Type} (l : V × Bool) : neg (neg l) = l := by
  rcases l with ⟨p,b⟩; cases b <;> rfl

private theorem holds_neg {V : Type} (v : V → Bool) (l : V × Bool) : Holds v (neg l) ↔ ¬ Holds v l := by
  rcases l with ⟨p,b⟩; cases h : v p <;> cases b <;> simp [Holds,neg,h]

private theorem implication_assignment {V : Type} [Fintype V]
    (r : (V × Bool) → (V × Bool) → Prop)
    (skew : ∀ l m, r l m → r (neg m) (neg l))
    (consistent : ∀ l, ¬ (ReflTransGen r l (neg l) ∧ ReflTransGen r (neg l) l)) :
    ∃ v : V → Bool, ∀ l m, r l m → Holds v l → Holds v m := by
  classical
  let enc : V × Bool → Supplier.Lit := fun l => ⟨(Fintype.equivFin V l.1).val, l.2⟩
  have enc_inj : Function.Injective enc := by
    rintro ⟨v,b⟩ ⟨w,c⟩ h
    have hv : (Fintype.equivFin V v).val = (Fintype.equivFin V w).val := congrArg Supplier.Lit.var h
    have hb : b = c := congrArg Supplier.Lit.pos h
    have he : v = w := (Fintype.equivFin V).injective (Fin.ext hv)
    exact Prod.ext he hb
  have enc_neg : ∀ l, enc (neg l) = (enc l).neg := by intro l; rfl
  let edges : Finset ((V × Bool) × (V × Bool)) := Finset.univ.filter fun e => r e.1 e.2
  let f : Supplier.TwoSat := ⟨Fintype.card V,
    edges.toList.map fun e => [(enc e.1).neg, enc e.2]⟩
  have wf : f.Wf := by
    intro c hc
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc
    refine ⟨by simp, ?_⟩
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> exact (Fintype.equivFin V _).isLt
  have nonempty : ∀ c ∈ f.clauses, c ≠ [] := by
    intro c hc
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc
    simp
  have imps : ∀ e : Supplier.Lit × Supplier.Lit,
      e ∈ f.imps ↔ ∃ l m, r l m ∧ e = (enc l, enc m) := by
    intro e
    constructor
    · intro he
      obtain ⟨c,hc,he⟩ := List.mem_flatMap.mp he
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
      have hr : r p.1 p.2 := (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).2
      change e ∈ [((enc p.1).neg.neg, enc p.2), ((enc p.2).neg, (enc p.1).neg)] at he
      simp only [Supplier.Lit.neg_neg, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨p.1,p.2,hr,rfl⟩
      · exact ⟨neg p.2,neg p.1,skew _ _ hr,by rw [enc_neg, enc_neg]⟩
    · rintro ⟨l,m,hr,rfl⟩
      apply List.mem_flatMap.mpr
      refine ⟨[(enc l).neg,enc m], ?_, ?_⟩
      · apply List.mem_map.mpr
        refine ⟨(l,m), ?_, rfl⟩
        exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩)
      · simp [Supplier.clauseImps, Supplier.Lit.neg_neg]
  have graph_edges : ∀ {u w}, f.graph.edge u w →
      ∃ l m, r l m ∧ (enc l).node = u ∧ (enc m).node = w := by
    intro u w he
    obtain ⟨_,_,e,he,hu,hw⟩ := (Supplier.graph_edge_iff f u w).mp he
    obtain ⟨l,m,hr,rfl⟩ := (imps e).mp he
    exact ⟨l,m,hr,hu,hw⟩
  have reflect : ∀ {u w}, f.graph.Reach u w →
      ∀ l m, (enc l).node = u → (enc m).node = w → ReflTransGen r l m := by
    intro u w h
    induction h with
    | refl u =>
      intro l m hl hm
      have he : l = m := enc_inj (Supplier.Lit.node_inj (hl.trans hm.symm))
      subst m
      exact ReflTransGen.refl
    | step he path ih =>
      intro l m hl hm
      obtain ⟨a,b,hr,ha,hb⟩ := graph_edges he
      have heq : l = a := enc_inj (Supplier.Lit.node_inj (hl.trans ha.symm))
      subst a
      exact (ReflTransGen.single hr).trans (ih b m hb hm)
  have noSCC : ∀ x, x < f.n →
      ¬ f.graph.SameSCC (Supplier.Lit.node ⟨x,true⟩) (Supplier.Lit.node ⟨x,false⟩) := by
    intro x hx hs
    let v : V := (Fintype.equivFin V).symm ⟨x,hx⟩
    have ht : enc (v,true) = ⟨x,true⟩ := by simp [enc,v]
    have hf : enc (v,false) = ⟨x,false⟩ := by simp [enc,v]
    apply consistent (v,true)
    constructor
    · exact reflect hs.1 (v,true) (v,false) (by rw [ht]) (by rw [hf])
    · exact reflect hs.2 (v,false) (v,true) (by rw [hf]) (by rw [ht])
  obtain ⟨a,ha⟩ := (Supplier.twoSat_iff_scc wf nonempty).mpr noSCC
  refine ⟨fun p => a (Fintype.equivFin V p).val, ?_⟩
  intro l m hr hl
  exact ((Supplier.sat_iff_closed wf).mp ha).2 (enc l,enc m)
    ((imps _).mpr ⟨l,m,hr,rfl⟩) hl

private theorem small_core {I V : Type} [Fintype V] (r : I → (V × Bool) → (V × Bool) → Prop)
    (skew : ∀ i l m, r i l m → r i (neg m) (neg l))
    (unsat : ¬ ∃ v : V → Bool, ∀ i l m, r i l m → Holds v l → Holds v m) :
    ∃ E : Finset I, E.card ≤ 2 * Fintype.card (V × Bool) ∧
      ¬ ∃ v : V → Bool, ∀ i ∈ E, ∀ l m, r i l m → Holds v l → Holds v m := by
  classical
  have bad : ∃ l, ReflTransGen (fun p q => ∃ i, r i p q) l (neg l) ∧
      ReflTransGen (fun p q => ∃ i, r i p q) (neg l) l := by
    by_contra h
    push Not at h
    obtain ⟨v,hv⟩ := implication_assignment (fun p q => ∃ i, r i p q)
      (by rintro l m ⟨i,hi⟩; exact ⟨i,skew i l m hi⟩) (fun l hh => h l hh.1 hh.2)
    apply unsat
    exact ⟨v,fun i l m hi => hv l m ⟨i,hi⟩⟩
  obtain ⟨l,hf,hb⟩ := bad
  obtain ⟨E,hE,hEr⟩ := sparse_reach r l
  obtain ⟨F,hF,hFr⟩ := sparse_reach r (neg l)
  refine ⟨E ∪ F, (Finset.card_union_le _ _).trans (by omega),?_⟩
  rintro ⟨v,hv⟩
  have closed : ∀ {a b}, ReflTransGen (Edge r (E ∪ F)) a b → Holds v a → Holds v b := by
    intro a b hh
    induction hh with
    | refl => exact id
    | @tail b c path edge ih =>
      obtain ⟨i,hi,hedge⟩ := edge
      exact fun ha => hv i hi b c hedge (ih ha)
  have incE : Edge r E ≤ Edge r (E ∪ F) := by
    rintro a b ⟨i,hi,hr⟩; exact ⟨i,Finset.mem_union_left F hi,hr⟩
  have incF : Edge r F ≤ Edge r (E ∪ F) := by
    rintro a b ⟨i,hi,hr⟩; exact ⟨i,Finset.mem_union_right E hi,hr⟩
  have pathE : ReflTransGen (Edge r (E ∪ F)) l (neg l) :=
    ReflTransGen.mono incE _ _ (hEr (neg l) hf)
  have pathF : ReflTransGen (Edge r (E ∪ F)) (neg l) l :=
    ReflTransGen.mono incF _ _ (hFr l hb)
  by_cases hl : Holds v l
  · exact (holds_neg v l).mp (closed pathE hl) hl
  · exact hl (closed pathF ((holds_neg v l).mpr hl))


private def rules {A : Type} (e : Bool) (w : List A) (t : Bool) :
    List (((A × Bool) × Bool) × ((A × Bool) × Bool)) :=
  match w with
  | [a] => [(((a,false),!t),((a,false),t))]
  | [a,b] => [(((a,false),e),((b,false),t)), (((a,false),!e),((b,true),t))]
  | _ => []

private def ruleEdge {A : Type} (e : Bool) (w : List A) (t : Bool)
    (l m : (A × Bool) × Bool) : Prop :=
  (l,m) ∈ rules e w t ∨ (neg m,neg l) ∈ rules e w t

private theorem rule_skew {A : Type} (e : Bool) (w : List A) (t : Bool)
    (l m : (A × Bool) × Bool) (h : ruleEdge e w t l m) :
    ruleEdge e w t (neg m) (neg l) := by
  simpa only [ruleEdge,neg_neg,or_comm] using h

private theorem closed_rule_iff {A : Type} (e : Bool) (w : List A) (t : Bool) (v : A × Bool → Bool) :
    (∀ l m, ruleEdge e w t l m → Holds v l → Holds v m) ↔
    (∀ l m, (l,m) ∈ rules e w t → Holds v l → Holds v m) := by
  constructor
  · intro h l m hm
    exact h l m (Or.inl hm)
  · intro h l m hm hl
    rcases hm with hm | hm
    · exact h l m hm hl
    · by_contra hn
      exact (holds_neg v l).mp (h (neg m) (neg l) hm ((holds_neg v m).mpr hn)) hl

private theorem rules_semantics {A : Type} (e : Bool) (w : List A) (t : Bool)
    (v : A × Bool → Bool) (hlen : w.length ≤ 2) (hnil : w = [] → t = e) :
    (normalized e (fun a => v (a,false)) (fun a => v (a,true))).evalOutput w = t ↔
    ∀ l m, ruleEdge e w t l m → Holds v l → Holds v m := by
  rw [closed_rule_iff]
  cases w with
  | nil => simp [rules,eval_nil,hnil rfl]
  | cons a tail =>
    cases tail with
    | nil =>
      cases hx : v (a,false) <;> cases t <;> simp [rules,eval_single,Holds,hx]
    | cons b tail =>
      cases tail with
      | nil =>
        cases hx : v (a,false) <;> cases hb : v (b,false) <;>
          cases hy : v (b,true) <;> cases e <;> cases t <;>
          simp [rules,eval_pair,Holds,hx,hb,hy] <;> exact ⟨a,by simp_all⟩
      | cons c tail => simp at hlen

theorem branch_core (k : ℕ) (D : Finset (List (Fin k))) (target : {w // w ∈ D} → Bool)
    (hlen : ∀ w ∈ D, (w : List (Fin k)).length ≤ 2) (e : Bool)
    (absent : ¬ ∃ x y : Fin k → Bool, CorrectOnFamily (normalized e x y) Subtype.val target) :
    ∃ E : Finset {w // w ∈ D}, E.card ≤ 8 * k + 1 ∧
      ¬ ∃ x y : Fin k → Bool, FitsSubsample (normalized e x y) Subtype.val target (fun i : E => i.val) := by
  classical
  by_cases emptybad : ∃ i : {w // w ∈ D}, i.val = [] ∧ target i ≠ e
  · obtain ⟨i,hi,ht⟩ := emptybad
    refine ⟨{i},by simp,?_⟩
    rintro ⟨x,y,hfit⟩
    have hh := hfit ⟨i,by simp⟩
    rw [hi,eval_nil] at hh
    exact ht hh.symm
  · have hnil : ∀ i : {w // w ∈ D}, i.val = [] → target i = e := by
      intro i hi
      by_contra hh
      exact emptybad ⟨i,hi,hh⟩
    let r (i : {w // w ∈ D}) := ruleEdge e i.val (target i)
    have us : ¬ ∃ v : Fin k × Bool → Bool,
        ∀ i l m, r i l m → Holds v l → Holds v m := by
      rintro ⟨v,hv⟩
      apply absent
      refine ⟨(fun a => v (a,false)),(fun a => v (a,true)),?_⟩
      intro i
      exact (rules_semantics e i.val (target i) v (hlen _ i.property) (hnil i)).mpr (hv i)
    obtain ⟨E,hE,hunsat⟩ := small_core r (fun i l m h => rule_skew _ _ _ l m h) us
    have card : E.card ≤ 8 * k + 1 := by
      simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] at hE
      omega
    refine ⟨E,card,?_⟩
    rintro ⟨x,y,hfit⟩
    let v : Fin k × Bool → Bool := fun p => if p.2 then y p.1 else x p.1
    apply hunsat
    refine ⟨v,?_⟩
    intro i hi
    apply (rules_semantics e i.val (target i) v (hlen _ i.property) (hnil i)).mp
    simpa only [v,Bool.false_eq_true,ite_false,ite_true] using hfit ⟨i,hi⟩

/-- A uniform linear sample cutoff suffices for exact two-state Boolean-output
realizability on arbitrary partial labelings of words of length at most two.
The constant is independent of the alphabet, sample domain and labels. -/
theorem alphabet_linear_sample_bound :
    ∃ C : ℕ, ∀ (k : ℕ) (D : Finset (List (Fin k)))
      (target : {word : List (Fin k) // word ∈ D} → Bool),
      (∀ word ∈ D, (word : List (Fin k)).length ≤ 2) →
      (∀ E : Finset {word : List (Fin k) // word ∈ D}, E.card ≤ C * (k + 1) →
        ∃ (State : Type) (_ : Fintype State) (machine : DFAO (Fin k) Bool State),
          Fintype.card State ≤ 2 ∧ FitsSubsample machine Subtype.val target (fun i : E => i.val)) →
      ∃ (State : Type) (_ : Fintype State) (machine : DFAO (Fin k) Bool State),
        Fintype.card State ≤ 2 ∧ CorrectOnFamily machine Subtype.val target := by
  classical
  refine ⟨16,?_⟩
  intro k D target hlen localModels
  by_contra absent
  have bn : ∀ e, ¬ ∃ x y : Fin k → Bool, CorrectOnFamily (normalized e x y) Subtype.val target := by
    rintro e ⟨x,y,hxy⟩
    exact absent ⟨Bool,inferInstance,normalized e x y,by decide,hxy⟩
  choose E hcard hbad using fun e => branch_core k D target hlen e (bn e)
  let U := E false ∪ E true
  have hu : U.card ≤ 16 * (k+1) := by
    have hh := Finset.card_union_le (E false) (E true)
    have h0 := hcard false
    have h1 := hcard true
    dsimp [U]
    omega
  obtain ⟨S,inst,M,hc,hfit⟩ := localModels U hu
  letI := inst
  obtain ⟨e,x,y,hagree⟩ := normalize_two_states M hc
  apply hbad e
  refine ⟨x,y,?_⟩
  intro i
  have hi : i.val ∈ U := by
    cases e
    · exact Finset.mem_union_left _ i.property
    · exact Finset.mem_union_right _ i.property
  exact (hagree _).trans (hfit ⟨i.val,hi⟩)


#print axioms alphabet_linear_sample_bound

end D5.S0.Automata.TwoStateShortWordSampleBound
