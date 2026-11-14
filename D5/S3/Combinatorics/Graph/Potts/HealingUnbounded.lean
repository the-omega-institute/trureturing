/- GID: D5/S3/Combinatorics/Graph/Potts/HealingUnbounded
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Potts/HealingUnbounded
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.claim; result=D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.result; claim=D5/S3/Combinatorics/Graph/Potts/HealingUnbounded.claim
   digest: Triangle trees force unbounded displacement before a tight set can augment. -/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
admission_basis: open-problem-resolution (#30587; Refuted)
escape_witness: independent transversals of the triangle tree omit a root-to-leaf
chain of apices, whose length is arbitrarily large.
All auxiliary theorems are private and consumed by the designated refutation.
Per-declaration shape against origin/dev; same-delivery prerequisites are expanded.
mono: proof_shape=bind-only; consumers=mem_mono,frustration,frustration_le,le_frustration,frustration_lower,frustration_exact,triangle_frustration,residual_exact
mem_mono: proof_shape=bind-only; consumers=frustration_lower,frustration_exact,triangle_frustration,residual_exact
frustration: proof_shape=bind-only; consumers=phi,Tight,claim,frustration_le,le_frustration,frustration_lower,frustration_exact,triangle_frustration,residual_exact
phi: proof_shape=bind-only; consumers=Tight,apices_tight
Tight: proof_shape=bind-only; consumers=Augmentable,Stuck,apices_tight
Augmentable: proof_shape=bind-only; consumers=Stuck,claim,displacement_bound
Stuck: proof_shape=bind-only; consumers=claim,apices_stuck
claim: proof_shape=bind-only; consumers=result
frustration_le: proof_shape=bind-only; consumers=frustration_exact,residual_exact
le_frustration: proof_shape=bind-only; consumers=frustration_lower,triangle_frustration
Vertex: proof_shape=bind-only; consumers=bridge,graph,bridge_increases,bridge_out_unique,bridge_in_unique,external_unique,degree_le,frustration_lower,coloring,bridge_color,frustration_exact,connected,apices,mem_apices,apices_independent,rootVertex,no_remaining_bridge,residual_exact,apices_dominating,independent_transversal,apex_excluded,descent,displacement_bound,result
bridge: proof_shape=bind-only; consumers=graph,graphDecidable,bridge_increases,bridge_out_unique,bridge_in_unique,bridge_color,no_remaining_bridge
graph: proof_shape=bind-only; consumers=graphDecidable,triangle_adj,external_unique,degree_le,frustration_lower,frustration_exact,triangle_reachable,connected,apices_independent,residual_exact,apices_tight,apices_dominating,apices_stuck,independent_transversal,apex_excluded,descent,displacement_bound,result
graphDecidable: proof_shape=bind-only; consumers=frustration_lower,frustration_exact,residual_exact,apices_tight,result
triangle_adj: proof_shape=bind-only; consumers=frustration_lower,frustration_exact,triangle_reachable,residual_exact,apices_dominating,apex_excluded
bridge_increases: proof_shape=bind-only; consumers=external_unique,no_remaining_bridge
bridge_out_unique: proof_shape=bind-only; consumers=external_unique
bridge_in_unique: proof_shape=bind-only; consumers=external_unique
external_unique: proof_shape=bind-only; consumers=degree_le
degree_le: proof_shape=bind-only; consumers=result
exists_mono_pair: proof_shape=bind-only; consumers=frustration_lower,triangle_frustration
frustration_lower: proof_shape=bind-only; consumers=frustration_exact
shade: proof_shape=bind-only; consumers=coloring,shade_child,bridge_color,frustration_exact
coloring: proof_shape=bind-only; consumers=bridge_color,frustration_exact
shade_child: proof_shape=bind-only; consumers=bridge_color
bridge_color: proof_shape=bind-only; consumers=frustration_exact
frustration_exact: proof_shape=bind-only; consumers=apices_tight
triangle_reachable: proof_shape=bind-only; consumers=connected
connected: proof_shape=content; consumers=result
apices: proof_shape=bind-only; consumers=mem_apices,apices_card,apices_independent,rootVertex,no_remaining_bridge,residual_exact,apices_tight,apices_dominating,apices_stuck,descent,displacement_bound,result
mem_apices: proof_shape=bind-only; consumers=apices_independent,rootVertex,no_remaining_bridge,residual_exact,apices_dominating,descent
apices_card: proof_shape=bind-only; consumers=apices_tight,displacement_bound
apices_independent: proof_shape=bind-only; consumers=apices_tight
triangle_frustration: proof_shape=bind-only; consumers=residual_exact
rootVertex: proof_shape=bind-only; consumers=residual_exact
no_remaining_bridge: proof_shape=bind-only; consumers=residual_exact
residual_exact: proof_shape=bind-only; consumers=apices_tight,result
apices_tight: proof_shape=bind-only; consumers=apices_stuck
apices_dominating: proof_shape=bind-only; consumers=apices_stuck
apices_stuck: proof_shape=bind-only; consumers=result
independent_transversal: proof_shape=bind-only; consumers=displacement_bound
apex_excluded: proof_shape=bind-only; consumers=descent
descent: proof_shape=content; consumers=displacement_bound
displacement_bound: proof_shape=content; consumers=result
result: proof_shape=content; consumers=refutes=claim
Direct frozen D5 dependencies: none.
-/

namespace D5.S3.Combinatorics.Graph.Potts.HealingUnbounded

open Finset

private noncomputable def mono {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter
    (Sym2.lift ⟨fun u v => c u = c v, fun _ _ => propext eq_comm⟩)

private lemma mem_mono {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) (u v : V) :
    s(u, v) ∈ mono G c ↔ G.Adj u v ∧ c u = c v := by
  simp [mono, SimpleGraph.mem_edgeFinset]

/-- The minimum number of monochromatic unordered edges of a Boolean colouring. -/
noncomputable def frustration {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf (Set.range (fun c : V → Bool => (mono G c).card))

/-- Vertex deletion uses the actual induced graph on the complement. -/
noncomputable def phi {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) : ℕ :=
  X.card + frustration (G.induce {v | v ∉ X})

/-- Tightness includes independence, as in Appendix B. -/
def Tight {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) : Prop :=
  G.IsIndepSet (X : Set V) ∧ phi G X = frustration G

/-- A tight set is augmentable by a new vertex while preserving tightness. -/
def Augmentable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) : Prop :=
  Tight G X ∧ ∃ v, v ∉ X ∧ Tight G (insert v X)

/-- A tight set is stuck when it has no tight independent augmentation. -/
def Stuck {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) : Prop :=
  Tight G X ∧ ¬ Augmentable G X

/-- The constant displacement assertion for all finite subcubic connected graphs. -/
def claim : Prop :=
  ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → (∀ v, G.degree v ≤ 3) →
    ¬ Nonempty (G ≃g SimpleGraph.completeGraph (Fin 4)) →
    ∀ S : Finset V, Stuck G S → 1 ≤ frustration (G.induce {v | v ∉ S}) →
    ∃ T : Finset V, Augmentable G T ∧ T.card = S.card ∧ (S \ T).card ≤ C

private lemma frustration_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) :
    frustration G ≤ (mono G c).card :=
  csInf_le' ⟨c, rfl⟩

private lemma le_frustration {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (h : ∀ c : V → Bool, k ≤ (mono G c).card) : k ≤ frustration G := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨c, rfl⟩
  exact h c

private abbrev Vertex (B : ℕ) := Fin B × Fin 3

private def bridge {B : ℕ} (x y : Vertex B) : Prop :=
  y.2 = 0 ∧
    ((x.1.val = 0 ∧ y.1.val = x.2.val + 1) ∨
      (x.1.val ≠ 0 ∧ x.2 ≠ 0 ∧ y.1.val = 2 * x.1.val + x.2.val + 1))

private def graph (B : ℕ) : SimpleGraph (Vertex B) where
  Adj x y := (x.1 = y.1 ∧ x.2 ≠ y.2) ∨ bridge x y ∨ bridge y x
  symm := ⟨by
    intro x y h
    rcases h with ⟨h₁, h₂⟩ | h | h
    · exact Or.inl ⟨h₁.symm, h₂.symm⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h | h
    · exact h.2 rfl
    all_goals
      rcases h with ⟨_, ⟨hx, hy⟩ | ⟨hx, hi, hy⟩⟩ <;> omega⟩

private instance graphDecidable (B : ℕ) : DecidableRel (graph B).Adj :=
  fun x y => by dsimp [graph, bridge]; infer_instance

private lemma triangle_adj {B : ℕ} (u : Fin B) {i j : Fin 3} (h : i ≠ j) :
    (graph B).Adj (u, i) (u, j) := Or.inl ⟨rfl, h⟩

private lemma bridge_increases {B : ℕ} {x y : Vertex B} (h : bridge x y) :
    x.1.val < y.1.val := by
  rcases h with ⟨_, ⟨hx, hy⟩ | ⟨hx, hi, hy⟩⟩ <;> omega

private lemma bridge_out_unique {B : ℕ} {x y z : Vertex B}
    (h : bridge x y) (k : bridge x z) : y = z := by
  rcases x with ⟨u, i⟩
  rcases y with ⟨v, j⟩
  rcases z with ⟨w, l⟩
  simp only [bridge] at h k
  rcases h with ⟨rfl, h⟩
  rcases k with ⟨rfl, k⟩
  congr 1
  apply Fin.ext
  rcases h with h | h <;> rcases k with k | k <;> omega

private lemma bridge_in_unique {B : ℕ} {x y z : Vertex B}
    (h : bridge y x) (k : bridge z x) : y = z := by
  rcases x with ⟨u, i⟩
  rcases y with ⟨v, j⟩
  rcases z with ⟨w, l⟩
  have hj := j.isLt
  have hl := l.isLt
  simp only [bridge, ne_eq, Fin.ext_iff] at h k
  rcases h.2 with h | h <;> rcases k.2 with k | k
  all_goals
    apply Prod.ext <;> apply Fin.ext <;> dsimp at * <;> omega

private lemma external_unique {B : ℕ} {x y z : Vertex B}
    (hy : (graph B).Adj x y) (hz : (graph B).Adj x z)
    (hxy : y.1 ≠ x.1) (hxz : z.1 ≠ x.1) : y = z := by
  rcases hy with hy | hy | hy
  · exact (hxy hy.1.symm).elim
  · rcases hz with hz | hz | hz
    · exact (hxz hz.1.symm).elim
    · exact bridge_out_unique hy hz
    · have hin := bridge_increases hz
      rcases hy with ⟨_, ⟨hx, _⟩ | ⟨_, hi, _⟩⟩
      · omega
      · exact (hi hz.1).elim
  · rcases hz with hz | hz | hz
    · exact (hxz hz.1.symm).elim
    · have hin := bridge_increases hy
      rcases hz with ⟨_, ⟨hx, _⟩ | ⟨_, hi, _⟩⟩
      · omega
      · exact (hi hy.1).elim
    · exact bridge_in_unique hy hz

private lemma degree_le (B : ℕ) (x : Vertex B) : (graph B).degree x ≤ 3 := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  change Fintype.card {y // (graph B).Adj x y} ≤ 3
  let f : {y // (graph B).Adj x y} → Fin 3 :=
    fun y => if y.val.1 = x.1 then y.val.2 else x.2
  have hf : Function.Injective f := by
    intro y z he
    apply Subtype.ext
    by_cases hy : y.val.1 = x.1 <;> by_cases hz : z.val.1 = x.1
    · have hp : y.val.2 = z.val.2 := by simpa [f, hy, hz] using he
      exact Prod.ext (hy.trans hz.symm) hp
    · have hp : y.val.2 = x.2 := by simpa [f, hy, hz] using he
      have heq : y.val = x := Prod.ext hy hp
      exact ((graph B).irrefl (heq ▸ y.property)).elim
    · have hp : x.2 = z.val.2 := by simpa [f, hy, hz] using he
      have heq : z.val = x := Prod.ext hz hp.symm
      exact ((graph B).irrefl (heq ▸ z.property)).elim
    · exact external_unique y.property z.property hy hz
  simpa using Fintype.card_le_of_injective f hf

private lemma exists_mono_pair (c : Fin 3 → Bool) :
    ∃ i j : Fin 3, i ≠ j ∧ c i = c j := by
  by_cases h : c 0 = c 1
  · exact ⟨0, 1, by decide, h⟩
  by_cases k : c 0 = c 2
  · exact ⟨0, 2, by decide, k⟩
  refine ⟨1, 2, by decide, ?_⟩
  cases h₀ : c 0 <;> cases h₁ : c 1 <;> cases h₂ : c 2 <;> simp_all

private lemma frustration_lower (B : ℕ) : B ≤ frustration (graph B) := by
  classical
  apply le_frustration
  intro c
  choose i j hij hc using fun u : Fin B => exists_mono_pair (fun a => c (u, a))
  let f : Fin B → Sym2 (Vertex B) := fun u => s((u, i u), (u, j u))
  have hf : Function.Injective f := by
    intro u v h
    change s((u, i u), (u, j u)) = s((v, i v), (v, j v)) at h
    rcases Sym2.eq_iff.mp h with h | h <;> exact congrArg Prod.fst h.1
  have hm (u : Fin B) : f u ∈ mono (graph B) c :=
    (mem_mono _ _ _ _).mpr ⟨triangle_adj u (hij u), hc u⟩
  simpa using Finset.card_le_card_of_injOn (s := univ) f
    (fun u _ => hm u) (fun _ _ _ _ h => hf h)

private def shade : ℕ → Bool
  | 0 => false
  | 1 => true
  | 2 => false
  | 3 => false
  | n + 4 => shade ((n + 2) / 2)
termination_by n => n

private def coloring {B : ℕ} (x : Vertex B) : Bool :=
  if x.2 = 0 then shade x.1.val else !(shade x.1.val)

private lemma shade_child (u : ℕ) (i : Fin 3) (hu : u ≠ 0) (hi : i ≠ 0) :
    shade (2 * u + i.val + 1) = shade u := by
  have hi' : i.val ≠ 0 := fun h => hi (Fin.ext h)
  have hil := i.isLt
  have he : 2 * u + i.val + 1 = (2 * u + i.val - 3) + 4 := by omega
  rw [he, shade]
  congr 1
  omega

private lemma bridge_color {B : ℕ} {x y : Vertex B} (h : bridge x y) :
    coloring x ≠ coloring y := by
  rcases x with ⟨u, i⟩
  rcases y with ⟨v, j⟩
  rcases h with ⟨rfl, ⟨hu, hv⟩ | ⟨hu, hi, hv⟩⟩
  all_goals dsimp at hu hv
  · have hu' : u.val = 0 := hu
    fin_cases i <;> simp_all [coloring, shade]
  · simp only [coloring, hi, ↓reduceIte, hv]
    rw [shade_child _ _ hu hi]
    cases shade u.val <;> decide

private lemma frustration_exact (B : ℕ) : frustration (graph B) = B := by
  classical
  apply le_antisymm _ (frustration_lower B)
  apply (frustration_le (graph B) coloring).trans
  let f : Fin B → Sym2 (Vertex B) := fun u => s((u, 1), (u, 2))
  have he : mono (graph B) coloring = univ.image f := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_mono]
      constructor
      · rintro ⟨hadj, hc⟩
        rcases hadj with ⟨hu, hi⟩ | hb | hb
        · rcases x with ⟨u, i⟩
          rcases y with ⟨v, j⟩
          dsimp at hu
          subst v
          have ht : (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by
            fin_cases i <;> fin_cases j <;>
              cases hs : shade u.val <;> simp_all [coloring]
          rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact mem_image.mpr ⟨u, mem_univ _, rfl⟩
          · exact mem_image.mpr ⟨u, mem_univ _, Sym2.eq_swap⟩
        · exact (bridge_color hb hc).elim
        · exact (bridge_color hb hc.symm).elim
      · rintro he
        obtain ⟨u, _, hu⟩ := mem_image.mp he
        rw [← mem_mono]
        rw [← hu]
        exact (mem_mono _ _ _ _).mpr ⟨triangle_adj u (by decide), rfl⟩
  rw [he]
  simpa using card_image_le (s := (univ : Finset (Fin B))) (f := f)

private lemma triangle_reachable {B : ℕ} (u : Fin B) (i j : Fin 3) :
    (graph B).Reachable (u, i) (u, j) := by
  by_cases h : i = j
  · subst j; exact SimpleGraph.Reachable.rfl
  · exact (triangle_adj u h).reachable

private lemma connected (B : ℕ) (hB : 4 ≤ B) : (graph B).Connected := by
  let r : Fin B := ⟨0, by omega⟩
  have hr : ∀ n (hn : n < B), (graph B).Reachable (r, 0) (⟨n, hn⟩, 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hz : n = 0
      · subst n; exact SimpleGraph.Reachable.rfl
      by_cases hsmall : n < 4
      · let i : Fin 3 := ⟨n - 1, by omega⟩
        apply (triangle_reachable r 0 i).trans
        apply SimpleGraph.Adj.reachable
        exact Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, by dsimp [i]; omega⟩⟩)
      · let p : ℕ := (n - 2) / 2
        let i : Fin 3 := ⟨(n - 2) % 2 + 1, by omega⟩
        have hp : p < n := by dsimp [p]; omega
        have hpB : p < B := by omega
        apply (ih p hp hpB).trans
        apply (triangle_reachable ⟨p, hpB⟩ 0 i).trans
        apply SimpleGraph.Adj.reachable
        apply Or.inr ∘ Or.inl
        refine ⟨rfl, Or.inr ⟨?_, ?_, ?_⟩⟩
        · dsimp [p]; omega
        · apply Fin.ne_of_val_ne; dsimp [i]; omega
        · dsimp [p, i]; omega
  have hall (x : Vertex B) : (graph B).Reachable (r, 0) x :=
    (hr x.1.val x.1.isLt).trans (triangle_reachable x.1 0 x.2)
  haveI : Nonempty (Vertex B) := ⟨(r, 0)⟩
  exact ⟨fun x y => (hall x).symm.trans (hall y)⟩

private def apices (B : ℕ) [NeZero B] : Finset (Vertex B) :=
  (univ.erase 0) ×ˢ {0}

private lemma mem_apices {B : ℕ} [NeZero B] (x : Vertex B) :
    x ∈ apices B ↔ x.1 ≠ 0 ∧ x.2 = 0 := by
  rcases x with ⟨u, i⟩
  by_cases hi : i = 0 <;> simp [apices, hi, eq_comm]

private lemma apices_card (B : ℕ) [NeZero B] : (apices B).card = B - 1 := by
  simp [apices]

private lemma apices_independent (B : ℕ) [NeZero B] :
    (graph B).IsIndepSet (apices B : Set (Vertex B)) := by
  intro x hx y hy hne hadj
  have hx := (mem_apices x).mp hx
  have hy := (mem_apices y).mp hy
  have hx' : x.1.val ≠ 0 := fun h => hx.1 (Fin.ext h)
  have hy' : y.1.val ≠ 0 := fun h => hy.1 (Fin.ext h)
  rcases hadj with h | h | h
  · exact h.2 (hx.2.trans hy.2.symm)
  · rcases h.2 with h | h
    · exact hx' h.1
    · exact h.2.1 hx.2
  · rcases h.2 with h | h
    · exact hy' h.1
    · exact h.2.1 hy.2

private lemma triangle_frustration {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Fin 3 → V)
    (he : ∀ i j, i ≠ j → G.Adj (e i) (e j)) : 1 ≤ frustration G := by
  apply le_frustration
  intro c
  obtain ⟨i, j, hij, hc⟩ := exists_mono_pair (c ∘ e)
  have hm : s(e i, e j) ∈ mono G c := (mem_mono _ _ _ _).mpr ⟨he i j hij, hc⟩
  exact card_pos.mpr ⟨_, hm⟩

private def rootVertex (B : ℕ) [NeZero B] (i : Fin 3) :
    {v : Vertex B // v ∉ apices B} :=
  ⟨(0, i), by simp [mem_apices]⟩

private lemma no_remaining_bridge {B : ℕ} [NeZero B]
    (x y : {v : Vertex B // v ∉ apices B}) : ¬ bridge x.val y.val := by
  intro h
  have hi := bridge_increases h
  apply y.property
  apply (mem_apices _).mpr
  refine ⟨?_, h.1⟩
  intro hz
  have : y.val.1.val = 0 := congrArg Fin.val hz
  omega

private lemma residual_exact (B : ℕ) [NeZero B] :
    frustration ((graph B).induce {v | v ∉ apices B}) = 1 := by
  classical
  let H := (graph B).induce {v | v ∉ apices B}
  apply le_antisymm
  · let c : {v : Vertex B // v ∉ apices B} → Bool := fun v => decide (v.val.2 = 2)
    apply (frustration_le H c).trans
    apply Finset.card_le_one.mpr
    have he (e : Sym2 {v : Vertex B // v ∉ apices B}) (hm : e ∈ mono H c) :
        e = s(rootVertex B 0, rootVertex B 1) := by
      induction e using Sym2.ind with
      | _ x y =>
        obtain ⟨hadj, hc⟩ := (mem_mono H c x y).mp hm
        dsimp [c] at hc
        change (graph B).Adj x.val y.val at hadj
        rcases hadj with ⟨hu, hi⟩ | hb | hb
        · have hx : x.val.1 = 0 ∨ x.val.2 ≠ 0 := by
            have := x.property
            simpa only [mem_apices, not_and_or, not_not] using this
          have hy : y.val.1 = 0 ∨ y.val.2 ≠ 0 := by
            have := y.property
            simpa only [mem_apices, not_and_or, not_not] using this
          have hv : x.val.1 = 0 := by
            by_contra hn
            have hn' : y.val.1 ≠ 0 := fun h => hn (hu.trans h)
            have hx0 := hx.resolve_left hn
            have hy0 := hy.resolve_left hn'
            have hxi := x.val.2.isLt
            have hyi := y.val.2.isLt
            generalize h₁ : x.val.2 = i at *
            generalize h₂ : y.val.2 = j at *
            fin_cases i <;> fin_cases j <;>
              simp_all [c]
          have hv' : y.val.1 = 0 := hu.symm.trans hv
          have hp : (x.val.2 = 0 ∧ y.val.2 = 1) ∨
              (x.val.2 = 1 ∧ y.val.2 = 0) := by
            generalize h₁ : x.val.2 = i at *
            generalize h₂ : y.val.2 = j at *
            fin_cases i <;> fin_cases j <;> simp_all [c]
          have hxv (i : Fin 3) (h : x.val.2 = i) : x = rootVertex B i :=
            Subtype.ext (Prod.ext hv h)
          have hyv (i : Fin 3) (h : y.val.2 = i) : y = rootVertex B i :=
            Subtype.ext (Prod.ext hv' h)
          rcases hp with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · rw [hxv _ h₁, hyv _ h₂]
          · rw [hxv _ h₁, hyv _ h₂]; exact Sym2.eq_swap
        · exact (no_remaining_bridge x y hb).elim
        · exact (no_remaining_bridge y x hb).elim
    intro e he₁ f hf
    exact (he e he₁).trans (he f hf).symm
  · apply triangle_frustration H (rootVertex B)
    intro i j hij
    exact triangle_adj 0 hij

private lemma apices_tight (B : ℕ) [NeZero B] : Tight (graph B) (apices B) := by
  refine ⟨apices_independent B, ?_⟩
  unfold phi
  rw [apices_card, residual_exact, frustration_exact]
  have := NeZero.ne B
  omega

private lemma apices_dominating (B : ℕ) [NeZero B] (hB : 4 ≤ B)
    (v : Vertex B) (hv : v ∉ apices B) :
    ∃ w ∈ apices B, (graph B).Adj v w := by
  by_cases hr : v.1 = 0
  · let u : Fin B := ⟨v.2.val + 1, by have := v.2.isLt; omega⟩
    refine ⟨(u, 0), (mem_apices _).mpr ⟨?_, rfl⟩, ?_⟩
    · apply Fin.ne_of_val_ne; dsimp [u]; omega
    · exact Or.inr (Or.inl ⟨rfl, Or.inl ⟨congrArg Fin.val hr, rfl⟩⟩)
  · have hp : v.2 ≠ 0 := fun h => hv ((mem_apices _).mpr ⟨hr, h⟩)
    exact ⟨(v.1, 0), (mem_apices _).mpr ⟨hr, rfl⟩, triangle_adj v.1 hp⟩

private lemma apices_stuck (B : ℕ) [NeZero B] (hB : 4 ≤ B) :
    Stuck (graph B) (apices B) := by
  refine ⟨apices_tight B, ?_⟩
  rintro ⟨_, v, hv, hT⟩
  obtain ⟨w, hw, hadj⟩ := apices_dominating B hB v hv
  exact hT.1 (mem_insert_self v _) (mem_insert_of_mem hw) hadj.ne hadj

private lemma independent_transversal {B : ℕ} (R : Finset (Vertex B))
    (hR : (graph B).IsIndepSet (R : Set (Vertex B))) (hcard : R.card = B) :
    ∃ r : Fin B → Fin 3, ∀ u, (u, r u) ∈ R := by
  classical
  have hinj : Set.InjOn Prod.fst (R : Set (Vertex B)) := by
    intro x hx y hy hxy
    by_contra hne
    have hp : x.2 ≠ y.2 := fun h => hne (Prod.ext hxy h)
    exact hR hx hy hne (Or.inl ⟨hxy, hp⟩)
  have hsurj := Finset.surjOn_of_injOn_of_card_le (s := R) (t := univ)
    Prod.fst (fun _ _ => mem_univ _) hinj (by simpa using hcard.symm.le)
  have hh (u : Fin B) : ∃ i : Fin 3, (u, i) ∈ R := by
    obtain ⟨x, hx, hxu⟩ := hsurj (mem_univ u)
    exact ⟨x.2, by simpa [← hxu] using hx⟩
  exact ⟨fun u => Classical.choose (hh u), fun u => Classical.choose_spec (hh u)⟩

private lemma apex_excluded {B : ℕ} (R : Finset (Vertex B))
    (hR : (graph B).IsIndepSet (R : Set (Vertex B)))
    (r : Fin B → Fin 3) (hr : ∀ u, (u, r u) ∈ R)
    (u : Fin B) (hi : r u ≠ 0) : (u, 0) ∉ R := by
  intro hu
  have hadj := triangle_adj u hi
  exact hR (hr u) hu hadj.ne hadj

private lemma descent {B : ℕ} [NeZero B] (R : Finset (Vertex B))
    (hR : (graph B).IsIndepSet (R : Set (Vertex B)))
    (r : Fin B → Fin 3) (hr : ∀ u, (u, r u) ∈ R) :
    ∀ k (u : Fin B), 0 < u.val → r u ≠ 0 → 2 ^ k * (u.val + 3) ≤ B + 2 →
      ∃ F : Finset (Vertex B), F ⊆ apices B \ R ∧
        (∀ x ∈ F, u.val ≤ x.1.val) ∧ k + 1 ≤ F.card := by
  intro k
  induction k with
  | zero =>
    intro u hu hi _
    refine ⟨{(u, 0)}, ?_, ?_, by simp⟩
    · apply singleton_subset_iff.mpr
      exact mem_sdiff.mpr ⟨(mem_apices _).mpr
        ⟨Fin.ne_of_val_ne (by simpa only [Fin.val_zero] using Nat.ne_of_gt hu), rfl⟩,
        apex_excluded R hR r hr u hi⟩
    · intro x hx
      simp only [mem_singleton] at hx
      subst x
      exact le_rfl
  | succ k ih =>
    intro u hu hi hbound
    let cval := 2 * u.val + (r u).val + 1
    have hport := (r u).isLt
    have hupper : cval + 3 ≤ 2 * (u.val + 3) := by dsimp [cval]; omega
    have htail : 2 ^ k * (cval + 3) ≤ B + 2 := by
      calc
        _ ≤ 2 ^ k * (2 * (u.val + 3)) := Nat.mul_le_mul_left _ hupper
        _ = 2 ^ (k + 1) * (u.val + 3) := by rw [pow_succ]; ring
        _ ≤ B + 2 := hbound
    have hpow : 0 < 2 ^ k := pow_pos (by decide) _
    have hcB : cval < B := by nlinarith
    let c : Fin B := ⟨cval, hcB⟩
    have huc : u.val < c.val := by dsimp [c, cval]; omega
    have hadj : (graph B).Adj (u, r u) (c, 0) := by
      exact Or.inr (Or.inl ⟨rfl, Or.inr ⟨Nat.ne_of_gt hu, hi, rfl⟩⟩)
    have hcnot : (c, 0) ∉ R := fun h => hR (hr u) h hadj.ne hadj
    have hci : r c ≠ 0 := by
      intro h
      apply hcnot
      simpa [h] using hr c
    obtain ⟨F, hF, hmin, hcard⟩ := ih c (by omega) hci htail
    have hnot : (u, 0) ∉ F := by
      intro h
      have hm := hmin _ h
      dsimp at hm
      omega
    refine ⟨insert (u, 0) F, ?_, ?_, ?_⟩
    · apply insert_subset_iff.mpr
      exact ⟨mem_sdiff.mpr ⟨(mem_apices _).mpr
        ⟨Fin.ne_of_val_ne (by simpa only [Fin.val_zero] using Nat.ne_of_gt hu), rfl⟩,
        apex_excluded R hR r hr u hi⟩, hF⟩
    · intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · exact huc.le.trans (hmin x hx)
    · rw [card_insert_of_notMem hnot]
      omega

private lemma displacement_bound (n B : ℕ) [NeZero B] (hB : 4 ≤ B)
    (hsize : B + 2 = 3 * 2 ^ (n + 1)) (T : Finset (Vertex B))
    (hT : Augmentable (graph B) T) (hcard : T.card = (apices B).card) :
    n + 1 ≤ (apices B \ T).card := by
  classical
  obtain ⟨v, hv, hRv⟩ := hT.2
  let R := insert v T
  have hR : (graph B).IsIndepSet (R : Set (Vertex B)) := hRv.1
  have hRc : R.card = B := by
    dsimp [R]
    rw [card_insert_of_notMem hv, hcard, apices_card]
    omega
  obtain ⟨r, hr⟩ := independent_transversal R hR hRc
  let u : Fin B := ⟨(r 0).val + 1, by have := (r 0).isLt; omega⟩
  have hadj : (graph B).Adj (0, r 0) (u, 0) :=
    Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)
  have hu : r u ≠ 0 := by
    intro heq
    have hm : (u, 0) ∈ R := by simpa [heq] using hr u
    exact hR (hr 0) hm hadj.ne hadj
  have hbound : 2 ^ n * (u.val + 3) ≤ B + 2 := by
    have hp := (r 0).isLt
    rw [hsize, pow_succ]
    dsimp [u]
    calc
      _ ≤ 2 ^ n * 6 := Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (2 ^ n * 2) := by ring
  obtain ⟨F, hF, _, hfcard⟩ := descent R hR r hr n u (by dsimp [u]; omega) hu hbound
  have hsub : apices B \ R ⊆ apices B \ T := by
    intro x hx
    obtain ⟨hs, hnr⟩ := mem_sdiff.mp hx
    exact mem_sdiff.mpr ⟨hs, fun ht => hnr (mem_insert_of_mem ht)⟩
  exact hfcard.trans (card_le_card (hF.trans hsub))

/-- There is no uniform bound on displacement to an augmentable tight set. -/
theorem result : ¬ claim := by
  rintro ⟨C, hC⟩
  let B := 3 * 2 ^ (C + 1) - 2
  have hp : 0 < 2 ^ C := pow_pos (by decide) _
  have hsize : B + 2 = 3 * 2 ^ (C + 1) := by
    dsimp [B]
    rw [pow_succ]
    omega
  have hB : 4 ≤ B := by rw [pow_succ] at hsize; omega
  haveI : NeZero B := ⟨by omega⟩
  have hnK : ¬ Nonempty (graph B ≃g SimpleGraph.completeGraph (Fin 4)) := by
    rintro ⟨e⟩
    have hc := Fintype.card_congr e.toEquiv
    change Fintype.card (Fin B × Fin 3) = Fintype.card (Fin 4) at hc
    simp only [Fintype.card_prod, Fintype.card_fin] at hc
    omega
  obtain ⟨T, hT, hc, hd⟩ := hC (Vertex B) (graph B) (connected B hB)
    (degree_le B) hnK (apices B) (apices_stuck B hB) (by rw [residual_exact])
  have hlarge := displacement_bound C B hB hsize T hT hc
  omega

end D5.S3.Combinatorics.Graph.Potts.HealingUnbounded
