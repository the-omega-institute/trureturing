/- GID: D5/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The recursive two-tree family separates tree stretch from gain reconstruction. -/

import D5.S3.Combinatorics.Graph.Chordal.Dirac
import D5.S3.Combinatorics.Graph.Chordal.TwoTreeFamily
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Analysis.Normed.Group.Int
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Stretch and gain reconstruction on recursive two-trees

Each frontier edge is directed. At the next step it acquires a fresh vertex
and two directed child edges along the path through that vertex. The original
edge remains in the graph.
-/

open scoped BigOperators ENNReal

namespace SimpleGraph

noncomputable section

local instance : DecidableRel (twoTree 0).Adj := Top.adjDecidable (Fin 3)

private theorem source_ne_target (d : ℕ) (e : TwoTreeFrontier d) :
    twoTreeSource d e ≠ twoTreeTarget d e := (twoTreeFrontierDart d e).fst_ne_snd
private theorem frontier_adj (d : ℕ) (e : TwoTreeFrontier d) :
    (twoTree d).Adj (twoTreeSource d e) (twoTreeTarget d e) :=
  (twoTreeFrontierDart d e).adj

private theorem frontier_card (d : ℕ) : Fintype.card (TwoTreeFrontier d) = 3 * 2 ^ d := by
  induction d with
  | zero => decide
  | succ d ih =>
    change Fintype.card (TwoTreeFrontier d × Bool) = _
    rw [Fintype.card_prod, ih, Fintype.card_bool, pow_succ, mul_assoc]

/-- The vertex count doubles in each round, starting with the three core vertices. -/
private theorem twoTree_card (d : ℕ) : Fintype.card (TwoTreeV d) = 3 * 2 ^ d := by
  induction d with
  | zero => decide
  | succ d ih =>
    change Fintype.card (TwoTreeV d ⊕ TwoTreeFrontier d) = _
    rw [Fintype.card_sum, ih, frontier_card, pow_succ]
    omega

private def attachOld {V I : Type*} (G : SimpleGraph V) (s t : I → V) :
    G ↪g twoTreeAttach G s t where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl
private theorem attach_connected {V I : Type*} {G : SimpleGraph V} {s t : I → V}
    (hG : G.Connected) : (twoTreeAttach G s t).Connected where
  nonempty := hG.nonempty.map Sum.inl
  preconnected := by
    have old (u v : V) : (twoTreeAttach G s t).Reachable (.inl u) (.inl v) :=
      (hG u v).map (attachOld G s t).toHom
    have fresh (e : I) : (twoTreeAttach G s t).Reachable (.inl (s e)) (.inr e) :=
      Adj.reachable (show (twoTreeAttach G s t).Adj (.inl (s e)) (.inr e) from Or.inl rfl)
    rintro (u | e) (v | f)
    · exact old u v
    · exact (old u (s f)).trans (fresh f)
    · exact (fresh e).symm.trans (old (s e) v)
    · exact (fresh e).symm.trans ((old (s e) (s f)).trans (fresh f))
private theorem twoTree_connected (d : ℕ) : (twoTree d).Connected := by
  induction d with
  | zero => exact connected_top
  | succ d ih => exact attach_connected ih

private theorem reverse_error {V H : Type*} [Group H] [PseudoMetricSpace H]
    [IsIsometricSMul Hᵐᵒᵖ H] {g : V → V → H} {φ : V → H}
    {a b : V} {ε : ℝ} (hrev : g b a = (g a b)⁻¹)
    (h : Dist.dist (φ a * g a b) (φ b) ≤ ε) :
    Dist.dist (φ b * g b a) (φ a) ≤ ε := by
  rw [hrev, ← dist_mul_right _ _ (g a b), mul_assoc, inv_mul_cancel, mul_one, _root_.dist_comm]
  exact h

/-- A triangle defect bound is a simultaneous edge error bound on every recursive two-tree. -/
theorem twoTree_exists_one_approximate_gain_potential (d : ℕ)
    {H : Type*} [Group H] [PseudoMetricSpace H] [IsIsometricSMul H H]
    [IsIsometricSMul Hᵐᵒᵖ H] (g : TwoTreeV d → TwoTreeV d → H) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ u v, (twoTree d).Adj u v → g v u = (g u v)⁻¹)
    (htri : ∀ u v w, (twoTree d).Adj u v → (twoTree d).Adj v w → (twoTree d).Adj u w →
      Dist.dist (g u v * g v w) (g u w) ≤ ε) :
    ∃ φ : TwoTreeV d → H, ∀ u v, (twoTree d).Adj u v →
      Dist.dist (g u v) ((φ u)⁻¹ * φ v) ≤ ε := by
  suffices ∃ φ : TwoTreeV d → H, ∀ u v, (twoTree d).Adj u v →
      Dist.dist (φ u * g u v) (φ v) ≤ ε by
    obtain ⟨φ, hφ⟩ := this
    refine ⟨φ, fun u v huv => ?_⟩
    rw [← dist_mul_left (φ u), mul_inv_cancel_left]
    exact hφ u v huv
  induction d with
  | zero =>
    let φ : TwoTreeV 0 → H := fun u =>
      if (u : Fin 3) = 0 then 1 else
      if (u : Fin 3) = 1 then g 0 1 else g 0 1 * g 1 2
    have h01 : Dist.dist (φ 0 * g 0 1) (φ 1) ≤ ε := by simpa [φ] using hε
    have h12 : Dist.dist (φ 1 * g 1 2) (φ 2) ≤ ε := by simpa [φ] using hε
    have h02 : Dist.dist (φ 0 * g 0 2) (φ 2) ≤ ε := by
      simpa [φ, _root_.dist_comm] using htri 0 1 2 (by decide) (by decide) (by decide)
    refine ⟨φ, fun u v huv => ?_⟩
    change Fin 3 at u v
    fin_cases u <;> fin_cases v
    · exact (huv.ne rfl).elim
    · exact h01
    · exact h02
    · exact reverse_error (hrev 0 1 (by decide)) h01
    · exact (huv.ne rfl).elim
    · exact h12
    · exact reverse_error (hrev 0 2 (by decide)) h02
    · exact reverse_error (hrev 1 2 (by decide)) h12
    · exact (huv.ne rfl).elim
  | succ d ih =>
    obtain ⟨ψ, hψ⟩ := ih (fun u v => g (.inl u) (.inl v))
      (fun _ _ h => hrev _ _ h) (fun _ _ _ h₁ h₂ h₃ => htri _ _ _ h₁ h₂ h₃)
    let φ : TwoTreeV (d + 1) → H := Sum.elim ψ fun e =>
      ψ (twoTreeSource d e) * g (.inl (twoTreeSource d e)) (.inl (twoTreeTarget d e)) *
        g (.inl (twoTreeTarget d e)) (.inr e)
    have fresh (e : TwoTreeFrontier d) (u : TwoTreeV d)
        (h : u = twoTreeSource d e ∨ u = twoTreeTarget d e) :
        Dist.dist (φ (.inl u) * g (.inl u) (.inr e)) (φ (.inr e)) ≤ ε := by
      rcases h with rfl | rfl
      · change Dist.dist (ψ _ * g _ _) ((ψ _ * g _ _) * g _ _) ≤ ε
        rw [mul_assoc, dist_mul_left, _root_.dist_comm]
        exact htri _ _ _ (frontier_adj d e) (Or.inr rfl) (Or.inl rfl)
      · change Dist.dist (ψ _ * g _ _) ((ψ _ * g _ _) * g _ _) ≤ ε
        rw [dist_mul_right, _root_.dist_comm]
        exact hψ _ _ (frontier_adj d e)
    refine ⟨φ, ?_⟩
    change ∀ u v : TwoTreeV d ⊕ TwoTreeFrontier d, _
    rintro (u | e) (v | f) h
    · exact hψ _ _ h
    · exact fresh f u h
    · exact reverse_error (hrev _ _ h.symm) (fresh e v h)
    · exact h.elim
private theorem fresh_chord {V I : Type*} {G : SimpleGraph V} {s t : I → V}
    (he : ∀ e, G.Adj (s e) (t e)) {e : I}
    (c : (twoTreeAttach G s t).Walk (.inr e) (.inr e)) (hc : c.IsCycle) (hn : 4 ≤ c.length) :
    ∃ a b, a ∈ c.support ∧ b ∈ c.support ∧ (twoTreeAttach G s t).Adj a b ∧ s(a, b) ∉ c.edges := by
  let A := twoTreeAttach G s t
  let a := c.getVert 1
  let b := c.getVert (c.length - 1)
  have ha : A.Adj (.inr e) a := by
    simpa [a] using c.adj_getVert_succ (i := 0) (by omega)
  have hb : A.Adj (.inr e) b := by
    have h := c.adj_getVert_succ (i := c.length - 1) (by omega)
    rw [show c.length - 1 + 1 = c.length by omega, c.getVert_length] at h
    exact h.symm
  have indices {i j : ℕ} (hi : 1 ≤ i) (hi' : i ≤ c.length) (hj : 1 ≤ j)
      (hj' : j ≤ c.length) (h : c.getVert i = c.getVert j) : i = j :=
    hc.getVert_injOn ⟨hi, hi'⟩ ⟨hj, hj'⟩ h
  have hab : a ≠ b := fun h ↦ by
    have := indices (i := 1) (j := c.length - 1) (by omega) (by omega)
      (by omega) (by omega) h
    omega
  have hchord : A.Adj a b := by
    cases ha' : a with
    | inr j => exfalso; simpa only [ha', A, twoTreeAttach] using ha
    | inl x =>
      cases hb' : b with
      | inr j => exfalso; simpa only [hb', A, twoTreeAttach] using hb
      | inl y =>
        simp only [ha'] at ha
        simp only [hb'] at hb
        have hx : x = s e ∨ x = t e := ha
        have hy : y = s e ∨ y = t e := hb
        simp only [ha', hb'] at hab ⊢
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact (hab rfl).elim
        · exact he e
        · exact (he e).symm
        · exact (hab rfl).elim
  refine ⟨a, b, c.getVert_mem_support _, c.getVert_mem_support _, hchord, ?_⟩
  intro h
  obtain ⟨i, hi, hij⟩ := (Walk.mk_mem_edges_iff_exists c).mp h
  have hpos : 1 ≤ i := by
    by_contra! hzero
    have : i = 0 := by omega
    subst i
    rw [c.getVert_zero] at hij
    rcases Sym2.eq_iff.mp hij with ⟨h, _⟩ | ⟨h, _⟩
    · exact ha.ne h
    · exact hb.ne h
  rcases Sym2.eq_iff.mp hij with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have := indices (i := i) (j := 1) hpos (by omega) (by omega) (by omega) h₁
    have := indices (i := i + 1) (j := c.length - 1) (by omega) (by omega)
      (by omega) (by omega) h₂
    omega
  · have := indices (i := i) (j := c.length - 1) hpos (by omega) (by omega) (by omega) h₁
    have := indices (i := i + 1) (j := 1) (by omega) (by omega) (by omega) (by omega) h₂
    omega
private theorem attach_chordal {V I : Type*} {G : SimpleGraph V} {s t : I → V}
    (hG : G.IsChordal) (he : ∀ e, G.Adj (s e) (t e)) : (twoTreeAttach G s t).IsChordal := by
  classical
  let A := twoTreeAttach G s t
  intro v p hp hn
  by_cases hnew : ∃ e : I, Sum.inr e ∈ p.support
  · obtain ⟨e, hm⟩ := hnew
    obtain ⟨a, b, ha, hb, hab, he'⟩ := fresh_chord he (p.rotate _ hm)
      ((Walk.isCycle_rotate hm).mpr hp) (by simpa using hn)
    exact ⟨a, b, (p.mem_support_rotate_iff _ _).mp ha, (p.mem_support_rotate_iff _ _).mp hb,
      hab, fun h => he' ((p.rotate_edges _ _).mem_iff.mpr h)⟩
  · let S : Set (V ⊕ I) := Set.range Sum.inl
    have hs : ∀ x ∈ p.support, x ∈ S := by
      rintro (x | e) hx
      · exact ⟨x, rfl⟩
      · exact (hnew ⟨e, hx⟩).elim
    let f : V ≃ S := Equiv.ofInjective Sum.inl Sum.inl_injective
    let iso : A.induce S ≃g G :=
      { toEquiv := f.symm
        map_rel_iff' := by
          intro u w
          obtain ⟨u, rfl⟩ := f.surjective u
          obtain ⟨w, rfl⟩ := f.surjective w
          simp only [Equiv.symm_apply_apply]
          rfl }
    let c := p.induce S hs
    have hm : c.map (Embedding.induce (G := A) S).toHom = p := p.map_induce hs
    have hc : c.IsCycle := (Walk.isCycle_map_iff_of_injective
      (Embedding.induce (G := A) S).injective).1 (hm.symm ▸ hp)
    have hlen : c.length = p.length := by
      exact (c.length_map (Embedding.induce (G := A) S).toHom).symm.trans
        (congrArg Walk.length hm)
    let b := c.map iso.toHom
    obtain ⟨x, y, hx, hy, hadj, hne⟩ := hG b (hc.map iso.injective)
      (by simpa [b, hlen] using hn)
    have lift_mem (z : V) (hz : z ∈ b.support) : f z ∈ c.support := by
      obtain ⟨u, hu, h⟩ := List.mem_map.mp (by simpa only [b, Walk.support_map] using hz)
      have heq : f.symm u = z := h
      exact (f.symm_apply_eq.mp heq) ▸ hu
    let inc : A.induce S →g A := (Embedding.induce (G := A) S).toHom
    have supports : p.support = c.support.map inc := by
      calc
        p.support = (c.map inc).support := congrArg Walk.support hm.symm
        _ = _ := c.support_map inc
    have edges : p.edges = c.edges.map (Sym2.map inc) := by
      calc
        p.edges = (c.map inc).edges := congrArg Walk.edges hm.symm
        _ = _ := c.edges_map inc
    refine ⟨.inl x, .inl y, ?_, ?_, hadj, ?_⟩
    · rw [supports]
      exact List.mem_map.mpr ⟨f x, lift_mem x hx, rfl⟩
    · rw [supports]
      exact List.mem_map.mpr ⟨f y, lift_mem y hy, rfl⟩
    · intro h
      apply hne
      rw [edges] at h
      obtain ⟨z, hz, heq⟩ := List.mem_map.mp h
      have hz' : z = s(f x, f y) := Sym2.map.injective (Embedding.induce (G := A) S).injective heq
      change s(x, y) ∈ (c.map iso.toHom).edges
      rw [Walk.edges_map]
      exact List.mem_map.mpr ⟨z, hz, by simp [hz', iso]⟩

/-- Every graph in the family is chordal and connected. -/
theorem twoTree_isChordal (d : ℕ) :
    (twoTree d).IsChordal ∧ (twoTree d).Connected ∧ Fintype.card (TwoTreeV d) = 3 * 2 ^ d := by
  refine ⟨?_, twoTree_connected d, twoTree_card d⟩
  induction d with
  | zero =>
    intro v p hp hn
    have h := hp.support_nodup.length_le_card
    rw [List.length_tail, Walk.length_support, twoTree_card] at h
    norm_num at h
    omega
  | succ d ih => exact attach_chordal ih (frontier_adj d)

private def quotientWalk {V W : Type*} [DecidableEq W] {T : SimpleGraph V} (f : V → W) {u v : V} :
    T.Walk u v → (T.map f).Walk (f u) (f v)
  | .nil => .nil
  | .cons (v := z) h p =>
    if he : f u = f z then (quotientWalk f p).copy he.symm rfl
    else .cons (map_adj_apply' h he) (quotientWalk f p)
private theorem quotientWalk_length {V W : Type*} [DecidableEq W] {T : SimpleGraph V} (f : V → W)
    {u v : V} (p : T.Walk u v) : (quotientWalk f p).length ≤ p.length := by
  induction p with
  | nil => exact le_rfl
  | cons h p ih =>
    unfold quotientWalk
    split <;> simp only [Walk.length_copy, Walk.length_cons] <;> omega
private theorem quotient_isTree {V W : Type*} {T : SimpleGraph V} (hT : T.IsTree)
    (f : V → W) (old : W → V) (hold : ∀ x, f (old x) = x)
    (hf : ∀ x, x = old (f x) ∨ T.Adj x (old (f x))) : (T.map f).IsTree := by
  classical
  refine isTree_iff_minimal_connected.mpr ⟨?_, ?_⟩
  · rw [connected_iff]
    refine ⟨?_, hT.connected.nonempty.map f⟩
    intro u v
    obtain ⟨p⟩ := hT.connected (old u) (old v)
    exact ⟨(quotientWalk f p).copy (hold u) (hold v)⟩
  · intro S hS hle
    let R : SimpleGraph V :=
      { Adj := fun u v => T.Adj u v ∧ (f u = f v ∨ S.Adj (f u) (f v))
        symm.symm _ _ h := ⟨h.1.symm, h.2.elim (fun he => Or.inl he.symm)
          (fun he => Or.inr he.symm)⟩
        loopless := ⟨fun _ h => h.1.ne rfl⟩ }
    have return_to_old (u : V) : R.Reachable u (old (f u)) := by
      rcases hf u with he | hadj
      · rw [← he]
      · exact Adj.reachable (show R.Adj u (old (f u)) from ⟨hadj, Or.inl (hold _).symm⟩)
    have liftEdge {a b : W} (h : S.Adj a b) : R.Reachable (old a) (old b) := by
      obtain ⟨_, x, y, hxy, hx, hy⟩ := (map_adj' f T a b).mp (hle h)
      have hxy' : R.Adj x y := ⟨hxy, Or.inr (by simpa only [hx, hy] using h)⟩
      simpa only [hx, hy] using (return_to_old x).symm.trans (hxy'.reachable.trans (return_to_old y))
    have liftWalk {u v : W} (p : S.Walk u v) : R.Reachable (old u) (old v) := by
      induction p with
      | nil => exact Reachable.rfl
      | cons h _ ih => exact (liftEdge h).trans ih
    have hR : R.Connected := by
      rw [connected_iff]
      refine ⟨?_, hT.connected.nonempty⟩
      intro u v
      obtain ⟨p⟩ := hS (f u) (f v)
      exact (return_to_old u).trans ((liftWalk p).trans (return_to_old v).symm)
    have hRT : R ≤ T := fun _ _ h => h.1
    have hTR := (isTree_iff_minimal_connected.mp hT).2 hR hRT
    intro a b h
    obtain ⟨hne, x, y, hxy, hx, hy⟩ := (map_adj' f T a b).mp h
    have hr : R.Adj x y := hTR hxy
    rcases hr.2 with he | hadj
    · exact (hne (hx.symm.trans (he.trans hy))).elim
    · simpa only [hx, hy] using hadj
private theorem leaf_dist {V : Type*} {T : SimpleGraph V} (hc : T.Connected)
    {w a b : V} (hwb : w ≠ b) (h : ∀ x, T.Adj w x → x = a) :
    T.dist a b + 1 ≤ T.dist w b := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist w b
  cases p with
  | nil => exact (hwb rfl).elim
  | cons hadj p =>
    have ha := h _ hadj
    subst a
    have := T.dist_le p
    simp only [Walk.length_cons] at hp
    omega

private theorem frontier_stretch_lower (d : ℕ) (T : SimpleGraph (TwoTreeV d))
    (hsub : T ≤ twoTree d) (hT : T.IsTree) :
    ∃ e, d + 2 ≤ T.dist (twoTreeSource d e) (twoTreeTarget d e) := by
  induction d with
  | zero =>
    by_contra! h
    have all (e : TwoTreeFrontier 0) : T.Adj (twoTreeSource 0 e) (twoTreeTarget 0 e) := by
      have hpos := hT.connected.pos_dist_of_ne (source_ne_target 0 e)
      exact dist_eq_one_iff_adj.mp (by have := h e; omega)
    have h01 : T.Adj (0 : Fin 3) 1 := all 0
    have h12 : T.Adj (1 : Fin 3) 2 := all 1
    have h20 : T.Adj (2 : Fin 3) 0 := all 2
    let p : T.Walk (0 : Fin 3) 2 := .cons h01 (.cons h12 .nil)
    have hp : p.IsPath := by
      rw [Walk.isPath_def]
      change [((0 : Fin 3)), 1, 2].Nodup
      decide
    have hq : (Walk.cons h20.symm Walk.nil).IsPath := by
      rw [Walk.isPath_def]
      change [((0 : Fin 3)), 2].Nodup
      decide
    have he := (hT.existsUnique_path _ _).unique hp hq
    have := congrArg Walk.length he
    change 2 = 1 at this
    omega
  | succ d ih =>
    classical
    change SimpleGraph (TwoTreeV d ⊕ TwoTreeFrontier d) at T
    let s := twoTreeSource d
    let t := twoTreeTarget d
    let choice (e : TwoTreeFrontier d) : TwoTreeV d :=
      if T.Adj (.inr e) (.inl (s e)) then s e else t e
    let f : TwoTreeV d ⊕ TwoTreeFrontier d → TwoTreeV d := Sum.elim id choice
    have hadj (e : TwoTreeFrontier d) : T.Adj (.inr e) (.inl (choice e)) := by
      haveI : Nontrivial (TwoTreeV d ⊕ TwoTreeFrontier d) :=
        ⟨⟨.inl (s e), .inl (t e), fun h => source_ne_target d e (Sum.inl.inj h)⟩⟩
      obtain ⟨v, hv⟩ := hT.connected.preconnected.exists_adj_of_nontrivial (.inr e)
      cases v with
      | inr j => exact False.elim (hsub hv)
      | inl u =>
        have hu : u = s e ∨ u = t e := hsub hv
        by_cases hs : T.Adj (.inr e) (.inl (s e))
        · simpa [choice, hs] using hs
        · rcases hu with rfl | rfl
          · contradiction
          · simpa [choice, hs] using hv
    have hm : T.map f ≤ twoTree d := by
      intro a b hab
      obtain ⟨hne, u, v, huv, rfl, rfl⟩ := (map_adj' f T a b).mp hab
      have mixed (u : TwoTreeV d) (e : TwoTreeFrontier d)
          (hu : u = s e ∨ u = t e) (hn : u ≠ choice e) :
          (twoTree d).Adj u (choice e) := by
        have hp : choice e = s e ∨ choice e = t e := by unfold choice; split <;> simp
        rcases hu with rfl | rfl <;> rcases hp with he | he
        · exact (hn he.symm).elim
        · rw [he]; exact frontier_adj d e
        · rw [he]; exact (frontier_adj d e).symm
        · exact (hn he.symm).elim
      rcases u with u | e <;> rcases v with v | j
      · exact hsub huv
      · exact mixed u j (hsub huv) hne
      · exact (mixed v e (hsub huv) hne.symm).symm
      · exact False.elim (hsub huv)
    have hMt : (T.map f).IsTree := quotient_isTree hT f Sum.inl (fun _ => rfl)
      (by rintro (u | e); exacts [Or.inl rfl, Or.inr (hadj e)])
    obtain ⟨e, he⟩ := ih (T.map f) hm hMt
    have short (u v : TwoTreeV d) : (T.map f).dist u v ≤ T.dist (.inl u) (.inl v) := by
      obtain ⟨p, hp⟩ := hT.connected.exists_walk_length_eq_dist (.inl u) (.inl v)
      exact ((T.map f).dist_le (quotientWalk f p)).trans ((quotientWalk_length f p).trans_eq hp)
    have hn : ¬(T.map f).Adj (s e) (t e) := fun h => by
      have := dist_eq_one_iff_adj.mpr h
      change d + 2 ≤ (T.map f).dist (s e) (t e) at he
      omega
    have only (v : TwoTreeV d ⊕ TwoTreeFrontier d) (hv : T.Adj (.inr e) v) :
        v = .inl (choice e) := by
      cases v with
      | inr j => exact False.elim (hsub hv)
      | inl u =>
        by_contra! hne
        have hne' : choice e ≠ u := fun h => hne (congrArg Sum.inl h.symm)
        have adj : (T.map f).Adj (choice e) u := map_adj_apply' hv hne'
        have hc : choice e = s e ∨ choice e = t e := by unfold choice; split <;> simp
        have hu : u = s e ∨ u = t e := hsub hv
        rcases hc with hc | hc <;> rcases hu with hu | hu
        · exact hne' (hc.trans hu.symm)
        · exact hn (hc ▸ hu ▸ adj)
        · exact hn (hu ▸ hc ▸ adj.symm)
        · exact hne' (hc.trans hu.symm)
    have hlong : d + 2 ≤ T.dist (.inl (s e)) (.inl (t e)) := he.trans (short (s e) (t e))
    by_cases hc : T.Adj (.inr e) (.inl (s e))
    · refine ⟨(e, true), ?_⟩
      have h := leaf_dist hT.connected (show (Sum.inr e : TwoTreeV (d + 1)) ≠ .inl (t e)
        from Sum.inr_ne_inl) only
      change d + 1 + 2 ≤ T.dist (.inr e) (.inl (t e))
      have : choice e = s e := if_pos hc
      rw [this] at h
      omega
    · refine ⟨(e, false), ?_⟩
      have h := leaf_dist hT.connected (show (Sum.inr e : TwoTreeV (d + 1)) ≠ .inl (s e)
        from Sum.inr_ne_inl) only
      change d + 1 + 2 ≤ T.dist (.inl (s e)) (.inr e)
      have : choice e = t e := if_neg hc
      rw [this, dist_comm (G := T) (u := .inl (t e))] at h
      rw [dist_comm]
      omega

private theorem attach_leaf_card {V I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (s : I → V) :
    Nat.card (twoTreeAttach G s s).edgeSet = Nat.card G.edgeSet + Fintype.card I := by
  rw [← Nat.card_congr (twoTreeAttachEdges G s s), Nat.card_sum]
  let e : I ≃ (Σ i : I, {u : V // u = s i ∨ u = s i}) :=
    { toFun := fun i => ⟨i, s i, Or.inl rfl⟩
      invFun := Sigma.fst
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨i, _, rfl | rfl⟩ <;> rfl }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card (α := I)]

/-- The three initial edges persist, and each insertion contributes two more edges. -/
theorem twoTree_edge_count (d : ℕ) :
    Nat.card (twoTree d).edgeSet = 3 * (2 ^ (d + 1) - 1) := by
  rw [← Nat.card_congr (twoTreeEdgeIdentification d).equiv]
  induction d with
  | zero => rw [Nat.card_eq_fintype_card]; decide
  | succ d ih =>
    change Nat.card (TwoTreeEdges d ⊕ (TwoTreeFrontier d × Bool)) = _
    rw [Nat.card_sum, Nat.card_prod, ih, Nat.card_eq_fintype_card (α := TwoTreeFrontier d),
      frontier_card, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
      pow_succ 2 (d + 1), pow_succ 2 d]
    have : 0 < 2 ^ d := Nat.two_pow_pos d
    omega
private theorem exists_stretch_upper (d : ℕ) :
    ∃ T ≤ twoTree d, T.IsTree ∧
      ∀ u v, (twoTree d).Adj u v → T.edist u v ≤ (d + 2 : ℕ) := by
  induction d with
  | zero =>
    let T := pathGraph 3
    refine ⟨T, le_top, isTree_pathGraph_add_one 2, ?_⟩
    intro u v _
    have h01 : T.Adj 0 1 := by decide
    have h12 : T.Adj 1 2 := by decide
    have B (u : Fin 3) : T.edist u 1 ≤ 1 := by
      fin_cases u
      · exact le_of_eq (edist_eq_one_iff_adj.mpr h01)
      · exact by simp
      · exact le_of_eq (edist_eq_one_iff_adj.mpr h12.symm)
    have h := T.edist_triangle (u := u) (v := (1 : Fin 3)) (w := v)
    rw [edist_comm (G := T) (u := (1 : Fin 3)) (v := v)] at h
    apply h.trans
    have htwo : (1 : ℕ∞) + 1 = 2 := by norm_num
    change _ ≤ (2 : ℕ∞)
    simpa only [htwo] using add_le_add (B u) (B v)
  | succ d ih =>
    obtain ⟨T, hTG, hT, hbound⟩ := ih
    let s := twoTreeSource d
    let t := twoTreeTarget d
    let S := twoTreeAttach T s s
    have hS : S.IsTree := by
      refine isTree_iff_connected_and_card.mpr ⟨attach_connected hT.connected, ?_⟩
      rw [attach_leaf_card, Nat.card_sum, Nat.card_eq_fintype_card (α := TwoTreeFrontier d),
        ← (isTree_iff_connected_and_card.mp hT).2]
      omega
    refine ⟨S, ?_, hS, ?_⟩
    · rintro (u | e) (v | j) h
      · exact hTG h
      · exact Or.inl (h.elim id id)
      · exact Or.inl (h.elim id id)
      · exact h.elim
    have old (u v : TwoTreeV d) : S.edist (.inl u) (.inl v) ≤ T.edist u v := by
      obtain ⟨p, hp⟩ := hT.connected.exists_walk_length_eq_edist u v
      rw [← hp, ← p.length_map (attachOld T s s).toHom]
      exact S.edist_le _
    have fresh (e : TwoTreeFrontier d) (u : TwoTreeV d)
        (h : u = s e ∨ u = t e) : S.edist (.inl u) (.inr e) ≤ (d + 1 + 2 : ℕ) := by
      have ha : S.Adj (.inl (s e)) (.inr e) := Or.inl rfl
      rcases h with rfl | rfl
      · rw [edist_eq_one_iff_adj.mpr ha]
        exact_mod_cast (show 1 ≤ d + 1 + 2 by omega)
      · apply (S.edist_triangle (v := .inl (s e))).trans
        rw [edist_eq_one_iff_adj.mpr ha]
        have hb := (old (t e) (s e)).trans (hbound _ _ (frontier_adj d e).symm)
        refine (add_le_add_left hb (1 : ℕ∞)).trans_eq ?_
        norm_cast
    rintro (u | e) (v | j) h
    · exact ((old u v).trans (hbound _ _ h)).trans (by exact_mod_cast (show d + 2 ≤ d + 1 + 2 by omega))
    · exact fresh j u h
    · rw [edist_comm]
      exact fresh e v h
    · exact h.elim

/-- Every spanning tree stretches some edge by at least `d+2`, and a spanning tree attains
this bound on all graph edges. -/
theorem twoTree_min_spanning_tree_stretch_eq (d : ℕ) :
    (∀ T ≤ twoTree d, T.IsTree →
      ∃ u v, (twoTree d).Adj u v ∧ (d + 2 : ℕ) ≤ T.edist u v) ∧
    (∃ T ≤ twoTree d, T.IsTree ∧
      ∀ u v, (twoTree d).Adj u v → T.edist u v ≤ (d + 2 : ℕ)) := by
  refine ⟨?_, exists_stretch_upper d⟩
  intro T hTG hT
  obtain ⟨e, he⟩ := frontier_stretch_lower d T hTG hT
  refine ⟨_, _, frontier_adj d e, ?_⟩
  rw [← (hT.connected _ _).coe_dist_eq_edist]
  exact_mod_cast he

private theorem triangle_count (d : ℕ) : Fintype.card (TwoTreeTriangles d) + 2 = 3 * 2 ^ d := by
  induction d with
  | zero => decide
  | succ d ih =>
    change Fintype.card (TwoTreeTriangles d ⊕ TwoTreeFrontier d) + 2 = _
    rw [Fintype.card_sum, frontier_card, pow_succ]
    omega

private theorem triangleGain_reverse {E : Type*} [AddCommGroup E] (d : ℕ)
    (τ : TwoTreeTriangles d → E) (u v : TwoTreeV d) :
    twoTreeTriangleGain d τ v u = -twoTreeTriangleGain d τ u v := by
  classical
  induction d with
  | zero =>
    change Fin 3 at u v
    fin_cases u <;> fin_cases v <;> simp [twoTreeTriangleGain]
  | succ d ih =>
    rcases u with u | e <;> rcases v with v | j
    · exact ih (τ ∘ Sum.inl) u v
    · simp [twoTreeTriangleGain, twoTreeInsertionGain]; split <;> simp
    · simp [twoTreeTriangleGain, twoTreeInsertionGain]; split <;> simp
    · simp [twoTreeTriangleGain, twoTreeInsertionGain]
private theorem triangleGain_sum {E : Type*} [AddCommGroup E] (d : ℕ)
    (τ : TwoTreeTriangles d → E) (i : TwoTreeTriangles d) :
    twoTreeTriangleSum d (twoTreeTriangleGain d τ) i = τ i := by
  classical
  induction d with
  | zero =>
    cases i
    simp [twoTreeTriangleSum, twoTreeOrientedTriangle, twoTreeTriangleGain]
  | succ d ih =>
    rcases i with i | e
    · have h := ih (τ ∘ Sum.inl) i
      cases twoTreeOrientedTriangle d i with
      | mk a bc =>
        cases bc
        simpa [twoTreeOrientedTriangle, twoTreeTriangleSum, twoTreeTriangleGain,
          twoTreeInsertionGain] using h
    · simp [twoTreeTriangleSum, twoTreeOrientedTriangle, twoTreeTriangleGain,
        twoTreeInsertionGain, (source_ne_target d e).symm,
        triangleGain_reverse d (τ ∘ Sum.inl) (twoTreeSource d e) (twoTreeTarget d e)] <;> abel

private theorem triangleGain_flat {E : Type*} [SeminormedAddCommGroup E] (d : ℕ)
    (τ : TwoTreeTriangles d → E) {ε : ℝ} (hτ : ∀ i, ‖τ i‖ ≤ ε) :
    ∀ u v w, (twoTree d).Adj u v → (twoTree d).Adj v w → (twoTree d).Adj u w →
      ‖twoTreeTriangleGain d τ u v + twoTreeTriangleGain d τ v w -
        twoTreeTriangleGain d τ u w‖ ≤ ε := by
  classical
  induction d with
  | zero =>
    intro u v w huv hvw huw
    change Fin 3 at u v w
    fin_cases u <;> fin_cases v <;> fin_cases w
    all_goals first
      | exact (huv.ne rfl).elim
      | exact (hvw.ne rfl).elim
      | exact (huw.ne rfl).elim
      | simpa [twoTreeTriangleGain] using hτ ()
  | succ d ih =>
    let g := twoTreeTriangleGain d (τ ∘ Sum.inl)
    let s := twoTreeSource d
    let t := twoTreeTarget d
    have parents (e : TwoTreeFrontier d) {u v : TwoTreeV d}
        (hu : u = s e ∨ u = t e) (hv : v = s e ∨ v = t e) (hn : u ≠ v) :
        (u = s e ∧ v = t e) ∨ (u = t e ∧ v = s e) := by
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact (hn rfl).elim
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact (hn rfl).elim
    have calcTri (e : TwoTreeFrontier d) :
        ‖g (s e) (t e) + -(g (s e) (t e) + τ (.inr e))‖ ≤ ε := by
      rw [show g (s e) (t e) + -(g (s e) (t e) + τ (.inr e)) = -τ (.inr e) by abel,
        norm_neg]
      exact hτ (.inr e)
    have reverse (e : TwoTreeFrontier d) : g (t e) (s e) = -g (s e) (t e) :=
      triangleGain_reverse d _ _ _
    have distinct (e : TwoTreeFrontier d) : t e ≠ s e := (source_ne_target d e).symm
    rintro (u | a) (v | b) (w | c) huv hvw huw
    · exact ih (τ ∘ Sum.inl) (fun i => hτ (.inl i)) _ _ _ huv hvw huw
    · rcases parents c huw hvw (show (twoTree d).Adj u v from huv).ne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa [twoTreeTriangleGain, twoTreeInsertionGain, g, s, t, distinct] using calcTri c
      · rw [show twoTreeTriangleGain (d + 1) τ (.inl (t c)) (.inl (s c)) =
          -g (s c) (t c) from reverse c]
        simp [twoTreeTriangleGain, twoTreeInsertionGain, g, s, t, distinct]
        simpa [g, s, t, add_comm] using hτ (.inr c)
    · rcases parents b huv hvw (show (twoTree d).Adj u w from huw).ne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa [twoTreeTriangleGain, twoTreeInsertionGain, g, s, t, distinct] using hτ (.inr b)
      · rw [show twoTreeTriangleGain (d + 1) τ (.inl (t b)) (.inl (s b)) =
          -g (s b) (t b) from reverse b]
        simp [twoTreeTriangleGain, twoTreeInsertionGain, g, s, t, distinct]
        simpa [add_comm] using hτ (.inr b)
    · exact hvw.elim
    · rcases parents a huv huw (show (twoTree d).Adj v w from hvw).ne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa [twoTreeTriangleGain, twoTreeInsertionGain, g, s, t, distinct] using calcTri a
      · rw [show twoTreeTriangleGain (d + 1) τ (.inl (t a)) (.inl (s a)) =
          -g (s a) (t a) from reverse a]
        simp [twoTreeTriangleGain, twoTreeInsertionGain, g, s, t, distinct]
        simpa [add_comm] using hτ (.inr a)
    · exact huw.elim
    · exact huv.elim
    · exact huv.elim
private theorem residual_frontier_sum {E : Type*} [AddCommGroup E] (d : ℕ)
    (τ : TwoTreeTriangles d → E) (φ : TwoTreeV d → E) :
    ∑ e : TwoTreeFrontier d,
      (twoTreeTriangleGain d τ (twoTreeSource d e) (twoTreeTarget d e) -
        (φ (twoTreeTarget d e) - φ (twoTreeSource d e))) = ∑ i, τ i := by
  classical
  induction d with
  | zero =>
    change ∑ e : Fin 3, _ = ∑ i : Unit, τ i
    rw [Fin.sum_univ_three]
    simp [twoTreeSource, twoTreeTarget, twoTreeTriangleGain,
      show (1 : Fin 3) + 1 = 2 by decide, show (2 : Fin 3) + 1 = 0 by decide] <;> abel
  | succ d ih =>
    change ∑ e : TwoTreeFrontier d × Bool, _ = ∑ i : TwoTreeTriangles d ⊕ TwoTreeFrontier d, τ i
    rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
    have pointwise (e : TwoTreeFrontier d) :
        ∑ b : Bool, (twoTreeTriangleGain (d + 1) τ (twoTreeSource (d + 1) (e,b))
          (twoTreeTarget (d + 1) (e,b)) -
          (φ (twoTreeTarget (d + 1) (e,b)) - φ (twoTreeSource (d + 1) (e,b)))) =
        (twoTreeTriangleGain d (τ ∘ Sum.inl) (twoTreeSource d e) (twoTreeTarget d e) -
          (φ (.inl (twoTreeTarget d e)) - φ (.inl (twoTreeSource d e)))) + τ (.inr e) := by
      rw [Fintype.sum_bool]
      simp [twoTreeSource, twoTreeTarget, twoTreeTriangleGain, twoTreeInsertionGain,
        (source_ne_target d e).symm]
      abel
    simp_rw [pointwise]
    rw [Finset.sum_add_distrib]
    have hold := ih (τ ∘ Sum.inl) (φ ∘ Sum.inl)
    simp only [Function.comp_apply] at hold
    rw [hold]

/-- Integral gains with triangle defects at most one can force an edge error of at least one. -/
theorem twoTree_integer_lower_bound_one (d : ℕ) :
    ∃ g : TwoTreeV d → TwoTreeV d → ℤ,
      (∀ u v, (twoTree d).Adj u v → g v u = -g u v) ∧
      (∀ u v w, (twoTree d).Adj u v → (twoTree d).Adj v w → (twoTree d).Adj u w →
        ‖g u v + g v w - g u w‖ ≤ 1) ∧
      (∀ φ : TwoTreeV d → ℤ, ∃ u v, (twoTree d).Adj u v ∧
        1 ≤ ‖g u v - (φ v - φ u)‖) := by
  let τ : TwoTreeTriangles d → ℤ := fun _ => 1
  let g := twoTreeTriangleGain d τ
  refine ⟨g, fun u v _ => triangleGain_reverse d τ u v,
    triangleGain_flat d τ (by simp [τ]), ?_⟩
  intro φ
  by_contra! h
  have hz (e : TwoTreeFrontier d) :
      g (twoTreeSource d e) (twoTreeTarget d e) -
        (φ (twoTreeTarget d e) - φ (twoTreeSource d e)) = 0 := by
    have hh := h _ _ (frontier_adj d e)
    rw [Int.norm_eq_abs, abs_lt] at hh
    let n := g (twoTreeSource d e) (twoTreeTarget d e) -
      (φ (twoTreeTarget d e) - φ (twoTreeSource d e))
    have hl : (-1 : ℤ) < n := by exact_mod_cast hh.1
    have hu : n < (1 : ℤ) := by exact_mod_cast hh.2
    show n = 0
    omega
  have hsum := residual_frontier_sum d τ φ
  change ∑ e : TwoTreeFrontier d, (g (twoTreeSource d e) (twoTreeTarget d e) -
    (φ (twoTreeTarget d e) - φ (twoTreeSource d e))) = _ at hsum
  simp only [hz, Finset.sum_const_zero, τ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hsum
  have hc := triangle_count d
  have hp := Nat.two_pow_pos d
  omega

/-- The real cycle coordinates in the basis of insertion triangles and the core triangle,
with the sum of absolute values as norm. -/
abbrev TwoTreeCycles (d : ℕ) := PiLp 1 (fun _ : TwoTreeTriangles d => ℝ)

/-- The gain whose oriented triangle sums are the unit cycle coordinates. -/
noncomputable def twoTreeCanonicalGain (d : ℕ) : TwoTreeV d → TwoTreeV d → TwoTreeCycles d :=
  by classical exact twoTreeTriangleGain d (fun i => PiLp.single 1 i 1)

/-- The canonical gain valued in signed circulations. -/
noncomputable def twoTreeCanonicalCirculationGain (d : ℕ) :
    TwoTreeV d → TwoTreeV d → TwoTreeCirculation ℝ d :=
  twoTreeTriangleGain d (twoTreeTriangleChain ℝ d)

private theorem map_triangle_gain {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    (L : E →+ F) (d : ℕ) (τ : TwoTreeTriangles d → E) (u v : TwoTreeV d) :
    L (twoTreeTriangleGain d τ u v) = twoTreeTriangleGain d (L ∘ τ) u v := by
  classical
  induction d with
  | zero =>
    simp only [twoTreeTriangleGain]
    split
    · rfl
    · split <;> simp [Function.comp_apply]
  | succ d ih =>
    rcases u with u | e <;> rcases v with v | j
    · exact ih (τ ∘ Sum.inl) u v
    · simp only [twoTreeTriangleGain, twoTreeInsertionGain]
      split <;> simp [ih] <;> rfl
    · simp only [twoTreeTriangleGain, twoTreeInsertionGain]
      split <;> simp [ih] <;> rfl
    · simp [twoTreeTriangleGain, twoTreeInsertionGain]

private theorem canonical_circulation_pairing (d : ℕ) (z : TwoTreeCirculation ℝ d) :
    (∑ e, z.val e • twoTreeCanonicalCirculationGain d (twoTreeEdgeSource d e)
      (twoTreeEdgeTarget d e)) = z := by
  classical
  change (∑ e, z.val e • twoTreeTriangleGain d (twoTreeTriangleChain ℝ d)
    (twoTreeEdgeSource d e) (twoTreeEdgeTarget d e)) = z
  rw [twoTree_triangle_gain_pairing]
  apply (twoTreeCirculationCoordinates ℝ d).injective
  funext i
  simp only [map_sum, map_smul, twoTree_triangle_chain_coordinate, Finset.sum_apply,
    Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

private theorem coordinates_canonical_gain (d : ℕ) (u v : TwoTreeV d) :
    (twoTreeCirculationCoordinates ℝ d) (twoTreeCanonicalCirculationGain d u v) =
      (twoTreeCanonicalGain d u v).ofLp := by
  classical
  let L := (twoTreeCirculationCoordinates ℝ d).toLinearMap.toAddMonoidHom
  change L (twoTreeTriangleGain d (twoTreeTriangleChain ℝ d) u v) = _
  rw [map_triangle_gain]
  have hτ : L ∘ twoTreeTriangleChain ℝ d = fun i => Pi.single i (1 : ℝ) := by
    funext i
    exact twoTree_triangle_chain_coordinate ℝ d i
  rw [hτ]
  let L' := (WithLp.linearEquiv 1 ℝ (TwoTreeTriangles d → ℝ)).toLinearMap.toAddMonoidHom
  exact (map_triangle_gain L' d (fun i => PiLp.single 1 i 1) u v).symm

private theorem filling_residual (d : ℕ) (p : TwoTreeV d → TwoTreeCirculation ℝ d)
    (u v : TwoTreeV d) :
    twoTreeFillingNorm d (twoTreeCanonicalCirculationGain d u v - (p v - p u)) =
      ‖twoTreeCanonicalGain d u v -
        (WithLp.toLp 1 (twoTreeCirculationCoordinates ℝ d (p v)) -
          WithLp.toLp 1 (twoTreeCirculationCoordinates ℝ d (p u)))‖ := by
  rw [twoTree_filling_norm_eq, map_sub, map_sub, coordinates_canonical_gain]
  rfl

/-- The optimal real Banach reconstruction constant for depth `d`. -/
def twoTreeBanachConstant (d : ℕ) : ℝ := 1 - 2 / (3 * 2 ^ d)
private theorem constant_succ (d : ℕ) :
    twoTreeBanachConstant (d + 1) = (twoTreeBanachConstant d + 1) / 2 := by
  unfold twoTreeBanachConstant
  rw [pow_succ]
  field_simp <;> ring
private theorem additive_reverse_error {V E : Type*} [SeminormedAddCommGroup E]
    {g : V → V → E} {φ : V → E} {a b : V} {r : ℝ} (hrev : g b a = -g a b)
    (h : ‖g a b - (φ b - φ a)‖ ≤ r) : ‖g b a - (φ a - φ b)‖ ≤ r := by
  rw [hrev, show -g a b - (φ a - φ b) = -(g a b - (φ b - φ a)) by abel, norm_neg]
  exact h
private theorem banach_upper {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (g : TwoTreeV d → TwoTreeV d → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ u v, (twoTree d).Adj u v → g v u = -g u v)
    (htri : ∀ u v w, (twoTree d).Adj u v → (twoTree d).Adj v w → (twoTree d).Adj u w →
      ‖g u v + g v w - g u w‖ ≤ ε) :
    ∃ φ : TwoTreeV d → E, ∀ u v, (twoTree d).Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ twoTreeBanachConstant d * ε := by
  induction d with
  | zero =>
    let r := (1 / 3 : ℝ) • (g 0 1 + g 1 2 - g 0 2)
    let φ : TwoTreeV 0 → E := fun u => if (u : Fin 3) = 0 then 0 else
      if (u : Fin 3) = 1 then g 0 1 - r else g 0 1 + g 1 2 - (2 : ℝ) • r
    have hr : ‖r‖ ≤ twoTreeBanachConstant 0 * ε := by
      simp only [r, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)]
      norm_num [twoTreeBanachConstant]
      exact htri 0 1 2 (by decide) (by decide) (by decide)
    have h01 : ‖g 0 1 - (φ 1 - φ 0)‖ ≤ twoTreeBanachConstant 0 * ε := by
      simpa [φ] using hr
    have h12 : ‖g 1 2 - (φ 2 - φ 1)‖ ≤ twoTreeBanachConstant 0 * ε := by
      convert hr using 2
      simp [φ]
      module
    have h02 : ‖g 0 2 - (φ 2 - φ 0)‖ ≤ twoTreeBanachConstant 0 * ε := by
      rw [← norm_neg r] at hr
      convert hr using 2
      simp [φ, r]
      module
    refine ⟨φ, fun u v h => ?_⟩
    change Fin 3 at u v
    fin_cases u <;> fin_cases v
    · exact (h.ne rfl).elim
    · exact h01
    · exact h02
    · exact additive_reverse_error (hrev 0 1 (by decide)) h01
    · exact (h.ne rfl).elim
    · exact h12
    · exact additive_reverse_error (hrev 0 2 (by decide)) h02
    · exact additive_reverse_error (hrev 1 2 (by decide)) h12
    · exact (h.ne rfl).elim
  | succ d ih =>
    obtain ⟨ψ, hψ⟩ := ih (fun u v => g (.inl u) (.inl v))
      (fun _ _ h => hrev _ _ h) (fun _ _ _ h₁ h₂ h₃ => htri _ _ _ h₁ h₂ h₃)
    let s := twoTreeSource d
    let t := twoTreeTarget d
    let fromSource (e : TwoTreeFrontier d) := ψ (s e) + g (.inl (s e)) (.inr e)
    let fromTarget (e : TwoTreeFrontier d) := ψ (t e) + g (.inl (t e)) (.inr e)
    let φ : TwoTreeV (d + 1) → E :=
      Sum.elim ψ fun e => (1 / 2 : ℝ) • (fromSource e + fromTarget e)
    have separation (e : TwoTreeFrontier d) :
        ‖fromTarget e - fromSource e‖ ≤ twoTreeBanachConstant d * ε + ε := by
      let a : TwoTreeV (d + 1) := .inl (s e)
      let b : TwoTreeV (d + 1) := .inl (t e)
      have ht := htri a b (.inr e) (frontier_adj d e) (Or.inr rfl) (Or.inl rfl)
      have ho := hψ (s e) (t e) (frontier_adj d e)
      have he : fromTarget e - fromSource e =
          -(g a b - (ψ (t e) - ψ (s e))) + (g a b + g b (.inr e) - g a (.inr e)) := by
        dsimp [fromSource, fromTarget, a, b]
        abel
      rw [he]
      refine (norm_add_le _ _).trans (add_le_add ?_ ht)
      rw [norm_neg]
      exact ho
    have half (e : TwoTreeFrontier d) :
        ‖(1 / 2 : ℝ) • (fromTarget e - fromSource e)‖ ≤ twoTreeBanachConstant (d + 1) * ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), constant_succ]
      refine (mul_le_mul_of_nonneg_left (separation e) (by norm_num)).trans_eq ?_
      ring
    have fresh (e : TwoTreeFrontier d) (u : TwoTreeV d) (h : u = s e ∨ u = t e) :
        ‖g (.inl u) (.inr e) - (φ (.inr e) - φ (.inl u))‖ ≤
          twoTreeBanachConstant (d + 1) * ε := by
      rcases h with rfl | rfl
      · have hh := half e
        rw [← norm_neg ((1 / 2 : ℝ) • (fromTarget e - fromSource e))] at hh
        convert hh using 2
        dsimp [φ, fromSource, fromTarget]
        module
      · convert half e using 2
        dsimp [φ, fromSource, fromTarget]
        module
    have hmono : twoTreeBanachConstant d ≤ twoTreeBanachConstant (d + 1) := by
      have h : twoTreeBanachConstant d ≤ 1 :=
        sub_le_self _ (div_nonneg (by norm_num) (by positivity))
      rw [constant_succ]
      linarith
    refine ⟨φ, ?_⟩
    rintro (u | e) (v | j) h
    · exact (hψ u v h).trans (mul_le_mul_of_nonneg_right hmono hε)
    · exact fresh j u h
    · exact additive_reverse_error (hrev _ _ h.symm) (fresh e v h)
    · exact h.elim

private theorem banach_coordinate_lower (d : ℕ) :
    ∀ φ : TwoTreeV d → TwoTreeCycles d, ∃ u v, (twoTree d).Adj u v ∧
      twoTreeBanachConstant d ≤ ‖twoTreeCanonicalGain d u v - (φ v - φ u)‖ := by
  classical
  let τ : TwoTreeTriangles d → TwoTreeCycles d := fun i => PiLp.single 1 i 1
  intro φ
  let r (e : TwoTreeFrontier d) := twoTreeTriangleGain d τ (twoTreeSource d e)
    (twoTreeTarget d e) - (φ (twoTreeTarget d e) - φ (twoTreeSource d e))
  have hsum : ∑ e, r e = ∑ i, τ i := residual_frontier_sum d τ φ
  have hnorm : ‖∑ i, τ i‖ = Fintype.card (TwoTreeTriangles d) := by
    rw [PiLp.norm_eq_sum (by simp : 0 < (1 : ℝ≥0∞).toReal)]
    let L := (WithLp.linearEquiv 1 ℝ (TwoTreeTriangles d → ℝ)).toLinearMap
    have coordinate (k : TwoTreeTriangles d) : (∑ i, τ i) k = 1 := by
      change L (∑ i, τ i) k = 1
      rw [map_sum, Finset.sum_apply]
      have eval (i : TwoTreeTriangles d) :
          L (τ i) k = (Pi.single i (1 : ℝ) : TwoTreeTriangles d → ℝ) k := rfl
      simp only [eval, Pi.single_apply]
      simp
    simp only [ENNReal.toReal_one, div_one, Real.rpow_one, coordinate, norm_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  by_contra! h
  have hlt : ∑ e, ‖r e‖ < (Fintype.card (TwoTreeFrontier d) : ℝ) * twoTreeBanachConstant d := by
    have he : Nonempty (TwoTreeFrontier d) := Fintype.card_pos_iff.mp (by rw [frontier_card]; positivity)
    have pointwise (e : TwoTreeFrontier d) : ‖r e‖ < twoTreeBanachConstant d :=
      h _ _ (frontier_adj d e)
    simpa [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_lt_sum_of_nonempty (s := Finset.univ) Finset.univ_nonempty
        (fun e _ => pointwise e))
  have hn := norm_sum_le (Finset.univ : Finset (TwoTreeFrontier d)) r
  rw [hsum, hnorm] at hn
  have hc := congrArg (fun n : ℕ => (n : ℝ)) (triangle_count d)
  push_cast at hc
  rw [frontier_card, Nat.cast_mul, Nat.cast_pow, twoTreeBanachConstant] at hlt
  have hp : (3 * (2 : ℝ) ^ d) ≠ 0 := by positivity
  have he : 3 * (2 : ℝ) ^ d * (1 - 2 / (3 * 2 ^ d)) = 3 * 2 ^ d - 2 := by
    field_simp
  norm_num only [Nat.cast_ofNat] at hlt
  rw [he] at hlt
  linarith

/-- The canonical cycle-space gain forces the stated bound on every potential. The same
bound times the triangle defect bound is attainable in every real normed space. -/
theorem twoTree_banach_exact_constant (d : ℕ) :
    (∀ u v, (twoTree d).Adj u v → twoTreeCanonicalGain d v u = -twoTreeCanonicalGain d u v) ∧
    (∀ u v w, (twoTree d).Adj u v → (twoTree d).Adj v w → (twoTree d).Adj u w →
      ‖twoTreeCanonicalGain d u v + twoTreeCanonicalGain d v w - twoTreeCanonicalGain d u w‖ ≤ 1) ∧
    (∀ φ : TwoTreeV d → TwoTreeCycles d, ∃ u v, (twoTree d).Adj u v ∧
      twoTreeBanachConstant d ≤ ‖twoTreeCanonicalGain d u v - (φ v - φ u)‖) ∧
    (∀ {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
      (g : TwoTreeV d → TwoTreeV d → E) (ε : ℝ), 0 ≤ ε →
      (∀ u v, (twoTree d).Adj u v → g v u = -g u v) →
      (∀ u v w, (twoTree d).Adj u v → (twoTree d).Adj v w → (twoTree d).Adj u w →
        ‖g u v + g v w - g u w‖ ≤ ε) →
      ∃ φ : TwoTreeV d → E, ∀ u v, (twoTree d).Adj u v →
        ‖g u v - (φ v - φ u)‖ ≤ twoTreeBanachConstant d * ε) ∧
    (∀ z : TwoTreeCirculation ℝ d,
      (∑ e, z.val e • twoTreeCanonicalCirculationGain d (twoTreeEdgeSource d e)
        (twoTreeEdgeTarget d e)) = z) ∧
    (∀ φ : TwoTreeV d → TwoTreeCirculation ℝ d, ∃ u v, (twoTree d).Adj u v ∧
      twoTreeBanachConstant d ≤
        twoTreeFillingNorm d (twoTreeCanonicalCirculationGain d u v - (φ v - φ u))) ∧
    (∃ φ : TwoTreeV d → TwoTreeCirculation ℝ d, ∀ u v, (twoTree d).Adj u v →
      twoTreeFillingNorm d (twoTreeCanonicalCirculationGain d u v - (φ v - φ u)) ≤
        twoTreeBanachConstant d) ∧
    (∀ i : TwoTreeTriangles d, twoTreeTriangleSum d (twoTreeCanonicalGain d) i = PiLp.single 1 i 1) := by
  classical
  let τ : TwoTreeTriangles d → TwoTreeCycles d := fun i => PiLp.single 1 i 1
  have hrev (u v : TwoTreeV d) (_ : (twoTree d).Adj u v) :
      twoTreeCanonicalGain d v u = -twoTreeCanonicalGain d u v :=
    triangleGain_reverse d τ u v
  have hflat := triangleGain_flat d τ (by simp [τ] : ∀ i, ‖τ i‖ ≤ 1)
  refine ⟨hrev, hflat, banach_coordinate_lower d, banach_upper d,
    canonical_circulation_pairing d, ?_, ?_, triangleGain_sum d τ⟩
  · intro φ
    obtain ⟨u, v, huv, h⟩ := banach_coordinate_lower d
      (fun a => WithLp.toLp 1 (twoTreeCirculationCoordinates ℝ d (φ a)))
    exact ⟨u, v, huv, (filling_residual d φ u v).symm ▸ h⟩
  · obtain ⟨ψ, hψ⟩ := banach_upper d (twoTreeCanonicalGain d) 1 zero_le_one hrev hflat
    let φ (u : TwoTreeV d) := (twoTreeCirculationCoordinates ℝ d).symm (ψ u).ofLp
    refine ⟨φ, fun u v h => ?_⟩
    rw [filling_residual]
    simpa [φ] using hψ u v h

end
end SimpleGraph
