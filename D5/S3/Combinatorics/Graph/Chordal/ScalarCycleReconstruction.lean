/- GID: D5/S3/Combinatorics/Graph/Chordal/ScalarCycleReconstruction
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar potential bounds and obstructions from graph cycles. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.ChordalWalkHolonomy
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

compile_only_with_mathlib

/-! # Scalar potentials from cycle constraints -/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The sum of the oriented scalar weights of a walk. -/
def Walk.scalarWeight (w : V → V → ℝ) {a b : V} : G.Walk a b → ℝ
  | .nil => 0
  | @Walk.cons _ _ u v _ _ p => w u v + p.scalarWeight w

namespace Walk

@[simp] theorem scalarWeight_nil (w : V → V → ℝ) {a : V} :
    (nil : G.Walk a a).scalarWeight w = 0 := rfl

@[simp] theorem scalarWeight_cons (w : V → V → ℝ) {a b c : V} (h : G.Adj a b)
    (p : G.Walk b c) : (cons h p).scalarWeight w = w a b + p.scalarWeight w := rfl

@[simp] theorem scalarWeight_append (w : V → V → ℝ) {a b c : V}
    (p : G.Walk a b) (q : G.Walk b c) :
    (p.append q).scalarWeight w = p.scalarWeight w + q.scalarWeight w := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih, add_assoc]

@[simp] theorem scalarWeight_copy (w : V → V → ℝ) {a b a' b' : V}
    (p : G.Walk a b) (ha : a = a') (hb : b = b') :
    (p.copy ha hb).scalarWeight w = p.scalarWeight w := by
  subst a' b'
  rfl

/-- A scalar walk with a repeated vertex factors into a shorter walk and a closed walk.
The order of the scalar summands is irrelevant. -/
theorem exists_shorter_of_not_isPath (w : V → V → ℝ) {a b : V} (p : G.Walk a b)
    (hp : ¬p.IsPath) :
    ∃ (x : V) (c : G.Walk x x) (q : G.Walk a b), 0 < c.length ∧
      q.length + c.length = p.length ∧ p.scalarWeight w = q.scalarWeight w + c.scalarWeight w := by
  classical
  induction p with
  | nil => exact (hp (by simp)).elim
  | @cons a x b h p ih =>
    by_cases ha : a ∈ p.support
    · let c := cons h (p.takeUntil a ha)
      let q := p.dropUntil a ha
      refine ⟨a, c, q, by simp [c], ?_, ?_⟩
      · have hl := congrArg Walk.length (p.take_spec ha)
        simp only [length_append] at hl
        simp [q, c]
        omega
      · have hs := congrArg (Walk.scalarWeight w) (p.take_spec ha)
        simp only [scalarWeight_append] at hs
        simp only [q,c,scalarWeight_cons]
        linarith
    · have hnp : ¬p.IsPath := fun hh => hp ((cons_isPath_iff h p).2 ⟨hh, ha⟩)
      obtain ⟨y, c, q, hc, hlen, hw⟩ := ih hnp
      refine ⟨y, c, cons h q, hc, ?_, ?_⟩
      · simp only [length_cons]; omega
      · simp only [scalarWeight_cons]; linarith

/-- The closed-walk constraints follow from two-edge backtracks and simple cycles. -/
theorem scalarWeight_nonneg_of_cycles (w : V → V → ℝ)
    (hedge : ∀ a b, G.Adj a b → 0 ≤ w a b + w b a)
    (hcycle : ∀ (a : V) (p : G.Walk a a), p.IsCycle → 0 ≤ p.scalarWeight w)
    {a : V} (p : G.Walk a a) : 0 ≤ p.scalarWeight w := by
  classical
  suffices h : ∀ n (a : V) (p : G.Walk a a), p.length = n → 0 ≤ p.scalarWeight w by
    exact h p.length a p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a p hlen
    cases p with
    | nil => simp
    | @cons a x _ h q =>
      by_cases hq : q.IsPath
      · by_cases hmem : s(a, x) ∈ q.edges
        · have he : s(x, a) ∈ q.edges := Sym2.eq_swap ▸ hmem
          rw [hq.eq_adj_toWalk_of_mem_edges he]
          simpa [Adj.toWalk] using hedge a x h
        · exact hcycle a _ ((cons_isCycle_iff q h).2 ⟨hq, hmem⟩)
      · obtain ⟨y, c, q', hc, hsum, hw⟩ := q.exists_shorter_of_not_isPath w hq
        have hq' : (cons h q').length < n := by
          simp only [length_cons] at hlen ⊢
          omega
        have hc' : c.length < n := by
          simp only [length_cons] at hlen
          omega
        have he : (cons h q).scalarWeight w =
            (cons h q').scalarWeight w + c.scalarWeight w := by
          simp only [scalarWeight_cons]
          linarith
        rw [he]
        exact add_nonneg (ih _ hq' _ _ rfl) (ih _ hc' _ _ rfl)

end Walk

/-- The elementary difference-constraint construction by shortest walk weights.
The potential is an infimum and requires only a lower bound on closed walk weights. -/
theorem exists_scalar_potential_of_nonneg_closed_walks (w : V → V → ℝ)
    (hclosed : ∀ (a : V) (p : G.Walk a a), 0 ≤ p.scalarWeight w) :
    ∃ p : V → ℝ, ∀ a b, G.Adj a b → p b ≤ p a + w a b := by
  classical
  have local_fit (C : G.ConnectedComponent) :
      ∃ p : C → ℝ, ∀ a b : C, C.toSimpleGraph.Adj a b → p b ≤ p a + w a.val b.val := by
    let H := C.toSimpleGraph
    let f (a b : C) := w a.val b.val
    let embed : H →g G := (Embedding.induce C.supp).toHom
    have hmap {a b : C} (q : H.Walk a b) : (q.map embed).scalarWeight w = q.scalarWeight f := by
      induction q with
      | nil => rfl
      | cons h q ih => simp [ih]; rfl
    obtain ⟨o, ho⟩ := C.nonempty_supp
    let root : C := ⟨o, ho⟩
    let values (a : C) := Set.range (fun q : H.Walk root a => q.scalarWeight f)
    have hnon (a : C) : (values a).Nonempty :=
      ⟨_, (C.connected_toSimpleGraph root a).some, rfl⟩
    have hbdd (a : C) : BddBelow (values a) := by
      let q : H.Walk a root := (C.connected_toSimpleGraph a root).some
      refine ⟨-q.scalarWeight f, ?_⟩
      rintro _ ⟨p, rfl⟩
      have hs := hclosed o ((p.append q).map embed)
      have hh := hmap (p.append q)
      rw [Walk.scalarWeight_append] at hh
      change -q.scalarWeight f ≤ p.scalarWeight f
      have hn : 0 ≤ p.scalarWeight f + q.scalarWeight f := hh ▸ hs
      linarith only [hn]
    refine ⟨fun a => sInf (values a), fun a b h => ?_⟩
    change sInf (values b) ≤ sInf (values a) + w a.val b.val
    apply (sub_le_iff_le_add).mp
    apply le_csInf (hnon a)
    rintro _ ⟨q, rfl⟩
    have h₁ : sInf (values b) ≤ (q.append h.toWalk).scalarWeight f :=
      csInf_le (hbdd b) ⟨q.append h.toWalk, rfl⟩
    simpa [Adj.toWalk, f, sub_le_iff_le_add] using h₁
  choose p hp using local_fit
  let φ (a : V) := p (G.connectedComponentMk a) ⟨a, ConnectedComponent.connectedComponentMk_mem⟩
  refine ⟨φ, fun a b hab => ?_⟩
  have he := ConnectedComponent.connectedComponentMk_eq_of_adj hab.symm
  have he' (x : V) (C : G.ConnectedComponent) (h : G.connectedComponentMk x = C) :
      φ x = p C ⟨x, h ▸ ConnectedComponent.connectedComponentMk_mem⟩ := by subst C; rfl
  rw [he' b _ he]
  exact hp (G.connectedComponentMk a) ⟨a, rfl⟩ ⟨b, he⟩ hab


private theorem weight_of_const {w : V → V → ℝ} {a b : V} (p : G.Walk a b) (M : ℝ)
    (h : ∀ i, i < p.length → w (p.getVert i) (p.getVert (i + 1)) = M) :
    p.scalarWeight w = p.length * M := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    have h₀ := h 0 (by simp)
    have h₀' : w a b = M := by simpa [Walk.getVert_cons_succ] using h₀
    have ht (i : ℕ) (hi : i < p.length) :
        w (p.getVert i) (p.getVert (i + 1)) = M := by
      have hh := h (i + 1) (by simpa using hi)
      simpa only [Walk.getVert_cons_succ] using hh
    simp only [Walk.scalarWeight_cons, h₀', ih ht, Walk.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

private theorem weight_telescope_le {w : V → V → ℝ} {a b : V} (p : G.Walk a b)
    (φ : V → ℝ) (M : ℝ) (h : ∀ i j, G.Adj i j → w i j - (φ j - φ i) ≤ M) :
    p.scalarWeight w - (φ b - φ a) ≤ p.length * M := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    simp only [Walk.scalarWeight_cons, Walk.length_cons, Nat.cast_add, Nat.cast_one]
    linarith [h a b hab]

private def orderedGain (r : V → ℕ) (v w : V) : ℝ :=
  if r v < r w then 1 else if r w < r v then -1 else 0

private theorem orderedGain_skew (r : V → ℕ) (v w : V) :
    orderedGain r w v = -orderedGain r v w := by
  rcases lt_trichotomy (r v) (r w) with h | h | h
  · simp [orderedGain, h, h.not_gt]
  · simp [orderedGain, h]
  · simp [orderedGain, h, h.not_gt]

private theorem orderedGain_flat (r : V → ℕ) (v w x : V) :
    |orderedGain r v w + orderedGain r w x - orderedGain r v x| ≤ 1 := by
  unfold orderedGain
  split_ifs <;> norm_num <;> omega

/-- Any simple cycle gives the scalar lower bound, witnessed by gains from its cyclic ordering.
Chordality is needed for the matching upper bound, and this direction applies to every graph. -/
theorem Walk.IsCycle.exists_scalar_gain_obstruction {a : V} {c : G.Walk a a} (hc : c.IsCycle) :
    ∃ g : V → V → ℝ, (∀ v w, g w v = -g v w) ∧
      (∀ v w x, |g v w + g w x - g v x| ≤ 1) ∧
      ∀ φ : V → ℝ, ∃ v w, G.Adj v w ∧
        1 - 2 / (c.length : ℝ) ≤ |g v w - (φ w - φ v)| := by
  classical
  let p := c.dropLast
  let r (v : V) := p.support.idxOf v
  let g := orderedGain r
  have hidx (i : ℕ) (hi : i ≤ p.length) : r (p.getVert i) = i := by
    rw [Walk.getVert_eq_support_getElem _ hi]
    exact hc.isPath_dropLast.support_nodup.idxOf_getElem i _
  have hinc (i : ℕ) (hi : i < p.length) : g (p.getVert i) (p.getVert (i+1)) = 1 := by
    have h : i < i + 1 := by omega
    simp [g, orderedGain, hidx i hi.le, hidx (i + 1) hi, h]
  have hlast := c.adj_penultimate hc.not_nil
  have hp0 : r a = 0 := by simpa using hidx 0 (Nat.zero_le _)
  have hpe : r c.penultimate = p.length := by
    simpa using hidx p.length (le_refl _)
  have hpos : 0 < p.length := by
    have := hc.three_le_length
    simp [p]
    omega
  have hlastg : g c.penultimate a = -1 := by
    simp [g, orderedGain, hp0, hpe, hpos]
  have hweight : c.scalarWeight g = (c.length : ℝ) - 2 := by
    calc
      c.scalarWeight g = (p.concat hlast).scalarWeight g := by rw [Walk.concat_dropLast hlast]
      _ = p.scalarWeight g + g c.penultimate a := by simp [Walk.concat]
      _ = _ := by
        rw [weight_of_const p 1 hinc, hlastg, mul_one]
        have he : p.length + 1 = c.length := c.length_dropLast_add_one hc.not_nil
        exact_mod_cast (show (p.length : ℤ) + -1 = (c.length : ℤ) - 2 by omega)
  refine ⟨g, orderedGain_skew r, orderedGain_flat r, fun φ => ?_⟩
  suffices ∃ v w, G.Adj v w ∧
      1 - 2 / (c.length : ℝ) ≤ g v w - (φ w - φ v) by
    obtain ⟨v, w, h, hr⟩ := this
    exact ⟨v, w, h, hr.trans (le_abs_self _)⟩
  by_contra! h
  let M := 1 - 2 / (c.length : ℝ)
  have hfail : ∀ v w, G.Adj v w → g v w - (φ w - φ v) < M := h
  have hupper := weight_telescope_le p φ M (fun v w h => (hfail v w h).le)
  have hstrict := hfail c.penultimate a hlast
  have htotal : p.scalarWeight g + g c.penultimate a < (c.length : ℝ) * M := by
    have he : (p.length : ℝ) + 1 = (c.length : ℝ) := by
      exact_mod_cast c.length_dropLast_add_one hc.not_nil
    rw [← he, add_mul, one_mul]
    linarith only [hupper, hstrict]
  have hsplit : c.scalarWeight g = p.scalarWeight g + g c.penultimate a := by
    conv_lhs => rw [← Walk.concat_dropLast hlast]
    simp [Walk.concat, p]
  rw [← hsplit, hweight] at htotal
  have hlen : (c.length : ℝ) ≠ 0 := by exact_mod_cast (show c.length ≠ 0 by have := hc.three_le_length; omega)
  have hM : (c.length : ℝ) * M = (c.length : ℝ) - 2 := by
    dsimp [M]
    field_simp
  rw [hM] at htotal
  exact (lt_irrefl _) htotal

namespace ScalarCycleReconstruction

/-- An additive walk gain is its scalar walk weight. -/
theorem scalarGain_of_walk (g : V → V → ℝ) {a b : V} (p : G.Walk a b) :
    Multiplicative.toAdd (p.gain (fun v w => Multiplicative.ofAdd (g v w))) = p.scalarWeight g := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
    rw [Walk.gain_cons, Walk.scalarWeight_cons]
    change g a b + Multiplicative.toAdd (p.gain _) = g a b + p.scalarWeight g
    rw [ih]

private theorem scalar_triangle_product_abs (g : V → V → ℝ)
    (hrev : ∀ a b, G.Adj a b → g b a = -g a b)
    (hdef : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      |g a b + g b c - g a c| ≤ 1)
    {n : ℕ} {x : Multiplicative ℝ}
    (h : TriangleProduct G (fun v w => Multiplicative.ofAdd (g v w)) n x) :
    |Multiplicative.toAdd x| ≤ (n : ℝ) := by
  induction h with
  | one => simp
  | triangle a b c hab hbc hca =>
    simp only [Nat.cast_one]
    change |g a b + g b c + g c a| ≤ 1
    rw [hrev a c hca.symm, ← sub_eq_add_neg]
    exact hdef a b c hab hbc hca.symm
  | @mul m n x y _ _ hx hy =>
    change |Multiplicative.toAdd x + Multiplicative.toAdd y| ≤ ((m + n : ℕ) : ℝ)
    exact (abs_add_le _ _).trans (by exact_mod_cast add_le_add hx hy)
  | @conj n x z _ hx =>
    change |Multiplicative.toAdd z + Multiplicative.toAdd x + -Multiplicative.toAdd z| ≤ _
    rw [show Multiplicative.toAdd z + Multiplicative.toAdd x + -Multiplicative.toAdd z =
      Multiplicative.toAdd x by ring]
    exact hx

theorem scalarWeight_shift (g : V → V → ℝ) (M : ℝ) {a b : V} (p : G.Walk a b) :
    p.scalarWeight (fun v w => g v w + M) = p.scalarWeight g + (p.length : ℝ) * M := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    simp only [Walk.scalarWeight_cons, Walk.length_cons, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem cycle_abs_weight_le [Finite V] (hG : G.IsChordal)
    (g : V → V → ℝ) (hrev : ∀ a b, G.Adj a b → g b a = -g a b)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      |g a b + g b c - g a c| ≤ 1) {a : V} (p : G.Walk a a) (hp : p.IsCycle) :
    |p.scalarWeight g| ≤ (p.length : ℝ) - 2 := by
  obtain ⟨n, hn, hprod⟩ := hG.closed_walk_triangle_product
    (fun a b => Multiplicative.ofAdd (g a b)) (fun a b h => hrev a b h) p
  have hsum := scalar_triangle_product_abs g hrev htri hprod
  rw [scalarGain_of_walk] at hsum
  have hn' : (n : ℝ) ≤ ((p.length - 2 : ℕ) : ℝ) := by exact_mod_cast hn
  rw [Nat.cast_sub (show 2 ≤ p.length from (by decide : 2 ≤ 3).trans hp.three_le_length)] at hn'
  exact hsum.trans hn'

end ScalarCycleReconstruction

end SimpleGraph
