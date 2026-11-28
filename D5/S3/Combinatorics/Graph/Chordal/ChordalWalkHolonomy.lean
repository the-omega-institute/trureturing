/- GID: D5/S3/Combinatorics/Graph/Chordal/ChordalWalkHolonomy
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Triangle factorizations of closed walks and bi-invariant gain bounds. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.GainPotential
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith

compile_only_with_mathlib

/-!
Omega original.
# Chordal closed walks and bi-invariant gain reconstruction

The algebraic theorem counts conjugates of triangle holonomies, before imposing
any metric. Natural subtraction makes the bound valid also for walks of length
zero and two. All imports are public; no separation or completeness is assumed.
-/

namespace SimpleGraph

universe u v
variable {V : Type u} {H : Type v} [Group H] {G : SimpleGraph V}

/-- Ordered product of gains along a walk. -/
def Walk.gain (g : V → V → H) : {a b : V} → G.Walk a b → H
  | _, _, .nil => 1
  | a, _, .cons (v := b) _ p => g a b * p.gain g

@[simp] theorem Walk.gain_nil (g : V → V → H) (a : V) :
    (Walk.nil : G.Walk a a).gain g = 1 := rfl

@[simp] theorem Walk.gain_cons (g : V → V → H) {a b c : V}
    (h : G.Adj a b) (p : G.Walk b c) :
    (p.cons h).gain g = g a b * p.gain g := rfl

@[simp] theorem Walk.gain_append (g : V → V → H) {a b c : V}
    (p : G.Walk a b) (q : G.Walk b c) :
    (p.append q).gain g = p.gain g * q.gain g := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih, mul_assoc]

@[simp] theorem Walk.gain_concat (g : V → V → H) {a b c : V}
    (p : G.Walk a b) (h : G.Adj b c) :
    (p.concat h).gain g = p.gain g * g b c := by simp [Walk.concat]

theorem Walk.gain_reverse (g : V → V → H)
    (hrev : ∀ a b, G.Adj a b → g b a = (g a b)⁻¹)
    {a b : V} (p : G.Walk a b) : p.reverse.gain g = (p.gain g)⁻¹ := by
  induction p with
  | nil => simp
  | cons h p ih => simp [Walk.reverse_cons, ih, hrev _ _ h]

theorem Walk.gain_of_potential (g : V → V → H) (φ : V → H)
    (hφ : ∀ a b, G.Adj a b → g a b = (φ a)⁻¹ * φ b)
    {a b : V} (p : G.Walk a b) : p.gain g = (φ a)⁻¹ * φ b := by
  induction p with
  | nil => simp
  | cons h p ih => simp [hφ _ _ h, ih, mul_assoc]

theorem Walk.gain_rotate [DecidableEq V] (g : V → V → H)
    {a z : V} (p : G.Walk a a) (hz : z ∈ p.support) :
    p.gain g = (p.takeUntil z hz).gain g * (p.rotate z hz).gain g *
      ((p.takeUntil z hz).gain g)⁻¹ := by
  have he : p.gain g = (p.takeUntil z hz).gain g * (p.dropUntil z hz).gain g := by
    rw [← Walk.gain_append, Walk.take_spec]
  rw [Walk.rotate, Walk.gain_append, he]
  group

/-- A certificate with exactly `n` triangle factors. Conjugation costs no factors. -/
inductive TriangleProduct (G : SimpleGraph V) (g : V → V → H) : ℕ → H → Prop
  | one : TriangleProduct G g 0 1
  | triangle (a b c : V) (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
      TriangleProduct G g 1 (g a b * g b c * g c a)
  | mul {m n : ℕ} {x y : H} : TriangleProduct G g m x → TriangleProduct G g n y →
      TriangleProduct G g (m + n) (x * y)
  | conj {n : ℕ} {x : H} (a : H) : TriangleProduct G g n x →
      TriangleProduct G g n (a * x * a⁻¹)

/-- Certificates expand to an actual list of conjugated triangle holonomies. -/
theorem TriangleProduct.exists_factors {g : V → V → H} {n : ℕ} {x : H}
    (h : TriangleProduct G g n x) :
    ∃ l : List H, l.length = n ∧ l.prod = x ∧ ∀ y ∈ l,
      ∃ (a b c : V) (q : H), G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        y = q * (g a b * g b c * g c a) * q⁻¹ := by
  induction h with
  | one => exact ⟨[], rfl, rfl, by simp⟩
  | triangle a b c hab hbc hca =>
    refine ⟨[g a b * g b c * g c a], rfl, by simp, ?_⟩
    intro y hy
    have hy' : y = g a b * g b c * g c a := by simpa using hy
    exact ⟨a, b, c, 1, hab, hbc, hca, by simpa using hy'⟩
  | mul hx hy ihx ihy =>
    obtain ⟨l, hl, hp, hf⟩ := ihx
    obtain ⟨k, hk, hq, hh⟩ := ihy
    refine ⟨l ++ k, by simp [hl, hk], by simp [hp, hq], ?_⟩
    intro y hy
    exact (List.mem_append.mp hy).elim (hf y) (hh y)
  | conj q hx ih =>
    obtain ⟨l, hl, hp, hf⟩ := ih
    refine ⟨l.map (fun y => q * y * q⁻¹), by simp [hl], ?_, ?_⟩
    · rw [← hp]
      have aux : ∀ k : List H, (k.map (fun y => q * y * q⁻¹)).prod = q * k.prod * q⁻¹ := by
        intro k
        induction k with
        | nil => simp
        | cons y k ih => simp only [List.map_cons, List.prod_cons, ih]; group
      exact aux l
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      obtain ⟨a, b, c, s, hab, hbc, hca, rfl⟩ := hf z hz
      exact ⟨a, b, c, q * s, hab, hbc, hca, by group⟩

theorem triangle_product_simplicial_step (g : V → V → H)
    (hrev : ∀ a b, G.Adj a b → g b a = (g a b)⁻¹)
    {z : V} (p : G.Walk z z)
    (hs : ∀ a b, G.Adj z a → a ∈ p.support → G.Adj z b → b ∈ p.support →
      a ≠ b → G.Adj a b)
    (ih : ∀ {a : V} (q : G.Walk a a), q.length < p.length →
      ∃ n, n ≤ q.length - 2 ∧ TriangleProduct G g n (q.gain g)) :
    ∃ n, n ≤ p.length - 2 ∧ TriangleProduct G g n (p.gain g) := by
  cases p with
  | nil => exact ⟨0, by simp, .one⟩
  | @cons z a z hza q =>
    cases q with
    | nil => exact (hza.ne rfl).elim
    | @cons a c z hac q =>
      obtain ⟨b, Q, hbz, he⟩ := Walk.exists_cons_eq_concat hac q
      have ha : a ∈ (Walk.cons hza (Walk.cons hac q)).support := by simp
      have hb : b ∈ (Walk.cons hza (Walk.cons hac q)).support := by
        rw [he]
        simp [Walk.support_concat, Q.end_mem_support]
      have len : (Walk.cons hza (Walk.cons hac q)).length = Q.length + 2 := by
        rw [he, Walk.length_cons, Walk.length_concat]
      by_cases hab : a = b
      · subst b
        obtain ⟨n, hn, hQ⟩ := ih Q (by rw [len]; omega)
        refine ⟨n, by rw [len]; omega, ?_⟩
        have hp : (Walk.cons hza (Walk.cons hac q)).gain g =
            g z a * Q.gain g * (g z a)⁻¹ := by
          rw [he, Walk.gain_cons, Walk.gain_concat, hrev z a hza]
          group
        rw [hp]
        exact hQ.conj (g z a)
      · have hab' : G.Adj a b := hs a b hza ha hbz.symm hb hab
        let R : G.Walk a a := Q.concat hab'.symm
        obtain ⟨n, hn, hR⟩ := ih R (by simp only [R, Walk.length_concat]; rw [len]; omega)
        refine ⟨n + 1, ?_, ?_⟩
        · simp only [R, Walk.length_concat] at hn
          rw [len]
          have : 1 ≤ Q.length := by
            cases Q with
            | nil => exact (hab rfl).elim
            | cons _ _ => simp
          omega
        · have hp : (Walk.cons hza (Walk.cons hac q)).gain g =
              (g z a * R.gain g * (g z a)⁻¹) * (g z a * g a b * g b z) := by
            rw [he, Walk.gain_cons, Walk.gain_concat]
            simp only [R, Walk.gain_concat, hrev a b hab']
            group
          rw [hp]
          exact (hR.conj (g z a)).mul (.triangle z a b hza hab' hbz)

/-- Every finite chordal closed walk has a certificate using at most `length - 2`
triangles. Backtracks and repeated vertices are allowed. -/
theorem IsChordal.closed_walk_triangle_product [Finite V] (hG : G.IsChordal)
    (g : V → V → H)
    (hrev : ∀ a b, G.Adj a b → g b a = (g a b)⁻¹)
    {a : V} (p : G.Walk a a) :
    ∃ n, n ≤ p.length - 2 ∧ TriangleProduct G g n (p.gain g) := by
  classical
  induction hn : p.length using Nat.strong_induction_on generalizing a p with
  | h N ih =>
    let S : Set V := {x | x ∈ p.support}
    have : Nonempty S := ⟨⟨a, p.start_mem_support⟩⟩
    obtain ⟨z, hz⟩ := (hG.induce S).exists_isSimplicial
    let R := p.rotate z z.property
    have hlen : R.length = N := by simp [R, hn]
    have hs : ∀ b c, G.Adj z.val b → b ∈ R.support → G.Adj z.val c → c ∈ R.support →
        b ≠ c → G.Adj b c := by
      intro b c hzb hb hzc hc hbc
      have hbS : b ∈ S := (p.mem_support_rotate_iff z z.property).mp hb
      have hcS : c ∈ S := (p.mem_support_rotate_iff z z.property).mp hc
      exact hz (x := ⟨b, hbS⟩) (y := ⟨c, hcS⟩) hzb hzc
        (fun he => hbc (congrArg Subtype.val he))
    obtain ⟨n, hn', hR⟩ := triangle_product_simplicial_step g hrev R hs (by
      intro b Q hQ
      exact ih Q.length (by omega) Q rfl)
    refine ⟨n, by simpa [R, hn] using hn', ?_⟩
    rw [p.gain_rotate g z.property]
    exact hR.conj _

section BiInvariant

variable [PseudoMetricSpace H] [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H]

/-- A triangle certificate bounds the holonomy in every bi-invariant pseudometric. -/
theorem TriangleProduct.dist_le {g : V → V → H} {ε : ℝ}
    (hrev : ∀ a b, G.Adj a b → g b a = (g a b)⁻¹)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      Dist.dist (g a b * g b c) (g a c) ≤ ε)
    {n : ℕ} {x : H} (h : TriangleProduct G g n x) :
    Dist.dist x 1 ≤ (n : ℝ) * ε := by
  induction h with
  | one => simp
  | triangle a b c hab hbc hca =>
    have he : Dist.dist (g a b * g b c * g c a) 1 =
        Dist.dist (g a b * g b c) (g a c) := by
      rw [hrev a c hca.symm]
      simpa using dist_mul_right (g a b * g b c) (g a c) (g a c)⁻¹
    simpa only [he, Nat.cast_one, one_mul] using htri a b c hab hbc hca.symm
  | @mul m n x y hx hy ihx ihy =>
    have he : Dist.dist (x * y) y = Dist.dist x 1 := by
      simpa using dist_mul_right x 1 y
    have ht := _root_.dist_triangle (x * y) y 1
    rw [he] at ht
    simp only [Nat.cast_add]
    nlinarith
  | @conj n x q hx ih =>
    have he : Dist.dist (q * x * q⁻¹) 1 = Dist.dist x 1 := by
      calc
        _ = Dist.dist (q * x * q⁻¹) (q * 1 * q⁻¹) := by simp
        _ = _ := by rw [dist_mul_right, dist_mul_left]
    rwa [he]

/-- Universal closed-walk holonomy bound, including degenerate closed walks. -/
theorem IsChordal.closed_walk_holonomy_bound [Finite V] (hG : G.IsChordal)
    (g : V → V → H) {ε : ℝ} (hε : 0 ≤ ε)
    (hrev : ∀ a b, G.Adj a b → g b a = (g a b)⁻¹)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      Dist.dist (g a b * g b c) (g a c) ≤ ε)
    {a : V} (p : G.Walk a a) :
    Dist.dist (p.gain g) 1 ≤ ((p.length - 2 : ℕ) : ℝ) * ε := by
  obtain ⟨n, hn, h⟩ := hG.closed_walk_triangle_product g hrev p
  exact (h.dist_le hrev htri).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hε)

end BiInvariant

/-- Forests are chordal, since they have no cycles. -/
theorem IsAcyclic.isChordal (hG : G.IsAcyclic) : G.IsChordal := by
  intro a p hp _
  exact (hG p hp).elim

/-- Inverse edge labels on a finite forest have an exact potential. -/
theorem IsAcyclic.exists_gain_potential [Finite V] (hG : G.IsAcyclic)
    (g : V → V → H)
    (hrev : ∀ a b, G.Adj a b → g b a = (g a b)⁻¹) :
    ∃ φ : V → H, ∀ a b, G.Adj a b → g a b = (φ a)⁻¹ * φ b := by
  classical
  apply hG.isChordal.exists_gain_potential g hrev
  intro a b c hab hbc hac
  exact (hG.cliqueFree_three {a, b, c} (is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)).elim

@[simp] theorem Walk.gain_map_id {T : SimpleGraph V} (hTG : T ≤ G)
    (g : V → V → H) {a b : V} (p : T.Walk a b) :
    (p.map (show T →g G from ⟨id, fun h => hTG h⟩)).gain g = p.gain g := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [ih]

section BiInvariantCorollaries

variable [PseudoMetricSpace H] [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H]

omit [IsIsometricSMul Hᵐᵒᵖ H] in
/-- The transport form of an edge error agrees with the usual gain error. -/
theorem gain_error_eq_fit (x y a : H) :
    Dist.dist a (x⁻¹ * y) = Dist.dist (x * a) y := by
  simpa [mul_assoc] using (dist_mul_left x a (x⁻¹ * y)).symm

/-- Tree-spanner reconstruction: a spanning tree of edge stretch at most `t`
gives error at most `(t - 1) ε`. The potential fits the tree exactly. -/
theorem IsChordal.exists_biinvariant_gain_potential_of_tree_spanner [Finite V]
    (hG : G.IsChordal) {T : SimpleGraph V} (hTG : T ≤ G) (hT : T.IsTree)
    (t : ℕ) (hstretch : ∀ a b, G.Adj a b → T.dist a b ≤ t)
    (g : V → V → H) {ε : ℝ} (hε : 0 ≤ ε)
    (hrev : ∀ a b, G.Adj a b → g b a = (g a b)⁻¹)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      Dist.dist (g a b * g b c) (g a c) ≤ ε) :
    ∃ φ : V → H,
      (∀ a b, T.Adj a b → g a b = (φ a)⁻¹ * φ b) ∧
      ∀ a b, G.Adj a b → Dist.dist (φ a * g a b) (φ b) ≤ ((t : ℝ) - 1) * ε := by
  obtain ⟨φ, hφ⟩ := hT.isAcyclic.exists_gain_potential g (fun a b h => hrev a b (hTG h))
  refine ⟨φ, hφ, ?_⟩
  intro a b hab
  obtain ⟨p, hp⟩ := hT.connected.exists_walk_length_eq_dist a b
  let q : G.Walk a b := p.map ⟨id, fun h => hTG h⟩
  let c : G.Walk a a := q.concat hab.symm
  have hq : q.gain g = (φ a)⁻¹ * φ b := by
    rw [Walk.gain_map_id]
    exact p.gain_of_potential g φ hφ
  have hc : Dist.dist (c.gain g) 1 = Dist.dist (φ a * g a b) (φ b) := by
    simp only [c, Walk.gain_concat, hrev a b hab, hq]
    calc
      _ = Dist.dist ((φ a)⁻¹ * φ b) (g a b) := by
        simpa using dist_mul_right ((φ a)⁻¹ * φ b) (g a b) (g a b)⁻¹
      _ = Dist.dist (φ b) (φ a * g a b) := by
        simpa [mul_assoc] using (dist_mul_left (φ a) ((φ a)⁻¹ * φ b) (g a b)).symm
      _ = _ := _root_.dist_comm _ _
  have hpos : 1 ≤ T.dist a b := hT.connected.pos_dist_of_ne hab.ne
  have hlen : c.length = T.dist a b + 1 := by simp [c, q, hp]
  have hcoeff : (((c.length - 2 : ℕ) : ℝ)) ≤ (t : ℝ) - 1 := by
    have hnat : c.length - 2 + 1 ≤ t := by have := hstretch a b hab; omega
    have hr : ((c.length - 2 : ℕ) : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast hnat
    linarith
  rw [← hc]
  exact (hG.closed_walk_holonomy_bound g hε hrev htri c).trans
    (mul_le_mul_of_nonneg_right hcoeff hε)

/-- Any family of root walks of length at most `r` gives the radius estimate.
No tree construction or compatibility between the chosen walks is needed. -/
theorem IsChordal.exists_biinvariant_gain_potential_of_rooted_walks [Finite V]
    (hG : G.IsChordal) (o : V) (r : ℕ) (hr : 1 ≤ r)
    (p : ∀ a, G.Walk o a) (hlen : ∀ a, (p a).length ≤ r)
    (g : V → V → H) {ε : ℝ} (hε : 0 ≤ ε)
    (hrev : ∀ a b, G.Adj a b → g b a = (g a b)⁻¹)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      Dist.dist (g a b * g b c) (g a c) ≤ ε) :
    ∃ φ : V → H, ∀ a b, G.Adj a b →
      Dist.dist (φ a * g a b) (φ b) ≤ (2 * (r : ℝ) - 1) * ε := by
  let φ (a : V) := (p a).gain g
  refine ⟨φ, ?_⟩
  intro a b hab
  let c := ((p a).concat hab).append (p b).reverse
  have hc : Dist.dist (c.gain g) 1 = Dist.dist (φ a * g a b) (φ b) := by
    simp only [c, Walk.gain_append, Walk.gain_concat, Walk.gain_reverse g hrev]
    simpa [φ] using dist_mul_right ((p a).gain g * g a b) ((p b).gain g) ((p b).gain g)⁻¹
  have hcoeff : (((c.length - 2 : ℕ) : ℝ)) ≤ 2 * (r : ℝ) - 1 := by
    have hnat : c.length - 2 + 1 ≤ 2 * r := by
      have ha := hlen a
      have hb := hlen b
      simp only [c, Walk.length_append, Walk.length_concat, Walk.length_reverse]
      omega
    have he : ((c.length - 2 : ℕ) : ℝ) + 1 ≤ 2 * (r : ℝ) := by exact_mod_cast hnat
    linarith
  rw [← hc]
  exact (hG.closed_walk_holonomy_bound g hε hrev htri c).trans
    (mul_le_mul_of_nonneg_right hcoeff hε)

/-- Radius corollary, expressed by an actual center and graph distances. -/
theorem IsChordal.exists_biinvariant_gain_potential_of_radius [Finite V]
    (hG : G.IsChordal) (hconn : G.Connected) (o : V) (r : ℕ)
    (hrad : ∀ a, G.dist o a ≤ r)
    (g : V → V → H) {ε : ℝ} (hε : 0 ≤ ε)
    (hrev : ∀ a b, G.Adj a b → g b a = (g a b)⁻¹)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      Dist.dist (g a b * g b c) (g a c) ≤ ε) :
    ∃ φ : V → H, ∀ a b, G.Adj a b →
      Dist.dist (φ a * g a b) (φ b) ≤ (2 * (r : ℝ) - 1) * ε := by
  classical
  by_cases hr : r = 0
  · refine ⟨fun _ => 1, ?_⟩
    intro a b hab
    have ha : o = a := hconn.dist_eq_zero_iff.mp (by have := hrad a; omega)
    have hb : o = b := hconn.dist_eq_zero_iff.mp (by have := hrad b; omega)
    exact (hab.ne (ha.symm.trans hb)).elim
  · choose p hp using hconn.exists_walk_length_eq_dist o
    exact hG.exists_biinvariant_gain_potential_of_rooted_walks o r (by omega) p
      (fun a => (hp a).trans_le (hrad a)) g hε hrev htri

/-- The radius-two specialization has error at most `3 ε`. -/
theorem IsChordal.exists_biinvariant_gain_potential_of_radius_two [Finite V]
    (hG : G.IsChordal) (hconn : G.Connected) (o : V)
    (hrad : ∀ a, G.dist o a ≤ 2)
    (g : V → V → H) {ε : ℝ} (hε : 0 ≤ ε)
    (hrev : ∀ a b, G.Adj a b → g b a = (g a b)⁻¹)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      Dist.dist (g a b * g b c) (g a c) ≤ ε) :
    ∃ φ : V → H, ∀ a b, G.Adj a b → Dist.dist (φ a * g a b) (φ b) ≤ 3 * ε := by
  have he : (2 * (2 : ℝ) - 1) = 3 := by norm_num
  simpa only [Nat.cast_ofNat, he] using
    hG.exists_biinvariant_gain_potential_of_radius hconn o 2 hrad g hε hrev htri

end BiInvariantCorollaries

end SimpleGraph
