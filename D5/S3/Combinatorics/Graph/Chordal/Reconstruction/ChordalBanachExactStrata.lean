/- GID: D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.subtwo_finite_group_claim; result=D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.not_subtwo_finite_group; claim=D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.subtwo_finite_group_claim
   digest: Exact scalar reconstruction, finite abelian reduction, and sharp geometric and group bounds on chordal graphs. -/

import D5.S3.Combinatorics.Graph.Chordal.GainPotential
import D5.S3.Combinatorics.Graph.Chordal.EliminationForest
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import OmegaMath.Combinatorics.Graph.ChordalGainReduction
import OmegaMath.Combinatorics.Graph.RootedAncestorReconstruction
import D5.S3.Combinatorics.Graph.Chordal.CliqueTreeBanachPotential
import OmegaMath.Combinatorics.Graph.ChordalWalkHolonomy
import OmegaMath.Combinatorics.Graph.FiniteHilbertJung
import OmegaMath.Combinatorics.Graph.GroupCliqueStrata
import OmegaMath.Combinatorics.Graph.ScalarCycleReconstruction
import D5.S3.Combinatorics.Graph.Chordal.SimplicialAndIntervalPotential
import OmegaMath.Combinatorics.Graph.PathPowerReconstruction
import OmegaMath.Combinatorics.Graph.ChordalPath49Metric
import OmegaMath.Combinatorics.Graph.L1Jung
import OmegaMath.Combinatorics.Graph.ChordalFanLower
import OmegaMath.Combinatorics.Graph.ChordalGroupCoefficient
import D5.S3.Combinatorics.Graph.Chordal.UniformGainPotential
import D5.S3.Combinatorics.Graph.Chordal.CompleteAndCliqueSumBanach
import D5.S3.Combinatorics.Graph.Chordal.ChordalBanachLimitTwo
import OmegaMath.Combinatorics.Graph.PairRetention
import OmegaMath.Combinatorics.Graph.PathPowerRadius
import OmegaMath.Combinatorics.Graph.HilbertSimplexRadius
import OmegaMath.Combinatorics.Graph.L1BalancedRadius
import OmegaMath.Combinatorics.Graph.L1Counting
import OmegaMath.Combinatorics.Graph.ChordalAbelianReduction
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import OmegaMath.Combinatorics.Graph.ChordalEightVertexMetric
import OmegaMath.Combinatorics.Graph.CliqueTreeRadiusForm
import OmegaMath.Combinatorics.Graph.CliqueTreeGroupSeparator
import OmegaMath.Combinatorics.Graph.CliqueTreeL1Separator
import OmegaMath.Combinatorics.Graph.CliqueTreeBanachOverlap
import OmegaMath.Combinatorics.Graph.RollingSpanOne
import D5.S3.Combinatorics.Graph.Chordal.Dirac

/-! # Chordal reconstruction strata

Scalar reconstruction is determined by circumference. A single modular cochain
decides universal abelian word-budget feasibility. Root-path coherence,
finite Hilbert centers and noncommutative clique orderings give further bounds.
-/
namespace SimpleGraph.GainReduction

universe u

variable {V : Type u} {G T : SimpleGraph V}

/-- A single canonical cochain over the residue ring decides universal abelian feasibility.
Choosing a spanning tree indexes the coordinates by the edges outside that tree. The
modulus bound ensures that triangle equations lift over the integers. -/
theorem finite_modulus_decides_abelian_reconstruction [Finite V] [LinearOrder V]
    (hG : G.IsChordal) (hTG : T ≤ G) (hT : T.IsTree) {k q : ℕ} (hq : 3 * k + 1 < q) :
    Reconstructs G (fun v w => reduce q (canonical G T v w))
      (reduce q '' defects G (canonical G T)) k ↔
    ∀ (A : Type u) [AddCommGroup A] (g : V → V → A) (U : Set A),
      (∀ v w, G.Adj v w → g w v = -g v w) → defects G g ⊆ U →
      Reconstructs G g U k := by
  classical
  rw [reconstructs_modular_iff_integral hG hq]
  constructor
  · rintro ⟨p, hp⟩ A _ g U hrev hU
    have hTc : T.IsChordal := fun _ c hc _ => (hT.isAcyclic c hc).elim
    obtain ⟨a, ha⟩ := integrate hTc g (fun v w h => hrev v w (hTG h))
      (fun v w x hvw hwx hvx => by
        have hc : (hvw.toWalk.append (hwx.toWalk.append hvx.symm.toWalk)).IsCycle := by
          rw [Walk.isCycle_iff_isPath_tail_and_le_length]
          simp [hvw.ne.symm, hwx.ne, hvx.ne.symm]
        exact (hT.isAcyclic _ hc).elim)
    let f (v w : V) := g v w - (a w - a v)
    have hf (v w : V) (h : G.Adj v w) : f w v = -f v w := by
      dsimp [f]
      rw [hrev v w h]
      abel
    let F := evalCochain (G := G) (T := T) f
    have hF (v w : V) (h : G.Adj v w) : F (canonical G T v w) = f v w :=
      eval_canonical f hf (fun v w h => by simp [f, ha v w h]) v w h
    have hmap : F '' defects G (canonical G T) ⊆ U := by
      rintro _ ⟨d, hd, rfl⟩
      apply hU
      rcases hd with rfl | ⟨v, w, x, hvw, hwx, hvx, rfl⟩
      · exact Or.inl (map_zero F)
      · refine Or.inr ⟨v, w, x, hvw, hwx, hvx, ?_⟩
        simp only [map_add, map_sub, hF v w hvw, hF w x hwx, hF v x hvx, f]
        abel
    refine ⟨fun v => a v + F (p v), fun v w h => ?_⟩
    obtain ⟨terms, ht, he⟩ := (hp v w h).map F
    refine ⟨terms, fun j => hmap (ht j), he.trans ?_⟩
    simp only [map_sub, hF v w h, f]
    abel
  · intro h
    exact h _ (canonical G T) _ (fun v w _ => canonical_rev v w) Set.Subset.rfl
end SimpleGraph.GainReduction
namespace SimpleGraph

variable {V E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Bounded ancestor edges in a rooted tree admit a Banach gain potential with coefficient
`2 - 2 / k`. The construction uses the unique root paths and allows arbitrary branching. -/
theorem IsTree.exists_ancestor_banach_gain_potential {S : SimpleGraph V}
    (hS : S.IsTree) (root : V) {k : ℕ} (hk : 0 < k)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ v w, g w v = -g v w)
    (htri : ∀ v w x, ((RootedAncestors.ofTree hS root).graph k).Adj v w →
      ((RootedAncestors.ofTree hS root).graph k).Adj w x →
      ((RootedAncestors.ofTree hS root).graph k).Adj v x → ‖g v w + g w x - g v x‖ ≤ ε) :
    ∃ p : V → E, ∀ v w, ((RootedAncestors.ofTree hS root).graph k).Adj v w →
      ‖g v w - (p w - p v)‖ ≤ (2 - 2 / (k : ℝ)) * ε :=
  (RootedAncestors.ofTree hS root).exists_banach_gain_potential hk g ε hε hrev htri
end SimpleGraph
namespace SimpleGraph

open scoped Pointwise
open GroupCliqueStrata (NormalSet)
variable {V H : Type*} [Group H] [PseudoMetricSpace H]
  [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H] {G : SimpleGraph V}

private theorem defectBall_normal {ε : ℝ} (hε : 0 ≤ ε) :
    NormalSet {x : H | Dist.dist x 1 ≤ ε} where
  one_mem := by simpa
  inv_mem := by
    intro x hx
    change Dist.dist x⁻¹ 1 ≤ ε
    simpa using (show Dist.dist x⁻¹ (1 : H)⁻¹ ≤ ε by rwa [dist_inv_inv])
  conj_mem := by
    intro a x hx
    change Dist.dist (a * x * a⁻¹) 1 ≤ ε
    simpa only [mul_one, mul_inv_cancel] using
      (show Dist.dist (a * x * a⁻¹) (a * 1 * a⁻¹) ≤ ε by rwa [dist_mul_right, dist_mul_left])

omit [IsIsometricSMul Hᵐᵒᵖ H] in
private theorem defectBall_word_bound {ε : ℝ} {n : ℕ} {x : H}
    (hx : x ∈ ({y : H | Dist.dist y 1 ≤ ε} : Set H) ^ n) :
    Dist.dist x 1 ≤ (n : ℝ) * ε := by
  induction n generalizing x with
  | zero =>
    have he : x = 1 := by simpa using hx
    simp [he]
  | succ n ih =>
    rw [pow_succ, Set.mem_mul] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    have h₁ : Dist.dist (u * v) u = Dist.dist v 1 := by
      simpa using (dist_mul_left u v 1)
    have h₂ : Dist.dist v 1 ≤ ε := hv
    have h₃ := ih hu
    have ht := _root_.dist_triangle (u * v) u 1
    rw [h₁] at ht
    push_cast
    linarith

private theorem residual_distance (g : V → V → H) (φ : V → H) (x y : V) :
    Dist.dist (GroupCliqueStrata.residual g φ x y) 1 = Dist.dist (g x y) ((φ x)⁻¹ * φ y) := by
  unfold GroupCliqueStrata.residual
  rw [show (1 : H) = (φ x * ((φ x)⁻¹ * φ y)) * (φ y)⁻¹ by group,
    dist_mul_right, dist_mul_left]

/-- The algebraic two-factor construction gives a uniform two-defect metric bound. -/
theorem IsChordal.exists_clique_four_group_gain_potential [Finite V] (hG : G.IsChordal)
    (hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ 4)
    (g : V → V → H) {ε : ℝ} (hε : 0 ≤ ε)
    (hrev : ∀ x y, G.Adj x y → g y x = (g x y)⁻¹)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z →
      Dist.dist (g x y * g y z) (g x z) ≤ ε) :
    ∃ φ : V → H, ∀ x y, G.Adj x y → Dist.dist (g x y) ((φ x)⁻¹ * φ y) ≤ 2 * ε := by
  obtain ⟨φ, hφ⟩ := GroupCliqueStrata.exists_potential_clique_le_four hG hclique
    (defectBall_normal hε) g hrev (fun x y z hxy hyz hxz => by
      change Dist.dist (g x y * g y z * (g x z)⁻¹) 1 ≤ ε
      simpa using (show Dist.dist (g x y * g y z * (g x z)⁻¹) (g x z * (g x z)⁻¹) ≤ ε by
        rw [dist_mul_right]
        exact htri x y z hxy hyz hxz))
  refine ⟨φ, fun x y h => ?_⟩
  have he := defectBall_word_bound (hφ x y h)
  rw [residual_distance] at he
  exact_mod_cast he

/-- The algebraic three-factor construction gives a uniform three-defect metric bound. -/
theorem IsChordal.exists_clique_five_group_gain_potential [Finite V] (hG : G.IsChordal)
    (hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ 5)
    (g : V → V → H) {ε : ℝ} (hε : 0 ≤ ε)
    (hrev : ∀ x y, G.Adj x y → g y x = (g x y)⁻¹)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z →
      Dist.dist (g x y * g y z) (g x z) ≤ ε) :
    ∃ φ : V → H, ∀ x y, G.Adj x y → Dist.dist (g x y) ((φ x)⁻¹ * φ y) ≤ 3 * ε := by
  obtain ⟨φ, hφ⟩ := GroupCliqueStrata.exists_potential_clique_le_five hG hclique
    (defectBall_normal hε) g hrev (fun x y z hxy hyz hxz => by
      change Dist.dist (g x y * g y z * (g x z)⁻¹) 1 ≤ ε
      simpa using (show Dist.dist (g x y * g y z * (g x z)⁻¹) (g x z * (g x z)⁻¹) ≤ ε by
        rw [dist_mul_right]
        exact htri x y z hxy hyz hxz))
  refine ⟨φ, fun x y h => ?_⟩
  have he := defectBall_word_bound (hφ x y h)
  rw [residual_distance] at he
  exact_mod_cast he
end SimpleGraph
namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

private theorem scalarGain_of_walk (g : V → V → ℝ) {a b : V} (p : G.Walk a b) :
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

private theorem scalarWeight_shift (g : V → V → ℝ) (M : ℝ) {a b : V} (p : G.Walk a b) :
    p.scalarWeight (fun v w => g v w + M) = p.scalarWeight g + (p.length : ℝ) * M := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    simp only [Walk.scalarWeight_cons, Walk.length_cons, ih, Nat.cast_add, Nat.cast_one]
    ring

/-- If the longest simple cycle has length `L`, the optimal scalar reconstruction
coefficient for triangle defect one is `1 - 2 / L`. -/
theorem IsChordal.scalar_circumference_exact [Finite V] (hG : G.IsChordal)
    {L : ℕ} (hL : ∀ (a : V) (c : G.Walk a a), c.IsCycle → c.length ≤ L)
    (hmax : ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ c.length = L) :
    (∀ g : V → V → ℝ, (∀ a b, G.Adj a b → g b a = -g a b) →
      (∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
        |g a b + g b c - g a c| ≤ 1) →
      ∃ φ : V → ℝ, ∀ a b, G.Adj a b → |g a b - (φ b - φ a)| ≤ 1 - 2 / (L : ℝ)) ∧
    ∃ g : V → V → ℝ, (∀ a b, g b a = -g a b) ∧
      (∀ a b c, |g a b + g b c - g a c| ≤ 1) ∧
      ∀ φ : V → ℝ, ∃ a b, G.Adj a b ∧ 1 - 2 / (L : ℝ) ≤ |g a b - (φ b - φ a)| := by
  obtain ⟨o, c, hc, hcL⟩ := hmax
  have hL3 : 3 ≤ L := hcL ▸ hc.three_le_length
  have hLR : (3 : ℝ) ≤ L := by exact_mod_cast hL3
  have hL0 : (0 : ℝ) < L := by linarith
  let M := 1 - 2 / (L : ℝ)
  have hM : 0 ≤ M := by
    dsimp [M]
    rw [sub_nonneg, div_le_iff₀ hL0]
    linarith
  constructor
  · intro g hrev htri
    let w (a b : V) := g a b + M
    have hback (a b : V) (h : G.Adj a b) : 0 ≤ w a b + w b a := by
      dsimp [w]
      rw [hrev a b h]
      linarith
    have hcycle (a : V) (p : G.Walk a a) (hp : p.IsCycle) : 0 ≤ p.scalarWeight w := by
      obtain ⟨n, hn, hprod⟩ := hG.closed_walk_triangle_product
        (fun a b => Multiplicative.ofAdd (g a b)) (fun a b h => hrev a b h) p
      have hsum := scalar_triangle_product_abs g hrev htri hprod
      rw [scalarGain_of_walk] at hsum
      have h₁ : -(n : ℝ) ≤ p.scalarWeight g := (abs_le.mp hsum).1
      have hlen : (3 : ℝ) ≤ p.length := by exact_mod_cast hp.three_le_length
      have hp₂ := hp.three_le_length
      have h₂ : (n : ℝ) ≤ (p.length : ℝ) - 2 := by
        rw [← Nat.cast_ofNat (R := ℝ), ← Nat.cast_sub (by omega : 2 ≤ p.length)]
        exact_mod_cast hn
      have h₃ : (p.length : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL a p hp
      have h₄ : (p.length : ℝ) - 2 ≤ (p.length : ℝ) * M := by
        have hm' : (p.length : ℝ) * 2 / (L : ℝ) ≤ 2 :=
          (div_le_iff₀ hL0).2 (by linarith)
        dsimp [M]
        rw [mul_sub, mul_one, ← mul_div_assoc]
        linarith
      dsimp [w]
      rw [scalarWeight_shift]
      linarith
    obtain ⟨φ, hφ⟩ := exists_scalar_potential_of_nonneg_closed_walks w
      (fun _ p => p.scalarWeight_nonneg_of_cycles w hback hcycle)
    refine ⟨φ, fun a b hab => abs_le.mpr ⟨?_, ?_⟩⟩
    · have he := hφ a b hab
      dsimp [w] at he
      linarith
    · have he := hφ b a hab.symm
      dsimp [w] at he
      rw [hrev a b hab] at he
      linarith
  · simpa only [← hcL] using hc.exists_scalar_gain_obstruction
end SimpleGraph
namespace SimpleGraph

variable {V H : Type*} [Group H] {G : SimpleGraph V}

/-- Explicit list formulation of the universal noncommutative factorization. -/
theorem IsChordal.closed_walk_triangle_factors [Finite V] (hG : G.IsChordal)
    (g : V → V → H)
    (hrev : ∀ a b, G.Adj a b → g b a = (g a b)⁻¹)
    {a : V} (p : G.Walk a a) :
    ∃ l : List H, l.length ≤ p.length - 2 ∧ l.prod = p.gain g ∧ ∀ y ∈ l,
      ∃ (a b c : V) (q : H), G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        y = q * (g a b * g b c * g c a) * q⁻¹ := by
  obtain ⟨n, hn, h⟩ := hG.closed_walk_triangle_product g hrev p
  obtain ⟨l, hl, hp, hf⟩ := h.exists_factors
  exact ⟨l, hl ▸ hn, hp, hf⟩

variable [PseudoMetricSpace H] [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H]

/-- Tree-spanner bound in the edge-error convention of `GainPotential`. -/
theorem IsChordal.exists_tree_spanner_approximate_gain_potential [Finite V]
    (hG : G.IsChordal) {T : SimpleGraph V} (hTG : T ≤ G) (hT : T.IsTree)
    (t : ℕ) (hstretch : ∀ a b, G.Adj a b → T.dist a b ≤ t)
    (g : V → V → H) {ε : ℝ} (hε : 0 ≤ ε)
    (hrev : ∀ a b, G.Adj a b → g b a = (g a b)⁻¹)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      Dist.dist (g a b * g b c) (g a c) ≤ ε) :
    ∃ φ : V → H, ∀ a b, G.Adj a b →
      Dist.dist (g a b) ((φ a)⁻¹ * φ b) ≤ ((t : ℝ) - 1) * ε := by
  obtain ⟨φ, _, hφ⟩ := hG.exists_biinvariant_gain_potential_of_tree_spanner
    hTG hT t hstretch g hε hrev htri
  exact ⟨φ, fun a b hab => by rw [gain_error_eq_fit]; exact hφ a b hab⟩

/-- Radius bound in the edge-error convention of `GainPotential`. -/
theorem IsChordal.exists_radius_approximate_gain_potential [Finite V]
    (hG : G.IsChordal) (hconn : G.Connected) (o : V) (r : ℕ)
    (hrad : ∀ a, G.dist o a ≤ r)
    (g : V → V → H) {ε : ℝ} (hε : 0 ≤ ε)
    (hrev : ∀ a b, G.Adj a b → g b a = (g a b)⁻¹)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      Dist.dist (g a b * g b c) (g a c) ≤ ε) :
    ∃ φ : V → H, ∀ a b, G.Adj a b →
      Dist.dist (g a b) ((φ a)⁻¹ * φ b) ≤ (2 * (r : ℝ) - 1) * ε := by
  obtain ⟨φ, hφ⟩ := hG.exists_biinvariant_gain_potential_of_radius hconn o r hrad g hε hrev htri
  exact ⟨φ, fun a b hab => by rw [gain_error_eq_fit]; exact hφ a b hab⟩
end SimpleGraph
namespace SimpleGraph

universe u v

/-- Hilbert clique-stratum upper bound: clique number at most `k+1` gives
error constant `J_k / (1-J_k)`, where `J_k = sqrt ((k-1)/(2k))`. -/
theorem IsChordal.exists_hilbert_jung_gain_potential
    {V : Type u} [Finite V] {G : SimpleGraph V} (hG : G.IsChordal)
    (k : ℕ) (hk : 1 ≤ k)
    (hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ k + 1)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε) :
    ∃ φ : V → E, ∀ u v, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤
        (Real.sqrt (((k : ℝ) - 1) / (2 * k)) /
          (1 - Real.sqrt (((k : ℝ) - 1) / (2 * k)))) * ε := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hq : Real.sqrt (((k : ℝ) - 1) / (2 * k)) < 1 := by
    have hratio : ((k : ℝ) - 1) / (2 * k) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    have hsq : Real.sqrt (((k : ℝ) - 1) / (2 * k)) ^ 2 = ((k : ℝ) - 1) / (2 * k) :=
      Real.sq_sqrt (div_nonneg (by
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        linarith) (by positivity))
    nlinarith [Real.sqrt_nonneg (((k : ℝ) - 1) / (2 * k))]
  apply hG.exists_gain_potential_of_finite_center k _ (Real.sqrt_nonneg _) hq ?_ hclique g ε hε hrev htri
  intro S p D hD hcard hdiam
  classical
  by_cases hs : S.Nonempty
  · let : Nonempty (↑S : Set V) := ⟨⟨hs.choose, hs.choose_spec⟩⟩
    obtain ⟨c, _, hc⟩ := FiniteHilbertJung.exists_jung_center
      (fun i : (↑S : Set V) => p i) k hk (by simpa using hcard) hD
      (fun i j => hdiam i i.property j j.property)
    exact ⟨c, fun x hx => hc ⟨x, hx⟩⟩
  · exact ⟨0, fun x hx => (hs ⟨x, hx⟩).elim⟩
end SimpleGraph
namespace SimpleGraph

/-- The separator recurrence gives an exact expression for the upper bound at finite height. -/
theorem cliqueTree_height_banach_gain_potential {V I E : Type*} [Finite V] [Finite I]
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {T : SimpleGraph I} {G : SimpleGraph V} {K : I → Set V}
    (hK : IsCliqueTree T G K) (hs : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty)
    (q : ℕ) (hq : 2 ≤ q) (hsep : ∀ a b, T.Adj a b → (K a ∩ K b).ncard ≤ q)
    (r : I) (h : ℕ) (hheight : ∀ a, T.dist r a ≤ h)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε) :
    ∃ φ : V → E, ∀ u v, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤
        (((q : ℝ) - 1) - ((q : ℝ) - 2) * (((q : ℝ) - 1) / q) ^ h) * ε := by
  have hdiam (a b : I) : T.dist a b ≤ 2 * h := by
    have hh : T.dist a b ≤ T.dist a r + T.dist r b := hK.isTree.connected.dist_triangle
    rw [T.dist_comm (u := a) (v := r)] at hh
    exact hh.trans (by have := hheight a; have := hheight b; omega)
  obtain ⟨φ, hφ⟩ := cliqueTree_center_extension_banach_potential hK hs q
    (by omega) hsep (2 * h) hdiam g ε hε hrev htri
  refine ⟨φ, fun a b hab => ?_⟩
  have hh := hφ a b hab
  rwa [show 2 * h / 2 = h by omega, cliqueTreeRadius_closed_form hq] at hh
end SimpleGraph
namespace SimpleGraph.BanachPathPower

/-- Width one is exact. Width two has optimal coefficient one. Every larger width
has optimal coefficient two, attained with a finite abelian target. -/
theorem pathPower_group_exact_strata (k : ℕ) (hk : 1 ≤ k) (C : ℝ) :
    GroupUniformBound k C ↔ (if k = 1 then 0 else if k = 2 then 1 else 2) ≤ C := by
  let B : ℝ := if k = 1 then 0 else if k = 2 then 1 else 2
  have hB : 0 ≤ B := by dsimp [B]; split_ifs <;> norm_num
  constructor
  · intro hC
    by_cases h₁ : k = 1
    · simpa [h₁] using hC.1
    by_cases h₂ : k = 2
    · subst k; simpa using triangle_power_lower C hC
    have h₃ : 3 ≤ k := by omega
    let := ChordalPath49.cayleyMetric
    let := ChordalPath49.cayley_left
    let := ChordalPath49.cayley_right
    obtain ⟨g, hrev, htri, hobs⟩ := ChordalPath49.metric_obstruction_from_words
      (ChordalPath49.stretchedGain k) (fun i j l => ChordalPath49.stretched_triangle_mem h₃)
      (ChordalPath49.stretched_exact_word_optimum_two h₃).2
    obtain ⟨p, hp⟩ := hC.2 (4 * k + 2) ChordalPath49.M g hrev htri
    obtain ⟨a, b, hab, hh⟩ := hobs p
    simpa [h₁, h₂] using hh.trans (hp a b hab)
  · intro hC
    refine ⟨hB.trans hC, fun n H _ _ _ _ g hrev htri => ?_⟩
    have hε : (0 : ℝ) ≤ 1 := by norm_num
    by_cases hs : k ≤ 2
    · obtain ⟨p, hp⟩ := pathPower_small_group_upper_bound hk hs g hε hrev htri
      refine ⟨p, fun a b hab => (hp a b hab).trans ?_⟩
      have hk12 : k = 1 ∨ k = 2 := by omega
      rcases hk12 with h | h <;> subst k <;> norm_num [B] at hC ⊢ <;> exact hC
    · obtain ⟨ℓ, r, _, hI, hG⟩ := pathPower_isIntervalGraph n k
      obtain ⟨p, hp⟩ := (intervalGraph_isChordal_and_two_approximate_gain_potential
        ℓ r hI hG g 1 hε hrev htri).2
      refine ⟨p, fun a b hab => (hp a b hab).trans ?_⟩
      simpa [B, show k ≠ 1 by omega, show k ≠ 2 by omega] using hC
end SimpleGraph.BanachPathPower
namespace SimpleGraph

open MeasureTheory

variable {Ω V : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : SimpleGraph V}

/-- The finite odd-family Jung bound gives a gain bound on chordal graphs with clique
number at most `2 * m + 2`. In particular, clique bounds four and six give factors
one and three for every real `L¹(μ)`. -/
theorem IsChordal.exists_l1_jung_gain_potential [Finite V] (hG : G.IsChordal)
    (m : ℕ) (hm : 1 ≤ m)
    (hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ 2 * m + 2)
    (g : V → V → Lp ℝ 1 μ) (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ i j, g j i = -g i j)
    (htri : ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l →
      ‖g i j + g j l - g i l‖ ≤ ε) :
    ∃ φ : V → Lp ℝ 1 μ, ∀ u v, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ (2 * (m : ℝ) - 1) * ε := by
  let q : ℝ := 1 - 1 / (2 * (m : ℝ))
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : 0 < 2 * (m : ℝ) := by linarith
  have hq : 0 ≤ q := by
    dsimp [q]
    rw [sub_nonneg, div_le_iff₀ hpos]
    linarith
  have hq1 : q < 1 := by
    dsimp [q]
    have hh := one_div_pos.mpr hpos
    linarith
  obtain ⟨p, hp⟩ := hG.exists_gain_potential_of_finite_center (2 * m + 1) q hq hq1
    (fun s x D hD hs hd => ChordalL1.exists_center_finset_odd m hm s x hD hs hd)
    hclique g ε hε hrev htri
  have he : q / (1 - q) = 2 * (m : ℝ) - 1 := by
    dsimp [q]
    field_simp
    ring
  exact ⟨p, fun a b hab => he ▸ hp a b hab⟩
end SimpleGraph
namespace SimpleGraph

/-- The universal bi-invariant group coefficient of a finite connected chordal graph
is attained at an integer no larger than four. -/
theorem IsChordal.group_coefficient_integral {V : Type*} [Finite V] [LinearOrder V]
    {G : SimpleGraph V} (hG : G.IsChordal) (hconn : G.Connected) :
    ∃ k : ℕ, k ≤ 4 ∧ ∀ C : ℝ, GroupCoefficient.Admissible G C ↔ (k : ℝ) ≤ C :=
  GroupCoefficient.integral hG hconn
end SimpleGraph
namespace SimpleGraph.BanachPathPower

/-- The cyclic abelian witness gives exact error two on any width-three path with
at least fourteen vertices. In particular, the universal group bound for
chordal graphs of clique number at most four is attained in an abelian group. -/
theorem pathPower_width_three_cyclic_exact {n : ℕ} (hn : 14 ≤ n) :
    letI := ChordalPath49.cayleyMetric
    ∃ g : Fin n → Fin n → ChordalPath49.M,
      (∀ a b, (pathPower n 3).Adj a b → g b a = (g a b)⁻¹) ∧
      (∀ a b c, (pathPower n 3).Adj a b → (pathPower n 3).Adj b c →
        (pathPower n 3).Adj a c → Dist.dist (g a b * g b c) (g a c) ≤ 1) ∧
      (∃ p : Fin n → ChordalPath49.M, ∀ a b, (pathPower n 3).Adj a b →
        Dist.dist (g a b) ((p a)⁻¹ * p b) ≤ 2) ∧
      (∀ p : Fin n → ChordalPath49.M, ∃ a b, (pathPower n 3).Adj a b ∧
        2 ≤ Dist.dist (g a b) ((p a)⁻¹ * p b)) := by
  let := ChordalPath49.cayleyMetric
  let := ChordalPath49.cayley_left
  let := ChordalPath49.cayley_right
  let f := fun i j : ℕ => ChordalPath49.forwardGain i (j - i)
  have ht (i j l : ℕ) (hij : i < j) (hjl : j < l) (hil : l ≤ i + 3) :
      f i j + f j l - f i l ∈ ChordalPath49.alphabet :=
    List.mem_cons_of_mem _ (ChordalPath49.ordered_triangle_defect_mem i j l hij hjl hil)
  obtain ⟨g, hr, htri, hlow⟩ := ChordalPath49.metric_obstruction_from_words
    f ht (ChordalPath49.exact_word_optimum_two hn).2
  obtain ⟨ℓ, r, _, hI, hshape⟩ := pathPower_isIntervalGraph n 3
  have hG := (intervalGraph_isChordal_and_two_approximate_gain_potential ℓ r hI hshape
    g 1 (by norm_num) hr htri).1
  obtain ⟨p, hp⟩ := hG.exists_clique_four_group_gain_potential
    (fun s hs => clique_card_le_width_add_one hs) g (ε := 1) (by norm_num) hr htri
  exact ⟨g, hr, htri, ⟨p, by simpa only [mul_one] using hp⟩, hlow⟩
end SimpleGraph.BanachPathPower
namespace SimpleGraph

open MeasureTheory

/-- The least uniform coefficient at clique number four is one in every nonzero
real `L¹(μ)`. The lower bound already occurs as a limit on chordal fans. -/
theorem l1_clique_four_exact {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [Nontrivial (Lp ℝ 1 μ)] (C : ℝ) :
    (∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))),
      G.IsChordal → (∀ s : Finset (Fin (n + 1)), G.IsClique (s : Set (Fin (n + 1))) →
        s.card ≤ 4) → ∀ g : Fin (n + 1) → Fin (n + 1) → Lp ℝ 1 μ,
      (∀ a b, g b a = -g a b) →
      (∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
        ‖g a b + g b c - g a c‖ ≤ 1) →
      ∃ p : Fin (n + 1) → Lp ℝ 1 μ, ∀ a b, G.Adj a b →
        ‖g a b - (p b - p a)‖ ≤ C) ↔ 1 ≤ C := by
  constructor
  · intro h
    by_contra! hlt
    obtain ⟨n, G, g, hG, hc, hr, ht, ho⟩ :=
      exists_chordal_clique_three_normed_gain_obstruction (Lp ℝ 1 μ) C hlt
    obtain ⟨p, hp⟩ := h n G hG (fun s hs => (hc s hs).trans (by omega)) g hr (fun a b c _ _ _ => ht a b c)
    obtain ⟨a, b, hab, he⟩ := ho p
    exact (not_lt_of_ge (hp a b hab)) he
  · intro hC n G hG hc g hr ht
    obtain ⟨p, hp⟩ := hG.exists_l1_jung_gain_potential 1 (by decide) hc g 1 (by norm_num) hr ht
    exact ⟨p, fun a b hab => (by norm_num at hp; exact hp a b hab : ‖g a b - (p b - p a)‖ ≤ 1).trans hC⟩
end SimpleGraph
namespace SimpleGraph.BanachPathPower

/-- The sub-two feasibility assertion for the normalized cyclic cochain on the
width-three path with twenty-seven vertices. -/
def subtwo_cyclic_path_claim : Prop :=
  letI := ChordalPath49.cayleyMetric
  ∃ p : Fin 27 → ChordalPath49.M, ∀ a b, (pathPower 27 3).Adj a b →
    Dist.dist (Multiplicative.ofAdd (ChordalPath49.skew
      (fun i j => ChordalPath49.forwardGain i (j - i)) a b)) ((p a)⁻¹ * p b) < 2

private theorem no_cyclic_subtwo_fit : ¬ subtwo_cyclic_path_claim := by
  let := ChordalPath49.cayleyMetric
  let f := fun i j : ℕ => ChordalPath49.forwardGain i (j - i)
  intro h
  change ∃ p : Fin 27 → ChordalPath49.M, ∀ a b, (pathPower 27 3).Adj a b →
    Dist.dist (Multiplicative.ofAdd (ChordalPath49.skew f a b)) ((p a)⁻¹ * p b) < 2 at h
  obtain ⟨p, hp⟩ := h
  apply (ChordalPath49.exact_word_optimum_two (N := 27) (by decide)).2
  refine ⟨fun v => Multiplicative.toAdd (p v), fun a b hab hspan => ?_⟩
  have hadj : (pathPower 27 3).Adj a b := ⟨fun h => (Nat.ne_of_lt hab) (congrArg Fin.val h),
    by omega, hspan⟩
  have hfit := hp a b hadj
  let x := ChordalPath49.skew f a b
  let y := -Multiplicative.toAdd (p a) + Multiplicative.toAdd (p b)
  change Dist.dist (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) < 2 at hfit
  change (GroupWordMetric.length ChordalPath49.letters_generate
    ((Multiplicative.ofAdd x)⁻¹ * Multiplicative.ofAdd y) : ℝ) < 2 at hfit
  have hlt : GroupWordMetric.length ChordalPath49.letters_generate
    ((Multiplicative.ofAdd x)⁻¹ * Multiplicative.ofAdd y) < 2 := by exact_mod_cast hfit
  have hunit : Dist.dist (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) ≤ (1 : ℝ) := by
    change (GroupWordMetric.length ChordalPath49.letters_generate _ : ℝ) ≤ 1
    exact_mod_cast (show GroupWordMetric.length ChordalPath49.letters_generate
      ((Multiplicative.ofAdd x)⁻¹ * Multiplicative.ofAdd y) ≤ 1 by omega)
  simpa [x, y, f, ChordalPath49.skew, hab, sub_eq_add_neg, add_comm] using
    (ChordalPath49.word_iff_distance 1 x y).1 (by simpa using hunit)
end SimpleGraph.BanachPathPower
namespace SimpleGraph.PairRetention

/-- The sharp extension recurrence and an exponential-length cycle give
the exact reconstruction coefficient of the arbitrary-depth pair-retention family. -/
theorem family_exact (m n D : ℕ) (hm : 3 ≤ m)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] (C : ℝ) :
    Upper (family m n D).graph E C ↔ 1 - 2 / ((m : ℝ) * (n + 1 : ℝ)^D) ≤ C := by
  have hroot : Upper (⊤ : SimpleGraph (Fin m)) E (1 - 2 / (m : ℝ)) := by
    intro g hr ht
    have hc : 2 ≤ Nat.card (Fin m) := by simpa using (show 2 ≤ m by omega)
    obtain ⟨p, hp⟩ := completeGraph_banach_upper_bound hc g 1 hr
      (fun a b c hab hbc hac => ht a b c hab hbc hac)
    have hmR : (m : ℝ) ≠ 0 := by positivity
    have he : ((m : ℝ) - 2) / m = 1 - 2 / m := by field_simp
    exact ⟨p, fun a b hab => by
      simpa [residual, Nat.card_eq_fintype_card, he] using hp a b hab⟩
  obtain ⟨hupper, g, hr, ht, hlow⟩ := family_matching_bounds m n D hm hroot
  constructor
  · intro h
    obtain ⟨p, hp⟩ := h g hr ht
    obtain ⟨a, b, hab, hb⟩ := hlow p
    exact hb.trans (hp a b hab)
  · intro h g hr ht
    obtain ⟨p, hp⟩ := hupper g hr ht
    exact ⟨p, fun a b hab => (hp a b hab).trans h⟩
end SimpleGraph.PairRetention
namespace SimpleGraph.BanachPathPower

/-- Every finite family in the target gives a lower bound on a uniform
power-path coefficient through its enclosing radius. -/
theorem powerPath_uniform_ge_doubled_radius {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {k : ℕ} (hk : 0 < k) {C r : ℝ} (hC : 0 ≤ C)
    (hfit : ∀ n, PairRetention.Upper (pathPower n k) E C)
    (x : Fin k → E) (hd : ∀ a b, ‖x a - x b‖ ≤ 1)
    (hr : ∀ y : E, ∃ a, r ≤ ‖(2 : ℝ) • x a - y‖) :
    r ≤ C := by
  by_contra! hlt
  obtain ⟨M, hM⟩ := exists_nat_gt (2 * C / (r - C))
  have hC' : 0 ≤ 2 * C / (r - C) := by positivity
  have hMR : 0 < (M : ℝ) := hC'.trans_lt hM
  have hMp : 0 < M := by exact_mod_cast hMR
  let a₀ : Fin k := ⟨0, hk⟩
  let u : Fin k → E := fun a => x a - x a₀
  have hu (a b : Fin k) : ‖u a - u b‖ ≤ 1 := by
    dsimp [u]
    rw [show x a - x a₀ - (x b - x a₀) = x a - x b by abel]
    exact hd a b
  obtain ⟨g, hg, ht, hball⟩ := exists_gain_for_doubled_radius hk hMp u 1
    (fun a => hd a a₀) hu
  obtain ⟨p, hp⟩ := hfit _ g hg ht
  obtain ⟨y, hy⟩ := hball p C hC hp
  obtain ⟨a, ha⟩ := hr (y + (2 : ℝ) • x a₀)
  have he : (2 : ℝ) • x a - (y + (2 : ℝ) • x a₀) = (2 : ℝ) • u a - y := by
    dsimp [u]
    rw [smul_sub]
    abel
  rw [he] at ha
  have hsmall : 2 * C / (M : ℝ) < r - C := by
    apply (div_lt_iff₀ hMR).2
    simpa [mul_comm] using (div_lt_iff₀ (sub_pos.mpr hlt)).1 hM
  linarith [ha.trans (hy a)]
end SimpleGraph.BanachPathPower
namespace SimpleGraph.BanachPathPower

/-- Euclidean targets attain the regular-simplex obstruction in the supremum
over path lengths at each positive width. -/
theorem hilbert_powerPath_uniform_lower {k : ℕ} (hk : 0 < k) {C : ℝ} (hC : 0 ≤ C)
    (hfit : ∀ n, PairRetention.Upper (pathPower n k) (EuclideanSpace ℝ (Fin k)) C) :
    Real.sqrt (2 - 2 / (k : ℝ)) ≤ C := by
  obtain ⟨x, hd, hr⟩ := FiniteHilbertJung.exists_diameter_one_simplex k hk
  exact powerPath_uniform_ge_doubled_radius hk hC hfit x hd hr
end SimpleGraph.BanachPathPower
namespace SimpleGraph.BanachPathPower

/-- At each positive even width, a finite-dimensional real L1 target attains
the Banach path-power coefficient in the supremum over path lengths. -/
theorem l1_even_powerPath_exact (m : ℕ) (hm : 0 < m) (C : ℝ) :
    (0 ≤ C ∧ ∀ n, PairRetention.Upper (pathPower n (2 * m))
      (PiLp 1 (fun _ : ChordalL1.BalancedCutCoordinate m => ℝ)) C) ↔
      2 - 2 / (2 * (m : ℝ)) ≤ C := by
  have hk : 0 < 2 * m := by omega
  constructor
  · rintro ⟨hC, hfit⟩
    obtain ⟨x, hd, hr⟩ := ChordalL1.exists_balanced_l1_family m hm
    exact powerPath_uniform_ge_doubled_radius hk hC hfit x hd hr
  · intro hC
    have hmR : 1 ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m from hm)
    have hbound : (0 : ℝ) ≤ 2 - 2 / (2 * (m : ℝ)) := by
      have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m)).2
        (show (2 : ℝ) ≤ 2 * (2 * (m : ℝ)) by linarith)
      linarith
    refine ⟨hbound.trans hC, fun n g hr ht => ?_⟩
    obtain ⟨p, hp⟩ := pathPower_banach_upper_bound n (2 * m) hk g 1 zero_le_one hr ht
    refine ⟨p, fun u v huv => (hp u v huv).trans ?_⟩
    simpa [Nat.cast_mul] using hC
end SimpleGraph.BanachPathPower
namespace SimpleGraph.BanachPathPower

open ChordalEightVertex in
/-- The split-graph witness attains the clique-four group coefficient in a finite abelian group. -/
theorem split_clique_four_group_witness :
    letI := cayleyMetric
    graph.IsChordal ∧ (∀ s : Finset V, graph.IsClique (s : Set V) → s.card ≤ 4) ∧
    (∃ A : Set V, graph.IsClique A ∧ graph.IsIndepSet Aᶜ) ∧
    (∀ u v w, graph.Adj u v → graph.Adj v w → graph.Adj u w →
      Dist.dist (Multiplicative.ofAdd (ChordalEightVertex.gain u v + ChordalEightVertex.gain v w))
        (Multiplicative.ofAdd (ChordalEightVertex.gain u w)) ≤ 1) ∧
    (∃ p : V → M, ∀ u v, graph.Adj u v →
      Dist.dist (Multiplicative.ofAdd (ChordalEightVertex.gain u v)) ((p u)⁻¹ * p v) ≤ 2) ∧
    (∀ p : V → M, ∃ u v, graph.Adj u v ∧
      2 ≤ Dist.dist (Multiplicative.ofAdd (ChordalEightVertex.gain u v)) ((p u)⁻¹ * p v)) := by
  let := cayleyMetric
  let := cayley_left
  let := cayley_right
  let A : Set V := {u | u.val < 4}
  have hc : graph.IsClique A := fun _ hu _ hv hne => split_partition.1 _ _ hu hv hne
  have hd : graph.IsIndepSet Aᶜ := fun u hu v hv _ =>
    split_partition.2 u v (by exact Nat.le_of_not_lt hu) (by exact Nat.le_of_not_lt hv)
  obtain ⟨p, hp⟩ := (exists_two_approximate_gain_potential_of_split A hc hd
    (fun u v => Multiplicative.ofAdd (ChordalEightVertex.gain u v)) 1 (by norm_num)
    (fun u v _ => congrArg Multiplicative.ofAdd (gain_reverse u v)) triangle_metric).2
  exact ⟨graph_chordal, clique_card_le_four, ⟨A, hc, hd⟩, triangle_metric,
    ⟨p, fun u v huv => by simpa using hp u v huv⟩, exists_metric_residual_ge_two⟩

open ChordalEightVertex in
/-- A sub-two fit on at least one of the two specified finite abelian witnesses. -/
def subtwo_finite_group_claim : Prop :=
  subtwo_cyclic_path_claim ∨ (letI := cayleyMetric
    ∃ p : V → M, ∀ u v, graph.Adj u v →
      Dist.dist (Multiplicative.ofAdd (ChordalEightVertex.gain u v)) ((p u)⁻¹ * p v) < 2)

/-- Each of the finite abelian cochains obstructs a sub-two fit. -/
theorem not_subtwo_finite_group : ¬ subtwo_finite_group_claim := by
  rintro (h | ⟨p, hp⟩)
  · exact no_cyclic_subtwo_fit h
  · obtain ⟨u, v, huv, h⟩ := ChordalEightVertex.exists_metric_residual_ge_two p
    exact h.not_gt (hp u v huv)
end SimpleGraph.BanachPathPower

namespace ChordalL1

open MeasureTheory

/-- The sharp radius for at most two m or two m plus one unit-diameter points,
uniformly over real L1 spaces. The lower bound uses a finite counting measure. -/
theorem l1_uniform_jung_exact (m k : ℕ) (hm : 0 < m) (hmk : 2 * m ≤ k)
    (hk : k ≤ 2 * m + 1) (C : ℝ) :
    (∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (s : Finset (Lp ℝ 1 μ)),
      s.card ≤ k → (∀ a ∈ s, ∀ b ∈ s, ‖a - b‖ ≤ 1) →
      ∃ c : Lp ℝ 1 μ, ∀ a ∈ s, ‖a - c‖ ≤ C) ↔ 1 - 1 / (2 * (m : ℝ)) ≤ C := by
  classical
  constructor
  · intro h
    let Ω := BalancedCutCoordinate m
    let : MeasurableSpace Ω := ⊤
    let μ : Measure Ω := Measure.count
    obtain ⟨x, hd, hr⟩ := exists_counting_radius_obstruction m hm
    let s := Finset.univ.image x
    have hs : s.card ≤ k := by
      have hcard := Finset.card_image_le (s := (Finset.univ : Finset (Fin (2 * m)))) (f := x)
      exact (by simpa [s] using hcard : s.card ≤ 2 * m).trans hmk
    obtain ⟨c, hc⟩ := h Ω μ s hs (by
      rintro _ ha _ hb
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hb
      exact hd a b)
    obtain ⟨a, ha⟩ := hr c
    exact ha.trans (hc (x a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩))
  · intro h Ω _ μ s hs hd
    obtain ⟨c, hc⟩ := exists_center_finset_odd m hm s id zero_le_one
      (hs.trans hk) (fun a ha b hb => hd a ha b hb)
    exact ⟨c, fun a ha => (hc a ha).trans (by simpa using h)⟩

end ChordalL1
namespace SimpleGraph.CliqueTreeGroupSeparator
open Classical
universe u v w
variable {V : Type u} {I : Type v} {H : Type w}
  [Group H] [PseudoMetricSpace H]
  [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H]
  {T : SimpleGraph I} {G : SimpleGraph V} {K : I → Set V}

/-- General separator bound. The bag index type may be infinite; only the vertex
type is finite. No completeness, commutativity, or separation of points is needed. -/
theorem cliqueTree_separator_group_potential [Finite V]
    (hK : IsCliqueTree T G K)
    (hs : ∀ a b, T.Adj a b → (K a ∩ K b).Nonempty)
    (s : ℕ) (hsep : ∀ a b, T.Adj a b → (K a ∩ K b).ncard ≤ s)
    (g : V → V → H) (δ : ℝ) (hδ : 0 ≤ δ)
    (hrev : ∀ x y, G.Adj x y → g y x = (g x y)⁻¹)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj x z →
      Dist.dist (g x y * g y z) (g x z) ≤ δ) :
    ∃ φ : V → H, ∀ x y, G.Adj x y →
      Dist.dist (g x y) ((φ x)⁻¹ * φ y) ≤ (max 1 s : ℕ) * δ := by
  let := Fintype.ofFinite V
  let : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  by_cases hv : Nonempty V
  · let := hv
    let := hK.isTree.connected.nonempty
    let r : I := Classical.choice inferInstance
    let hne := bags_nonempty hK hs
    let R := RootedAncestors.ofTree hK.isTree r
    let a := oldest R K hne
    let g' := diagonalGain g
    have gz (x : V) : g' x x = 1 := by simp [g', diagonalGain]
    have ge (x y : V) (h : G.Adj x y) : g' x y = g x y := by
      simp [g', diagonalGain, h.ne]
    have gr (x y : V) (h : G.Adj x y) : g' y x = (g' x y)⁻¹ := by
      rw [ge y x h.symm, ge x y h, hrev x y h]
    have gt (x y z : V) (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : G.Adj x z) :
        Dist.dist (g' x y * g' y z) (g' x z) ≤ δ := by
      rw [ge x y hxy, ge y z hyz, ge x z hxz]; exact htri x y z hxy hyz hxz
    obtain ⟨φ, hφ⟩ := exists_frozen_potential hK r a g'
    have forward {b : I} {x y : V} (hx : x ∈ K b) (hy : y ∈ K b)
        (hxy : birthIndex R K b x ≤ birthIndex R K b y) :
        Dist.dist (φ x * g' x y) (φ y) ≤ (max 1 s : ℕ) * δ := by
      rw [hφ b x hx, hφ b y hy]
      exact frozen_forward_bound hK r hne hs s hsep g' hδ gz gr gt b x y hx hy hxy
    refine ⟨φ, fun x y hxy => ?_⟩
    obtain ⟨b, hx, hy⟩ := hK.edge x y hxy
    have hres : Dist.dist (g x y) ((φ x)⁻¹ * φ y) = Dist.dist (φ x * g' x y) (φ y) := by
      rw [ge x y hxy, ← dist_mul_left (φ x), mul_inv_cancel_left]
    rw [hres]
    rcases le_total (birthIndex R K b x) (birthIndex R K b y) with hle | hle
    · exact forward hx hy hle
    · have hf := forward hy hx hle
      have he : Dist.dist (φ x * g' x y) (φ y) = Dist.dist (φ y * g' y x) (φ x) := by
        rw [gr x y hxy]
        calc
          _ = Dist.dist (φ y) (φ x * g' x y) := _root_.dist_comm _ _
          _ = _ := by
            have hh := dist_mul_right (φ y * (g' x y)⁻¹) (φ x) (g' x y)
            simpa only [inv_mul_cancel_right] using hh
      rw [he]; exact hf
  · exact ⟨fun _ => 1, fun x => (hv ⟨x⟩).elim⟩
end SimpleGraph.CliqueTreeGroupSeparator
namespace SimpleGraph.CliqueTreeL1Separator

open MeasureTheory
universe u v w
variable {V : Type u} {I : Type w} {G : SimpleGraph V} {T : SimpleGraph I} {K : I → Set V}
variable {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Uniform L1 reconstruction on arbitrary finite clique-tree bags, with adjacent
intersections of size at most 2, 3, 4, or 5. Neither bag sizes nor depth are bounded. -/
theorem cliqueTree_l1_separator_potential [Finite V] [Finite I]
    (hK : IsCliqueTree T G K)
    (q : ℕ) (hq : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5)
    (hsep : ∀ a b, T.Adj a b → (K a ∩ K b).ncard ≤ q)
    (g : V → V → Lp ℝ 1 μ) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j) (htri : TriangleFlat G g ε) :
    ∃ φ : V → Lp ℝ 1 μ, ∀ u v, G.Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ coefficient q * ε := by
  classical
  let := Fintype.ofFinite I
  obtain ⟨r⟩ := hK.isTree.connected.nonempty
  obtain ⟨parent, hpar, hedge⟩ := rooted_layers hK.isTree r
  let p₀ (v : V) : Lp ℝ 1 μ := if h : (K r).Nonempty then g h.choose v else 0
  refine invariant_layers hK g ε (coefficient q) ?_ (T.dist r) parent hpar hedge p₀ ?_
    (Finset.univ.sup (T.dist r)) (fun a => Finset.le_sup (f := T.dist r) (Finset.mem_univ a))
  · intro a b hab p hp
    let S := bag (K a ∩ K b)
    have hSA : (S : Set V) ⊆ K b := fun x hx => (mem_bag.mp hx).2
    obtain ⟨p', heq, hfit⟩ := extend_small_separator hSA (hK.clique b) q hq
      (by simpa [S] using hsep a b hab) g ε hε hrev htri p
      (fun u hu v hv huv => hp u (mem_bag.mp hu) v (mem_bag.mp hv) huv)
    exact ⟨p', fun x hx => heq x (mem_bag.mpr hx), hfit⟩
  · intro a ha u hu v hv huv
    have har : a = r := (hK.isTree.connected.dist_eq_zero_iff.mp ha).symm
    subst a
    have hn : (K r).Nonempty := ⟨u, hu⟩
    simp only [p₀, dite_eq_left hn]
    have hR : 1 ≤ coefficient q := by rcases hq with rfl | rfl | rfl | rfl <;> norm_num [coefficient]
    exact (defect_bound g ε hε hrev htri (fun _ => huv)
      (fun h => hK.clique r hn.choose_spec hu h)
      (fun h => hK.clique r hn.choose_spec hv h)).trans
        (by simpa using mul_le_mul_of_nonneg_right hR hε)
end SimpleGraph.CliqueTreeL1Separator
namespace SimpleGraph

variable {V H : Type*} [Group H] [PseudoMetricSpace H]
  [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H] {G : SimpleGraph V}

/-- A clique-number bound also holds for graphs presented without a clique tree. -/
theorem IsChordal.exists_clique_number_group_gain_potential [Finite V] (hG : G.IsChordal)
    (k : ℕ) (hk : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ k)
    (g : V → V → H) (ε : ℝ) (hε : 0 ≤ ε)
    (hr : ∀ a b, G.Adj a b → g b a = (g a b)⁻¹)
    (ht : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      Dist.dist (g a b * g b c) (g a c) ≤ ε) :
    ∃ p : V → H, ∀ a b, G.Adj a b →
      Dist.dist (g a b) ((p a)⁻¹ * p b) ≤ ((k - 1 : ℕ) : ℝ) * ε := by
  classical
  by_cases hsmall : k ≤ 2
  · have flat (a b c : V) (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) :
        g a b * g b c = g a c := by
      let s : Finset V := {a, b, c}
      have hcl : G.IsClique (s : Set V) := by
        intro x hx y hy hne
        simp only [s, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        all_goals first | contradiction | assumption | exact hab.symm | exact hbc.symm | exact hac.symm
      have hs : s.card = 3 := by simp [s, hab.ne, hbc.ne, hac.ne]
      have := hk s hcl
      omega
    obtain ⟨p, hp⟩ := hG.exists_gain_potential g hr flat
    refine ⟨p, fun a b hab => ?_⟩
    rw [hp a b hab]
    have hz : Dist.dist ((p a)⁻¹ * p b) ((p a)⁻¹ * p b) = 0 := _root_.dist_self _
    rw [hz]
    positivity
  · have enlarge {C : ℝ} (hC : C ≤ (↑(k - 1 : ℕ) : ℝ))
        (h : ∃ p : V → H, ∀ a b, G.Adj a b →
          Dist.dist (g a b) ((p a)⁻¹ * p b) ≤ C * ε) :
        ∃ p : V → H, ∀ a b, G.Adj a b →
          Dist.dist (g a b) ((p a)⁻¹ * p b) ≤ (↑(k - 1 : ℕ) : ℝ) * ε := by
      obtain ⟨p, hp⟩ := h
      exact ⟨p, fun a b hab => (hp a b hab).trans (mul_le_mul_of_nonneg_right hC hε)⟩
    by_cases hmid : k ≤ 4
    · exact enlarge (by exact_mod_cast (show 2 ≤ k - 1 by omega))
        (hG.exists_clique_four_group_gain_potential (fun s hs => (hk s hs).trans hmid) g hε hr ht)
    · exact enlarge (by exact_mod_cast (show 4 ≤ k - 1 by omega))
        (hG.exists_uniform_approximate_gain_potential g ε hε hr ht)
end SimpleGraph
namespace SimpleGraph.CliqueTreeBanachOverlap
universe u v w
variable {V : Type u} {I : Type w} {G : SimpleGraph V} {T : SimpleGraph I} {K : I → Set V}
variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

open CliqueTreeL1Separator

/-- Arbitrary finite clique-tree Banach upper bound two under the mixed separator rules. -/
theorem cliqueTree_banach_two [Finite V] [Finite I] (hK : IsCliqueTree T G K)
    (r : I) (hsep : ∀ a, a ≠ r → Allowed K r (rootParent hK.isTree r) a)
    (g : V → V → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hrev : ∀ i j, g j i = -g i j) (htri : TriangleFlat G g ε) :
    ∃ φ : V → E, ∀ u v, G.Adj u v → ‖g u v - (φ v - φ u)‖ ≤ 2 * ε := by
  exact rooted_banach_two hK r (rootParent hK.isTree r)
    (rooted_layers hK.isTree r).choose_spec.1 (rooted_layers hK.isTree r).choose_spec.2
    hsep g ε hε hrev htri
end SimpleGraph.CliqueTreeBanachOverlap

namespace Omega.RollingCliques.SpanOne
variable {M n k : ℕ} {hM : 2 ≤ M} {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Reconstruction on span-one rolling clique graphs has coefficient two minus two over M squared. -/
theorem exists_potential (g : Vertex M n k hM → Vertex M n k hM → E)
    (ε : ℝ) (hε : 0 ≤ ε) (hrev : ∀ u v, g v u = -g u v)
    (htri : ∀ u v z, (graph M n k hM).Adj u v → (graph M n k hM).Adj v z →
      (graph M n k hM).Adj u z → ‖g u v + g v z - g u z‖ ≤ ε) :
    ∃ φ : Vertex M n k hM → E, ∀ u v, (graph M n k hM).Adj u v →
      ‖g u v - (φ v - φ u)‖ ≤ (2 - 2 / (M : ℝ)^2) * ε :=
  ⟨fun v => potential g v.1 v.2, potential_bound g ε hε hrev htri⟩
end Omega.RollingCliques.SpanOne
