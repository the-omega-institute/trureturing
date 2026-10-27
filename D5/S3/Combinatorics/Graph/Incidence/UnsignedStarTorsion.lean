/- GID: D5/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Incidence/UnsignedStarTorsion
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Indexed unsigned star lattices and sparse integer recovery. -/



import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-!
Admission basis: escape-witness (pre-compile statement).
Content: integral_of_bipartite, walk_potential, nonbipartite_potential, potential_remainders,
total_not_in_image, integer_potential_alternative,
integral_of_support_nonbipartite, source_coefficients_of_sparse_multiple.
The live escape is nonbipartite_potential: a propagated pair of opposite
residues either defines a bipartition or collapses to a constant two-torsion
residue. It is used in the remainder, total-class, and integral recovery paths.
Consumed bind-only helpers: edge_residues -> potential_remainders;
recover_divisible -> integer_potential_alternative and integral_of_support_nonbipartite;
sign_bipartite -> integer_potential_alternative and integral_of_support_nonbipartite;
starMap_eq_sum -> source_coefficients_of_sparse_multiple.
No project frozen mathematical premise is imported. Pinned Mathlib supplies
walks, bipartitions, ZMod and integer division, not the unsigned classification.
Attribution: caller's completed primary proof Sections 6-7, SHA256
f776b4a6cba72126daf67658b7c846279a39d61cbdd41f6e2cfdd400f8e487f8.
The unrestricted original integral full-blocker / Good / AM remains open.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Incidence.UnsignedStarTorsion

open scoped BigOperators

/-- Individual original edge indices are retained, even for parallel edges. -/
structure Edges (V X : Type*) where
  left : X → V
  right : X → V
  loopless : ∀ i, left i ≠ right i

namespace Edges

variable {V X : Type*} (g : Edges V X)

/-- Delete indices, then forget multiplicity only for the adjacency relation. -/
def graphAfterDeleting (D : Set X) : SimpleGraph V where
  Adj u v := ∃ i, i ∉ D ∧
    ((g.left i = u ∧ g.right i = v) ∨ (g.left i = v ∧ g.right i = u))
  symm := by
    constructor
    rintro u v ⟨i, hi, h | h⟩
    · exact ⟨i, hi, Or.inr h⟩
    · exact ⟨i, hi, Or.inl h⟩
  loopless := by
    constructor
    rintro u ⟨i, _, h | h⟩ <;> exact g.loopless i (h.1.trans h.2.symm)

/-- The exact integer map, with no saturation of its image. -/
def starMap : (V → ℤ) →ₗ[ℤ] (X → ℤ) where
  toFun a i := a (g.left i) + a (g.right i)
  map_add' a b := by funext i; simp only [Pi.add_apply]; ring
  map_smul' n a := by
    funext i
    change n * a (g.left i) + n * a (g.right i) = n * (a (g.left i) + a (g.right i))
    ring

private theorem walk_potential {A : Type*} [AddCommGroup A]
    {G : SimpleGraph V} (t : V → A)
    (ht : ∀ ⦃u v⦄, G.Adj u v → t u + t v = 0)
    {u v : V} (p : G.Walk u v) : t v = t u ∨ t v = -t u := by
  induction p with
  | nil => exact Or.inl rfl
  | @cons u v w h p ih =>
    have hv : t v = -t u := eq_neg_of_add_eq_zero_right (ht h)
    rcases ih with ih | ih
    · exact Or.inr (ih.trans hv)
    · exact Or.inl (by rw [ih, hv, neg_neg])

/-- Nonbipartiteness forces a potential with opposite adjacent values to be a
constant of order dividing two. The proof constructs a bipartition if the
two propagated signs differ; no coloring or residue classification is assumed. -/
private theorem nonbipartite_potential {A : Type*} [AddCommGroup A]
    {G : SimpleGraph V} (hG : G.Connected) (hn : ¬ G.IsBipartite)
    (t : V → A) (ht : ∀ ⦃u v⦄, G.Adj u v → t u + t v = 0) :
    ∃ c, c + c = 0 ∧ ∀ v, t v = c := by
  classical
  let r : V := Classical.choice hG.nonempty
  have hp (v : V) : t v = t r ∨ t v = -t r :=
    (hG r v).elim (walk_potential t ht)
  have hc : t r = -t r := by
    by_contra hc
    apply hn
    apply SimpleGraph.IsBipartiteWith.isBipartite
      (s := {v | t v = t r}) (t := {v | t v = -t r})
    constructor
    · exact Set.disjoint_left.mpr (fun v h₁ h₂ => hc (h₁.symm.trans h₂))
    · intro u v huv
      have hv : t v = -t u := eq_neg_of_add_eq_zero_right (ht huv)
      rcases hp u with hu | hu
      · exact Or.inl ⟨hu, by simpa [hu] using hv⟩
      · exact Or.inr ⟨hu, by simpa [hu] using hv⟩
  refine ⟨t r, ?_, fun v => (hp v).elim id (fun h => h.trans hc.symm)⟩
  calc
    t r + t r = -t r + t r := congrArg (fun x => x + t r) hc
    _ = 0 := neg_add_cancel _

/-- The exact integer unsigned star map is injective on a connected
nonbipartite original graph. This consumed corollary keeps the general
nonbipartite potential theorem private in its owning module. -/
theorem starMap_injective
    (hc : (g.graphAfterDeleting ∅).Connected)
    (hn : ¬ (g.graphAfterDeleting ∅).IsBipartite) :
    Function.Injective g.starMap := by
  intro a b hab
  have hadj : ∀ ⦃u v⦄, (g.graphAfterDeleting ∅).Adj u v →
      (a u - b u) + (a v - b v) = 0 := by
    rintro u v ⟨i, _, h | h⟩
    all_goals
      have he := congrFun hab i
      change a (g.left i) + a (g.right i) =
        b (g.left i) + b (g.right i) at he
      rw [h.1, h.2] at he
      omega
  obtain ⟨c, hcc, ht⟩ := nonbipartite_potential hc hn
    (fun v => a v - b v) hadj
  funext v
  have hv := ht v
  omega

private theorem edge_residues (k : ℕ) (z : X → ℤ) (a : V → ℤ)
    (ha : ∀ i, (k : ℤ) * z i = g.starMap a i) :
    ∀ ⦃u v⦄, (g.graphAfterDeleting ∅).Adj u v →
      (a u : ZMod k) + (a v : ZMod k) = 0 := by
  rintro u v ⟨i, _, h | h⟩
  all_goals
    have hz : ((a (g.left i) + a (g.right i) : ℤ) : ZMod k) = 0 := by
      change ((g.starMap a i : ℤ) : ZMod k) = 0
      rw [← ha i]
      simp
    simpa [h.1, h.2, add_comm] using hz

/-- On a connected nonbipartite original graph the actual integer coefficients
have one common remainder, either zero or half the positive multiplier. -/
theorem potential_remainders (hc : (g.graphAfterDeleting ∅).Connected)
    (hn : ¬ (g.graphAfterDeleting ∅).IsBipartite)
    (k : ℕ) (hk : 0 < k) (z : X → ℤ) (a : V → ℤ)
    (ha : ∀ i, (k : ℤ) * z i = g.starMap a i) :
    ∃ r : ℤ, 0 ≤ r ∧ r < k ∧ (r = 0 ∨ 2 * r = k) ∧
      ∀ v, a v % (k : ℤ) = r := by
  let : NeZero k := ⟨by omega⟩
  obtain ⟨c, hcc, ht⟩ := nonbipartite_potential hc hn
    (fun v => (a v : ZMod k)) (g.edge_residues k z a ha)
  let r : ℤ := c.val
  have hr0 : 0 ≤ r := by
    change (0 : ℤ) ≤ (c.val : ℤ)
    exact_mod_cast (Nat.zero_le c.val)
  have hrk : r < k := by
    change (c.val : ℤ) < (k : ℤ)
    exact_mod_cast c.val_lt
  have hr (v : V) : a v % (k : ℤ) = r := by
    rw [← ZMod.val_intCast, ht v]
  have hdiv : (k : ℤ) ∣ 2 * r := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hrval : (r : ZMod k) = c := by simp [r]
    simpa [Int.cast_mul, hrval, two_mul] using hcc
  obtain ⟨m, hm⟩ := hdiv
  have hkp : (0 : ℤ) < k := by exact_mod_cast hk
  have hm0 : 0 ≤ m := by
    by_contra h
    have hneg := mul_neg_of_pos_of_neg hkp (show m < 0 by omega)
    nlinarith
  have hm2 : m < 2 := by
    by_contra h
    have hmul := mul_le_mul_of_nonneg_left (show (2 : ℤ) ≤ m by omega) hkp.le
    nlinarith
  refine ⟨r, hr0, hrk, ?_, hr⟩
  rcases (by omega : m = 0 ∨ m = 1) with hm' | hm'
  · left; nlinarith
  · right; nlinarith

private theorem recover_divisible (k : ℕ) (hk : 0 < k) (z : X → ℤ) (a : V → ℤ)
    (ha : ∀ i, (k : ℤ) * z i = g.starMap a i)
    (hd : ∀ v, (k : ℤ) ∣ a v) :
    g.starMap (fun v => a v / (k : ℤ)) = z := by
  funext i
  have hl := Int.ediv_mul_cancel (hd (g.left i))
  have hr := Int.ediv_mul_cancel (hd (g.right i))
  have he := ha i
  change (k : ℤ) * z i = a (g.left i) + a (g.right i) at he
  change a (g.left i) / (k : ℤ) + a (g.right i) / (k : ℤ) = z i
  have hkn : (k : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  apply mul_left_cancel₀ hkn
  nlinarith [hl, hr]

/-- In a connected bipartite original graph, subtract a signed root kernel
from the actual integer potential before proving divisibility and cancelling.
The root and the two colors are obtained from the graph hypotheses. -/
theorem integral_of_bipartite
    (hc : (g.graphAfterDeleting ∅).Connected)
    (hb : (g.graphAfterDeleting ∅).IsBipartite)
    (k : ℕ) (hk : 0 < k) (z : X → ℤ) (a : V → ℤ)
    (ha : ∀ i, (k : ℤ) * z i = g.starMap a i) :
    ∃ b : V → ℤ, g.starMap b = z := by
  classical
  obtain ⟨s, t, hst⟩ := hb.exists_isBipartiteWith
  let e : V → ℤ := fun v => if v ∈ s then 1 else -1
  have he (v : V) : e v = 1 ∨ e v = -1 := by
    dsimp [e]
    split_ifs <;> simp
  have hed : ∀ ⦃u v⦄, (g.graphAfterDeleting ∅).Adj u v → e u + e v = 0 := by
    intro u v huv
    rcases hst.mem_of_adj huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · have hv' : v ∉ s := fun hs => Set.disjoint_left.mp hst.disjoint hs hv
      simp [e, hu, hv']
    · have hu' : u ∉ s := fun hs => Set.disjoint_left.mp hst.disjoint hs hu
      simp [e, hu', hv]
  let r : V := Classical.choice hc.nonempty
  let a' : V → ℤ := fun v => a v - e v * (e r * a r)
  have har : a' r = 0 := by
    rcases he r with hr | hr <;> simp [a', hr]
  have ha' (i : X) : (k : ℤ) * z i = g.starMap a' i := by
    have he' : e (g.left i) + e (g.right i) = 0 :=
      hed ⟨i, by simp, Or.inl ⟨rfl, rfl⟩⟩
    have hi := ha i
    change (k : ℤ) * z i = a (g.left i) + a (g.right i) at hi
    change (k : ℤ) * z i = a' (g.left i) + a' (g.right i)
    dsimp [a']
    have hm := congrArg (fun x : ℤ => x * (e r * a r)) he'
    nlinarith
  have hd (v : V) : (k : ℤ) ∣ a' v := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hp : (a' v : ZMod k) = (a' r : ZMod k) ∨
        (a' v : ZMod k) = -(a' r : ZMod k) :=
      (hc r v).elim (walk_potential (fun w => (a' w : ZMod k))
        (g.edge_residues k z a' ha'))
    rcases hp with hp | hp <;> simpa [har] using hp
  exact ⟨fun v => a' v / (k : ℤ), g.recover_divisible k hk z a' ha' hd⟩

private theorem sign_bipartite (z : X → ℤ) (a : V → ℤ) (k : ℕ)
    (ha : ∀ i, (k : ℤ) * z i = g.starMap a i) (hn : ∀ v, a v ≠ 0) :
    (g.graphAfterDeleting {i | z i ≠ 0}).IsBipartite := by
  apply SimpleGraph.IsBipartiteWith.isBipartite
    (s := {v | 0 < a v}) (t := {v | a v < 0})
  constructor
  · exact Set.disjoint_left.mpr (fun v h₁ h₂ => by dsimp at h₁ h₂; omega)
  · rintro u v ⟨i, hi, h | h⟩
    all_goals
      have hz : z i = 0 := by simpa using hi
      have he := ha i
      change (k : ℤ) * z i = a (g.left i) + a (g.right i) at he
      rw [hz, mul_zero, h.1, h.2] at he
      have hu := hn u
      have hv := hn v
      change (0 < a u ∧ a v < 0) ∨ (a u < 0 ∧ 0 < a v)
      omega

private theorem total_not_in_image
    (hc : (g.graphAfterDeleting ∅).Connected)
    (hn : ¬ (g.graphAfterDeleting ∅).IsBipartite) :
    ¬ ∃ b : V → ℤ, ∀ i, g.starMap b i = 1 := by
  rintro ⟨b, hb⟩
  have ht : ∀ ⦃u v⦄, (g.graphAfterDeleting ∅).Adj u v →
      (2 * b u - 1) + (2 * b v - 1) = 0 := by
    rintro u v ⟨i, _, h | h⟩
    all_goals
      have he := hb i
      change b (g.left i) + b (g.right i) = 1 at he
      rw [h.1, h.2] at he
      omega
  obtain ⟨c, hcc, ht'⟩ := nonbipartite_potential hc hn (fun v => 2 * b v - 1) ht
  have he := ht' (Classical.choice hc.nonempty)
  omega

/-- Every torsion candidate on a connected nonbipartite original graph is
either integral or the full-component class. In the latter case its class is
nonzero, its double is an explicit star combination, and signs color the
graph after deletion of the original support. -/
theorem integer_potential_alternative
    (hc : (g.graphAfterDeleting ∅).Connected)
    (hn : ¬ (g.graphAfterDeleting ∅).IsBipartite)
    (k : ℕ) (hk : 0 < k) (z : X → ℤ) (a : V → ℤ)
    (ha : ∀ i, (k : ℤ) * z i = g.starMap a i) :
    (∃ b : V → ℤ, g.starMap b = z) ∨
      (Even k ∧ (∀ v, a v ≠ 0) ∧
        (∃ b : V → ℤ, (∀ i, z i = g.starMap b i + 1) ∧
          g.starMap (fun v => 2 * b v + 1) = fun i => 2 * z i) ∧
        (¬ ∃ b : V → ℤ, g.starMap b = z) ∧
        (g.graphAfterDeleting {i | z i ≠ 0}).IsBipartite) := by
  obtain ⟨r, hr0, hrk, hr, hv⟩ := g.potential_remainders hc hn k hk z a ha
  rcases hr with hr | hr
  · left
    exact ⟨fun v => a v / (k : ℤ), g.recover_divisible k hk z a ha
      (fun v => Int.dvd_of_emod_eq_zero (by rw [hv v, hr]))⟩
  · right
    have hkn : (k : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    have hrpos : 0 < r := by omega
    have hnz (v : V) : a v ≠ 0 := by
      intro hav
      have := hv v
      simp [hav] at this
      omega
    have hd (v : V) : (k : ℤ) ∣ a v - r := by
      apply Int.dvd_of_emod_eq_zero
      rw [Int.sub_emod, hv v, Int.emod_eq_of_lt hr0 hrk, sub_self, Int.zero_emod]
    let b : V → ℤ := fun v => (a v - r) / (k : ℤ)
    have he (v : V) : (k : ℤ) * b v = a v - r := by
      simpa [b, mul_comm] using Int.ediv_mul_cancel (hd v)
    have hb (i : X) : z i = g.starMap b i + 1 := by
      have hl := he (g.left i)
      have hr' := he (g.right i)
      have hm := ha i
      change (k : ℤ) * z i = a (g.left i) + a (g.right i) at hm
      change z i = b (g.left i) + b (g.right i) + 1
      apply mul_left_cancel₀ hkn
      nlinarith
    have hdbl : g.starMap (fun v => 2 * b v + 1) = fun i => 2 * z i := by
      funext i
      have := hb i
      change z i = b (g.left i) + b (g.right i) + 1 at this
      change (2 * b (g.left i) + 1) + (2 * b (g.right i) + 1) = 2 * z i
      omega
    refine ⟨?_, hnz, ⟨b, hb, hdbl⟩, ?_, g.sign_bipartite z a k ha hnz⟩
    · rw [even_iff_two_dvd]
      have heven : 2 ∣ (k : ℤ) := ⟨r, by omega⟩
      exact_mod_cast heven
    · rintro ⟨b', hb'⟩
      apply g.total_not_in_image hc hn
      refine ⟨fun v => b' v - b v, fun i => ?_⟩
      have h₁ := congrFun hb' i
      have h₂ := hb i
      change b' (g.left i) + b' (g.right i) = z i at h₁
      change z i = b (g.left i) + b (g.right i) + 1 at h₂
      change (b' (g.left i) - b (g.left i)) + (b' (g.right i) - b (g.right i)) = 1
      omega

/-- Sparse torsion localizes to original edges: if deletion of the actual
support is nonbipartite, an actual multiple in the exact image can be
integrated with coefficient one. The deleted graph need not be connected. -/
theorem integral_of_support_nonbipartite
    (hc : (g.graphAfterDeleting ∅).Connected)
    (k : ℕ) (hk : 0 < k) (z : X → ℤ) (a : V → ℤ)
    (hn : ¬ (g.graphAfterDeleting {i | z i ≠ 0}).IsBipartite)
    (ha : ∀ i, (k : ℤ) * z i = g.starMap a i) :
    ∃ b : V → ℤ, g.starMap b = z := by
  have hn₀ : ¬ (g.graphAfterDeleting ∅).IsBipartite := by
    intro hb
    obtain ⟨s, t, hst⟩ := hb.exists_isBipartiteWith
    apply hn
    apply SimpleGraph.IsBipartiteWith.isBipartite (s := s) (t := t)
    refine ⟨hst.disjoint, ?_⟩
    rintro u v ⟨i, _, he⟩
    exact hst.mem_of_adj ⟨i, by simp, he⟩
  obtain ⟨r, _, _, hr, hv⟩ := g.potential_remainders hc hn₀ k hk z a ha
  by_cases hr0 : r = 0
  · refine ⟨fun v => a v / (k : ℤ), g.recover_divisible k hk z a ha ?_⟩
    intro v
    exact Int.dvd_of_emod_eq_zero (by rw [hv v, hr0])
  · exact (hn (g.sign_bipartite z a k ha (fun v hav =>
      hr0 (by simpa [hav] using (hv v).symm)))).elim

/-- The original Boolean star row; distinct endpoints ensure its values are zero or one. -/
def starRow [DecidableEq V] (v : V) (i : X) : ℤ :=
  (if g.left i = v then 1 else 0) + (if g.right i = v then 1 else 0)

private theorem starMap_eq_sum [Fintype V] [DecidableEq V] (a : V → ℤ) (i : X) :
    g.starMap a i = ∑ v, a v * g.starRow v i := by
  simp [starRow, mul_add, Finset.sum_add_distrib, eq_comm, starMap]

/-- Recover actual integer coefficients of the original source rows. Both
source-to-star decompositions and star-to-source certificates are supplied
explicitly; all rows, including larger Boolean rows, participate. The support
bound counts original indices, without identifying parallel edges. -/
theorem source_coefficients_of_sparse_multiple [Fintype V] [DecidableEq V]
    [Fintype X] [DecidableEq X] {H : Type*} [Fintype H]
    (hc : (g.graphAfterDeleting ∅).Connected) (q : ℕ)
    (hrobust : ∀ D : Finset X, D.card ≤ q →
      ¬ (g.graphAfterDeleting (D : Set X)).IsBipartite)
    (rows : H → X → ℤ) (d : H → V → ℤ) (c : V → H → ℤ)
    (hd : ∀ T, g.starMap (d T) = rows T)
    (hcert : ∀ v i, g.starRow v i = ∑ T, c v T * rows T i)
    (k : ℕ) (hk : 0 < k) (z : X → ℤ)
    (hsupport : (Finset.univ.filter (fun i => z i ≠ 0)).card ≤ q)
    (h : H → ℤ) (hmult : ∀ i, (k : ℤ) * z i = ∑ T, h T * rows T i) :
    ∃ b : V → ℤ, g.starMap b = z ∧
      ∀ i, z i = ∑ T, (∑ v, b v * c v T) * rows T i := by
  classical
  let a : V → ℤ := fun v => ∑ T, h T * d T v
  have ha (i : X) : (k : ℤ) * z i = g.starMap a i := by
    rw [hmult]
    change _ = (∑ T, h T * d T (g.left i)) + ∑ T, h T * d T (g.right i)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T _
    have he := congrFun (hd T) i
    change d T (g.left i) + d T (g.right i) = rows T i at he
    rw [← he]
    ring
  have hn : ¬ (g.graphAfterDeleting {i | z i ≠ 0}).IsBipartite := by
    simpa using hrobust (Finset.univ.filter (fun i => z i ≠ 0)) hsupport
  obtain ⟨b, hb⟩ := g.integral_of_support_nonbipartite hc k hk z a hn ha
  refine ⟨b, hb, fun i => ?_⟩
  rw [← congrFun hb i, g.starMap_eq_sum]
  simp_rw [hcert, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro v _
  ring

#print axioms integral_of_bipartite
#print axioms potential_remainders
#print axioms integer_potential_alternative
#print axioms integral_of_support_nonbipartite
#print axioms source_coefficients_of_sparse_multiple

end Edges

end D5.S3.Combinatorics.Graph.Incidence.UnsignedStarTorsion
