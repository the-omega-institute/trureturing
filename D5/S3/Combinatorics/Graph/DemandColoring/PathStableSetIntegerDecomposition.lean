/- GID: D5/S3/Combinatorics/Graph/DemandColoring/PathStableSetIntegerDecomposition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DemandColoring/PathStableSetIntegerDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed lattice points in path-polytope dilates split into exactly k admissible words. -/

import D5.S3.Combinatorics.Graph.DemandColoring.BipartiteDemandColoring
import D5.S1.Words.AdmissibleWords.PathStableSetPolytope
import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators Pointwise

namespace D5.S3.Combinatorics.Graph.DemandColoring.PathStableSetIntegerDecomposition

open D5.S1.Words.AdmissibleWords
open AdmissibleCount PathStableSetPolytope
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (adm_iff_no_adjacent_true)
open BipartiteDemandColoring (exists_independent_layers)

/-- Exact natural path demands, using the native total path two-coloring. -/
theorem exists_admissible_layers (n k : ℕ) (z : Fin n → ℕ)
    (hv : ∀ i, z i ≤ k)
    (he : ∀ i j, i.val + 1 = j.val → z i + z j ≤ k) :
    ∃ W : Fin k → Fin n → Bool, (∀ c, Adm n (W c)) ∧
      ∀ i, (Finset.univ.filter (fun c => W c i = true)).card = z i := by
  obtain ⟨W, independent, count⟩ := exists_independent_layers
    (SimpleGraph.pathGraph n) (SimpleGraph.pathGraph.bicoloring n) k z hv (by
      intro u v huv
      rcases SimpleGraph.pathGraph_adj.mp huv with h | h
      · exact he u v h
      · simpa only [Nat.add_comm] using he v u h)
  refine ⟨W, ?_, count⟩
  intro c
  apply (adm_iff_no_adjacent_true n (W c)).mpr
  intro i j hij
  by_contra h
  have both : W c i = true ∧ W c j = true := by
    cases hi : W c i <;> cases hj : W c j <;> simp_all
  exact independent c both.1 both.2
    (by intro e; have := congrArg Fin.val e; omega)
    (SimpleGraph.pathGraph_adj.mpr (Or.inl hij))

private theorem mem_nat_smul_iff (n k : ℕ) (x : Fin n → ℝ) :
    x ∈ (k : ℝ) • polytope n ↔
      (∀ i, 0 ≤ x i ∧ x i ≤ k) ∧
      ∀ i j, i.val + 1 = j.val → x i + x j ≤ k := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have eqi : ∀ i, (k : ℝ) * y i = x i := fun i => congrFun hxy i
    constructor
    · intro i
      constructor
      · rw [← eqi i]; exact mul_nonneg (Nat.cast_nonneg k) (hy.1 i).1
      · rw [← eqi i]
        simpa using mul_le_mul_of_nonneg_left (hy.1 i).2 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    · intro i j hij
      have h := mul_le_mul_of_nonneg_left (hy.2 i j hij) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      simpa only [mul_add, mul_one, eqi] using h
  · rintro ⟨hv, he⟩
    by_cases hk : k = 0
    · subst k
      have hx : x = 0 := by
        funext i
        exact le_antisymm (by simpa using (hv i).2) (hv i).1
      refine ⟨0, ?_, ?_⟩
      · exact ⟨by simp, by simp⟩
      · simp [hx]
    · have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      refine ⟨fun i => x i / k, ?_, ?_⟩
      · constructor
        · intro i
          exact ⟨div_nonneg (hv i).1 hkpos.le, (div_le_one hkpos).mpr (hv i).2⟩
        · intro i j hij
          rw [← add_div]
          exact (div_le_one hkpos).mpr (he i j hij)
      · funext i
        change (k : ℝ) * (x i / k) = x i
        exact mul_div_cancel₀ (x i) (ne_of_gt hkpos)

/-- Every signed lattice point of the genuine scalar image of the existing path polytope
is a sum of exactly k admissible occupancy vectors, and conversely. Empty and repeated layers
are allowed, including k = 0 and the empty path. -/
theorem lattice_mem_nat_smul_polytope_iff (n k : ℕ) (q : Fin n → ℤ) :
    (fun i => (q i : ℝ)) ∈ (k : ℝ) • polytope n ↔
      ∃ W : Fin k → Fin n → Bool,
        (∀ c, Adm n (W c)) ∧
        (fun i => (q i : ℝ)) = ∑ c, occupancy (W c) := by
  classical
  rw [mem_nat_smul_iff]
  constructor
  · rintro ⟨hv, he⟩
    have nonneg : ∀ i, 0 ≤ q i := by
      intro i
      exact_mod_cast (hv i).1
    let z : Fin n → ℕ := fun i => (q i).toNat
    have castz : ∀ i, (z i : ℝ) = (q i : ℝ) := by
      intro i
      exact_mod_cast Int.toNat_of_nonneg (nonneg i)
    obtain ⟨W, admissible, count⟩ := exists_admissible_layers n k z (by
      intro i
      have h : (z i : ℝ) ≤ k := by rw [castz]; exact (hv i).2
      exact_mod_cast h) (by
      intro i j hij
      have h : (z i : ℝ) + z j ≤ k := by rw [castz, castz]; exact he i j hij
      exact_mod_cast h)
    refine ⟨W, admissible, ?_⟩
    funext i
    rw [Finset.sum_apply]
    calc
      (q i : ℝ) = (z i : ℝ) := (castz i).symm
      _ = ((Finset.univ.filter (fun c => W c i = true)).card : ℝ) := by rw [count]
      _ = ∑ c, occupancy (W c) i := by
        simp [occupancy, Finset.sum_boole]
  · rintro ⟨W, admissible, hq⟩
    have member : ∀ c, occupancy (W c) ∈ polytope n := by
      intro c
      rw [← convexHull_vertices]
      exact subset_convexHull ℝ _ ⟨W c, admissible c, rfl⟩
    have eqi : ∀ i, (q i : ℝ) = ∑ c, occupancy (W c) i := by
      intro i
      simpa using congrFun hq i
    constructor
    · intro i
      rw [eqi]
      refine ⟨Finset.sum_nonneg (fun c _ => (member c).1 i |>.1), ?_⟩
      calc
        ∑ c, occupancy (W c) i ≤ ∑ _c : Fin k, (1 : ℝ) :=
          Finset.sum_le_sum (fun c _ => (member c).1 i |>.2)
        _ = k := by simp
    · intro i j hij
      rw [eqi, eqi, ← Finset.sum_add_distrib]
      calc
        ∑ c, (occupancy (W c) i + occupancy (W c) j) ≤ ∑ _c : Fin k, (1 : ℝ) :=
          Finset.sum_le_sum (fun c _ => (member c).2 i j hij)
        _ = k := by simp

end D5.S3.Combinatorics.Graph.DemandColoring.PathStableSetIntegerDecomposition
