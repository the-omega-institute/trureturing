/- GID: D5/S3/Combinatorics/Graph/CommonNeighborhood/GroupCentralizerBound
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/CommonNeighborhood/GroupCentralizerBound
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.CommonNeighborhood.NeighbourhoodCliqueBound]
   utility: none
   digest: Every finite nonabelian group has n >= 3z, z | n and noncentral commuting-graph CN energy at most 2 sum max(|C(x)| - z - 2, 0) <= n max(2(n + z)/p - 2z - 4, 0), below both 2n((n + z)/p - z - 1) and n(n - z - 2) < 2(n - 1)(n - 2). -/

import D5.S3.Combinatorics.Graph.CommonNeighborhood.NeighbourhoodCliqueBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Centralizer and least-prime bounds for the commuting graph of a finite nonabelian group. -/

noncomputable section

namespace D5.S3.Combinatorics.Graph.CommonNeighborhood.GroupCentralizerBound

attribute [local instance] Classical.propDecidable

/-
proof_shape:
  center_dvd: bind-only, Lagrange for the center (consumer: result)
  centralizer_card_eq, prime_mul_card_le, four_center_le: content (consumer: result)
  result: content
direct frozen dependencies:
  D5/S3/Combinatorics/Graph/CommonNeighborhood/NeighbourhoodCliqueBound.result
    (statement_id sha256:6fcb98eb465071d206530ed3b2e307ffef56bce840c1e7703998475368c42ded)
  D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound.Vertex, commutingGraph
    (definitions; statement_id sha256:4a61e26c582e3a9997b9d862d130ebfd8cd223970eceb985e8b3f0f6933182cd)
escape_witness: the centralizer C(x) of a noncentral element is exactly the disjoint union of the
  center, x and the graph neighbours of x, so deg(x) = |C(x)| - z - 1 (the frozen group module
  proves only the inequality); C(x) is proper, so its index divides |G| and exceeds 1, giving
  p |C(x)| <= |G|; and the center is a proper subgroup of C(x), giving 4z <= |G|. The
  neighbourhood-clique bound turns these into the energy chain.
admission_basis: escape-witness
-/

open Finset
open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation (graphEnergy)
open D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound (Vertex commutingGraph)

section Centralizer

variable {G : Type} [Group G] [Fintype G]

/-- `C(x)` is the disjoint union of the center, `x` and the graph neighbours of `x`. -/
private theorem centralizer_card_eq (x : Vertex G) :
    Fintype.card (Subgroup.centralizer ({x.val} : Set G)) =
      Fintype.card (Subgroup.center G) + 1 + (commutingGraph G).degree x := by
  let Z : Finset G := univ.filter (fun y => y ∈ Subgroup.center G)
  let K : Finset G := univ.filter (fun y => y ∈ Subgroup.centralizer ({x.val} : Set G))
  let N : Finset G := univ.filter
    (fun y => y ∉ Subgroup.center G ∧ y ≠ x.val ∧ x.val * y = y * x.val)
  let e : (commutingGraph G).neighborSet x ≃
      {y : G // y ∉ Subgroup.center G ∧ y ≠ x.val ∧ x.val * y = y * x.val} :=
    { toFun := fun y => ⟨y.val.val, y.val.property,
        fun h => y.property.1 (Subtype.ext h.symm), y.property.2⟩
      invFun := fun y => ⟨⟨y.val, y.property.1⟩,
        ⟨fun h => y.property.2.1 (congrArg Subtype.val h.symm), y.property.2.2⟩⟩
      left_inv := by intro y; rfl
      right_inv := by intro y; rfl }
  have hN : (commutingGraph G).degree x = N.card := by
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    exact (Fintype.card_congr e).trans (Fintype.card_subtype _)
  have hZ : Z.card = Fintype.card (Subgroup.center G) := (Fintype.card_subtype _).symm
  have hK : K.card = Fintype.card (Subgroup.centralizer ({x.val} : Set G)) :=
    (Fintype.card_subtype _).symm
  have hx : x.val ∉ N := by simp [N]
  have hdis : Disjoint Z (insert x.val N) := by
    apply Finset.disjoint_left.mpr
    intro y hy hz
    have hyZ : y ∈ Subgroup.center G := (mem_filter.mp hy).2
    rcases mem_insert.mp hz with h | h
    · subst y; exact x.property hyZ
    · exact (mem_filter.mp h).2.1 hyZ
  have hset : Z ∪ insert x.val N = K := by
    ext y
    simp only [Z, K, N, mem_union, mem_insert, mem_filter, mem_univ, true_and,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro (h | h | h)
      · exact ((Subgroup.mem_center_iff.mp h) x.val).symm
      · subst y; rfl
      · exact h.2.2.symm
    · intro h
      by_cases hc : y ∈ Subgroup.center G
      · exact Or.inl hc
      · by_cases hyx : y = x.val
        · exact Or.inr (Or.inl hyx)
        · exact Or.inr (Or.inr ⟨hc, hyx, h.symm⟩)
  rw [← hK, ← hset, Finset.card_union_of_disjoint hdis, Finset.card_insert_of_notMem hx, hZ, hN]
  ring

/-- `C(x)` is proper, so its index is a divisor of `|G|` exceeding one: `p |C(x)| ≤ |G|`. -/
private theorem prime_mul_card_le (x : Vertex G) :
    (Fintype.card G).minFac * Fintype.card (Subgroup.centralizer ({x.val} : Set G)) ≤
      Fintype.card G := by
  let K := Subgroup.centralizer ({x.val} : Set G)
  have hproper : K ≠ ⊤ := by
    intro h
    exact x.property ((Subgroup.centralizer_eq_top_iff_subset.mp h) (Set.mem_singleton _))
  have hindex : 2 ≤ K.index := K.one_lt_index_of_ne_top hproper
  have hdvd : K.index ∣ Fintype.card G := by
    simpa only [Nat.card_eq_fintype_card] using K.index_dvd_card
  have hp : (Fintype.card G).minFac ≤ K.index := Nat.minFac_le_of_dvd hindex hdvd
  have hcard : Fintype.card K * K.index = Fintype.card G := by
    simpa only [Nat.card_eq_fintype_card] using K.card_mul_index
  calc (Fintype.card G).minFac * Fintype.card K
      ≤ K.index * Fintype.card K := Nat.mul_le_mul_right _ hp
    _ = Fintype.card G := by rw [mul_comm, hcard]

/-- The center is a proper subgroup of a proper centralizer: `4z ≤ |G|`. -/
private theorem four_center_le (x : Vertex G) :
    4 * Fintype.card (Subgroup.center G) ≤ Fintype.card G := by
  let Z := Subgroup.center G
  let K := Subgroup.centralizer ({x.val} : Set G)
  have hle : Z ≤ K := Subgroup.center_le_centralizer _
  have hne : Z ≠ K := by
    intro h
    apply x.property
    have hx : x.val ∈ K := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    rw [← h] at hx
    exact hx
  have hdvd : Fintype.card Z ∣ Fintype.card K := by
    simpa only [Nat.card_eq_fintype_card] using Subgroup.card_dvd_of_le hle
  have hlt : Fintype.card Z < Fintype.card K := by
    have hle' : Nat.card Z ≤ Nat.card K := Subgroup.card_le_of_le hle
    have hne' : Nat.card Z ≠ Nat.card K := fun h => hne (Subgroup.eq_of_le_of_card_ge hle h.ge)
    simp only [Nat.card_eq_fintype_card] at hle' hne'
    omega
  have hZpos : 0 < Fintype.card Z := Fintype.card_pos_iff.mpr ⟨⟨1, Z.one_mem⟩⟩
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : 2 ≤ c := by
    rcases c with _ | _ | c
    · simp at hc
    · simp at hc; omega
    · omega
  have h2 : 2 * Fintype.card K ≤ Fintype.card G := by
    have := prime_mul_card_le x
    have hp : 2 ≤ (Fintype.card G).minFac :=
      (Nat.minFac_prime (by
        have : 1 < Fintype.card K := by omega
        have := Fintype.card_subtype_le (fun y : G => y ∈ K)
        omega)).two_le
    nlinarith
  nlinarith

/-- Lagrange: the order of the center divides the order of the group. -/
private theorem center_dvd : Fintype.card (Subgroup.center G) ∣ Fintype.card G := by
  simpa only [Nat.card_eq_fintype_card] using (Subgroup.center G).card_subgroup_dvd_card

end Centralizer

/-- Let `G` be a finite nonabelian group. Write `z` for the order of its center, `n` for the
number of noncentral elements, `C(x)` for the centralizer of `x` and `p` for the least prime
dividing `|G|`. Then `z ≥ 1`, `n ≥ 3z`, `n ≥ z + 2 ≥ 3` and `z ∣ n`, and the common-neighbourhood
energy of the commuting graph on the noncentral elements satisfies
`E ≤ 2 Σ_x max(|C(x)| - z - 2, 0) ≤ n·max(2(n + z)/p - 2z - 4, 0)`, which is at most both
`2n((n + z)/p - z - 1)` and `n·max(n - z - 4, 0) ≤ n(n - z - 2) < 2(n - 1)(n - 2)`. -/
theorem result (G : Type) [Group G] [Fintype G]
    (nonabelian : ∃ a b : G, a * b ≠ b * a) :
    1 ≤ Fintype.card (Subgroup.center G) ∧
      3 * Fintype.card (Subgroup.center G) ≤ Fintype.card (Vertex G) ∧
      Fintype.card (Subgroup.center G) + 2 ≤ Fintype.card (Vertex G) ∧
      3 ≤ Fintype.card (Vertex G) ∧
      Fintype.card (Subgroup.center G) ∣ Fintype.card (Vertex G) ∧
      graphEnergy (commutingGraph G) .commonNeighbour ≤
        2 * ∑ x : Vertex G,
          max ((Fintype.card (Subgroup.centralizer ({x.val} : Set G)) : ℝ) -
            Fintype.card (Subgroup.center G) - 2) 0 ∧
      2 * ∑ x : Vertex G,
          max ((Fintype.card (Subgroup.centralizer ({x.val} : Set G)) : ℝ) -
            Fintype.card (Subgroup.center G) - 2) 0 ≤
        (Fintype.card (Vertex G) : ℝ) *
          max (2 * ((Fintype.card (Vertex G) : ℝ) + Fintype.card (Subgroup.center G)) /
              (Fintype.card G).minFac - 2 * Fintype.card (Subgroup.center G) - 4) 0 ∧
      (Fintype.card (Vertex G) : ℝ) *
          max (2 * ((Fintype.card (Vertex G) : ℝ) + Fintype.card (Subgroup.center G)) /
              (Fintype.card G).minFac - 2 * Fintype.card (Subgroup.center G) - 4) 0 ≤
        2 * (Fintype.card (Vertex G) : ℝ) *
          (((Fintype.card (Vertex G) : ℝ) + Fintype.card (Subgroup.center G)) /
              (Fintype.card G).minFac - Fintype.card (Subgroup.center G) - 1) ∧
      (Fintype.card (Vertex G) : ℝ) *
          max (2 * ((Fintype.card (Vertex G) : ℝ) + Fintype.card (Subgroup.center G)) /
              (Fintype.card G).minFac - 2 * Fintype.card (Subgroup.center G) - 4) 0 ≤
        (Fintype.card (Vertex G) : ℝ) *
          max ((Fintype.card (Vertex G) : ℝ) - Fintype.card (Subgroup.center G) - 4) 0 ∧
      (Fintype.card (Vertex G) : ℝ) *
          max ((Fintype.card (Vertex G) : ℝ) - Fintype.card (Subgroup.center G) - 4) 0 ≤
        (Fintype.card (Vertex G) : ℝ) *
          ((Fintype.card (Vertex G) : ℝ) - Fintype.card (Subgroup.center G) - 2) ∧
      (Fintype.card (Vertex G) : ℝ) *
          ((Fintype.card (Vertex G) : ℝ) - Fintype.card (Subgroup.center G) - 2) <
        2 * ((Fintype.card (Vertex G) : ℝ) - 1) * ((Fintype.card (Vertex G) : ℝ) - 2) := by
  obtain ⟨a, b, hab⟩ := nonabelian
  have ha : a ∉ Subgroup.center G := fun h => hab ((Subgroup.mem_center_iff.mp h) b).symm
  set z := Fintype.card (Subgroup.center G) with hzdef
  set n := Fintype.card (Vertex G) with hndef
  have hz : 1 ≤ z := Fintype.card_pos_iff.mpr ⟨⟨1, (Subgroup.center G).one_mem⟩⟩
  have hn : n + z = Fintype.card G := by
    have h1 := Fintype.card_subtype_compl (fun x : G => x ∈ Subgroup.center G)
    have h2 : z ≤ Fintype.card G :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    have h3 : Fintype.card {x : G // x ∈ Subgroup.center G} = z := rfl
    simp only [hndef, NoncentralBound.Vertex] at h1 ⊢
    omega
  have h4 := four_center_le (⟨a, ha⟩ : Vertex G)
  have h3z : 3 * z ≤ n := by omega
  have hdvd : z ∣ n := by
    have := center_dvd (G := G)
    rw [← hn] at this
    exact (Nat.dvd_add_right (dvd_refl z)).mp (by rwa [add_comm] at this)
  have hp2 : 2 ≤ (Fintype.card G).minFac := (Nat.minFac_prime (by omega)).two_le
  have hpR : (2 : ℝ) ≤ (Fintype.card G).minFac := by exact_mod_cast hp2
  have hnR : (n : ℝ) + z = Fintype.card G := by exact_mod_cast hn
  have hC (x : Vertex G) : (Fintype.card (Subgroup.centralizer ({x.val} : Set G)) : ℝ) ≤
      ((n : ℝ) + z) / (Fintype.card G).minFac := by
    rw [le_div_iff₀ (by linarith), hnR, mul_comm]
    exact_mod_cast prime_mul_card_le x
  -- one centralizer exceeds the center, so `(n + z)/p ≥ z + 1`
  have hCz : (z : ℝ) + 1 ≤ ((n : ℝ) + z) / (Fintype.card G).minFac := by
    have := hC ⟨a, ha⟩
    have heq := centralizer_card_eq (⟨a, ha⟩ : Vertex G)
    have : ((z : ℝ) + 1) ≤ Fintype.card (Subgroup.centralizer ({a} : Set G)) := by
      have : z + 1 ≤ Fintype.card (Subgroup.centralizer ({a} : Set G)) := by
        rw [heq]; omega
      exact_mod_cast this
    linarith
  have hzR : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have h3R : 3 * (z : ℝ) ≤ n := by exact_mod_cast h3z
  refine ⟨hz, h3z, by omega, by omega, hdvd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hE, -⟩ := NeighbourhoodCliqueBound.result (commutingGraph G)
    refine hE.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [centralizer_card_eq x, ← hzdef]
    push_cast
    ring_nf
  · have hconst : ∀ M : ℝ, (n : ℝ) * M = ∑ _x : Vertex G, M := fun M => by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hndef]
    rw [hconst, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have hx := hC x
    rcases le_total ((Fintype.card (Subgroup.centralizer ({x.val} : Set G)) : ℝ) - z - 2) 0
      with h | h
    · rw [max_eq_right h, mul_zero]; exact le_max_right _ _
    · rw [max_eq_left h]
      refine le_trans ?_ (le_max_left _ _)
      have : 2 * ((n : ℝ) + z) / (Fintype.card G).minFac =
          2 * (((n : ℝ) + z) / (Fintype.card G).minFac) := by ring
      rw [this]; linarith
  · have : 2 * (n : ℝ) * (((n : ℝ) + z) / (Fintype.card G).minFac - z - 1) =
        (n : ℝ) * (2 * (((n : ℝ) + z) / (Fintype.card G).minFac) - 2 * z - 2) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have : 2 * ((n : ℝ) + z) / (Fintype.card G).minFac =
        2 * (((n : ℝ) + z) / (Fintype.card G).minFac) := by ring
    rw [this]
    exact max_le (by linarith) (by linarith)
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply max_le_max_right
    have hq : 2 * ((n : ℝ) + z) / (Fintype.card G).minFac ≤ (n : ℝ) + z := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact max_le (by linarith) (by linarith)
  · nlinarith

#print axioms result

end D5.S3.Combinatorics.Graph.CommonNeighborhood.GroupCentralizerBound
