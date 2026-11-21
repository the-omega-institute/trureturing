/- GID: D5/S3/Combinatorics/Graph/CommonNeighborhood/GroupCentralizerBound
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/CommonNeighborhood/GroupCentralizerBound
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.CommonNeighborhood.NeighbourhoodCliqueBound]
   utility: none
   digest: Every finite nonabelian group has (p^2 - 1)z <= n, z | n and noncentral commuting-graph CN energy at most 2 sum max(|C(x)| - z - 2, 0) <= n max(2(n + z)/p - 2z - 4, 0), below both 2n((n + z)/p - z - 1) and n(n - z - 2) < 2(n - 1)(n - 2). -/

import D5.S3.Combinatorics.Graph.CommonNeighborhood.NeighbourhoodCliqueBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Centralizer and least-prime bounds for the commuting graph of a finite nonabelian group. -/

noncomputable section

namespace D5.S3.Combinatorics.Graph.CommonNeighborhood.GroupCentralizerBound

attribute [local instance] Classical.propDecidable

/-
proof_shape:
  prime_mul_card_le, prime_sq_center_le, center_dvd: bind-only (consumer: result)
  result: content
direct frozen dependencies:
  D5/S3/Combinatorics/Graph/CommonNeighborhood/NeighbourhoodCliqueBound.result
    (statement_id sha256:6fcb98eb465071d206530ed3b2e307ffef56bce840c1e7703998475368c42ded)
  D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound.Vertex, commutingGraph,
    degree_and_center_le_centralizer (statement_id STATEMENT_ID_NONCENTRAL)
escape_witness: the public conclusion itself (form 2): no frozen predecessor provides the
  least-prime chain. The index of a proper centralizer C(x) is a divisor of |G| exceeding one, so
  it is at least the least prime p dividing |G| and p |C(x)| <= |G|; the center is a proper
  subgroup of C(x) whose index is likewise at least p, so p^2 z <= |G|. With the frozen
  inequality deg(x) + z + 1 <= |C(x)| and the neighbourhood-clique bound these give the energy
  chain through n max(2(n + z)/p - 2z - 4, 0) and the order bound (p^2 - 1) z <= n.
admission_basis: escape-witness
-/

open Finset
open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation (graphEnergy)
open D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound (Vertex commutingGraph)

section Centralizer

variable {G : Type} [Group G] [Fintype G]

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

/-- The center is a proper subgroup of a proper centralizer, of index at least `p`:
`p² z ≤ |G|`. -/
private theorem prime_sq_center_le (x : Vertex G) :
    (Fintype.card G).minFac ^ 2 * Fintype.card (Subgroup.center G) ≤ Fintype.card G := by
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
  have hKG : Fintype.card K ∣ Fintype.card G := by
    simpa only [Nat.card_eq_fintype_card] using K.card_subgroup_dvd_card
  have hlt : Fintype.card Z < Fintype.card K := by
    have hle' : Nat.card Z ≤ Nat.card K := Subgroup.card_le_of_le hle
    have hne' : Nat.card Z ≠ Nat.card K := fun h => hne (Subgroup.eq_of_le_of_card_ge hle h.ge)
    simp only [Nat.card_eq_fintype_card] at hle' hne'
    omega
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : 2 ≤ c := by
    rcases c with _ | _ | c
    · simp at hc
    · simp at hc; omega
    · omega
  have hcG : c ∣ Fintype.card G := (Dvd.intro_left _ hc.symm).trans hKG
  have hpc : (Fintype.card G).minFac ≤ c := Nat.minFac_le_of_dvd hc2 hcG
  have h1 := prime_mul_card_le x
  calc (Fintype.card G).minFac ^ 2 * Fintype.card Z
      = (Fintype.card G).minFac * ((Fintype.card G).minFac * Fintype.card Z) := by ring
    _ ≤ (Fintype.card G).minFac * (c * Fintype.card Z) := by gcongr
    _ = (Fintype.card G).minFac * Fintype.card K := by rw [hc]; ring
    _ ≤ Fintype.card G := h1

/-- Lagrange: the order of the center divides the order of the group. -/
private theorem center_dvd : Fintype.card (Subgroup.center G) ∣ Fintype.card G := by
  simpa only [Nat.card_eq_fintype_card] using (Subgroup.center G).card_subgroup_dvd_card

end Centralizer

/-- Let `G` be a finite nonabelian group. Write `z` for the order of its center, `n` for the
number of noncentral elements, `C(x)` for the centralizer of `x` and `p` for the least prime
dividing `|G|`. Then `z ≥ 1`, `n ≥ (p² - 1)z`, `n ≥ z + 2 ≥ 3` and `z ∣ n`, and the common-neighbourhood
energy of the commuting graph on the noncentral elements satisfies
`E ≤ 2 Σ_x max(|C(x)| - z - 2, 0) ≤ n·max(2(n + z)/p - 2z - 4, 0)`, which is at most both
`2n((n + z)/p - z - 1)` and `n·max(n - z - 4, 0) ≤ n(n - z - 2) < 2(n - 1)(n - 2)`. -/
theorem result (G : Type) [Group G] [Fintype G]
    (nonabelian : ∃ a b : G, a * b ≠ b * a) :
    1 ≤ Fintype.card (Subgroup.center G) ∧
      ((Fintype.card G).minFac ^ 2 - 1) * Fintype.card (Subgroup.center G) ≤
        Fintype.card (Vertex G) ∧
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
  have h4 := prime_sq_center_le (⟨a, ha⟩ : Vertex G)
  have hp2 : 2 ≤ (Fintype.card G).minFac := (Nat.minFac_prime (by
    have := Fintype.card_pos_iff.mpr ⟨(1 : G)⟩
    have hb : (1 : G) ≠ a := fun h => ha (h ▸ (Subgroup.center G).one_mem)
    have : 1 < Fintype.card G := Fintype.one_lt_card_iff.mpr ⟨1, a, hb⟩
    omega)).two_le
  have hpsq : (Fintype.card G).minFac ^ 2 * z ≤ n + z := by rw [hn]; exact h4
  have hpz : ((Fintype.card G).minFac ^ 2 - 1) * z ≤ n := by
    have h4le : 4 ≤ (Fintype.card G).minFac ^ 2 := by nlinarith
    rw [Nat.sub_mul, one_mul]
    omega
  have h3z : 3 * z ≤ n := by
    have h4le : 4 ≤ (Fintype.card G).minFac ^ 2 := by nlinarith
    have : 3 * z ≤ ((Fintype.card G).minFac ^ 2 - 1) * z := Nat.mul_le_mul_right _ (by omega)
    omega
  have hdvd : z ∣ n := by
    have := center_dvd (G := G)
    rw [← hn] at this
    exact (Nat.dvd_add_right (dvd_refl z)).mp (by rwa [add_comm] at this)
  have hpR : (2 : ℝ) ≤ (Fintype.card G).minFac := by exact_mod_cast hp2
  have hnR : (n : ℝ) + z = Fintype.card G := by exact_mod_cast hn
  have hC (x : Vertex G) : (Fintype.card (Subgroup.centralizer ({x.val} : Set G)) : ℝ) ≤
      ((n : ℝ) + z) / (Fintype.card G).minFac := by
    rw [le_div_iff₀ (by linarith), hnR, mul_comm]
    exact_mod_cast prime_mul_card_le x
  -- one centralizer exceeds the center, so `(n + z)/p ≥ z + 1`
  have hCz : (z : ℝ) + 1 ≤ ((n : ℝ) + z) / (Fintype.card G).minFac := by
    have := hC ⟨a, ha⟩
    have hd : (commutingGraph G).degree ⟨a, ha⟩ + z + 1 ≤
        Fintype.card (Subgroup.centralizer ({a} : Set G)) :=
      NoncentralBound.degree_and_center_le_centralizer G (⟨a, ha⟩ : Vertex G)
    have : ((z : ℝ) + 1) ≤ Fintype.card (Subgroup.centralizer ({a} : Set G)) := by
      have : z + 1 ≤ Fintype.card (Subgroup.centralizer ({a} : Set G)) := by omega
      exact_mod_cast this
    linarith
  have hzR : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have h3R : 3 * (z : ℝ) ≤ n := by exact_mod_cast h3z
  refine ⟨hz, hpz, by omega, by omega, hdvd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hE, -⟩ := NeighbourhoodCliqueBound.result (commutingGraph G)
    refine hE.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    refine Finset.sum_le_sum fun x _ => max_le_max_right _ ?_
    have hd := NoncentralBound.degree_and_center_le_centralizer G x
    have : ((commutingGraph G).degree x : ℝ) + z + 1 ≤
        Fintype.card (Subgroup.centralizer ({x.val} : Set G)) := by exact_mod_cast hd
    linarith
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
