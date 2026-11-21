/- GID: D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.CommonNeighborhood.NeighbourhoodCliqueBound]
   utility: none
   digest: Every finite noncommutative ring, associative or not, has n >= 3z, z | n and noncentral commuting-graph CN energy at most 2 sum max(|C(x)| - z - 2, 0) <= n max(2(n + z)/p - 2z - 4, 0) <= n(n - z - 2) < 2(n - 1)(n - 2). -/

/- Escape audit unfinished for result: https://github.com/the-omega-institute/trureturing/issues/32738 -/
import D5.S3.Combinatorics.Graph.CommonNeighborhood.NeighbourhoodCliqueBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Strict common-neighbourhood energy bound for the commuting graph of a finite ring. -/

noncomputable section

namespace D5.S3.Combinatorics.Graph.CommonNeighborhood.RingNoncentralBound

attribute [local instance] Classical.propDecidable

/-
proof_shape:
  ringCenter, Vertex, commutingGraph, centralizerCard: definitions
  addCentralizer: definition (an additive subgroup built from Mathlib's Set.centralizer closure
    lemmas)
  mem_center_iff, mem_single_iff: bind-only (consumers: centralizer_card_eq, prime_mul_card_le,
    four_center_le, result)
  center_dvd: bind-only, Lagrange for the center subgroup (consumer: result)
  centralizer_card_eq, prime_mul_card_le, four_center_le: content (consumer: result)
  result: content
direct frozen dependencies:
  D5/S3/Combinatorics/Graph/CommonNeighborhood/NeighbourhoodCliqueBound.result
    (statement_id sha256:6fcb98eb465071d206530ed3b2e307ffef56bce840c1e7703998475368c42ded)
escape_witness: the centralizer C(x) of a noncentral element is a proper additive subgroup that
  is exactly the disjoint union of the center, x and the graph neighbours of x, so
  deg(x) = |C(x)| - z - 1; its index divides |R| and exceeds 1, so p |C(x)| <= |R| for the least
  prime p dividing |R|; and the center is a proper additive subgroup of C(x), giving
  4z <= |R|. The neighbourhood-clique bound turns these into the energy chain.
admission_basis: escape-witness
-/

open Finset
open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation

/-- The (commutative) center: the elements commuting with every element. -/
def ringCenter (R : Type) [Mul R] : Set R := Set.centralizer Set.univ

/-- The vertices are the individual noncentral elements. -/
abbrev Vertex (R : Type) [Mul R] := {x : R // x ∉ ringCenter R}

/-- Distinct noncentral elements are adjacent precisely when they commute. -/
def commutingGraph (R : Type) [Mul R] : SimpleGraph (Vertex R) where
  Adj x y := x ≠ y ∧ x.val * y.val = y.val * x.val
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

/-- The order `|C(x)|` of the centralizer of `x`. -/
def centralizerCard (R : Type) [Mul R] [Fintype R] (x : R) : ℕ :=
  Fintype.card (Set.centralizer ({x} : Set R))

section Centralizer

variable {R : Type} [NonUnitalNonAssocRing R]

/-- A centralizer of a set, as an additive subgroup. -/
private def addCentralizer (S : Set R) : AddSubgroup R where
  carrier := Set.centralizer S
  zero_mem' := Set.zero_mem_centralizer
  add_mem' := Set.add_mem_centralizer
  neg_mem' := Set.neg_mem_centralizer

private theorem mem_center_iff {x : R} : x ∈ ringCenter R ↔ ∀ y, y * x = x * y := by
  simp [ringCenter, Set.mem_centralizer_iff]

private theorem mem_single_iff {x y : R} : y ∈ Set.centralizer ({x} : Set R) ↔ x * y = y * x := by
  simp [Set.mem_centralizer_iff]

variable [Fintype R]

/-- `C(x)` is the disjoint union of the center, `x` and the graph neighbours of `x`. -/
private theorem centralizer_card_eq (x : Vertex R) :
    centralizerCard R x.val =
      Fintype.card (ringCenter R) + 1 + (commutingGraph R).degree x := by
  let Z : Finset R := univ.filter (fun y => y ∈ ringCenter R)
  let K : Finset R := univ.filter (fun y => y ∈ Set.centralizer ({x.val} : Set R))
  let N : Finset R := univ.filter
    (fun y => y ∉ ringCenter R ∧ y ≠ x.val ∧ x.val * y = y * x.val)
  let e : (commutingGraph R).neighborSet x ≃
      {y : R // y ∉ ringCenter R ∧ y ≠ x.val ∧ x.val * y = y * x.val} :=
    { toFun := fun y => ⟨y.val.val, y.val.property,
        fun h => y.property.1 (Subtype.ext h.symm), y.property.2⟩
      invFun := fun y => ⟨⟨y.val, y.property.1⟩,
        ⟨fun h => y.property.2.1 (congrArg Subtype.val h.symm), y.property.2.2⟩⟩
      left_inv := by intro y; rfl
      right_inv := by intro y; rfl }
  have hN : (commutingGraph R).degree x = N.card := by
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    exact (Fintype.card_congr e).trans (Fintype.card_subtype _)
  have hZ : Z.card = Fintype.card (ringCenter R) := (Fintype.card_subtype _).symm
  have hK : K.card = centralizerCard R x.val := (Fintype.card_subtype _).symm
  have hx : x.val ∉ N := by simp [N]
  have hdis : Disjoint Z (insert x.val N) := by
    apply Finset.disjoint_left.mpr
    intro y hy hz
    have hyZ : y ∈ ringCenter R := (mem_filter.mp hy).2
    rcases mem_insert.mp hz with h | h
    · subst y; exact x.property hyZ
    · exact (mem_filter.mp h).2.1 hyZ
  have hset : Z ∪ insert x.val N = K := by
    ext y
    simp only [Z, K, N, mem_union, mem_insert, mem_filter, mem_univ, true_and, mem_single_iff]
    constructor
    · rintro (h | h | h)
      · exact ((mem_center_iff.mp h) x.val)
      · subst y; rfl
      · exact h.2.2
    · intro h
      by_cases hc : y ∈ ringCenter R
      · exact Or.inl hc
      · by_cases hyx : y = x.val
        · exact Or.inr (Or.inl hyx)
        · exact Or.inr (Or.inr ⟨hc, hyx, h⟩)
  rw [← hK, ← hset, Finset.card_union_of_disjoint hdis, Finset.card_insert_of_notMem hx, hZ, hN]
  ring

/-- `C(x)` is proper, so its index is a divisor of `|R|` exceeding one: `p |C(x)| ≤ |R|`. -/
private theorem prime_mul_card_le (x : Vertex R) :
    (Fintype.card R).minFac * centralizerCard R x.val ≤ Fintype.card R := by
  let K := addCentralizer ({x.val} : Set R)
  have hproper : K ≠ ⊤ := by
    intro h
    apply x.property
    rw [mem_center_iff]
    intro y
    have hy : y ∈ K := h ▸ AddSubgroup.mem_top y
    exact ((mem_single_iff.mp hy)).symm
  have hindex : 2 ≤ K.index := K.one_lt_index_of_ne_top hproper
  have hdvd : K.index ∣ Fintype.card R := by
    simpa only [Nat.card_eq_fintype_card] using K.index_dvd_card
  have hp : (Fintype.card R).minFac ≤ K.index := Nat.minFac_le_of_dvd hindex hdvd
  have hcard : Fintype.card K * K.index = Fintype.card R := by
    simpa only [Nat.card_eq_fintype_card] using K.card_mul_index
  have hK : Fintype.card K = centralizerCard R x.val := Fintype.card_congr (Equiv.refl _)
  calc (Fintype.card R).minFac * centralizerCard R x.val
      ≤ K.index * centralizerCard R x.val := Nat.mul_le_mul_right _ hp
    _ = Fintype.card R := by rw [← hK, mul_comm, hcard]

/-- The center is a proper additive subgroup of a proper centralizer: `4z ≤ |R|`. -/
private theorem four_center_le (x : Vertex R) :
    4 * Fintype.card (ringCenter R) ≤ Fintype.card R := by
  let Z := addCentralizer (Set.univ : Set R)
  let K := addCentralizer ({x.val} : Set R)
  have hle : Z ≤ K := fun y hy => Set.centralizer_subset (Set.subset_univ _) hy
  have hne : Z ≠ K := by
    intro h
    apply x.property
    have hx : x.val ∈ K := mem_single_iff.mpr rfl
    rw [← h] at hx
    exact hx
  have hdvd : Fintype.card Z ∣ Fintype.card K := by
    simpa only [Nat.card_eq_fintype_card] using AddSubgroup.card_dvd_of_le hle
  have hlt : Fintype.card Z < Fintype.card K := by
    have hcl := Fintype.card_le_of_injective (Set.inclusion hle) (Set.inclusion_injective hle)
    rcases lt_or_eq_of_le hcl with h | h
    · exact h
    · exfalso; apply hne
      exact (AddSubgroup.eq_of_le_of_card_ge hle (by
        simp only [Nat.card_eq_fintype_card]; exact h.ge))
  have hZpos : 0 < Fintype.card Z := Fintype.card_pos_iff.mpr ⟨⟨0, Z.zero_mem⟩⟩
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : 2 ≤ c := by
    rcases c with _ | _ | c
    · simp at hc
    · simp at hc; omega
    · omega
  have h2 : 2 * Fintype.card K ≤ Fintype.card R := by
    have := prime_mul_card_le x
    have hp : 2 ≤ (Fintype.card R).minFac :=
      (Nat.minFac_prime (by
        have : 1 < Fintype.card K := by omega
        have := Fintype.card_subtype_le (fun y : R => y ∈ K)
        omega)).two_le
    have hK : Fintype.card K = centralizerCard R x.val := Fintype.card_congr (Equiv.refl _)
    nlinarith
  have hZc : Fintype.card Z = Fintype.card (ringCenter R) := Fintype.card_congr (Equiv.refl _)
  rw [← hZc]
  nlinarith

/-- Lagrange: the order of the center divides the order of the ring. -/
private theorem center_dvd : Fintype.card (ringCenter R) ∣ Fintype.card R := by
  have h := (addCentralizer (Set.univ : Set R)).card_addSubgroup_dvd_card
  have hc : Fintype.card (addCentralizer (Set.univ : Set R)) = Fintype.card (ringCenter R) :=
    Fintype.card_congr (Equiv.refl _)
  simp only [Nat.card_eq_fintype_card, hc] at h
  exact h

end Centralizer

/-- Let `R` be a finite ring, associative or not, not necessarily unital, with two
non-commuting elements. Write `z` for the order of its center, `n` for the number of noncentral
elements, `C(x)` for the centralizer of `x` and `p` for the least prime dividing `|R|`. Then
`z ≥ 1`, `n ≥ 3z`, `n ≥ z + 2 ≥ 3` and `z ∣ n`, and the common-neighbourhood energy of the
commuting graph on the noncentral elements satisfies
`E ≤ 2 Σ_x max(|C(x)| - z - 2, 0) ≤ n·max(2(n + z)/p - 2z - 4, 0) ≤ n·max(n - z - 4, 0)
  ≤ n(n - z - 2) < 2(n - 1)(n - 2)`. -/
theorem result (R : Type) [NonUnitalNonAssocRing R] [Fintype R]
    (noncommutative : ∃ a b : R, a * b ≠ b * a) :
    1 ≤ Fintype.card (ringCenter R) ∧
      3 * Fintype.card (ringCenter R) ≤ Fintype.card (Vertex R) ∧
      Fintype.card (ringCenter R) + 2 ≤ Fintype.card (Vertex R) ∧
      3 ≤ Fintype.card (Vertex R) ∧
      Fintype.card (ringCenter R) ∣ Fintype.card (Vertex R) ∧
      graphEnergy (commutingGraph R) .commonNeighbour ≤
        2 * ∑ x : Vertex R,
          max ((centralizerCard R x.val : ℝ) - Fintype.card (ringCenter R) - 2) 0 ∧
      2 * ∑ x : Vertex R,
          max ((centralizerCard R x.val : ℝ) - Fintype.card (ringCenter R) - 2) 0 ≤
        (Fintype.card (Vertex R) : ℝ) *
          max (2 * ((Fintype.card (Vertex R) : ℝ) + Fintype.card (ringCenter R)) /
              (Fintype.card R).minFac - 2 * Fintype.card (ringCenter R) - 4) 0 ∧
      (Fintype.card (Vertex R) : ℝ) *
          max (2 * ((Fintype.card (Vertex R) : ℝ) + Fintype.card (ringCenter R)) /
              (Fintype.card R).minFac - 2 * Fintype.card (ringCenter R) - 4) 0 ≤
        (Fintype.card (Vertex R) : ℝ) *
          max ((Fintype.card (Vertex R) : ℝ) - Fintype.card (ringCenter R) - 4) 0 ∧
      (Fintype.card (Vertex R) : ℝ) *
          max ((Fintype.card (Vertex R) : ℝ) - Fintype.card (ringCenter R) - 4) 0 ≤
        (Fintype.card (Vertex R) : ℝ) *
          ((Fintype.card (Vertex R) : ℝ) - Fintype.card (ringCenter R) - 2) ∧
      (Fintype.card (Vertex R) : ℝ) *
          ((Fintype.card (Vertex R) : ℝ) - Fintype.card (ringCenter R) - 2) <
        2 * ((Fintype.card (Vertex R) : ℝ) - 1) * ((Fintype.card (Vertex R) : ℝ) - 2) := by
  obtain ⟨a, b, hab⟩ := noncommutative
  have ha : a ∉ ringCenter R := fun h => hab ((mem_center_iff.mp h) b).symm
  set z := Fintype.card (ringCenter R) with hzdef
  set n := Fintype.card (Vertex R) with hndef
  have hz : 1 ≤ z := Fintype.card_pos_iff.mpr ⟨⟨0, Set.zero_mem_centralizer⟩⟩
  have hn : n + z = Fintype.card R := by
    have h1 := Fintype.card_subtype_compl (fun x : R => x ∈ ringCenter R)
    have h2 : z ≤ Fintype.card R :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    have h3 : Fintype.card {x : R // x ∈ ringCenter R} = z := rfl
    simp only [hndef, Vertex] at h1 ⊢
    omega
  have h4 := four_center_le (⟨a, ha⟩ : Vertex R)
  have h3z : 3 * z ≤ n := by omega
  have hdvd : z ∣ n := by
    have := center_dvd (R := R)
    rw [← hn] at this
    exact (Nat.dvd_add_right (dvd_refl z)).mp (by rwa [add_comm] at this)
  have hp2 : 2 ≤ (Fintype.card R).minFac := (Nat.minFac_prime (by omega)).two_le
  have hpR : (2 : ℝ) ≤ (Fintype.card R).minFac := by exact_mod_cast hp2
  have hnR : (n : ℝ) + z = Fintype.card R := by exact_mod_cast hn
  have hzR : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have h3R : 3 * (z : ℝ) ≤ n := by exact_mod_cast h3z
  -- per-vertex inequality `|C(x)| ≤ (n + z)/p`
  have hC (x : Vertex R) : (centralizerCard R x.val : ℝ) ≤ ((n : ℝ) + z) / (Fintype.card R).minFac := by
    rw [le_div_iff₀ (by linarith), hnR, mul_comm]
    exact_mod_cast prime_mul_card_le x
  refine ⟨hz, h3z, by omega, by omega, hdvd, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hE, -⟩ := NeighbourhoodCliqueBound.result (commutingGraph R)
    refine hE.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [centralizer_card_eq x, ← hzdef]
    push_cast
    ring_nf
  · have hconst : ∀ M : ℝ, (n : ℝ) * M = ∑ _x : Vertex R, M := fun M => by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hndef]
    rw [hconst, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have hx := hC x
    rcases le_total ((centralizerCard R x.val : ℝ) - z - 2) 0 with h | h
    · rw [max_eq_right h, mul_zero]; exact le_max_right _ _
    · rw [max_eq_left h]
      refine le_trans ?_ (le_max_left _ _)
      have : 2 * ((n : ℝ) + z) / (Fintype.card R).minFac =
          2 * (((n : ℝ) + z) / (Fintype.card R).minFac) := by ring
      rw [this]; linarith
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply max_le_max_right
    have hq : 2 * ((n : ℝ) + z) / (Fintype.card R).minFac ≤ (n : ℝ) + z := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact max_le (by linarith) (by linarith)
  · nlinarith

#print axioms result

end D5.S3.Combinatorics.Graph.CommonNeighborhood.RingNoncentralBound
