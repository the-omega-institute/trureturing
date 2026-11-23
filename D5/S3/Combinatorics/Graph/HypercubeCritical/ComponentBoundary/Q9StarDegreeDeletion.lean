/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarDegreeDeletion
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarDegreeDeletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarDegreeDeletion.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarDegreeDeletion.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarDegreeDeletion.claim
   digest: A degree-deletion certificate bounds every subcubic extension of a 108-point cubic star in Q9 by 255. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves

/-! An integer degree-deletion dual for the literal three-leaf star. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarDegreeDeletion

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (flip_adj)
open BalancedCubeGirth (adjacent_exists_flip)
open CoordinateHalves.CubeBitMoves (toggle)

private def excess {V : Type*} [DecidableEq V] (N : V → Finset V)
    (R : Finset V) (d : ℕ) (v : V) : ℕ :=
  (N v ∩ R).card - d

/-- Weight the deletion inequalities and use symmetry to collect by deleted vertex. -/
private theorem degreeDeletionDual {V : Type*} [DecidableEq V] (N : V → Finset V)
    (symm : ∀ v x, x ∈ N v ↔ v ∈ N x) (R U : Finset V)
    (d s : ℕ) (weight : V → ℕ)
    (hdeg : ∀ v ∈ U, (N v ∩ U).card ≤ d)
    (hcoeff : ∀ v ∈ R, weight v * excess N R d v + ∑ x ∈ N v ∩ R, weight x ≤ s) :
    ∑ v ∈ R, weight v * excess N R d v ≤ s * (R \ U).card := by
  let D := R \ U
  let k := excess N R d
  have localBound (v : V) (hv : v ∈ R) :
      k v ≤ (if v ∈ D then k v else 0) + (N v ∩ D).card := by
    by_cases hd : v ∈ D
    · simp only [ite_eq_left hd]
      omega
    · have hu : v ∈ U := by
        by_contra hvu
        exact hd (mem_sdiff.mpr ⟨hv, hvu⟩)
      have hsplit : (N v ∩ R) \ U = N v ∩ D := by
        ext x
        simp [D, and_assoc]
      have hkept : ((N v ∩ R) ∩ U).card ≤ d :=
        (card_le_card (by
          intro x hx
          simp only [mem_inter] at hx ⊢
          exact ⟨hx.1.1, hx.2⟩)).trans (hdeg v hu)
      have hcard := card_inter_add_card_sdiff (N v ∩ R) U
      rw [hsplit] at hcard
      simp only [hd, ite_false, zero_add, k, excess]
      omega
  have selfSum :
      (∑ v ∈ R, weight v * (if v ∈ D then k v else 0)) =
        ∑ v ∈ D, weight v * k v := by
    simp only [mul_ite, mul_zero]
    rw [← sum_filter]
    congr 1
    exact filter_mem_eq_inter.trans (inter_eq_right.mpr sdiff_subset)
  have neighborSum :
      (∑ v ∈ R, weight v * (N v ∩ D).card) =
        ∑ x ∈ D, ∑ v ∈ N x ∩ R, weight v := by
    calc
      _ = ∑ v ∈ R, ∑ x ∈ D, if x ∈ N v then weight v else 0 := by
        apply sum_congr rfl
        intro v _
        rw [← sum_filter]
        have hfilter : D.filter (· ∈ N v) = N v ∩ D := by
          ext x
          simp [and_comm]
        rw [hfilter, sum_const, nsmul_eq_mul, mul_comm]
        rfl
      _ = ∑ x ∈ D, ∑ v ∈ R, if v ∈ N x then weight v else 0 := by
        rw [sum_comm]
        apply sum_congr rfl
        intro x _
        apply sum_congr rfl
        intro v _
        by_cases h : x ∈ N v
        · simp [h, (symm v x).mp h]
        · simp [h, mt (symm v x).mpr h]
      _ = _ := by
        apply sum_congr rfl
        intro x _
        rw [← sum_filter]
        congr 1
        ext v
        simp [and_comm]
  calc
    _ ≤ ∑ v ∈ R, weight v * ((if v ∈ D then k v else 0) + (N v ∩ D).card) :=
      sum_le_sum fun v hv => Nat.mul_le_mul_left _ (localBound v hv)
    _ = ∑ v ∈ D, (weight v * k v + ∑ x ∈ N v ∩ R, weight x) := by
      simp only [Nat.mul_add, sum_add_distrib, selfSum, neighborSum]
    _ ≤ ∑ _v ∈ D, s := sum_le_sum fun v hv => hcoeff v (sdiff_subset hv)
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, mul_comm]
      rfl

private abbrev Vertex := BitVec 9

private def neighbors (v : Vertex) : Finset Vertex :=
  (univ : Finset (Fin 9)).image (toggle v)

private theorem mem_neighbors_iff (v x : Vertex) :
    x ∈ neighbors v ↔ (hypercube 9).Adj (cubeBitVec 9 v) (cubeBitVec 9 x) := by
  simp only [neighbors, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    rw [toggle, cubeBitVec_xor_single]
    exact flip_adj _ _
  · intro h
    obtain ⟨i, hi⟩ := adjacent_exists_flip h
    refine ⟨i, (cubeBitVec 9).injective ?_⟩
    rw [toggle, cubeBitVec_xor_single, hi]
    rfl

private def baseB : List ℕ := [12, 15, 18, 23, 27, 29, 34, 36, 40, 45, 48, 51]

private def baseM : List ℕ := [2, 4, 7, 8, 11, 16, 21, 25, 26, 28, 35, 37, 38, 41, 47, 49, 55, 56]

private def starList : List Vertex :=
  (baseM ++ ([1, 2, 4] : List ℕ).flatMap
    (fun z => (baseB ++ baseM).map (fun x => x + 64 * z))).map (BitVec.ofNat 9)

private def starBits : Finset Vertex := starList.toFinset

/-- Census orbit 23 in the vacuum and the three singleton layers of Q9. -/
def starSupport : Finset (Fin 9 → Bool) :=
  starBits.map (cubeBitVec 9).toEmbedding

private def vertices : List Vertex :=
  (List.finRange 512).map BitVec.ofFin

private theorem mem_vertices (v : Vertex) : v ∈ vertices :=
  List.mem_map.mpr ⟨v.toFin, List.mem_finRange _, rfl⟩

-- The masks permit constant-size membership tests inside the degree computations.
set_option linter.style.longLine false in
private def inStar (v : Vertex) : Bool :=
  Nat.testBit
    0x000000000000000000000000000000000000000000000000018ba37c3ea599940000000000000000018ba37c3ea59994018ba37c3ea599940182826816210994
    v.toNat

set_option linter.style.longLine false in
private def inResidual (v : Vertex) : Bool :=
  Nat.testBit
    0xfffffffffffffffffe745c83c15a666bfe745c83c15a666b4000000000000002fe745c83c15a666b400000000000000240000000000000026814140180486002
    v.toNat

private def allBits : Finset Vertex :=
  (univ : Finset (Fin 512)).image BitVec.ofFin

private theorem mem_allBits (v : Vertex) : v ∈ allBits :=
  mem_image.mpr ⟨v.toFin, mem_univ _, rfl⟩

private def filteredNeighbors (contains : Vertex → Bool) (v : Vertex) : Finset Vertex :=
  (neighbors v).filter (fun x => contains x = true)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Closed certificate checks evaluate up to 512 vertices in the kernel.
private theorem inStar_iff (v : Vertex) : inStar v = true ↔ v ∈ starBits := by
  let mask := allBits.filter (fun x => inStar x = true)
  have h : starList.all inStar = true := by decide +kernel
  have hcard : (allBits.filter (fun x => inStar x = true)).card ≤ starBits.card := by
    decide +kernel
  have heq : starBits = mask :=
    eq_of_subset_of_card_le (fun x hx =>
      mem_filter.mpr ⟨mem_allBits x, List.all_eq_true.mp h x (List.mem_toFinset.mp hx)⟩) hcard
  rw [heq]
  simp only [mask, mem_filter, mem_allBits, true_and]

private def residual : Finset Vertex :=
  allBits.filter (fun v => inResidual v = true)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Closed certificate checks evaluate up to 512 vertices in the kernel.
private theorem mem_residual (v : Vertex) :
    v ∈ residual ↔ v ∉ starBits ∧ (neighbors v ∩ starBits).card = 0 := by
  have h : vertices.all (fun x => inResidual x ==
      (!inStar x && ((filteredNeighbors inStar x).card == 0))) = true := by
    decide +kernel
  have hn : filteredNeighbors inStar v = neighbors v ∩ starBits := by
    ext x
    simp only [filteredNeighbors, mem_filter, mem_inter, inStar_iff]
  simp only [residual, mem_filter, mem_allBits, true_and]
  rw [beq_iff_eq.mp (List.all_eq_true.mp h v (mem_vertices v)), Bool.and_eq_true,
    Bool.not_eq_true_eq_eq_false, ← Bool.eq_false_eq_not_eq_true, inStar_iff, hn, beq_iff_eq]

/-- Positive multipliers grouped by the symmetry orbits of their rows. -/
private def multiplierRows : List (ℕ × List Vertex) := [
  (32, [193, 321, 385]),
  (62, [206, 214, 234, 244, 251, 253, 334, 342, 362, 372, 379, 381, 398, 406, 426, 436, 443, 445]),
  (32, [222, 238, 246, 250, 252, 255, 350, 366, 374, 378, 380, 383, 414, 430, 438, 442, 444, 447]),
  (62, [450, 452, 459, 469, 489, 497]),
  (3, [454, 458, 468, 491, 501, 505]),
  (18, [455, 456, 464, 473, 483, 485]),
  (32, [461, 467, 480]),
  (7, [472, 487]),
  (32, [474, 476, 486, 495, 503, 504]),
  (32, [479, 492, 498])]

private def multiplier (v : Vertex) : ℕ :=
  ((multiplierRows.find? fun row => row.2.contains v).map Prod.fst).getD 0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Closed certificate checks evaluate up to 512 vertices in the kernel.
private theorem star_data :
    starBits.card = 108 ∧
    (∀ v ∈ starBits, (neighbors v ∩ starBits).card = 3) ∧
    residual.card = 186 := by
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  have h : starList.all (fun v => (filteredNeighbors inStar v).card == 3) = true := by
    decide +kernel
  intro v hv
  have hn : filteredNeighbors inStar v = neighbors v ∩ starBits := by
    ext x
    simp only [filteredNeighbors, mem_filter, mem_inter, inStar_iff]
  rw [← hn]
  exact beq_iff_eq.mp (List.all_eq_true.mp h v (List.mem_toFinset.mp hv))

private def residualExcess (v : Vertex) : ℕ :=
  (filteredNeighbors inResidual v).card - 3

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- The column and right-hand-side checks evaluate the full multiplier table.
private theorem dual_data :
    (∑ v ∈ residual, multiplier v * excess neighbors residual 3 v) = 7320 ∧
    (∀ v ∈ residual,
      multiplier v * excess neighbors residual 3 v +
        ∑ x ∈ neighbors v ∩ residual, multiplier x ≤ 192) := by
  have hn (v : Vertex) : filteredNeighbors inResidual v = neighbors v ∩ residual := by
    ext x
    simp only [filteredNeighbors, mem_filter, mem_inter, residual, mem_allBits, true_and]
  have he (v : Vertex) : excess neighbors residual 3 v = residualExcess v := by
    rw [residualExcess, hn, excess]
  simp only [he, ← hn]
  constructor
  · decide +kernel
  · have h : vertices.all (fun v => !inResidual v ||
        decide (multiplier v * residualExcess v +
          ∑ x ∈ filteredNeighbors inResidual v, multiplier x ≤ 192)) = true := by
      decide +kernel
    intro v hv
    have hm := (mem_filter.mp hv).2
    have hc := List.all_eq_true.mp h v (mem_vertices v)
    simpa only [hm, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hc

private theorem encoded_bound (U : Finset Vertex) (hC : starBits ⊆ U)
    (hdeg : ∀ v ∈ U, (neighbors v ∩ U).card ≤ 3) : U.card ≤ 255 := by
  have hsymm (v x : Vertex) : x ∈ neighbors v ↔ v ∈ neighbors x := by
    rw [mem_neighbors_iff, mem_neighbors_iff]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hres : U \ starBits ⊆ residual := by
    intro v hv
    obtain ⟨hvu, hvc⟩ := mem_sdiff.mp hv
    refine (mem_residual v).mpr ⟨hvc, ?_⟩
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro c hc
    obtain ⟨hcv, hcC⟩ := mem_inter.mp hc
    have hsub : insert v (neighbors c ∩ starBits) ⊆ neighbors c ∩ U := by
      apply insert_subset_iff.mpr
      exact ⟨mem_inter.mpr ⟨(hsymm v c).mp hcv, hvu⟩,
        inter_subset_inter_left hC⟩
    have hnot : v ∉ neighbors c ∩ starBits := fun h => hvc (mem_inter.mp h).2
    have hle := (card_le_card hsub).trans (hdeg c (hC hcC))
    rw [card_insert_of_notMem hnot, star_data.2.1 c hcC] at hle
    omega
  have hdual := degreeDeletionDual neighbors hsymm residual U 3 192 multiplier hdeg dual_data.2
  rw [dual_data.1] at hdual
  have hpartition := card_sdiff_add_card_eq_card hC
  have hresidual := card_sdiff_add_card_inter residual U
  have hcard : (U \ starBits).card ≤ (residual ∩ U).card := by
    apply card_le_card
    intro v hv
    exact mem_inter.mpr ⟨hres hv, (mem_sdiff.mp hv).1⟩
  rw [star_data.1] at hpartition
  rw [star_data.2.2] at hresidual
  omega

open Classical in
/-- The assertion that this specific star extends to an induced subcubic set above 255. -/
noncomputable def claim : Prop :=
  ∃ U : Finset (Fin 9 → Bool), starSupport ⊆ U ∧ 255 < U.card ∧
    ∀ v ∈ U, (U.filter (fun x => (hypercube 9).Adj v x)).card ≤ 3

open Classical in
/-- Every subcubic extension of the literal 108-point star has at most 255 vertices. -/
theorem result : ¬ claim := by
  rintro ⟨U, hC, hcard, hdeg⟩
  let e := cubeBitVec 9
  let T := U.map e.symm.toEmbedding
  have hT (v : Vertex) : v ∈ T ↔ e v ∈ U := by
    simp only [T, mem_map_equiv, Equiv.symm_symm]
  have hsub : starBits ⊆ T := by
    intro v hv
    exact (hT v).mpr (hC (mem_map.mpr ⟨v, hv, rfl⟩))
  have hlocal (v : Vertex) (hv : v ∈ T) : (neighbors v ∩ T).card ≤ 3 := by
    have heq : (neighbors v ∩ T).map e.toEmbedding =
        U.filter (fun x => (hypercube 9).Adj (e v) x) := by
      ext x
      obtain ⟨y, rfl⟩ := e.surjective x
      simp only [mem_map_equiv, e.symm_apply_apply, mem_inter, mem_filter,
        hT, mem_neighbors_iff, and_comm]
      rfl
    rw [← card_map e.toEmbedding, heq]
    exact hdeg (e v) ((hT v).mp hv)
  have hle := encoded_bound T hsub hlocal
  change (U.map e.symm.toEmbedding).card ≤ 255 at hle
  rw [card_map] at hle
  omega

#print axioms result

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarDegreeDeletion
