/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q8OrientedFiberNeighborhood
   generality: I
   mirror-B: none(waiver:isolated-verification)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Actual projections and coordinate flips give the four-axis Q8 neighborhood bounds. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CubeFiberNeighborhoodBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8FourFiberCapacityCertificate

/-! The list in the certificate counts vertices by their bits on the selected axes,
in least-significant-axis-first order. Dropping an axis merges the two fibres that
differ on that axis. Each resulting table has a cost bounded by the same ambient
closed neighborhood, using the unselected axes as residual coordinates. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8OrientedFiberNeighborhood

open Finset
open BalancedCriticalSpectrum (flip)
open CubeClosedNeighborhoodRecurrence (closedNeighborhood h)
open Q8FourFiberCapacityCertificate (dropAxis neighborhoodCost ProjectionConstraints)
open scoped BigOperators

open private costWith from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8FourFiberCapacityCertificate

private abbrev Vertex := Fin 8 → Bool

private def bits {k : ℕ} (p : Fin (2 ^ k)) : Fin k → Bool :=
  (BitVec.ofFin p).getLsb

private noncomputable def patternEquiv (k : ℕ) : Fin (2 ^ k) ≃ (Fin k → Bool) :=
  Equiv.ofBijective bits ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨fun p q he => by
      have hb : BitVec.ofFin p = BitVec.ofFin q :=
        BitVec.eq_of_getLsbD_eq_iff.mpr fun i hi => congrFun he ⟨i, hi⟩
      exact congrArg BitVec.toFin hb,
      by simp⟩)

private def insertBit {d : ℕ} (i : Fin (d + 1)) (b : Bool) (p : Fin (2 ^ d)) :
    Fin (2 ^ (d + 1)) :=
  let place := 2 ^ (i : ℕ)
  (BitVec.ofNat (d + 1) (p.val % place + b.toNat * place + (p.val / place) * (2 * place))).toFin

private theorem bits_insertBit {d : ℕ} (hd : d ≤ 3) (i : Fin (d + 1)) (b : Bool)
    (p : Fin (2 ^ d)) :
    bits (insertBit i b p) = i.insertNth (α := fun _ => Bool) b (bits p) := by
  ext j
  revert i b p j
  interval_cases d <;> decide +kernel

private theorem dropAxis_ofFn {d : ℕ} (hd : d ≤ 3) (i : Fin (d + 1))
    (f : Fin (2 ^ (d + 1)) → ℕ) :
    dropAxis d i (List.ofFn f) =
      List.ofFn (fun p => f (insertBit i false p) + f (insertBit i true p)) := by
  interval_cases d <;> fin_cases i <;> rfl

private def neighbor {k : ℕ} (p : Fin (2 ^ k)) (i : Fin k) : Fin (2 ^ k) :=
  (BitVec.ofFin p ^^^ BitVec.ofNat k (2 ^ (i : ℕ))).toFin

private theorem neighbor_val {k : ℕ} (hk : k ≤ 4) (p : Fin (2 ^ k)) (i : Fin k) :
    (neighbor p i : ℕ) = p.val ^^^ (2 ^ (i : ℕ)) := by
  revert p i
  interval_cases k <;> decide +kernel

private theorem bits_neighbor {k : ℕ} (hk : k ≤ 4) (p : Fin (2 ^ k)) (i : Fin k) :
    bits (neighbor p i) = flip (bits p) i := by
  ext j
  revert p i j
  interval_cases k <;> decide +kernel

/-- The count table in binary order for the restriction to the given axes. -/
def fiberCounts {k : ℕ} (S : Finset Vertex) (axes : Fin k ↪ Fin 8) : List ℕ :=
  List.ofFn fun p : Fin (2 ^ k) => (S.filter fun x => (fun i => x (axes i)) = bits p).card

private theorem dropAxis_fiberCounts {d : ℕ} (hd : d ≤ 3) (S : Finset Vertex)
    (axes : Fin (d + 1) ↪ Fin 8) (i : Fin (d + 1)) :
    dropAxis d i (fiberCounts S axes) = fiberCounts S (i.succAboveEmb.trans axes) := by
  unfold fiberCounts
  rw [dropAxis_ofFn hd]
  congr 1
  funext p
  have hremove (x : Vertex) :
      i.removeNth (α := fun _ => Bool) (fun j => x (axes j)) =
        (fun j => x (axes (i.succAbove j))) := rfl
  simp only [bits_insertBit hd, Fin.eq_insertNth_iff, hremove]
  let T := S.filter fun x => (fun j => x (axes (i.succAbove j))) = bits p
  have hfalse : (T.filter fun x => ¬ x (axes i) = true) =
      T.filter (fun x => x (axes i) = false) := by
    congr 1
    funext x
    cases x (axes i) <;> simp
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (fun x => x (axes i) = true)
  rw [hfalse, Nat.add_comm] at hsplit
  simpa only [T, Finset.filter_filter, and_comm,
    Function.Embedding.trans_apply, Fin.coe_succAboveEmb] using hsplit

private theorem fiberCounts_sum {k : ℕ} (S : Finset Vertex) (axes : Fin k ↪ Fin 8) :
    (fiberCounts S axes).sum = S.card := by
  rw [fiberCounts, Fin.sum_ofFn]
  refine Eq.trans ?_ (Finset.card_eq_sum_card_fiberwise
    (s := S) (f := fun x => (patternEquiv k).symm (fun i => x (axes i)))
    (t := univ) (fun _ _ => mem_univ _)).symm
  apply sum_congr rfl
  intro p _
  congr 1
  ext x
  simp only [mem_filter, Equiv.symm_apply_eq]
  rfl

private theorem map_closedNeighborhood {m n : ℕ}
    (e : (Fin m → Bool) ≃ (Fin n → Bool))
    (he : ∀ x y, hammingDist (e x) (e y) = hammingDist x y)
    (S : Finset (Fin m → Bool)) :
    closedNeighborhood (S.map e.toEmbedding) = (closedNeighborhood S).map e.toEmbedding := by
  ext v
  obtain ⟨x, rfl⟩ := e.surjective v
  simp only [closedNeighborhood, mem_filter, mem_univ, true_and, mem_map_equiv,
    Equiv.symm_apply_apply]
  constructor
  · rintro ⟨v, hv, hd⟩
    obtain ⟨y, rfl⟩ := e.surjective v
    exact ⟨y, by simpa using hv, by simpa only [he] using hd⟩
  · rintro ⟨y, hy, hd⟩
    exact ⟨e y, by simpa using hy, by rwa [he]⟩

private theorem reindex_hamming {m n : ℕ} (e : Fin m ≃ Fin n) (x y : Fin n → Bool) :
    hammingDist (x ∘ e) (y ∘ e) = hammingDist x y := by
  simpa only [hammingDist, card_eq_sum_ones, sum_filter, Function.comp_apply] using
    e.sum_comp (fun i => if x i ≠ y i then (1 : ℕ) else 0)

private theorem extend_axes {k : ℕ} (hk : k ≤ 8) (axes : Fin k ↪ Fin 8) :
    ∃ e : Fin (k + (8 - k)) ≃ Fin 8, ∀ i, e (Fin.castAdd (8 - k) i) = axes i := by
  let front := Fin.castAddEmb (8 - k) (n := k)
  let f := Function.extend front axes (fun _ => 0)
  have hf (i : Fin k) : f (front i) = axes i :=
    front.injective.extend_apply axes _ i
  have hinj : Set.InjOn f (↑(univ.map front) : Set (Fin (k + (8 - k)))) := by
    intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := mem_map.mp (mem_coe.mp hx)
    obtain ⟨j, -, rfl⟩ := mem_map.mp (mem_coe.mp hy)
    rw [hf, hf] at hxy
    exact congrArg front (axes.injective hxy)
  obtain ⟨e, he⟩ := Finset.exists_equiv_extend_of_card_eq
    (t := (univ : Finset (Fin 8))) (by simp; omega) (subset_univ _) hinj
  refine ⟨e.trans (Equiv.subtypeUnivEquiv (fun _ => mem_univ _)), fun i => ?_⟩
  exact (he (front i) (mem_map_of_mem _ (mem_univ i))).trans (hf i)

private theorem fiber_card_eq_product {k n : ℕ} (S : Finset Vertex) (axes : Fin k ↪ Fin 8)
    (e : Fin (k + n) ≃ Fin 8) (he : ∀ i, e (Fin.castAdd n i) = axes i)
    (p : Fin k → Bool) :
    (S.filter fun x => (fun i => x (axes i)) = p).card =
      (univ.filter fun y : Fin n → Bool => (Fin.append p y) ∘ e.symm ∈ S).card := by
  let a := Fin.appendEquiv (α := Bool) k n
  have hinverse (x : Vertex) (hx : (fun i => x (axes i)) = p) :
      Fin.append p (a.symm (x ∘ e)).2 ∘ e.symm = x := by
    have hfirst : (a.symm (x ∘ e)).1 = p := by
      funext i
      change x (e (Fin.castAdd n i)) = p i
      rw [he, congrFun hx i]
    have hpair : a.symm (x ∘ e) = (p, (a.symm (x ∘ e)).2) := Prod.ext hfirst rfl
    have happ := congrArg a hpair
    rw [a.apply_symm_apply] at happ
    funext j
    exact (congrFun happ (e.symm j)).symm.trans (by simp)
  refine Finset.card_bij'
    (fun x _ => (a.symm (x ∘ e)).2) (fun y _ => Fin.append p y ∘ e.symm) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxS, hxP⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rw [hinverse x hxP]
    exact hxS
  · intro y hy
    refine mem_filter.mpr ⟨(mem_filter.mp hy).2, ?_⟩
    funext i
    rw [← he i]
    simp
  · intro x hx
    exact hinverse x (mem_filter.mp hx).2
  · intro y _
    have hcomp : (Fin.append p y ∘ e.symm) ∘ e = a (p, y) := by
      funext j
      simp [a, Function.comp_def]
    rw [hcomp, a.symm_apply_apply]

private theorem foldl_max_le {α : Type*} (l : List α) (f : α → ℕ) (start bound : ℕ)
    (hstart : start ≤ bound) (hvals : ∀ i ∈ l, f i ≤ bound) :
    l.foldl (fun acc i => max acc (f i)) start ≤ bound := by
  induction l generalizing start with
  | nil => exact hstart
  | cons i l ih =>
      exact ih _ (max_le hstart (hvals i (by simp))) (fun j hj => hvals j (by simp [hj]))

private theorem cost_le_pattern_sum {k : ℕ} (hk : k ≤ 4) (F : (Fin k → Bool) → ℕ) :
    neighborhoodCost k (List.ofFn fun p : Fin (2 ^ k) => F (bits p)) ≤
      ∑ p : Fin k → Bool, max (h (8 - k) (F p)) (univ.sup fun i : Fin k => F (flip p i)) := by
  let bound := fun (p : Fin k → Bool) =>
    max (h (8 - k) (F p)) (univ.sup fun i : Fin k => F (flip p i))
  let counts := List.ofFn fun p : Fin (2 ^ k) => F (bits p)
  have hget (p : Fin (2 ^ k)) : counts.toArray[p.val]! = F (bits p) := by
    rw [getElem!_pos _ _ (by simp [counts])]
    simp [counts]
  have hsum : (List.ofFn fun p : Fin (2 ^ k) => bound (bits p)).sum =
      ∑ p : Fin k → Bool, bound p := by
    rw [Fin.sum_ofFn]
    exact (patternEquiv k).sum_comp bound
  let localCost := fun j : ℕ =>
    (List.range k).foldl (fun acc i => max acc counts.toArray[j ^^^ (2 ^ i)]!)
      (h (8 - k) counts.toArray[j]!)
  have hlist : (List.range (2 ^ k)).map localCost =
      List.ofFn (fun p : Fin (2 ^ k) => localCost p) := by
    apply List.ext_getElem
    · simp
    · simp
  change neighborhoodCost k counts ≤ ∑ p, bound p
  rw [← hsum, neighborhoodCost, costWith]
  change ((List.range (2 ^ k)).map localCost).sum ≤ _
  rw [hlist, Fin.sum_ofFn, Fin.sum_ofFn]
  apply sum_le_sum
  intro p _
  change (List.range k).foldl (fun acc i => max acc counts.toArray[p.val ^^^ (2 ^ i)]!)
      (h (8 - k) counts.toArray[p.val]!) ≤ bound (bits p)
  rw [hget]
  apply foldl_max_le _ _ _ _ (le_max_left _ _)
  intro i hi
  let axis : Fin k := ⟨i, List.mem_range.mp hi⟩
  rw [show p.val ^^^ (2 ^ i) = (neighbor p axis).val from (neighbor_val hk p axis).symm,
    hget, bits_neighbor hk]
  exact (Finset.le_sup (f := fun i : Fin k => F (flip (bits p) i)) (mem_univ axis)).trans
    (le_max_right _ _)

set_option maxHeartbeats 600000 in
-- Elaborating the product-coordinate counts compares dependent finite-set instances.
/-- Every table of actual fibres on at most four axes has cost bounded by the
closed neighborhood in the original eight-cube. -/
theorem neighborhoodCost_fiberCounts_le {k : ℕ} (hk : k ≤ 4) (S : Finset Vertex)
    (axes : Fin k ↪ Fin 8) :
    neighborhoodCost k (fiberCounts S axes) ≤ (closedNeighborhood S).card := by
  obtain ⟨e, he⟩ := extend_axes (by omega) axes
  let reindex := Equiv.arrowCongr e.symm (Equiv.refl Bool)
  let T := S.map reindex.toEmbedding
  let A := Fin.appendEquiv (α := Bool) k (8 - k)
  let U := T.map A.symm.toEmbedding
  have hmap : U.map A.toEmbedding = T := by simp [U, Finset.map_map]
  have hhood : (closedNeighborhood T).card = (closedNeighborhood S).card := by
    rw [show T = S.map reindex.toEmbedding from rfl,
      map_closedNeighborhood reindex (reindex_hamming e), Finset.card_map]
  let F (p : Fin k → Bool) := (S.filter fun x => (fun i => x (axes i)) = p).card
  have hf : F = fun p =>
      (univ.filter fun y : Fin (8 - k) → Bool => (p, y) ∈ U).card := by
    funext p
    dsimp only [F]
    rw [fiber_card_eq_product S axes e he]
    simp only [U, T, mem_map_equiv, Equiv.symm_symm]
    rfl
  calc
    _ ≤ ∑ p : Fin k → Bool, max (h (8 - k) (F p))
        (univ.sup fun i : Fin k => F (flip p i)) := cost_le_pattern_sum hk F
    _ ≤ (closedNeighborhood (U.map A.toEmbedding)).card := by
      rw [hf]
      exact CubeFiberNeighborhoodBound.sum_max_le_closedNeighborhood_card U
    _ = (closedNeighborhood S).card := by rw [hmap, hhood]

private theorem fiberCounts_capacity {k : ℕ} (hk : k ≤ 8) (S : Finset Vertex)
    (axes : Fin k ↪ Fin 8) {c : ℕ} (hc : c ∈ fiberCounts S axes) : c ≤ 2 ^ (8 - k) := by
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc
  obtain ⟨e, he⟩ := extend_axes hk axes
  rw [fiber_card_eq_product S axes e he (bits p)]
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

/-- Number of vertices of the support on one side of an axis. -/
def sideCount (S : Finset Vertex) (i : Fin 8) (b : Bool) : ℕ :=
  (S.filter fun x => x i = b).card

private theorem fiberCounts_one (S : Finset Vertex) (axes : Fin 1 ↪ Fin 8) :
    (fiberCounts S axes)[1]! = sideCount S (axes 0) true := by
  unfold fiberCounts sideCount
  rw [getElem!_pos _ _ (by simp)]
  simp only [List.getElem_ofFn]
  congr 1
  ext x
  simp only [mem_filter]
  have hbits : ∀ j : Fin 1, bits (⟨1, by decide⟩ : Fin (2 ^ 1)) j = true := by
    decide +kernel
  exact and_congr_right fun _ => ⟨fun h => (congrFun h 0).trans (hbits 0),
    fun h => funext fun j => by
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact h.trans (hbits 0).symm⟩

/-- A neighborhood cap and the oriented one-side counts give the certificate
constraints on every nonempty subprojection of the selected axes. -/
theorem projectionConstraints_fiberCounts {k cap : ℕ} (hk : k ≤ 4) (S : Finset Vertex)
    (axes : Fin k ↪ Fin 8) (hcap : (closedNeighborhood S).card ≤ cap)
    (hm : ∀ i, 11 ≤ sideCount S (axes i) true ∧ sideCount S (axes i) true ≤ S.card / 2) :
    ProjectionConstraints S.card cap k (fiberCounts S axes) := by
  induction k with
  | zero => trivial
  | succ d ih =>
    rw [ProjectionConstraints]
    refine ⟨(neighborhoodCost_fiberCounts_le hk S axes).trans hcap, ?_, ?_⟩
    · cases d with
      | zero => simpa only [ite_true, fiberCounts_one] using hm 0
      | succ d => trivial
    · intro i
      rw [dropAxis_fiberCounts (by omega) S axes i]
      exact ih (by omega) (i.succAboveEmb.trans axes) (fun j => hm (i.succAbove j))

private abbrev firstFour : Fin 4 ↪ Fin 8 := Fin.castAddEmb 4

/-- The four-axis certificate yields the two neighborhood bounds for supports
whose first four one-sides are already oriented toward the smaller side. -/
theorem closedNeighborhood_lower_bounds_of_oriented (S : Finset Vertex)
    (hm : ∀ i : Fin 4, 11 ≤ sideCount S (firstFour i) true ∧
      sideCount S (firstFour i) true ≤ S.card / 2) :
    (S.card = 36 → 107 ≤ (closedNeighborhood S).card) ∧
    (S.card = 39 → 110 ≤ (closedNeighborhood S).card) := by
  have hlen : (fiberCounts S firstFour).length = 16 := by simp [fiberCounts]
  have hcounts : ∀ c ∈ fiberCounts S firstFour, c ≤ 16 :=
    fun _ hc => fiberCounts_capacity (by decide) S firstFour hc
  constructor
  · intro hS
    by_contra! hsmall
    have htest := projectionConstraints_fiberCounts (by decide) S firstFour
      (cap := 106) (by omega) hm
    rw [hS] at htest
    exact Q8FourFiberCapacityCertificate.exclude36 _ hlen
      ((fiberCounts_sum S firstFour).trans hS) hcounts htest
  · intro hS
    by_contra! hsmall
    have htest := projectionConstraints_fiberCounts (by decide) S firstFour
      (cap := 109) (by omega) hm
    rw [hS] at htest
    exact Q8FourFiberCapacityCertificate.exclude39 _ hlen
      ((fiberCounts_sum S firstFour).trans hS) hcounts htest

private def flipAxes (mask : Fin 8 → Bool) : Vertex ≃ Vertex :=
  Equiv.piCongrRight fun i =>
    if mask i then Bool.involutive_not.toPerm Bool.not else Equiv.refl Bool

private theorem flipAxes_apply (mask : Fin 8 → Bool) (x : Vertex) (i : Fin 8) :
    flipAxes mask x i = if mask i then !x i else x i := by
  cases hmask : mask i <;> simp [flipAxes, hmask, Function.Involutive.toPerm]

private theorem flipAxes_hamming (mask : Fin 8 → Bool) (x y : Vertex) :
    hammingDist (flipAxes mask x) (flipAxes mask y) = hammingDist x y :=
  hammingDist_comp (fun i => (if mask i then Bool.involutive_not.toPerm Bool.not
    else Equiv.refl Bool : Bool ≃ Bool)) fun _ => Equiv.injective _

private theorem sideCount_flipAxes (S : Finset Vertex) (mask : Fin 8 → Bool) (i : Fin 8) :
    sideCount (S.map (flipAxes mask).toEmbedding) i true =
      sideCount S i (!mask i) := by
  unfold sideCount
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  ext x
  cases hmask : mask i <;> cases hx : x i <;>
    simp [Function.comp_apply, flipAxes_apply, hmask, hx]

private theorem sideCount_add (S : Finset Vertex) (i : Fin 8) :
    sideCount S i true + sideCount S i false = S.card := by
  unfold sideCount
  have hn (x : Vertex) : (¬ x i = true) ↔ x i = false := by cases x i <;> simp
  simpa only [hn] using Finset.card_filter_add_card_filter_not (s := S) (fun x => x i = true)

/-- For a support of size 36 or 39, respectively, if both sides of each of
the first four axes contain at least eleven vertices, the closed neighborhood
has size at least 107 or 110, respectively. -/
theorem closedNeighborhood_lower_bounds (S : Finset Vertex)
    (hm : ∀ (i : Fin 4) (b : Bool), 11 ≤ sideCount S (firstFour i) b) :
    (S.card = 36 → 107 ≤ (closedNeighborhood S).card) ∧
    (S.card = 39 → 110 ≤ (closedNeighborhood S).card) := by
  let mask (i : Fin 8) : Bool :=
    decide (i.val < 4 ∧ sideCount S i false < sideCount S i true)
  let T := S.map (flipAxes mask).toEmbedding
  have heq : T.card = S.card := Finset.card_map _
  have hhood : (closedNeighborhood T).card = (closedNeighborhood S).card := by
    rw [show T = S.map (flipAxes mask).toEmbedding from rfl,
      map_closedNeighborhood _ (flipAxes_hamming mask), Finset.card_map]
  have horiented (i : Fin 4) : 11 ≤ sideCount T (firstFour i) true ∧
      sideCount T (firstFour i) true ≤ T.card / 2 := by
    change 11 ≤ sideCount (S.map (flipAxes mask).toEmbedding) (firstFour i) true ∧ _
    rw [sideCount_flipAxes, heq]
    refine ⟨hm i _, ?_⟩
    have hi : (firstFour i).val < 4 := i.isLt
    have hadd := sideCount_add S (firstFour i)
    by_cases hlt : sideCount S (firstFour i) false < sideCount S (firstFour i) true
    · simp only [mask, hi, hlt, and_self, decide_true, Bool.not_true]
      omega
    · simp only [mask, hi, hlt, and_false, decide_false, Bool.not_false]
      omega
  simpa only [heq, hhood] using closedNeighborhood_lower_bounds_of_oriented T horiented

#print axioms neighborhoodCost_fiberCounts_le
#print axioms projectionConstraints_fiberCounts
#print axioms closedNeighborhood_lower_bounds_of_oriented
#print axioms closedNeighborhood_lower_bounds

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q8OrientedFiberNeighborhood
