/- GID: D5/S3/Fourier/Concentration/DisjointTriplePhaseIdentity
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/DisjointTriplePhaseIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Disjoint triples isolate a mixed phase term beyond the pair spectrum. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

open Finset

namespace D5.S3.Fourier.Concentration.DisjointTriplePhaseIdentity

/-! The disjoint degree-three sum for complementary weights in a commutative ring. -/

set_option autoImplicit false

universe uv uJ uR

variable {V : Type uv} {J : Type uJ} {R : Type uR}

private def merge [DecidableEq V] (r : V → V) (a b : V) (v : V) : V :=
  if r v = r b then r a else r v

private theorem merge_idempotent [DecidableEq V] {r : V → V} (hr : ∀ v, r (r v) = r v)
    (a b : V) : ∀ v, merge r a b (merge r a b v) = merge r a b v := by
  intro v
  by_cases h : r v = r b
  · simp only [merge, h, ite_true, hr a]
    split <;> rfl
  · simp [merge, h, hr v]

private theorem merge_preserves_iff [DecidableEq V] {r : V → V} (hr : ∀ v, r (r v) = r v)
    (a b : V) (f : V → J) :
    (∀ v, f (merge r a b v) = f v) ↔ (∀ v, f (r v) = f v) ∧ f a = f b := by
  constructor
  · intro hf
    have ha : f (r a) = f a := by
      by_cases hab : r a = r b
      · simpa [merge, hab] using hf a
      · simpa [merge, hab] using hf a
    have hb : f (r a) = f b := by simpa [merge] using hf b
    have hroot : f (r a) = f (r b) := by simpa [merge, hr b] using hf (r b)
    refine ⟨fun v => ?_, ha.symm.trans hb⟩
    by_cases hv : r v = r b
    · rw [hv, ← hroot]
      simpa [merge, hv] using hf v
    · simpa [merge, hv] using hf v
  · rintro ⟨hf, hab⟩ v
    by_cases hv : r v = r b
    · simp only [merge, hv, ite_true]
      rw [hf a, hab, ← hf b, ← hv, hf v]
    · simpa [merge, hv] using hf v

private def collapse [DecidableEq V] : List (V × V) → V → V
  | [] => id
  | edge :: rest => merge (collapse rest) edge.1 edge.2

private theorem collapse_idempotent [DecidableEq V] (edges : List (V × V)) :
    ∀ v, collapse edges (collapse edges v) = collapse edges v := by
  induction edges with
  | nil => intro v; rfl
  | cons e rest ih => exact merge_idempotent ih e.1 e.2

private theorem collapse_preserves_iff [DecidableEq V] (edges : List (V × V)) (f : V → J) :
    (∀ v, f (collapse edges v) = f v) ↔ ∀ e ∈ edges, f e.1 = f e.2 := by
  induction edges with
  | nil => simp [collapse]
  | cons e rest ih =>
    simp [collapse, merge_preserves_iff (collapse_idempotent rest), ih, and_comm]

private abbrev Root (r : V → V) := {v : V // r v = v}

private def assignmentEquiv {r : V → V} (hr : ∀ v, r (r v) = r v) :
    {f : V → J // ∀ v, f (r v) = f v} ≃ (Root r → J) where
  toFun f v := f.val v.val
  invFun g := ⟨fun v => g ⟨r v, hr v⟩, fun v => by simp only [hr v]⟩
  left_inv f := Subtype.ext (funext f.property)
  right_inv g := funext fun v => congrArg g (Subtype.ext v.property)


private theorem constrained_sum_factor [Fintype V] [Fintype J] [DecidableEq V] [DecidableEq J]
    [CommSemiring R] (r : V → V) (hr : ∀ v, r (r v) = r v) (weight : V → J → R) :
    (∑ f : {f : V → J // ∀ v, f (r v) = f v}, ∏ v : V, weight v (f.val v)) =
      ∏ c : Root r, ∑ j : J, ∏ v ∈ univ.filter (fun v => r v = c.val), weight v j := by
  let root (v : V) : Root r := ⟨r v, hr v⟩
  let block (c : Root r) (j : J) := ∏ v ∈ univ.filter (fun v => root v = c), weight v j
  have hblock (c : Root r) (j : J) :
      block c j = ∏ v ∈ univ.filter (fun v => r v = c.val), weight v j := by
    apply prod_congr
    · ext v
      simp only [mem_filter, mem_univ, true_and]
      exact Subtype.ext_iff
    · intros
      rfl
  have hprod (g : Root r → J) :
      (∏ v : V, weight v (g (root v))) = ∏ c : Root r, block c (g c) := by
    calc
      _ = ∏ c : Root r, ∏ v ∈ univ.filter (fun v => root v = c), weight v (g (root v)) :=
        (prod_fiberwise (univ : Finset V) root (fun v => weight v (g (root v)))).symm
      _ = _ := by
        apply prod_congr rfl
        intro c _
        apply prod_congr rfl
        intro v hv
        rw [(mem_filter.mp hv).2]
  calc
    _ = ∑ g : Root r → J, ∏ v : V, weight v (g (root v)) := by
      apply Fintype.sum_equiv (assignmentEquiv hr)
      intro f
      apply prod_congr rfl
      intro v _
      exact congrArg (weight v) (f.property v).symm
    _ = ∑ g : Root r → J, ∏ c : Root r, block c (g c) := sum_congr rfl fun g _ => hprod g
    _ = ∏ c : Root r, ∑ j : J, block c j := (Fintype.prod_sum block).symm
    _ = _ := by simp only [hblock]


abbrev Slots := Fin 3 ⊕ Fin 3
private abbrev Edge := Fin 3 × Fin 3

private def endpoints (e : Edge) : Slots × Slots := (Sum.inl e.1, Sum.inr e.2)

private def listedEdges (s : Finset Edge) : List Edge :=
  ((List.finRange 9).map (finProdFinEquiv : Edge ≃ Fin 9).symm).filter (· ∈ s)

private theorem mem_listedEdges (s : Finset Edge) (e : Edge) : e ∈ listedEdges s ↔ e ∈ s := by
  have h : e ∈ (List.finRange 9).map (finProdFinEquiv : Edge ≃ Fin 9).symm :=
    List.mem_map.mpr ⟨(finProdFinEquiv : Edge ≃ Fin 9) e, List.mem_finRange _,
      (finProdFinEquiv : Edge ≃ Fin 9).symm_apply_apply e⟩
  simp [listedEdges, h]

private def reps (s : Finset Edge) : Slots → Slots := collapse ((listedEdges s).map endpoints)

private theorem reps_idempotent (s : Finset Edge) (v : Slots) : reps s (reps s v) = reps s v :=
  collapse_idempotent _ v

private theorem reps_preserves_iff (s : Finset Edge) (f : Slots → J) :
    (∀ v, f (reps s v) = f v) ↔ ∀ e ∈ s, f (Sum.inl e.1) = f (Sum.inr e.2) := by
  rw [reps, collapse_preserves_iff]
  constructor
  · intro hf e he
    exact hf (endpoints e) (List.mem_map.mpr ⟨e, (mem_listedEdges s e).mpr he, rfl⟩)
  · rintro hf _ he
    obtain ⟨e, hmem, rfl⟩ := List.mem_map.mp he
    exact hf e ((mem_listedEdges s e).mp hmem)

/-- Weight of pairs of ordered triples with disjoint index supports. -/
def disjointMass [Fintype J] [DecidableEq J] [CommRing R] (weight : Slots → J → R) : R :=
  ∑ f : Slots → J,
    if ∀ e : Edge, f (Sum.inl e.1) ≠ f (Sum.inr e.2) then ∏ v, weight v (f v) else 0

private theorem disjointMass_component_expansion [Fintype J] [DecidableEq J] [CommRing R]
    (weight : Slots → J → R) :
    disjointMass weight =
      ∑ s ∈ (univ : Finset Edge).powerset, (-1 : R) ^ s.card *
        ∏ c : Root (reps s), ∑ j : J,
          ∏ v ∈ univ.filter (fun v => reps s v = c.val), weight v j := by
  let edgeEqual (f : Slots → J) (e : Edge) := f (Sum.inl e.1) = f (Sum.inr e.2)
  let indicator (f : Slots → J) (e : Edge) : R := if edgeEqual f e then 1 else 0
  let fw (f : Slots → J) := ∏ v, weight v (f v)
  have complementTerm (f : Slots → J) (e : Edge) :
      1 - indicator f e = if ¬ edgeEqual f e then 1 else 0 := by
    by_cases h : edgeEqual f e <;> simp [indicator, h]
  have disjointTerm (f : Slots → J) :
      (if ∀ e, ¬ edgeEqual f e then fw f else 0) =
        (∏ e : Edge, (1 - indicator f e)) * fw f := by
    simp_rw [complementTerm]
    rw [Fintype.prod_ite_zero]
    split <;> simp
  have productExpand (f : Slots → J) :
      (∏ e : Edge, (1 - indicator f e)) =
        ∑ s ∈ (univ : Finset Edge).powerset, (-1 : R) ^ s.card *
          ∏ e ∈ s, indicator f e := by
    simpa only [prod_const_one, mul_one] using
      (prod_sub (fun _ : Edge => (1 : R)) (indicator f) univ)
  have matchTerm (s : Finset Edge) (f : Slots → J) :
      (∏ e ∈ s, indicator f e) * fw f =
        if ∀ v, f (reps s v) = f v then fw f else 0 := by
    simp only [indicator, Finset.prod_ite_zero, prod_const_one]
    have hp : (∀ e ∈ s, edgeEqual f e) ↔ ∀ v, f (reps s v) = f v :=
      (reps_preserves_iff s f).symm
    simp only [hp]
    split <;> simp
  have same_sum (s : Finset Edge) :
      (∑ f : Slots → J, if ∀ v, f (reps s v) = f v then fw f else 0) =
        ∏ c : Root (reps s), ∑ j : J,
          ∏ v ∈ univ.filter (fun v => reps s v = c.val), weight v j := by
    rw [← sum_filter, ← sum_subtype_eq_sum_filter, subtype_univ]
    exact constrained_sum_factor (reps s) (reps_idempotent s) weight
  unfold disjointMass
  change (∑ f : Slots → J, if ∀ e, ¬ edgeEqual f e then fw f else 0) = _
  simp only [disjointTerm, productExpand, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  simp only [mul_assoc, matchTerm, ← mul_sum, same_sum]


private def componentSlots (s : Finset Edge) (c : Root (reps s)) : Finset Slots :=
  univ.filter (fun v => reps s v = c.val)

private def imbalance (s : Finset Edge) (c : Root (reps s)) : ℤ :=
  (((componentSlots s c).filter (fun v => v.isLeft)).card : ℤ) -
    ((componentSlots s c).filter (fun v => !v.isLeft)).card

private def labels (s : Finset Edge) (k : ℤ) : Finset (Root (reps s)) :=
  univ.filter (fun c => imbalance s c = k)

private def signature (s : Finset Edge) : List ℤ :=
  (List.finRange 5).flatMap (fun i => List.replicate (labels s ((i.val : ℤ)-2)).card ((i.val : ℤ)-2))

private def possibleSignatures : Finset (List ℤ) :=
  (univ : Finset Edge).powerset.image signature

private def signedMultiplicity (m : List ℤ) : ℤ :=
  ∑ s ∈ (univ : Finset Edge).powerset with signature s = m, (-1 : ℤ) ^ s.card

private def signatureTable : Finset (List ℤ × ℤ) :=
  { ([-2,1,1], -3), ([-1,-1,2], -3),
    ([-1,-1,-1,1,1,1], 1), ([-1,-1,0,1,1], -9), ([-1,-1,1,1], 18),
    ([-1,0,0,1], 18), ([-1,0,1], -63), ([-1,1], 51),
    ([0], -31), ([0,0], 27), ([0,0,0], -6) }



set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The certificate enumerates the 512 subsets of the nine cross edges.
private theorem signature_table_correct :
    possibleSignatures.image (fun m => (m, signedMultiplicity m)) = signatureTable := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
-- All components of the cross-edge subsets are covered.
private theorem imbalance_range :
    ∀ (s : Finset Edge) (c : Root (reps s)), -2 ≤ imbalance s c ∧ imbalance s c ≤ 2 := by
  decide

private theorem component_product [CommMonoid R] (s : Finset Edge) (z : ℤ → R) :
    (∏ c : Root (reps s), z (imbalance s c)) = ((signature s).map z).prod := by
  let label (c : Root (reps s)) : Fin 5 :=
    ⟨(imbalance s c + 2).toNat, by obtain ⟨_, _⟩ := imbalance_range s c; omega⟩
  have label_spec (c : Root (reps s)) : (label c).val - (2 : ℤ) = imbalance s c := by
    obtain ⟨ha, _⟩ := imbalance_range s c
    dsimp [label]
    omega
  calc
    _ = ∏ i : Fin 5, ∏ c ∈ univ.filter (fun c => label c = i), z (imbalance s c) :=
      (prod_fiberwise univ label (fun c => z (imbalance s c))).symm
    _ = ∏ i : Fin 5, (z ((i.val : ℤ) - 2)) ^ (labels s ((i.val : ℤ) - 2)).card := by
      apply prod_congr rfl
      intro i _
      rw [← prod_const]
      apply prod_congr
      · ext c
        simp only [labels, mem_filter, mem_univ, true_and]
        rw [← label_spec c, sub_left_inj]
        norm_cast
        exact Fin.ext_iff
      · intro c hc
        exact congrArg z (mem_filter.mp hc).2
    _ = _ := by
      rw [Fin.prod_univ_def]
      unfold signature
      generalize List.finRange 5 = xs
      induction xs with
      | nil => rfl
      | cons i rest ih =>
        simp only [List.flatMap_cons, List.map_append, List.map_cons, List.prod_append,
          List.prod_cons, List.map_replicate, List.prod_replicate, ih]

private def signedPower [Monoid R] (x y : R) (n : ℤ) : R :=
  if 0 ≤ n then x ^ n.toNat else y ^ (-n).toNat

private theorem mul_pow_eq_signedPower [CommMonoid R] (x y : R) (hxy : x * y = 1)
    (a b : ℕ) : x ^ a * y ^ b = signedPower x y ((a : ℤ) - b) := by
  rcases le_or_gt b a with h | h
  · have ht : 0 ≤ (a : ℤ) - b := sub_nonneg.mpr (by exact_mod_cast h)
    have hm : ((a : ℤ) - b).toNat = a - b := by omega
    rw [signedPower, ite_eq_left ht, hm]
    calc
      _ = x ^ (a - b) * (x * y) ^ b := by
        rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel h]
      _ = _ := by simp [hxy]
  · have ht : ¬ 0 ≤ (a : ℤ) - b := by omega
    have hm : (-((a : ℤ) - b)).toNat = b - a := by omega
    rw [signedPower, ite_eq_right ht, hm]
    calc
      _ = (x * y) ^ a * y ^ (b - a) := by
        rw [mul_pow, mul_assoc, ← pow_add, Nat.add_comm a, Nat.sub_add_cancel h.le]
      _ = _ := by simp [hxy]

/-- Use the first weight family on the left slots and the second on the right slots. -/
def slotWeight [Monoid R] (x y : J → R) : Slots → J → R :=
  fun v j => if v.isLeft then x j else y j

private theorem prod_slotWeight_eq [CommMonoid R] (x y : J → R) (hx : ∀ j, x j * y j = 1)
    (s : Finset Slots) (j : J) :
    (∏ v ∈ s, slotWeight x y v j) =
      signedPower (x j) (y j) (((s.filter (fun v => v.isLeft)).card : ℤ) -
        (s.filter (fun v => !v.isLeft)).card) := by
  have hsplit := prod_filter_mul_prod_filter_not s (fun v => v.isLeft) (fun v => slotWeight x y v j)
  have left : (∏ v ∈ s with v.isLeft, slotWeight x y v j) = (x j) ^ (s.filter (fun v => v.isLeft)).card := by
    rw [← prod_const]
    exact prod_congr rfl fun v hv => ite_eq_left (mem_filter.mp hv).2
  have right : (∏ v ∈ s with ¬ v.isLeft, slotWeight x y v j) =
      (y j) ^ (s.filter (fun v => !v.isLeft)).card := by
    rw [← prod_const]
    apply prod_congr
    · ext v
      simp
    · intro v hv
      exact ite_eq_right (by simpa using (mem_filter.mp hv).2)
  rw [← hsplit, left, right, mul_pow_eq_signedPower _ _ (hx j)]


private theorem signed_signature_sum [CommRing R] (z : ℤ → R) :
    (∑ s ∈ (univ : Finset Edge).powerset,
      (-1 : R) ^ s.card * ∏ c : Root (reps s), z (imbalance s c)) =
      ∑ row ∈ signatureTable, (row.2 : R) * (row.1.map z).prod := by
  simp only [component_product]
  have hfib (m : List ℤ) :
      (∑ s ∈ (univ : Finset Edge).powerset with signature s = m,
        (-1 : R) ^ s.card * (m.map z).prod) = (signedMultiplicity m : R) * (m.map z).prod := by
    rw [← sum_mul, signedMultiplicity, Int.cast_sum]
    simp
  calc
    _ = ∑ m ∈ possibleSignatures,
        ∑ s ∈ (univ : Finset Edge).powerset with signature s = m,
          (-1 : R) ^ s.card * (m.map z).prod := by
      symm
      rw [← sum_fiberwise_of_maps_to (fun s hs => mem_image_of_mem signature hs)]
      apply sum_congr rfl
      intro m _
      apply sum_congr rfl
      intro s hs
      rw [(mem_filter.mp hs).2]
    _ = ∑ m ∈ possibleSignatures, (signedMultiplicity m : R) * (m.map z).prod := by
      simp only [hfib]
    _ = _ := by
      rw [← signature_table_correct, sum_image]
      intro a _ b _ heq
      exact congrArg Prod.fst heq

/-- The pair contribution as a polynomial in the alphabet size and first power product. -/
def pairPolynomial [CommRing R] (nu : R × R) : R :=
  let (n, u) := nu
  u ^ 3 + (18 - 9 * n) * u ^ 2 + (18 * n ^ 2 - 63 * n + 51) * u
    - 6 * n ^ 3 + 27 * n ^ 2 - 31 * n

/-- The full pair data and one mixed phase contribution determine the disjoint triple sum. -/
theorem disjoint_triple_phase_identity [Fintype J] [DecidableEq J] [CommRing R]
    (x y : J → R) (hxy : ∀ j, x j * y j = 1) :
    let pairPart := pairPolynomial (R := R)
    disjointMass (slotWeight x y) =
      pairPart ((Fintype.card J : R), (∑ j, x j) * ∑ j, y j) -
        3 * ((∑ j, x j ^ 2) * (∑ j, y j) ^ 2 + (∑ j, y j ^ 2) * (∑ j, x j) ^ 2) := by
  dsimp only
  rw [disjointMass_component_expansion]
  have hblock (s : Finset Edge) (c : Root (reps s)) :
      (∑ j : J, ∏ v ∈ univ.filter (fun v => reps s v = c.val), slotWeight x y v j) =
        ∑ j : J, signedPower (x j) (y j) (imbalance s c) := by
    apply sum_congr rfl
    intro j _
    exact prod_slotWeight_eq x y hxy (componentSlots s c) j
  simp only [hblock]
  rw [signed_signature_sum (fun k => ∑ j, signedPower (x j) (y j) k)]
  simp [signatureTable, signedPower, pairPolynomial]
  ring

end D5.S3.Fourier.Concentration.DisjointTriplePhaseIdentity
