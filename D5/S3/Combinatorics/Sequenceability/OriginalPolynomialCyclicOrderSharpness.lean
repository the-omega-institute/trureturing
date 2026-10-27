/- GID: D5/S3/Combinatorics/Sequenceability/OriginalPolynomialCyclicOrderSharpness
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/OriginalPolynomialCyclicOrderSharpness
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: A polynomial-size cyclic group attains the original all-support component bound. -/

import D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderSharpness
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.SetTheory.Cardinal.Finite

/-!
The caller supplied the quadratic refinement in quadratic-cyclic-candidate.txt.
For m ≥ 2 put r=m-1, L=6*r-1, and N=m*L. In ZMod N use natural
representatives q=N-L, p=4*r, a_j=2*r+2*j, and b_j=L-a_j. The a-labels
and p are even; the b-labels and L are odd. All non-q labels together sum
to r*L+4*r<N. A nonempty zero support therefore contains q, and its remaining
natural sum is L. Parity and the bound b_j≥2*r+1 force exactly one b-label;
the remaining sum then forces exactly its matching a-label.

The original coordinates, complete coefficient-one zero-support family,
canonical graph, and structural upper bound are retained. The lower bound
transports the full-family result of OriginalFiniteOrderSharpness, while the
upper bound directly applies OriginalFiniteOrderComponentBound. The carrier
has exactly m*(6*m-7) elements, so its growth is quadratic. This construction
makes no arbitrary-integer-coefficient classification, optimal-carrier claim,
or literature-priority claim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped Classical BigOperators

namespace D5.S3.Combinatorics.Sequenceability.OriginalPolynomialCyclicOrderSharpness

open OriginalFiniteOrderSharpness (Index Coordinate q p a b full triple)
open DisjointMinimalZeroOrdering (MinimalZeroSupport)
open BooleanRowChargeConnectivity (supportIntersectionGraph)
open OriginalFiniteOrderComponentBound (q_containing_component_card_lt)

abbrev rank (m : ℕ) : ℕ := m - 1

def block (m : ℕ) : ℕ := 6 * rank m - 1
def modulus (m : ℕ) : ℕ := m * block m
abbrev WitnessGroup (m : ℕ) := ZMod (modulus m)

def avalue (m : ℕ) (j : Index m) : ℕ := 2 * rank m + 2 * j.val
def bvalue (m : ℕ) (j : Index m) : ℕ := block m - avalue m j

def weight (m : ℕ) : Coordinate m → ℕ
  | Sum.inl none => modulus m - block m
  | Sum.inl (some j) => avalue m j
  | Sum.inr none => 4 * rank m
  | Sum.inr (some j) => bvalue m j

def label (m : ℕ) (x : Coordinate m) : WitnessGroup m := (weight m x : ℕ)

/-- This is the full original proper minimal-zero-support family. -/
def supports (m : ℕ) : Finset (Finset (Coordinate m)) :=
  (full m).powerset.filter
    (fun B => B ⊂ full m ∧ MinimalZeroSupport (label m) B)

private def isB (m : ℕ) : Coordinate m → Prop
  | Sum.inr (some _) => True
  | _ => False

private def bPart (m : ℕ) (D : Finset (Coordinate m)) : Finset (Coordinate m) :=
  D.filter (isB m)

private lemma rank_pos (m : ℕ) (hm : 2 ≤ m) : 0 < rank m := by
  dsimp [rank]
  omega

private lemma block_pos (m : ℕ) (hm : 2 ≤ m) : 0 < block m := by
  have hr := rank_pos m hm
  unfold block
  omega

private lemma four_rank_lt_block (m : ℕ) (hm : 2 ≤ m) :
    4 * rank m < block m := by
  have hr := rank_pos m hm
  unfold block
  omega

private lemma block_lt_modulus (m : ℕ) (hm : 2 ≤ m) :
    block m < modulus m := by
  have hL := block_pos m hm
  have hle := Nat.mul_le_mul_right (block m) hm
  unfold modulus
  omega

private lemma twice_block_le_modulus (m : ℕ) (hm : 2 ≤ m) :
    2 * block m ≤ modulus m := by
  exact Nat.mul_le_mul_right (block m) hm

private lemma modulus_pos (m : ℕ) (hm : 2 ≤ m) : 0 < modulus m :=
  lt_trans (block_pos m hm) (block_lt_modulus m hm)

private lemma avalue_bounds (m : ℕ) (hm : 2 ≤ m) (j : Index m) :
    0 < avalue m j ∧ 2 * rank m ≤ avalue m j ∧
      avalue m j ≤ 4 * rank m - 2 := by
  have hr := rank_pos m hm
  have hj : j.val < rank m := j.isLt
  dsimp [avalue]
  omega

private lemma bvalue_bounds (m : ℕ) (hm : 2 ≤ m) (j : Index m) :
    2 * rank m + 1 ≤ bvalue m j ∧ bvalue m j ≤ 4 * rank m - 1 ∧
      bvalue m j < block m := by
  have hr := rank_pos m hm
  have ha := avalue_bounds m hm j
  dsimp [bvalue, block]
  omega

private lemma pair_value (m : ℕ) (hm : 2 ≤ m) (j : Index m) :
    avalue m j + bvalue m j = block m := by
  have ha := avalue_bounds m hm j
  have hL := four_rank_lt_block m hm
  dsimp [bvalue]
  omega

private lemma block_mod_two (m : ℕ) (hm : 2 ≤ m) : block m % 2 = 1 := by
  have hr := rank_pos m hm
  unfold block
  omega

private lemma avalue_mod_two (m : ℕ) (j : Index m) : avalue m j % 2 = 0 := by
  unfold avalue
  omega

private lemma bvalue_mod_two (m : ℕ) (hm : 2 ≤ m) (j : Index m) :
    bvalue m j % 2 = 1 := by
  have hp := pair_value m hm j
  have hL := block_mod_two m hm
  have ha := avalue_mod_two m j
  omega

private lemma weight_bounds (m : ℕ) (hm : 2 ≤ m) (x : Coordinate m) :
    0 < weight m x ∧ weight m x < modulus m := by
  have hr := rank_pos m hm
  have hL := block_pos m hm
  have h4 := four_rank_lt_block m hm
  have hN := block_lt_modulus m hm
  have hN2 := twice_block_le_modulus m hm
  rcases x with (_ | j) | (_ | j)
  · change 0 < modulus m - block m ∧ modulus m - block m < modulus m
    omega
  · have ha := avalue_bounds m hm j
    change 0 < avalue m j ∧ avalue m j < modulus m
    omega
  · change 0 < 4 * rank m ∧ 4 * rank m < modulus m
    omega
  · have hb := bvalue_bounds m hm j
    change 0 < bvalue m j ∧ bvalue m j < modulus m
    omega

private lemma weight_injective (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (weight m) := by
  have hr := rank_pos m hm
  have h4 := four_rank_lt_block m hm
  have hN := twice_block_le_modulus m hm
  intro x y he
  rcases x with (_ | i) | (_ | i) <;>
    rcases y with (_ | j) | (_ | j) <;> simp only [weight] at he
  · rfl
  · have hj := avalue_bounds m hm j
    omega
  · omega
  · have hj := bvalue_bounds m hm j
    omega
  · have hi := avalue_bounds m hm i
    omega
  · have hij : i = j := Fin.ext (by dsimp [avalue] at he; omega)
    subst j
    rfl
  · have hi := avalue_bounds m hm i
    omega
  · have hi := avalue_mod_two m i
    have hj := bvalue_mod_two m hm j
    omega
  · omega
  · have hj := avalue_bounds m hm j
    omega
  · rfl
  · have hj := bvalue_bounds m hm j
    omega
  · have hi := bvalue_bounds m hm i
    omega
  · have hi := bvalue_mod_two m hm i
    have hj := avalue_mod_two m j
    omega
  · have hi := bvalue_bounds m hm i
    omega
  · have hi := pair_value m hm i
    have hj := pair_value m hm j
    have hv : avalue m i = avalue m j := by omega
    have hij : i = j := Fin.ext (by dsimp [avalue] at hv; omega)
    subst j
    rfl

private lemma label_injective (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (label m) := by
  intro x y he
  apply weight_injective m hm
  have hv := congrArg ZMod.val he
  simpa only [label, ZMod.val_natCast_of_lt (weight_bounds m hm x).2,
    ZMod.val_natCast_of_lt (weight_bounds m hm y).2] using hv

private lemma label_nonzero (m : ℕ) (hm : 2 ≤ m) (x : Coordinate m) :
    label m x ≠ 0 := by
  intro hz
  have hv := congrArg ZMod.val hz
  have hb := weight_bounds m hm x
  simp only [label, ZMod.val_natCast_of_lt hb.2, ZMod.val_zero] at hv
  omega

private lemma label_q_neg (m : ℕ) (hm : 2 ≤ m) :
    label m (q m) = -((block m : ℕ) : WitnessGroup m) := by
  have hle := (block_lt_modulus m hm).le
  change ((modulus m - block m : ℕ) : ZMod (modulus m)) = -((block m : ℕ) : _)
  rw [Nat.cast_sub hle]
  simp

private lemma label_order (m : ℕ) (hm : 2 ≤ m) :
    addOrderOf (label m (q m)) = m := by
  have hdiv : block m ∣ modulus m := ⟨m, by simp [modulus, Nat.mul_comm]⟩
  have hg : Nat.gcd (modulus m) (block m) = block m :=
    Nat.dvd_antisymm (Nat.gcd_dvd_right _ _) (Nat.dvd_gcd hdiv (dvd_refl _))
  rw [label_q_neg m hm, addOrderOf_neg]
  rw [ZMod.addOrderOf_coe _ (ne_of_gt (modulus_pos m hm)), hg]
  exact Nat.mul_div_cancel m (block_pos m hm)

private lemma modulus_polynomial (m : ℕ) (hm : 2 ≤ m) :
    modulus m = m * (6 * m - 7) := by
  have hr : rank m + 1 = m := by dsimp [rank]; omega
  have hblock : block m = 6 * m - 7 := by
    unfold block
    omega
  simp only [modulus, hblock]

private lemma carrier_card (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (WitnessGroup m) = m * (6 * m - 7) := by
  rw [Nat.card_zmod]
  exact modulus_polynomial m hm

private lemma sum_label (m : ℕ) (C : Finset (Coordinate m)) :
    (∑ x ∈ C, label m x) = ((∑ x ∈ C, weight m x : ℕ) : WitnessGroup m) := by
  simp only [label, Nat.cast_sum]

private lemma two_weights_le (m : ℕ) (C : Finset (Coordinate m))
    {x y : Coordinate m} (hxy : x ≠ y) (hx : x ∈ C) (hy : y ∈ C) :
    weight m x + weight m y ≤ ∑ z ∈ C, weight m z := by
  have hsub : ({x, y} : Finset (Coordinate m)) ⊆ C := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  calc
    _ = ∑ z ∈ ({x, y} : Finset (Coordinate m)), weight m z := by simp [hxy]
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

private lemma nonq_sum (m : ℕ) (hm : 2 ≤ m) :
    (∑ x ∈ (Finset.univ : Finset (Coordinate m)).erase (q m), weight m x) =
      rank m * block m + 4 * rank m := by
  have hexpand :
      (∑ x ∈ (Finset.univ : Finset (Coordinate m)).erase (q m), weight m x) =
        (∑ j : Index m, avalue m j) +
          (4 * rank m + ∑ j : Index m, bvalue m j) := by
    rw [← Finset.sum_ite_mem_eq]
    rw [Fintype.sum_sum_type]
    simp [Fintype.sum_option, q, weight]
  have hpairs :
      (∑ j : Index m, avalue m j) + (∑ j : Index m, bvalue m j) =
        rank m * block m := by
    rw [← Finset.sum_add_distrib]
    simp_rw [pair_value m hm]
    simp [Index, rank]
  omega

private lemma nonq_sum_lt_modulus (m : ℕ) (hm : 2 ≤ m) :
    rank m * block m + 4 * rank m < modulus m := by
  have hr : rank m + 1 = m := by dsimp [rank]; omega
  have hrpos := rank_pos m hm
  have hL := four_rank_lt_block m hm
  have hprod : modulus m = rank m * block m + block m := by
    calc
      modulus m = (rank m + 1) * block m := by simp only [modulus, hr]
      _ = _ := by ring
  rw [hprod]
  omega

/-- A zero support has q, and its remaining natural labels sum exactly to L. -/
private lemma zero_rest_sum (m : ℕ) (hm : 2 ≤ m) (C : Finset (Coordinate m))
    (hCn : C.Nonempty) (hz : (∑ x ∈ C, label m x) = 0) :
    q m ∈ C ∧ (∑ x ∈ C.erase (q m), weight m x) = block m := by
  let D := C.erase (q m)
  have hsub : D ⊆ (Finset.univ : Finset (Coordinate m)).erase (q m) := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ _⟩
  have hbound : (∑ x ∈ D, weight m x) ≤ rank m * block m + 4 * rank m := by
    rw [← nonq_sum m hm]
    exact Finset.sum_le_sum_of_subset hsub
  have hlt : (∑ x ∈ D, weight m x) < modulus m :=
    lt_of_le_of_lt hbound (nonq_sum_lt_modulus m hm)
  have hq : q m ∈ C := by
    by_contra hnq
    have hD : D = C := Finset.erase_eq_of_notMem hnq
    have hcast : ((∑ x ∈ D, weight m x : ℕ) : WitnessGroup m) = 0 := by
      rw [hD]
      exact (sum_label m C).symm.trans hz
    have hv := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hv
    obtain ⟨x, hx⟩ := hCn
    have hpos := (weight_bounds m hm x).1
    have hle : weight m x ≤ ∑ z ∈ D, weight m z := by
      apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      rw [hD]
      exact hx
    omega
  have he := Finset.add_sum_erase C (label m) hq
  rw [hz, label_q_neg m hm] at he
  have hsum : (∑ x ∈ D, label m x) = ((block m : ℕ) : WitnessGroup m) := by
    change -((block m : ℕ) : WitnessGroup m) + (∑ x ∈ D, label m x) = 0 at he
    exact (neg_add_eq_zero.mp he).symm
  rw [sum_label] at hsum
  have hv := congrArg ZMod.val hsum
  rw [ZMod.val_natCast_of_lt hlt,
    ZMod.val_natCast_of_lt (block_lt_modulus m hm)] at hv
  exact ⟨hq, hv⟩

/-- For a q-free natural sum L, parity and size force exactly one b-label. -/
private lemma bPart_card_one (m : ℕ) (hm : 2 ≤ m) (D : Finset (Coordinate m))
    (hnq : q m ∉ D) (hsum : (∑ x ∈ D, weight m x) = block m) :
    (bPart m D).card = 1 := by
  have hparity : (∑ x ∈ D, weight m x % 2) = (bPart m D).card := by
    calc
      _ = ∑ x ∈ D, if isB m x then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        rcases x with (_ | i) | (_ | i)
        · exact (hnq hx).elim
        · simpa [weight, isB] using avalue_mod_two m i
        · simp [weight, isB, Nat.mul_mod]
        · simpa [weight, isB] using bvalue_mod_two m hm i
      _ = _ := by simp [bPart]
  have hkodd : (bPart m D).card % 2 = 1 := by
    calc
      _ = (∑ x ∈ D, weight m x % 2) % 2 :=
        congrArg (fun n : ℕ => n % 2) hparity.symm
      _ = (∑ x ∈ D, weight m x) % 2 := (Finset.sum_nat_mod D 2 (weight m)).symm
      _ = 1 := by rw [hsum, block_mod_two m hm]
  have hlow : (2 * rank m + 1) * (bPart m D).card ≤ ∑ x ∈ D, weight m x := by
    calc
      _ = ∑ _x ∈ bPart m D, (2 * rank m + 1) := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ bPart m D, weight m x := by
        apply Finset.sum_le_sum
        intro x hx
        have hxB : isB m x := (Finset.mem_filter.mp hx).2
        rcases x with (_ | j) | (_ | j)
        · simp [isB] at hxB
        · simp [isB] at hxB
        · simp [isB] at hxB
        · exact (bvalue_bounds m hm j).1
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hkle : (bPart m D).card ≤ 2 := by
    by_contra hn
    have hk3 : 3 ≤ (bPart m D).card := by omega
    have hmul := Nat.mul_le_mul_left (2 * rank m + 1) hk3
    have hL : block m < (2 * rank m + 1) * 3 := by unfold block; omega
    omega
  omega

/-- Parity and interval bounds classify ALL nonempty original zero supports. -/
private lemma zero_support_iff (m : ℕ) (hm : 2 ≤ m) (C : Finset (Coordinate m)) :
    (C.Nonempty ∧ (∑ x ∈ C, label m x) = 0) ↔
      ∃ j : Index m, C = triple m j := by
  constructor
  · rintro ⟨hCn, hz⟩
    have hr := rank_pos m hm
    obtain ⟨hq, hsum⟩ := zero_rest_sum m hm C hCn hz
    let D := C.erase (q m)
    have hDsum : (∑ x ∈ D, weight m x) = block m := hsum
    have hnqD : q m ∉ D := Finset.notMem_erase _ _
    have hsome : ∃ j : Index m, bPart m D = {b m j} := by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (bPart_card_one m hm D hnqD hDsum)
      have hxmem : x ∈ bPart m D := by rw [hx]; exact Finset.mem_singleton_self _
      have hxB : isB m x := (Finset.mem_filter.mp hxmem).2
      rcases x with (_ | j) | (_ | j)
      · simp [isB] at hxB
      · simp [isB] at hxB
      · simp [isB] at hxB
      · exact ⟨j, hx⟩
    obtain ⟨j, hBj⟩ := hsome
    have hjB : b m j ∈ bPart m D := by rw [hBj]; exact Finset.mem_singleton_self _
    have hj : b m j ∈ D := (Finset.mem_filter.mp hjB).1
    have huniq (i : Index m) (hi : b m i ∈ D) : i = j := by
      have hiB : b m i ∈ bPart m D := Finset.mem_filter.mpr ⟨hi, trivial⟩
      rw [hBj] at hiB
      have he : b m i = b m j := Finset.mem_singleton.mp hiB
      simpa [b] using he
    let R := D.erase (b m j)
    have hRsum : (∑ x ∈ R, weight m x) = avalue m j := by
      have he := Finset.add_sum_erase D (weight m) hj
      rw [hDsum] at he
      change bvalue m j + (∑ x ∈ R, weight m x) = block m at he
      have hp := pair_value m hm j
      omega
    have hnq : q m ∉ R := by
      intro hx
      have hxD := Finset.mem_of_mem_erase hx
      exact (Finset.mem_erase.mp hxD).1 rfl
    have hnb (i : Index m) : b m i ∉ R := by
      intro hx
      have hi := huniq i (Finset.mem_of_mem_erase hx)
      subst i
      exact Finset.notMem_erase _ _ hx
    have hnp : p m ∉ R := by
      intro hx
      have hle : weight m (p m) ≤ ∑ x ∈ R, weight m x :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
      change 4 * rank m ≤ ∑ x ∈ R, weight m x at hle
      have hjA := (avalue_bounds m hm j).2.2
      omega
    have hRa (x : Coordinate m) (hx : x ∈ R) : ∃ i : Index m, x = a m i := by
      rcases x with (_ | i) | (_ | i)
      · exact (hnq hx).elim
      · exact ⟨i, rfl⟩
      · exact (hnp hx).elim
      · exact (hnb i hx).elim
    have hRn : R.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      rw [he, Finset.sum_empty] at hRsum
      have hpos := (avalue_bounds m hm j).1
      omega
    obtain ⟨x, hx⟩ := hRn
    obtain ⟨i, rfl⟩ := hRa x hx
    have hRsingle : R = {a m i} := by
      ext y
      simp only [Finset.mem_singleton]
      constructor
      · intro hy
        obtain ⟨k, rfl⟩ := hRa y hy
        by_contra hne
        have hle := two_weights_le m R hne hy hx
        change avalue m k + avalue m i ≤ ∑ x ∈ R, weight m x at hle
        have hkA := (avalue_bounds m hm k).2.1
        have hiA := (avalue_bounds m hm i).2.1
        have hjA := (avalue_bounds m hm j).2.2
        omega
      · rintro rfl
        exact hx
    have hv : avalue m i = avalue m j := by
      simpa only [hRsingle, Finset.sum_singleton, a, weight] using hRsum
    have hij : i = j := Fin.ext (by dsimp [avalue] at hv; omega)
    subst i
    refine ⟨j, ?_⟩
    have hCrestore : insert (q m) D = C := Finset.insert_erase hq
    have hDrestore : insert (b m j) R = D := Finset.insert_erase hj
    rw [← hCrestore, ← hDrestore, hRsingle]
    ext y
    simp only [triple, Finset.mem_insert, Finset.mem_singleton]
    tauto
  · rintro ⟨j, rfl⟩
    refine ⟨⟨q m, by simp [triple]⟩, ?_⟩
    have hsum : (∑ x ∈ triple m j, label m x) =
        label m (q m) + (label m (a m j) + label m (b m j)) := by
      simp [triple, q, a, b]
    have hab : label m (a m j) + label m (b m j) =
        ((block m : ℕ) : WitnessGroup m) := by
      change (avalue m j : WitnessGroup m) + (bvalue m j : WitnessGroup m) = _
      simpa only [Nat.cast_add] using
        congrArg (fun n : ℕ => (n : WitnessGroup m)) (pair_value m hm j)
    rw [hsum, label_q_neg m hm, hab]
    exact neg_add_cancel _

private lemma minimal_support_equiv (m : ℕ) (hm : 2 ≤ m) (B : Finset (Coordinate m)) :
    MinimalZeroSupport (label m) B ↔
      MinimalZeroSupport (OriginalFiniteOrderSharpness.label m) B := by
  have hproduct := (OriginalFiniteOrderSharpness.sharpness m hm).2.2.2.2.2.1
  have he (C : Finset (Coordinate m)) :
      (C.Nonempty ∧ (∑ x ∈ C, label m x) = 0) ↔
        (C.Nonempty ∧ (∑ x ∈ C, OriginalFiniteOrderSharpness.label m x) = 0) :=
    (zero_support_iff m hm C).trans (hproduct C).symm
  constructor
  · rintro ⟨hn, hz, hmin⟩
    have hB := (he B).mp ⟨hn, hz⟩
    refine ⟨hB.1, hB.2, ?_⟩
    intro C hsub hCn hCz
    exact hmin C hsub hCn ((he C).mpr ⟨hCn, hCz⟩).2
  · rintro ⟨hn, hz, hmin⟩
    have hB := (he B).mpr ⟨hn, hz⟩
    refine ⟨hB.1, hB.2, ?_⟩
    intro C hsub hCn hCz
    exact hmin C hsub hCn ((he C).mp ⟨hCn, hCz⟩).2

private lemma supports_eq_product (m : ℕ) (hm : 2 ≤ m) :
    supports m = OriginalFiniteOrderSharpness.supports m := by
  ext B
  simp only [supports, OriginalFiniteOrderSharpness.supports, Finset.mem_filter,
    minimal_support_equiv m hm B]

/-- The cyclic carrier is explicitly quadratic in m, with the entire original
coordinate set and ALL proper original minimal zero supports retained. -/
theorem sharpness (m : ℕ) (hm : 2 ≤ m) :
    Finite (WitnessGroup m) ∧
    IsAddCyclic (WitnessGroup m) ∧
    Nat.card (WitnessGroup m) = m * (6 * m - 7) ∧
    Function.Injective (label m) ∧
    (∀ x : Coordinate m, label m x ≠ 0) ∧
    q m ∈ full m ∧
    addOrderOf (label m (q m)) = m ∧
    (∀ C : Finset (Coordinate m),
      (C.Nonempty ∧ (∑ x ∈ C, label m x) = 0) ↔
        ∃ j : Index m, C = triple m j) ∧
    (∀ B : Finset (Coordinate m),
      B ∈ supports m ↔ B ⊂ full m ∧ MinimalZeroSupport (label m) B) ∧
    (supports m).card = m - 1 ∧
    (∀ B ∈ supports m, q m ∈ B) ∧
    (∀ B ∈ supports m, ∀ D ∈ supports m, B ≠ D →
      Disjoint (B.erase (q m)) (D.erase (q m))) ∧
    (((Finset.univ : Finset (supports m)).filter
        (fun B : supports m => q m ∈ B.val)).image
      (supportIntersectionGraph (supports m) (q m)).connectedComponentMk).card = m - 1 := by
  letI : NeZero (modulus m) := ⟨ne_of_gt (modulus_pos m hm)⟩
  have hfinite : Finite (WitnessGroup m) := by infer_instance
  have hcyclic : IsAddCyclic (WitnessGroup m) := by infer_instance
  obtain ⟨_, _, _, _, _, _, hmemP, hcardP, hqP, hdisP, hgraphP⟩ :=
    OriginalFiniteOrderSharpness.sharpness m hm
  have hE := supports_eq_product m hm
  have hmem (B : Finset (Coordinate m)) :
      B ∈ supports m ↔ B ⊂ full m ∧ MinimalZeroSupport (label m) B := by
    rw [hE, hmemP B, minimal_support_equiv m hm B]
  have hcard : (supports m).card = m - 1 := by rw [hE]; exact hcardP
  have hq : ∀ B ∈ supports m, q m ∈ B := by simpa only [hE] using hqP
  have hdis : ∀ B ∈ supports m, ∀ D ∈ supports m, B ≠ D →
      Disjoint (B.erase (q m)) (D.erase (q m)) := by
    simpa only [hE] using hdisP
  have hlower : m - 1 ≤
      (((Finset.univ : Finset (supports m)).filter
          (fun B : supports m => q m ∈ B.val)).image
        (supportIntersectionGraph (supports m) (q m)).connectedComponentMk).card := by
    rw [hE]
    exact Nat.le_of_eq hgraphP.symm
  have hmzero : m • label m (q m) = 0 := by
    simpa only [label_order m hm] using addOrderOf_nsmul_eq_zero (label m (q m))
  have hcanonical :=
    q_containing_component_card_lt (α := Coordinate m) (G := WitnessGroup m)
      (label m) (full m) (supports m) hmem (q m) m hm hmzero
  have hupper :
      (((Finset.univ : Finset (supports m)).filter
          (fun B : supports m => q m ∈ B.val)).image
        (supportIntersectionGraph (supports m) (q m)).connectedComponentMk).card < m := by
    refine lt_of_eq_of_lt ?_ hcanonical
    congr 1
    ext c
    simp
  have hcount := Nat.le_antisymm (Nat.le_sub_one_of_lt hupper) hlower
  exact ⟨hfinite, hcyclic, carrier_card m hm, label_injective m hm,
    label_nonzero m hm, Finset.mem_univ _, label_order m hm,
    zero_support_iff m hm, hmem, hcard, hq, hdis, hcount⟩

end D5.S3.Combinatorics.Sequenceability.OriginalPolynomialCyclicOrderSharpness
