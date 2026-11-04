/- GID: D5/S3/Combinatorics/Sequenceability/OriginalAffineBinarySharpness
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/OriginalAffineBinarySharpness
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.Data.Nat.Log]
   utility: none
   digest: Affine binary points realize original zero supports at every odd order. -/

import D5.S3.Combinatorics.Sequenceability.OriginalFiniteOrderSharpness
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite

/-!
Put m=2*s+1 and d=clog 2 (2*s).  Embed the m-1 pair indices in the
binary d-space, and place their vectors in the affine half-space with
first coordinate one.  An even nonempty zero subset of these distinct
points has at least four members.  This, together with the torsion
coordinate, excludes every nonempty original zero support except a triple.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped Classical BigOperators

namespace D5.S3.Combinatorics.Sequenceability.OriginalAffineBinarySharpness

open OriginalFiniteOrderSharpness (Index Coordinate q p a b triple coordinate_sum)

def modulus (s : ℕ) : ℕ := 2 * s + 1
def dimension (s : ℕ) : ℕ := Nat.clog 2 (2 * s)
abbrev PairIndex (s : ℕ) := Index (modulus s)
abbrev Vector (s : ℕ) := Fin (dimension s) → ZMod 2
abbrev Binary (s : ℕ) := ZMod 2 × Vector s
abbrev WitnessGroup (s : ℕ) := ZMod (modulus s) × Binary s

/-- The numerical logarithm bound supplies the injection; it is not a
zero-support assumption. -/
def vectorEmbedding (s : ℕ) : PairIndex s ↪ Vector s :=
  Classical.choice (Function.Embedding.nonempty_of_card_le
    (α := PairIndex s) (β := Vector s) (by
      have h := Nat.le_pow_clog (by decide : 1 < 2) (2 * s)
      have hsize : Fintype.card (Vector s) = 2 ^ dimension s := by
        rw [← Nat.card_eq_fintype_card]
        change Nat.card (Fin (dimension s) → ZMod 2) = 2 ^ dimension s
        rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      rw [hsize]
      simpa [PairIndex, Index, modulus, dimension] using h))

def point (s : ℕ) (i : PairIndex s) : Binary s := (1, vectorEmbedding s i)

private lemma dimension_pos (s : ℕ) (hs : 1 ≤ s) : 0 < dimension s := by
  exact Nat.clog_pos (by decide) (by omega)

private def originAxis (s : ℕ) (hs : 1 ≤ s) : Fin (dimension s) :=
  ⟨0, dimension_pos s hs⟩

def sentinel (s : ℕ) (hs : 1 ≤ s) : Binary s :=
  (0, Pi.single (originAxis s hs) 1)

def label (s : ℕ) (hs : 1 ≤ s) : Coordinate (modulus s) → WitnessGroup s
  | Sum.inl none => (1, 0)
  | Sum.inl (some i) => (s, point s i)
  | Sum.inr none => (-1, sentinel s hs)
  | Sum.inr (some i) => (s, point s i)

private lemma point_injective (s : ℕ) : Function.Injective (point s) := by
  intro i j h
  exact (vectorEmbedding s).injective (congrArg Prod.snd h)

private lemma sentinel_nonzero (s : ℕ) (hs : 1 ≤ s) : sentinel s hs ≠ 0 := by
  intro h
  have he := congrArg (fun z : Binary s => z.2 (originAxis s hs)) h
  norm_num [sentinel] at he

private lemma twice_binary (s : ℕ) (v : Binary s) : v + v = 0 := by
  apply Prod.ext
  · exact CharTwo.add_self_eq_zero v.1
  · funext j
    exact CharTwo.add_self_eq_zero (v.2 j)

private lemma points_sum_first (s : ℕ) (T : Finset (PairIndex s)) :
    (∑ i ∈ T, point s i).1 = (T.card : ZMod 2) := by
  simp [Prod.fst_sum, point, Finset.sum_const, nsmul_eq_mul]

/-- Distinct affine points cannot form a two-member zero subset. -/
private lemma zero_sum_card_ne_two (s : ℕ) (T : Finset (PairIndex s))
    (hz : (∑ i ∈ T, point s i) = 0) : T.card ≠ 2 := by
  intro hc
  obtain ⟨i, j, hij, hT⟩ := Finset.card_eq_two.mp hc
  have hsum : point s i + point s j = 0 := by
    simpa [hT, hij] using hz
  have he : point s i = point s j := by
    calc
      point s i = point s i + (point s j + point s j) := by
        rw [twice_binary, add_zero]
      _ = (point s i + point s j) + point s j := (add_assoc _ _ _).symm
      _ = point s j := by rw [hsum, zero_add]
  exact hij (point_injective s he)

private def singles (s : ℕ) (C : Finset (Coordinate (modulus s))) :
    Finset (PairIndex s) := Finset.univ.filter (fun i =>
      (a (modulus s) i ∈ C ∧ b (modulus s) i ∉ C) ∨
      (a (modulus s) i ∉ C ∧ b (modulus s) i ∈ C))

private def doubles (s : ℕ) (C : Finset (Coordinate (modulus s))) :
    Finset (PairIndex s) := Finset.univ.filter (fun i =>
      a (modulus s) i ∈ C ∧ b (modulus s) i ∈ C)

private def epsilon (s : ℕ) (C : Finset (Coordinate (modulus s))) : ℕ :=
  if q (modulus s) ∈ C then 1 else 0

private lemma epsilon_le_one (s : ℕ) (C : Finset (Coordinate (modulus s))) :
    epsilon s C ≤ 1 := by
  unfold epsilon
  split_ifs <;> omega

private lemma singles_doubles_bound (s : ℕ)
    (C : Finset (Coordinate (modulus s))) :
    (singles s C).card + (doubles s C).card ≤ 2 * s := by
  have hd : Disjoint (singles s C) (doubles s C) := by
    apply Finset.disjoint_left.mpr
    intro i hi hd
    have hab : a (modulus s) i ∈ C ∧ b (modulus s) i ∈ C := by
      simpa [doubles] using hd
    simp [singles, hab.1, hab.2] at hi
  have hc := Finset.card_le_univ (singles s C ∪ doubles s C)
  rw [Finset.card_union_of_disjoint hd] at hc
  simpa [PairIndex, Index, modulus] using hc

private lemma binary_sum (s : ℕ) (hs : 1 ≤ s)
    (C : Finset (Coordinate (modulus s))) :
    (∑ x ∈ C, label s hs x).2 =
      (∑ i ∈ singles s C, point s i) +
      (if p (modulus s) ∈ C then sentinel s hs else 0) := by
  have hab :
      (∑ i : PairIndex s, if a (modulus s) i ∈ C then point s i else 0) +
      (∑ i : PairIndex s, if b (modulus s) i ∈ C then point s i else 0) =
      ∑ i ∈ singles s C, point s i := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i : PairIndex s, if i ∈ singles s C then point s i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases ha : a (modulus s) i ∈ C <;>
          by_cases hb : b (modulus s) i ∈ C <;>
          simp [singles, ha, hb, twice_binary]
      _ = _ := Finset.sum_ite_mem_eq (singles s C) (point s)
  rw [Prod.snd_sum, coordinate_sum]
  change ((if q (modulus s) ∈ C then 0 else 0) +
      (∑ i : PairIndex s, if a (modulus s) i ∈ C then point s i else 0)) +
    ((if p (modulus s) ∈ C then sentinel s hs else 0) +
      ∑ i : PairIndex s, if b (modulus s) i ∈ C then point s i else 0) = _
  simp only [ite_self, zero_add]
  calc
    _ = ((∑ i : PairIndex s, if a (modulus s) i ∈ C then point s i else 0) +
      (∑ i : PairIndex s, if b (modulus s) i ∈ C then point s i else 0)) +
      (if p (modulus s) ∈ C then sentinel s hs else 0) := by abel
    _ = _ := by rw [hab]

private lemma twice_s (s : ℕ) :
    ((2 * s : ℕ) : ZMod (modulus s)) = -1 := by
  have h := ZMod.natCast_self (modulus s)
  unfold modulus at h ⊢
  push_cast at h ⊢
  linear_combination h

private lemma sum_indicator_const {R : Type*} [Ring R]
    (s : ℕ) (T : Finset (PairIndex s)) (z : R) :
    (∑ i : PairIndex s, if i ∈ T then z else 0) = (T.card : R) * z := by
  rw [Finset.sum_ite_mem_eq T (fun _ => z)]
  simp only [Finset.sum_const, nsmul_eq_mul]

private lemma torsion_sum (s : ℕ) (hs : 1 ≤ s)
    (C : Finset (Coordinate (modulus s))) :
    (∑ x ∈ C, label s hs x).1 =
      (epsilon s C : ZMod (modulus s)) -
      (if p (modulus s) ∈ C then (1 : ZMod (modulus s)) else 0) +
      (s : ZMod (modulus s)) * ((singles s C).card : ZMod (modulus s)) -
      ((doubles s C).card : ZMod (modulus s)) := by
  have h2s : (s : ZMod (modulus s)) + s = -1 := by
    have h := twice_s s
    push_cast at h
    linear_combination h
  have hab :
      (∑ i : PairIndex s, if a (modulus s) i ∈ C then (s : ZMod (modulus s)) else 0) +
      (∑ i : PairIndex s, if b (modulus s) i ∈ C then (s : ZMod (modulus s)) else 0) =
      (s : ZMod (modulus s)) * ((singles s C).card : ZMod (modulus s)) -
        ((doubles s C).card : ZMod (modulus s)) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i : PairIndex s,
          ((if i ∈ singles s C then (s : ZMod (modulus s)) else 0) -
            (if i ∈ doubles s C then (1 : ZMod (modulus s)) else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases ha : a (modulus s) i ∈ C <;>
          by_cases hb : b (modulus s) i ∈ C <;>
          simp [singles, doubles, ha, hb, h2s]
      _ = _ := by
        rw [Finset.sum_sub_distrib, sum_indicator_const, sum_indicator_const]
        ring
  rw [Prod.fst_sum, coordinate_sum]
  change ((if q (modulus s) ∈ C then (1 : ZMod (modulus s)) else 0) +
      (∑ i : PairIndex s, if a (modulus s) i ∈ C then (s : ZMod (modulus s)) else 0)) +
    ((if p (modulus s) ∈ C then (-1 : ZMod (modulus s)) else 0) +
      ∑ i : PairIndex s, if b (modulus s) i ∈ C then (s : ZMod (modulus s)) else 0) = _
  by_cases hq : q (modulus s) ∈ C <;>
    by_cases hp : p (modulus s) ∈ C <;>
    simp [epsilon, hq, hp] <;>
    linear_combination hab

private lemma cast_small (s : ℕ) {x y : ℕ}
    (hx : x < modulus s) (hy : y < modulus s)
    (he : (x : ZMod (modulus s)) = (y : ZMod (modulus s))) : x = y := by
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] using hv

private lemma triple_nonempty_zero (s : ℕ) (hs : 1 ≤ s) (i : PairIndex s) :
    (triple (modulus s) i).Nonempty ∧
      (∑ x ∈ triple (modulus s) i, label s hs x) = 0 := by
  refine ⟨⟨q (modulus s), by simp [triple]⟩, ?_⟩
  have ht : (∑ x ∈ triple (modulus s) i, label s hs x) =
      label s hs (q (modulus s)) + label s hs (a (modulus s) i) +
        label s hs (b (modulus s) i) := by
    simp [triple, q, a, b, add_assoc]
  rw [ht]
  apply Prod.ext
  · change 1 + (s : ZMod (modulus s)) + s = 0
    have h := twice_s s
    push_cast at h
    linear_combination h
  · change 0 + point s i + point s i = 0
    simpa only [zero_add] using twice_binary s (point s i)

/-- Every original coordinate subset is classified, with no injectivity of labels. -/
private lemma zero_support_iff (s : ℕ) (hs : 1 ≤ s)
    (C : Finset (Coordinate (modulus s))) :
    (C.Nonempty ∧ (∑ x ∈ C, label s hs x) = 0) ↔
      ∃ i : PairIndex s, C = triple (modulus s) i := by
  constructor
  · rintro ⟨hC, hz⟩
    have heps := epsilon_le_one s C
    have hcount := singles_doubles_bound s C
    have hepslt : epsilon s C < modulus s := by unfold modulus; omega
    have hbin := congrArg (fun z : WitnessGroup s => z.2) hz
    change (∑ x ∈ C, label s hs x).2 = 0 at hbin
    rw [binary_sum] at hbin
    have htor := congrArg (fun z : WitnessGroup s => z.1) hz
    change (∑ x ∈ C, label s hs x).1 = 0 at htor
    rw [torsion_sum] at htor
    have hpar : ((singles s C).card : ZMod 2) = 0 := by
      have hf := congrArg (fun z : Binary s => z.1) hbin
      change (∑ i ∈ singles s C, point s i).1 +
        (if p (modulus s) ∈ C then sentinel s hs else 0).1 = 0 at hf
      rw [points_sum_first] at hf
      by_cases hp : p (modulus s) ∈ C <;> simpa [hp, sentinel] using hf
    obtain ⟨l, hl⟩ := ZMod.natCast_eq_zero_iff_even.mp hpar
    have hsc : (singles s C).card = 2 * l := by omega
    have hscale : (s : ZMod (modulus s)) *
        ((singles s C).card : ZMod (modulus s)) = -(l : ZMod (modulus s)) := by
      rw [hsc]
      have h2s := twice_s s
      push_cast at h2s ⊢
      linear_combination (l : ZMod (modulus s)) * h2s
    by_cases hp : p (modulus s) ∈ C
    · have hlpos : 0 < l := by
        by_contra hn
        have hlzero : l = 0 := by omega
        have hS : singles s C = ∅ := Finset.card_eq_zero.mp (by omega)
        have hP : sentinel s hs = 0 := by simpa [hp, hS] using hbin
        exact sentinel_nonzero s hs hP
      have hsmall : 1 + l + (doubles s C).card < modulus s := by
        unfold modulus
        omega
      have hcast : (((1 + l + (doubles s C).card : ℕ)) : ZMod (modulus s)) =
          (epsilon s C : ZMod (modulus s)) := by
        rw [hscale] at htor
        simp [hp] at htor
        push_cast
        linear_combination -htor
      have he := cast_small s hsmall hepslt hcast
      omega
    · have hTsum : (∑ i ∈ singles s C, point s i) = 0 := by
        simpa [hp] using hbin
      by_cases hS : singles s C = ∅
      · have hklt : (doubles s C).card < modulus s := by unfold modulus; omega
        have hcast : (epsilon s C : ZMod (modulus s)) =
            ((doubles s C).card : ZMod (modulus s)) := by
          apply sub_eq_zero.mp
          simpa [hp, hS] using htor
        have hk : (doubles s C).card = epsilon s C :=
          (cast_small s hepslt hklt hcast).symm
        have hbalance (i : PairIndex s) :
            a (modulus s) i ∈ C ↔ b (modulus s) i ∈ C := by
          have hi : i ∉ singles s C := by rw [hS]; simp
          by_cases ha : a (modulus s) i ∈ C <;>
            by_cases hb : b (modulus s) i ∈ C <;>
            simp [singles, ha, hb] at hi ⊢
        have hq : q (modulus s) ∈ C := by
          by_contra hq
          have hD : doubles s C = ∅ := Finset.card_eq_zero.mp (by
            simpa [epsilon, hq] using hk)
          have hnob (i : PairIndex s) : b (modulus s) i ∉ C := by
            intro hi
            have hd : i ∈ doubles s C := by
              simp [doubles, hi, (hbalance i).mpr hi]
            rw [hD] at hd
            exact Finset.notMem_empty i hd
          obtain ⟨x, hx⟩ := hC
          rcases x with (_ | i) | (_ | i)
          · exact hq hx
          · exact hnob i ((hbalance i).mp hx)
          · exact hp hx
          · exact hnob i hx
        have hkone : (doubles s C).card = 1 := by simpa [epsilon, hq] using hk
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hkone
        have hmem (j : PairIndex s) : b (modulus s) j ∈ C ↔ j = i := by
          have he : j ∈ doubles s C ↔ j = i := by
            simp only [hi, Finset.mem_singleton]
          have hd : j ∈ doubles s C ↔ b (modulus s) j ∈ C := by
            simp only [doubles, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · exact And.right
            · intro hb
              exact ⟨(hbalance j).mpr hb, hb⟩
          exact hd.symm.trans he
        refine ⟨i, ?_⟩
        ext x
        rcases x with (_ | j) | (_ | j)
        · change q (modulus s) ∈ C ↔ q (modulus s) ∈ triple (modulus s) i
          simp [triple, hq]
        · simpa [triple, q, a, b] using (hbalance j).trans (hmem j)
        · change p (modulus s) ∈ C ↔ p (modulus s) ∈ triple (modulus s) i
          have hpnot : p (modulus s) ∉ triple (modulus s) i := by
            simp [triple, q, p, a, b]
          simp only [hp, hpnot]
        · simpa [triple, q, a, b] using hmem j
      · have hpos : 0 < (singles s C).card := by
          by_contra hn
          have hc : (singles s C).card = 0 := by omega
          exact hS (Finset.card_eq_zero.mp hc)
        have hne := zero_sum_card_ne_two s (singles s C) hTsum
        have hlbig : 2 ≤ l := by omega
        have hsmall : l + (doubles s C).card < modulus s := by unfold modulus; omega
        have hcast : (((l + (doubles s C).card : ℕ)) : ZMod (modulus s)) =
            (epsilon s C : ZMod (modulus s)) := by
          rw [hscale] at htor
          simp [hp] at htor
          push_cast
          linear_combination -htor
        have he := cast_small s hsmall hepslt hcast
        omega
  · rintro ⟨i, rfl⟩
    exact triple_nonempty_zero s hs i

private lemma label_order (s : ℕ) (hs : 1 ≤ s) :
    addOrderOf (label s hs (q (modulus s))) = modulus s := by
  simp [label, q, Prod.addOrderOf_mk]

private lemma carrier_card (s : ℕ) :
    Nat.card (WitnessGroup s) = modulus s * 2 ^ (dimension s + 1) := by
  simp only [WitnessGroup, Binary, Vector, Nat.card_prod, Nat.card_fun,
    Nat.card_zmod, Nat.card_fin]
  rw [pow_succ]
  ring

private lemma carrier_quadratic (s : ℕ) (hs : 1 ≤ s) :
    Nat.card (WitnessGroup s) < 4 * modulus s * (modulus s - 1) := by
  rw [carrier_card]
  have hd := dimension_pos s hs
  have hpred : 2 ^ (dimension s).pred < 2 * s := by
    exact Nat.pow_pred_clog_lt_self (by decide) (by omega)
  have he : dimension s = (dimension s).pred + 1 := by
    simpa only [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hd).symm
  have hpow : 2 ^ dimension s < 4 * s := by
    calc
      2 ^ dimension s = 2 ^ ((dimension s).pred + 1) :=
        congrArg (fun n : ℕ => (2 : ℕ) ^ n) he
      _ = 2 ^ (dimension s).pred * 2 := pow_succ _ _
      _ < (2 * s) * 2 := Nat.mul_lt_mul_of_pos_right hpred (by decide)
      _ = 4 * s := by ring
  have hnext : 2 ^ (dimension s + 1) < 8 * s := by
    calc
      _ = 2 ^ dimension s * 2 := pow_succ _ _
      _ < (4 * s) * 2 := Nat.mul_lt_mul_of_pos_right hpow (by decide)
      _ = 8 * s := by ring
  have hm : 0 < modulus s := by unfold modulus; omega
  have hr : modulus s - 1 = 2 * s := by unfold modulus; omega
  calc
    modulus s * 2 ^ (dimension s + 1) < modulus s * (8 * s) :=
      Nat.mul_lt_mul_of_pos_left hnext hm
    _ = 4 * modulus s * (modulus s - 1) := by rw [hr]; ring

/-- For every odd m=2*s+1 at least three, an affine binary carrier has
the complete original triple family, and cardinality strictly below
4*m*(m-1).  The labels within each pair are equal. -/
theorem sharpness (s : ℕ) (hs : 1 ≤ s) :
    Finite (WitnessGroup s) ∧
    Nat.card (WitnessGroup s) = modulus s * 2 ^ (dimension s + 1) ∧
    Nat.card (WitnessGroup s) < 4 * modulus s * (modulus s - 1) ∧
    addOrderOf (label s hs (q (modulus s))) = modulus s ∧
    ¬ Function.Injective (label s hs) ∧
    (∀ C : Finset (Coordinate (modulus s)),
      (C.Nonempty ∧ (∑ x ∈ C, label s hs x) = 0) ↔
        ∃ i : PairIndex s, C = triple (modulus s) i) := by
  letI : NeZero (modulus s) := ⟨by unfold modulus; omega⟩
  refine ⟨inferInstance, carrier_card s, carrier_quadratic s hs,
    label_order s hs, ?_, zero_support_iff s hs⟩
  intro hinj
  let i : PairIndex s := ⟨0, by dsimp [Index, modulus]; omega⟩
  have he : a (modulus s) i = b (modulus s) i := hinj (show
    label s hs (a (modulus s) i) = label s hs (b (modulus s) i) from rfl)
  simpa [a, b] using he

end D5.S3.Combinatorics.Sequenceability.OriginalAffineBinarySharpness
