/- GID: D5/S3/Arith/FibonacciAtomic/LocalWiring/BoundedBinaryRecurrence
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LocalWiring/BoundedBinaryRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Defs, mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Sigma]
   utility: none
   digest: Exact finite separation and executable first-match synthesis for bounded binary recurrences. -/

import D5.S3.Arith.FibonacciAtomic.LocalWiring.PublicRowSeedReadiness
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Init.Data.BitVec.Lemmas

/-! For a genuine bounded-order forward binary recurrence, an authentic finite prefix
suffices to compute every later output, without identifying private coefficients. -/

namespace D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrence

open scoped BigOperators
open PublicRowSeedReadiness (bitNat rowStream seedFromPrefix public_row_seed_readiness)

section Separation

variable {A : Type*} [CommRing A] {r s : ℕ}

/-- The monic constant-coefficient shift annihilator specified by the lower coefficients. -/
private def ann (c : Fin r → A) (x : ℕ → A) (i : ℕ) : A :=
  x (i + r) - ∑ j, c j * x (i + j.val)

private theorem swap_middle (a b c d : A) : a + b + (d + c) = a + c + (d + b) := by
  calc
    _ = a + (b + (c + d)) := by rw [add_assoc, add_comm d c]
    _ = a + (c + (b + d)) := by rw [add_left_comm b c]
    _ = _ := by rw [add_assoc, add_comm d b]

private theorem ann_sub (c : Fin r → A) (x y : ℕ → A) (i : ℕ) :
    ann c (fun n => x n - y n) i = ann c x i - ann c y i := by
  simp only [ann, sub_eq_add_neg, mul_add, mul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, neg_add_rev, neg_neg]
  apply swap_middle

private theorem ann_zero (c : Fin r → A) (i : ℕ) : ann c (fun _ => 0) i = 0 := by
  simp [ann]

private theorem ann_commute (c : Fin r → A) (b : Fin s → A) (x : ℕ → A) (i : ℕ) :
    ann c (ann b x) i = ann b (ann c x) i := by
  have htop : i + r + s = i + s + r := by omega
  have hleft (j : Fin r) : i + j.val + s = i + s + j.val := by omega
  have hright (k : Fin s) : i + k.val + r = i + r + k.val := by omega
  have hdouble :
      (∑ j, ∑ k, c j * (b k * x (i + j.val + k.val))) =
        ∑ k, ∑ j, b k * (c j * x (i + k.val + j.val)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    have h : i + j.val + k.val = i + k.val + j.val := by omega
    rw [h]
    ac_rfl
  simp only [ann, sub_eq_add_neg, mul_add, mul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, neg_add_rev, neg_neg, Finset.mul_sum]
  rw [htop, hdouble]
  simp only [hleft, hright]
  apply swap_middle

private theorem ann_ann_sub_eq_zero (c : Fin r → A) (b : Fin s → A) (x y : ℕ → A)
    (hx : ∀ i, ann c x i = 0) (hy : ∀ i, ann b y i = 0) (i : ℕ) :
    ann c (ann b (fun n => x n - y n)) i = 0 := by
  have hxy : ann b (fun n => x n - y n) = fun n => ann b x n - ann b y n :=
    funext (ann_sub b x y)
  rw [hxy, ann_sub, ann_commute c b x]
  simp only [show ann c x = (fun _ => 0) from funext hx,
    show ann b y = (fun _ => 0) from funext hy, ann_zero, sub_zero]

/-- Two monic recurrences of orders `r` and `s` agree everywhere if their first `r+s`
values agree. The zero orders are allowed. -/
private theorem stream_eq_of_ann_eq_zero (c : Fin r → A) (b : Fin s → A) (x y : ℕ → A)
    (hx : ∀ i, ann c x i = 0) (hy : ∀ i, ann b y i = 0)
    (h : ∀ i < r + s, x i = y i) : ∀ i, x i = y i := by
  let z := fun i => x i - y i
  have hz (i : ℕ) : ann c (ann b z) i = 0 := ann_ann_sub_eq_zero c b x y hx hy i
  have zzero (i : ℕ) : z i = 0 := by
    induction i using Nat.strongRecOn with
    | ind i ih =>
      by_cases hi : i < r + s
      · exact sub_eq_zero.mpr (h i hi)
      let k := i - (r+s)
      have htop : k + r + s = i := by dsimp [k]; omega
      have hfirst : (∑ l, b l * z (k + r + l.val)) = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        rw [ih _ (by have := l.isLt; omega), mul_zero]
      have hsecond : (∑ j, c j * ann b z (k + j.val)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have hj := j.isLt
        rw [ann, ih _ (by omega)]
        have hinner : (∑ l, b l * z (k + j.val + l.val)) = 0 := by
          apply Finset.sum_eq_zero
          intro l _
          rw [ih _ (by have := l.isLt; omega), mul_zero]
        rw [hinner, sub_self, mul_zero]
      have he := hz k
      change z (k + r + s) - (∑ l, b l * z (k + r + l.val)) -
        (∑ j, c j * ann b z (k + j.val)) = 0 at he
      simpa only [htop, hfirst, hsecond, sub_zero] using he
  exact fun i => sub_eq_zero.mp (zzero i)

end Separation

/-- Address bit zero is the least significant bit of the mask. -/
private def maskBits {d : Nat} (m : Fin (2 ^ d)) (i : Fin d) : Bool :=
  (BitVec.ofFin m).getLsbD i.val

private def pack : (d : Nat) → (Fin d → Bool) → BitVec d
  | 0, _ => 0#0
  | d + 1, f => (pack d (fun j => f j.succ)).concat (f 0)

/-- The natural mask representing these coefficients in least-significant-first order. -/
private def encodeMask {d : Nat} (f : Fin d → Bool) : Fin (2 ^ d) := (pack d f).toFin

private theorem maskBits_encodeMask {d : Nat} (f : Fin d → Bool) (i : Fin d) :
    maskBits (encodeMask f) i = f i := by
  induction d with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact BitVec.getLsbD_concat_zero
    · change ((pack d (fun j => f j.succ)).concat (f 0)).getLsbD (j.val + 1) =
        f j.succ
      rw [BitVec.getLsbD_concat_succ]
      exact ih (fun j => f j.succ) j

/-- Enumerate from numeric mask zero through mask `2 ^ d - 1`, inclusive. -/
def masks (d : Nat) : List (Fin d → Bool) := (List.finRange (2 ^ d)).map maskBits

private theorem mem_masks {d : Nat} (f : Fin d → Bool) : f ∈ masks d :=
  List.mem_map.mpr ⟨encodeMask f, List.mem_finRange _, funext (maskBits_encodeMask f)⟩

private theorem length_masks (d : Nat) : (masks d).length = 2 ^ d := by
  rw [masks, List.length_map, List.length_finRange]

private theorem maskBits_injective {d : Nat} {m n : Fin (2 ^ d)}
    (h : maskBits m = maskBits n) : m = n := by
  have he : BitVec.ofFin m = BitVec.ofFin n :=
    BitVec.eq_of_getLsbD_eq_iff.mpr (fun i hi => congrFun h ⟨i, hi⟩)
  exact congrArg BitVec.toFin he

/-- Prepend zero taps without changing the terminal index of a prediction. -/
private def pad {r d : Nat} (hr : r ≤ d) (c : Fin r → Bool) (j : Fin d) : Bool :=
  Fin.addCases (fun _ : Fin (d-r) => false) c
    (Fin.cast (by omega : d = (d-r)+r) j)

private theorem pad_law {r d : Nat} (hr : r ≤ d) (c : Fin r → Bool) (z : Nat → Bool)
    (h : ∀ i : Nat, bitNat (z (i+r)) =
      (∑ j : Fin r, bitNat (c j) * bitNat (z (i+j.val))) % 2) :
    ∀ i : Nat, bitNat (z (i+d)) =
      (∑ j : Fin d, bitNat (pad hr c j) * bitNat (z (i+j.val))) % 2 := by
  intro i
  have hd : (d-r)+r = d := by omega
  have hs :
      (∑ j : Fin d, bitNat (pad hr c j) * bitNat (z (i+j.val))) =
      ∑ j : Fin ((d-r)+r),
        bitNat (Fin.addCases (fun _ : Fin (d-r) => false) c j) *
          bitNat (z (i+j.val)) := by
    apply Fintype.sum_equiv (finCongr hd.symm)
    intro j
    rfl
  rw [hs, Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Fin.val_natAdd, bitNat,
    Bool.false_eq_true, ite_false, Nat.zero_mul, Finset.sum_const_zero, Nat.zero_add,
    ← Nat.add_assoc]
  have hi := h (i+(d-r))
  rw [Nat.add_assoc, hd] at hi
  exact hi

/-- Literal all-index binary recurrence, presented with finite ordinary sums modulo two. -/
def Recurrence {r : Nat} (c : Fin r → Bool) (s : Nat → Bool) : Prop :=
  ∀ i : Nat, bitNat (s (i+r)) =
    (∑ j : Fin r, bitNat (c j) * bitNat (s (i+j.val))) % 2

/-- A legal stream has some order at most the public bound, with no minimality condition. -/
def Legal (d : Nat) (s : Nat → Bool) : Prop :=
  ∃ r : Nat, r ≤ d ∧ ∃ c : Fin r → Bool, Recurrence c s

/-- First n bits in emission order, starting with index zero. -/
def observed (n : Nat) (s : Nat → Bool) : List Bool :=
  List.ofFn (fun j : Fin n => s j.val)

private theorem observed_iff (n : Nat) (s t : Nat → Bool) :
    observed n s = observed n t ↔ ∀ i < n, s i = t i := by
  rw [observed, observed, List.ofFn_inj]
  exact ⟨fun h i hi => congrFun h ⟨i, hi⟩, fun h => funext fun j => h j j.isLt⟩

private theorem bitNat_injective : Function.Injective bitNat := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitNat]

private def fieldBit (b : Bool) : ZMod 2 := (bitNat b : ZMod 2)

private theorem fieldBit_injective : Function.Injective fieldBit := by
  intro a b h
  cases a <;> cases b
  · rfl
  · change (0 : ZMod 2) = 1 at h
    exact ((by decide : (0 : ZMod 2) ≠ 1) h).elim
  · change (1 : ZMod 2) = 0 at h
    exact ((by decide : (1 : ZMod 2) ≠ 0) h).elim
  · rfl

open Fin.NatCast in
private theorem cast_mod_two (n : Nat) : ((n % 2 : Nat) : ZMod 2) = (n : ZMod 2) := by
  apply Fin.ext
  change (Nat.cast (R := Fin 2) (n % 2)).val = (Nat.cast (R := Fin 2) n).val
  rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_mod]

private theorem field_annihilates {r : Nat} (c : Fin r → Bool) (s : Nat → Bool)
    (h : Recurrence c s) :
    ∀ i, ann (fieldBit ∘ c) (fieldBit ∘ s) i = 0 := by
  intro i
  apply sub_eq_zero.mpr
  change (bitNat (s (i+r)) : ZMod 2) = ∑ j : Fin r,
    (bitNat (c j) : ZMod 2) * (bitNat (s (i+j.val)) : ZMod 2)
  rw [h i, cast_mod_two, Nat.cast_sum]
  simp only [Nat.cast_mul]

private theorem separation (d : Nat) {s t : Nat → Bool} (hs : Legal d s) (ht : Legal d t)
    (he : observed (2*d) s = observed (2*d) t) : ∀ i, s i = t i := by
  obtain ⟨r, hr, c, hc⟩ := hs
  obtain ⟨r', hr', c', hc'⟩ := ht
  intro k
  apply fieldBit_injective
  exact stream_eq_of_ann_eq_zero (fieldBit ∘ c) (fieldBit ∘ c') (fieldBit ∘ s) (fieldBit ∘ t)
    (field_annihilates c s hc) (field_annihilates c' t hc')
    (fun i hi => congrArg fieldBit ((observed_iff _ s t).mp he i (by omega))) k

private theorem same_recurrence {r : Nat} (c : Fin r → Bool) {s t : Nat → Bool}
    (hs : Recurrence c s) (ht : Recurrence c t) (h : ∀ i < r, s i = t i) :
    ∀ i, s i = t i := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk : k < r
    · exact h k hk
    · let i := k-r
      have e : i+r = k := by dsimp [i]; omega
      apply bitNat_injective
      rw [← e, hs i, ht i]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [ih _ (by have := j.isLt; dsimp [i]; omega)]

private theorem candidate_initial {d : Nat} (c seed : Fin d → Bool) (j : Fin d) :
    rowStream c seed j.val = seed j :=
  (public_row_seed_readiness d c seed 2 (by decide)).2.2.2.2.2.2.1 j

private theorem candidate_recurrence {d : Nat} (c seed : Fin d → Bool) :
    Recurrence c (rowStream c seed) :=
  (public_row_seed_readiness d c seed 2 (by decide)).2.2.2.2.2.2.2.2.1

private theorem seed_observed {d : Nat} (s : Nat → Bool) (j : Fin d) :
    seedFromPrefix (observed (2*d) s) j = s j.val := by
  have hj : j.val < 2*d := by have := j.isLt; omega
  rw [seedFromPrefix, observed, List.getElem?_ofFn, dite_eq_left hj, Option.getD_some]

/-- The first coefficient row whose generated first 2d bits match the observed word. -/
def synthesize (d : Nat) (word : List Bool) : Option (Fin d → Bool) :=
  (masks d).find? (fun c => observed (2*d) (rowStream c (seedFromPrefix word)) == word)

/-- Output of the actual selected generator at any zero-based index. -/
def generated (d : Nat) (word : List Bool) (i : Nat) : Option Bool :=
  (synthesize d word).map (fun c => rowStream c (seedFromPrefix word) i)

private theorem matching_exists (d : Nat) (s : Nat → Bool) (hs : Legal d s)
    (word : List Bool) (hw : word = observed (2*d) s) :
    ∃ c, synthesize d word = some c := by
  obtain ⟨r, hr, c, hc⟩ := hs
  let b := pad hr c
  have hb : Recurrence b s := pad_law hr c s hc
  have he : ∀ i, rowStream b (seedFromPrefix word) i = s i :=
    same_recurrence b (candidate_recurrence _ _) hb (fun i hi => by
      rw [candidate_initial b _ ⟨i, hi⟩, hw]
      exact seed_observed s ⟨i, hi⟩)
  have hm : (observed (2*d) (rowStream b (seedFromPrefix word)) == word) = true := by
    rw [beq_iff_eq, hw]
    exact (observed_iff _ _ _).mpr fun i _ => by simpa only [← hw] using he i
  cases h : synthesize d word with
  | none => exact ((List.find?_eq_none.mp h) _ (mem_masks b) hm).elim
  | some c => exact ⟨c, rfl⟩

private theorem matching_correct (d : Nat) (s : Nat → Bool) (hs : Legal d s)
    (word : List Bool) (hw : word = observed (2*d) s) {c : Fin d → Bool}
    (h : synthesize d word = some c) : ∀ i, rowStream c (seedFromPrefix word) i = s i := by
  have hm := List.find?_some h
  apply separation d ⟨d, Nat.le_refl _, c, candidate_recurrence _ _⟩ hs
  exact (beq_iff_eq.mp hm).trans hw

private theorem first_match {d : Nat} {word : List Bool} {c : Fin d → Bool}
    (h : synthesize d word = some c) :
    ∃ earlier later, masks d = earlier ++ c :: later ∧ ∀ b ∈ earlier,
      observed (2*d) (rowStream b (seedFromPrefix word)) ≠ word := by
  obtain ⟨_, earlier, later, he, hb⟩ := List.find?_eq_some_iff_append.mp h
  exact ⟨earlier, later, he, fun b hm hc => by
    have hh := hb b hm
    simp [hc] at hh⟩

/-- The exact sufficient prefix length and concrete bounded binary first-match synthesis. -/
theorem bounded_binary_recurrence (d : Nat) :
    (∀ (word : List Bool) (i : Nat) (s : Nat → Bool), Legal d s →
      word = observed (2*d) s → generated d word i = some (s i)) ∧
    (∀ s t : Nat → Bool, Legal d s → Legal d t →
      observed (2*d) s = observed (2*d) t → ∀ i, s i = t i) ∧
    (∀ (word : List Bool) (s : Nat → Bool), Legal d s → word = observed (2*d) s →
      ∃ c, synthesize d word = some c ∧ (∀ i, rowStream c (seedFromPrefix word) i = s i) ∧
        ∃ earlier later, masks d = earlier ++ c :: later ∧ ∀ b ∈ earlier,
          observed (2*d) (rowStream b (seedFromPrefix word)) ≠ word) ∧
    (masks d).length = 2^d ∧
    (d = 0 → ∀ i, generated d [] i = some false) := by
  refine ⟨?_, ?_, ?_, length_masks d, ?_⟩
  · intro word i s hs hw
    obtain ⟨c, hc⟩ := matching_exists d s hs word hw
    rw [generated, hc, Option.map_some, matching_correct d s hs word hw hc i]
  · intro s t hs ht he
    exact separation d hs ht he
  · intro word s hs hw
    obtain ⟨c, hc⟩ := matching_exists d s hs word hw
    exact ⟨c, hc, matching_correct d s hs word hw hc, first_match hc⟩
  · rintro rfl i
    have h0 : Legal 0 (fun _ => false) :=
      ⟨0, Nat.le_refl _, Fin.elim0, by intro j; simp [bitNat]⟩
    obtain ⟨c, hc⟩ := matching_exists 0 (fun _ => false) h0 [] rfl
    rw [generated, hc, Option.map_some, matching_correct 0 (fun _ => false) h0 [] rfl hc i]

#print axioms bounded_binary_recurrence

end D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrence
