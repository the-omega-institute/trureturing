/- GID: D5/S1/Words/ParryNormalPrefix
   generality: G
   mirror-B: D5/B/S1/Words/ParryNormalPrefix
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Ordered greedy reconstruction of proper image prefixes under image-length dominance. -/
import D5.S1.Words.Powers.WordPower
import D5.S1.Words.RankOneMorphismIterationBoundDefs
import Mathlib.Data.List.TakeDrop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.ParryNormalPrefix

open RankOneMorphismIterationBound (subst image image_add)

/-- Concatenation power of a finite word, including the empty zeroth power. -/
def wordPower {α : Type*} (w : List α) (d : ℕ) : List α :=
  Powers.wordPower d w

/-- Ordered blocks selected by exactly `count` greedy quotient/remainder steps.
The largest image exponent is `count - 1`; zero digits are retained as empty blocks. -/
def greedyBlocks {α : Type*} (f : α → List α) (z : α) : ℕ → ℕ → List α
  | 0, _ => []
  | k + 1, n => wordPower (image f k z) (n / (image f k z).length) ++
      greedyBlocks f z k (n % (image f k z).length)

private theorem power_length {α : Type*} (w : List α) (d : ℕ) :
    (wordPower w d).length = d * w.length := by
  exact Powers.length_wordPower d w

private theorem take_power_tail {α : Type*} (w t : List α) (d n : ℕ)
    (hw : 0 < w.length) (ht : t.length ≤ w.length)
    (hn : n < (wordPower w d ++ t).length) :
    (wordPower w d ++ t).take n = wordPower w (n / w.length) ++
      (if n / w.length < d then w else t).take (n % w.length) := by
  induction d generalizing n with
  | zero =>
      have hnt : n < t.length := by simpa [wordPower, Powers.wordPower_zero] using hn
      have hnw : n < w.length := lt_of_lt_of_le hnt ht
      simp [wordPower, Powers.wordPower_zero, Nat.div_eq_of_lt hnw, Nat.mod_eq_of_lt hnw]
  | succ d ih =>
      by_cases hsmall : n < w.length
      · simp [wordPower, Powers.wordPower_succ, List.take_append,
          Nat.div_eq_of_lt hsmall, Nat.mod_eq_of_lt hsmall,
          Nat.sub_eq_zero_of_le (Nat.le_of_lt hsmall)]
      · have hle : w.length ≤ n := by omega
        obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hle
        have hr : r < (wordPower w d ++ t).length := by
          simpa [wordPower, Powers.wordPower_succ, List.length_append] using hn
        rw [show wordPower w (d+1) ++ t = w ++ (wordPower w d ++ t) by
          simp [wordPower, Powers.wordPower_succ, List.append_assoc]]
        rw [List.take_append, List.take_of_length_le (by omega : w.length ≤ w.length+r)]
        simp only [Nat.add_sub_cancel_left]
        rw [ih r hr, Nat.add_div_left _ hw, Nat.add_mod_left]
        simp [wordPower, Powers.wordPower_succ, List.append_assoc]

private theorem image_shape {α : Type*} (f : α → List α) (z : α)
    (digit : α → ℕ) (next : α → Option α)
    (hshape : ∀ a, f a = List.replicate (digit a) z ++ (next a).toList)
    (k : ℕ) (a : α) :
    image f (k+1) a = wordPower (image f k z) (digit a) ++
      subst (image f k) (next a).toList := by
  rw [image_add f k 1]
  simp only [RankOneMorphismIterationBound.image_one, hshape, subst,
    List.flatMap_append, List.flatMap_replicate, wordPower, Powers.wordPower]

/-- Every proper prefix of every actual iterate has the same ordered greedy
block description. The substitution may terminate or return to a cyclic state.
Image-length dominance is an explicit hypothesis, not a reconstruction premise. -/
theorem greedy_remainder_prefix {α : Type*} (f : α → List α) (z : α)
    (digit : α → ℕ) (next : α → Option α)
    (hshape : ∀ a, f a = List.replicate (digit a) z ++ (next a).toList)
    (hpositive : ∀ k, 0 < (image f k z).length)
    (hdominant : ∀ k a, (image f k a).length ≤ (image f k z).length)
    (k : ℕ) (a : α) (n : ℕ) (hn : n < (image f k a).length) :
    (image f k a).take n = greedyBlocks f z k n := by
  induction k generalizing a n with
  | zero =>
      have hn0 : n = 0 := by simpa [image] using hn
      subst n; simp [greedyBlocks]
  | succ k ih =>
      let w := image f k z
      let t := subst (image f k) (next a).toList
      have ht : t.length ≤ w.length := by
        cases he : next a with
        | none => simp [t, he, subst]
        | some b => simpa [t, he, subst, w] using hdominant k b
      have hs := image_shape f z digit next hshape k a
      have hn' : n < (wordPower w (digit a) ++ t).length := by
        rw [hs] at hn
        exact hn
      have hc := take_power_tail w t (digit a) n (hpositive k) ht hn'
      rw [hs, hc]
      simp only [greedyBlocks]
      congr 1
      split_ifs with hq
      · exact ih z (n % w.length) (Nat.mod_lt _ (hpositive k))
      · cases he : next a with
        | none =>
            have hlen : n < digit a * w.length := by
              simpa only [t, he, Option.toList_none, subst, List.flatMap_nil,
                List.length_append, List.length_nil, Nat.add_zero, power_length] using hn'
            have hdiv : n / w.length < digit a := (Nat.div_lt_iff_lt_mul (hpositive k)).mpr
              (by simpa [Nat.mul_comm] using hlen)
            exact (hq hdiv).elim
        | some b =>
            have hlen : n < digit a * w.length + (image f k b).length := by
              simpa only [t, he, List.length_append, power_length, Option.toList_some,
                subst, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hn'
            have hrem := Nat.mod_add_div n w.length
            have hmul : digit a * w.length ≤ (n / w.length) * w.length :=
              Nat.mul_le_mul_right _ (by omega)
            have hr : n % w.length < (image f k b).length := by
              rw [Nat.mul_comm w.length] at hrem
              omega
            simpa [t, he, subst] using ih b (n % w.length) hr

/-- Every finite successor-digit window is lexicographically bounded by the root
window: either all digits agree, or the first differing digit is smaller. -/
def SuccessorDominated {α : Type*} (c : α → ℕ) (s : α → α) (z : α) : Prop :=
  ∀ a k, (∀ i, i < k → c ((s^[i]) a) = c ((s^[i]) z)) ∨
    ∃ q, q < k ∧ (∀ i, i < q → c ((s^[i]) a) = c ((s^[i]) z)) ∧
      c ((s^[q]) a) < c ((s^[q]) z)

private theorem successor_length {α : Type*} (f : α → List α) (z : α)
    (c : α → ℕ) (s : α → α)
    (hf : ∀ a, f a = List.replicate (c a) z ++ [s a]) (k : ℕ) (a : α) :
    (image f (k+1) a).length = c a * (image f k z).length +
      (image f k (s a)).length := by
  rw [image_shape f z c (fun a => some (s a)) hf k a]
  simp [power_length, subst]

private theorem successor_positive {α : Type*} (f : α → List α) (z : α)
    (c : α → ℕ) (s : α → α)
    (hf : ∀ a, f a = List.replicate (c a) z ++ [s a]) (k : ℕ) (a : α) :
    0 < (image f k a).length := by
  induction k generalizing a with
  | zero => simp [image]
  | succ k ih => rw [successor_length f z c s hf]; have := ih (s a); omega

private theorem prefix_length_balance {α : Type*} (f : α → List α) (z : α)
    (c : α → ℕ) (s : α → α)
    (hf : ∀ a, f a = List.replicate (c a) z ++ [s a])
    (k q : ℕ) (a b : α)
    (he : ∀ i, i < q → c ((s^[i]) a) = c ((s^[i]) b)) :
    (image f (k+q) a).length + (image f k ((s^[q]) b)).length =
      (image f (k+q) b).length + (image f k ((s^[q]) a)).length := by
  induction q generalizing a b with
  | zero => simp [Nat.add_comm]
  | succ q ih =>
      have hab : c a = c b := by simpa using he 0 (by omega)
      have ht : ∀ i, i < q → c ((s^[i]) (s a)) = c ((s^[i]) (s b)) := by
        intro i hi
        simpa only [Function.iterate_succ_apply] using he (i+1) (by omega)
      have hh := ih (s a) (s b) ht
      rw [Nat.add_succ, successor_length f z c s hf,
        successor_length f z c s hf, hab]
      simp only [Function.iterate_succ_apply]
      omega

private theorem successor_dominance {α : Type*} (f : α → List α) (z : α)
    (c : α → ℕ) (s : α → α)
    (hf : ∀ a, f a = List.replicate (c a) z ++ [s a])
    (hd : SuccessorDominated c s z) (k : ℕ) (a : α) :
    (image f k a).length ≤ (image f k z).length := by
  induction k using Nat.strong_induction_on generalizing a with
  | h k ih =>
      obtain he | ⟨q, hq, he, hlt⟩ := hd a k
      · have hb := prefix_length_balance f z c s hf 0 k a z he
        simpa [image] using Nat.le_of_eq hb
      · have hb := prefix_length_balance f z c s hf (k-q) q a z he
        have hk : k = (k-q-1)+1+q := by omega
        have hsmall : k-q-1 < k := by omega
        have hbound := ih (k-q-1) hsmall (s ((s^[q]) a))
        have hp := successor_positive f z c s hf (k-q-1) ((s^[q]) z)
        have htail := successor_positive f z c s hf (k-q-1) (s ((s^[q]) z))
        have hm : (c ((s^[q]) a)+1) * (image f (k-q-1) z).length ≤
            c ((s^[q]) z) * (image f (k-q-1) z).length :=
          Nat.mul_le_mul_right _ hlt
        have ht : (image f (k-q) ((s^[q]) a)).length <
            (image f (k-q) ((s^[q]) z)).length := by
          rw [show k-q = (k-q-1)+1 by omega,
            successor_length f z c s hf, successor_length f z c s hf]
          rw [Nat.add_mul] at hm
          omega
        rw [show k-q+q = k by omega] at hb
        omega

/-- Lexicographic dominance of the actual successor-digit streams earns
image-length dominance, and hence the exact ordered greedy reconstruction. -/
theorem greedy_prefix_of_successor_dominance {α : Type*} (f : α → List α) (z : α)
    (c : α → ℕ) (s : α → α)
    (hf : ∀ a, f a = List.replicate (c a) z ++ [s a])
    (hd : SuccessorDominated c s z) (k : ℕ) (a : α) (n : ℕ)
    (hn : n < (image f k a).length) :
    (image f k a).take n = greedyBlocks f z k n := by
  exact greedy_remainder_prefix f z c (fun a => some (s a)) hf
    (fun j => successor_positive f z c s hf j z)
    (successor_dominance f z c s hf hd) k a n hn

#print axioms greedy_prefix_of_successor_dominance
#print axioms greedy_remainder_prefix

end D5.S1.Words.ParryNormalPrefix
