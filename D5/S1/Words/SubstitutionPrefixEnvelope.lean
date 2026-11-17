/- GID: D5/S1/Words/SubstitutionPrefixEnvelope
   generality: G
   mirror-B: D5/B/S1/Words/SubstitutionPrefixEnvelope
   mirror-E: none(waiver:integer-word-estimates)
   anchors: []
   utility: none
   digest: Block charges control all recursive prefixes and two-block intervals. -/
import D5.S1.Words.RankOneMorphismIterationBoundDefs
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-! Alternating concatenation and recursive prefix estimates. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.SubstitutionPrefixEnvelope

open RankOneMorphismIterationBound (subst image image_add)
open scoped BigOperators

/-- Alternation starts positively at the beginning of the supplied list. -/
def charge {α : Type*} (w : α → ℤ) (v : List α) : ℤ := (v.map w).alternatingSum

private theorem charge_append {α : Type*} (w : α → ℤ) (u v : List α) :
    charge w (u ++ v) = charge w u + (-1 : ℤ)^u.length * charge w v := by
  simp [charge, List.alternatingSum_append]

private theorem abs_charge_append {α : Type*} (w : α → ℤ) (u v : List α) :
    |charge w (u ++ v)| ≤ |charge w u| + |charge w v| := by
  rw [charge_append]
  simpa [abs_mul] using abs_add_le (charge w u) ((-1 : ℤ)^u.length * charge w v)

private theorem abs_charge_right {α : Type*} (w : α → ℤ) (u v : List α) :
    |charge w v| ≤ |charge w (u ++ v)| + |charge w u| := by
  have he : |charge w v| = |charge w (u ++ v) - charge w u| := by
    rw [charge_append, add_sub_cancel_left, abs_mul, abs_neg_one_pow, one_mul]
  rw [he]
  exact abs_sub (charge w (u ++ v)) (charge w u)

private theorem flatMap_charge {α : Type*} (w : α → ℤ) (g : α → List α)
    (H : ℤ) (hg : ∀ a, |charge w (g a)| ≤ H) (l : List α) :
    |charge w (l.flatMap g)| ≤ (l.length : ℤ) * H := by
  induction l with
  | nil => simp [charge]
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have ha := abs_charge_append w (g a) (l.flatMap g)
    have hb := hg a
    nlinarith

private theorem flatMap_prefix {α : Type*} (w : α → ℤ) (g : α → List α)
    (H P : ℤ) (hH : 0 ≤ H) (hP : 0 ≤ P)
    (hg : ∀ a, |charge w (g a)| ≤ H)
    (hp : ∀ a t, |charge w ((g a).take t)| ≤ P) (l : List α) (t : ℕ) :
    |charge w ((l.flatMap g).take t)| ≤ (l.length : ℤ) * H + P := by
  induction l generalizing t with
  | nil => simpa [charge] using hP
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    by_cases ht : t ≤ (g a).length
    · rw [List.take_append_of_le_length ht]
      have ha := hp a t
      have hl : 0 ≤ (l.length : ℤ) * H := mul_nonneg (by positivity) hH
      nlinarith
    · rw [List.take_append, List.take_of_length_le (by omega)]
      have ha := abs_charge_append w (g a) ((l.flatMap g).take (t - (g a).length))
      have hb := hg a
      have hc := ih (t - (g a).length)
      nlinarith

/-- A complete-block bound at every level gives a bound for every prefix,
including empty prefixes and take indices beyond the end of the image. -/
theorem prefix_envelope {α : Type*} (w : α → ℤ) (f : α → List α)
    (M : ℤ) (B : ℕ) (H : ℕ → ℤ) (hM : 0 ≤ M)
    (hw : ∀ a, |w a| ≤ M) (hf : ∀ a, (f a).length ≤ B)
    (hH : ∀ j, 0 ≤ H j) (hb : ∀ j a, |charge w (image f j a)| ≤ H j) :
    ∀ j a t, |charge w ((image f j a).take t)| ≤
      M + (B : ℤ) * ∑ i ∈ Finset.range j, H i := by
  intro j
  induction j with
  | zero =>
    intro a t
    cases t with
    | zero => simpa [charge] using hM
    | succ t => simpa [image, charge] using hw a
  | succ j ih =>
    intro a t
    have hP : 0 ≤ M + (B : ℤ) * ∑ i ∈ Finset.range j, H i :=
      add_nonneg hM (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => hH i))
    have hh := flatMap_prefix w (image f j) (H j)
      (M + (B : ℤ) * ∑ i ∈ Finset.range j, H i) (hH j) hP (hb j) (ih) (f a) t
    have hl : ((f a).length : ℤ) * H j ≤ (B : ℤ) * H j :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hf a) (hH j)
    rw [image_add]
    simp only [image, subst, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [Finset.sum_range_succ]
    change |charge w (((f a).flatMap (image f j)).take t)| ≤ _
    nlinarith

private theorem infix_charge {α : Type*} (w : α → ℤ) (l v : List α) (P : ℤ)
    (hp : ∀ t, |charge w (l.take t)| ≤ P) (hv : v <:+: l) :
    |charge w v| ≤ 2 * P := by
  obtain ⟨pre, post, rfl⟩ := hv
  have hpre := hp pre.length
  have hboth := hp (pre ++ v).length
  have htakepre : (pre ++ v ++ post).take pre.length = pre := by
    simp [List.append_assoc]
  rw [htakepre] at hpre
  have htake : (pre ++ v ++ post).take (pre ++ v).length = pre ++ v := List.take_left
  rw [htake] at hboth
  have hh := abs_charge_right w pre v
  omega

/-- Any actual infix of two level-j images has at most four times
the prefix envelope, without parity assumptions on any image length. -/
theorem two_block_interval_bound {α : Type*} (w : α → ℤ) (f : α → List α)
    (M : ℤ) (B : ℕ) (H : ℕ → ℤ) (hM : 0 ≤ M)
    (hw : ∀ a, |w a| ≤ M) (hf : ∀ a, (f a).length ≤ B)
    (hH : ∀ j, 0 ≤ H j) (hb : ∀ j a, |charge w (image f j a)| ≤ H j)
    (j : ℕ) (a b : α) (v : List α) (hv : v <:+: image f j a ++ image f j b) :
    |charge w v| ≤ 4 * (M + (B : ℤ) * ∑ i ∈ Finset.range j, H i) := by
  have hp := prefix_envelope w f M B H hM hw hf hH hb j
  have hh := infix_charge w (image f j a ++ image f j b) v
    (2 * (M + (B : ℤ) * ∑ i ∈ Finset.range j, H i)) (by
      intro t
      rw [List.take_append]
      have h := abs_charge_append w ((image f j a).take t)
        ((image f j b).take (t - (image f j a).length))
      have h₁ := hp a t
      have h₂ := hp b (t - (image f j a).length)
      omega) hv
  omega

end D5.S1.Words.SubstitutionPrefixEnvelope
