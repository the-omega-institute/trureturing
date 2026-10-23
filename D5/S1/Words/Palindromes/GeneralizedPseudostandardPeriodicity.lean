/- GID: D5/S1/Words/Palindromes/GeneralizedPseudostandardPeriodicity
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/GeneralizedPseudostandardPeriodicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Generalized pseudostandard words and involutory reflection structure. -/

/-
admission_basis: open-problem-resolution (#15626; Proved)
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15921
Fixed-point equations and finite prefixes reuse Function.IsFixedPt and List.ofFn.
The letter equivalence uses Function.Involutive.toPerm.
The settling result uses normalization and the two directive-tail implications.
Declaration: TailConditions; proof_shape: bind-only; escape_witness: none
  consumers: Generates.tail_necessary, TailConditions.adjacent_product, TailConditions.conjugation, TailConditions.gap, TailConditions.perm_iterate, TailConditions.perm_next, TailConditions.perm_periodic, TailConditions.stable_gap, claim, result, tail_sufficient_period
Declaration: same_perm_pal; proof_shape: bind-only; escape_witness: none
  consumers: Generates.border_periodic
Declaration: pal_border; proof_shape: bind-only; escape_witness: none
  consumers: Generates.border_periodic
Declaration: border_read; proof_shape: bind-only; escape_witness: none
  conclusion: the periodic equality of the underlying sequence; consumers: Generates.border_periodic, PseudopalindromicNormalization.finite_border_period, PseudopalindromicNormalization.pre_prefix
Declaration: Generates.border_periodic; proof_shape: bind-only; escape_witness: none
  consumers: tail_sufficient_period
Declaration: gap_bound; proof_shape: bind-only; escape_witness: none
  consumers: TailConditions.gap
Declaration: stable_increments; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_stable_gap, TailConditions.stable_gap
Declaration: TailConditions.gap; proof_shape: bind-only; escape_witness: none
  consumers: TailConditions.stable_gap
Declaration: TailConditions.stable_gap; proof_shape: bind-only; escape_witness: none
  consumers: tail_sufficient_period
Declaration: InvAntimorphism.perm_square; proof_shape: bind-only; escape_witness: none
  consumers: TailConditions.adjacent_product, TailConditions.perm_next
Declaration: TailConditions.conjugation; proof_shape: bind-only; escape_witness: none
  consumers: TailConditions.adjacent_product
Declaration: TailConditions.adjacent_product; proof_shape: bind-only; escape_witness: none
  consumers: TailConditions.perm_next
Declaration: TailConditions.perm_next; proof_shape: bind-only; escape_witness: none
  consumers: TailConditions.perm_iterate
Declaration: TailConditions.perm_iterate; proof_shape: bind-only; escape_witness: none
  consumers: TailConditions.perm_periodic
Declaration: TailConditions.perm_periodic; proof_shape: bind-only; escape_witness: none
  consumers: tail_sufficient_period
Declaration: constant_gap_iterate; proof_shape: bind-only; escape_witness: none
  consumers: tail_sufficient_period
Declaration: tail_sufficient_period; proof_shape: bind-only; escape_witness: none
  consumers: result
Declaration: pal_read; proof_shape: bind-only; escape_witness: none
  consumers: pre_pal_read
Declaration: fromInvolution; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_gap_inequality, fromInvolution_perm
Declaration: integerWord; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_conjugation, Generates.periodic_gap_inequality, Generates.periodic_letter_image, Generates.tail_necessary, integerWord_nat, integerWord_surjective, long_prefix_reflection, reflection_letter, reflection_prefix
Declaration: integerWord_nat; proof_shape: bind-only; escape_witness: none
  consumers: integerWord_surjective, long_prefix_reflection, reflection_letter, reflection_prefix
Declaration: integerWord_surjective; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_conjugation, Generates.periodic_gap_inequality
Declaration: IsReflection; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_conjugation, Generates.periodic_gap_inequality, ReflectionCenter, reflection_center_coset, reflection_conjugation, reflection_diff_translation, reflection_involutive, reflection_letter, reflection_perm_unique, reflection_prefix, reflection_shift_translation
Declaration: pre_pal_read; proof_shape: bind-only; escape_witness: none
  consumers: long_prefix_reflection
Declaration: long_prefix_reflection; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_reflection
Declaration: reflection_prefix; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_gap_inequality
Declaration: reflection_perm_unique; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_conjugation
Declaration: reflection_conjugation; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_conjugation
Declaration: reflection_letter; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_letter_image
Declaration: twistedTranslations; proof_shape: bind-only; escape_witness: none
  consumers: periodic_center_coset, reflection_center_coset, reflection_shift_translation
Declaration: ReflectionCenter; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_gap_inequality, periodic_center_coset, reflection_center_coset, reflection_shift_translation
Declaration: reflection_diff_translation; proof_shape: bind-only; escape_witness: none
  consumers: reflection_center_coset
Declaration: reflection_shift_translation; proof_shape: bind-only; escape_witness: none
  consumers: reflection_center_coset
Declaration: reflection_center_coset; proof_shape: bind-only; escape_witness: none
  consumers: periodic_center_coset
Declaration: periodic_center_coset; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_gap_inequality
Declaration: reflection_involutive; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_gap_inequality
Declaration: fromInvolution_perm; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_gap_inequality
Declaration: Generates.next_letter; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_letter_image
Declaration: Generates.normalized_next_le; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_gap_inequality
Declaration: Generates.periodic_reflection; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_conjugation, Generates.periodic_gap_inequality, Generates.periodic_letter_image
Declaration: Generates.periodic_gap_inequality; proof_shape: bind-only; escape_witness: none
  consumers: Generates.periodic_stable_gap
Declaration: Generates.periodic_stable_gap; proof_shape: bind-only; escape_witness: none
  consumers: Generates.tail_necessary
Declaration: Generates.periodic_letter_image; proof_shape: bind-only; escape_witness: none
  consumers: Generates.tail_necessary
Declaration: Generates.periodic_conjugation; proof_shape: bind-only; escape_witness: none
  consumers: Generates.tail_necessary
Declaration: Generates.tail_necessary; proof_shape: bind-only; escape_witness: none
  consumers: result
Declaration: claim; proof_shape: bind-only; escape_witness: none
  consumer: result (statement)
Declaration: result; proof_shape: content; escape_witness: D5.S1.Words.Palindromes.PseudopalindromicNormalization.period_extend_left
-/

import D5.S1.Words.Palindromes.PseudopalindromicNormalization
import Mathlib.Data.Nat.Periodic
import Mathlib.GroupTheory.Archimedean
import Mathlib.GroupTheory.SpecificGroups.Cyclic

open D5.S1.Words.Palindromes.PseudopalindromicNormalization

open D5.S1.Words.Palindromes

namespace D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity

def TailConditions (δ : ℕ → α) (Θ : ℕ → InvAntimorphism α) (k : ℕ) : Prop :=
  (∀ i j, 1 ≤ i → 1 ≤ j →
    (Θ (k + i)).toFun [δ (k + i + 1)] =
      (Θ (k + j)).toFun [δ (k + j + 1)]) ∧
  ∀ i, 1 ≤ i → ∀ w, (Θ (k + i)).toFun w = w →
    (Θ (k + i + 2)).toFun ((Θ (k + i + 1)).toFun w) = (Θ (k + i + 1)).toFun w

end D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity

namespace D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity
variable {α : Type*}

private theorem same_perm_pal (θ σ : InvAntimorphism α) (P : List α)
    (h : (PseudopalindromicNormalization.InvAntimorphism.perm θ) = (PseudopalindromicNormalization.InvAntimorphism.perm σ)) (hp : Function.IsFixedPt θ.toFun P) : Function.IsFixedPt σ.toFun P := by
  unfold Function.IsFixedPt at *
  simpa only [InvAntimorphism.map_word, h] using hp

private theorem pal_border (θ : InvAntimorphism α) (P Q : List α)
    (hp : Function.IsFixedPt θ.toFun P) (hq : Function.IsFixedPt θ.toFun Q) (hpre : P <+: Q) : P <:+ Q := by
  simpa only [show θ.toFun P = P from hp] using θ.prefix_to_suffix P Q hpre hq

private theorem border_read (u : ℕ → α) (m p j : ℕ)
    (hs : (List.ofFn (fun i : Fin m => u i)) <:+ (List.ofFn (fun i : Fin (m + p) => u i))) (hj : j < m) : u (j + p) = u j := by
  have hpref : (List.ofFn (fun i : Fin m => u i)) <+: (List.ofFn (fun i : Fin (m + p) => u i)) :=
    PseudopalindromicNormalization.pre_prefix u (Nat.le_add_right m p)
  have hlen : (List.ofFn (fun i : Fin m => u i)).length + p =
      (List.ofFn (fun i : Fin (m + p) => u i)).length := by simp
  have hjp : j + p < (List.ofFn (fun i : Fin (m + p) => u i)).length := by
    rw [PseudopalindromicNormalization.pre_length]
    omega
  have hperiod := PseudopalindromicNormalization.finite_border_period
    _ _ hpref hs p hlen j hjp
  calc
    u (j + p) = (List.ofFn (fun i : Fin (m + p) => u i))[j + p]'hjp := by
      symm
      exact PseudopalindromicNormalization.pre_get u (m + p) (j + p) hjp
    _ = (List.ofFn (fun i : Fin (m + p) => u i))[j]'(by simp; omega) := hperiod
    _ = u j := PseudopalindromicNormalization.pre_get u (m + p) j (by simp; omega)

namespace Generates
variable {δ : ℕ → α} {Θ : ℕ → InvAntimorphism α}
    {u : ℕ → α} {W : ℕ → List α} (hg : Generates δ Θ u W)
include hg

private theorem border_periodic (N p t : ℕ)
    (hl : ∀ n, N ≤ n → (W (n + t)).length = (W n).length + p)
    (hp : ∀ n, N ≤ n → (Θ (n + t)).perm = (Θ n).perm) :
    Function.Periodic u p := by
  intro j
  let n := N + j + 1
  have hn : N ≤ n := by dsimp [n]; omega
  have hs : W n <:+ W (n + t) :=
    pal_border (Θ (n + t)) (W n) (W (n + t))
      (same_perm_pal (Θ n) (Θ (n + t)) _ (hp n hn).symm ((PseudopalindromicNormalization.Generates.pal hg) n (by omega)))
      ((PseudopalindromicNormalization.Generates.pal hg) (n + t) (by omega)) ((PseudopalindromicNormalization.Generates.nested_le hg) (by omega))
  have he : W (n + t) = (List.ofFn (fun i : Fin ((W n).length + p) => u i)) := by
    rw [hg.2.2 (n + t), hl n hn]
  rw [hg.2.2 n, he] at hs
  have hjn := (PseudopalindromicNormalization.Generates.length_ge hg) n
  exact border_read u (W n).length p j hs (by dsimp [n] at hjn ⊢; omega)

end Generates
end D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity

namespace D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity
variable {α : Type*}

private theorem gap_bound (θ σ τ : InvAntimorphism α) (P Q R : List α) (a b : α)
    (hp : Function.IsFixedPt θ.toFun P) (hq : IsClosure σ (P ++ [a]) Q)
    (hr : IsClosure τ (Q ++ [b]) R)
    (hab : θ.toFun [a] = σ.toFun [b])
    (htr : ∀ w, Function.IsFixedPt θ.toFun w → Function.IsFixedPt τ.toFun (σ.toFun w)) :
    R.length + P.length ≤ 2 * Q.length := by
  have he : (PseudopalindromicNormalization.InvAntimorphism.letter θ) a = (PseudopalindromicNormalization.InvAntimorphism.letter σ) b := by simpa using hab
  have hc := (palindrome_transport_iff θ σ τ).mp htr
  have heb : (PseudopalindromicNormalization.InvAntimorphism.letter τ) b = (PseudopalindromicNormalization.InvAntimorphism.letter σ) a := by
    have hg := congrArg (fun π : Equiv.Perm α => π b) hc
    simpa only [Equiv.Perm.mul_apply, InvAntimorphism.perm_apply, ← he, InvAntimorphism.letterInvolutive] using hg
  have hea : (PseudopalindromicNormalization.InvAntimorphism.letter τ) ((PseudopalindromicNormalization.InvAntimorphism.letter σ) a) = b := by
    rw [← heb, (PseudopalindromicNormalization.InvAntimorphism.letterInvolutive τ)]
  let S := σ.toFun [a] ++ σ.toFun P ++ [b]
  have hs : S <:+ Q ++ [b] := by
    have ht := (PseudopalindromicNormalization.InvAntimorphism.prefix_to_suffix σ) (P ++ [a]) Q hq.1 hq.2.1
    obtain ⟨r, heq⟩ := ht
    refine ⟨r, ?_⟩
    dsimp [S]
    rw [← heq, σ.map_append]
    simp only [List.append_assoc]
  have hsp : Function.IsFixedPt τ.toFun S := by
    have ht := pal_wrap τ [(PseudopalindromicNormalization.InvAntimorphism.letter σ) a] (σ.toFun P) (htr P hp)
    simpa only [S, InvAntimorphism.map_singleton, hea] using ht
  have hm := closure_suffix_bound τ (Q ++ [b]) R S hr hs hsp
  have hl : S.length = P.length + 2 := by
    simp [S, Nat.add_comm, Nat.add_left_comm]
  rw [hl, List.length_append, List.length_singleton] at hm
  omega

private theorem stable_increments (L : ℕ → ℕ) (N : ℕ) (hL : StrictMono L)
    (hc : ∀ n, N ≤ n → L (n + 2) + L n ≤ 2 * L (n + 1)) :
    ∃ M g, N ≤ M ∧ 0 < g ∧ ∀ n, M ≤ n → L (n + 1) = L n + g := by
  let d (i : ℕ) := L (N + i + 1) - L (N + i)
  have hd : Antitone d := by
    apply antitone_nat_of_succ_le
    intro i
    have hc' := hc (N + i) (by omega)
    have h1 := hL (show N + i < N + i + 1 by omega)
    have h2 := hL (show N + i + 1 < N + i + 2 by omega)
    dsimp [d]
    have he : N + (i + 1) = N + i + 1 := by omega
    rw [he]
    change L (N + i + 2) - L (N + i + 1) ≤ L (N + i + 1) - L (N + i)
    omega
  obtain ⟨j, hj⟩ := WellFoundedLT.antitone_chain_condition hd
  refine ⟨N + j, d j, by omega, ?_, ?_⟩
  · have := hL (show N + j < N + j + 1 by omega)
    dsimp [d]; omega
  · intro n hn
    have he := hj (n - N) (by omega)
    have hi : N + (n - N) = n := by omega
    dsimp [d] at he
    rw [hi] at he
    have := hL (show n < n + 1 by omega)
    dsimp [d]
    omega

namespace TailConditions
variable {δ : ℕ → α} {Θ : ℕ → InvAntimorphism α} {k : ℕ}
    (ht : TailConditions δ Θ k)
include ht

private theorem gap {u : ℕ → α} {W : ℕ → List α}
    (hg : Generates δ Θ u W) (i : ℕ) (hi : 1 ≤ i) :
    (W (k + i + 2)).length + (W (k + i)).length ≤
      2 * (W (k + i + 1)).length := by
  exact gap_bound (Θ (k + i)) (Θ (k + i + 1)) (Θ (k + i + 2))
    (W (k + i)) (W (k + i + 1)) (W (k + i + 2))
    (δ (k + i + 1)) (δ (k + i + 2))
    ((PseudopalindromicNormalization.Generates.pal hg) _ (by omega)) ((PseudopalindromicNormalization.Generates.step hg) _) ((PseudopalindromicNormalization.Generates.step hg) _)
    (by simpa only [Nat.add_assoc] using ht.1 i (i + 1) hi (by omega))
    (by simpa only [Function.IsFixedPt, Nat.add_assoc] using ht.2 i hi)

private theorem stable_gap {u : ℕ → α} {W : ℕ → List α}
    (hg : Generates δ Θ u W) :
    ∃ N g, k + 1 ≤ N ∧ 0 < g ∧
      ∀ n, N ≤ n → (W (n + 1)).length = (W n).length + g := by
  apply stable_increments (fun n => (W n).length) (k + 1)
    (PseudopalindromicNormalization.Generates.lengths_strictMono hg)
  intro n hn
  have he : k + (n - k) = n := by omega
  simpa only [he] using ht.gap hg (n - k) (by omega)

end TailConditions
end D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity

namespace D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity
variable {α : Type*}

@[simp] private theorem InvAntimorphism.perm_square (θ : InvAntimorphism α) :
    (PseudopalindromicNormalization.InvAntimorphism.perm θ) * (PseudopalindromicNormalization.InvAntimorphism.perm θ) = 1 := by
  exact mul_eq_one_iff_eq_inv.mpr rfl

namespace TailConditions
variable {δ : ℕ → α} {Θ : ℕ → InvAntimorphism α} {k : ℕ}
    (ht : TailConditions δ Θ k)
include ht

private theorem conjugation (n : ℕ) (hn : k + 1 ≤ n) :
    (Θ (n + 2)).perm = (Θ (n + 1)).perm * (Θ n).perm * (Θ (n + 1)).perm := by
  have hi : 1 ≤ n - k := by omega
  have he : k + (n - k) = n := by omega
  have hp := ht.2 (n - k) hi
  rw [he] at hp
  exact (palindrome_transport_iff _ _ _).mp hp

private theorem adjacent_product (n : ℕ) (hn : k + 1 ≤ n) :
    (Θ (n + 1)).perm * (Θ n).perm = ((Θ (k + 2)).perm * (Θ (k + 1)).perm) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have hc := (TailConditions.conjugation ht) n hn
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc, hc, mul_assoc,
      InvAntimorphism.perm_square, mul_one] using ih

private theorem perm_next (n : ℕ) (hn : k + 1 ≤ n) :
    (Θ (n + 1)).perm = ((Θ (k + 2)).perm * (Θ (k + 1)).perm) * (Θ n).perm := by
  rw [← (TailConditions.adjacent_product ht) n hn, mul_assoc, InvAntimorphism.perm_square, mul_one]

private theorem perm_iterate (n t : ℕ) (hn : k + 1 ≤ n) :
    (Θ (n + t)).perm = ((Θ (k + 2)).perm * (Θ (k + 1)).perm) ^ t * (Θ n).perm := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.add_succ, (TailConditions.perm_next ht) (n + t) (by omega), ih, pow_succ', mul_assoc]
    simp only [mul_assoc]

private theorem perm_periodic (n : ℕ) (hn : k + 1 ≤ n) :
    (Θ (n + orderOf (((Θ (k + 2)).perm * (Θ (k + 1)).perm)))).perm = (Θ n).perm := by
  rw [(TailConditions.perm_iterate ht) n _ hn, pow_orderOf_eq_one, one_mul]

end TailConditions
end D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity

namespace D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity
variable {α : Type*}

private theorem constant_gap_iterate (W : ℕ → List α) (N g : ℕ)
    (hg : ∀ n, N ≤ n → (W (n + 1)).length = (W n).length + g)
    (n t : ℕ) (hn : N ≤ n) :
    (W (n + t)).length = (W n).length + g * t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.add_succ, hg (n + t) (by omega), ih, Nat.mul_succ, Nat.add_assoc]

private theorem tail_sufficient_period {δ : ℕ → α} {Θ : ℕ → InvAntimorphism α}
    {u : ℕ → α} {W : ℕ → List α} {k : ℕ}
    (hg : Generates δ Θ u W) (ht : TailConditions δ Θ k) :
    ∃ g, 0 < g ∧
      Function.Periodic u (g * orderOf (((Θ (k + 2)).perm * (Θ (k + 1)).perm))) := by
  obtain ⟨N, g, hN, hgp, hgap⟩ := (TailConditions.stable_gap ht) hg
  refine ⟨g, hgp, ?_⟩
  exact (Generates.border_periodic hg) N (g * orderOf (((Θ (k + 2)).perm * (Θ (k + 1)).perm))) (orderOf (((Θ (k + 2)).perm * (Θ (k + 1)).perm)))
    (constant_gap_iterate W N g hgap · _ ·)
    (fun n hn => (TailConditions.perm_periodic ht) n (by omega))

end D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity

namespace D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity
variable {α : Type*}

private theorem pal_read (θ : InvAntimorphism α) (w : List α) (hp : Function.IsFixedPt θ.toFun w)
    (j : ℕ) (hj : j < w.length) :
    w[j] = (PseudopalindromicNormalization.InvAntimorphism.perm θ) (w[w.length - 1 - j]'(by omega)) := by
  have he : (w.map (PseudopalindromicNormalization.InvAntimorphism.perm θ)).reverse = w := ((PseudopalindromicNormalization.InvAntimorphism.map_word θ) w).symm.trans hp
  have hh := List.getElem_of_eq he (by simpa using hj)
  simpa only [List.getElem_reverse, List.getElem_map, List.length_map] using hh.symm


end D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity

open D5.S1.Words.Palindromes.PseudopalindromicNormalization
open D5.S1.Words.Palindromes.PseudopalindromicNormalization

open D5.S1.Words.Palindromes

namespace D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity

end D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity

namespace D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity
variable {α : Type*}
private def fromInvolution (π : Equiv.Perm α) (hi : Function.Involutive π) : InvAntimorphism α where
  toFun w := (w.map π).reverse
  map_append v w := by simp
  involutive w := by
    simp only [List.map_reverse, List.reverse_reverse, List.map_map]
    have hf : (fun a => π (π a)) = (fun a => a) := funext hi
    simp only [Function.comp_def, hf]
    simp

private def integerWord (u : ℕ → α) (p : ℕ) (z : ℤ) : α := u (Int.natMod z p)

private theorem integerWord_nat (u : ℕ → α) (p : ℕ) (hp : Function.Periodic u p) (n : ℕ) :
    integerWord u p n = u n := by
  unfold integerWord Int.natMod
  rw [← Int.natCast_emod, Int.toNat_natCast]
  exact hp.map_mod_nat n

private theorem integerWord_surjective (u : ℕ → α) (p : ℕ)
    (hp : Function.Periodic u p) (hu : Function.Surjective u) :
    Function.Surjective (integerWord u p) := by
  intro a
  obtain ⟨n, hn⟩ := hu a
  exact ⟨n, (integerWord_nat u p hp n).trans hn⟩

private def IsReflection (x : ℤ → α) (c : ℤ) (π : Equiv.Perm α) : Prop :=
  ∀ z, x (c - z) = π (x z)

private theorem pre_pal_read (u : ℕ → α) (L : ℕ) (θ : InvAntimorphism α)
    (h : Function.IsFixedPt θ.toFun ((List.ofFn (fun i : Fin L => u i)))) (j : ℕ) (hj : j < L) :
    u j = (PseudopalindromicNormalization.InvAntimorphism.perm θ) (u (L - 1 - j)) := by
  have hh := pal_read θ ((List.ofFn (fun i : Fin L => u i))) h j (by simpa using hj)
  rw [pre_get, pre_get] at hh
  simpa only [pre_length] using hh

private theorem long_prefix_reflection (u : ℕ → α) (p L : ℕ) (θ : InvAntimorphism α)
    (hp0 : 0 < p) (hp : Function.Periodic u p) (hL : p ≤ L)
    (h : Function.IsFixedPt θ.toFun ((List.ofFn (fun i : Fin L => u i)))) :
    IsReflection (integerWord u p) ((L : ℤ) - 1) (PseudopalindromicNormalization.InvAntimorphism.perm θ) := by
  intro z
  let r := (z % (p : ℤ)).toNat
  have hz0 : 0 ≤ z % (p : ℤ) := Int.emod_nonneg _ (by omega)
  have hrZ : (r : ℤ) = z % (p : ℤ) := Int.toNat_of_nonneg hz0
  have hrp : r < p := by
    have := Int.emod_lt_of_pos z (show (0 : ℤ) < p by omega)
    omega
  have he : ((L : ℤ) - 1 - z) % (p : ℤ) =
      ((L : ℤ) - 1 - (r : ℤ)) % (p : ℤ) := by
    simp only [Int.sub_emod, hrZ, Int.emod_emod]
  have hi : (L : ℤ) - 1 - (r : ℤ) = ((L - 1 - r : ℕ) : ℤ) := by omega
  calc
    integerWord u p ((L : ℤ) - 1 - z) =
        integerWord u p ((L : ℤ) - 1 - (r : ℤ)) := by simp only [integerWord, Int.natMod, he]
    _ = u (L - 1 - r) := by rw [hi]; exact integerWord_nat u p hp _
    _ = (PseudopalindromicNormalization.InvAntimorphism.perm θ) (u r) := by
      have hh := pre_pal_read u L θ h (L - 1 - r) (by omega)
      simpa only [show L - 1 - (L - 1 - r) = r by omega] using hh
    _ = (PseudopalindromicNormalization.InvAntimorphism.perm θ) (integerWord u p z) := rfl

private theorem reflection_prefix (u : ℕ → α) (p L : ℕ) (θ : InvAntimorphism α)
    (hp : Function.Periodic u p)
    (h : IsReflection (integerWord u p) ((L : ℤ) - 1) (PseudopalindromicNormalization.InvAntimorphism.perm θ)) :
    Function.IsFixedPt θ.toFun ((List.ofFn (fun i : Fin L => u i))) := by
  unfold Function.IsFixedPt
  rw [(PseudopalindromicNormalization.InvAntimorphism.map_word θ)]
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hjL : j < L := by simpa using hj'
    have hi : (L : ℤ) - 1 - (j : ℤ) = ((L - 1 - j : ℕ) : ℤ) := by omega
    have hh := h j
    rw [hi, integerWord_nat u p hp, integerWord_nat u p hp] at hh
    simp only [List.getElem_reverse, List.length_map, pre_length,
      List.getElem_map, pre_get]
    change (PseudopalindromicNormalization.InvAntimorphism.perm θ) (u (L - 1 - j)) = u j
    rw [hh]
    exact (PseudopalindromicNormalization.InvAntimorphism.letterInvolutive θ) _

private theorem reflection_perm_unique (x : ℤ → α) (hu : Function.Surjective x)
    (c : ℤ) (π σ : Equiv.Perm α) (hπ : IsReflection x c π)
    (hσ : IsReflection x c σ) : π = σ := by
  apply DFunLike.coe_injective
  apply hu.injective_comp_right
  exact funext fun z => (hπ z).symm.trans (hσ z)

private theorem reflection_conjugation (x : ℤ → α) (a b : ℤ) (π σ : Equiv.Perm α)
    (hπ : IsReflection x a π) (hσ : IsReflection x b σ) :
    IsReflection x (2 * b - a) (σ * π * σ) := by
  intro z
  have he : 2 * b - a - z = b - (a - (b - z)) := by ring
  rw [he, hσ, hπ, hσ]
  rfl

private theorem reflection_letter (u : ℕ → α) (p L : ℕ) (θ : InvAntimorphism α)
    (hp : Function.Periodic u p)
    (h : IsReflection (integerWord u p) ((L : ℤ) - 1) (PseudopalindromicNormalization.InvAntimorphism.perm θ)) :
    (PseudopalindromicNormalization.InvAntimorphism.perm θ) (u L) = integerWord u p (-1) := by
  have hh := h L
  have he : (L : ℤ) - 1 - L = -1 := by omega
  rw [he, integerWord_nat u p hp] at hh
  exact hh.symm

end D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity

namespace D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity
variable {α : Type*}

private def twistedTranslations (x : ℤ → α) : AddSubgroup ℤ where
  carrier := {d | ∃ ρ : Equiv.Perm α, ∀ z, x (z + d) = ρ (x z)}
  zero_mem' := ⟨1, by intro z; simp⟩
  add_mem' := by
    rintro a b ⟨π, hπ⟩ ⟨σ, hσ⟩
    refine ⟨σ * π, ?_⟩
    intro z
    rw [← add_assoc, hσ, hπ]
    rfl
  neg_mem' := by
    rintro d ⟨π, hπ⟩
    refine ⟨π.symm, ?_⟩
    intro z
    have hh := congrArg π.symm (hπ (z - d))
    rw [sub_add_cancel, Equiv.symm_apply_apply] at hh
    simpa only [sub_eq_add_neg] using hh.symm

private def ReflectionCenter (x : ℤ → α) (c : ℤ) : Prop :=
  ∃ π : Equiv.Perm α, IsReflection x c π

private theorem reflection_diff_translation (x : ℤ → α) (a b : ℤ)
    (π σ : Equiv.Perm α) (hπ : IsReflection x a π) (hσ : IsReflection x b σ) :
    b - a ∈ twistedTranslations x := by
  refine ⟨σ * π, ?_⟩
  intro z
  have he : z + (b - a) = b - (a - z) := by ring
  rw [he, hσ, hπ]
  rfl

private theorem reflection_shift_translation (x : ℤ → α) (c d : ℤ)
    (hc : ReflectionCenter x c) (hd : d ∈ twistedTranslations x) :
    ReflectionCenter x (c + d) := by
  obtain ⟨σ, hσ⟩ := hc
  obtain ⟨ρ, hρ⟩ := hd
  refine ⟨ρ * σ, ?_⟩
  intro z
  have he : c + d - z = (c - z) + d := by ring
  rw [he, hρ, hσ]
  rfl

private theorem reflection_center_coset (x : ℤ → α) (c : ℤ) (hc : ReflectionCenter x c)
    (d : ℤ) : ReflectionCenter x d ↔ d - c ∈ twistedTranslations x := by
  constructor
  · rintro ⟨π, hπ⟩
    obtain ⟨σ, hσ⟩ := hc
    exact reflection_diff_translation x c d σ π hσ hπ
  · intro hd
    have h := reflection_shift_translation x c (d - c) hc hd
    simpa only [add_sub_cancel] using h

private theorem periodic_center_coset (x : ℤ → α) (c : ℤ)
    (hc : ReflectionCenter x c) :
    ∃ g : ℕ, ∀ d, ReflectionCenter x d ↔ (g : ℤ) ∣ d - c := by
  obtain ⟨a, ha⟩ :=
    (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top (twistedTranslations x)).mp inferInstance
  have he : twistedTranslations x = AddSubgroup.zmultiples a := by
    exact ha.symm
  refine ⟨a.natAbs, ?_⟩
  intro d
  rw [reflection_center_coset x c hc d, he, Int.mem_zmultiples_iff,
    Int.natAbs_dvd]

private theorem reflection_involutive (x : ℤ → α) (hu : Function.Surjective x)
    (c : ℤ) (π : Equiv.Perm α) (hπ : IsReflection x c π) : Function.Involutive π := by
  intro a
  obtain ⟨z, rfl⟩ := hu a
  have hh := hπ (c - z)
  have he : c - (c - z) = z := by ring
  rw [he, hπ] at hh
  exact hh.symm

end D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity

namespace D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity
variable {α : Type*}

private theorem fromInvolution_perm (π : Equiv.Perm α) (hi : Function.Involutive π) :
    (fromInvolution π hi).perm = π := by
  exact ((fromInvolution π hi).perm_unique π (fun _ => rfl)).symm

namespace Generates
variable {δ : ℕ → α} {Θ : ℕ → InvAntimorphism α}
    {u : ℕ → α} {W : ℕ → List α} (hg : Generates δ Θ u W)
include hg

private theorem next_letter (n : ℕ) : δ (n + 1) = u (W n).length := by
  have hpre := ((PseudopalindromicNormalization.Generates.step hg) n).1
  have hi : (W n).length < (W n ++ [δ (n + 1)]).length := by simp
  have he := hpre.getElem hi
  have hr := (PseudopalindromicNormalization.Generates.read hg) (n + 1) (W n).length (by have := (PseudopalindromicNormalization.Generates.strict_growth hg) n; omega)
  calc
    δ (n + 1) = (W n ++ [δ (n + 1)])[(W n).length]'hi := by simp
    _ = (W (n + 1))[(W n).length]'(by have := (PseudopalindromicNormalization.Generates.strict_growth hg) n; omega) := he
    _ = u (W n).length := hr

private theorem normalized_next_le (hn : IsNormalized u W) (n m : ℕ)
    (hm : (W n).length < m) (hp : (∃ θ : InvAntimorphism α, Function.IsFixedPt θ.toFun (List.ofFn (fun i : Fin m => u i)))) :
    (W (n + 1)).length ≤ m := by
  obtain ⟨j, hj⟩ := hn m hp
  have hjL : (W j).length = m := by simpa using congrArg List.length hj
  have hnj : n < j := (PseudopalindromicNormalization.Generates.lengths_strictMono hg).lt_iff_lt.mp (by omega)
  have hle := (PseudopalindromicNormalization.Generates.lengths_strictMono hg).monotone (show n + 1 ≤ j by omega)
  omega

private theorem periodic_reflection (p : ℕ) (hp0 : 0 < p) (hp : Function.Periodic u p)
    (n : ℕ) (hn : p ≤ n) :
    IsReflection (integerWord u p) (((W n).length : ℤ) - 1) (Θ n).perm := by
  apply long_prefix_reflection u p _ _ hp0 hp (le_trans hn ((PseudopalindromicNormalization.Generates.length_ge hg) n))
  rw [← hg.2.2]
  exact (PseudopalindromicNormalization.Generates.pal hg) n (by omega)

private theorem periodic_gap_inequality (hn : IsNormalized u W) (p : ℕ)
    (hp0 : 0 < p) (hp : Function.Periodic u p) (hu : Function.Surjective u) (n : ℕ) (hnp : p ≤ n) :
    (W (n + 2)).length + (W n).length ≤ 2 * (W (n + 1)).length := by
  let A := (W n).length
  let B := (W (n + 1)).length
  let T := 2 * B - A
  have hAB : A < B := (PseudopalindromicNormalization.Generates.strict_growth hg) n
  have hT : B < T := by dsimp [T]; omega
  have hθ := (Generates.periodic_reflection hg) p hp0 hp n hnp
  have hσ := (Generates.periodic_reflection hg) p hp0 hp (n + 1) (by omega)
  let x := integerWord u p
  obtain ⟨g, hcoset⟩ := periodic_center_coset x ((A : ℤ) - 1)
    ⟨(Θ n).perm, hθ⟩
  have hd := (hcoset ((B : ℤ) - 1)).mp ⟨(Θ (n + 1)).perm, hσ⟩
  have hTcast : (T : ℤ) - 1 - ((A : ℤ) - 1) =
      (((B : ℤ) - 1) - ((A : ℤ) - 1)) +
      (((B : ℤ) - 1) - ((A : ℤ) - 1)) := by dsimp [T]; omega
  have hcenter : ReflectionCenter x ((T : ℤ) - 1) :=
    (hcoset _).mpr (by rw [hTcast]; exact dvd_add hd hd)
  obtain ⟨π, hπ⟩ := hcenter
  have hinv := reflection_involutive x (integerWord_surjective u p hp hu) _ π hπ
  have ht : Function.IsFixedPt (fromInvolution π hinv).toFun (List.ofFn (fun i : Fin T => u i)) := by
    apply reflection_prefix u p T _ hp
    rw [fromInvolution_perm]
    exact hπ
  have hle := (Generates.normalized_next_le hg) hn (n + 1) T hT ⟨_, ht⟩
  change (W (n + 2)).length ≤ T at hle
  dsimp [A, B] at hAB
  dsimp [T, A, B] at hle
  omega

private theorem periodic_stable_gap (hn : IsNormalized u W) (p : ℕ)
    (hp0 : 0 < p) (hp : Function.Periodic u p) (hu : Function.Surjective u) :
    ∃ N g, p ≤ N ∧
      ∀ n, N ≤ n → (W (n + 1)).length = (W n).length + g := by
  obtain ⟨N, g, hN, _, hgap⟩ := GeneralizedPseudostandardPeriodicity.stable_increments (fun n => (W n).length) p (PseudopalindromicNormalization.Generates.lengths_strictMono hg)
    ((Generates.periodic_gap_inequality hg) hn p hp0 hp hu)
  exact ⟨N, g, hN, hgap⟩

private theorem periodic_letter_image (p : ℕ) (hp0 : 0 < p) (hp : Function.Periodic u p)
    (n : ℕ) (hn : p ≤ n) :
    (Θ n).perm (δ (n + 1)) = integerWord u p (-1) := by
  rw [(Generates.next_letter hg)]
  exact reflection_letter u p _ _ hp ((Generates.periodic_reflection hg) p hp0 hp n hn)

private theorem periodic_conjugation (p N g : ℕ) (hp0 : 0 < p)
    (hp : Function.Periodic u p) (hu : Function.Surjective u) (hN : p ≤ N)
    (hgap : ∀ n, N ≤ n → (W (n + 1)).length = (W n).length + g)
    (n : ℕ) (hn : N ≤ n) :
    (Θ (n + 2)).perm = (Θ (n + 1)).perm * (Θ n).perm * (Θ (n + 1)).perm := by
  apply reflection_perm_unique (integerWord u p) (integerWord_surjective u p hp hu)
    (((W (n + 2)).length : ℤ) - 1)
  · exact (Generates.periodic_reflection hg) p hp0 hp (n + 2) (by omega)
  · have h1 := hgap n hn
    have h2 := hgap (n + 1) (by omega)
    change (W (n + 2)).length = (W (n + 1)).length + g at h2
    have hc := reflection_conjugation (integerWord u p)
      (((W n).length : ℤ) - 1) (((W (n + 1)).length : ℤ) - 1)
      (Θ n).perm (Θ (n + 1)).perm
      ((Generates.periodic_reflection hg) p hp0 hp n (by omega))
      ((Generates.periodic_reflection hg) p hp0 hp (n + 1) (by omega))
    have he : ((W (n + 2)).length : ℤ) - 1 =
        2 * (((W (n + 1)).length : ℤ) - 1) - (((W n).length : ℤ) - 1) := by omega
    rwa [← he] at hc

private theorem tail_necessary (hn : IsNormalized u W) (hu : Function.Surjective u)
    (hp : ∃ p, 0 < p ∧ Function.Periodic u p) : ∃ k, TailConditions δ Θ k := by
  obtain ⟨p, hp0, hp⟩ := hp
  obtain ⟨N, g, hN, hgap⟩ := (Generates.periodic_stable_gap hg) hn p hp0 hp hu
  refine ⟨N, ?_, ?_⟩
  · intro i j hi hj
    simp only [InvAntimorphism.map_singleton, List.singleton_inj, ← InvAntimorphism.perm_apply]
    exact ((Generates.periodic_letter_image hg) p hp0 hp (N + i) (by omega)).trans
      ((Generates.periodic_letter_image hg) p hp0 hp (N + j) (by omega)).symm
  · intro i hi
    apply (palindrome_transport_iff _ _ _).mpr
    exact (Generates.periodic_conjugation hg) p N g hp0 hp hu hN hgap (N + i) (by omega)

end Generates
end D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity

open D5.S1.Words.Palindromes.PseudopalindromicNormalization
open D5.S1.Words.Palindromes.PseudopalindromicNormalization

open D5.S1.Words.Palindromes

namespace D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity

def claim : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α],
    (∀ (δ : ℕ → α) (Θ : ℕ → InvAntimorphism α) (u : ℕ → α)
      (W : ℕ → List α), Generates δ Θ u W →
      ∃ δ' Θ' W', Generates δ' Θ' u W' ∧ IsNormalized u W') ∧
    (∀ (δ : ℕ → α) (Θ : ℕ → InvAntimorphism α) (u : ℕ → α)
      (W : ℕ → List α), Generates δ Θ u W → IsNormalized u W → Function.Surjective u →
      ((∃ p, 0 < p ∧ Function.Periodic u p) ↔ ∃ k, TailConditions δ Θ k))

end D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity

namespace D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity

theorem result : claim := by
  intro α _ _
  constructor
  · intro δ Θ u W hg
    exact (PseudopalindromicNormalization.Generates.normalization_exists hg)
  · intro δ Θ u W hg hn hu
    constructor
    · exact (GeneralizedPseudostandardPeriodicity.Generates.tail_necessary hg) hn hu
    · rintro ⟨k, hk⟩
      obtain ⟨g, hg0, hp⟩ := tail_sufficient_period hg hk
      refine ⟨g * orderOf (((Θ (k + 2)).perm * (Θ (k + 1)).perm)), Nat.mul_pos hg0 (orderOf_pos _), ?_⟩
      exact hp

end D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity
