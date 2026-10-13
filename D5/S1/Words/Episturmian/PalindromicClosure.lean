/- GID: D5/S1/Words/Episturmian/PalindromicClosure
   generality: G
   mirror-B: D5/B/S1/Words/Episturmian/PalindromicClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: literal palindromic closure and central-word construction -/

/- proof_shape: central_length_ge: content; escape_witness: D5.S1.Words.Episturmian.PalindromicClosure.central_length_ge
   escape_witness: central_length_ge
   admission_basis: escape-witness
   Declarations:
   proof_shape: extension_exists: bind-only; consumer: PalindromicClosure.palClosure
   definition: palClosure; consumer: PalindromicClosure.palClosure_spec
   proof_shape: palClosure_spec: bind-only; consumer: PalindromicClosure.palClosure_formula_cut
   proof_shape: suffix_cut_exists: bind-only; consumer: PalindromicClosure.palCut
   definition: palCut; consumer: PalindromicClosure.palCut_spec
   proof_shape: palCut_spec: bind-only; consumer: PalindromicClosure.palindrome_extension_length
   proof_shape: palCut_min: bind-only; consumer: PalindromicClosure.palindrome_extension_length
   proof_shape: palindrome_extension_middle: bind-only; consumer: PalindromicClosure.palindrome_extension_length
   proof_shape: palindrome_extension_length: bind-only; consumer: PalindromicClosure.palClosure_formula_cut
   proof_shape: closure_candidate_palindrome: bind-only; consumer: PalindromicClosure.palClosure_formula_cut
   proof_shape: palClosure_formula_cut: bind-only; consumer: MorphicDecomposition.Hword_palClosure
   definition: central; consumer: PalindromicClosure.central_length_ge
   proof_shape: central_length_ge: content; escape_witness: D5.S1.Words.Episturmian.PalindromicClosure.central_length_ge; consumer: PalindromicClosure.cDelta
   definition: cDelta; consumer: PalindromicClosure.claim
   definition: Lang; consumer: PalindromicClosure.claim
   definition: BoundedPQ; consumer: PalindromicClosure.claim
   definition: fractionalPower; consumer: PalindromicClosure.DioAdmissible
   definition: DioAdmissible; consumer: PalindromicClosure.dio
   definition: dio; consumer: PalindromicClosure.claim
   definition: claim; consumer: DiophantineExponentCriterion.result
   Direct frozen dependencies (pre-existing): D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs; D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor; sha256:54f2f8a1cd3a83f896d4018ef9821e5aa1b6046bd757ec6a999734a691651d1c
   Finite prefixes use the existing factor operator at start zero.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16158
-/

import D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs
import Mathlib.Data.List.Palindrome

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Episturmian.PalindromicClosure
open D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs
variable {d : Nat}
attribute [local instance] Classical.propDecidable

private theorem extension_exists (w : List (Fin d)) :
    ∃ n : Nat, ∃ p : List (Fin d), w <+: p ∧ List.Palindrome p ∧ p.length = n := by
  exact ⟨_, w ++ w.reverse, List.prefix_append _ _, List.Palindrome.append_reverse w, rfl⟩

noncomputable def palClosure (w : List (Fin d)) : List (Fin d) :=
  Classical.choose (Nat.find_spec (extension_exists w))

theorem palClosure_spec (w : List (Fin d)) :
    w <+: palClosure w ∧ List.Palindrome (palClosure w) ∧
      ∀ p, w <+: p → List.Palindrome p → (palClosure w).length ≤ p.length := by
  have h := Classical.choose_spec (Nat.find_spec (extension_exists w))
  refine ⟨h.1, h.2.1, ?_⟩
  intro p hpre hpal
  change (Classical.choose (Nat.find_spec (extension_exists w))).length ≤ p.length
  rw [h.2.2]
  exact Nat.find_min' (extension_exists w) ⟨p, hpre, hpal, rfl⟩

private theorem suffix_cut_exists (w : List (Fin d)) :
    ∃ k : Nat, k ≤ w.length ∧ List.Palindrome (w.drop k) := by
  exact ⟨w.length, le_rfl, by simp; exact List.Palindrome.nil⟩

noncomputable def palCut (w : List (Fin d)) : Nat :=
  Nat.find (suffix_cut_exists w)

theorem palCut_spec (w : List (Fin d)) :
    palCut w ≤ w.length ∧ List.Palindrome (w.drop (palCut w)) :=
  Nat.find_spec (suffix_cut_exists w)

theorem palCut_min (w : List (Fin d)) (k : Nat)
    (hk : k ≤ w.length) (hp : List.Palindrome (w.drop k)) : palCut w ≤ k :=
  Nat.find_min' (suffix_cut_exists w) ⟨hk, hp⟩

theorem palindrome_extension_middle {w r : List (Fin d)}
    (hp : List.Palindrome (w ++ r)) (hm : r.length ≤ w.length) :
    List.Palindrome (w.drop r.length) := by
  have h := hp.reverse_eq
  have ht := congrArg (List.take r.length) h
  have htr : r.reverse.take r.length = r.reverse := by
    simpa only [List.length_reverse] using (List.take_length (l := r.reverse))
  rw [List.reverse_append, List.take_append_of_le_length (by simp),
    htr, List.take_append_of_le_length hm] at ht
  have hw : w = r.reverse ++ w.drop r.length := by
    rw [ht]
    exact (List.take_append_drop _ _).symm
  rw [List.reverse_append, hw] at h
  simp only [List.reverse_append, List.reverse_reverse, List.append_assoc,
    List.append_cancel_left_eq, List.append_cancel_right_eq] at h
  exact List.Palindrome.of_reverse_eq h

theorem palindrome_extension_length (w p : List (Fin d))
    (hpre : w <+: p) (hpal : List.Palindrome p) :
    w.length + palCut w ≤ p.length := by
  obtain ⟨r, rfl⟩ := hpre
  simp only [List.length_append]
  by_cases hm : r.length ≤ w.length
  · have hc := palCut_min w r.length hm (palindrome_extension_middle hpal hm)
    omega
  · have hc := (palCut_spec w).1
    omega

theorem closure_candidate_palindrome (w : List (Fin d)) :
    List.Palindrome (w ++ (w.take (palCut w)).reverse) := by
  have hpal := (palCut_spec w).2.reverse_eq
  have he : w ++ (w.take (palCut w)).reverse =
      (w.take (palCut w) ++ w.drop (palCut w)) ++ (w.take (palCut w)).reverse := by
    rw [List.take_append_drop]
  apply List.Palindrome.of_reverse_eq
  rw [he]
  simp only [List.reverse_append, List.reverse_reverse, hpal, List.append_assoc]

theorem palClosure_formula_cut (w : List (Fin d)) :
    palClosure w = w ++ (w.take (palCut w)).reverse := by
  have hs := palClosure_spec w
  have hp := closure_candidate_palindrome w
  have hlen : (palClosure w).length = (w ++ (w.take (palCut w)).reverse).length := by
    have hu := hs.2.2 _ (List.prefix_append _ _) hp
    have hl := palindrome_extension_length w (palClosure w) hs.1 hs.2.1
    have hc := (palCut_spec w).1
    simp only [List.length_append, List.length_reverse, List.length_take,
      Nat.min_eq_left hc] at hu ⊢
    omega
  obtain ⟨r, hr⟩ := hs.1
  have hrlen : r.length = palCut w := by
    rw [← hr] at hlen
    simp only [List.length_append, List.length_reverse, List.length_take,
      Nat.min_eq_left (palCut_spec w).1] at hlen
    omega
  have hp' : List.Palindrome (w ++ r) := by rw [hr]; exact hs.2.1
  have hh := congrArg (List.take r.length) hp'.reverse_eq
  have htr : r.reverse.take r.length = r.reverse := by
    simpa only [List.length_reverse] using (List.take_length (l := r.reverse))
  rw [List.reverse_append, List.take_append_of_le_length (by simp),
    htr, List.take_append_of_le_length
      (by rw [hrlen]; exact (palCut_spec w).1)] at hh
  have hh' := congrArg List.reverse hh
  simp only [List.reverse_reverse] at hh'
  rw [hrlen] at hh'
  rw [← hr, hh']

noncomputable def central (Delta : Nat → Fin d) : Nat → List (Fin d)
  | 0 => []
  | k + 1 => palClosure (central Delta k ++ [Delta k])

theorem central_length_ge (Delta : Nat → Fin d) (k : Nat) :
    k ≤ (central Delta k).length := by
  induction k with
  | zero => simp [central]
  | succ k ih =>
    have h := (palClosure_spec (central Delta k ++ [Delta k])).1.length_le
    simp only [List.length_append, List.length_singleton] at h
    change k + 1 ≤ (palClosure (central Delta k ++ [Delta k])).length
    omega

noncomputable def cDelta (Delta : Nat → Fin d) (n : Nat) : Fin d :=
  (central Delta (n + 1)).get ⟨n, by have h := central_length_ge Delta (n+1); omega⟩

def Lang (x : Nat → Fin d) : Set (List (Fin d)) :=
  {w | ∃ i, ∀ j : Fin w.length, w.get j = x (i + j.val)}

def BoundedPQ (Delta : Nat → Fin d) : Prop :=
  ∃ B, ∀ i, ∃ j < B, Delta (i + j) ≠ Delta i

def fractionalPower (V : List (Fin d)) (hV : V ≠ []) (ell : Nat) : List (Fin d) :=
  (List.range ell).map (fun i => V.get ⟨i % V.length,
    Nat.mod_lt _ (List.length_pos_iff.mpr hV)⟩)

def DioAdmissible (x : Nat → Fin d) (rho : NNReal) : Prop :=
  ∀ L : Nat, ∃ U V : List (Fin d), ∃ ell : Nat, ∃ hV : V ≠ [],
    V.length ≤ ell ∧ U.length + ell ≥ L ∧
    (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) x (U.length + ell) = U ++ fractionalPower V hV ell ∧
    (U.length + ell : Real) / (U.length + V.length) ≥ (rho : Real)

noncomputable def dio (x : Nat → Fin d) : ENNReal :=
  ⨆ (rho : NNReal) (_ : DioAdmissible x rho), (rho : ENNReal)

def claim : Prop := ∀ (d : Nat) (Delta t : Nat → Fin d),
  Lang t = Lang (cDelta Delta) → (¬ ∃ N p, 0 < p ∧ ∀ n ≥ N, t (n+p) = t n) →
    (dio t < ⊤ ↔ BoundedPQ Delta)
end D5.S1.Words.Episturmian.PalindromicClosure
