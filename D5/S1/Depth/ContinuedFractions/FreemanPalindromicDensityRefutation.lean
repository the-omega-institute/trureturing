/- GID: D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation
   generality: G
   mirror-B: D5/B/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Freeman's upper-limsup palindromic-density bound is false. -/

/-
result: proof_shape: content; escape_witness: none.
admission_basis: open-problem-resolution (#22972; Refuted).
Direct frozen dependencies: E, W, WL, WG (declaration identities below).
The finite evaluator, positive digits and complete prefix enumeration follow #22972.
Freeman's Lemmas 3.1–3.2 and section-7 block substitution supply the matrix method.
The integer MobiusInt interface is I-level and lacks the rational evaluator bridge.
The G-level proof uses Matrix (Fin 2) (Fin 2) ℚ and frozen word powers.
The only public theorem is result. Its escape audit is unfinished: https://github.com/the-omega-institute/trureturing/issues/27283.
Utility is none; no basis=refutes exemption is asserted.

Declaration classification (same-delivery helpers are inlined for classification).
Each row has escape_witness: none and the module basis above.
Data definitions below prove no proposition.
name | proof_shape | direct frozen dependencies | consumers
finiteCF | bind-only | none
  consumers: IsFiniteMPalindrome,finiteCF_cons_cons,finiteCF_eq_p_div_u,finiteCF_reverse_eq,finiteCF_mul_reverse_iff
IsFiniteMPalindrome | bind-only | none | PrefixLength
PrefixLength | bind-only | none
  consumers: IsMPalindromic,density,qualifying_pow,qualifying_infinite,witness_density_one
IsMPalindromic | bind-only | none | claim,qualifying_infinite
density | bind-only | none | claim,witness_density_one
claim | bind-only | E | result
finiteCF_cons_cons | bind-only | none | finiteCF_eq_p_div_u
smat | bind-only | none
  consumers: qmatList,qmatList_cons,qmatList_nonneg,qmatList_pos,finiteCF_eq_p_div_u,qmatList_reverse,theta_block,qmatList_pair
qmatList | bind-only | none
  consumers: qmatList_nil,qmatList_cons,qmatList_append,qmatList_nonneg,qmatList_pos,finiteCF_eq_p_div_u,qmatList_reverse,finiteCF_reverse_eq,finiteCF_mul_reverse_iff,qmat_pow_fixed,qmatList_pair,stage_matrix_fixed
qmatList_nil | bind-only | none | qmatList_nonneg,qmatList_pos,finiteCF_eq_p_div_u,qmatList_pair
qmatList_cons | bind-only | none | qmatList_nonneg,qmatList_pos,finiteCF_eq_p_div_u,qmatList_pair
qmatList_append | bind-only | none | stage_matrix_fixed
qmatList_nonneg | content | none | qmatList_pos
qmatList_pos | content | none | finiteCF_eq_p_div_u,finiteCF_mul_reverse_iff
finiteCF_eq_p_div_u | content | none | finiteCF_reverse_eq,finiteCF_mul_reverse_iff
qmatList_reverse | bind-only | none | finiteCF_reverse_eq
finiteCF_reverse_eq | content | none | finiteCF_mul_reverse_iff
finiteCF_mul_reverse_iff | content | none | qualifying_pow
theta | bind-only | none | theta_qmul,theta_block,qmat_pow_fixed,stage_matrix_fixed,qualifying_pow
theta_qmul | bind-only | none | qmat_pow_fixed,stage_matrix_fixed
theta_block | bind-only | none | stage_matrix_fixed
powWord_prefix | bind-only | W | stage_prefix_succ,powWord_get_zero
stage | bind-only | W
  consumers: stage_prefix_succ,stage_prefix,stage_length_lower,limitA,limitA_eq_stage,prefix_limitA,stage_get_zero,stage_length_pos,limitA_block,limitA_six,limitA_four,stage_pos,limitA_aperiodic,stage_matrix_fixed,qualifying_pow,qualifying_infinite,witness_density_one
stage_prefix_succ | bind-only | W | stage_prefix
stage_prefix | bind-only | W | limitA_eq_stage,stage_get_zero
stage_length_lower | content | W,WL | limitA,limitA_eq_stage,stage_get_zero,stage_length_pos
limitA | bind-only | W,WL
  consumers: limitA_eq_stage,prefix_limitA,limitA_block,limitA_six,limitA_four,limitA_pos,limitA_aperiodic,qualifying_pow,qualifying_infinite,witness_density_one,result
limitA_eq_stage | content | W,WL | prefix_limitA,limitA_block
prefix_limitA | content | W,WL | qualifying_pow
powWord_mono | bind-only | W | qualifying_pow
powWord_get_zero | bind-only | W,WL | limitA_four
stage_get_zero | bind-only | W,WL | limitA_four
powWord_two_even | bind-only | WG,W,WL | limitA_six
stage_length_pos | content | W,WL
  consumers: limitA_four,qualifying_pow,qualifying_infinite,witness_density_one
limitA_block | content | W,WL | limitA_six,limitA_four
limitA_six | content | WG,W,WL | limitA_aperiodic
limitA_four | content | W,WL | limitA_aperiodic
powWord_pos | bind-only | W | stage_pos,qualifying_pow
stage_pos | content | W | limitA_pos,qualifying_pow
limitA_pos | content | W,WL | result
limitA_aperiodic | content | WG,W,WL | result
limsup_eq_one_of_frequently | bind-only | none | limsup_nth_ratio_one
nth_successor_bound | bind-only | none | limsup_nth_ratio_one
nth_ratio_bounds | bind-only | none | limsup_nth_ratio_one
infinite_of_large_pairs | bind-only | none | limsup_nth_ratio_one,qualifying_infinite
limsup_nth_ratio_one | content | none | witness_density_one
qmat_pow_fixed | bind-only | W | stage_matrix_fixed,qualifying_pow
qmatList_pair | bind-only | none | stage_matrix_fixed
stage_matrix_fixed | content | W | qualifying_pow
qualifying_pow | content | W,WL | qualifying_infinite,witness_density_one
qualifying_infinite | content | W,WL | result
witness_density_one | content | W,WL | result
result | content | E,WG,W,WL | none

Frozen declaration identities (from the existing scoped report; owner source hashes match):
E: D5/S1/Words/Complexity/MorseHedlund.EventuallyPeriodicWord
  sha256:525fc3b0fd4ae2ac90248f2101965c6987e00c7d4ad1801af52ffae20317dab2
W: D5/S1/Words/Powers/WordPower.wordPower
  sha256:a6e228e7ee6ecdc474ee0b218a6a0c370496359d57e770a78cc40f1991acc416
WL: D5/S1/Words/Powers/WordPower.length_wordPower
  sha256:debf5e4132f97f82101c3032c0cf4922d3f005aae64c4067de34e835705ee5bf
WG: D5/S1/Words/Powers/WordPower.wordPower_getElem?
  sha256:d5429ef122a2fd986008c7f5739d051dd117fca9b6c9d1f25ba2e0df06304a50
-/

import Mathlib.Algebra.ContinuedFractions.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.Real.GoldenRatio
import D5.S1.Words.Complexity.MorseHedlund

import D5.S1.Words.Powers.WordPower

/-! A nested positive word has arbitrarily long clusters of 2-palindromic prefixes. -/

namespace D5.S1.Depth.ContinuedFractions.FreemanPalindromicDensityRefutation

open D5.S1.Words.Powers

/-- Finite regular continued fractions, using Mathlib's existing evaluator.
The empty-list value is a totalization and is excluded from qualifying prefixes. -/
def finiteCF : List ℕ → ℚ
  | [] => 0
  | a :: tail =>
      (⟨(a : ℚ), Stream'.Seq.ofList (tail.map fun b => ⟨1, (b : ℚ)⟩)⟩ :
        GenContFract ℚ).convs' tail.length

/-- The source's reversal is List.reverse; its word lengths are List.length. -/
def IsFiniteMPalindrome (m : ℕ) (U : List ℕ) : Prop :=
  U ≠ [] ∧ (∀ a ∈ U, 0 < a) ∧ finiteCF U = (m : ℚ) * finiteCF U.reverse

def PrefixLength (m : ℕ) (A : ℕ → ℕ) (n : ℕ) : Prop :=
  0 < n ∧ IsFiniteMPalindrome m (List.ofFn fun i : Fin n => A i)

def IsMPalindromic (m : ℕ) (A : ℕ → ℕ) : Prop :=
  Set.Infinite {n : ℕ | PrefixLength m A n}

/-- Mathlib's canonical increasing enumeration; no auxiliary sequence is assumed. -/
noncomputable def density (m : ℕ) (A : ℕ → ℕ) : ℝ :=
  Filter.limsup (fun k : ℕ =>
    (Nat.nth (PrefixLength m A) k : ℝ) / (Nat.nth (PrefixLength m A) (k + 1) : ℝ)) Filter.atTop

/-- Conjecture 7.1, first sentence only. The Fibonacci equality is a separate assertion. -/
def claim : Prop :=
  ∀ m : ℕ, 0 < m → ∀ A : ℕ → ℕ, (∀ n : ℕ, 0 < A n) →
    IsMPalindromic m A →
    ¬ D5.S1.Words.Complexity.EventuallyPeriodicWord A →
    density m A ≤ 1 / Real.goldenRatio


private lemma finiteCF_cons_cons (a b : ℕ) (tail : List ℕ) :
    finiteCF (a :: b :: tail) = (a : ℚ) + 1 / finiteCF (b :: tail) := by
  exact Rat.ext rfl rfl

private def smat (t : ℕ) : Matrix (Fin 2) (Fin 2) ℚ := !![(t : ℚ), 1; 1, 0]

private def qmatList (w : List ℕ) : Matrix (Fin 2) (Fin 2) ℚ := (w.map smat).prod

private theorem qmatList_nil : qmatList [] = 1 := rfl

private theorem qmatList_cons (a : ℕ) (w : List ℕ) :
    qmatList (a :: w) = smat a * qmatList w := rfl

private theorem qmatList_append (xs ys : List ℕ) :
    qmatList (xs ++ ys) = qmatList xs * qmatList ys := by
  simp only [qmatList, List.map_append, List.prod_append]

private theorem qmatList_nonneg (w : List ℕ) :
    0 ≤ (qmatList w) 0 0 ∧ 0 ≤ (qmatList w) 0 1 ∧
    0 ≤ (qmatList w) 1 0 ∧ 0 ≤ (qmatList w) 1 1 := by
  induction w with
  | nil => norm_num [qmatList_nil]
  | cons a tail ih =>
      rcases ih with ⟨hp, hq, hu, hv⟩
      rw [qmatList_cons]
      simpa [smat, Matrix.mul_apply, Fin.sum_univ_two] using
        (show 0 ≤ (a : ℚ) * (qmatList tail) 0 0 + (qmatList tail) 1 0 ∧
          0 ≤ (a : ℚ) * (qmatList tail) 0 1 + (qmatList tail) 1 1 ∧
          0 ≤ (qmatList tail) 0 0 ∧ 0 ≤ (qmatList tail) 0 1 from
          ⟨by positivity, by positivity, hp, hq⟩)

private theorem qmatList_pos (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 0 < a) :
    0 < (qmatList w) 0 0 ∧ 0 < (qmatList w) 0 1 ∧ 0 < (qmatList w) 1 0 := by
  induction w with
  | nil => contradiction
  | cons a tail ih =>
      have ha : 0 < (a : ℚ) := by exact_mod_cast hpos a (by simp)
      cases tail with
      | nil => simpa [qmatList_cons, qmatList_nil, smat, Matrix.mul_apply, Fin.sum_univ_two] using ha
      | cons b tail =>
          have htail : ∀ c ∈ b :: tail, 0 < c := by
            intro c hc
            exact hpos c (List.mem_cons_of_mem a hc)
          rcases ih (by simp) htail with ⟨hp, hq, hu⟩
          have hv := (qmatList_nonneg (b :: tail)).2.2.2
          rw [qmatList_cons]
          simpa [smat, Matrix.mul_apply, Fin.sum_univ_two] using
            (show 0 < (a : ℚ) * (qmatList (b :: tail)) 0 0 + (qmatList (b :: tail)) 1 0 ∧
              0 < (a : ℚ) * (qmatList (b :: tail)) 0 1 + (qmatList (b :: tail)) 1 1 ∧
              0 < (qmatList (b :: tail)) 0 0 from ⟨by positivity, by positivity, hp⟩)

private theorem finiteCF_eq_p_div_u (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 0 < a) :
    finiteCF w = (qmatList w) 0 0 / (qmatList w) 1 0 := by
  cases w with
  | nil => contradiction
  | cons a tail =>
      induction tail generalizing a with
      | nil =>
          simp [finiteCF, GenContFract.convs', GenContFract.convs'Aux, qmatList_cons, qmatList_nil,
            smat, Matrix.mul_apply, Fin.sum_univ_two]
      | cons b tail ih =>
          have htail : b :: tail ≠ [] := List.cons_ne_nil b tail
          have htailpos : ∀ c ∈ b :: tail, 0 < c := by
            intro c hc; exact hpos c (List.mem_cons_of_mem a hc)
          have hp := qmatList_pos (b :: tail) htail htailpos
          have ihtail := ih b htail htailpos
          rw [finiteCF_cons_cons]
          rw [qmatList_cons]
          simp [smat, Matrix.mul_apply, Fin.sum_univ_two]
          rw [ihtail]
          field_simp [ne_of_gt hp.1]

private theorem qmatList_reverse (w : List ℕ) :
    qmatList w.reverse = (qmatList w).transpose := by
  have hs : (w.map smat).map Matrix.transpose = w.map smat := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  simp only [qmatList, Matrix.transpose_list_prod, hs, List.map_reverse]


private theorem finiteCF_reverse_eq (w : List ℕ) (hw : w ≠ []) (hpos : ∀ a ∈ w, 0 < a) :
    finiteCF w.reverse = (qmatList w) 0 0 / (qmatList w) 0 1 := by
  rw [finiteCF_eq_p_div_u w.reverse (by simpa) (by simpa using hpos), qmatList_reverse]
  rfl

private theorem finiteCF_mul_reverse_iff (m : ℕ) (w : List ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 0 < a) :
    finiteCF w = (m : ℚ) * finiteCF w.reverse ↔ (qmatList w) 0 1 = (m : ℚ) * (qmatList w) 1 0 := by
  rcases qmatList_pos w hw hpos with ⟨hp, hq, hu⟩
  rw [finiteCF_eq_p_div_u w hw hpos, finiteCF_reverse_eq w hw hpos]
  constructor <;> intro h
  · field_simp [ne_of_gt hq, ne_of_gt hu] at h
    apply (mul_left_cancel₀ (ne_of_gt hp))
    nlinarith [h]
  · field_simp [ne_of_gt hq, ne_of_gt hu]
    nlinarith


private def theta (m : ℕ) (X : Matrix (Fin 2) (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  Matrix.diagonal ![1, (m : ℚ)⁻¹] * X.transpose * Matrix.diagonal ![1, (m : ℚ)]

private theorem theta_qmul (hm : 0 < m) (X Y : Matrix (Fin 2) (Fin 2) ℚ) :
    theta m (X * Y) = theta m Y * theta m X := by
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [theta, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
    field_simp [hmq]

private theorem theta_block (hm : 0 < m) (t : ℕ) :
    theta m (smat (m * t) * smat t) = smat (m * t) * smat t := by
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [theta, smat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
    field_simp [hmq]

private theorem powWord_prefix {α : Type} (w : List α) (n : Nat) :
    w <+: wordPower (n + 1) w := by
  exact List.prefix_append w (wordPower n w)

private def stage : Nat → List Nat
  | 0 => [4, 2]
  | k + 1 =>
      wordPower (k + 2) (stage k) ++
        wordPower (k + 1) [6, 3] ++
        wordPower (k + 2) (stage k)

private theorem stage_prefix_succ (k : Nat) : stage k <+: stage (k + 1) := by
  simp only [stage]
  exact List.IsPrefix.trans (powWord_prefix (stage k) (k + 1))
    ((List.prefix_append _ _).trans (List.prefix_append _ _))

private theorem stage_prefix {k t : Nat} (h : k ≤ t) : stage k <+: stage t := by
  exact @Nat.rel_of_forall_rel_succ_of_le (List ℕ) List.IsPrefix
    ⟨fun _ => List.prefix_rfl⟩ ⟨fun _ _ _ => List.IsPrefix.trans⟩
    stage stage_prefix_succ k t h

private theorem stage_length_lower (k : Nat) : k + 1 ≤ (stage k).length := by
  induction k with
  | zero => simp [stage]
  | succ k ih =>
      simp [stage, length_wordPower]
      omega

private def limitA (n : Nat) : Nat :=
  (stage (n + 1))[n]'(by have h := stage_length_lower (n + 1); omega)

private theorem limitA_eq_stage (k n : Nat) (hn : n < (stage k).length) :
    limitA n = (stage k)[n]'hn := by
  have h₁ := stage_prefix (Nat.le_max_left k (n + 1))
  have h₂ := stage_prefix (Nat.le_max_right k (n + 1))
  exact (h₂.getElem (by have := stage_length_lower (n + 1); omega)).trans
    (h₁.getElem hn).symm

private theorem prefix_limitA (k : Nat) :
    List.ofFn (fun i : Fin (stage k).length => limitA i) = stage k := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simpa using limitA_eq_stage k i hj

private theorem powWord_mono {α : Type} (w : List α) {a b : Nat} (h : a ≤ b) :
    wordPower a w <+: wordPower b w := by
  apply List.IsPrefix.flatten
  apply List.prefix_replicate_iff.mpr
  simp [h]

private theorem powWord_get_zero {α : Type} (w : List α) (hw : 0 < w.length) (n : Nat) :
    (wordPower (n + 1) w)[0]'(by
      rw [length_wordPower]
      exact Nat.mul_pos (by omega) hw) = w[0]'hw := by
  exact ((powWord_prefix w n).getElem hw).symm

private theorem stage_get_zero (k : Nat) :
    (stage k)[0]'(by have := stage_length_lower k; omega) = 4 := by
  have h := (stage_prefix (Nat.zero_le k)).getElem (i := 0) (by simp [stage])
  simpa [stage] using h.symm

private theorem powWord_two_even (n j : Nat) (hj : j < n) :
    (wordPower n [6, 3])[2 * j]'(by simp [length_wordPower]; omega) = 6 := by
  have h := wordPower_getElem? n [6, 3] (2 * j) (by simp; omega)
  have hsome : (wordPower n [6, 3])[2 * j]? = some 6 := by
    simpa using h
  exact (List.getElem?_eq_some_iff.mp hsome).choose_spec


private theorem stage_length_pos (k : Nat) : 0 < (stage k).length := by
  have := stage_length_lower k
  omega

private theorem limitA_block (k : Nat) (xs w ys : List Nat)
    (h : stage k = xs ++ (w ++ ys)) (i : Nat) (hi : i < w.length) :
    limitA (xs.length + i) = w[i] := by
  rw [limitA_eq_stage k (xs.length + i) (by rw [h]; simp only [List.length_append]; omega)]
  simp only [h]
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact List.getElem_append_left hi

private theorem limitA_six (k j : Nat) (hj : j < k + 1) :
    limitA ((k + 2) * (stage k).length + 2 * j) = 6 := by
  have h := limitA_block (k + 1) (wordPower (k + 2) (stage k))
    (wordPower (k + 1) [6, 3]) (wordPower (k + 2) (stage k))
    (by simp only [stage, List.append_assoc]) (2 * j) (by simp [length_wordPower]; omega)
  simpa only [length_wordPower] using h.trans (powWord_two_even (k + 1) j hj)

private theorem limitA_four (k : Nat) :
    limitA ((k + 2) * (stage k).length + 2 * (k + 1)) = 4 := by
  have h := limitA_block (k + 1)
    (wordPower (k + 2) (stage k) ++ wordPower (k + 1) [6, 3])
    (wordPower (k + 2) (stage k)) [] (by simp [stage]) 0
    (by rw [length_wordPower]; exact Nat.mul_pos (by omega) (stage_length_pos k))
  have hz := powWord_get_zero (stage k) (stage_length_pos k) (k + 1)
  have hh := h.trans (hz.trans (stage_get_zero k))
  simpa [List.length_append, length_wordPower, Nat.mul_comm] using hh

private theorem powWord_pos (w : List Nat) (n : Nat) (hw : ∀ a ∈ w, 0 < a) :
    ∀ a ∈ wordPower n w, 0 < a := by
  intro a ha
  obtain ⟨v, hv, ha⟩ := List.mem_flatten.mp ha
  have hvw : v = w := (List.mem_replicate.mp hv).2
  subst v
  exact hw a ha


private theorem stage_pos (k : Nat) : ∀ a ∈ stage k, 0 < a := by
  induction k with
  | zero => simp [stage]
  | succ k ih =>
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · exact powWord_pos _ _ ih a ha
        · exact powWord_pos _ _ (by simp) a ha
      · exact powWord_pos _ _ ih a ha

private theorem limitA_pos (n : Nat) : 0 < limitA n := by
  exact stage_pos (n + 1) _ (List.getElem_mem _)

private theorem limitA_aperiodic :
    ¬ (∃ s p : Nat, 0 < p ∧ ∀ t, limitA (s + t + p) = limitA (s + t)) := by
  rintro ⟨s, p, hp, hper⟩
  let k := s + p
  let b := (k + 2) * (stage k).length
  let q := b + s + 2
  have h6 := limitA_six k (s + 1) (by dsimp [k]; omega)
  have h4 := limitA_four k
  have hper2 : limitA (s + q + 2 * p) = limitA (s + q) := by
    calc
      limitA (s + q + 2 * p) = limitA (s + (q + p) + p) := by congr 1; omega
      _ = limitA (s + (q + p)) := hper (q + p)
      _ = limitA (s + q + p) := by congr 1; omega
      _ = limitA (s + q) := hper q
  have hi : s + q + 2 * p = (k + 2) * (stage k).length + 2 * (k + 1) := by dsimp [k,q,b]; omega
  have hj : s + q = (k + 2) * (stage k).length + 2 * (s + 1) := by dsimp [q,b]; omega
  rw [hi,hj,h4,h6] at hper2
  norm_num at hper2


/-- A generic limsup envelope: frequent values arbitrarily close to one force limsup one. -/
private theorem limsup_eq_one_of_frequently
    (u : ℕ → ℝ)
    (hlo : ∀ n, 0 ≤ u n)
    (hhi : ∀ n, u n ≤ 1)
    (hfreq : ∀ c : ℝ, c < 1 → ∃ᶠ n in Filter.atTop, c ≤ u n) :
    Filter.limsup u Filter.atTop = 1 := by
  have hco := Filter.isCoboundedUnder_le_of_le Filter.atTop hlo
  have hbound : Filter.IsBoundedUnder (fun x y : ℝ => x ≤ y) Filter.atTop u := by
    change ∃ b : ℝ, ∀ᶠ n in Filter.atTop, u n ≤ b
    exact ⟨1, Filter.Eventually.of_forall hhi⟩
  exact le_antisymm
    (Filter.limsup_le_of_le hco (Filter.Eventually.of_forall hhi))
    ((Filter.le_limsup_iff' hco hbound).mpr hfreq)


private lemma nth_successor_bound (P : ℕ → Prop) [DecidablePred P] (hP : Set.Infinite {n | P n})
    (t t' : ℕ) (ht : P t) (ht' : P t') (hlt : t < t') :
    Nat.nth P (Nat.count P t + 1) ≤ t' := by
  classical
  apply (Nat.nth_add_one_le_iff hP ht').mpr
  simpa only [Nat.nth_count ht] using hlt

private lemma nth_ratio_bounds (P : ℕ → Prop) (hP : Set.Infinite {n | P n})
    (hpos : ∀ n, P n → 0 < n) (i : ℕ) :
    0 ≤ (Nat.nth P i : ℝ) / Nat.nth P (i + 1) ∧
    (Nat.nth P i : ℝ) / Nat.nth P (i + 1) ≤ 1 := by
  have hden : 0 < (Nat.nth P (i + 1) : ℝ) := by
    exact_mod_cast hpos _ (Nat.nth_mem_of_infinite hP (i + 1))
  constructor
  · positivity
  · apply (div_le_one hden).mpr
    exact_mod_cast (Nat.nth_strictMono hP).monotone (Nat.le_succ i)

private lemma infinite_of_large_pairs (P : ℕ → Prop) (T : ℕ → ℕ)
    (hmem : ∀ k, P (T k)) (hlarge : ∀ k, k + 1 ≤ T k) :
    Set.Infinite {n | P n} := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  exact ⟨T n, hmem n, hlarge n⟩

private lemma limsup_nth_ratio_one (P : ℕ → Prop) (T T' : ℕ → ℕ)
    (hmem : ∀ k, P (T k)) (hmem' : ∀ k, P (T' k))
    (hlarge : ∀ k, k + 1 ≤ T k) (hlt : ∀ k, T k < T' k)
    (hpos : ∀ n, P n → 0 < n)
    (hratio : ∀ c : ℝ, c < 1 → ∃ K : ℕ, ∀ k, K ≤ k → c ≤ (T k : ℝ) / T' k) :
    Filter.limsup (fun i : ℕ => (Nat.nth P i : ℝ) / Nat.nth P (i + 1)) Filter.atTop = 1 := by
  classical
  have hP := infinite_of_large_pairs P T hmem hlarge
  apply limsup_eq_one_of_frequently
  · intro i; exact (nth_ratio_bounds P hP hpos i).1
  · intro i; exact (nth_ratio_bounds P hP hpos i).2
  · intro c hc
    obtain ⟨K, hK⟩ := hratio c hc
    rw [Filter.frequently_atTop]
    intro N
    let k := max K (Nat.nth P N + 1)
    let i := Nat.count P (T k)
    have hindex : N ≤ i := by
      apply (Nat.nth_le_nth hP).mp
      rw [Nat.nth_count (hmem k)]
      change Nat.nth P N ≤ T k
      have hk0 : Nat.nth P N < k := by
        have := Nat.le_max_right K (Nat.nth P N + 1)
        dsimp [k]
        omega
      exact hk0.le.trans (Nat.le_of_lt (hlarge k))
    refine ⟨i, hindex, ?_⟩
    have hnext := nth_successor_bound P hP (T k) (T' k) (hmem k) (hmem' k) (hlt k)
    have hd : 0 < (Nat.nth P (i + 1) : ℝ) := by
      exact_mod_cast hpos _ (Nat.nth_mem_of_infinite hP (i + 1))
    have hnextR : (Nat.nth P (i + 1) : ℝ) ≤ T' k := Nat.cast_le.mpr hnext
    have hlo := hK k (Nat.le_max_left _ _)
    have hquot : (T k : ℝ) / T' k ≤ (T k : ℝ) / Nat.nth P (i + 1) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd hnextR
    exact hlo.trans (by simpa only [i, Nat.nth_count (hmem k)] using hquot)


private lemma qmat_pow_fixed (m : ℕ) (hm : 0 < m) (w : List ℕ)
    (hw : theta m (qmatList w) = qmatList w) (n : ℕ) :
    theta m (qmatList (wordPower n w)) = qmatList (wordPower n w) := by
  have hprod : qmatList (wordPower n w) = qmatList w ^ n := by
    simp [qmatList, wordPower, List.map_flatten, List.prod_flatten, List.map_replicate]
  rw [hprod]
  clear hprod
  induction n with
  | zero =>
      have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
      ext i j
      fin_cases i <;> fin_cases j <;> simp [theta, hmq]
  | succ n ih =>
      rw [pow_succ, theta_qmul hm, ih, hw]
      exact (pow_succ' (qmatList w) n).symm.trans (pow_succ (qmatList w) n)

private lemma qmatList_pair (a b : ℕ) : qmatList [a,b] = (· * ·) (smat a) (smat b) := by
  simp only [qmatList_cons, qmatList_nil, mul_one]

private lemma stage_matrix_fixed (k : ℕ) : theta 2 (qmatList (stage k)) = qmatList (stage k) := by
  induction k with
  | zero => simpa only [stage, qmatList_pair] using theta_block (by decide) 2
  | succ k ih =>
      have hR := qmat_pow_fixed 2 (by decide) (stage k) ih (k + 2)
      have hB := qmat_pow_fixed 2 (by decide) [6, 3]
        (by simpa only [qmatList_pair] using theta_block (by decide) 3) (k + 1)
      simp only [stage, qmatList_append, theta_qmul (by decide : 0 < 2), hR, hB]
      exact (mul_assoc _ _ _).symm

private lemma qualifying_pow (k j : ℕ) (hj : 0 < j) (hjk : j ≤ k + 2) :
    PrefixLength 2 limitA (j * (stage k).length) := by
  let w := wordPower j (stage k)
  have hpre : w <+: stage (k + 1) := by
    change w <+: ((wordPower (k + 2) (stage k) ++ wordPower (k + 1) [6, 3]) ++
      wordPower (k + 2) (stage k))
    exact (powWord_mono (stage k) hjk).trans
      ((List.prefix_append _ _).trans (List.prefix_append _ _))
  have hlen : w.length = j * (stage k).length := length_wordPower _ _
  have hlenpos : 0 < w.length := by rw [hlen]; exact Nat.mul_pos hj (stage_length_pos k)
  have hprefix : List.ofFn (fun i : Fin w.length => limitA i) = w := by
    apply List.ext_getElem
    · simp [List.length_ofFn]
    · intro i hi hj'
      have ht := List.getElem_of_eq (prefix_limitA (k + 1)) (i := i)
        (by simpa using (Nat.lt_of_lt_of_le hj' hpre.length_le))
      have hw := hpre.getElem hj'
      simpa [List.length_ofFn] using ht.trans hw.symm
  rw [← hlen]
  refine ⟨hlenpos, ?_⟩
  rw [hprefix]
  have hne : w ≠ [] := List.ne_nil_of_length_pos hlenpos
  have hpos := powWord_pos (stage k) j (stage_pos k)
  refine ⟨hne, hpos, ?_⟩
  apply (finiteCF_mul_reverse_iff 2 w hne hpos).mpr
  have hfix := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℚ => X 0 1)
    (qmat_pow_fixed 2 (by decide) (stage k) (stage_matrix_fixed k) j)
  simpa [theta, w, mul_comm] using hfix.symm

private lemma qualifying_infinite : IsMPalindromic 2 limitA := by
  apply infinite_of_large_pairs (PrefixLength 2 limitA) (fun k => (k + 1) * (stage k).length)
  · intro k
    exact qualifying_pow k (k + 1) (by omega) (by omega)
  · intro k
    exact Nat.le_mul_of_pos_right _ (stage_length_pos k)

private lemma witness_density_one : density 2 limitA = 1 := by
  apply limsup_nth_ratio_one (PrefixLength 2 limitA)
    (fun k => (k + 1) * (stage k).length) (fun k => (k + 2) * (stage k).length)
  · intro k; exact qualifying_pow k (k + 1) (by omega) (by omega)
  · intro k; exact qualifying_pow k (k + 2) (by omega) (by omega)
  · intro k; exact Nat.le_mul_of_pos_right _ (stage_length_pos k)
  · intro k
    exact Nat.mul_lt_mul_of_pos_right (by omega) (stage_length_pos k)
  · intro n hn; exact hn.1
  · intro c hc
    obtain ⟨K, hK⟩ := exists_nat_gt (1/(1-c))
    refine ⟨K, ?_⟩
    intro k hk
    have hK' : (K : ℝ) ≤ k := Nat.cast_le.mpr hk
    have hbase : (1:ℝ) < K * (1-c) := (div_lt_iff₀ (by linarith : 0 < 1-c)).mp hK
    have hlinear : c * ((k:ℝ) + 2) ≤ (k:ℝ) + 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hK') (by linarith : 0 ≤ 1-c)]
    have hL : 0 < ((stage k).length : ℝ) := by exact_mod_cast stage_length_pos k
    have hd : 0 < (((k + 2) * (stage k).length : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_pos (by omega : 0 < k + 2) (stage_length_pos k))
    apply (le_div_iff₀ hd).mpr
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hlinear hL.le]


theorem result : ¬ claim := by
  intro hclaim
  have haper : ¬ D5.S1.Words.Complexity.EventuallyPeriodicWord limitA := limitA_aperiodic
  have hu := hclaim 2 (by decide) limitA limitA_pos qualifying_infinite haper
  rw [witness_density_one] at hu
  have hphi : 1 / Real.goldenRatio < 1 := by
    simpa only [one_div] using inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  linarith


end D5.S1.Depth.ContinuedFractions.FreemanPalindromicDensityRefutation
