/- GID: D5/S1/Words/Episturmian/MorphicDecomposition
   generality: G
   mirror-B: D5/B/S1/Words/Episturmian/MorphicDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Justin morphic decomposition and finite central prefixes -/

/- escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin
   admission_basis: escape-witness
   Declarations:
   proof_shape: extension_exists: bind-only; consumer: MorphicDecomposition.palClosure
   definition: palClosure; consumer: MorphicDecomposition.palClosure_spec
   proof_shape: palClosure_spec: bind-only; consumer: MorphicDecomposition.palClosure_formula_cut
   proof_shape: suffix_cut_exists: bind-only; consumer: MorphicDecomposition.palCut
   definition: palCut; consumer: MorphicDecomposition.palCut_spec
   proof_shape: palCut_spec: bind-only; consumer: MorphicDecomposition.palindrome_extension_length
   proof_shape: palCut_min: bind-only; consumer: MorphicDecomposition.palindrome_extension_length
   proof_shape: palindrome_extension_middle: bind-only; consumer: MorphicDecomposition.palindrome_extension_length
   proof_shape: palindrome_extension_length: bind-only; consumer: MorphicDecomposition.palClosure_formula_cut
   proof_shape: closure_candidate_palindrome: bind-only; consumer: MorphicDecomposition.palClosure_formula_cut
   proof_shape: palClosure_formula_cut: bind-only; consumer: MorphicDecomposition.Hword_palClosure
   definition: central; consumer: MorphicDecomposition.central_length_ge
   proof_shape: central_length_ge: bind-only; consumer: MorphicDecomposition.cDelta
   definition: cDelta; consumer: MorphicDecomposition.claim
   definition: Lang; consumer: MorphicDecomposition.claim
   definition: BoundedPQ; consumer: MorphicDecomposition.claim
   definition: fractionalPower; consumer: MorphicDecomposition.DioAdmissible
   definition: DioAdmissible; consumer: MorphicDecomposition.dio
   definition: dio; consumer: MorphicDecomposition.claim
   definition: claim; consumer: DiophantineExponentCriterion.result
   proof_shape: central_prefix_succ: bind-only; consumer: MorphicDecomposition.central_prefix_of_le
   proof_shape: central_prefix_of_le: bind-only; consumer: MorphicDecomposition.central_get_eq_cDelta
   proof_shape: central_get_eq_cDelta: bind-only; consumer: MorphicDecomposition.central_is_cDelta_prefix
   proof_shape: central_is_cDelta_prefix: bind-only; consumer: MorphicDecomposition.cDelta_morphicImage
   definition: letterImage; consumer: MorphicDecomposition.mu
   definition: mu; consumer: MorphicDecomposition.mu_length_step
   proof_shape: mu_length_step: bind-only; consumer: MorphicDecomposition.mu_length_mono
   proof_shape: mu_length_mono: bind-only; consumer: MorphicDecomposition.mu_length_pos, BoundedPowers.mu_length_increases_over_B
   proof_shape: mu_length_pos: bind-only; consumer: BoundedPowers.cDelta_constant_run_cover
   proof_shape: mu_length_triangle: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.mu_length_triangle; consumer: MorphicDecomposition.mu_length_at_run_start
   proof_shape: mu_length_at_run_start: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.mu_length_triangle; consumer: BoundedPowers.cDelta_constant_run_cover
   proof_shape: mu_constant_run: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.mu_constant_run; consumer: BoundedPowers.cDelta_constant_run_cover
   definition: Lword; consumer: MorphicDecomposition.Hword
   definition: Hword; consumer: MorphicDecomposition.Hword_reverse
   proof_shape: letterImage_conjugacy: bind-only; consumer: MorphicDecomposition.Hword_reverse
   proof_shape: Hword_reverse: bind-only; consumer: MorphicDecomposition.Hword_palindrome_iff
   proof_shape: Hword_starts: bind-only; consumer: MorphicDecomposition.Hword_injective
   proof_shape: Hword_cons: bind-only; consumer: MorphicDecomposition.Hword_injective
   proof_shape: Hword_injective: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.Hword_injective; consumer: MorphicDecomposition.Hword_palindrome_iff
   proof_shape: Hword_palindrome_iff: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.Hword_injective; consumer: MorphicDecomposition.Hword_palCut
   proof_shape: Lword_append: bind-only; consumer: MorphicDecomposition.Hword_palCut
   proof_shape: Lword_prefix: bind-only; consumer: MorphicDecomposition.Hword_palCut
   proof_shape: Hword_suffix_decode: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.Hword_suffix_decode; consumer: MorphicDecomposition.Hword_palCut
   proof_shape: palindrome_suffix_last_starts: bind-only; consumer: MorphicDecomposition.Lword_palClosure
   proof_shape: palindrome_suffix_Hword_starts: bind-only; consumer: MorphicDecomposition.Hword_palCut
   proof_shape: Hword_palCut: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.Hword_injective; consumer: MorphicDecomposition.Hword_palClosure
   proof_shape: Hword_palClosure: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.Hword_injective; consumer: MorphicDecomposition.Lword_palClosure
   proof_shape: Lword_suffix_nonx: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.Lword_suffix_nonx; consumer: MorphicDecomposition.Lword_palClosure
   proof_shape: palCut_le_of_suffix: bind-only; consumer: MorphicDecomposition.Lword_palClosure
   proof_shape: Lword_palClosure: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.Hword_injective; consumer: MorphicDecomposition.Hword_append_letter_closure
   proof_shape: palClosure_of_palindrome: bind-only; consumer: MorphicDecomposition.central_Justin
   proof_shape: Hword_append_letter_closure: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.Hword_injective; consumer: MorphicDecomposition.central_Justin
   proof_shape: central_Justin: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin; consumer: MorphicDecomposition.central_Justin_shift
   proof_shape: central_Justin_shift: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin; consumer: MorphicDecomposition.central_morphic_finite
   definition: muWord; consumer: MorphicDecomposition.central_morphic_finite
   proof_shape: mu_shift: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.mu_shift; consumer: MorphicDecomposition.central_morphic_finite
   proof_shape: central_morphic_finite: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin; consumer: MorphicDecomposition.cDelta_morphicImage
   definition: MorphicImage; consumer: MorphicDecomposition.cDelta_morphicImage
   proof_shape: wordPrefix_isPrefix: bind-only; consumer: MorphicDecomposition.cDelta_morphicImage
   proof_shape: cDelta_morphicImage: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin; consumer: BoundedPowers.cDelta_constant_run_cover
   definition: HasPeriodOn; consumer: MorphicDecomposition.periodic_interval_mod
   proof_shape: wordPrefix_length: bind-only; consumer: MorphicDecomposition.periodic_interval_mod
   proof_shape: periodic_interval_mod: bind-only; consumer: MorphicDecomposition.periodic_interval_prefix
   proof_shape: periodic_interval_prefix: bind-only; consumer: MorphicDecomposition.uniform_finite_window
   proof_shape: wordPrefix_append: bind-only; consumer: MorphicDecomposition.uniform_finite_window
   definition: PeriodicRunCover; consumer: MorphicDecomposition.run_cover_near_period
   proof_shape: run_cover_near_period: bind-only; consumer: MorphicDecomposition.uniform_finite_window
   proof_shape: uniform_finite_window: bind-only; consumer: BoundedPowers.uniform_window_transfer
   proof_shape: wordPower_add: bind-only; consumer: BoundedPowers.powerChunk_exists
   proof_shape: wordPower_period: bind-only; consumer: BoundedPowers.powerChunks_cover
   proof_shape: wordPrefix_constant: bind-only; consumer: BoundedPowers.powerChunk_exists
   Direct frozen dependencies (pre-existing): D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs; D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor; sha256:54f2f8a1cd3a83f896d4018ef9821e5aa1b6046bd757ec6a999734a691651d1c | D5/S1/Words/Powers/WordPower; D5.S1.Words.Powers.wordPower; sha256:a6e228e7ee6ecdc474ee0b218a6a0c370496359d57e770a78cc40f1991acc416 | D5/S1/Words/Powers/WordPower; D5.S1.Words.Powers.wordPower_succ; sha256:2555a0f5d0c0ce76d62ea9dc70d6f8b1554ec0d5a37821080b16cbaabc5c2b5d | D5/S1/Words/Powers/WordPower; D5.S1.Words.Powers.length_wordPower; sha256:debf5e4132f97f82101c3032c0cf4922d3f005aae64c4067de34e835705ee5bf | D5/S1/Words/Powers/WordPower; D5.S1.Words.Powers.wordPower_period_getElem?; sha256:d9c6a06ea421449d240a7406ecf38761aeedd1293e31e9ba625eece0556d16cd
   Finite prefixes use the existing factor operator at start zero.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16158
-/

import D5.S1.Words.MBonacciSentinelDesubstitution
import D5.S1.Words.Powers.WordPower
import Mathlib.Data.List.Palindrome
import Mathlib.Data.List.PeriodicityLemma

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Episturmian.MorphicDecomposition
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

theorem central_prefix_succ (Delta : Nat → Fin d) (k : Nat) :
    central Delta k <+: central Delta (k+1) := by
  exact (List.prefix_append _ _).trans (palClosure_spec (central Delta k ++ [Delta k])).1

theorem central_prefix_of_le (Delta : Nat → Fin d) {k m : Nat} (h : k ≤ m) :
    central Delta k <+: central Delta m := by
  induction m with
  | zero =>
    have hk : k = 0 := by omega
    subst k
    exact List.prefix_refl _
  | succ m ih =>
    by_cases hkm : k ≤ m
    · exact (ih hkm).trans (central_prefix_succ Delta m)
    · have hk : k = m+1 := by omega
      subst k
      exact List.prefix_refl _

theorem central_get_eq_cDelta (Delta : Nat → Fin d) (k i : Nat)
    (hi : i < (central Delta k).length) : (central Delta k)[i] = cDelta Delta i := by
  unfold cDelta
  simp only [List.get_eq_getElem]
  by_cases hk : k ≤ i+1
  · exact (central_prefix_of_le Delta hk).getElem hi
  · have hh : i < (central Delta (i+1)).length := by have := central_length_ge Delta (i+1); omega
    exact ((central_prefix_of_le Delta (by omega : i+1 ≤ k)).getElem hh).symm

theorem central_is_cDelta_prefix (Delta : Nat → Fin d) (k : Nat) :
    (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (cDelta Delta) (central Delta k).length = central Delta k := by
  apply List.ext_getElem
  · simp [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add]
  · intro i hi hj
    simp only [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add, List.getElem_map, List.getElem_range]
    exact (central_get_eq_cDelta Delta k i hj).symm

def letterImage (x z : Fin d) : List (Fin d) :=
  if z = x then [x] else [x, z]

def mu (Delta : Nat → Fin d) : Nat → Fin d → List (Fin d)
  | 0, z => [z]
  | n + 1, z => (letterImage (Delta n) z).flatMap (mu Delta n)

theorem mu_length_step (Delta : Nat → Fin d) (n : Nat) (z : Fin d) :
    (mu Delta (n+1) z).length =
      if z = Delta n then (mu Delta n z).length
      else (mu Delta n (Delta n)).length + (mu Delta n z).length := by
  by_cases h : z = Delta n
  · simp [mu, letterImage, h]
  · simp [mu, letterImage, h]

 theorem mu_length_mono (Delta : Nat → Fin d) (z : Fin d) {n m : Nat} (hnm : n ≤ m) :
    (mu Delta n z).length ≤ (mu Delta m z).length := by
  apply (monotone_nat_of_le_succ (f := fun k => (mu Delta k z).length) _) hnm
  intro k
  rw [mu_length_step]
  split_ifs <;> omega

theorem mu_length_pos (Delta : Nat → Fin d) (n : Nat) (z : Fin d) :
    0 < (mu Delta n z).length := by
  have h := mu_length_mono Delta z (Nat.zero_le n)
  exact lt_of_lt_of_le (by decide : 0 < 1)
    (by simpa only [mu, List.length_singleton] using h)

theorem mu_length_triangle (Delta : Nat → Fin d) (n : Nat)
    (u v z : Fin d) (huv : u ≠ v) :
    (mu Delta n z).length ≤ (mu Delta n u).length + (mu Delta n v).length := by
  induction n with
  | zero => simp [mu]
  | succ n ih =>
    rw [mu_length_step, mu_length_step, mu_length_step]
    split_ifs <;> simp_all <;> omega

theorem mu_length_at_run_start (Delta : Nat → Fin d) (n : Nat)
    (hstart : n = 0 ∨ Delta (n-1) ≠ Delta n) (z : Fin d) :
    (mu Delta n z).length ≤ 2 * (mu Delta n (Delta n)).length := by
  cases n with
  | zero => simp [mu]
  | succ n =>
    have hyx : Delta n ≠ Delta (n+1) := by simpa using hstart
    have htri := mu_length_triangle Delta (n+1) (Delta (n+1)) (Delta n) z hyx.symm
    have hy : (mu Delta (n+1) (Delta n)).length ≤
        (mu Delta (n+1) (Delta (n+1))).length := by
      rw [mu_length_step, mu_length_step]
      simp [hyx.symm]
    omega

theorem mu_constant_run (Delta : Nat → Fin d) (n a : Nat) (x z : Fin d)
    (hconst : ∀ i < a, Delta (n+i) = x) :
    mu Delta (n+a) z =
      if z = x then mu Delta n x else (fun A a => D5.S1.Words.Powers.wordPower a A) (mu Delta n x) a ++ mu Delta n z := by
  induction a generalizing z with
  | zero => by_cases h : z = x <;> simp [D5.S1.Words.Powers.wordPower, h]
  | succ a ih =>
    have hpre : ∀ i < a, Delta (n+i) = x := by intro i hi; exact hconst i (by omega)
    have hlast : Delta (n+a) = x := hconst a (by omega)
    have hx := ih z hpre
    have hx' := ih x hpre
    rw [show n+(a+1) = n+a+1 by omega, mu, hlast]
    by_cases hz : z = x
    · subst z
      simp only [letterImage, if_pos rfl, List.flatMap_singleton]
      simpa using hx
    · simp only [letterImage, if_neg hz, List.flatMap_cons, List.flatMap_singleton, List.flatMap_nil, List.append_nil]
      rw [hx, if_neg hz]
      simp only [ite_true] at hx'
      rw [hx', D5.S1.Words.Powers.wordPower_succ, List.append_assoc]

def Lword (x : Fin d) (w : List (Fin d)) : List (Fin d) := w.flatMap (letterImage x)

def Hword (x : Fin d) (w : List (Fin d)) : List (Fin d) := Lword x w ++ [x]

theorem letterImage_conjugacy (x z : Fin d) :
    [x] ++ (letterImage x z).reverse = letterImage x z ++ [x] := by
  by_cases h : z = x <;> simp [letterImage, h]

theorem Hword_reverse (x : Fin d) (w : List (Fin d)) :
    (Hword x w).reverse = Hword x w.reverse := by
  let R : FreeMonoid (Fin d) → FreeMonoid (Fin d) → Prop :=
    fun a b => [x] ++ a.toList = b.toList ++ [x]
  have h := List.prod_hom_rel w.reverse
    (r := R)
    (f := fun z => FreeMonoid.ofList (letterImage x z).reverse)
    (g := fun z => FreeMonoid.ofList (letterImage x z))
    (by simp [R])
    (by
      intro z a b hab
      change [x] ++ (letterImage x z).reverse ++ a.toList =
        letterImage x z ++ b.toList ++ [x]
      rw [letterImage_conjugacy, List.append_assoc, hab]
      simp [List.append_assoc])
  simpa [R, Hword, Lword, FreeMonoid.toList_prod, List.map_map,
    Function.comp_def, List.flatMap_def, List.reverse_flatten, List.map_reverse] using h

theorem Hword_starts (x : Fin d) (w : List (Fin d)) : ∃ r, Hword x w = x :: r := by
  cases w with
  | nil => exact ⟨[], by simp [Hword, Lword]⟩
  | cons z w => by_cases hz : z = x <;> simp [Hword, Lword, letterImage, hz]

theorem Hword_cons (x z : Fin d) (w : List (Fin d)) :
    Hword x (z::w) = if z = x then x :: Hword x w else x :: z :: Hword x w := by
  by_cases hz : z = x <;> simp [Hword, Lword, letterImage, hz]

theorem Hword_injective (x : Fin d) : Function.Injective (Hword x) := by
  intro u
  induction u with
  | nil =>
    intro v he
    cases v with
    | nil => rfl
    | cons z v =>
      rw [Hword_cons] at he
      have h0 : Hword x [] = [x] := by simp [Hword, Lword]
      rw [h0] at he
      split_ifs at he <;> simp [Hword, Lword] at he
  | cons z u ih =>
    intro v he
    cases v with
    | nil =>
      have hlen := congrArg List.length he
      rw [Hword_cons] at hlen
      split_ifs at hlen <;> simp [Hword, Lword] at hlen <;> omega
    | cons y v =>
      rw [Hword_cons, Hword_cons] at he
      by_cases hz : z = x
      · by_cases hy : y = x
        · simp only [if_pos hz, if_pos hy, List.cons.injEq, true_and] at he
          have huv := ih he
          simp [hz, hy, huv]
        · simp only [if_pos hz, if_neg hy, List.cons.injEq, true_and] at he
          obtain ⟨r, hr⟩ := Hword_starts x u
          rw [hr] at he
          have hxy := (List.cons.inj he).1
          exact (hy hxy.symm).elim
      · by_cases hy : y = x
        · simp only [if_neg hz, if_pos hy, List.cons.injEq, true_and] at he
          obtain ⟨r, hr⟩ := Hword_starts x v
          rw [hr] at he
          have hzx := (List.cons.inj he).1
          exact (hz hzx).elim
        · simp only [if_neg hz, if_neg hy, List.cons.injEq, true_and] at he
          exact congrArg₂ List.cons he.1 (ih he.2)

theorem Hword_palindrome_iff (x : Fin d) (w : List (Fin d)) :
    List.Palindrome (Hword x w) ↔ List.Palindrome w := by
  rw [List.Palindrome.iff_reverse_eq, Hword_reverse, List.Palindrome.iff_reverse_eq]
  exact ⟨fun h => Hword_injective x h, fun h => congrArg (Hword x) h⟩

theorem Lword_append (x : Fin d) (u v : List (Fin d)) :
    Lword x (u++v) = Lword x u ++ Lword x v := by simp [Lword]

theorem Lword_prefix (x : Fin d) {u w : List (Fin d)} (h : u <+: w) :
    Lword x u <+: Lword x w := by
  exact h.flatMap (letterImage x)

theorem Hword_suffix_decode (x : Fin d) (w s : List (Fin d))
    (hs : s <:+ Hword x w) (hstart : ∃ r, s = x :: r) :
    ∃ v, v <:+ w ∧ s = Hword x v := by
  induction w with
  | nil =>
    obtain ⟨r, rfl⟩ := hstart
    have hl := hs.length_le
    simp [Hword, Lword] at hl
    subst r
    exact ⟨[], List.suffix_refl _, by simp [Hword, Lword]⟩
  | cons z w ih =>
    by_cases hz : z = x
    · rw [Hword_cons, if_pos hz, List.suffix_cons_iff] at hs
      rcases hs with he | hs
      · exact ⟨z::w, List.suffix_refl _, by simpa only [Hword_cons, if_pos hz] using he⟩
      · obtain ⟨v, hv, he⟩ := ih hs
        exact ⟨v, hv.trans (List.suffix_cons z w), he⟩
    · rw [Hword_cons, if_neg hz, List.suffix_cons_iff] at hs
      rcases hs with he | hs
      · exact ⟨z::w, List.suffix_refl _, by simpa only [Hword_cons, if_neg hz] using he⟩
      · rw [List.suffix_cons_iff] at hs
        rcases hs with he | hs
        · obtain ⟨r, hr⟩ := hstart
          have hxz : x = z := (List.cons.inj (hr.symm.trans he)).1
          exact (hz hxz.symm).elim
        · obtain ⟨v, hv, he⟩ := ih hs
          exact ⟨v, hv.trans (List.suffix_cons z w), he⟩

theorem palindrome_suffix_last_starts (z : Fin d) (p s : List (Fin d))
    (hs : s <:+ p++[z]) (hp : List.Palindrome s) (hne : s ≠ []) :
    ∃ r, s = z::r := by
  have hh := hs.reverse
  rw [hp.reverse_eq, List.reverse_append] at hh
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    List.prefix_cons_iff] at hh
  rcases hh with hn | ⟨r, hr, hpre⟩
  · exact (hne hn).elim
  · exact ⟨r, hr⟩

theorem palindrome_suffix_Hword_starts (x : Fin d) (w s : List (Fin d))
    (hs : s <:+ Hword x w) (hpal : List.Palindrome s) (hne : s ≠ []) :
    ∃ r, s = x :: r := by
  exact palindrome_suffix_last_starts x (Lword x w) s hs hpal hne

theorem Hword_palCut (x : Fin d) (w : List (Fin d)) :
    palCut (Hword x w) = (Lword x (w.take (palCut w))).length := by
  let p := w.take (palCut w)
  let v := w.drop (palCut w)
  have hsplit : Hword x w = Lword x p ++ Hword x v := by
    change Lword x w ++ [x] = Lword x p ++ (Lword x v ++ [x])
    rw [← List.append_assoc, ← Lword_append]
    congr 2
    exact (List.take_append_drop _ _).symm
  have hupper : palCut (Hword x w) ≤ (Lword x p).length := by
    apply palCut_min
    · rw [hsplit, List.length_append]; omega
    · rw [hsplit, List.drop_left]
      exact (Hword_palindrome_iff x v).mpr (palCut_spec w).2
  let c := palCut (Hword x w)
  let S := (Hword x w).drop c
  have hshort : c ≤ (Lword x w).length := by
    apply palCut_min
    · simp [Hword]
    · simp only [Hword, List.drop_left]
      exact List.Palindrome.singleton x
  have hne : S ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [S, List.length_drop, Hword, List.length_append, List.length_singleton,
      List.length_nil] at hl
    omega
  have hs : S <:+ Hword x w := List.drop_suffix _ _
  have hp : List.Palindrome S := (palCut_spec (Hword x w)).2
  have hstart := palindrome_suffix_Hword_starts x w S hs hp hne
  obtain ⟨s, hsw, he⟩ := Hword_suffix_decode x w S hs hstart
  have hspal : List.Palindrome s := (Hword_palindrome_iff x s).mp (he ▸ hp)
  obtain ⟨r, hr⟩ := hsw
  have hcut : palCut w ≤ r.length := by
    apply palCut_min
    · rw [← hr, List.length_append]; omega
    · rw [← hr, List.drop_left]
      exact hspal
  have hpr : p <+: r := by
    dsimp [p]
    have ht : w.take (palCut w) = r.take (palCut w) := by
      calc
        w.take (palCut w) = (r++s).take (palCut w) := congrArg (List.take (palCut w)) hr.symm
        _ = r.take (palCut w) := List.take_append_of_le_length hcut
    rw [ht]
    exact List.take_prefix _ _
  have hlpr := (Lword_prefix x hpr).length_le
  have hcw : c = (Lword x r).length := by
    have hl := congrArg List.length he
    simp only [S, List.length_drop, Hword, List.length_append, List.length_singleton] at hl
    have hc := (palCut_spec (Hword x w)).1
    have hlen : (Lword x w).length = (Lword x r).length + (Lword x s).length := by
      rw [← hr, Lword_append, List.length_append]
    simp only [Hword, List.length_append, List.length_singleton] at hc
    omega
  change c = (Lword x p).length
  omega

theorem Hword_palClosure (x : Fin d) (w : List (Fin d)) :
    palClosure (Hword x w) = Hword x (palClosure w) := by
  let p := w.take (palCut w)
  have hsplit : Hword x w = Lword x p ++ Hword x (w.drop (palCut w)) := by
    change Lword x w ++ [x] = Lword x p ++ (Lword x (w.drop (palCut w)) ++ [x])
    rw [← List.append_assoc, ← Lword_append]
    congr 2
    exact (List.take_append_drop _ _).symm
  have htake : (Hword x w).take (Lword x p).length = Lword x p := by
    rw [hsplit, List.take_left]
  have hconj : [x] ++ (Lword x p).reverse = Lword x p.reverse ++ [x] := by
    simpa only [Hword, List.reverse_append, List.reverse_singleton] using Hword_reverse x p
  rw [palClosure_formula_cut, Hword_palCut]
  change Hword x w ++ ((Hword x w).take (Lword x p).length).reverse = Hword x (palClosure w)
  rw [htake, palClosure_formula_cut]
  change (Lword x w ++ [x]) ++ (Lword x p).reverse = (Lword x (w++p.reverse)) ++ [x]
  rw [List.append_assoc, hconj, Lword_append, List.append_assoc]

theorem Lword_suffix_nonx (x z : Fin d) (w s : List (Fin d))
    (hz : z ≠ x) (hs : s <:+ Lword x w) (hstart : ∃ r, s = z :: r) :
    [x] ++ s ++ [x] <:+ Hword x w := by
  induction w with
  | nil =>
    obtain ⟨r, rfl⟩ := hstart
    have hl := hs.length_le
    simp [Lword] at hl
  | cons y w ih =>
    have hh : Hword x w <:+ Hword x (y::w) := by
      rw [Hword_cons]
      split_ifs
      · exact ⟨[x], rfl⟩
      · exact ⟨[x,y], rfl⟩
    have hbad : ∀ r, s ≠ x :: r := by
      intro r he
      obtain ⟨t, ht⟩ := hstart
      exact hz (List.cons.inj (ht.symm.trans he)).1
    by_cases hy : y = x
    · have he : Lword x (y::w) = x :: Lword x w := by simp [Lword, letterImage, hy]
      rw [he, List.suffix_cons_iff] at hs
      rcases hs with hs | hs
      · exact (hbad _ hs).elim
      · exact (ih hs).trans hh
    · have he : Lword x (y::w) = x :: y :: Lword x w := by simp [Lword, letterImage, hy]
      rw [he, List.suffix_cons_iff] at hs
      rcases hs with hs | hs
      · exact (hbad _ hs).elim
      · rw [List.suffix_cons_iff] at hs
        rcases hs with hs | hs
        · have hw : [x] ++ s ++ [x] = Hword x (y::w) := by
            rw [hs]
            simp [Hword, he, List.append_assoc]
          rw [hw]
        · exact (ih hs).trans hh

theorem palCut_le_of_suffix (w s : List (Fin d)) (hs : s <:+ w)
    (hp : List.Palindrome s) : palCut w ≤ w.length-s.length := by
  apply palCut_min
  · omega
  · rw [← List.suffix_iff_eq_drop.mp hs]
    exact hp

theorem Lword_palClosure (x z : Fin d) (p : List (Fin d)) (hz : z ≠ x) :
    palClosure (Lword x (p++[z])) = Hword x (palClosure (p++[z])) := by
  let w := p++[z]
  let r := w.take (palCut w)
  let v := w.drop (palCut w)
  have hsplitw : w = r++v := (List.take_append_drop _ _).symm
  have hvpal : List.Palindrome v := (palCut_spec w).2
  have hlast : palCut w ≤ p.length := by
    apply palCut_min
    · simp [w]
    · simp only [w, List.drop_left]
      exact List.Palindrome.singleton z
  have hvne : v ≠ [] := by
    intro hn
    have hl := congrArg List.length hn
    simp only [v, List.length_drop, List.length_nil] at hl
    have hwlen : w.length = p.length+1 := by simp [w]
    omega
  obtain ⟨v', hv⟩ := palindrome_suffix_last_starts z p v (List.drop_suffix _ _) hvpal hvne
  let T := z :: Lword x v'
  have hL : Lword x w = (Lword x r ++ [x]) ++ T := by
    rw [hsplitw, Lword_append, hv]
    simp [Lword, letterImage, hz, T, List.append_assoc]
  have hH : Hword x v = [x] ++ T ++ [x] := by
    rw [hv]
    simp [Hword, Lword, letterImage, hz, T, List.append_assoc]
  have hTpal : List.Palindrome T := by
    have hh := ((Hword_palindrome_iff x v).mpr hvpal).reverse_eq
    rw [hH] at hh
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.reverse_singleton, List.append_assoc, List.append_cancel_left_eq,
      List.append_cancel_right_eq] at hh
    exact List.Palindrome.of_reverse_eq hh
  have hu : palCut (Lword x w) ≤ (Lword x r).length+1 := by
    apply palCut_min
    · rw [hL, List.length_append, List.length_append, List.length_singleton]; omega
    · have hd : (Lword x w).drop ((Lword x r).length+1) = T := by
        rw [hL]
        simpa only [List.length_append, List.length_singleton] using
          (List.drop_left (l₁ := Lword x r ++ [x]) (l₂ := T))
      rwa [hd]
  let c := palCut (Lword x w)
  let S := (Lword x w).drop c
  have hLend : Lword x w = (Lword x p ++ [x]) ++ [z] := by
    simp [w, Lword, letterImage, hz, List.append_assoc]
  have hshort : c ≤ (Lword x p).length+1 := by
    apply palCut_min
    · rw [hLend]; simp
    · rw [hLend]
      have hd : (Lword x p ++ [x] ++ [z]).drop ((Lword x p).length+1) = [z] := by
        simpa only [List.length_append, List.length_singleton] using
          (List.drop_left (l₁ := Lword x p ++ [x]) (l₂ := [z]))
      rw [hd]
      exact List.Palindrome.singleton z
  have hSne : S ≠ [] := by
    intro hn
    have hh := congrArg List.length hn
    simp only [S, List.length_drop, hLend, List.length_append, List.length_singleton, List.length_nil] at hh
    omega
  have hSpal : List.Palindrome S := (palCut_spec (Lword x w)).2
  have hSsuf : S <:+ Lword x w := List.drop_suffix _ _
  obtain ⟨s', hs'⟩ := palindrome_suffix_last_starts z (Lword x p++[x]) S
    (by rwa [← hLend]) hSpal hSne
  have hlift := Lword_suffix_nonx x z w S hz hSsuf ⟨s', hs'⟩
  have hliftpal : List.Palindrome ([x]++S++[x]) := by
    simpa only [List.singleton_append, List.cons_append, List.nil_append] using List.Palindrome.cons_concat x hSpal
  have hlow := palCut_le_of_suffix (Hword x w) ([x]++S++[x]) hlift hliftpal
  have hcutH : palCut (Hword x w) = (Lword x r).length := Hword_palCut x w
  have hcmax := (palCut_spec (Lword x w)).1
  have hlengthlift := hlift.length_le
  simp only [List.length_append, List.length_singleton, S, List.length_drop,
    Hword] at hlow hlengthlift
  have hecut : c = (Lword x r).length+1 := by
    change palCut (Lword x w ++ [x]) = (Lword x r).length at hcutH
    rw [hcutH] at hlow
    omega
  have htake : (Lword x w).take c = Lword x r ++ [x] := by
    rw [hecut, hL]
    simpa only [List.length_append, List.length_singleton] using
      (List.take_left (l₁ := Lword x r ++ [x]) (l₂ := T))
  have htakeH : (Hword x w).take (palCut (Hword x w)) = Lword x r := by
    rw [hcutH]
    have hh : Hword x w = Lword x r ++ Hword x v := by
      rw [hsplitw, Hword, Lword_append, List.append_assoc]
      rfl
    rw [hh, List.take_left]
  rw [← Hword_palClosure x w, palClosure_formula_cut, palClosure_formula_cut]
  change Lword x w ++ ((Lword x w).take c).reverse =
    Hword x w ++ ((Hword x w).take (palCut (Hword x w))).reverse
  rw [htake, htakeH]
  simp [Hword, List.reverse_append, List.append_assoc]

theorem palClosure_of_palindrome (w : List (Fin d)) (hp : List.Palindrome w) :
    palClosure w = w := by
  have hs := palClosure_spec w
  exact (hs.1.eq_of_length_le (hs.2.2 w (List.prefix_refl _) hp)).symm

theorem Hword_append_letter_closure (x z : Fin d) (w : List (Fin d)) :
    palClosure (Hword x w ++ [z]) = Hword x (palClosure (w++[z])) := by
  by_cases hz : z = x
  · subst z
    have he : Hword x w ++ [x] = Hword x (w++[x]) := by simp [Hword, Lword, letterImage, List.append_assoc]
    rw [he, Hword_palClosure]
  · have he : Hword x w ++ [z] = Lword x (w++[z]) := by simp [Hword, Lword, letterImage, hz, List.append_assoc]
    rw [he]
    exact Lword_palClosure x z w hz

theorem central_Justin (x : Fin d) (Delta : Nat → Fin d) (k : Nat) :
    central (Stream'.cons x Delta) (k+1) = Hword x (central Delta k) := by
  induction k with
  | zero =>
    simp only [central, Stream'.cons, List.nil_append]
    rw [palClosure_of_palindrome [x] (List.Palindrome.singleton x)]
    simp [Hword, Lword]
  | succ k ih =>
    change palClosure (central (Stream'.cons x Delta) (k+1) ++ [Delta k]) =
      Hword x (palClosure (central Delta k ++ [Delta k]))
    rw [ih, Hword_append_letter_closure]

theorem central_Justin_shift (Delta : Nat → Fin d) (k : Nat) :
    central Delta (k+1) = Hword (Delta 0) (central (fun n => Delta (n+1)) k) := by
  have he : Stream'.cons (Delta 0) (fun n => Delta (n+1)) = Delta := by
    funext n
    cases n <;> rfl
  rw [← he]
  exact central_Justin (Delta 0) (fun n => Delta (n+1)) k

def muWord (Delta : Nat → Fin d) (n : Nat) (w : List (Fin d)) : List (Fin d) :=
  w.flatMap (mu Delta n)

theorem mu_shift (Delta : Nat → Fin d) (n : Nat) (z : Fin d) :
    mu Delta (n+1) z = Lword (Delta 0) (mu (fun j => Delta (j+1)) n z) := by
  induction n generalizing z with
  | zero => simp [mu, Lword]
  | succ n ih =>
    change (letterImage (Delta (n+1)) z).flatMap (mu Delta (n+1)) =
      ((letterImage (Delta (n+1)) z).flatMap (mu (fun j => Delta (j+1)) n)).flatMap (letterImage (Delta 0))
    rw [List.flatMap_assoc]
    congr 1
    funext y
    exact ih y

theorem central_morphic_finite (Delta : Nat → Fin d) (n k : Nat) :
    central Delta (n+k) = muWord Delta n (central (fun j => Delta (n+j)) k) ++ central Delta n := by
  induction n generalizing Delta with
  | zero => simp [muWord, mu, central]
  | succ n ih =>
    rw [show n+1+k = (n+k)+1 by omega, central_Justin_shift, ih]
    have he : (fun j => Delta (n+j+1)) = (fun j => Delta (n+1+j)) := by
      funext j
      congr 1
      omega
    simp only [Hword, Lword, List.flatMap_append]
    rw [he]
    have hm : muWord Delta (n+1) (central (fun j => Delta (n+1+j)) k) =
        (muWord (fun j => Delta (j+1)) n (central (fun j => Delta (n+1+j)) k)).flatMap (letterImage (Delta 0)) := by
      simp only [muWord, List.flatMap_assoc]
      congr 1
      funext z
      exact mu_shift Delta n z
    rw [hm, central_Justin_shift Delta n]
    simp only [Hword, Lword, List.append_assoc]

def MorphicImage (source target : Nat → Fin d) (f : Fin d → List (Fin d)) : Prop :=
  ∀ k, let W := ((fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) source k).flatMap f
    (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) target W.length = W

theorem wordPrefix_isPrefix (x : Nat → Fin d) {k m : Nat} (h : k ≤ m) :
    (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) x k <+: (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) x m := by
  refine ⟨D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x k (m-k), ?_⟩
  simpa only [Nat.zero_add, Nat.add_sub_of_le h] using
    (D5.S1.Words.MBonacciSentinelDesubstitution.factor_add x 0 k (m-k)).symm

theorem cDelta_morphicImage (Delta : Nat → Fin d) (n : Nat) :
    MorphicImage (cDelta (fun j => Delta (n+j))) (cDelta Delta) (mu Delta n) := by
  intro k
  let tail := fun j => Delta (n+j)
  let W := ((fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (cDelta tail) k).flatMap (mu Delta n)
  have hpre : (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (cDelta tail) k <+: central tail k := by
    rw [← central_is_cDelta_prefix tail k]
    exact wordPrefix_isPrefix _ (central_length_ge tail k)
  have hpre' : W <+: central Delta (n+k) := by
    rcases hpre with ⟨u, hu⟩
    have hmu : W <+: (central tail k).flatMap (mu Delta n) := by
      refine ⟨u.flatMap (mu Delta n), ?_⟩
      change W ++ u.flatMap (mu Delta n) = (central tail k).flatMap (mu Delta n)
      rw [← List.flatMap_append, hu]
    have hf := central_morphic_finite Delta n k
    rw [hf]
    exact hmu.trans (List.prefix_append _ _)
  change (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (cDelta Delta) W.length = W
  apply List.ext_getElem
  · simp [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add]
  · intro i hi hj
    have hic : i < (central Delta (n+k)).length := lt_of_lt_of_le hj hpre'.length_le
    simp only [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add, List.getElem_map, List.getElem_range]
    exact (central_get_eq_cDelta Delta (n+k) i hic).symm.trans (hpre'.getElem hj).symm

def HasPeriodOn (x : Nat → Fin d) (q b e : Nat) : Prop :=
  ∀ i, b ≤ i → i + q < e → x (i+q) = x i

private theorem wordPrefix_length (x : Nat → Fin d) (n : Nat) :
    ((fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) x n).length = n := by
  exact D5.S1.Words.MBonacciSentinelDesubstitution.factor_len x 0 n

theorem periodic_interval_mod (x : Nat → Fin d) (q b e : Nat)
    (hq : 0 < q) (hperiod : HasPeriodOn x q b e) (i : Nat) (hi : b+i < e) :
    x (b+i) = x (b+i%q) := by
  let W := (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => x (b+j)) (e-b)
  have hper : List.HasPeriod W q := by
    apply List.hasPeriod_iff_getElem?.mpr
    intro j hj
    have hj0 : j < e-b := by have := wordPrefix_length (fun j => x (b+j)) (e-b); change j < W.length-q at hj; dsimp [W] at hj; simp only [wordPrefix_length] at hj; omega
    have hjq : j+q < e-b := by dsimp [W] at hj; simp only [wordPrefix_length] at hj; omega
    have hs := hperiod (b+j) (by omega) (by omega)
    simpa [W, D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add, List.getElem?_map, List.getElem?_range, hj0, hjq, Nat.add_assoc] using congrArg some hs.symm
  have hiw : i < W.length := by simp only [W, wordPrefix_length]; omega
  have him : i%q < e-b := by have := Nat.mod_le i q; omega
  have hh := hper.getElem?_mod q i W hiw
  have hi' : i < e-b := by omega
  simpa [W, D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add, List.getElem?_map, List.getElem?_range, hi', him] using hh.symm

theorem periodic_interval_prefix (x : Nat → Fin d) (q b ell e : Nat)
    (hq : 0 < q) (hql : q ≤ ell) (hend : b+ell ≤ e)
    (hperiod : HasPeriodOn x q b e) :
    ∃ V : List (Fin d), ∃ hV : V ≠ [],
      V.length = q ∧ (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun i => x (b+i)) ell = fractionalPower V hV ell := by
  let V := (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun i => x (b+i)) q
  have hvlen : V.length = q := wordPrefix_length _ _
  have hV : V ≠ [] := by intro hn; have := congrArg List.length hn; simp only [List.length_nil] at this; omega
  refine ⟨V, hV, hvlen, ?_⟩
  apply List.ext_getElem
  · simp [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add, fractionalPower]
  · intro i hi hj
    simp only [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add, fractionalPower, List.getElem_map, List.getElem_range,
      List.get_eq_getElem]
    have hil : i < ell := by simpa [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add] using hi
    have hb := periodic_interval_mod x q b e hq hperiod i (by omega)
    simpa [V, D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add, hvlen, List.get_eq_getElem] using hb

theorem wordPrefix_append (x : Nat → Fin d) (u ell : Nat) :
    (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) x (u+ell) = (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) x u ++ (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => x (u+j)) ell := by
  simpa only [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add] using
    D5.S1.Words.MBonacciSentinelDesubstitution.factor_add x 0 u ell

structure PeriodicRunCover (x : Nat → Fin d) (q a : Nat) where
  beginRun : Nat → Nat
  endRun : Nat → Nat
  start_zero : beginRun 0 = 0
  span : ∀ k, beginRun k + a*q ≤ endRun k
  next_order : ∀ k, endRun k ≤ beginRun (k+1)
  gap : ∀ k, beginRun (k+1) - endRun k ≤ 2*q
  periodic : ∀ k, HasPeriodOn x q (beginRun k) (endRun k)
  unbounded : ∀ n, ∃ k, n < endRun k

theorem run_cover_near_period (x : Nat → Fin d) (q a M n : Nat)
    (cover : PeriodicRunCover x q a) :
    (HasPeriodOn x q n (n+M*q)) ∨
    ∃ u ≤ (M+2)*q, HasPeriodOn x q (n+u) (n+u+a*q) := by
  classical
  let k := Nat.find (cover.unbounded n)
  have hnk : n < cover.endRun k := Nat.find_spec (cover.unbounded n)
  have hprev : k = 0 ∨ cover.endRun (k-1) ≤ n := by
    by_cases hk : k = 0
    · exact Or.inl hk
    · right
      have hkm : k-1 < k := by omega
      have hh := Nat.find_min (cover.unbounded n) hkm
      omega
  by_cases hbeg : n < cover.beginRun k
  · right
    refine ⟨cover.beginRun k - n, ?_, ?_⟩
    · have hk : k ≠ 0 := by intro he; rw [he, cover.start_zero] at hbeg; omega
      have hp : cover.endRun (k-1) ≤ n := hprev.resolve_left hk
      have hg := cover.gap (k-1)
      have he := cover.next_order (k-1)
      have hks : k-1+1 = k := by omega
      rw [hks] at hg he
      have hMq : 2*q ≤ (M+2)*q := by nlinarith
      omega
    · have heq : n+(cover.beginRun k-n) = cover.beginRun k := by omega
      rw [heq]
      intro j hj hje
      exact cover.periodic k j hj (lt_of_lt_of_le hje (cover.span k))
  · by_cases hremain : n+M*q ≤ cover.endRun k
    · left
      intro j hj hje
      exact cover.periodic k j (by omega) (lt_of_lt_of_le hje hremain)
    · right
      refine ⟨cover.beginRun (k+1)-n, ?_, ?_⟩
      · have he := cover.next_order k
        have hg := cover.gap k
        have hex : cover.beginRun (k+1)-n =
            (cover.endRun k-n) + (cover.beginRun (k+1)-cover.endRun k) := by omega
        have hrem : cover.endRun k - n ≤ M*q := by omega
        rw [hex]
        nlinarith
      · have he := cover.next_order k
        have heq : n+(cover.beginRun (k+1)-n) = cover.beginRun (k+1) := by omega
        rw [heq]
        intro j hj hje
        exact cover.periodic (k+1) j hj (lt_of_lt_of_le hje (cover.span (k+1)))

theorem uniform_finite_window (x : Nat → Fin d) (q a M n : Nat)
    (hq : 0 < q) (hM : 2 ≤ M) (ha : M*(M+3) ≤ a)
    (cover : PeriodicRunCover x q a) :
    ∃ U V : List (Fin d), ∃ ell : Nat, ∃ hV : V ≠ [],
      V.length = q ∧ V.length ≤ ell ∧ U.length ≤ (M+2)*q ∧
      M*q ≤ U.length+ell ∧ U.length+ell ≤ (a+M+2)*q ∧
      (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => x (n+j)) (U.length+ell) = U ++ fractionalPower V hV ell ∧
      (M : Real) ≤ (U.length+ell : Real)/(U.length+V.length) := by
  have hMa : M ≤ a := by nlinarith
  rcases run_cover_near_period x q a M n cover with hper | ⟨u, hu, hper⟩
  · obtain ⟨V, hV, hvq, hword⟩ :=
      periodic_interval_prefix x q n (M*q) (n+M*q) hq (by nlinarith) (by omega) hper
    refine ⟨[], V, M*q, hV, hvq, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hvq]; nlinarith
    · simp
    · simp
    · simp only [List.length_nil, zero_add]; nlinarith
    · simpa using hword
    · simp only [List.length_nil, zero_add, hvq]
      simp only [Nat.cast_add, Nat.cast_zero, Nat.cast_mul, zero_add]
      have hqr : (0 : Real) < q := by exact_mod_cast hq
      rw [mul_div_cancel_right₀ (M : Real) (ne_of_gt hqr)]
  · obtain ⟨V, hV, hvq, hword⟩ :=
      periodic_interval_prefix x q (n+u) (a*q) (n+u+a*q) hq (by nlinarith) (by omega) hper
    let U := (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => x (n+j)) u
    have huLen : U.length = u := wordPrefix_length _ _
    refine ⟨U, V, a*q, hV, hvq, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hvq]; nlinarith
    · rwa [huLen]
    · rw [huLen]; nlinarith
    · rw [huLen]; nlinarith
    · rw [huLen, wordPrefix_append]
      have htail : (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => x (n+(u+j))) (a*q) = fractionalPower V hV (a*q) := by
        simpa only [Nat.add_assoc] using hword
      exact congrArg (U ++ ·) htail
    · rw [huLen, hvq]
      have hqr : (0 : Real) < q := by exact_mod_cast hq
      apply (le_div_iff₀ (by positivity : (0 : Real) < u+q)).2
      have hN : M*(u+q) ≤ u+a*q := by
        have h1 : M*u ≤ M*((M+2)*q) := Nat.mul_le_mul_left M hu
        have h2 : (M*(M+3))*q ≤ a*q := Nat.mul_le_mul_right q ha
        nlinarith
      exact_mod_cast hN

 theorem wordPower_add (A : List (Fin d)) (r s : Nat) :
    (fun A a => D5.S1.Words.Powers.wordPower a A) A (r+s) = (fun A a => D5.S1.Words.Powers.wordPower a A) A r ++ (fun A a => D5.S1.Words.Powers.wordPower a A) A s := by
  simp only [D5.S1.Words.Powers.wordPower, List.replicate_add, List.flatten_append]

 theorem wordPower_period (A : List (Fin d)) (r : Nat) :
    List.HasPeriod ((fun A a => D5.S1.Words.Powers.wordPower a A) A r) A.length := by
  apply List.hasPeriod_iff_getElem?.mpr
  intro i hi
  have hlen := D5.S1.Words.Powers.length_wordPower r A
  have hb : i + A.length < r * A.length := by dsimp at hi; omega
  exact D5.S1.Words.Powers.wordPower_period_getElem? r A i hb

 theorem wordPrefix_constant (s : Nat → Fin d) (x : Fin d) (a : Nat)
    (h : ∀ j < a, s j = x) : (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) s a = List.replicate a x := by
  simpa only [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add,
    List.length_range] using
    (List.map_eq_replicate_iff.mpr (fun j hj => h j (List.mem_range.mp hj)))

end D5.S1.Words.Episturmian.MorphicDecomposition
