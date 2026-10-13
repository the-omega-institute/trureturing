/- GID: D5/S1/Words/Episturmian/MorphicDecomposition
   generality: G
   mirror-B: D5/B/S1/Words/Episturmian/MorphicDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Justin morphic decomposition and finite central prefixes -/

/- proof_shape: central_Justin: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin
   escape_witness: central_Justin
   admission_basis: escape-witness
   Declarations:
   proof_shape: central_prefix_succ: bind-only; consumer: MorphicDecomposition.central_prefix_of_le
   proof_shape: central_prefix_of_le: bind-only; consumer: MorphicDecomposition.central_get_eq_cDelta
   proof_shape: central_get_eq_cDelta: content; escape_witness: D5.S1.Words.Episturmian.PalindromicClosure.central_length_ge; consumer: MorphicDecomposition.central_is_cDelta_prefix
   proof_shape: central_is_cDelta_prefix: content; escape_witness: D5.S1.Words.Episturmian.PalindromicClosure.central_length_ge; consumer: MorphicDecomposition.cDelta_morphicImage
   definition: letterImage; consumer: MorphicDecomposition.mu
   definition: mu; consumer: MorphicDecomposition.mu_length_step
   proof_shape: mu_length_step: bind-only; consumer: MorphicDecomposition.mu_length_pos
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
   proof_shape: Lword_append: bind-only; consumer: MorphicDecomposition.Lword_prefix
   proof_shape: Lword_prefix: bind-only; consumer: MorphicDecomposition.Hword_palCut
   proof_shape: Hword_suffix_decode: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.Hword_suffix_decode; consumer: MorphicDecomposition.Hword_palCut
   proof_shape: palindrome_suffix_Hword_starts: bind-only; consumer: MorphicDecomposition.Hword_palCut
   proof_shape: Hword_palCut: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.Hword_injective; consumer: MorphicDecomposition.Hword_palClosure
   proof_shape: Hword_palClosure: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.Hword_injective; consumer: MorphicDecomposition.Lword_palClosure
   proof_shape: Lword_suffix_nonx: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.Lword_suffix_nonx; consumer: MorphicDecomposition.Lword_palClosure
   proof_shape: palindrome_suffix_last_starts: bind-only; consumer: MorphicDecomposition.Lword_palClosure
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
   proof_shape: cDelta_morphicImage: content; escape_witness: D5.S1.Words.Episturmian.PalindromicClosure.central_length_ge; consumer: BoundedPowers.cDelta_constant_run_cover
   Direct frozen dependencies (pre-existing): D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs; D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor; sha256:54f2f8a1cd3a83f896d4018ef9821e5aa1b6046bd757ec6a999734a691651d1c | D5/S1/Words/Powers/WordPower; D5.S1.Words.Powers.wordPower; sha256:a6e228e7ee6ecdc474ee0b218a6a0c370496359d57e770a78cc40f1991acc416 | D5/S1/Words/Powers/WordPower; D5.S1.Words.Powers.wordPower_succ; sha256:2555a0f5d0c0ce76d62ea9dc70d6f8b1554ec0d5a37821080b16cbaabc5c2b5d
   Finite prefixes use the existing factor operator at start zero.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16158
-/

import D5.S1.Words.Episturmian.PalindromicClosure
import D5.S1.Words.MBonacciSentinelDesubstitution
import D5.S1.Words.Powers.WordPower

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Episturmian.MorphicDecomposition
open D5.S1.Words.Episturmian.PalindromicClosure
variable {d : Nat}

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

theorem mu_length_pos (Delta : Nat → Fin d) (n : Nat) (z : Fin d) :
    0 < (mu Delta n z).length := by
  induction n with
  | zero => simp [mu]
  | succ n ih => rw [mu_length_step]; split_ifs <;> omega

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
  obtain ⟨r, rfl⟩ := h
  exact ⟨Lword x r, (Lword_append x u r).symm⟩

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

theorem palindrome_suffix_Hword_starts (x : Fin d) (w s : List (Fin d))
    (hs : s <:+ Hword x w) (hpal : List.Palindrome s) (hne : s ≠ []) :
    ∃ r, s = x :: r := by
  have hp := hs.reverse
  rw [hpal.reverse_eq, Hword_reverse] at hp
  obtain ⟨r, hr⟩ := Hword_starts x w.reverse
  rw [hr, List.prefix_cons_iff] at hp
  rcases hp with he | ⟨t, he, ht⟩
  · exact (hne he).elim
  · exact ⟨t, he⟩

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

end D5.S1.Words.Episturmian.MorphicDecomposition
