/- GID: D5/S1/Words/Episturmian/DensePowerWindow
   generality: G
   mirror-B: D5/B/S1/Words/Episturmian/DensePowerWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: uniform finite windows and dense powers -/

/- proof_shape: powerChunks_cover: content; escape_witness: D5.S1.Words.Episturmian.DensePowerWindow.powerChunks_cover
   escape_witness: powerChunks_cover
   admission_basis: escape-witness
   Declarations:
   definition: HasPeriodOn; consumer: DensePowerWindow.periodic_interval_mod
   proof_shape: wordPrefix_length: bind-only; consumer: DensePowerWindow.periodic_interval_mod
   proof_shape: periodic_interval_mod: bind-only; consumer: DensePowerWindow.periodic_interval_prefix
   proof_shape: periodic_interval_prefix: bind-only; consumer: DensePowerWindow.uniform_finite_window
   proof_shape: wordPrefix_append: bind-only; consumer: DensePowerWindow.uniform_finite_window
   definition: PeriodicRunCover; consumer: DensePowerWindow.run_cover_near_period
   proof_shape: run_cover_near_period: bind-only; consumer: DensePowerWindow.uniform_finite_window
   proof_shape: uniform_finite_window: bind-only; consumer: DensePowerWindow.uniform_window_transfer
   proof_shape: wordPower_add: bind-only; consumer: DensePowerWindow.powerChunk_exists
   proof_shape: wordPower_period: bind-only; consumer: DensePowerWindow.powerChunks_cover
   proof_shape: wordPrefix_constant: bind-only; consumer: DensePowerWindow.powerChunk_exists
   definition: imagePrefix; consumer: DensePowerWindow.imagePrefix_add
   proof_shape: imagePrefix_add: bind-only; consumer: DensePowerWindow.morphicImage_segment
   proof_shape: imagePrefix_succ: bind-only; consumer: DensePowerWindow.imagePrefix_length_ge
   proof_shape: imagePrefix_length_ge: bind-only; consumer: DensePowerWindow.powerChunks_cover
   definition: PowerChunk; consumer: DensePowerWindow.powerChunk_exists
   proof_shape: powerChunk_exists: bind-only; consumer: BoundedPowers.cDelta_constant_run_cover
   proof_shape: morphicImage_segment: bind-only; consumer: DensePowerWindow.powerChunks_cover
   proof_shape: periodOn_of_segment: bind-only; consumer: DensePowerWindow.powerChunks_cover
   proof_shape: powerChunks_cover: content; escape_witness: D5.S1.Words.Episturmian.DensePowerWindow.powerChunks_cover; consumer: BoundedPowers.cDelta_constant_run_cover
   proof_shape: wordPrefix_mem_Lang: bind-only; consumer: DensePowerWindow.language_prefix_occurrence
   proof_shape: language_prefix_occurrence: bind-only; consumer: DensePowerWindow.uniform_window_transfer
   proof_shape: uniform_window_transfer: bind-only; consumer: DensePowerWindow.arbitrarily_dense_powers_dio_top
   proof_shape: arbitrarily_dense_powers_dio_top: bind-only; consumer: BoundedPowers.not_boundedPQ_dio_top
   Direct frozen dependencies (pre-existing): D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs; D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor; sha256:54f2f8a1cd3a83f896d4018ef9821e5aa1b6046bd757ec6a999734a691651d1c | D5/S1/Words/Powers/WordPower; D5.S1.Words.Powers.length_wordPower; sha256:debf5e4132f97f82101c3032c0cf4922d3f005aae64c4067de34e835705ee5bf | D5/S1/Words/Powers/WordPower; D5.S1.Words.Powers.wordPower; sha256:a6e228e7ee6ecdc474ee0b218a6a0c370496359d57e770a78cc40f1991acc416 | D5/S1/Words/Powers/WordPower; D5.S1.Words.Powers.wordPower_period_getElem?; sha256:d9c6a06ea421449d240a7406ecf38761aeedd1293e31e9ba625eece0556d16cd
   Finite prefixes use the existing factor operator at start zero.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16158
-/

import D5.S1.Words.Episturmian.MorphicDecomposition
import Mathlib.Data.List.PeriodicityLemma

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Episturmian.DensePowerWindow
open D5.S1.Words.Episturmian.PalindromicClosure
open D5.S1.Words.Episturmian.MorphicDecomposition
variable {d : Nat}

def HasPeriodOn (x : Nat → Fin d) (q b e : Nat) : Prop :=
  ∀ i, b ≤ i → i + q < e → x (i+q) = x i

private theorem wordPrefix_length (x : Nat → Fin d) (n : Nat) :
    ((fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) x n).length = n := by simp [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add]

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
  simp [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add, List.range_add, List.map_append, List.map_map, Function.comp_def]

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
  apply List.ext_getElem
  · simp [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add]
  · intro j hj hj'
    simp only [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add, List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact h j (by simpa [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add] using hj)

 def imagePrefix (s : Nat → Fin d) (f : Fin d → List (Fin d)) (k : Nat) : List (Fin d) :=
   ((fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) s k).flatMap f

 theorem imagePrefix_add (s : Nat → Fin d) (f : Fin d → List (Fin d)) (k j : Nat) :
    imagePrefix s f (k+j) = imagePrefix s f k ++ imagePrefix (fun i => s (k+i)) f j := by
  simp only [imagePrefix, wordPrefix_append, List.flatMap_append]

 theorem imagePrefix_succ (s : Nat → Fin d) (f : Fin d → List (Fin d)) (k : Nat) :
    imagePrefix s f (k+1) = imagePrefix s f k ++ f (s k) := by
  let L := (D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor s 0 (k+1)).map f
  have ht : L.take k = (D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor s 0 k).map f := by
    simp [L, D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add, ← List.map_take, List.take_range]
  have hd : L.drop k = [f (s k)] := by
    simp [L, D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add, List.range_succ, List.map_append, List.drop_append]
  have hp := List.take_sum_flatten L k
  have hs := List.drop_sum_flatten L k
  rw [ht] at hp
  rw [hd] at hs
  have he := List.take_append_drop ((L.map List.length).take k).sum L.flatten
  rw [hp, hs] at he
  simpa [L, imagePrefix, List.flatMap_def] using he.symm


 theorem imagePrefix_length_ge (s : Nat → Fin d) (f : Fin d → List (Fin d))
    (hpos : ∀ z, 0 < (f z).length) (k : Nat) : k ≤ (imagePrefix s f k).length := by
  induction k with
  | zero => simp [imagePrefix, D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add]
  | succ k ih => rw [imagePrefix_succ, List.length_append]; have := hpos (s k); omega

 structure PowerChunk (s : Nat → Fin d) (f : Fin d → List (Fin d))
    (A : List (Fin d)) (a p : Nat) where
   step : Nat
   copies : Nat
   sep : List (Fin d)
   step_pos : 0 < step
   copies_ge : a ≤ copies
   sep_short : sep.length ≤ 2*A.length
   image_eq : imagePrefix (fun j => s (p+j)) f step = (fun A a => D5.S1.Words.Powers.wordPower a A) A copies ++ sep

 theorem powerChunk_exists (s : Nat → Fin d) (f : Fin d → List (Fin d))
    (A : List (Fin d)) (B : Fin d → List (Fin d)) (x : Fin d) (a p : Nat)
    (ha : 0 < a) (hfx : f x = A)
    (hf : ∀ z, z ≠ x → f z = (fun A a => D5.S1.Words.Powers.wordPower a A) A a ++ B z)
    (hB : ∀ z, (B z).length ≤ 2*A.length) :
    Nonempty (PowerChunk s f A a p) := by
  classical
  by_cases hh : ∃ j, j < a ∧ s (p+j) ≠ x
  · let j := Nat.find hh
    have hj := Nat.find_spec hh
    have hprev : ∀ i < j, s (p+i) = x := by
      intro i hi
      have hn := Nat.find_min hh hi
      by_contra hne
      exact hn ⟨by omega, hne⟩
    have hp : imagePrefix (fun i => s (p+i)) f j = (fun A a => D5.S1.Words.Powers.wordPower a A) A j := by
      simp only [imagePrefix, wordPrefix_constant _ x j hprev, List.flatMap_replicate, hfx, D5.S1.Words.Powers.wordPower]
    refine ⟨⟨j+1, j+a, B (s (p+j)), by omega, by omega, hB _, ?_⟩⟩
    rw [imagePrefix_succ, hp, hf _ hj.2, ← List.append_assoc, ← wordPower_add]
  · have hp : ∀ j < a, s (p+j) = x := by
      intro j hj
      by_contra hne
      exact hh ⟨j,hj,hne⟩
    refine ⟨⟨a, a, [], ha, le_rfl, by simp, ?_⟩⟩
    simp only [imagePrefix, wordPrefix_constant _ x a hp, List.flatMap_replicate, hfx,
      D5.S1.Words.Powers.wordPower, List.append_nil]


 theorem morphicImage_segment (s t : Nat → Fin d) (f : Fin d → List (Fin d))
    (hi : MorphicImage s t f) (p step : Nat) (W S : List (Fin d))
    (he : imagePrefix (fun j => s (p+j)) f step = W ++ S)
    (j : Nat) (hj : j < W.length) :
    t ((imagePrefix s f p).length+j) = W[j] := by
  have h := hi (p+step)
  change (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) t (imagePrefix s f (p+step)).length = imagePrefix s f (p+step) at h
  rw [imagePrefix_add, he] at h
  have hk : (imagePrefix s f p).length+j <
      (imagePrefix s f p ++ (W++S)).length := by simp only [List.length_append]; omega
  have hh := congrArg (fun l : List (Fin d) => l[(imagePrefix s f p).length+j]?) h
  have hleft : (imagePrefix s f p).length ≤ (imagePrefix s f p).length+j := by omega
  simp only [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add, List.getElem?_map, List.getElem?_range, hk, if_true,
    Option.map_some, List.getElem?_append_right hleft, Nat.add_sub_cancel_left,
    List.getElem?_append_left hj, List.getElem?_eq_getElem hj] at hh
  exact Option.some.inj hh

 theorem periodOn_of_segment (t : Nat → Fin d) (W : List (Fin d)) (b q : Nat)
    (hget : ∀ j (hj : j < W.length), t (b+j) = W[j]) (hper : List.HasPeriod W q) :
    HasPeriodOn t q b (b+W.length) := by
  intro i hi hie
  have h0 : i-b < W.length := by omega
  have h1 : i-b+q < W.length := by omega
  have he : i = b+(i-b) := by omega
  have hh := (List.hasPeriod_iff_getElem?.mp hper) (i-b) (by omega)
  rw [List.getElem?_eq_getElem h0, List.getElem?_eq_getElem h1] at hh
  rw [he, Nat.add_assoc, hget (i-b+q) h1, hget (i-b) h0]
  exact (Option.some.inj hh).symm

 theorem powerChunks_cover (s t : Nat → Fin d) (f : Fin d → List (Fin d))
    (A : List (Fin d)) (a : Nat)
    (hi : MorphicImage s t f) (hfpos : ∀ z, 0 < (f z).length)
    (chunks : ∀ p, Nonempty (PowerChunk s f A a p)) :
    Nonempty (PeriodicRunCover t A.length a) := by
  classical
  let chunk := fun p => Classical.choice (chunks p)
  let p : Nat → Nat := Nat.rec 0 (fun _ prev => prev + (chunk prev).step)
  have hp0 : p 0 = 0 := rfl
  have hps : ∀ k, p (k+1) = p k + (chunk (p k)).step := by intro k; rfl
  have hpk : ∀ k, k ≤ p k := by
    intro k
    induction k with
    | zero => omega
    | succ k ih => rw [hps]; have := (chunk (p k)).step_pos; omega
  let beg := fun k => (imagePrefix s f (p k)).length
  let ending := fun k => beg k + (chunk (p k)).copies*A.length
  have hnext : ∀ k, beg (k+1) = ending k + (chunk (p k)).sep.length := by
    intro k
    dsimp [beg, ending]
    rw [hps, imagePrefix_add, (chunk (p k)).image_eq]
    simp only [List.length_append, D5.S1.Words.Powers.length_wordPower, Nat.add_assoc]
  refine ⟨⟨beg, ending, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [beg, hp0, imagePrefix, D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add]
  · intro k
    dsimp [ending]
    have hh := Nat.mul_le_mul_right A.length (chunk (p k)).copies_ge
    omega
  · intro k
    rw [hnext]
    omega
  · intro k
    rw [hnext, Nat.add_sub_cancel_left]
    exact (chunk (p k)).sep_short
  · intro k
    have hg := morphicImage_segment s t f hi (p k) (chunk (p k)).step
      ((fun A a => D5.S1.Words.Powers.wordPower a A) A (chunk (p k)).copies) (chunk (p k)).sep (chunk (p k)).image_eq
    have hh := periodOn_of_segment t ((fun A a => D5.S1.Words.Powers.wordPower a A) A (chunk (p k)).copies) (beg k) A.length
      hg (wordPower_period A _)
    simpa only [D5.S1.Words.Powers.length_wordPower, ending] using hh
  · intro n
    refine ⟨n+1, ?_⟩
    have hh := imagePrefix_length_ge s f hfpos (p (n+1))
    have hp := hpk (n+1)
    dsimp [ending, beg]
    omega


theorem wordPrefix_mem_Lang (x : Nat → Fin d) (H : Nat) : (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) x H ∈ Lang x := by
  refine ⟨0, ?_⟩
  intro j
  simp only [Nat.zero_add]
  rcases j with ⟨j, hj⟩
  simp [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add, List.get_eq_getElem]

theorem language_prefix_occurrence (t x : Nat → Fin d) (H : Nat)
    (hlang : Lang t = Lang x) :
    ∃ n, ∀ ell ≤ H, (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) t ell = (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => x (n+j)) ell := by
  have hm := wordPrefix_mem_Lang t H
  rw [hlang] at hm
  obtain ⟨n, hn⟩ := hm
  refine ⟨n, ?_⟩
  intro ell hell
  apply List.map_congr_left
  intro j hj
  have hjell : j < ell := List.mem_range.mp hj
  have hjH : j < H := by omega
  have hget := hn ⟨j, by simpa [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add] using hjH⟩
  simpa [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add, List.get_eq_getElem] using hget

theorem uniform_window_transfer (t x : Nat → Fin d) (q a M : Nat)
    (hlang : Lang t = Lang x) (hq : 0 < q) (hM : 2 ≤ M)
    (ha : M*(M+3) ≤ a) (cover : PeriodicRunCover x q a) :
    ∃ U V : List (Fin d), ∃ ell : Nat, ∃ hV : V ≠ [],
      V.length = q ∧ V.length ≤ ell ∧ U.length ≤ (M+2)*q ∧
      M*q ≤ U.length+ell ∧ U.length+ell ≤ (a+M+2)*q ∧
      (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) t (U.length+ell) = U ++ fractionalPower V hV ell ∧
      (M : Real) ≤ (U.length+ell : Real)/(U.length+V.length) := by
  obtain ⟨n, hn⟩ := language_prefix_occurrence t x ((a+M+2)*q) hlang
  obtain ⟨U, V, ell, hV, hvq, hvell, hu, hlow, hhigh, hword, hratio⟩ :=
    uniform_finite_window x q a M n hq hM ha cover
  exact ⟨U, V, ell, hV, hvq, hvell, hu, hlow, hhigh,
    (hn _ hhigh).trans hword, hratio⟩

theorem arbitrarily_dense_powers_dio_top (t x : Nat → Fin d)
    (hlang : Lang t = Lang x)
    (hdense : ∀ M : Nat, 2 ≤ M → ∃ q a : Nat, 0 < q ∧
      M*(M+3) ≤ a ∧ Nonempty (PeriodicRunCover x q a)) : dio t = ⊤ := by
  have hadm : ∀ rho : NNReal, DioAdmissible t rho := by
    intro rho L
    obtain ⟨m, hm⟩ := exists_nat_ge (rho : Real)
    let M := m + L + 2
    have hM : 2 ≤ M := by omega
    obtain ⟨q, a, hq, ha, ⟨cover⟩⟩ := hdense M hM
    obtain ⟨U, V, ell, hV, hvq, hvell, hu, hlow, hhigh, hword, hratio⟩ :=
      uniform_window_transfer t x q a M hlang hq hM ha cover
    refine ⟨U, V, ell, hV, hvell, ?_, hword, ?_⟩
    · have hL : L ≤ M*q := by dsimp [M]; nlinarith
      omega
    · have hrho : (rho : Real) ≤ M := by
        have hMM : m ≤ M := by omega
        have hMMr : (m : Real) ≤ M := by exact_mod_cast hMM
        linarith
      exact hrho.trans hratio
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro rho
  exact le_iSup_of_le rho (le_iSup_of_le (hadm rho) le_rfl)

end D5.S1.Words.Episturmian.DensePowerWindow
