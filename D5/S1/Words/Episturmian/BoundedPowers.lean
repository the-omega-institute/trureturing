/- GID: D5/S1/Words/Episturmian/BoundedPowers
   generality: G
   mirror-B: D5/B/S1/Words/Episturmian/BoundedPowers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: period desubstitution and bounded supplier -/

/- escape_witness: D5.S1.Words.Episturmian.BoundedPowers.extendedMu_period_lift
   admission_basis: escape-witness
   Declarations:
   definition: imagePrefix; consumer: BoundedPowers.imagePrefix_add
   proof_shape: imagePrefix_add: bind-only; consumer: BoundedPowers.morphicImage_segment
   proof_shape: imagePrefix_succ: bind-only; consumer: BoundedPowers.powerChunk_exists
   proof_shape: imagePrefix_length_ge: bind-only; consumer: BoundedPowers.powerChunks_cover
   definition: PowerChunk; consumer: BoundedPowers.powerChunk_exists
   proof_shape: powerChunk_exists: bind-only; consumer: BoundedPowers.cDelta_constant_run_cover
   proof_shape: morphicImage_segment: bind-only; consumer: BoundedPowers.powerChunks_cover
   proof_shape: periodOn_of_segment: bind-only; consumer: BoundedPowers.powerChunks_cover
   proof_shape: powerChunks_cover: bind-only; consumer: BoundedPowers.cDelta_constant_run_cover
   proof_shape: wordPrefix_mem_Lang: bind-only; consumer: BoundedPowers.language_prefix_occurrence
   proof_shape: language_prefix_occurrence: bind-only; consumer: BoundedPowers.uniform_window_transfer
   proof_shape: uniform_window_transfer: bind-only; consumer: BoundedPowers.arbitrarily_dense_powers_dio_top
   proof_shape: arbitrarily_dense_powers_dio_top: bind-only; consumer: BoundedPowers.not_boundedPQ_dio_top
   definition: ConstantBlock; consumer: BoundedPowers.unboundedPQ_iff_long_blocks
   definition: RunStart; consumer: BoundedPowers.constant_block_at_run_start
   proof_shape: unboundedPQ_iff_long_blocks: bind-only; consumer: BoundedPowers.not_boundedPQ_dio_top
   proof_shape: constant_block_at_run_start: bind-only; consumer: BoundedPowers.not_boundedPQ_dio_top
   proof_shape: cDelta_constant_run_cover: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin; consumer: BoundedPowers.not_boundedPQ_dio_top
   proof_shape: not_boundedPQ_dio_top: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin; consumer: BoundedPowers.dio_finite_implies_boundedPQ
   proof_shape: dio_finite_implies_boundedPQ: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin; consumer: DiophantineExponentCriterion.result
   proof_shape: morphicImage_block_get: bind-only; consumer: BoundedPowers.morphicImage_block_position
   proof_shape: morphicImage_block_position: bind-only; consumer: BoundedPowers.morphic_periodic_factor_bound
   proof_shape: Hword_prefix_decode: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.Hword_suffix_decode; consumer: BoundedPowers.Hword_prefix_reflect
   proof_shape: Hword_prefix_reflect: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.Hword_injective; consumer: BoundedPowers.Hword_period_desubstitute
   proof_shape: Hword_period_desubstitute: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.Hword_injective; consumer: BoundedPowers.extendedMu_period_lift
   definition: extendedMu; consumer: BoundedPowers.extendedMu_shift
   proof_shape: muWord_shift: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.mu_shift; consumer: BoundedPowers.extendedMu_shift
   proof_shape: extendedMu_shift: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin; consumer: BoundedPowers.central_prefix_extendedMu
   proof_shape: Hword_prefix: bind-only; consumer: BoundedPowers.central_prefix_extendedMu
   proof_shape: central_prefix_extendedMu: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin; consumer: BoundedPowers.extendedMu_period_lift
   proof_shape: muWord_prefix: bind-only; consumer: BoundedPowers.extendedMu_period_lift
   proof_shape: extendedMu_period_lift: content; escape_witness: D5.S1.Words.Episturmian.BoundedPowers.extendedMu_period_lift; consumer: BoundedPowers.morphic_periodic_factor_bound
   proof_shape: morphicImage_shift: bind-only; consumer: BoundedPowers.morphicImage_extended_prefix
   proof_shape: central_prefix_imagePrefix: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin; consumer: BoundedPowers.morphicImage_central_prefix
   proof_shape: morphicImage_central_prefix: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin; consumer: BoundedPowers.morphicImage_extended_prefix
   proof_shape: morphicImage_extended_prefix: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin; consumer: BoundedPowers.extendedMu_segment_occurrence
   proof_shape: imagePrefix_length_strictMono: bind-only; consumer: BoundedPowers.morphic_periodic_factor_bound
   proof_shape: extendedMu_segment_occurrence: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin; consumer: BoundedPowers.morphic_periodic_factor_bound
   proof_shape: mu_length_uniform_ratio: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.mu_length_triangle; consumer: BoundedPowers.boundedPQ_image_scale
   proof_shape: central_succ_morphic: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin; consumer: BoundedPowers.central_length_le_image_sum
   proof_shape: image_sum_step: bind-only; consumer: BoundedPowers.central_length_le_image_sum
   proof_shape: central_length_le_image_sum: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin; consumer: BoundedPowers.boundedPQ_image_scale
   proof_shape: mu_length_increases_over_B: bind-only; consumer: BoundedPowers.mu_length_blocks_ge
   proof_shape: mu_length_blocks_ge: bind-only; consumer: BoundedPowers.boundedPQ_image_scale
   proof_shape: boundedPQ_image_scale: content; escape_witness: D5.S1.Words.Episturmian.MorphicDecomposition.central_Justin; consumer: BoundedPowers.cDelta_periodic_factor_bound
   proof_shape: wordPrefix_subinterval: bind-only; consumer: BoundedPowers.morphic_periodic_factor_bound
   proof_shape: morphic_periodic_factor_bound: content; escape_witness: D5.S1.Words.Episturmian.BoundedPowers.extendedMu_period_lift; consumer: BoundedPowers.cDelta_periodic_factor_bound
   proof_shape: cDelta_periodic_factor_bound: content; escape_witness: D5.S1.Words.Episturmian.BoundedPowers.extendedMu_period_lift; consumer: BoundedPowers.boundedPQ_boundedPowers
   definition: BoundedPowers; consumer: BoundedPowers.dio_finite_of_bounded_powers
   proof_shape: dio_finite_of_bounded_powers: bind-only; consumer: DiophantineExponentCriterion.result
   proof_shape: boundedPowers_of_language_eq: bind-only; consumer: DiophantineExponentCriterion.result
   proof_shape: fractionalPower_period: bind-only; consumer: BoundedPowers.boundedPQ_boundedPowers
   proof_shape: boundedPQ_boundedPowers: content; escape_witness: D5.S1.Words.Episturmian.BoundedPowers.extendedMu_period_lift; consumer: DiophantineExponentCriterion.result
   Direct frozen dependencies (pre-existing): D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs; D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor; sha256:54f2f8a1cd3a83f896d4018ef9821e5aa1b6046bd757ec6a999734a691651d1c | D5/S1/Words/Powers/WordPower; D5.S1.Words.Powers.length_wordPower; sha256:debf5e4132f97f82101c3032c0cf4922d3f005aae64c4067de34e835705ee5bf | D5/S1/Words/Powers/WordPower; D5.S1.Words.Powers.wordPower; sha256:a6e228e7ee6ecdc474ee0b218a6a0c370496359d57e770a78cc40f1991acc416 | D5/S1/Words/Powers/WordPower; D5.S1.Words.Powers.wordPower_period_getElem?; sha256:d9c6a06ea421449d240a7406ecf38761aeedd1293e31e9ba625eece0556d16cd
   Finite prefixes use the existing factor operator at start zero.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16158
-/

import D5.S1.Words.Episturmian.MorphicDecomposition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Episturmian.BoundedPowers
open D5.S1.Words.Episturmian.MorphicDecomposition
variable {d : Nat}

 def imagePrefix (s : Nat → Fin d) (f : Fin d → List (Fin d)) (k : Nat) : List (Fin d) :=
   ((fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) s k).flatMap f

 theorem imagePrefix_add (s : Nat → Fin d) (f : Fin d → List (Fin d)) (k j : Nat) :
    imagePrefix s f (k+j) = imagePrefix s f k ++ imagePrefix (fun i => s (k+i)) f j := by
  simp only [imagePrefix, wordPrefix_append, List.flatMap_append]

 theorem imagePrefix_succ (s : Nat → Fin d) (f : Fin d → List (Fin d)) (k : Nat) :
    imagePrefix s f (k+1) = imagePrefix s f k ++ f (s k) := by
  rw [imagePrefix_add]
  simp [imagePrefix, D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor]

 theorem imagePrefix_length_ge (s : Nat → Fin d) (f : Fin d → List (Fin d))
    (hpos : ∀ z, 0 < (f z).length) (k : Nat) : k ≤ (imagePrefix s f k).length := by
  let L := (D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor s 0 k).map (fun z => (f z).length)
  have hL : ∀ i ∈ L, 1 ≤ i := by
    intro i hi
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hi
    exact hpos z
  have h := List.length_le_sum_of_one_le L hL
  simpa [L, imagePrefix, D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor,
    List.length_flatMap, List.map_map, Function.comp_def] using h

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

def ConstantBlock (Delta : Nat → Fin d) (i a : Nat) : Prop :=
  ∀ j < a, Delta (i+j) = Delta i

def RunStart (Delta : Nat → Fin d) (i : Nat) : Prop :=
  i = 0 ∨ Delta (i-1) ≠ Delta i

theorem unboundedPQ_iff_long_blocks (Delta : Nat → Fin d) :
    ¬ BoundedPQ Delta ↔ ∀ a : Nat, ∃ i, ConstantBlock Delta i a := by
  classical
  simp only [BoundedPQ, not_exists, not_forall, not_exists, not_and,
    not_not, ConstantBlock]

 theorem constant_block_at_run_start (Delta : Nat → Fin d) (i a : Nat)
    (hc : ConstantBlock Delta i a) :
    ∃ n ≤ i, RunStart Delta n ∧
      ∀ j < i+a-n, Delta (n+j) = Delta n := by
  classical
  let P : Nat → Prop := fun n => n ≤ i ∧ ∀ j, n ≤ j → j ≤ i → Delta j = Delta i
  have hp : ∃ n, P n := by
    refine ⟨i, le_rfl, ?_⟩
    intro j hj hji
    have he : j = i := by omega
    simp [he]
  let n := Nat.find hp
  have hspec : P n := Nat.find_spec hp
  have hni : n ≤ i := hspec.1
  have hnx : Delta n = Delta i := hspec.2 n le_rfl hni
  have hs : RunStart Delta n := by
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      intro he
      have hprev : P (n-1) := by
        refine ⟨by omega, ?_⟩
        intro j hj hji
        by_cases hjn : n ≤ j
        · exact hspec.2 j hjn hji
        · have hej : j = n-1 := by omega
          rw [hej, he, hnx]
      have hmin : n ≤ n-1 := Nat.find_min' hp hprev
      omega
  refine ⟨n, hni, hs, ?_⟩
  intro j hj
  rw [hnx]
  by_cases hji : n+j ≤ i
  · exact hspec.2 (n+j) (by omega) hji
  · have hja : n+j-i < a := by omega
    have hh := hc (n+j-i) hja
    have he : i+(n+j-i) = n+j := by omega
    rwa [he] at hh

 theorem cDelta_constant_run_cover (Delta : Nat → Fin d) (n a : Nat)
    (ha : 0 < a) (hstart : n = 0 ∨ Delta (n-1) ≠ Delta n)
    (hc : ∀ j < a, Delta (n+j) = Delta n) :
    Nonempty (PeriodicRunCover (cDelta Delta) (mu Delta n (Delta n)).length a) := by
  let x := Delta n
  let A := mu Delta n x
  let B := mu Delta n
  let f := mu Delta (n+a)
  let tail := cDelta (fun j => Delta (n+a+j))
  have hfx : f x = A := by
    simpa [f, A] using mu_constant_run Delta n a x x hc
  have hf : ∀ z, z ≠ x → f z = (fun A a => D5.S1.Words.Powers.wordPower a A) A a ++ B z := by
    intro z hz
    simpa only [f, A, B, if_neg hz] using mu_constant_run Delta n a x z hc
  have hB : ∀ z, (B z).length ≤ 2*A.length := by
    intro z
    exact mu_length_at_run_start Delta n hstart z
  exact powerChunks_cover tail (cDelta Delta) f A a (cDelta_morphicImage Delta (n+a))
    (mu_length_pos Delta (n+a)) (fun p => powerChunk_exists tail f A B x a p ha hfx hf hB)

 theorem not_boundedPQ_dio_top (Delta t : Nat → Fin d)
    (hlang : Lang t = Lang (cDelta Delta)) (hunbounded : ¬ BoundedPQ Delta) : dio t = ⊤ := by
  apply arbitrarily_dense_powers_dio_top t (cDelta Delta) hlang
  intro M hM
  let a := M*(M+3)
  have ha : 0 < a := by dsimp [a]; nlinarith
  obtain ⟨i, hi⟩ := (unboundedPQ_iff_long_blocks Delta).mp hunbounded a
  obtain ⟨n, hni, hs, hc⟩ := constant_block_at_run_start Delta i a hi
  have hconst : ∀ j < a, Delta (n+j) = Delta n := by
    intro j hj
    exact hc j (by omega)
  exact ⟨(mu Delta n (Delta n)).length, a, mu_length_pos Delta n (Delta n), le_rfl,
    cDelta_constant_run_cover Delta n a ha hs hconst⟩

 theorem dio_finite_implies_boundedPQ (Delta t : Nat → Fin d)
    (hlang : Lang t = Lang (cDelta Delta)) (hfin : dio t < ⊤) : BoundedPQ Delta := by
  by_contra hn
  rw [not_boundedPQ_dio_top Delta t hlang hn] at hfin
  exact (lt_irrefl _ hfin)

 theorem morphicImage_block_get (s t : Nat → Fin d) (f : Fin d → List (Fin d))
    (hi : MorphicImage s t f) (k j : Nat) (hj : j < (f (s k)).length) :
    t ((imagePrefix s f k).length+j) = (f (s k))[j] := by
  apply morphicImage_segment s t f hi k 1 (f (s k)) [] _ j hj
  simp [imagePrefix, D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor]

 theorem morphicImage_block_position (s t : Nat → Fin d) (f : Fin d → List (Fin d))
    (hi : MorphicImage s t f) (hpos : ∀ z, 0 < (f z).length) (n : Nat) :
    ∃ k j, ∃ hj : j < (f (s k)).length,
      n = (imagePrefix s f k).length+j ∧ t n = (f (s k))[j] := by
  classical
  have hex : ∃ m, n < (imagePrefix s f m).length :=
    ⟨n+1, lt_of_lt_of_le (by omega) (imagePrefix_length_ge s f hpos _)⟩
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  have hmpos : 0 < m := by
    by_contra hh
    have hm0 : m = 0 := by omega
    change n < (imagePrefix s f m).length at hm
    rw [hm0] at hm
    simp [imagePrefix,D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add] at hm
  have hprev : (imagePrefix s f (m-1)).length ≤ n := by
    have hn := Nat.find_min hex (by omega : m-1 < m)
    omega
  have hsucc : imagePrefix s f m = imagePrefix s f (m-1) ++ f (s (m-1)) := by
    rw [show m = m-1+1 by omega, imagePrefix_succ]
    congr 1 <;> congr 1 <;> omega
  rw [hsucc,List.length_append] at hm
  let k := m-1
  let j := n-(imagePrefix s f k).length
  have he : n = (imagePrefix s f k).length+j := by dsimp [j,k]; omega
  have hj : j < (f (s k)).length := by dsimp [j,k]; omega
  exact ⟨k,j,hj,he,by rw [he]; exact morphicImage_block_get s t f hi k j hj⟩

 theorem Hword_prefix_decode (x : Fin d) (w s : List (Fin d))
    (hs : s <+: Hword x w) (hlast : ∃ p, s = p ++ [x]) :
    ∃ v, v <+: w ∧ s = Hword x v := by
   have hrev := hs.reverse
   rw [Hword_reverse] at hrev
   have hstart : ∃ r, s.reverse = x :: r := by
     obtain ⟨p,rfl⟩ := hlast
     exact ⟨p.reverse, by simp⟩
   obtain ⟨v,hv,he⟩ := Hword_suffix_decode x w.reverse s.reverse hrev hstart
   refine ⟨v.reverse,?_,?_⟩
   · simpa using hv.reverse
   · have hh := congrArg List.reverse he
     simpa [Hword_reverse] using hh

 theorem Hword_prefix_reflect (x : Fin d) (u w : List (Fin d))
    (h : Hword x u <+: Hword x w) : u <+: w := by
   obtain ⟨v,hv,he⟩ := Hword_prefix_decode x w (Hword x u) h ⟨Lword x u,rfl⟩
   have huv := Hword_injective x he
   rwa [← huv] at hv

 theorem Hword_period_desubstitute (x : Fin d) (w : List (Fin d)) (p : Nat)
    (hp : 0 < p) (hplen : p < (Hword x w).length) (hperiod : List.HasPeriod (Hword x w) p) :
    ∃ v : List (Fin d), v <+: w ∧ 0 < v.length ∧ (Lword x v).length = p ∧
      List.HasPeriod w v.length := by
   have h0 : 0 < (Hword x w).length := by omega
   have hget := (List.hasPeriod_iff_getElem?.mp hperiod) 0 (by omega)
   have hfirst : (Hword x w)[0] = x := by
     obtain ⟨r,hr⟩ := Hword_starts x w
     simp only [hr,List.getElem_cons_zero]
   rw [Nat.zero_add,List.getElem?_eq_getElem h0,List.getElem?_eq_getElem hplen] at hget
   have hx : (Hword x w)[p] = x := (Option.some.inj hget).symm.trans hfirst
   have hlast : ∃ r, (Hword x w).take (p+1) = r ++ [x] := by
     refine ⟨(Hword x w).take p,?_⟩
     rw [List.take_succ_eq_append_getElem hplen,hx]
   obtain ⟨v,hv,he⟩ := Hword_prefix_decode x w ((Hword x w).take (p+1))
     (List.take_prefix _ _) hlast
   have hlen : (Lword x v).length = p := by
     have hh := congrArg List.length he
     rw [List.length_take,Nat.min_eq_left (by omega : p+1 ≤ (Hword x w).length)] at hh
     simp only [Hword,List.length_append,List.length_singleton] at hh
     omega
   have hvpos : 0 < v.length := by
     by_contra h
     have hn : v=[] := List.length_eq_zero_iff.mp (by omega)
     have hlen0 : (Lword x v).length=0 := by simp [hn,Lword]
     omega
   have htake : (Hword x w).take p = Lword x v := by
     have hh := congrArg (List.take p) he
     simp only [List.take_take,Nat.min_eq_left (by omega : p ≤ p+1),Hword] at hh
     rw [← hlen,List.take_left] at hh
     simpa only [hlen,Hword] using hh
   have hpre : Hword x w <+: Hword x (v++w) := by
     have hh : Hword x w <+: (Hword x w).take p ++ Hword x w := hperiod
     rw [htake] at hh
     simpa only [Hword,Lword_append,List.append_assoc] using hh
   refine ⟨v,hv,hvpos,hlen,?_⟩
   change w <+: w.take v.length ++ w
   have hvtake : w.take v.length = v := by
     obtain ⟨r,hr⟩ := hv
     rw [← hr,List.take_left]
   rw [hvtake]
   exact Hword_prefix_reflect x w (v++w) hpre

 noncomputable def extendedMu (Delta : Nat → Fin d) (n : Nat) (w : List (Fin d)) : List (Fin d) :=
   muWord Delta n w ++ central Delta n

 theorem muWord_shift (Delta : Nat → Fin d) (n : Nat) (w : List (Fin d)) :
    muWord Delta (n+1) w = Lword (Delta 0) (muWord (fun j => Delta (j+1)) n w) := by
   simp only [muWord,Lword,List.flatMap_assoc]
   congr 1
   funext z
   exact mu_shift Delta n z

 theorem extendedMu_shift (Delta : Nat → Fin d) (n : Nat) (w : List (Fin d)) :
    extendedMu Delta (n+1) w = Hword (Delta 0) (extendedMu (fun j => Delta (j+1)) n w) := by
   simp only [extendedMu,muWord_shift,central_Justin_shift,Hword,Lword_append,List.append_assoc]

 theorem Hword_prefix (x : Fin d) {u w : List (Fin d)} (hu : u <+: w) :
    Hword x u <+: Hword x w := by
   obtain ⟨r,rfl⟩ := hu
   obtain ⟨s,hs⟩ := Hword_starts x r
   refine ⟨s,?_⟩
   change (Lword x u ++ [x]) ++ s = Lword x (u++r) ++ [x]
   rw [Lword_append]
   simp only [List.append_assoc]
   change Lword x u ++ x::s = Lword x u ++ Hword x r
   rw [hs]

 theorem central_prefix_extendedMu (Delta : Nat → Fin d) (n : Nat) (w : List (Fin d)) :
    central Delta n <+: extendedMu Delta n w := by
   induction n generalizing Delta with
   | zero => simp [central]
   | succ n ih =>
     rw [central_Justin_shift,extendedMu_shift]
     exact Hword_prefix _ (ih _)

 theorem muWord_prefix (Delta : Nat → Fin d) (n : Nat) {u w : List (Fin d)}
    (hu : u <+: w) : muWord Delta n u <+: muWord Delta n w :=
   hu.flatMap (mu Delta n)

 theorem extendedMu_period_lift (Delta : Nat → Fin d) (n : Nat) (w : List (Fin d)) (p : Nat)
    (hp : 0 < p) (hlen : p+(central Delta n).length < (extendedMu Delta n w).length)
    (hperiod : List.HasPeriod (extendedMu Delta n w) p) :
    ∃ v : List (Fin d), v <+: w ∧ 0 < v.length ∧ (muWord Delta n v).length = p ∧
      List.HasPeriod w v.length := by
   induction n generalizing Delta p with
   | zero =>
     have hpw : p < w.length := by simpa [extendedMu,muWord,mu,central] using hlen
     have hper : List.HasPeriod w p := by simpa [extendedMu,muWord,mu,central] using hperiod
     refine ⟨w.take p,List.take_prefix _ _,?_,?_,?_⟩
     · simp only [List.length_take,Nat.min_eq_left (Nat.le_of_lt hpw)]
       exact hp
     · simp [muWord,mu,Nat.min_eq_left (Nat.le_of_lt hpw)]
     · simpa only [List.length_take,Nat.min_eq_left (Nat.le_of_lt hpw)] using hper
   | succ n ih =>
     let tail := fun j => Delta (j+1)
     let x := Delta 0
     let E := extendedMu tail n w
     let C := central tail n
     have hext : extendedMu Delta (n+1) w = Hword x E := extendedMu_shift Delta n w
     have hcent : central Delta (n+1) = Hword x C := central_Justin_shift Delta n
     rw [hext] at hperiod
     rw [hext,hcent] at hlen
     obtain ⟨v0,hv0,hq,hlen0,hperE⟩ := Hword_period_desubstitute x E p hp (by omega) hperiod
     let q := v0.length
     have htake : E.take q = v0 := by
       obtain ⟨r,hr⟩ := hv0
       rw [← hr,List.take_left]
     have hsplit : E = v0 ++ E.drop q := by rw [← htake,List.take_append_drop]
     have hC : C <+: E := central_prefix_extendedMu tail n w
     have hdrop : E.drop q <+: E := hperE.drop_prefix q
     have hL : (Lword x C).length < (Lword x (E.drop q)).length := by
       simp only [Hword,List.length_append,List.length_singleton] at hlen
       have hh : (Lword x E).length = p+(Lword x (E.drop q)).length := by
         conv_lhs => rw [hsplit,Lword_append,List.length_append]
         rw [hlen0]
       rw [hh] at hlen
       omega
     have hlenE : q+C.length < E.length := by
       by_contra hh
       have hdropLen : (E.drop q).length ≤ C.length := by simp only [List.length_drop]; omega
       have hpre : E.drop q <+: C := by
         exact List.prefix_of_prefix_length_le hdrop hC hdropLen
       have hl := (Lword_prefix x hpre).length_le
       omega
     obtain ⟨v,hv,hvpos,hlenv,hperw⟩ := ih tail q hq hlenE hperE
     have himage : muWord tail n v <+: E :=
       (muWord_prefix tail n hv).trans (List.prefix_append _ _)
     have hiV0 : muWord tail n v <+: v0 :=
       List.prefix_of_prefix_length_le himage hv0 (by rw [hlenv])
     have heq : muWord tail n v = v0 := hiV0.eq_of_length (by rw [hlenv])
     refine ⟨v,hv,hvpos,?_,hperw⟩
     rw [muWord_shift]
     change (Lword x (muWord tail n v)).length = p
     rw [heq,hlen0]

 theorem morphicImage_shift (s t : Nat → Fin d) (f : Fin d → List (Fin d))
    (hi : MorphicImage s t f) (k : Nat) :
    MorphicImage (fun j => s (k+j)) (fun j => t ((imagePrefix s f k).length+j)) f := by
   intro r
   have hk := hi k
   have hkr := hi (k+r)
   change (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) t (imagePrefix s f k).length = imagePrefix s f k at hk
   change (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) t (imagePrefix s f (k+r)).length = imagePrefix s f (k+r) at hkr
   rw [imagePrefix_add,List.length_append,wordPrefix_append,hk] at hkr
   exact (List.append_cancel_left hkr)

 theorem central_prefix_imagePrefix (Delta : Nat → Fin d) (n : Nat) (s : Nat → Fin d)
    (k : Nat) (hk : (central Delta n).length ≤ k) :
    central Delta n <+: imagePrefix s (mu Delta n) k := by
   let W := (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) s k
   have h0 := central_prefix_extendedMu Delta n W
   have h1 : muWord Delta n W <+: extendedMu Delta n W := List.prefix_append _ _
   have hl : (central Delta n).length ≤ (muWord Delta n W).length := by
     exact hk.trans (imagePrefix_length_ge s (mu Delta n) (mu_length_pos Delta n) k)
   exact List.prefix_of_prefix_length_le h0 h1 hl

 theorem morphicImage_central_prefix (Delta : Nat → Fin d) (n : Nat) (s t : Nat → Fin d)
    (hi : MorphicImage s t (mu Delta n)) :
    (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) t (central Delta n).length = central Delta n := by
   let k := (central Delta n).length
   have hpre := central_prefix_imagePrefix Delta n s k le_rfl
   have h := hi k
   change (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) t (imagePrefix s (mu Delta n) k).length = imagePrefix s (mu Delta n) k at h
   have hk : (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) t (central Delta n).length <+: imagePrefix s (mu Delta n) k := by
     rw [← h]
     exact wordPrefix_isPrefix t hpre.length_le
   have he : (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) t (central Delta n).length <+: central Delta n :=
     List.prefix_of_prefix_length_le hk hpre (by simp [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add])
   exact he.eq_of_length (by simp [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add])

 theorem morphicImage_extended_prefix (Delta : Nat → Fin d) (n : Nat) (s t : Nat → Fin d)
    (hi : MorphicImage s t (mu Delta n)) (k : Nat) :
    (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) t (extendedMu Delta n ((fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) s k)).length = extendedMu Delta n ((fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) s k) := by
   have h0 := hi k
   change (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) t (imagePrefix s (mu Delta n) k).length = imagePrefix s (mu Delta n) k at h0
   have h1 := morphicImage_central_prefix Delta n _ _ (morphicImage_shift s t (mu Delta n) hi k)
   simp only [extendedMu,List.length_append,wordPrefix_append]
   exact congrArg₂ List.append h0 h1

 theorem imagePrefix_length_strictMono (s : Nat → Fin d) (f : Fin d → List (Fin d))
    (hpos : ∀ z, 0 < (f z).length) : StrictMono (fun k => (imagePrefix s f k).length) := by
   apply strictMono_nat_of_lt_succ
   intro k
   rw [imagePrefix_succ,List.length_append]
   have := hpos (s k)
   omega

 theorem extendedMu_segment_occurrence (Delta : Nat → Fin d) (n : Nat) (s t : Nat → Fin d)
    (hi : MorphicImage s t (mu Delta n)) (k l : Nat) (hkl : k ≤ l) :
    (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => t ((imagePrefix s (mu Delta n) k).length+j))
      ((imagePrefix s (mu Delta n) l).length-(imagePrefix s (mu Delta n) k).length+(central Delta n).length) =
      extendedMu Delta n ((fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => s (k+j)) (l-k)) := by
   have hs := morphicImage_shift s t (mu Delta n) hi k
   have hp := morphicImage_extended_prefix Delta n _ _ hs (l-k)
   have hl := congrArg List.length (imagePrefix_add s (mu Delta n) k (l-k))
   rw [Nat.add_sub_of_le hkl,List.length_append] at hl
   have he : (imagePrefix s (mu Delta n) l).length-(imagePrefix s (mu Delta n) k).length =
       (imagePrefix (fun j => s (k+j)) (mu Delta n) (l-k)).length := by omega
   rw [he]
   simpa only [extendedMu,List.length_append,muWord,imagePrefix] using hp

 theorem mu_length_uniform_ratio (Delta : Nat → Fin d) (B : Nat)
    (hB : ∀ i, ∃ j < B, Delta (i+j) ≠ Delta i) (n : Nat) (u v : Fin d) :
    (mu Delta n u).length ≤ (B+2)*(mu Delta n v).length := by
   cases n with
   | zero => simp [mu]
   | succ n =>
     have hc : ConstantBlock Delta n 1 := by
       intro j hj
       have he : j=0 := by omega
       simp [he]
     obtain ⟨m,hm,hs,hconst⟩ := constant_block_at_run_start Delta n 1 hc
     let a := n+1-m
     have ha : 0 < a := by dsimp [a]; omega
     have hx : Delta m = Delta n := by
       have hh := hconst (n-m) (by omega)
       simpa only [Nat.add_sub_of_le hm] using hh.symm
     have hab : a < B := by
       obtain ⟨j,hj,hne⟩ := hB m
       by_contra hh
       exact hne (hconst j (by dsimp [a] at hh; omega))
     have he : m+a=n+1 := by dsimp [a]; omega
     have hrun : ∀ j < a, Delta (m+j) = Delta m := hconst
     have hqpos := mu_length_pos Delta m (Delta m)
     have hu := mu_length_at_run_start Delta m hs u
     have hv := mu_length_at_run_start Delta m hs v
     have huimage := mu_constant_run Delta m a (Delta m) u hrun
     have hvimage := mu_constant_run Delta m a (Delta m) v hrun
     rw [he] at huimage hvimage
     have hupper : (mu Delta (n+1) u).length ≤ (a+2)*(mu Delta m (Delta m)).length := by
       rw [huimage]
       split_ifs <;> (try simp only [List.length_append,D5.S1.Words.Powers.length_wordPower]) <;> nlinarith
     have hlower : (mu Delta m (Delta m)).length ≤ (mu Delta (n+1) v).length := by
       rw [hvimage]
       split_ifs <;> (try simp only [List.length_append,D5.S1.Words.Powers.length_wordPower]) <;> nlinarith
     nlinarith

 theorem central_succ_morphic (Delta : Nat → Fin d) (n : Nat) :
    central Delta (n+1) = mu Delta n (Delta n) ++ central Delta n := by
   rw [central_morphic_finite Delta n 1]
   have hc : central (fun j => Delta (n+j)) 1 = [Delta n] := by
     simp only [central,List.nil_append,Nat.add_zero]
     exact palClosure_of_palindrome _ (List.Palindrome.singleton _)
   rw [hc]
   simp [muWord]

 theorem image_sum_step (Delta : Nat → Fin d) (n : Nat) :
    (∑ z : Fin d, (mu Delta (n+1) z).length) =
      (∑ z : Fin d, (mu Delta n z).length) + (d-1)*(mu Delta n (Delta n)).length := by
   have he : ∀ z : Fin d, (mu Delta (n+1) z).length =
       (mu Delta n z).length + if z=Delta n then 0 else (mu Delta n (Delta n)).length := by
     intro z
     rw [mu_length_step]
     split_ifs <;> omega
   simp_rw [he]
   rw [Finset.sum_add_distrib]
   congr 1
   have hcard : ({z : Fin d | ¬z=Delta n} : Finset (Fin d)).card = d-1 := by
     have he : ({z : Fin d | ¬z=Delta n} : Finset (Fin d)) = Finset.univ.erase (Delta n) := by
       ext z
       simp
     rw [he,Finset.card_erase_of_mem (by simp)]
     simp
   simp [Finset.sum_ite,hcard]

 theorem central_length_le_image_sum (Delta : Nat → Fin d) (hd : 2 ≤ d) (n : Nat) :
    (central Delta n).length ≤ ∑ z : Fin d, (mu Delta n z).length := by
   induction n with
   | zero => simp [central]
   | succ n ih =>
     rw [central_succ_morphic,List.length_append,image_sum_step]
     have hh : 1 ≤ d-1 := by omega
     nlinarith

 theorem mu_length_increases_over_B (Delta : Nat → Fin d) (B : Nat)
    (hB : ∀ i, ∃ j < B, Delta (i+j) ≠ Delta i) (n : Nat) (z : Fin d) :
    (mu Delta n z).length+1 ≤ (mu Delta (n+B) z).length := by
   have hj : ∃ j < B, z ≠ Delta (n+j) := by
     by_cases hz : z=Delta n
     · obtain ⟨j,hj,hne⟩ := hB n
       exact ⟨j,hj,by simpa [hz] using hne.symm⟩
     · obtain ⟨j,hj,hne⟩ := hB n
       exact ⟨0,by omega,by simpa using hz⟩
   obtain ⟨j,hj,hne⟩ := hj
   have hbefore := mu_length_mono Delta z (by omega : n ≤ n+j)
   have hafter := mu_length_mono Delta z (by omega : n+j+1 ≤ n+B)
   have hstep := mu_length_step Delta (n+j) z
   have hpos := mu_length_pos Delta (n+j) (Delta (n+j))
   rw [if_neg hne] at hstep
   omega

 theorem mu_length_blocks_ge (Delta : Nat → Fin d) (B : Nat)
    (hB : ∀ i, ∃ j < B, Delta (i+j) ≠ Delta i) (k : Nat) (z : Fin d) :
    k+1 ≤ (mu Delta (k*B) z).length := by
   induction k with
   | zero => simp [mu]
   | succ k ih =>
     have hh := mu_length_increases_over_B Delta B hB (k*B) z
     rw [Nat.add_mul,Nat.one_mul]
     omega

 theorem boundedPQ_image_scale (Delta : Nat → Fin d) (B p : Nat) (hd : 2 ≤ d) (hp : 0 < p)
    (hB : ∀ i, ∃ j < B, Delta (i+j) ≠ Delta i) :
    ∃ n, (∀ z, p < (mu Delta n z).length) ∧
      (∀ z, (mu Delta n z).length ≤ 2*(B+2)*p) ∧
      (central Delta n).length ≤ d*(2*(B+2)*p) := by
   classical
   have hex : ∃ n, ∀ z : Fin d, p < (mu Delta n z).length := by
     refine ⟨p*B,?_⟩
     intro z
     have := mu_length_blocks_ge Delta B hB p z
     omega
   let n := Nat.find hex
   have hn : ∀ z : Fin d, p < (mu Delta n z).length := Nat.find_spec hex
   have hnpos : 0 < n := by
     by_contra hh
     have hn0 : n=0 := by omega
     have hz := hn (Delta 0)
     rw [hn0] at hz
     simp [mu] at hz
     omega
   have hprev := Nat.find_min hex (by omega : n-1<n)
   push_neg at hprev
   obtain ⟨v,hv⟩ := hprev
   have hprevAll : ∀ z, (mu Delta (n-1) z).length ≤ (B+2)*p := by
     intro z
     have hh := mu_length_uniform_ratio Delta B hB (n-1) z v
     nlinarith
   have hupper : ∀ z, (mu Delta n z).length ≤ 2*(B+2)*p := by
     intro z
     have he : n=n-1+1 := by omega
     rw [he,mu_length_step]
     have h0 := hprevAll z
     have h1 := hprevAll (Delta (n-1))
     split_ifs <;> nlinarith
   refine ⟨n,hn,hupper,?_⟩
   have hs := central_length_le_image_sum Delta hd n
   have hsum : (∑ z : Fin d, (mu Delta n z).length) ≤ d*(2*(B+2)*p) := by
     calc
       _ ≤ ∑ z : Fin d, 2*(B+2)*p := Finset.sum_le_sum (fun z _ => hupper z)
       _ = _ := by simp
   exact hs.trans hsum



 theorem wordPrefix_subinterval (x : Nat → Fin d) (L a ell : Nat) (h : a+ell ≤ L) :
    (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => x (a+j)) ell <:+: (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) x L := by
   refine ⟨(fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) x a,(fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => x (a+ell+j)) (L-(a+ell)),?_⟩
   have he : L=a+ell+(L-(a+ell)) := by omega
   conv_rhs => rw [he,wordPrefix_append,wordPrefix_append]

 theorem morphic_periodic_factor_bound (Delta : Nat → Fin d) (n : Nat) (s t : Nat → Fin d)
    (hi : MorphicImage s t (mu Delta n)) (p Q b ell : Nat) (hp : 0 < p)
    (hsmall : ∀ z, p < (mu Delta n z).length)
    (hlarge : ∀ z, (mu Delta n z).length ≤ Q)
    (hperiod : List.HasPeriod ((fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => t (b+j)) ell) p) :
    ell ≤ p+(central Delta n).length+2*Q := by
   by_contra hnot
   have hlong : p+(central Delta n).length+2*Q < ell := by omega
   let f := mu Delta n
   let C := (central Delta n).length
   change ∀ z, (f z).length ≤ Q at hlarge
   obtain ⟨k,j,hj,hbj,hget⟩ := morphicImage_block_position s t f hi (mu_length_pos Delta n) b
   let K := k+1
   let start := (imagePrefix s f K).length
   have hstart0 : b ≤ start := by
     dsimp [start,K]
     rw [imagePrefix_succ,List.length_append]
     omega
   have hstart : start ≤ b+Q := by
     dsimp [start,K]
     rw [imagePrefix_succ,List.length_append]
     have hh := hlarge (s k)
     omega
   let lastpos := b+ell-C
   obtain ⟨l,r,hr,hel,hgetl⟩ := morphicImage_block_position s t f hi (mu_length_pos Delta n) lastpos
   let ending := (imagePrefix s f l).length
   have hend : ending+C ≤ b+ell := by dsimp [ending,lastpos,C] at hel ⊢; omega
   have hendLarge : b+ell < ending+Q+C := by
     have hh := hlarge (s l)
     dsimp [lastpos,ending,C] at hel ⊢
     omega
   have hstartEnd : start+p < ending := by dsimp [C] at hendLarge; omega
   have hKl : K ≤ l := by
     by_contra hh
     have hm := imagePrefix_length_strictMono s f (mu_length_pos Delta n) (by omega : l<K)
     change ending < start at hm
     omega
   let input := (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => s (K+j)) (l-K)
   let W := extendedMu Delta n input
   have hWlen : W.length = ending-start+C := by
     have h := congrArg List.length (imagePrefix_add s f K (l-K))
     rw [Nat.add_sub_of_le hKl,List.length_append] at h
     dsimp [W,extendedMu,input,C]
     simp only [List.length_append]
     change (imagePrefix (fun j => s (K+j)) f (l-K)).length + (central Delta n).length = _
     dsimp [ending,start]
     omega
   have hocc : (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => t (start+j)) W.length = W := by
     have hh := extendedMu_segment_occurrence Delta n s t hi K l hKl
     rw [← hWlen] at hh
     exact hh
   let a := start-b
   have hfit : a+W.length ≤ ell := by dsimp [a]; rw [hWlen]; omega
   have hinfix : W <:+: (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => t (b+j)) ell := by
     have hh := wordPrefix_subinterval (fun j => t (b+j)) ell a W.length hfit
     have he : (fun j => t (b+(a+j))) = fun j => t (start+j) := by
       funext j
       congr 1
       dsimp [a]
       omega
     rw [he,hocc] at hh
     exact hh
   have hperW : List.HasPeriod W p := hperiod.infix hinfix
   have hlenW : p+(central Delta n).length < W.length := by rw [hWlen]; dsimp [C]; omega
   obtain ⟨v,hv,hvpos,hvlen,hvper⟩ := extendedMu_period_lift Delta n input p hp hlenW hperW
   cases v with
   | nil => simp at hvpos
   | cons z v =>
     have hh := hsmall z
     simp only [muWord,List.flatMap_cons,List.length_append] at hvlen
     omega

 theorem cDelta_periodic_factor_bound (Delta : Nat → Fin d) (B : Nat)
    (hB : ∀ i, ∃ j < B, Delta (i+j) ≠ Delta i) (hd : 2 ≤ d)
    (p b ell : Nat) (hp : 0 < p)
    (hper : List.HasPeriod ((fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => cDelta Delta (b+j)) ell) p) :
    ell ≤ (1+2*(d+2)*(B+2))*p := by
   obtain ⟨n,hsmall,hlarge,hcentral⟩ := boundedPQ_image_scale Delta B p hd hp hB
   have hh := morphic_periodic_factor_bound Delta n _ _ (cDelta_morphicImage Delta n)
     p (2*(B+2)*p) b ell hp hsmall hlarge hper
   nlinarith



def BoundedPowers (x : Nat → Fin d) : Prop :=
  ∃ C : NNReal, ∀ n (V : List (Fin d)) (hV : V ≠ []) (ell : Nat),
    V.length ≤ ell → (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => x (n+j)) ell = fractionalPower V hV ell →
    (ell : Real) / V.length ≤ (C : Real)

theorem dio_finite_of_bounded_powers (x : Nat → Fin d) (hb : BoundedPowers x) :
    dio x < ⊤ := by
  obtain ⟨C, hC⟩ := hb
  have hbound : dio x ≤ (C : ENNReal) := by
    apply iSup_le
    intro rho
    apply iSup_le
    intro hadm
    obtain ⟨U, V, ell, hV, hvell, hlength, hword, hratio⟩ := hadm 0
    have htail : (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => x (U.length+j)) ell = fractionalPower V hV ell := by
      rw [wordPrefix_append] at hword
      exact (List.append_inj hword (by simp [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add])).2
    have hp := hC U.length V hV ell hvell htail
    have hq : (0 : Real) < V.length := by exact_mod_cast List.length_pos_iff.mpr hV
    have hratio2 : (U.length+ell : Real)/(U.length+V.length) ≤ (ell : Real)/V.length := by
      apply (div_le_div_iff₀ (by positivity) hq).2
      have hvellr : (V.length : Real) ≤ ell := by exact_mod_cast hvell
      nlinarith [Nat.cast_nonneg (α := Real) U.length]
    apply ENNReal.coe_le_coe.mpr
    exact_mod_cast hratio.trans (hratio2.trans hp)
  exact lt_of_le_of_lt hbound ENNReal.coe_lt_top

 theorem boundedPowers_of_language_eq (t x : Nat → Fin d)
    (hlang : Lang t = Lang x) (hb : BoundedPowers x) : BoundedPowers t := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨C, ?_⟩
  intro n V hV ell hvell he
  let W := (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => t (n+j)) ell
  have hm : W ∈ Lang t := by
    refine ⟨n, ?_⟩
    intro j
    rcases j with ⟨j, hj⟩
    simp [W, D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add, List.get_eq_getElem]
  rw [hlang] at hm
  obtain ⟨m, hm⟩ := hm
  have hx : (fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => x (m+j)) ell = W := by
    apply List.ext_getElem
    · simp [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add, W]
    · intro j hj hj'
      have hjell : j < ell := by simpa [D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add] using hj
      have hh := hm ⟨j, by simpa [W,D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add] using hjell⟩
      simpa [W,D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor, Nat.zero_add,List.get_eq_getElem] using hh.symm
  exact hC m V hV ell hvell (hx.trans he)


 theorem fractionalPower_period (V : List (Fin d)) (hV : V ≠ []) (ell : Nat) :
    List.HasPeriod (fractionalPower V hV ell) V.length := by
   apply List.hasPeriod_iff_getElem?.mpr
   intro i hi
   have hi0 : i < ell := by simp only [fractionalPower,List.length_map,List.length_range] at hi; omega
   have hiq : i+V.length < ell := by simp only [fractionalPower,List.length_map,List.length_range] at hi; omega
   simp only [fractionalPower,List.getElem?_map,List.getElem?_range,hi0,hiq,if_true,Option.map_some]
   congr 1
   congr 1
   simp [Nat.add_mod]

 theorem boundedPQ_boundedPowers (Delta : Nat → Fin d) (hb : BoundedPQ Delta) :
    BoundedPowers (cDelta Delta) := by
   obtain ⟨B,hB⟩ := hb
   have hd : 2 ≤ d := by
     obtain ⟨j,hj,hne⟩ := hB 0
     by_contra hn
     have h0 := (Delta 0).isLt
     have h1 := (Delta (0+j)).isLt
     apply hne
     apply Fin.ext
     omega
   let C := 1+2*(d+2)*(B+2)
   refine ⟨(C : Nat),?_⟩
   intro b V hV ell hle he
   have hp : 0 < V.length := List.length_pos_iff.mpr hV
   have hper : List.HasPeriod ((fun x n => D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs.factor x 0 n) (fun j => cDelta Delta (b+j)) ell) V.length := by
     rw [he]
     exact fractionalPower_period V hV ell
   have hh := cDelta_periodic_factor_bound Delta B hB hd V.length b ell hp hper
   apply (div_le_iff₀ (by exact_mod_cast hp : (0 : Real) < V.length)).2
   exact_mod_cast hh

end D5.S1.Words.Episturmian.BoundedPowers
