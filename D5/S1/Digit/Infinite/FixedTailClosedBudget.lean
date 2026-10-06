/- GID: D5/S1/Digit/Infinite/FixedTailClosedBudget
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/FixedTailClosedBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed legal tails attain the endpoint budget for every finite return word. -/

import D5.S1.Digit.Infinite.ClosedObservationGraphRealization
import D5.S1.Words.Powers.WordPower
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped Topology

namespace D5.S1.Digit.Infinite.FixedTailClosedBudget

open D5.S1.Words.Powers (wordPower)

private def intervalDistance (x l u : ℝ) : ℝ := max (l - x) (max 0 (x - u))

private theorem intervalDistance_nonneg (x l u : ℝ) : 0 ≤ intervalDistance x l u := by
  unfold intervalDistance
  exact (le_max_left _ _).trans (le_max_right _ _)

private theorem affine_endpoint_bound (a b lo hi l u x : ℝ) (hx : x ∈ Set.Icc lo hi) :
    intervalDistance (a * x + b) l u ≤
      max (intervalDistance (a * lo + b) l u)
        (intervalDistance (a * hi + b) l u) := by
  let F : ℝ →ₗ[ℝ] ℝ := LinearMap.mulLeft ℝ a
  have hf : ConvexOn ℝ Set.univ (fun y : ℝ => a * y + b) :=
    (F.convexOn convex_univ).add_const b
  have hfc : ConcaveOn ℝ Set.univ (fun y : ℝ => a * y + b) :=
    (F.concaveOn convex_univ).add_const b
  have hd : ConvexOn ℝ Set.univ (fun y => intervalDistance (a * y + b) l u) :=
    ((convexOn_const l convex_univ).sub hfc).sup
      ((convexOn_const 0 convex_univ).sup (hf.sub (concaveOn_const u convex_univ)))
  exact hd.le_on_segment (Set.mem_univ lo) (Set.mem_univ hi) (Icc_subset_segment hx)

private def returnEval (A : Fin 2 → ℝ) (a : ℝ) (z : List (Fin 2)) (x : ℝ) : ℝ :=
  z.foldr (fun i y => A i + a * y) x

private noncomputable def hullLower (A : Fin 2 → ℝ) (a : ℝ) : ℝ :=
  if 0 ≤ a then min (A 0) (A 1) / (1 - a)
  else (min (A 0) (A 1) + a * max (A 0) (A 1)) / (1 - a ^ 2)

private noncomputable def hullUpper (A : Fin 2 → ℝ) (a : ℝ) : ℝ :=
  if 0 ≤ a then max (A 0) (A 1) / (1 - a)
  else (max (A 0) (A 1) + a * min (A 0) (A 1)) / (1 - a ^ 2)

private theorem returnEval_repeat (A : Fin 2 → ℝ) (a : ℝ)
    (w : List (Fin 2)) (n : ℕ) (x : ℝ) :
    returnEval A a (wordPower n w) x = (returnEval A a w)^[n] x := by
  unfold returnEval wordPower
  rw [List.foldr_flatten]
  have hrepl : List.replicate n w = (List.replicate n ()).map (fun _ => w) := by
    simp only [List.map_replicate]
  rw [hrepl, List.foldr_map]
  exact (List.foldr_const (fun y => w.foldr (fun i y => A i + a * y) y)
    x (List.replicate n ())).trans (by rw [List.length_replicate])

private theorem affine_iterate_limit (b a e x : ℝ) (ha : |a| < 1)
    (he : b + a * e = e) :
    Filter.Tendsto (fun n => (fun y : ℝ => b + a * y)^[n] x)
      Filter.atTop (nhds e) := by
  let K : NNReal := ‖a‖₊
  have hK : ContractingWith K (fun y : ℝ => b + a * y) := by
    constructor
    · change ‖a‖ < 1
      simpa only [Real.norm_eq_abs] using ha
    · simpa only [K, Function.comp_def, one_mul, smul_eq_mul] using
        (isometry_add_left b).lipschitz.comp
          (lipschitzWith_smul a : LipschitzWith ‖a‖₊ (fun y : ℝ => a • y))
  have hfix : e = hK.fixedPoint (fun y : ℝ => b + a * y) :=
    hK.fixedPoint_unique he
  rw [hfix]
  exact hK.tendsto_iterate_fixedPoint x

private theorem hull_equations (A : Fin 2 → ℝ) (a : ℝ) (ha : |a| < 1) :
    let m := hullLower A a
    let M := hullUpper A a
    m ≤ M ∧
      (if 0 ≤ a then min (A 0) (A 1) + a * m = m ∧
        max (A 0) (A 1) + a * M = M
      else min (A 0) (A 1) + a * M = m ∧
        max (A 0) (A 1) + a * m = M) := by
  have hab := abs_lt.mp ha
  have hden : 0 < 1 - a := by linarith
  have hden2 : 0 < 1 - a ^ 2 := by nlinarith
  have horder : min (A 0) (A 1) ≤ max (A 0) (A 1) := min_le_max
  dsimp only
  unfold hullLower hullUpper
  split_ifs with hs
  · constructor
    · exact div_le_div_of_nonneg_right horder hden.le
    · constructor <;> field_simp [ne_of_gt hden, ne_of_gt hden2] <;> ring
  · constructor
    · apply (div_le_div_iff_of_pos_right hden2).mpr
      nlinarith
    · constructor <;> field_simp [ne_of_gt hden, ne_of_gt hden2] <;> ring

private theorem hull_invariant (A : Fin 2 → ℝ) (a : ℝ) (ha : |a| < 1)
    (i : Fin 2) :
    Set.MapsTo (fun x => A i + a * x)
      (Set.Icc (hullLower A a) (hullUpper A a))
      (Set.Icc (hullLower A a) (hullUpper A a)) := by
  have h := hull_equations A a ha
  dsimp only at h
  have hAi : min (A 0) (A 1) ≤ A i ∧ A i ≤ max (A 0) (A 1) := by
    fin_cases i
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
    · exact ⟨min_le_right _ _, le_max_right _ _⟩
  intro x hx
  by_cases hs : 0 ≤ a
  · rw [if_pos hs] at h
    constructor <;> nlinarith [h.2.1, h.2.2, hx.1, hx.2, hAi.1, hAi.2]
  · rw [if_neg hs] at h
    have hs' : a ≤ 0 := le_of_not_ge hs
    constructor <;> nlinarith [h.2.1, h.2.2, hx.1, hx.2, hAi.1, hAi.2]

private theorem returnEval_mem_hull (A : Fin 2 → ℝ) (a : ℝ) (ha : |a| < 1)
    (z : List (Fin 2)) (x : ℝ)
    (hx : x ∈ Set.Icc (hullLower A a) (hullUpper A a)) :
    returnEval A a z x ∈ Set.Icc (hullLower A a) (hullUpper A a) := by
  induction z with
  | nil => exact hx
  | cons i z ih => exact hull_invariant A a ha i ih

private theorem extremal_words (A : Fin 2 → ℝ) (a : ℝ) (ha : |a| < 1) :
    ∃ wlo whi : List (Fin 2), ∀ x : ℝ,
      Filter.Tendsto (fun n => returnEval A a (wordPower n wlo) x)
        Filter.atTop (nhds (hullLower A a)) ∧
      Filter.Tendsto (fun n => returnEval A a (wordPower n whi) x)
        Filter.atTop (nhds (hullUpper A a)) := by
  let ilo : Fin 2 := if A 0 ≤ A 1 then 0 else 1
  let ihi : Fin 2 := if A 0 ≤ A 1 then 1 else 0
  have hlo : A ilo = min (A 0) (A 1) := by
    dsimp [ilo]; split_ifs with h
    · exact (min_eq_left h).symm
    · exact (min_eq_right (le_of_not_ge h)).symm
  have hhi : A ihi = max (A 0) (A 1) := by
    dsimp [ihi]; split_ifs with h
    · exact (max_eq_right h).symm
    · exact (max_eq_left (le_of_not_ge h)).symm
  have he := (hull_equations A a ha).2
  by_cases hs : 0 ≤ a
  · rw [if_pos hs] at he
    refine ⟨[ilo], [ihi], fun x => ?_⟩
    simp only [returnEval_repeat]
    change Filter.Tendsto (fun n => (fun y => A ilo + a * y)^[n] x) _ _ ∧
      Filter.Tendsto (fun n => (fun y => A ihi + a * y)^[n] x) _ _
    exact ⟨affine_iterate_limit _ _ _ _ ha (hlo ▸ he.1),
      affine_iterate_limit _ _ _ _ ha (hhi ▸ he.2)⟩
  · rw [if_neg hs] at he
    have haa : |a ^ 2| < 1 := by rw [abs_pow]; nlinarith [abs_nonneg a]
    refine ⟨[ilo, ihi], [ihi, ilo], fun x => ?_⟩
    have hel : A ilo + a * A ihi + a ^ 2 * hullLower A a = hullLower A a := by
      rw [hlo, hhi]
      calc
        _ = min (A 0) (A 1) + a * (max (A 0) (A 1) + a * hullLower A a) := by ring
        _ = hullLower A a := by rw [he.2]; exact he.1
    have heu : A ihi + a * A ilo + a ^ 2 * hullUpper A a = hullUpper A a := by
      rw [hlo, hhi]
      calc
        _ = max (A 0) (A 1) + a * (min (A 0) (A 1) + a * hullUpper A a) := by ring
        _ = hullUpper A a := by rw [he.1]; exact he.2
    have hlmap : returnEval A a [ilo, ihi] =
        (fun y => A ilo + a * A ihi + a ^ 2 * y) := by
      funext y; simp only [returnEval, List.foldr_cons, List.foldr_nil]; ring
    have humap : returnEval A a [ihi, ilo] =
        (fun y => A ihi + a * A ilo + a ^ 2 * y) := by
      funext y; simp only [returnEval, List.foldr_cons, List.foldr_nil]; ring
    simp only [returnEval_repeat, hlmap, humap]
    exact ⟨affine_iterate_limit _ _ _ _ haa hel, affine_iterate_limit _ _ _ _ haa heu⟩

private theorem hull_minimal (A : Fin 2 → ℝ) (a : ℝ) (ha : |a| < 1)
    (l u : ℝ) (hlu : l ≤ u)
    (hJ : ∀ i : Fin 2, Set.MapsTo (fun x => A i + a * x) (Set.Icc l u) (Set.Icc l u)) :
    Set.Icc (hullLower A a) (hullUpper A a) ⊆ Set.Icc l u := by
  obtain ⟨wl, wu, hw⟩ := extremal_words A a ha
  have hmem (z : List (Fin 2)) : returnEval A a z l ∈ Set.Icc l u := by
    induction z with
    | nil => exact ⟨le_rfl, hlu⟩
    | cons i z ih => exact hJ i ih
  have hl := isClosed_Icc.mem_of_tendsto (hw l).1 (Filter.Eventually.of_forall (fun n => hmem _))
  have hu := isClosed_Icc.mem_of_tendsto (hw l).2 (Filter.Eventually.of_forall (fun n => hmem _))
  intro x hx
  exact ⟨hl.1.trans hx.1, hx.2.trans hu.2⟩


open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization (closed_observation_graph_realization)

/-- A finite path in the actual incoming-guard graph. -/
inductive SourcePath : Bool → List Label → Bool → Prop
  | nil (s) : SourcePath s [] s
  | cons {s s' s'' l w} : lawful s l s' → SourcePath s' w s'' →
      SourcePath s (l :: w) s''

/-- Synchronous stems and two return triples, including empty stems. -/
structure FixedTailData where
  guard : Fin 2 → Bool
  stem : Fin 2 → List Label
  stemColor : List (Fin 6)
  blocks : Fin 2 → Fin 2 → List Label
  blockColor : Fin 2 → List (Fin 6)
  a₀ : ℕ
  L : ℕ
  positive_length : 1 ≤ L
  stem_length : ∀ j, (stem j).length = a₀
  stem_color_length : stemColor.length = a₀
  block_length : ∀ j i, (blocks j i).length = L
  block_color_length : ∀ i, (blockColor i).length = L
  stem_path : ∀ j, SourcePath false (stem j) (guard j)
  block_path : ∀ j i, SourcePath (guard j) (blocks j i) (guard j)
  first_distinct : blocks 0 0 ≠ blocks 0 1

private noncomputable def wordScalar (w : List Label) (x : ℝ) : ℝ :=
  w.foldr branch x

/-- Maximum departure-coordinate cost over all nonempty source suffixes.
The terminal coordinate is omitted, and the empty source contributes zero. -/
private noncomputable def wordCost : List Label → List (Fin 6) → ℝ → ℝ
  | [], _, _ => 0
  | l :: w, i :: r, x => max
      (intervalDistance (wordScalar (l :: w) x) (cellLower i) (cellUpper i))
      (wordCost w r x)
  | _ :: _, [], _ => 0

private def wordObserved (c : ℝ) : List Label → List (Fin 6) → ℝ → Prop
  | [], [], _ => True
  | l :: w, i :: r, x => wordScalar (l :: w) x ∈ observation c i ∧ wordObserved c w r x
  | _, _, _ => False

private def addressPrefix : List Label → LegalDigits → LegalDigits → Prop
  | [], x, y => x = y
  | l :: w, x, y => window x 0 = l ∧ addressPrefix w (originalT x) y

private noncomputable def translation (d : FixedTailData) (j i : Fin 2) : ℝ :=
  wordScalar (d.blocks j i) 0

private noncomputable def slope (d : FixedTailData) : ℝ := (-g) ^ d.L

private noncomputable def lower (d : FixedTailData) (j : Fin 2) : ℝ :=
  hullLower (translation d j) (slope d)

private noncomputable def upper (d : FixedTailData) (j : Fin 2) : ℝ :=
  hullUpper (translation d j) (slope d)

private noncomputable def entryCost (d : FixedTailData) (j : Fin 2)
    (i : Option (Fin 2)) (x : ℝ) : ℝ :=
  match i with
  | none => wordCost (d.stem j) d.stemColor x
  | some i => wordCost (d.blocks j i) (d.blockColor i) x

/-- The indexed suffix certificate, grouped into two stems and four return blocks.
Both endpoints are tested in every group, including repeated suffix values. -/
private noncomputable def familyBudget (d : FixedTailData) : ℝ :=
  Finset.univ.sup' ⟨(0, none), Finset.mem_univ _⟩
    (fun e : Fin 2 × Option (Fin 2) =>
      max (entryCost d e.1 e.2 (lower d e.1)) (entryCost d e.1 e.2 (upper d e.1)))

private def addressObserved (c : ℝ) : List (Fin 6) → LegalDigits → Prop
  | [], _ => True
  | i :: r, x => kappa x ∈ observation c i ∧ addressObserved c r (originalT x)

/-- The tails are fixed before the universal choice of the finite return word.
Each source retains its own unobserved terminal address. -/
private def allHistories (d : FixedTailData) (c : ℝ) (tails : Fin 2 → LegalDigits) : Prop :=
  (∀ j, stateAddress (d.guard j) (tails j)) ∧
  ∀ (z : List (Fin 2)) (j : Fin 2), ∃ source : LegalDigits,
    stateAddress false source ∧
    addressPrefix (d.stem j ++ z.flatMap (d.blocks j)) source (tails j) ∧
    addressObserved c (d.stemColor ++ z.flatMap d.blockColor) source

private theorem wordScalar_append (u v : List Label) (x : ℝ) :
    wordScalar (u ++ v) x = wordScalar u (wordScalar v x) := by
  exact List.foldr_append

private theorem wordScalar_affine (w : List Label) (x : ℝ) :
    wordScalar w x = wordScalar w 0 + (-g) ^ w.length * x := by
  induction w with
  | nil => simp [wordScalar]
  | cons l w ih =>
    simp only [List.length_cons, pow_succ]
    change offset l - g * wordScalar w x =
      offset l - g * wordScalar w 0 + (-g) ^ w.length * (-g) * x
    rw [ih]; ring

private theorem wordScalar_continuous (w : List Label) : Continuous (wordScalar w) := by
  have he : wordScalar w = (fun x => wordScalar w 0 + (-g) ^ w.length * x) :=
    funext (wordScalar_affine w)
  rw [he]
  fun_prop

private theorem prefix_scalar (w : List Label) (x y : LegalDigits)
    (h : addressPrefix w x y) : kappa x = wordScalar w (kappa y) := by
  induction w generalizing x with
  | nil => simpa [addressPrefix, wordScalar] using congrArg kappa h
  | cons l w ih =>
    rcases h with ⟨hl, hw⟩
    rw [(closed_observation_graph_realization.2.2.1 x).1, hl, ih _ hw]
    rfl

private theorem source_path_realization {s s' : Bool} {w : List Label}
    (h : SourcePath s w s') (y : LegalDigits) (hy : stateAddress s' y) :
    ∃ x : LegalDigits, stateAddress s x ∧ addressPrefix w x y := by
  induction h with
  | nil s => exact ⟨y, hy, rfl⟩
  | @cons s s' s'' l w hl hw ih =>
    obtain ⟨z, hz, hzy⟩ := ih hy
    obtain ⟨x, hx, _⟩ := closed_observation_graph_realization.2.2.2.1 s l s' z hl hz
    exact ⟨x, hx.1, hx.2.1, hx.2.2 ▸ hzy⟩

private theorem source_path_maps {s s' : Bool} {w : List Label}
    (h : SourcePath s w s') : Set.MapsTo (wordScalar w) (stateInterval s') (stateInterval s) := by
  intro y hy
  have hr := closed_observation_graph_realization.2.1
  obtain ⟨tail, htail, hval⟩ := (hr s' ▸ hy : y ∈ kappa '' {x | stateAddress s' x})
  obtain ⟨x, hx, hp⟩ := source_path_realization h tail htail
  rw [← hval, ← prefix_scalar w x tail hp]
  exact hr s ▸ ⟨x, hx, rfl⟩

private theorem slope_contracts (d : FixedTailData) : 0 < |slope d| ∧ |slope d| < 1 := by
  have ht : 0 < t := inv_pos.mpr Real.goldenRatio_pos
  have ht1 : t < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hg : 0 < g := pow_pos ht 3
  have hg1 : g < 1 := pow_lt_one₀ ht.le ht1 (by decide)
  have hL : d.L ≠ 0 := by have := d.positive_length; omega
  simp only [slope, abs_pow, abs_neg, abs_of_pos hg]
  exact ⟨pow_pos hg _, pow_lt_one₀ hg.le hg1 hL⟩

private theorem block_scalar (d : FixedTailData) (j i : Fin 2) (x : ℝ) :
    wordScalar (d.blocks j i) x = translation d j i + slope d * x := by
  rw [wordScalar_affine, d.block_length]
  rfl

private theorem hull_in_state (d : FixedTailData) (j : Fin 2) :
    Set.Icc (lower d j) (upper d j) ⊆ stateInterval (d.guard j) := by
  apply hull_minimal (translation d j) (slope d) (slope_contracts d).2
  · have ht : 0 < t := inv_pos.mpr Real.goldenRatio_pos
    split_ifs <;> linarith
  · intro i x hx
    have hm := source_path_maps (d.block_path j i) hx
    rwa [block_scalar] at hm


private theorem path_append {s s' s'' : Bool} {u v : List Label}
    (hu : SourcePath s u s') (hv : SourcePath s' v s'') : SourcePath s (u ++ v) s'' := by
  induction hu with
  | nil => exact hv
  | cons hl hw ih => exact .cons hl (ih hv)

private theorem return_path (d : FixedTailData) (j : Fin 2) (z : List (Fin 2)) :
    SourcePath (d.guard j) (z.flatMap (d.blocks j)) (d.guard j) := by
  induction z with
  | nil => exact .nil _
  | cons i z ih => exact path_append (d.block_path j i) ih

private theorem return_scalar (d : FixedTailData) (j : Fin 2) (z : List (Fin 2)) (x : ℝ) :
    wordScalar (z.flatMap (d.blocks j)) x = returnEval (translation d j) (slope d) z x := by
  induction z with
  | nil => rfl
  | cons i z ih =>
    simp only [List.flatMap_cons, wordScalar_append, block_scalar, ih]
    rfl

private theorem state_subset (s : Bool) : stateInterval s ⊆ stateInterval false := by
  cases s
  · exact Set.Subset.rfl
  · exact Set.Icc_subset_Icc le_rfl (le_add_of_nonneg_left zero_le_one)

private theorem distance_observation (c x : ℝ) (i : Fin 6)
    (hx : x ∈ stateInterval false) (hc : 0 ≤ c) :
    intervalDistance x (cellLower i) (cellUpper i) ≤ c ↔ x ∈ observation c i := by
  unfold intervalDistance observation
  simp only [max_le_iff, Set.mem_Icc, le_min_iff]
  constructor
  · rintro ⟨hl, _, hu⟩
    exact ⟨⟨hx.1, by linarith⟩, hx.2, by linarith⟩
  · rintro ⟨⟨_, hl⟩, _, hu⟩
    exact ⟨by linarith, hc, by linarith⟩

private theorem cost_nonneg (w : List Label) (r : List (Fin 6)) (x : ℝ) :
    0 ≤ wordCost w r x := by
  cases w with
  | nil => exact le_rfl
  | cons l w =>
    cases r with
    | nil => exact le_rfl
    | cons i r => exact (intervalDistance_nonneg _ _ _).trans (le_max_left _ _)

private theorem cost_observed {s s' : Bool} {w : List Label} (hw : SourcePath s w s')
    (r : List (Fin 6)) (hr : w.length = r.length) (x c : ℝ)
    (hx : x ∈ stateInterval s') (hc : 0 ≤ c) :
    wordCost w r x ≤ c ↔ wordObserved c w r x := by
  induction hw generalizing r with
  | nil s =>
    have hr0 : r = [] := List.length_eq_zero_iff.mp hr.symm
    subst r
    simp only [wordCost, wordObserved, iff_true]
    exact hc
  | @cons s s' s'' l w hl hw ih =>
    cases r with
    | nil => simp at hr
    | cons i r =>
      have hr' : w.length = r.length := by simpa using hr
      have hs := state_subset s (source_path_maps (.cons hl hw) hx)
      change max _ _ ≤ c ↔ _ ∧ _
      rw [max_le_iff, distance_observation c _ i hs hc, ih r hr' hx]

private theorem cost_append (u v : List Label) (r t' : List (Fin 6))
    (hr : u.length = r.length) (x : ℝ) :
    wordCost (u ++ v) (r ++ t') x =
      max (wordCost u r (wordScalar v x)) (wordCost v t' x) := by
  induction u generalizing r with
  | nil =>
    have hr0 : r = [] := List.length_eq_zero_iff.mp hr.symm
    subst r
    simp only [List.nil_append, wordCost]
    exact (max_eq_right (cost_nonneg v t' x)).symm
  | cons l u ih =>
    cases r with
    | nil => simp at hr
    | cons i r =>
      simp only [List.cons_append, wordCost]
      rw [show wordScalar (l :: (u ++ v)) x =
        wordScalar (l :: u) (wordScalar v x) from wordScalar_append (l :: u) v x,
        ih r (by simpa using hr), max_assoc]

private theorem cost_endpoint_bound (w : List Label) (r : List (Fin 6))
    (lo hi x : ℝ) (hx : x ∈ Set.Icc lo hi) :
    wordCost w r x ≤ max (wordCost w r lo) (wordCost w r hi) := by
  induction w generalizing r with
  | nil => simp [wordCost]
  | cons l w ih =>
    cases r with
    | nil => simp [wordCost]
    | cons i r =>
      change max _ _ ≤ max (max _ _) (max _ _)
      apply max_le
      · have hb := affine_endpoint_bound ((-g) ^ (l :: w).length)
          (wordScalar (l :: w) 0) lo hi (cellLower i) (cellUpper i) x hx
        have he (y : ℝ) : (-g) ^ (l :: w).length * y +
            wordScalar (l :: w) 0 = wordScalar (l :: w) y := by
          exact (add_comm _ _).trans (wordScalar_affine (l :: w) y).symm
        rw [he x, he lo, he hi] at hb
        apply hb.trans
        exact max_le ((le_max_left _ _).trans (le_max_left _ _))
          ((le_max_left _ _).trans (le_max_right _ _))
      · apply (ih r).trans
        exact max_le ((le_max_right _ _).trans (le_max_left _ _))
          ((le_max_right _ _).trans (le_max_right _ _))

private theorem cost_continuous (w : List Label) (r : List (Fin 6)) :
    Continuous (wordCost w r) := by
  induction w generalizing r with
  | nil => exact continuous_const
  | cons l w ih =>
    cases r with
    | nil => exact continuous_const
    | cons i r =>
      change Continuous (fun x => max
        (intervalDistance (wordScalar (l :: w) x) (cellLower i) (cellUpper i))
        (wordCost w r x))
      apply Continuous.max _ (ih r)
      unfold intervalDistance
      exact (continuous_const.sub (wordScalar_continuous _)).max
        (continuous_const.max ((wordScalar_continuous _).sub continuous_const))


private theorem return_lengths (d : FixedTailData) (j : Fin 2) (z : List (Fin 2)) :
    (z.flatMap (d.blocks j)).length = (z.flatMap d.blockColor).length := by
  induction z with
  | nil => rfl
  | cons i z ih => simp only [List.flatMap_cons, List.length_append,
      d.block_length, d.block_color_length, ih]

private theorem entry_bounded (d : FixedTailData) (j : Fin 2) (i : Option (Fin 2)) :
    entryCost d j i (lower d j) ≤ familyBudget d ∧
      entryCost d j i (upper d j) ≤ familyBudget d := by
  have h := Finset.le_sup' (fun e : Fin 2 × Option (Fin 2) =>
      max (entryCost d e.1 e.2 (lower d e.1)) (entryCost d e.1 e.2 (upper d e.1)))
    (Finset.mem_univ (j, i))
  exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩

private theorem budget_nonneg (d : FixedTailData) : 0 ≤ familyBudget d :=
  (cost_nonneg (d.stem 0) d.stemColor (lower d 0)).trans (entry_bounded d 0 none).1

private theorem entry_inside_bound (d : FixedTailData) (j : Fin 2)
    (i : Option (Fin 2)) (x : ℝ) (hx : x ∈ Set.Icc (lower d j) (upper d j)) :
    entryCost d j i x ≤ familyBudget d := by
  have he := entry_bounded d j i
  cases i with
  | none => exact (cost_endpoint_bound _ _ _ _ _ hx).trans (max_le he.1 he.2)
  | some i => exact (cost_endpoint_bound _ _ _ _ _ hx).trans (max_le he.1 he.2)

private theorem return_cost_bound (d : FixedTailData) (j : Fin 2) (z : List (Fin 2))
    (x : ℝ) (hx : x ∈ Set.Icc (lower d j) (upper d j)) :
    wordCost (z.flatMap (d.blocks j)) (z.flatMap d.blockColor) x ≤ familyBudget d := by
  induction z with
  | nil => exact budget_nonneg d
  | cons i z ih =>
    simp only [List.flatMap_cons]
    rw [cost_append _ _ _ _ (by rw [d.block_length, d.block_color_length])]
    apply max_le _ ih
    rw [return_scalar]
    exact entry_inside_bound d j (some i) _
      (returnEval_mem_hull _ _ (slope_contracts d).2 z x hx)

private theorem history_cost_bound (d : FixedTailData) (j : Fin 2) (z : List (Fin 2))
    (x : ℝ) (hx : x ∈ Set.Icc (lower d j) (upper d j)) :
    wordCost (d.stem j ++ z.flatMap (d.blocks j))
      (d.stemColor ++ z.flatMap d.blockColor) x ≤ familyBudget d := by
  rw [cost_append _ _ _ _ (by rw [d.stem_length, d.stem_color_length]), return_scalar]
  exact max_le (entry_inside_bound d j none _
    (returnEval_mem_hull _ _ (slope_contracts d).2 z x hx)) (return_cost_bound d j z x hx)

private theorem wordObserved_actual (c : ℝ) (w : List Label)
    (r : List (Fin 6)) (x y : LegalDigits) (hr : w.length = r.length)
    (hp : addressPrefix w x y) :
    wordObserved c w r (kappa y) ↔ addressObserved c r x := by
  induction w generalizing r x with
  | nil =>
    have hr0 : r = [] := List.length_eq_zero_iff.mp hr.symm
    subst r
    exact Iff.rfl
  | cons l w ih =>
    cases r with
    | nil => simp at hr
    | cons i r =>
      change (_ ∧ _) ↔ (_ ∧ _)
      rw [← prefix_scalar (l :: w) x y hp,
        ih r (originalT x) (by simpa using hr) hp.2]

private theorem histories_cost (d : FixedTailData) (c : ℝ) (hc : 0 ≤ c)
    (tails : Fin 2 → LegalDigits) (ht : ∀ j, stateAddress (d.guard j) (tails j)) :
    allHistories d c tails ↔ ∀ (z : List (Fin 2)) (j : Fin 2),
      wordCost (d.stem j ++ z.flatMap (d.blocks j))
        (d.stemColor ++ z.flatMap d.blockColor) (kappa (tails j)) ≤ c := by
  have hlen (z : List (Fin 2)) (j : Fin 2) :
      (d.stem j ++ z.flatMap (d.blocks j)).length =
        (d.stemColor ++ z.flatMap d.blockColor).length := by
    rw [List.length_append, List.length_append, d.stem_length,
      d.stem_color_length, return_lengths]
  have he (z : List (Fin 2)) (j : Fin 2) := cost_observed
    (path_append (d.stem_path j) (return_path d j z))
    (d.stemColor ++ z.flatMap d.blockColor) (hlen z j) (kappa (tails j)) c
    (closed_observation_graph_realization.2.1 (d.guard j) ▸ ⟨tails j, ht j, rfl⟩) hc
  constructor
  · intro hall z j
    obtain ⟨source, _, hp, ho⟩ := hall.2 z j
    apply (he z j).mpr
    exact (wordObserved_actual c _ _ source (tails j) (hlen z j) hp).mpr ho
  · intro hall
    refine ⟨ht, fun z j => ?_⟩
    obtain ⟨source, hs, hp⟩ := source_path_realization
      (path_append (d.stem_path j) (return_path d j z)) (tails j) (ht j)
    exact ⟨source, hs, hp,
      (wordObserved_actual c _ _ source (tails j) (hlen z j) hp).mp ((he z j).mp (hall z j))⟩

private theorem necessary_endpoint (d : FixedTailData) (c : ℝ)
    (x : Fin 2 → ℝ)
    (hall : ∀ (z : List (Fin 2)) (j : Fin 2),
      wordCost (d.stem j ++ z.flatMap (d.blocks j))
        (d.stemColor ++ z.flatMap d.blockColor) (x j) ≤ c) :
    familyBudget d ≤ c := by
  have hentry (j : Fin 2) (i : Option (Fin 2)) (z : List (Fin 2)) :
      entryCost d j i (returnEval (translation d j) (slope d) z (x j)) ≤ c := by
    cases i with
    | none =>
      have h := hall z j
      rw [cost_append _ _ _ _ (by rw [d.stem_length, d.stem_color_length]), return_scalar] at h
      exact (le_max_left _ _).trans h
    | some i =>
      have h := hall (i :: z) j
      rw [cost_append _ _ _ _ (by rw [d.stem_length, d.stem_color_length])] at h
      have h' := (le_max_right _ _).trans h
      simp only [List.flatMap_cons] at h'
      rw [cost_append _ _ _ _ (by rw [d.block_length, d.block_color_length]), return_scalar] at h'
      exact (le_max_left _ _).trans h'
  have hends (j : Fin 2) (i : Option (Fin 2)) :
      entryCost d j i (lower d j) ≤ c ∧ entryCost d j i (upper d j) ≤ c := by
    obtain ⟨wl, wu, hw⟩ := extremal_words (translation d j) (slope d) (slope_contracts d).2
    have hcont : Continuous (entryCost d j i) := by
      cases i with
      | none => exact cost_continuous _ _
      | some i => exact cost_continuous _ _
    exact ⟨isClosed_Iic.mem_of_tendsto (hcont.tendsto _ |>.comp (hw (x j)).1)
        (Filter.Eventually.of_forall (fun n => hentry j i (wordPower n wl))),
      isClosed_Iic.mem_of_tendsto (hcont.tendsto _ |>.comp (hw (x j)).2)
        (Filter.Eventually.of_forall (fun n => hentry j i (wordPower n wu)))⟩
  apply Finset.sup'_le
  intro e _
  exact max_le (hends e.1 e.2).1 (hends e.1 e.2).2

private theorem fixed_pair_exists (d : FixedTailData) :
    ∃ tails : Fin 2 → LegalDigits, ∀ j,
      stateAddress (d.guard j) (tails j) ∧ kappa (tails j) ∈ Set.Icc (lower d j) (upper d j) := by
  have h (j : Fin 2) : ∃ tail : LegalDigits,
      stateAddress (d.guard j) tail ∧ kappa tail = lower d j := by
    have hm : lower d j ∈ stateInterval (d.guard j) := hull_in_state d j
      ⟨le_rfl, (hull_equations _ _ (slope_contracts d).2).1⟩
    obtain ⟨tail, ht, hv⟩ :=
      (closed_observation_graph_realization.2.1 (d.guard j) ▸ hm :
        lower d j ∈ kappa '' {x | stateAddress (d.guard j) x})
    exact ⟨tail, ht, hv⟩
  choose tails ht hv using h
  refine ⟨tails, fun j => ⟨ht j, ?_⟩⟩
  rw [hv j]
  exact ⟨le_rfl, (hull_equations _ _ (slope_contracts d).2).1⟩

private theorem budget_equivalence (d : FixedTailData) :
    0 ≤ familyBudget d ∧
    (∀ c : ℝ, 0 ≤ c → ((∃ tails, allHistories d c tails) ↔ familyBudget d ≤ c)) ∧
    (∀ tails : Fin 2 → LegalDigits,
      (∀ j, stateAddress (d.guard j) (tails j) ∧
        kappa (tails j) ∈ Set.Icc (lower d j) (upper d j)) →
      allHistories d (familyBudget d) tails) := by
  have hsuff (tails : Fin 2 → LegalDigits)
      (ht : ∀ j, stateAddress (d.guard j) (tails j) ∧
        kappa (tails j) ∈ Set.Icc (lower d j) (upper d j)) :
      allHistories d (familyBudget d) tails := by
    apply (histories_cost d _ (budget_nonneg d) tails (fun j => (ht j).1)).mpr
    intro z j
    exact history_cost_bound d j z _ (ht j).2
  refine ⟨budget_nonneg d, ?_, hsuff⟩
  intro c hc
  constructor
  · rintro ⟨tails, ht⟩
    exact necessary_endpoint d c (fun j => kappa (tails j))
      ((histories_cost d c hc tails ht.1).mp ht)
  · intro hbudget
    obtain ⟨tails, ht⟩ := fixed_pair_exists d
    refine ⟨tails, (histories_cost d c hc tails (fun j => (ht j).1)).mpr ?_⟩
    exact fun z j => (history_cost_bound d j z _ (ht j).2).trans hbudget


private theorem coefficient_add (x y : ℝ) (hx : inCoefficientField x)
    (hy : inCoefficientField y) : inCoefficientField (x + y) := by
  obtain ⟨a, b, rfl⟩ := hx
  obtain ⟨c, d, rfl⟩ := hy
  refine ⟨a + c, b + d, ?_⟩
  push_cast
  ring

private theorem coefficient_neg (x : ℝ) (hx : inCoefficientField x) :
    inCoefficientField (-x) := by
  obtain ⟨a, b, rfl⟩ := hx
  refine ⟨-a, -b, ?_⟩
  push_cast
  ring

private theorem coefficient_mul (x y : ℝ) (hx : inCoefficientField x)
    (hy : inCoefficientField y) : inCoefficientField (x * y) := by
  have ht2 : t ^ 2 + t = 1 := by
    dsimp [t, D5.S1.Digit.Infinite.SignedSeriesRange.alpha]
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  obtain ⟨a, b, rfl⟩ := hx
  obtain ⟨c, d, rfl⟩ := hy
  refine ⟨a * c + b * d, a * d + b * c - b * d, ?_⟩
  push_cast
  have h := congrArg (fun z : ℝ => (b : ℝ) * d * z) ht2
  nlinarith only [h]

private theorem coefficient_inv (x : ℝ) (hx : inCoefficientField x) :
    inCoefficientField x⁻¹ := by
  by_cases hx0 : x = 0
  · subst x; exact ⟨0, 0, by norm_num⟩
  obtain ⟨a, b, hxab⟩ := hx
  have ht2 : t ^ 2 + t = 1 := by
    dsimp [t, D5.S1.Digit.Infinite.SignedSeriesRange.alpha]
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  let D : ℚ := a ^ 2 - a * b - b ^ 2
  have hprod : x * ((a : ℝ) - b - b * t) = (D : ℝ) := by
    rw [hxab]
    dsimp [D]
    push_cast
    have h := congrArg (fun z : ℝ => (b : ℝ) ^ 2 * z) ht2
    nlinarith only [h]
  have hD : D ≠ 0 := by
    intro hD
    have hc : (a : ℝ) - b - b * t = 0 := by
      have h := hprod
      rw [hD, Rat.cast_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hx0
    by_cases hb : b = 0
    · rw [hb] at hc hxab
      simp only [Rat.cast_zero, sub_zero, zero_mul, add_zero] at hc hxab
      exact hx0 (hxab.trans hc)
    · have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
      have htRat : t = (((a - b) / b : ℚ) : ℝ) := by
        push_cast
        apply (eq_div_iff hbR).mpr
        linarith
      exact (Real.goldenRatio_irrational.inv).ne_rat ((a - b) / b) htRat
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  refine ⟨(a - b) / D, -b / D, ?_⟩
  push_cast
  have he : x⁻¹ = ((a : ℝ) - b - b * t) / (D : ℝ) := by
    apply (eq_div_iff hDR).mpr
    rw [← hprod]
    calc
      x⁻¹ * (x * ((a : ℝ) - b - b * t)) =
          (x⁻¹ * x) * ((a : ℝ) - b - b * t) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hx0, one_mul]
  rw [he]
  ring

private theorem coefficient_max (x y : ℝ) (hx : inCoefficientField x)
    (hy : inCoefficientField y) : inCoefficientField (max x y) := by
  rcases le_total x y with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

private theorem coefficient_min (x y : ℝ) (hx : inCoefficientField x)
    (hy : inCoefficientField y) : inCoefficientField (min x y) := by
  rcases le_total x y with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

private theorem coefficient_constants :
    inCoefficientField (0 : ℝ) ∧ inCoefficientField (1 : ℝ) ∧ inCoefficientField t := by
  exact ⟨⟨0, 0, by norm_num⟩, ⟨1, 0, by norm_num⟩, ⟨0, 1, by norm_num⟩⟩

private theorem coefficient_pow (x : ℝ) (hx : inCoefficientField x) (n : ℕ) :
    inCoefficientField (x ^ n) := by
  induction n with
  | zero => simpa using coefficient_constants.2.1
  | succ n ih => rw [pow_succ]; exact coefficient_mul _ _ ih hx

private theorem offset_field (l : Label) : inCoefficientField (offset l) := by
  unfold offset
  have hb (i : Fin 3) : inCoefficientField (if l.val i then (1 : ℝ) else 0) := by
    split_ifs <;> exact (by first | exact coefficient_constants.2.1 | exact coefficient_constants.1)
  exact coefficient_add _ _ (coefficient_add _ _ (hb 0)
    (coefficient_neg _ (coefficient_mul _ _ coefficient_constants.2.2 (hb 1))))
    (coefficient_mul _ _ (coefficient_pow _ coefficient_constants.2.2 2) (hb 2))

private theorem wordScalar_field (w : List Label) (x : ℝ) (hx : inCoefficientField x) :
    inCoefficientField (wordScalar w x) := by
  induction w with
  | nil => exact hx
  | cons l w ih =>
    exact coefficient_add _ _ (offset_field l) (coefficient_neg _
      (coefficient_mul _ _ (coefficient_pow _ coefficient_constants.2.2 3) ih))

private theorem hull_field (A : Fin 2 → ℝ) (a : ℝ)
    (hA : ∀ i, inCoefficientField (A i)) (ha : inCoefficientField a) :
    inCoefficientField (hullLower A a) ∧ inCoefficientField (hullUpper A a) := by
  have hlo := coefficient_min _ _ (hA 0) (hA 1)
  have hhi := coefficient_max _ _ (hA 0) (hA 1)
  have hdiv (x y : ℝ) (hx : inCoefficientField x) (hy : inCoefficientField y) :
      inCoefficientField (x / y) := by
    rw [div_eq_mul_inv]
    exact coefficient_mul _ _ hx (coefficient_inv _ hy)
  have hd := coefficient_add _ _ coefficient_constants.2.1 (coefficient_neg _ ha)
  have hd2 := coefficient_add _ _ coefficient_constants.2.1
    (coefficient_neg _ (coefficient_pow _ ha 2))
  unfold hullLower hullUpper
  split_ifs
  · exact ⟨hdiv _ _ hlo hd, hdiv _ _ hhi hd⟩
  · exact ⟨hdiv _ _ (coefficient_add _ _ hlo (coefficient_mul _ _ ha hhi)) hd2,
      hdiv _ _ (coefficient_add _ _ hhi (coefficient_mul _ _ ha hlo)) hd2⟩

private theorem cell_field (i : Fin 6) :
    inCoefficientField (cellLower i) ∧ inCoefficientField (cellUpper i) := by
  have hlin (a b : ℚ) : inCoefficientField ((a : ℝ) + b * t) := ⟨a, b, rfl⟩
  have hcut (i : Fin 5) : inCoefficientField (cuts i) := by
    have hl := coefficient_mul _ _ (show inCoefficientField ((10 : ℝ)⁻¹) from
      coefficient_inv _ ⟨10, 0, by norm_num⟩) (coefficient_pow _ coefficient_constants.2.2 2)
    have hsub (x y : ℝ) (hx : inCoefficientField x) (hy : inCoefficientField y) :
        inCoefficientField (x - y) := by
      rw [sub_eq_add_neg]
      exact coefficient_add _ _ hx (coefficient_neg _ hy)
    have hnat (n : ℕ) : inCoefficientField (n : ℝ) := ⟨n, 0, by norm_num⟩
    fin_cases i <;> dsimp only [cuts]
    · exact hsub _ _ (coefficient_neg _ (coefficient_pow _ coefficient_constants.2.2 2))
        (by simpa [lambda, div_eq_mul_inv, mul_comm] using hl)
    · exact hsub _ _ (coefficient_pow _ coefficient_constants.2.2 3)
        (coefficient_mul _ _ (hnat 3) (by simpa [lambda, div_eq_mul_inv, mul_comm] using hl))
    · exact hsub _ _ coefficient_constants.2.2
        (coefficient_mul _ _ (hnat 5) (by simpa [lambda, div_eq_mul_inv, mul_comm] using hl))
    · exact hsub _ _ (coefficient_mul _ _ (hnat 2) coefficient_constants.2.2)
        (coefficient_mul _ _ (hnat 7) (by simpa [lambda, div_eq_mul_inv, mul_comm] using hl))
    · exact coefficient_add _ _ (coefficient_mul _ _ (hnat 2) coefficient_constants.2.2)
        (by simpa [lambda, div_eq_mul_inv, mul_comm] using hl)
  fin_cases i <;> dsimp only [cellLower, cellUpper]
  · exact ⟨by simpa using hlin (-1) 0, hcut 0⟩
  · exact ⟨hcut 0, hcut 1⟩
  · exact ⟨hcut 1, hcut 2⟩
  · exact ⟨hcut 2, hcut 3⟩
  · exact ⟨hcut 3, hcut 4⟩
  · exact ⟨hcut 4, by simpa using hlin 1 1⟩

private theorem cost_field (w : List Label) (r : List (Fin 6)) (x : ℝ)
    (hx : inCoefficientField x) : inCoefficientField (wordCost w r x) := by
  induction w generalizing r with
  | nil => exact coefficient_constants.1
  | cons l w ih =>
    cases r with
    | nil => exact coefficient_constants.1
    | cons i r =>
      unfold wordCost intervalDistance
      exact coefficient_max _ _ (coefficient_max _ _
        (coefficient_add _ _ (cell_field i).1 (coefficient_neg _ (wordScalar_field _ x hx)))
        (coefficient_max _ _ coefficient_constants.1
          (coefficient_add _ _ (wordScalar_field _ x hx) (coefficient_neg _ (cell_field i).2))))
        (ih r)

private theorem budget_field (d : FixedTailData) : inCoefficientField (familyBudget d) := by
  have hends (j : Fin 2) : inCoefficientField (lower d j) ∧ inCoefficientField (upper d j) :=
    hull_field _ _ (fun i => wordScalar_field _ 0 coefficient_constants.1)
      (coefficient_pow _ (coefficient_neg _ (coefficient_pow _ coefficient_constants.2.2 3)) d.L)
  obtain ⟨e, _, he⟩ := Finset.exists_mem_eq_sup'
    ⟨(0, none), Finset.mem_univ _⟩ (fun e : Fin 2 × Option (Fin 2) =>
      max (entryCost d e.1 e.2 (lower d e.1)) (entryCost d e.1 e.2 (upper d e.1)))
  unfold familyBudget
  rw [he]
  apply coefficient_max
  · cases e.2 <;> exact cost_field _ _ _ (hends e.1).1
  · cases e.2 <;> exact cost_field _ _ _ (hends e.1).2

/-- The least closed budget for every finite choice word is attained by one pair
of legal terminal addresses. Every pair whose coordinates lie in the two explicit
minimal return hulls attains this same budget. -/
theorem fixed_tail_closed_budget (d : FixedTailData) :
    inCoefficientField (familyBudget d) ∧
    0 ≤ familyBudget d ∧
    (∀ c : ℝ, 0 ≤ c → ((∃ tails, allHistories d c tails) ↔ familyBudget d ≤ c)) ∧
    (∀ tails : Fin 2 → LegalDigits,
      (∀ j, stateAddress (d.guard j) (tails j) ∧
        kappa (tails j) ∈ Set.Icc (lower d j) (upper d j)) →
      allHistories d (familyBudget d) tails) :=
  ⟨budget_field d, budget_equivalence d⟩

end D5.S1.Digit.Infinite.FixedTailClosedBudget
