/- GID: D5/S1/Digit/Infinite/FixedTailClosedBudget
   generality: G
   mirror-B: D5/B/S1/Digit/Infinite/FixedTailClosedBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite affine endpoint certificate gives the least closed budget for all terminal values in two fixed interval hulls. -/

import D5.S1.Digit.Infinite.ClosedObservationGraphRealization
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped Topology

namespace D5.S1.Digit.Infinite.FixedTailClosedBudget

private def intervalDistance (x l u : ℝ) : ℝ := max (l - x) (max 0 (x - u))

private def inBox (lo hi : Fin 2 → ℝ) (x : Fin 2 → ℝ) : Prop :=
  ∀ j, x j ∈ Set.Icc (lo j) (hi j)

private def value {m : ℕ} (a b : Fin m → ℝ) (source : Fin m → Fin 2)
    (x : Fin 2 → ℝ) (i : Fin m) : ℝ :=
  a i * x (source i) + b i

private theorem intervalDistance_nonneg (x l u : ℝ) : 0 ≤ intervalDistance x l u := by
  unfold intervalDistance
  exact (le_max_left _ _).trans (le_max_right _ _)

private theorem intervalDistance_bounds (x l u D : ℝ)
    (h : intervalDistance x l u ≤ D) :
    l - D ≤ x ∧ x ≤ u + D := by
  unfold intervalDistance at h
  have h₁ := (max_le_iff.mp h).1
  have h₂ := (max_le_iff.mp h).2
  have h₃ := (max_le_iff.mp h₂).2
  constructor <;> linarith

private theorem affine_endpoint_bound (a b lo hi l u x : ℝ) (hlo : lo ≤ hi)
    (hx : x ∈ Set.Icc lo hi) :
    intervalDistance (a * x + b) l u ≤
      max (intervalDistance (a * lo + b) l u)
        (intervalDistance (a * hi + b) l u) := by
  let D : ℝ := max (intervalDistance (a * lo + b) l u)
    (intervalDistance (a * hi + b) l u)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact (intervalDistance_nonneg _ _ _).trans (le_max_left _ _)
  have hleft : l - D ≤ a * lo + b ∧ a * lo + b ≤ u + D := by
    exact intervalDistance_bounds _ _ _ _ (le_max_left _ _)
  have hright : l - D ≤ a * hi + b ∧ a * hi + b ≤ u + D := by
    exact intervalDistance_bounds _ _ _ _ (le_max_right _ _)
  have hbetween : l - D ≤ a * x + b ∧ a * x + b ≤ u + D := by
    rcases hx with ⟨hxlo, hxhi⟩
    by_cases ha : 0 ≤ a
    · constructor <;> nlinarith
    · have ha' : a ≤ 0 := le_of_not_ge ha
      constructor <;> nlinarith
  change intervalDistance (a * x + b) l u ≤ D
  unfold intervalDistance
  apply max_le
  · linarith [hbetween.1]
  · apply max_le
    · exact hD
    · linarith [hbetween.2]

private theorem affine_endpoint_bound_for_slot
    {m : ℕ} (a b : Fin m → ℝ) (source : Fin m → Fin 2)
    (lo hi : Fin 2 → ℝ) (left right : Fin m → ℝ) (i : Fin m)
    (hlo : ∀ j, lo j ≤ hi j) (x : Fin 2 → ℝ) (hx : inBox lo hi x) :
    intervalDistance (value a b source x i) (left i) (right i) ≤
      max
        (intervalDistance (value a b source (fun j => lo j) i) (left i) (right i))
        (intervalDistance (value a b source (fun j => hi j) i) (left i) (right i)) := by
  apply affine_endpoint_bound (a i) (b i) (lo (source i)) (hi (source i))
    (left i) (right i) (x (source i)) (hlo (source i)) (hx (source i))

private def theta {m : ℕ} (a b : Fin m → ℝ) (source : Fin m → Fin 2)
    (lo hi : Fin 2 → ℝ) (left right : Fin m → ℝ) (hm : 0 < m) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun i =>
    max
      (intervalDistance (value a b source (fun j => lo j) i) (left i) (right i))
      (intervalDistance (value a b source (fun j => hi j) i) (left i) (right i)))

private def closedAt {m : ℕ} (a b : Fin m → ℝ) (source : Fin m → Fin 2)
    (left right : Fin m → ℝ) (c : ℝ) (x : Fin 2 → ℝ) : Prop :=
  ∀ i, intervalDistance (value a b source x i) (left i) (right i) ≤ c

private def endpointAt {m : ℕ} (a b : Fin m → ℝ) (source : Fin m → Fin 2)
    (lo hi : Fin 2 → ℝ) (left right : Fin m → ℝ) (c : ℝ) : Prop :=
  ∀ i,
    intervalDistance (value a b source (fun j => lo j) i) (left i) (right i) ≤ c ∧
    intervalDistance (value a b source (fun j => hi j) i) (left i) (right i) ≤ c


private def returnEval (A : Fin 2 → ℝ) (a : ℝ) (z : List (Fin 2)) (x : ℝ) : ℝ :=
  z.foldr (fun i y => A i + a * y) x

private def repeatWord (w : List (Fin 2)) (n : ℕ) : List (Fin 2) :=
  (List.replicate n w).flatten

private def hullLower (A : Fin 2 → ℝ) (a : ℝ) : ℝ :=
  if 0 ≤ a then min (A 0) (A 1) / (1 - a)
  else (min (A 0) (A 1) + a * max (A 0) (A 1)) / (1 - a ^ 2)

private def hullUpper (A : Fin 2 → ℝ) (a : ℝ) : ℝ :=
  if 0 ≤ a then max (A 0) (A 1) / (1 - a)
  else (max (A 0) (A 1) + a * min (A 0) (A 1)) / (1 - a ^ 2)

private theorem returnEval_append (A : Fin 2 → ℝ) (a : ℝ)
    (u v : List (Fin 2)) (x : ℝ) :
    returnEval A a (u ++ v) x = returnEval A a u (returnEval A a v x) := by
  exact List.foldr_append

private theorem returnEval_repeat (A : Fin 2 → ℝ) (a : ℝ)
    (w : List (Fin 2)) (n : ℕ) (x : ℝ) :
    returnEval A a (repeatWord w n) x = (returnEval A a w)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [repeatWord, List.replicate_succ, List.flatten_cons, returnEval_append]
    rw [show returnEval A a (List.replicate n w).flatten x =
      (returnEval A a w)^[n] x from ih, Function.iterate_succ_apply']

private theorem affine_iterate_limit (b a e x : ℝ) (ha : |a| < 1)
    (he : b + a * e = e) :
    Filter.Tendsto (fun n => (fun y : ℝ => b + a * y)^[n] x)
      Filter.atTop (nhds e) := by
  have hformula (n : ℕ) : (fun y : ℝ => b + a * y)^[n] x =
      e + a ^ n * (x - e) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ]
      nlinarith only [he]
  simp_rw [hformula]
  simpa using Filter.Tendsto.const_add e
    ((tendsto_pow_atTop_nhds_zero_iff.mpr ha).mul_const (x - e))

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
      Filter.Tendsto (fun n => returnEval A a (repeatWord wlo n) x)
        Filter.atTop (nhds (hullLower A a)) ∧
      Filter.Tendsto (fun n => returnEval A a (repeatWord whi n) x)
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
      rw [hlo, hhi]; nlinarith only [he.1, he.2]
    have heu : A ihi + a * A ilo + a ^ 2 * hullUpper A a = hullUpper A a := by
      rw [hlo, hhi]; nlinarith only [he.1, he.2]
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

private noncomputable def familyBudget (d : FixedTailData) : ℝ :=
  Finset.univ.sup' ⟨(0, none), Finset.mem_univ _⟩
    (fun e : Fin 2 × Option (Fin 2) =>
      max (entryCost d e.1 e.2 (lower d e.1)) (entryCost d e.1 e.2 (upper d e.1)))

private def allHistories (d : FixedTailData) (c : ℝ) (tails : Fin 2 → LegalDigits) : Prop :=
  (∀ j, stateAddress (d.guard j) (tails j)) ∧
  ∀ (z : List (Fin 2)) (j : Fin 2),
    wordObserved c (d.stem j ++ z.flatMap (d.blocks j))
      (d.stemColor ++ z.flatMap d.blockColor) (kappa (tails j))

private theorem wordScalar_append (u v : List Label) (x : ℝ) :
    wordScalar (u ++ v) x = wordScalar u (wordScalar v x) := by
  exact List.foldr_append

private theorem wordScalar_affine (w : List Label) (x : ℝ) :
    wordScalar w x = wordScalar w 0 + (-g) ^ w.length * x := by
  induction w with
  | nil => simp [wordScalar]
  | cons l w ih =>
    simp only [wordScalar, List.foldr_cons, List.length_cons, pow_succ] at ih ⊢
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
    change wordScalar (d.blocks j i) x ∈ stateInterval (d.guard j)
    · exact source_path_maps (d.block_path j i) hx
    · rw [block_scalar]

/-- The complete finite endpoint certificate is the exact threshold for one fixed pair of
terminal interval hulls. The endpoint bound is obtained from affine branches, while the
finite supremum supplies the common budget for every slot at once. -/
theorem fixed_tail_closed_budget
    (m : ℕ) (hm : 0 < m) (a b : Fin m → ℝ) (source : Fin m → Fin 2)
    (lo hi : Fin 2 → ℝ) (left right : Fin m → ℝ)
    (hlo : ∀ j, lo j ≤ hi j) (hleft : ∀ i, left i ≤ right i) :
    let θ := theta a b source lo hi left right hm
    (0 ≤ θ) ∧
      (∀ c, 0 ≤ c →
        ((∃ x : Fin 2 → ℝ, inBox lo hi x ∧
            ∀ y : Fin 2 → ℝ, inBox lo hi y → closedAt a b source left right c y) ↔
          θ ≤ c) ∧
        (θ ≤ c → ∀ x : Fin 2 → ℝ, inBox lo hi x →
          ∀ y : Fin 2 → ℝ, inBox lo hi y → closedAt a b source left right c y)) := by
  dsimp only
  let θ := theta a b source lo hi left right hm
  have hθ_nonneg : 0 ≤ θ := by
    have hi0 : (⟨0, hm⟩ : Fin m) ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
    have h0 : 0 ≤ max
        (intervalDistance (value a b source (fun j => lo j) ⟨0, hm⟩) (left ⟨0, hm⟩) (right ⟨0, hm⟩))
        (intervalDistance (value a b source (fun j => hi j) ⟨0, hm⟩) (left ⟨0, hm⟩) (right ⟨0, hm⟩)) :=
      (intervalDistance_nonneg _ _ _).trans (le_max_left _ _)
    have hs : max
        (intervalDistance (value a b source (fun j => lo j) ⟨0, hm⟩) (left ⟨0, hm⟩) (right ⟨0, hm⟩))
        (intervalDistance (value a b source (fun j => hi j) ⟨0, hm⟩) (left ⟨0, hm⟩) (right ⟨0, hm⟩)) ≤ θ := by
      dsimp [θ, theta]
      exact Finset.le_sup' (fun i : Fin m =>
        max (intervalDistance (value a b source (fun j => lo j) i) (left i) (right i))
          (intervalDistance (value a b source (fun j => hi j) i) (left i) (right i))) hi0
    exact h0.trans hs
  have hendpoint_iff (c : ℝ) :
      (θ ≤ c ↔ endpointAt a b source lo hi left right c) := by
    constructor
    · intro hc i
      constructor
      · exact (le_max_left _ _).trans ((Finset.le_sup' _ (Finset.mem_univ i)).trans hc)
      · exact (le_max_right _ _).trans ((Finset.le_sup' _ (Finset.mem_univ i)).trans hc)
    · intro he
      dsimp [θ, theta]
      apply Finset.sup'_le
      intro i hi'
      exact max_le (he i).1 (he i).2
  refine ⟨hθ_nonneg, ?_⟩
  intro c hc
  constructor
  · constructor
    · rintro ⟨x, hx, hy⟩
      have he : endpointAt a b source lo hi left right c := by
        intro i
        constructor
        · exact (hy (fun j => lo j) (fun j => by simp [hlo j])) i
        · exact (hy (fun j => hi j) (fun j => by simp [hlo j])) i
      exact hendpoint_iff c |>.2 he
    · intro hcθ
      have he := hendpoint_iff c |>.1 hcθ
      let x : Fin 2 → ℝ := fun j => (lo j + hi j) / 2
      have hx : inBox lo hi x := by
        intro j
        dsimp [x]
        constructor <;> linarith [hlo j]
      refine ⟨x, hx, ?_⟩
      intro y hy i
      exact (affine_endpoint_bound_for_slot a b source lo hi left right i hlo y hy).trans
        (max_le (he i).1 (he i).2)
  · intro hcθ x hx y hy i
    have he := hendpoint_iff c |>.1 hcθ
    exact (affine_endpoint_bound_for_slot a b source lo hi left right
      i hlo y hy).trans (max_le (he i).1 (he i).2)

end D5.S1.Digit.Infinite.FixedTailClosedBudget
