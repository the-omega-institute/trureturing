/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: ["mathlib/module/Mathlib.Data.Finset.Max"]
   utility: none
   digest: A fixed lower graph gives every actual factor completion a common positive margin. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
import Mathlib.Data.Finset.Max

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral Completion MemoryGraph InteriorRoot StrictSupply

/-- Gaps of all allowed high edges, including edges outside the retained core.
The target is uniquely determined by the original memory shift. -/
noncomputable def graphGapValues (n K : ℕ) (d : ℝ) : Finset ℝ := by
  classical
  exact (Finset.univ.filter (fun v : MemoryVertex n =>
    MemoryEdge .lower K d v .c (memoryShift v .c) ∧ memoryRun v .c K)).image
      (fun v => memoryValue v 0 - chi ^ (K - 1) * d)

/-- The exact finite minimum when high edges exist; zero is only a placeholder
for the separate branch in which the graph has no allowed high edge. -/
noncomputable def graphMargin (n K : ℕ) (d : ℝ) : ℝ := by
  classical
  exact if h : (graphGapValues n K d).Nonempty then (graphGapValues n K d).min' h else 0

/-- Every member is a strict lower-edge gap, so its attained minimum is positive. -/
theorem graph_gap_minimum (n K : ℕ) (d : ℝ)
    (nonempty : (graphGapValues n K d).Nonempty) :
    0 < graphMargin n K d ∧
      IsLeast (↑(graphGapValues n K d) : Set ℝ) (graphMargin n K d) := by
  classical
  have least := Finset.isLeast_min' (graphGapValues n K d) nonempty
  rw [graphMargin, dif_pos nonempty]
  refine ⟨?_, least⟩
  rcases Finset.mem_image.mp least.1 with ⟨v, hv, eq⟩
  rcases (Finset.mem_filter.mp hv).2 with ⟨edge, high⟩
  rw [← eq]
  exact sub_pos.mpr (edge.2.2 high)

/-- Each high letter on an original lower-graph path inherits the same finite
edge minimum at the before-Kth-c state. No margin is assumed on the path. -/
theorem lower_graph_high_gap (n K : ℕ) (d : ℝ) (positive : 0 < K) (memory : K ≤ n)
    (ω : ℤ → CuLetter) (member : ω ∈ MemoryLanguage .lower n K d)
    (i : ℤ) (high : ∀ k : Fin K, ω (i - (k : ℕ)) = .c) :
    (graphGapValues n K d).Nonempty ∧
      graphMargin n K d ≤ pastState ω i - chi ^ (K - 1) * d := by
  classical
  rcases (original_memory_graph_correspondence .lower n K d positive memory ω).mp member
    with ⟨p, path, _⟩
  have eq := path_memory_reconstruction p ω (fun j => (path j).1)
  have current : ω i = .c := by simpa using high ⟨0, positive⟩
  have run := (window_run n K positive (by omega) ω i).mpr high
  have edge : MemoryEdge .lower K d (memoryWindow n ω i) .c
      (memoryShift (memoryWindow n ω i) .c) := by
    simpa only [eq, window_shift, current] using path i
  have mem : memoryValue (memoryWindow n ω i) 0 - chi ^ (K - 1) * d ∈
      graphGapValues n K d := by
    apply Finset.mem_image.mpr
    exact ⟨memoryWindow n ω i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      edge, by simpa only [current] using run⟩, rfl⟩
  have nonempty : (graphGapValues n K d).Nonempty := ⟨_, mem⟩
  refine ⟨nonempty, (graph_gap_minimum n K d nonempty).2.2 mem |>.trans ?_⟩
  rw [window_value]
  exact sub_le_sub_right (original_memory_envelopes ω i n).2.2.1 _

/-- The numerical reset floor, independent of model and ownership. -/
noncomputable def resetFloor (R : Return) : ℝ :=
  hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high)

/-- The original three-term half minimum, with the graph term omitted precisely
when there is no allowed high edge. -/
noncomputable def fixedGraphActualMargin (n K : ℕ) (b : ℝ) (R : Return) : ℝ := by
  classical
  let d := (lam - b) / g ^ 2 / chi ^ K
  let automatic := b - actualAutomaticCost K
  let reset := g ^ 2 * chi ^ K * (resetFloor R - d)
  exact if (graphGapValues n K d).Nonempty then
    min (min automatic reset) (g ^ 2 * chi * graphMargin n K d) / 2
  else min automatic reset / 2

/-- Canonical completion is specified by literal runs, independently of any
supply conclusion. All-u and empty factors use just the merged low reset. -/
def CanonicalFactorCompletion (R : Return) (w : List CuLetter) (xs : List Return) : Prop :=
  if CuLetter.c ∈ w then
    ∃ (a : ℕ) (first : Return) (rest : List Return),
      (if w.getLast? = some CuLetter.c then w ++ [CuLetter.u] else w) =
        List.replicate a CuLetter.u ++ executionWord (first :: rest) ∧
      xs = (⟨R.m + a, 1, by have := R.m_pos; omega, by decide⟩ : Return) ::
        ⟨first.m + 1, first.r, by omega, first.r_pos⟩ :: rest
  else w = List.replicate w.length CuLetter.u ∧
    xs = [(⟨R.m + w.length, 1, by have := R.m_pos; omega, by decide⟩ : Return)]

/-- Uniqueness follows from the original finite-run parser, rather than from
error bounds or a choice of actual realization. -/
theorem canonical_factor_completion_unique (R : Return) (w : List CuLetter)
    (xs ys : List Return) (hx : CanonicalFactorCompletion R w xs)
    (hy : CanonicalFactorCompletion R w ys) : xs = ys := by
  classical
  have last (first : Return) (rest : List Return) :
      (executionWord (first :: rest)).getLast? = some CuLetter.u := by
    induction rest generalizing first with
    | nil => simp [executionWord, List.getLast?_replicate, first.m_pos.ne']
    | cons b rest ih =>
      simp only [executionWord, List.getLast?_append] at ih ⊢
      rw [ih b]
      rfl
  by_cases hc : CuLetter.c ∈ w
  · simp only [CanonicalFactorCompletion, if_pos hc] at hx hy
    rcases hx with ⟨a, first, rest, parse, rfl⟩
    rcases hy with ⟨a', first', rest', parse', rfl⟩
    have endFill : (if w.getLast? = some CuLetter.c then w ++ [CuLetter.u] else w) = [] ∨
        (if w.getLast? = some CuLetter.c then w ++ [CuLetter.u] else w).getLast? =
          some CuLetter.u := by
      rw [parse]
      right
      simp [last first rest]
    rcases finite_run_decomposition _ endFill with ⟨p, _, unique⟩
    have eq : (a, first :: rest) = (a', first' :: rest') :=
      (unique (a, first :: rest) parse).trans (unique (a', first' :: rest') parse').symm
    rcases Prod.mk.inj eq with ⟨rfl, heq⟩
    rcases List.cons.inj heq with ⟨rfl, rfl⟩
    rfl
  · simp only [CanonicalFactorCompletion, if_neg hc] at hx hy
    exact hx.2.trans hy.2.symm

set_option maxHeartbeats 1500000 in
/-- Quantitative guards for the canonical factor completion: the first visible
return uses the reset floor and every later return keeps the auxiliary guard. -/
private theorem auxiliary_factor_quantitative_completion (o : Ownership) (b : ℝ) (K : ℕ)
    (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K))) :
    ∃ R : Return, R.r = 1 ∧
      max (max (xSide .high) (ySide .high)) ((lam - b) / g ^ 2 / chi ^ K) <
        resetFloor R ∧
      ∀ (gamma : ℝ), 0 ≤ gamma → ∀ (model : Model) (w : List CuLetter),
        AuxiliaryFactor K ((lam - b) / g ^ 2 / chi ^ K + gamma) w → CuLetter.c ∈ w →
        ∃ (a : ℕ) (first : Return) (rest : List Return),
          let filled := if w.getLast? = some CuLetter.c then w ++ [CuLetter.u] else w
          let reset : Return := ⟨R.m + a, 1, by have := R.m_pos; omega, by decide⟩
          let extra : Return := ⟨first.m + 1, first.r, by omega, first.r_pos⟩
          filled = List.replicate a CuLetter.u ++ executionWord (first :: rest) ∧
          GuardTrace K (min (resetFloor R) ((lam - b) / g ^ 2 / chi ^ K + gamma))
            false .high (reset :: extra :: rest) (initial .high model) ∧
          listWeight (reset :: extra :: rest) = wordWeight w + (20 + 6 * R.m) +
            (if w.getLast? = some CuLetter.c then 12 else 6) := by
  classical
  let d := (lam - b) / g ^ 2 / chi ^ K
  rcases ClosedSupply.actual_reset_first_return o b K hK hqb hbp with
    ⟨R, hr, hB, hStrict, _, _, _, hIncrease⟩
  rcases auxiliary_factor_upper_completion o b K hK hqb hbp with ⟨Rold, _, complete⟩
  refine ⟨R, hr, hB, ?_⟩
  intro gamma hgamma model w hw hc
  rcases hw with ⟨ω, hω, i, occurrence⟩
  have base : AuxiliaryFactor K d w := by
    refine ⟨ω, ⟨hω.1, ?_⟩, i, occurrence⟩
    intro j high
    have cp : 0 < chi := pow_pos TailGeometry.tail_arithmetic.2.2.2.1 20
    exact (mul_le_mul_of_nonneg_left (by linarith : d ≤ d + gamma)
      (pow_pos cp (K - 1)).le).trans (hω.2 j high)
  rcases complete model w base hc with ⟨a, first, rest, parse, _, _, _, weight⟩
  let filled := if w.getLast? = some CuLetter.c then w ++ [CuLetter.u] else w
  let reset : Return := ⟨R.m + a, 1, by have := R.m_pos; omega, by decide⟩
  let extra : Return := ⟨first.m + 1, first.r, by omega, first.r_pos⟩
  change filled = List.replicate a CuLetter.u ++ executionWord (first :: rest) at parse
  have plen : filled.length = a + (executionWord (first :: rest)).length := by
    rw [parse]; simp
  have originalLetter (n : ℕ) (hn : n < filled.length)
      (hnc : n + 1 < filled.length ∨ filled[n] = .c) :
      ∃ hnw : n < w.length, filled[n] = w[n] := by
    by_cases he : w.getLast? = some CuLetter.c
    · have feq : filled = w ++ [CuLetter.u] := by simp [filled, he]
      have flen : filled.length = w.length + 1 := by simp [feq]
      by_cases hnw : n < w.length
      · refine ⟨hnw, ?_⟩; simp [feq, List.getElem_append, hnw]
      · have neq : n = w.length := by omega
        have fu : filled[n] = .u := by simp [feq, List.getElem_append, hnw, neq]
        rcases hnc with hnc | hnc
        · omega
        · rw [fu] at hnc; cases hnc
    · have feq : filled = w := by simp [filled, he]
      refine ⟨by simpa [feq] using hn, ?_⟩
      simp [feq]
  have letters : ∀ k : Fin (executionWord (first :: rest)).length,
      (k.val + 1 < (executionWord (first :: rest)).length ∨
        (executionWord (first :: rest))[k.val] = .c) →
      ω (i + (a : ℤ) + (k : ℕ)) = (executionWord (first :: rest))[k.val] := by
    intro k hk
    have atParsed : filled[a + k.val]'(by omega) = (executionWord (first :: rest))[k.val] := by
      simp [parse, List.getElem_append, show ¬ a + k.val < a by omega,
        show a + k.val - a = k.val by omega]
    have hcond : a + k.val + 1 < filled.length ∨ filled[a + k.val] = .c := by
      rcases hk with hk | hk
      · exact Or.inl (by omega)
      · exact Or.inr (atParsed.trans hk)
    obtain ⟨hnw, heq⟩ := originalLetter (a + k.val) (by omega) hcond
    have hh := occurrence ⟨a + k.val, hnw⟩
    have idx : i + ((a + k.val : ℕ) : ℤ) = i + (a : ℤ) + (k : ℕ) := by omega
    simpa only [idx] using hh.trans (heq.symm.trans atParsed)
  have trace := occurrence_run_guards K (d + gamma) (by omega)
    ω hω (i + a) (first :: rest) letters
  rcases bilateral_past_state with ⟨_, _, bounds, _⟩
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have gp : 0 < g := by dsimp [g, t]; nlinarith
  have g1 : g < 1 := by dsimp [g, t]; nlinarith
  have cp : 0 < chi := pow_pos gp 20
  have rp : 0 < rho := pow_pos gp 6
  have c1 : chi < 1 := pow_lt_one₀ gp.le g1 (by decide)
  have r1 : rho < 1 := pow_lt_one₀ gp.le g1 (by decide)
  have hp : 0 < hSide .high := by dsimp [hSide]; nlinarith
  have ap : 0 < aSide .high := mul_pos (sub_pos.mpr r1) hp
  have initialBounds := (actual_complete_boundary_geometry model []).1 .high 0
  simp only [List.take_nil, execute] at initialBounds
  have initialPos : 0 < initial .high model := lt_trans ap initialBounds.1
  have gap : 0 ≤ hSide .high - chi * initial .high model := by
    have hh := mul_le_mul_of_nonneg_right c1.le initialPos.le
    linarith [initialBounds.2]
  have pm : rho ^ (R.m + a) ≤ rho ^ R.m :=
    pow_le_pow_of_le_one rp.le r1.le (by omega)
  have merged : returnMap .high R (initial .high model) ≤
      returnMap .high reset (initial .high model) := by
    have hh := mul_le_mul_of_nonneg_right pm gap
    dsimp [returnMap, reset]; rw [hr]; simp only [pow_one]; linarith
  let z := returnMap .high reset (initial .high model)
  have bz : hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) < z :=
    lt_of_lt_of_le (hStrict _ initialBounds.1) merged
  have dz : d < z := by
    have dd := lt_of_le_of_lt (le_max_right
      (max (xSide .high) (ySide .high)) d) hB
    exact lt_trans dd bz
  have za : aSide .high ≤ z := by
    have hh := (actual_complete_boundary_geometry model [reset]).1 .high 1
    simpa [execute, z] using hh.1.le
  have firstOutput : returnMap .high first (pastState ω (i + a)) <
      returnMap .high extra z := by
    have hi := (hIncrease first.m first.r z (by have := first.m_pos; omega)
      (by have := first.r_pos; omega) trace.1 za).2
    have weak : returnMap .high first (pastState ω (i + a)) ≤
        returnMap .high first (hSide .high) := by
      have hh := mul_nonneg (mul_pos (pow_pos rp first.m) (pow_pos cp first.r)).le
        (sub_nonneg.mpr (bounds ω (i + a)).2)
      dsimp [returnMap]; nlinarith
    have strong : returnMap .high first (hSide .high) < returnMap .high extra z := by
      dsimp [returnMap, extra] at *; linarith only [hi]
    exact lt_of_le_of_lt weak strong
  have restTrace : GuardTrace K (min (resetFloor R) (d + gamma)) false .high rest
      (returnMap .high extra z) := by
    apply (uniform_guard_trace_iff_split K _ false .high rest _).mpr
    intro before item after split
    have old := (uniform_guard_trace_iff_split K (d + gamma) false .high rest _).mp
      trace.2.2 before item after split
    have diff := ResetCodebook.execute_seed_difference before
      (returnMap .high first (pastState ω (i + a))) (returnMap .high extra z)
    have positive := mul_pos (pow_pos gp (listWeight before)) (sub_pos.mpr firstOutput)
    refine ⟨old.1, ?_⟩
    intro high
    have bound := old.2 high
    change d + gamma ≤ _ at bound
    change min (resetFloor R) (d + gamma) ≤ _
    exact (min_le_right _ _).trans (bound.trans (by linarith))
  refine ⟨a, first, rest, parse, ?_, ?_⟩
  · refine ⟨by dsimp [reset]; omega, ?_, trace.1, ?_, restTrace⟩
    · intro high
      dsimp [reset] at high
      omega
    · intro _
      exact (min_le_left _ _).trans bz.le
  · dsimp only [listWeight] at weight ⊢
    dsimp only [reset, extra] at *
    omega

set_option maxHeartbeats 1800000 in
-- One state guard is chosen before all factors; actual slot costs consume it.
/-- Fixing the lower graph fixes one positive actual margin before factors of
arbitrary length, return exponents, depth and weight. The same reset works for
both actual source models and every endpoint ownership. Original literal tails
and their zero-error futures are part of every ActualPairSupply witness. -/
theorem fixed_lower_graph_actual_margin (n K : ℕ) (b : ℝ) (hK : 2 ≤ K) (memory : K ≤ n)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K))) :
    ∃ R : Return, R.r = 1 ∧
      max (max (xSide .high) (ySide .high)) ((lam - b) / g ^ 2 / chi ^ K) < resetFloor R ∧
      0 < fixedGraphActualMargin n K b R ∧
      ((graphGapValues n K ((lam - b) / g ^ 2 / chi ^ K)).Nonempty →
        0 < graphMargin n K ((lam - b) / g ^ 2 / chi ^ K) ∧
        IsLeast (↑(graphGapValues n K ((lam - b) / g ^ 2 / chi ^ K)) : Set ℝ)
          (graphMargin n K ((lam - b) / g ^ 2 / chi ^ K))) ∧
      ∀ (model : Model) (o : Ownership) (w : List CuLetter),
        (∃ ω ∈ MemoryLanguage .lower n K ((lam - b) / g ^ 2 / chi ^ K), Occurs ω w) →
        ∃! xs : List Return, CanonicalFactorCompletion R w xs ∧
          ActualPairSupply model o (b - fixedGraphActualMargin n K b R) .strict xs ∧
          listWeight xs = wordWeight w + (20 + 6 * R.m) +
            (if CuLetter.c ∈ w then if w.getLast? = some CuLetter.c then 12 else 6 else 0) := by
  classical
  let d := (lam - b) / g ^ 2 / chi ^ K
  rcases auxiliary_factor_quantitative_completion (fun _ => false) b K hK hqb hbp with
    ⟨R, hr, hB, complete⟩
  let B := resetFloor R
  let auto := b - actualAutomaticCost K
  let scale := g ^ 2 * chi ^ K
  let graph := g ^ 2 * chi * graphMargin n K d
  let gamma := if (graphGapValues n K d).Nonempty then graphMargin n K d / chi ^ (K - 1)
    else B - d
  let eps := fixedGraphActualMargin n K b R
  have gp : 0 < g := TailGeometry.tail_arithmetic.2.2.2.1
  have cp : 0 < chi := pow_pos gp 20
  have sp : 0 < scale := mul_pos (pow_pos gp 2) (pow_pos cp K)
  have Bd : d < B := (le_max_right _ _).trans_lt hB
  have ap : 0 < auto := sub_pos.mpr ((actual_automatic_cost_envelope K hK).1.trans hqb)
  have rp : 0 < scale * (B - d) := mul_pos sp (sub_pos.mpr Bd)
  have gpMargin : (graphGapValues n K d).Nonempty → 0 < graph := by
    intro hn
    exact mul_pos (mul_pos (pow_pos gp 2) cp) (graph_gap_minimum n K d hn).1
  have gammap : 0 < gamma := by
    dsimp [gamma]
    split_ifs with hn
    · exact div_pos (graph_gap_minimum n K d hn).1 (pow_pos cp (K - 1))
    · exact sub_pos.mpr Bd
  have ep : 0 < eps := by
    dsimp [eps, fixedGraphActualMargin]
    split_ifs with hn
    · exact div_pos (lt_min (lt_min ap rp) (gpMargin hn)) (by norm_num)
    · exact div_pos (lt_min ap rp) (by norm_num)
  have ea : eps < auto := by
    dsimp [eps, fixedGraphActualMargin]
    split_ifs
    · have hm := (min_le_left (min auto (scale * (B - d))) graph).trans
        (min_le_left auto (scale * (B - d)))
      change min (min auto (scale * (B - d))) graph / 2 < auto
      linarith
    · have hm := min_le_left auto (scale * (B - d))
      change min auto (scale * (B - d)) / 2 < auto
      linarith
  have er : eps < scale * (B - d) := by
    dsimp [eps, fixedGraphActualMargin]
    split_ifs
    · have hm := (min_le_left (min auto (scale * (B - d))) graph).trans
        (min_le_right auto (scale * (B - d)))
      change min (min auto (scale * (B - d))) graph / 2 < scale * (B - d)
      linarith
    · have hm := min_le_right auto (scale * (B - d))
      change min auto (scale * (B - d)) / 2 < scale * (B - d)
      linarith
  have eg : eps < scale * gamma := by
    by_cases hn : (graphGapValues n K d).Nonempty
    · have id : scale * gamma = graph := by
        dsimp [gamma]
        rw [if_pos hn]
        have pk : chi ^ K = chi ^ (K - 1) * chi := by
          rw [← pow_succ]; congr 1; omega
        dsimp [scale, graph]
        rw [pk]
        field_simp
      rw [id]
      have hm := min_le_right (min auto (scale * (B - d))) graph
      have gpos := gpMargin hn
      dsimp [eps, fixedGraphActualMargin]
      rw [if_pos hn]
      change min (min auto (scale * (B - d))) graph / 2 < graph
      linarith
    · simpa [gamma, hn] using er
  have guardCost (D : ℝ) (hD : min B (d + gamma) ≤ D) : lam - scale * D < b - eps := by
    have bound : eps < scale * (min B (d + gamma) - d) := by
      by_cases h : B ≤ d + gamma
      · simpa only [min_eq_left h] using er
      · rw [min_eq_right (le_of_not_ge h)]
        simpa using eg
    have slope := mul_le_mul_of_nonneg_left hD sp.le
    have eq : scale * d = lam - b := by dsimp [scale, d]; field_simp
    linarith
  have supplier (model : Model) (o : Ownership) (xs : List Return)
      (trace : GuardTrace K (min B (d + gamma)) false .high xs (initial .high model)) :
      ActualPairSupply model o (b - eps) .strict xs := by
    apply actual_capped_strict_supply_of_high_costs model o K hK (b - eps)
      (by dsimp [auto] at ea; linarith) xs
    · intro a ha
      obtain ⟨before, after, split⟩ := List.mem_iff_append.mp ha
      exact ((uniform_guard_trace_iff_split K _ false .high xs _).mp trace
        before a after split).1
    · intro before a after split high
      exact guardCost _ (((uniform_guard_trace_iff_split K _ false .high xs _).mp trace
        before a after split).2 high)
  have strengthened (ω : ℤ → CuLetter) (hw : ω ∈ MemoryLanguage .lower n K d) :
      ω ∈ AuxiliaryLanguage K (d + gamma) := by
    refine ⟨hw.1, ?_⟩
    intro i high
    have hg := lower_graph_high_gap n K d (by omega) memory ω hw i high
    have hn := hg.1
    have gammaeq : chi ^ (K - 1) * gamma = graphMargin n K d := by
      dsimp [gamma]
      rw [if_pos hn]
      field_simp
    rw [mul_add, gammaeq]
    linarith [hg.2]
  refine ⟨R, hr, hB, ep, graph_gap_minimum n K d, ?_⟩
  intro model o w factor
  rcases factor with ⟨ω, hw, occurrence⟩
  by_cases hc : CuLetter.c ∈ w
  · rcases complete gamma gammap.le model w ⟨ω, strengthened ω hw, occurrence⟩ hc with
      ⟨a, first, rest, parse, quantitative, weight⟩
    let reset : Return := ⟨R.m + a, 1, by have := R.m_pos; omega, by decide⟩
    let extra : Return := ⟨first.m + 1, first.r, by omega, first.r_pos⟩
    let xs := reset :: extra :: rest
    have canon : CanonicalFactorCompletion R w xs := by
      simp only [CanonicalFactorCompletion, if_pos hc]
      exact ⟨a, first, rest, parse, rfl⟩
    refine ⟨xs, ⟨canon, supplier model o xs quantitative, ?_⟩, ?_⟩
    · simpa only [if_pos hc] using weight
    · intro ys hy
      exact canonical_factor_completion_unique R w ys xs hy.1 canon
  · have allu : w = List.replicate w.length CuLetter.u := by
      apply List.eq_replicate_length.mpr
      intro l hl
      cases l
      · exact False.elim (hc hl)
      · rfl
    let reset : Return := ⟨R.m + w.length, 1, by have := R.m_pos; omega, by decide⟩
    have tr : GuardTrace K (min B (d + gamma)) false .high [reset]
        (initial .high model) := by
      refine ⟨by dsimp [reset]; omega, ?_, trivial⟩
      intro high
      dsimp [reset] at high
      omega
    have canon : CanonicalFactorCompletion R w [reset] := by
      simp only [CanonicalFactorCompletion, if_neg hc]
      exact ⟨allu, rfl⟩
    have repweight (a : ℕ) : wordWeight (List.replicate a CuLetter.u) = 6 * a := by
      induction a with
      | zero => rfl
      | succ a ih => simp [List.replicate_succ, wordWeight, ih]; omega
    refine ⟨[reset], ⟨canon, supplier model o [reset] tr, ?_⟩, ?_⟩
    · simp only [if_neg hc]
      rw [allu, repweight]
      simp only [listWeight, reset]
      omega
    · intro ys hy
      exact canonical_factor_completion_unique R w ys [reset] hy.1 canon

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedGraphMargin
