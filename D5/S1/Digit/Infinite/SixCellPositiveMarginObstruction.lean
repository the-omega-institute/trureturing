/- GID: D5/S1/Digit/Infinite/SixCellPositiveMarginObstruction
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SixCellPositiveMarginObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: At most six connected cells cannot decode with a positive uniform margin. -/

import D5.S1.Digit.Infinite.ClosedObservationGraphRealization
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Monotone
import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SixCellPositiveMarginObstruction

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
  (closed_observation_graph_realization)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open scoped Topology

/-- An actual cell includes only scalars in the source support. -/
def cell {q : ℕ} (Q : ℝ → Fin q) (i : Fin q) : Set ℝ :=
  {x | x ∈ stateInterval false ∧ Q x = i}

/-- Every fibre is a nonempty connected interval; the cell numbering is arbitrary. -/
def connectedInstrument {q : ℕ} (Q : ℝ → Fin q) : Prop :=
  ∀ i, IsConnected (cell Q i)

/-- Closed cell rectangles distinguish all legal labelled branch points. -/
def closedGridPure {q : ℕ} (Q : ℝ → Fin q) : Prop :=
  ∀ (i j : Fin q) (l m : Label) (y z : ℝ),
    y ∈ stateInterval (outgoing l) → z ∈ stateInterval (outgoing m) →
    y ∈ closure (cell Q j) → z ∈ closure (cell Q j) →
    branch l y ∈ closure (cell Q i) → branch m z ∈ closure (cell Q i) → l = m

private lemma parameters : (8 / 13 : ℝ) < t ∧ t < 5 / 8 ∧
    t ^ 2 = 1 - t ∧ g = 2 * t - 1 ∧ t ^ 4 = 2 - 3 * t := by
  have hp : 0 < t := inv_pos.mpr Real.goldenRatio_pos
  have hs : t ^ 2 + t = 1 := by
    change (Real.goldenRatio⁻¹) ^ 2 + Real.goldenRatio⁻¹ = 1
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  have h3 : t ^ 3 = 2 * t - 1 := by
    nlinarith [congrArg (fun x : ℝ => t * x) hs]
  refine ⟨?_, ?_, by linarith, h3, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith [congrArg (fun x : ℝ => t ^ 2 * x) hs]

private lemma realize (l : Label) {y : ℝ} (hy : y ∈ stateInterval (outgoing l)) :
    ∃ x : LegalDigits, window x 0 = l ∧ kappa x = branch l y ∧
      kappa (originalT x) = y := by
  obtain ⟨_, hrange, hrec, hprepend, _⟩ :=
    closed_observation_graph_realization
  rw [← hrange] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨x, hx, _⟩ := hprepend false l (outgoing l) z ⟨by simp, rfl⟩ hz
  refine ⟨x, hx.2.1, ?_, ?_⟩
  · rw [(hrec x).1, hx.2.1, hx.2.2, hzy]
  · rw [hx.2.2, hzy]

private lemma branch_support (l : Label) {y : ℝ}
    (hy : y ∈ stateInterval (outgoing l)) : branch l y ∈ stateInterval false := by
  obtain ⟨x, _, hx, _⟩ := realize l hy
  rw [← hx]
  rw [← closed_observation_graph_realization.2.1]
  exact ⟨x, by simp [stateAddress], rfl⟩

private lemma purity_of_correct {q : ℕ} (Q : ℝ → Fin q)
    (d : Fin q × Fin q → Label) {η : ℝ} (hη : 0 < η)
    (hcorrect : ∀ x : LegalDigits, ∀ e₀ e₁ : ℝ, |e₀| < η → |e₁| < η →
      d (Q (Set.projIcc (-1) (1 + t) (by linarith [parameters.1]) (kappa x + e₀)),
         Q (Set.projIcc (-1) (1 + t) (by linarith [parameters.1])
           (kappa (originalT x) + e₁))) = window x 0) : closedGridPure Q := by
  intro i j l m y z hyl hzm hy hz hly hmz
  have decode (a : Label) (b : ℝ) (hb : b ∈ stateInterval (outgoing a))
      (hbj : b ∈ closure (cell Q j)) (hbi : branch a b ∈ closure (cell Q i)) :
      d (i, j) = a := by
    obtain ⟨x, hxl, hx, hxt⟩ := realize a hb
    obtain ⟨u, hu, heu⟩ := Real.mem_closure_iff.mp hbi η hη
    obtain ⟨v, hv, hev⟩ := Real.mem_closure_iff.mp hbj η hη
    have hc := hcorrect x (u - kappa x) (v - kappa (originalT x))
      (by simpa [hx] using heu) (by simpa [hxt] using hev)
    rw [add_sub_cancel, add_sub_cancel] at hc
    simp only [Set.projIcc_of_mem (by linarith [parameters.1])
      (show u ∈ Set.Icc (-1) (1 + t) from hu.1),
      Set.projIcc_of_mem (by linarith [parameters.1])
        (show v ∈ Set.Icc (-1) (1 + t) from hv.1)] at hc
    simpa only [hu.2, hv.2, hxl] using hc
  exact (decode l y hyl hy hly).symm.trans (decode m z hzm hz hmz)

private lemma ordered_relabel {q : ℕ} (Q : ℝ → Fin q) (hQ : connectedInstrument Q) :
    ∃ e : Fin q ≃ Fin q, MonotoneOn (fun x => e (Q x)) (stateInterval false) := by
  classical
  choose r hr using fun i => (hQ i).nonempty
  have hrinj : Function.Injective r := by
    intro i j h
    exact (hr i).2.symm.trans (h ▸ (hr j).2)
  let s := Finset.univ.image r
  have hcard : s.card = q := by
    rw [Finset.card_image_of_injective _ hrinj, Finset.card_fin]
  let a := s.orderEmbOfFin hcard
  have ha (i : Fin q) : a i ∈ s := s.orderEmbOfFin_mem hcard i
  have har (i : Fin q) : r (Q (a i)) = a i := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (ha i)
    rw [← hj, (hr j).2]
  have hf : Function.Injective (fun i => Q (a i)) := by
    intro i j hij
    apply a.injective
    rw [← har i, ← har j]
    exact congrArg r hij
  let f : Fin q ≃ Fin q := Equiv.ofBijective (fun i => Q (a i))
    ⟨hf, (Finite.surjective_of_injective hf)⟩
  have haX (i : Fin q) : a i ∈ stateInterval false := by
    rw [← har i]; exact (hr _).1
  refine ⟨f.symm, ?_⟩
  intro x hx y hy hxy
  by_contra h
  have hij : f.symm (Q y) < f.symm (Q x) := lt_of_not_ge h
  have hab := a.strictMono hij
  have hax : Q (a (f.symm (Q x))) = Q x := f.apply_symm_apply (Q x)
  have hay : Q (a (f.symm (Q y))) = Q y := f.apply_symm_apply (Q y)
  have hne : Q x ≠ Q y := by intro he; simp [he] at hij
  by_cases hle : a (f.symm (Q y)) ≤ x
  · have hc := (hQ (Q y)).Icc_subset ⟨haX _, hay⟩ ⟨hy, rfl⟩ ⟨hle, hxy⟩
    exact hne hc.2
  · have hc := (hQ (Q x)).Icc_subset ⟨hx, rfl⟩ ⟨haX _, hax⟩
      ⟨(lt_of_not_ge hle).le, hab.le⟩
    exact hne (hay.symm.trans hc.2).symm

private lemma closed_interval {q : ℕ} (Q : ℝ → Fin q)
    (hQ : MonotoneOn Q (stateInterval false)) (i : Fin q) :
    (closure (cell Q i)).OrdConnected := by
  obtain ⟨u, hu, heu⟩ :=
    (Set.ordConnected_singleton (a := i)).preimage_monotoneOn hQ
  have hcell : cell Q i = stateInterval false ∩ u := by
    rw [← heu]
    ext x
    simp only [cell, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff]
  have hc : (cell Q i).OrdConnected := by
    rw [hcell]
    exact Set.ordConnected_Icc.inter hu
  exact hc.isPreconnected.closure.ordConnected

private lemma adjacent_boundary {q : ℕ} (Q : ℝ → Fin q)
    (hQ : MonotoneOn Q (stateInterval false)) (i j : Fin q)
    (hij : i.val + 1 = j.val) {a b : ℝ}
    (ha : a ∈ cell Q i) (hb : b ∈ cell Q j) :
    ∃ β : ℝ, a ≤ β ∧ β ≤ b ∧
      β ∈ closure (cell Q i) ∧ β ∈ closure (cell Q j) := by
  have hi : i < j := by omega
  have hupper : ∀ x ∈ cell Q i, x ≤ b := by
    intro x hx
    by_contra h
    have hle := hQ hb.1 hx.1 (lt_of_not_ge h).le
    rw [hb.2, hx.2] at hle
    exact hi.not_ge hle
  have hn : (cell Q i).Nonempty := ⟨a, ha⟩
  have hB : BddAbove (cell Q i) := ⟨b, hupper⟩
  let β := sSup (cell Q i)
  have hal : a ≤ β := le_csSup hB ha
  have hbu : β ≤ b := csSup_le hn hupper
  refine ⟨β, hal, hbu, csSup_mem_closure hn hB, ?_⟩
  apply Real.mem_closure_iff.mpr
  intro ε hε
  by_cases he : β = b
  · exact ⟨b, hb, by simp [he, hε]⟩
  have hlt : β < b := lt_of_le_of_ne hbu he
  let z := min b (β + ε / 2)
  have hzlo : β < z := lt_min hlt (by linarith)
  have hzhi : z ≤ b := min_le_left _ _
  have hzε : z ≤ β + ε / 2 := min_le_right _ _
  have hzX : z ∈ stateInterval false := ⟨ha.1.1.trans (hal.trans hzlo.le),
    hzhi.trans hb.1.2⟩
  have hzi : i ≤ Q z := by simpa [ha.2] using hQ ha.1 hzX (hal.trans hzlo.le)
  have hzj : Q z ≤ j := by simpa [hb.2] using hQ hzX hb.1 hzhi
  have hne : Q z ≠ i := by
    intro heq
    exact (not_le_of_gt hzlo) (le_csSup hB ⟨hzX, heq⟩)
  have heq : Q z = j := by apply Fin.ext; omega
  refine ⟨z, ⟨hzX, heq⟩, ?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hzlo.le)]
  linarith

/-- The five actual windows, ordered three, null, five, two, twenty-five. -/
def labelIndex : Fin 5 → Label := fun i =>
  if i.val = 0 then threeLabel else if i.val = 1 then nullLabel else
    if i.val = 2 then fiveLabel else if i.val = 3 then twoLabel else twoFiveLabel

theorem label_index_injective : Function.Injective labelIndex := by
  intro i j he
  have he' := congrArg (fun w : Label => (w.val 0, w.val 1, w.val 2)) he
  fin_cases i <;> try fin_cases j
  all_goals simp [labelIndex, threeLabel, nullLabel, fiveLabel, twoLabel, twoFiveLabel] at he'
  all_goals rfl

private lemma forced_colors (Q : ℝ → Fin 6)
    (hQ : MonotoneOn Q (stateInterval false)) (hp : closedGridPure Q) :
    Q (-1) = 0 ∧ Q (-t ^ 2) = 1 ∧ Q g = 2 ∧ Q t = 3 ∧ Q (2 * t) = 4 ∧
    Q (1 + t) = 5 ∧ Q (-1 / 2) = 0 ∧ Q 0 = 1 ∧ Q (t / 2) = 2 := by
  classical
  obtain ⟨htlo, hthi, hs, hg, hfour⟩ := parameters
  have ht : 0 < t := by linarith
  have hhalf : (1 / 2 : ℝ) < t := by linarith
  have htone : t < 1 := by linarith
  let a : Fin 5 → ℝ := fun i =>
    if i.val = 0 then -t ^ 2 else if i.val = 1 then g else if i.val = 2 then t else
      if i.val = 3 then 2 * t else 1 + t
  let b : Fin 5 → ℝ := fun i =>
    if i.val = 0 then -t - t ^ 4 else if i.val = 1 then -t ^ 4 else
      if i.val = 2 then g else if i.val = 3 then 1 - t ^ 4 else 2 * t
  have hinj : Function.Injective labelIndex := label_index_injective
  have hmlegal (i : Fin 5) : (-1 : ℝ) ∈ stateInterval (outgoing (labelIndex i)) := by
    fin_cases i <;> simp [labelIndex, stateInterval, outgoing, threeLabel,
      nullLabel, fiveLabel, twoLabel, twoFiveLabel] <;> linarith
  have htlegal (i : Fin 5) : t ∈ stateInterval (outgoing (labelIndex i)) := by
    fin_cases i <;> simp [labelIndex, stateInterval, outgoing, threeLabel,
      nullLabel, fiveLabel, twoLabel, twoFiveLabel] <;> linarith
  have haeval (i : Fin 5) : branch (labelIndex i) (-1) = a i := by
    fin_cases i <;> simp [labelIndex, a, branch, offset, threeLabel, nullLabel,
      fiveLabel, twoLabel, twoFiveLabel, hs, hg] <;> ring
  have hbeval (i : Fin 5) : branch (labelIndex i) t = b i := by
    fin_cases i <;> simp [labelIndex, b, branch, offset, threeLabel, nullLabel,
      fiveLabel, twoLabel, twoFiveLabel, hs, hg, hfour] <;> nlinarith only [hs]
  have haX (i : Fin 5) : a i ∈ stateInterval false :=
    haeval i ▸ branch_support (labelIndex i) (hmlegal i)
  have hbX (i : Fin 5) : b i ∈ stateInterval false :=
    hbeval i ▸ branch_support (labelIndex i) (htlegal i)
  have haMono : StrictMono a := by
    intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> try fin_cases j
    all_goals norm_num at hij
    all_goals simp [a] <;>
      nlinarith only [hs, hg, htlo, hthi]
  have hbMono : StrictMono b := by
    intro i j hij
    change i.val < j.val at hij
    fin_cases i <;> try fin_cases j
    all_goals norm_num at hij
    all_goals simp [b] <;>
      nlinarith only [hs, hg, hfour, htlo, hthi]
  have mem (x : ℝ) (hx : x ∈ stateInterval false) :
      x ∈ closure (cell Q (Q x)) := subset_closure ⟨hx, rfl⟩
  have row (v : Fin 5 → ℝ) (y : ℝ)
      (hev : ∀ i, branch (labelIndex i) y = v i)
      (hy : ∀ i, y ∈ stateInterval (outgoing (labelIndex i)))
      (hv : StrictMono v) : StrictMono (fun i => Q (v i)) := by
    intro i j hij
    have hxi := hev i ▸ branch_support (labelIndex i) (hy i)
    have hxj := hev j ▸ branch_support (labelIndex j) (hy j)
    have hyX : y ∈ stateInterval false := by
      have hy0 := hy 0
      change y ∈ stateInterval false at hy0
      exact hy0
    have hle := hQ hxi hxj (hv hij).le
    apply lt_of_le_of_ne hle
    intro he
    have hil := hp (Q (v i)) (Q y) (labelIndex i) (labelIndex j) y y (hy i) (hy j)
      (mem y hyX) (mem y hyX) (by rw [hev i]; exact mem _ hxi)
      (by rw [hev j, he]; exact mem _ hxj)
    exact (ne_of_lt hij) (hinj hil)
  have hA := row a (-1) haeval hmlegal haMono
  have hB := row b t hbeval htlegal hbMono
  have hA01 := hA (show (0 : Fin 5) < 1 by decide)
  have hA12 := hA (show (1 : Fin 5) < 2 by decide)
  have hA23 := hA (show (2 : Fin 5) < 3 by decide)
  have hA34 := hA (show (3 : Fin 5) < 4 by decide)
  have hB01 := hB (show (0 : Fin 5) < 1 by decide)
  have hB12 := hB (show (1 : Fin 5) < 2 by decide)
  have hB23 := hB (show (2 : Fin 5) < 3 by decide)
  have hB34 := hB (show (3 : Fin 5) < 4 by decide)
  simp [a, b] at hA01 hA12 hA23 hA34 hB01 hB12 hB23 hB34
  have hQg : Q g = 2 := by apply Fin.ext; omega
  have hQt : Q t = 3 := by apply Fin.ext; omega
  have hQ2t : Q (2 * t) = 4 := by apply Fin.ext; omega
  have hQphi : Q (1 + t) = 5 := by apply Fin.ext; omega
  have hQb0 : Q (-t - t ^ 4) = 0 := by apply Fin.ext; omega
  have hQb1 : Q (-t ^ 4) = 1 := by apply Fin.ext; omega
  have hQb3 : Q (1 - t ^ 4) = 3 := by apply Fin.ext; omega
  have inX (x : ℝ) (hlo : -1 ≤ x) (hhi : x ≤ 1 + t) :
      x ∈ stateInterval false := ⟨hlo, hhi⟩
  have hXm : (-1 : ℝ) ∈ stateInterval false := inX _ (by linarith) (by linarith)
  have hXp : 1 + t ∈ stateInterval false := inX _ (by linarith) (by linarith)
  have hQm : Q (-1) = 0 := by
    have hh := hQ hXm (hbX 0) (by dsimp [b]; nlinarith only [htlo, hfour])
    norm_num [b, hQb0] at hh
    apply Fin.ext; omega
  have hQamin : Q (-t ^ 2) = 1 := by
    have hle : (Q (-t ^ 2)).val ≤ 1 := by omega
    have hne : Q (-t ^ 2) ≠ 0 := by
      intro he
      have hp3 : branch threeLabel (1 + t) = -1 := by
        simp [branch, offset, threeLabel, hg]
        nlinarith only [hs]
      have hp0 : branch nullLabel (1 + t) = -t ^ 2 := by
        simp [branch, offset, nullLabel, hg]
        nlinarith only [hs]
      have hn := hp 0 5 threeLabel nullLabel (1 + t) (1 + t)
        (by simpa [stateInterval, outgoing, threeLabel] using hXp)
        (by simpa [stateInterval, outgoing, nullLabel] using hXp)
        (by simpa [hQphi] using mem _ hXp) (by simpa [hQphi] using mem _ hXp)
        (by rw [hp3]; simpa [hQm] using mem _ hXm)
        (by rw [hp0]; simpa [a, he] using mem _ (haX 0))
      have hn' := congrArg (fun w : Label => w.val 1) hn
      norm_num [threeLabel, nullLabel] at hn'
    apply Fin.ext; omega
  let s : ℝ := t / 2
  let r : ℝ := (1 + t) / 2
  have hXmhalf : (-1 / 2 : ℝ) ∈ stateInterval false := inX _ (by linarith) (by linarith)
  have hXzero : (0 : ℝ) ∈ stateInterval false := inX _ (by linarith) (by linarith)
  have hXs : s ∈ stateInterval false := inX _ (by dsimp [s]; linarith) (by dsimp [s]; linarith)
  have hXr : r ∈ stateInterval false := inX _ (by dsimp [r]; linarith) (by dsimp [r]; linarith)
  have hfix3 : branch threeLabel (-1 / 2) = -1 / 2 := by
    simp [branch, offset, threeLabel, hg]; ring
  have hfix0 : branch nullLabel 0 = 0 := by simp [branch, offset, nullLabel]
  have hfix5 : branch fiveLabel s = s := by
    simp [branch, offset, fiveLabel, s, hg, hs]; nlinarith only [hs]
  have hfix2 : branch twoLabel r = r := by
    simp [branch, offset, twoLabel, r, hg]
    nlinarith only [hs]
  have hQslegal : s ∈ stateInterval (outgoing fiveLabel) := by
    simp [stateInterval, outgoing, fiveLabel]; dsimp [s]; constructor <;> linarith
  have diagonal (u v : ℝ) (lu lv : Label)
      (hu : u ∈ stateInterval (outgoing lu)) (hv : v ∈ stateInterval (outgoing lv))
      (hfu : branch lu u = u) (hfv : branch lv v = v)
      (hux : u ∈ stateInterval false) (hvx : v ∈ stateInterval false)
      (hneq : lu ≠ lv) : Q u ≠ Q v := by
    intro he
    apply hneq
    exact hp (Q u) (Q u) lu lv u v hu hv (mem u hux)
      (by simpa [he] using mem v hvx) (by rw [hfu]; exact mem u hux)
      (by rw [hfv]; simpa [he] using mem v hvx)
  have hD01 := diagonal (-1 / 2) 0 threeLabel nullLabel
    (by simpa [stateInterval, outgoing, threeLabel] using hXmhalf)
    (by simpa [stateInterval, outgoing, nullLabel] using hXzero)
    hfix3 hfix0 hXmhalf hXzero (by
      intro he; have hh := congrArg (fun w : Label => w.val 1) he
      norm_num [threeLabel, nullLabel] at hh)
  have hD12 := diagonal 0 s nullLabel fiveLabel
    (by simpa [stateInterval, outgoing, nullLabel] using hXzero) hQslegal
    hfix0 hfix5 hXzero hXs (by
      intro he; have hh := congrArg (fun w : Label => w.val 2) he
      norm_num [nullLabel, fiveLabel] at hh)
  have hD23 := diagonal s r fiveLabel twoLabel hQslegal
    (by simpa [stateInterval, outgoing, twoLabel] using hXr)
    hfix5 hfix2 hXs hXr (by
      intro he; have hh := congrArg (fun w : Label => w.val 0) he
      norm_num [fiveLabel, twoLabel] at hh)
  have hL01 := hQ hXmhalf hXzero (by linarith)
  have hL12 := hQ hXzero hXs (by dsimp [s]; linarith)
  have hL23 := hQ hXs hXr (by dsimp [s, r]; linarith)
  have hRlo := hQ (haX 2) hXr (by dsimp [a, r]; linarith)
  have hRhi := hQ hXr (hbX 3) (by dsimp [b, r]; nlinarith only [htlo, hfour])
  simp [a, b, hQt, hQb3] at hRlo hRhi
  have hQr : Q r = 3 := by apply Fin.ext; omega
  have hQs : Q s = 2 := by apply Fin.ext; omega
  have hQ0 : Q 0 = 1 := by apply Fin.ext; omega
  have hQhalf : Q (-1 / 2) = 0 := by apply Fin.ext; omega
  exact ⟨hQm, hQamin, hQg, hQt, hQ2t, hQphi, hQhalf, hQ0, hQs⟩

private lemma no_pure_ordered (Q : ℝ → Fin 6)
    (hQ : MonotoneOn Q (stateInterval false)) (hp : closedGridPure Q) : False := by
  classical
  obtain ⟨htlo, hthi, hs, hg, hfour⟩ := parameters
  obtain ⟨hQm, hQamin, hQg, hQt, hQ2t, hQphi, hQhalf, hQ0, hQs⟩ := forced_colors Q hQ hp
  let a : Fin 5 → ℝ := fun i =>
    if i.val = 0 then -t ^ 2 else if i.val = 1 then g else if i.val = 2 then t else
      if i.val = 3 then 2 * t else 1 + t
  let s : ℝ := t / 2
  have inX (x : ℝ) (hlo : -1 ≤ x) (hhi : x ≤ 1 + t) :
      x ∈ stateInterval false := ⟨hlo, hhi⟩
  have hXm : (-1 : ℝ) ∈ stateInterval false := inX _ (by linarith) (by linarith)
  have hXp : 1 + t ∈ stateInterval false := inX _ (by linarith) (by linarith)
  have hXmhalf : (-1 / 2 : ℝ) ∈ stateInterval false := inX _ (by linarith) (by linarith)
  have hXzero : (0 : ℝ) ∈ stateInterval false := inX _ (by linarith) (by linarith)
  have hXs : s ∈ stateInterval false := inX _ (by dsimp [s]; linarith) (by dsimp [s]; linarith)
  have hmlegal (i : Fin 5) : (-1 : ℝ) ∈ stateInterval (outgoing (labelIndex i)) := by
    fin_cases i <;> simp [labelIndex, stateInterval, outgoing, threeLabel,
      nullLabel, fiveLabel, twoLabel, twoFiveLabel] <;> linarith only [htlo]
  have htlegal (i : Fin 5) : t ∈ stateInterval (outgoing (labelIndex i)) := by
    fin_cases i <;> simp [labelIndex, stateInterval, outgoing, threeLabel,
      nullLabel, fiveLabel, twoLabel, twoFiveLabel] <;> linarith only [htlo]
  have haeval (i : Fin 5) : branch (labelIndex i) (-1) = a i := by
    fin_cases i <;> simp [labelIndex, a, branch, offset, threeLabel, nullLabel,
      fiveLabel, twoLabel, twoFiveLabel, hs, hg] <;> ring
  have haX (i : Fin 5) : a i ∈ stateInterval false :=
    haeval i ▸ branch_support (labelIndex i) (hmlegal i)
  have hbeval4 : branch twoFiveLabel t = 2 * t := by
    simp [branch, offset, twoFiveLabel, hs, hg]; nlinarith only [hs]
  have mem (x : ℝ) (hx : x ∈ stateInterval false) :
      x ∈ closure (cell Q (Q x)) := subset_closure ⟨hx, rfl⟩
  have hfix3 : branch threeLabel (-1 / 2) = -1 / 2 := by
    simp [branch, offset, threeLabel, hg]; ring
  have hfix0 : branch nullLabel 0 = 0 := by simp [branch, offset, nullLabel]
  have hfix5 : branch fiveLabel s = s := by
    simp [branch, offset, fiveLabel, s, hg, hs]; nlinarith only [hs]
  have hQslegal : s ∈ stateInterval (outgoing fiveLabel) := by
    simp [stateInterval, outgoing, fiveLabel]; dsimp [s]; constructor <;> linarith
  obtain ⟨β₁, hβ₁lo, hβ₁hi, hβ₁0, hβ₁1⟩ := adjacent_boundary Q hQ 0 1 (by decide)
    (show (-1 / 2 : ℝ) ∈ cell Q 0 from ⟨hXmhalf, hQhalf⟩)
    (show -t ^ 2 ∈ cell Q 1 from ⟨haX 0, hQamin⟩)
  obtain ⟨β₂, hβ₂lo, hβ₂hi, hβ₂1, hβ₂2⟩ := adjacent_boundary Q hQ 1 2 (by decide)
    (show (0 : ℝ) ∈ cell Q 1 from ⟨hXzero, hQ0⟩)
    (show g ∈ cell Q 2 from ⟨haX 1, hQg⟩)
  obtain ⟨β₃, hβ₃lo, hβ₃hi, hβ₃2, hβ₃3⟩ := adjacent_boundary Q hQ 2 3 (by decide)
    (show s ∈ cell Q 2 from ⟨hXs, hQs⟩)
    (show t ∈ cell Q 3 from ⟨haX 2, hQt⟩)
  have hc := closed_interval Q hQ
  have hm0 : (-1 : ℝ) ∈ closure (cell Q 0) := by simpa [hQm] using mem _ hXm
  have hh0 : (-1 / 2 : ℝ) ∈ closure (cell Q 0) := by simpa [hQhalf] using mem _ hXmhalf
  have hz1 : (0 : ℝ) ∈ closure (cell Q 1) := by simpa [hQ0] using mem _ hXzero
  have ha1 : -t ^ 2 ∈ closure (cell Q 1) := by simpa [a, hQamin] using mem _ (haX 0)
  have hs2 : s ∈ closure (cell Q 2) := by simpa only [show Q s = 2 from hQs] using mem s hXs
  have hg2 : g ∈ closure (cell Q 2) := by simpa [a, hQg] using mem _ (haX 1)
  have ht3 : t ∈ closure (cell Q 3) := by simpa [a, hQt] using mem _ (haX 2)
  have h2t4 : 2 * t ∈ closure (cell Q 4) := by simpa [a, hQ2t] using mem _ (haX 3)
  have hp5 : 1 + t ∈ closure (cell Q 5) := by simpa [hQphi] using mem _ hXp
  have hβlegal (β : ℝ) (hlo : -1 / 2 ≤ β) (hhi : β ≤ t) (i : Fin 5) :
      β ∈ stateInterval (outgoing (labelIndex i)) := by
    fin_cases i <;> simp [labelIndex, stateInterval, outgoing, threeLabel, nullLabel,
      fiveLabel, twoLabel, twoFiveLabel] <;> constructor <;> linarith only [hlo, hhi, htlo]
  have hb1legal (i : Fin 5) := hβlegal β₁ hβ₁lo (by nlinarith only [hβ₁hi, hs, htlo]) i
  have hb2legal (i : Fin 5) := hβlegal β₂ (by linarith) (by linarith [hg]) i
  have hb3legal (i : Fin 5) := hβlegal β₃ (by dsimp [s] at hβ₃lo; linarith) hβ₃hi i
  have force (j : Fin 6) (assigned : Fin 6 → Label)
      (occupied : ∀ i : Fin 6, ∃ y, y ∈ stateInterval (outgoing (assigned i)) ∧
        y ∈ closure (cell Q j) ∧ branch (assigned i) y ∈ closure (cell Q i))
      (label : Label) (y : ℝ) (hy : y ∈ stateInterval (outgoing label))
      (hyj : y ∈ closure (cell Q j)) (k : Fin 6)
      (unique : ∀ i, assigned i = label → i = k) :
      branch label y ∈ closure (cell Q k) := by
    have hx := branch_support label hy
    obtain ⟨z, hz, hzj, hzi⟩ := occupied (Q (branch label y))
    have he := hp (Q (branch label y)) j _ label z y hz hy hzj hyj hzi (mem _ hx)
    simpa [unique _ he] using mem _ hx
  let labels0 : Fin 6 → Label := fun i =>
    if i.val ≤ 1 then threeLabel else if i.val = 2 then nullLabel else
      if i.val = 3 then fiveLabel else if i.val = 4 then twoLabel else twoFiveLabel
  have occupied0 : ∀ i : Fin 6, ∃ y, y ∈ stateInterval (outgoing (labels0 i)) ∧
      y ∈ closure (cell Q 0) ∧ branch (labels0 i) y ∈ closure (cell Q i) := by
    intro i
    fin_cases i
    · exact ⟨-1 / 2, by change (-1 / 2 : ℝ) ∈ stateInterval false; exact hXmhalf,
        hh0, by simpa [labels0, hfix3] using hh0⟩
    · exact ⟨-1, hmlegal 0, hm0, by change branch (labelIndex 0) (-1) ∈ _; rw [haeval 0]; exact ha1⟩
    · exact ⟨-1, hmlegal 1, hm0, by change branch (labelIndex 1) (-1) ∈ _; rw [haeval 1]; exact hg2⟩
    · exact ⟨-1, hmlegal 2, hm0, by change branch (labelIndex 2) (-1) ∈ _; rw [haeval 2]; exact ht3⟩
    · exact ⟨-1, hmlegal 3, hm0, by change branch (labelIndex 3) (-1) ∈ _; rw [haeval 3]; exact h2t4⟩
    · exact ⟨-1, hmlegal 4, hm0, by change branch (labelIndex 4) (-1) ∈ _; rw [haeval 4]; exact hp5⟩
  have next0 (n : Fin 4) : branch (labelIndex ⟨n.val + 1, by omega⟩) β₁ ∈
      closure (cell Q ⟨n.val + 2, by omega⟩) := by
    apply force 0 labels0 occupied0 _ β₁ (hb1legal _) hβ₁0
    intro i he
    have he' := congrArg (fun w : Label => (w.val 0, w.val 1, w.val 2)) he
    fin_cases n <;> fin_cases i <;>
      simp [labels0, labelIndex, threeLabel, nullLabel, fiveLabel, twoLabel, twoFiveLabel] at he'
    all_goals rfl
  have hb1three : branch threeLabel β₁ ∈ closure (cell Q 0) := by
    apply (hc 0).out hm0 hh0
    constructor
    · have hlegal := branch_support threeLabel (hb1legal 0)
      exact hlegal.1
    · simp [branch, offset, threeLabel]
      nlinarith only [hβ₁lo, hg, htlo]
  let labels1 : Fin 6 → Label := fun i =>
    if i.val = 0 then threeLabel else if i.val ≤ 2 then nullLabel else
      if i.val = 3 then fiveLabel else if i.val = 4 then twoLabel else twoFiveLabel
  have occupied1 : ∀ i : Fin 6, ∃ y, y ∈ stateInterval (outgoing (labels1 i)) ∧
      y ∈ closure (cell Q 1) ∧ branch (labels1 i) y ∈ closure (cell Q i) := by
    intro i
    fin_cases i
    · exact ⟨β₁, hb1legal 0, hβ₁1, hb1three⟩
    · exact ⟨0, by simpa [labels1, stateInterval, outgoing, nullLabel] using hXzero,
        hz1, by simpa [labels1, hfix0] using hz1⟩
    · exact ⟨β₁, hb1legal 1, hβ₁1, next0 0⟩
    · exact ⟨β₁, hb1legal 2, hβ₁1, next0 1⟩
    · exact ⟨β₁, hb1legal 3, hβ₁1, next0 2⟩
    · exact ⟨β₁, hb1legal 4, hβ₁1, next0 3⟩
  have next1 (n : Fin 3) : branch (labelIndex ⟨n.val + 2, by omega⟩) β₂ ∈
      closure (cell Q ⟨n.val + 3, by omega⟩) := by
    apply force 1 labels1 occupied1 _ β₂ (hb2legal _) hβ₂1
    intro i he
    have he' := congrArg (fun w : Label => (w.val 0, w.val 1, w.val 2)) he
    fin_cases n <;> fin_cases i <;>
      simp [labels1, labelIndex, threeLabel, nullLabel, fiveLabel, twoLabel, twoFiveLabel] at he'
    all_goals rfl
  have hb2three : branch threeLabel β₂ ∈ closure (cell Q 0) := by
    apply (hc 0).out hm0 hh0
    constructor
    · exact (branch_support threeLabel (hb2legal 0)).1
    · simp [branch, offset, threeLabel]
      nlinarith only [hβ₂lo, hg, htlo]
  have hb2null : branch nullLabel β₂ ∈ closure (cell Q 1) := by
    apply (hc 1).out ha1 hz1
    simp [branch, offset, nullLabel]
    constructor
    · have hm := mul_le_mul_of_nonneg_left hβ₂hi (by linarith [hg] : 0 ≤ g)
      nlinarith only [hm, hs, hg, htlo, hthi]
    · nlinarith only [hβ₂lo, hg, htlo]
  let labels2 : Fin 6 → Label := fun i =>
    if i.val = 0 then threeLabel else if i.val = 1 then nullLabel else
      if i.val ≤ 3 then fiveLabel else if i.val = 4 then twoLabel else twoFiveLabel
  have occupied2 : ∀ i : Fin 6, ∃ y, y ∈ stateInterval (outgoing (labels2 i)) ∧
      y ∈ closure (cell Q 2) ∧ branch (labels2 i) y ∈ closure (cell Q i) := by
    intro i
    fin_cases i
    · exact ⟨β₂, hb2legal 0, hβ₂2, hb2three⟩
    · exact ⟨β₂, hb2legal 1, hβ₂2, hb2null⟩
    · exact ⟨s, hQslegal, hs2, by simpa [labels2, hfix5] using hs2⟩
    · exact ⟨β₂, hb2legal 2, hβ₂2, next1 0⟩
    · exact ⟨β₂, hb2legal 3, hβ₂2, next1 1⟩
    · exact ⟨β₂, hb2legal 4, hβ₂2, next1 2⟩
  have hb3two : branch twoLabel β₃ ∈ closure (cell Q 4) := by
    apply force 2 labels2 occupied2 _ β₃ (hb3legal 3) hβ₃2
    intro i he
    have he' := congrArg (fun w : Label => (w.val 0, w.val 1, w.val 2)) he
    fin_cases i <;>
      simp [labels2, labelIndex, threeLabel, nullLabel, fiveLabel, twoLabel, twoFiveLabel] at he'
    all_goals rfl
  have hbad := hp 4 3 twoLabel twoFiveLabel β₃ t (hb3legal 3) (htlegal 4)
    hβ₃3 ht3 hb3two (by rw [hbeval4]; exact h2t4)
  have hbad' := congrArg (fun w : Label => w.val 2) hbad
  change false = true at hbad'
  cases hbad'

/-- No instrument with one through six nonempty connected cells can decode every
actual legal address with a positive uniform open error margin. -/
theorem result (q : ℕ) (hq : 1 ≤ q ∧ q ≤ 6) (Q : ℝ → Fin q)
    (hQ : connectedInstrument Q) (d : Fin q × Fin q → Label)
    (η : ℝ) (hη : 0 < η) :
    ∃ x : LegalDigits, ∃ e₀ e₁ : ℝ, |e₀| < η ∧ |e₁| < η ∧
      d (Q (Set.projIcc (-1) (1 + t) (by linarith [parameters.1]) (kappa x + e₀)),
         Q (Set.projIcc (-1) (1 + t) (by linarith [parameters.1])
           (kappa (originalT x) + e₁))) ≠ window x 0 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨e, he⟩ := ordered_relabel Q hQ
  let P : ℝ → Fin 6 := fun x => Fin.castLE hq.2 (e (Q x))
  let d₆ : Fin 6 × Fin 6 → Label := fun ij =>
    if h : ij.1.val < q ∧ ij.2.val < q then
      d (e.symm ⟨ij.1.val, h.1⟩, e.symm ⟨ij.2.val, h.2⟩) else nullLabel
  have hdecode (u v : ℝ) : d₆ (P u, P v) = d (Q u, Q v) := by
    simp [d₆, P]
  have hP : MonotoneOn P (stateInterval false) := by
    intro u hu v hv huv
    exact he hu hv huv
  have hcorrect : ∀ x : LegalDigits, ∀ e₀ e₁ : ℝ, |e₀| < η → |e₁| < η →
      d₆ (P (Set.projIcc (-1) (1 + t) (by linarith [parameters.1]) (kappa x + e₀)),
          P (Set.projIcc (-1) (1 + t) (by linarith [parameters.1])
            (kappa (originalT x) + e₁))) = window x 0 := by
    intro x e₀ e₁ h₀ h₁
    rw [hdecode]
    exact hn x e₀ e₁ h₀ h₁
  exact no_pure_ordered P hP (purity_of_correct P d₆ hη hcorrect)

end D5.S1.Digit.Infinite.SixCellPositiveMarginObstruction
