/- GID: D5/S1/Digit/Infinite/PendingObligationLift
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/PendingObligationLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transported endpoint exclusions characterize exact finite observation histories. -/

import D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth
import D5.S1.Digit.Infinite.LateLabelStateBound

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.PendingObligationLift

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidth

/-- Insert the current exclusions, transport all outstanding equalities, and
discard equalities outside the next guard interval. -/
noncomputable def pending (F : ℕ → ℝ → ℝ) (P I Z : ℕ → Set ℝ) : ℕ → Set ℝ
  | 0 => ∅
  | n + 1 => (F n '' (pending F P I Z n ∪ (Z n ∩ P n))) ∩ I (n + 1)

private theorem history_avoidance (F : ℕ → ℝ → ℝ) (P I Z : ℕ → Set ℝ)
    (x : ℕ → ℝ) (n : ℕ)
    (hF : ∀ j < n, Function.Injective (F j))
    (hP : ∀ j < n, x j ∈ P j) (hI : ∀ j ≤ n, x j ∈ I j)
    (hstep : ∀ j < n, x (j + 1) = F j (x j)) :
    x n ∉ pending F P I Z n ↔ ∀ j < n, x j ∉ Z j := by
  induction n with
  | zero => simp [pending]
  | succ n ih =>
    have hpast := ih (fun j hj => hF j (by omega))
      (fun j hj => hP j (by omega)) (fun j hj => hI j (by omega))
      (fun j hj => hstep j (by omega))
    have hmem : x (n + 1) ∈ pending F P I Z (n + 1) ↔
        x n ∈ pending F P I Z n ∨ x n ∈ Z n := by
      rw [pending, Set.mem_inter_iff, and_iff_left (hI (n + 1) le_rfl)]
      rw [hstep n (by omega), (hF n (by omega)).mem_set_image]
      simp only [Set.mem_union, Set.mem_inter_iff, hP n (by omega), and_true]
    rw [hmem, not_or, hpast]
    constructor
    · rintro ⟨hp, hn⟩ j hj
      by_cases hjn : j < n
      · exact hp j hjn
      · have : j = n := by omega
        simpa [this] using hn
    · intro h
      exact ⟨fun j hj => h j (by omega), h n (by omega)⟩

private theorem exact_targets (Q : ℝ → Fin 6) (b : ℝ) (hb : 0 ≤ b)
    (x : LegalDigits) (r : ℕ → Fin 6) (P I : ℕ → Set ℝ) (n : ℕ)
    (hP : ∀ j < n, kappa (bitShift x (3 * j)) ∈ P j)
    (hI : ∀ j ≤ n, kappa (bitShift x (3 * j)) ∈ I j)
    (hE : ∀ j < n, kappa (bitShift x (3 * j)) ∈ observation b (r j)) :
    kappa (bitShift x (3 * n)) ∉ pending
      (fun j => inverseBranch (window x j)) P I
      (fun j => observation b (r j) \ exactObservation Q b (r j)) n ↔
    ∃ target : ℕ → ℝ,
      (∀ j, target j ∈ stateInterval false ∧
        |kappa (bitShift x (3 * j)) - target j| ≤ b) ∧
      (∀ j < n, Q (target j) = r j) ∧
      (∀ j, n ≤ j → target j = kappa (bitShift x (3 * j))) := by
  classical
  have hg : g ≠ 0 := (pow_pos (inv_pos.mpr Real.goldenRatio_pos) 3).ne'
  have hF (j : ℕ) : Function.Injective (inverseBranch (window x j)) := by
    intro a a' he
    exact sub_right_injective ((div_left_inj' hg).mp he)
  have hstep (j : ℕ) : kappa (bitShift x (3 * (j + 1))) =
      inverseBranch (window x j) (kappa (bitShift x (3 * j))) := by
    have he := (closed_observation_graph_realization.2.2.1 (bitShift x (3 * j))).1
    rw [window_shift x j, original_t_shift x j] at he
    apply (eq_div_iff hg).mpr
    dsimp [branch] at he
    linarith
  have hhistory := history_avoidance (fun j => inverseBranch (window x j)) P I
    (fun j => observation b (r j) \ exactObservation Q b (r j))
    (fun j => kappa (bitShift x (3 * j))) n
    (fun j _ => hF j) hP hI (fun j _ => hstep j)
  have hsupport (j : ℕ) : kappa (bitShift x (3 * j)) ∈ stateInterval false :=
    (closed_observation_graph_realization.2.1 false) ▸
      ⟨bitShift x (3 * j), by simp [stateAddress], rfl⟩
  rw [hhistory]
  constructor
  · intro h
    have hactual (j : ℕ) (hj : j < n) :
        kappa (bitShift x (3 * j)) ∈ exactObservation Q b (r j) := by
      by_contra hn
      exact h j hj ⟨hE j hj, hn⟩
    have hex (j : ℕ) : ∃ y : ℝ, y ∈ stateInterval false ∧
        |kappa (bitShift x (3 * j)) - y| ≤ b ∧
        (j < n → Q y = r j) ∧ (n ≤ j → y = kappa (bitShift x (3 * j))) := by
      by_cases hj : j < n
      · obtain ⟨y, hy, hQ, he⟩ := (hactual j hj).2
        exact ⟨y, hy, he, fun _ => hQ, fun hn => False.elim (by omega)⟩
      · exact ⟨kappa (bitShift x (3 * j)), hsupport j, by simpa using hb,
          fun hn => False.elim (hj hn), fun _ => rfl⟩
    choose target ht using hex
    exact ⟨target, fun j => ⟨(ht j).1, (ht j).2.1⟩,
      fun j hj => (ht j).2.2.1 hj, fun j hj => (ht j).2.2.2 hj⟩
  · rintro ⟨target, ht, hr, _⟩ j hj ⟨_, hn⟩
    exact hn ⟨hsupport j, target j, (ht j).1, hr j hj, (ht j).2⟩

private theorem chain_pieces {q : ℕ} {R b : ℝ} {r : List (Fin 6)}
    {vs : List (Vertex q R)} {w : List Label} (hp : ClosedPath b r vs w) :
    vs.length = w.length + 1 ∧
    ∀ (x : LegalDigits), addressChain x vs w → ∀ (fallback : Vertex q R)
      (j : ℕ), j ≤ w.length →
      kappa (bitShift x (3 * j)) ∈ piece ((vs[j]?).getD fallback) := by
  induction hp with
  | point i v hi =>
    refine ⟨rfl, ?_⟩
    intro x hx fallback j hj
    have hj0 : j = 0 := by simpa using hj
    subst j
    simpa [bitShift] using hx.2
  | step i r v u vs l w hi he hp ih =>
    refine ⟨by simpa only [List.length_cons] using congrArg Nat.succ ih.1, ?_⟩
    intro x hx fallback j hj
    change stateAddress v.val.1 x ∧ kappa x ∈ piece v ∧ window x 0 = l ∧
      addressChain (originalT x) (u :: vs) w at hx
    cases j with
    | zero => simpa [bitShift] using hx.2.1
    | succ j =>
      have hh := ih.2 (originalT x) hx.2.2.2 fallback j (by simpa using hj)
      have heq : 3 + 3 * j = 3 * (j + 1) := by omega
      simpa only [originalT, bitShift_bitShift, heq, List.getElem?_cons_succ] using hh

/-- All past exclusions are equivalent to avoiding the transported terminal set.
A closed observed path followed by one unobserved source edge therefore has an
exact target record precisely when its chosen terminal address avoids that set. -/
theorem result :
    (∀ (F : ℕ → ℝ → ℝ) (P I Z : ℕ → Set ℝ) (x : ℕ → ℝ) (n : ℕ),
      (∀ j < n, Function.Injective (F j)) →
      (∀ j < n, x j ∈ P j) → (∀ j ≤ n, x j ∈ I j) →
      (∀ j < n, x (j + 1) = F j (x j)) →
      (x n ∉ pending F P I Z n ↔ ∀ j < n, x j ∉ Z j)) ∧
    (∀ (Q : ℝ → Fin 6) (b : ℝ), 0 ≤ b → ∀ (x : LegalDigits)
      (r : ℕ → Fin 6) (P I : ℕ → Set ℝ) (n : ℕ),
      (∀ j < n, kappa (bitShift x (3 * j)) ∈ P j) →
      (∀ j ≤ n, kappa (bitShift x (3 * j)) ∈ I j) →
      (∀ j < n, kappa (bitShift x (3 * j)) ∈ observation b (r j)) →
      (kappa (bitShift x (3 * n)) ∉ pending
        (fun j => inverseBranch (window x j)) P I
        (fun j => observation b (r j) \ exactObservation Q b (r j)) n ↔
      ∃ target : ℕ → ℝ,
        (∀ j, target j ∈ stateInterval false ∧
          |kappa (bitShift x (3 * j)) - target j| ≤ b) ∧
        (∀ j < n, Q (target j) = r j) ∧
        (∀ j, n ≤ j → target j = kappa (bitShift x (3 * j))))) ∧
    (∀ {q : ℕ} {R : ℝ} (b : ℝ), 0 ≤ b → ∀ (Q : ℝ → Fin 6)
      (r : List (Fin 6)) (vs : List (Vertex q R)) (w : List Label),
      ClosedPath b r vs w → ∀ (v : Vertex q R), vs.getLast? = some v →
      ∀ (l : Label) (u : Vertex q R), edge v l u → ∀ (y : LegalDigits),
      stateAddress u.val.1 y → kappa y ∈ piece u →
      ∃ x : LegalDigits, addressChain x vs w ∧
        bitShift x (3 * (w.length + 1)) = y ∧
        window (bitShift x (3 * w.length)) 0 = l ∧
        (finiteTail x ↔ finiteTail y) ∧
        (kappa y ∉ pending (fun j => inverseBranch (window x j))
          (fun j => piece ((vs[j]?).getD u))
          (fun j => stateInterval ((vs[j]?).getD u).val.1)
          (fun j => observation b ((r[j]?).getD 0) \
            exactObservation Q b ((r[j]?).getD 0)) (w.length + 1) ↔
        ∃ target : ℕ → ℝ,
          (∀ j, target j ∈ stateInterval false ∧
            |kappa (bitShift x (3 * j)) - target j| ≤ b) ∧
          (∀ j < w.length + 1, Q (target j) = (r[j]?).getD 0) ∧
          (∀ j, w.length + 1 ≤ j → target j = kappa (bitShift x (3 * j))))) := by
  refine ⟨history_avoidance, exact_targets, ?_⟩
  intro q R b hb Q r vs w hp v hlast l u he y hy hyp
  obtain ⟨z, hz, hprefix⟩ := (closed_observation_graph_realization.2.2.2.1
    v.val.1 l u.val.1 y he.1 hy).exists
  change window z 0 = l ∧ originalT z = y at hprefix
  have hg : g ≠ 0 := (pow_pos (inv_pos.mpr Real.goldenRatio_pos) 3).ne'
  obtain ⟨a, ha, hay⟩ := he.2.2 hyp
  have hzp : kappa z ∈ piece v := by
    have hrec := (closed_observation_graph_realization.2.2.1 z).1
    rw [hprefix.1, hprefix.2] at hrec
    have halg := (div_eq_iff hg).mp hay
    dsimp [branch] at hrec
    have heq : kappa z = a := by linarith
    exact heq ▸ ha
  obtain ⟨x, hx, hxz⟩ := closed_observation_graph_realization.2.2.2.2.2.2.1
    b r vs w hp v hlast z hz hzp
  have hxy : bitShift x (3 * (w.length + 1)) = y := by
    rw [show 3 * (w.length + 1) = 3 * w.length + 3 by omega, ← bitShift_bitShift,
      hxz, ← originalT, hprefix.2]
  have hlen := (chain_pieces hp).1
  have htrace (j : ℕ) (hj : j ≤ w.length + 1) :
      kappa (bitShift x (3 * j)) ∈ piece ((vs[j]?).getD u) := by
    by_cases hjw : j ≤ w.length
    · exact (chain_pieces hp).2 x hx u j hjw
    · have hjn : j = w.length + 1 := by omega
      subst j
      rw [List.getElem?_eq_none (l := vs) (i := w.length + 1) hlen.le]
      simpa only [Option.getD_none, hxy] using hyp
  have hinterval (j : ℕ) (hj : j ≤ w.length + 1) :
      kappa (bitShift x (3 * j)) ∈ stateInterval ((vs[j]?).getD u).val.1 := by
    exact Set.Icc_subset_Icc ((vs[j]?).getD u).property.2.2.1.1
      ((vs[j]?).getD u).property.2.2.2.1.2 (htrace j hj)
  have hread := closed_path_read b r vs w hp
  have hclosed (j : ℕ) (hj : j < w.length + 1) :
      kappa (bitShift x (3 * j)) ∈ observation b ((r[j]?).getD 0) := by
    have hjr : j < r.length := by rw [← hread.1]; exact hj
    simpa only [List.get_eq_getElem, List.getElem?_eq_getElem hjr, Option.getD_some]
      using (hread.2 x hx).2 ⟨j, hjr⟩
  have hfinite : finiteTail x ↔ finiteTail y := by
    constructor
    · intro h
      simpa only [hxy] using D5.S1.Digit.Infinite.LateLabelStateBound.finite_shift x (3 * (w.length + 1)) h
    · intro h
      exact finite_tail_unshift x (3 * (w.length + 1)) (hxy.symm ▸ h)
  refine ⟨x, hx, hxy, by simpa only [hxz] using hprefix.1, hfinite, ?_⟩
  simpa only [hxy] using exact_targets Q b hb x (fun j => (r[j]?).getD 0)
    (fun j => piece ((vs[j]?).getD u))
    (fun j => stateInterval ((vs[j]?).getD u).val.1) (w.length + 1)
    (fun j hj => htrace j (by omega)) hinterval hclosed

end D5.S1.Digit.Infinite.PendingObligationLift
