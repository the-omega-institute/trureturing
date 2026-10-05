/- GID: D5/S1/Words/RankOneMorphismIterationBoundAutomaton
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundAutomaton
   mirror-E: none(waiver:consumed-source-subset-automaton)
   anchors: []
   digest: The actual indexed-image roots and 2^N finite subset checker. -/
import D5.S1.Words.RankOneMorphismIterationBoundPresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound
namespace Parameters
variable {f : Morphism} (p : Parameters f)

open D5.S0.Automata.DFAOStateLowerBound

/-- Moore presentation on actual indexed image positions. -/
def heightMachine : DFAO (Fin p.lam) ℤ (State f) where
  step := p.transition
  start := ⟨0, ⟨0, by rw [p.image_length]; simp only [mult, ite_true]; exact Nat.mul_pos p.n_pos p.d_pos⟩⟩
  accept := ∅
  output := p.coding

/-- Actual source root for the residue e modulo gcd(first image lengths). -/
def root (e : Fin p.d) : Finset (State f) :=
  (Finset.univ : Finset (Fin p.n)).image (fun j =>
    ⟨0, ⟨e.val + j.val * p.d, by
      rw [p.image_length]; simp only [mult, ite_true]
      have he := e.isLt
      have hj := j.isLt
      nlinarith⟩⟩) ∪
  (Finset.univ : Finset (Fin p.m)).image (fun j =>
    ⟨1, ⟨e.val + j.val * p.d, by
      rw [p.image_length]; norm_num [mult]
      have he := e.isLt
      have hj := j.isLt
      nlinarith⟩⟩)

theorem root_nonempty (e : Fin p.d) : (p.root e).Nonempty := by
  refine ⟨⟨0, ⟨e.val, by rw [p.image_length]; simp only [mult, ite_true]; have := e.isLt; have := p.n_pos; nlinarith⟩⟩, ?_⟩
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  exact ⟨⟨0, p.n_pos⟩, Finset.mem_univ _, by simp⟩

/-- Acceptance is exact constancy of the actual prefix-height coding. -/
def Monochromatic (S : Finset (State f)) : Prop :=
  S.Nonempty ∧ ∀ q ∈ S, ∀ r ∈ S, p.coding q = p.coding r

instance monochromaticDecidable (S : Finset (State f)) : Decidable (p.Monochromatic S) :=
  inferInstanceAs (Decidable (S.Nonempty ∧ ∀ q ∈ S, ∀ r ∈ S, p.coding q = p.coding r))

/-- All finite subsets of actual source states, with their deterministic image transition. -/
def subsetMachine : DFA (Fin p.lam) (Finset (State f)) where
  step S j := S.image (p.transition · j)
  start := ∅
  accept := {S | p.Monochromatic S}

theorem subset_eval (S : Finset (State f)) (v : List (Fin p.lam)) :
    p.subsetMachine.evalFrom S v = S.image (fun q => p.heightMachine.toDFA.evalFrom q v) := by
  induction v generalizing S with
  | nil => simp
  | cons j v ih =>
    simp only [DFA.evalFrom_cons, subsetMachine, heightMachine] at *
    rw [ih, Finset.image_image]
    rfl

theorem subset_card : Fintype.card (Finset (State f)) = iterationBound f := by
  rw [Fintype.card_finset, state_card]
  rfl

/-- Exact source-root reachability; digit length specifies the actual iteration. -/
def RootAccepts (e : Fin p.d) (v : List (Fin p.lam)) : Prop :=
  p.Monochromatic (p.subsetMachine.evalFrom (p.root e) v)

instance rootAcceptsDecidable (e : Fin p.d) (v : List (Fin p.lam)) :
    Decidable (p.RootAccepts e v) := inferInstanceAs (Decidable (p.Monochromatic _))

private theorem shorter_accepting_word {α σ : Type*} [Fintype σ]
    (M : DFA α σ) (s : σ) (v : List α) (hv : M.evalFrom s v ∈ M.accept) :
    ∃ w : List α, w.length < Fintype.card σ ∧ M.evalFrom s w ∈ M.accept := by
  classical
  have hex : ∃ n, ∃ w : List α, w.length = n ∧ M.evalFrom s w ∈ M.accept :=
    ⟨v.length, v, rfl, hv⟩
  obtain ⟨w, hw, ha⟩ := Nat.find_spec hex
  refine ⟨w, ?_, ha⟩
  by_contra h
  have hlen : Fintype.card σ ≤ w.length := by omega
  obtain ⟨q, a, b, c, heq, hab, hb, hqa, hqb, hqc⟩ := M.evalFrom_split hlen rfl
  have hac : M.evalFrom s (a ++ c) ∈ M.accept := by
    rw [M.evalFrom_of_append, hqa, hqc]
    exact ha
  have hmin := Nat.find_min' hex ⟨a ++ c, rfl, hac⟩
  have hbpos : 0 < b.length := List.length_pos_iff.mpr hb
  have hlenw : w.length = a.length + b.length + c.length := by simp [heq, Nat.add_assoc]
  simp only [List.length_append] at hmin
  omega

/-- The explicit source-specific subset-state cutoff, prior to the finite semantic bridge. -/
theorem root_cutoff :
    (∃ e : Fin p.d, ∃ v : List (Fin p.lam), p.RootAccepts e v) ↔
    ∃ e : Fin p.d, ∃ v : List (Fin p.lam), v.length < iterationBound f ∧ p.RootAccepts e v := by
  constructor
  · rintro ⟨e, v, hv⟩
    obtain ⟨w, hw, ha⟩ := shorter_accepting_word p.subsetMachine (p.root e) v hv
    exact ⟨e, w, (by simpa only [subset_card] using hw), ha⟩
  · rintro ⟨e, v, hv, ha⟩; exact ⟨e, v, ha⟩

/-- All retained digits, including leading zeros, of one specified length. -/
def digitWords : ℕ → List (List (Fin p.lam))
  | 0 => [[]]
  | t+1 => (List.finRange p.lam).flatMap (fun j => (digitWords t).map (j :: ·))

theorem mem_digitWords (t : ℕ) (v : List (Fin p.lam)) :
    v ∈ p.digitWords t ↔ v.length = t := by
  induction t generalizing v with
  | zero => simp [digitWords]
  | succ t ih =>
    cases v with
    | nil => simp [digitWords]
    | cons j v => simp [digitWords, ih]

/-- A total finite search on the actual source roots and subset transition. -/
def subsetChecker : Bool :=
  (List.range (iterationBound f)).any (fun t =>
    (List.finRange p.d).any (fun e =>
      (p.digitWords t).any (fun v => decide (p.RootAccepts e v))))

theorem subsetChecker_correct :
    p.subsetChecker = true ↔ ∃ e : Fin p.d, ∃ v : List (Fin p.lam), p.RootAccepts e v := by
  rw [p.root_cutoff]
  simp only [subsetChecker, List.any_eq_true, List.mem_range, List.mem_finRange,
    true_and, decide_eq_true_eq, mem_digitWords]
  constructor
  · rintro ⟨t, ht, e, v, hv, ha⟩
    exact ⟨e, v, hv ▸ ht, ha⟩
  · rintro ⟨e, v, hv, ha⟩
    exact ⟨v.length, hv, e, v, rfl, ha⟩

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
