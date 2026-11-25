/- GID: D5/S1/Dynamics/Shadowing/QuasiFiniteType
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/QuasiFiniteType
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact-length quasi-finite type is equivalent to uniform two-tail shadowing. -/

import D5.S1.Dynamics.Shadowing.LanguageCharacterization

/-! A two-sided characterization for Question 5.4 of Meddaugh and Stephens,
*Shadowing with small diameter sets of bounded cardinality*, arXiv:2509.04312v1. -/

open Set SymbolicDynamics.FullShift
open D5.S1.Dynamics.Shadowing.LanguageCharacterization

namespace D5.S1.Dynamics.Shadowing

variable {A : Type*} [TopologicalSpace A]

/-- A point realizes the given word at its prescribed coordinates. -/
def MatchesWord {a b : ℤ} (x : ℤ → A) (w : IntervalWord A a b) : Prop :=
  ∀ i : Set.Icc a b, x i.1 = w i

private def IsQuasiFiniteTypeThreshold (X : Subshift A ℤ) (M : ℕ) : Prop :=
  ∀ n : ℕ, M ≤ n → ∀ (a : ℤ) (p q : ℕ),
    ∀ (u : IntervalWord A (a - p) (a - 1))
      (w : IntervalWord A a (a + n - 1))
      (v : IntervalWord A (a + n) (a + n + q - 1)),
    (∃ x : X.carrier, MatchesWord x.1 u ∧ MatchesWord x.1 w) →
    (∃ y : X.carrier, MatchesWord y.1 w ∧ MatchesWord y.1 v) →
    ∃ w' : IntervalWord A a (a + n - 1), ∃ z : X.carrier,
      MatchesWord z.1 u ∧ MatchesWord z.1 w' ∧ MatchesWord z.1 v

/-- Definition 3.5 with words indexed by their intended positions. The joint occurrences
of `u,w` and `w,v` witness legality in the interval language. The bridge and replacement
both occupy the `n` consecutive positions starting at `a`. The context lengths are
unrestricted. -/
def QuasiFiniteType (X : Subshift A ℤ) : Prop :=
  ∃ M : ℕ, IsQuasiFiniteTypeThreshold X M

/-- A uniformly bounded central interval suffices to join points that agree on a
fixed centered window. The same joined point agrees on both full coordinate tails. -/
def HasExactTailSplicing (X : Subshift A ℤ) : Prop :=
  ∃ r L : ℕ, 0 < L ∧ ∀ x y : X.carrier,
    Set.EqOn x.1 y.1 (Set.Icc (-(r : ℤ)) r) →
    ∃ z : X.carrier,
      (∀ i : ℤ, i ≤ -(L : ℤ) → z.1 i = x.1 i) ∧
      (∀ i : ℤ, (L : ℤ) ≤ i → z.1 i = y.1 i)

/-- The orbit at integer time, using the inverse shift for negative times. -/
def shiftAt (X : Subshift A ℤ) (i : ℤ) (x : X.carrier) : X.carrier :=
  ⟨shift i x.1, X.mapsTo i x.2⟩

private theorem splice_outside_bridge [DiscreteTopology A] [Finite A]
    {X : Subshift A ℤ} {M : ℕ}
    (hQFT : IsQuasiFiniteTypeThreshold X M)
    {n : ℕ} (hn : M ≤ n) {a : ℤ} {x y : X.carrier}
    (hxy : Set.EqOn x.1 y.1 (Set.Icc a (a + n - 1))) :
    ∃ z : X.carrier, (∀ i : ℤ, i < a → z.1 i = x.1 i) ∧
      (∀ i : ℤ, a + n ≤ i → z.1 i = y.1 i) := by
  let candidates (j : ℕ) : Set X.carrier := {z |
    (∀ i : ℤ, a - j ≤ i → i < a → z.1 i = x.1 i) ∧
    (∀ i : ℤ, a + n ≤ i → i < a + n + j → z.1 i = y.1 i)}
  have hNonempty (j : ℕ) : (candidates j).Nonempty := by
    let u : IntervalWord A (a - j) (a - 1) := fun i => x.1 i.1
    let w : IntervalWord A a (a + n - 1) := fun i => x.1 i.1
    let v : IntervalWord A (a + n) (a + n + j - 1) := fun i => y.1 i.1
    obtain ⟨_, z, hzu, _, hzv⟩ := hQFT n hn a j j u w v
      ⟨x, fun _ => rfl, fun _ => rfl⟩
      ⟨y, fun i => (hxy i.2).symm, fun _ => rfl⟩
    exact ⟨z, fun i hlo hhi => hzu ⟨i, hlo, by omega⟩,
      fun i hlo hhi => hzv ⟨i, hlo, by omega⟩⟩
  have hClosedCoord (i : ℤ) (value : A) :
      IsClosed {z : X.carrier | z.1 i = value} := by
    have hEval : Continuous (fun z : X.carrier => z.1 i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact (isClosed_discrete ({value} : Set A)).preimage hEval
  have hClosed (j : ℕ) : IsClosed (candidates j) := by
    simp only [candidates, Set.ofPred_and, Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => hClosedCoord i (x.1 i)).inter
      (isClosed_iInter fun i => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => hClosedCoord i (y.1 i))
  let : CompactSpace X.carrier := isCompact_iff_compactSpace.mp X.isClosed.isCompact
  have hNested (j : ℕ) : candidates (j + 1) ⊆ candidates j := by
    intro z hz
    exact ⟨fun i hlo hhi => hz.1 i (by omega) hhi,
      fun i hlo hhi => hz.2 i hlo (by omega)⟩
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    candidates hNested hNonempty (hClosed 0).isCompact hClosed
  have hAll := Set.mem_iInter.mp hz
  exact ⟨z, fun i hi => (hAll (a - i).toNat).1 i (by omega) hi,
    fun i hi => (hAll ((i - (a + n)).toNat + 1)).2 i hi (by omega)⟩

/-- Exact-length quasi-finite type is equivalent to uniform exact splicing of both tails
for points in a common centered cylinder. -/
theorem quasiFiniteType_iff_exactTailSplicing [DiscreteTopology A] [Finite A]
    (X : Subshift A ℤ) : QuasiFiniteType X ↔ HasExactTailSplicing X := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M, M + 1, Nat.succ_pos _, fun x y hxy => ?_⟩
    obtain ⟨z, hleft, hright⟩ :=
      splice_outside_bridge hM (n := 2 * M + 1) (by omega) (a := -(M : ℤ))
        (x := x) (y := y) (fun i hi => hxy ⟨hi.1, by have := hi.2; omega⟩)
    exact ⟨z, fun i hi => hleft i (by omega), fun i hi => hright i (by omega)⟩
  · rintro ⟨r, L, _, hsplice⟩
    let R := max r L
    refine ⟨2 * R + 1, fun n hn a p q u w v hleft hright => ?_⟩
    obtain ⟨x, hxu, hxw⟩ := hleft
    obtain ⟨y, hyw, hyv⟩ := hright
    let c : ℤ := a + R
    have hrR : r ≤ R := le_max_left _ _
    have hLR : L ≤ R := le_max_right _ _
    have hcenter : Set.EqOn (shiftAt X c x).1 (shiftAt X c y).1
        (Set.Icc (-(r : ℤ)) r) := by
      intro i hi
      let j : Set.Icc a (a + n - 1) := ⟨c + i, by
        have ⟨hlo, hhi⟩ := hi
        dsimp [c]
        constructor <;> omega⟩
      exact (hxw j).trans (hyw j).symm
    obtain ⟨z, hzleft, hzright⟩ := hsplice _ _ hcenter
    let z' := shiftAt X (-c) z
    have hcoord (i : ℤ) : z'.1 i = z.1 (i - c) := by
      change z.1 (-c + i) = z.1 (i - c)
      rw [show -c + i = i - c by omega]
    refine ⟨fun i => z'.1 i.1, z', ?_, fun _ => rfl, ?_⟩
    · intro i
      rw [hcoord]
      have hi := i.2.2
      have hz := hzleft (i.1 - c) (by dsimp [c]; omega)
      change z.1 (i.1 - c) = x.1 (c + (i.1 - c)) at hz
      rw [show c + (i.1 - c) = i.1 by omega] at hz
      exact hz.trans (hxu i)
    · intro i
      rw [hcoord]
      have hi := i.2.1
      have hz := hzright (i.1 - c) (by dsimp [c]; omega)
      change z.1 (i.1 - c) = y.1 (c + (i.1 - c)) at hz
      rw [show c + (i.1 - c) = i.1 by omega] at hz
      exact hz.trans (hyv i)

#print axioms quasiFiniteType_iff_exactTailSplicing

/-- One tracer follows the negative orbit of `x` and the positive orbit of `y`.
For each accuracy the tolerance and cutoff are chosen uniformly, and all three
orbits use the same integer time. The possible jump is between times `-1` and `0`. -/
def HasTwoTailShadowing (X : Subshift A ℤ) [MetricSpace X.carrier] : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℕ, 0 < L ∧
    ∀ x y : X.carrier, dist x y < δ →
      ∃ z : X.carrier,
        (∀ i : ℤ, i ≤ -(L : ℤ) → dist (shiftAt X i z) (shiftAt X i x) < ε) ∧
        (∀ i : ℤ, (L : ℤ) ≤ i → dist (shiftAt X i z) (shiftAt X i y) < ε)

/-- Meddaugh–Stephens quasi-finite type is equivalent to uniform same-time
two-tail shadowing of a single jump in every compatible metric. -/
theorem quasiFiniteType_iff_twoTailShadowing [DiscreteTopology A] [Finite A]
    (X : Subshift A ℤ) (d : MetricSpace X.carrier)
    (hd : d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace X.carrier)) :
    let := d
    QuasiFiniteType X ↔ HasTwoTailShadowing X := by
  have controls := metric_window_controls X d hd
  let := d
  rw [quasiFiniteType_iff_exactTailSplicing X]
  obtain ⟨hSmall, hLarge⟩ := controls
  constructor
  · rintro ⟨r, L, hL, hsplice⟩ ε hε
    obtain ⟨k, hk⟩ := hLarge ε hε
    obtain ⟨δ, hδ, hr⟩ := hSmall r
    refine ⟨δ, hδ, L + k, by omega, fun x y hxy => ?_⟩
    obtain ⟨z, hleft, hright⟩ := hsplice x y (by
      intro j hj
      exact hr x y hxy j hj)
    refine ⟨z, ?_, ?_⟩
    · intro i hi
      apply hk
      intro j hj
      have hjUpper := hj.2
      exact hleft (i + j) (by omega)
    · intro i hi
      apply hk
      intro j hj
      have hjLower := hj.1
      exact hright (i + j) (by omega)
  · intro hTrace
    obtain ⟨ε, hε, hε₀⟩ := hSmall 0
    obtain ⟨δ, hδ, L, hL, hJoin⟩ := hTrace ε hε
    obtain ⟨r, hr⟩ := hLarge δ hδ
    have hZero : (0 : ℤ) ∈ Set.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) := by simp
    refine ⟨r, L, hL, fun x y hxy => ?_⟩
    obtain ⟨z, hleft, hright⟩ := hJoin x y (hr x y (fun _ hj => hxy hj))
    refine ⟨z, ?_, ?_⟩
    · intro i hi
      simpa only [shiftAt, shift_apply, add_zero] using hε₀ _ _ (hleft i hi) 0 hZero
    · intro i hi
      simpa only [shiftAt, shift_apply, add_zero] using hε₀ _ _ (hright i hi) 0 hZero

#print axioms quasiFiniteType_iff_twoTailShadowing

end D5.S1.Dynamics.Shadowing
