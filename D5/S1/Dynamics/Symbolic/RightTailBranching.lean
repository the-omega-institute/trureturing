/- GID: D5/S1/Dynamics/Symbolic/RightTailBranching
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/RightTailBranching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite set of branching futures bounds the number of pasts. -/

import D5.S1.Dynamics.Shadowing.IntervalObstruction.Basic
import D5.S1.Dynamics.Shadowing.LanguageCharacterization
import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.NatCard

/-! Counting two-sided extensions of a prescribed future by their last branching choice. -/

open Set SymbolicDynamics.FullShift

namespace D5.S1.Dynamics.Symbolic.RightTailBranching

variable {A : Type*} [TopologicalSpace A]

/-- The forward tail starting at coordinate `-depth`. -/
def tail (x : ℤ → A) (depth : ℕ) : ℕ → A :=
  fun i => x ((i : ℤ) - (depth : ℤ))

/-- The two-sided configurations with prescribed nonnegative coordinates. -/
def extensions (X : Subshift A ℤ) (u : ℕ → A) : Set X.carrier :=
  {x | tail x.1 0 = u}

private def precedingLetters (X : Subshift A ℤ) (u : ℕ → A) : Set A :=
  {a | ∃ x : extensions X u, x.1.1 (-1) = a}

/-- Futures with two distinct immediately preceding letters in the shift. -/
def branchingTails (X : Subshift A ℤ) : Set (ℕ → A) :=
  {u | ∃ a ∈ precedingLetters X u, ∃ b ∈ precedingLetters X u, a ≠ b}

/-- A right tail is periodic from its initial coordinate. -/
def PeriodicTail (u : ℕ → A) : Prop :=
  ∃ p : ℕ, 0 < p ∧ ∀ i : ℕ, u (i + p) = u i

private def prior (x : ℤ → A) (depth : ℕ) : A :=
  x (-(depth : ℤ) - 1)

private theorem prior_mem (X : Subshift A ℤ) (x : X.carrier) (n : ℕ) :
    prior x.1 n ∈ precedingLetters X (tail x.1 n) := by
  let y : X.carrier := ⟨shift (-(n : ℤ)) x.1, X.mapsTo _ x.2⟩
  have hy : y ∈ extensions X (tail x.1 n) := by
    funext i
    change x.1 (-(n : ℤ) + ((i : ℤ) - ((0 : ℕ) : ℤ))) =
      x.1 ((i : ℤ) - (n : ℤ))
    exact congrArg x.1 (by push_cast; omega)
  exact ⟨⟨y, hy⟩, rfl⟩

private noncomputable def defaultLetter [Nonempty A] (X : Subshift A ℤ) (u : ℕ → A) : A := by
  classical
  exact if h : (precedingLetters X u).Nonempty then h.choose else Classical.arbitrary A

private theorem defaultLetter_mem [Nonempty A] (X : Subshift A ℤ) (u : ℕ → A)
    (h : (precedingLetters X u).Nonempty) :
    defaultLetter X u ∈ precedingLetters X u := by
  classical
  simpa [defaultLetter, h] using h.choose_spec

omit [TopologicalSpace A] in
private theorem depth_eq {u : ℕ → A} (hu : ¬ PeriodicTail u) {x y : ℤ → A}
    (hx : tail x 0 = u) (hy : tail y 0 = u) {m n : ℕ}
    (heq : tail x m = tail y n) : m = n := by
  have aux (x y : ℤ → A) (hx : tail x 0 = u) (hy : tail y 0 = u)
      {m n : ℕ} (hmn : m < n) (h : tail x m = tail y n) : False := by
    apply hu
    refine ⟨n - m, by omega, fun i => ?_⟩
    rw [← congrFun hx (i + (n - m)), ← congrFun hy i]
    have he := congrFun h (i + n)
    simp only [tail, Nat.cast_zero] at he ⊢
    simpa only [show ((i + n : ℕ) : ℤ) - (m : ℤ) =
        ((i + (n - m) : ℕ) : ℤ) - (0 : ℤ) by omega,
      show ((i + n : ℕ) : ℤ) - (n : ℤ) = (i : ℤ) - (0 : ℤ) by omega] using he
  rcases lt_trichotomy m n with h | h | h
  · exact (aux x y hx hy h heq).elim
  · exact h
  · exact (aux y x hy hx h heq.symm).elim

omit [TopologicalSpace A] in
private theorem tail_succ_eq {x y : ℤ → A} {n : ℕ}
    (h : tail x n = tail y n) (hl : prior x n = prior y n) :
    tail x (n + 1) = tail y (n + 1) := by
  funext i
  cases i with
  | zero =>
    simpa only [tail, prior, show ((0 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) =
      -(n : ℤ) - 1 by omega] using hl
  | succ i =>
    simpa only [tail, show ((i + 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) =
      (i : ℤ) - (n : ℤ) by omega] using congrFun h i

private def exceptional [Nonempty A] (X : Subshift A ℤ) (x : ℤ → A) : Set ℕ :=
  {n | prior x n ≠ defaultLetter X (tail x n)}

private theorem exceptional_branch [Nonempty A] {X : Subshift A ℤ} (x : X.carrier)
    {n : ℕ} (hn : n ∈ exceptional X x.1) : tail x.1 n ∈ branchingTails X := by
  have h := prior_mem X x n
  exact ⟨prior x.1 n, h, defaultLetter X (tail x.1 n),
    defaultLetter_mem X _ ⟨_, h⟩, hn⟩

private theorem eq_of_following_defaults [Nonempty A] {X : Subshift A ℤ}
    {x y : ℤ → A} {n : ℕ} (h : tail x n = tail y n)
    (hx : ∀ m ≥ n, m ∉ exceptional X x) (hy : ∀ m ≥ n, m ∉ exceptional X y) : x = y := by
  have hAll (k : ℕ) : tail x (n + k) = tail y (n + k) := by
    induction k with
    | zero => simpa using h
    | succ k ih =>
      apply tail_succ_eq ih
      have dx : prior x (n + k) = defaultLetter X (tail x (n + k)) :=
        not_ne_iff.mp (hx _ (by omega))
      have dy : prior y (n + k) = defaultLetter X (tail y (n + k)) :=
        not_ne_iff.mp (hy _ (by omega))
      rw [dx, dy, ih]
  funext j
  let k := j.natAbs
  let i := (j + (n : ℤ) + (k : ℤ)).toNat
  have hIndex : (i : ℤ) - ((n + k : ℕ) : ℤ) = j := by
    dsimp [i, k]
    omega
  simpa only [tail, hIndex] using congrFun (hAll k) i

/-- With finitely many branching tails, a nonperiodic future has at most one extension
plus one for each available nondefault letter at a branching tail. The code of a past
uses its last nondefault choice, whose depth is determined by the future. -/
theorem finite_extensions_of_not_periodic [Fintype A] (X : Subshift A ℤ)
    (hB : (branchingTails X).Finite) {u : ℕ → A} (hu : ¬ PeriodicTail u) :
    (extensions X u).Finite ∧
      Nat.card (extensions X u) ≤
        1 + Nat.card (branchingTails X) * (Fintype.card A - 1) := by
  classical
  let : Nonempty A := ⟨u 0⟩
  let : Fintype (branchingTails X) := hB.fintype
  let Codes := Σ v : branchingTails X, {a : A // a ≠ defaultLetter X v.1}
  let : Fintype Codes := inferInstanceAs
    (Fintype (Σ v : branchingTails X, {a : A // a ≠ defaultLetter X v.1}))
  let fin (x : extensions X u) : Finset ℕ :=
    (Set.Finite.of_injOn
      (fun _ hn => exceptional_branch x.1 hn)
      (fun _ _ _ _ h => depth_eq hu x.2 x.2 h) hB).toFinset
  have hFin (x : extensions X u) (n : ℕ) : n ∈ fin x ↔ n ∈ exceptional X x.1.1 :=
    Set.Finite.mem_toFinset _
  let last (x : extensions X u) (h : (fin x).Nonempty) := (fin x).max' h
  have hLast (x : extensions X u) (h : (fin x).Nonempty) :
      last x h ∈ exceptional X x.1.1 :=
    (hFin _ _).mp (Finset.max'_mem _ _)
  let code (x : extensions X u) : Option Codes :=
    if h : (fin x).Nonempty then
      some ⟨⟨tail x.1.1 (last x h), exceptional_branch x.1 (hLast x h)⟩,
        ⟨prior x.1.1 (last x h), hLast x h⟩⟩
    else none
  have hAfter (x : extensions X u) (h : (fin x).Nonempty) (m : ℕ)
      (hm : last x h < m) : m ∉ exceptional X x.1.1 := by
    intro hx
    exact (not_le_of_gt hm) ((fin x).le_max' m ((hFin _ _).mpr hx))
  have hEmpty (x : extensions X u) (h : ¬ (fin x).Nonempty) (m : ℕ) :
      m ∉ exceptional X x.1.1 := fun hx => h ⟨m, (hFin _ _).mpr hx⟩
  have hinj : Function.Injective code := by
    intro x y heq
    apply Subtype.ext
    apply Subtype.ext
    by_cases hx : (fin x).Nonempty <;> by_cases hy : (fin y).Nonempty
    · simp only [code, dite_eq_left hx, dite_eq_left hy, Option.some.injEq] at heq
      have hTail : tail x.1.1 (last x hx) = tail y.1.1 (last y hy) :=
        congrArg (fun c : Codes => c.1.1) heq
      have hPrior : prior x.1.1 (last x hx) = prior y.1.1 (last y hy) :=
        congrArg (fun c : Codes => c.2.1) heq
      have hd := depth_eq hu x.2 y.2 hTail
      rw [← hd] at hTail hPrior
      refine eq_of_following_defaults (tail_succ_eq hTail hPrior)
        (fun m hm => hAfter x hx m (by omega))
        (fun m hm => hAfter y hy m (by omega))
    · simp [code, hx, hy] at heq
    · simp [code, hx, hy] at heq
    · exact eq_of_following_defaults (x.2.trans y.2.symm)
        (fun m _ => hEmpty x hx m) (fun m _ => hEmpty y hy m)
  have hCard := Nat.card_le_card_of_injective code hinj
  refine ⟨Set.finite_coe_iff.mp (Finite.of_injective code hinj), ?_⟩
  rw [Nat.card_eq_fintype_card (α := Option Codes), Fintype.card_option] at hCard
  have hc : Fintype.card Codes = Fintype.card (branchingTails X) * (Fintype.card A - 1) := by
    change Fintype.card (Σ v : branchingTails X, {a : A // a ≠ defaultLetter X v.1}) = _
    simp [Fintype.card_sigma]
  rw [hc] at hCard
  rw [Nat.card_eq_fintype_card (α := branchingTails X)]
  omega


/-- A two-sided configuration with a positive period. -/
def PeriodicPoint (x : ℤ → A) : Prop :=
  ∃ p : ℕ, 0 < p ∧ Function.Periodic x (p : ℤ)

private theorem periodic_extension_unique {X : Subshift A ℤ} {u : ℕ → A}
    (x y : extensions X u) (hx : PeriodicPoint x.1.1) (hy : PeriodicPoint y.1.1) :
    x = y := by
  obtain ⟨p, hp, hpPeriod⟩ := hx
  obtain ⟨q, hq, hqPeriod⟩ := hy
  apply Subtype.ext
  apply Subtype.ext
  funext j
  let step : ℤ := (p : ℤ) * (q : ℤ)
  have hpStep : Function.Periodic x.1.1 step := by
    simpa [step, mul_comm] using hpPeriod.nat_mul q
  have hqStep : Function.Periodic y.1.1 step := hqPeriod.nat_mul p
  have step_pos : 0 < step := mul_pos (by exact_mod_cast hp) (by exact_mod_cast hq)
  let k := j.natAbs
  have hk : (k : ℤ) ≤ (k : ℤ) * step := by
    simpa using mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ step by omega)
      (Int.natCast_nonneg k)
  have hj : 0 ≤ j + (k : ℤ) * step := by
    dsimp [k] at hk ⊢
    omega
  have hTail := congrFun (x.2.trans y.2.symm) (j + (k : ℤ) * step).toNat
  simp only [tail, Nat.cast_zero, sub_zero, Int.toNat_of_nonneg hj] at hTail
  exact ((hpStep.nat_mul k) j).symm.trans
    (hTail.trans ((hqStep.nat_mul k) j))

private theorem infinite_extensions_of_nonperiodic_extension {X : Subshift A ℤ}
    {u : ℕ → A} (hu : PeriodicTail u) (x : extensions X u) (hx : ¬ PeriodicPoint x.1.1) :
    ¬ (extensions X u).Finite := by
  obtain ⟨p, hp, hPeriod⟩ := hu
  have hMult (k i : ℕ) : u (i + k * p) = u i :=
    (show Function.Periodic u p from hPeriod).nat_mul k i
  let iterate (k : ℕ) : extensions X u :=
    ⟨⟨shift ((k * p : ℕ) : ℤ) x.1.1, X.mapsTo _ x.1.2⟩, by
      funext i
      change x.1.1 (((k * p : ℕ) : ℤ) + ((i : ℤ) - ((0 : ℕ) : ℤ))) = u i
      rw [show (((k * p : ℕ) : ℤ) + ((i : ℤ) - ((0 : ℕ) : ℤ))) =
          ((i + k * p : ℕ) : ℤ) - ((0 : ℕ) : ℤ) by push_cast; omega]
      exact (congrFun x.2 _).trans (hMult k i)⟩
  have no_lt (m n : ℕ) (hmn : m < n) (h : iterate m = iterate n) : False := by
    apply hx
    have hProd : m * p < n * p := Nat.mul_lt_mul_of_pos_right hmn hp
    refine ⟨n * p - m * p, by omega, ?_⟩
    intro i
    have hValue := congrArg (fun z : extensions X u =>
      z.1.1 (i - ((m * p : ℕ) : ℤ))) h
    change x.1.1 (((m * p : ℕ) : ℤ) + (i - ((m * p : ℕ) : ℤ))) =
      x.1.1 (((n * p : ℕ) : ℤ) + (i - ((m * p : ℕ) : ℤ))) at hValue
    simpa only [show (((m * p : ℕ) : ℤ) + (i - ((m * p : ℕ) : ℤ))) = i by omega,
      show (((n * p : ℕ) : ℤ) + (i - ((m * p : ℕ) : ℤ))) =
        i + ((n * p - m * p : ℕ) : ℤ) by omega] using hValue.symm
  have injective : Function.Injective iterate := by
    intro m n h
    rcases lt_trichotomy m n with hlt | heq | hgt
    · exact (no_lt m n hlt h).elim
    · exact heq
    · exact (no_lt n m hgt h.symm).elim
  intro hFin
  have : Finite (extensions X u) := hFin.to_subtype
  exact (not_finite_iff_infinite.mpr (inferInstance : Infinite ℕ))
    (Finite.of_injective iterate injective)

/-- For a shift with finitely many branching futures, finite future fibers are equivalent
to periodic futures having only periodic extensions. In that case all fibers satisfy
the same explicit finite bound. -/
theorem uniform_finite_extensions_iff [Fintype A] (X : Subshift A ℤ)
    (hB : (branchingTails X).Finite) :
    (∀ u, (extensions X u).Finite ∧
      Nat.card (extensions X u) ≤
        1 + Nat.card (branchingTails X) * (Fintype.card A - 1)) ↔
    ∀ u, PeriodicTail u → ∀ x : extensions X u, PeriodicPoint x.1.1 := by
  classical
  constructor
  · intro h u hu x
    by_contra hx
    exact infinite_extensions_of_nonperiodic_extension hu x hx (h u).1
  · intro h u
    by_cases hp : PeriodicTail u
    · have : Subsingleton (extensions X u) :=
        ⟨fun x y => periodic_extension_unique x y (h u hp x) (h u hp y)⟩
      refine ⟨Set.finite_coe_iff.mp inferInstance, ?_⟩
      have : Nat.card (extensions X u) ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr inferInstance
      omega
    · exact finite_extensions_of_not_periodic X hB hp


section Metric

open D5.S1.Dynamics.Shadowing
open D5.S1.Dynamics.Shadowing.LanguageCharacterization

variable [DiscreteTopology A] [Finite A]

private theorem shiftOne_iterate_apply (X : Subshift A ℤ)
    (x : X.carrier) (k : ℕ) (i : ℤ) :
    ((shiftOne X)^[k] x).1 i = x.1 ((k : ℤ) + i) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change ((shiftOne X)^[k] x).1 (1 + i) = _
    rw [ih, show ((k + 1 : ℕ) : ℤ) + i = (k : ℤ) + (1 + i) by omega]

/-- Lemma 4.7 of Gangloff, Guillon and Oprocha for any compatible metric. A uniform
strict forward Bowen bound is equivalent to the same cardinal bound on future fibers. -/
theorem forwardBowenBound_iff_bounded_extensions (X : Subshift A ℤ)
    (d : MetricSpace X.carrier)
    (hd : d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace X.carrier))
    (N : ℕ) :
    let := d
    (∃ ε : ℝ, 0 < ε ∧ ForwardBowenBound (shiftOne X) univ ε N) ↔
      ∀ u, (extensions X u).encard ≤ (N : ℕ∞) := by
  classical
  have controls := metric_window_controls X d hd
  let := d
  constructor
  · rintro ⟨ε, hε, hBound⟩ u
    obtain ⟨k, hClose⟩ := controls.2 ε hε
    by_cases hNonempty : (extensions X u).Nonempty
    · obtain ⟨x, hx⟩ := hNonempty
      let translate (y : X.carrier) : X.carrier :=
        ⟨shift (k : ℤ) y.1, X.mapsTo _ y.2⟩
      have hMaps : MapsTo translate (extensions X u)
          (univ ∩ ForwardBowen (shiftOne X) ε (translate x)) := by
        intro y hy
        refine ⟨mem_univ _, fun t => hClose _ _ (fun i hi => ?_)⟩
        rw [shiftOne_iterate_apply, shiftOne_iterate_apply]
        change x.1 ((k : ℤ) + ((t : ℤ) + i)) = y.1 ((k : ℤ) + ((t : ℤ) + i))
        have hj : 0 ≤ (k : ℤ) + ((t : ℤ) + i) := by
          have := hi.1
          omega
        have hxy := congrFun (hx.trans hy.symm) ((k : ℤ) + ((t : ℤ) + i)).toNat
        simpa only [tail, Nat.cast_zero, sub_zero, Int.toNat_of_nonneg hj] using hxy
      have hInj : InjOn translate (extensions X u) := by
        intro y _ z _ hEq
        apply Subtype.ext
        funext i
        have hVal := congrArg (fun y : X.carrier => y.1 (i - (k : ℤ))) hEq
        change y.1 ((k : ℤ) + (i - (k : ℤ))) = z.1 ((k : ℤ) + (i - (k : ℤ))) at hVal
        simpa only [show (k : ℤ) + (i - (k : ℤ)) = i by omega] using hVal
      exact (encard_le_encard_of_injOn hMaps hInj).trans (hBound _ (mem_univ _))
    · simp [Set.not_nonempty_iff_eq_empty.mp hNonempty]
  · intro h
    obtain ⟨ε, hε, hAgree⟩ := controls.1 0
    refine ⟨ε, hε, fun x _ => ?_⟩
    refine (encard_le_encard (t := extensions X (tail x.1 0)) ?_).trans (h _)
    intro y hy
    funext n
    have hn : (0 : ℤ) ∈ Set.Icc (-(0 : ℕ) : ℤ) ((0 : ℕ) : ℤ) := by simp
    have hLabel := hAgree _ _ (hy.2 n) 0 hn
    rw [shiftOne_iterate_apply, shiftOne_iterate_apply] at hLabel
    simpa only [tail, Nat.cast_zero, sub_zero, add_zero] using hLabel.symm

/-- A finite branching set leaves a single obstruction to finite positive expansivity.
Every periodic future must have only periodic two-sided extensions. -/
theorem finitelyPositiveExpansive_iff_periodic_extensions (X : Subshift A ℤ)
    (hB : (branchingTails X).Finite) (d : MetricSpace X.carrier)
    (hd : d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace X.carrier)) :
    let := d
    FinitelyPositiveExpansive (shiftOne X) ↔
      ∀ u, PeriodicTail u → ∀ x : extensions X u, PeriodicPoint x.1.1 := by
  let := d
  constructor
  · rintro ⟨ε, hε, N, _, hBound⟩ u hu x
    by_contra hx
    have hCard := (forwardBowenBound_iff_bounded_extensions X d hd N).mp
      ⟨ε, hε, hBound⟩ u
    exact infinite_extensions_of_nonperiodic_extension hu x hx (finite_of_encard_le_coe hCard)
  · intro h
    let : Fintype A := Fintype.ofFinite A
    let N := 1 + Nat.card (branchingTails X) * (Fintype.card A - 1)
    have hCard (u : ℕ → A) : (extensions X u).encard ≤ (N : ℕ∞) := by
      obtain ⟨hFin, hBound⟩ := (uniform_finite_extensions_iff X hB).mpr h u
      have : Finite (extensions X u) := hFin.to_subtype
      change ENat.card (extensions X u) ≤ _
      rw [ENat.card_eq_coe_natCard]
      exact_mod_cast hBound
    obtain ⟨ε, hε, hBound⟩ :=
      (forwardBowenBound_iff_bounded_extensions X d hd N).mpr hCard
    exact ⟨ε, hε, N, by dsimp [N]; omega, hBound⟩

end Metric

end D5.S1.Dynamics.Symbolic.RightTailBranching
