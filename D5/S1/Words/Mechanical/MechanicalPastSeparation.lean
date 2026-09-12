/- GID: D5/S1/Words/Mechanical/MechanicalPastSeparation
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalPastSeparation
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Actual lower and upper irrational mechanical traces have an exact two-site
     disagreement, giving a sharp prediction threshold even with the entire past. -/

import D5.S1.Words.Mechanical.MechanicalBalance
import Mathlib.NumberTheory.Real.Irrational

set_option autoImplicit false

namespace D5.S1.Words.Mechanical.PastSeparation

/-- A lower mechanical trace, with its boundary crossing at integer time `m`. -/
noncomputable def lower (alpha : Real) (m t : Int) : Int :=
  ⌊((t + 1 - m : Int) : Real) * alpha⌋ - ⌊((t - m : Int) : Real) * alpha⌋

/-- The upper boundary convention on exactly the same rotation orbit. -/
noncomputable def upper (alpha : Real) (m t : Int) : Int :=
  ⌈((t + 1 - m : Int) : Real) * alpha⌉ - ⌈((t - m : Int) : Real) * alpha⌉

/-- The actual two-sided boundary orbit, not a graph of independently chosen edges. -/
def BoundaryTrace (alpha : Real) (w : Int → Int) : Prop :=
  ∃ m : Int, w = lower alpha m ∨ w = upper alpha m

/-- All length-`J` windows beginning at times at most zero agree.  In particular,
this includes the current window, with samples at times `0,...,J-1`. -/
def PastEq (J : Nat) (u v : Int → Int) : Prop :=
  ∀ t : Int, t ≤ 0 → ∀ k : Fin J, u (t + (k.val : Int)) = v (t + (k.val : Int))

/-- The complete observed segment, including both times zero and `h`. -/
def SegmentEq (L h : Nat) (u v : Int → Int) : Prop :=
  ∀ s : Nat, s ≤ h → ∀ k : Fin L,
    u ((s : Int) + (k.val : Int)) = v ((s : Int) + (k.val : Int))

private theorem ceil_mul (alpha : Real) (ha : Irrational alpha)
    (k : Int) (hk : k ≠ 0) :
    ⌈(k : Real) * alpha⌉ = ⌊(k : Real) * alpha⌋ + 1 := by
  apply (Int.ceil_eq_floor_add_one_iff_notMem _).mpr
  rintro ⟨z, hz⟩
  exact (ha.intCast_mul hk).ne_int z hz.symm

/-- Away from the two integer-boundary samples, the floor/ceiling corrections cancel. -/
theorem agree_off_boundary {alpha : Real} (ha : Irrational alpha)
    (m t : Int) (hprev : t ≠ m - 1) (hnow : t ≠ m) :
    lower alpha m t = upper alpha m t := by
  have h₁ : t + 1 - m ≠ 0 := by omega
  have h₀ : t - m ≠ 0 := by omega
  unfold lower upper
  rw [ceil_mul alpha ha _ h₁, ceil_mul alpha ha _ h₀]
  omega

/-- The two boundary samples are exchanged, rather than assigned independent labels. -/
theorem boundary_values {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (m : Int) :
    lower alpha m (m - 1) = 1 ∧ upper alpha m (m - 1) = 0 ∧
      lower alpha m m = 0 ∧ upper alpha m m = 1 := by
  have hf : ⌊alpha⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨ha0.le, ha1⟩
  have hc : ⌈alpha⌉ = 1 := by
    apply Int.ceil_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  have hfn : ⌊-alpha⌋ = -1 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  have hcn : ⌈-alpha⌉ = 0 := by
    apply Int.ceil_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  have hprev : m - 1 + 1 - m = (0 : Int) := by omega
  have hneg : m - 1 - m = (-1 : Int) := by omega
  have hnext : m + 1 - m = (1 : Int) := by omega
  simp [lower, upper, hprev, hneg, hnext, hf, hc, hfn, hcn]

/-- Exact disagreement support for every irrational slope in `(0,1)`. -/
theorem disagree_iff {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (ha : Irrational alpha) (m t : Int) :
    lower alpha m t ≠ upper alpha m t ↔ t = m - 1 ∨ t = m := by
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    exact h (agree_off_boundary ha m t hn.1 hn.2)
  · intro h
    rcases boundary_values ha0 ha1 m with ⟨hp, hq, hr, hs⟩
    rcases h with rfl | rfl
    · omega
    · omega

/-- These are genuinely binary traces, although integer values simplify the floor algebra. -/
theorem lower_binary {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (m t : Int) : lower alpha m t = 0 ∨ lower alpha m t = 1 := by
  have hf : ⌊alpha⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨ha0.le, ha1⟩
  have hl := Int.le_floor_add (((t - m : Int) : Real) * alpha) alpha
  have hu := Int.le_floor_add_floor (((t - m : Int) : Real) * alpha) alpha
  rw [hf, add_zero] at hl hu
  have he : ((t + 1 - m : Int) : Real) * alpha =
      ((t - m : Int) : Real) * alpha + alpha := by push_cast; ring
  unfold lower
  rw [he]
  omega

theorem upper_binary {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (ha : Irrational alpha) (m t : Int) :
    upper alpha m t = 0 ∨ upper alpha m t = 1 := by
  by_cases hp : t = m - 1
  · subst t
    exact Or.inl (boundary_values ha0 ha1 m).2.1
  by_cases hq : t = m
  · subst t
    exact Or.inr (boundary_values ha0 ha1 m).2.2.2
  rw [← agree_off_boundary ha m t hp hq]
  exact lower_binary ha0 ha1 m t

/-- Moving the clock transports the same boundary state; the sides do not change. -/
theorem lower_shift (alpha : Real) (m t : Int) :
    lower alpha m (t + 1) = lower alpha (m - 1) t := by
  have h₀ : t + 1 - m = t - (m - 1) := by omega
  have h₁ : t + 1 + 1 - m = t + 1 - (m - 1) := by omega
  simp only [lower, h₀, h₁]

theorem upper_shift (alpha : Real) (m t : Int) :
    upper alpha m (t + 1) = upper alpha (m - 1) t := by
  have h₀ : t + 1 - m = t - (m - 1) := by omega
  have h₁ : t + 1 + 1 - m = t + 1 - (m - 1) := by omega
  simp only [upper, h₀, h₁]

/-- A boundary beyond the current window is invisible at every past time. -/
theorem whole_past_agrees {alpha : Real} (ha : Irrational alpha)
    (J : Nat) (m : Int) (hm : (J : Int) < m) :
    PastEq J (lower alpha m) (upper alpha m) := by
  intro t ht k
  have hk := k.isLt
  apply agree_off_boundary ha
  · omega
  · omega

/-- For this same pair, observation disagreement disappears again after the crossing. -/
theorem future_rejoins {alpha : Real} (ha : Irrational alpha)
    (m t : Int) (ht : m < t) : lower alpha m t = upper alpha m t := by
  apply agree_off_boundary ha <;> omega

/-- The inclusion threshold is sufficient for arbitrary traces, with no mechanical assumption. -/
theorem segment_of_current_coverage {J L h : Nat} (hcover : L + h ≤ J)
    {u v : Int → Int} (hp : PastEq J u v) : SegmentEq L h u v := by
  intro s hs k
  have hk := k.isLt
  have hi : s + k.val < J := by omega
  have he := hp 0 (by omega) ⟨s + k.val, hi⟩
  simpa using he

/-- A concrete failed-coverage witness has identical entire past and different terminal window. -/
theorem invisible_past_visible_future {alpha : Real}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (ha : Irrational alpha)
    {J L h : Nat} (hL : 0 < L) (hgap : J < L + h) :
    ∃ u v : Int → Int, BoundaryTrace alpha u ∧ BoundaryTrace alpha v ∧
      PastEq J u v ∧
      (∃ k : Fin L, u ((h : Int) + (k.val : Int)) ≠
        v ((h : Int) + (k.val : Int))) ∧ ¬ SegmentEq L h u v := by
  let m : Int := ((L + h : Nat) : Int)
  have hm : (J : Int) < m := by exact_mod_cast hgap
  let k : Fin L := ⟨L - 1, by omega⟩
  have htime : (h : Int) + (k.val : Int) = m - 1 := by
    dsimp [k, m]
    omega
  have hdiff : lower alpha m ((h : Int) + (k.val : Int)) ≠
      upper alpha m ((h : Int) + (k.val : Int)) :=
    (disagree_iff ha0 ha1 ha m _).mpr (Or.inl htime)
  refine ⟨lower alpha m, upper alpha m, ⟨m, Or.inl rfl⟩,
    ⟨m, Or.inr rfl⟩, whole_past_agrees ha J m hm, ⟨k, hdiff⟩, ?_⟩
  intro hs
  exact hdiff (hs h le_rfl k)

/-- The sharp full-past prediction law on the actual two-sided boundary orbit. -/
theorem whole_past_prediction_iff {alpha : Real}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (ha : Irrational alpha)
    (J L h : Nat) (hL : 0 < L) :
    (∀ u v : Int → Int, BoundaryTrace alpha u → BoundaryTrace alpha v →
      PastEq J u v → SegmentEq L h u v) ↔ L + h ≤ J := by
  constructor
  · intro hall
    by_contra hn
    have hgap : J < L + h := by omega
    obtain ⟨u, v, hu, hv, hp, _, hnseg⟩ :=
      invisible_past_visible_future ha0 ha1 ha hL hgap
    exact hnseg (hall u v hu hv hp)
  · intro hcover u v _ _ hp
    exact segment_of_current_coverage hcover hp

/-- Even an unbounded past leaves a target-relevant residual pair whenever coverage fails. -/
theorem whole_past_kernel_not_target_kernel {alpha : Real}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (ha : Irrational alpha)
    (J : Nat) :
    ∃ u v : Int → Int, BoundaryTrace alpha u ∧ BoundaryTrace alpha v ∧
      PastEq J u v ∧ u (J : Int) ≠ v (J : Int) := by
  obtain ⟨u, v, hu, hv, hp, ⟨k, hk⟩, _⟩ :=
    invisible_past_visible_future ha0 ha1 ha
      (J := J) (L := 1) (h := J) (by omega) (by omega)
  have hk0 : k.val = 0 := by have := k.isLt; omega
  exact ⟨u, v, hu, hv, hp, by simpa [hk0] using hk⟩

#print axioms disagree_iff
#print axioms whole_past_prediction_iff
#print axioms whole_past_kernel_not_target_kernel

end D5.S1.Words.Mechanical.PastSeparation
