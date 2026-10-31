/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Essential periods extracted from actual colored periodic skeletons. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.PeriodicSkeletonDensity
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Algebra.Ring.Periodic

/-! The colored skeleton keeps both its mask and its actual letters. Essential
periods require a nonempty skeleton and its least positive global period.
The source period structure will also require strict growth, divisibility and
coverage, with no extra assumptions inserted into the balanced application.
Public escape registrations remain unfinished under
https://github.com/the-omega-institute/trureturing/issues/24726. -/

set_option autoImplicit false

open Set Function SymbolicDynamics.FullShift Filter
open scoped Topology BigOperators

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.PeriodicSkeleton

/-- Literal periodicity at one signed coordinate, with all integer multiples. -/
def CoordinatePeriodic {A : Type*} (x : ℤ → A) (p : ℕ) (i : ℤ) : Prop :=
  ∀ k : ℤ, x (i + k * (p : ℤ)) = x i

/-- The actual set of period-p coordinates. Positive periods are imposed by
period structures and essentiality rather than hidden in this predicate. -/
def sites {A : Type*} (x : ℤ → A) (p : ℕ) : Set ℤ :=
  {i | CoordinatePeriodic x p i}

/-- Actual letters on periodic coordinates and holes elsewhere. -/
noncomputable def color {A : Type*} (x : ℤ → A) (p : ℕ) (i : ℤ) : Option A := by
  classical
  exact if CoordinatePeriodic x p i then some (x i) else none

theorem coordinate_periodic_of_dvd {A : Type*} {x : ℤ → A} {p q : ℕ} {i : ℤ}
    (hpq : p ∣ q) (hi : CoordinatePeriodic x p i) : CoordinatePeriodic x q i := by
  obtain ⟨m, rfl⟩ := hpq
  intro k
  have he : i + k * ((p * m : ℕ) : ℤ) = i + (k * (m : ℤ)) * (p : ℤ) := by
    push_cast
    ring
  rw [he]
  exact hi (k * (m : ℤ))

theorem coordinate_periodic_translate {A : Type*} {x : ℤ → A} {p : ℕ} {i : ℤ}
    (hi : CoordinatePeriodic x p i) (t : ℤ) :
    CoordinatePeriodic x p (i + t * (p : ℤ)) := by
  intro k
  have he : (i + t * (p : ℤ)) + k * (p : ℤ) = i + (t + k) * (p : ℤ) := by ring
  rw [he]
  exact (hi (t + k)).trans (hi t).symm

theorem coordinate_periodic_translate_iff {A : Type*} (x : ℤ → A) (p : ℕ) (i t : ℤ) :
    CoordinatePeriodic x p (i + t * (p : ℤ)) ↔ CoordinatePeriodic x p i := by
  constructor
  · intro h
    have hh := coordinate_periodic_translate h (-t)
    have he : (i + t * (p : ℤ)) + (-t) * (p : ℤ) = i := by ring
    rwa [he] at hh
  · exact fun h => coordinate_periodic_translate h t

theorem color_eq_some_iff {A : Type*} (x : ℤ → A) (p : ℕ) (i : ℤ) (a : A) :
    color x p i = some a ↔ CoordinatePeriodic x p i ∧ x i = a := by
  classical
  by_cases h : CoordinatePeriodic x p i <;> simp [color, h]

/-- A period of a colored skeleton preserves actual letters on its mask. -/
theorem value_eq_of_color_period {A : Type*} {x : ℤ → A} {p : ℕ} {q i : ℤ}
    (hcolor : Function.Periodic (color x p) q) (hi : CoordinatePeriodic x p i)
    (t : ℤ) : x (i + t * q) = x i := by
  have hsome : color x p (i + t * q) = some (x i) :=
    ((hcolor.int_mul t) i).trans ((color_eq_some_iff x p i (x i)).mpr ⟨hi, rfl⟩)
  exact ((color_eq_some_iff x p (i + t * q) (x i)).mp hsome).2

/-- Refinement along divisibility lets a larger colored skeleton translate
all smaller-period coordinates, in both signed translation directions. -/
theorem coordinate_translate_of_super_color_period {A : Type*} {x : ℤ → A}
    {p r : ℕ} {q i : ℤ} (hpr : p ∣ r)
    (hcolor : Function.Periodic (color x r) q) (hi : CoordinatePeriodic x p i)
    (t : ℤ) : CoordinatePeriodic x p (i + t * q) := by
  intro k
  have hbase := value_eq_of_color_period hcolor (coordinate_periodic_of_dvd hpr hi) t
  have hother := value_eq_of_color_period hcolor
    (coordinate_periodic_of_dvd hpr (coordinate_periodic_translate hi k)) t
  calc
    x ((i + t * q) + k * (p : ℤ)) = x ((i + k * (p : ℤ)) + t * q) := by
      congr 1
      ring
    _ = x (i + k * (p : ℤ)) := hother
    _ = x i := hi k
    _ = x (i + t * q) := hbase.symm

/-- A period of a larger colored skeleton is also a period of every
smaller skeleton whose defining period divides the larger one. -/
theorem color_periodic_of_dvd {A : Type*} {x : ℤ → A} {p r : ℕ} {q : ℤ}
    (hpr : p ∣ r) (hcolor : Function.Periodic (color x r) q) :
    Function.Periodic (color x p) q := by
  classical
  intro i
  have hiff : CoordinatePeriodic x p (i + q) ↔ CoordinatePeriodic x p i := by
    constructor
    · intro h
      have hh := coordinate_translate_of_super_color_period hpr hcolor h (-1)
      simpa only [neg_one_mul, add_neg_cancel_right] using hh
    · intro h
      simpa only [one_mul] using coordinate_translate_of_super_color_period hpr hcolor h 1
  by_cases hi : CoordinatePeriodic x p i
  · have hv := value_eq_of_color_period hcolor (coordinate_periodic_of_dvd hpr hi) 1
    simp only [one_mul] at hv
    simp [color, hi, hiff.mpr hi, hv]
  · have hni : ¬ CoordinatePeriodic x p (i + q) := fun h => hi (hiff.mp h)
    simp [color, hi, hni]


/-- Iterating the actual unit shift gives the corresponding natural shift. -/
theorem iterate_unit_shift {A : Type*} (x : ℤ → A) (n : ℕ) :
    ((shift (1 : ℤ))^[n]) x = shift (n : ℤ) x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simpa only [Nat.cast_add, Nat.cast_one] using (shift_add (n : ℤ) 1 x).symm

/-- Natural dynamical periods are exactly positive-direction integer periods. -/
theorem isPeriodicPt_unit_shift_iff {A : Type*} (x : ℤ → A) (n : ℕ) :
    Function.IsPeriodicPt (shift (1 : ℤ)) n x ↔ Function.Periodic x (n : ℤ) := by
  change ((shift (1 : ℤ))^[n]) x = x ↔ _
  rw [iterate_unit_shift]
  constructor
  · intro h i
    have hh := congrFun h i
    change x ((n : ℤ) + i) = x i at hh
    simpa only [add_comm] using hh
  · intro h
    funext i
    change x ((n : ℤ) + i) = x i
    simpa only [add_comm] using h i

/-- A colored p-skeleton is globally p-periodic, including its holes. -/
theorem color_self_periodic {A : Type*} (x : ℤ → A) (p : ℕ) :
    Function.Periodic (color x p) (p : ℤ) := by
  classical
  intro i
  have hiff : CoordinatePeriodic x p (i + (p : ℤ)) ↔ CoordinatePeriodic x p i := by
    simpa only [one_mul] using coordinate_periodic_translate_iff x p i 1
  by_cases hi : CoordinatePeriodic x p i
  · have hv := hi 1
    simp only [one_mul] at hv
    simp [color, hi, hiff.mpr hi, hv]
  · have hn : ¬ CoordinatePeriodic x p (i + (p : ℤ)) := fun h => hi (hiff.mp h)
    simp [color, hi, hn]

/-- The least natural period of the actual colored skeleton under unit shift. -/
noncomputable def leastPeriod {A : Type*} (x : ℤ → A) (p : ℕ) : ℕ :=
  Function.minimalPeriod (shift (1 : ℤ)) (color x p)

theorem leastPeriod_pos {A : Type*} (x : ℤ → A) {p : ℕ} (hp : 0 < p) :
    0 < leastPeriod x p := by
  exact ((isPeriodicPt_unit_shift_iff (color x p) p).mpr
    (color_self_periodic x p)).minimalPeriod_pos hp

theorem leastPeriod_dvd {A : Type*} (x : ℤ → A) (p : ℕ) : leastPeriod x p ∣ p := by
  exact ((isPeriodicPt_unit_shift_iff (color x p) p).mpr
    (color_self_periodic x p)).minimalPeriod_dvd

theorem color_leastPeriod_periodic {A : Type*} (x : ℤ → A) (p : ℕ) :
    Function.Periodic (color x p) (leastPeriod x p : ℤ) := by
  exact (isPeriodicPt_unit_shift_iff (color x p) (leastPeriod x p)).mp
    (Function.isPeriodicPt_minimalPeriod _ _)

/-- Extracting the colored skeleton's least period preserves the entire
actual periodic-position set, and hence every original letter on it. -/
theorem sites_leastPeriod_eq {A : Type*} (x : ℤ → A) (p : ℕ) :
    sites x (leastPeriod x p) = sites x p := by
  ext i
  constructor
  · intro hi
    exact coordinate_periodic_of_dvd (leastPeriod_dvd x p) hi
  · intro hi k
    exact value_eq_of_color_period (color_leastPeriod_periodic x p) hi k

theorem color_leastPeriod_eq {A : Type*} (x : ℤ → A) (p : ℕ) :
    color x (leastPeriod x p) = color x p := by
  classical
  funext i
  have hiff : CoordinatePeriodic x (leastPeriod x p) i ↔ CoordinatePeriodic x p i := by
    change i ∈ sites x (leastPeriod x p) ↔ i ∈ sites x p
    rw [sites_leastPeriod_eq]
  by_cases hi : CoordinatePeriodic x p i
  · simp [color, hi, hiff.mpr hi]
  · have hn : ¬ CoordinatePeriodic x (leastPeriod x p) i := fun h => hi (hiff.mp h)
    simp [color, hi, hn]

/-- The source's essentiality: a nonempty skeleton with positive least
period exactly equal to the proposed period. -/
def EssentialPeriod {A : Type*} (x : ℤ → A) (p : ℕ) : Prop :=
  0 < p ∧ (sites x p).Nonempty ∧ leastPeriod x p = p

/-- A nonempty positive-period skeleton always supplies an actual essential
period. No essentiality of the original period is assumed. -/
theorem leastPeriod_essential {A : Type*} (x : ℤ → A) {p : ℕ}
    (hp : 0 < p) (hnonempty : (sites x p).Nonempty) :
    EssentialPeriod x (leastPeriod x p) := by
  refine ⟨leastPeriod_pos x hp, ?_, ?_⟩
  · rw [sites_leastPeriod_eq]
    exact hnonempty
  · change Function.minimalPeriod (shift (1 : ℤ)) (color x (leastPeriod x p)) = _
    rw [color_leastPeriod_eq]
    rfl

/-- The least periods of nested colored skeletons divide one another.
The proof transports actual letters, not merely a nested set of masks. -/
theorem leastPeriod_dvd_of_dvd {A : Type*} (x : ℤ → A) {p r : ℕ} (hpr : p ∣ r) :
    leastPeriod x p ∣ leastPeriod x r := by
  have hc := color_periodic_of_dvd hpr (color_leastPeriod_periodic x r)
  exact ((isPeriodicPt_unit_shift_iff (color x p) (leastPeriod x r)).mpr hc).minimalPeriod_dvd

end D5.S1.Dynamics.Symbolic.PermutativeLifts.PeriodicSkeleton
