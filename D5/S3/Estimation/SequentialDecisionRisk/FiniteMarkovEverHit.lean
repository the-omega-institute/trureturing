/- GID: D5/S3/Estimation/SequentialDecisionRisk/FiniteMarkovEverHit
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/FiniteMarkovEverHit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-step hitting probabilities converge to the least nonnegative harmonic hitting function. -/

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Linarith

open scoped BigOperators Topology Classical
open Filter

namespace D5.S3.Estimation.SequentialDecisionRisk.FiniteMarkovEverHit

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The probability of occupying the absorbing target after at most n transitions. -/
noncomputable def hitWithin (W : S → S → ℝ) (target : S) : ℕ → S → ℝ
  | 0 => fun x => if x = target then 1 else 0
  | n + 1 => fun x => ∑ y, W x y * hitWithin W target n y

/-- The supremum of the finite-step hitting probabilities, including time zero. -/
noncomputable def everHit (W : S → S → ℝ) (target x : S) : ℝ :=
  ⨆ n, hitWithin W target n x

private theorem within_bounds (W : S → S → ℝ) (target : S)
    (hW0 : ∀ x y, 0 ≤ W x y) (hW1 : ∀ x, ∑ y, W x y = 1) :
    ∀ n x, 0 ≤ hitWithin W target n x ∧ hitWithin W target n x ≤ 1 := by
  intro n
  induction n with
  | zero => intro x; by_cases hx : x = target <;> simp [hitWithin, hx]
  | succ n ih =>
    intro x
    constructor
    · exact Finset.sum_nonneg (fun y _ => mul_nonneg (hW0 x y) (ih y).1)
    · calc
        _ ≤ ∑ y, W x y * 1 := Finset.sum_le_sum (fun y _ =>
          mul_le_mul_of_nonneg_left (ih y).2 (hW0 x y))
        _ = 1 := by simpa using hW1 x

private theorem within_target (W : S → S → ℝ) (target : S)
    (hfix : ∀ y, W target y = if y = target then 1 else 0) :
    ∀ n, hitWithin W target n target = 1 := by
  intro n
  induction n with
  | zero => simp [hitWithin]
  | succ n ih => simpa [hitWithin, hfix] using ih

private theorem within_mono (W : S → S → ℝ) (target : S)
    (hW0 : ∀ x y, 0 ≤ W x y) (hW1 : ∀ x, ∑ y, W x y = 1)
    (hfix : ∀ y, W target y = if y = target then 1 else 0) (x : S) :
    Monotone (fun n => hitWithin W target n x) := by
  have step : ∀ n x, hitWithin W target n x ≤ hitWithin W target (n + 1) x := by
    intro n
    induction n with
    | zero =>
      intro x
      by_cases hx : x = target
      · subst x; rw [within_target W target hfix 0, within_target W target hfix 1]
      · simpa [hitWithin, hx] using (within_bounds W target hW0 hW1 1 x).1
    | succ n ih =>
      intro x
      exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (ih y) (hW0 x y))
  exact monotone_nat_of_le_succ (fun n => step n x)

universe u
def Future (S : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => S × Future S n

noncomputable instance futureFintype : (n : ℕ) → Fintype (Future S n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => @instFintypeProd _ _ inferInstance (futureFintype n)

noncomputable def futureMass (W : S → S → ℝ) : (n : ℕ) → S → Future S n → ℝ
  | 0 => fun _ _ => 1
  | n + 1 => fun x p => W x p.1 * futureMass W n p.1 p.2

def visits (target : S) : (n : ℕ) → S → Future S n → Prop
  | 0 => fun x _ => x = target
  | n + 1 => fun x p => x = target ∨ visits target n p.1 p.2

private theorem future_mass_sum (W : S → S → ℝ)
    (hW1 : ∀ x, ∑ y, W x y = 1) :
    ∀ n x, ∑ p, futureMass W n x p = 1 := by
  intro n
  induction n with
  | zero => intro x; simp [Future, futureMass]
  | succ n ih =>
    intro x
    change (∑ p : S × Future S n, W x p.1 * futureMass W n p.1 p.2) = 1
    simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, ih, mul_one]
    exact hW1 x

private theorem within_is_hit_probability (W : S → S → ℝ) (target : S)
    (hW1 : ∀ x, ∑ y, W x y = 1)
    (hfix : ∀ y, W target y = if y = target then 1 else 0) :
    ∀ n x, hitWithin W target n x =
      ∑ p, futureMass W n x p * (if visits target n x p then (1 : ℝ) else 0) := by
  classical
  intro n
  induction n with
  | zero => intro x; simp [hitWithin, Future, futureMass, visits]
  | succ n ih =>
    intro x
    by_cases hx : x = target
    · subst x
      rw [within_target W target hfix]
      simpa [visits] using (future_mass_sum W hW1 (n + 1) target).symm
    · change (∑ y, W x y * hitWithin W target n y) =
        ∑ p : S × Future S n, (W x p.1 * futureMass W n p.1 p.2) *
          (if x = target ∨ visits target n p.1 p.2 then (1 : ℝ) else 0)
      simp only [hx, false_or, Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum, ← ih]

/-- Finite-step hitting probabilities converge to the least nonnegative harmonic
function equal to one at the target. A second absorbing label has value zero.
There is no termination, irreducibility, or mean-hitting-time hypothesis. -/
theorem ever_hit_harmonic (W : S → S → ℝ) (d0 d1 : S) (hne : d0 ≠ d1)
    (hW0 : ∀ x y, 0 ≤ W x y) (hW1 : ∀ x, ∑ y, W x y = 1)
    (hfix0 : ∀ y, W d0 y = if y = d0 then 1 else 0)
    (hfix1 : ∀ y, W d1 y = if y = d1 then 1 else 0) :
    (∀ x, 0 ≤ everHit W d1 x ∧ everHit W d1 x ≤ 1) ∧
    everHit W d1 d0 = 0 ∧ everHit W d1 d1 = 1 ∧
    (∀ x, Tendsto (fun n => hitWithin W d1 n x) atTop (𝓝 (everHit W d1 x))) ∧
    (∀ x, ∑ y, W x y * everHit W d1 y = everHit W d1 x) ∧
    (∀ n x, hitWithin W d1 n x =
      ∑ p, futureMass W n x p * (if visits d1 n x p then (1 : ℝ) else 0)) ∧
    (∀ g : S → ℝ, (∀ x, 0 ≤ g x) → 1 ≤ g d1 →
      (∀ x, ∑ y, W x y * g y ≤ g x) → ∀ x, everHit W d1 x ≤ g x) := by
  have hb (x : S) : BddAbove (Set.range (fun n => hitWithin W d1 n x)) :=
    ⟨1, fun _ ⟨n, hn⟩ => hn ▸ (within_bounds W d1 hW0 hW1 n x).2⟩
  have ht (x : S) : Tendsto (fun n => hitWithin W d1 n x) atTop (𝓝 (everHit W d1 x)) :=
    tendsto_atTop_ciSup (within_mono W d1 hW0 hW1 hfix1 x) (hb x)
  have hz : ∀ n, hitWithin W d1 n d0 = 0 := by
    intro n
    induction n with
    | zero => simp [hitWithin, hne]
    | succ n ih => simpa [hitWithin, hfix0] using ih
  refine ⟨?_, ?_, ?_, ht, ?_, within_is_hit_probability W d1 hW1 hfix1, ?_⟩
  · intro x
    exact ⟨(within_bounds W d1 hW0 hW1 0 x).1.trans (le_ciSup (hb x) 0),
      ciSup_le (fun n => (within_bounds W d1 hW0 hW1 n x).2)⟩
  · simp [everHit, hz]
  · simp [everHit, within_target W d1 hfix1]
  · intro x
    have hs : Tendsto (fun n => ∑ y, W x y * hitWithin W d1 n y) atTop
        (𝓝 (∑ y, W x y * everHit W d1 y)) :=
      tendsto_finsetSum _ (fun y _ => (ht y).const_mul (W x y))
    have hshift : Tendsto (fun n => hitWithin W d1 (n + 1) x) atTop
        (𝓝 (everHit W d1 x)) :=
      (tendsto_add_atTop_iff_nat 1).mpr (ht x)
    exact tendsto_nhds_unique hs hshift
  · intro g hg hg1 hsuper x
    apply ciSup_le
    intro n
    have hi : ∀ n x, hitWithin W d1 n x ≤ g x := by
      intro n
      induction n with
      | zero => intro y; by_cases hy : y = d1 <;> simp [hitWithin, hy, hg, hg1]
      | succ n ih =>
        intro y
        exact (Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (ih z) (hW0 y z))).trans
          (hsuper y)
    exact hi n x

end D5.S3.Estimation.SequentialDecisionRisk.FiniteMarkovEverHit
