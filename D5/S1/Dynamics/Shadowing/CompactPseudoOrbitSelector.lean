/- GID: D5/S1/Dynamics/Shadowing/CompactPseudoOrbitSelector
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/CompactPseudoOrbitSelector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact closed bi-infinite pseudo-orbits and fixed-selector local-to-global tracing. -/

import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! The product topology is used throughout. No metric on the sequence space is installed. -/

open Set Filter
open scoped Topology

namespace D5.S1.Dynamics.Shadowing.CompactSelector

variable {M : Type*} [MetricSpace M] (f : M ≃ₜ M)

/-- The literal link error at integer time `i`, in the primary convention. -/
def linkError (x : ℤ → M) (i : ℤ) : ℝ := dist (x (i + 1)) (f (x i))

/-- Closed errors at every integer time; no restriction on their support. -/
def ClosedPseudoOrbit (δ : ℝ) (x : ℤ → M) : Prop := ∀ i, linkError f x i ≤ δ

/-- The entire closed domain, with the subtype of the product topology. -/
abbrev Space (δ : ℝ) := {x : ℤ → M // ClosedPseudoOrbit f δ x}

private theorem continuous_linkError (i : ℤ) : Continuous (fun x : ℤ → M => linkError f x i) :=
  (continuous_apply (i + 1)).dist (f.continuous.comp (continuous_apply i))

/-- Closedness includes equality in every one of the infinitely many error bounds. -/
theorem isClosed_domain (δ : ℝ) : IsClosed {x : ℤ → M | ClosedPseudoOrbit f δ x} := by
  simp only [ClosedPseudoOrbit, ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (continuous_linkError f i) continuous_const

instance [CompactSpace M] (δ : ℝ) : CompactSpace (Space f δ) :=
  isCompact_iff_compactSpace.mp (isClosed_domain f δ).isCompact

/-- Restriction of a fixed selector uses this literal inclusion of closed domains. -/
def inclusion {γ δ : ℝ} (h : γ ≤ δ) : C(Space f γ, Space f δ) where
  toFun x := ⟨x.1, fun i => (x.2 i).trans h⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Every integer shift is a homeomorphism of the same original closed domain. -/
def shift {δ : ℝ} (k : ℤ) : Space f δ ≃ₜ Space f δ where
  toFun x := ⟨SymbolicDynamics.FullShift.shift k x.1, fun i => by
    simpa only [linkError, SymbolicDynamics.FullShift.shift_apply, add_assoc] using
      x.2 (k + i)⟩
  invFun x := ⟨SymbolicDynamics.FullShift.shift (-k) x.1, fun i => by
    simpa only [linkError, SymbolicDynamics.FullShift.shift_apply, add_assoc] using
      x.2 (-k + i)⟩
  left_inv x := by apply Subtype.ext; funext i; simp
  right_inv x := by apply Subtype.ext; funext i; simp
  continuous_toFun := ((SymbolicDynamics.FullShift.continuous_shift k).comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((SymbolicDynamics.FullShift.continuous_shift (-k)).comp
    continuous_subtype_val).subtype_mk _

@[simp] theorem shift_apply {δ : ℝ} (k : ℤ) (x : Space f δ) (i : ℤ) :
    (shift f k x).1 i = x.1 (k + i) := rfl

@[simp] theorem shift_zero {δ : ℝ} (x : Space f δ) : shift f 0 x = x := by
  apply Subtype.ext; funext i; simp

theorem shift_add {δ : ℝ} (k l : ℤ) (x : Space f δ) :
    shift f (k + l) x = shift f k (shift f l x) := by
  apply Subtype.ext; funext i; simp [add_comm, add_left_comm]

/-- The true orbit uses the group of homeomorphisms, including negative powers. -/
def orbit (p : M) (i : ℤ) : M := (f ^ i) p

@[simp] theorem orbit_zero (p : M) : orbit f p 0 = p := by simp [orbit]

theorem orbit_step (p : M) (i : ℤ) : orbit f p (i + 1) = f (orbit f p i) := by
  rw [orbit, show i + 1 = 1 + i by omega, zpow_add, zpow_one, Homeomorph.mul_apply]
  rfl

/-- The continuous genuine-orbit map into every nonnegative closed domain. -/
def trueOrbit {δ : ℝ} (hδ : 0 ≤ δ) : C(M, Space f δ) where
  toFun p := ⟨orbit f p, fun i => by simpa [linkError, orbit_step] using hδ⟩
  continuous_toFun := (continuous_pi fun i => (f ^ i).continuous).subtype_mk _

theorem shift_trueOrbit {δ : ℝ} (hδ : 0 ≤ δ) (k : ℤ) (p : M) :
    shift f k (trueOrbit f hδ p) = trueOrbit f hδ ((f ^ k) p) := by
  apply Subtype.ext; funext i
  change (f ^ (k + i)) p = (f ^ i) ((f ^ k) p)
  rw [add_comm k i, zpow_add, Homeomorph.mul_apply]

private theorem eq_orbit_of_zero_errors (x : ℤ → M)
    (hx : ∀ i, linkError f x i = 0) : x = orbit f (x 0) := by
  have hs (i : ℤ) : x (i + 1) = f (x i) := dist_eq_zero.mp (hx i)
  funext i
  induction i using Int.induction_on with
  | zero => simp
  | succ n ih => rw [hs, orbit_step, ih]
  | pred n ih =>
    apply f.injective
    have horbit := congrArg (fun z : Space f 0 => z.1 1)
      (shift_trueOrbit f (le_refl 0) (-(n : ℤ) - 1) (x 0))
    change orbit f (x 0) (-(n : ℤ) - 1 + 1) =
      orbit f ((f ^ (-(n : ℤ) - 1)) (x 0)) 1 at horbit
    have hrec : f (orbit f (x 0) (-(n : ℤ) - 1)) = orbit f (x 0) (-(n : ℤ)) := by
      simpa only [sub_add_cancel, orbit, zpow_one] using horbit.symm
    rw [hrec]
    have ht : f (x (-(n : ℤ) - 1)) = x (-(n : ℤ)) := by
      simpa only [sub_add_cancel] using (hs (-(n : ℤ) - 1)).symm
    exact ht.trans ih

/-- Continuity and the true-orbit identity force a uniform finite edge window.
The smallness premise tests only that window; the sequence itself ranges over
the entire fixed compact domain, including sequences with infinitely many errors. -/
theorem finite_window [CompactSpace M] {δ : ℝ} (hδ : 0 ≤ δ)
    (Q : Space f δ → M) (hQ : Continuous Q)
    (hfix : ∀ p, Q (trueOrbit f hδ p) = p) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∃ η > 0, ∀ x : Space f δ,
      (∀ i : ℤ, i.natAbs ≤ T → linkError f x.1 i ≤ η) → dist (Q x) (x.1 0) < ε := by
  classical
  by_contra hn
  push Not at hn
  have bad (n : ℕ) : ∃ x : Space f δ,
      (∀ i : ℤ, i.natAbs ≤ n → linkError f x.1 i ≤ 1 / ((n : ℝ) + 1)) ∧
      ε ≤ dist (Q x) (x.1 0) := hn n (1 / ((n : ℝ) + 1)) (by positivity)
  choose x hx hb using bad
  let : FirstCountableTopology M := inferInstance
  let : FirstCountableTopology (ℤ → M) := inferInstance
  let : FirstCountableTopology (Space f δ) :=
    TopologicalSpace.firstCountableTopology_induced (Space f δ) (ℤ → M) Subtype.val
  obtain ⟨a, φ, hφ, ha⟩ := CompactSpace.tendsto_subseq x
  have hz (i : ℤ) : linkError f a.1 i = 0 := by
    have he : Tendsto (fun n => linkError f (x (φ n)).1 i) atTop
        (𝓝 (linkError f a.1 i)) :=
      ((continuous_linkError f i).comp continuous_subtype_val).continuousAt.tendsto.comp ha
    have hr : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hle : linkError f a.1 i ≤ 0 := le_of_tendsto_of_tendsto he hr (by
      filter_upwards [eventually_ge_atTop i.natAbs] with n hn
      exact hx (φ n) i (hn.trans (hφ.id_le n)))
    exact le_antisymm hle dist_nonneg
  have heq : a = trueOrbit f hδ (a.1 0) := Subtype.ext (eq_orbit_of_zero_errors f a.1 hz)
  have hd : Tendsto (fun n => dist (Q (x (φ n))) ((x (φ n)).1 0)) atTop
      (𝓝 (dist (Q a) (a.1 0))) :=
    (hQ.continuousAt.tendsto.comp ha).dist
      (((continuous_apply 0).comp continuous_subtype_val).continuousAt.tendsto.comp ha)
  have hbad := ge_of_tendsto hd (Eventually.of_forall fun n => hb (φ n))
  have hqa : Q a = a.1 0 := by
    calc Q a = Q (trueOrbit f hδ (a.1 0)) := congrArg Q heq
         _ = a.1 0 := hfix _
  rw [hqa, dist_self] at hbad
  exact (not_le_of_gt hε) hbad

/-- One-step exact equivariance supplies all positive and negative integer times. -/
theorem equivariant_integer {δ : ℝ} (Q : Space f δ → M)
    (heq : ∀ x, Q (shift f 1 x) = f (Q x)) (k : ℤ) (x : Space f δ) :
    Q (shift f k x) = orbit f (Q x) k := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have ht : shift f ((n : ℤ) + 1) x = shift f 1 (shift f n x) := by
      rw [← shift_add]
      exact congrArg (fun k : ℤ => shift f k x) (by omega)
    rw [ht, heq, ih, ← orbit_step]
  | pred n ih =>
    apply f.injective
    calc
      f (Q (shift f (-(n : ℤ) - 1) x)) =
          Q (shift f 1 (shift f (-(n : ℤ) - 1) x)) := (heq _).symm
      _ = Q (shift f (-(n : ℤ)) x) := by
        rw [← shift_add]
        exact congrArg (fun k : ℤ => Q (shift f k x)) (by omega)
      _ = orbit f (Q x) (-(n : ℤ)) := ih
      _ = f (orbit f (Q x) (-(n : ℤ) - 1)) := by rw [← orbit_step]; congr 1; omega

/-- The compactness window is uniform over all integer centers on one fixed domain. -/
theorem finite_window_all_times [CompactSpace M] {δ : ℝ} (hδ : 0 ≤ δ)
    (Q : Space f δ → M) (hQ : Continuous Q)
    (hfix : ∀ p, Q (trueOrbit f hδ p) = p)
    (heq : ∀ x, Q (shift f 1 x) = f (Q x)) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∃ η > 0, ∀ (x : Space f δ) (k : ℤ),
      (∀ i : ℤ, i.natAbs ≤ T → linkError f x.1 (k + i) ≤ η) →
        dist (orbit f (Q x) k) (x.1 k) < ε := by
  obtain ⟨T, η, hη, hw⟩ := finite_window f hδ Q hQ hfix ε hε
  refine ⟨T, η, hη, fun x k hx => ?_⟩
  have h := hw (shift f k x) (fun i hi => by
    simpa only [linkError, shift_apply, add_assoc] using hx i hi)
  simpa only [equivariant_integer f Q heq, shift_apply, add_zero] using h

private theorem eventually_cofinite_iff_natAbs (p : ℤ → Prop) :
    (∀ᶠ i in cofinite, p i) ↔ ∃ A : ℕ, ∀ i : ℤ, A ≤ i.natAbs → p i := by
  classical
  constructor
  · intro hp
    have hf := eventually_cofinite.mp hp
    refine ⟨hf.toFinset.sup Int.natAbs + 1, fun i hi => ?_⟩
    by_contra hn
    have hb : i.natAbs ≤ hf.toFinset.sup Int.natAbs :=
      Finset.le_sup (hf.mem_toFinset.mpr hn)
    omega
  · rintro ⟨A, hA⟩
    apply eventually_cofinite.mpr
    apply (Set.finite_Icc (-(A : ℤ)) (A : ℤ)).subset
    intro i hi
    have ha : i.natAbs < A := lt_of_not_ge fun h => hi (hA i h)
    have hleft := Int.le_natAbs (a := -i)
    have hright := Int.le_natAbs (a := i)
    simp only [Int.natAbs_neg] at hleft
    constructor <;> omega

/-- One fixed equivariant orbit retraction gives all-scale global tracing and
two-sided limit tracing on its entire original domain. The second conclusion
has both the explicit `natAbs` tail and the cofinite-filter formulation. -/
theorem global_and_limit_shadowing [CompactSpace M] {δ : ℝ} (hδ : 0 < δ)
    (Q : Space f δ → M) (hQ : Continuous Q)
    (hfix : ∀ p, Q (trueOrbit f hδ.le p) = p)
    (heq : ∀ x, Q (shift f 1 x) = f (Q x)) :
    (∀ ε > 0, ∃ γ > 0, ∃ hγδ : γ ≤ δ, ∀ (x : Space f γ) (k : ℤ),
      dist (orbit f (Q (inclusion f hγδ x)) k) (x.1 k) < ε) ∧
    (∀ x : Space f δ, Tendsto (linkError f x.1) cofinite (𝓝 0) →
      (∀ ε > 0, ∃ N : ℕ, ∀ k : ℤ, N ≤ k.natAbs →
        dist (orbit f (Q x) k) (x.1 k) < ε) ∧
      Tendsto (fun k : ℤ => dist (orbit f (Q x) k) (x.1 k)) cofinite (𝓝 0)) := by
  constructor
  · intro ε hε
    obtain ⟨T, η, hη, hw⟩ := finite_window_all_times f hδ.le Q hQ hfix heq ε hε
    refine ⟨min δ η, lt_min hδ hη, min_le_left _ _, fun x k => ?_⟩
    exact hw (inclusion f (min_le_left δ η) x) k
      (fun i _ => (x.2 (k + i)).trans (min_le_right _ _))
  · intro x hx
    have ht : ∀ ε > 0, ∃ N : ℕ, ∀ k : ℤ, N ≤ k.natAbs →
        dist (orbit f (Q x) k) (x.1 k) < ε := by
      intro ε hε
      obtain ⟨T, η, hη, hw⟩ := finite_window_all_times f hδ.le Q hQ hfix heq ε hε
      have herr : ∀ᶠ i in cofinite, linkError f x.1 i ≤ η :=
        (hx.eventually (Iio_mem_nhds hη)).mono fun _ hi => hi.le
      obtain ⟨A, hA⟩ := (eventually_cofinite_iff_natAbs _).mp herr
      refine ⟨A + T, fun k hk => hw x k (fun i hi => hA (k + i) ?_)⟩
      have hb := Int.natAbs_sub_le (k + i) i
      simp only [add_sub_cancel_right] at hb
      omega
    refine ⟨ht, Metric.tendsto_nhds.mpr fun ε hε => ?_⟩
    have htail := (eventually_cofinite_iff_natAbs _).mpr (ht ε hε)
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using htail

#print axioms finite_window
#print axioms global_and_limit_shadowing

end D5.S1.Dynamics.Shadowing.CompactSelector
