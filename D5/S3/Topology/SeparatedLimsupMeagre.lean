/- GID: D5/S3/Topology/SeparatedLimsupMeagre
   generality: G
   mirror-B: D5/B/S3/Topology/SeparatedLimsupMeagre
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Distinct real limsups on dense sets force a meagre convergence locus. -/

module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic.Linarith

/-!
# Separated dense limsup classes

The fixed-gap closed-tail argument extends the category mechanism of Carvalho and
Varandas, *Genericity of historic behavior for maps and flows*, arXiv:2107.01200v1,
Theorem A, to arbitrary sequences of continuous real functions on topological spaces.
The real limsup has its usual conditionally complete default semantics. No global
boundedness assumption, metrizability of the domain, or Baire assumption is used.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter
open scoped Topology

universe u

/-- Distinct constant real limsups on two dense sets make the convergence locus
meagre. The function sequence need not be bounded, and the domain need not be Baire. -/
theorem separated_limsup_isMeagre {X : Type u} [TopologicalSpace X]
    (U : ℕ → X → ℝ) (hU : ∀ n, Continuous (U n))
    (A B : Set X) (hA : Dense A) (hB : Dense B) (a b : ℝ) (hab : a ≠ b)
    (ha : ∀ x ∈ A, Filter.limsup (fun n => U n x) atTop = a)
    (hb : ∀ x ∈ B, Filter.limsup (fun n => U n x) atTop = b) :
    IsMeagre {x | ∃ L : ℝ, Tendsto (fun n => U n x) atTop (𝓝 L)} := by
  let ε : ℝ := |a - b| / 4
  have hε : 0 < ε := div_pos (abs_pos.mpr (sub_ne_zero.mpr hab)) (by norm_num)
  let E : ℕ → Set X := fun N => {x | ∀ n, N ≤ n → |U n x - U N x| ≤ ε}
  have hclosed (N : ℕ) : IsClosed (E N) := by
    simp only [E, setOf_forall]
    exact isClosed_iInter fun n => isClosed_iInter fun _ =>
      isClosed_le ((hU n).sub (hU N)).abs continuous_const
  have hnd (N : ℕ) : IsNowhereDense (E N) := by
    rw [(hclosed N).isNowhereDense_iff]
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hvalue (S : Set X) (hS : Dense S) (c : ℝ)
        (hc : ∀ y ∈ S, Filter.limsup (fun n => U n y) atTop = c) :
        |c - U N x| ≤ ε := by
      have hsub : S ∩ interior (E N) ⊆ {y | |c - U N y| ≤ ε} := by
        intro y hy
        have htail := interior_subset hy.2
        have hlo : ∀ᶠ n in atTop, U N y - ε ≤ U n y := by
          filter_upwards [eventually_ge_atTop N] with n hn
          have := (abs_le.mp (htail n hn)).1
          linarith
        have hhi : ∀ᶠ n in atTop, U n y ≤ U N y + ε := by
          filter_upwards [eventually_ge_atTop N] with n hn
          have := (abs_le.mp (htail n hn)).2
          linarith
        have hl := le_limsup_of_frequently_le hlo.frequently
          (isBoundedUnder_of_eventually_le hhi)
        have hu := limsup_le_of_le (isCoboundedUnder_le_of_eventually_le atTop hlo) hhi
        rw [hc y hy.1] at hl hu
        change |c - U N y| ≤ ε
        rw [abs_le]
        constructor <;> linarith only [hl, hu]
      exact closure_minimal hsub
        (isClosed_le (continuous_const.sub (hU N)).abs continuous_const)
        (isOpen_interior.closure_inter ⟨hS x, hx⟩)
    have hax := abs_le.mp (hvalue A hA a ha)
    have hbx := abs_le.mp (hvalue B hB b hb)
    have hgap : |a - b| ≤ 2 * ε := abs_le.mpr ⟨by linarith, by linarith⟩
    dsimp [ε] at hgap hε
    linarith
  apply (isMeagre_iUnion fun N => (hnd N).isMeagre).mono
  rintro x ⟨L, hL⟩
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hL.cauchySeq ε hε
  exact mem_iUnion.mpr ⟨N, fun n hn => (by
    simpa only [Real.dist_eq] using (hN n hn).le)⟩
