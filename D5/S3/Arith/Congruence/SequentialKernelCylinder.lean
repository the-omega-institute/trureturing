/- GID: D5/S3/Arith/Congruence/SequentialKernelCylinder
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/SequentialKernelCylinder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj]
   utility: none
   digest: History-dependent Markov kernels multiply only selected coordinate cylinder caps. -/

import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
The actual trajectory law is Mathlib's `lmarginalPartialTraj`; normalization
and preservation of prefix observables are supplied by its Markov kernels.
The new deduction eliminates an arbitrary finite selected set of coordinates.
Unselected coordinates use `DependsOn.lmarginalPartialTraj_of_le` directly.
No independence, joint-cylinder cap, or prefix-preservation hypothesis is used.

Search result: repository trajectory, weighted-product and cylinder modules,
pinned Mathlib IonescuTulcea, LeanSearch and public Lean code search supplied
prefix marginal preservation but no matching selected-cylinder product bound.
This is a general measure inequality; it has no computational-instance content.
The Erdős 7 local-kernel argument uses it at fixed head coordinates before
averaging pairs of actual residue layouts.
-/

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Finset
open scoped ENNReal

namespace D5.S3.Arith.Congruence.SequentialKernelCylinder

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Selected cylinders under the actual history-dependent trajectory kernel incur
only their selected one-step caps, without any independence assumption. -/
theorem selected_cylinder_bound
    {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)]
    (E : (i : ℕ) → Set (X i)) (hE : ∀ i, MeasurableSet (E i))
    (c : ℕ → ℝ≥0∞) (a b : ℕ) (hab : a ≤ b) (s : Finset ℕ)
    (hs : s ⊆ Finset.Ioc a b)
    (hcap : ∀ n, n + 1 ∈ s → ∀ z, κ n z (E (n + 1)) ≤ c (n + 1))
    (x₀ : (i : ℕ) → X i) :
    lmarginalPartialTraj κ a b
      (fun x => ∏ i ∈ s, (E i).indicator (fun _ => (1 : ℝ≥0∞)) (x i)) x₀ ≤
      ∏ i ∈ s, c i := by
  classical
  let F (t : Finset ℕ) (x : (i : ℕ) → X i) : ℝ≥0∞ :=
    ∏ i ∈ t, (E i).indicator (fun _ => (1 : ℝ≥0∞)) (x i)
  have hF (t : Finset ℕ) : Measurable (F t) := by
    apply Finset.measurable_prod
    intro i hi
    exact (measurable_const.indicator (hE i)).comp (measurable_pi_apply i)
  change lmarginalPartialTraj κ a b (F s) x₀ ≤ ∏ i ∈ s, c i
  induction b, hab using Nat.le_induction generalizing s with
  | base =>
      have empty : s = ∅ := by simpa using hs
      subst s
      simp only [F, Finset.prod_empty]
      rw [lmarginalPartialTraj_le κ le_rfl measurable_const]
  | succ b hab ih =>
      let t := s.erase (b + 1)
      have hts : t ⊆ Finset.Ioc a b := by
        intro i hi
        obtain ⟨hne, his⟩ := Finset.mem_erase.mp hi
        obtain ⟨hai, hib⟩ := Finset.mem_Ioc.mp (hs his)
        exact Finset.mem_Ioc.mpr ⟨hai, by omega⟩
      have htc : ∀ n, n + 1 ∈ t → ∀ z, κ n z (E (n + 1)) ≤ c (n + 1) :=
        fun n hn => hcap n (Finset.mem_of_mem_erase hn)
      have iht := ih t hts htc
      have hdep : DependsOn (F t) (Finset.Iic b) := by
        intro x y hxy
        apply Finset.prod_congr rfl
        intro i hi
        rw [hxy i (Finset.mem_Iic.mpr (Finset.mem_Ioc.mp (hts hi)).2)]
      rw [← lmarginalPartialTraj_self hab b.le_succ (hF s)]
      by_cases hlast : b + 1 ∈ s
      · have split (x : (i : ℕ) → X i) :
            F s x = F t x * (E (b + 1)).indicator (fun _ => (1 : ℝ≥0∞)) (x (b + 1)) := by
          exact (Finset.prod_erase_mul _ _ hlast).symm
        have unchanged (x : (i : ℕ) → X i) (z : X (b + 1)) :
            F t (Function.update x (b + 1) z) = F t x := by
          apply hdep
          intro i hi
          apply Function.update_of_ne
          have hib := Finset.mem_Iic.mp hi
          omega
        have step (x : (i : ℕ) → X i) :
            lmarginalPartialTraj κ b (b + 1) (F s) x ≤ F t x * c (b + 1) := by
          rw [lmarginalPartialTraj_succ b (hF s)]
          simp_rw [split, unchanged, Function.update_self]
          rw [lintegral_const_mul _ (measurable_const.indicator (hE (b + 1)))]
          change F t x * (∫⁻ z, (E (b + 1)).indicator 1 z ∂κ b (Preorder.frestrictLe b x)) ≤ _
          rw [lintegral_indicator_one (hE (b + 1))]
          exact mul_le_mul' le_rfl (hcap b hlast _)
        calc
          _ ≤ lmarginalPartialTraj κ a b (fun x => F t x * c (b + 1)) x₀ :=
            lmarginalPartialTraj_mono a b step x₀
          _ = lmarginalPartialTraj κ a b (F t) x₀ * c (b + 1) := by
            unfold lmarginalPartialTraj
            exact lintegral_mul_const _ ((hF t).comp measurable_updateFinset)
          _ ≤ (∏ i ∈ t, c i) * c (b + 1) := mul_le_mul' iht le_rfl
          _ = ∏ i ∈ s, c i := Finset.prod_erase_mul _ _ hlast
      · have eqt : t = s := Finset.erase_eq_of_notMem hlast
        rw [← eqt, hdep.lmarginalPartialTraj_of_le (b + 1) (hF t) le_rfl]
        exact iht

#print axioms selected_cylinder_bound

end D5.S3.Arith.Congruence.SequentialKernelCylinder
