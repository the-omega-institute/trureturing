/- GID: D5/S3/Analytic/GoldenTomography/PronyAbsoluteTargetStability
   generality: I
   mirror-B: D5/B/S3/Analytic/GoldenTomography/PronyAbsoluteTargetStability
   mirror-E: none(waiver:unbounded-absolute-target-error-bound)
   anchors: []
   utility: none
   digest: A contractive finite moment prefix controls the absolute error of the entire target sequence. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Analytic.GoldenTomography.PronyAbsoluteTargetStability

open FinitePronyHankelReconstruction

private def tailGain (theta : Real) : Nat → Real
  | 0 => 0
  | d + 1 => (theta + (1 + theta) * tailGain theta d) / (1 - theta)

/-- Only the tail is propagated. The initial block is kept at its measured bound.
The argument concerns finite sums, so summability is not presumed. -/
private theorem tail_bound (theta : Real) (ht0 : 0 ≤ theta) (ht1 : theta < 1) :
    ∀ d : Nat, ∀ nodes weights : Fin d → Real, ∀ epsilon : Real,
      0 ≤ epsilon → (∀ j, |nodes j| ≤ theta) →
      (∀ k : Nat, k < d → |pronyMoment nodes weights k| ≤ epsilon) →
      ∀ N : Nat,
        (∑ k ∈ Finset.range N, |pronyMoment nodes weights (d + k)|) ≤
          tailGain theta d * epsilon := by
  intro d
  induction d with
  | zero =>
      intro nodes weights epsilon he hn hp N
      simp [pronyMoment, tailGain]
  | succ d ih =>
      intro nodes weights epsilon he hn hp N
      let ns : Fin d → Real := fun j => nodes j.succ
      let ws : Fin d → Real := fun j => weights j.succ * (nodes j.succ - nodes 0)
      let f : Nat → Real := pronyMoment nodes weights
      let v : Nat → Real := pronyMoment ns ws
      have hdef (n : Nat) : v n = f (n + 1) - nodes 0 * f n := by
        change pronyMoment ns ws n =
          pronyMoment nodes weights (n + 1) - nodes 0 * pronyMoment nodes weights n
        calc
          _ = ∑ j : Fin (d + 1), weights j * (nodes j - nodes 0) * nodes j ^ n := by
            rw [Fin.sum_univ_succ]
            simp [pronyMoment, ns, ws]
          _ = _ := by
            unfold pronyMoment
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            rw [pow_succ]
            ring
      have hns (j : Fin d) : |ns j| ≤ theta := hn j.succ
      have hvprefix (k : Nat) (hk : k < d) : |v k| ≤ (1 + theta) * epsilon := by
        rw [hdef]
        calc
          _ ≤ |f (k + 1)| + |nodes 0 * f k| := by
            simpa using (abs_sub_le (f (k + 1)) 0 (nodes 0 * f k))
          _ = |f (k + 1)| + |nodes 0| * |f k| := by rw [abs_mul]
          _ ≤ epsilon + theta * epsilon :=
            add_le_add (hp (k + 1) (by omega))
              (mul_le_mul (hn 0) (hp k (by omega)) (abs_nonneg _) ht0)
          _ = (1 + theta) * epsilon := by ring
      have he' : 0 ≤ (1 + theta) * epsilon :=
        mul_nonneg (by linarith) he
      have hv := ih ns ws ((1 + theta) * epsilon) he' hns hvprefix N
      let S : Real := ∑ k ∈ Finset.range N, |f (d + 1 + k)|
      let P : Real := ∑ k ∈ Finset.range N, |f (d + k)|
      have hshift (N : Nat) :
          (∑ k ∈ Finset.range N, |f (d + k)|) + |f (d + N)| =
            |f d| + ∑ k ∈ Finset.range N, |f (d + 1 + k)| := by
        induction N with
        | zero => simp
        | succ N ihN =>
            simp only [Finset.sum_range_succ]
            have hi : d + 1 + N = d + (N + 1) := by omega
            rw [hi]
            linarith
      have hs := hshift N
      have hfd : |f d| ≤ epsilon := hp d (by omega)
      have hlast : 0 ≤ |f (d + N)| := abs_nonneg _
      have hPS : P ≤ epsilon + S := by
        dsimp [P, S]
        linarith
      have hstep : S ≤ theta * P + ∑ k ∈ Finset.range N, |v (d + k)| := by
        dsimp [S, P]
        calc
          _ ≤ ∑ k ∈ Finset.range N, (theta * |f (d + k)| + |v (d + k)|) := by
            apply Finset.sum_le_sum
            intro k _
            have hfstep : f (d + 1 + k) = nodes 0 * f (d + k) + v (d + k) := by
              have hh := hdef (d + k)
              have hi : d + 1 + k = (d + k) + 1 := by omega
              rw [hi]
              linarith
            rw [hfstep]
            calc
              _ ≤ |nodes 0 * f (d + k)| + |v (d + k)| := abs_add _ _
              _ = |nodes 0| * |f (d + k)| + |v (d + k)| := by rw [abs_mul]
              _ ≤ theta * |f (d + k)| + |v (d + k)| :=
                add_le_add_right (mul_le_mul_of_nonneg_right (hn 0) (abs_nonneg _)) _
          _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
      have hPS' := mul_le_mul_of_nonneg_left hPS ht0
      have hmain : (1 - theta) * S ≤
          (theta + (1 + theta) * tailGain theta d) * epsilon := by
        change (∑ k ∈ Finset.range N, |v (d + k)|) ≤
          tailGain theta d * ((1 + theta) * epsilon) at hv
        nlinarith
      have hd : 0 < 1 - theta := sub_pos.mpr ht1
      have hcancel : (1 - theta) * (tailGain theta (d + 1) * epsilon) =
          (theta + (1 + theta) * tailGain theta d) * epsilon := by
        have hdne : 1 - theta ≠ 0 := ne_of_gt hd
        simp only [tailGain]
        field_simp [hdne]
        <;> ring
      have hresult : S ≤ tailGain theta (d + 1) * epsilon := by
        apply (mul_le_mul_left hd).mp
        exact hmain.trans_eq hcancel.symm
      simpa only [S, f, Nat.succ_eq_add_one] using hresult

private theorem single_family_bound
    (theta : Real) (ht0 : 0 ≤ theta) (ht1 : theta < 1)
    (d : Nat) (nodes weights : Fin d → Real) (epsilon : Real)
    (he : 0 ≤ epsilon) (hn : ∀ j, |nodes j| ≤ theta)
    (hp : ∀ k : Nat, k < d → |pronyMoment nodes weights k| ≤ epsilon) :
    Summable (fun n => |pronyMoment nodes weights n|) ∧
      (∑' n : Nat, |pronyMoment nodes weights n|) ≤
        ((d : Real) + (((1 + theta) / (1 - theta)) ^ d - 1) / 2) * epsilon := by
  have hclosed (d : Nat) :
      tailGain theta d = (((1 + theta) / (1 - theta)) ^ d - 1) / 2 := by
    have hd : 1 - theta ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
    induction d with
    | zero => simp [tailGain]
    | succ d ih =>
        rw [tailGain, ih, pow_succ]
        field_simp [hd]
        <;> ring
  let f : Nat → Real := fun n => |pronyMoment nodes weights n|
  have hnonneg (n : Nat) : 0 ≤ f n := abs_nonneg _
  have hprefix : (∑ k ∈ Finset.range d, f k) ≤ (d : Real) * epsilon := by
    calc
      _ ≤ ∑ k ∈ Finset.range d, epsilon := by
        apply Finset.sum_le_sum
        intro k hk
        exact hp k (Finset.mem_range.mp hk)
      _ = _ := by simp
  have hfinite (N : Nat) : (∑ k ∈ Finset.range N, f k) ≤
      ((d : Real) + (((1 + theta) / (1 - theta)) ^ d - 1) / 2) * epsilon := by
    have htail := tail_bound theta ht0 ht1 d nodes weights epsilon he hn hp N
    have hextra : 0 ≤ ∑ k ∈ Finset.range d, f (N + k) :=
      Finset.sum_nonneg (fun k _ => hnonneg (N + k))
    have hcompare : (∑ k ∈ Finset.range N, f k) ≤
        ∑ k ∈ Finset.range (d + N), f k := by
      rw [show d + N = N + d by omega, Finset.sum_range_add]
      linarith
    calc
      _ ≤ ∑ k ∈ Finset.range (d + N), f k := hcompare
      _ = (∑ k ∈ Finset.range d, f k) + ∑ k ∈ Finset.range N, f (d + k) := by
        rw [Finset.sum_range_add]
      _ ≤ (d : Real) * epsilon + tailGain theta d * epsilon :=
        add_le_add hprefix htail
      _ = _ := by rw [hclosed]; ring
  exact ⟨summable_of_sum_range_le hnonneg hfinite,
    Real.tsum_le_of_sum_range_le hnonneg hfinite⟩

/-- Absolute target recovery from a finite noisy moment prefix.
The two families may have signed or zero weights, repeated nodes, or arbitrarily
close nodes. There is no recovery claim about individual nodes or hidden coordinates.
The constant is independent of the time horizon, but depends on the total mode
budget and on the strict contraction gap. The zero-mode case is included. -/
theorem prony_target_absolute_error_bound
    {d e : Nat} (nodes weights : Fin d → Real) (otherNodes otherWeights : Fin e → Real)
    (theta epsilon : Real) (ht0 : 0 ≤ theta) (ht1 : theta < 1) (he : 0 ≤ epsilon)
    (hn : ∀ j, |nodes j| ≤ theta) (hm : ∀ j, |otherNodes j| ≤ theta)
    (hp : ∀ k : Nat, k < d + e →
      |pronyMoment nodes weights k - pronyMoment otherNodes otherWeights k| ≤ epsilon) :
    Summable (fun n => |pronyMoment nodes weights n - pronyMoment otherNodes otherWeights n|) ∧
      (∑' n : Nat, |pronyMoment nodes weights n - pronyMoment otherNodes otherWeights n|) ≤
        (((d + e : Nat) : Real) +
          (((1 + theta) / (1 - theta)) ^ (d + e) - 1) / 2) * epsilon := by
  let ns : Fin (d + e) → Real := Fin.addCases nodes otherNodes
  let ws : Fin (d + e) → Real := Fin.addCases weights (fun j => -otherWeights j)
  have hmoment (k : Nat) : pronyMoment ns ws k =
      pronyMoment nodes weights k - pronyMoment otherNodes otherWeights k := by
    simp [pronyMoment, ns, ws, Fin.sum_univ_add, sub_eq_add_neg,
      Finset.sum_neg_distrib]
  have hns : ∀ j, |ns j| ≤ theta := by
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simpa [ns] using hn i
    · intro i
      simpa [ns] using hm i
  have hp' : ∀ k : Nat, k < d + e → |pronyMoment ns ws k| ≤ epsilon := by
    intro k hk
    rw [hmoment]
    exact hp k hk
  have result := single_family_bound theta ht0 ht1 (d + e) ns ws epsilon he hns hp'
  simpa only [hmoment] using result

#print axioms prony_target_absolute_error_bound

end D5.S3.Analytic.GoldenTomography.PronyAbsoluteTargetStability
