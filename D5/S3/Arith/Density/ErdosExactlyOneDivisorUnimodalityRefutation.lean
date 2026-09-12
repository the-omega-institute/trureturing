/- GID: D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation
   generality: G
   mirror-B: D5/B/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.GCDMonoid.Finset, mathlib/module/Mathlib.Analysis.SpecificLimits.Basic, mathlib/module/Mathlib.Data.Nat.Periodic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.claim; result=D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.result; claim=D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.claim
   digest: Exact periodic densities refute unimodality of the density of integers with one divisor in an interval. -/

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Periodic

namespace D5.S3.Arith.Density.ErdosExactlyOneDivisorUnimodalityRefutation

open Filter Function Set Topology
open scoped Classical

noncomputable section

/-- A set of natural numbers has density `delta` when its proportion in `[0, N)` tends to
`delta`. Including zero does not change the natural density. -/
def hasDensity (A : Set ℕ) (delta : ℝ) : Prop :=
  by
    classical
    exact Tendsto
      (fun (N : ℕ) => (((Finset.range N).filter fun k => k ∈ A).card : ℝ) / (N : ℝ))
      atTop (nhds delta)

/-- Every set with a positive period has natural density equal to the fraction of one period
that it occupies. -/
theorem hasDensity_of_periodic (A : Set ℕ) (P : ℕ) (hP : 0 < P)
    (hperiodic : Periodic (fun k => k ∈ A) P) :
    hasDensity A
      (((Finset.range P).filter fun k => k ∈ A).card / (P : ℝ)) := by
  classical
  let p : ℕ → Prop := fun k => k ∈ A
  let c : ℕ := Nat.count p P
  have hp : Periodic p P := hperiodic
  have hfull : ∀ q : ℕ, Nat.count p (P * q) = q * c := by
    intro q
    induction q with
    | zero => simp [c]
    | succ q ih =>
        rw [Nat.mul_succ, Nat.count_add, ih]
        have hshift : (fun k => p (P * q + k)) = p := by
          funext k
          apply propext
          simpa [Nat.mul_comm, Nat.add_comm, Nat.nsmul_eq_mul] using hp.nsmul q k
        simp only [hshift]
        simp [c, Nat.add_mul]
  have hcount : ∀ N : ℕ,
      Nat.count p N = (N / P) * c + Nat.count p (N % P) := by
    intro N
    conv_lhs => rw [← Nat.mod_add_div N P]
    rw [Nat.count_add', hfull]
    have hshift : (fun k => p (k + P * (N / P))) = p := by
      funext k
      apply propext
      simpa [Nat.mul_comm, Nat.nsmul_eq_mul] using hp.nsmul (N / P) k
    simp only [hshift]
    exact Nat.add_comm _ _
  have hmod : Tendsto (fun N : ℕ => ((N % P : ℕ) : ℝ) / (N : ℝ)) atTop (nhds 0) :=
    tendsto_mod_div_atTop_nhds_zero_nat hP
  have hrem_nonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ ((Nat.count p (N % P) : ℕ) : ℝ) :=
    Eventually.of_forall fun _ => Nat.cast_nonneg _
  have hrem_bdd : ∀ᶠ N : ℕ in atTop,
      ((Nat.count p (N % P) : ℕ) : ℝ) ≤ (P : ℝ) :=
    Eventually.of_forall fun N => by
      exact_mod_cast (Nat.count_le p).trans (Nat.le_of_lt (Nat.mod_lt N hP))
  have hrem : Tendsto
      (fun N : ℕ => ((Nat.count p (N % P) : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds 0) :=
    tendsto_bdd_div_atTop_nhds_zero hrem_nonneg hrem_bdd tendsto_natCast_atTop_atTop
  have hlimit : Tendsto
      (fun N : ℕ =>
        (c : ℝ) / (P : ℝ) * (1 - ((N % P : ℕ) : ℝ) / (N : ℝ)) +
          ((Nat.count p (N % P) : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds ((c : ℝ) / (P : ℝ))) := by
    convert (tendsto_const_nhds.mul (tendsto_const_nhds.sub hmod)).add hrem using 1
    all_goals simp
  rw [hasDensity]
  rw [show (((Finset.range P).filter fun k => k ∈ A).card : ℝ) = (c : ℝ) by
    simp [c, p, Nat.count_eq_card_filter_range]]
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [show (((Finset.range N).filter fun k => k ∈ A).card : ℝ) =
      (Nat.count p N : ℝ) by simp [p, Nat.count_eq_card_filter_range], hcount N]
  push_cast
  have hNdecomp : (N : ℝ) = (N % P : ℕ) + (P : ℝ) * (N / P : ℕ) := by
    exact_mod_cast (Nat.mod_add_div N P).symm
  field_simp [Nat.ne_of_gt hP, Nat.ne_of_gt hN]
  nlinarith [hNdecomp]

/-- There is exactly one eligible divisor when precisely one member of the finite interval
`(n, m)` divides `N`. -/
def exactlyOneDivisorIn (n m N : ℕ) : Prop :=
  ∃! d : {d // d ∈ Finset.Ioo n m}, (d : ℕ) ∣ N

private def intervalPeriod (n m : ℕ) : ℕ :=
  (Finset.Ioo n m).lcm id

end

end D5.S3.Arith.Density.ErdosExactlyOneDivisorUnimodalityRefutation
