/- GID: D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation
   generality: G
   mirror-B: D5/B/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Basic, mathlib/module/Mathlib.Data.Nat.Periodic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.claim; result=D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.result; claim=D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.claim
   digest: Exact periodic densities refute unimodality of the density of integers with one divisor in an interval. -/

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
  ∃! d, n < d ∧ d < m ∧ d ∣ N

private def intervalPeriod (n m : ℕ) : ℕ :=
  (Finset.Ioo n m).lcm id

/-- The natural density of integers having exactly one divisor in `(n, m)`, with junk value zero
if the density does not exist. The periodic-density theorem proves existence for every `n, m`. -/
def epsOne (n m : ℕ) : ℝ :=
  if h : ∃ delta, hasDensity {N | exactlyOneDivisorIn n m N} delta then h.choose else 0

/-- Weak unimodality on the natural-number tail beginning at `lo`. -/
def Unimodal (f : ℕ → ℝ) (lo : ℕ) : Prop :=
  ∃ m0, lo ≤ m0 ∧
    (∀ a b, lo ≤ a → a ≤ b → b ≤ m0 → f a ≤ f b) ∧
    (∀ a b, m0 ≤ a → a ≤ b → f b ≤ f a)

/-- Erdős's 1979 suggestion that, for every `n`, the density is unimodal as `m` ranges over
`m > n + 1`. -/
def claim : Prop :=
  ∀ n : ℕ, Unimodal (fun m => epsOne n m) (n + 2)

/-- The exact densities at `(n,m) = (2,6), (2,7), (2,8)` form a strict valley, refuting the
unimodality claim. -/
theorem result : ¬claim := by
  have hperiodPositive (n m : ℕ) : 0 < intervalPeriod n m := by
    apply Nat.pos_of_ne_zero
    rw [intervalPeriod, Finset.lcm_ne_zero_iff]
    intro d hd
    simp only [id_eq]
    have hdpos := (Finset.mem_Ioo.mp hd).1
    omega
  have hperiodic (n m : ℕ) :
      Periodic (fun N => exactlyOneDivisorIn n m N) (intervalPeriod n m) := by
    intro N
    apply propext
    constructor
    · rintro ⟨d, ⟨hdn, hdm, hdN⟩, hunique⟩
      have hdP : d ∣ intervalPeriod n m := by
        unfold intervalPeriod
        rcases Finset.dvd_lcm (α := ℕ) (f := id) (Finset.mem_Ioo.mpr ⟨hdn, hdm⟩) with ⟨k, hk⟩
        exact ⟨k, hk⟩
      refine ⟨d, ⟨hdn, hdm, (Nat.dvd_add_iff_left hdP).mpr hdN⟩, ?_⟩
      intro e he
      have heP : e ∣ intervalPeriod n m := by
        unfold intervalPeriod
        rcases Finset.dvd_lcm (α := ℕ) (f := id)
            (Finset.mem_Ioo.mpr ⟨he.1, he.2.1⟩) with ⟨k, hk⟩
        exact ⟨k, hk⟩
      exact hunique e ⟨he.1, he.2.1, (Nat.dvd_add_iff_left heP).mp he.2.2⟩
    · rintro ⟨d, ⟨hdn, hdm, hdN⟩, hunique⟩
      have hdP : d ∣ intervalPeriod n m := by
        unfold intervalPeriod
        rcases Finset.dvd_lcm (α := ℕ) (f := id) (Finset.mem_Ioo.mpr ⟨hdn, hdm⟩) with ⟨k, hk⟩
        exact ⟨k, hk⟩
      refine ⟨d, ⟨hdn, hdm, (Nat.dvd_add_iff_left hdP).mp hdN⟩, ?_⟩
      intro e he
      have heP : e ∣ intervalPeriod n m := by
        unfold intervalPeriod
        rcases Finset.dvd_lcm (α := ℕ) (f := id)
            (Finset.mem_Ioo.mpr ⟨he.1, he.2.1⟩) with ⟨k, hk⟩
        exact ⟨k, hk⟩
      exact hunique e ⟨he.1, he.2.1, (Nat.dvd_add_iff_left heP).mpr he.2.2⟩
  have hperiodDensity (n m : ℕ) :
      hasDensity {N | exactlyOneDivisorIn n m N}
        (((Finset.range (intervalPeriod n m)).filter
          (exactlyOneDivisorIn n m)).card / (intervalPeriod n m : ℝ)) := by
    simpa only [Set.mem_ofPred_eq] using
      hasDensity_of_periodic {N | exactlyOneDivisorIn n m N} (intervalPeriod n m)
        (hperiodPositive n m) (hperiodic n m)
  have heps (n m : ℕ) :
      epsOne n m =
        (((Finset.range (intervalPeriod n m)).filter
          (exactlyOneDivisorIn n m)).card / (intervalPeriod n m : ℝ)) := by
    have hdensity := hperiodDensity n m
    rw [epsOne, dif_pos ⟨_, hdensity⟩]
    exact tendsto_nhds_unique (Exists.choose_spec ⟨_, hdensity⟩) hdensity
  have hexact (n m N : ℕ) :
      exactlyOneDivisorIn n m N ↔
        ((Finset.Ioo n m).filter fun d => d ∣ N).card = 1 := by
    simp only [exactlyOneDivisorIn, Finset.card_eq_one_iff_existsUnique,
      Finset.mem_filter, Finset.mem_Ioo, and_assoc]
  have h6 : epsOne 2 6 = 13 / 30 := by
    rw [heps]
    have hP6 : intervalPeriod 2 6 = 60 := by decide
    have hc6 : ((Finset.range 60).filter (exactlyOneDivisorIn 2 6)).card = 26 := by
      rw [Finset.filter_congr fun N _ => hexact 2 6 N]
      decide
    rw [hP6, hc6]
    norm_num
  have h7 : epsOne 2 7 = 11 / 30 := by
    rw [heps]
    have hP7 : intervalPeriod 2 7 = 60 := by decide
    have hc7 : ((Finset.range 60).filter (exactlyOneDivisorIn 2 7)).card = 22 := by
      rw [Finset.filter_congr fun N _ => hexact 2 7 N]
      decide
    rw [hP7, hc7]
    norm_num
  have h8 : epsOne 2 8 = 13 / 35 := by
    rw [heps]
    have hP8 : intervalPeriod 2 8 = 420 := by decide
    have hc8 : ((Finset.range 420).filter (exactlyOneDivisorIn 2 8)).card = 156 := by
      rw [Finset.filter_congr fun N _ => hexact 2 8 N]
      set_option maxRecDepth 100000 in decide
    rw [hP8, hc8]
    norm_num
  intro hclaim
  obtain ⟨m0, _, hincreasing, hdecreasing⟩ := hclaim 2
  by_cases hpeak : 7 ≤ m0
  · have h67 := hincreasing 6 7 (by norm_num) (by norm_num) hpeak
    change epsOne 2 6 ≤ epsOne 2 7 at h67
    rw [h6, h7] at h67
    norm_num at h67
  · have hm0 : m0 ≤ 7 := by omega
    have h78 := hdecreasing 7 8 hm0 (by norm_num)
    change epsOne 2 8 ≤ epsOne 2 7 at h78
    rw [h7, h8] at h78
    norm_num at h78

#print axioms hasDensity_of_periodic
#print axioms result

end

end D5.S3.Arith.Density.ErdosExactlyOneDivisorUnimodalityRefutation
