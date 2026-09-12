/- GID: D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation
   generality: G
   mirror-B: D5/B/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.claim; result=D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.result; claim=D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.claim
   digest: Exact densities refute unimodality for integers with one divisor in an interval. -/

import D5.S3.ObserverMemory.Prediction.EventualCycleAverage

namespace D5.S3.Arith.Density.ErdosExactlyOneDivisorUnimodalityRefutation

open Filter Function Set Topology
open scoped Classical Fin.NatCast

noncomputable section

/-- A set of natural numbers has density `delta` when its proportion in `[0, N)` tends to
`delta`. Including zero does not change the natural density. -/
def hasDensity (A : Set ℕ) (delta : ℝ) : Prop :=
  by
    classical
    exact Tendsto
      (fun (N : ℕ) => (((Finset.range N).filter fun k => k ∈ A).card : ℝ) / (N : ℝ))
      atTop (nhds delta)

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

/-- A strict valley after `lo` is incompatible with weak unimodality on that tail. -/
theorem not_unimodal_of_valley (f : ℕ → ℝ) (lo a b c : ℕ) (hla : lo ≤ a)
    (hab : a < b) (hbc : b < c) (hba : f b < f a) (hbc' : f b < f c) :
    ¬ Unimodal f lo := by
  rintro ⟨m0, _, hincreasing, hdecreasing⟩
  by_cases hm0 : m0 ≤ b
  · exact (not_lt_of_ge (hdecreasing b c hm0 hbc.le)) hbc'
  · exact (not_lt_of_ge (hincreasing a b hla hab.le (Nat.lt_of_not_ge hm0).le)) hba

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
    let P := intervalPeriod n m
    let A : Set ℕ := {N | exactlyOneDivisorIn n m N}
    let value : Fin P → ℝ := fun j => if (j : ℕ) ∈ A then 1 else 0
    have hP : 0 < P := hperiodPositive n m
    letI : NeZero P := ⟨Nat.ne_of_gt hP⟩
    have hiterate (t : ℕ) :
        ((fun x : Fin P => x + 1)^[t]) 0 = (t : Fin P) := by
      induction t with
      | zero => rfl
      | succ t ih =>
          rw [Function.iterate_succ_apply', ih]
          rw [Nat.cast_succ]
    have hcycle (t : ℕ) :
        ((fun x : Fin P => x + 1)^[t]) 0 =
          id (Fin.mk (t % P) (Nat.mod_lt t hP)) := by
      rw [hiterate]
      rfl
    have havg :=
      D5.S3.ObserverMemory.Prediction.EventualCycleAverage.eventual_cycle_average
        (fun x : Fin P => x + 1) value (0 : Fin P) hP id 0 (by
          intro t
          simpa using hcycle t)
    have hmembership (t : ℕ) : t ∈ A ↔ (t % P) ∈ A := by
      have hp : Periodic (fun N => N ∈ A) P := by
        simpa [A, P] using hperiodic n m
      simpa [Nat.mod_add_div t P, Nat.add_comm, Nat.mul_comm, Nat.nsmul_eq_mul] using
        hp.nsmul (t / P) (t % P)
    have hnormalization (N : ℕ) :
        (((Finset.range N).filter fun t => t ∈ A).card : ℝ) =
          ∑ t ∈ Finset.range N, value (t : Fin P) := by
      calc
        (((Finset.range N).filter fun t => t ∈ A).card : ℝ) =
            ∑ t ∈ Finset.range N, if t ∈ A then (1 : ℝ) else 0 := by simp
        _ = ∑ t ∈ Finset.range N,
              if ((t : Fin P) : ℕ) ∈ A then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro t _
            simp only [Fin.val_natCast, hmembership t]
        _ = ∑ t ∈ Finset.range N, value (t : Fin P) := by rfl
    have hperiodNormalization :
        (∑ j : Fin P, value j) =
          (((Finset.range P).filter fun t => t ∈ A).card : ℝ) := by
      have h := Fin.sum_univ_eq_sum_range
        (fun t : ℕ => value (t : Fin P)) P
      rw [hnormalization]
      simpa [Fin.cast_val_eq_self] using h
    simp only [hiterate, id_eq] at havg
    have hprefix :
        (fun N : ℕ => (∑ t ∈ Finset.range N, value (t : Fin P)) / (N : ℝ)) =
          (fun N : ℕ =>
            (((Finset.range N).filter fun t => t ∈ A).card : ℝ) / (N : ℝ)) := by
      funext N
      rw [hnormalization]
    rw [hprefix] at havg
    rw [hperiodNormalization] at havg
    simpa [hasDensity, A, P] using havg
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
  have hvalley := not_unimodal_of_valley (fun m => epsOne 2 m) 4 6 7 8
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [h6, h7]; norm_num) (by rw [h7, h8]; norm_num)
  exact hvalley (hclaim 2)

#print axioms not_unimodal_of_valley
#print axioms result

end

end D5.S3.Arith.Density.ErdosExactlyOneDivisorUnimodalityRefutation
