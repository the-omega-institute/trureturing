/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteClosedClassLimits
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteClosedClassLimits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Genuine periodic limits on every actual closed class of a finite stochastic matrix. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteCyclicBlocks
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing

open Finset Matrix Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteClosedClassLimits
open FiniteClosedClasses FiniteGenuinePeriods FiniteCyclicBlocks
noncomputable section
universe u
variable {X : Type u} [Fintype X] [DecidableEq X]
variable {P : Matrix X X ℝ} {C : ClosedClass P}

private theorem subtype_sum {S : Type u} [Fintype S] (q : S → Prop) [DecidablePred q]
    (f : S → ℝ) : (∑ x : {x // q x}, f x.val) = ∑ x : S, if q x then f x else 0 := by
  classical
  rw [← Finset.sum_subtype (p := q) (univ.filter q) (fun _ => by simp), sum_filter]

private theorem phase_row_sum (hP : P ∈ rowStochastic ℝ X) (K : ClassPeriods P C)
    (n : ℕ) (x : C.val) (j : ZMod (period (restriction P C.val) K.base)) :
    (∑ y : Phase K j, (restriction P C.val ^ n) x y.val) =
      if K.phase x + (n : ZMod (period (restriction P C.val) K.base)) = j then 1 else 0 := by
  classical
  have hS := actual_structure P hP
  have hs := (rowStochastic ℝ C.val).pow_mem (hS.class_stochastic C) n
  have hz (y : C.val) (hy : K.phase x + (n : ZMod (period (restriction P C.val) K.base)) ≠ K.phase y) :
      (restriction P C.val ^ n) x y = 0 := by
    apply le_antisymm _ (hs.1 x y)
    apply le_of_not_gt
    exact fun hp => hy (K.path_residue n x y ((hS.class_powers C n x y) ▸ hp))
  rw [subtype_sum (fun y : C.val => K.phase y = j)]
  split_ifs with he
  · rw [← sum_row_of_mem_rowStochastic hs x]
    apply sum_congr rfl
    intro y _
    by_cases hy : K.phase y = j
    · simp [hy]
    · simp [hy, hz y (by rw [he]; exact Ne.symm hy)]
  · apply sum_eq_zero
    intro y _
    by_cases hy : K.phase y = j
    · simp [hy, hz y (by rwa [hy])]
    · simp [hy]

private theorem stationary_power (hP : P ∈ rowStochastic ℝ X)
    (mu : C.val → ℝ) (hn : ∀ x, 0 ≤ mu x) (hm : ∑ x, mu x = 1)
    (ht : mu ᵥ* restriction P C.val = mu) (n : ℕ) :
    mu ᵥ* (restriction P C.val ^ n) = mu := by
  let : FiniteStochasticMixing.RowStochastic (restriction P C.val) :=
    ⟨fun x => ⟨(actual_structure P hP).class_stochastic C |>.1 x,
      sum_row_of_mem_rowStochastic ((actual_structure P hP).class_stochastic C) x⟩⟩
  let : FiniteStochasticMixing.StochasticVec mu := ⟨hn, hm⟩
  let : FiniteStochasticMixing.Stationary mu (restriction P C.val) := ⟨ht⟩
  exact (FiniteStochasticMixing.multi_step_stationary mu (restriction P C.val) n).stationary

private theorem phase_mass (hP : P ∈ rowStochastic ℝ X) (K : ClassPeriods P C)
    (mu : C.val → ℝ) (ht : mu ᵥ* restriction P C.val = mu) (hm : ∑ x, mu x = 1)
    (j : ZMod (period (restriction P C.val) K.base)) :
    ∑ y : Phase K j, mu y.val = 1 / (period (restriction P C.val) K.base : ℝ) := by
  classical
  let p := period (restriction P C.val) K.base
  let : NeZero p := ⟨ne_of_gt K.positive⟩
  let mass (j : ZMod p) : ℝ := ∑ y : Phase K j, mu y.val
  have step (j : ZMod p) : mass (j + 1) = mass j := by
    change (∑ y : Phase K (j + 1), mu y.val) = ∑ y : Phase K j, mu y.val
    conv_lhs => arg 2; ext y; rw [← ht]
    simp only [Matrix.vecMul, dotProduct]
    rw [sum_comm]
    simp_rw [← mul_sum]
    have he (x : C.val) : (∑ y : Phase K (j+1), restriction P C.val x y.val) =
        if K.phase x = j then 1 else 0 := by
      simpa only [pow_one, Nat.cast_one, add_right_cancel_iff] using phase_row_sum hP K 1 x (j+1)
    simp_rw [he, mul_ite, mul_one, mul_zero]
    exact (subtype_sum (fun x : C.val => K.phase x = j) mu).symm
  have all (n : ℕ) : mass (n : ZMod p) = mass 0 := by
    induction n with
    | zero => simp
    | succ n ih => simpa only [Nat.cast_add, Nat.cast_one] using (step n).trans ih
  have equal (j : ZMod p) : mass j = mass 0 := by
    simpa only [ZMod.natCast_zmod_val] using all j.val
  have total : ∑ j : ZMod p, mass j = 1 := by
    simp only [mass, subtype_sum]
    rw [sum_comm]
    simpa using hm
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt K.positive
  have he : (p : ℝ) * mass 0 = 1 := by
    simpa only [equal, sum_const, card_univ, ZMod.card, nsmul_eq_mul] using total
  have hf : mass 0 = 1 / (p : ℝ) := (eq_div_iff hp).mpr (by nlinarith [he])
  exact (equal j).trans hf

private theorem phase_stationary (hP : P ∈ rowStochastic ℝ X) (K : ClassPeriods P C)
    (mu : C.val → ℝ) (hn : ∀ x, 0 ≤ mu x) (hm : ∑ x, mu x = 1)
    (ht : mu ᵥ* restriction P C.val = mu)
    (j : ZMod (period (restriction P C.val) K.base)) :
    (fun y : Phase K j => (period (restriction P C.val) K.base : ℝ) * mu y.val) ᵥ* block K j =
      (fun y : Phase K j => (period (restriction P C.val) K.base : ℝ) * mu y.val) := by
  classical
  let p := period (restriction P C.val) K.base
  ext y
  change (∑ x : Phase K j, ((p : ℝ) * mu x.val) *
    (restriction P C.val ^ p) x.val y.val) = (p : ℝ) * mu y.val
  rw [show mu y.val = (mu ᵥ* (restriction P C.val ^ p)) y.val by
    rw [stationary_power hP mu hn hm ht]]
  simp only [Matrix.vecMul, dotProduct, mul_sum, mul_assoc]
  rw [subtype_sum (fun x : C.val => K.phase x = j)
    (fun x => (p : ℝ) * (mu x * (restriction P C.val ^ p) x y.val))]
  apply sum_congr rfl
  intro x _
  by_cases hx : K.phase x = j
  · simp [hx]
  · have hz : (restriction P C.val ^ p) x y.val = 0 := by
      apply le_antisymm _ (Matrix.pow_apply_nonneg ((actual_structure P hP).class_stochastic C).1 p x y.val)
      apply le_of_not_gt
      intro hp
      have he := K.path_residue p x y.val ((actual_structure P hP).class_powers C p x y.val ▸ hp)
      simp only [ZMod.natCast_self, add_zero, y.property] at he
      exact hx he
    simp [hx, hz]

private theorem phase_normalized (hP : P ∈ rowStochastic ℝ X) (K : ClassPeriods P C)
    (mu : C.val → ℝ) (ht : mu ᵥ* restriction P C.val = mu) (hm : ∑ x, mu x = 1)
    (j : ZMod (period (restriction P C.val) K.base)) :
    ∑ y : Phase K j, (period (restriction P C.val) K.base : ℝ) * mu y.val = 1 := by
  rw [← mul_sum, phase_mass hP K mu ht hm j]
  have hp : (period (restriction P C.val) K.base : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt K.positive
  field_simp

private theorem stationary_positive (hP : P ∈ rowStochastic ℝ X)
    (mu : C.val → ℝ) (hn : ∀ x, 0 ≤ mu x) (hm : ∑ x, mu x = 1)
    (ht : mu ᵥ* restriction P C.val = mu) (y : C.val) : 0 < mu y := by
  have hi := (actual_structure P hP).class_irreducible C
  obtain ⟨x, _, hx⟩ := (sum_pos_iff_of_nonneg (fun x _ => hn x)).mp (by rw [hm]; norm_num)
  obtain ⟨n, _, hxy⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hi.nonneg).mp hi x y
  rw [← stationary_power hP mu hn hm ht n]
  change 0 < ∑ z, mu z * (restriction P C.val ^ n) z y
  exact (sum_pos_iff_of_nonneg (fun z _ => mul_nonneg (hn z)
    (Matrix.pow_apply_nonneg hi.nonneg n z y))).mpr ⟨x, mem_univ _, mul_pos hx hxy⟩

private theorem conditional_limit (hP : P ∈ rowStochastic ℝ X) (K : ClassPeriods P C)
    (hB : Blocks K) (mu : C.val → ℝ) (hn : ∀ x, 0 ≤ mu x) (hm : ∑ x, mu x = 1)
    (ht : mu ᵥ* restriction P C.val = mu)
    (j : ZMod (period (restriction P C.val) K.base)) :
    Tendsto (fun n : ℕ => block K j ^ n) atTop
      (𝓝 (fun _ y : Phase K j => (period (restriction P C.val) K.base : ℝ) * mu y.val)) := by
  let : Nonempty (Phase K j) := hB.nonempty j
  obtain ⟨v, _, _, _, hu, hv⟩ := FiniteStochasticMixing.primitive_convergence
    (block K j) (hB.stochastic j) (hB.primitive j)
  have he := hu (fun y : Phase K j => (period (restriction P C.val) K.base : ℝ) * mu y.val)
    (fun y => mul_nonneg (Nat.cast_nonneg _) (hn y.val))
    (phase_normalized hP K mu ht hm j) (phase_stationary hP K mu hn hm ht j)
  simpa only [← he] using hv

private theorem stationary_unique (hP : P ∈ rowStochastic ℝ X) (K : ClassPeriods P C)
    (hB : Blocks K) (mu : C.val → ℝ) (hn : ∀ x, 0 ≤ mu x) (hm : ∑ x, mu x = 1)
    (ht : mu ᵥ* restriction P C.val = mu)
    (nu : C.val → ℝ) (hnu : ∀ x, 0 ≤ nu x) (hns : ∑ x, nu x = 1)
    (hnt : nu ᵥ* restriction P C.val = nu) : nu = mu := by
  ext y
  let j := K.phase y
  let : Nonempty (Phase K j) := hB.nonempty j
  obtain ⟨v, _, _, _, hu, _⟩ := FiniteStochasticMixing.primitive_convergence
    (block K j) (hB.stochastic j) (hB.primitive j)
  have hmuv := hu (fun y : Phase K j => (period (restriction P C.val) K.base : ℝ) * mu y.val)
    (fun y => mul_nonneg (Nat.cast_nonneg _) (hn y.val))
    (phase_normalized hP K mu ht hm j) (phase_stationary hP K mu hn hm ht j)
  have hnuv := hu (fun y : Phase K j => (period (restriction P C.val) K.base : ℝ) * nu y.val)
    (fun y => mul_nonneg (Nat.cast_nonneg _) (hnu y.val))
    (phase_normalized hP K nu hnt hns j) (phase_stationary hP K nu hnu hns hnt j)
  have he := congrFun (hnuv.trans hmuv.symm) (⟨y, rfl⟩ : Phase K j)
  have hp : (period (restriction P C.val) K.base : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt K.positive
  exact (mul_left_cancel₀ hp) he

private theorem residue_limit (hP : P ∈ rowStochastic ℝ X) (K : ClassPeriods P C)
    (hB : Blocks K) (mu : C.val → ℝ) (hn : ∀ x, 0 ≤ mu x) (hm : ∑ x, mu x = 1)
    (ht : mu ᵥ* restriction P C.val = mu) (d : ℕ) (hd : 0 < d)
    (hpd : period (restriction P C.val) K.base ∣ d) (i : ℕ) (x y : C.val) :
    Tendsto (fun n : ℕ => (P ^ (d * n + i)) x.val y.val) atTop
      (𝓝 (if K.phase x + (i : ZMod (period (restriction P C.val) K.base)) = K.phase y
        then (period (restriction P C.val) K.base : ℝ) * mu y else 0)) := by
  classical
  let p := period (restriction P C.val) K.base
  let j := K.phase y
  let yy : Phase K j := ⟨y, rfl⟩
  obtain ⟨q, hqeq⟩ := hpd
  have hq : 0 < q := by nlinarith [K.positive]
  have hqtop : Tendsto (fun n : ℕ => q * n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hq) tendsto_id
  have hlimit := (conditional_limit hP K hB mu hn hm ht j).comp hqtop
  have he (n : ℕ) : (P ^ (d * n + i)) x.val y.val =
      ∑ k : Phase K j, (restriction P C.val ^ i) x k.val * (block K j ^ (q * n)) k yy := by
    have hS := actual_structure P hP
    rw [← hS.class_powers C]
    have hexp : d * n + i = i + p * (q * n) := by rw [hqeq]; ring
    rw [hexp, pow_add, Matrix.mul_apply]
    have hk (k : Phase K j) : (block K j ^ (q*n)) k yy =
        (restriction P C.val ^ (p * (q*n))) k.val y :=
      (hB.powers j (q*n) k yy).trans (hS.class_powers C _ k.val y).symm
    simp_rw [hk]
    rw [subtype_sum (fun k : C.val => K.phase k = j)
      (fun k => (restriction P C.val ^ i) x k * (restriction P C.val ^ (p * (q*n))) k y)]
    apply sum_congr rfl
    intro k _
    by_cases hkj : K.phase k = j
    · simp [hkj]
    · have hz : (restriction P C.val ^ (p * (q*n))) k y = 0 := by
        apply le_antisymm _ (Matrix.pow_apply_nonneg (hS.class_stochastic C).1 _ k y)
        apply le_of_not_gt
        intro hp
        have hem := K.path_residue (p*(q*n)) k y ((hS.class_powers C _ k y) ▸ hp)
        simp only [Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero] at hem
        exact hkj hem
      simp [hkj, hz]
  have hs : Tendsto
      (fun n : ℕ => ∑ k : Phase K j, (restriction P C.val ^ i) x k.val *
        (block K j ^ (q*n)) k yy) atTop
      (𝓝 (∑ k : Phase K j, (restriction P C.val ^ i) x k.val * ((p : ℝ) * mu y))) :=
    tendsto_finsetSum _ fun k _ =>
      ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlimit k)) yy).const_mul _
  have hsum : (∑ k : Phase K j, (restriction P C.val ^ i) x k.val * ((p : ℝ) * mu y)) =
      if K.phase x + (i : ZMod p) = K.phase y then (p : ℝ) * mu y else 0 := by
    rw [← sum_mul, phase_row_sum hP K i x j]
    split_ifs <;> simp
  rw [hsum] at hs
  exact hs.congr (fun n => (he n).symm)

/-- A stationary row and all actual ambient subsequence limits for the genuine cyclic phases. -/
structure ClassLimit (K : ClassPeriods P C) where
  stationaryRow : C.val → ℝ
  nonnegative : ∀ y, 0 ≤ stationaryRow y
  normalized : ∑ y, stationaryRow y = 1
  stationary : stationaryRow ᵥ* restriction P C.val = stationaryRow
  unique : ∀ nu : C.val → ℝ, (∀ y, 0 ≤ nu y) → (∑ y, nu y = 1) →
    nu ᵥ* restriction P C.val = nu → nu = stationaryRow
  positive : ∀ y, 0 < stationaryRow y
  phase_mass : ∀ j : ZMod (period (restriction P C.val) K.base),
    ∑ y : Phase K j, stationaryRow y.val = 1 / (period (restriction P C.val) K.base : ℝ)
  convergence : ∀ (d : ℕ), 0 < d → period (restriction P C.val) K.base ∣ d →
    ∀ (i : ℕ) (x y : C.val),
    Tendsto (fun n : ℕ => (P ^ (d * n + i)) x.val y.val) atTop
      (𝓝 (if K.phase x + (i : ZMod (period (restriction P C.val) K.base)) = K.phase y
        then (period (restriction P C.val) K.base : ℝ) * stationaryRow y else 0))

/-- Every actual closed class has its strictly positive unique stationary row and actual phase limits. -/
theorem actual_limits (P : Matrix X X ℝ) (hP : P ∈ rowStochastic ℝ X)
    (C : ClosedClass P) : ∃ K : ClassPeriods P C, Blocks K ∧ Nonempty (ClassLimit K) := by
  classical
  obtain ⟨K, hB⟩ := actual_blocks P hP C
  let : Nonempty C.val := ⟨K.base⟩
  have hS := actual_structure P hP
  let : FiniteStochasticMixing.RowStochastic (restriction P C.val) :=
    ⟨fun x => ⟨(hS.class_stochastic C).1 x, sum_row_of_mem_rowStochastic (hS.class_stochastic C) x⟩⟩
  obtain ⟨mu, hm, ht⟩ := FiniteStochasticMixing.stationary_distribution_exists (restriction P C.val)
  refine ⟨K, hB, ⟨{
    stationaryRow := mu
    nonnegative := hm.nonneg
    normalized := hm.rowsum
    stationary := ht.stationary
    unique := stationary_unique hP K hB mu hm.nonneg hm.rowsum ht.stationary
    positive := stationary_positive hP mu hm.nonneg hm.rowsum ht.stationary
    phase_mass := phase_mass hP K mu ht.stationary hm.rowsum
    convergence := residue_limit hP K hB mu hm.nonneg hm.rowsum ht.stationary }⟩⟩

end
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteClosedClassLimits
