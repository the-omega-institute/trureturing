/- GID: D5/S3/Quantum/SpinChains/Sl2WeightInjectivity
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/Sl2WeightInjectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Locally nilpotent raising makes lowering powers injective at natural weights. -/

import Mathlib.Algebra.Lie.Sl2

attribute [local instance] LieRing.ofAssociativeRing

namespace D5.S3.Quantum.SpinChains.Sl2WeightInjectivity

/-- A lowering power has zero kernel at natural weight at least its exponent,
provided a raising power annihilates the vector. -/
theorem lowering_kernel_zero {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V]
    {h e f : Module.End K V} (t : IsSl2Triple h e f) (n : ℕ) :
    ∀ (v : V) (q k : ℕ), h v = (q : K) • v → k ≤ q →
      (e ^ n) v = 0 → (f ^ k) v = 0 → v = 0 := by
  have lower_pow_raise {v : V} {μ : K}
      (hv : h v = μ • v) (k : ℕ) :
      (f ^ (k + 1)) (e v) = e ((f ^ (k + 1)) v) -
        (((k + 1 : ℕ) : K) * (μ - k)) • ((f ^ k) v) := by
    induction k with
    | zero =>
      have ht := congrArg (fun op : Module.End K V => op v) t.lie_e_f
      simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply] at ht
      simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_one,
        Nat.cast_zero, sub_zero, one_mul]
      rw [hv] at ht
      apply (eq_sub_iff_add_eq).mpr
      simpa [add_comm] using ((sub_eq_iff_eq_add).mp ht).symm
    | succ k ih =>
      have hg : h ((f ^ (k + 1)) v) = (μ - 2 * (k + 1 : ℕ)) • ((f ^ (k + 1)) v) := by
        have hv' : ⁅-h, v⁆ = (-μ) • v := by simpa using congrArg Neg.neg hv
        have z := t.symm.lie_h_pow_toEnd_e hv' (k + 1)
        have z' : -(h ((f ^ (k + 1)) v)) =
            (-μ + 2 * (k + 1 : ℕ)) • ((f ^ (k + 1)) v) := by
          simpa [LieModule.toEnd_module_end] using z
        rw [neg_eq_iff_eq_neg, ← neg_smul] at z'
        convert z' using 1
        congr 1
        ring
      have ht := congrArg (fun op : Module.End K V => op ((f ^ (k + 1)) v)) t.lie_e_f
      simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply] at ht
      rw [hg] at ht
      rw [pow_succ', Module.End.mul_apply, ih, map_sub, map_smul]
      rw [show f (e ((f ^ (k + 1)) v)) =
        e (f ((f ^ (k + 1)) v)) - (μ - 2 * (k + 1 : ℕ)) • ((f ^ (k + 1)) v) by
          apply (eq_sub_iff_add_eq).mpr
          simpa [add_comm] using ((sub_eq_iff_eq_add).mp ht).symm]
      simp only [← Module.End.mul_apply, ← pow_succ', Nat.cast_add, Nat.cast_one]
      module
  induction n with
  | zero =>
    intro v q k hv hk hn hz
    simpa using hn
  | succ n ih =>
    intro v q k hv hk hn hz
    have hrv : h (e v) = ((q + 2 : ℕ) : K) • (e v) := by
      simpa [LieModule.toEnd_module_end] using t.lie_h_pow_toEnd_e hv 1
    have hrn : (e ^ n) (e v) = 0 := by
      simpa [pow_succ, Module.End.mul_apply] using hn
    have hnext : (f ^ (k + 1)) v = 0 := by
      rw [pow_succ', Module.End.mul_apply, hz, map_zero]
    have hrh : (f ^ (k + 1)) (e v) = 0 := by
      rw [lower_pow_raise hv, hnext, hz]
      simp
    have hrzero : e v = 0 := ih (e v) (q + 2) (k + 1) hrv (by omega) hrn hrh
    by_contra hvzero
    have P : t.HasPrimitiveVectorWith v (q : K) :=
      { ne_zero := hvzero, lie_h := hv, lie_e := hrzero }
    have hne := P.pow_toEnd_f_ne_zero_of_eq_nat rfl hk
    apply hne
    simpa [LieModule.toEnd_module_end] using hz

end D5.S3.Quantum.SpinChains.Sl2WeightInjectivity
