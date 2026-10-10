/- GID: D5/S3/Quantum/SpinChains/Sl2WeightFiltration
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/Sl2WeightFiltration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral sl₂ weights control the ranks of filtration-lowering endomorphisms. -/

import D5.S3.Quantum.SpinChains.Sl2WeightInjectivity
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

attribute [local instance] LieRing.ofAssociativeRing

namespace D5.S3.Quantum.SpinChains.Sl2WeightFiltration

open Module

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

/-- The commutator relations, including the zero representation. -/
structure Sl2Relations (h e f : Module.End K V) : Prop where
  ef : e * f - f * e = h
  he : h * e - e * h = (2 : K) • e
  hf : h * f - f * h = -(2 : K) • f

/-- The weight subspace with integer label. -/
def weightSpace (h : Module.End K V) (s : ℤ) : Submodule K V := h.eigenspace (s : K)

/-- A finite certificate that integer weight subspaces span the representation. -/
def IntegralWeights (h : Module.End K V) : Prop :=
  ∃ S : Finset ℤ, (⨆ s ∈ S, weightSpace h s) = ⊤

/-- The increasing filtration by integer weights. -/
def weightLE (h : Module.End K V) (s : ℤ) : Submodule K V :=
  ⨆ t : ℤ, ⨆ (_ : t ≤ s), weightSpace h t

/-- The decreasing filtration by integer weights. -/
def weightGE (h : Module.End K V) (s : ℤ) : Submodule K V :=
  ⨆ t : ℤ, ⨆ (_ : s ≤ t), weightSpace h t

omit [CharZero K] in
private theorem relations_symm {h e f : Module.End K V} (a : Sl2Relations h e f) :
    Sl2Relations (-h) f e := by
  constructor
  · rw [← a.ef]; abel
  · calc
      (-h) * f - f * (-h) = -(h * f - f * h) := by simp only [neg_mul, mul_neg]; abel
      _ = (2 : K) • f := by rw [a.hf]; simp
  · calc
      (-h) * e - e * (-h) = -(h * e - e * h) := by simp only [neg_mul, mul_neg]; abel
      _ = -(2 : K) • e := by rw [a.he]; simp

private theorem shift_pow {h a : Module.End K V} {δ μ : K}
    (ha : h * a - a * h = δ • a) {v : V} (hv : h v = μ • v) (r : ℕ) :
    h ((a ^ r) v) = (μ + r * δ) • ((a ^ r) v) := by
  induction r with
  | zero => simpa using hv
  | succ r ih =>
    have z := congrArg (fun A : Module.End K V => A ((a ^ r) v)) ha
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at z
    rw [ih, map_smul] at z
    rw [pow_succ', Module.End.mul_apply]
    rw [show h (a ((a ^ r) v)) = δ • a ((a ^ r) v) +
      (μ + r * δ) • a ((a ^ r) v) by exact (sub_eq_iff_eq_add.mp z)]
    simp only [Nat.cast_add, Nat.cast_one]
    module

/-- Raising powers shift the integer weight by twice the exponent. -/
theorem raising_pow_weight {h e f : Module.End K V} (a : Sl2Relations h e f)
    {s : ℤ} {v : V} (hv : v ∈ weightSpace h s) (r : ℕ) :
    (e ^ r) v ∈ weightSpace h (s + 2 * (r : ℤ)) := by
  apply Module.End.mem_eigenspace_iff.mpr
  have z := shift_pow a.he (Module.End.mem_eigenspace_iff.mp hv) r
  convert z using 2
  push_cast
  ring

/-- Lowering powers shift the integer weight by minus twice the exponent. -/
theorem lowering_pow_weight {h e f : Module.End K V} (a : Sl2Relations h e f)
    {s : ℤ} {v : V} (hv : v ∈ weightSpace h s) (r : ℕ) :
    (f ^ r) v ∈ weightSpace h (s - 2 * (r : ℤ)) := by
  apply Module.End.mem_eigenspace_iff.mpr
  have z := shift_pow a.hf (Module.End.mem_eigenspace_iff.mp hv) r
  convert z using 2
  push_cast
  ring

private theorem locally_nilpotent_of_shift [FiniteDimensional K V]
    {h a : Module.End K V} {δ μ : K} (ha : h * a - a * h = δ • a) (hδ : δ ≠ 0)
    {v : V} (hv : h v = μ • v) : ∃ n : ℕ, (a ^ n) v = 0 := by
  by_contra hn
  have hn' : ∀ n : ℕ, (a ^ n) v ≠ 0 := by simpa using hn
  have hi : Function.Injective (fun n : ℕ => μ + n * δ) := by
    intro m n heq
    apply Nat.cast_injective (R := K)
    exact mul_right_cancel₀ hδ (add_left_cancel heq)
  have li := h.eigenvectors_linearIndependent' (fun n : ℕ => μ + n * δ) hi
    (fun n => (a ^ n) v) (fun n => ⟨Module.End.mem_eigenspace_iff.mpr
      (shift_pow ha hv n), hn' n⟩)
  exact Module.Finite.not_linearIndependent_of_infinite _ li

/-- Every weight vector is locally annihilated by the raising operator. -/
theorem raising_locally_nilpotent [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f)
    {s : ℤ} {v : V} (hv : v ∈ weightSpace h s) : ∃ n : ℕ, (e ^ n) v = 0 :=
  locally_nilpotent_of_shift a.he (by norm_num) (Module.End.mem_eigenspace_iff.mp hv)

/-- Every weight vector is locally annihilated by the lowering operator. -/
theorem lowering_locally_nilpotent [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f)
    {s : ℤ} {v : V} (hv : v ∈ weightSpace h s) : ∃ n : ℕ, (f ^ n) v = 0 :=
  locally_nilpotent_of_shift a.hf (by norm_num) (Module.End.mem_eigenspace_iff.mp hv)

private theorem kernel_zero_of_relations {h e f : Module.End K V}
    (a : Sl2Relations h e f) {v : V} {q r n : ℕ}
    (hv : h v = (q : K) • v) (hr : r ≤ q)
    (hn : (e ^ n) v = 0) (hz : (f ^ r) v = 0) : v = 0 := by
  by_cases hh : h = 0
  · by_cases hq : q = 0
    · have : r = 0 := by omega
      simpa [this] using hz
    · have z : (q : K) • v = 0 := by simpa [hh] using hv.symm
      exact (smul_eq_zero.mp z).resolve_left (by exact_mod_cast hq)
  · have triple : IsSl2Triple h e f := {
      h_ne_zero := hh
      lie_e_f := a.ef
      lie_h_e_nsmul := by simpa [Ring.lie_def, two_smul] using a.he
      lie_h_f_nsmul := by simpa [Ring.lie_def, two_smul] using a.hf }
    exact Sl2WeightInjectivity.lowering_kernel_zero triple n v q r hv hr hn hz

/-- A lowering power is injective on a weight at least its exponent. -/
theorem lowering_pow_injective [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f) (s : ℤ) (r : ℕ)
    (hr : (r : ℤ) ≤ s) : Function.Injective (fun v : weightSpace h s => (f ^ r) (v : V)) := by
  intro x y hxy
  have hv : (x : V) - y ∈ weightSpace h s := Submodule.sub_mem _ x.property y.property
  obtain ⟨n, hn⟩ := raising_locally_nilpotent a hv
  have hs : 0 ≤ s := by omega
  have hw : h ((x : V) - y) = (s.toNat : K) • ((x : V) - y) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hs]
    exact Module.End.mem_eigenspace_iff.mp hv
  have hz : (f ^ r) ((x : V) - y) = 0 := by
    change (f ^ r) (x : V) = (f ^ r) (y : V) at hxy
    rw [map_sub, hxy, sub_self]
  have z := kernel_zero_of_relations a hw (by omega) hn hz
  exact Subtype.ext (sub_eq_zero.mp z)

/-- A raising power is injective on a weight at most minus its exponent. -/
theorem raising_pow_injective [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f) (t : ℤ) (r : ℕ)
    (hr : t ≤ -(r : ℤ)) : Function.Injective (fun v : weightSpace h t => (e ^ r) (v : V)) := by
  intro x y hxy
  have hv : (x : V) - y ∈ weightSpace h t := Submodule.sub_mem _ x.property y.property
  obtain ⟨n, hn⟩ := lowering_locally_nilpotent a hv
  have ht : 0 ≤ -t := by omega
  have hw : (-h) ((x : V) - y) = ((-t).toNat : K) • ((x : V) - y) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg ht]
    change -(h ((x : V) - y)) = ((-t : ℤ) : K) • ((x : V) - y)
    rw [Module.End.mem_eigenspace_iff.mp hv, Int.cast_neg, neg_smul]
  have hz : (e ^ r) ((x : V) - y) = 0 := by
    change (e ^ r) (x : V) = (e ^ r) (y : V) at hxy
    rw [map_sub, hxy, sub_self]
  have z := kernel_zero_of_relations (relations_symm a) hw (by omega) hn hz
  exact Subtype.ext (sub_eq_zero.mp z)

/-- Opposite integer weight spaces have equal dimension. -/
theorem weight_finrank_symm [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f) (s : ℤ) :
    finrank K (weightSpace h s) = finrank K (weightSpace h (-s)) := by
  have pos (s : ℤ) (hs : 0 ≤ s) :
      finrank K (weightSpace h s) = finrank K (weightSpace h (-s)) := by
    let L : weightSpace h s →ₗ[K] weightSpace h (-s) :=
      ((f ^ s.toNat).comp (weightSpace h s).subtype).codRestrict _ (fun v => by
        have label : s - 2 * (s.toNat : ℤ) = -s := by omega
        simpa only [label, LinearMap.comp_apply, Submodule.subtype_apply] using
          lowering_pow_weight a v.property s.toNat)
    let R : weightSpace h (-s) →ₗ[K] weightSpace h s :=
      ((e ^ s.toNat).comp (weightSpace h (-s)).subtype).codRestrict _ (fun v => by
        have label : -s + 2 * (s.toNat : ℤ) = s := by omega
        simpa only [label, LinearMap.comp_apply, Submodule.subtype_apply] using
          raising_pow_weight a v.property s.toNat)
    have hL : Function.Injective L := by
      intro x y eq
      exact lowering_pow_injective a s s.toNat (by omega) (congrArg Subtype.val eq)
    have hR : Function.Injective R := by
      intro x y eq
      exact raising_pow_injective a (-s) s.toNat (by omega) (congrArg Subtype.val eq)
    exact le_antisymm (LinearMap.finrank_le_finrank_of_injective hL)
      (LinearMap.finrank_le_finrank_of_injective hR)
  by_cases hs : 0 ≤ s
  · exact pos s hs
  · have eq := pos (-s) (by omega)
    rw [neg_neg] at eq
    exact eq.symm

/-- Lowering powers reach every vector in a sufficiently negative target weight. -/
theorem lowering_pow_surjective [FiniteDimensional K V]
    {h e f : Module.End K V} (a : Sl2Relations h e f) (t : ℤ) (r : ℕ)
    (ht : t ≤ -(r : ℤ)) (y : V) (hy : y ∈ weightSpace h t) :
    ∃ x ∈ weightSpace h (t + 2 * (r : ℤ)), (f ^ r) x = y := by
  let n := (-t).toNat
  have hn : (n : ℤ) = -t := Int.toNat_of_nonneg (by omega)
  have hrn : r ≤ n := by omega
  let L : weightSpace h (-t) →ₗ[K] weightSpace h t :=
    ((f ^ n).comp (weightSpace h (-t)).subtype).codRestrict _ (fun v => by
      have label : -t - 2 * (n : ℤ) = t := by omega
      simpa only [label, LinearMap.comp_apply, Submodule.subtype_apply] using
        lowering_pow_weight a v.property n)
  have hL : Function.Injective L := by
    intro x z eq
    exact lowering_pow_injective a (-t) n (by omega) (congrArg Subtype.val eq)
  have dim : finrank K (weightSpace h (-t)) = finrank K (weightSpace h t) := by
    have eq := weight_finrank_symm a (-t)
    rw [neg_neg] at eq
    exact eq
  obtain ⟨z, hz⟩ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).mp hL ⟨y, hy⟩
  refine ⟨(f ^ (n - r)) z, ?_, ?_⟩
  · have label : -t - 2 * ((n - r : ℕ) : ℤ) = t + 2 * (r : ℤ) := by omega
    simpa only [label, LinearMap.comp_apply, Submodule.subtype_apply] using
      lowering_pow_weight a z.property (n - r)
  · have hzy : (f ^ n) (z : V) = y := congrArg Subtype.val hz
    rw [← Module.End.mul_apply, ← pow_add, show r + (n - r) = n by omega, hzy]

end D5.S3.Quantum.SpinChains.Sl2WeightFiltration
