/- GID: D5/S3/Factorization/Galois/ActualWindowCommonKernel
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/ActualWindowCommonKernel
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Actual common kernels identify simultaneous window intersections and rank minimizers. -/

import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

/-!
The common constraint uses one tuple in the original extension field. Its
distinguished output coordinate is zero; retaining that coordinate also covers
a singleton family without a separate codomain convention.

For a nonzero label r, inverse multiplication describes the actual scaled
window r W. No passage to an abstract degree lattice or to independent pairwise
minimizers occurs. The kernel construction is the linear-algebraic interface
for the original-label return from a common constraint matrix.
-/

noncomputable section

namespace D5.S3.Factorization.Galois.ActualWindowCommonKernel

open Module

variable {F L ι : Type*} [Field F] [Field L] [Algebra F L]

/-- The actual intersection of the windows scaled by nonzero labels. -/
def intersection (W : ι → Submodule F L) (r : ι → L) : Submodule F L :=
  ⨅ i, (W i).comap (LinearMap.mulLeft F (r i)⁻¹)

/-- All coordinates are constrained against the same distinguished coordinate. -/
def constraint (W : ι → Submodule F L) (k : ι) (p : ι → L) :
    (∀ i, W i) →ₗ[F] (ι → L) where
  toFun v i := p k * (v i : L) - p i * (v k : L)
  map_add' v w := by
    ext i
    simp only [Pi.add_apply, Submodule.coe_add]
    ring
  map_smul' a v := by
    ext i
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, Algebra.smul_def]
    ring

private theorem kernel_coordinate (W : ι → Submodule F L) (k : ι)
    (p : ι → L) (hp : p k ≠ 0) (v : LinearMap.ker (constraint W k p)) (i : ι) :
    p i / p k * (v.1 k : L) = (v.1 i : L) := by
  have h := congrFun (LinearMap.mem_ker.mp v.2) i
  change p k * (v.1 i : L) - p i * (v.1 k : L) = 0 at h
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hp).mpr
  simpa only [mul_comm] using (sub_eq_zero.mp h).symm

/-- Projection to one coordinate, with the simultaneous inverse reconstructed
inside the original windows. -/
private def kernelEquiv (W : ι → Submodule F L) (k : ι)
    (p : ι → L) (hp : ∀ i, p i ≠ 0) :
    LinearMap.ker (constraint W k p) ≃ₗ[F]
      intersection W (fun i => p k / p i) := by
  let project : LinearMap.ker (constraint W k p) →ₗ[F]
      intersection W (fun i => p k / p i) :=
    { toFun := fun v => ⟨(v.1 k : L), by
        change ∀ i, (p k / p i)⁻¹ * (v.1 k : L) ∈ W i
        intro i
        rw [inv_div, kernel_coordinate W k p (hp k) v i]
        exact (v.1 i).2⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  refine LinearEquiv.ofBijective project ⟨?_, ?_⟩
  · intro v w h
    have hcoord : (v.1 k : L) = (w.1 k : L) := congrArg Subtype.val h
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rw [← kernel_coordinate W k p (hp k) v i,
      ← kernel_coordinate W k p (hp k) w i, hcoord]
  · intro x
    let v : ∀ i, W i := fun i => ⟨p i / p k * (x : L), by
      have hx := (Submodule.mem_iInf.mp x.2) i
      change (p k / p i)⁻¹ * (x : L) ∈ W i at hx
      simpa only [inv_div] using hx⟩
    have hv : v ∈ LinearMap.ker (constraint W k p) := by
      apply LinearMap.mem_ker.mpr
      ext i
      change p k * (p i / p k * (x : L)) -
        p i * (p k / p k * (x : L)) = 0
      field_simp
      <;> ring
    refine ⟨⟨v, hv⟩, Subtype.ext ?_⟩
    change p k / p k * (x : L) = (x : L)
    rw [div_self (hp k), one_mul]

private theorem ratio_mem (W : ι → Submodule F L) (k : ι)
    (p : ∀ i, W i) (hp : ∀ i, (p i : L) ≠ 0) :
    (p k : L) ∈ intersection W (fun i => (p k : L) / (p i : L)) := by
  change ∀ i, ((p k : L) / (p i : L))⁻¹ * (p k : L) ∈ W i
  intro i
  rw [inv_div, div_mul_cancel₀ _ (hp k)]
  exact (p i).2

/-- Rank-nullity for the common constraint gives the dimension of the actual
original-label intersection. The same tuple witnesses positive intersection. -/
theorem common_kernel_rank_identity [Fintype ι] [FiniteDimensional F L]
    (W : ι → Submodule F L) (k : ι) (p : ∀ i, W i)
    (hp : ∀ i, (p i : L) ≠ 0) :
    finrank F (LinearMap.range (constraint W k (fun i => (p i : L)))) +
        finrank F (intersection W (fun i => (p k : L) / (p i : L))) =
      ∑ i, finrank F (W i) ∧
    0 < finrank F (intersection W (fun i => (p k : L) / (p i : L))) := by
  constructor
  · have h := (constraint W k (fun i => (p i : L))).finrank_range_add_finrank_ker
    rw [(kernelEquiv W k (fun i => (p i : L)) hp).finrank_eq,
      Module.finrank_pi_fintype] at h
    exact h
  · apply Submodule.one_le_finrank_iff.mpr
    intro hbot
    have hm := ratio_mem W k p hp
    rw [hbot, Submodule.mem_bot] at hm
    exact hp k hm

private theorem original_tuple (W : ι → Submodule F L) (k : ι)
    (r : ι → L) (hr : ∀ i, r i ≠ 0) (hk : r k = 1)
    (hI : intersection W r ≠ ⊥) :
    ∃ p : ∀ i, W i, (∀ i, (p i : L) ≠ 0) ∧
      (fun i => (p k : L) / (p i : L)) = r := by
  obtain ⟨w, hw, hne⟩ := Submodule.ne_bot_iff.mp hI
  let p : ∀ i, W i := fun i => ⟨(r i)⁻¹ * w, by
    exact (Submodule.mem_iInf.mp hw) i⟩
  have hp : ∀ i, (p i : L) ≠ 0 := fun i => mul_ne_zero (inv_ne_zero (hr i)) hne
  refine ⟨p, hp, ?_⟩
  funext i
  change ((r k)⁻¹ * w) / ((r i)⁻¹ * w) = r i
  rw [hk]
  field_simp

/-- One tuple in the original windows simultaneously maximizes common-constraint
rank and attains the minimum positive dimension over all original labels. -/
theorem exists_joint_rank_minimizer [Fintype ι] [FiniteDimensional F L]
    (W : ι → Submodule F L) (k : ι) (hW : ∀ i, W i ≠ ⊥) :
    ∃ p : ∀ i, W i, (∀ i, (p i : L) ≠ 0) ∧
      (∀ (q : ∀ i, W i), (∀ i, (q i : L) ≠ 0) →
        finrank F (LinearMap.range (constraint W k (fun i => (q i : L)))) ≤
          finrank F (LinearMap.range (constraint W k (fun i => (p i : L))))) ∧
      (∀ r : ι → L, (∀ i, r i ≠ 0) → r k = 1 →
        0 < finrank F (intersection W r) →
        finrank F (intersection W (fun i => (p k : L) / (p i : L))) ≤
          finrank F (intersection W r)) := by
  classical
  have hex (i : ι) : ∃ x : W i, (x : L) ≠ 0 := by
    obtain ⟨x, hx, hn⟩ := Submodule.ne_bot_iff.mp (hW i)
    exact ⟨⟨x, hx⟩, hn⟩
  choose q hq using hex
  let S : Set ℕ := {n | ∃ p : ∀ i, W i, (∀ i, (p i : L) ≠ 0) ∧
    finrank F (intersection W (fun i => (p k : L) / (p i : L))) = n}
  have hS : S.Nonempty := ⟨_, q, hq, rfl⟩
  obtain ⟨p, hp, hd⟩ := Nat.sInf_mem hS
  have hmin (q : ∀ i, W i) (hq : ∀ i, (q i : L) ≠ 0) :
      finrank F (intersection W (fun i => (p k : L) / (p i : L))) ≤
        finrank F (intersection W (fun i => (q k : L) / (q i : L))) := by
    rw [hd]
    exact Nat.sInf_le (show _ ∈ S from ⟨q, hq, rfl⟩)
  refine ⟨p, hp, ?_, ?_⟩
  · intro q hq
    have hpdim := (common_kernel_rank_identity W k p hp).1
    have hqdim := (common_kernel_rank_identity W k q hq).1
    have hle := hmin q hq
    omega
  · intro r hr hk hpos
    have hI : intersection W r ≠ ⊥ := Submodule.one_le_finrank_iff.mp hpos
    obtain ⟨q, hq, heq⟩ := original_tuple W k r hr hk hI
    simpa only [heq] using hmin q hq

#print axioms common_kernel_rank_identity
#print axioms exists_joint_rank_minimizer

end D5.S3.Factorization.Galois.ActualWindowCommonKernel
