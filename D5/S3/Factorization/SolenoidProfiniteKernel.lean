/- GID: D5/S3/Factorization/SolenoidProfiniteKernel
   generality: I
   mirror-B: D5/B/S3/Factorization/SolenoidProfiniteKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The solenoid projects exactly onto the circle with profinite kernel. -/

import D5.S1.Dynamics.UniversalSolenoid
import D5.S3.Factorization.ProfinitePrimeDecomposition

/- Provenance: new assembly over pinned mathlib's finite circle-torsion
   classification (`AddCircle.nsmul_eq_zero_iff`) and the existing explicit
   prime-adic decomposition of compatible residues. -/

namespace D5.S3.Factorization.SolenoidProfiniteKernel

open D5.S1.Dynamics
open D5.S3.Factorization.ProfinitePrimeDecomposition

private instance (m : ℕ+) : NeZero m.1 := ⟨Nat.ne_of_gt m.2⟩
private instance (m n : ℕ+) : NeZero (m.1 * n.1) :=
  ⟨Nat.mul_ne_zero (Nat.ne_of_gt m.2) (Nat.ne_of_gt n.2)⟩

private theorem toAddCircle_cast_mul (m n : ℕ+)
    (x : ZMod (m.1 * n.1)) :
    ZMod.toAddCircle (ZMod.cast x : ZMod m.1) =
      n.1 • ZMod.toAddCircle x := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [ZMod.cast_intCast (dvd_mul_right m.1 n.1), ZMod.toAddCircle_intCast,
    ZMod.toAddCircle_intCast]
  change ((k / (m.1 : ℝ) : ℝ) : AddCircle (1 : ℝ)) =
    n.1 • ((k / ((m.1 * n.1 : ℕ) : ℝ) : ℝ) : AddCircle (1 : ℝ))
  rw [← AddCircle.coe_nsmul]
  apply congrArg (fun y : ℝ ↦ (y : AddCircle (1 : ℝ)))
  have hm : (m.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt m.2)
  have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt n.2)
  rw [nsmul_eq_mul]
  push_cast
  field_simp [hm, hn]

/-- Send compatible residues to the corresponding point of the solenoid's
visible-phase kernel. -/
noncomputable def residueToKernel (x : ProfiniteIntegers) :
    UniversalSolenoid.projection.ker :=
  ⟨⟨fun m ↦ ZMod.toAddCircle (x.1 m), by
      intro m n
      rw [← toAddCircle_cast_mul]
      exact congrArg ZMod.toAddCircle
        (x.2 m ⟨m.1 * n.1, Nat.mul_pos m.2 n.2⟩ (dvd_mul_right m.1 n.1))⟩,
    by
      change ZMod.toAddCircle (x.1 ⟨1, Nat.zero_lt_one⟩) = 0
      rw [ZMod.toAddCircle_eq_zero]
      exact Subsingleton.elim _ _⟩

private theorem kernel_coordinate_torsion
    (theta : UniversalSolenoid.projection.ker) (m : ℕ+) :
    m.1 • theta.1.1 m = 0 := by
  calc
    m.1 • theta.1.1 m = theta.1.1 ⟨1, Nat.zero_lt_one⟩ := by
      simpa using theta.1.2 ⟨1, Nat.zero_lt_one⟩ m
    _ = 0 := theta.2

private theorem exists_kernel_residue
    (theta : UniversalSolenoid.projection.ker) (m : ℕ+) :
    ∃ j : ZMod m.1, ZMod.toAddCircle j = theta.1.1 m := by
  obtain ⟨j, hj, hjtheta⟩ :=
    (AddCircle.nsmul_eq_zero_iff m.2).mp (kernel_coordinate_torsion theta m)
  refine ⟨(j : ZMod m.1), ?_⟩
  rw [ZMod.toAddCircle_natCast]
  simpa using hjtheta

private noncomputable def kernelResidue
    (theta : UniversalSolenoid.projection.ker) (m : ℕ+) : ZMod m.1 :=
  Classical.choose (exists_kernel_residue theta m)

@[simp] private theorem toAddCircle_kernelResidue
    (theta : UniversalSolenoid.projection.ker) (m : ℕ+) :
    ZMod.toAddCircle (kernelResidue theta m) = theta.1.1 m :=
  Classical.choose_spec (exists_kernel_residue theta m)

private theorem kernelResidue_compatible
    (theta : UniversalSolenoid.projection.ker) (m n : ℕ+)
    (h : m.1 ∣ n.1) :
    ZMod.cast (kernelResidue theta n) = kernelResidue theta m := by
  obtain ⟨k, hk⟩ := h
  have hkpos : 0 < k := by
    by_contra hkzero
    have : k = 0 := Nat.eq_zero_of_not_pos hkzero
    subst k
    simp only [mul_zero] at hk
    exact (Nat.ne_of_gt n.2) hk
  let q : ℕ+ := ⟨k, hkpos⟩
  have hn : n = ⟨m.1 * q.1, Nat.mul_pos m.2 q.2⟩ := by
    apply Subtype.ext
    exact hk
  subst n
  letI : NeZero (m.1 * q.1) :=
    ⟨Nat.mul_ne_zero (Nat.ne_of_gt m.2) (Nat.ne_of_gt q.2)⟩
  apply ZMod.toAddCircle_injective m.1
  calc
    ZMod.toAddCircle
          (ZMod.cast (kernelResidue theta
            ⟨m.1 * q.1, Nat.mul_pos m.2 q.2⟩) : ZMod m.1) =
        q.1 • ZMod.toAddCircle
          (kernelResidue theta
            ⟨m.1 * q.1, Nat.mul_pos m.2 q.2⟩) :=
      toAddCircle_cast_mul m q _
    _ = q.1 • theta.1.1
          ⟨m.1 * q.1, Nat.mul_pos m.2 q.2⟩ :=
      congrArg (q.1 • ·)
        (toAddCircle_kernelResidue theta
          ⟨m.1 * q.1, Nat.mul_pos m.2 q.2⟩)
    _ = theta.1.1 m := theta.1.2 m q
    _ = ZMod.toAddCircle (kernelResidue theta m) :=
      (toAddCircle_kernelResidue theta m).symm

/-- Recover the compatible residue family carried by a point in the
visible-phase kernel. -/
noncomputable def kernelToResidues
    (theta : UniversalSolenoid.projection.ker) : ProfiniteIntegers :=
  ⟨kernelResidue theta, kernelResidue_compatible theta⟩

/-- The kernel of the visible projection is equivalent to compatible
residues modulo every positive integer. -/
noncomputable def kernelResidueEquiv :
    UniversalSolenoid.projection.ker ≃ ProfiniteIntegers where
  toFun := kernelToResidues
  invFun := residueToKernel
  left_inv theta := by
    apply Subtype.ext
    apply Subtype.ext
    funext m
    exact toAddCircle_kernelResidue theta m
  right_inv x := by
    apply Subtype.ext
    funext m
    apply ZMod.toAddCircle_injective m.1
    exact toAddCircle_kernelResidue (residueToKernel x) m

/-- The hidden kernel is classified by one prime-adic integer coordinate
for every prime. -/
noncomputable def profiniteKernelEquiv :
    UniversalSolenoid.projection.ker ≃ (∀ p : Nat.Primes, ℤ_[p.1]) :=
  kernelResidueEquiv.trans profinitePrimeEquiv

/-- The universal solenoid gives a short exact sequence onto the visible
circle, and its kernel is exactly the product of all prime-adic integer
coordinates. -/
theorem universal_solenoid_profinite_exact :
    Function.Exact
        ((↑) : UniversalSolenoid.projection.ker → UniversalSolenoid)
        UniversalSolenoid.projection ∧
      Function.Surjective UniversalSolenoid.projection ∧
      Function.Bijective profiniteKernelEquiv := by
  refine ⟨?_, UniversalSolenoid.projection_surjective,
    profiniteKernelEquiv.bijective⟩
  intro theta
  constructor
  · intro htheta
    exact ⟨⟨theta, htheta⟩, rfl⟩
  · rintro ⟨theta, rfl⟩
    exact theta.2

end D5.S3.Factorization.SolenoidProfiniteKernel
