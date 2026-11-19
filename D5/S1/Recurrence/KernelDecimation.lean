/- GID: D5/S1/Recurrence/KernelDecimation
   generality: G
   mirror-B: D5/B/S1/Recurrence/KernelDecimation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite arithmetic kernels give literal fixed-coefficient finite decimation families over any commutative ring. -/

import D5.S1.Recurrence.PowerBaseDecimation
import D5.S0.Automata.FiniteKernelDFAO

/-! Kernel members are the actual decimated sequence maps. -/

namespace D5.S1.Recurrence.BinaryDecimation

open D5.S0.Automata.FiniteKernelDFAO

/-- Finite kernels supply fixed coefficient families via one-hot transition
coefficients. Equal sequences have already been identified by the kernel set. -/
theorem finite_kernel_baseFamily {R : Type*} [CommRing R] (k : ℕ) (a : ℕ → R)
    (hfin : Finite ↥(kKernel k a)) : BaseFamily k a := by
  classical
  obtain ⟨q, ⟨e⟩⟩ := @Finite.exists_equiv_fin ↥(kKernel k a) hfin
  let step (i : Fin q) (r : Fin k) : Fin q :=
    e ⟨fun n => (e.symm i).val (k * n + r.val),
      chr_kernel_lam_mem (e.symm i).prop r.isLt⟩
  refine ⟨Fin q, inferInstance, fun i n => (e.symm i).val n,
    e ⟨a, chr_self_mem_kernel a⟩,
    (fun r i j => if j = step i r then 1 else 0), ?_, ?_⟩
  · intro n
    simp
  · intro r i n
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    dsimp [step]
    rw [Equiv.symm_apply_apply]

end D5.S1.Recurrence.BinaryDecimation
