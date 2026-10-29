/- GID: D5/S3/Arith/FibonacciAtomic/Kernels/NativeKernelRigidity
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Kernels/NativeKernelRigidity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact multiplicative Hermitian kernels on all native Fibonacci source trees take only zero and one. -/

import D5.S3.Arith.FibonacciAtomic.SourceTransportCentralizer
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Kernels.NativeKernelRigidity

open GenealogicalFiberTransport (Source substitution)
open SourceTransportCentralizer (source_transport_centralizer)

/-- Every total complex kernel on the actual nonempty finite ordered source trees
is zero-or-one valued if it is Hermitian, preserves all comparisons under the
native substitution, and is multiplicative on all constructor quadruples. -/
theorem kernel_zero_or_one (K : Source → Source → ℂ)
    (hHermitian : ∀ s t, K t s = star (K s t))
    (hTransport : ∀ s t, K (substitution s) (substitution t) = K s t)
    (hMul : ∀ s t u v,
      K (FreeMagma.mul s t) (FreeMagma.mul u v) = K s u * K t v) :
    ∀ s t, K s t = 0 ∨ K s t = 1 := by
  have transport_two (s t : Source) :
      K (substitution (substitution s)) (substitution (substitution t)) = K s t :=
    (hTransport _ _).trans (hTransport s t)
  have iterate_mul (n : ℕ) (s t : Source) :
      substitution^[n] (FreeMagma.mul s t) =
        FreeMagma.mul (substitution^[n] s) (substitution^[n] t) :=
    Function.Semiconj₂.iterate
      (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
        fun s t => substitution.map_mul s t) n s t
  have orbit (n : ℕ) :
      substitution (substitution (substitution^[n] (.of true))) =
        FreeMagma.mul (substitution (substitution^[n] (.of true)))
          (substitution^[n] (.of true)) :=
    (source_transport_centralizer.1 _).mpr ⟨n, rfl⟩
  have product {a b : ℂ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
      a * b = 0 ∨ a * b = 1 := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  have reverse {s t : Source} (h : K s t = 0 ∨ K s t = 1) :
      K t s = 0 ∨ K t s = 1 := by
    rw [hHermitian s t]
    rcases h with h | h <;> simp [h]
  have alpha_orbit (n : ℕ) :
      K (.of true) (substitution^[n] (.of true)) = 0 ∨
        K (.of true) (substitution^[n] (.of true)) = 1 := by
    have hid : K (.of true) (substitution^[n] (.of true)) =
        K (.of true) (substitution^[n] (.of true)) *
          K (.of true) (substitution^[n] (.of true)) := by
      calc
        _ = K (substitution (substitution (.of true)))
            (substitution (substitution (substitution^[n] (.of true)))) :=
          (transport_two _ _).symm
        _ = K (FreeMagma.mul (.of false) (.of true))
            (FreeMagma.mul (substitution (substitution^[n] (.of true)))
              (substitution^[n] (.of true))) := by rw [orbit n]; rfl
        _ = K (.of false) (substitution (substitution^[n] (.of true))) *
            K (.of true) (substitution^[n] (.of true)) := hMul _ _ _ _
        _ = _ := by rw [show K (.of false) (substitution (substitution^[n] (.of true))) =
            K (.of true) (substitution^[n] (.of true)) from hTransport _ _]
    exact eq_zero_or_one_of_sq_eq_self (by simpa only [pow_two] using hid.symm)
  have alpha_row (u : Source) : ∀ n : ℕ,
      K (.of true) (substitution^[n] u) = 0 ∨
        K (.of true) (substitution^[n] u) = 1 := by
    induction u with
    | of b =>
      intro n
      cases b with
      | true => exact alpha_orbit n
      | false =>
        have he : substitution^[n] (.of false) = substitution^[n + 1] (.of true) :=
          Function.iterate_succ_apply _ _ _ |>.symm
        rw [he]
        exact alpha_orbit (n + 1)
    | mul s t hs ht =>
      intro n
      have recurrence : K (.of true) (substitution^[n] (FreeMagma.mul s t)) =
          K (.of true) (substitution^[n + 1] s) *
            K (.of true) (substitution^[n + 2] t) := by
        rw [iterate_mul]
        calc
          _ = K (substitution (substitution (.of true)))
              (substitution (substitution
                (FreeMagma.mul (substitution^[n] s) (substitution^[n] t)))) :=
            (transport_two _ _).symm
          _ = K (.of false) (substitution (substitution (substitution^[n] s))) *
              K (.of true) (substitution (substitution (substitution^[n] t))) :=
            hMul _ _ _ _
          _ = K (.of true) (substitution (substitution^[n] s)) *
              K (.of true) (substitution (substitution (substitution^[n] t))) := by
            rw [show K (.of false) (substitution (substitution (substitution^[n] s))) =
              K (.of true) (substitution (substitution^[n] s)) from hTransport _ _]
          _ = _ := by simp only [Function.iterate_succ_apply']
      rw [recurrence]
      exact product (hs (n + 1)) (ht (n + 2))
  have leaf_row (b : Bool) (u : Source) : K (.of b) u = 0 ∨ K (.of b) u = 1 := by
    cases b with
    | true => exact alpha_row u 0
    | false =>
      cases u with
      | of c =>
        cases c with
        | true => exact reverse (alpha_row (.of false) 0)
        | false =>
          rw [show K (.of false) (.of false) = K (.of true) (.of true) from
            hTransport (.of true) (.of true)]
          exact alpha_row (.of true) 0
      | mul s t =>
        have beta_stable : substitution (substitution (.of false)) =
            FreeMagma.mul (substitution (.of false)) (.of false) :=
          (source_transport_centralizer.1 _).mpr ⟨1, rfl⟩
        have recurrence : K (.of false) (FreeMagma.mul s t) =
            K (.of true) s * K (.of true) (substitution t) := by
          calc
            _ = K (substitution (substitution (.of false)))
                (substitution (substitution (FreeMagma.mul s t))) :=
              (transport_two _ _).symm
            _ = K (substitution (.of false)) (substitution (substitution s)) *
                K (.of false) (substitution (substitution t)) := by
              rw [beta_stable]
              exact hMul _ _ _ _
            _ = _ := by
              rw [show K (substitution (.of false)) (substitution (substitution s)) =
                  K (.of true) s from transport_two (.of true) s,
                show K (.of false) (substitution (substitution t)) =
                  K (.of true) (substitution t) from hTransport _ _]
        rw [recurrence]
        exact product (alpha_row s 0) (alpha_row t 1)
  intro s
  induction s with
  | of b => exact leaf_row b
  | mul s t hs ht =>
    intro u
    cases u with
    | of b => exact reverse (leaf_row b (FreeMagma.mul s t))
    | mul u v =>
      rw [hMul]
      exact product (hs u) (ht v)

end D5.S3.Arith.FibonacciAtomic.Kernels.NativeKernelRigidity
