/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteRotation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteRotation
   mirror-E: none(waiver:finite-certificate-support-for-an-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree.result; instance=D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteRotation.rotate13_adj
   digest: Kernel-checks column rotation adjacency for the thirteen-column graph. -/

import D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFiniteCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite

open D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation (gp)

private theorem rotate13_adj_one (v w : V13) :
    (gp 13 3).Adj (rotate13 1 v) (rotate13 1 w) ↔ (gp 13 3).Adj v w := by
  decide +kernel +revert

theorem rotate13_adj (r : Fin 13) (v w : V13) :
    (gp 13 3).Adj (rotate13 r v) (rotate13 r w) ↔ (gp 13 3).Adj v w := by
  have h (k : Nat) : ∀ v w : V13,
      (gp 13 3).Adj (rotate13 (Fin.ofNat 13 k) v)
        (rotate13 (Fin.ofNat 13 k) w) ↔
        (gp 13 3).Adj v w := by
    induction k with
    | zero =>
      intro v w
      simp [rotate13]
    | succ k ih =>
      intro v w
      have hsucc (x : V13) :
          rotate13 (Fin.ofNat 13 (k + 1)) x =
            rotate13 1 (rotate13 (Fin.ofNat 13 k) x) := by
        have hk : Fin.ofNat 13 (k + 1) = Fin.ofNat 13 k + 1 := by
          simpa using (Fin.ofNat_add k (1 : Fin 13)).symm
        cases x with
        | mk b i =>
          apply Prod.ext
          · rfl
          · change i - Fin.ofNat 13 (k + 1) = (i - Fin.ofNat 13 k) - 1
            rw [hk, sub_sub]
      rw [hsucc v, hsucc w, rotate13_adj_one]
      exact ih v w
  simpa only [Fin.ofNat_val_eq_self] using h r.val v w

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite
