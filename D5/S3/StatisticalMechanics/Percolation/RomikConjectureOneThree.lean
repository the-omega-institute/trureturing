/- GID: D5/S3/StatisticalMechanics/Percolation/RomikConjectureOneThree
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/RomikConjectureOneThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The published open-range cylinder identity determines the rational functions and yields their common regular boundary evaluation. -/

import D5.S3.StatisticalMechanics.Percolation.RomikCylinderPfaffian
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false

open D5.S0.Certificates.IshikawaKoutschanMotzkinPfaffianRefutation (pfaffian)

namespace RatFunc

/-- Canonical evaluations at all sufficiently large natural integers determine a
rational function over `ℚ`. The roots of the two reduced denominators are finite. -/
private theorem eq_of_eventually_eval_natCast_eq {f g : RatFunc ℚ}
    (h : ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      f.eval (RingHom.id ℚ) (k : ℚ) = g.eval (RingHom.id ℚ) (k : ℚ)) :
    f = g := by
  obtain ⟨N, hN⟩ := h
  have denominatorRoots :
      ({x : ℚ | f.denom.IsRoot x} ∪ {x : ℚ | g.denom.IsRoot x}).Finite :=
    (Polynomial.finite_setOfPred_isRoot f.denom_ne_zero).union
      (Polynomial.finite_setOfPred_isRoot g.denom_ne_zero)
  have tailInfinite : (Set.range fun n : ℕ => ((N + n : ℕ) : ℚ)).Infinite :=
    Set.infinite_range_of_injective fun _ _ heq =>
      Nat.add_left_cancel (Nat.cast_injective heq)
  have cross : f.num * g.denom = g.num * f.denom := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (tailInfinite.sdiff denominatorRoots).mono
    rintro x ⟨⟨n, rfl⟩, hx⟩
    have hf : f.denom.eval ((N + n : ℕ) : ℚ) ≠ 0 :=
      fun hz => hx (Or.inl hz)
    have hg : g.denom.eval ((N + n : ℕ) : ℚ) ≠ 0 :=
      fun hz => hx (Or.inr hz)
    have heval := hN (N + n) (Nat.le_add_right N n)
    simp only [RatFunc.eval, Polynomial.eval₂_id] at heval
    simpa only [Set.mem_ofPred_eq, Polynomial.eval_mul] using (div_eq_div_iff hf hg).mp heval
  exact ((num_mul_eq_mul_denom_iff g.denom_ne_zero).mp cross).trans (num_div_denom g)

end RatFunc

namespace RomikRational

/-- The open-range Pfaffian evaluations identify the source rational function. -/
private theorem eq_rationalCylinder_of_open_eval_eq {m : ℕ} {R : RatFunc ℚ}
    (hR : ∀ N : ℕ, m < N →
      RatFunc.eval (RingHom.id ℚ) (N : ℚ) R = pfaffian (cylinderMatrix m (N : ℚ))) :
    R = rationalCylinder m := by
  apply RatFunc.eq_of_eventually_eval_natCast_eq
  refine ⟨m + 1, fun N hN => ?_⟩
  exact (hR N hN).trans (evaluate_rationalCylinder m N (Nat.le_of_lt hN)).2.symm

/-- Conjecture 1.3 of arXiv:2611.26570v1. The open-range hypothesis is the
coincidence of (1.1) and (4.4), with the entries used in (5.25).
Both rational functions are regular at the boundary and evaluate to the
same explicit Pfaffian on the first `k - 1` prescribed edges. -/
theorem source_rationalCylinder_boundary (R : ℕ → RatFunc ℚ)
    (hR : ∀ m N : ℕ, 1 ≤ m → m < N →
      RatFunc.eval (RingHom.id ℚ) (N : ℚ) (R m) = pfaffian (cylinderMatrix m (N : ℚ)))
    (k : ℕ) (hk : 2 ≤ k) :
    R k = rationalCylinder k ∧
      R (k - 1) = rationalCylinder (k - 1) ∧
      R k ∈ regularAt (k : ℚ) ∧
      R (k - 1) ∈ regularAt (k : ℚ) ∧
      RatFunc.eval (RingHom.id ℚ) (k : ℚ) (R k) =
        pfaffian (cylinderMatrix (k - 1) (k : ℚ)) ∧
      RatFunc.eval (RingHom.id ℚ) (k : ℚ) (R (k - 1)) =
        pfaffian (cylinderMatrix (k - 1) (k : ℚ)) := by
  have current : R k = rationalCylinder k :=
    eq_rationalCylinder_of_open_eval_eq (fun N hN => hR k N (by omega) hN)
  have previous : R (k - 1) = rationalCylinder (k - 1) :=
    eq_rationalCylinder_of_open_eval_eq (fun N hN => hR (k - 1) N (by omega) hN)
  have full := evaluate_rationalCylinder k k le_rfl
  have smaller := evaluate_rationalCylinder (k - 1) k (by omega)
  have reduce : pfaffian (cylinderMatrix k (k : ℚ)) =
      pfaffian (cylinderMatrix (k - 1) (k : ℚ)) := by
    have hs : k - 1 + 1 = k := by omega
    have h := cylinder_pfaffian_boundary (k - 1)
    rw [hs] at h
    exact h
  refine ⟨current, previous, ?_, ?_, ?_, ?_⟩
  · rw [current]
    exact full.1
  · rw [previous]
    exact smaller.1
  · rw [current]
    exact full.2.trans reduce
  · rw [previous]
    exact smaller.2

end RomikRational
