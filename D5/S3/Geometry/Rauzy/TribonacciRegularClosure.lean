/- GID: D5/S3/Geometry/Rauzy/TribonacciRegularClosure
   generality: I
   mirror-B: D5/B/S3/Geometry/Rauzy/TribonacciRegularClosure
   mirror-E: none(waiver:unbounded-analytic-inference)
   anchors: []
   utility: none
   digest: The actual non-Perron Tribonacci Rauzy fractal is the closure of its interior. -/

import D5.S3.Geometry.Rauzy.TribonacciInterior
import D5.S3.Topology.ContractingCoverRegularClosure

/-! The exact three-prefix cover supplies regular closure of the original Rauzy set. -/

namespace D5.S3.Geometry.Rauzy.TribonacciRegularClosure

open D5.S0.Tower.Tribonacci
open RauzyFractal Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem affine_lipschitz (a b : Complex) {q : NNReal}
    (hb : ‖b‖ ≤ (q : ℝ)) : LipschitzWith q (fun w : Complex => a + b * w) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm,
    show a + b * x - (a + b * y) = b * (x - y) by ring, norm_mul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

private theorem affine_open (a b : Complex) (hb : b ≠ 0) :
    IsOpenMap (fun w : Complex => a + b * w) :=
  (isOpenMap_add_left a).comp (Homeomorph.mulLeft₀ b hb).isOpenMap

/-- The original finite-name Rauzy closure is regular closed under precisely
the two original root hypotheses. No covering or interior premise is added. -/
theorem rauzyFractal_closure_interior {z : Complex}
    (hz : z ∈ Binet.tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠ (Values.tribonacciConstant : Complex)) :
    closure (interior (rauzyFractal z)) = rauzyFractal z := by
  have hr := Binet.tribonacci_secondary_root_abs_lt_one hz hz_ne
  have hroot := (Binet.tribonacci_secondary_root_relations hz hz_ne).2.2
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hroot
  have h2 : ‖z ^ 2‖ ≤ ‖z‖ := by
    rw [norm_pow]
    nlinarith [mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hr.le)]
  have h3 : ‖z ^ 3‖ ≤ ‖z‖ := by
    calc
      ‖z ^ 3‖ = ‖z ^ 2‖ * ‖z‖ := by rw [pow_succ, norm_mul]
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right (h2.trans hr.le) (norm_nonneg z)
      _ = ‖z‖ := one_mul _
  let f : Fin 3 → Complex → Complex :=
    ![zeroPrefixMap z, oneZeroPrefixMap z, oneOneZeroPrefixMap z]
  apply D5.S3.Topology.ContractingCoverRegularClosure.closure_interior_eq_of_contracting_cover
    (rauzyFractal_isCompact hz hz_ne)
    (TribonacciInterior.rauzyFractal_interior_nonempty hz hz_ne)
    (q := ‖z‖₊) (show ‖z‖₊ < 1 from hr) f
  · intro i
    fin_cases i
    · change LipschitzWith ‖z‖₊ (fun w : Complex => z * w)
      convert affine_lipschitz 0 z (q := ‖z‖₊) (le_refl ‖z‖) using 1 <;> simp
    · exact affine_lipschitz 1 (z ^ 2) (q := ‖z‖₊) h2
    · exact affine_lipschitz (1 + z) (z ^ 3) (q := ‖z‖₊) h3
  · intro i
    fin_cases i
    · change IsOpenMap (fun w : Complex => z * w)
      exact (Homeomorph.mulLeft₀ z hz0).isOpenMap
    · exact affine_open 1 (z ^ 2) (pow_ne_zero _ hz0)
    · exact affine_open (1 + z) (z ^ 3) (pow_ne_zero _ hz0)
  · apply Eq.trans ?_ (rauzyFractal_prefix_cover hz hz_ne)
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((hx | hx) | hx)
      · exact mem_iUnion.mpr ⟨0, hx⟩
      · exact mem_iUnion.mpr ⟨1, hx⟩
      · exact mem_iUnion.mpr ⟨2, hx⟩

end D5.S3.Geometry.Rauzy.TribonacciRegularClosure
