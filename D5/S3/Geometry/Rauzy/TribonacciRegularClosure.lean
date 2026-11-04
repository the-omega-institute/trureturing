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
open RauzyFractal Names ModelSet Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem window_prefix_cover (z : Complex) :
    tribonacciInternalWindow z ⊆
      zeroPrefixMap z '' tribonacciInternalWindow z ∪
        oneZeroPrefixMap z '' tribonacciInternalWindow z ∪
        oneOneZeroPrefixMap z '' tribonacciInternalWindow z := by
  have hzero : (0 : Complex) ∈ tribonacciInternalWindow z :=
    ⟨0, ⟨Fin.elim0, trivial⟩, by simp [conjugateCoordinate]⟩
  have hone : (1 : Complex) ∈ tribonacciInternalWindow z := by
    simpa [oneZeroPrefixMap] using one_zero_prefix_mem_window 0 hzero
  rintro w ⟨Q, name, rfl⟩
  match Q with
  | 0 =>
    exact Or.inl (Or.inl ⟨0, hzero, by simp [zeroPrefixMap, conjugateCoordinate]⟩)
  | 1 =>
    cases h : name.1 0
    · exact Or.inl (Or.inl ⟨0, hzero, by
        simp only [zeroPrefixMap, mul_zero, conjugateCoordinate]
        rw [Fin.sum_univ_succ]
        simp [h]⟩)
    · exact Or.inl (Or.inr ⟨0, hzero, by
        simp only [oneZeroPrefixMap, mul_zero, add_zero, conjugateCoordinate]
        rw [Fin.sum_univ_succ]
        simp [h]⟩)
  | 2 =>
    cases h0 : name.1 0 <;> cases h1 : name.1 1
    · exact Or.inl (Or.inl ⟨0, hzero, by
        simp [conjugateCoordinate, Fin.sum_univ_succ, zeroPrefixMap, h0, h1]⟩)
    · exact Or.inl (Or.inl ⟨1, hone, by
        simp [conjugateCoordinate, Fin.sum_univ_succ, zeroPrefixMap, h0, h1]⟩)
    · exact Or.inl (Or.inr ⟨0, hzero, by
        simp [conjugateCoordinate, Fin.sum_univ_succ, oneZeroPrefixMap, h0, h1]⟩)
    · exact Or.inr ⟨0, hzero, by
        simp [conjugateCoordinate, Fin.sum_univ_succ, oneOneZeroPrefixMap, h0, h1]⟩
  | n + 3 =>
    obtain ⟨split, rfl⟩ := (tribonacciNameSplitEquiv n).symm.surjective name
    rcases split with tail | (tail | tail)
    · refine Or.inl (Or.inl ⟨conjugateCoordinate z tail, ⟨n + 2, tail, rfl⟩, ?_⟩)
      change zeroPrefixMap z (conjugateCoordinate z tail) =
        conjugateCoordinate z ⟨Fin.cons false tail.1, _⟩
      rw [conjugateCoordinate_cons (n + 2) z false tail]
      simp [zeroPrefixMap]
    · refine Or.inl (Or.inr ⟨conjugateCoordinate z tail, ⟨n + 1, tail, rfl⟩, ?_⟩)
      let inner : TribonacciName (n + 2) :=
        ⟨Fin.cons false tail.1, (admissible_cons_false (n + 1) tail.1).2 tail.2⟩
      change oneZeroPrefixMap z (conjugateCoordinate z tail) =
        conjugateCoordinate z ⟨Fin.cons true inner.1, _⟩
      rw [conjugateCoordinate_cons (n + 2) z true inner,
        conjugateCoordinate_cons (n + 1) z false tail]
      simp [oneZeroPrefixMap]
      ring
    · refine Or.inr ⟨conjugateCoordinate z tail, ⟨n, tail, rfl⟩, ?_⟩
      let inner : TribonacciName (n + 1) :=
        ⟨Fin.cons false tail.1, (admissible_cons_false n tail.1).2 tail.2⟩
      let middle : TribonacciName (n + 2) :=
        ⟨Fin.cons true inner.1, by
          simpa [inner] using (admissible_cons_true_false n tail.1).2 tail.2⟩
      change oneOneZeroPrefixMap z (conjugateCoordinate z tail) =
        conjugateCoordinate z ⟨Fin.cons true middle.1, _⟩
      rw [conjugateCoordinate_cons (n + 2) z true middle,
        conjugateCoordinate_cons (n + 1) z true inner,
        conjugateCoordinate_cons n z false tail]
      simp [oneOneZeroPrefixMap]
      ring

/-- Every point has an admissible prefix preimage in the same Rauzy closure. -/
theorem rauzyFractal_prefix_cover {z : Complex}
    (hz : z ∈ D5.S0.Tower.Tribonacci.Binet.tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠ (D5.S0.Tower.Tribonacci.Values.tribonacciConstant : Complex)) :
    zeroPrefixMap z '' rauzyFractal z ∪
        oneZeroPrefixMap z '' rauzyFractal z ∪
        oneOneZeroPrefixMap z '' rauzyFractal z = rauzyFractal z := by
  refine subset_antisymm (rauzyFractal_prefix_invariant z) ?_
  have hK := rauzyFractal_isCompact hz hz_ne
  apply closure_minimal
  · exact (window_prefix_cover z).trans
      (union_subset_union (union_subset_union (image_mono subset_closure)
        (image_mono subset_closure)) (image_mono subset_closure))
  · exact ((hK.image (by unfold zeroPrefixMap; fun_prop)).union
      (hK.image (by unfold oneZeroPrefixMap; fun_prop))).union
      (hK.image (by unfold oneOneZeroPrefixMap; fun_prop)) |>.isClosed

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
