/- GID: D5/S0/Tower/Tribonacci/RauzyFractal
   generality: I
   mirror-B: D5/B/S0/Tower/Tribonacci/RauzyFractal
   mirror-E: none(waiver:unbounded-symbolic-cover)
   anchors: []
   utility: none
   digest: The compact Tribonacci Rauzy closure is exactly covered by its three admissible prefix images. -/

import D5.S0.Tower.Tribonacci.ModelSet
import Mathlib.Topology.MetricSpace.Bounded

/-! The Tribonacci internal window is upgraded here to a compact Rauzy
fractal closure, with its three admissible prefix contractions. -/

namespace D5.S0.Tower.Tribonacci.RauzyFractal

open D5.S0.Tower.Tribonacci.Names
open D5.S0.Tower.Tribonacci.ModelSet
open Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! The three admissible initial blocks are `0`, `10`, and `110`.  Their
internal-coordinate maps are the three contractions of the Tribonacci Rauzy
construction.  We first prove the finite-word transport identities, so the
subsequent invariant statements do not hide a symbolic assumption. -/

noncomputable def rauzyFractal (z : Complex) : Set Complex :=
  closure (tribonacciInternalWindow z)

noncomputable def zeroPrefixMap (z : Complex) : Complex → Complex :=
  fun w ↦ z * w

noncomputable def oneZeroPrefixMap (z : Complex) : Complex → Complex :=
  fun w ↦ 1 + z ^ 2 * w

noncomputable def oneOneZeroPrefixMap (z : Complex) : Complex → Complex :=
  fun w ↦ 1 + z + z ^ 3 * w

private theorem conjugateCoordinate_cons
    (Q : Nat) (z : Complex) (head : Bool)
    (tail : TribonacciName Q)
    (h : TribonacciAdmissible (Q + 1) (Fin.cons head tail.1)) :
    conjugateCoordinate z ⟨Fin.cons head tail.1, h⟩ =
      (if head then 1 else 0) + z * conjugateCoordinate z tail := by
  unfold conjugateCoordinate
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr (by simp)
  intro i hi
  by_cases htail : tail.1 i
  · simp only [htail, ↓reduceIte]
    rw [Fin.val_succ, pow_succ]
    ring
  · simp [htail]

private theorem zero_prefix_mem_window {z : Complex} (w : Complex)
    (hw : w ∈ tribonacciInternalWindow z) :
    zeroPrefixMap z w ∈ tribonacciInternalWindow z := by
  obtain ⟨Q, name, rfl⟩ := hw
  let out : TribonacciName (Q + 1) :=
    ⟨Fin.cons false name.1, (admissible_cons_false Q name.1).2 name.2⟩
  refine ⟨Q + 1, out, ?_⟩
  rw [conjugateCoordinate_cons Q z false name]
  simp [zeroPrefixMap]

private theorem one_zero_prefix_mem_window {z : Complex} (w : Complex)
    (hw : w ∈ tribonacciInternalWindow z) :
    oneZeroPrefixMap z w ∈ tribonacciInternalWindow z := by
  obtain ⟨Q, name, rfl⟩ := hw
  let inner : TribonacciName (Q + 1) :=
    ⟨Fin.cons false name.1, (admissible_cons_false Q name.1).2 name.2⟩
  let out : TribonacciName (Q + 2) :=
    ⟨Fin.cons true inner.1, by
      simpa [inner] using (admissible_cons_true_false Q name.1).2 name.2⟩
  refine ⟨Q + 2, out, ?_⟩
  rw [conjugateCoordinate_cons (Q + 1) z true inner,
    conjugateCoordinate_cons Q z false name]
  simp [oneZeroPrefixMap]
  ring_nf

private theorem one_one_zero_prefix_mem_window {z : Complex} (w : Complex)
    (hw : w ∈ tribonacciInternalWindow z) :
    oneOneZeroPrefixMap z w ∈ tribonacciInternalWindow z := by
  obtain ⟨Q, name, rfl⟩ := hw
  let inner : TribonacciName (Q + 1) :=
    ⟨Fin.cons false name.1, (admissible_cons_false Q name.1).2 name.2⟩
  let middle : TribonacciName (Q + 2) :=
    ⟨Fin.cons true inner.1, by
      simpa [inner] using (admissible_cons_true_false Q name.1).2 name.2⟩
  let out : TribonacciName (Q + 3) :=
    ⟨Fin.cons true middle.1, by
      simpa [inner, middle] using (admissible_cons_true_true_false Q name.1).2 name.2⟩
  refine ⟨Q + 3, out, ?_⟩
  rw [conjugateCoordinate_cons (Q + 2) z true middle,
    conjugateCoordinate_cons (Q + 1) z true inner,
    conjugateCoordinate_cons Q z false name]
  simp [oneOneZeroPrefixMap]
  ring_nf

theorem rauzyFractal_nonempty (z : Complex) : (rauzyFractal z).Nonempty := by
  refine ⟨0, subset_closure ?_⟩
  refine ⟨0, ⟨fun i => Fin.elim0 i, trivial⟩, ?_⟩
  simp [conjugateCoordinate]

theorem rauzyFractal_isCompact {z : Complex}
    (hz : z ∈ D5.S0.Tower.Tribonacci.Binet.tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠
      (D5.S0.Tower.Tribonacci.Values.tribonacciConstant : Complex)) :
    IsCompact (rauzyFractal z) := by
  exact (tribonacci_internal_window_is_bounded hz hz_ne).isCompact_closure

theorem rauzyFractal_subset_closedBall {z : Complex}
    (hz : z ∈ D5.S0.Tower.Tribonacci.Binet.tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠
      (D5.S0.Tower.Tribonacci.Values.tribonacciConstant : Complex)) :
    rauzyFractal z ⊆ Metric.closedBall 0 (1 - ‖z‖)⁻¹ := by
  have hz_contract :=
    D5.S0.Tower.Tribonacci.Binet.tribonacci_secondary_root_abs_lt_one hz hz_ne
  rw [rauzyFractal]
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro w hw
  obtain ⟨Q, name, rfl⟩ := hw
  simpa [Metric.mem_closedBall, dist_zero_right] using
    (conjugate_coordinate_norm_le z name hz_contract)

private theorem mapsTo_closure_of_mapsTo_closure
    {f : Complex → Complex} {s : Set Complex}
    (hf : Continuous f) (hfs : MapsTo f s s) :
    MapsTo f (closure s) (closure s) := by
  intro x hx
  have himage : f x ∈ closure (f '' s) :=
    image_closure_subset_closure_image hf ⟨x, hx, rfl⟩
  exact closure_mono (image_subset_iff.mpr hfs) himage

theorem zeroPrefixMap_mapsTo_rauzyFractal (z : Complex) :
    MapsTo (zeroPrefixMap z) (rauzyFractal z) (rauzyFractal z) := by
  apply mapsTo_closure_of_mapsTo_closure (s := tribonacciInternalWindow z)
  · change Continuous (fun w : Complex => z * w)
    exact continuous_const_mul z
  · intro w hw
    exact zero_prefix_mem_window w hw

theorem oneZeroPrefixMap_mapsTo_rauzyFractal (z : Complex) :
    MapsTo (oneZeroPrefixMap z) (rauzyFractal z) (rauzyFractal z) := by
  apply mapsTo_closure_of_mapsTo_closure (s := tribonacciInternalWindow z)
  · change Continuous (fun w : Complex => 1 + z ^ 2 * w)
    fun_prop
  · intro w hw
    exact one_zero_prefix_mem_window w hw

theorem oneOneZeroPrefixMap_mapsTo_rauzyFractal (z : Complex) :
    MapsTo (oneOneZeroPrefixMap z) (rauzyFractal z) (rauzyFractal z) := by
  apply mapsTo_closure_of_mapsTo_closure (s := tribonacciInternalWindow z)
  · change Continuous (fun w : Complex => 1 + z + z ^ 3 * w)
    fun_prop
  · intro w hw
    exact one_one_zero_prefix_mem_window w hw

theorem rauzyFractal_prefix_invariant (z : Complex) :
    zeroPrefixMap z '' rauzyFractal z ∪
        oneZeroPrefixMap z '' rauzyFractal z ∪
        oneOneZeroPrefixMap z '' rauzyFractal z ⊆ rauzyFractal z := by
  rintro w (hw | hw)
  · rcases hw with hw | hw
    · rcases hw with ⟨u, hu, rfl⟩
      exact zeroPrefixMap_mapsTo_rauzyFractal z hu
    · rcases hw with ⟨u, hu, rfl⟩
      exact oneZeroPrefixMap_mapsTo_rauzyFractal z hu
  · rcases hw with ⟨u, hu, rfl⟩
    exact oneOneZeroPrefixMap_mapsTo_rauzyFractal z hu

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
    · exact Or.inl (Or.inl ⟨0, hzero, by simp [conjugateCoordinate, zeroPrefixMap, h]⟩)
    · exact Or.inl (Or.inr ⟨0, hzero, by simp [conjugateCoordinate, oneZeroPrefixMap, h]⟩)
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

end D5.S0.Tower.Tribonacci.RauzyFractal
