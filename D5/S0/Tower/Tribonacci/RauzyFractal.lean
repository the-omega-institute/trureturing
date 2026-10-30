/- GID: D5/S0/Tower/Tribonacci/RauzyFractal
   generality: I
   mirror-B: D5/B/S0/Tower/Tribonacci/RauzyFractal
   mirror-E: none(waiver:exact-attractor-equality)
   anchors: []
   utility: none
   digest: The bounded Tribonacci window has a compact Rauzy closure and three prefix contractions. -/

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

private theorem conjugateCoordinate_head_tail
    (Q : Nat) (z : Complex)
    (name : TribonacciName (Q + 1)) :
    conjugateCoordinate z name =
      (if name.1 0 then 1 else 0) +
        z * conjugateCoordinate z
          ⟨Fin.tail name.1, admissible_tail Q name.2⟩ := by
  let tail : TribonacciName Q :=
    ⟨Fin.tail name.1, admissible_tail Q name.2⟩
  have hname : Fin.cons (name.1 0) tail.1 = name.1 := by
    dsimp [tail]
    exact Fin.cons_self_tail name.1
  have hcons : TribonacciAdmissible (Q + 1) (Fin.cons (name.1 0) tail.1) := by
    rw [hname]
    exact name.2
  have hcoord := conjugateCoordinate_cons Q z (name.1 0) tail hcons
  have hsub :
      (⟨Fin.cons (name.1 0) tail.1, hcons⟩ : TribonacciName (Q + 1)) = name := by
    apply Subtype.ext
    exact hname
  rw [hsub] at hcoord
  simpa [tail] using hcoord

private theorem zero_mem_internal_window (z : Complex) :
    0 ∈ tribonacciInternalWindow z := by
  refine ⟨0, ⟨fun i => Fin.elim0 i, trivial⟩, ?_⟩
  simp [conjugateCoordinate]

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

private theorem tribonacciInternalWindow_subset_prefix_union (z : Complex) :
    tribonacciInternalWindow z ⊆
      zeroPrefixMap z '' tribonacciInternalWindow z ∪
        oneZeroPrefixMap z '' tribonacciInternalWindow z ∪
          oneOneZeroPrefixMap z '' tribonacciInternalWindow z := by
  intro w hw
  obtain ⟨Q, name, rfl⟩ := hw
  match Q with
  | 0 =>
      left
      refine ⟨0, zero_mem_internal_window z, ?_⟩
      simp [zeroPrefixMap, conjugateCoordinate]
  | 1 =>
      cases hd : name.1 0 with
      | false =>
          left
          refine ⟨0, zero_mem_internal_window z, ?_⟩
          simp [zeroPrefixMap, conjugateCoordinate, hd]
      | true =>
          right
          left
          refine ⟨0, zero_mem_internal_window z, ?_⟩
          simp [oneZeroPrefixMap, conjugateCoordinate, hd]
  | 2 =>
      cases h0 : name.1 0 with
      | false =>
          let tail : TribonacciName 1 :=
            ⟨Fin.tail name.1, admissible_tail 1 name.2⟩
          left
          refine ⟨conjugateCoordinate z tail, ⟨1, tail, rfl⟩, ?_⟩
          have hcoord := conjugateCoordinate_head_tail 1 z name
          simpa [tail, zeroPrefixMap, h0] using hcoord.symm
      | true =>
          cases h1 : name.1 1 with
          | false =>
              right
              left
              refine ⟨0, zero_mem_internal_window z, ?_⟩
              simp [oneZeroPrefixMap, conjugateCoordinate, h0, h1]
          | true =>
              right
              right
              refine ⟨0, zero_mem_internal_window z, ?_⟩
              simp [oneOneZeroPrefixMap, conjugateCoordinate, h0, h1]
  | n + 3 =>
      let tail₁ : TribonacciName (n + 2) :=
        ⟨Fin.tail name.1, admissible_tail (n + 2) name.2⟩
      let tail₂ : TribonacciName (n + 1) :=
        ⟨Fin.tail tail₁.1, admissible_tail (n + 1) tail₁.2⟩
      let tail₃ : TribonacciName n :=
        ⟨Fin.tail tail₂.1, admissible_tail n tail₂.2⟩
      cases h0 : name.1 0 with
      | false =>
          left
          refine ⟨conjugateCoordinate z tail₁, ⟨n + 2, tail₁, rfl⟩, ?_⟩
          have hcoord := conjugateCoordinate_head_tail (n + 2) z name
          simpa [tail₁, zeroPrefixMap, h0] using hcoord.symm
      | true =>
          cases h1 : tail₁.1 0 with
          | false =>
              right
              left
              refine ⟨conjugateCoordinate z tail₂, ⟨n + 1, tail₂, rfl⟩, ?_⟩
              have hcoord₀ := conjugateCoordinate_head_tail (n + 2) z name
              have hcoord₁ := conjugateCoordinate_head_tail (n + 1) z tail₁
              have hcoord₁' :
                  conjugateCoordinate z tail₁ =
                    z * conjugateCoordinate z tail₂ := by
                simpa [tail₂, h1] using hcoord₁
              calc
                oneZeroPrefixMap z (conjugateCoordinate z tail₂) =
                    1 + z ^ 2 * conjugateCoordinate z tail₂ := by
                      rfl
                _ = 1 + z * conjugateCoordinate z tail₁ := by
                      rw [hcoord₁']
                      ring
                _ = conjugateCoordinate z name := by
                      simpa [tail₁, h0] using hcoord₀.symm
          | true =>
              cases h2 : tail₂.1 0 with
              | false =>
                  right
                  right
                  refine ⟨conjugateCoordinate z tail₃, ⟨n, tail₃, rfl⟩, ?_⟩
                  have hcoord₀ := conjugateCoordinate_head_tail (n + 2) z name
                  have hcoord₁ := conjugateCoordinate_head_tail (n + 1) z tail₁
                  have hcoord₂ := conjugateCoordinate_head_tail n z tail₂
                  have hcoord₁' :
                      conjugateCoordinate z tail₁ =
                        1 + z * conjugateCoordinate z tail₂ := by
                    simpa [tail₂, h1] using hcoord₁
                  have hcoord₂' :
                      conjugateCoordinate z tail₂ =
                        z * conjugateCoordinate z tail₃ := by
                    simpa [tail₃, h2] using hcoord₂
                  calc
                    oneOneZeroPrefixMap z (conjugateCoordinate z tail₃) =
                        1 + z + z ^ 3 * conjugateCoordinate z tail₃ := by
                          rfl
                    _ = 1 + z * (1 + z * conjugateCoordinate z tail₂) := by
                          rw [hcoord₂']
                          ring
                    _ = 1 + z * conjugateCoordinate z tail₁ := by
                          rw [hcoord₁']
                    _ = conjugateCoordinate z name := by
                          simpa [tail₁, h0] using hcoord₀.symm
              | true =>
                  exfalso
                  have hforbidden :=
                    (admissible_add_three_iff n name.1).1 name.2 |>.1
                  simp [tail₁, tail₂, h0, h1, h2, Fin.tail] at hforbidden

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

theorem rauzyFractal_eq_prefix_union {z : Complex}
    (hz : z ∈ D5.S0.Tower.Tribonacci.Binet.tribonacciCharacteristicPolynomial.roots)
    (hz_ne : z ≠
      (D5.S0.Tower.Tribonacci.Values.tribonacciConstant : Complex)) :
    rauzyFractal z =
      zeroPrefixMap z '' rauzyFractal z ∪
        oneZeroPrefixMap z '' rauzyFractal z ∪
          oneOneZeroPrefixMap z '' rauzyFractal z := by
  apply subset_antisymm
  · change closure (tribonacciInternalWindow z) ⊆
      zeroPrefixMap z '' rauzyFractal z ∪
        oneZeroPrefixMap z '' rauzyFractal z ∪
          oneOneZeroPrefixMap z '' rauzyFractal z
    have hcompact : IsCompact (rauzyFractal z) :=
      rauzyFractal_isCompact hz hz_ne
    have hzero : IsCompact (zeroPrefixMap z '' rauzyFractal z) := by
      apply hcompact.image
      change Continuous (fun w : Complex => z * w)
      exact continuous_const_mul z
    have hone : IsCompact (oneZeroPrefixMap z '' rauzyFractal z) := by
      apply hcompact.image
      change Continuous (fun w : Complex => 1 + z ^ 2 * w)
      fun_prop
    have honeone : IsCompact (oneOneZeroPrefixMap z '' rauzyFractal z) := by
      apply hcompact.image
      change Continuous (fun w : Complex => 1 + z + z ^ 3 * w)
      fun_prop
    have hclosed :
        IsClosed
          (zeroPrefixMap z '' rauzyFractal z ∪
            oneZeroPrefixMap z '' rauzyFractal z ∪
              oneOneZeroPrefixMap z '' rauzyFractal z) := by
      exact ((hzero.union hone).union honeone).isClosed
    apply closure_minimal _ hclosed
    intro w hw
    have hsubset := tribonacciInternalWindow_subset_prefix_union z hw
    rcases hsubset with hsubset | hsubset
    · exact Or.inl (image_mono subset_closure hsubset)
    · rcases hsubset with hsubset | hsubset
      · exact Or.inl (image_mono subset_closure hsubset)
      · exact Or.inr (image_mono subset_closure hsubset)
  · exact rauzyFractal_prefix_invariant z

end D5.S0.Tower.Tribonacci.RauzyFractal
