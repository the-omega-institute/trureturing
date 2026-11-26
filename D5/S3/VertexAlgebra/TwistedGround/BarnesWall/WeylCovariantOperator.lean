/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/WeylCovariantOperator
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BarnesWall/WeylCovariantOperator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Trace]
   utility: none
   digest: A binary Weyl displacement sum gives a covariant operator with maximal trace normalization. -/

import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization

/-!
# Existence of a binary Weyl covariant operator

The zero-sign charge operators use the multiplication order of
`WeylIntertwinerTraceProduct` and `OperatorAlgebra.chargeOperator`. The trace
argument takes the vanishing of the nonzero displacement traces as a premise.
In the Barnes–Wall setting, `WeylIntertwinerTraceProduct.displacement_trace_eq_zero`
supplies it from the perfect pairing and the actual charge multiplication law.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.WeylCovariantOperator

open LatticeTwistedGroundRealization (sign_zero)
open LatticeTwistedGroundRealization.SignQuotient (F₂ complexSign complexSign_add)
open scoped BigOperators

noncomputable section

variable {A V : Type*} [AddCommGroup A] [Module F₂ A] [AddCommGroup V] [Module ℂ V]
variable {W : Submodule F₂ A} {g : A →ₗ[F₂] A} {H : LinearMap.BilinForm F₂ A}
variable {q : A → F₂} {P : A → Module.End ℂ V}


private abbrev displacementMap (g : A →ₗ[F₂] A) : A →ₗ[F₂] A :=
  g + LinearMap.id

local notation "tr" => LinearMap.trace ℂ V

private theorem charge_add_self (x : A) : x + x = 0 := by
  calc
    x + x = (1 : F₂) • x + (1 : F₂) • x := by simp
    _ = 0 := by rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]

private theorem action_eq_displacement_add (x : A) : g x = (displacementMap g) x + x := by
  change g x = (g x + x) + x
  rw [add_assoc, charge_add_self, add_zero]

variable (hker : LinearMap.ker (displacementMap g) = W)
variable (hiso : ∀ u ∈ W, ∀ v ∈ W, H u v = 0)
variable (hq : ∀ w ∈ W, q w = 0)
variable (hpolar : ∀ x y, q (x + y) = q x + q y + (H x y + H (g x) (g y)))

/-- The phase at a displacement, evaluated using a preimage. -/
def displacementPhase (H : LinearMap.BilinForm F₂ A) (q : A → F₂)
    (a : W → A) (w : W) : F₂ :=
  q (a w) + H (w : A) (a w)

include hker hiso hq hpolar in
/-- Preimages differ by an element of `W`, which leaves the phase unchanged. -/
theorem phase_eq_of_preimages {w : W} {b c : A}
    (hb : (displacementMap g) b = (w : A)) (hc : (displacementMap g) c = (w : A)) :
    q b + H (w : A) b = q c + H (w : A) c := by
  let k := b + c
  have hk0 : (displacementMap g) k = 0 := by
    change (displacementMap g) (b + c) = 0
    rw [map_add, hb, hc, charge_add_self]
  have hk : k ∈ W := by
    rw [← hker]
    exact LinearMap.mem_ker.mpr hk0
  have hfix : g k = k := by
    rw [action_eq_displacement_add k, hk0, zero_add]
  have hgb : g b = (w : A) + b := by
    rw [action_eq_displacement_add b, hb]
  have hW := hiso (w : A) w.property k hk
  have hcross : H b k + H (g b) (g k) = 0 := by
    rw [hfix, hgb, LinearMap.BilinForm.add_left, hW, zero_add, CharTwo.add_self_eq_zero]
  have hqk : q (b + k) = q b := by
    simp only [hpolar b k, hq k hk, hcross, add_zero]
  have hbc : b + k = c := by
    change b + (b + c) = c
    rw [← add_assoc, charge_add_self, zero_add]
  calc
    _ = q (b + k) + H (w : A) (b + k) := by
      rw [hqk, LinearMap.BilinForm.add_right, hW, add_zero]
    _ = _ := by rw [hbc]

include hpolar in
private theorem polar_symm (x y : A) :
    H x y + H (g x) (g y) = H y x + H (g y) (g x) := by
  have h := (hpolar x y).symm.trans ((congrArg q (add_comm x y)).trans (hpolar y x))
  rw [add_comm (q y) (q x)] at h
  exact add_left_cancel h

include hker hiso hq hpolar in
private theorem translation_phase (a : W → A) (ha : ∀ w : W, (displacementMap g) (a w) = (w : A))
    {x : A} {s : W} (hs : (s : A) = (displacementMap g) x) (w : W) :
    displacementPhase H q a w + H (w : A) x =
      q x + (displacementPhase H q a (w + s) + H (g x) ((w + s : W) : A)) := by
  let b := a w
  have hb : (displacementMap g) b = (w : A) := ha w
  have hpreimage : (displacementMap g) (b + x) = ((w + s : W) : A) := by
    rw [map_add, hb, Submodule.coe_add, hs]
  have hgb : g b = (w : A) + b := by
    rw [action_eq_displacement_add b, hb]
  have hs_left (y : A) : H (s : A) y = H (g x) y + H x y := by
    rw [hs]
    exact LinearMap.BilinForm.add_left (g x) x y
  have hcross : H b x + H (g b) (g x) = H (s : A) b + H (g x) (w : A) := by
    calc
      _ = H x b + H (g x) (g b) := polar_symm hpolar b x
      _ = H x b + (H (g x) (w : A) + H (g x) b) := by
        rw [hgb, LinearMap.BilinForm.add_right]
      _ = _ := by
        rw [hs_left]
        ac_rfl
  have hdiag : H x x = H (g x) (g x) := by
    apply CharTwo.add_eq_zero.mp
    have h := hpolar x x
    rw [charge_add_self, hq 0 W.zero_mem, CharTwo.add_self_eq_zero, zero_add] at h
    exact h.symm
  have hdiag_displacement : H (s : A) x = H (g x) (s : A) := by
    calc
      _ = H (g x) x + H x x := hs_left x
      _ = H (g x) (g x) + H (g x) x := by
        rw [hdiag, add_comm (H (g x) x)]
      _ = _ := by
        rw [hs]
        exact (LinearMap.BilinForm.add_right (g x) (g x) x).symm
  have ht : displacementPhase H q a (w + s) =
      displacementPhase H q a w + q x + H (g x) (w : A) + H (w : A) x + H (g x) (s : A) := by
    calc
      _ = q (b + x) + H ((w + s : W) : A) (b + x) :=
        phase_eq_of_preimages hker hiso hq hpolar (ha (w + s)) hpreimage
      _ = (q b + q x + (H (s : A) b + H (g x) (w : A))) +
            ((H (w : A) b + H (w : A) x) + (H (s : A) b + H (s : A) x)) := by
        rw [hpolar b x, hcross, Submodule.coe_add, LinearMap.BilinForm.add_left,
          LinearMap.BilinForm.add_right (w : A) b x, LinearMap.BilinForm.add_right (s : A) b x]
      _ = _ := by
        change _ = q b + H (w : A) b + q x + H (g x) (w : A) + H (w : A) x + H (g x) (s : A)
        rw [← hdiag_displacement]
        calc
          _ = (q b + H (w : A) b + q x + H (g x) (w : A) + H (w : A) x + H (s : A) x) +
              H (s : A) b + H (s : A) b := by ac_rfl
          _ = _ := CharTwo.add_cancel_right _ _
  rw [ht, Submodule.coe_add, LinearMap.BilinForm.add_right]
  symm
  calc
    _ = (displacementPhase H q a w + H (w : A) x) + (q x + q x) +
        (H (g x) (w : A) + H (g x) (w : A)) + (H (g x) (s : A) + H (g x) (s : A)) := by
      abel
    _ = _ := by simp only [CharTwo.add_self_eq_zero, add_zero]

variable [Fintype W]

/-- The Weyl sum with identity coefficient one. -/
def covariantOperator (H : LinearMap.BilinForm F₂ A) (P : A → Module.End ℂ V)
    (q : A → F₂) (a : W → A) : Module.End ℂ V :=
  ∑ w : W, complexSign (displacementPhase H q a w) • P (w : A)

include hker hiso hq hpolar in
/-- Translation by the displacement identifies the two covariance sums. -/
theorem operator_covariance (himage : LinearMap.range (displacementMap g) = W)
    (hmul : ∀ x y, P x * P y = complexSign (H x y) • P (x + y))
    (a : W → A) (ha : ∀ w : W, (displacementMap g) (a w) = (w : A)) (x : A) :
    covariantOperator H P q a * P x =
      complexSign (q x) • (P (g x) * covariantOperator H P q a) := by
  classical
  let s : W := ⟨(displacementMap g) x, himage ▸ LinearMap.mem_range_self (displacementMap g) x⟩
  have hs : (s : A) = (displacementMap g) x := rfl
  simp only [covariantOperator, Finset.sum_mul, Finset.mul_sum, Finset.smul_sum,
    smul_mul_assoc, mul_smul_comm, hmul, smul_smul, ← complexSign_add]
  apply Fintype.sum_equiv (Equiv.addRight s) _ _
  intro w
  change complexSign (displacementPhase H q a w + H (w : A) x) • P ((w : A) + x) =
    complexSign (q x + (displacementPhase H q a (w + s) + H (g x) ((w + s : W) : A))) •
      P (g x + ((w + s : W) : A))
  have hcharge : g x + ((w + s : W) : A) = (w : A) + x := by
    rw [Submodule.coe_add, hs]
    change g x + ((w : A) + (g x + x)) = (w : A) + x
    calc
      _ = (g x + g x) + ((w : A) + x) := by ac_rfl
      _ = _ := by rw [charge_add_self, zero_add]
  rw [translation_phase hker hiso hq hpolar a ha hs w, hcharge]

variable [Module.Finite ℂ V]

include hker hq in
/-- Only the zero displacement contributes to the trace. -/
theorem operator_trace (hzero : P 0 = 1)
    (htrace : ∀ w : W, (w : A) ≠ 0 → tr (P (w : A)) = 0)
    (a : W → A) (ha : ∀ w : W, (displacementMap g) (a w) = (w : A)) :
    tr (covariantOperator H P q a) = (Module.finrank ℂ V : ℂ) := by
  classical
  have ha0 : a 0 ∈ W := by
    have hz : a 0 ∈ LinearMap.ker (displacementMap g) :=
      LinearMap.mem_ker.mpr (ha 0)
    exact hker ▸ hz
  have ht0 : displacementPhase H q a 0 = 0 := by
    simp only [displacementPhase, hq _ ha0, Submodule.coe_zero,
      LinearMap.BilinForm.zero_left, add_zero]
  simp only [covariantOperator, map_sum, map_smul]
  rw [Finset.sum_eq_single (0 : W)]
  · rw [ht0, LatticeTwistedGroundRealization.sign_zero, one_smul,
      Submodule.coe_zero, hzero, LinearMap.trace_one]
  · intro w _ hw
    have hw' : (w : A) ≠ 0 := fun hz => hw (Submodule.coe_eq_zero.mp hz)
    rw [htrace w hw', smul_zero]
  · exact fun hn => (hn (Finset.mem_univ _)).elim

omit [Fintype W] in
include hker hiso hq hpolar in
/-- The displacement sum gives a nonzero covariant operator of trace `finrank`. -/
theorem exists_covariant_operator [Finite W] [Nontrivial V]
    (himage : LinearMap.range (displacementMap g) = W) (hzero : P 0 = 1)
    (hmul : ∀ x y, P x * P y = complexSign (H x y) • P (x + y))
    (htrace : ∀ w : W, (w : A) ≠ 0 → tr (P (w : A)) = 0) :
    ∃ U : Module.End ℂ V, U ≠ 0 ∧
      (∀ x : A, U * P x = complexSign (q x) • (P (g x) * U)) ∧
      tr U = (Module.finrank ℂ V : ℂ) := by
  let : Fintype W := Fintype.ofFinite W
  have hpreimage (w : W) : ∃ x : A, (displacementMap g) x = (w : A) := by
    have hw : (w : A) ∈ LinearMap.range (displacementMap g) := himage.symm ▸ w.property
    exact LinearMap.mem_range.mp hw
  let a : W → A := fun w => Classical.choose (hpreimage w)
  have ha (w : W) : (displacementMap g) (a w) = (w : A) :=
    Classical.choose_spec (hpreimage w)
  have htr := operator_trace (H := H) hker hq hzero htrace a ha
  refine ⟨covariantOperator H P q a, ?_,
    operator_covariance hker hiso hq hpolar himage hmul a ha, htr⟩
  intro hz
  rw [hz, map_zero] at htr
  have hdim : (Module.finrank ℂ V : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Module.finrank_pos (R := ℂ) (M := V)))
  exact hdim htr.symm

end

end D5.S3.VertexAlgebra.TwistedGround.WeylCovariantOperator
