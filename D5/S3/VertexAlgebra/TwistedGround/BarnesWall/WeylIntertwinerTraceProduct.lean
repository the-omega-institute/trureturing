/- GID: D5/S3/VertexAlgebra/TwistedGround/BarnesWall/WeylIntertwinerTraceProduct
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BarnesWall/WeylIntertwinerTraceProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Trace]
   utility: none
   digest: The normalized trace product of binary Heisenberg intertwiners is a Gauss sum. -/

import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
import Mathlib.LinearAlgebra.Trace

/-!
# Trace product of binary Heisenberg intertwiners

The trace pairing recovers the displacement coefficients of an exact
endomorphism expansion. Covariance computes those coefficients from the
identity coefficient by cyclically moving one displacement operator.

For the Barnes–Wall calculation, the two sections are the preimages in
`Q8TraceSign.actual_preimages`. The exponent on the common image
is the one in `Q8TraceSign.defectGroundExponent`, including the
diagonal contribution from the square of the displacement operator.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BarnesWall.WeylIntertwinerTraceProduct

open LatticeTwistedGroundRealization.SignQuotient (F₂ complexSign complexSign_add)
open LatticeTwistedGroundRealization (sign_zero sign_one sign_square sign_nonzero)
open scoped BigOperators

noncomputable section

variable {A V : Type*} [AddCommGroup A] [Module F₂ A] [AddCommGroup V] [Module ℂ V]

local notation "tr" => LinearMap.trace ℂ _

private theorem charge_add_self (a : A) : a + a = 0 := by
  calc
    a + a = (1 : F₂) • a + (1 : F₂) • a := by simp
    _ = 0 := by rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]

variable {H : LinearMap.BilinForm F₂ A} {P : A → Module.End ℂ V}
variable (hzero : P 0 = 1)
variable (hmul : ∀ x y, P x * P y = complexSign (H x y) • P (x + y))

include hzero hmul

private theorem trace_mul_eq_zero_of_commute {U : Module.End ℂ V} {w t : A}
    (hcomm : U * P t = P t * U) (hpair : H w t + H t w = 1) :
    tr (U * P w) = 0 := by
  have hswap : P w * P t = complexSign (H w t + H t w) • (P t * P w) := by
    rw [hmul w t, hmul t w, add_comm t w, smul_smul, ← complexSign_add,
      CharTwo.add_cancel_right]
  rw [hpair, sign_one, neg_one_smul] at hswap
  have hanti : (U * P w) * P t = -(P t * (U * P w)) := by
    rw [mul_assoc, hswap, mul_neg, ← mul_assoc U (P t) (P w), hcomm, mul_assoc]
  have hneg : tr ((U * P w) * P t * P t) = -tr ((U * P w) * P t * P t) := by
    calc
      _ = -tr ((P t * (U * P w)) * P t) := by rw [hanti, neg_mul, map_neg]
      _ = _ := by
        rw [mul_assoc (P t) (U * P w) (P t), LinearMap.trace_mul_comm ℂ (P t) ((U * P w) * P t)]
  have htwice : (2 : ℂ) * tr ((U * P w) * P t * P t) = 0 := by
    rw [two_mul]
    exact add_eq_zero_iff_eq_neg.mpr hneg
  have hz := (mul_eq_zero.mp htwice).resolve_left (by norm_num)
  rw [mul_assoc (U * P w) (P t) (P t), hmul t t, charge_add_self, hzero,
    mul_smul_comm, mul_one, map_smul, smul_eq_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left (sign_nonzero _)

/-- A nonzero charge has trace zero when the symmetrized cocycle separates it. -/
theorem displacement_trace_eq_zero
    (hperfect : ∀ w : A, w ≠ 0 → ∃ t : A, H w t + H t w = 1)
    {w : A} (hw : w ≠ 0) : tr (P w) = 0 := by
  obtain ⟨t, ht⟩ := hperfect w hw
  have hc : (1 : Module.End ℂ V) * P t = P t * 1 := by rw [one_mul, mul_one]
  simpa only [one_mul] using trace_mul_eq_zero_of_commute hzero hmul hc ht

variable [Fintype A] [Module.Finite ℂ V]

private theorem trace_mul_of_expansion
    (hperfect : ∀ w : A, w ≠ 0 → ∃ t : A, H w t + H t w = 1)
    {U : Module.End ℂ V} {c : A → ℂ} (hExpand : U = ∑ x, c x • P x) (w : A) :
    tr (U * P w) = c w * (complexSign (H w w) * (Module.finrank ℂ V : ℂ)) := by
  classical
  rw [hExpand]
  simp only [Finset.sum_mul, smul_mul_assoc, hmul, map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single w]
  · rw [charge_add_self, hzero, LinearMap.trace_one]
  · intro x _ hx
    have hxw : x + w ≠ 0 :=
      fun h => hx (add_right_cancel (h.trans (charge_add_self w).symm))
    simp only [displacement_trace_eq_zero hzero hmul hperfect hxw, mul_zero]
  · intro hw
    exact (hw (Finset.mem_univ w)).elim

/-- The identity coefficient of an exact expansion accounts for the whole trace. -/
theorem trace_of_expansion
    (hperfect : ∀ w : A, w ≠ 0 → ∃ t : A, H w t + H t w = 1)
    {U : Module.End ℂ V} {c : A → ℂ} (hExpand : U = ∑ x, c x • P x) :
    tr U = c 0 * (Module.finrank ℂ V : ℂ) := by
  simpa only [hzero, mul_one, map_zero, LinearMap.zero_apply, sign_zero, one_mul] using
    trace_mul_of_expansion hzero hmul hperfect hExpand 0

omit [Fintype A] [Module.Finite ℂ V] in
private theorem trace_mul_of_displacement {U : Module.End ℂ V} {g : A → A} {q : A → F₂}
    (hcov : ∀ x, U * P x = complexSign (q x) • (P (g x) * U))
    {a w : A} (hw : g a + a = w) :
    tr (U * P w) = complexSign (q a + H w a + H w w) * tr U := by
  have hprod : P w = complexSign (H a (g a)) • (P a * P (g a)) := by
    rw [hmul a (g a), add_comm a (g a), hw, smul_smul, sign_square, one_smul]
  have hga : g a = w + a := by
    rw [← hw, add_assoc, charge_add_self, add_zero]
  have hphase :
      H a (g a) + (q a + H (g a) (g a)) = q a + H w a + H w w := by
    have hfirst : H w (g a) = H (g a) (g a) + H a (g a) := by
      rw [← hw, map_add, LinearMap.add_apply]
    have hsecond : H w (g a) = H w w + H w a := by
      conv_lhs => rw [hga]
      rw [map_add]
    calc
      _ = q a + (H (g a) (g a) + H a (g a)) := by ac_rfl
      _ = q a + H w (g a) := by rw [hfirst]
      _ = _ := by rw [hsecond]; ac_rfl
  calc
    _ = complexSign (H a (g a)) * tr ((U * P a) * P (g a)) := by
      rw [hprod, mul_smul_comm, map_smul, smul_eq_mul, mul_assoc]
    _ = complexSign (H a (g a)) * (complexSign (q a) * tr ((P (g a) * U) * P (g a))) := by
      rw [hcov a, smul_mul_assoc, map_smul, smul_eq_mul]
    _ = complexSign (H a (g a)) * (complexSign (q a) * tr (U * (P (g a) * P (g a)))) := by
      rw [mul_assoc (P (g a)) U (P (g a)),
        ← LinearMap.trace_mul_cycle' ℂ U (P (g a)) (P (g a))]
    _ = complexSign (H a (g a)) * (complexSign (q a) * (complexSign (H (g a) (g a)) * tr U)) := by
      rw [hmul (g a) (g a), charge_add_self, hzero, mul_smul_comm, mul_one, map_smul, smul_eq_mul]
    _ = _ := by
      rw [← hphase, complexSign_add (H a (g a)), complexSign_add (q a)]
      ring

variable [Nontrivial V]

omit hzero hmul in
private theorem dimension_ne_zero : (Module.finrank ℂ V : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Module.finrank_pos (R := ℂ) (M := V)))

private theorem exists_expansion
    (hperfect : ∀ w : A, w ≠ 0 → ∃ t : A, H w t + H t w = 1)
    (hcard : Fintype.card A = (Module.finrank ℂ V)^2)
    (U : Module.End ℂ V) : ∃ c : A → ℂ, U = ∑ x, c x • P x := by
  classical
  have hli : LinearIndependent ℂ P := Fintype.linearIndependent_iff.mpr fun c hc w => by
    have hw := trace_mul_of_expansion hzero hmul hperfect (U := 0) hc.symm w
    rw [zero_mul, map_zero] at hw
    exact (mul_eq_zero.mp hw.symm).resolve_right
      (mul_ne_zero (sign_nonzero _) (dimension_ne_zero (V := V)))
  have hdim : Fintype.card A = Module.finrank ℂ (Module.End ℂ V) := by
    rw [Module.finrank_linearMap, ← pow_two, hcard]
  let b := basisOfLinearIndependentOfCardEqFinrank' (K := ℂ) P hli hdim
  use fun x => b.repr U x
  simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank'] using (b.sum_repr U).symm

/-- A preimage of a displacement determines its coefficient from the identity coefficient. -/
theorem coefficient_of_displacement
    (hperfect : ∀ w : A, w ≠ 0 → ∃ t : A, H w t + H t w = 1)
    {U : Module.End ℂ V} {c : A → ℂ} (hExpand : U = ∑ x, c x • P x)
    {g : A → A} {q : A → F₂}
    (hcov : ∀ x, U * P x = complexSign (q x) • (P (g x) * U))
    {a w : A} (hw : g a + a = w) :
    c w = complexSign (q a + H w a) * c 0 := by
  apply mul_right_cancel₀
    (mul_ne_zero (sign_nonzero (H w w)) (dimension_ne_zero (V := V)))
  calc
    c w * (complexSign (H w w) * (Module.finrank ℂ V : ℂ)) =
        tr (U * P w) := (trace_mul_of_expansion hzero hmul hperfect hExpand w).symm
    _ = complexSign (q a + H w a + H w w) * tr U :=
      trace_mul_of_displacement hzero hmul hcov hw
    _ = _ := by rw [complexSign_add, trace_of_expansion hzero hmul hperfect hExpand]; ring

/-- A fixed vector of phase zero kills the coefficients that pair nontrivially with it. -/
theorem coefficient_eq_zero_of_fixed
    (hperfect : ∀ w : A, w ≠ 0 → ∃ t : A, H w t + H t w = 1)
    {U : Module.End ℂ V} {c : A → ℂ} (hExpand : U = ∑ x, c x • P x)
    {g : A → A} {q : A → F₂}
    (hcov : ∀ x, U * P x = complexSign (q x) • (P (g x) * U))
    {w t : A} (hfix : g t = t) (hphase : q t = 0) (hpair : H w t + H t w = 1) :
    c w = 0 := by
  have hc : U * P t = P t * U := by
    simpa only [hfix, hphase, sign_zero, one_smul] using hcov t
  have hz := trace_mul_eq_zero_of_commute hzero hmul hc hpair
  rw [trace_mul_of_expansion hzero hmul hperfect hExpand w] at hz
  exact (mul_eq_zero.mp hz).resolve_right
    (mul_ne_zero (sign_nonzero _) (dimension_ne_zero (V := V)))

variable {W : Submodule F₂ A}

/-- If the phase-zero fixed vectors in `W` separate all charges outside
`W`, the expansion is supported in `W`. This applies when `W` equals
its orthogonal complement under the symmetrized cocycle. -/
theorem coefficient_support_of_fixed
    (hperfect : ∀ w : A, w ≠ 0 → ∃ t : A, H w t + H t w = 1)
    {U : Module.End ℂ V} {c : A → ℂ} (hExpand : U = ∑ x, c x • P x)
    {g : A → A} {q : A → F₂}
    (hcov : ∀ x, U * P x = complexSign (q x) • (P (g x) * U))
    (hfixed : ∀ t ∈ W, g t = t ∧ q t = 0)
    (hseparate : ∀ w ∉ W, ∃ t ∈ W, H w t + H t w = 1) :
    ∀ w ∉ W, c w = 0 := by
  intro w hw
  obtain ⟨t, ht, hpair⟩ := hseparate w hw
  obtain ⟨hfix, hphase⟩ := hfixed t ht
  exact coefficient_eq_zero_of_fixed hzero hmul hperfect hExpand hcov hfix hphase hpair

private theorem trace_ne_zero_of_displacement
    (hperfect : ∀ w : A, w ≠ 0 → ∃ t : A, H w t + H t w = 1)
    {U : Module.End ℂ V} {c : A → ℂ} (hExpand : U = ∑ x, c x • P x)
    {g : A → A} {q : A → F₂}
    (hcov : ∀ x, U * P x = complexSign (q x) • (P (g x) * U))
    (a : W → A) (ha : ∀ w : W, g (a w) + a w = (w : A))
    (hsupport : ∀ w ∉ W, c w = 0) (hne : U ≠ 0) :
    tr U ≠ 0 := by
  classical
  intro ht
  rw [trace_of_expansion hzero hmul hperfect hExpand] at ht
  have hc : c 0 = 0 := (mul_eq_zero.mp ht).resolve_right (dimension_ne_zero (V := V))
  have hall (w : A) : c w = 0 := by
    by_cases hw : w ∈ W
    · have hw' : g (a ⟨w, hw⟩) + a ⟨w, hw⟩ = w := ha ⟨w, hw⟩
      rw [coefficient_of_displacement hzero hmul hperfect hExpand hcov hw', hc, mul_zero]
    · exact hsupport w hw
  exact hne (by simpa only [hall, zero_smul, Finset.sum_const_zero] using hExpand)

variable [Fintype W]

/-- The trace product before division. Expanding the second intertwiner and
pairing with the first leaves a single sum over the common displacement space. -/
theorem trace_mul_eq_gauss_sum
    (hperfect : ∀ w : A, w ≠ 0 → ∃ t : A, H w t + H t w = 1)
    {Ui Uj : Module.End ℂ V} {ci cj : A → ℂ}
    (hUi : Ui = ∑ x, ci x • P x) (hUj : Uj = ∑ x, cj x • P x)
    {gi gj : A → A} {qi qj : A → F₂}
    (hcovI : ∀ x, Ui * P x = complexSign (qi x) • (P (gi x) * Ui))
    (hcovJ : ∀ x, Uj * P x = complexSign (qj x) • (P (gj x) * Uj))
    (a b : W → A) (ha : ∀ w : W, gi (a w) + a w = (w : A))
    (hb : ∀ w : W, gj (b w) + b w = (w : A)) (hsupportJ : ∀ w ∉ W, cj w = 0) :
    (Module.finrank ℂ V : ℂ) * tr (Ui * Uj) =
      (tr Ui * tr Uj) *
        ∑ w : W, complexSign (qi (a w) + qj (b w) + H (w : A) (a w + b w + (w : A))) := by
  classical
  have hsum : tr (Ui * Uj) = ∑ w : W, cj w * tr (Ui * P w) := by
    calc
      _ = ∑ x : A, cj x * tr (Ui * P x) := by
        rw [hUj]
        simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
      _ = _ := by
        symm
        calc
          _ = ∑ x ∈ Finset.univ.filter (fun x : A => x ∈ W), cj x * tr (Ui * P x) :=
            (Finset.sum_subtype (Finset.univ.filter (fun x : A => x ∈ W))
              (fun x => by simp) (fun x => cj x * tr (Ui * P x))).symm
          _ = _ := by
            apply Finset.sum_filter_of_ne
            intro x _ hne
            by_contra hx
            exact hne (by rw [hsupportJ x hx, zero_mul])
  rw [hsum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [trace_mul_of_expansion hzero hmul hperfect hUi,
    coefficient_of_displacement hzero hmul hperfect hUi hcovI (ha w),
    coefficient_of_displacement hzero hmul hperfect hUj hcovJ (hb w),
    trace_of_expansion hzero hmul hperfect hUi, trace_of_expansion hzero hmul hperfect hUj]
  simp only [map_add, complexSign_add]
  ring

/-- Fixed vectors of phase zero give the support condition and the sections
make the traces of the nonzero intertwiners nonzero. The normalized trace of
their product is the sign Gauss sum with the complete exponent. -/
private theorem normalized_trace_mul_eq_gauss_sum_of_expansions
    (hperfect : ∀ w : A, w ≠ 0 → ∃ t : A, H w t + H t w = 1)
    {Ui Uj : Module.End ℂ V} {ci cj : A → ℂ}
    (hUi : Ui = ∑ x, ci x • P x) (hUj : Uj = ∑ x, cj x • P x)
    {gi gj : A → A} {qi qj : A → F₂}
    (hcovI : ∀ x, Ui * P x = complexSign (qi x) • (P (gi x) * Ui))
    (hcovJ : ∀ x, Uj * P x = complexSign (qj x) • (P (gj x) * Uj))
    (a b : W → A) (ha : ∀ w : W, gi (a w) + a w = (w : A))
    (hb : ∀ w : W, gj (b w) + b w = (w : A))
    (hfixedI : ∀ t ∈ W, gi t = t ∧ qi t = 0) (hfixedJ : ∀ t ∈ W, gj t = t ∧ qj t = 0)
    (hseparate : ∀ w ∉ W, ∃ t ∈ W, H w t + H t w = 1)
    (hneI : Ui ≠ 0) (hneJ : Uj ≠ 0) :
    ((Module.finrank ℂ V : ℂ) * tr (Ui * Uj)) / (tr Ui * tr Uj) =
      ∑ w : W, complexSign (qi (a w) + qj (b w) + H (w : A) (a w + b w + (w : A))) := by
  have hsupportI := coefficient_support_of_fixed hzero hmul hperfect hUi hcovI hfixedI hseparate
  have hsupportJ := coefficient_support_of_fixed hzero hmul hperfect hUj hcovJ hfixedJ hseparate
  have htrI := trace_ne_zero_of_displacement hzero hmul hperfect hUi hcovI a ha hsupportI hneI
  have htrJ := trace_ne_zero_of_displacement hzero hmul hperfect hUj hcovJ b hb hsupportJ hneJ
  apply (div_eq_iff (mul_ne_zero htrI htrJ)).2
  rw [mul_comm _ (tr Ui * tr Uj)]
  exact trace_mul_eq_gauss_sum hzero hmul hperfect hUi hUj hcovI hcovJ a b ha hb hsupportJ

/-- For a full-size binary Heisenberg representation, the normalized trace product of
two nonzero intertwiners is the Gauss sum on their common displacement subspace. -/
theorem normalized_trace_mul_eq_gauss_sum
    (hperfect : ∀ w : A, w ≠ 0 → ∃ t : A, H w t + H t w = 1)
    (hcard : Fintype.card A = (Module.finrank ℂ V)^2)
    {Ui Uj : Module.End ℂ V} {gi gj : A → A} {qi qj : A → F₂}
    (hcovI : ∀ x, Ui * P x = complexSign (qi x) • (P (gi x) * Ui))
    (hcovJ : ∀ x, Uj * P x = complexSign (qj x) • (P (gj x) * Uj))
    (a b : W → A) (ha : ∀ w : W, gi (a w) + a w = (w : A))
    (hb : ∀ w : W, gj (b w) + b w = (w : A))
    (hfixedI : ∀ t ∈ W, gi t = t ∧ qi t = 0) (hfixedJ : ∀ t ∈ W, gj t = t ∧ qj t = 0)
    (hseparate : ∀ w ∉ W, ∃ t ∈ W, H w t + H t w = 1)
    (hneI : Ui ≠ 0) (hneJ : Uj ≠ 0) :
    ((Module.finrank ℂ V : ℂ) * tr (Ui * Uj)) / (tr Ui * tr Uj) =
      ∑ w : W, complexSign (qi (a w) + qj (b w) + H (w : A) (a w + b w + (w : A))) := by
  obtain ⟨ci, hUi⟩ := exists_expansion hzero hmul hperfect hcard Ui
  obtain ⟨cj, hUj⟩ := exists_expansion hzero hmul hperfect hcard Uj
  exact normalized_trace_mul_eq_gauss_sum_of_expansions hzero hmul hperfect
    hUi hUj hcovI hcovJ a b ha hb hfixedI hfixedJ hseparate hneI hneJ

#print axioms normalized_trace_mul_eq_gauss_sum

end

end D5.S3.VertexAlgebra.TwistedGround.BarnesWall.WeylIntertwinerTraceProduct
