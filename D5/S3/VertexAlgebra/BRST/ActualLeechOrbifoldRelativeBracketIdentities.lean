/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeBracketIdentities
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeBracketIdentities
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Explicit relative primitives for the skew and Jacobi defects. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBracket

/-! The translation primitive for the relative skew defect and its Jacobi consequence. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open ActualLeechOrbifoldCriticalMatter (matter hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge)
open LatticeQuartetContraction (chargeProject)
open RelativeCohomology (GradedCycles GradedCohomology)
open private assocY_modes term_truncation
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes
open private ghost_square ward Q_T E_b E_T degree_b degree_T momentum_b momentum_T
  degree_mode momentum_mode from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCurrent
open private native_mem native_degree native_closed boundary_of_native
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBracket

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup
local notation "Cycles" => GradedCycles planeFrame planeBasis
local notation "Coh" => GradedCohomology planeFrame planeBasis

local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _
local instance (p : Charge hyperbolicPlane) (g : ℤ) : AddCommGroup (Cycles p g) :=
  Submodule.addCommGroup _

private theorem mode_closed (n : ℤ) {u v : ComplexState}
    (qu : Q u = 0) (qv : Q v = 0) : Q (originalMode n u v) = 0 := by
  rw [actualQ_mode_superderivation, qu, qv]
  simp only [map_zero, LinearMap.zero_apply, add_zero]

private theorem energy_mode
    (n : ℤ) {u v : ComplexState} (bu : b0 u = 0) (bv : b0 v = 0)
    (qu : Q u = 0) (qv : Q v = 0) :
    E (originalMode n u v) = -((n + 1 : ℤ) : ℂ) • originalMode n u v := by
  rw [← ward 0, mode_closed n qu qv, actual_b0_mode, bu, bv]
  simp only [map_zero, LinearMap.zero_apply, zero_add, add_zero]
  have hBu : Q (B u) = T u := by
    simpa only [qu, map_zero, add_zero] using ward (-1) u
  rw [actualQ_mode_superderivation, hBu, qv, map_zero, add_zero, translation_mode,
    show n + 1 - 1 = n by omega]

private theorem mode_tail (u v : ComplexState) :
    ∃ N₀ : ℕ, ∀ k ≥ N₀, originalMode (k : ℤ) u v = 0 := by
  obtain ⟨M, hM⟩ := term_truncation (reassoc u) (reassoc v)
  refine ⟨M.toNat, fun k hk => reassoc.injective ?_⟩
  rw [reassoc_originalMode, assocY_modes]
  exact (finsum_eq_zero_of_forall_eq_zero (hM _ (by omega))).trans reassoc.map_zero.symm

private def skewCoefficient (k : ℕ) : ℂ :=
  -((-1 : ℂ) ^ (k + 1)) / ((k + 1).factorial : ℂ)

def skewCorrection (u v : ComplexState) (k : ℕ) : ComplexState :=
  skewCoefficient k • (T ^ (k + 1)) (originalMode (k : ℤ) v u)

/-- Actual odd/odd super-skew at mode -1, with the j=0 term on the left. -/
abbrev OddProductSkewLaw : Prop :=
  ∀ (u v : ComplexState), Degree 1 u → Degree 1 v →
    originalMode (-1) u v + originalMode (-1) v u = ∑ᶠ k : ℕ, skewCorrection u v k

/-- A term of the absolute primitive, with j=k+1. -/
def skewPrimitiveTerm (u v : ComplexState) (k : ℕ) : ComplexState :=
  skewCoefficient k • B ((T ^ k) (originalMode (k : ℤ) v u))

/-- The skew primitive lives in the kernel of the original b0 on the relative shell. -/
def skewPrimitive (u v : ComplexState) : ComplexState :=
  -b0 (∑ᶠ k : ℕ, skewPrimitiveTerm u v k)

private theorem skew_support (u v : ComplexState) :
    ∃ M : ℕ, (∀ k ≥ M, skewPrimitiveTerm u v k = 0) ∧
      (∀ k ≥ M, skewCorrection u v k = 0) := by
  obtain ⟨M, hM⟩ := mode_tail v u
  exact ⟨M, fun k hk => by simp [skewPrimitiveTerm, hM k hk],
    fun k hk => by simp [skewCorrection, hM k hk]⟩

private theorem sum_skew {f : ℕ → ComplexState} (M : ℕ) (hf : ∀ k ≥ M, f k = 0) :
    (∑ᶠ k : ℕ, f k) = ∑ k ∈ Finset.range M, f k := by
  apply finsum_eq_sum_of_support_subset
  intro k hk
  apply Finset.mem_range.mpr
  exact lt_of_not_ge (fun h => hk (hf k h))

private theorem translated_mode
    {p q : Charge hyperbolicPlane} {u v : ComplexState}
    (pu : Momentum p u) (pv : Momentum q v) (du : Degree 1 u) (dv : Degree 1 v)
    (bu : b0 u = 0) (bv : b0 v = 0) (qu : Q u = 0) (qv : Q v = 0) (k l : ℕ) :
    let z := (T ^ l) (originalMode (k : ℤ) v u)
    Q z = 0 ∧ E z = (((l : ℤ) - (k + 1) : ℤ) : ℂ) • z ∧
      Degree 2 z ∧ Momentum (p + q) z := by
  induction l with
  | zero =>
    simp only [pow_zero, Module.End.one_apply]
    have hd : Degree (1 + 1) (originalMode (k : ℤ) v u) :=
      degree_mode (k : ℤ) (x := v) (y := u) dv du
    refine ⟨mode_closed (k : ℤ) qv qu, ?_, hd, ?_⟩
    · simpa only [Nat.cast_zero, zero_sub, Int.cast_neg] using energy_mode (k : ℤ) bv bu qv qu
    · exact (add_comm q p) ▸ momentum_mode (k : ℤ) pv pu
  | succ l ih =>
    simp only [pow_succ', Module.End.mul_apply]
    obtain ⟨hq, he, hn, hp⟩ := ih
    refine ⟨by rw [Q_T, hq, map_zero], ?_, degree_T hn, momentum_T hp⟩
    rw [E_T, he, map_smul]
    have hcast : (((l.succ : ℕ) : ℤ) - ((k : ℤ) + 1) : ℤ) =
        ((l : ℤ) - ((k : ℤ) + 1) : ℤ) + 1 := by omega
    rw [hcast, Int.cast_add, Int.cast_one, add_smul, one_smul]

private theorem skew_term_properties
    {p q : Charge hyperbolicPlane} {u v : ComplexState}
    (pu : Momentum p u) (pv : Momentum q v) (du : Degree 1 u) (dv : Degree 1 v)
    (bu : b0 u = 0) (bv : b0 v = 0) (qu : Q u = 0) (qv : Q v = 0) (k : ℕ) :
    Q (skewPrimitiveTerm u v k) = skewCorrection u v k ∧
      E (skewPrimitiveTerm u v k) = 0 ∧ Degree 1 (skewPrimitiveTerm u v k) ∧
      Momentum (p + q) (skewPrimitiveTerm u v k) := by
  let z := (T ^ k) (originalMode (k : ℤ) v u)
  obtain ⟨hq, he, hd, hp⟩ := translated_mode pu pv du dv bu bv qu qv k k
  change Q z = 0 at hq
  change Degree 2 z at hd
  change Momentum (p + q) z at hp
  change Q (skewCoefficient k • B z) = _ ∧ E (skewCoefficient k • B z) = 0 ∧
    Degree 1 (skewCoefficient k • B z) ∧ Momentum (p + q) (skewCoefficient k • B z)
  have hE : E (B z) = 0 := by
    rw [E_b, he, show ((k : ℤ) - ((k : ℤ) + 1) : ℤ) = -1 by omega, map_smul, sub_self]
  have hQz : Q (B z) = T z := by
    have h : Q (B z) + B (Q z) = T z := ward (-1) z
    simpa only [hq, map_zero, add_zero] using h
  have hn := degree_b (-1) hd
  have hm : Momentum (p + q) (B z) := momentum_b (-1) hp
  refine ⟨?_, by rw [map_smul, hE, smul_zero], ?_, ?_⟩
  · rw [map_smul, hQz, skewCorrection, pow_succ', Module.End.mul_apply]
  · simpa only [Degree, show (2 - 1 : ℤ) = 1 by norm_num, map_smul, smul_comm (skewCoefficient k)]
      using congrArg (fun w : ComplexState => skewCoefficient k • w) hn
  · unfold Momentum at hm ⊢
    simp only [map_smul, hm]

/-- The termwise translation homotopy, followed by -b0, gives an actual relative boundary. -/
theorem skew_boundary
    (hS : OddProductSkewLaw) {p q : Charge hyperbolicPlane} {u v : ComplexState}
    (hu : reassoc u ∈ relativeShell p) (hv : reassoc v ∈ relativeShell q)
    (du : Degree 1 u) (dv : Degree 1 v) (qu : Q u = 0) (qv : Q v = 0) :
    reassoc (skewPrimitive u v) ∈ relativeShell (p + q) ∧ Degree 0 (skewPrimitive u v) ∧
      Q (skewPrimitive u v) = current u v + current v u := by
  obtain ⟨pu, bu, _⟩ := (relative_iff p u).mp hu
  obtain ⟨pv, bv, _⟩ := (relative_iff q v).mp hv
  obtain ⟨M, hP, hR⟩ := skew_support u v
  let A := ∑ k ∈ Finset.range M, skewPrimitiveTerm u v k
  have hterm := skew_term_properties pu pv du dv bu bv qu qv
  have hA : skewPrimitive u v = -b0 A := by rw [skewPrimitive, sum_skew M hP]
  have hAQ : Q A = originalMode (-1) u v + originalMode (-1) v u := by
    rw [hS u v du dv, sum_skew M hR]
    simp only [A, map_sum]
    exact Finset.sum_congr rfl (fun k _ => (hterm k).1)
  have hAE : E A = 0 := by
    have term_energy (k : ℕ) : E (skewPrimitiveTerm u v k) = 0 := (hterm k).2.1
    simp only [A, map_sum, term_energy, Finset.sum_const_zero]
  have hAN : Degree 1 A := by
    have hd (k : ℕ) := (hterm k).2.2.1
    simp only [Degree, A, map_sum, Finset.smul_sum] at hd ⊢
    exact Finset.sum_congr rfl (fun k _ => hd k)
  have hAP : Momentum (p + q) A := by
    let g : ComplexState →ₗ[ℂ] AssocState := reassoc.toLinearMap
    let f : ComplexState →ₗ[ℂ] AssocState := (rightLift (chargeProject (p + q))).comp g
    let terms : ℕ → ComplexState := skewPrimitiveTerm u v
    change f (∑ k ∈ Finset.range M, terms k) = g (∑ k ∈ Finset.range M, terms k)
    exact (map_sum f terms (Finset.range M)).trans
      ((Finset.sum_congr rfl (fun k _ => (hterm k).2.2.2)).trans
        (map_sum g terms (Finset.range M)).symm)
  have hBP := momentum_b 0 hAP
  have hBN := degree_b 0 hAN
  refine ⟨(relative_iff _ _).mpr ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hA]
    let f := rightLift (chargeProject (p + q))
    let z : ComplexState := b0 A
    change f (reassoc (-z)) = reassoc (-z)
    exact (congrArg f (reassoc.map_neg z)).trans
      ((f.map_neg (reassoc z)).trans
        ((congrArg Neg.neg hBP).trans (reassoc.map_neg z).symm))
  · rw [hA, map_neg, ghost_square 0 A, neg_zero]
  · rw [hA, map_neg, E_b 0, hAE]
    simp only [map_zero, Int.cast_zero, zero_smul, sub_zero, neg_zero]
  · simpa only [hA, Degree, sub_self, map_neg, smul_neg, neg_inj] using hBN
  · have h := ward 0 A
    rw [hAE, hAQ, map_add, b0_product bu bv, b0_product bv bu] at h
    rw [hA, map_neg]
    have hn : Q (b0 A) = -(current u v + current v u) := eq_neg_of_add_eq_zero_left h
    exact (congrArg Neg.neg hn).trans (neg_neg _)

/-- The even (0,0,0) identity on the two extracted currents suffices. -/
abbrev EvenCurrentLaw : Prop :=
  ∀ (u v w : ComplexState), Degree 1 u → Degree 1 v →
    originalMode 0 (B u) (originalMode 0 (B v) w) =
      originalMode 0 (originalMode 0 (B u) (B v)) w +
        originalMode 0 (B v) (originalMode 0 (B u) w)

/-- The mode-zero extraction of the current is an exact state identity. -/
theorem B_current (u v : ComplexState) (du : Degree 1 u) :
    B (current u v) = originalMode 0 (B u) (B v) := by
  change B (originalMode 0 (B u) v) = _
  rw [actual_b_minus_one_mode, ghost_square (-1) u, even_B_of_degree_one du]
  simp only [map_zero, LinearMap.zero_apply, zero_add]

/-- The even (0,0,0) commutator gives left-Leibniz before passage to the quotient. -/
theorem current_leftLeibniz (hL : EvenCurrentLaw) (u v w : ComplexState)
    (du : Degree 1 u) (dv : Degree 1 v) :
    current u (current v w) = current (current u v) w + current v (current u w) := by
  change originalMode 0 (B u) (originalMode 0 (B v) w) =
    originalMode 0 (B (current u v)) w + originalMode 0 (B v) (originalMode 0 (B u) w)
  rw [B_current u v du]
  exact hL u v w du dv

/-- The two representatives of the skew defect define the zero class in the
common output shell. This form avoids a cast between p+q and q+p. -/
theorem skew_defect_class_zero (hS : OddProductSkewLaw)
    {p q : Charge hyperbolicPlane} (u : Cycles p 1) (v : Cycles q 1)
    (z : Cycles (p + q) 1)
    (hz : nativeValue z = current (nativeValue u) (nativeValue v) +
      current (nativeValue v) (nativeValue u)) :
    (Submodule.Quotient.mk z : Coh (p + q) 1) = 0 := by
  obtain ⟨h, d, w⟩ := skew_boundary hS (native_mem u) (native_mem v)
    (native_degree u) (native_degree v) (native_closed u) (native_closed v)
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (boundary_of_native z _ h d (w.trans hz.symm))

/-- A cyclic Jacobi witness, in a single pinned output shell with no momentum casts. -/
theorem jacobi_boundary (hS : OddProductSkewLaw) (hL : EvenCurrentLaw)
    {p q r : Charge hyperbolicPlane} {u v w : ComplexState}
    (hu : reassoc u ∈ relativeShell p) (hv : reassoc v ∈ relativeShell q)
    (hw : reassoc w ∈ relativeShell r)
    (du : Degree 1 u) (dv : Degree 1 v) (dw : Degree 1 w)
    (qu : Q u = 0) (qv : Q v = 0) (qw : Q w = 0) :
    ∃ a : ComplexState, reassoc a ∈ relativeShell (p + q + r) ∧ Degree 0 a ∧
      Q a = current u (current v w) + current v (current w u) + current w (current u v) := by
  obtain ⟨hUV, dUV, qUV⟩ := current_closed hu hv du dv qu qv
  obtain ⟨hs, ds, qs⟩ := skew_boundary hS hw hu dw du qw qu
  obtain ⟨ht, dt, qt⟩ := skew_boundary hS hUV hw dUV dw qUV qw
  obtain ⟨hs', ds', qs'⟩ := right_boundary hv hs dv ds qv
  have hp : q + (r + p) = p + q + r := by abel
  rw [hp] at hs'
  refine ⟨current v (skewPrimitive w u) + skewPrimitive (current u v) w, ?_, ?_, ?_⟩
  · rw [map_add]
    exact (relativeShell (p + q + r)).add_mem hs' ht
  · have hsN : N (current v (skewPrimitive w u)) = 0 := by
      simpa only [Degree, Int.cast_zero, zero_smul] using ds'
    have htN : N (skewPrimitive (current u v) w) = 0 := by
      simpa only [Degree, Int.cast_zero, zero_smul] using dt
    simp only [Degree, map_add, hsN, htN, Int.cast_zero, zero_smul, add_zero]
  · rw [map_add, qs', qt, qs, map_add, current_leftLeibniz hL u v w du dv]
    abel

/-- Every class represented by the cyclic Jacobi defect is zero. -/
theorem jacobi_defect_class_zero (hS : OddProductSkewLaw) (hL : EvenCurrentLaw)
    {p q r : Charge hyperbolicPlane} (u : Cycles p 1) (v : Cycles q 1) (w : Cycles r 1)
    (z : Cycles (p + q + r) 1)
    (hz : nativeValue z =
      current (nativeValue u) (current (nativeValue v) (nativeValue w)) +
      current (nativeValue v) (current (nativeValue w) (nativeValue u)) +
      current (nativeValue w) (current (nativeValue u) (nativeValue v))) :
    (Submodule.Quotient.mk z : Coh (p + q + r) 1) = 0 := by
  obtain ⟨a, hs, hd, hq⟩ := jacobi_boundary hS hL (native_mem u) (native_mem v) (native_mem w)
    (native_degree u) (native_degree v) (native_degree w)
    (native_closed u) (native_closed v) (native_closed w)
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (boundary_of_native z a hs hd (hq.trans hz.symm))

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
