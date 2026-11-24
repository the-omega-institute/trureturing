/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeHHBBBSlitExtension
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native HHBB B product extends analytically through the lower equilateral ratio. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource

/-! The principal-root B value at outer root one, and its agreement with
the native doubled-mode series for arbitrary actual HHBB states. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct Topology

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBBSlitExtension

open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeHalfFockGradedTrace (actualGrade actual_basis_apply oddWeight)
open Orbifold.NativeOddTwistedIntertwiner (Twisted TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeMixedPairField (mu_coeff_even_zero)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open NativeFourHHomogeneousExtension (occupation_monomials_have_marked_words)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open NativeMixedUpperProductCusp (bJointTerm bSewnNumerator b_joint_product_hasSum)
open NativeMixedArbitrarySewing (hhbbCorrelation)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
  (doubleSlit isOpen_doubleSlit isOpen_slitDomain)

open private bSewnNumerator_differentiableOn punctureExcitation_cast wordAt_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
open private occupationGrade_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalOverlap
open private sqrt_square square_root_disk from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
open private BasisIndex ambientBasis from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension
open private BasisQuad HHBBLinear basisTuples component component_eq_zero project_basis_val
  bLinear bLinear_apply onComponents expand from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing
open private mem_doubleSlit_of_im from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource

local notation "ℒ" => leechData

set_option maxHeartbeats 4000000 in
/-- For marked HHBB tensors at outer root one, the exact B value is
analytic on the double slit and sums the native product throughout the
unit disk at the principal root. -/
theorem hhbb_marked_b_slit_extension {X : Type*}
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d) :
    let G := doubledOccupation slot n l
    let M := (G .P).toNat
    let K := (G .Q).toNat
    let L := (G .R).toNat
    let N := (G .S).toNat
    let W := wordAt ℒ slot colour n l
    let B := fun y : ℂ => Complex.sqrt y ^ (-(6 + (K : ℤ) + L)) *
      Complex.I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
      bSewnNumerator K L N (W .P) (W .Q) (W .R) (W .S) p q r d y
    AnalyticOnNhd ℂ B doubleSlit ∧
      ∀ {y : ℂ}, ‖y‖ < 1 →
        HasSum (bJointTerm false false v w u b 1 (Complex.sqrt y)) (B y) := by
  let G := doubledOccupation slot n l
  let g (i : Puncture) := (G i).toNat
  let M := g .P
  let K := g .Q
  let L := g .R
  let N := g .S
  let W := wordAt ℒ slot colour n l
  let phase := Complex.I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3)
  let numerator := bSewnNumerator K L N (W .P) (W .Q) (W .R) (W .S) p q r d
  let B (y : ℂ) := Complex.sqrt y ^ (-(6 + (K : ℤ) + L)) * phase * numerator y
  change AnalyticOnNhd ℂ B doubleSlit ∧
    ∀ {y : ℂ}, ‖y‖ < 1 →
      HasSum (bJointTerm false false v w u b 1 (Complex.sqrt y)) (B y)
  constructor
  · intro y hy
    have hroot₀ : Complex.sqrt y ≠ 0 := by
      intro h
      apply Complex.slitPlane_ne_zero hy.2
      calc
        y = Complex.sqrt y ^ (2 : ℕ) := (sqrt_square y).symm
        _ = 0 := by simp [h]
    have hroot : AnalyticAt ℂ Complex.sqrt y :=
      Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane y hy.2
    have hnum : AnalyticAt ℂ numerator y :=
      (bSewnNumerator_differentiableOn K L N (W .P) (W .Q) (W .R) (W .S) p q r d).analyticOnNhd
        isOpen_slitDomain y hy.1
    have hphase : AnalyticAt ℂ (fun _ : ℂ => phase) y := analyticAt_const
    exact (((hroot.zpow (n := -(6 + (K : ℤ) + L)) hroot₀).mul hphase).mul hnum)
  · intro y hy₁
    by_cases hy₀ : y = 0
    · subst y
      have hsqrt : Complex.sqrt 0 = 0 :=
        (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp (sqrt_square 0)
      have hB : B 0 = 0 := by
        simp only [B, hsqrt, zero_zpow _ (by omega : -(6 + (K : ℤ) + L) ≠ 0), zero_mul]
      rw [hsqrt, hB]
      refine hasSum_zero.congr_fun ?_
      rintro ⟨i, j⟩
      by_cases hi : i = 0
      · subst i
        unfold bJointTerm
        dsimp only [Prod.fst, Prod.snd]
        rw [mu_coeff_even_zero false 0 v w ⟨0, rfl⟩]
        simp
      · simp [bJointTerm, zero_zpow i hi]
    have hg (i : Puncture) := occupationGrade_eq slot colour n l i
    have hG (i : Puncture) : (g i : ℤ) = G i := by
      change (((G i).toNat : ℕ) : ℤ) = G i
      rw [hg i, punctureExcitation_cast]
    have hM₀ : (M : ℤ) % 2 = 0 := by simpa only [M, hG] using hpar.1
    have hK₀ : (K : ℤ) % 2 = 0 := by simpa only [K, hG] using hpar.2.1
    have hL₁ : (L : ℤ) % 2 = 1 := by simpa only [L, hG] using hpar.2.2.1
    have hN₁ : (N : ℤ) % 2 = 1 := by simpa only [N, hG] using hpar.2.2.2
    have hKL : Odd ((K : ℤ) + L) := Int.odd_iff.mpr (by omega)
    have hNM : Odd ((N : ℤ) - M) := Int.odd_iff.mpr (by omega)
    have huGrade : u.val ∈ actualGrade ℒ leechUnit M := by
      rw [hu, show M = _ from hg .P]
      exact wordAt_grade slot colour n l .P p
    have hvGrade : v.val ∈ actualGrade ℒ leechUnit K := by
      rw [hv, show K = _ from hg .Q]
      exact wordAt_grade slot colour n l .Q q
    have hwGrade : w.val ∈ actualGrade ℒ leechUnit L := by
      rw [hw, show L = _ from hg .R]
      exact wordAt_grade slot colour n l .R r
    have hbGrade : b.val ∈ actualGrade ℒ leechUnit N := by
      rw [hb, show N = _ from hg .S]
      exact wordAt_grade slot colour n l .S d
    obtain ⟨hroot₀, hroot₁⟩ := square_root_disk (sqrt_square y) hy₀ hy₁
    have hsum := b_joint_product_hasSum false false M K L N v w u b
      (W .P) (W .Q) (W .R) (W .S) p q r d hvGrade hwGrade huGrade hbGrade hv hw hu hb hKL hNM
      (xRoot := 1) (zRoot := Complex.sqrt y) one_ne_zero
      (by simpa only [div_one] using norm_pos_iff.mpr hroot₀)
      (by simpa only [div_one] using hroot₁)
    simpa only [B, phase, numerator, div_one, one_zpow, one_mul, sqrt_square] using hsum

set_option maxHeartbeats 4000000 in
-- The marked decomposition reduces the ambient basis and the projected states together.
private theorem component_b_slit_extension (u v : TwistedEven) (w b : TwistedOdd)
    (i : BasisQuad) :
    let u' := component false u i.1
    let v' := component false v i.2.1
    let w' := component true w i.2.2.1
    let b' := component true b i.2.2.2
    ∃ B : ℂ → ℂ, AnalyticOnNhd ℂ B doubleSlit ∧
      ∀ {y : ℂ}, ‖y‖ < 1 →
        HasSum (bJointTerm false false v' w' u' b' 1 (Complex.sqrt y)) (B y) := by
  classical
  let u' := component false u i.1
  let v' := component false v i.2.1
  let w' := component true w i.2.2.1
  let b' := component true b i.2.2.2
  change ∃ B : ℂ → ℂ, AnalyticOnNhd ℂ B doubleSlit ∧
    ∀ {y : ℂ}, ‖y‖ < 1 →
      HasSum (bJointTerm false false v' w' u' b' 1 (Complex.sqrt y)) (B y)
  let index : Puncture → BasisIndex
    | .P => i.1
    | .Q => i.2.1
    | .R => i.2.2.1
    | .S => i.2.2.2
  let odd : Puncture → Bool
    | .P => false
    | .Q => false
    | .R => true
    | .S => true
  by_cases h : ∀ t, oddWeight ℒ (index t).1 % 2 = (if odd t then 1 else 0)
  swap
  · obtain ⟨t, ht⟩ := not_forall.mp h
    have hzero (F : HHBBLinear) : F u' v' w' b' = 0 := by
      cases t with
      | P => simp [show u' = 0 from component_eq_zero false u i.1 ht]
      | Q => simp [show v' = 0 from component_eq_zero false v i.2.1 ht]
      | R => simp [show w' = 0 from component_eq_zero true w i.2.2.1 ht]
      | S => simp [show b' = 0 from component_eq_zero true b i.2.2.2 ht]
    refine ⟨fun _ => 0, analyticOnNhd_const, ?_⟩
    intro y _
    have hz : bJointTerm false false v' w' u' b' 1 (Complex.sqrt y) = fun _ => 0 := by
      funext j
      rw [← bLinear_apply]
      exact hzero _
    rw [hz]
    exact hasSum_zero
  obtain ⟨m, slot, colour, n, hmarks⟩ :=
    occupation_monomials_have_marked_words (fun t => (index t).1)
  let l := List.finRange m
  let W := wordAt ℒ slot colour n l
  have hweight (t : Puncture) :
      doubledOccupation slot n l t % 2 = ((if odd t then 1 else 0 : ℕ) : ℤ) := by
    rw [(hmarks t).2]
    exact_mod_cast h t
  have hpar : MixedParity slot n l := ⟨hweight .P, hweight .Q, hweight .R, hweight .S⟩
  let ground (s : Bool) (a : Twisted ℒ leechUnit s) (t : Puncture) :
      ActualGround ℒ leechUnit :=
    ambientBasis.repr a.val (index t) • Pi.single (index t).2 (1 : ℂ)
  have hword (s : Bool) (a : Twisted ℒ leechUnit s) (t : Puncture) (ht : odd t = s) :
      (component s a (index t)).val = W t ⊗ₜ[ℂ] ground s a t := by
    have hp := h t
    rw [ht] at hp
    rw [component, Submodule.coe_smul, project_basis_val, ite_eq_left hp,
      actual_basis_apply ℒ leechUnit (index t).1 (index t).2]
    change ambientBasis.repr a.val (index t) •
        (MvPolynomial.monomial (index t).1 (1 : ℂ) ⊗ₜ[ℂ] Pi.single (index t).2 (1 : ℂ)) =
      W t ⊗ₜ[ℂ] (ambientBasis.repr a.val (index t) • Pi.single (index t).2 (1 : ℂ))
    have hW : W t = MvPolynomial.monomial (index t).1 (1 : ℂ) := (hmarks t).1
    rw [TensorProduct.tmul_smul, hW]
  let p := ground false u .P
  let q := ground false v .Q
  let r := ground true w .R
  let d := ground true b .S
  have hu : u'.val = W .P ⊗ₜ[ℂ] p := hword false u .P rfl
  have hv : v'.val = W .Q ⊗ₜ[ℂ] q := hword false v .Q rfl
  have hw : w'.val = W .R ⊗ₜ[ℂ] r := hword true w .R rfl
  have hb : b'.val = W .S ⊗ₜ[ℂ] d := hword true b .S rfl
  exact ⟨_, hhbb_marked_b_slit_extension slot colour n l hpar u' v' w' b'
    p q r d hu hv hw hb⟩

/-- For all actual HHBB states the B series at outer root one has a
representative analytic on the double slit. The series agreement holds at
each point of the unit disk with the stated principal root. -/
theorem hhbb_native_b_slit_extension (u v : TwistedEven) (w b : TwistedOdd) :
    ∃ B : ℂ → ℂ, AnalyticOnNhd ℂ B doubleSlit ∧
      ∀ {y : ℂ}, ‖y‖ < 1 →
        HasSum (bJointTerm false false v w u b 1 (Complex.sqrt y)) (B y) := by
  classical
  let value (i : BasisQuad) := Classical.choose (component_b_slit_extension u v w b i)
  have hvalue (i : BasisQuad) := Classical.choose_spec (component_b_slit_extension u v w b i)
  refine ⟨fun y => ∑ i ∈ basisTuples u v w b, value i y, ?_, ?_⟩
  · intro y hy
    exact Finset.analyticAt_fun_sum (basisTuples u v w b)
      (fun i _ => (hvalue i).1 y hy)
  · intro y hy₁
    refine (hasSum_sum (s := basisTuples u v w b) fun i _ =>
      (hvalue i).2 hy₁).congr_fun ?_
    intro j
    simpa only [onComponents, bLinear_apply] using
      expand u v w b (bLinear 1 (Complex.sqrt y) j)

/-- The lower equilateral physical cross ratio. -/
def lowerEquilateral : ℂ :=
  ⟨1 / 2, -(Real.sqrt 3 / 2)⟩

/-- Near the lower equilateral point the actual HHBB native B product
extends holomorphically. On the part of the neighborhood inside the unit
disk the literal doubled-mode series sums to the extension at the same
principal root, so the extension equals the canonical HHBB correlation. -/
theorem hhbb_native_b_equilateral_extension (u v : TwistedEven) (w b : TwistedOdd) :
    ∃ (ε : ℝ) (B : ℂ → ℂ), 0 < ε ∧
      AnalyticOnNhd ℂ B (Metric.ball lowerEquilateral ε) ∧
      ∀ y ∈ Metric.ball lowerEquilateral ε, ‖y‖ < 1 →
        HasSum (bJointTerm false false v w u b 1 (Complex.sqrt y)) (B y) ∧
        hhbbCorrelation u v w b 1 y = B y := by
  have hcenter : lowerEquilateral ∈ doubleSlit := by
    apply mem_doubleSlit_of_im
    change -(Real.sqrt 3 / 2) ≠ 0
    exact neg_ne_zero.mpr (ne_of_gt (div_pos (Real.sqrt_pos.2 (by norm_num)) (by norm_num)))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_doubleSlit.mem_nhds hcenter)
  obtain ⟨B, hB, hsum⟩ := hhbb_native_b_slit_extension u v w b
  refine ⟨ε, B, hε, hB.mono hsub, ?_⟩
  intro y hy hy₁
  have hb := hsum hy₁
  exact ⟨hb, by simpa only [hhbbCorrelation, one_mul] using hb.tsum_eq⟩

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBBSlitExtension
