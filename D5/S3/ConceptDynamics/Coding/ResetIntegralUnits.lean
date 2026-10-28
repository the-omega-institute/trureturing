/- GID: D5/S3/ConceptDynamics/Coding/ResetIntegralUnits
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetIntegralUnits
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Coupled golden and Eisenstein units in the original integral reset time ring. -/
import D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
import D5.S3.Arith.Congruence.QuadraticOrderMoments.CalderonReciprocalMoments
import D5.S0.Carrier.AlgebraicModel
import D5.S1.Scale.UnitGroup
import D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore
import D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetIntegralUnits
open Polynomial ResetSignIntegerCyclic ResetIntegralGluing
open scoped QuadraticAlgebra
open D5.S0.Carrier
open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore

private theorem f_two : f 2 = goldenPolynomial := by
  simp [f, S, goldenPolynomial, Finset.sum_range_succ]
  ring
private theorem g_two : g 2 = (X ^ 2 - C (-1) * X + C 1 : ℤ[X]) := by
  simp [g, S, Finset.sum_range_succ]
  ring

def golden : Plus 2 ≃+* GoldenInt :=
  (Ideal.quotEquivOfEq (congrArg (fun p : ℤ[X] => (Ideal.span {p} : Ideal ℤ[X])) f_two)).trans
    goldenAdjoinRootEquiv

def eisenstein : Minus 2 ≃+* EisensteinOrder :=
  (Ideal.quotEquivOfEq
    (congrArg (fun p : ℤ[X] => (Ideal.span {p} : Ideal ℤ[X])) g_two)).trans
      (CalderonReciprocalMoments.coordinateEquiv (-1 : ℤ) 1).toRingEquiv

private theorem common_two :
    reduce (g 2) = (X ^ 2 - C (-1) * X + C 1 : (ZMod 2)[X]) := by
  rw [g_two]
  simp [reduce, CharTwo.sub_eq_add]

def common : Common 2 ≃+* E₂ :=
  (Ideal.quotEquivOfEq (congrArg
    (fun p : (ZMod 2)[X] => (Ideal.span {p} : Ideal (ZMod 2)[X])) common_two)).trans
      (CalderonReciprocalMoments.coordinateEquiv (-1 : ZMod 2) 1).toRingEquiv

def goldenReduce : GoldenInt →+* E₂ where
  toFun z := ⟨(z.a : ZMod 2), (z.b : ZMod 2)⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' z y := by ext <;> simp
  map_mul' z y := by
    ext <;> simp [a_mul, b_mul] <;> ring

private theorem common_plus (z : Plus 2) :
    common (rplus 2 z) = goldenReduce (golden z) := by
  have h : common.toRingHom.comp (rplus 2) =
      goldenReduce.comp golden.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · exact Subsingleton.elim _ _
    · change CalderonReciprocalMoments.rootToCoordinates (-1 : ZMod 2) 1 (AdjoinRoot.mk _ (reduce X)) =
        goldenReduce (goldenAdjoinRootToInt (AdjoinRoot.mk _ X))
      simp [CalderonReciprocalMoments.rootToCoordinates, reduce, goldenAdjoinRootToInt, goldenReduce, phi,
        QuadraticAlgebra.omega]
  exact DFunLike.congr_fun h z

private theorem common_minus (z : Minus 2) :
    common (rminus 2 z) = modTwo (eisenstein z) := by
  have h : common.toRingHom.comp (rminus 2) =
      modTwo.comp eisenstein.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · exact Subsingleton.elim _ _
    · change CalderonReciprocalMoments.rootToCoordinates (-1 : ZMod 2) 1 (AdjoinRoot.mk _ (reduce X)) =
        modTwo (CalderonReciprocalMoments.rootToCoordinates (-1 : ℤ) 1 (AdjoinRoot.mk _ X))
      simp [CalderonReciprocalMoments.rootToCoordinates, reduce, modTwo, QuadraticAlgebra.omega]
  exact DFunLike.congr_fun h z

private theorem common_field_data : IsField (Common 2) ∧ Nat.card (Common 2) = 4 := by
  let I : Ideal EisensteinOrder := Ideal.span {(2 : EisensteinOrder)}
  obtain ⟨hm,hc,_,e,_,_⟩ :=
    D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.inert_eisenstein_quotient_frobenius
      2 (by decide)
  letI : I.IsMaximal := hm
  letI : Field (EisensteinOrder ⧸ I) := Ideal.Quotient.field I
  have hf : IsField E₂ := e.symm.toMulEquiv.isField (Field.toIsField _)
  refine ⟨common.toMulEquiv.isField hf, ?_⟩
  calc
    Nat.card (Common 2) = Nat.card E₂ := Nat.card_congr common.toEquiv
    _ = Nat.card (EisensteinOrder ⧸ I) := Nat.card_congr e.symm.toEquiv
    _ = 4 := hc

/-- Literal coefficient charts and the field of four elements, with fixed root orientation. -/
theorem quadratic_charts :
    IsField (Common 2) ∧ Nat.card (Common 2) = 4 ∧
    golden (AdjoinRoot.root (f 2)) = phi ∧
    eisenstein (AdjoinRoot.root (g 2)) = QuadraticAlgebra.omega ∧
    common (AdjoinRoot.root (reduce (g 2))) = QuadraticAlgebra.omega ∧
    (∀ z : Plus 2, common (rplus 2 z) = goldenReduce (golden z)) ∧
    (∀ z : Minus 2, common (rminus 2 z) = modTwo (eisenstein z)) := by
  refine ⟨common_field_data.1, common_field_data.2, ?_, ?_, ?_,
    common_plus, common_minus⟩
  · change goldenAdjoinRootToInt (AdjoinRoot.mk _ X) = phi
    exact AdjoinRoot.lift_root _
  · change CalderonReciprocalMoments.rootToCoordinates (-1 : ℤ) 1 (AdjoinRoot.mk _ X) = QuadraticAlgebra.omega
    simp [CalderonReciprocalMoments.rootToCoordinates]
  · change CalderonReciprocalMoments.rootToCoordinates (-1 : ZMod 2) 1 (AdjoinRoot.mk _ X) = QuadraticAlgebra.omega
    simp [CalderonReciprocalMoments.rootToCoordinates]

def goldenComponent : QF 2 →+* GoldenInt := golden.toRingHom.comp (plus 2)
def eisensteinComponent : QF 2 →+* EisensteinOrder := eisenstein.toRingHom.comp (minus 2)

private theorem component_compatibility (z : QF 2) :
    goldenReduce (goldenComponent z) = modTwo (eisensteinComponent z) := by
  change goldenReduce (golden (plus 2 z)) = modTwo (eisenstein (minus 2 z))
  rw [← quadratic_charts.2.2.2.2.2.1, ← quadratic_charts.2.2.2.2.2.2]
  exact congrArg common ((toCompatible 2 z).property)


private theorem F_two : F 2 = X ^ 4 - X ^ 2 - 2 * X - 1 := by
  simp [F, S, Finset.sum_range_succ]
  ring

private theorem x_inverse : fp 2 X * fp 2 (X ^ 3 - X - 2) = 1 := by
  apply sub_eq_zero.mp
  rw [← map_one (fp 2), ← map_mul, ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  have h : X * (X ^ 3 - X - 2) - 1 = F 2 := by rw [F_two]; ring
  rw [h]

/-- Literal forward time, with its integral inverse polynomial. -/
def xUnit : (QF 2)ˣ where
  val := fp 2 X
  inv := fp 2 (X ^ 3 - X - 2)
  val_inv := x_inverse
  inv_val := by simpa only [mul_comm] using x_inverse

/-- The original sign involution, with itself as inverse. -/
def wUnit : (QF 2)ˣ where
  val := fp 2 (W 2)
  inv := fp 2 (W 2)
  val_inv := sign_square 2
  inv_val := sign_square 2

private def goldenUnits : (QF 2)ˣ →* GoldenIntˣ := Units.map goldenComponent
private def eisensteinUnits : (QF 2)ˣ →* EisensteinOrderˣ := Units.map eisensteinComponent

private theorem golden_x : goldenUnits xUnit = phiUnit := by
  apply Units.ext
  change goldenAdjoinRootToInt (AdjoinRoot.mk _ X) = phi
  exact AdjoinRoot.lift_root _

private theorem golden_w : goldenUnits wUnit = 1 := by
  apply Units.ext
  change golden (plus 2 (fp 2 (W 2))) = 1
  rw [show plus 2 (fp 2 (W 2)) = 1 from congrArg Prod.fst (gluing_generators 2).2.1]
  exact map_one golden

private theorem eisenstein_w : eisensteinUnits wUnit = -1 := by
  apply Units.ext
  change eisenstein (minus 2 (fp 2 (W 2))) = -1
  rw [show minus 2 (fp 2 (W 2)) = -1 from congrArg Prod.snd (gluing_generators 2).2.1]
  simp

private theorem golden_neg : goldenUnits (-1) = -1 := by
  apply Units.ext
  change goldenComponent (-1) = -1
  simp

private theorem components_injective :
    Function.Injective (fun u : (QF 2)ˣ => (goldenUnits u, eisensteinUnits u)) := by
  intro u v h
  apply Units.ext
  apply (gluing 2).injective
  apply Subtype.ext
  apply Prod.ext
  · apply golden.injective
    exact congrArg (fun p : GoldenIntˣ × EisensteinOrderˣ => (p.1 : GoldenInt)) h
  · apply eisenstein.injective
    exact congrArg (fun p : GoldenIntˣ × EisensteinOrderˣ => (p.2 : EisensteinOrder)) h

private theorem golden_kernel (u : (QF 2)ˣ) (hu : goldenUnits u = 1) :
    u = 1 ∨ u = wUnit := by
  have hm : modTwo (eisensteinUnits u : EisensteinOrder) = 1 := by
    change modTwo (eisensteinComponent (u : QF 2)) = 1
    rw [← component_compatibility]
    change goldenReduce (goldenUnits u : GoldenInt) = 1
    rw [hu, Units.val_one, map_one]
  have hi := unit_modTwo (eisensteinUnits u) hm
  have hn := norm_unit_one (eisensteinUnits u)
  simp only [QuadraticAlgebra.norm_def, hi, mul_zero, zero_mul, sub_zero] at hn
  have hr : (eisensteinUnits u : EisensteinOrder).re = 1 ∨
      (eisensteinUnits u : EisensteinOrder).re = -1 := by
    have hf : ((eisensteinUnits u : EisensteinOrder).re - 1) *
        ((eisensteinUnits u : EisensteinOrder).re + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with h | h
    · left; linarith
    · right; linarith
  rcases hr with hr | hr
  · left
    apply components_injective
    apply Prod.ext
    · simpa only [map_one] using hu
    · change eisensteinUnits u = eisensteinUnits 1
      rw [map_one]
      apply Units.ext
      apply QuadraticAlgebra.ext <;> simp [hi, hr]
  · right
    apply components_injective
    apply Prod.ext
    · simpa only [golden_w] using hu
    · change eisensteinUnits u = eisensteinUnits wUnit
      rw [eisenstein_w]
      apply Units.ext
      apply QuadraticAlgebra.ext <;> simp [hi, hr]

/-- Independent scalar sign, original sign involution, and arbitrary signed time. -/
def normal (n : ℤ) (a b : Fin 2) : (QF 2)ˣ :=
  (-1) ^ a.val * wUnit ^ b.val * xUnit ^ n

private def signBool (a : Fin 2) : Bool := decide (a.val = 1)

private theorem normal_golden (n : ℤ) (a b : Fin 2) :
    (goldenUnits (normal n a b) : GoldenInt) = signedPhiPower (signBool a) n := by
  simp only [normal, map_mul, map_pow, map_zpow, golden_neg, golden_w, golden_x,
    one_pow, mul_one]
  fin_cases a <;> simp [signBool, signedPhiPower]

private theorem normal_exists (u : (QF 2)ˣ) :
    ∃ n : ℤ, ∃ a b : Fin 2, u = normal n a b := by
  obtain ⟨s,n,hn⟩ := (D5.S1.Scale.golden_units_eq_signed_phi_pow
    (goldenUnits u : GoldenInt)).mp (goldenUnits u).isUnit
  let a : Fin 2 := if s then 1 else 0
  let base := normal n a 0
  have hb : goldenUnits base = goldenUnits u := by
    apply Units.ext
    rw [normal_golden]
    cases s <;> simpa [a, signBool] using hn.symm
  let v := u * base⁻¹
  have hv : goldenUnits v = 1 := by simp [v, hb]
  obtain hv | hv := golden_kernel v hv
  · refine ⟨n,a,0,?_⟩
    have he : u = v * base := by simp [v]
    simpa only [hv, one_mul] using he
  · refine ⟨n,a,1,?_⟩
    calc
      u = v * base := by simp [v]
      _ = normal n a 1 := by rw [hv]; simp [base, normal]; ac_rfl

private theorem normal_injective {n m : ℤ} {a b c d : Fin 2}
    (h : normal n a b = normal m c d) : n = m ∧ a = c ∧ b = d := by
  have hg := congrArg (fun u : (QF 2)ˣ => (goldenUnits u : GoldenInt)) h
  rw [normal_golden, normal_golden] at hg
  have hs := D5.S1.Scale.signedPhiPower_unique hg
  have ha : a = c := by
    fin_cases a <;> fin_cases c <;> simp_all [signBool]
  obtain rfl := hs.2
  obtain rfl := ha
  have hw : wUnit ^ b.val = wUnit ^ d.val :=
    mul_left_cancel (mul_right_cancel h)
  have he := congrArg eisensteinUnits hw
  simp only [map_pow, eisenstein_w] at he
  have hb : b = d := by
    fin_cases b <;> fin_cases d <;> try rfl
    all_goals have hr := congrArg (fun u : EisensteinOrderˣ => (u : EisensteinOrder).re) he
              norm_num at hr
  exact ⟨rfl,rfl,hb⟩

/-- Every integral unit has a unique signed time and two independent signs. -/
theorem unit_normal_form (u : (QF 2)ˣ) :
    ∃! p : ℤ × Fin 2 × Fin 2, u = normal p.1 p.2.1 p.2.2 := by
  obtain ⟨n,a,b,h⟩ := normal_exists u
  refine ⟨(n,a,b),h,?_⟩
  rintro ⟨m,c,d⟩ he
  obtain ⟨hn,ha,hb⟩ := normal_injective (he.symm.trans h)
  exact Prod.ext hn (Prod.ext ha hb)

private theorem w_square : wUnit ^ 2 = 1 := by
  apply Units.ext
  change (wUnit : QF 2) ^ 2 = 1
  simpa only [wUnit, pow_two] using sign_square 2

private theorem torsion_pow_add (u : (QF 2)ˣ) (hu : u ^ 2 = 1) (a b : ZMod 2) :
    u ^ (a + b).val = u ^ a.val * u ^ b.val := by
  fin_cases a <;> fin_cases b
  · change u ^ (0 : ℕ) = u ^ (0 : ℕ) * u ^ (0 : ℕ); simp
  · change u ^ (1 : ℕ) = u ^ (0 : ℕ) * u ^ (1 : ℕ); simp
  · change u ^ (1 : ℕ) = u ^ (1 : ℕ) * u ^ (0 : ℕ); simp
  · change u ^ (0 : ℕ) = u ^ (1 : ℕ) * u ^ (1 : ℕ)
    simpa only [pow_zero, pow_one, ← pow_two] using hu.symm

/-- Parameters are ordered as signed time, scalar sign, then original sign. -/
def parameterHom : Multiplicative ℤ × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* (QF 2)ˣ where
  toFun p := normal p.1.toAdd p.2.1.toAdd p.2.2.toAdd
  map_one' := by
    change (-1 : (QF 2)ˣ) ^ (0 : ℕ) * wUnit ^ (0 : ℕ) * xUnit ^ (0 : ℤ) = 1
    simp
  map_mul' p r := by
    change (-1) ^ (p.2.1.toAdd + r.2.1.toAdd).val *
      wUnit ^ (p.2.2.toAdd + r.2.2.toAdd).val * xUnit ^ (p.1.toAdd + r.1.toAdd) =
      ((-1) ^ p.2.1.toAdd.val * wUnit ^ p.2.2.toAdd.val * xUnit ^ p.1.toAdd) *
      ((-1) ^ r.2.1.toAdd.val * wUnit ^ r.2.2.toAdd.val * xUnit ^ r.1.toAdd)
    rw [torsion_pow_add (-1) (by simp), torsion_pow_add wUnit w_square, zpow_add]
    ac_rfl

private theorem parameter_bijective : Function.Bijective parameterHom := by
  constructor
  · rintro ⟨n,a,b⟩ ⟨m,c,d⟩ h
    obtain ⟨hn,ha,hb⟩ := normal_injective h
    exact Prod.ext (Multiplicative.toAdd.injective hn)
      (Prod.ext (Multiplicative.toAdd.injective ha) (Multiplicative.toAdd.injective hb))
  · intro u
    obtain ⟨n,a,b,h⟩ := normal_exists u
    exact ⟨(Multiplicative.ofAdd n, Multiplicative.ofAdd a, Multiplicative.ofAdd b), h.symm⟩

/-- The unit group, with the literal forward-time and sign orientation. -/
def unitsEquiv : (QF 2)ˣ ≃*
    Multiplicative ℤ × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
  (MulEquiv.ofBijective parameterHom parameter_bijective).symm

end D5.S3.ConceptDynamics.Coding.ResetIntegralUnits
