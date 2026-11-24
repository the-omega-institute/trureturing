/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeFullMixedField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeFullMixedField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full twisted mixed coefficients from the two actual parity projections. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedMultiplicityOne
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParityEvenExclusion
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParityOddCurrent

/-! The fixed-source signed identities transport to the two actual twisted
parities. The stress mode determines which components can occur at each
doubled exponent, and the Leech channel theorems determine their coefficients. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFullMixedField

open LatticeGeneratingFieldLocality hiding paritySign epsilon
open LatticeInvolution LatticePositiveEnergy
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticeHalfFockParityT
open HalfFock.LatticeHalfFockParityField
open StateFieldResidueReconstruction (integerBinomial epsilon)
open ActualLeechHyperbolic (leechData)
open NativeOddTwistedIntertwiner
open private mem_parity paritySign_not J_val odd_even_exponent_zero
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private fixedAction_val zeroSignedFinsum stress stress_action stress_odd_zero stress_odd_one
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTopDetection
open private oddPart oddPart_grade oddPart_on_odd
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddZhuTopBalance

noncomputable section

variable {D : LatticeData} {hu : IsUnit D.G.det}

/-- The actual fixed-source mode on the entire twisted tensor. -/
def ambientFixedMode (a : FixedCarrier D) (m : ℤ) : Module.End ℂ (ActualTensor D hu) :=
  (correctedField D hu a.val).coeff (-2*m-2)

/-- The exponent `e` labels physical mode `-e/2-1` in the mixed coefficient. -/
abbrev Coefficients (D : LatticeData) (hu : IsUnit D.G.det) :=
  ℤ → OddCarrier D →ₗ[ℂ] ActualTensor D hu →ₗ[ℂ] ActualTensor D hu

/-- The signed fixed-source Borcherds identity on the doubled exponent grid. -/
def signedBorcherds (F : Coefficients D hu) (a : FixedCarrier D) (b : OddCarrier D)
    (v : ActualTensor D hu) (p e r : ℤ) : Prop :=
  let left := fun i : ℕ => integerBinomial p i • F (e-2*(p-i)) (oddMode D a (r+i) b) v
  let first := fun i : ℕ => (((-1 : ℂ)^i) * integerBinomial r i) •
    ambientFixedMode a (p+r-i) (F (e-2*i) b v)
  let second := fun i : ℕ => (((-1 : ℂ)^i) * integerBinomial r i) •
    (epsilon r • F (e-2*(r-i)) b (ambientFixedMode a (p+i) v))
  Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
    Function.HasFiniteSupport second ∧
    (∑ᶠ i, left i) = (∑ᶠ i, first i) - (∑ᶠ i, second i)

/-- Lower-truncated fields on the actual tensor, with physical translation
and the fixed-source signed Borcherds identity. -/
structure LawfulField (D : LatticeData) (hu : IsUnit D.G.det) where
  coeff : Coefficients D hu
  truncation : ∀ b v, ∃ B : ℤ, ∀ e < B, coeff e b v = 0
  derivative : ∀ b v (e : ℤ), coeff e (oddTranslation D b) v =
    ((e : ℂ) / 2 + 1) • coeff (e+2) b v
  borcherds : ∀ a b v p e r, signedBorcherds coeff a b v p e r

private theorem parity_sq (v : ActualTensor D hu) :
    actualParity D hu (actualParity D hu v) = v := by
  have h : (actualParity D hu).comp (actualParity D hu) = LinearMap.id := by
    unfold actualParity
    rw [← TensorProduct.map_comp]
    have hs : (sigmaLinear D).comp (sigmaLinear D) = LinearMap.id :=
      LinearMap.ext (sigma_involutive D)
    rw [hs, LinearMap.id_comp, TensorProduct.map_id]
  exact LinearMap.congr_fun h v

/-- Projection onto the actual twisted sign eigenspace. -/
def project (s : Bool) : ActualTensor D hu →ₗ[ℂ] Twisted D hu s :=
  LinearMap.codRestrict _
    ((2 : ℂ)⁻¹ • (LinearMap.id + paritySign s • actualParity D hu)) (fun v => by
      apply (mem_parity D hu _ _).mpr
      simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
        map_smul, map_add, parity_sq]
      cases s <;> norm_num [paritySign] <;> module)

private theorem project_val (s : Bool) (v : ActualTensor D hu) :
    (project s v).val = (2 : ℂ)⁻¹ • (v + paritySign s • actualParity D hu v) := rfl

private theorem project_split (v : ActualTensor D hu) :
    (project false v).val + (project true v).val = v := by
  simp only [project_val, paritySign, Bool.false_eq_true, ↓reduceIte, one_smul, neg_one_smul]
  module

set_option maxHeartbeats 600000 in
private theorem project_on (s t : Bool) (v : Twisted D hu s) :
    (project t v.val).val = if t = s then v.val else 0 := by
  rw [project_val, (mem_parity D hu _ _).mp v.property, smul_smul]
  cases s <;> cases t <;> norm_num [paritySign] <;> module

private theorem ambientFixedMode_on (s : Bool) (a : FixedCarrier D) (m : ℤ)
    (v : Twisted D hu s) :
    (fixedAction s a m v).val = ambientFixedMode a m v.val :=
  fixedAction_val s a m v

private theorem project_fixed (t : Bool) (a : FixedCarrier D) (m : ℤ)
    (v : ActualTensor D hu) :
    project t (ambientFixedMode a m v) = fixedAction t a m (project t v) := by
  apply Subtype.ext
  rw [project_val, fixedAction_val, project_val]
  have h : actualParity D hu (ambientFixedMode a m v) =
      ambientFixedMode a m (actualParity D hu v) := by
    unfold ambientFixedMode
    rw [correctedField_target_parity, (mem_fixedSpace D a.val).mp a.property]
  change _ = ambientFixedMode a m _
  rw [h, map_smul, map_add, map_smul]

private def component (F : LawfulField D hu) (s t : Bool) (e : ℤ) :
    OddCarrier D →ₗ[ℂ] Twisted D hu s →ₗ[ℂ] Twisted D hu t where
  toFun b := (project t).comp ((F.coeff e b).comp (paritySpace D hu (paritySign s)).subtype)
  map_add' b c := LinearMap.ext fun _ => by simp
  map_smul' z b := LinearMap.ext fun _ => by simp

private theorem project_borcherds (F : LawfulField D hu) (s t : Bool)
    (a : FixedCarrier D) (b : OddCarrier D) (v : Twisted D hu s) (p e r : ℤ) :
    let left := fun i : ℕ =>
      integerBinomial p i • component F s t (e-2*(p-i)) (oddMode D a (r+i) b) v
    let first := fun i : ℕ => (((-1 : ℂ)^i) * integerBinomial r i) •
      fixedAction t a (p+r-i) (component F s t (e-2*i) b v)
    let second := fun i : ℕ => (((-1 : ℂ)^i) * integerBinomial r i) •
      (epsilon r • component F s t (e-2*(r-i)) b (fixedAction s a (p+i) v))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
      (∑ᶠ i, left i) = (∑ᶠ i, first i) - (∑ᶠ i, second i) := by
  have law := F.borcherds a b v.val p e r
  dsimp only [signedBorcherds] at law
  obtain ⟨hl, hf, hs, he⟩ := law
  have mapped (f : ℕ → ActualTensor D hu) (h : Function.HasFiniteSupport f) :
      (fun i => project t (f i)).HasFiniteSupport := h.subset (fun i hi => by
    contrapose! hi
    simp [Function.notMem_support.mp hi])
  have he' := congrArg (project t) he
  have map_sum (f : ℕ → ActualTensor D hu) (h : Function.HasFiniteSupport f) :
      project t (∑ᶠ i, f i) = ∑ᶠ i, project t (f i) :=
    (project t).toAddMonoidHom.map_finsum h
  rw [map_sub, map_sum _ hl, map_sum _ hf, map_sum _ hs] at he'
  exact ⟨by simpa only [component, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      Submodule.subtype_apply, map_smul] using mapped _ hl,
    by simpa only [component, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      Submodule.subtype_apply, map_smul, project_fixed] using mapped _ hf,
    by simpa only [component, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      Submodule.subtype_apply, map_smul, ambientFixedMode_on s] using mapped _ hs,
    by simpa only [component, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      Submodule.subtype_apply, LinearMap.toAddMonoidHom_coe, map_smul, project_fixed,
      ambientFixedMode_on s] using he'⟩

private lemma component_truncation (F : LawfulField D hu) (s t : Bool) (k : ℤ)
    (b : OddCarrier D) (v : Twisted D hu s) :
    ∃ N : ℤ, ∀ n ≥ N, component F s t (-2*n-k) b v = 0 := by
  obtain ⟨B, hB⟩ := F.truncation b v.val
  refine ⟨(1-B-k)/2+1, fun n hn => ?_⟩
  change project t (F.coeff (-2*n-k) b v.val) = 0
  rw [hB _ (by omega), map_zero]

private lemma component_derivative (F : LawfulField D hu) (s t : Bool)
    (b : OddCarrier D) (v : Twisted D hu s) (e : ℤ) :
    component F s t e (oddTranslation D b) v =
      ((e : ℂ) / 2 + 1) • component F s t (e+2) b v := by
  change project t (F.coeff e (oddTranslation D b) v.val) = _
  rw [F.derivative, map_smul]
  rfl

private def integralDiagonal (F : LawfulField D hu) (s : Bool) :
    NativeSameParity.LawfulField D hu s where
  coeff n := component F s s (-2*n-2)
  truncation := component_truncation F s s 2
  derivative b v n := by
    have h := component_derivative F s s b v (-2*n-2)
    rw [show -2*n-2+2 = -2*(n-1)-2 by omega] at h
    convert h using 2
    push_cast
    ring
  borcherds a b v p q r := by
    have h := project_borcherds F s s a b v p (-2*q-2) r
    dsimp only [NativeSameParity.signedBorcherds] at h ⊢
    simp only [show ∀ i : ℕ, -2*q-2-2*(p-i) = -2*(p+q-i)-2 by intro; omega,
      show ∀ i : ℕ, -2*q-2-2*i = -2*(q+i)-2 by intro; omega,
      show ∀ i : ℕ, -2*q-2-2*(r-i) = -2*(q+r-i)-2 by intro; omega] at h
    exact h

private def halfIntegralOffDiagonal (F : LawfulField D hu) (s : Bool) :
    LawfulMixedField D hu s where
  coeff n := component F s (!s) (-2*n-3)
  truncation := component_truncation F s (!s) 3
  derivative b v n := by
    have h := component_derivative F s (!s) b v (-2*n-3)
    rw [show -2*n-3+2 = -2*(n-1)-3 by omega] at h
    convert h using 2
    push_cast
    ring
  borcherds a b v p q r := by
    have h := project_borcherds F s (!s) a b v p (-2*q-3) r
    dsimp only [mixedBorcherds] at h ⊢
    simp only [show ∀ i : ℕ, -2*q-3-2*(p-i) = -2*(p+q-i)-3 by intro; omega,
      show ∀ i : ℕ, -2*q-3-2*i = -2*(q+i)-3 by intro; omega,
      show ∀ i : ℕ, -2*q-3-2*(r-i) = -2*(q+r-i)-3 by intro; omega] at h
    exact h

private theorem mixed_ext (s : Bool) (H G : LawfulMixedField D hu s)
    (h : H.coeff = G.coeff) : H = G := by
  cases H
  cases G
  congr

/-- On the full actual field, the integral diagonal coefficients vanish and
each half-integral off-diagonal block is a unique multiple of the native field. -/
theorem leech_projected_classification (F : LawfulField leechData leechUnit) (s : Bool) :
    (∀ n b (v : Twisted leechData leechUnit s), project s (F.coeff (-2*n-2) b v.val) = 0) ∧
    (∃! z : ℂ, ∀ n b (v : Twisted leechData leechUnit s),
      project (!s) (F.coeff (-2*n-3) b v.val) = z • J leechData leechUnit s n b v) := by
  constructor
  · have hz : (integralDiagonal F s).coeff = 0 := by
      cases s
      · exact NativeSameParity.leech_even_sameParity_coeff_eq_zero (integralDiagonal F false)
      · exact NativeSameParity.OddDirectional.leech_odd_sameParity_coeff_eq_zero
          (integralDiagonal F true)
    intro n b v
    exact LinearMap.congr_fun (LinearMap.congr_fun (congrFun hz n) b) v
  · let H := halfIntegralOffDiagonal F s
    obtain ⟨z, hz, hu⟩ := leech_mixed_multiplicity_one s H
    have equivalence (c : ℂ) : H = (nativeMixedField leechData leechUnit s).scale c ↔
        ∀ n b (v : Twisted leechData leechUnit s),
          project (!s) (F.coeff (-2*n-3) b v.val) = c • J leechData leechUnit s n b v := by
      constructor
      · intro he n b v
        exact congrArg (fun G : LawfulMixedField leechData leechUnit s => G.coeff n b v) he
      · intro he
        let G := (nativeMixedField leechData leechUnit s).scale c
        change H = G
        have hc : H.coeff = G.coeff := by
          funext n
          exact LinearMap.ext fun b => LinearMap.ext fun v => he n b v
        exact mixed_ext s H G hc
    exact ⟨z, (equivalence z).mp hz, fun y hy => hu y ((equivalence y).mpr hy)⟩


private theorem ambient_stress (v : ActualTensor D hu) :
    ambientFixedMode (stress D) 1 v = actualTensorL0 D hu v := by
  rw [← project_split v, map_add, map_add]
  rw [← ambientFixedMode_on false, ← ambientFixedMode_on true, stress_action, stress_action]

private theorem ambient_commutator_one (F : LawfulField D hu) (a : FixedCarrier D)
    (b : OddCarrier D) (v : ActualTensor D hu) (e : ℤ) :
    ambientFixedMode a 1 (F.coeff e b v) - F.coeff e b (ambientFixedMode a 1 v) =
      F.coeff (e-2) (oddMode D a 0 b) v + F.coeff e (oddMode D a 1 b) v := by
  classical
  let term (i : ℕ) := integerBinomial 1 i • F.coeff (e-2*(1-i)) (oddMode D a i b) v
  have h := (F.borcherds a b v 1 e 0).2.2.2
  dsimp only [signedBorcherds] at h
  rw [zeroSignedFinsum, zeroSignedFinsum] at h
  simp only [Nat.cast_zero, add_zero, sub_zero, mul_zero, zero_add,
    epsilon, zpow_zero, one_smul] at h
  change (∑ᶠ i, term i) = _ at h
  have hsupp : Function.support term ⊆ (↑(Finset.range 2) : Set ℕ) := by
    intro i hi
    by_contra hout
    simp only [Finset.mem_coe, Finset.mem_range] at hout
    have hz : Ring.choose (1 : ℤ) i = 0 := by
      change Ring.choose ((1 : ℕ) : ℤ) i = 0
      simp only [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega : 1 < i), Nat.cast_zero]
    exact hi (by simp [term, integerBinomial, hz])
  rw [← h, finsum_eq_sum_of_support_subset _ hsupp]
  simp [Finset.sum_range_succ, term, integerBinomial]

private theorem ambient_energy (F : LawfulField D hu) (e h : ℤ) (M : ℕ)
    (b : OddCarrier D) (hb : b.val ∈ grade D h)
    (v : ActualTensor D hu) (hv : v ∈ actualGrade D hu M) :
    actualTensorL0 D hu (F.coeff e b v) =
      ((D.rank : ℂ) / 16 + (((M : ℤ) + 2*h + e : ℤ) : ℂ) / 2) • F.coeff e b v := by
  have hvL : actualTensorL0 D hu v = ((D.rank : ℂ) / 16 + (M : ℂ) / 2) • v := by
    simpa only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] using hv
  have hcomm := ambient_commutator_one F (stress D) b v e
  rw [ambient_stress, ambient_stress, stress_odd_zero hu, stress_odd_one hu h b hb, hvL,
    F.derivative b v (e-2), show e-2+2 = e by omega] at hcomm
  simp only [map_smul, LinearMap.smul_apply] at hcomm
  rw [sub_eq_iff_eq_add] at hcomm
  rw [hcomm, ← add_smul, ← add_smul]
  congr 1
  push_cast
  ring

private theorem parity_of_energy (N : ℤ) (x : ActualTensor D hu)
    (hx : actualTensorL0 D hu x = ((D.rank : ℂ) / 16 + (N : ℂ) / 2) • x) :
    actualParity D hu x = (-1 : ℂ)^N • x := by
  by_cases hz : x = 0
  · simp [hz]
  let B := actualAmbientBasis D hu
  have hrepr : B.repr x ≠ 0 := fun h => hz (B.repr.injective (h.trans (map_zero _).symm))
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hrepr
  have hc := congrArg (fun v => B.repr v i) hx
  rw [actualTensorL0_repr] at hc
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
  have hscalar := mul_right_cancel₀ (Finsupp.mem_support_iff.mp hi) hc
  have heq : (oddWeight D i.1 : ℂ) = (N : ℂ) := by linear_combination 2 * hscalar
  have heq' : (oddWeight D i.1 : ℤ) = N := by exact_mod_cast heq
  have hm : x ∈ actualGrade D hu (oddWeight D i.1) := by
    simpa only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero, ← heq] using hx
  rw [← heq', zpow_natCast]
  exact actualParity_on_actualGrade D hu _ ⟨x, hm⟩

private theorem exponent_sign (M : ℕ) (h e : ℤ) :
    (-1 : ℂ)^((M : ℤ)+2*h+e) = (-1 : ℂ)^e * (-1 : ℂ)^M := by
  have hn : (-1 : ℂ) ≠ 0 := by norm_num
  have h2 : (-1 : ℂ)^(2*h) = 1 := by rw [zpow_mul]; norm_num
  rw [zpow_add₀ hn, zpow_add₀ hn, h2, mul_one, zpow_natCast, mul_comm]

private theorem coeff_parity (F : LawfulField D hu) (e : ℤ)
    (b : OddCarrier D) (v : ActualTensor D hu) :
    actualParity D hu (F.coeff e b v) = (-1 : ℂ)^e • F.coeff e b (actualParity D hu v) := by
  classical
  have homogeneous (h : ℤ) (c : OddCarrier D) (hc : c.val ∈ grade D h) :
      actualParity D hu (F.coeff e c v) =
        (-1 : ℂ)^e • F.coeff e c (actualParity D hu v) := by
    let B := actualAmbientBasis D hu
    let L := (actualParity D hu).comp (F.coeff e c)
    let R := (-1 : ℂ)^e • (F.coeff e c).comp (actualParity D hu)
    have hlr : L = R := by
      apply B.ext
      rintro ⟨d, j⟩
      let M := oddWeight D d
      let x := B (d, j)
      have hx : x ∈ actualGrade D hu M :=
        actualGradeVector_mem D hu M ⟨⟨d, rfl⟩, j⟩
      change actualParity D hu (F.coeff e c x) = (-1 : ℂ)^e • F.coeff e c (actualParity D hu x)
      rw [parity_of_energy _ _ (ambient_energy F e h M c hc x hx),
        actualParity_on_actualGrade D hu M ⟨x, hx⟩, map_smul, smul_smul, exponent_sign]
    exact LinearMap.congr_fun hlr v
  let part (h : ℤ) := oddPart D (gradeProjection D h b.val)
  have hsum : (∑ h ∈ stateEnergies D b.val, part h) = b := by
    simp only [part, ← map_sum, sum_gradeProjections, oddPart_on_odd]
  let L := (actualParity D hu).comp ((LinearMap.applyₗ v).comp (F.coeff e))
  let R := (-1 : ℂ)^e • (LinearMap.applyₗ (actualParity D hu v)).comp (F.coeff e)
  change L b = R b
  rw [← hsum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro h _
  exact homogeneous h (part h)
    (oddPart_grade h ⟨gradeProjection D h b.val, gradeProjection_mem D h b.val⟩)

private theorem even_diagonal (F : LawfulField D hu) (s : Bool)
    (e : ℤ) (he : Even e) (b : OddCarrier D) (v : Twisted D hu s) :
    (project s (F.coeff e b v.val)).val = F.coeff e b v.val := by
  have h := coeff_parity F e b v.val
  rw [neg_one_zpow_eq_ite, ite_eq_left he, one_smul,
    (mem_parity D hu _ _).mp v.property, map_smul] at h
  let w : Twisted D hu s := ⟨_, (mem_parity D hu _ _).mpr h⟩
  simpa only [ite_eq_left rfl, ite_true] using project_on s s w

private theorem odd_offDiagonal (F : LawfulField D hu) (s : Bool)
    (e : ℤ) (he : ¬ Even e) (b : OddCarrier D) (v : Twisted D hu s) :
    (project (!s) (F.coeff e b v.val)).val = F.coeff e b v.val := by
  have h := coeff_parity F e b v.val
  rw [neg_one_zpow_eq_ite, ite_eq_right he, (mem_parity D hu _ _).mp v.property,
    map_smul, smul_smul, neg_one_mul, ← paritySign_not] at h
  let w : Twisted D hu (!s) := ⟨_, (mem_parity D hu _ _).mpr h⟩
  simpa only [ite_eq_left rfl, ite_true] using project_on (!s) (!s) w

/-- Every full field has zero integral modes and two uniquely determined
native components. The formula holds on all actual tensors at every doubled
exponent, including inhomogeneous inputs. -/
theorem leech_full_classification (F : LawfulField leechData leechUnit) :
    (∀ e, Even e → ∀ b v, F.coeff e b v = 0) ∧
    (∃! z : Bool → ℂ, ∀ e b v, F.coeff e b v =
      z false • (correctedField leechData leechUnit b.val).coeff e (project false v).val +
      z true • (correctedField leechData leechUnit b.val).coeff e (project true v).val) := by
  let q := leech_projected_classification F
  have evenOn (s : Bool) (e : ℤ) (he : Even e) (b : OddCarrier leechData)
      (v : Twisted leechData leechUnit s) : F.coeff e b v.val = 0 := by
    obtain ⟨k, hk⟩ := he
    let n := -k-1
    have he' : e = -2*n-2 := by dsimp [n]; omega
    have hz := congrArg Subtype.val ((q s).1 n b v)
    rw [← he', even_diagonal F s e ⟨k, hk⟩ b v] at hz
    exact hz
  have evenAll (e : ℤ) (he : Even e) (b : OddCarrier leechData)
      (v : ActualTensor leechData leechUnit) : F.coeff e b v = 0 := by
    rw [← project_split v, map_add,
      evenOn false e he b (project false v), evenOn true e he b (project true v), add_zero]
  refine ⟨evenAll, ?_⟩
  classical
  let z (s : Bool) : ℂ := Classical.choose (q s).2
  have hz (s : Bool) := (Classical.choose_spec (q s).2).1
  have atParity (s : Bool) (e : ℤ) (b : OddCarrier leechData)
      (v : Twisted leechData leechUnit s) : F.coeff e b v.val =
        z s • (correctedField leechData leechUnit b.val).coeff e v.val := by
    by_cases he : Even e
    · rw [evenOn s e he, odd_even_exponent_zero leechData leechUnit b e he, smul_zero]
    · let n := -(e+3)/2
      have he' : e = -2*n-3 := by
        simp only [even_iff_two_dvd] at he
        dsimp [n]
        omega
      have h := congrArg Subtype.val (hz s n b v)
      change (project (!s) (F.coeff (-2*n-3) b v.val)).val =
        z s • (J leechData leechUnit s n b v).val at h
      rw [J_val, ← he', odd_offDiagonal F s e he b v] at h
      exact h
  refine ⟨z, ?_, ?_⟩
  · intro e b v
    conv_lhs => rw [← project_split v, map_add]
    rw [atParity, atParity]
  · intro y hy
    funext s
    apply (Classical.choose_spec (q s).2).2 (y s)
    intro n b v
    apply Subtype.ext
    have he : ¬ Even (-2*n-3) := by simp only [even_iff_two_dvd]; omega
    change (project (!s) (F.coeff (-2*n-3) b v.val)).val =
      y s • (J leechData leechUnit s n b v).val
    rw [odd_offDiagonal F s _ he b v, J_val, hy, project_on, project_on]
    cases s <;> simp

#print axioms NativeSameParity.leech_even_sameParity_coeff_eq_zero
#print axioms NativeSameParity.OddDirectional.leech_odd_sameParity_coeff_eq_zero
#print axioms leech_mixed_evenToOdd_multiplicity_one
#print axioms leech_mixed_oddToEven_multiplicity_one
#print axioms leech_projected_classification
#print axioms leech_full_classification

end

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFullMixedField
