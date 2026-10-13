/- GID: D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Signed integral reset dynamics and an arithmetic obstruction to equivariant splitting. -/
import D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect

open Multiplicative
open scoped BigOperators
open D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
  (VertexModule transition stationaryTransition StationaryModule DimensionGroup induced)

theorem flip_twice (x : MonoidAlgebra ℤ Sign) : resetFlip (resetFlip x) = x := by
  change (x * MonoidAlgebra.single (ofAdd true : Sign) 1) *
    MonoidAlgebra.single (ofAdd true : Sign) 1 = x
  rw [mul_assoc, MonoidAlgebra.single_mul_single]
  have ht : (ofAdd true : Sign) * ofAdd true = 1 := by decide
  simp [ht, ← MonoidAlgebra.one_def]

private def inverseSucc (n : ℕ) : Module.End ℤ (VertexModule Sign (n + 1)) :=
  ({ toFun := fun y => Fin.snoc (fun j : Fin n => y j.succ)
        (resetFlip (y 0) - ∑ j : Fin n, y j.succ)
     map_zero' := by
       funext i
       refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
     map_add' := by
       intro y z
       funext i
       refine Fin.lastCases ?_ (fun j => ?_) i
       · simp only [Fin.snoc_last, Pi.add_apply, map_add, Finset.sum_add_distrib]
         abel
       · simp
    } : VertexModule Sign (n + 1) →+ VertexModule Sign (n + 1)).toIntLinearMap

/-- The inverse of the original right-row transition uses only integer subtraction. -/
def resetInverse (q : ℕ) (hq : 0 < q) : Module.End ℤ (VertexModule Sign q) :=
  match q with
  | 0 => False.elim (Nat.not_lt_zero 0 hq)
  | n + 1 => inverseSucc n

/-- Both integral inverse identities hold at every positive length, including one. -/
theorem reset_transition_inverse (q : ℕ) (hq : 0 < q) :
    resetInverse q hq * transition (resetMatrix q) = 1 ∧
      transition (resetMatrix q) * resetInverse q hq = 1 := by
  cases q with
  | zero => omega
  | succ n =>
      have hp (y : VertexModule Sign (n + 1)) :
          resetInverse (n + 1) hq y = Fin.snoc (fun j : Fin n => y j.succ)
            (resetFlip (y 0) - ∑ j : Fin n, y j.succ) := rfl
      constructor
      · apply LinearMap.ext
        intro v
        funext i
        change resetInverse (n + 1) hq (transition (resetMatrix (n + 1)) v) i = v i
        rw [hp]
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Fin.snoc_last, transition_zero, transition_succ]
          change resetFlip (resetFlip (∑ i, v i)) - ∑ j : Fin n, v j.castSucc = _
          rw [flip_twice, Fin.sum_univ_castSucc]
          abel
        · simp only [Fin.snoc_castSucc, transition_succ]
      · apply LinearMap.ext
        intro v
        funext i
        change transition (resetMatrix (n + 1)) (resetInverse (n + 1) hq v) i = v i
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [transition_zero, hp, Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          have hs : (∑ j : Fin n, v j.succ) +
              (resetFlip (v 0) - ∑ j : Fin n, v j.succ) = resetFlip (v 0) := by abel
          rw [hs]
          exact flip_twice (v 0)
        · rw [transition_succ, hp, Fin.snoc_castSucc]

/-- The actual transition is an automorphism of the entire integer module. -/
def resetTransitionEquiv (q : ℕ) (hq : 0 < q) :
    VertexModule Sign q ≃ₗ[ℤ] VertexModule Sign q :=
  LinearEquiv.ofLinearMap (transition (resetMatrix q)) (resetInverse q hq)
    (reset_transition_inverse q hq).2 (reset_transition_inverse q hq).1

private def nativeLift (q : ℕ) (hq : 0 < q) :
    DimensionGroup (resetMatrix q) →ₗ[ℤ] VertexModule Sign q :=
  Module.DirectLimit.lift ℤ ℕ (fun _ : ℕ => VertexModule Sign q)
    (stationaryTransition (transition (resetMatrix q))) (fun n => resetInverse q hq ^ n)
    (by
      intro i j hij v
      have hh : resetInverse q hq ^ j * transition (resetMatrix q) ^ (j - i) =
          resetInverse q hq ^ i := by
        rw [← pow_mul_pow_sub (resetInverse q hq) hij, mul_assoc,
          pow_mul_pow_eq_one (j - i) (reset_transition_inverse q hq).1, mul_one]
      exact LinearMap.congr_fun hh v)

private abbrev stage (q n : ℕ) : VertexModule Sign q →ₗ[ℤ] DimensionGroup (resetMatrix q) :=
  Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => VertexModule Sign q)
    (stationaryTransition (transition (resetMatrix q))) n

private theorem nativeLift_stage (q : ℕ) (hq : 0 < q) (n : ℕ) (v : VertexModule Sign q) :
    nativeLift q hq (stage q n v) = (resetInverse q hq ^ n) v :=
  by
    dsimp only [nativeLift, stage]
    exact Module.DirectLimit.lift_of (R := ℤ) (ι := ℕ)
      (G := fun _ : ℕ => VertexModule Sign q)
      (f := stationaryTransition (transition (resetMatrix q)))
      (fun n => resetInverse q hq ^ n) _ v

/-- Stage zero identifies the original stationary colimit with its integer row module.
This is an identification of modules, without a coordinatewise cone assertion. -/
def resetNativeEquiv (q : ℕ) (hq : 0 < q) :
    DimensionGroup (resetMatrix q) ≃ₗ[ℤ] VertexModule Sign q :=
  LinearEquiv.ofLinearMap (nativeLift q hq) (stage q 0)
    (by ext v; simp only [LinearMap.comp_apply, nativeLift_stage, pow_zero,
          Module.End.one_apply, LinearMap.id_apply])
    (by
      apply Module.DirectLimit.hom_ext
      intro n
      apply LinearMap.ext
      intro v
      change stage q 0 (nativeLift q hq (stage q n v)) = stage q n v
      rw [nativeLift_stage]
      have hh : (transition (resetMatrix q) ^ n) ((resetInverse q hq ^ n) v) = v :=
        LinearMap.congr_fun (pow_mul_pow_eq_one n (reset_transition_inverse q hq).2) v
      calc
        _ = stage q n ((transition (resetMatrix q) ^ n) ((resetInverse q hq ^ n) v)) := by
          exact (Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
            (G := fun _ : ℕ => VertexModule Sign q)
            (f := stationaryTransition (transition (resetMatrix q)))
            (i := 0) (j := n) (hij := Nat.zero_le n)
            (x := (resetInverse q hq ^ n) v)).symm
        _ = _ := congrArg (stage q n) hh)

/-- A stage-n row is read at stage zero by n inverse transitions. -/
theorem resetNativeEquiv_stage (q : ℕ) (hq : 0 < q) (n : ℕ) (v : VertexModule Sign q) :
    resetNativeEquiv q hq (Module.DirectLimit.of ℤ ℕ
      (fun _ : ℕ => VertexModule Sign q)
      (stationaryTransition (transition (resetMatrix q))) n v) = (resetInverse q hq ^ n) v :=
  nativeLift_stage q hq n v

/-- The original time endomorphism, rather than the complement action, is intertwined. -/
theorem resetNativeEquiv_theta (q : ℕ) (hq : 0 < q)
    (x : DimensionGroup (resetMatrix q)) :
    resetNativeEquiv q hq (resetTheta q x) =
      transition (resetMatrix q) (resetNativeEquiv q hq x) := by
  have hh : (nativeLift q hq).comp (resetTheta q) =
      (transition (resetMatrix q)).comp (nativeLift q hq) := by
    apply Module.DirectLimit.hom_ext
    intro n
    apply LinearMap.ext
    intro v
    change nativeLift q hq (resetTheta q (stage q n v)) =
      transition (resetMatrix q) (nativeLift q hq (stage q n v))
    rw [show resetTheta q (stage q n v) =
      stage q n (transition (resetMatrix q) v) from resetTheta_apply_of q n v]
    rw [nativeLift_stage, nativeLift_stage]
    have hc : Commute (resetInverse q hq) (transition (resetMatrix q)) :=
      (reset_transition_inverse q hq).1.trans (reset_transition_inverse q hq).2.symm
    exact LinearMap.congr_fun (hc.pow_left n).eq v
  exact LinearMap.congr_fun hh x


private theorem native_zero (q : ℕ) (hq : 0 < q) (v : VertexModule Sign q) :
    resetNativeEquiv q hq (stage q 0 v) = v := by
  change nativeLift q hq (stage q 0 v) = v
  rw [nativeLift_stage]
  rfl

private theorem native_class (q : ℕ) (hq : 0 < q) :
    resetNativeEquiv q hq (resetOddClass q) = resetOddVector q := native_zero q hq _

/-- Identity plus genuine time on the original stationary dimension group. -/
def resetNativeDefect (q : ℕ) : Module.End ℤ (DimensionGroup (resetMatrix q)) :=
  LinearMap.id + resetTheta q

/-- The primitive character is transported along the actual stage-zero identification. -/
def resetNativeCharacter (q : ℕ) (hq : 0 < q) :
    DimensionGroup (resetMatrix q) →ₗ[ℤ] ℤ :=
  (resetCharacter q).comp (resetNativeEquiv q hq).toLinearMap

/-- The finite integer solver, returned to the original colimit at stage zero. -/
def resetNativePreimage (q : ℕ) (hq : 0 < q) (y : DimensionGroup (resetMatrix q)) :
    DimensionGroup (resetMatrix q) :=
  (resetNativeEquiv q hq).symm (resetPreimage q hq (resetNativeEquiv q hq y))

private theorem native_defect (q : ℕ) (hq : 0 < q) (x : DimensionGroup (resetMatrix q)) :
    resetNativeEquiv q hq (resetNativeDefect q x) =
      resetDefect q (resetNativeEquiv q hq x) := by
  simp only [resetNativeDefect, resetDefect, LinearMap.add_apply, LinearMap.id_apply,
    map_add, resetNativeEquiv_theta]

private theorem character_transition (q : ℕ) (hq : 0 < q) (ho : Odd q)
    (v : VertexModule Sign q) :
    resetCharacter q (transition (resetMatrix q) v) = -resetCharacter q v := by
  have hz := (reset_odd_image q hq ho (resetDefect q v)).mp ⟨v, rfl⟩
  change resetCharacter q (v + transition (resetMatrix q) v) = 0 at hz
  rw [map_add] at hz
  omega

private theorem character_inverse (q : ℕ) (hq : 0 < q) (ho : Odd q)
    (v : VertexModule Sign q) :
    resetCharacter q (resetInverse q hq v) = -resetCharacter q v := by
  have hz := character_transition q hq ho (resetInverse q hq v)
  have hh := LinearMap.congr_fun (reset_transition_inverse q hq).2 v
  change transition (resetMatrix q) (resetInverse q hq v) = v at hh
  rw [hh] at hz
  omega

/-- The factor (-1)^n is necessary to descend the character through forward stages. -/
theorem reset_native_character_stage (q : ℕ) (hq : 0 < q) (ho : Odd q)
    (n : ℕ) (v : VertexModule Sign q) :
    resetNativeCharacter q hq (Module.DirectLimit.of ℤ ℕ
      (fun _ : ℕ => VertexModule Sign q)
      (stationaryTransition (transition (resetMatrix q))) n v) =
      (-1 : ℤ) ^ n * resetCharacter q v := by
  change resetCharacter q (resetNativeEquiv q hq (stage q n v)) = _
  rw [show resetNativeEquiv q hq (stage q n v) = (resetInverse q hq ^ n) v from
    resetNativeEquiv_stage q hq n v]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, character_inverse q hq ho, ih, pow_succ]
      ring

/-- Genuine time negates the primitive native character. -/
theorem reset_native_character_theta (q : ℕ) (hq : 0 < q) (ho : Odd q)
    (x : DimensionGroup (resetMatrix q)) :
    resetNativeCharacter q hq (resetTheta q x) = -resetNativeCharacter q hq x := by
  change resetCharacter q (resetNativeEquiv q hq (resetTheta q x)) = _
  rw [resetNativeEquiv_theta, character_transition q hq ho]
  rfl

/-- The native character is onto all integers. -/
theorem reset_native_character_surjective (q : ℕ) (hq : 0 < q) :
    Function.Surjective (resetNativeCharacter q hq) :=
  (reset_character_surjective q hq).comp (resetNativeEquiv q hq).surjective

/-- The full odd kernel on the original colimit has a unique integer coefficient. -/
theorem reset_native_odd_kernel (q : ℕ) (hq : 0 < q) (ho : Odd q)
    (x : DimensionGroup (resetMatrix q)) :
    resetNativeDefect q x = 0 ↔ ∃! k : ℤ, x = k • resetOddClass q := by
  have hx : resetNativeDefect q x = 0 ↔ resetDefect q (resetNativeEquiv q hq x) = 0 := by
    rw [← native_defect, ← map_zero (resetNativeEquiv q hq)]
    exact (resetNativeEquiv q hq).injective.eq_iff.symm
  rw [hx, reset_odd_kernel q hq ho]
  apply existsUnique_congr
  intro k
  constructor
  · intro hk
    apply (resetNativeEquiv q hq).injective
    rw [map_smul, native_class]
    exact hk
  · rintro rfl
    rw [map_smul, native_class]

/-- Exact integral solvability in the original stationary dimension group. -/
theorem reset_native_odd_image (q : ℕ) (hq : 0 < q) (ho : Odd q)
    (y : DimensionGroup (resetMatrix q)) :
    (∃ x, resetNativeDefect q x = y) ↔ resetNativeCharacter q hq y = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (reset_odd_image q hq ho _).mp ⟨resetNativeEquiv q hq x, (native_defect q hq x).symm⟩
  · intro hy
    obtain ⟨v, hv⟩ := (reset_odd_image q hq ho (resetNativeEquiv q hq y)).mpr hy
    refine ⟨(resetNativeEquiv q hq).symm v, (resetNativeEquiv q hq).injective ?_⟩
    rw [native_defect, LinearEquiv.apply_symm_apply, hv]

/-- Every solvable native fibre is the explicit solution plus a unique multiple of c. -/
theorem reset_native_odd_all_solutions (q : ℕ) (hq : 0 < q) (ho : Odd q)
    (y : DimensionGroup (resetMatrix q)) (hy : resetNativeCharacter q hq y = 0)
    (x : DimensionGroup (resetMatrix q)) :
    resetNativeDefect q x = y ↔
      ∃! k : ℤ, x = resetNativePreimage q hq y + k • resetOddClass q := by
  have hx : resetNativeDefect q x = y ↔
      resetDefect q (resetNativeEquiv q hq x) = resetNativeEquiv q hq y := by
    rw [← native_defect]
    exact (resetNativeEquiv q hq).injective.eq_iff.symm
  rw [hx]
  have hf := reset_odd_all_solutions q hq ho (resetNativeEquiv q hq y) hy
    (resetNativeEquiv q hq x)
  change (resetDefect q (resetNativeEquiv q hq x) = resetNativeEquiv q hq y ↔
    ∃! k : ℤ, resetNativeEquiv q hq x =
      resetPreimage q hq (resetNativeEquiv q hq y) + k • resetOddVector q) at hf
  rw [hf]
  apply existsUnique_congr
  intro k
  constructor
  · intro hk
    apply (resetNativeEquiv q hq).injective
    simpa only [map_add, map_smul, native_class, resetNativePreimage,
      LinearEquiv.apply_symm_apply] using hk
  · intro hk
    simpa only [map_add, map_smul, native_class, resetNativePreimage,
      LinearEquiv.apply_symm_apply] using congrArg (resetNativeEquiv q hq) hk

/-- The native image is the exact kernel of the primitive signed character. -/
theorem reset_native_odd_range (q : ℕ) (hq : 0 < q) (ho : Odd q) :
    LinearMap.range (resetNativeDefect q) = LinearMap.ker (resetNativeCharacter q hq) := by
  ext y
  exact reset_native_odd_image q hq ho y

/-- The ordinary native cokernel is free cyclic, with no torsion. -/
def resetNativeOddCokernelEquiv (q : ℕ) (hq : 0 < q) (ho : Odd q) :
    (DimensionGroup (resetMatrix q) ⧸ LinearMap.range (resetNativeDefect q)) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ (reset_native_odd_range q hq ho)).trans
    ((resetNativeCharacter q hq).quotKerEquivOfSurjective (reset_native_character_surjective q hq))


/-- The primitive native character evaluates to q+1 on the odd kernel generator. -/
theorem reset_native_pairing (q : ℕ) (hq : 0 < q) (ho : Odd q) :
    resetNativeCharacter q hq (resetOddClass q) = (q + 1 : ℕ) := by
  change resetCharacter q (resetNativeEquiv q hq (resetOddClass q)) = _
  rw [native_class]
  have ht : (ofAdd true : Sign) ≠ 1 := by decide
  have hc (i : Fin q) : (resetOddVector q i).coeff (ofAdd true) = -((-1 : ℤ) ^ i.val) := by
    change (((-1 : ℤ) ^ i.val) •
      (MonoidAlgebra.single (1 : Sign) (1 : ℤ) -
        MonoidAlgebra.single (ofAdd true : Sign) (1 : ℤ))).coeff
        (ofAdd true) = _
    rw [MonoidAlgebra.coeff_smul_apply]
    simp [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_single, ht]
  have hs (i : Fin q) :
      (if Even i.val then (resetOddVector q i).coeff 1 -
        (resetOddVector q i).coeff (ofAdd true) else 0) = 1 + (-1 : ℤ) ^ i.val := by
    rw [resetOddVector_coeff_one, hc, neg_one_pow_eq_ite]
    by_cases hi : Even i.val <;> simp [hi]
  change (∑ i : Fin q, if Even i.val then (resetOddVector q i).coeff 1 -
    (resetOddVector q i).coeff (ofAdd true) else 0) = _
  simp_rw [hs]
  rw [Finset.sum_add_distrib, Fin.sum_neg_one_pow]
  have he : ¬ Even q := by simp only [Nat.even_iff, Nat.odd_iff] at *; omega
  simp [he]

/-- The odd kernel and image intersect only at zero. -/
theorem reset_native_kernel_inf_range (q : ℕ) (hq : 0 < q) (ho : Odd q) :
    LinearMap.ker (resetNativeDefect q) ⊓ LinearMap.range (resetNativeDefect q) = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  obtain ⟨hk, hr⟩ := Submodule.mem_inf.mp hx
  obtain ⟨k, hxk, _⟩ := (reset_native_odd_kernel q hq ho x).mp hk
  have hz : resetNativeCharacter q hq x = 0 := by
    rw [reset_native_odd_range q hq ho] at hr
    exact hr
  rw [hxk, map_smul, reset_native_pairing q hq ho, smul_eq_mul] at hz
  have hd : ((q + 1 : ℕ) : ℤ) ≠ 0 := by positivity
  have hkzero : k = 0 := (mul_eq_zero.mp hz).resolve_right hd
  rw [hxk, hkzero, zero_smul]

/-- The sum of image and kernel has exactly the divisibility obstruction q+1. -/
theorem reset_native_sum_criterion (q : ℕ) (hq : 0 < q) (ho : Odd q)
    (x : DimensionGroup (resetMatrix q)) :
    x ∈ LinearMap.range (resetNativeDefect q) ⊔ LinearMap.ker (resetNativeDefect q) ↔
      ((q + 1 : ℕ) : ℤ) ∣ resetNativeCharacter q hq x := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨k, rfl, _⟩ := (reset_native_odd_kernel q hq ho b).mp hb
    have hz : resetNativeCharacter q hq a = 0 := by
      rw [reset_native_odd_range q hq ho] at ha
      exact ha
    rw [map_add, hz, map_smul, reset_native_pairing q hq ho, smul_eq_mul, zero_add]
    exact dvd_mul_left _ _
  · rintro ⟨k, hk⟩
    have hz : resetNativeCharacter q hq (x - k • resetOddClass q) = 0 := by
      rw [map_sub, map_smul, reset_native_pairing q hq ho, smul_eq_mul, hk]
      ring
    have ha : x - k • resetOddClass q ∈ LinearMap.range (resetNativeDefect q) :=
      (reset_native_odd_image q hq ho _).mpr hz
    have hb : k • resetOddClass q ∈ LinearMap.ker (resetNativeDefect q) := by
      change resetNativeDefect q (k • resetOddClass q) = 0
      rw [map_smul]
      have hc : resetNativeDefect q (resetOddClass q) = 0 :=
        (reset_odd_killed_class q hq ho).2
      rw [hc, smul_zero]
    exact Submodule.mem_sup.mpr ⟨x - k • resetOddClass q, ha,
      k • resetOddClass q, hb, sub_add_cancel _ _⟩

/-- Residue of the primitive character modulo the exact kernel pairing. -/
def resetNativeResidue (q : ℕ) (hq : 0 < q) :
    DimensionGroup (resetMatrix q) →ₗ[ℤ] ZMod (q + 1) :=
  (Int.castAddHom (ZMod (q + 1))).toIntLinearMap.comp (resetNativeCharacter q hq)

private theorem residue_surjective (q : ℕ) (hq : 0 < q) :
    Function.Surjective (resetNativeResidue q hq) :=
  ZMod.intCast_surjective.comp (reset_native_character_surjective q hq)

private theorem residue_kernel (q : ℕ) (hq : 0 < q) (ho : Odd q) :
    LinearMap.ker (resetNativeResidue q hq) =
      LinearMap.range (resetNativeDefect q) ⊔ LinearMap.ker (resetNativeDefect q) := by
  ext x
  change (resetNativeCharacter q hq x : ZMod (q + 1)) = 0 ↔ _
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact (reset_native_sum_criterion q hq ho x).symm

/-- Only the quotient by image PLUS kernel is finite cyclic of order q+1. -/
def resetNativeCombinedQuotientEquiv (q : ℕ) (hq : 0 < q) (ho : Odd q) :
    (DimensionGroup (resetMatrix q) ⧸
      (LinearMap.range (resetNativeDefect q) ⊔ LinearMap.ker (resetNativeDefect q))) ≃ₗ[ℤ]
      ZMod (q + 1) :=
  (Submodule.quotEquivOfEq _ _ (residue_kernel q hq ho).symm).trans
    ((resetNativeResidue q hq).quotKerEquivOfSurjective (residue_surjective q hq))

/-- There is no integer-linear section intertwining genuine time with negation. -/
theorem reset_native_no_equivariant_linear_section (q : ℕ) (hq : 0 < q) (ho : Odd q) :
    ¬ ∃ s : ℤ →ₗ[ℤ] DimensionGroup (resetMatrix q),
      (resetNativeCharacter q hq).comp s = LinearMap.id ∧
      ∀ n : ℤ, resetTheta q (s n) = s (-n) := by
  rintro ⟨s, hsection, htime⟩
  have hz : resetNativeDefect q (s 1) = 0 := by
    change s 1 + resetTheta q (s 1) = 0
    rw [htime, map_neg, add_neg_cancel]
  obtain ⟨k, hk, _⟩ := (reset_native_odd_kernel q hq ho (s 1)).mp hz
  have hone := LinearMap.congr_fun hsection 1
  change resetNativeCharacter q hq (s 1) = 1 at hone
  rw [hk, map_smul, reset_native_pairing q hq ho, smul_eq_mul] at hone
  have hd : ((q + 1 : ℕ) : ℤ) ∣ (1 : ℤ) := ⟨k, by simpa only [mul_comm] using hone.symm⟩
  have hn : q + 1 ∣ 1 := Int.natCast_dvd_natCast.mp hd
  have hh := Nat.dvd_one.mp hn
  omega

/-- A complete equation classifier at all positive lengths: even fibres are singletons,
while odd fibres have the signed obstruction and a unique cyclic parameter. -/
theorem reset_native_all_solutions (q : ℕ) (hq : 0 < q)
    (y x : DimensionGroup (resetMatrix q)) :
    (Even q → (resetNativeDefect q x = y ↔ x = resetNativePreimage q hq y)) ∧
    (Odd q → (resetNativeDefect q x = y ↔
      resetNativeCharacter q hq y = 0 ∧
        ∃! k : ℤ, x = resetNativePreimage q hq y + k • resetOddClass q)) := by
  constructor
  · intro he
    have hf := (reset_even_unique_solution q hq he (resetNativeEquiv q hq y)).2
      (resetNativeEquiv q hq x)
    constructor
    · intro hx
      apply (resetNativeEquiv q hq).injective
      rw [resetNativePreimage, LinearEquiv.apply_symm_apply]
      exact hf.mp ((native_defect q hq x).symm.trans (congrArg (resetNativeEquiv q hq) hx))
    · intro hx
      apply (resetNativeEquiv q hq).injective
      rw [native_defect]
      apply hf.mpr
      rw [hx, resetNativePreimage, LinearEquiv.apply_symm_apply]
  · intro ho
    constructor
    · intro hx
      have hy := (reset_native_odd_image q hq ho y).mp ⟨x, hx⟩
      exact ⟨hy, (reset_native_odd_all_solutions q hq ho y hy x).mp hx⟩
    · rintro ⟨hy, hx⟩
      exact (reset_native_odd_all_solutions q hq ho y hy x).mpr hx

end D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
