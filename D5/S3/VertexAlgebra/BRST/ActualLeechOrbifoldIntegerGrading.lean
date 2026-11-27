/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldIntegerGrading
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldIntegerGrading
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Finite integer grading of the actual relative ghost-one BRST Lie algebra. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldAllWeightDimension
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRealRootBracket
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRealRootLocalNilpotence
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Regroup the native momentum direct sum by the degree `2 p₀ - p₁`. The
actual energy bound confines its support to a finite interval at each degree. -/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped DirectSum

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge bilinear)
open LatticePositiveEnergy (chargeEnergy two_chargeEnergy)
open RelativeCohomology (GradedCycles GradedCohomology ghostOneCohomologyEquivNonzero)

local notation "Momentum" => Charge hyperbolicPlane
local notation "H" => fun p : Momentum => GradedCohomology planeFrame planeBasis p 1
local notation "incl" => DirectSum.lof ℂ Momentum H
local notation "component" => DirectSum.component ℂ Momentum H

local instance (p : Momentum) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _

local instance (p : Momentum) : AddCommGroup (GradedCycles planeFrame planeBasis p 1) :=
  Submodule.addCommGroup _

/-- The integer degree is `2m + n` in coordinates `(m,n) = (p₀, -p₁)`. -/
def integerDegree (p : Momentum) : ℤ := 2 * p (0 : Fin 2) - p (1 : Fin 2)

theorem integerDegree_add (p q : Momentum) :
    integerDegree (p + q) = integerDegree p + integerDegree q := by
  simp only [integerDegree, Pi.add_apply]
  omega

theorem momentum_one_eq_of_degree_eq (p : Momentum) {d : ℤ} (hd : integerDegree p = d) :
    p (1 : Fin 2) = 2 * p (0 : Fin 2) - d := by
  unfold integerDegree at hd
  omega

/-- The plane energy bound at degree `d` confines the first coordinate to an integer interval. -/
theorem momentum_zero_mem_interval (p : Momentum) {d : ℤ} (hd : integerDegree p = d)
    (he : p (0 : Fin 2) * p (1 : Fin 2) ≤ 1) : p (0 : Fin 2) ∈ Set.Icc (min 0 d) (max 0 d) := by
  have hcoord := momentum_one_eq_of_degree_eq p hd
  have hmul {a b : ℤ} (ha : 1 ≤ a) (hb : 2 ≤ b) : 2 ≤ a * b := calc
    2 = 1 * 2 := by decide
    _ ≤ a * 2 := mul_le_mul_of_nonneg_right ha (by decide)
    _ ≤ a * b := mul_le_mul_of_nonneg_left hb (by omega)
  change min 0 d ≤ p (0 : Fin 2) ∧ p (0 : Fin 2) ≤ max 0 d
  constructor
  · by_contra hlo
    obtain ⟨h0, hd'⟩ := lt_min_iff.mp (lt_of_not_ge hlo)
    have h := hmul (a := -(p (0 : Fin 2))) (b := -(p (1 : Fin 2))) (by omega) (by omega)
    rw [neg_mul_neg] at h
    omega
  · by_contra hhi
    obtain ⟨h0, hd'⟩ := max_lt_iff.mp (lt_of_not_ge hhi)
    have h := hmul (a := p (0 : Fin 2)) (b := p (1 : Fin 2)) (by omega) (by omega)
    omega

/-- The momentum fiber at degree `d` with available level at least zero. -/
def allowedMomenta (d : ℤ) : Set Momentum :=
  {p | integerDegree p = d ∧ p (0 : Fin 2) * p (1 : Fin 2) ≤ 1}

theorem allowedMomenta_finite (d : ℤ) : (allowedMomenta d).Finite := by
  change Finite (allowedMomenta d)
  let coord (p : allowedMomenta d) : Set.Icc (min 0 d) (max 0 d) :=
    ⟨p.val (0 : Fin 2), momentum_zero_mem_interval p.val p.property.1 p.property.2⟩
  apply Finite.of_injective coord
  intro p q h
  have h0 : p.val (0 : Fin 2) = q.val (0 : Fin 2) := congrArg Subtype.val h
  have h1 : p.val (1 : Fin 2) = q.val (1 : Fin 2) := by
    rw [momentum_one_eq_of_degree_eq p.val p.property.1,
      momentum_one_eq_of_degree_eq q.val q.property.1, h0]
  apply Subtype.ext
  funext (i : Fin 2)
  fin_cases i
  · exact h0
  · exact h1

theorem allowedMomenta_zero : allowedMomenta 0 = {0} := by
  apply Set.ext
  intro p
  constructor
  · intro hp
    have h := momentum_zero_mem_interval p hp.1 hp.2
    have h0 : p (0 : Fin 2) = 0 := by
      have hb : 0 ≤ p (0 : Fin 2) ∧ p (0 : Fin 2) ≤ 0 := by
        simpa only [Set.mem_Icc, min_self, max_self] using h
      exact le_antisymm hb.2 hb.1
    have h1 : p (1 : Fin 2) = 0 := by
      simp only [momentum_one_eq_of_degree_eq p hp.1, h0, mul_zero, sub_zero]
    apply Set.mem_singleton_iff.mpr
    funext (i : Fin 2)
    fin_cases i
    · exact h0
    · exact h1
  · intro hp
    rw [Set.mem_singleton_iff.mp hp]
    simp [allowedMomenta, integerDegree]

/-- Negative available level kills every class in the actual ghost-one quotient. -/
theorem ghostOne_eq_zero_of_one_lt (p : Momentum)
    (hp : 1 < p (0 : Fin 2) * p (1 : Fin 2)) (x : H p) : x = 0 := by
  exact ghostOne_eq_zero_of_negative_level p (by rw [plane_chargeEnergy]; omega) x

/-- Every momentum supporting a nonzero native ghost-one class has norm at most two. -/
theorem momentum_norm_le_two_of_ghostOne_ne_zero (p : Momentum) (x : H p) (hx : x ≠ 0) :
    bilinear hyperbolicPlane p p ≤ 2 := by
  have hbound : chargeEnergy hyperbolicPlane p ≤ 1 :=
    le_of_not_gt (fun h => hx (ghostOne_eq_zero_of_negative_level p (by omega) x))
  have hnorm := two_chargeEnergy hyperbolicPlane p
  omega

theorem ghostOne_support_finite (d : ℤ) :
    {p : Momentum | integerDegree p = d ∧ ∃ x : H p, x ≠ 0}.Finite := by
  apply (allowedMomenta_finite d).subset
  rintro p ⟨hd, x, hx⟩
  refine ⟨hd, le_of_not_gt (fun hp => hx (ghostOne_eq_zero_of_one_lt p hp x))⟩

/-- The concrete degree component inside the momentum direct sum. -/
def integerDegreeComponent (d : ℤ) : Submodule ℂ MomentumH1 :=
  ⨆ p : allowedMomenta d, LinearMap.range (incl p.val)

theorem incl_mem_integerDegreeComponent (p : Momentum) (x : H p) :
    incl p x ∈ integerDegreeComponent (integerDegree p) := by
  by_cases hp : p (0 : Fin 2) * p (1 : Fin 2) ≤ 1
  · exact Submodule.mem_iSup_of_mem (⟨p, rfl, hp⟩ : allowedMomenta (integerDegree p))
      (LinearMap.mem_range_self (incl p) x)
  · rw [ghostOne_eq_zero_of_one_lt p (lt_of_not_ge hp) x, map_zero]
    exact Submodule.zero_mem _

private theorem integerDegreeComponent_le_ker {d : ℤ} {p : Momentum}
    (hp : integerDegree p ≠ d) : integerDegreeComponent d ≤ LinearMap.ker (component p) := by
  unfold integerDegreeComponent
  apply iSup_le
  rintro q _ ⟨x, rfl⟩
  have hqp : q.val ≠ p := by
    intro h
    apply hp
    rw [← h]
    exact q.property.1
  rw [LinearMap.mem_ker, DirectSum.component.of, dite_eq_right hqp]

/-- The concrete integer components give an internal direct sum of the actual quotient. -/
theorem integerDegreeComponent_internal : DirectSum.IsInternal integerDegreeComponent := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro d
    rw [Submodule.disjoint_def]
    intro z hz hrest
    apply DirectSum.ext_component ℂ
    intro p
    rw [map_zero]
    by_cases hp : integerDegree p = d
    · have hle : (⨆ e ≠ d, integerDegreeComponent e) ≤ LinearMap.ker (component p) :=
        iSup₂_le fun e he => integerDegreeComponent_le_ker (by rw [hp]; exact Ne.symm he)
      exact LinearMap.mem_ker.mp (hle hrest)
    · exact LinearMap.mem_ker.mp (integerDegreeComponent_le_ker hp hz)
  · apply top_unique
    intro z hz
    clear hz
    induction z using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | of p x =>
      change incl p x ∈ ⨆ d, integerDegreeComponent d
      exact Submodule.mem_iSup_of_mem (integerDegree p) (incl_mem_integerDegreeComponent p x)
    | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- The native BRST bracket adds the integer degrees. -/
theorem integerDegreeComponent_lie {d e : ℤ} {x y : MomentumH1}
    (hx : x ∈ integerDegreeComponent d) (hy : y ∈ integerDegreeComponent e) :
    ⁅x, y⁆ ∈ integerDegreeComponent (d + e) := by
  unfold integerDegreeComponent at hx hy
  refine Submodule.iSup_induction _ (motive := fun z => ⁅z, y⁆ ∈ integerDegreeComponent (d + e))
    hx ?_ ?_ ?_
  · rintro p _ ⟨u, rfl⟩
    refine Submodule.iSup_induction _
      (motive := fun z => ⁅incl p.val u, z⁆ ∈ integerDegreeComponent (d + e)) hy ?_ ?_ ?_
    · rintro q _ ⟨v, rfl⟩
      change momentumBracket (incl p.val u) (incl q.val v) ∈ _
      rw [momentumBracket_incl]
      have hp : integerDegree p.val = d := p.property.1
      have hq : integerDegree q.val = e := q.property.1
      simpa only [integerDegree_add, hp, hq] using
        incl_mem_integerDegreeComponent (p.val + q.val) (bracket p.val q.val u v)
    · rw [lie_zero]
      exact Submodule.zero_mem _
    · intro z w hz hw
      rw [lie_add]
      exact Submodule.add_mem _ hz hw
  · rw [zero_lie]
    exact Submodule.zero_mem _
  · intro z w hz hw
    rw [add_lie]
    exact Submodule.add_mem _ hz hw

theorem integerDegreeComponent_zero :
    integerDegreeComponent 0 = LinearMap.range RealRootBracket.cartanClass := by
  have hcartan : LinearMap.range RealRootBracket.cartanClass = LinearMap.range (incl 0) := by
    unfold RealRootBracket.cartanClass
    exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
      RelativeZeroMomentum.ghostOneCohomologyEquiv.symm.surjective)
  rw [hcartan]
  unfold integerDegreeComponent
  apply le_antisymm
  · apply iSup_le
    intro p
    have hp : p.val = 0 := by
      simpa only [allowedMomenta_zero, Set.mem_singleton_iff] using p.property
    rw [hp]
  · exact le_iSup (fun p : allowedMomenta 0 => LinearMap.range (incl p.val))
      ⟨0, by rw [allowedMomenta_zero]; exact Set.mem_singleton _⟩

theorem integerDegreeComponent_zero_finrank :
    Module.finrank ℂ (integerDegreeComponent 0) = 2 := by
  rw [integerDegreeComponent_zero]
  have hinj : Function.Injective RealRootBracket.cartanClass := by
    intro f g h
    apply RelativeZeroMomentum.ghostOneCohomologyEquiv.symm.injective
    have hc := congrArg (fun z : MomentumH1 => component 0 z) h
    change component 0 (incl 0 (RelativeZeroMomentum.ghostOneCohomologyEquiv.symm f)) =
      component 0 (incl 0 (RelativeZeroMomentum.ghostOneCohomologyEquiv.symm g)) at hc
    simpa only [DirectSum.component.lof_self] using hc
  calc
    _ = Module.finrank ℂ (Fin 2 → ℂ) :=
      (LinearEquiv.ofInjective RealRootBracket.cartanClass hinj).finrank_eq.symm
    _ = 2 := by simp

set_option maxHeartbeats 1000000 in
-- The BRST quotient and the orbifold eigenspace carry large inferred module structures.
/-- Each native momentum summand is finite-dimensional, including the Cartan at zero. -/
theorem ghostOneMomentum_finiteDimensional (p : Momentum) : FiniteDimensional ℂ (H p) := by
  by_cases hp : p = 0
  · subst p
    exact FiniteDimensional.of_injective RelativeZeroMomentum.ghostOneCohomologyEquiv.toLinearMap
      RelativeZeroMomentum.ghostOneCohomologyEquiv.injective
  · let equivalence := ghostOneCohomologyEquivNonzero p hp
    haveI : FiniteDimensional ℂ (RelativeCohomology.OrbifoldWeight p) :=
      ActualLeechOrbifoldAllWeightDimension.orbifoldWeight_finite
        (1 - p (0 : Fin 2) * p (1 : Fin 2))
    exact FiniteDimensional.of_injective equivalence.toLinearMap equivalence.injective

set_option maxHeartbeats 1000000 in
-- The ambient direct sum requires elaborating the module on the native quotient family.
/-- Each integer component is a finite sum of finite-dimensional actual momentum summands. -/
theorem integerDegreeComponent_finiteDimensional (d : ℤ) :
    FiniteDimensional ℂ (integerDegreeComponent d) := by
  have finiteIndex : Finite (allowedMomenta d) := allowedMomenta_finite d
  have finiteRange (p : allowedMomenta d) : FiniteDimensional ℂ (LinearMap.range (incl p.val)) := by
    haveI := ghostOneMomentum_finiteDimensional p.val
    exact LinearMap.finiteDimensional_range (incl p.val)
  unfold integerDegreeComponent
  exact @Submodule.finiteDimensional_iSup ℂ MomentumH1 _ _ _ _ finiteIndex _ finiteRange

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
