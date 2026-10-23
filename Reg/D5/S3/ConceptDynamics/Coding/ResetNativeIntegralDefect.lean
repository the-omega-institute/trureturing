import D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
open D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
open D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy (VertexModule DimensionGroup transition stationaryTransition)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
noncomputable section

abbrev G (q : ℕ) := DimensionGroup (resetMatrix q)
abbrev Positive := {q : ℕ // 0 < q}

private def register (S : Signature) (law : Realization S → Prop) (Target : Prop)
    (actual bad : Realization S) (bridge : Target ↔ law actual)
    (hp : law actual) (hn : ¬ law bad) (hd : ObservationalDependence S actual)
    (hrole : Subsingleton S.Role) (hanchor : IsEmpty S.Anchor) :
    Registration ⟨S, law⟩ Target where
  actual := actual
  bridge := bridge
  variation := ⟨hp, bad, hn⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, ?_, hn⟩
      · intro j hj
        exact (hj (hrole.elim _ _)).elim
      · funext e
        exact (hanchor.false e).elim
    · intro e
      exact (hanchor.false e).elim
  dependence := hd

abbrev rowSignature : Signature where
  Params := Nat
  State := G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := G
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev rowActual : Realization rowSignature := realize rowSignature (fun _ _ x => x) (fun e => nomatch e)
abbrev rowBad : Realization rowSignature := realize rowSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem class_ne : resetOddClass 1 ≠ 0 := resetOddClass_ne_zero 1 (by decide) (by decide)

private theorem row_dependence : ObservationalDependence rowSignature rowActual := by
  intro i
  exact ⟨1, resetOddClass 1, 0, class_ne⟩

private def rowRegistration (law : Realization rowSignature → Prop) (Target : Prop)
    (bridge : Target ↔ law rowActual) (hp : law rowActual) (hn : ¬ law rowBad) :
    Registration ⟨rowSignature, law⟩ Target :=
  register rowSignature law Target rowActual rowBad bridge hp hn row_dependence inferInstance inferInstance

private theorem unit_witness : ∃ x : G 1, resetNativeCharacter 1 (by decide) x = 1 :=
  reset_native_character_surjective 1 (by decide) 1

private theorem not_kernel_of_character_one {x : G 1}
    (hx : resetNativeCharacter 1 (by decide) x = 1) :
    ¬ ∃! k : ℤ, x = k • resetOddClass 1 := by
  intro h
  obtain ⟨k, hk, _⟩ := h
  have hp := congrArg (resetNativeCharacter 1 (by decide)) hk
  rw [map_smul, reset_native_pairing 1 (by decide) (by decide), smul_eq_mul, hx] at hp
  norm_num at hp
  omega

abbrev kernelArena : Arena where
  signature := rowSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (ho : Odd q) (x : G q),
    resetNativeDefect q (r.readout () q x) = 0 ↔ ∃! k : ℤ, x = k • resetOddClass q

private theorem kernel_bad : ¬ kernelArena.Law rowBad := by
  intro h
  obtain ⟨x, hx⟩ := unit_witness
  exact not_kernel_of_character_one hx ((h 1 (by decide) (by decide) x).mp (map_zero _))

def kernelRegistration := rowRegistration kernelArena.Law
  (∀ (q : ℕ) (hq : 0 < q) (ho : Odd q) (x : G q),
    resetNativeDefect q x = 0 ↔ ∃! k : ℤ, x = k • resetOddClass q)
  Iff.rfl reset_native_odd_kernel kernel_bad

abbrev imageArena : Arena where
  signature := rowSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (ho : Odd q) (y : G q),
    (∃ x, resetNativeDefect q x = r.readout () q y) ↔ resetNativeCharacter q hq y = 0

private theorem image_bad : ¬ imageArena.Law rowBad := by
  intro h
  obtain ⟨x, hx⟩ := unit_witness
  have hz := (h 1 (by decide) (by decide) x).mp ⟨0, map_zero _⟩
  rw [hx] at hz
  omega

def imageRegistration := rowRegistration imageArena.Law
  (∀ (q : ℕ) (hq : 0 < q) (ho : Odd q) (y : G q),
    (∃ x, resetNativeDefect q x = y) ↔ resetNativeCharacter q hq y = 0)
  Iff.rfl reset_native_odd_image image_bad

abbrev solutionsArena : Arena where
  signature := rowSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (ho : Odd q) (y : G q)
    (_hy : resetNativeCharacter q hq y = 0) (x : G q),
    resetNativeDefect q (r.readout () q x) = y ↔
      ∃! k : ℤ, x = resetNativePreimage q hq y + k • resetOddClass q

private theorem solutions_bad : ¬ solutionsArena.Law rowBad := by
  intro h
  obtain ⟨x, hx⟩ := unit_witness
  have hh := (h 1 (by decide) (by decide) 0 (map_zero _) x).mp (map_zero _)
  have hz := (reset_native_odd_all_solutions 1 (by decide) (by decide) 0 (map_zero _) x).mpr hh
  exact not_kernel_of_character_one hx ((reset_native_odd_kernel 1 (by decide) (by decide) x).mp hz)

def solutionsRegistration := rowRegistration solutionsArena.Law
  (∀ (q : ℕ) (hq : 0 < q) (ho : Odd q) (y : G q)
    (hy : resetNativeCharacter q hq y = 0) (x : G q),
    resetNativeDefect q x = y ↔ ∃! k : ℤ, x = resetNativePreimage q hq y + k • resetOddClass q)
  Iff.rfl reset_native_odd_all_solutions solutions_bad

abbrev allSolutionsArena : Arena where
  signature := rowSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (y x : G q),
    (Even q → (resetNativeDefect q (r.readout () q x) = y ↔ x = resetNativePreimage q hq y)) ∧
    (Odd q → (resetNativeDefect q (r.readout () q x) = y ↔
      resetNativeCharacter q hq y = 0 ∧
        ∃! k : ℤ, x = resetNativePreimage q hq y + k • resetOddClass q))

private theorem all_solutions_bad : ¬ allSolutionsArena.Law rowBad := by
  intro h
  apply solutions_bad
  intro q hq ho y hy x
  have hh := (h q hq y x).2 ho
  exact hh.trans (and_iff_right hy)

def allSolutionsRegistration := rowRegistration allSolutionsArena.Law
  (∀ (q : ℕ) (hq : 0 < q) (y x : G q),
    (Even q → (resetNativeDefect q x = y ↔ x = resetNativePreimage q hq y)) ∧
    (Odd q → (resetNativeDefect q x = y ↔ resetNativeCharacter q hq y = 0 ∧
      ∃! k : ℤ, x = resetNativePreimage q hq y + k • resetOddClass q)))
  Iff.rfl reset_native_all_solutions all_solutions_bad

abbrev charSignature : Signature where
  Params := Positive
  State p := G p.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev charActual : Realization charSignature :=
  realize charSignature (fun _ p => resetNativeCharacter p.val p.property) (fun e => nomatch e)
abbrev charBad : Realization charSignature := realize charSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev charOne : Realization charSignature := realize charSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem char_dependence : ObservationalDependence charSignature charActual := by
  intro i
  obtain ⟨x, hx⟩ := unit_witness
  refine ⟨⟨1, by decide⟩, x, 0, ?_⟩
  change resetNativeCharacter 1 (by decide) x ≠ resetNativeCharacter 1 (by decide) 0
  rw [hx, map_zero]
  decide

private def charRegistration (law : Realization charSignature → Prop) (Target : Prop)
    (bad : Realization charSignature) (bridge : Target ↔ law charActual)
    (hp : law charActual) (hn : ¬ law bad) : Registration ⟨charSignature, law⟩ Target :=
  register charSignature law Target charActual bad bridge hp hn char_dependence inferInstance inferInstance

abbrev charOntoArena : Arena where
  signature := charSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q), Function.Surjective (r.readout () ⟨q, hq⟩)

private theorem char_onto_bad : ¬ charOntoArena.Law charBad := by
  intro h
  obtain ⟨x, hx⟩ := h 1 (by decide) 1
  change (0 : ℤ) = 1 at hx
  omega

def charOntoRegistration := charRegistration charOntoArena.Law
  (∀ (q : ℕ) (hq : 0 < q), Function.Surjective (resetNativeCharacter q hq))
  charBad Iff.rfl reset_native_character_surjective char_onto_bad

abbrev pairingArena : Arena where
  signature := charSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (_ho : Odd q),
    r.readout () ⟨q, hq⟩ (resetOddClass q) = ((q + 1 : ℕ) : ℤ)

private theorem pairing_bad : ¬ pairingArena.Law charBad := by
  intro h
  have hz := h 1 (by decide) (by decide)
  change (0 : ℤ) = 2 at hz
  omega

def pairingRegistration := charRegistration pairingArena.Law
  (∀ (q : ℕ) (hq : 0 < q) (ho : Odd q), resetNativeCharacter q hq (resetOddClass q) = (q + 1 : ℕ))
  charBad Iff.rfl reset_native_pairing pairing_bad

abbrev charThetaArena : Arena where
  signature := charSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (_ho : Odd q) (x : G q),
    r.readout () ⟨q, hq⟩ (resetTheta q x) = -r.readout () ⟨q, hq⟩ x

private theorem char_theta_bad : ¬ charThetaArena.Law charOne := by
  intro h
  have hz := h 1 (by decide) (by decide) 0
  change (1 : ℤ) = -1 at hz
  omega

def charThetaRegistration := charRegistration charThetaArena.Law
  (∀ (q : ℕ) (hq : 0 < q) (ho : Odd q) (x : G q),
    resetNativeCharacter q hq (resetTheta q x) = -resetNativeCharacter q hq x)
  charOne Iff.rfl reset_native_character_theta char_theta_bad

abbrev charStageArena : Arena where
  signature := charSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (_ho : Odd q) (n : ℕ) (v : VertexModule Sign q),
    r.readout () ⟨q, hq⟩ (Module.DirectLimit.of ℤ ℕ (fun _ => VertexModule Sign q)
      (stationaryTransition (transition (resetMatrix q))) n v) = (-1 : ℤ)^n * resetCharacter q v

private theorem char_stage_bad : ¬ charStageArena.Law charOne := by
  intro h
  have hz := h 1 (by decide) (by decide) 0 0
  change (1 : ℤ) = (-1 : ℤ)^0 * resetCharacter 1 0 at hz
  simp at hz

def charStageRegistration := charRegistration charStageArena.Law
  (∀ (q : ℕ) (hq : 0 < q) (ho : Odd q) (n : ℕ) (v : VertexModule Sign q),
    resetNativeCharacter q hq (Module.DirectLimit.of ℤ ℕ (fun _ => VertexModule Sign q)
      (stationaryTransition (transition (resetMatrix q))) n v) = (-1 : ℤ)^n * resetCharacter q v)
  charOne Iff.rfl reset_native_character_stage char_stage_bad
abbrev finiteMapSignature : Signature where
  Params := Positive
  State p := G p.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := VertexModule Sign p.val
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev finiteMapActual : Realization finiteMapSignature :=
  realize finiteMapSignature (fun _ p => resetNativeEquiv p.val p.property) (fun e => nomatch e)
abbrev finiteMapBad : Realization finiteMapSignature :=
  realize finiteMapSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev finiteMapConstant : Realization finiteMapSignature :=
  realize finiteMapSignature (fun _ p _ => resetOddVector p.val) (fun e => nomatch e)

private theorem vector_ne : resetOddVector 1 ≠ 0 := by
  intro h
  have hz := congrArg (fun v : VertexModule Sign 1 => (v 0).coeff 1) h
  rw [resetOddVector_coeff_one] at hz
  simp at hz

private theorem finiteMap_dependence : ObservationalDependence finiteMapSignature finiteMapActual := by
  intro i
  obtain ⟨x, hx⟩ := (resetNativeEquiv 1 (by decide)).surjective (resetOddVector 1)
  refine ⟨⟨1, by decide⟩, x, 0, ?_⟩
  change resetNativeEquiv 1 (by decide) x ≠ resetNativeEquiv 1 (by decide) 0
  rw [hx, map_zero]
  exact vector_ne

private def finiteMapRegistration (law : Realization finiteMapSignature → Prop) (Target : Prop)
    (bad : Realization finiteMapSignature) (bridge : Target ↔ law finiteMapActual)
    (hp : law finiteMapActual) (hn : ¬ law bad) : Registration ⟨finiteMapSignature, law⟩ Target :=
  register finiteMapSignature law Target finiteMapActual bad bridge hp hn
    finiteMap_dependence inferInstance inferInstance

abbrev nativeStageArena : Arena where
  signature := finiteMapSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (n : ℕ) (v : VertexModule Sign q),
    r.readout () ⟨q, hq⟩ (Module.DirectLimit.of ℤ ℕ (fun _ => VertexModule Sign q)
      (stationaryTransition (transition (resetMatrix q))) n v) = (resetInverse q hq ^ n) v

private theorem native_stage_bad : ¬ nativeStageArena.Law finiteMapBad := by
  intro h
  have hz := h 1 (by decide) 0 (resetOddVector 1)
  change 0 = (resetInverse 1 (by decide) ^ 0) (resetOddVector 1) at hz
  exact vector_ne (by simpa only [pow_zero, Module.End.one_apply] using hz.symm)

def nativeStageRegistration := finiteMapRegistration nativeStageArena.Law
  (∀ (q : ℕ) (hq : 0 < q) (n : ℕ) (v : VertexModule Sign q),
    resetNativeEquiv q hq (Module.DirectLimit.of ℤ ℕ (fun _ => VertexModule Sign q)
      (stationaryTransition (transition (resetMatrix q))) n v) = (resetInverse q hq ^ n) v)
  finiteMapBad Iff.rfl resetNativeEquiv_stage native_stage_bad

abbrev nativeThetaArena : Arena where
  signature := finiteMapSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (x : G q),
    r.readout () ⟨q, hq⟩ (resetTheta q x) = transition (resetMatrix q) (r.readout () ⟨q, hq⟩ x)

private theorem native_theta_bad : ¬ nativeThetaArena.Law finiteMapConstant := by
  intro h
  have hz := h 1 (by decide) 0
  change resetOddVector 1 = transition (resetMatrix 1) (resetOddVector 1) at hz
  rw [reset_odd_transition 1 (by decide) (by decide)] at hz
  have hc := congrArg (fun v : VertexModule Sign 1 => (v 0).coeff 1) hz
  simp only [Pi.neg_apply, MonoidAlgebra.coeff_neg, Finsupp.neg_apply,
    resetOddVector_coeff_one, Fin.val_zero, pow_zero] at hc
  omega

def nativeThetaRegistration := finiteMapRegistration nativeThetaArena.Law
  (∀ (q : ℕ) (hq : 0 < q) (x : G q), resetNativeEquiv q hq (resetTheta q x) =
    transition (resetMatrix q) (resetNativeEquiv q hq x))
  finiteMapConstant Iff.rfl resetNativeEquiv_theta native_theta_bad

abbrev rangeSignature : Signature where
  Params := Nat
  State q := Module.End ℤ (G q)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := Submodule ℤ (G q)
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev rangeActual : Realization rangeSignature :=
  realize rangeSignature (fun _ _ f => LinearMap.range f) (fun e => nomatch e)
abbrev rangeBad : Realization rangeSignature := realize rangeSignature (fun _ _ _ => ⊤) (fun e => nomatch e)

private theorem range_dependence : ObservationalDependence rangeSignature rangeActual := by
  intro i
  refine ⟨1, 0, LinearMap.id, ?_⟩
  intro hh
  change LinearMap.range (0 : Module.End ℤ (G 1)) = LinearMap.range LinearMap.id at hh
  have hc : resetOddClass 1 ∈ LinearMap.range (LinearMap.id : Module.End ℤ (G 1)) := ⟨_, rfl⟩
  rw [← hh] at hc
  obtain ⟨v, hv⟩ := hc
  exact class_ne hv.symm

private def rangeRegistration (law : Realization rangeSignature → Prop) (Target : Prop)
    (bridge : Target ↔ law rangeActual) (hp : law rangeActual) (hn : ¬ law rangeBad) :
    Registration ⟨rangeSignature, law⟩ Target :=
  register rangeSignature law Target rangeActual rangeBad bridge hp hn range_dependence inferInstance inferInstance

abbrev rangeArena : Arena where
  signature := rangeSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (_ho : Odd q),
    r.readout () q (resetNativeDefect q) = LinearMap.ker (resetNativeCharacter q hq)

private theorem range_bad : ¬ rangeArena.Law rangeBad := by
  intro h
  obtain ⟨x, hx⟩ := unit_witness
  have hh := h 1 (by decide) (by decide)
  have hz : resetNativeCharacter 1 (by decide) x = 0 := by
    have he : x ∈ LinearMap.ker (resetNativeCharacter 1 (by decide)) := hh ▸ Submodule.mem_top
    exact he
  omega

def rangeEqualityRegistration := rangeRegistration rangeArena.Law
  (∀ (q : ℕ) (hq : 0 < q) (ho : Odd q),
    LinearMap.range (resetNativeDefect q) = LinearMap.ker (resetNativeCharacter q hq))
  Iff.rfl reset_native_odd_range range_bad

abbrev intersectionArena : Arena where
  signature := rangeSignature
  Law r := ∀ (q : ℕ) (_hq : 0 < q) (_ho : Odd q),
    LinearMap.ker (resetNativeDefect q) ⊓ r.readout () q (resetNativeDefect q) = ⊥

private theorem intersection_bad : ¬ intersectionArena.Law rangeBad := by
  intro h
  have hh := h 1 (by decide) (by decide)
  have hc : resetOddClass 1 ∈ LinearMap.ker (resetNativeDefect 1) :=
    (reset_odd_killed_class 1 (by decide) (by decide)).2
  have hz : resetOddClass 1 ∈ (⊥ : Submodule ℤ (G 1)) := by
    rw [← hh]
    exact ⟨hc, Submodule.mem_top⟩
  exact class_ne ((Submodule.mem_bot ℤ).mp hz)

def intersectionRegistration := rangeRegistration intersectionArena.Law
  (∀ (q : ℕ) (hq : 0 < q) (ho : Odd q),
    LinearMap.ker (resetNativeDefect q) ⊓ LinearMap.range (resetNativeDefect q) = ⊥)
  Iff.rfl reset_native_kernel_inf_range intersection_bad

abbrev sumArena : Arena where
  signature := rangeSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (_ho : Odd q) (x : G q),
    x ∈ r.readout () q (resetNativeDefect q) ⊔ LinearMap.ker (resetNativeDefect q) ↔
      ((q + 1 : ℕ) : ℤ) ∣ resetNativeCharacter q hq x

private theorem sum_bad : ¬ sumArena.Law rangeBad := by
  intro h
  obtain ⟨x, hx⟩ := unit_witness
  have hh := (h 1 (by decide) (by decide) x).mp (by change x ∈ (⊤ : Submodule ℤ (G 1)) ⊔ _; simp)
  change (2 : ℤ) ∣ resetNativeCharacter 1 (by decide) x at hh
  rw [hx] at hh
  norm_num at hh

def sumRegistration := rangeRegistration sumArena.Law
  (∀ (q : ℕ) (hq : 0 < q) (ho : Odd q) (x : G q),
    x ∈ LinearMap.range (resetNativeDefect q) ⊔ LinearMap.ker (resetNativeDefect q) ↔
      ((q + 1 : ℕ) : ℤ) ∣ resetNativeCharacter q hq x)
  Iff.rfl reset_native_sum_criterion sum_bad

abbrev inverseSignature : Signature where
  Params := Positive
  State p := Module.End ℤ (VertexModule Sign p.val)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Module.End ℤ (VertexModule Sign p.val)
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev inverseActual : Realization inverseSignature := realize inverseSignature (fun _ _ f => f) (fun e => nomatch e)
abbrev inverseBad : Realization inverseSignature := realize inverseSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem one_ne_zero : (1 : Module.End ℤ (VertexModule Sign 1)) ≠ 0 := by
  intro hh
  have hz := LinearMap.congr_fun hh (resetOddVector 1)
  exact vector_ne hz

abbrev inverseArena : Arena where
  signature := inverseSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q),
    resetInverse q hq * r.readout () ⟨q, hq⟩ (transition (resetMatrix q)) = 1 ∧
      r.readout () ⟨q, hq⟩ (transition (resetMatrix q)) * resetInverse q hq = 1

private theorem inverse_bad : ¬ inverseArena.Law inverseBad := by
  intro h
  have hz := (h 1 (by decide)).1
  change resetInverse 1 (by decide) * 0 = 1 at hz
  rw [mul_zero] at hz
  exact one_ne_zero hz.symm

def inverseRegistration : Registration inverseArena
  (∀ (q : ℕ) (hq : 0 < q), resetInverse q hq * transition (resetMatrix q) = 1 ∧
    transition (resetMatrix q) * resetInverse q hq = 1) :=
  register inverseSignature inverseArena.Law _ inverseActual inverseBad Iff.rfl
    reset_transition_inverse inverse_bad (by intro i; exact ⟨⟨1, by decide⟩, 1, 0, one_ne_zero⟩)
    inferInstance inferInstance

abbrev timeSignature : Signature where
  Params := Nat
  State q := Module.End ℤ (G q)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := Module.End ℤ (G q)
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev timeActual : Realization timeSignature := realize timeSignature (fun _ _ f => f) (fun e => nomatch e)
abbrev timeBad : Realization timeSignature := realize timeSignature (fun _ _ _ => -LinearMap.id) (fun e => nomatch e)

abbrev sectionArena : Arena where
  signature := timeSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (_ho : Odd q),
    ¬ ∃ s : ℤ →ₗ[ℤ] G q, (resetNativeCharacter q hq).comp s = LinearMap.id ∧
      ∀ n : ℤ, r.readout () q (resetTheta q) (s n) = s (-n)

private theorem section_bad : ¬ sectionArena.Law timeBad := by
  intro h
  obtain ⟨x, hx⟩ := unit_witness
  apply h 1 (by decide) (by decide)
  refine ⟨LinearMap.toSpanSingleton ℤ (G 1) x, ?_, ?_⟩
  · apply LinearMap.ext
    intro n
    change resetNativeCharacter 1 (by decide) (n • x) = n
    rw [map_smul, hx, smul_eq_mul, mul_one]
  · intro n
    simp only [timeBad, realize, LinearMap.neg_apply, LinearMap.id_apply,
      LinearMap.toSpanSingleton_apply, neg_smul]

private theorem time_dependence : ObservationalDependence timeSignature timeActual := by
  intro i
  refine ⟨1, LinearMap.id, 0, ?_⟩
  intro hh
  exact class_ne (LinearMap.congr_fun hh (resetOddClass 1))

def sectionRegistration : Registration sectionArena
  (∀ (q : ℕ) (hq : 0 < q) (ho : Odd q),
    ¬ ∃ s : ℤ →ₗ[ℤ] G q, (resetNativeCharacter q hq).comp s = LinearMap.id ∧
      ∀ n : ℤ, resetTheta q (s n) = s (-n)) :=
  register timeSignature sectionArena.Law _ timeActual timeBad Iff.rfl
    reset_native_no_equivariant_linear_section section_bad time_dependence inferInstance inferInstance

noncomputable def registration_reset_transition_inverse : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_transition_inverse)
    (Realization inverseArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_transition_inverse_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.inverseRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨inverseArena⟩
  objectArena := .source ⟨inverseArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source inverseArena ⟨inverseRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize inverseSignature (fun _ _ f => f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_resetNativeEquiv_stage : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.resetNativeEquiv_stage)
    (Realization nativeStageArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.resetNativeEquiv_stage_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.nativeStageRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨nativeStageArena⟩
  objectArena := .source ⟨nativeStageArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nativeStageArena ⟨nativeStageRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize finiteMapSignature (fun _ p => resetNativeEquiv p.val p.property) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_resetNativeEquiv_theta : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.resetNativeEquiv_theta)
    (Realization nativeThetaArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.resetNativeEquiv_theta_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.nativeThetaRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨nativeThetaArena⟩
  objectArena := .source ⟨nativeThetaArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nativeThetaArena ⟨nativeThetaRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize finiteMapSignature (fun _ p => resetNativeEquiv p.val p.property) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_reset_native_character_stage : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_character_stage)
    (Realization charStageArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_character_stage_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.charStageRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨charStageArena⟩
  objectArena := .source ⟨charStageArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source charStageArena ⟨charStageRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize charSignature (fun _ p => resetNativeCharacter p.val p.property) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_reset_native_character_theta : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_character_theta)
    (Realization charThetaArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_character_theta_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.charThetaRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨charThetaArena⟩
  objectArena := .source ⟨charThetaArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source charThetaArena ⟨charThetaRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize charSignature (fun _ p => resetNativeCharacter p.val p.property) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_reset_native_character_surjective : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_character_surjective)
    (Realization charOntoArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_character_surjective_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.charOntoRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨charOntoArena⟩
  objectArena := .source ⟨charOntoArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source charOntoArena ⟨charOntoRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize charSignature (fun _ p => resetNativeCharacter p.val p.property) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_reset_native_odd_kernel : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_odd_kernel)
    (Realization kernelArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_odd_kernel_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.kernelRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨kernelArena⟩
  objectArena := .source ⟨kernelArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source kernelArena ⟨kernelRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rowSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_reset_native_odd_image : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_odd_image)
    (Realization imageArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_odd_image_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.imageRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨imageArena⟩
  objectArena := .source ⟨imageArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source imageArena ⟨imageRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rowSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "arg", "body", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_reset_native_odd_all_solutions : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_odd_all_solutions)
    (Realization solutionsArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_odd_all_solutions_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.solutionsRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨solutionsArena⟩
  objectArena := .source ⟨solutionsArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source solutionsArena ⟨solutionsRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rowSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_reset_native_odd_range : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_odd_range)
    (Realization rangeArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_odd_range_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.rangeEqualityRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨rangeArena⟩
  objectArena := .source ⟨rangeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rangeArena ⟨rangeEqualityRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rangeSignature (fun _ _ f => LinearMap.range f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_reset_native_pairing : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_pairing)
    (Realization pairingArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_pairing_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.pairingRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨pairingArena⟩
  objectArena := .source ⟨pairingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pairingArena ⟨pairingRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize charSignature (fun _ p => resetNativeCharacter p.val p.property) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_reset_native_kernel_inf_range : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_kernel_inf_range)
    (Realization intersectionArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_kernel_inf_range_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.intersectionRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨intersectionArena⟩
  objectArena := .source ⟨intersectionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source intersectionArena ⟨intersectionRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rangeSignature (fun _ _ f => LinearMap.range f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_reset_native_sum_criterion : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_sum_criterion)
    (Realization sumArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_sum_criterion_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.sumRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨sumArena⟩
  objectArena := .source ⟨sumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sumArena ⟨sumRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rangeSignature (fun _ _ f => LinearMap.range f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_reset_native_no_equivariant_linear_section : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_no_equivariant_linear_section)
    (Realization sectionArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_no_equivariant_linear_section_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.sectionRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨sectionArena⟩
  objectArena := .source ⟨sectionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sectionArena ⟨sectionRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize timeSignature (fun _ _ f => f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "arg", "body", "arg", "arg", "body", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def registration_reset_native_all_solutions : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_all_solutions)
    (Realization allSolutionsArena.signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.reset_native_all_solutions_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect.allSolutionsRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨allSolutionsArena⟩
  objectArena := .source ⟨allSolutionsArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source allSolutionsArena ⟨allSolutionsRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rowSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
