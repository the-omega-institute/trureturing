import Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
import D5.S3.Quantum.Fibers.SharedEnergyGapBound

/-! Labelled-degree audit for all indecomposable zero-weight exponents. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace Reg.D5.S3.Quantum.Fibers.SharedEnergyGapBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
open _root_.D5.S3.Quantum.Fibers.SharedEnergyGapBound

abbrev signature : Signature where
  Params := Unit
  State _ := Exponent
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def readoutFunction : Unit → Unit → Exponent → ℕ := fun _ _ alpha => degree alpha
def actual : Realization signature := realize signature readoutFunction (fun e => nomatch e)
def shifted : Realization signature := realize signature (fun _ _ alpha => degree alpha + 1)
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 2 ≤ m → ∀ (alpha : Exponent), Indecomposable m alpha →
    R.readout () () alpha ≤ 2*m-1
private theorem bridge : (type_of% indecomposable_degree_bound) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law shifted := by
  intro h
  let alpha : Exponent := fun i j =>
    if i = 2 ∧ j = 1 then 2 else if i = 0 ∧ j = 2 then 1 else 0
  have hi : Indecomposable 2 alpha := by
    refine ⟨?_, ?_, ?_⟩
    · intro hz
      have he := congrFun (congrFun hz 2) 1
      norm_num [alpha] at he
    · norm_num [weight, alpha, energy, Fin.sum_univ_succ]
    · intro beta hle hw
      have hs : beta = fun i j => if i = 2 ∧ j = 1 then beta 2 1 else
          if i = 0 ∧ j = 2 then beta 0 2 else 0 := by
        ext i j
        split_ifs with h₁ h₂
        · obtain ⟨rfl, rfl⟩ := h₁; rfl
        · obtain ⟨rfl, rfl⟩ := h₂; rfl
        · have he := hle i j
          simpa [alpha, h₁, h₂] using he
      have hk : (beta 2 1 : ℤ) + 2 * (-(beta 0 2 : ℤ)) = 0 := by
        rw [hs] at hw
        simp [weight, energy, Fin.sum_univ_succ] at hw
        linear_combination hw
      let A : Matrix (Fin 1) (Fin 2) ℤ := !![1, 2]
      let v : Fin 2 → ℤ := ![2, -1]
      have hdet : (_root_.D5.S3.Arith.Lattices.CofactorKernel.augment A).det ≠ 0 := by
        have he : _root_.D5.S3.Arith.Lattices.CofactorKernel.augment A =
            !![1, 1; 1, 2] := by
          ext i j
          fin_cases i <;> fin_cases j <;> rfl
        rw [he, Matrix.det_fin_two]
        norm_num
      have hv : A *ᵥ v = 0 := by
        ext i
        fin_cases i
        norm_num [A, v, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      have hx : A *ᵥ ![(beta 2 1 : ℤ), -(beta 0 2 : ℤ)] = 0 := by
        ext i
        fin_cases i
        simpa [A, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hk
      have hgc : Finset.univ.gcd v = 1 := by
        have h₀ : Finset.univ.gcd v ∣ v 0 := Finset.gcd_dvd (Finset.mem_univ _)
        have h₁ : Finset.univ.gcd v ∣ v 1 := Finset.gcd_dvd (Finset.mem_univ _)
        have hd : Finset.univ.gcd v ∣ 1 := by
          convert dvd_add h₀ h₁ using 1
          norm_num [v]
        have hn := normalize_eq_one.mpr (isUnit_iff_dvd_one.mpr hd)
        simpa only [Finset.normalize_gcd] using hn
      obtain ⟨ell, he⟩ := _root_.D5.S3.Arith.Lattices.CofactorKernel.primitive_kernel_span
        A hdet v hv (by norm_num [v, Fin.sum_univ_succ]) hgc _ hx
      have he₁ : (beta 2 1 : ℤ) = ell*2 := by simpa [v] using he 0
      have he₂ : -(beta 0 2 : ℤ) = ell*(-1) := by simpa [v] using he 1
      have hb : beta 2 1 ≤ 2 := by simpa [alpha] using hle 2 1
      have he : ell = 0 ∨ ell = 1 := by omega
      rcases he with rfl | rfl
      · left
        have h₁ : beta 2 1 = 0 := by omega
        have h₂ : beta 0 2 = 0 := by omega
        rw [hs]
        simp only [h₁, h₂, ite_self]
        rfl
      · right
        have h₁ : beta 2 1 = 2 := by omega
        have h₂ : beta 0 2 = 1 := by omega
        rw [hs]
        simp only [h₁, h₂]
        rfl
  have he := h 2 (by omega) alpha hi
  change degree alpha + 1 ≤ 2*2-1 at he
  norm_num [degree, alpha, Fin.sum_univ_succ] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, (fun _ _ => 1), ?_⟩
  intro h
  change degree 0 = degree (fun _ _ => 1) at h
  norm_num [degree, Fin.sum_univ_succ] at h

def family : Registration arena (type_of% indecomposable_degree_bound) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp indecomposable_degree_bound, shifted, rejected⟩
  sensitivity := ⟨fun i => ⟨shifted,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    indecomposable_degree_bound (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyGapBound.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyGapBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature readoutFunction (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.SharedEnergyGapBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Quantum.Fibers.SharedEnergyGapBound
