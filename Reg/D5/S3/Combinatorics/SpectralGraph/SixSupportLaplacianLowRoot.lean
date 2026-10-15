import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
open _root_.D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix Filter Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

def balancedLaw (f : ℝ → ℝ) : Prop :=
    (∀ m : ℝ, 1 ≤ m →
      (∃ z : Fin 6 → ℝ, z ≠ 0 ∧ quotient m m m *ᵥ z = f m • z) ∧
      0 < f m ∧ f m < m ∧
      3*m/(m+4) < f m ∧ f m < 3 ∧
      f m = 6*m/(m+4+Real.sqrt ((m+4)^2-12)) ∧
      (∀ e : ℝ, 0 < e → ∀ z : Fin 6 → ℝ, z ≠ 0 →
        quotient m m m *ᵥ z = e • z → f m ≤ e) ∧
      (∀ x : ℝ, (x • (1 : Matrix (Fin 6) (Fin 6) ℝ) - quotient m m m).det =
        x*(x-m^2-m)*(x^2-(m^2+4*m)*x+3*m^2)^2) ∧
      f m < m^2+m ∧
      m^2+m < (m^2+4*m+m*Real.sqrt ((m+4)^2-12))/2) ∧
    Tendsto f atTop (𝓝 3) ∧
    Tendsto (fun n : ℕ => f (n : ℝ)) atTop (𝓝 3) ∧
    (∀ K : ℝ, K < 3 → ∃ n : ℕ, 1 ≤ n ∧ K < f n ∧
      ∃ z : Fin 6 → ℝ, z ≠ 0 ∧ quotient n n n *ᵥ z = f n • z)

abbrev balancedSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def balancedActual : Realization balancedSignature :=
  realize balancedSignature (fun _ _ m => balancedLow m) (fun e => nomatch e)

def balancedRejected : Realization balancedSignature :=
  realize balancedSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev balancedArena : Arena where
  signature := balancedSignature
  Law r := balancedLaw (r.readout () ())

private theorem balanced_rejected_law : ¬ balancedArena.Law balancedRejected := by
  intro h
  change balancedLaw (fun _ => 0) at h
  have hh : (0 : ℝ) < 0 := (h.1 1 (by norm_num)).2.1
  exact lt_irrefl _ hh

private theorem balanced_dependence : ObservationalDependence balancedSignature balancedActual := by
  intro i
  refine ⟨(),1,4,?_⟩
  change balancedLow 1 ≠ balancedLow 4
  have h1 := (balanced_sharp_threshold.1 1 (by norm_num)).2.2.1
  have h4 := (balanced_sharp_threshold.1 4 (by norm_num)).2.2.2.1
  norm_num at h1 h4
  linarith

def balancedSource : Registration balancedArena (type_of% @balanced_sharp_threshold) where
  actual := balancedActual
  bridge := Iff.rfl
  variation := ⟨balanced_sharp_threshold,balancedRejected,balanced_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨balancedRejected,?_,rfl,balanced_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := balanced_dependence

def balancedRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@balanced_sharp_threshold) (Realization balancedSignature) Type Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot.balancedUnit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot.balancedSource
  realizationSource := none
  generated := false
  arena := .source ⟨balancedArena⟩
  objectArena := .source ⟨balancedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source balancedArena ⟨balancedSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize balancedSignature (fun _ _ m => balancedLow m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg","fn","arg","fn","fn","arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


def geometryLaw (f : ℝ → ℝ → ℝ → Matrix (Fin 6) (Fin 6) ℝ) : Prop :=
    ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c),
    ((∀ z : Fin 6 → ℝ,
      dotProduct (fun i => weights a b c i * z i) (quotient a b c *ᵥ z) =
        a*b*(z 0-z 1)^2 + a*c*(z 0-z 2)^2 + b*c*(z 1-z 2)^2 +
        a*b*c*((z 0-z 5)^2+(z 1-z 4)^2+(z 2-z 3)^2)) ∧
    (∀ z, quotient a b c *ᵥ z = 0 ↔ ∃ t, z = fun _ => t) ∧
    quotient a b c *ᵥ (fun _ => (1 : ℝ)) = 0 ∧
    vecMul (weights a b c) (quotient a b c) = 0) ∧
    (f a b c).PosSemidef ∧
    (f a b c = diagonal (rootWeights a b c) *
      (quotient a b c).submatrix supportPermutation supportPermutation *
        diagonal (fun i => (rootWeights a b c i)⁻¹)) ∧
    (∀ e : ℝ, ∀ z : Fin 6 → ℝ, z ≠ 0 → f a b c *ᵥ z = e • z →
      toQuotientVector a b c z ≠ 0 ∧
        quotient a b c *ᵥ toQuotientVector a b c z = e • toQuotientVector a b c z)

def smallLaw (f : ℝ → ℝ → ℝ → Matrix (Fin 6) (Fin 6) ℝ) : Prop :=
    ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hb3 : b ≤ 3),
    ∃ t : ℝ, Function.Injective (fun u : Fin 2 → ℝ =>
        (![u 0,u 1,0,t*u 0,t*u 1,0] : Fin 6 → ℝ)) ∧
      ∀ u : Fin 2 → ℝ, u ≠ 0 →
        dotProduct (![u 0,u 1,0,t*u 0,t*u 1,0] : Fin 6 → ℝ)
          ((f a b c - (3 : ℝ) • 1) *ᵥ ![u 0,u 1,0,t*u 0,t*u 1,0]) < 0

def lowLaw (f : ℝ → ℝ → ℝ → Matrix (Fin 6) (Fin 6) ℝ) : Prop :=
    ∀ (a b c : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c),
    ∃ e : ℝ, 0 < e ∧ e < 3 ∧ ∃ z : Fin 6 → ℝ, z ≠ 0 ∧ f a b c *ᵥ z = e • z

abbrev matrixSignature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 6) (Fin 6) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def symmetricActual : Realization matrixSignature :=
  realize matrixSignature (fun _ p c => symmetric p.1 p.2 c) (fun e => nomatch e)
def quotientActual : Realization matrixSignature :=
  realize matrixSignature (fun _ p c => quotient p.1 p.2 c) (fun e => nomatch e)
def matrixZero : Realization matrixSignature :=
  realize matrixSignature (fun _ _ _ => 0) (fun e => nomatch e)
def matrixThree : Realization matrixSignature :=
  realize matrixSignature (fun _ _ _ => (3 : ℝ) • 1) (fun e => nomatch e)

abbrev geometryArena : Arena where
  signature := matrixSignature
  Law r := geometryLaw (fun a b c => r.readout () ⟨a,b⟩ c)

abbrev smallArena : Arena where
  signature := matrixSignature
  Law r := smallLaw (fun a b c => r.readout () ⟨a,b⟩ c)

abbrev lowArena : Arena where
  signature := matrixSignature
  Law r := lowLaw (fun a b c => r.readout () ⟨a,b⟩ c)

private theorem geometry_rejected : ¬ geometryArena.Law matrixZero := by
  intro h
  have hh := (h 1 1 1 (by norm_num) (by norm_num) (by norm_num)).2.2.1
  have h00 := congrFun (congrFun hh 0) 0
  norm_num [matrixZero,realize,rootWeights,quotient,supportPermutation,
    Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.diagonal_apply] at h00
  change (0 : ℝ) = 3 at h00
  norm_num at h00

private theorem small_rejected : ¬ smallArena.Law matrixThree := by
  intro h
  obtain ⟨t,ht,hn⟩ := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hu : (![1,0] : Fin 2 → ℝ) ≠ 0 := by
    intro hz; have hh := congrFun hz 0; norm_num at hh
  have hn' := hn ![1,0] hu
  simp [matrixThree,realize] at hn'

private theorem low_rejected : ¬ lowArena.Law matrixZero := by
  intro h
  obtain ⟨e,he,he3,z,hz,heq⟩ := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  change (0 : Matrix (Fin 6) (Fin 6) ℝ) *ᵥ z = e • z at heq
  simp only [Matrix.zero_mulVec] at heq
  exact hz ((smul_eq_zero.mp heq.symm).resolve_left he.ne')

private theorem symmetric_dependence : ObservationalDependence matrixSignature symmetricActual := by
  intro i
  refine ⟨⟨1,1⟩,1,2,?_⟩
  intro h
  have hh := congrFun (congrFun h 0) 0
  norm_num [symmetricActual,realize,symmetric] at hh

private theorem quotient_dependence : ObservationalDependence matrixSignature quotientActual := by
  intro i
  refine ⟨⟨1,1⟩,1,2,?_⟩
  intro h
  have hh := congrFun (congrFun h 0) 0
  norm_num [quotientActual,realize,quotient] at hh

def geometrySource : Registration geometryArena (type_of% @quotient_geometry) where
  actual := symmetricActual
  bridge := Iff.rfl
  variation := ⟨@quotient_geometry,matrixZero,geometry_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨matrixZero,?_,rfl,geometry_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := symmetric_dependence

def smallSource : Registration smallArena (type_of% @small_second_negative_plane) where
  actual := symmetricActual
  bridge := Iff.rfl
  variation := ⟨@small_second_negative_plane,matrixThree,small_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨matrixThree,?_,rfl,small_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := symmetric_dependence

def lowSource : Registration lowArena (type_of% @positive_real_low_eigenvalue) where
  actual := quotientActual
  bridge := Iff.rfl
  variation := ⟨@positive_real_low_eigenvalue,matrixZero,low_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨matrixZero,?_,rfl,low_rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := quotient_dependence

def geometryRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@quotient_geometry) (Realization matrixSignature) Type Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot.geometryUnit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot.geometrySource
  realizationSource := none
  generated := false
  arena := .source ⟨geometryArena⟩
  objectArena := .source ⟨geometryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source geometryArena ⟨geometrySource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ p c => symmetric p.1 p.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","arg","fn","arg","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def smallRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@small_second_negative_plane) (Realization matrixSignature) Type Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot.smallUnit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot.smallSource
  realizationSource := none
  generated := false
  arena := .source ⟨smallArena⟩
  objectArena := .source ⟨smallArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source smallArena ⟨smallSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ p c => symmetric p.1 p.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg","body","arg","body","body","fn","arg","arg","fn","arg","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def lowRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@positive_real_low_eigenvalue) (Realization matrixSignature) Type Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot.lowUnit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot.lowSource
  realizationSource := none
  generated := false
  arena := .source ⟨lowArena⟩
  objectArena := .source ⟨lowArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lowArena ⟨lowSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ p c => quotient p.1 p.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","arg","body","arg","arg","arg","body","arg","fn","arg","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
