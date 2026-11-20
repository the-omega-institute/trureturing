import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.TangentInvariantForms
import Reg.Support.DependentFamily

/-! Source-bound audits of the invariant bilinear forms on the pure quaternions. The readouts are
the invariant form `c ⟪x, y⟫` as a function of its scalar `c`, and the three-parameter form
`α ⟪x, y⟫ + β ⟪n, x⟫ ⟪n, y⟫ + γ ⟪n, x * y⟫` as a function of `α`. -/

namespace Reg.D5.S3.Quantum.AURICOmega.TangentInvariantForms

open _root_.D5.S3.Quantum.AURICOmega.TangentInvariantForms
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open scoped InnerProductSpace Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

/-- The quaternion `1` has inner product `1` with itself. -/
theorem inner_one_one : ⟪(1 : ℍ[ℝ]), (1 : ℍ[ℝ])⟫_ℝ = 1 := by
  rw [inner_eq_components]; simp

/-! ## The scalar multiple of the inner product -/
namespace Scalar

/-- Two quaternions `x`, `y`; the state is the scalar `c`. -/
abbrev signature : Signature where
  Params := Σ _ : ℍ[ℝ], ℍ[ℝ]
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The value `c ⟪x, y⟫`. -/
def observe (p : Σ _ : ℍ[ℝ], ℍ[ℝ]) (c : ℝ) : ℝ := c * ⟪p.1, p.2⟫_ℝ

def actual : Realization signature :=
  realize signature (fun _ => observe) (fun e => nomatch e)

/-- The value `c ⟪x, y⟫ + 1`. -/
def rejected : Realization signature :=
  realize signature (fun _ p c => c * ⟪p.1, p.2⟫_ℝ + 1) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
  change (0 : ℝ) * ⟪(1 : ℍ[ℝ]), (1 : ℍ[ℝ])⟫_ℝ ≠ 1 * ⟪(1 : ℍ[ℝ]), (1 : ℍ[ℝ])⟫_ℝ
  rw [inner_one_one]; norm_num

/-- The zero form is invariant under every conjugation. -/
theorem zero_invariant (u : unitary ℍ[ℝ]) (x y : ℍ[ℝ]) :
    (0 : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ) ((u : ℍ[ℝ]) * x * star (u : ℍ[ℝ]))
      ((u : ℍ[ℝ]) * y * star (u : ℍ[ℝ])) = (0 : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ) x y := by
  simp

/-- For the zero form the rejected reading would give `0 = c ⟪0, 0⟫ + 1`. -/
theorem rejected_zero (c : ℝ)
    (h : ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 →
      (0 : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ) x y = rejected.readout () ⟨x, y⟩ c) : False := by
  have hh := h 0 0 (by simp) (by simp)
  simp [rejected, realize] at hh

/-! ### `invariant_bilinear_tfae` -/

/-- Retain the complete family and list telescope of `invariant_bilinear_tfae`; only the
multiple `c ⟪x, y⟫` in the first item is read out. -/
abbrev tfaeArena : Arena where
  signature := signature
  Law r := ∀ (S : Set (unitary ℍ[ℝ])),
    List.TFAE
      [ ∀ B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ,
          (∀ u ∈ S, ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 →
            B ((u : ℍ[ℝ]) * x * star (u : ℍ[ℝ])) ((u : ℍ[ℝ]) * y * star (u : ℍ[ℝ])) = B x y) →
          ∃ c : ℝ, ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 → B x y = r.readout () ⟨x, y⟩ c,
        ∀ B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ, (∀ x y, B x y = B y x) →
          (∀ u ∈ S, ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 →
            B ((u : ℍ[ℝ]) * x * star (u : ℍ[ℝ])) ((u : ℍ[ℝ]) * y * star (u : ℍ[ℝ])) = B x y) →
          ∃ c : ℝ, ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 → B x y = c * ⟪x, y⟫_ℝ,
        ∀ W : Submodule ℝ ℍ[ℝ], (∀ w ∈ W, w.re = 0) →
          (∀ u ∈ S, ∀ w ∈ W, (u : ℍ[ℝ]) * w * star (u : ℍ[ℝ]) ∈ W) →
          W = ⊥ ∨ ∀ x : ℍ[ℝ], x.re = 0 → x ∈ W ]

/-- For all unit quaternions the third item holds, so the rejected first item would have to
hold as well, and it fails for the zero form. -/
theorem tfae_rejected_law : ¬ tfaeArena.Law rejected := by
  intro h
  have h13 := (invariant_bilinear_tfae Set.univ).out 1 3
  have h3 := h13.1 fun B hB => conj_invariant_bilinear_eq_smul_inner B
    fun u => hB u (Set.mem_univ u)
  have h13' := (h Set.univ).out 1 3
  obtain ⟨c, hc⟩ := h13'.2 h3 0 fun u _ x y _ _ => zero_invariant u x y
  exact rejected_zero c hc

/-- The exact statement of the source theorem. -/
abbrev tfaeStatement : Prop := type_of% @invariant_bilinear_tfae

def tfae_registration_proof : Registration tfaeArena tfaeStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@invariant_bilinear_tfae, rejected, tfae_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, tfae_rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

/-! ### `conj_invariant_bilinear_eq_smul_inner` -/

/-- Retain the complete form and invariance telescope of
`conj_invariant_bilinear_eq_smul_inner`; only the multiple `c ⟪x, y⟫` is read out. -/
abbrev univArena : Arena where
  signature := signature
  Law r := ∀ (B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ),
    (∀ u : unitary ℍ[ℝ], ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 →
      B ((u : ℍ[ℝ]) * x * star (u : ℍ[ℝ])) ((u : ℍ[ℝ]) * y * star (u : ℍ[ℝ])) = B x y) →
    ∃ c : ℝ, ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 → B x y = r.readout () ⟨x, y⟩ c

theorem univ_rejected_law : ¬ univArena.Law rejected := by
  intro h
  obtain ⟨c, hc⟩ := h 0 fun u x y _ _ => zero_invariant u x y
  exact rejected_zero c hc

/-- The exact statement of the source theorem. -/
abbrev univStatement : Prop := type_of% @conj_invariant_bilinear_eq_smul_inner

def univ_registration_proof : Registration univArena univStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@conj_invariant_bilinear_eq_smul_inner, rejected, univ_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, univ_rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Scalar

/-! ## The three-parameter family of one conjugation -/
namespace Family

/-- A unit quaternion `u`, the coefficients `β`, `γ` and two quaternions `x`, `y`; the state is
the coefficient `α`. -/
abbrev Params := Σ _ : unitary ℍ[ℝ], Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℍ[ℝ], ℍ[ℝ]

abbrev signature : Signature where
  Params := Params
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The value `α ⟪x, y⟫ + β ⟪n, x⟫ ⟪n, y⟫ + γ ⟪n, x * y⟫` with `n = u.im`. -/
def observe (p : Params) (α : ℝ) : ℝ :=
  α * ⟪p.2.2.2.1, p.2.2.2.2⟫_ℝ +
    p.2.1 * ⟪(p.1 : ℍ[ℝ]).im, p.2.2.2.1⟫_ℝ * ⟪(p.1 : ℍ[ℝ]).im, p.2.2.2.2⟫_ℝ +
    p.2.2.1 * ⟪(p.1 : ℍ[ℝ]).im, p.2.2.2.1 * p.2.2.2.2⟫_ℝ

def actual : Realization signature :=
  realize signature (fun _ => observe) (fun e => nomatch e)

/-- The same value plus `1`. -/
def rejected : Realization signature :=
  realize signature (fun _ p α => observe p α + 1) (fun e => nomatch e)

/-- Retain the complete unit quaternion, hypothesis, form and coefficient telescope of
`conj_invariant_bilinear_iff`; only the three-parameter form, as a function of `α`, is read out. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (u : unitary ℍ[ℝ]), (u : ℍ[ℝ]).re ≠ 0 → (u : ℍ[ℝ]).im ≠ 0 →
    ∀ (B : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ),
    (∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 →
        B ((u : ℍ[ℝ]) * x * star (u : ℍ[ℝ])) ((u : ℍ[ℝ]) * y * star (u : ℍ[ℝ])) = B x y) ↔
      ∃ α β γ : ℝ, ∀ x y : ℍ[ℝ], x.re = 0 → y.re = 0 →
        B x y = r.readout () ⟨u, β, γ, x, y⟩ α

/-- The unit quaternion `3/5 + (4/5) i`. -/
def rotor : unitary ℍ[ℝ] :=
  ⟨⟨3 / 5, 4 / 5, 0, 0⟩, Unitary.mem_iff.mpr
    ⟨by ext <;> simp <;> norm_num, by ext <;> simp <;> norm_num⟩⟩

theorem rotor_re : (rotor : ℍ[ℝ]).re ≠ 0 := by
  change (3 / 5 : ℝ) ≠ 0; norm_num

theorem rotor_im : (rotor : ℍ[ℝ]).im ≠ 0 := fun h => by
  have h' := congrArg (fun z : ℍ[ℝ] => z.imI) h
  change (4 / 5 : ℝ) = 0 at h'
  norm_num at h'

/-- For the rotation `3/5 + (4/5) i` the zero form is invariant, while the rejected reading would
give `0 = 1` at `x = y = 0`. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨α, β, γ, hf⟩ := (h rotor rotor_re rotor_im 0).1 fun x y _ _ => by simp
  have hh := hf 0 0 (by simp) (by simp)
  simp [rejected, realize, observe] at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 0, 0, 1, 1⟩, 0, 1, ?_⟩
  change observe ⟨1, 0, 0, 1, 1⟩ 0 ≠ observe ⟨1, 0, 0, 1, 1⟩ 1
  simp only [observe, zero_mul, add_zero, one_mul, inner_one_one]
  norm_num

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @conj_invariant_bilinear_iff

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@conj_invariant_bilinear_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Family

def invariant_bilinear_tfae_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@invariant_bilinear_tfae) (Realization Scalar.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TangentInvariantForms.invariant_bilinear_tfae_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TangentInvariantForms.Scalar.tfae_registration_proof
  realizationSource := none
  generated := false
  arena := .source ⟨Scalar.tfaeArena⟩
  objectArena := .source ⟨Scalar.tfaeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Scalar.tfaeArena ⟨Scalar.tfae_registration_proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Scalar.signature (fun _ => Scalar.observe) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TangentInvariantForms
    definition := none
    coordinates := #[4, 5]
    readouts := #[{
      path := #["body", "arg", "fn", "arg", "body", "body", "arg", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def conj_invariant_bilinear_eq_smul_inner_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@conj_invariant_bilinear_eq_smul_inner) (Realization Scalar.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TangentInvariantForms.conj_invariant_bilinear_eq_smul_inner_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TangentInvariantForms.Scalar.univ_registration_proof
  realizationSource := none
  generated := false
  arena := .source ⟨Scalar.univArena⟩
  objectArena := .source ⟨Scalar.univArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Scalar.univArena ⟨Scalar.univ_registration_proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Scalar.signature (fun _ => Scalar.observe) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TangentInvariantForms
    definition := none
    coordinates := #[3, 4]
    readouts := #[{
      path := #["body", "body", "arg", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def conj_invariant_bilinear_iff_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@conj_invariant_bilinear_iff) (Realization Family.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.TangentInvariantForms.conj_invariant_bilinear_iff_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.TangentInvariantForms.Family.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Family.arena⟩
  objectArena := .source ⟨Family.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Family.arena ⟨Family.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Family.signature (fun _ => Family.observe) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.TangentInvariantForms
    definition := none
    coordinates := #[0, 5, 6, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "fn", "arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.TangentInvariantForms
