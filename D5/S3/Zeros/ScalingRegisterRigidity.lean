/- GID: D5/S3/Zeros/ScalingRegisterRigidity
   generality: I
   mirror-B: D5/B/S3/Zeros/ScalingRegisterRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Conditional register exclusion for realized analytic readings with equal total code. -/

import D5.S0.Conventions.TotalCode
import D5.S3.Zeros.CompletedZeta

namespace D5.S3.Zeros.ScalingRegisterRigidity

open Set
open D5.S0.Conventions.TotalCode
open D5.S3.Weil.LabeledZeta
open D5.S3.Zeros.CompletedZeta

/--
A scaling register is a nontrivial coordinatewise exponential factor whose coordinate
dependence is mediated by the ledger length. The semantic word "unrecorded" is not
represented by this predicate; ledger custody remains a narrative-layer classification.
-/
def ScalingRegister {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (R : ℂ → A → ℂ) : Prop :=
  (∃ g : ℂ → ℂ, ∀ s a, R s a = Complex.exp (g s * (length a : ℂ))) ∧
    ∃ s a, R s a ≠ 1

/-- Address-independent factors are the formal proxy for explicit global ledger factors. -/
def AddressIndependent {A : Type*} (R : ℂ → A → ℂ) : Prop :=
  ∀ s a b, R s a = R s b

/--
A nontrivial scaling register cannot be address-independent: at the zero address every
exponential register is one.
-/
theorem scaling_register_not_address_independent {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (R : ℂ → A → ℂ)
    (hRegister : ScalingRegister length R) :
    ¬ AddressIndependent R := by
  rcases hRegister with ⟨⟨g, hShape⟩, ⟨s, a, hNontrivial⟩⟩
  intro hIndependent
  have hAtZero : R s a = R s 0 := hIndependent s a 0
  have hZero : R s 0 = 1 := by simp [hShape]
  exact hNontrivial (hAtZero.trans hZero)

/-- The register predicate is inhabited: it is not an empty antecedent. -/
theorem integer_scaling_register_exists :
    ScalingRegister (Int.castAddHom ℝ)
      (fun (_ : ℂ) (a : ℤ) => Complex.exp ((Real.pi * Complex.I) * (a : ℂ))) := by
  constructor
  · refine ⟨fun _ => Real.pi * Complex.I, ?_⟩
    intro s a
    simp only [Int.coe_castAddHom]
    norm_cast
  · refine ⟨0, 1, ?_⟩
    dsimp
    norm_num [Complex.exp_pi_mul_I]

/-- Apply a tagged register to the data field while preserving rules and ledger. -/
def applyRegister {A Rules Ledger : Type*} (R : ℂ → A → ℂ)
    (X : TotalCode (A → ℂ → ℂ) Rules Ledger) :
    TotalCode (A → ℂ → ℂ) Rules Ledger :=
  { X with data := fun a s => R s a * X.data a s }

/--
`RealizesAt a X f` is the typed realization relation between a total-code object and
its analytic reading at the declared address `a`. Its second field is a model law:
the declared projection must carry `applyRegister R X` to pointwise multiplication
of the reading by `R · a`. This compatibility is part of the model structure, not an
independent bridge hypothesis claimed to follow from mathlib.
-/
structure RealizesAt {A Rules Ledger : Type*} (a : A)
    (X : TotalCode (A → ℂ → ℂ) Rules Ledger) (f : ℂ → ℂ) : Prop where
  reads : ∀ s, X.data a s = f s
  register_compatible : ∀ (R : ℂ → A → ℂ) s,
    (applyRegister R X).data a s = R s a * f s

/-- A nontrivial register changes every total code whose tagged data are nowhere zero. -/
theorem applyRegister_ne_of_nontrivial {A Rules Ledger : Type*}
    (R : ℂ → A → ℂ) (X : TotalCode (A → ℂ → ℂ) Rules Ledger)
    (hData : ∀ a s, X.data a s ≠ 0) (hNontrivial : ∃ s a, R s a ≠ 1) :
    applyRegister R X ≠ X := by
  rintro hEqual
  rcases hNontrivial with ⟨s, a, hR⟩
  have hDataEqual := congrArg TotalCode.data hEqual
  have hAtWitness := congrFun (congrFun hDataEqual a) s
  apply hR
  apply mul_right_cancel₀ (hData a s)
  simpa [applyRegister] using hAtWitness

/--
Conditional rigidity for two analytic functions realized by an object and its registered
action. Analytic uniqueness identifies the readings on `U`; the `RealizesAt` model law
identifies the second reading with the pointwise registered action; equal total code and
nowhere-zero tagged data then force the register to be pointwise one.
-/
theorem realized_same_germ_same_total_code_forces_trivial_register
    {U : Set ℂ} {f fRegister : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hfRegister : AnalyticOnNhd ℂ fRegister U)
    (hU : IsPreconnected U) {s₀ : ℂ} (hs₀ : s₀ ∈ U)
    (hSameGerm : f =ᶠ[nhds s₀] fRegister)
    {A Rules Ledger : Type*} (R : ℂ → A → ℂ)
    (X : TotalCode (A → ℂ → ℂ) Rules Ledger) (a : A)
    (hRealizes : RealizesAt a X f)
    (hRegisterRealizes : RealizesAt a (applyRegister R X) fRegister)
    (hData : ∀ a s, X.data a s ≠ 0)
    (hSameTotalCode : applyRegister R X = X) :
    Set.EqOn f fRegister U ∧
      (∀ s, fRegister s = R s a * f s) ∧ ∀ s a, R s a = 1 := by
  have hUnique : Set.EqOn f fRegister U :=
    analytic_continuation_unique hf hfRegister hU hs₀ hSameGerm
  have hRealizedAction : ∀ s, fRegister s = R s a * f s := by
    intro s
    rw [← hRegisterRealizes.reads s, hRealizes.register_compatible R s]
  refine ⟨hUnique, hRealizedAction, ?_⟩
  intro s a
  by_contra hR
  have hObjectChange : applyRegister R X ≠ X :=
    applyRegister_ne_of_nontrivial R X hData ⟨s, a, hR⟩
  have hComponentChange := no_hidden_register.2 (applyRegister R) X hObjectChange
  rw [hSameTotalCode] at hComponentChange
  rcases hComponentChange with hChanged | hChanged | hChanged
  · exact hChanged rfl
  · exact hChanged rfl
  · exact hChanged rfl

/-- A realized code-preserving continuation cannot carry a scaling register. -/
theorem realized_same_germ_same_total_code_excludes_scaling_register
    {U : Set ℂ} {f fRegister : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hfRegister : AnalyticOnNhd ℂ fRegister U)
    (hU : IsPreconnected U) {s₀ : ℂ} (hs₀ : s₀ ∈ U)
    (hSameGerm : f =ᶠ[nhds s₀] fRegister)
    {A Rules Ledger : Type*} [AddMonoid A] (length : LedgerLength A)
    (R : ℂ → A → ℂ) (X : TotalCode (A → ℂ → ℂ) Rules Ledger) (a : A)
    (hRealizes : RealizesAt a X f)
    (hRegisterRealizes : RealizesAt a (applyRegister R X) fRegister)
    (hData : ∀ a s, X.data a s ≠ 0)
    (hSameTotalCode : applyRegister R X = X) :
    ¬ ScalingRegister length R := by
  intro hScaling
  obtain ⟨_, _, hTrivial⟩ :=
    realized_same_germ_same_total_code_forces_trivial_register
      hf hfRegister hU hs₀ hSameGerm R X a hRealizes hRegisterRealizes hData hSameTotalCode
  rcases hScaling.2 with ⟨s, a, hNontrivial⟩
  exact hNontrivial (hTrivial s a)

end D5.S3.Zeros.ScalingRegisterRigidity
