/- GID: D5/S3/Zeros/ScalingRegisterRigidity
   generality: I
   mirror-B: D5/B/S3/Zeros/ScalingRegisterRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exclude scaling registers from code-preserving analytic continuations. -/

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
Conditional rigidity at the two formal layers represented here. Analytic continuation
uniqueness makes the two continuations equal on `U`. Independently, if applying `R` leaves
the same total code and the tagged data are nowhere zero, then `R` is pointwise one.

The second conclusion is constructive: a non-one witness would make `applyRegister R X`
different from `X`; `no_hidden_register` would expose a changed component, contradicting
the supplied total-code equality. This statement does not identify `R` with an analytic
continuation operation or internalize ledger custody, so it makes no claim beyond those two
typed layers.
-/
theorem same_germ_same_total_code_forces_trivial_register
    {U : Set ℂ} {f fRegister : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hfRegister : AnalyticOnNhd ℂ fRegister U)
    (hU : IsPreconnected U) {s₀ : ℂ} (hs₀ : s₀ ∈ U)
    (hSameGerm : f =ᶠ[nhds s₀] fRegister)
    {A Rules Ledger : Type*} (R : ℂ → A → ℂ)
    (X : TotalCode (A → ℂ → ℂ) Rules Ledger)
    (hData : ∀ a s, X.data a s ≠ 0)
    (hSameTotalCode : applyRegister R X = X) :
    Set.EqOn f fRegister U ∧ ∀ s a, R s a = 1 := by
  have hUnique : Set.EqOn f fRegister U :=
    analytic_continuation_unique hf hfRegister hU hs₀ hSameGerm
  refine ⟨hUnique, ?_⟩
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

end D5.S3.Zeros.ScalingRegisterRigidity
