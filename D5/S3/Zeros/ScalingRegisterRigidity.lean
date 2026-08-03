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
A nontrivial scaling register cannot be address-independent. The nontrivial-length
hypothesis records that the supplied ledger has a genuine coordinate direction; the proof
also uses the zero address, where every exponential register is definitionally one.
-/
theorem scaling_register_not_address_independent {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (R : ℂ → A → ℂ)
    (hLength : ∃ a, length a ≠ 0) (hRegister : ScalingRegister length R) :
    ¬ AddressIndependent R := by
  rcases hLength with ⟨a₀, ha₀⟩
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

/-- Both independent kernel arguments excluding a scaling register. -/
structure NoScalingRegister {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (R : ℂ → A → ℂ) : Prop where
  analyticLayer : ¬ ScalingRegister length R
  totalCodeLayer : ¬ ScalingRegister length R

/--
The C3a conclusion, at the formal analytic and definitional scope available in this repository.
The same-germ premise is consumed by analytic continuation uniqueness. The same-total-code
premise is consumed through `no_hidden_register`, whose second clause exposes a changed
data, rules, or ledger component. A "real addition" is represented by the two explicit
bridge hypotheses saying that a scaling register changes both the continued function and
the represented object.

Honest scope declaration: Lean does not internalize the institutional predicates
"unrecorded" or "explicit ledger", nor derive the two bridge hypotheses from complex
analysis. Accordingly this theorem is closed only at the analytic layer plus the
definitional `TotalCode` reading of criterion 7.2; it does not claim an ontological proof
beyond those typed inputs.
-/
theorem same_germ_same_total_code_has_no_scaling_register
    {U : Set ℂ} {f fRegister : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hfRegister : AnalyticOnNhd ℂ fRegister U)
    (hU : IsPreconnected U) {s₀ : ℂ} (hs₀ : s₀ ∈ U)
    (hSameGerm : f =ᶠ[nhds s₀] fRegister)
    {Data Rules Ledger : Type*}
    (update : TotalCode Data Rules Ledger → TotalCode Data Rules Ledger)
    (X : TotalCode Data Rules Ledger) (hSameTotalCode : update X = X)
    {A : Type*} [AddMonoid A] (length : LedgerLength A) (R : ℂ → A → ℂ)
    (hChangesContinuation : ScalingRegister length R →
      ∃ s ∈ U, fRegister s ≠ f s)
    (hChangesObject : ScalingRegister length R → update X ≠ X) :
    NoScalingRegister length R := by
  have hUnique : Set.EqOn f fRegister U :=
    analytic_continuation_unique hf hfRegister hU hs₀ hSameGerm
  constructor
  · intro hRegister
    rcases hChangesContinuation hRegister with ⟨s, hs, hChange⟩
    exact hChange (hUnique hs).symm
  · intro hRegister
    have hObjectChange : update X ≠ X := hChangesObject hRegister
    have hComponentChange :=
      no_hidden_register.2 update X hObjectChange
    rw [hSameTotalCode] at hComponentChange
    rcases hComponentChange with hData | hRules | hLedger
    · exact hData rfl
    · exact hRules rfl
    · exact hLedger rfl

/-- A certificate from 23.4 directly rules out every nontrivial scaling-register witness. -/
theorem no_scaling_register_rejects_witness {A : Type*} [AddMonoid A]
    {length : LedgerLength A} {R : ℂ → A → ℂ}
    (hNoRegister : NoScalingRegister length R)
    (g : ℂ → ℂ) (hShape : ∀ s a, R s a = Complex.exp (g s * (length a : ℂ)))
    (s : ℂ) (a : A) (hNontrivial : R s a ≠ 1) : False := by
  exact hNoRegister.analyticLayer ⟨⟨g, hShape⟩, ⟨s, a, hNontrivial⟩⟩

end D5.S3.Zeros.ScalingRegisterRigidity
