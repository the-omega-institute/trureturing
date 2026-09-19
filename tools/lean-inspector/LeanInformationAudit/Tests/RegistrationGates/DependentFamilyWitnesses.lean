import LeanInformationAudit.Tests.RegistrationGates.DependentFamilyOriginal
import LeanInformationAudit.RegistrationWitnesses
open MeasureTheory Finset
open scoped BigOperators ENNReal
noncomputable section

namespace D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
universe u v

abbrev Readout {J : Type*} {Z : ℕ → Type*} (N : ℕ) :=
  (J × History Z N) → History Z N

def readoutSigma {J : Type*} {Z : ℕ → Type*} [Fintype J] [∀ n, Fintype (Z n)]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    [∀ n, MeasurableSpace (Z n)] [∀ n, MeasurableSingletonClass (Z n)]
    {N t : ℕ} (ρ : Readout (J := J) (Z := Z) N) (ht : t ≤ N) :
    MeasurableSpace (J × History Z N) :=
  MeasurableSpace.comap (fun ω => readPrefix ht (ρ ω)) inferInstance

def Law {J : Type*} {Z : ℕ → Type*} [Fintype J] [∀ n, Fintype (Z n)]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    [∀ n, MeasurableSpace (Z n)] [∀ n, MeasurableSingletonClass (Z n)]
    (N : ℕ)
    (ρ : Readout (J := J) (Z := Z) N)
    (ν : J → ℝ) (hν : (∀ j, 0 ≤ ν j) ∧ ∑ j, ν j = 1)
    (K : (n : ℕ) → J → History Z n → Z n → ℝ)
    (hK : ∀ n < N, (∀ j h z, 0 ≤ K n j h z) ∧ ∀ j h, ∑ z, K n j h z = 1) : Prop :=
  IsProbabilityMeasure (historyLaw ν K N) ∧
    (∀ t (ht : t ≤ N) (f : J → History Z t → ℝ),
      (∫ ω, f ω.1 (readPrefix ht (ρ ω)) ∂historyLaw ν K N) =
        ∑ j, ∑ h, ν j * likelihood K t j h * f j h) ∧
    (∀ t (ht : t < N) (f : History Z (t+1) → ℝ),
      (historyLaw ν K N)[(fun ω => f (readPrefix (Nat.succ_le_of_lt ht) (ρ ω))) |
          readoutSigma ρ (Nat.le_of_lt ht)] =ᵐ[historyLaw ν K N]
      fun ω => ∑ z, historyMass ν K (t+1)
          (Fin.snoc (readPrefix (Nat.le_of_lt ht) (ρ ω)) z) /
          historyMass ν K t (readPrefix (Nat.le_of_lt ht) (ρ ω)) *
          f (Fin.snoc (readPrefix (Nat.le_of_lt ht) (ρ ω)) z))

def identityReadout {J : Type*} {Z : ℕ → Type*} {N : ℕ} : Readout (J := J) (Z := Z) N :=
  fun ω => ω.2

abbrev Family := ∀ (J : Type u) (Z : ℕ → Type v) (N : ℕ), Readout (J := J) (Z := Z) N

def identityFamily : Family.{u,v} := fun _ _ _ ω => ω.2

def FullLaw (ρ : Family.{u,v}) : Prop :=
  ∀ {J : Type u} {Z : ℕ → Type v} [Fintype J] [∀ n, Fintype (Z n)]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    [∀ n, MeasurableSpace (Z n)] [∀ n, MeasurableSingletonClass (Z n)]
    (ν : J → ℝ) (hν : (∀ j, 0 ≤ ν j) ∧ ∑ j, ν j = 1)
    (K : (n : ℕ) → J → History Z n → Z n → ℝ) (N : ℕ)
    (hK : ∀ n < N, (∀ j h z, 0 ≤ K n j h z) ∧ ∀ j h, ∑ z, K n j h z = 1),
    Law N (ρ J Z N) ν hν K hK

theorem fullLaw_identity : FullLaw identityFamily.{u,v} :=
  @history_law_conditional_expectation.{u,v}

abbrev Fiber := (J : Type u) × (Z : (ℕ → Type v)) × ℕ
abbrev FiberReadout (x : Fiber.{u,v}) := Readout (J := x.1) (Z := x.2.1) x.2.2
abbrev TargetJ := ULift.{u} Unit
abbrev TargetZ (_ : ℕ) := ULift.{v} Bool

def targetFiber : Fiber.{u,v} := ⟨TargetJ, TargetZ, 1⟩
def trueTargetReadout : FiberReadout targetFiber.{u,v} := fun _ _ => ⟨true⟩

def badFiber : (x : Fiber.{u,v}) → FiberReadout x := by
  classical
  exact Function.update (fun x ω => ω.2) targetFiber trueTargetReadout

def badFamily : Family.{u,v} := fun J Z N => badFiber ⟨J, Z, N⟩

theorem badFamily_target : badFamily TargetJ.{u} TargetZ.{v} 1 = trueTargetReadout := by
  classical
  unfold badFamily badFiber
  exact Function.update_self targetFiber trueTargetReadout (fun x ω => ω.2)

def targetNu : TargetJ.{u} → ℝ := fun _ => 1

def targetK : (n : ℕ) → TargetJ.{u} → History TargetZ.{v} n → TargetZ.{v} n → ℝ :=
  fun _ _ _ z => if z.down = false then 1 else 0

def targetF : TargetJ.{u} → History TargetZ.{v} 1 → ℝ :=
  fun _ h => if (h 0).down = true then 1 else 0

theorem target_hnu : (∀ j : TargetJ.{u}, 0 ≤ targetNu j) ∧ ∑ j, targetNu j = 1 := by
  simp [targetNu]

theorem target_hK : ∀ n < 1, (∀ j h z, 0 ≤ targetK.{u,v} n j h z) ∧
    ∀ j h, ∑ z, targetK n j h z = 1 := by
  intro n hn
  constructor
  · intro j h z
    cases z with | up b => cases b <;> norm_num [targetK]
  · intro j h
    change (∑ z : ULift Bool, if z.down = false then (1 : ℝ) else 0) = 1
    rw [← (Equiv.ulift : ULift Bool ≃ Bool).symm.sum_comp]
    simp

theorem bad_integral_one :
    (∫ ω : TargetJ.{u} × History TargetZ.{v} 1,
      targetF ω.1 (readPrefix (show 1 ≤ 1 from le_rfl) (trueTargetReadout ω))
      ∂historyLaw targetNu targetK 1) = 1 := by
  letI : IsProbabilityMeasure (historyLaw targetNu.{u} targetK.{u,v} 1) :=
    (history_law_conditional_expectation targetNu target_hnu targetK 1 target_hK).1
  change (∫ _ : TargetJ × History TargetZ 1, (1 : ℝ) ∂historyLaw targetNu targetK 1) = 1
  simp

theorem target_sum_zero :
    (∑ j : TargetJ.{u}, ∑ h : History TargetZ.{v} 1,
      targetNu j * likelihood targetK 1 j h * targetF j h) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro h _
  have hz : Fin.last 0 = (0 : Fin 1) := rfl
  simp only [likelihood, one_mul, hz, targetK, targetF, targetNu]
  cases hb : (h 0).down <;> simp [hb]

theorem bad_not_law : ¬ FullLaw badFamily.{u,v} := by
  intro h
  have e := (h targetNu target_hnu targetK 1 target_hK).2.1 1 le_rfl targetF
  rw [badFamily_target] at e
  have bad : (1 : ℝ) = 0 := bad_integral_one.symm.trans (e.trans target_sum_zero)
  exact one_ne_zero bad

theorem global_variation : ∃ ρ ρ' : Family.{u,v}, FullLaw ρ ∧ ¬FullLaw ρ' :=
  ⟨identityFamily, badFamily, fullLaw_identity, bad_not_law⟩

theorem history_zero_subsingleton (J : Type u) (Z : ℕ → Type v)
    (ρ ρ' : Readout (J := J) (Z := Z) 0) : ρ = ρ' := by
  funext ω i
  exact Fin.elim0 i

theorem zero_no_variation (J : Type u) (Z : ℕ → Type v)
    (L : Readout (J := J) (Z := Z) 0 → Prop) :
    ¬ ∃ ρ ρ', L ρ ∧ ¬ L ρ' := by
  rintro ⟨ρ, ρ', hp, hn⟩
  exact hn ((history_zero_subsingleton J Z ρ ρ') ▸ hp)

#print axioms fullLaw_identity
#print axioms bad_not_law
#print axioms global_variation
#print axioms zero_no_variation
end D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation

namespace D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
universe u v

/-- The proposed sensitivity quantifies over complete families, with one role and no anchors. -/
def SoleRoleSensitivity : Prop :=
  ∀ i : Unit, ∃ r r' : Unit → Family.{u,v},
    (∀ j, j ≠ i → r j = r' j) ∧
    (FullLaw (r ()) ↔ ¬ FullLaw (r' ()))

theorem sole_role_sensitive : SoleRoleSensitivity.{u,v} := by
  intro i
  refine ⟨fun _ => identityFamily, fun _ => badFamily, ?_, ?_⟩
  · intro j h
    exact False.elim (h (Subsingleton.elim j i))
  · exact ⟨fun _ => bad_not_law, fun _ => fullLaw_identity⟩

theorem badFamily_elsewhere (x : Fiber.{u,v}) (h : x ≠ targetFiber) :
    badFiber x = (fun ω => ω.2) := by
  classical
  exact Function.update_of_ne h trueTargetReadout (fun x ω => ω.2)

theorem every_zero_readout_law {J : Type u} {Z : ℕ → Type v}
    [Fintype J] [∀ n, Fintype (Z n)]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    [∀ n, MeasurableSpace (Z n)] [∀ n, MeasurableSingletonClass (Z n)]
    (ρ : Readout (J := J) (Z := Z) 0)
    (ν : J → ℝ) (hν : (∀ j, 0 ≤ ν j) ∧ ∑ j, ν j = 1)
    (K : (n : ℕ) → J → History Z n → Z n → ℝ)
    (hK : ∀ n < 0, (∀ j h z, 0 ≤ K n j h z) ∧ ∀ j h, ∑ z, K n j h z = 1) :
    Law 0 ρ ν hν K hK := by
  rw [history_zero_subsingleton J Z ρ identityReadout]
  exact history_law_conditional_expectation ν hν K 0 hK


end D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
