import D5.S3.Quantum.Dynamics.FibonacciModFourClock
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Dynamics.FibonacciModFourClock
open _root_.D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Quantum.Dynamics.FibonacciModFourClock

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ Delta => clock Delta) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ Delta => clock Delta + 1) (fun e => nomatch e)

def formula (Delta : ℝ) : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  let x := Complex.exp (-Complex.I * (Delta : ℂ))
  let Pplus := (1 / 2 : ℂ) • (1 + U ^ 3)
  let Pminus := (1 / 2 : ℂ) • (1 - U ^ 3)
  let A := (1 + 2 * x ^ 3) / 3
  let B := x * (2 + x ^ 3) / 3
  let C := (1 - x ^ 3) / 3
  A • Pplus + B • Pminus +
    C • (U * (Pplus + x • Pminus)) +
    C • (U ^ 2 * (Pplus - x • Pminus))

def arena : Arena where
  signature := signature
  Law R := ∀ Delta : ℝ, U ^ 6 = 1 ∧ R.readout () () Delta = formula Delta

theorem actual_law : arena.Law actual := by
  intro Delta
  exact fixed_clock_formula Delta

theorem rejected_law : ¬ arena.Law rejected := by
  intro hbad
  have h := (hbad 0).2
  change clock 0 + 1 = formula 0 at h
  have ha : clock 0 = formula 0 := (fixed_clock_formula 0).2
  rw [← ha] at h
  have hone : (1 : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) = 0 :=
    add_eq_left.mp h
  exact one_ne_zero hone

theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro k hki
    cases i
    cases k
    exact (hki rfl).elim
  · intro i
    exact nomatch i

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, Real.pi, ?_⟩
  change clock 0 ≠ clock Real.pi
  have hzero : clock 0 = 1 := by simp [clock, hamiltonianPropagator]
  have hphase : Complex.exp (-Complex.I * (Real.pi : ℂ)) = -1 := by
    rw [neg_mul, Complex.exp_neg]
    rw [mul_comm Complex.I, Complex.exp_pi_mul_I]
    norm_num
  have hpi : clock Real.pi = (-1 / 3 : ℂ) • 1 +
      (2 / 3 : ℂ) • (U ^ 2 + U ^ 4) := by
    have h := (fixed_clock_formula Real.pi).2
    dsimp only at h
    rw [hphase] at h
    convert h using 1
    norm_num [mul_add, mul_sub, mul_smul_comm, smul_add, smul_sub,
      smul_smul, ← pow_succ', ← pow_add]
    module
  let z : Fin 4 × Fin 4 := (2, 0)
  have hentry (k : ℕ) (hne : (digitPermutation ^ k) z ≠ z) : (U ^ k) z z = 0 := by
    rw [U, ← map_pow]
    simp only [Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]
    simp [Equiv.Perm.inv_def, Equiv.eq_symm_apply, hne]
  have htwo : (digitPermutation ^ 2) z ≠ z := by decide
  have hfour : (digitPermutation ^ 4) z ≠ z := by decide
  intro heq
  rw [hzero, hpi] at heq
  have hz := congrArg (fun Q => Q z z) heq
  norm_num [Matrix.add_apply, Matrix.smul_apply, hentry 2 htwo, hentry 4 hfour] at hz

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

register_information_theorem fixed_clock_formula in arena
  readout via (realize signature (fun _ _ Delta => clock Delta) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Dynamics.FibonacciModFourClock
    coordinates := #[]
    readouts := #[{ path := #["body", "arg", "fn", "arg"], stateBinder := 0 }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity
#print axioms dependence

end Reg.D5.S3.Quantum.Dynamics.FibonacciModFourClock
