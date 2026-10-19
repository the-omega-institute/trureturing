import Reg.Support.FibonacciQuadratic
import Reg.Support.FibonacciFactorCompletion.CountBoundsReadouts
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EvenLengthAsymptotics
import Mathlib.Logic.Encodable.Basic
import Reg.Support.FibonacciConsensusUniverse
import Reg.Support.SingleDependentReadout
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.Support.FibonacciOperations.Witness
noncomputable section
universe u
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion

abbrev budget_witness :=
  Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ActualCountRateBridge.ExactOriginal39.budget_witness

theorem budget_bounds (b : ℝ)
    (lower : lam - g^2 * chi^2 * hSide .high < b)
    (upper : b < lam - g^2 * chi^2 * (aSide .high / (1-rho*chi^2))) :
    0 ≤ b ∧ b < lam := by
  have bounds := Reg.Support.FibonacciQuadratic.t_bounds
  have gp : 0 < g := TailGeometry.tail_arithmetic.2.2.2.1
  have gq : g < 1 / 4 := by dsimp [g]; linarith [bounds.2]
  have cp : 0 < chi := pow_pos gp 20
  have coef : 0 < g^2 * chi^2 := mul_pos (sq_pos_of_pos gp) (sq_pos_of_pos cp)
  have rp : 0 < rho := pow_pos gp 6
  have r1 : rho < 1 := pow_lt_one₀ gp.le (by linarith : g < 1) (by decide)
  have c1 : chi < 1 := pow_lt_one₀ gp.le (by linarith : g < 1) (by decide)
  have c2 : chi^2 < 1 := pow_lt_one₀ cp.le c1 (by decide)
  have den : 0 < 1-rho*chi^2 := by nlinarith
  have hp : 0 < hSide .high := by dsimp [hSide]; linarith
  have hs : hSide .high < 1 := by dsimp [hSide]; linarith
  have ap : 0 < aSide .high := mul_pos (sub_pos.mpr r1) hp
  have cost : 0 < g^2 * chi^2 * (aSide .high / (1-rho*chi^2)) :=
    mul_pos coef (div_pos ap den)
  have cp1 : chi^2 < 1 := c2
  have rhoSmall : rho < 1 / 4096 := by
    have hh := pow_lt_pow_left₀ gq gp.le (by decide : (6 : ℕ) ≠ 0)
    norm_num [rho] at hh ⊢
    exact hh
  have scaleSmall : g^2 * chi^2 < rho := by
    have p36 : g^36 < 1 := pow_lt_one₀ gp.le (by linarith : g < 1) (by decide)
    calc
      g^2 * chi^2 = g^6 * g^36 := by dsimp [chi]; ring
      _ < g^6 * 1 := mul_lt_mul_of_pos_left p36 (pow_pos gp 6)
      _ = rho := by simp [rho]
  have small : g^2 * chi^2 * hSide .high < 1 / 4096 := by
    have zz := mul_lt_mul_of_pos_left hs coef
    exact (by simpa using zz : g^2 * chi^2 * hSide .high < g^2 * chi^2).trans
      (scaleSmall.trans rhoSmall)
  have lamLower : 3 / 80 < lam := by dsimp [lam, T2]; linarith [bounds.2]
  constructor <;> linarith

local instance : Encodable Reg.Support.FibonacciConsensusUniverse.Configuration.{u} :=
  Encodable.ofCountable _

def encoding (c : Reg.Support.FibonacciConsensusUniverse.Configuration.{u}) : List Bool :=
  List.replicate (Encodable.encode c) true

theorem encoding_injective : Function.Injective encoding.{u} := by
  intro c d eq
  apply Encodable.encode_injective
  simpa [encoding] using congrArg List.length eq

/-- The full reached set at each finite horizon has a finite code-length bound. -/
theorem finite_peak (o : Ownership) (b : ℝ) (bp : 0 ≤ b) (H : ℕ) :
    ∃ B : ℕ, Peak (Reg.Support.FibonacciConsensusUniverse.action.{u} b)
      Reg.Support.FibonacciConsensusUniverse.initial (OperationRecord o b .closed)
      encoding H ≤ (B : WithTop ℕ) := by
  classical
  let X := Σ n : Fin (H+1), Fin n.val → Color
  let stateOf : X → Reg.Support.FibonacciConsensusUniverse.Configuration.{u} := fun x =>
    ⟨(List.ofFn x.2, (Reg.Support.FibonacciConsensus.output b (List.ofFn x.2)).length)⟩
  let B := Finset.univ.sup (fun x : X => (encoding (stateOf x)).length)
  refine ⟨B, ?_⟩
  apply iSup_le
  intro c
  apply iSup_le
  rintro ⟨alpha, r, t, record, execution, acquired, equal⟩
  have lowered := Reg.Support.DecoderConfigurationTransport.run_inverse
    Reg.Support.FibonacciConsensusUniverse.equivalence
    (Reg.Support.FibonacciConsensus.action b) (full r) execution
  have inv := (Reg.Support.FibonacciConsensus.run_invariant o b bp alpha r record
    (Reg.Support.DecoderConfigurationTransport.frame
      Reg.Support.FibonacciConsensusUniverse.equivalence.symm t) lowered).1
  let x : X := ⟨⟨t.acquired, by omega⟩, fun i => r i.val⟩
  have he : c = stateOf x := by
    rw [← equal]
    apply ULift.ext
    exact inv
  rw [he]
  exact_mod_cast (Finset.le_sup (f := fun x : X => (encoding (stateOf x)).length)
    (Finset.mem_univ x))
end
end Reg.Support.FibonacciOperations.Witness
