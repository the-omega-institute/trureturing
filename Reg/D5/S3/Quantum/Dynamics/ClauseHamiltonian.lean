import D5.S3.Quantum.Dynamics.ClauseHamiltonian
import Reg.Support.BoundedRunSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Reg.D5.S3.Quantum.Dynamics.ClauseHamiltonian

open _root_.PredictiveThermodynamic.Physical
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open scoped Matrix Kronecker
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit

def observedCount (r : PrimitiveRealization (cutSignature Bool Bool))
    {n : Nat} (F : Formula n) : Nat := by
  classical
  let readout : Bool → Bool := r.readout ()
  exact (Finset.univ.filter (fun a : Assignment n =>
    readout ((standardFormula F).eval a) = true)).card

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ {n : Nat} (F : Formula n),
    (fullPartition F =
        3 * (partitionNumerator F : Complex) / 2 ^ ((n + 1) * F.length + 1) ∧
      Int.floor ((2 / 3 : Real) * (fullPartition F).re) = (observedCount r F : Int)) ∧
    (hiddenHamiltonian F).IsHermitian ∧ (fullHamiltonian F).IsHermitian ∧
    (∀ c ∈ F, (clauseProjector c).IsHermitian ∧
      clauseProjector c * clauseProjector c = clauseProjector c ∧
      ∃ s : Finset (Fin n), s.card ≤ c.length ∧
        ∀ a b : Assignment n, (∀ i ∈ s, a i = b i) →
          clauseProjector c a a = clauseProjector c b b) ∧
    ((Fintype.card (Assignment n) : Complex)⁻¹ •
        partialTraceRight (fullHamiltonian F) -
      (Matrix.trace (fullHamiltonian F) /
        (2 * (Fintype.card (Assignment n) : Complex))) • (1 : Matrix Bool Bool Complex) =
      visibleProjector - (1 / 2 : Complex) • (1 : Matrix Bool Bool Complex)) ∧
    (1 / 2 : Complex) • partialTraceLeft (fullHamiltonian F) =
      hiddenHamiltonian F + (1 / 2 : Complex) •
        (1 : Matrix (Assignment n) (Assignment n) Complex) ∧
    fullHamiltonian F =
      (visibleProjector - (1 / 2 : Complex) • (1 : Matrix Bool Bool Complex)) ⊗ₖ
        (1 : Matrix (Assignment n) (Assignment n) Complex) +
      (1 : Matrix Bool Bool Complex) ⊗ₖ
        (hiddenHamiltonian F + (1 / 2 : Complex) •
          (1 : Matrix (Assignment n) (Assignment n) Complex)) ∧
    (∀ M : Matrix Bool Bool Complex,
      fullHamiltonian F * (M ⊗ₖ (1 : Matrix (Assignment n) (Assignment n) Complex)) -
        (M ⊗ₖ (1 : Matrix (Assignment n) (Assignment n) Complex)) * fullHamiltonian F =
        (visibleProjector * M - M * visibleProjector) ⊗ₖ
          (1 : Matrix (Assignment n) (Assignment n) Complex)) ∧
    (∀ c d : Std.Sat.CNF.Clause (Fin n),
      clauseProjector c * clauseProjector d = clauseProjector d * clauseProjector c) ∧
    clauseProjector (n := n) [] = 1 ∧
    (∀ M : Matrix Bool Bool Complex,
      let C := fullHamiltonian F * (M ⊗ₖ (1 : Matrix (Assignment n) (Assignment n) Complex)) -
        (M ⊗ₖ (1 : Matrix (Assignment n) (Assignment n) Complex)) * fullHamiltonian F
      C - ((Fintype.card (Assignment n) : Complex)⁻¹ • partialTraceRight C) ⊗ₖ
        (1 : Matrix (Assignment n) (Assignment n) Complex) = 0) ∧
    (∀ (t : Real) (rho : Matrix (Bool × Assignment n) (Bool × Assignment n) Complex),
      let U := NormedSpace.exp ((-Complex.I * (t : Complex)) • fullHamiltonian F)
      let U_A := NormedSpace.exp ((-Complex.I * (t : Complex)) •
        (visibleProjector - (1 / 2 : Complex) • (1 : Matrix Bool Bool Complex)))
      partialTraceRight (U * rho * star U) =
        U_A * partialTraceRight rho * star U_A) ∧
    (let beta := Real.log 2
     let X := CStarMatrix.ofMatrix (-(beta : Complex) • fullHamiltonian F)
     let A := CStarMatrix.ofMatrix (-(beta : Complex) • visibleProjector)
     let B := CStarMatrix.ofMatrix (-(beta : Complex) • hiddenHamiltonian F)
     let Ac := CStarMatrix.ofMatrix (-(beta : Complex) •
       (visibleProjector - (1 / 2 : Complex) • (1 : Matrix Bool Bool Complex)))
     let Bc := CStarMatrix.ofMatrix (-(beta : Complex) •
       (hiddenHamiltonian F + (1 / 2 : Complex) •
         (1 : Matrix (Assignment n) (Assignment n) Complex)))
     ∃ hX : IsSelfAdjoint X, ∃ hA : IsSelfAdjoint A, ∃ hB : IsSelfAdjoint B,
     ∃ hAc : IsSelfAdjoint Ac, ∃ hBc : IsSelfAdjoint Bc,
       gibbsState X hX = productState (gibbsState Ac hAc) (gibbsState B hB) ∧
       gibbsState Ac hAc = gibbsState A hA ∧
       gibbsState Bc hBc = gibbsState B hB ∧
       partialTraceLeft (CStarMatrix.ofMatrix.symm (gibbsState X hX).1) =
         CStarMatrix.ofMatrix.symm (gibbsState B hB).1 ∧
       (n = 0 → CStarMatrix.ofMatrix.symm (gibbsState B hB).1 = 1) ∧
       ∀ rho : DensityState Bool,
         SupportContained rho (gibbsState Ac hAc) ∧
         SupportContained (productState rho (gibbsState B hB)) (gibbsState X hX) ∧
         partialTraceRight (CStarMatrix.ofMatrix.symm
           (productState rho (gibbsState B hB)).1) = CStarMatrix.ofMatrix.symm rho.1 ∧
         extendedQuantumRelativeEntropy (productState rho (gibbsState B hB))
           (gibbsState X hX) = extendedQuantumRelativeEntropy rho (gibbsState Ac hAc) ∧
         quantumRelativeEntropy (productState rho (gibbsState B hB)) (gibbsState X hX) -
           quantumRelativeEntropy rho (gibbsState Ac hAc) = 0 ∧
         extendedQuantumRelativeEntropy (productState rho (gibbsState B hB))
           (productState rho (gibbsState B hB)) = 0)

def symbols : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun b => b)

def erased : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun _ => false)

def sourceLaw : arena.Law symbols := by
  intro n F
  simpa [arena, observedCount, symbols, cutRealization, satisfyingCount] using
    clause_partition_recovery F

def erased_fails : ¬arena.Law erased := by
  intro all
  have bad := (all (n := 0) []).1.2
  have good := (clause_partition_recovery (n := 0) []).1.2
  have hn : satisfyingCount (n := 0) [] = 1 := by
    simp [satisfyingCount, standardFormula, Std.Sat.CNF.eval]
  have hz : observedCount erased (n := 0) [] = 0 := by
    simp [observedCount, erased, cutRealization]
  rw [hn] at good
  change Int.floor ((2 / 3 : Real) * (fullPartition (n := 0) []).re) =
    (observedCount erased (n := 0) [] : Int) at bad
  rw [hz] at bad
  omega

def variation : FiniteLawVariation arena := ⟨symbols, erased, sourceLaw, erased_fails⟩

def sensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i
    obtain ⟨r, r', hr, hr'⟩ := variation
    refine ⟨r, r', ?_, ?_, ⟨fun _ => hr', fun _ => hr⟩⟩
    · intro j hj; cases i; cases j; exact (hj rfl).elim
    · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i

def dependence : ∃ b b' : Bool, symbols.readout () b ≠ symbols.readout () b' :=
  ⟨false, true, by change false ≠ true; decide⟩

register_information_theorem _root_.PredictiveThermodynamic.Physical.clause_partition_recovery
  in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun b => b))
  primitives symbols.toPrimitiveBundle
  realization inline (symbols) := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => @clause_partition_recovery⟩
  variation variation sensitivity sensitivity
  escape from (Bool) escape continues (open)

end Reg.D5.S3.Quantum.Dynamics.ClauseHamiltonian
