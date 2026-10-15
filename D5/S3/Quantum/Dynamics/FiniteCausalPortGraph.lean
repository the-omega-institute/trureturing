/- GID: D5/S3/Quantum/Dynamics/FiniteCausalPortGraph
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/FiniteCausalPortGraph
   mirror-E: none(waiver:content-registration-pending)
   anchors: []
   utility: none
   digest: Finite causal matrix instruments have derived disjoint-port interchange and static cut semantics. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity
import D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix ComplexOrder MatrixOrder Kronecker
namespace D5.S3.Quantum.Dynamics.FiniteCausalPortGraph

/-- The state includes all ports that can interact again. Any reference is another tensor factor. -/
abbrev State (I : Type*) := Matrix I I ℂ

/-- A physical branch is an actual finite Kraus family, not a function on an abstract payload. -/
def branch {I O M : Type*} [Fintype I] [Fintype M]
    (K : M → Matrix O I ℂ) (ρ : State I) : State O :=
  ∑ m, K m * ρ * (K m)ᴴ

/-- Complete instruments have finite actual outcomes and finite unobserved Kraus labels. -/
structure Instrument (I O : Type*) [Fintype I] [DecidableEq I] [Fintype O] where
  outcomes : ℕ
  hidden : ℕ
  kraus : Fin outcomes → Fin hidden → Matrix O I ℂ
  normalized : ∑ a, ∑ μ, (kraus a μ)ᴴ * kraus a μ = 1

/-- The same genuine quantum channel as the canonical CP/TP supplier; no channel theory is duplicated. -/
noncomputable def Instrument.channel {I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (J : Instrument I O) :
    D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel I O :=
  Classical.choose (D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel
    (fun p : Fin J.outcomes × Fin J.hidden => J.kraus p.1 p.2)
    (by simpa [Fintype.sum_prod_type] using J.normalized))

private theorem branch_comp {I J O M N : Type*} [Fintype I] [Fintype J]
    [Fintype M] [Fintype N] (A : M → Matrix J I ℂ) (B : N → Matrix O J ℂ) (ρ : State I) :
    branch B (branch A ρ) =
      ∑ n, ∑ m, (B n * A m) * ρ * (B n * A m)ᴴ := by
  simp only [branch, Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- An operation on the left port keeps every right-port coordinate, including entanglement. -/
def leftBranch {I O J M : Type*} [Fintype I] [Fintype J] [DecidableEq J] [Fintype M]
    (A : M → Matrix O I ℂ) : State (I × J) → State (O × J) :=
  branch (fun m => A m ⊗ₖ (1 : Matrix J J ℂ))

/-- This spectator lift acts on the full joint matrix, not on a reduced local density. -/
def rightBranch {I J P N : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype N]
    (B : N → Matrix P J ℂ) : State (I × J) → State (I × P) :=
  branch (fun n => (1 : Matrix I I ℂ) ⊗ₖ B n)

/-- Disjoint quantum ports interchange, including arbitrary correlated spectator states.
The intermediate dimensions may differ; the identity follows from rectangular tensor multiplication. -/
theorem disjoint_port_interchange {I J O P M N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] [Fintype P] [DecidableEq P]
    [Fintype M] [Fintype N]
    (A : M → Matrix O I ℂ) (B : N → Matrix P J ℂ) (ρ : State (I × J)) :
    rightBranch B (leftBranch A ρ) = leftBranch A (rightBranch B ρ) := by
  unfold rightBranch leftBranch
  rw [branch_comp, branch_comp]
  simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  exact Finset.sum_comm

/-- A spectator extension of a normalized finite instrument is itself normalized. -/
private theorem lift_normalized {I O R : Type*} [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R] [Fintype O] (J : Instrument I O) :
    ∑ a, ∑ μ, (J.kraus a μ ⊗ₖ (1 : Matrix R R ℂ))ᴴ *
      (J.kraus a μ ⊗ₖ (1 : Matrix R R ℂ)) = 1 := by
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hh := congrArg (fun Z : State I => Z ⊗ₖ (1 : State R)) J.normalized
  ext ⟨i,r⟩ ⟨j,s⟩
  have hv := congrArg (fun Z : State (I × R) => Z (i,r) (j,s)) hh
  by_cases hij : i = j <;> by_cases hrs : r = s <;>
    simpa [Matrix.kronecker_apply, Matrix.sum_apply, Finset.sum_mul,
      Matrix.one_kronecker_one, Matrix.one_apply, Prod.mk.injEq, hij, hrs] using hv

/-- References and returning environments remain legal spectators of a canonical CPTP instrument. -/
noncomputable def Instrument.withSpectator {I O R : Type*} [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R] [Fintype O] (J : Instrument I O) : Instrument (I × R) (O × R) where
  outcomes := J.outcomes
  hidden := J.hidden
  kraus a μ := J.kraus a μ ⊗ₖ (1 : Matrix R R ℂ)
  normalized := lift_normalized J

/-- Change only the tensor coordinates of a cut. This keeps the full joint matrix. -/
def inCoordinates {Q V : Type*} (e : Q ≃ V) (ρ : State Q) : State V :=
  ρ.submatrix e.symm e.symm

private theorem inCoordinates_injective {Q V : Type*} (e : Q ≃ V) :
    Function.Injective (inCoordinates e) := by
  intro X Y h
  ext i j
  simpa [inCoordinates] using congrArg (fun Z : State V => Z (e i) (e j)) h

/-- A certificate that four actual edge maps use two disjoint typed ports.
The fields identify individual edge maps with spectator extensions. No commuting-function or
whole-path equality is supplied by the graph. -/
structure PortSquare (Q₀ Q₁ Q₂ Q₃ : Type*)
    (a₀ : State Q₀ → State Q₁) (b₀ : State Q₀ → State Q₂)
    (b₁ : State Q₁ → State Q₃) (a₂ : State Q₂ → State Q₃) where
  I : Type
  J : Type
  O : Type
  P : Type
  finiteI : Fintype I
  finiteJ : Fintype J
  finiteO : Fintype O
  finiteP : Fintype P
  decI : DecidableEq I
  decJ : DecidableEq J
  decO : DecidableEq O
  decP : DecidableEq P
  M : Type
  N : Type
  finiteM : Fintype M
  finiteN : Fintype N
  A : M → Matrix O I ℂ
  B : N → Matrix P J ℂ
  at₀ : Q₀ ≃ I × J
  at₁ : Q₁ ≃ O × J
  at₂ : Q₂ ≃ I × P
  at₃ : Q₃ ≃ O × P
  left_before : ∀ X, inCoordinates at₁ (a₀ X) =
    @leftBranch I O J M finiteI finiteJ decJ finiteM A (inCoordinates at₀ X)
  right_before : ∀ X, inCoordinates at₂ (b₀ X) =
    @rightBranch I J P N finiteI decI finiteJ finiteN B (inCoordinates at₀ X)
  right_after : ∀ X, inCoordinates at₃ (b₁ X) =
    @rightBranch O J P N finiteO decO finiteJ finiteN B (inCoordinates at₁ X)
  left_after : ∀ X, inCoordinates at₃ (a₂ X) =
    @leftBranch I O P M finiteI finiteP decP finiteM A (inCoordinates at₂ X)

private theorem PortSquare.diamond {Q₀ Q₁ Q₂ Q₃ : Type*}
    {a₀ : State Q₀ → State Q₁} {b₀ : State Q₀ → State Q₂}
    {b₁ : State Q₁ → State Q₃} {a₂ : State Q₂ → State Q₃}
    (S : PortSquare Q₀ Q₁ Q₂ Q₃ a₀ b₀ b₁ a₂) (X : State Q₀) :
    b₁ (a₀ X) = a₂ (b₀ X) := by
  letI := S.finiteI; letI := S.finiteJ; letI := S.finiteO; letI := S.finiteP
  letI := S.decI; letI := S.decJ; letI := S.decO; letI := S.decP
  letI := S.finiteM; letI := S.finiteN
  apply inCoordinates_injective S.at₃
  rw [S.right_after, S.left_before, S.left_after, S.right_before]
  exact disjoint_port_interchange S.A S.B _

open D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity
open D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport

/-- Actual records use finite alphabets at finitely many event occurrences. -/
abbrev Records {E : Type} (outcomes : E → ℕ) := ∀ e, Fin (outcomes e)

/-- A causal graph has finite typed quantum cuts and local normalized instrument data.
The local Kraus choice reads only the already observed predecessor record and its own outcome.
Every observer, memory and environment that returns later is part of a cut interface. -/
structure QuantumPortGraph (E : Type) [PartialOrder E] where
  cut : Set E → Type
  finiteCut : ∀ K, Fintype (cut K)
  decidableCut : ∀ K, DecidableEq (cut K)
  outcomes : E → ℕ
  hidden : E → ℕ
  kraus : ∀ {K : Set E} {e : E}, Enabled K e →
    (∀ d : K, Fin (outcomes d)) → Fin (outcomes e) → Fin (hidden e) →
    Matrix (cut (insert e K)) (cut K) ℂ
  normalized : ∀ {K : Set E} {e : E} (hen : Enabled K e)
    (h : ∀ d : K, Fin (outcomes d)),
    letI := finiteCut K
    letI := decidableCut K
    ∑ a, ∑ μ, (kraus hen h a μ)ᴴ * kraus hen h a μ = 1
  square : ∀ {K : Set E} {a b : E}, IsLowerSet K → K.Finite →
    ∀ (ha : Enabled K a) (hb : Enabled K b)
      (hab : Enabled (insert a K) b) (hba : Enabled (insert b K) a)
      (h : Records outcomes),
    PortSquare (cut K) (cut (insert a K)) (cut (insert b K)) (cut (insert a (insert b K)))
      (@branch (cut K) (cut (insert a K)) (Fin (hidden a)) (finiteCut K) inferInstance
        (kraus ha (fun d => h d) (h a)))
      (@branch (cut K) (cut (insert b K)) (Fin (hidden b)) (finiteCut K) inferInstance
        (kraus hb (fun d => h d) (h b)))
      (fun X => (Set.insert_comm b a K) ▸
        @branch (cut (insert a K)) (cut (insert b (insert a K))) (Fin (hidden b))
          (finiteCut _) inferInstance (kraus hab (fun d => h d) (h b)) X)
      (@branch (cut (insert b K)) (cut (insert a (insert b K))) (Fin (hidden a))
        (finiteCut _) inferInstance (kraus hba (fun d => h d) (h a)))

noncomputable def QuantumPortGraph.readout {E : Type} [PartialOrder E]
    (G : QuantumPortGraph E) (h : Records G.outcomes) : DependentReadout E where
  fibre K := State (G.cut K)
  edge := fun {K} {e} hen => @branch (G.cut K) (G.cut (insert e K)) (Fin (G.hidden e))
    (G.finiteCut K) inferInstance (G.kraus hen (fun d => h d) (h e))

/-- Quantum topological-order independence is derived from actual disjoint typed port squares. -/
theorem quantum_schedule_independence {E : Type} [PartialOrder E]
    (G : QuantumPortGraph E) (h : Records G.outcomes) {I J : Set E}
    (hI : IsLowerSet I) (hJ : IsLowerSet J) (hfin : J.Finite)
    (l m : List E) (hl : Exec I l J) (hm : Exec I m J) (X : State (G.cut I)) :
    pathMap (G.readout h) l hl X = pathMap (G.readout h) m hm X := by
  have hd : DiamondCompatible (G.readout h) := by
    intro K a b hK hf ha hb hab hba X
    have hh := (G.square hK hf ha hb hab hba h).diamond X
    have heq : insert b (insert a K) = insert a (insert b K) := Set.insert_comm b a K
    simp only [pathMap, QuantumPortGraph.readout] at *
    have back := congrArg (fun z : State (G.cut (insert a (insert b K))) =>
      Eq.rec (motive := fun (L : Set E) (_ : insert a (insert b K) = L) => State (G.cut L)) z heq.symm) hh
    have cancel (Y : State (G.cut (insert b (insert a K)))) :
        heq.symm ▸ (heq ▸ Y) = Y := by
      exact Eq.recOn (motive := fun L (hL : insert b (insert a K) = L) =>
        ∀ Y : State (G.cut (insert b (insert a K))), hL.symm ▸ (hL ▸ Y) = Y) heq
          (fun _ => rfl) Y
    rw [cancel] at back
    exact back
  exact (pathIndependent_iff_diamondCompatible _).mpr hd hI hJ hfin l m hl hm X

#print axioms disjoint_port_interchange
#print axioms quantum_schedule_independence
end D5.S3.Quantum.Dynamics.FiniteCausalPortGraph
