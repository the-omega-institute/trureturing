import Reg.Support.BinaryMachineAudit
import Mathlib.Logic.Encodable.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Countable.Basic

set_option autoImplicit false
namespace Reg.Support.BinaryLanguageAudit
open _root_.Complexity

/-- A numerical diagonal exceeds every natural-coefficient polynomial envelope. -/
def diagonalSize (n : Nat) := n + 2 * powerBound n n n + 1

theorem envelope_le_diagonal (c e : Nat) :
    powerBound c e (c + e) ≤ powerBound (c + e) (c + e) (c + e) := by
  unfold powerBound
  exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))

theorem diagonal_not_bounded : ¬ PolynomialBound diagonalSize := by
  rintro ⟨c,e,h⟩
  have hh := h (c+e)
  have hb := envelope_le_diagonal c e
  unfold diagonalSize at hh
  omega

def diagonalOutput (w : Word) : Word := List.replicate (diagonalSize w.length) true

theorem diagonal_not_polyTime : ¬ PolyTime diagonalOutput := by
  rintro ⟨M,c,e,h⟩
  let input : Word := List.replicate (c+e) false
  obtain ⟨t,out,ht,hr,ho⟩ := h input
  have hl := runInput_output_length_le M t input (true,out) hr
  change out.output.length ≤ input.length + 2*t at hl
  rw [ho] at hl
  have hn : input.length = c+e := by simp [input]
  simp only [diagonalOutput,List.length_replicate,hn] at hl
  rw [hn] at ht
  have hb := envelope_le_diagonal c e
  unfold diagonalSize at hl
  omega

-- Finite instruction tables have countably many complete machine descriptions.
deriving instance Fintype for Symbol
instance moveCountable : Countable Move := by
  let encode : Move → Nat := fun d => match d with
    | .left => 0 | .stay => 1 | .right => 2
  have h : Function.Injective encode := by
    intro x y h
    cases x <;> cases y <;> simp_all [encode]
  exact h.countable

instance instructionCountable (n : Nat) : Countable (Instruction n) := by
  let encode : Instruction n → Sum Bool (Symbol × Move × Fin n) := fun ins => match ins with
    | .halt b => .inl b
    | .step a d q => .inr (a,d,q)
  have h : Function.Injective encode := by
    intro x y h
    cases x <;> cases y <;> simp_all [encode]
  exact h.countable

instance machineCountable : Countable Machine := by
  let encode : Machine → Σ n : Nat,
      Fin (n+1) × (Fin (n+1) → Symbol → Instruction (n+1)) :=
    fun M => ⟨M.states,M.start,M.code⟩
  have hinj : Function.Injective encode := by
    intro M N h
    cases M
    cases N
    cases h
    rfl
  exact hinj.countable

noncomputable instance descriptionsEncodable : Encodable (Machine × Nat × Nat) :=
  Encodable.ofCountable _

def verifierLanguage (d : Machine × Nat × Nat) (input : Word) : Prop :=
  ∃ witness : Word, witness.length ≤ powerBound d.2.1 d.2.2 input.length ∧
    Accepts d.1 (pairWords input witness)

noncomputable def description (n : Nat) : Machine × Nat × Nat :=
  (Encodable.decode (α := Machine × Nat × Nat) n).getD (identityMachine,0,0)

noncomputable def diagonalLanguage (x : Word) : Prop :=
  ¬ verifierLanguage (description x.length) x

/-- This witness is diagonalization over all original verifier descriptions;
it makes no claim about the complexity of original CNF-SAT. -/
theorem diagonal_not_inNP : ¬ InNP diagonalLanguage := by
  classical
  rintro ⟨M,c,e,_,h⟩
  let d : Machine × Nat × Nat := (M,c,e)
  let x : Word := List.replicate (Encodable.encode d) true
  have hd : description x.length = d := by
    simp [description,x,Encodable.encodek]
  have hh := h x
  change (¬ verifierLanguage (description x.length) x ↔ verifierLanguage d x) at hh
  rw [hd] at hh
  tauto

theorem identity_polynomial : PolynomialTimeMachine identityMachine := by
  refine ⟨1,0,?_⟩
  intro input
  exact ⟨1,true,Tape.ofInput input,by simp [powerBound],rfl⟩

theorem full_inNP : InNP (fun _ => True) := by
  refine ⟨identityMachine,0,0,?_,?_⟩
  · refine ⟨1,0,?_⟩
    intro input
    exact ⟨1,true,Tape.ofInput input,by simp [powerBound],rfl⟩
  · intro input
    constructor
    · intro _
      exact ⟨[],by simp [powerBound],1,Tape.ofInput (pairWords input []),rfl⟩
    · intro _
      trivial

end Reg.Support.BinaryLanguageAudit
