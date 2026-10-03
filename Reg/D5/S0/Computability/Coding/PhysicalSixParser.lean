import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.Coding.PhysicalSixParser
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S0.Computability.Coding.PhysicalSixParser

open _root_.D5.S0.Computability.Coding PhysicalSixParser
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open Reg.Support.PhysicalParserCells LeanInformationAudit

/- The Law retains every source premise, conclusion and prefix bound. Its only
intervention replaces the specified Boolean cell observations. At the identity
readout it is the complete original statement; erasure contradicts a required
true cell and the retained frame. The further residual remains open. -/

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ (m : Track → ℤ → Bool) (h : Track → ℤ) (W B k : ℕ)
    (hhome : m (7, false) 0 = false ∧ m (7, true) 0 = true)
    (hmarks : ∀ j : ℕ, 0 < j → j ≤ W → m (7, false) j = true ∧ m (7, true) j = true)
    (hk : k ≤ W) (hB : k ≤ B),
    run ⟨.sourceRewind 0, rewindHeads h k k k, m⟩ (5 * k + 2) =
        observeCells r ⟨.pad 0 0, rewindHeads h 0 0 0, m⟩ ∧
      ∀ n ≤ 5 * k + 2, RewindFrame m h B
        (run ⟨.sourceRewind 0, rewindHeads h k k k, m⟩ n)

def cellRealization : PrimitiveRealization (cutSignature Bool Bool) :=
  @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)

def erased_fails : ¬ arena.Law erased := by
  intro bad
  obtain ⟨result, frame⟩ := bad (fun t _ => t.2) (fun _ => 0) 0 0 0
    ⟨rfl, rfl⟩ (by intro j hj hj0; omega) (by omega) (by omega)
  obtain ⟨a, b, c, _, _, _, _, _, _, cells⟩ := frame 2 (by omega)
  have contradiction := congrFun (congrFun cells (0, true)) 0
  rw [result] at contradiction
  exact Bool.false_ne_true contradiction

def cellVariation : FiniteLawVariation arena :=
  ⟨cellRealization, erased, coupled_source_rewind, erased_fails⟩

def cellSensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i
    obtain ⟨r, r', hr, hr'⟩ := cellVariation
    refine ⟨r, r', ?_, ?_, ⟨fun _ => hr', fun _ => hr⟩⟩
    · intro j hj; cases i; cases j; exact (hj rfl).elim
    · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i


/-- The actual observation distinguishes the two physical Boolean cell values. -/
def dependence : ∃ b b' : Bool, cellRealization.readout () b ≠ cellRealization.readout () b' :=
  ⟨false, true, Bool.false_ne_true⟩

private theorem _root_.D5.S0.Computability.Coding.PhysicalSixParser.coupled_source_rewind.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} Reg.D5.S0.Computability.Coding.PhysicalSixParser.arena (∀ (m : D5.S0.Computability.Coding.PhysicalSixParser.Track → Int → Bool) (h : D5.S0.Computability.Coding.PhysicalSixParser.Track → Int) (W B k : Nat) (hhome : And (@Eq.{1} Bool (m (@Prod.mk.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) Bool (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) (nat_lit 7) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (nat_lit 7))) Bool.false) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) Bool.false) (@Eq.{1} Bool (m (@Prod.mk.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) Bool (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) (nat_lit 7) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (nat_lit 7))) Bool.true) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) Bool.true)) (hmarks : ∀ (j : Nat), @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) j → @LE.le.{0} Nat instLENat j W → And (@Eq.{1} Bool (m (@Prod.mk.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) Bool (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) (nat_lit 7) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (nat_lit 7))) Bool.false) (@Nat.cast.{0} Int instNatCastInt j)) Bool.true) (@Eq.{1} Bool (m (@Prod.mk.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) Bool (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) (nat_lit 7) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (nat_lit 7))) Bool.true) (@Nat.cast.{0} Int instNatCastInt j)) Bool.true)) (hk : @LE.le.{0} Nat instLENat k W) (hB : @LE.le.{0} Nat instLENat k B), And (@Eq.{1} D5.S0.Computability.Coding.PhysicalSixParser.Configuration (D5.S0.Computability.Coding.PhysicalSixParser.run (D5.S0.Computability.Coding.PhysicalSixParser.Configuration.mk (D5.S0.Computability.Coding.PhysicalSixParser.Control.sourceRewind (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 0) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (nat_lit 0)))) (D5.S0.Computability.Coding.PhysicalSixParser.rewindHeads h (@Nat.cast.{0} Int instNatCastInt k) (@Nat.cast.{0} Int instNatCastInt k) (@Nat.cast.{0} Int instNatCastInt k)) m) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) k) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (D5.S0.Computability.Coding.PhysicalSixParser.Configuration.mk (D5.S0.Computability.Coding.PhysicalSixParser.Control.pad (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (nat_lit 0) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 0))) (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))) (nat_lit 0) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))) (nat_lit 0)))) (D5.S0.Computability.Coding.PhysicalSixParser.rewindHeads h (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) m)) (∀ (n : Nat), @LE.le.{0} Nat instLENat n (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) k) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) → D5.S0.Computability.Coding.PhysicalSixParser.RewindFrame m h B (D5.S0.Computability.Coding.PhysicalSixParser.run (D5.S0.Computability.Coding.PhysicalSixParser.Configuration.mk (D5.S0.Computability.Coding.PhysicalSixParser.Control.sourceRewind (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) (nat_lit 0) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (nat_lit 0)))) (D5.S0.Computability.Coding.PhysicalSixParser.rewindHeads h (@Nat.cast.{0} Int instNatCastInt k) (@Nat.cast.{0} Int instNatCastInt k) (@Nat.cast.{0} Int instNatCastInt k)) m) n))) Reg.D5.S0.Computability.Coding.PhysicalSixParser.cellRealization := by exact ⟨Iff.rfl⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S0.Computability.Coding.PhysicalSixParser.coupled_source_rewind) (type_of% (arena)) (type_of% (arena)) (type_of% (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))) (type_of% (cellVariation)) (type_of% (cellSensitivity)) (type_of% (Bool)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "Coding") "PhysicalSixParser") 0) "D5") "S0") "Computability") "Coding") "PhysicalSixParser") "coupled_source_rewind") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "Coding") "PhysicalSixParser") 0) "D5") "S0") "Computability") "Coding") "PhysicalSixParser") "coupled_source_rewind") "__primitive_realization"),
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (arena) ((cellRealization)) (cellRealization.toPrimitiveBundle) ⟨(D5.S0.Computability.Coding.PhysicalSixParser.coupled_source_rewind.__primitive_realization)⟩,
  readout := some (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)),
  variation := some ⟨(cellVariation)⟩,
  sensitivity := some ⟨(cellSensitivity)⟩,
  escapeFrom := some (Bool),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S0.Computability.Coding.PhysicalSixParser
