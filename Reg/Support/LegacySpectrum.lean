import Reg.Support.BoundedRunSpace
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

namespace Reg.Support.LegacySpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
open _root_.D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
open LeanInformationAudit

/-- Constructor spelling of the frozen index, with equality checked below. -/
def indexReadout : SpectrumAtom → Fin 5
  | .t1 => ⟨Nat.zero, by decide⟩
  | .t2 => ⟨Nat.succ Nat.zero, by decide⟩
  | .t3 => ⟨Nat.succ (Nat.succ Nat.zero), by decide⟩
  | .t4 => ⟨Nat.succ (Nat.succ (Nat.succ Nat.zero)), by decide⟩
  | .t5 => ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))), by decide⟩

theorem indexReadout_eq : indexReadout = SpectrumAtom.index := by
  funext atom
  cases atom <;> rfl

theorem bridge : LegacyPrimitiveRealization spectrumArena
    (Function.Bijective SpectrumAtom.index)
    (@RegistrationTemplates.cutRealization SpectrumAtom (Fin 5) (inferInstanceAs (DecidableEq (Fin 5))) (fun atom => indexReadout atom)) := by
  rw [indexReadout_eq]
  exact ⟨Iff.rfl⟩

theorem sensitivity : FiniteSlotSensitivity spectrumArena := by
  constructor
  · intro i
    refine ⟨RegistrationTemplates.cutRealization SpectrumAtom.index,
      RegistrationTemplates.cutRealization (fun _ => (0 : Fin 5)), ?_, ?_, ?_⟩
    · intro j different
      exact (different (@Subsingleton.elim Unit inferInstance _ _)).elim
    · intro j
      exact Fin.elim0 j
    · constructor
      · intro _ h
        exact (by decide : SpectrumAtom.t1 ≠ SpectrumAtom.t2) (h.1 rfl)
      · intro _
        exact spectrum_atom_index_bijective
  · intro i
    exact Fin.elim0 i

theorem dependence : ∃ x y, SpectrumAtom.index x ≠ SpectrumAtom.index y :=
  ⟨.t1, .t2, by decide⟩

#print axioms sensitivity
#print axioms dependence
end Reg.Support.LegacySpectrum
