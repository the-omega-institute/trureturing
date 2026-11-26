import GRH.Lib.Adelic.Adeles.AdditiveCharDefs
import GRH.Lib.General.Topology.LocalDefs
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic number theory (textbook or folklore).

This file: A finite product of completions is an instance of `SemilocalField`. -/

attribute [-simp] Subtype.forall

variable {E : Type} [Field E] [NumberField E] {P : Finset (FinPlace E)}

/-- The product of the completions E_w over the places w in P. -/
abbrev LocProd (P : Finset (FinPlace E)) := ∀ w : P, LocField w.1

open Valued

noncomputable instance :
  SemilocalField (LocProd P) := by refine ⟨.copy (⨅ i, v.integer.comap (Pi.evalRingHom _ i)) _
  (by aesop), MulEquiv.piUnits.symm (uniformizer ·.1), (Subring.copy_eq ..).ge ?_, isCompact_univ_pi
  (isCompact_LocInt ·.1), (MeasureTheory.volume_pi_pi _).trans ?_, isOpen_set_pi ?_ fun _ _ ↦
  isOpen_integer _, tendsto_pi_nhds.2 fun _ ↦ tendsto_zero_pow_of_v_lt_one ?_, fun _ _ ↦ by
  simpa [funext_iff, Classical.skolem, forall_and] using! fun _ ↦
  isValuationPair_valuationSubring (LocInt _) ..⟩ <;> simp +decide [v.mem_integer_iff]

lemma mem_O_locProd {x : LocProd P} : x ∈ SemilocalField.O ↔ ∀ i, v (x i) ≤ 1 := Set.mem_univ_pi
