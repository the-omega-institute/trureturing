/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangePerron
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangePerron
   mirror-E: none(waiver:reduced-perron-coefficient)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The actual rational denominator readout registers the reduced Perron identity. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangePerron
import Reg.Support.DependentFamily
import Mathlib.Tactic

open D5.S1.Words.KAbelianLagrange GenContFract
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangePerron
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => Rat.den) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, Irrational x → ∀ n : ℕ,
    1 / ((R.readout () () (x.convergent n) : ℝ) ^ 2 *
      |x - (x.convergent n : ℝ)|) =
        ((IntFractPair.stream x n).getD ⟨0, 0⟩).fr⁻¹ +
          GenContFract.convs'Aux (Stream'.Seq.ofList
            (List.ofFn (fun i : Fin n =>
              ((GenContFract.of x).s.get? i).getD ⟨1, 1⟩)).reverse) n

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨perron_coefficient, bad, ?_⟩
    intro h
    have hx : Irrational (Real.sqrt 2) := irrational_sqrt_two
    have hf : 0 < Int.fract (Real.sqrt 2) := Int.fract_pos.mpr (hx.ne_int _)
    have hh := h (Real.sqrt 2) hx 0
    have he : (0 : ℝ) = (Int.fract (Real.sqrt 2))⁻¹ := by
      simpa [bad, realize, IntFractPair.stream_zero, IntFractPair.of,
        GenContFract.convs'Aux] using hh
    exact (ne_of_gt (inv_pos.mpr hf)) he.symm
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have hx : Irrational (Real.sqrt 2) := irrational_sqrt_two
      have hf : 0 < Int.fract (Real.sqrt 2) := Int.fract_pos.mpr (hx.ne_int _)
      have hh := h (Real.sqrt 2) hx 0
      have he : (0 : ℝ) = (Int.fract (Real.sqrt 2))⁻¹ := by
        simpa [bad, realize, IntFractPair.stream_zero, IntFractPair.of,
          GenContFract.convs'Aux] using hh
      exact (ne_of_gt (inv_pos.mpr hf)) he.symm
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, hbad⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, (1 : ℚ) / 2, ?_⟩
    norm_num [actual, realize]

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.KAbelianLagrange.KAbelianLagrangePerron
  coordinates := #[]
  readouts := #[{ path := #["body", "body", "body", "fn", "arg", "arg", "fn",
    "arg", "fn", "arg", "arg", "fn"], functionOperand := true }] }

register_information_theorem perron_coefficient in arena
  readout via (realize signature (fun _ _ => Rat.den) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangePerron
