/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangePeaks
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangePeaks
   mirror-E: none(waiver:two-sided-splice-estimate)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The actual rational denominator registers the two-sided center estimate. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangePeaks
import Reg.Support.DependentFamily
import Mathlib.Tactic
open D5.S1.Words.KAbelianLagrange GenContFract
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangePeaks
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
  Law R := ∀ (α x y : ℝ) (_hα : Irrational α)
    (_hx : Irrational x) (_hx0 : 0 < x) (_hx1 : x < 1)
    (_hy : Irrational y) (_hy0 : 0 < y) (_hy1 : y < 1)
    (n L : ℕ) (_hLn : L ≤ n)
    (_hleft : ∀ i < L,
      (GenContFract.of α).s.get? (n - (i + 1)) = (GenContFract.of x).s.get? i)
    (_hright : ∀ i < L,
      (GenContFract.of α).s.get? (n + 1 + i) = (GenContFract.of y).s.get? i),
    |1 / ((R.readout () () (α.convergent n) : ℝ) ^ 2 *
      |α - (α.convergent n : ℝ)|) -
      (((GenContFract.of α).s.get? n).getD ⟨1, 1⟩).b - x - y| ≤
        2 / (Nat.fib (L + 1) : ℝ) ^ 2

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hs1 : 1 < Real.sqrt 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have hs2 : Real.sqrt 2 < 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have hx : Irrational (Real.sqrt 2 / 2) := by
        exact irrational_sqrt_two.div_natCast (m := 2) (by norm_num)
      have hh := h (Real.sqrt 2) (Real.sqrt 2 / 2) (Real.sqrt 2 / 2)
        irrational_sqrt_two hx (by positivity) (by linarith) hx
        (by positivity) (by linarith) 0 0 le_rfl (by intro i hi; omega)
        (by intro i hi; omega)
      have hnt : ¬(GenContFract.of (Real.sqrt 2)).TerminatedAt 0 := by
        intro ht
        have he := GenContFract.of_correctness_of_terminatedAt ht
        rw [Real.convs_eq_convergent] at he
        exact irrational_sqrt_two.ne_rat _ he
      obtain ⟨P, hP⟩ := Option.ne_none_iff_exists'.mp hnt
      have ha : 1 ≤ P.b := GenContFract.of_one_le_get?_partDen
        (GenContFract.partDen_eq_s_b hP)
      have he : |-(P.b) - Real.sqrt 2 / 2 - Real.sqrt 2 / 2| ≤ 2 := by
        simpa [bad, realize, hP] using hh
      have hb := (abs_le.mp he).1
      linarith
    exact ⟨perron_block_estimate, bad, hbad⟩
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hs1 : 1 < Real.sqrt 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have hs2 : Real.sqrt 2 < 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have hx : Irrational (Real.sqrt 2 / 2) := by
        exact irrational_sqrt_two.div_natCast (m := 2) (by norm_num)
      have hh := h (Real.sqrt 2) (Real.sqrt 2 / 2) (Real.sqrt 2 / 2)
        irrational_sqrt_two hx (by positivity) (by linarith) hx
        (by positivity) (by linarith) 0 0 le_rfl (by intro i hi; omega)
        (by intro i hi; omega)
      have hnt : ¬(GenContFract.of (Real.sqrt 2)).TerminatedAt 0 := by
        intro ht
        have he := GenContFract.of_correctness_of_terminatedAt ht
        rw [Real.convs_eq_convergent] at he
        exact irrational_sqrt_two.ne_rat _ he
      obtain ⟨P, hP⟩ := Option.ne_none_iff_exists'.mp hnt
      have ha : 1 ≤ P.b := GenContFract.of_one_le_get?_partDen
        (GenContFract.partDen_eq_s_b hP)
      have he : |-(P.b) - Real.sqrt 2 / 2 - Real.sqrt 2 / 2| ≤ 2 := by
        simpa [bad, realize, hP] using hh
      have hb := (abs_le.mp he).1
      linarith
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
  owner := `D5.S1.Words.KAbelianLagrange.KAbelianLagrangePeaks
  coordinates := #[]
  readouts := #[{ path := #["body", "body", "body", "body", "body",
    "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
    "fn", "arg", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg",
    "fn", "arg", "fn", "arg", "arg", "fn"], functionOperand := true }] }

register_information_theorem perron_block_estimate in arena
  readout via (realize signature (fun _ _ => Rat.den) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangePeaks
