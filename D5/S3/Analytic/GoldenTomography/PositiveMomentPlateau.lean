/- GID: D5/S3/Analytic/GoldenTomography/PositiveMomentPlateau
   generality: I
   mirror-B: D5/B/S3/Analytic/GoldenTomography/PositiveMomentPlateau
   mirror-E: none(waiver:unbounded-positive-moment-obstruction)
   anchors: []
   utility: none
   digest: Two bounded positive spectral measures can hide an arbitrarily long flat moment difference. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Analytic.GoldenTomography.PositiveMomentPlateau

open FinitePronyHankelReconstruction

private def plateauWeights : (d : Nat) → (Fin d → Real) → Fin d → Real
  | 0, _ => fun i => Fin.elim0 i
  | d + 1, nodes =>
      let tailNodes : Fin d → Real := fun j => nodes j.succ
      let tailWeights := plateauWeights d tailNodes
      let lifted : Fin d → Real := fun j =>
        (1 - nodes 0) * tailWeights j / (tailNodes j - nodes 0)
      Fin.cons (1 - ∑ j, lifted j) lifted

/-- An explicit spectral family satisfies a convex delay recursion.
The gaps are used only to construct this lower-bound witness. -/
private theorem bounded_plateau :
    ∀ d : Nat, ∀ nodes : Fin d → Real,
      Function.Injective nodes → (∀ i, 0 ≤ nodes i ∧ nodes i ≤ 1) →
      (∀ n, 0 ≤ pronyMoment nodes (plateauWeights d nodes) n ∧
        pronyMoment nodes (plateauWeights d nodes) n ≤ 1) ∧
      (∀ n, n < d → pronyMoment nodes (plateauWeights d nodes) n = 1) := by
  intro d
  induction d with
  | zero =>
      intro nodes hi hb
      constructor
      · intro n
        simp [pronyMoment]
      · intro n hn
        omega
  | succ d ih =>
      intro nodes hi hb
      let a : Real := nodes 0
      let ns : Fin d → Real := fun j => nodes j.succ
      let ws : Fin d → Real := plateauWeights d ns
      let cs : Fin (d + 1) → Real := plateauWeights (d + 1) nodes
      let f : Nat → Real := pronyMoment nodes cs
      let v : Nat → Real := pronyMoment ns ws
      have hni : Function.Injective ns := by
        intro i j hij
        exact Fin.succ_injective (hi hij)
      have hnb (j : Fin d) : 0 ≤ ns j ∧ ns j ≤ 1 := hb j.succ
      have hv := ih ns hni hnb
      have ha : 0 ≤ a ∧ a ≤ 1 := hb 0
      have hz : f 0 = 1 := by
        simp [f, cs, plateauWeights, pronyMoment, Fin.sum_univ_succ]
      have hcoef (j : Fin d) :
          cs j.succ * (nodes j.succ - a) = (1 - a) * ws j := by
        have hgap : nodes j.succ - a ≠ 0 := by
          apply sub_ne_zero.mpr
          intro he
          have h := hi he
          have hvv := congrArg Fin.val h
          simp at hvv
        change ((1 - a) * ws j / (nodes j.succ - a)) * (nodes j.succ - a) = _
        exact div_mul_cancel₀ _ hgap
      have hdef (n : Nat) : (1 - a) * v n = f (n + 1) - a * f n := by
        calc
          _ = ∑ j : Fin (d + 1), cs j * (nodes j - a) * nodes j ^ n := by
            rw [Fin.sum_univ_succ]
            change (1 - a) * (∑ j : Fin d, ws j * ns j ^ n) =
              cs 0 * (a - a) * a ^ n +
                ∑ j : Fin d, cs j.succ * (nodes j.succ - a) * nodes j.succ ^ n
            simp only [sub_self, mul_zero, zero_mul, zero_add]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [hcoef]
            dsimp [ns]
            ring
          _ = _ := by
            dsimp [f, pronyMoment]
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            rw [pow_succ]
            ring
      have hstep (n : Nat) : f (n + 1) = a * f n + (1 - a) * v n := by
        have h := hdef n
        linarith
      have hu : ∀ n, 0 ≤ f n ∧ f n ≤ 1 := by
        intro n
        induction n with
        | zero => rw [hz]; norm_num
        | succ n ihn =>
            have hvn : 0 ≤ v n ∧ v n ≤ 1 := hv.1 n
            have hna : 0 ≤ 1 - a := sub_nonneg.mpr ha.2
            have h0 := mul_nonneg ha.1 ihn.1
            have h1 := mul_nonneg hna hvn.1
            have h2 := mul_le_mul_of_nonneg_left ihn.2 ha.1
            have h3 := mul_le_mul_of_nonneg_left hvn.2 hna
            rw [hstep]
            constructor <;> nlinarith
      have hp : ∀ n, n < d + 1 → f n = 1 := by
        intro n
        induction n with
        | zero => intro _; exact hz
        | succ n ihn =>
            intro hn
            have hvn : v n = 1 := hv.2 n (by omega)
            rw [hstep, ihn (by omega), hvn]
            ring
      exact ⟨hu, hp⟩

/-- For any prescribed distinct stable nonnegative nodes, two nonnegative
weight families of arbitrarily bounded total mass have a positive flat moment
difference on the first d indices, while the difference stays within that
same height at every later index. No lower mass or gap is imposed uniformly.
This theorem constructs the spectral witness; the positive block realization
and the asymptotic bounded-noise minimax conclusion are separate ordinary proofs. -/
theorem positive_moment_plateau
    {d : Nat} (nodes : Fin d → Real) (hi : Function.Injective nodes)
    (hb : ∀ i, 0 ≤ nodes i ∧ nodes i ≤ 1)
    (budget : Real) (hbudget : 0 < budget) :
    ∃ delta : Real, 0 < delta ∧ ∃ plus minus : Fin d → Real,
      (∀ i, 0 ≤ plus i ∧ 0 ≤ minus i) ∧
      (∑ i, (plus i + minus i)) ≤ budget ∧
      (∀ n, 0 ≤ pronyMoment nodes plus n - pronyMoment nodes minus n ∧
        pronyMoment nodes plus n - pronyMoment nodes minus n ≤ delta) ∧
      (∀ n, n < d → pronyMoment nodes plus n - pronyMoment nodes minus n = delta) := by
  let cs : Fin d → Real := plateauWeights d nodes
  let B : Real := ∑ i, |cs i|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  let delta : Real := budget / (1 + B)
  have hd : 0 < delta := div_pos hbudget (by linarith)
  have hnorm : delta * (1 + B) = budget := by
    exact div_mul_cancel₀ budget (ne_of_gt (show 0 < 1 + B by linarith))
  let plus : Fin d → Real := fun i => delta * max (cs i) 0
  let minus : Fin d → Real := fun i => delta * max (-cs i) 0
  have hs (x : Real) : max x 0 - max (-x) 0 = x ∧
      max x 0 + max (-x) 0 = |x| := by
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx]
      constructor <;> ring
    · have hx' : x ≤ 0 := le_of_not_ge hx
      rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'), abs_of_nonpos hx']
      constructor <;> ring
  have hm (n : Nat) : pronyMoment nodes plus n - pronyMoment nodes minus n =
      delta * pronyMoment nodes cs n := by
    unfold pronyMoment
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [plus, minus]
    calc
      _ = delta * (max (cs i) 0 - max (-cs i) 0) * nodes i ^ n := by ring
      _ = _ := by rw [(hs (cs i)).1]; ring
  have hu := bounded_plateau d nodes hi hb
  refine ⟨delta, hd, plus, minus, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨mul_nonneg hd.le (le_max_right _ _),
      mul_nonneg hd.le (le_max_right _ _)⟩
  · have he : (∑ i, (plus i + minus i)) = delta * B := by
      dsimp [B]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [plus, minus]
      rw [← mul_add, (hs (cs i)).2]
    rw [he]
    nlinarith
  · intro n
    rw [hm]
    have hn : 0 ≤ pronyMoment nodes cs n ∧ pronyMoment nodes cs n ≤ 1 := hu.1 n
    constructor
    · exact mul_nonneg hd.le hn.1
    · simpa using mul_le_mul_of_nonneg_left hn.2 hd.le
  · intro n hn
    rw [hm]
    have he : pronyMoment nodes cs n = 1 := hu.2 n hn
    rw [he, mul_one]

#print axioms positive_moment_plateau

end D5.S3.Analytic.GoldenTomography.PositiveMomentPlateau
