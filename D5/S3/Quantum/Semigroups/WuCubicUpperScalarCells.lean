import D5.S3.Quantum.Semigroups.WuCubicCornerInterpolation
import D5.S3.Quantum.Semigroups.WuCubicUpperCornerJetRational
import D5.S3.Quantum.Semigroups.WuCubicUpperPartition
import Batteries.Tactic.OpenPrivate

/-! Closed-cell certificates for the two scalar upper focal long-crossing tests. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Semigroups.WuCubicUpperScalarCells

open scoped BigOperators Topology
open WuCubicCornerInterpolation (boxCorner finite_box_floor_of_second_deriv)
open WuCubicGibbsCheckedCoverCompact (InBox)
open WuCubicHellingerMatrix (longTest focalOffsets)
open WuCubicUpperCornerJet (replayFocalY replayScalarMinus replayScalarPlus scalar_replay_semantics)
open WuCubicUpperPartition (Box)
open D5.S0.Certificates.BoxCover.RationalIntervalExpression (Expr value)

open private Checked.expr Checked.ok Checked.sound Checked.lo Checked.hi
  from D5.S3.Quantum.Semigroups.WuCubicGibbsCheckedCoverCompact
open private along Jet Jet.val Jet.second Jet.sound Jet.ok Jet.encloses
  padBox jetScalarMinus jetScalarPlus
  from D5.S3.Quantum.Semigroups.WuCubicUpperCornerJetRational

variable {box : Fin 5 → ℚ × ℚ} {i : Fin 5}

private noncomputable def boxLo (b : Fin 4 → ℚ × ℚ) (i : Fin 4) : ℝ := (b i).1
private noncomputable def boxHi (b : Fin 4 → ℚ × ℚ) (i : Fin 4) : ℝ := (b i).2

private def padPoint (x : Fin 4 → ℝ) : Fin 5 → ℝ := Fin.lastCases 0 x

private theorem padPoint_mem {b : Fin 4 → ℚ × ℚ} {x : Fin 4 → ℝ}
    (hx : ∀ i, boxLo b i ≤ x i ∧ x i ≤ boxHi b i) : InBox (padBox b) (padPoint x) := by
  intro k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp only [padBox, padPoint, Fin.lastCases_last, Rat.cast_zero, le_refl, and_self]
  · simpa only [padBox, padPoint, Fin.lastCases_castSucc, boxLo, boxHi] using hx j

private theorem padPoint_update (x : Fin 4 → ℝ) (i : Fin 4) (t : ℝ) :
    padPoint (Function.update x i t) = Function.update (padPoint x) i.castSucc t := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp only [padPoint, Fin.lastCases_last, Function.update_of_ne (Fin.castSucc_ne_last i).symm]
  · by_cases h : j = i
    · subst j
      simp only [padPoint, Fin.lastCases_castSucc, Function.update_self]
    · have h' : j.castSucc ≠ i.castSucc := fun he => h (Fin.castSucc_injective 4 he)
      simp only [padPoint, Fin.lastCases_castSucc, Function.update_of_ne h,
        Function.update_of_ne h']

private def secondAbsBound (a : Jet box i) : ℚ :=
  max (-Checked.lo (Jet.second a)) (Checked.hi (Jet.second a))

private noncomputable def scalarInterpolationLoss (b : Fin 4 → ℚ × ℚ)
    (J : (i : Fin 4) → Jet (padBox b) i.castSucc) : ℝ :=
  ∑ i, (secondAbsBound (J i) : ℝ) * (boxHi b i - boxLo b i) ^ 2 / 8

private theorem jet_scalar_box_floor (b : Fin 4 → ℚ × ℚ)
    (J : (i : Fin 4) → Jet (padBox b) i.castSucc) (F : (Fin 5 → ℝ) → ℝ)
    (hvalue : ∀ i z, value z (Checked.expr (Jet.val (J i))) = F z)
    (hcheck : ∀ i, Jet.ok (J i) = true) (L : ℝ)
    (hcorner : ∀ ε, L + scalarInterpolationLoss b J ≤
      F (padPoint (boxCorner (boxLo b) (boxHi b) ε)))
    (x : Fin 4 → ℝ) (hx : ∀ i, boxLo b i ≤ x i ∧ x i ≤ boxHi b i) :
    L ≤ F (padPoint x) := by
  have hchecks (i : Fin 4) :
      Checked.ok (Jet.val (J i)) = true ∧ Checked.ok (Jet.second (J i)) = true := by
    have h := Bool.and_eq_true_iff.mp (hcheck i)
    exact ⟨h.1, (Bool.and_eq_true_iff.mp h.2).2⟩
  refine finite_box_floor_of_second_deriv (fun y => F (padPoint y)) (boxLo b) (boxHi b)
    (fun i => (secondAbsBound (J i) : ℝ)) x L hx ?_ hcorner ?_
  · intro i
    have hord : Checked.lo (Jet.second (J i)) ≤ Checked.hi (Jet.second (J i)) :=
      (Checked.sound (Jet.second (J i)) (hchecks i).2).2
    have hn : 0 ≤ secondAbsBound (J i) := by
      rcases le_total 0 (Checked.hi (Jet.second (J i))) with hu | hu
      · exact hu.trans (le_max_right _ _)
      · exact (neg_nonneg.mpr (hord.trans hu)).trans (le_max_left _ _)
    exact_mod_cast hn
  · intro y hy i
    let a := J i
    let g : ℝ → ℝ := fun t => F (padPoint (Function.update y i t))
    have hslice (t : ℝ) (ht : t ∈ Set.Icc (boxLo b i) (boxHi b i)) :
        (∃ d, HasDerivAt g d t) ∧ (∃ d, HasDerivAt (deriv g) d t) ∧
          |deriv (deriv g) t| ≤ (secondAbsBound a : ℝ) := by
      let z := padPoint (Function.update y i t)
      have hz : InBox (padBox b) z := by
        apply padPoint_mem
        intro j
        by_cases h : j = i
        · subst j
          simpa only [Function.update_self, Set.mem_Icc] using ht
        · simpa only [Function.update_of_ne h] using hy j
      have hcoord : z i.castSucc = t := by
        simp only [z, padPoint, Fin.lastCases_castSucc, Function.update_self]
      -- Replacing the same coordinate again gives the original slice, including at the endpoints.
      have halong : along (Jet.val a) i.castSucc z = g := by
        funext s
        change value (Function.update (padPoint (Function.update y i t)) i.castSucc s)
          (Checked.expr (Jet.val a)) = F (padPoint (Function.update y i s))
        rw [padPoint_update y i t, Function.update_idem, ← padPoint_update y i s]
        exact hvalue i _
      obtain ⟨hfirst, hsecond⟩ := Jet.sound a z hz (hchecks i).1
      have hbounds := Jet.encloses a hz (hcheck i)
      dsimp only at hbounds
      rw [halong, hcoord] at hbounds hsecond
      have hfirstAt := hfirst.self_of_nhds
      rw [halong, hcoord] at hfirstAt
      refine ⟨⟨_, hfirstAt⟩, ⟨_, hsecond⟩, abs_le.mpr ⟨?_, ?_⟩⟩
      · have hneg : -secondAbsBound a ≤ Checked.lo (Jet.second a) := by
          simpa only [secondAbsBound, neg_neg] using
            neg_le_neg (le_max_left (-Checked.lo (Jet.second a)) (Checked.hi (Jet.second a)))
        have hreal : ((-secondAbsBound a : ℚ) : ℝ) ≤ (Checked.lo (Jet.second a) : ℝ) :=
          Rat.cast_le.mpr hneg
        rw [Rat.cast_neg] at hreal
        exact hreal.trans hbounds.2.2.1
      · exact hbounds.2.2.2.trans
          (Rat.cast_le.mpr (le_max_right (-Checked.lo (Jet.second a)) (Checked.hi (Jet.second a))))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨_, hd⟩ := (hslice t ht).1
      exact hd.continuousAt.continuousWithinAt
    · intro t ht
      obtain ⟨_, hd⟩ := (hslice t (Set.Ioo_subset_Icc_self ht)).1
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨_, hd⟩ := (hslice t (Set.Ioo_subset_Icc_self ht)).2.1
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      have hbound := (abs_le.mp (hslice t (Set.Ioo_subset_Icc_self ht)).2.2).2
      simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using hbound

-- The annotations do not appear in either interpretation of the expression.
private def rationalValue (x : Fin 5 → ℚ) : Expr 5 → ℚ
  | .input i _ _ => x i
  | .const q _ _ => q
  | .add _ _ a b => rationalValue x a + rationalValue x b
  | .neg _ _ a => -rationalValue x a
  | .mul _ _ a b => rationalValue x a * rationalValue x b
  | .square _ _ a => rationalValue x a ^ 2
  | .inv _ _ a => (rationalValue x a)⁻¹

private theorem cast_rationalValue (x : Fin 5 → ℚ) (e : Expr 5) :
    (rationalValue x e : ℝ) = value (fun i => (x i : ℝ)) e := by
  induction e <;>
    simp_all only [rationalValue, value, Rat.cast_add, Rat.cast_neg, Rat.cast_mul,
      Rat.cast_pow, Rat.cast_inv, one_div]

private def rationalCorner (b : Box) (ε : Fin 4 → Bool) : Fin 5 → ℚ :=
  Fin.lastCases 0 (fun i => if ε i then (b i).2 else (b i).1)

private theorem cast_rationalCorner (b : Box) (ε : Fin 4 → Bool) :
    (fun i => (rationalCorner b ε i : ℝ)) = padPoint (boxCorner (boxLo b) (boxHi b) ε) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [rationalCorner, padPoint, Fin.lastCases_last, Rat.cast_zero]
  · simp only [rationalCorner, padPoint, Fin.lastCases_castSucc, boxCorner, boxLo, boxHi]
    split <;> rfl

private def rationalLoss (b : Box) (J : (i : Fin 4) → Jet (padBox b) i.castSucc) : ℚ :=
  ∑ i, secondAbsBound (J i) * ((b i).2 - (b i).1) ^ 2 / 8

private theorem cast_rationalLoss (b : Box) (J : (i : Fin 4) → Jet (padBox b) i.castSucc) :
    (rationalLoss b J : ℝ) = scalarInterpolationLoss b J := by
  simp only [rationalLoss, scalarInterpolationLoss, Rat.cast_sum, Rat.cast_mul, Rat.cast_sub,
    Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, boxLo, boxHi]

private def jetFloorCheck (b : Box) (J : (i : Fin 4) → Jet (padBox b) i.castSucc)
    (floor : ℚ) : Bool :=
  let threshold := floor + rationalLoss b J
  let expr := Checked.expr (Jet.val (J 0))
  decide (∀ i : Fin 4, Jet.ok (J i) = true) &&
    decide (∀ ε : Fin 4 → Bool, threshold ≤ rationalValue (rationalCorner b ε) expr)

private theorem jetFloorCheck_sound (b : Box) (J : (i : Fin 4) → Jet (padBox b) i.castSucc)
    (F : (Fin 5 → ℝ) → ℝ) (hvalue : ∀ i z, value z (Checked.expr (Jet.val (J i))) = F z)
    (floor : ℚ) (hcheck : jetFloorCheck b J floor = true)
    {x : Fin 4 → ℝ} (hx : WuCubicUpperPartition.InBox b x) :
    (floor : ℝ) ≤ F (padPoint x) := by
  unfold jetFloorCheck at hcheck
  obtain ⟨hjet, hcorner⟩ := Bool.and_eq_true_iff.mp hcheck
  refine jet_scalar_box_floor b J F hvalue (of_decide_eq_true hjet) floor ?_ x hx
  intro ε
  have h := (Rat.cast_le (K := ℝ)).mpr ((of_decide_eq_true hcorner) ε)
  rwa [Rat.cast_add, cast_rationalLoss, cast_rationalValue, cast_rationalCorner, hvalue] at h

/-- Check a common positive floor for the two upper focal long-crossing tests.
Each sign uses its own derivative loss and all sixteen exact corner values. -/
def longTestCheck (b : Box) (floor : ℚ) : Bool :=
  decide (0 < floor) && (jetFloorCheck b (jetScalarMinus b) floor &&
    jetFloorCheck b (jetScalarPlus b) floor)

/-- The checked floor holds for the physical long-crossing pair at every point
of the closed cell, including boundary and degenerate slices. -/
theorem longTestCheck_sound {b : Box} {floor : ℚ} (hcheck : longTestCheck b floor = true)
    {x : Fin 4 → ℝ} (hx : WuCubicUpperPartition.InBox b x) :
    let y := focalOffsets (x 1) (x 2) (x 3)
    0 < (floor : ℝ) ∧ ((floor : ℝ) ≤ longTest (-1) (x 0) y ∧
      (floor : ℝ) ≤ longTest 1 (x 0) y) := by
  obtain ⟨hfloor, htests⟩ := Bool.and_eq_true_iff.mp hcheck
  obtain ⟨hm, hp⟩ := Bool.and_eq_true_iff.mp htests
  have hm' := jetFloorCheck_sound b (jetScalarMinus b) replayScalarMinus
    (fun i z => (scalar_replay_semantics b i z).1) floor hm hx
  have hp' := jetFloorCheck_sound b (jetScalarPlus b) replayScalarPlus
    (fun i z => (scalar_replay_semantics b i z).2) floor hp hx
  change 0 < (floor : ℝ) ∧ ((floor : ℝ) ≤ longTest (-1) (padPoint x 0) (replayFocalY (padPoint x)) ∧
    (floor : ℝ) ≤ longTest 1 (padPoint x 0) (replayFocalY (padPoint x)))
  refine ⟨Rat.cast_pos.mpr (of_decide_eq_true hfloor), ?_⟩
  simpa only [longTest, WuCubicHellingerMatrix.weightSum, replayScalarMinus, replayScalarPlus,
    WuCubicUpperCornerJet.replayP0, WuCubicUpperCornerJet.replayP2,
    WuCubicUpperCornerJet.replayLong, WuCubicUpperCornerJet.replayResidual,
    neg_one_mul, one_mul, sub_eq_add_neg] using And.intro hm' hp'

/-- The first leaf of the upper focal replay partition. -/
def firstUpperReplayCell : Box :=
  ![(1049 / 1000, 33719 / 32000), (0, 1 / 256), (-1 / 128, -1 / 256), (0, 1 / 4)]

theorem firstUpperReplayCell_accepted : longTestCheck firstUpperReplayCell (1 / 8) = true := by
  decide +kernel

/-- Both long-crossing tests are strictly positive throughout the first cell. -/
theorem firstUpperReplayCell_longTests {x : Fin 4 → ℝ}
    (hx : WuCubicUpperPartition.InBox firstUpperReplayCell x) :
    let y := focalOffsets (x 1) (x 2) (x 3)
    0 < longTest (-1) (x 0) y ∧ 0 < longTest 1 (x 0) y := by
  obtain ⟨hfloor, hm, hp⟩ := longTestCheck_sound firstUpperReplayCell_accepted hx
  exact ⟨hfloor.trans_le hm, hfloor.trans_le hp⟩

#print axioms firstUpperReplayCell_accepted
#print axioms firstUpperReplayCell_longTests

end D5.S3.Quantum.Semigroups.WuCubicUpperScalarCells
