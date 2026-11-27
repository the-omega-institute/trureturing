import D5.S3.Quantum.Semigroups.WuCubicGibbsCheckedCoverCompact
import D5.S3.Quantum.Semigroups.WuCubicThermalDerivatives
import D5.S3.Quantum.Semigroups.WuCubicHellingerMatrix
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Topology

namespace D5.S3.Quantum.Semigroups.WuCubicUpperCornerJet

open D5.S0.Certificates.BoxCover.RationalIntervalExpression
open WuCubicGibbsCheckedCoverCompact (InBox)
open WuCubicThermalDerivatives
open private Checked Checked.expr Checked.ok Checked.sound Checked.lo Checked.hi
  input lit plus minus times sq recip eval_input eval_lit eval_plus eval_minus eval_times
  eval_sq eval_recip from D5.S3.Quantum.Semigroups.WuCubicGibbsCheckedCoverCompact
open WuCubicHellingerMatrix (Vec3 focalOffsets levels lowerWeight upperWeight longCrossing)
open WuCubicOccupationTaylor (gibbsLevels)
open private gamma c e from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private leftGap middleGap rightGap fieldOverGap scaledMixture endpointField endpointLinear
  lowerTiltFactor upperTiltFactor cast_zero cast_one cast_two
  edgeRows edgeWeights entropyWeights massWeights massChange massRow gibbsMass
  from D5.S3.Quantum.Semigroups.WuCubicHellingerMatrix

variable {box : Fin 5 → ℚ × ℚ}

private noncomputable def along (a : Checked box) (i : Fin 5) (z : Fin 5 → ℝ) : ℝ → ℝ :=
  fun s => value (Function.update z i s) (Checked.expr a)

private def Between (a : Checked box) (v : ℝ) : Prop :=
  (Checked.lo a : ℝ) ≤ v ∧ v ≤ (Checked.hi a : ℝ)

private theorem checked_bounds (a : Checked box) {z : Fin 5 → ℝ}
    (hz : InBox box z) (ha : Checked.ok a = true) : Between a (value z (Checked.expr a)) :=
  checked_expression_encloses box z hz (Checked.expr a) (Checked.sound a ha).1

-- The derivative identities hold on a real neighborhood of each checked point,
-- including when the point lies on a face or a degenerate interval.
private structure Jet (box : Fin 5 → ℚ × ℚ) (i : Fin 5) where
  val : Checked box
  first : Checked box
  second : Checked box
  sound : ∀ z, InBox box z → Checked.ok val = true →
    (∀ᶠ s in 𝓝 (z i), HasDerivAt (along val i z) (along first i z s) s) ∧
    HasDerivAt (deriv (along val i z)) (value z (Checked.expr second)) (z i)

-- The derivative rules for products, squares and reciprocals differentiate
-- the annotated first-derivative function. Its equality with the ordinary
-- derivative on a neighborhood transfers the second-derivative identity.
private theorem hasDerivAt_first {f f₁ : ℝ → ℝ} {x f₂ : ℝ}
    (hf : ∀ᶠ s in 𝓝 x, HasDerivAt f (f₁ s) s)
    (hdf : HasDerivAt (deriv f) f₂ x) : HasDerivAt f₁ f₂ x := by
  apply hdf.congr_of_eventuallyEq
  filter_upwards [hf] with s hs
  exact hs.deriv.symm

variable {i : Fin 5}

private def Jet.ok (a : Jet box i) : Bool :=
  Checked.ok a.val && (Checked.ok a.first && Checked.ok a.second)

private theorem Jet.encloses (a : Jet box i) {z : Fin 5 → ℝ}
    (hz : InBox box z) (h : a.ok = true) :
    let f := along a.val i z
    Between a.val (f (z i)) ∧ Between a.first (deriv f (z i)) ∧
      Between a.second (deriv (deriv f) (z i)) := by
  obtain ⟨hv, hd⟩ := Bool.and_eq_true_iff.mp
    (show (Checked.ok a.val && (Checked.ok a.first && Checked.ok a.second)) = true from h)
  obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp hd
  obtain ⟨hf, hdf⟩ := a.sound z hz hv
  dsimp only
  rw [hf.self_of_nhds.deriv, hdf.deriv]
  simpa only [along, Function.update_eq_self] using
    And.intro (checked_bounds a.val hz hv)
      (And.intro (checked_bounds a.first hz h₁) (checked_bounds a.second hz h₂))

private def Jet.coord (box : Fin 5 → ℚ × ℚ) (i j : Fin 5) : Jet box i where
  val := input box j
  first := lit (if j = i then 1 else 0)
  second := lit 0
  sound z _ _ := by
    by_cases h : j = i
    · subst j
      have hv : along (input box i) i z = fun s => s := by
        funext s
        simp only [along, eval_input, Function.update_self]
      rw [hv, deriv_id'']
      constructor
      · apply Filter.Eventually.of_forall
        intro s
        simpa [along, eval_lit] using hasDerivAt_id' s
      · simpa only [eval_lit, Rat.cast_zero] using hasDerivAt_const (z i) (1 : ℝ)
    · have hv : along (input box j) i z = fun _ => z j := by
        funext s
        simp only [along, eval_input, Function.update_of_ne h]
      rw [hv, deriv_const']
      constructor
      · apply Filter.Eventually.of_forall
        intro s
        simpa [along, eval_lit, h] using hasDerivAt_const s (z j)
      · simpa only [eval_lit, Rat.cast_zero] using hasDerivAt_const (z i) (0 : ℝ)

private def Jet.const (q : ℚ) : Jet box i where
  val := lit q
  first := lit 0
  second := lit 0
  sound z _ _ := by
    have hv : along (lit (box := box) q) i z = fun _ => (q : ℝ) := by
      funext s
      exact eval_lit (box := box) (Function.update z i s) q
    rw [hv, deriv_const']
    constructor
    · apply Filter.Eventually.of_forall
      intro s
      simpa only [along, eval_lit, Rat.cast_zero] using hasDerivAt_const s (q : ℝ)
    · simpa only [eval_lit, Rat.cast_zero] using hasDerivAt_const (z i) (0 : ℝ)

private def Jet.add (a b : Jet box i) : Jet box i where
  val := plus a.val b.val
  first := plus a.first b.first
  second := plus a.second b.second
  sound z hz h := by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp
      (show (Checked.ok a.val && Checked.ok b.val) = true from h)
    obtain ⟨hf, hdf⟩ := a.sound z hz ha
    obtain ⟨hg, hdg⟩ := b.sound z hz hb
    simp only [along, eval_plus]
    constructor
    · filter_upwards [hf, hg] with s hs ht
      exact hs.fun_add ht
    · refine (hdf.fun_add hdg).congr_of_eventuallyEq ?_
      filter_upwards [hf, hg] with s hs ht
      exact (hs.fun_add ht).deriv.trans (congrArg₂ (· + ·) hs.deriv.symm ht.deriv.symm)

private def Jet.neg (a : Jet box i) : Jet box i where
  val := minus a.val
  first := minus a.first
  second := minus a.second
  sound z hz h := by
    obtain ⟨hf, hdf⟩ := a.sound z hz h
    simp only [along, eval_minus]
    constructor
    · filter_upwards [hf] with s hs
      exact hs.fun_neg
    · refine hdf.fun_neg.congr_of_eventuallyEq ?_
      filter_upwards [hf] with s hs
      exact hs.fun_neg.deriv.trans (congrArg Neg.neg hs.deriv.symm)

private def Jet.mul (a b : Jet box i) : Jet box i where
  val := times a.val b.val
  first := plus (times a.first b.val) (times a.val b.first)
  second := plus (plus (times a.second b.val) (times (times (lit 2) a.first) b.first))
    (times a.val b.second)
  sound z hz h := by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp
      (show (Checked.ok a.val && Checked.ok b.val) = true from h)
    obtain ⟨hf, hdf⟩ := a.sound z hz ha
    obtain ⟨hg, hdg⟩ := b.sound z hz hb
    have hv : along (times a.val b.val) i z =
        fun s => along a.val i z s * along b.val i z s := by
      funext s
      simp only [along, eval_times]
    rw [hv]
    simp only [along, eval_times, eval_plus, eval_lit, Rat.cast_ofNat]
    constructor
    · filter_upwards [hf, hg] with s hs ht
      exact hs.fun_mul ht
    · simpa only [along, Function.update_eq_self] using
        hasDerivAt_deriv_mul hf hg (hasDerivAt_first hf hdf) (hasDerivAt_first hg hdg)

private def Jet.square (a : Jet box i) : Jet box i where
  val := sq a.val
  first := times (times (lit 2) a.val) a.first
  second := plus (times (lit 2) (sq a.first)) (times (times (lit 2) a.val) a.second)
  sound z hz h := by
    obtain ⟨hf, hdf⟩ := a.sound z hz h
    have hv : along (sq a.val) i z = fun s => along a.val i z s ^ 2 := by
      funext s
      simp only [along, eval_sq]
    rw [hv]
    simp only [along, eval_sq, eval_times, eval_plus, eval_lit, Rat.cast_ofNat]
    constructor
    · filter_upwards [hf] with s hs
      convert hs.fun_mul hs using 1 <;> simp only [along, pow_two] <;> ring
    · simpa only [along, Function.update_eq_self] using
        hasDerivAt_deriv_square hf (hasDerivAt_first hf hdf)

private def Jet.inv (a : Jet box i) : Jet box i :=
  let invSq := recip (sq a.val)
  let invCube := recip (times (sq a.val) a.val)
  { val := recip a.val
    first := times (minus a.first) invSq
    second := plus (times (minus a.second) invSq) (times (times (lit 2) (sq a.first)) invCube)
    sound := by
      intro z hz h
      change (Checked.ok a.val && decide (Checked.hi a.val < 0 ∨ 0 < Checked.lo a.val)) = true at h
      obtain ⟨ha, hsign⟩ := Bool.and_eq_true_iff.mp h
      obtain ⟨hf, hdf⟩ := a.sound z hz ha
      have hn : along a.val i z (z i) ≠ 0 := by
        obtain ⟨hl, hu⟩ := checked_bounds a.val hz ha
        simp only [along, Function.update_eq_self]
        rcases (of_decide_eq_true hsign : Checked.hi a.val < 0 ∨ 0 < Checked.lo a.val) with h | h
        · have hh : (Checked.hi a.val : ℝ) < 0 := by exact_mod_cast h
          exact (hu.trans_lt hh).ne
        · have hh : (0 : ℝ) < (Checked.lo a.val : ℝ) := by exact_mod_cast h
          exact (hh.trans_le hl).ne'
      have hne : ∀ᶠ s in 𝓝 (z i), along a.val i z s ≠ 0 :=
        hf.self_of_nhds.continuousAt.eventually_ne hn
      have hv : along (recip a.val) i z = fun s => (along a.val i z s)⁻¹ := by
        funext s
        simp only [along, eval_recip, one_div]
      rw [hv]
      simp only [along, invSq, invCube, eval_recip, eval_times, eval_sq, eval_plus,
        eval_minus, eval_lit, Rat.cast_ofNat]
      constructor
      · filter_upwards [hf, hne] with s hs h₀
        simpa only [along, div_eq_mul_inv, one_mul] using hs.fun_inv h₀
      · simpa only [along, Function.update_eq_self, div_eq_mul_inv, one_mul, ← pow_succ] using
          hasDerivAt_deriv_one_div hf (hasDerivAt_first hf hdf) hn }

local infixl:65 " +ⱼ " => Jet.add
local infixl:70 " *ⱼ " => Jet.mul

-- The first four intervals are carried over with their original rational
-- endpoints. The fifth input has the closed interval [0, 0].
private def padBox (b : Fin 4 → ℚ × ℚ) : Fin 5 → ℚ × ℚ :=
  Fin.lastCases (0, 0) b

-- This is the factor left in cuts in verify.py.
private def normalizedLeftGapJet (b : Fin 4 → ℚ × ℚ) (i : Fin 4) : Jet (padBox b) i.castSucc :=
  let r := Jet.coord (padBox b) i.castSucc 0
  let y₀ := Jet.coord (padBox b) i.castSucc 1
  let y₁ := Jet.coord (padBox b) i.castSucc 2
  let t := r +ⱼ Jet.const (-1)
  r.square.inv +ⱼ (y₁ +ⱼ y₀.neg) *ⱼ t.inv

private noncomputable def normalizedLeftGap (z : Fin 5 → ℝ) : ℝ :=
  1 / z 0 ^ 2 + (z 2 - z 1) / (z 0 - 1)

private theorem normalizedLeftGap_slice (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    along (normalizedLeftGapJet b i).val i.castSucc z =
      (fun s => normalizedLeftGap (Function.update z i.castSucc s)) := by
  funext s
  simp only [along, normalizedLeftGapJet, normalizedLeftGap, Jet.add, Jet.mul, Jet.neg,
    Jet.inv, Jet.square, Jet.coord, Jet.const, eval_input, eval_lit, eval_plus,
    eval_minus, eval_times, eval_sq, eval_recip, Rat.cast_neg, Rat.cast_one,
    sub_eq_add_neg, div_eq_mul_inv, one_mul]

private theorem normalizedLeftGap_encloses (b : Fin 4 → ℚ × ℚ) (i : Fin 4)
    {z : Fin 5 → ℝ} (hz : InBox (padBox b) z) (h : (normalizedLeftGapJet b i).ok = true) :
    let a := normalizedLeftGapJet b i
    let k := i.castSucc
    let f := fun s => normalizedLeftGap (Function.update z k s)
    Between a.val (f (z k)) ∧ Between a.first (deriv f (z k)) ∧
      Between a.second (deriv (deriv f) (z k)) := by
  have ha := (normalizedLeftGapJet b i).encloses hz h
  dsimp only at ha
  rw [normalizedLeftGap_slice b i z] at ha
  exact ha

private theorem normalizedLeftGap_rootChecks (i : Fin 4) :
    (normalizedLeftGapJet upperRoot i).ok = true := by
  fin_cases i <;> decide +kernel

private theorem normalizedLeftGap_root_encloses (i : Fin 4) {z : Fin 5 → ℝ}
    (hz : InBox (padBox upperRoot) z) :
    let a := normalizedLeftGapJet upperRoot i
    let k := i.castSucc
    let f := fun s => normalizedLeftGap (Function.update z k s)
    Between a.val (f (z k)) ∧ Between a.first (deriv f (z k)) ∧
      Between a.second (deriv (deriv f) (z k)) :=
  normalizedLeftGap_encloses upperRoot i hz (normalizedLeftGap_rootChecks i)


/-! Rational Jet expressions for the actual upper focal tests.  This section
keeps Checked and Jet private while exposing only their semantic replay
theorem. -/

private def jetConst (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (q : ℚ) :
    Jet (padBox b) i.castSucc :=
  Jet.const q

private def jetCoord (b : Fin 4 → ℚ × ℚ) (i j : Fin 4) :
    Jet (padBox b) i.castSucc :=
  Jet.coord (padBox b) i.castSucc j.castSucc

private def focalOffsetJet (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Fin 3 → Jet (padBox b) i.castSucc :=
  let y₀ := jetCoord b i 1
  let y₁ := jetCoord b i 2
  let blend := jetCoord b i 3
  ![y₀, y₁, y₁ +ⱼ (jetConst b i (1 / 128) +ⱼ y₁.neg) *ⱼ blend]

private def normalizedLevelsJet (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Fin 3 → Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  let y := focalOffsetJet b i
  ![r.square.inv +ⱼ y 0, r.inv +ⱼ y 1, r.inv +ⱼ y 2]

noncomputable def replayFocalY (z : Fin 5 → ℝ) : Vec3 :=
  focalOffsets (z 1) (z 2) (z 3)

noncomputable def replayNormalizedLevels (z : Fin 5 → ℝ) : Vec3 :=
  levels (z 0) (replayFocalY z)

private def jetMiddleGap (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  let y₁ := jetCoord b i 2
  let blend := jetCoord b i 3
  let t := r +ⱼ jetConst b i (-1)
  (jetConst b i (1 / 128) +ⱼ y₁.neg) *ⱼ blend *ⱼ t.inv

private def jetRightGap (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  let y := focalOffsetJet b i
  let t := r +ⱼ jetConst b i (-1)
  r.inv +ⱼ (y 2).neg *ⱼ t.inv

private def jetGamma (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  jetConst b i (9 / 4) *ⱼ (jetConst b i 1 +ⱼ r.square *ⱼ r).inv

private def jetC (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  jetGamma b i *ⱼ r *ⱼ (r +ⱼ jetConst b i 1) *ⱼ jetConst b i (1 / 2)

private def jetE (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  jetGamma b i *ⱼ r *ⱼ (r +ⱼ jetConst b i (-1)) *ⱼ jetConst b i (1 / 6)

private def jetFieldOverGap (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  let r2 := r.square
  let num := jetConst b i 2 *ⱼ jetGamma b i *ⱼ r *ⱼ
    (r2 +ⱼ jetConst b i 4 *ⱼ r +ⱼ jetConst b i 1)
  num *ⱼ (jetConst b i 3 *ⱼ (r2 +ⱼ r +ⱼ jetConst b i 1)).inv

private def jetScaledMixture (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  let x := normalizedLevelsJet b i
  let s := jetMiddleGap b i
  let n := x 1
  let q := x 2
  let quad := n.square +ⱼ n *ⱼ q +ⱼ q.square
  let first := jetFieldOverGap b i *ⱼ quad *ⱼ jetConst b i (1 / 2)
  let second := jetE b i *ⱼ (r +ⱼ jetConst b i (-1)) *ⱼ s.square
  let third := jetC b i *ⱼ s *ⱼ (n +ⱼ q)
  s *ⱼ (first +ⱼ second +ⱼ third.neg)

private def jetLowerWeight (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  let x := normalizedLevelsJet b i
  let m := x 0
  let n := x 1
  let q := x 2
  let l := normalizedLeftGapJet b i
  let s := jetMiddleGap b i
  let first := jetC b i *ⱼ l.square *ⱼ (m +ⱼ n)
  let core := jetC b i *ⱼ (m +ⱼ (n +ⱼ n) +ⱼ q) +ⱼ
    jetE b i *ⱼ (r +ⱼ jetConst b i (-1)) *ⱼ (l +ⱼ s) *ⱼ jetConst b i (-3)
  let second := l *ⱼ s *ⱼ core
  (first +ⱼ second +ⱼ (jetScaledMixture b i).neg) *ⱼ jetConst b i (1 / 2)

private def jetUpperWeight (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  let x := normalizedLevelsJet b i
  let n := x 1
  let q := x 2
  let s := jetMiddleGap b i
  let u := jetRightGap b i
  let first := jetC b i *ⱼ u.square *ⱼ (q +ⱼ jetConst b i 1)
  let core := jetC b i *ⱼ (n +ⱼ (q +ⱼ q) +ⱼ jetConst b i 1) +ⱼ
    jetE b i *ⱼ (r +ⱼ jetConst b i (-1)) *ⱼ (s +ⱼ u) *ⱼ jetConst b i (-3)
  let second := u *ⱼ s *ⱼ core
  (first +ⱼ second +ⱼ (jetScaledMixture b i).neg) *ⱼ jetConst b i (1 / 2)

private def jetLongCrossing (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  let x := normalizedLevelsJet b i
  let l := normalizedLeftGapJet b i
  let s := jetMiddleGap b i
  let u := jetRightGap b i
  let sum := x 0 +ⱼ x 1 +ⱼ x 2 +ⱼ jetConst b i 1
  let correction := jetE b i *ⱼ (r +ⱼ jetConst b i (-1)) *ⱼ
    (l +ⱼ (u +ⱼ jetConst b i 2 *ⱼ s)) *ⱼ jetConst b i (-3)
  l *ⱼ u *ⱼ (jetC b i *ⱼ sum +ⱼ correction)

private def jetEndpointField (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  jetGamma b i *ⱼ r *ⱼ (r.square +ⱼ r +ⱼ jetConst b i 1).inv

private def jetEndpointLinear (b : Fin 4 → ℚ × ℚ) (i : Fin 4)
    (v w : Jet (padBox b) i.castSucc) : Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  let first := r *ⱼ (r +ⱼ jetConst b i 2) *ⱼ v
  let second := (jetConst b i 2 *ⱼ r +ⱼ jetConst b i 1) *ⱼ w
  first +ⱼ second

private def jetLowerTiltFactor (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  let x := normalizedLevelsJet b i
  let y := focalOffsetJet b i
  let t := r +ⱼ jetConst b i (-1)
  let gap := r.square.inv +ⱼ (y 2 +ⱼ (y 0).neg) *ⱼ t.inv
  jetEndpointField b i *ⱼ gap *ⱼ jetEndpointLinear b i (x 0) (x 2)

private def jetUpperTiltFactor (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  let x := normalizedLevelsJet b i
  let t := r +ⱼ jetConst b i (-1)
  let gap := r.inv +ⱼ (focalOffsetJet b i 1).neg *ⱼ t.inv
  jetEndpointField b i *ⱼ gap *ⱼ jetEndpointLinear b i (x 1) (jetConst b i 1) *ⱼ r

private def jetResidual (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  let t := r +ⱼ jetConst b i (-1)
  let y := focalOffsetJet b i
  let lower := jetLowerWeight b i
  let upper := jetUpperWeight b i
  let lowerTilt := jetLowerTiltFactor b i
  let upperTilt := jetUpperTiltFactor b i
  let first := upper *ⱼ lowerTilt *ⱼ (r *ⱼ (y 0 *ⱼ t.inv) +ⱼ (y 2).neg *ⱼ t.inv)
  let second := lower *ⱼ upperTilt *ⱼ (y 1 *ⱼ t.inv)
  (first +ⱼ second.neg) *ⱼ jetConst b i 2

private def jetScalarMinus (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Jet (padBox b) i.castSucc :=
  let p := jetLowerWeight b i +ⱼ jetUpperWeight b i
  jetLongCrossing b i *ⱼ p +ⱼ jetResidual b i *ⱼ jetConst b i (-4)

private def jetScalarPlus (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Jet (padBox b) i.castSucc :=
  let p := jetLowerWeight b i +ⱼ jetUpperWeight b i
  jetLongCrossing b i *ⱼ p +ⱼ jetResidual b i *ⱼ jetConst b i 4

noncomputable def replayP0 (z : Fin 5 → ℝ) : ℝ :=
  lowerWeight (z 0) (replayFocalY z)

noncomputable def replayP2 (z : Fin 5 → ℝ) : ℝ :=
  upperWeight (z 0) (replayFocalY z)

noncomputable def replayLong (z : Fin 5 → ℝ) : ℝ :=
  longCrossing (z 0) (replayFocalY z)

noncomputable def replayResidual (z : Fin 5 → ℝ) : ℝ :=
  WuCubicHellingerMatrix.residual (z 0) (replayFocalY z)

noncomputable def replayScalarMinus (z : Fin 5 → ℝ) : ℝ :=
  replayLong z * (replayP0 z + replayP2 z) - 4 * replayResidual z

noncomputable def replayScalarPlus (z : Fin 5 → ℝ) : ℝ :=
  replayLong z * (replayP0 z + replayP2 z) + 4 * replayResidual z

/-- The minus signed replay matrix on the same focal variables. -/
noncomputable def replayMatrix (z : Fin 5 → ℝ) :
    WuCubicHellingerMatrix.Mat3 :=
  WuCubicHellingerMatrix.signedMatrix (-1) (z 0) (replayFocalY z)

theorem replayMatrix_isSymm (z : Fin 5 → ℝ) :
    (replayMatrix z).IsSymm := by
  simpa only [replayMatrix] using
    WuCubicHellingerMatrix.signedMatrix_isSymm (-1) (z 0) (replayFocalY z)

theorem replayMatrix_interpretation (z : Fin 5 → ℝ) :
    replayMatrix z =
      WuCubicHellingerMatrix.signedMatrix (-1) (z 0) (replayFocalY z) := rfl

theorem replayMatrix_entry (z : Fin 5 → ℝ) (i j : Fin 3) :
    replayMatrix z i j =
      4 * WuCubicHellingerMatrix.weightSum (z 0) (replayFocalY z) ^ 3 *
        (WuCubicHellingerMatrix.occupationMatrix (z 0) (replayFocalY z) i j -
          WuCubicHellingerMatrix.debitMatrix i j) -
        WuCubicHellingerMatrix.signedRow (-1) (z 0) (replayFocalY z) i *
          WuCubicHellingerMatrix.signedRow (-1) (z 0) (replayFocalY z) j := rfl

-- Rewrite only the value projection. Unfolding entire jets also expands both
-- derivative expressions before the simplifier reaches a projection.
private theorem Jet.add_value (z : Fin 5 → ℝ) (a b : Jet box i) :
    value z (Checked.expr (a +ⱼ b).val) =
      value z (Checked.expr a.val) + value z (Checked.expr b.val) := rfl

private theorem Jet.neg_value (z : Fin 5 → ℝ) (a : Jet box i) :
    value z (Checked.expr a.neg.val) = -value z (Checked.expr a.val) := rfl

private theorem Jet.mul_value (z : Fin 5 → ℝ) (a b : Jet box i) :
    value z (Checked.expr (a *ⱼ b).val) =
      value z (Checked.expr a.val) * value z (Checked.expr b.val) := rfl

private theorem Jet.inv_value (z : Fin 5 → ℝ) (a : Jet box i) :
    value z (Checked.expr a.inv.val) = (value z (Checked.expr a.val))⁻¹ := by
  exact (eval_recip z a.val).trans (one_div _)

private theorem Jet.square_value (z : Fin 5 → ℝ) (a : Jet box i) :
    value z (Checked.expr a.square.val) = value z (Checked.expr a.val) ^ 2 := rfl

private theorem Jet.const_value (z : Fin 5 → ℝ) (q : ℚ) :
    value z (Checked.expr (Jet.const (box := box) (i := i) q).val) = (q : ℝ) := rfl

private theorem Jet.coord_value (z : Fin 5 → ℝ) (j : Fin 5) :
    value z (Checked.expr (Jet.coord box i j).val) = z j := rfl

private theorem coord_cast_zero : (0 : Fin 4).castSucc = (0 : Fin 5) := rfl
private theorem coord_cast_one : (1 : Fin 4).castSucc = (1 : Fin 5) := rfl
private theorem coord_cast_two : (2 : Fin 4).castSucc = (2 : Fin 5) := rfl
private theorem coord_cast_three : (3 : Fin 4).castSucc = (3 : Fin 5) := rfl

private theorem focalOffsetJet_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4)
    (z : Fin 5 → ℝ) (k : Fin 3) :
    value z (Checked.expr (focalOffsetJet b i k).val) = replayFocalY z k := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> decide
  rcases hk with rfl | rfl | rfl <;>
    simp only [focalOffsetJet, replayFocalY, focalOffsets, jetCoord, jetConst,
      Jet.coord_value, Jet.const_value, Jet.add_value, Jet.mul_value, Jet.neg_value,
      coord_cast_one, coord_cast_two, coord_cast_three, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat, sub_eq_add_neg, _root_.Matrix.cons_val_zero, _root_.Matrix.cons_val_one,
      _root_.Matrix.cons_val_two, _root_.Matrix.head_cons, _root_.Matrix.tail_cons]

private theorem normalizedLevelsJet_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4)
    (z : Fin 5 → ℝ) (k : Fin 3) :
    value z (Checked.expr (normalizedLevelsJet b i k).val) =
      replayNormalizedLevels z k := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> decide
  rcases hk with rfl | rfl | rfl <;>
    simp only [normalizedLevelsJet, jetCoord, Jet.add_value, Jet.inv_value, Jet.square_value,
      Jet.coord_value, coord_cast_zero, focalOffsetJet_value, replayNormalizedLevels, levels,
      gibbsLevels, cast_zero, cast_one, cast_two, _root_.Matrix.cons_val_zero,
      _root_.Matrix.cons_val_one, _root_.Matrix.cons_val_two, _root_.Matrix.head_cons,
      _root_.Matrix.tail_cons]

private theorem jetLeftGap_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    value z (Checked.expr (normalizedLeftGapJet b i).val) = leftGap (z 0) (replayFocalY z) := by
  simp only [normalizedLeftGapJet, Jet.add_value, Jet.mul_value, Jet.neg_value, Jet.inv_value,
    Jet.square_value, Jet.coord_value, Jet.const_value, leftGap, replayFocalY, focalOffsets,
    _root_.Matrix.cons_val_zero, _root_.Matrix.cons_val_one, Rat.cast_neg, Rat.cast_one,
    sub_eq_add_neg, div_eq_mul_inv]

private theorem jetMiddleGap_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    value z (Checked.expr (jetMiddleGap b i).val) =
      middleGap (z 0) (replayFocalY z) := by
  simp only [jetMiddleGap, jetCoord, jetConst, Jet.add_value, Jet.neg_value, Jet.mul_value,
    Jet.inv_value, Jet.coord_value, Jet.const_value, coord_cast_zero, coord_cast_two,
    coord_cast_three, middleGap, replayFocalY, focalOffsets, _root_.Matrix.cons_val_zero,
    _root_.Matrix.cons_val_one, _root_.Matrix.cons_val_two, _root_.Matrix.head_cons,
    _root_.Matrix.tail_cons, Rat.cast_neg, Rat.cast_one, sub_eq_add_neg, div_eq_mul_inv]
  ring

private theorem jetRightGap_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    value z (Checked.expr (jetRightGap b i).val) =
      rightGap (z 0) (replayFocalY z) := by
  simp only [jetRightGap, jetCoord, jetConst, Jet.add_value, Jet.neg_value, Jet.mul_value,
    Jet.inv_value, Jet.coord_value, Jet.const_value, coord_cast_zero, focalOffsetJet_value,
    rightGap, Rat.cast_neg, Rat.cast_one, sub_eq_add_neg, div_eq_mul_inv] <;> ring

private theorem jetGamma_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    value z (Checked.expr (jetGamma b i).val) = gamma (z 0) := by
  simp only [jetGamma, jetCoord, jetConst, Jet.add_value, Jet.mul_value, Jet.square_value,
    Jet.inv_value, Jet.coord_value, Jet.const_value, coord_cast_zero, gamma, Rat.cast_div,
    Rat.cast_mul, Rat.cast_inv, Rat.cast_one, Rat.cast_ofNat, div_eq_mul_inv, mul_inv, pow_succ] <;>
    ring

private theorem jetFieldOverGap_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    value z (Checked.expr (jetFieldOverGap b i).val) = fieldOverGap (z 0) := by
  simp only [jetFieldOverGap, jetGamma_value, jetCoord, jetConst, Jet.add_value, Jet.mul_value,
    Jet.square_value, Jet.inv_value, Jet.coord_value, Jet.const_value, coord_cast_zero,
    fieldOverGap, Rat.cast_one, Rat.cast_ofNat, div_eq_mul_inv]

private theorem jetC_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    value z (Checked.expr (jetC b i).val) = c (z 0) := by
  simp only [jetC, jetGamma_value, jetCoord, jetConst, Jet.add_value, Jet.mul_value,
    Jet.coord_value, Jet.const_value, coord_cast_zero, c, Rat.cast_div, Rat.cast_mul,
    Rat.cast_inv, Rat.cast_one, Rat.cast_ofNat, div_eq_mul_inv, one_mul]

private theorem jetE_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    value z (Checked.expr (jetE b i).val) = e (z 0) := by
  simp only [jetE, jetGamma_value, jetCoord, jetConst, Jet.add_value, Jet.mul_value,
    Jet.coord_value, Jet.const_value, coord_cast_zero, e, Rat.cast_div, Rat.cast_mul,
    Rat.cast_inv, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat, sub_eq_add_neg, div_eq_mul_inv,
    one_mul]

private theorem jetScaledMixture_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    value z (Checked.expr (jetScaledMixture b i).val) = scaledMixture (z 0) (replayFocalY z) := by
  simp only [jetScaledMixture, jetFieldOverGap_value, jetC_value, jetE_value,
    normalizedLevelsJet_value, replayNormalizedLevels, jetMiddleGap_value, jetCoord, jetConst,
    Jet.add_value, Jet.mul_value, Jet.neg_value, Jet.square_value, Jet.coord_value,
    Jet.const_value, coord_cast_zero, scaledMixture, Rat.cast_div, Rat.cast_mul, Rat.cast_inv,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat, sub_eq_add_neg, div_eq_mul_inv, one_mul]

private theorem jetLowerWeight_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    value z (Checked.expr (jetLowerWeight b i).val) = replayP0 z := by
  simp only [jetLowerWeight, jetC_value, jetE_value, normalizedLevelsJet_value,
    replayNormalizedLevels, jetLeftGap_value, jetMiddleGap_value, jetScaledMixture_value,
    jetCoord, jetConst, Jet.add_value, Jet.mul_value, Jet.neg_value, Jet.square_value,
    Jet.coord_value, Jet.const_value, coord_cast_zero, replayP0, lowerWeight, Rat.cast_div,
    Rat.cast_mul, Rat.cast_inv, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat, sub_eq_add_neg,
    div_eq_mul_inv, one_mul] <;> ring

private theorem jetUpperWeight_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    value z (Checked.expr (jetUpperWeight b i).val) = replayP2 z := by
  simp only [jetUpperWeight, jetC_value, jetE_value, normalizedLevelsJet_value,
    replayNormalizedLevels, jetRightGap_value, jetMiddleGap_value, jetScaledMixture_value,
    jetCoord, jetConst, Jet.add_value, Jet.mul_value, Jet.neg_value, Jet.square_value,
    Jet.coord_value, Jet.const_value, coord_cast_zero, replayP2, upperWeight, Rat.cast_div,
    Rat.cast_mul, Rat.cast_inv, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat, sub_eq_add_neg,
    div_eq_mul_inv, one_mul] <;> ring

private theorem jetLongCrossing_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    value z (Checked.expr (jetLongCrossing b i).val) = replayLong z := by
  simp only [jetLongCrossing, jetC_value, jetE_value, normalizedLevelsJet_value,
    replayNormalizedLevels, jetLeftGap_value, jetMiddleGap_value, jetRightGap_value,
    jetCoord, jetConst, Jet.add_value, Jet.mul_value, Jet.coord_value, Jet.const_value,
    coord_cast_zero, replayLong, longCrossing, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat,
    sub_eq_add_neg] <;> ring

private theorem jetEndpointLinear_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ)
    (v w : Jet (padBox b) i.castSucc) :
    value z (Checked.expr (jetEndpointLinear b i v w).val) =
      endpointLinear (z 0) (value z (Checked.expr v.val)) (value z (Checked.expr w.val)) := by
  simp only [jetEndpointLinear, jetCoord, jetConst, Jet.add_value, Jet.mul_value,
    Jet.coord_value, Jet.const_value, coord_cast_zero, endpointLinear, Rat.cast_one, Rat.cast_ofNat]

private theorem jetEndpointField_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    value z (Checked.expr (jetEndpointField b i).val) = endpointField (z 0) := by
  simp only [jetEndpointField, jetGamma_value, jetCoord, jetConst, Jet.add_value, Jet.mul_value,
    Jet.square_value, Jet.inv_value, Jet.coord_value, Jet.const_value, coord_cast_zero,
    endpointField, Rat.cast_one, div_eq_mul_inv]

private theorem jetLowerTiltFactor_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    value z (Checked.expr (jetLowerTiltFactor b i).val) = lowerTiltFactor (z 0) (replayFocalY z) := by
  simp only [jetLowerTiltFactor, jetEndpointField_value, jetEndpointLinear_value,
    normalizedLevelsJet_value, replayNormalizedLevels, focalOffsetJet_value, jetCoord, jetConst,
    Jet.add_value, Jet.mul_value, Jet.neg_value, Jet.inv_value, Jet.square_value, Jet.coord_value,
    Jet.const_value, coord_cast_zero, lowerTiltFactor, Rat.cast_neg, Rat.cast_one,
    sub_eq_add_neg, div_eq_mul_inv]

private theorem jetUpperTiltFactor_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    value z (Checked.expr (jetUpperTiltFactor b i).val) = upperTiltFactor (z 0) (replayFocalY z) := by
  simp only [jetUpperTiltFactor, jetEndpointField_value, jetEndpointLinear_value,
    normalizedLevelsJet_value, replayNormalizedLevels, focalOffsetJet_value, jetCoord, jetConst,
    Jet.add_value, Jet.mul_value, Jet.neg_value, Jet.inv_value, Jet.coord_value, Jet.const_value,
    coord_cast_zero, upperTiltFactor, Rat.cast_neg, Rat.cast_one, sub_eq_add_neg, div_eq_mul_inv] <;>
    ring

private theorem jetResidual_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    value z (Checked.expr (jetResidual b i).val) = replayResidual z := by
  simp only [jetResidual, jetLowerTiltFactor_value, jetUpperTiltFactor_value,
    jetLowerWeight_value, jetUpperWeight_value, focalOffsetJet_value, jetCoord, jetConst,
    Jet.add_value, Jet.mul_value, Jet.neg_value, Jet.inv_value, Jet.coord_value, Jet.const_value,
    coord_cast_zero, replayResidual, WuCubicHellingerMatrix.residual, replayP0, replayP2,
    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat, sub_eq_add_neg, div_eq_mul_inv] <;> ring

private theorem jetScalar_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    value z (Checked.expr (jetLowerWeight b i).val) = replayP0 z ∧
    value z (Checked.expr (jetUpperWeight b i).val) = replayP2 z ∧
    value z (Checked.expr (jetLongCrossing b i).val) = replayLong z ∧
    value z (Checked.expr (jetResidual b i).val) = replayResidual z ∧
    value z (Checked.expr (jetScalarMinus b i).val) = replayScalarMinus z ∧
    value z (Checked.expr (jetScalarPlus b i).val) = replayScalarPlus z := by
  refine ⟨jetLowerWeight_value b i z, jetUpperWeight_value b i z,
    jetLongCrossing_value b i z, jetResidual_value b i z, ?_, ?_⟩ <;>
    simp only [jetScalarMinus, jetScalarPlus, jetConst, Jet.add_value, Jet.mul_value,
      Jet.const_value, jetLowerWeight_value, jetUpperWeight_value, jetLongCrossing_value,
      jetResidual_value, replayScalarMinus, replayScalarPlus, Rat.cast_neg, Rat.cast_ofNat] <;>
    ring

/-- The two scalar tests in verify.py have their exact real interpretation
after evaluation of the rational expression tree. -/
theorem scalar_replay_semantics (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (z : Fin 5 → ℝ) :
    let a := jetScalarMinus b i
    let c := jetScalarPlus b i
    value z (Checked.expr a.val) = replayScalarMinus z ∧
      value z (Checked.expr c.val) = replayScalarPlus z := by
  intro a c
  obtain ⟨_, _, _, _, hm, hp⟩ := jetScalar_value b i z
  exact ⟨hm, hp⟩

private def jetBasis (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Fin 3 → Fin 3 → Jet (padBox b) i.castSucc :=
  let q := jetConst b i
  ![![q 1, q 0, q 0], ![q (1 / 2), q 1, q (-1)], ![q (1 / 2), q 1, q 1]]

private theorem jetBasis_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4)
    (z : Fin 5 → ℝ) (j k : Fin 3) :
    value z (Checked.expr (jetBasis b i j k).val) = WuCubicHellingerMatrix.basis j k := by
  fin_cases j <;> fin_cases k <;>
    norm_num [jetBasis, jetConst, Jet.const_value, WuCubicHellingerMatrix.basis,
      Rat.cast_div, Rat.cast_neg, Rat.cast_zero, Rat.cast_one, Rat.cast_ofNat,
      _root_.Matrix.cons_val_zero, _root_.Matrix.cons_val_one, _root_.Matrix.cons_val_two,
      _root_.Matrix.head_cons, _root_.Matrix.tail_cons]

private def jetEdgeRow (b : Fin 4 → ℚ × ℚ) (i : Fin 4) :
    Fin 4 → Fin 3 → Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  let B := jetBasis b i
  ![fun j => r *ⱼ B 0 j +ⱼ (B 1 j).neg, fun j => r *ⱼ B 0 j +ⱼ (B 2 j).neg,
    fun j => r *ⱼ B 1 j, fun j => r *ⱼ B 2 j]

private theorem jetEdgeRow_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4)
    (z : Fin 5 → ℝ) (k : Fin 4) (j : Fin 3) :
    value z (Checked.expr (jetEdgeRow b i k j).val) = edgeRows (z 0) k j := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by fin_cases k <;> decide
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [jetEdgeRow, edgeRows, jetBasis_value, jetCoord, Jet.coord_value,
      coord_cast_zero, Jet.add_value, Jet.mul_value, Jet.neg_value, sub_eq_add_neg,
      _root_.Matrix.cons_val_zero, _root_.Matrix.cons_val_one, _root_.Matrix.cons_val_two,
      _root_.Matrix.cons_val_three, _root_.Matrix.head_cons, _root_.Matrix.tail_cons]

private def jetMassWeight (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (k : Fin 3) :
    Jet (padBox b) i.castSucc :=
  let r := jetCoord b i 0
  let g : Fin 3 → Jet (padBox b) i.castSucc := ![r.square.inv, r.inv, r.inv]
  let y := focalOffsetJet b i k
  let three := jetConst b i 3
  three *ⱼ (g k).square +ⱼ y *ⱼ (three *ⱼ g k +ⱼ y)

private theorem jetMassWeight_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4)
    (z : Fin 5 → ℝ) (k : Fin 3) :
    value z (Checked.expr (jetMassWeight b i k).val) = massWeights (z 0) (replayFocalY z) k := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> decide
  rcases hk with rfl | rfl | rfl <;>
    simp only [jetMassWeight, massWeights, jetCoord, jetConst, focalOffsetJet_value,
      Jet.coord_value, Jet.const_value, Jet.add_value, Jet.mul_value, Jet.inv_value,
      Jet.square_value, coord_cast_zero, Rat.cast_ofNat, gibbsLevels, cast_zero, cast_one,
      cast_two, _root_.Matrix.cons_val_zero, _root_.Matrix.cons_val_one,
      _root_.Matrix.cons_val_two, _root_.Matrix.head_cons, _root_.Matrix.tail_cons]

private def jetOccupationEntry (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (j k : Fin 3) :
    Jet (padBox b) i.castSucc :=
  let q := jetConst b i
  let r := jetCoord b i 0
  let x := normalizedLevelsJet b i
  let y := focalOffsetJet b i
  let B := jetBasis b i
  let edge := fun l w => w *ⱼ jetEdgeRow b i l j *ⱼ jetEdgeRow b i l k
  let edges := edge 0 (r *ⱼ x 0 +ⱼ x 1) +ⱼ edge 1 (r *ⱼ x 0 +ⱼ x 2) +ⱼ
    edge 2 (r *ⱼ x 1 +ⱼ q 1) +ⱼ edge 3 (r *ⱼ x 2 +ⱼ q 1)
  let entropy := fun l => (x l +ⱼ q (1 / 3) *ⱼ (y l).square) *ⱼ B l j *ⱼ B l k
  let mass := jetMassWeight b i
  let massDelta := y 0 *ⱼ mass 0 +ⱼ y 1 *ⱼ mass 1 +ⱼ y 2 *ⱼ mass 2
  let row := fun l => mass 0 *ⱼ B 0 l +ⱼ mass 1 *ⱼ B 1 l +ⱼ mass 2 *ⱼ B 2 l
  let total := (q 1 +ⱼ (r.square *ⱼ r).inv).square
  let massFactor := (q 1 +ⱼ (massDelta *ⱼ (q 3 *ⱼ total).inv).neg) *ⱼ (q 4 *ⱼ total).inv
  jetGamma b i *ⱼ edges +ⱼ (q (9 / 4) *ⱼ (entropy 0 +ⱼ entropy 1 +ⱼ entropy 2)).neg +ⱼ
    massFactor *ⱼ row j *ⱼ row k

private theorem jetOccupationEntry_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4)
    (z : Fin 5 → ℝ) (j k : Fin 3) :
    value z (Checked.expr (jetOccupationEntry b i j k).val) =
      WuCubicHellingerMatrix.occupationMatrix (z 0) (replayFocalY z) j k := by
  simp only [jetOccupationEntry, jetConst, jetCoord, Jet.const_value, Jet.coord_value,
    coord_cast_zero, Jet.add_value, Jet.mul_value, Jet.neg_value, Jet.square_value,
    Jet.inv_value, jetBasis_value, jetEdgeRow_value, jetGamma_value, jetMassWeight_value,
    normalizedLevelsJet_value, focalOffsetJet_value, replayNormalizedLevels,
    WuCubicHellingerMatrix.occupationMatrix, edgeWeights, entropyWeights, massChange,
    massRow, gibbsMass, levels, Fin.sum_univ_three, Fin.sum_univ_four,
    _root_.Matrix.cons_val_zero, _root_.Matrix.cons_val_one, _root_.Matrix.cons_val_two,
    _root_.Matrix.cons_val_three, _root_.Matrix.head_cons, _root_.Matrix.tail_cons,
    Rat.cast_one, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_inv, sub_eq_add_neg, div_eq_mul_inv,
    pow_three, pow_two, add_assoc, mul_assoc]

private def jetDebitEntry (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (j k : Fin 3) :
    Jet (padBox b) i.castSucc :=
  let debit : Fin 3 → Fin 3 → ℚ :=
    ![![3 / 128, 1 / 64, 3 / 2], ![1 / 64, 1 / 32, 0], ![3 / 2, 0, 1 / 32]]
  jetConst b i (debit j k)

private theorem jetDebitEntry_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4)
    (z : Fin 5 → ℝ) (j k : Fin 3) :
    value z (Checked.expr (jetDebitEntry b i j k).val) = WuCubicHellingerMatrix.debitMatrix j k := by
  fin_cases j <;> fin_cases k <;>
    norm_num [jetDebitEntry, jetConst, Jet.const_value, WuCubicHellingerMatrix.debitMatrix,
      WuCubicHellingerMatrix.basis, Fin.sum_univ_three, Rat.cast_div, Rat.cast_zero,
      Rat.cast_one, Rat.cast_ofNat, _root_.Matrix.cons_val_zero,
      _root_.Matrix.cons_val_one, _root_.Matrix.cons_val_two, _root_.Matrix.head_cons,
      _root_.Matrix.tail_cons]

private def jetSignedRow (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (sign : ℚ) (j : Fin 3) :
    Jet (padBox b) i.castSucc :=
  let p₀ := jetLowerWeight b i
  let p₂ := jetUpperWeight b i
  let v₀ := jetLowerTiltFactor b i *ⱼ jetEdgeRow b i 1 j
  let v₂ := jetUpperTiltFactor b i *ⱼ jetBasis b i 1 j
  (p₀ +ⱼ p₂) *ⱼ (v₀ +ⱼ v₂) +ⱼ
    jetConst b i sign *ⱼ ((p₂ *ⱼ v₀ +ⱼ (p₀ *ⱼ v₂).neg) *ⱼ jetConst b i (1 / 3))

private theorem jetSignedRow_value (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (sign : ℚ)
    (z : Fin 5 → ℝ) (j : Fin 3) :
    value z (Checked.expr (jetSignedRow b i sign j).val) =
      WuCubicHellingerMatrix.signedRow (sign : ℝ) (z 0) (replayFocalY z) j := by
  simp only [jetSignedRow, jetConst, Jet.const_value, Jet.add_value, Jet.mul_value,
    Jet.neg_value, jetLowerTiltFactor_value, jetUpperTiltFactor_value, jetEdgeRow_value,
    jetBasis_value, jetLowerWeight_value, jetUpperWeight_value, replayP0, replayP2,
    WuCubicHellingerMatrix.signedRow, WuCubicHellingerMatrix.weightSum,
    WuCubicHellingerMatrix.lowerTilt, WuCubicHellingerMatrix.upperTilt,
    Rat.cast_inv, Rat.cast_ofNat, sub_eq_add_neg, div_eq_mul_inv, one_mul]

-- The order of ENTRIES in verify.py.
private def upperEntryIndices : Fin 6 → Fin 3 × Fin 3 :=
  ![(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)]

private def jetSignedMatrixEntry (b : Fin 4 → ℚ × ℚ) (i : Fin 4) (sign : ℚ) (n : Fin 6) :
    Jet (padBox b) i.castSucc :=
  let j := (upperEntryIndices n).1
  let k := (upperEntryIndices n).2
  let p := jetLowerWeight b i +ⱼ jetUpperWeight b i
  let w := jetSignedRow b i sign
  jetConst b i 4 *ⱼ (p.square *ⱼ p) *ⱼ
    (jetOccupationEntry b i j k +ⱼ (jetDebitEntry b i j k).neg) +ⱼ (w j *ⱼ w k).neg

/-- Pointwise value of each upper entry, with `sign = -1` or `sign = 1`
giving the corresponding matrix in `verify.py`. -/
theorem signed_matrix_replay_semantics (b : Fin 4 → ℚ × ℚ) (i : Fin 4)
    (sign : ℚ) (z : Fin 5 → ℝ) (n : Fin 6) :
    value z (Checked.expr (jetSignedMatrixEntry b i sign n).val) =
      WuCubicHellingerMatrix.signedMatrix (sign : ℝ) (z 0) (replayFocalY z)
        (upperEntryIndices n).1 (upperEntryIndices n).2 := by
  simp only [jetSignedMatrixEntry, jetConst, Jet.const_value, Jet.add_value, Jet.mul_value,
    Jet.neg_value, Jet.square_value, jetLowerWeight_value, jetUpperWeight_value,
    jetOccupationEntry_value, jetDebitEntry_value, jetSignedRow_value, replayP0, replayP2,
    WuCubicHellingerMatrix.signedMatrix, WuCubicHellingerMatrix.weightSum,
    Rat.cast_ofNat, pow_three, pow_two, sub_eq_add_neg, mul_assoc]

end D5.S3.Quantum.Semigroups.WuCubicUpperCornerJet
