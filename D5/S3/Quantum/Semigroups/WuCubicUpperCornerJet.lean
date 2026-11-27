import D5.S3.Quantum.Semigroups.WuCubicGibbsCheckedCoverCompact
import D5.S3.Quantum.Semigroups.WuCubicThermalDerivatives
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

-- The first four intervals are carried over with their original rational
-- endpoints. The fifth input has the closed interval [0, 0].
private def padBox (b : Fin 4 → ℚ × ℚ) : Fin 5 → ℚ × ℚ :=
  Fin.lastCases (0, 0) b

-- This is the factor left in cuts in verify.py.
private def normalizedLeftGapJet (b : Fin 4 → ℚ × ℚ) (i : Fin 4) : Jet (padBox b) i.castSucc :=
  let r := Jet.coord (padBox b) i.castSucc 0
  let y₀ := Jet.coord (padBox b) i.castSucc 1
  let y₁ := Jet.coord (padBox b) i.castSucc 2
  let t := r.add (Jet.const (-1))
  r.square.inv.add ((y₁.add y₀.neg).mul t.inv)

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

end D5.S3.Quantum.Semigroups.WuCubicUpperCornerJet
