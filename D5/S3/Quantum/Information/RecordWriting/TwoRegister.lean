/- GID: D5/S3/Quantum/Information/RecordWriting/TwoRegister
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/RecordWriting/TwoRegister
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp bath-variation cost of recording on exactly two classical binary registers. -/

import D5.S3.TotalVariation.Pinsker
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Wonyong Chung, *The thermodynamic budget of objectivity*, arXiv:2611.34909v1,
Section VIII after Eq. (7), asks about the collective speed limit with fragment-fragment gates.
Here the model is the finite scheduled classical process on two binary registers, with uniform
initial conditional laws, reversible permutations and local partial resets. The cost counts
bath endpoint total variations. The bound concerns this finite model, whose state space has
exactly four points. Spectators, feedback, coherent gates and continuous thermodynamic cost
are outside its scope. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Information.RecordWriting.TwoRegister

open D5.S3.TotalVariation.Pinsker (totalVariation)

abbrev Point := Bool × Bool
abbrev Mass := Point → ℝ

/-- A finite normalized nonnegative real mass function. -/
structure Law (α : Type) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  normalized : ∑ x, mass x = 1

/-- The signs are +1 on `false` and -1 on `true`. -/
def sign (x : Bool) : ℝ := if x then -1 else 1

/-- The three nonconstant Walsh moments of a signed mass on the two-bit cube. -/
def momentA (p : Mass) : ℝ := p (false, false) + p (false, true) - p (true, false) - p (true, true)
def momentB (p : Mass) : ℝ := p (false, false) + p (true, false) - p (false, true) - p (true, true)
def momentC (p : Mass) : ℝ := p (false, false) + p (true, true) - p (false, true) - p (true, false)

private theorem moment_formulas (p : Mass) :
    momentA p = (∑ z : Point, p z * sign z.1) ∧
    momentB p = (∑ z : Point, p z * sign z.2) ∧
    momentC p = ∑ z : Point, p z * (sign z.1 * sign z.2) := by
  constructor
  · simp [momentA, Fintype.sum_prod_type, sign]
    ring
  constructor
  · simp [momentB, Fintype.sum_prod_type, sign]
    ring
  · simp [momentC, Fintype.sum_prod_type, sign]
    ring

/-- Sum of the two largest absolute nonconstant Walsh moments. -/
def potential (p : Mass) : ℝ :=
  max (|momentA p| + |momentB p|)
    (max (|momentA p| + |momentC p|) (|momentB p| + |momentC p|))

private theorem max_abs_add_sub (x y : ℝ) : max |x + y| |x - y| = |x| + |y| := by
  apply le_antisymm
  · exact max_le (abs_add_le _ _) (abs_sub _ _)
  · rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hx, abs_of_nonneg hy]
      exact le_trans (le_abs_self _) (le_max_left _ _)
    · rw [abs_of_nonneg hx, abs_of_nonpos hy]
      exact le_trans (le_of_eq (by ring : x + -y = x - y))
        ((le_abs_self _).trans (le_max_right _ _))
    · rw [abs_of_nonpos hx, abs_of_nonneg hy]
      exact le_trans (le_of_eq (by ring : -x + y = -(x - y)))
        ((neg_le_abs _).trans (le_max_right _ _))
    · rw [abs_of_nonpos hx, abs_of_nonpos hy]
      exact le_trans (le_of_eq (by ring : -x + -y = -(x + y)))
        ((neg_le_abs _).trans (le_max_left _ _))

private theorem abs_double (x y : ℝ) : |2 * (x - y)| = 2 * |x - y| := by
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

/-- The potential is the least upper bound of twice all pairwise mass distances. -/
theorem potential_le_iff (p : Mass) (K : ℝ) :
    potential p ≤ K ↔ ∀ s t : Point, 2 * |p s - p t| ≤ K := by
  have hab₁ : momentA p + momentB p = 2 * (p (false, false) - p (true, true)) := by
    unfold momentA momentB; ring
  have hab₂ : momentA p - momentB p = 2 * (p (false, true) - p (true, false)) := by
    unfold momentA momentB; ring
  have hac₁ : momentA p + momentC p = 2 * (p (false, false) - p (true, false)) := by
    unfold momentA momentC; ring
  have hac₂ : momentA p - momentC p = 2 * (p (false, true) - p (true, true)) := by
    unfold momentA momentC; ring
  have hbc₁ : momentB p + momentC p = 2 * (p (false, false) - p (false, true)) := by
    unfold momentB momentC; ring
  have hbc₂ : momentB p - momentC p = 2 * (p (true, false) - p (true, true)) := by
    unfold momentB momentC; ring
  simp only [potential, ← max_abs_add_sub, hab₁, hab₂, hac₁, hac₂, hbc₁, hbc₂,
    abs_double, max_le_iff]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, ⟨⟨h₃, h₄⟩, ⟨h₅, h₆⟩⟩⟩ ⟨x, y⟩ ⟨u, v⟩
    have hK : 0 ≤ K := (by positivity : 0 ≤ 2 * |p (false, false) - p (true, true)|).trans h₁
    cases x <;> cases y <;> cases u <;> cases v <;>
      first | assumption | simpa only [sub_self, abs_zero, mul_zero] using hK |
        (rwa [abs_sub_comm])
  · intro h
    exact ⟨⟨h _ _, h _ _⟩, ⟨⟨h _ _, h _ _⟩, ⟨h _ _, h _ _⟩⟩⟩

/-- The greatest and least of the four masses. -/
def maxMass (p : Mass) : ℝ := Finset.univ.sup' Finset.univ_nonempty p
def minMass (p : Mass) : ℝ := Finset.univ.inf' Finset.univ_nonempty p

/-- The Walsh potential equals twice the range of the mass function. -/
theorem potential_eq_twice_range (p : Mass) : potential p = 2 * (maxMass p - minMass p) := by
  apply le_antisymm
  · apply (potential_le_iff p _).mpr
    intro s t
    have hs := Finset.le_sup' p (Finset.mem_univ s)
    have ht := Finset.le_sup' p (Finset.mem_univ t)
    have hs' := Finset.inf'_le p (Finset.mem_univ s)
    have ht' := Finset.inf'_le p (Finset.mem_univ t)
    change p s ≤ maxMass p at hs
    change p t ≤ maxMass p at ht
    change minMass p ≤ p s at hs'
    change minMass p ≤ p t at ht'
    have h : |p s - p t| ≤ maxMass p - minMass p := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  · obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty p
    obtain ⟨t, _, ht⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty p
    change maxMass p = p s at hs
    change minMass p = p t at ht
    rw [hs, ht]
    have h := (potential_le_iff p _).mp le_rfl s t
    linarith [le_abs_self (p s - p t)]

/-- Relabel the four masses by a reversible permutation. -/
def permute (e : Equiv.Perm Point) (p : Law Point) : Law Point where
  mass z := p.mass (e.symm z)
  nonneg _z := p.nonneg _
  normalized := (Equiv.sum_comp e.symm p.mass).trans p.normalized

/-- An arbitrary reversible permutation of the four masses costs no potential. -/
theorem potential_permute (e : Equiv.Perm Point) (p : Law Point) :
    potential (permute e p).mass = potential p.mass := by
  apply le_antisymm
  · apply (potential_le_iff _ _).mpr
    intro s t
    exact (potential_le_iff p.mass _).mp le_rfl (e.symm s) (e.symm t)
  · apply (potential_le_iff _ _).mpr
    intro s t
    have h := (potential_le_iff (permute e p).mass _).mp le_rfl (e s) (e t)
    simpa [permute] using h

/-- The uniform law of two binary registers. -/
def uniform : Law Point where
  mass _ := 1 / 4
  nonneg _ := by norm_num
  normalized := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

private theorem potential_uniform : potential uniform.mass = 0 := by
  norm_num [potential, momentA, momentB, momentC, uniform]

/-- A local bath has a mixing weight in `[0,1]` and a binary reset law. -/
structure Bath where
  weight : ℝ
  weight_nonneg : 0 ≤ weight
  weight_le_one : weight ≤ 1
  reset : Law Bool

/-- The marginal on the second coordinate. -/
def marginalSecond (p : Mass) (y : Bool) : ℝ := p (false, y) + p (true, y)

/-- The marginal on the first coordinate. -/
def marginalFirst (p : Mass) (x : Bool) : ℝ := p (x, false) + p (x, true)

/-- Apply the first-coordinate bath to the joint mass function. -/
def firstBath (d : Bath) (p : Law Point) : Law Point where
  mass z := (1 - d.weight) * p.mass z + d.weight * d.reset.mass z.1 * marginalSecond p.mass z.2
  nonneg z := add_nonneg (mul_nonneg (sub_nonneg.mpr d.weight_le_one) (p.nonneg z))
    (mul_nonneg (mul_nonneg d.weight_nonneg (d.reset.nonneg _))
      (add_nonneg (p.nonneg _) (p.nonneg _)))
  normalized := by
    have hp := p.normalized
    have hr := d.reset.normalized
    simp only [Fintype.sum_prod_type, Fintype.sum_bool] at hp ⊢
    simp only [Fintype.sum_bool] at hr
    simp only [marginalSecond]
    have hp' : p.mass (false, false) + p.mass (false, true) +
        p.mass (true, false) + p.mass (true, true) = 1 := by linarith
    have hr' : d.reset.mass true = 1 - d.reset.mass false := by linarith
    rw [hr']
    linear_combination hp'

/-- Mean sign of the reset distribution. -/
def resetMoment (d : Bath) : ℝ := d.reset.mass false - d.reset.mass true

/-- Exact evolution of the three Walsh moments under the first-coordinate bath. -/
theorem firstBath_moments (d : Bath) (p : Law Point) :
    momentA (firstBath d p).mass = (1 - d.weight) * momentA p.mass + d.weight * resetMoment d ∧
    momentB (firstBath d p).mass = momentB p.mass ∧
    momentC (firstBath d p).mass = (1 - d.weight) * momentC p.mass +
      d.weight * resetMoment d * momentB p.mass := by
  have hp := p.normalized
  have hr := d.reset.normalized
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at hp
  simp only [Fintype.sum_bool] at hr
  have hp' : p.mass (false, false) + p.mass (false, true) +
      p.mass (true, false) + p.mass (true, true) = 1 := by linarith
  have hr' : d.reset.mass true = 1 - d.reset.mass false := by linarith
  constructor
  · simp only [momentA, firstBath, marginalSecond, resetMoment]
    rw [hr']
    linear_combination (d.weight * (2 * d.reset.mass false - 1)) * hp'
  constructor
  · simp only [momentB, firstBath, marginalSecond]
    rw [hr']; ring
  · simp only [momentC, momentB, firstBath, marginalSecond, resetMoment]
    ring

private theorem resetMoment_abs_le_one (d : Bath) : |resetMoment d| ≤ 1 := by
  have hr := d.reset.normalized
  simp only [Fintype.sum_bool] at hr
  unfold resetMoment
  exact abs_le.mpr ⟨by linarith [d.reset.nonneg false], by linarith [d.reset.nonneg true]⟩

/-- The bath cannot increase the absolute correlation beyond the larger of its old
absolute correlation and the untouched marginal's absolute moment. -/
theorem firstBath_correlation_bound (d : Bath) (p : Law Point) :
    |momentC (firstBath d p).mass| ≤ max |momentC p.mass| |momentB p.mass| := by
  rw [(firstBath_moments d p).2.2]
  calc
    _ ≤ |(1 - d.weight) * momentC p.mass| + |d.weight * resetMoment d * momentB p.mass| :=
      abs_add_le _ _
    _ = (1 - d.weight) * |momentC p.mass| +
        d.weight * |resetMoment d| * |momentB p.mass| := by
      simp only [abs_mul, abs_of_nonneg (sub_nonneg.mpr d.weight_le_one),
        abs_of_nonneg d.weight_nonneg]
    _ ≤ (1 - d.weight) * max |momentC p.mass| |momentB p.mass| +
        d.weight * max |momentC p.mass| |momentB p.mass| := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr d.weight_le_one)
      · rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ d.weight_nonneg
        exact (mul_le_of_le_one_left (abs_nonneg _) (resetMoment_abs_le_one d)).trans
          (le_max_right _ _)
    _ = _ := by ring

private theorem moment_diff_le (p q : Mass) (χ : Point → ℝ) (hχ : ∀ z, |χ z| ≤ 1) :
    |(∑ z, p z * χ z) - ∑ z, q z * χ z| ≤ 2 * totalVariation p q := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ z, |p z * χ z - q z * χ z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z, |p z - q z| := by
      apply Finset.sum_le_sum
      intro z _
      rw [← sub_mul, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hχ z)
    _ = _ := by unfold totalVariation; ring

/-- Each Walsh moment changes by at most twice the total variation of the joint laws. -/
theorem moment_differences_le_variation (p q : Mass) :
    |momentA p - momentA q| ≤ 2 * totalVariation p q ∧
    |momentB p - momentB q| ≤ 2 * totalVariation p q ∧
    |momentC p - momentC q| ≤ 2 * totalVariation p q := by
  obtain ⟨ha, hb, hc⟩ := moment_formulas p
  obtain ⟨ha', hb', hc'⟩ := moment_formulas q
  rw [ha, ha', hb, hb', hc, hc']
  refine ⟨moment_diff_le p q (fun z => sign z.1) ?_,
    moment_diff_le p q (fun z => sign z.2) ?_,
    moment_diff_le p q (fun z => sign z.1 * sign z.2) ?_⟩
  all_goals intro ⟨x, y⟩; cases x <;> cases y <;> norm_num [sign]

private theorem abs_le_old_add_change (x y : ℝ) : |x| ≤ |y| + |x - y| := by
  calc
    |x| = |y + (x - y)| := by ring_nf
    _ ≤ _ := abs_add_le _ _

/-- The potential increase under a first bath is bounded by the largest change in the
first and correlation moments, even when the two moments change simultaneously. -/
theorem firstBath_potential_change (d : Bath) (p : Law Point) :
    potential (firstBath d p).mass ≤ potential p.mass +
      max |momentA (firstBath d p).mass - momentA p.mass|
        |momentC (firstBath d p).mass - momentC p.mass| := by
  let a := momentA p.mass
  let b := momentB p.mass
  let c := momentC p.mass
  let a' := momentA (firstBath d p).mass
  let c' := momentC (firstBath d p).mass
  let Δ := max |a' - a| |c' - c|
  have ha : |a'| ≤ |a| + Δ :=
    (abs_le_old_add_change a' a).trans (add_le_add le_rfl (le_max_left _ _))
  have hc : |c'| ≤ |c| + Δ :=
    (abs_le_old_add_change c' c).trans (add_le_add le_rfl (le_max_right _ _))
  have hcb : |c'| ≤ max |c| |b| := firstBath_correlation_bound d p
  have hAB : |a| + |b| ≤ potential p.mass := le_max_left _ _
  have hAC : |a| + |c| ≤ potential p.mass := (le_max_left _ _).trans (le_max_right _ _)
  have hBC : |b| + |c| ≤ potential p.mass := (le_max_right _ _).trans (le_max_right _ _)
  unfold potential at ⊢
  rw [(firstBath_moments d p).2.1]
  change max (|a'| + |b|) (max (|a'| + |c'|) (|b| + |c'|)) ≤ potential p.mass + Δ
  apply max_le
  · linarith
  apply max_le
  · rcases le_total |c| |b| with h | h
    · rw [max_eq_right h] at hcb
      linarith
    · rw [max_eq_left h] at hcb
      linarith
  · linarith

/-- Each first bath consumes at least half the potential it creates. -/
theorem firstBath_potential_le (d : Bath) (p : Law Point) :
    potential (firstBath d p).mass ≤ potential p.mass +
      2 * totalVariation (firstBath d p).mass p.mass := by
  have h := moment_differences_le_variation (firstBath d p).mass p.mass
  exact (firstBath_potential_change d p).trans (add_le_add le_rfl (max_le h.1 h.2.2))

/-- Swap the two registers. -/
def swap : Equiv.Perm Point := Equiv.prodComm Bool Bool

/-- A second-coordinate bath is the conjugate of the first bath by coordinate swap. -/
def secondBath (d : Bath) (p : Law Point) : Law Point :=
  permute swap (firstBath d (permute swap p))

private theorem variation_permute (e : Equiv.Perm Point) (p q : Law Point) :
    totalVariation (permute e p).mass (permute e q).mass = totalVariation p.mass q.mass := by
  unfold totalVariation
  congr 1
  exact Equiv.sum_comp e.symm (fun z => |p.mass z - q.mass z|)

private theorem swap_swap_mass (p : Law Point) : (permute swap (permute swap p)).mass = p.mass := by
  funext z
  rcases z with ⟨x, y⟩
  rfl

/-- The same bound holds for a second-coordinate bath. -/
theorem secondBath_potential_le (d : Bath) (p : Law Point) :
    potential (secondBath d p).mass ≤ potential p.mass +
      2 * totalVariation (secondBath d p).mass p.mass := by
  have h := firstBath_potential_le d (permute swap p)
  rw [potential_permute] at h
  unfold secondBath
  rw [potential_permute]
  have hv := variation_permute swap (firstBath d (permute swap p)) (permute swap p)
  rw [swap_swap_mass] at hv
  rw [hv]
  exact h

/-- An elementary scheduled operation on the four-point joint law. -/
inductive Step where
  | reversible (e : Equiv.Perm Point)
  | first (bath : Bath)
  | second (bath : Bath)

/-- Actual joint law after an elementary step. -/
def Step.apply : Step → Law Point → Law Point
  | .reversible e, p => permute e p
  | .first d, p => firstBath d p
  | .second d, p => secondBath d p

/-- Endpoint total variation of a bath step, with zero charge for reversible gates. -/
def Step.cost (s : Step) (p : Law Point) : ℝ :=
  match s with
  | .reversible _ => 0
  | .first d => totalVariation (firstBath d p).mass p.mass
  | .second d => totalVariation (secondBath d p).mass p.mass

private theorem step_potential_le (s : Step) (p : Law Point) :
    potential (s.apply p).mass ≤ potential p.mass + 2 * s.cost p := by
  cases s with
  | reversible e => simp [Step.apply, Step.cost, potential_permute]
  | first d => exact firstBath_potential_le d p
  | second d => exact secondBath_potential_le d p

/-- Iterate the scheduled operations in their listed order. -/
def run : List Step → Law Point → Law Point
  | [], p => p
  | s :: ss, p => run ss (s.apply p)

/-- Sum of bath variations along the actual joint-law trajectory. -/
def bathVariation : List Step → Law Point → ℝ
  | [], _ => 0
  | s :: ss, p => s.cost p + bathVariation ss (s.apply p)

/-- Telescope the potential along an arbitrary finite scheduled protocol. -/
theorem run_potential_le (ss : List Step) (p : Law Point) :
    potential (run ss p).mass ≤ potential p.mass + 2 * bathVariation ss p := by
  induction ss generalizing p with
  | nil => simp [run, bathVariation]
  | cons s ss ih =>
    simp only [run, bathVariation]
    linarith [ih (s.apply p), step_potential_le s p]

/-- The first marginal TV is half the difference of the signed first moments in magnitude. -/
private theorem first_variation_eq (p q : Law Point) :
    totalVariation (marginalFirst p.mass) (marginalFirst q.mass) =
      |momentA p.mass - momentA q.mass| / 2 := by
  have hp := p.normalized
  have hq := q.normalized
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at hp hq
  have h : momentA p.mass - momentA q.mass =
      2 * (marginalFirst p.mass false - marginalFirst q.mass false) := by
    unfold momentA marginalFirst
    linarith
  have h' : marginalFirst p.mass true - marginalFirst q.mass true =
      -(marginalFirst p.mass false - marginalFirst q.mass false) := by
    unfold marginalFirst; linarith
  unfold totalVariation
  rw [h, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), Fintype.sum_bool, h', abs_neg]
  ring

/-- The second marginal TV is half the difference of the signed second moments in magnitude. -/
private theorem second_variation_eq (p q : Law Point) :
    totalVariation (marginalSecond p.mass) (marginalSecond q.mass) =
      |momentB p.mass - momentB q.mass| / 2 := by
  have hp := p.normalized
  have hq := q.normalized
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at hp hq
  have h : momentB p.mass - momentB q.mass =
      2 * (marginalSecond p.mass false - marginalSecond q.mass false) := by
    unfold momentB marginalSecond; linarith
  have h' : marginalSecond p.mass true - marginalSecond q.mass true =
      -(marginalSecond p.mass false - marginalSecond q.mass false) := by
    unfold marginalSecond; linarith
  unfold totalVariation
  rw [h, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), Fintype.sum_bool, h', abs_neg]
  ring

/-- The two marginal contrasts obtained from the two uniform event branches are bounded by
 the sum of their actual bath endpoint variations. This applies to arbitrary fixed finite lists
 of local bath steps and reversible permutations, with either list allowed to be empty. -/
theorem recording_bound (protocol0 protocol1 : List Step) :
    totalVariation (marginalFirst (run protocol0 uniform).mass)
        (marginalFirst (run protocol1 uniform).mass) +
      totalVariation (marginalSecond (run protocol0 uniform).mass)
        (marginalSecond (run protocol1 uniform).mass) ≤
      bathVariation protocol0 uniform + bathVariation protocol1 uniform := by
  let p := run protocol0 uniform
  let q := run protocol1 uniform
  have hp := run_potential_le protocol0 uniform
  have hq := run_potential_le protocol1 uniform
  rw [potential_uniform, zero_add] at hp hq
  have hpAB : |momentA p.mass| + |momentB p.mass| ≤ potential p.mass := le_max_left _ _
  have hqAB : |momentA q.mass| + |momentB q.mass| ≤ potential q.mass := le_max_left _ _
  rw [first_variation_eq, second_variation_eq]
  linarith [abs_sub (momentA p.mass) (momentA q.mass),
    abs_sub (momentB p.mass) (momentB q.mass)]

/-- A binary law of mean sign `m`, used below for the sharpness construction. -/
private def biasedBit (m : ℝ) (hm₀ : 0 ≤ m) (hm₁ : m ≤ 1) : Law Bool where
  mass x := if x then (1 - m) / 2 else (1 + m) / 2
  nonneg x := by cases x <;> simp <;> linarith
  normalized := by simp; ring

private def fairBit : Law Bool := biasedBit 0 (by norm_num) (by norm_num)

private def fullReset (r : Law Bool) : Bath := ⟨1, by norm_num, le_rfl, r⟩

private def productMass (r s : Law Bool) : Mass := fun z => r.mass z.1 * s.mass z.2

private theorem uniform_product : uniform.mass = productMass fairBit fairBit := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> norm_num [uniform, productMass, fairBit, biasedBit]

private theorem first_full_uniform (r : Law Bool) :
    (firstBath (fullReset r) uniform).mass = productMass r fairBit := by
  funext ⟨x, y⟩
  change (1 - 1) * (1 / 4 : ℝ) +
      1 * r.mass x * (1 / 4 + 1 / 4) = r.mass x * fairBit.mass y
  cases y <;> norm_num [fairBit, biasedBit]

private theorem second_full_after_first (r s : Law Bool) :
    (secondBath (fullReset s) (firstBath (fullReset r) uniform)).mass = productMass r s := by
  funext ⟨x, y⟩
  change (1 - 1) * (firstBath (fullReset r) uniform).mass (x, y) +
      1 * s.mass y * ((firstBath (fullReset r) uniform).mass (x, false) +
        (firstBath (fullReset r) uniform).mass (x, true)) = _
  rw [first_full_uniform]
  norm_num [productMass, fairBit, biasedBit]
  ring

private theorem variation_product_right (r s t : Law Bool) :
    totalVariation (productMass r s) (productMass r t) = totalVariation s.mass t.mass := by
  unfold totalVariation
  rw [Fintype.sum_prod_type]
  simp only [productMass, ← mul_sub, abs_mul, abs_of_nonneg (r.nonneg _)]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, r.normalized, one_mul]

private theorem variation_product_left (r s t : Law Bool) :
    totalVariation (productMass s r) (productMass t r) = totalVariation s.mass t.mass := by
  have h : (∑ z : Point, |productMass s r (swap z) - productMass t r (swap z)|) =
      ∑ z : Point, |productMass s r z - productMass t r z| :=
    Equiv.sum_comp swap (fun z => |productMass s r z - productMass t r z|)
  unfold totalVariation at ⊢
  rw [← h]
  simp only [productMass, swap, Equiv.prodComm_apply]
  simp_rw [mul_comm (s.mass _) (r.mass _), mul_comm (t.mass _) (r.mass _)]
  exact variation_product_right r s t

private theorem variation_biased_fair (m : ℝ) (hm₀ : 0 ≤ m) (hm₁ : m ≤ 1) :
    totalVariation (biasedBit m hm₀ hm₁).mass fairBit.mass = m / 2 := by
  have hpos : (1 + m) / 2 - (1 / 2 : ℝ) = m / 2 := by ring
  have hneg : (1 - m) / 2 - (1 / 2 : ℝ) = -(m / 2) := by ring
  norm_num [totalVariation, Fintype.sum_bool, biasedBit, fairBit]
  rw [hpos, hneg, abs_neg, abs_of_nonneg (by positivity : 0 ≤ m / 2)]
  ring

private def complement : Equiv.Perm Point where
  toFun z := (!z.1, !z.2)
  invFun z := (!z.1, !z.2)
  left_inv := by intro ⟨x, y⟩; simp
  right_inv := by intro ⟨x, y⟩; simp

/-- Every pair of marginal contrasts in `[0,1]` is attained with equality in
`recording_bound`: two full local resets in each branch, followed in the second
branch by a reversible complement of both registers. -/
theorem recording_bound_sharp (m₁ m₂ : ℝ)
    (h₁₀ : 0 ≤ m₁) (h₁₁ : m₁ ≤ 1) (h₂₀ : 0 ≤ m₂) (h₂₁ : m₂ ≤ 1) :
    ∃ protocol0 protocol1 : List Step,
      totalVariation (marginalFirst (run protocol0 uniform).mass)
        (marginalFirst (run protocol1 uniform).mass) = m₁ ∧
      totalVariation (marginalSecond (run protocol0 uniform).mass)
        (marginalSecond (run protocol1 uniform).mass) = m₂ ∧
      bathVariation protocol0 uniform + bathVariation protocol1 uniform = m₁ + m₂ := by
  let r := biasedBit m₁ h₁₀ h₁₁
  let s := biasedBit m₂ h₂₀ h₂₁
  let p := secondBath (fullReset s) (firstBath (fullReset r) uniform)
  have hp : p.mass = productMass r s := second_full_after_first r s
  have ha : momentA p.mass = m₁ := by
    rw [hp]
    simp [momentA, productMass, r, s, biasedBit]
    ring
  have hb : momentB p.mass = m₂ := by
    rw [hp]
    simp [momentB, productMass, r, s, biasedBit]
    ring
  have ha' : momentA (permute complement p).mass = -momentA p.mass := by
    simp [momentA, permute, complement, Equiv.symm_mk]
    ring
  have hb' : momentB (permute complement p).mass = -momentB p.mass := by
    simp [momentB, permute, complement, Equiv.symm_mk]
    ring
  refine ⟨[.first (fullReset r), .second (fullReset s)],
    [.first (fullReset r), .second (fullReset s), .reversible complement], ?_, ?_, ?_⟩
  · rw [first_variation_eq]
    change |momentA p.mass - momentA (permute complement p).mass| / 2 = m₁
    rw [ha', ha, abs_of_nonneg (by linarith : 0 ≤ m₁ - -m₁)]
    ring
  · rw [second_variation_eq]
    change |momentB p.mass - momentB (permute complement p).mass| / 2 = m₂
    rw [hb', hb, abs_of_nonneg (by linarith : 0 ≤ m₂ - -m₂)]
    ring
  · have hcost₁ : totalVariation (firstBath (fullReset r) uniform).mass uniform.mass = m₁ / 2 := by
      rw [first_full_uniform, uniform_product, variation_product_left]
      exact variation_biased_fair m₁ h₁₀ h₁₁
    have hcost₂ : totalVariation p.mass (firstBath (fullReset r) uniform).mass = m₂ / 2 := by
      rw [hp, first_full_uniform, variation_product_right]
      exact variation_biased_fair m₂ h₂₀ h₂₁
    simp only [bathVariation, Step.cost, Step.apply, ← show p = secondBath (fullReset s)
      (firstBath (fullReset r) uniform) from rfl, hcost₁, hcost₂]
    ring

end D5.S3.Quantum.Information.RecordWriting.TwoRegister
