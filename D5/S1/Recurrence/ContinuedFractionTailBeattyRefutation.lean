/- GID: D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation
   generality: I
   mirror-B: D5/B/S1/Recurrence/ContinuedFractionTailBeattyRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation.claim; result=D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation.result; claim=D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation.claim
   digest: Positive continued-fraction tails cross the Beatty line at the first index. -/

/-
result — proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#18586; Refuted).
Direct frozen dependencies:
  D5/S0/Asymptotics/MetallicFamily.metallicValue
    statement_id: sha256:2255a436520217f661a078dc4e6e9e7aba690fd427d49e4a585ad57920cd9625
  D5/S0/Asymptotics/MetallicFamily.metallic_family_value
    statement_id: sha256:3b0abd7299849ff0bc39e2ec76d3ebebc00c82180300925a2f24bfc79d1345a9
  D5/S0/Asymptotics/MetallicMinimum.metallic_value_minimal_nontrivial
    statement_id: sha256:1ce969f4d45227805aafed674b3c4eb9d9a983d66edc44d3e832974395482407
All private proof declarations are bind-only and consumed:
  metallic_value_sq → beta_value, error_identity, error_bounds;
  metallic_value_bounds → error_bounds, error_next_bounds, error_lipschitz, tail_exists, result;
  beta_value → result; error_identity → error_bounds;
  error_bounds → error_next_bounds, tail_exists;
  error_set_closed → completeErrors; completeErrors, nonemptyErrors → tail_exists;
  error_next_bounds → errorOperator; error_lipschitz → error_operator_contracting;
  error_operator_contracting → tail_exists; tail_exists → result.
The claim keeps the source's radical expression inline; proofs use the frozen
metallicValue owner, with definitional correspondence at its occurrences.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The quantified Pell-index conclusion and finite-truncation identification are not
statements of this module.
-/

import D5.S0.Asymptotics.MetallicFamily
import D5.S0.Asymptotics.MetallicMinimum
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

noncomputable section

namespace D5.S1.Recurrence.ContinuedFractionTailBeattyRefutation

open D5.S0.Asymptotics.MetallicFamily

/-- The offset `β = (vα² - α)/(α² + 1)`. -/
def beta (u : ℕ) (v : ℝ) : ℝ :=
  (v * metallicValue u ^ 2 - metallicValue u) / (metallicValue u ^ 2 + 1)

/-- `s` is a sequence of positive tails of the continued fraction (14): `s_n = nu + v + n²/s_{n+1}`. -/
def IsTail (u : ℕ) (v : ℝ) (s : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → 0 < s n ∧ s n = n * u + v + (n : ℝ) ^ 2 / s (n + 1)

/-- The generalisation of Conjecture 20 stated after eq. (14): for a natural number `u`, positive tails
with `s_n = αn + β + O(1/n)` round down to the Beatty sequence with slope `α` and offset `β`. -/
def claim : Prop :=
  ∀ (u : ℕ), 1 ≤ u → ∀ (v : ℝ) (s : ℕ → ℝ), IsTail u v s →
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |s n - ((((u : ℝ) + Real.sqrt ((u : ℝ) ^ 2 + 4)) / 2) * n + beta u v)| ≤ C / n) →
      ∀ n : ℕ, 1 ≤ n →
        ⌊s n⌋ = ⌊(((u : ℝ) + Real.sqrt ((u : ℝ) ^ 2 + 4)) / 2) * n + beta u v⌋

private theorem metallic_value_sq : metallicValue 2 ^ 2 = 2 * metallicValue 2 + 1 := by
  have hv := (D5.S0.Asymptotics.MetallicFamily.metallic_family_value 2).2
  change 1 / metallicValue 2 = metallicValue 2 - 2 at hv
  have hp : 0 < metallicValue 2 :=
    lt_of_lt_of_le Real.goldenRatio_pos
      ((D5.S0.Asymptotics.MetallicMinimum.metallic_value_minimal_nontrivial.2) 2 (by decide)).1
  have hm := (div_eq_iff hp.ne').mp hv
  nlinarith

private theorem metallic_value_bounds : 2 < metallicValue 2 ∧ metallicValue 2 < 5 / 2 := by
  have hs : metallicValue 2 = 1 + Real.sqrt 2 := by
    change ((2 : ℝ) + Real.sqrt ((2 : ℝ) ^ 2 + 4)) / 2 = 1 + Real.sqrt 2
    rw [show (2 : ℝ) ^ 2 + 4 = (2 : ℝ) ^ 2 * 2 by norm_num,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    ring
  rw [hs]
  constructor
  · linarith [Real.one_lt_sqrt_two]
  · linarith [Real.sqrt_two_lt_three_halves]

private theorem beta_value : beta 2 1 = 1 / 2 := by
  unfold beta
  have h := metallic_value_sq
  have hd : metallicValue 2 ^ 2 + 1 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) zero_lt_one)
  apply (div_eq_iff hd).2
  nlinarith

private def errorMap (n t : ℝ) : ℝ :=
  2 * n + 1 + n ^ 2 / (metallicValue 2 * (n + 1) + 1 / 2 + t) -
    (metallicValue 2 * n + 1 / 2)

private theorem error_identity (n t : ℝ)
    (hd : metallicValue 2 * (n + 1) + 1 / 2 + t ≠ 0) :
    errorMap n t * (metallicValue 2 * (n + 1) + 1 / 2 + t) =
      metallicValue 2 ^ 2 / 4 - ((metallicValue 2 - 2) * n - 1 / 2) * t := by
  unfold errorMap
  have hv := div_mul_cancel₀ (n ^ 2) hd
  linear_combination hv - (n ^ 2 + n + 1 / 4) * metallic_value_sq

private theorem error_bounds (n t : ℝ) (hn : 1 ≤ n)
    (ht : 0 ≤ t) (htop : t ≤ 1 / (n + 1)) :
    1 / (8 * n) < errorMap n t ∧ errorMap n t < metallicValue 2 / (4 * n) := by
  have ha := metallic_value_bounds
  have hap : 0 < metallicValue 2 :=
    lt_of_lt_of_le Real.goldenRatio_pos
      ((D5.S0.Asymptotics.MetallicMinimum.metallic_value_minimal_nontrivial.2) 2 (by decide)).1
  have hn0 : 0 < n := by linarith
  have hnp : 0 < n + 1 := by linarith
  have hnt : (n + 1) * t ≤ 1 := (le_mul_inv_iff₀' hnp).mp htop
  have hd : 0 < metallicValue 2 * (n + 1) + 1 / 2 + t := by positivity
  have hi := error_identity n t hd.ne'
  have hnt' : n * t ≤ 1 := by nlinarith
  have hmul : (metallicValue 2 - 2) * (n * t) ≤ metallicValue 2 - 2 :=
    mul_le_of_le_one_right (by linarith) hnt'
  have hhalf : t ≤ 1 / 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ n - 1) ht]
  have hmuln := mul_le_mul_of_nonneg_right hmul hn0.le
  have hscale := congrArg (fun z : ℝ => z * (8 * n)) hi
  have hascale : 2 * n * metallicValue 2 ^ 2 = 4 * n * metallicValue 2 + 2 * n := by
    linear_combination 2 * n * metallic_value_sq
  have hsign : 0 ≤ (18 - 5 * metallicValue 2) * (n - 1) :=
    mul_nonneg (by linarith [ha.2]) (by linarith)
  have hnt0 : 0 ≤ n * t := mul_nonneg hn0.le ht
  have hlow : 1 / (8 * n) < errorMap n t := by
    apply (div_lt_iff₀ (by positivity : 0 < 8 * n)).2
    apply (mul_lt_mul_iff_of_pos_right hd).mp
    nlinarith only [hscale, hascale, hmuln, hsign, hhalf, hnt0, ha.2]
  refine ⟨hlow, ?_⟩
  have hdz : 0 < metallicValue 2 * (n + 1) + 1 / 2 := by positivity
  have hz := error_identity n 0 (by simpa using hdz.ne')
  have hzp : 0 < errorMap n 0 := by
    apply (mul_pos_iff_of_pos_right hdz).mp
    nlinarith [metallic_value_sq]
  have hle : errorMap n t ≤ errorMap n 0 := by
    unfold errorMap
    gcongr
  have hu : errorMap n 0 * (4 * n) < metallicValue 2 := by
    apply (mul_lt_mul_iff_of_pos_right (by linarith : 0 < metallicValue 2)).mp
    nlinarith [mul_pos hzp (by linarith : 0 < metallicValue 2 + 1 / 2)]
  exact (lt_div_iff₀ (by positivity : 0 < 4 * n)).2
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity)) hu)

open scoped BoundedContinuousFunction

private def ErrorSet : Set (ℕ →ᵇ ℝ) :=
  {f | ∀ n : ℕ, 0 ≤ f n ∧ f n ≤ 1 / ((n : ℝ) + 1)}

private theorem error_set_closed : IsClosed ErrorSet := by
  simp only [ErrorSet, Set.ofPred_forall]
  apply isClosed_iInter
  intro n
  exact (isClosed_le continuous_const
    (BoundedContinuousFunction.lipschitz_eval_const n).continuous).inter
    (isClosed_le (BoundedContinuousFunction.lipschitz_eval_const n).continuous continuous_const)

private instance completeErrors : CompleteSpace ↥ErrorSet := error_set_closed.completeSpace_coe

private instance nonemptyErrors : Nonempty ↥ErrorSet := ⟨⟨BoundedContinuousFunction.const ℕ 0, by
  intro n
  simp only [BoundedContinuousFunction.const_apply]
  exact ⟨le_rfl, by positivity⟩⟩⟩

private theorem error_next_bounds (f : ↥ErrorSet) (n : ℕ) :
    0 < errorMap ((n : ℝ) + 1) (f.val (n + 1)) ∧
    errorMap ((n : ℝ) + 1) (f.val (n + 1)) ≤ 1 / ((n : ℝ) + 1) := by
  have hf := f.property (n + 1)
  push_cast at hf
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb := error_bounds ((n : ℝ) + 1) (f.val (n + 1)) (by linarith) hf.1 hf.2
  refine ⟨lt_trans (by positivity) hb.1, le_of_lt (hb.2.trans ?_)⟩
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [metallic_value_bounds]

private def errorOperator (f : ↥ErrorSet) : ↥ErrorSet :=
  ⟨BoundedContinuousFunction.mkOfDiscrete
    (fun n : ℕ => errorMap ((n : ℝ) + 1) (f.val (n + 1))) 1 (by
      intro i j
      rw [Real.dist_eq, abs_le]
      have hi := error_next_bounds f i
      have hj := error_next_bounds f j
      have hi' : 1 / ((i : ℝ) + 1) ≤ 1 := by
        apply (div_le_iff₀ (by positivity)).2; norm_num
      have hj' : 1 / ((j : ℝ) + 1) ≤ 1 := by
        apply (div_le_iff₀ (by positivity)).2; norm_num
      constructor <;> linarith), by
    intro n
    exact ⟨(error_next_bounds f n).1.le, (error_next_bounds f n).2⟩⟩

private theorem error_lipschitz (n t u : ℝ) (hn : 1 ≤ n) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    dist (errorMap n t) (errorMap n u) ≤ (1 / 4 : ℝ) * dist t u := by
  have hn0 : 0 < n := by linarith
  have ha := metallic_value_bounds
  have hap : 0 < metallicValue 2 :=
    lt_of_lt_of_le Real.goldenRatio_pos
      ((D5.S0.Asymptotics.MetallicMinimum.metallic_value_minimal_nontrivial.2) 2 (by decide)).1
  let d := metallicValue 2 * (n + 1) + 1 / 2 + t
  let e := metallicValue 2 * (n + 1) + 1 / 2 + u
  have hd : 0 < d := by dsimp [d]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hdn : 2 * n ≤ d := by dsimp [d]; nlinarith [ha.1]
  have hen : 2 * n ≤ e := by dsimp [e]; nlinarith [ha.1]
  have hprod : (2 * n) * (2 * n) ≤ d * e :=
    mul_le_mul hdn hen (by positivity) hd.le
  have hc : 0 ≤ n ^ 2 / (d * e) := by positivity
  have hc' : n ^ 2 / (d * e) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (mul_pos hd he)).2
    nlinarith
  have hid : errorMap n t - errorMap n u = -(n ^ 2 / (d * e)) * (t - u) := by
    calc
      _ = n ^ 2 / d - n ^ 2 / e := by dsimp [errorMap, d, e]; ring
      _ = _ := by rw [div_sub_div _ _ hd.ne' he.ne']; dsimp [d, e]; ring
  rw [Real.dist_eq, Real.dist_eq, hid, abs_mul, abs_neg, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_right hc' (abs_nonneg _)

private theorem error_operator_contracting : ContractingWith (1 / 4) errorOperator := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul (fun f g => ?_)⟩
  change dist (errorOperator f).val (errorOperator g).val ≤ (1 / 4 : ℝ) * dist f.val g.val
  apply (BoundedContinuousFunction.dist_le (by positivity)).2
  intro n
  change dist (errorMap ((n : ℝ) + 1) (f.val (n + 1)))
    (errorMap ((n : ℝ) + 1) (g.val (n + 1))) ≤ _
  calc
    _ ≤ (1 / 4 : ℝ) * dist (f.val (n + 1)) (g.val (n + 1)) :=
      error_lipschitz _ _ _ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
        (f.property (n + 1)).1 (g.property (n + 1)).1
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (BoundedContinuousFunction.dist_coe_le_dist (n + 1)) (by norm_num)

private theorem tail_exists : ∃ s : ℕ → ℝ, IsTail 2 1 s ∧
    ∀ n : ℕ, 1 ≤ n → 1 / (8 * n) < s n - (metallicValue 2 * n + 1 / 2) ∧
      s n - (metallicValue 2 * n + 1 / 2) < metallicValue 2 / (4 * n) := by
  let e : ↥ErrorSet := error_operator_contracting.fixedPoint errorOperator
  have he : errorOperator e = e := error_operator_contracting.fixedPoint_isFixedPt
  have heq (k : ℕ) : e.val k = errorMap ((k : ℝ) + 1) (e.val (k + 1)) :=
    (congrArg (fun f : ↥ErrorSet => f.val k) he).symm
  let s : ℕ → ℝ := fun n => match n with
    | 0 => 1
    | k + 1 => metallicValue 2 * ((k : ℝ) + 1) + 1 / 2 + e.val k
  have heb (k : ℕ) : 1 / (8 * ((k : ℝ) + 1)) < e.val k ∧
      e.val k < metallicValue 2 / (4 * ((k : ℝ) + 1)) := by
    have hf := e.property (k + 1)
    push_cast at hf
    rw [heq k]
    exact error_bounds _ _ (by have := Nat.cast_nonneg (α := ℝ) k; linarith) hf.1 hf.2
  refine ⟨s, ?_, ?_⟩
  · intro n hn
    cases n with
    | zero => omega
    | succ k =>
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have ha := metallic_value_bounds
      have hr := heq k
      dsimp [s]
      push_cast
      constructor
      · nlinarith [(e.property k).1]
      · dsimp [errorMap] at hr
        linear_combination hr
  · intro n hn
    cases n with
    | zero => omega
    | succ k => simpa [s] using heb k

theorem result : ¬ claim := by
  intro h
  obtain ⟨s, hs, hb⟩ := tail_exists
  have hbeta := beta_value
  have hbig : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |s n - (metallicValue 2 * n + beta 2 1)| ≤ C / n := by
    refine ⟨metallicValue 2 / 4, fun n hn => ?_⟩
    have hn0 : (0 : ℝ) < n := Nat.cast_pos'.mpr hn
    have hep : 0 < s n - (metallicValue 2 * n + 1 / 2) :=
      lt_trans (by positivity) (hb n hn).1
    rw [hbeta, abs_of_pos hep]
    simpa only [div_mul_eq_div_div] using (hb n hn).2.le
  have hf := h 2 (by norm_num) 1 s hs hbig 1 (by norm_num)
  change ⌊s 1⌋ = ⌊metallicValue 2 * (1 : ℕ) + beta 2 1⌋ at hf
  have hline : ⌊metallicValue 2 * (1 : ℕ) + beta 2 1⌋ = (2 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    rw [hbeta]
    push_cast
    constructor <;> nlinarith [metallic_value_bounds]
  rw [hline] at hf
  have hl := Int.lt_floor_add_one (s 1)
  rw [hf] at hl
  norm_num at hl
  have hr := (hs 1 (by norm_num)).2
  have hp := (hs 2 (by norm_num)).1
  norm_num at hr
  have hd : 0 < (s 2)⁻¹ := inv_pos.mpr hp
  linarith

end D5.S1.Recurrence.ContinuedFractionTailBeattyRefutation

