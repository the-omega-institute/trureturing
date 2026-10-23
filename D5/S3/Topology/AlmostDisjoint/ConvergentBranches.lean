/- GID: D5/S3/Topology/AlmostDisjoint/ConvergentBranches
   generality: G
   mirror-B: D5/B/S3/Topology/AlmostDisjoint/ConvergentBranches
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Convergent four-letter branches have continuum limit fibers. -/

import Mathlib.Topology.MetricSpace.HausdorffAlexandroff
import Mathlib.Topology.Sequences
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Basic.Denumerable
import Mathlib.Logic.Equiv.List
import Mathlib.Order.Zorn

open Set Filter Topology
open scoped Cardinal

namespace D5.S3.Topology.AlmostDisjoint.ConvergentBranches

abbrev Letter := Bool × Bool
abbrev Branch := ℕ → Letter
abbrev Word := {s : List Letter // s ≠ []}

/-- Words are stored in the reversed-wordPrefix orientation of PiNat.res. -/
def wordPrefix (x : Branch) (n : ℕ) : Word :=
  ⟨PiNat.res x (n + 1), by intro h; have := congrArg List.length h; simp at this⟩

def branchSet (x : Branch) : Set Word := range (wordPrefix x)

/-- Chronological binary digits, padded by zeros after the word. -/
def wordBits (s : Word) (i : ℕ) : Bool :=
  (s.val.reverse[i]?.getD (false, false)).1

noncomputable def wordValue (s : Word) : unitInterval := Real.fromBinary (wordBits s)
noncomputable def limitValue (x : Branch) : unitInterval :=
  Real.fromBinary (fun i => (x i).1)

/-- Every neighborhood misses only finitely many values on the selected set. -/
def ConvergesOn {α Y : Type*} [TopologicalSpace Y] (u : α → Y)
    (A : Set α) (r : Y) : Prop := ∀ V ∈ 𝓝 r, (A \ u ⁻¹' V).Finite

private theorem wordPrefix_injective (x : Branch) : Function.Injective (wordPrefix x) := by
  intro n m h
  have hl := congrArg (fun s : Word => s.val.length) h
  simpa [wordPrefix] using hl

private theorem branch_infinite (x : Branch) : (branchSet x).Infinite :=
  infinite_range_of_injective (wordPrefix_injective x)

private theorem branch_inter_finite {x y : Branch} (hne : x ≠ y) :
    (branchSet x ∩ branchSet y).Finite := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ y k := by
    by_contra h
    apply hne
    funext k
    exact not_not.mp (not_exists.mp h k)
  apply (Set.finite_lt_nat k).image (wordPrefix x) |>.subset
  rintro s ⟨⟨n, rfl⟩, m, hm⟩
  have hnm : n = m := by
    have hl := congrArg (fun s : Word => s.val.length) hm
    simpa [wordPrefix] using hl.symm
  subst m
  have he : PiNat.res x (n + 1) = PiNat.res y (n + 1) :=
    (congrArg Subtype.val hm).symm
  refine ⟨n, ?_, rfl⟩
  change n < k
  by_contra hn
  exact hk (PiNat.res_eq_res.mp he (by omega))

private theorem res_reverse_getD (x : Branch) (n i : ℕ) (hi : i < n) :
    ((PiNat.res x n).reverse[i]?.getD (false, false)) = x i := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [PiNat.res_succ, List.reverse_cons]
    by_cases hin : i < n
    · rw [List.getElem?_append_left (by simpa using hin)]
      exact ih hin
    · have hi' : i = n := by omega
      subst i
      rw [List.getElem?_append_right (by simp)]
      simp

private theorem wordPrefix_bits (x : Branch) (n i : ℕ) (hi : i < n + 1) :
    wordBits (wordPrefix x n) i = (x i).1 := by
  exact congrArg Prod.fst (res_reverse_getD x (n + 1) i hi)

private theorem prefix_dyadic (x : Branch) (n : ℕ) :
    (wordValue (wordPrefix x n) : ℝ) =
      ∑ i ∈ Finset.range (n + 1),
        (finTwoEquiv.symm (x i).1 : ℝ) * ((2 : ℝ) ^ (i + 1))⁻¹ := by
  change Real.ofDigits (fun i => finTwoEquiv.symm (wordBits (wordPrefix x n) i)) = _
  rw [Real.ofDigits_eq_sum_add_ofDigits _ (n + 1)]
  have ht : (fun i => finTwoEquiv.symm (wordBits (wordPrefix x n) (i + (n + 1)))) =
      (fun _ : ℕ => (0 : Fin 2)) := by
    funext i
    have hn : (PiNat.res x (n + 1)).reverse[i + (n + 1)]? = none :=
      List.getElem?_eq_none (by simp)
    change finTwoEquiv.symm ((PiNat.res x (n + 1)).reverse[i + (n + 1)]?.getD
      (false, false)).1 = 0
    rw [hn]
    rfl
  rw [ht]
  simp only [Real.ofDigits, Real.ofDigitsTerm, Fin.val_zero, Nat.cast_zero,
    zero_mul, tsum_zero, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [wordPrefix_bits x n i (Finset.mem_range.mp hi)]
  norm_num

instance : Infinite Word := Infinite.of_injective (wordPrefix (fun _ => (false, false)))
  (wordPrefix_injective _)

noncomputable def wordEquivNat : Word ≃ ℕ :=
  Classical.choice (nonempty_equiv_of_countable : Nonempty (Word ≃ ℕ))

private theorem wordPrefix_error (x : Branch) (n : ℕ) :
    dist (wordValue (wordPrefix x n)) (limitValue x) ≤ ((2 : ℝ) ^ (n + 1))⁻¹ := by
  change |Real.ofDigits (fun i => finTwoEquiv.symm (wordBits (wordPrefix x n) i)) -
    Real.ofDigits (fun i => finTwoEquiv.symm (x i).1)| ≤ _
  exact Real.abs_ofDigits_sub_ofDigits_le (fun i hi => by rw [wordPrefix_bits x n i hi])

private theorem wordPrefix_tendsto (x : Branch) :
    Tendsto (fun n => wordValue (wordPrefix x n)) atTop (𝓝 (limitValue x)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (wordPrefix_error x)
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  simpa [inv_pow, Function.comp_def] using h.comp (tendsto_add_atTop_nat 1)

theorem convergesOn_range {α Y : Type*} [TopologicalSpace Y]
    (f : ℕ → α) (u : α → Y) (r : Y)
    (h : Tendsto (u ∘ f) atTop (𝓝 r)) : ConvergesOn u (range f) r := by
  intro V hV
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h hV)
  apply ((Set.finite_lt_nat N).image f).subset
  rintro a ⟨⟨n, rfl⟩, hn⟩
  refine ⟨n, ?_, rfl⟩
  change n < N
  by_contra hn'
  exact hn (hN n (Nat.le_of_not_gt hn'))

private theorem limit_continuous : Continuous limitValue :=
  Real.fromBinary_continuous.comp (continuous_pi fun i =>
    continuous_fst.comp (continuous_apply i))

private theorem limit_surjective : Function.Surjective limitValue := by
  intro r
  obtain ⟨a, ha⟩ := Real.fromBinary_surjective r
  exact ⟨fun n => (a n, false), ha⟩

private theorem branch_cardinal : Cardinal.mk Branch = Cardinal.continuum := by
  simp only [Branch, Letter, Cardinal.mk_arrow, Cardinal.mk_prod, Cardinal.mk_bool,
    Cardinal.mk_nat, Cardinal.lift_id]
  convert Cardinal.nat_power_aleph0 (by decide : 2 ≤ 4) using 1; norm_num

private theorem fiber_cardinal (r : unitInterval) :
    Cardinal.mk {x : Branch // limitValue x = r} = Cardinal.continuum := by
  obtain ⟨a, ha⟩ := Real.fromBinary_surjective r
  let f : (ℕ → Bool) → {x : Branch // limitValue x = r} :=
    fun b => ⟨fun n => (a n, b n), ha⟩
  have hf : Function.Injective f := by
    intro b c h
    funext n
    exact congrArg (fun x : {x : Branch // limitValue x = r} => (x.val n).2) h
  apply le_antisymm
  · exact (Cardinal.mk_subtype_le _).trans_eq branch_cardinal
  · have h := Cardinal.mk_le_of_injective hf
    simpa only [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat,
      Cardinal.lift_id, Cardinal.two_power_aleph0] using h

/-- The actual four-letter tree supply, with all its convergence and fiber properties. -/
theorem branch_system (n : ℕ) :
    (∀ x : Branch, (wordValue (wordPrefix x n) : ℝ) =
      ∑ i ∈ Finset.range (n + 1),
        (finTwoEquiv.symm (x i).1 : ℝ) * ((2 : ℝ) ^ (i + 1))⁻¹) ∧
    (∀ x : Branch, (branchSet x).Infinite) ∧
    (∀ x y : Branch, x ≠ y → (branchSet x ∩ branchSet y).Finite) ∧
    (∀ x : Branch, ConvergesOn wordValue (branchSet x) (limitValue x)) ∧
    Continuous limitValue ∧ Function.Surjective limitValue ∧
    (∀ r : unitInterval, Cardinal.mk {x : Branch // limitValue x = r} = Cardinal.continuum) := by
  exact ⟨fun x => prefix_dyadic x n, branch_infinite, fun _ _ => branch_inter_finite,
    fun x => convergesOn_range (wordPrefix x) wordValue (limitValue x) (wordPrefix_tendsto x),
    limit_continuous, limit_surjective, fiber_cardinal⟩

end D5.S3.Topology.AlmostDisjoint.ConvergentBranches
