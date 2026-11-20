/- GID: D5/S3/TotalVariation/GroupedParityBias
   generality: G
   mirror-B: D5/B/S3/TotalVariation/GroupedParityBias
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The binary affine output law identifies each nonzero column's bias product. -/

import D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators

/-! Recovery of grouped input biases from finite binary affine output masses. -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.TotalVariation.GroupedParityBias

open D5.S3.Divergence.ClassicalDPI (channelOutput)
open D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift (labelKernel)

variable {A I : Type*} [AddCommGroup A] [Fintype A] [Fintype I]

def sign (ψ : AddChar A ℂ) (x : A) : ℝ := (ψ x).re

theorem value_cases (two : ∀ x : A, x + x = 0) (ψ : AddChar A ℂ) (x : A) :
    ψ x = 1 ∨ ψ x = -1 := by
  apply mul_self_eq_one_iff.mp
  rw [← AddChar.map_add_eq_mul, two, AddChar.map_zero_eq_one]

private theorem sign_add (two : ∀ x : A, x + x = 0) (ψ : AddChar A ℂ) (x y : A) :
    sign ψ (x + y) = sign ψ x * sign ψ y := by
  unfold sign
  rw [AddChar.map_add_eq_mul]
  rcases value_cases two ψ x with h | h <;> simp [h]

private theorem sign_sum (two : ∀ x : A, x + x = 0) (ψ : AddChar A ℂ)
    (s : Finset I) (x : I → A) :
    sign ψ (∑ i ∈ s, x i) = ∏ i ∈ s, sign ψ (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign]
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, sign_add two, ih]

open Classical in
private theorem sum_sign (x : A) :
    (∑ ψ : AddChar A ℂ, sign ψ x) = if x = 0 then (Fintype.card A : ℝ) else 0 := by
  have h := congrArg Complex.re (AddChar.sum_apply_eq_ite x)
  by_cases hx : x = 0 <;> simpa [sign, Complex.re_sum, hx] using h

open Classical in
private theorem orthogonality (two : ∀ x : A, x + x = 0) (x y : A) :
    (∑ ψ : AddChar A ℂ, sign ψ x * sign ψ y) =
      if x = y then (Fintype.card A : ℝ) else 0 := by
  have hz : x + y = 0 ↔ x = y := by
    calc
      x + y = 0 ↔ x = -y := eq_neg_iff_add_eq_zero.symm
      _ ↔ x = y := by rw [← eq_neg_iff_add_eq_zero.mpr (two y)]
  simp_rw [← sign_add two, sum_sign, hz]

noncomputable def moment (μ : A → ℝ) (ψ : AddChar A ℂ) : ℝ :=
  ∑ x, μ x * sign ψ x

theorem law_from_moments (two : ∀ x : A, x + x = 0)
    (μ ν : A → ℝ) (h : ∀ ψ, moment μ ψ = moment ν ψ) : μ = ν := by
  classical
  have hproject (m : A → ℝ) (a : A) :
      (∑ ψ : AddChar A ℂ, sign ψ a * moment m ψ) = m a * Fintype.card A := by
    unfold moment
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [show ∀ (c u v : ℝ), u * (c * v) = c * (u * v) by intro c u v; ring,
      ← Finset.mul_sum, orthogonality two]
    rw [Finset.sum_eq_single a]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  funext a
  apply mul_right_cancel₀ (show (Fintype.card A : ℝ) ≠ 0 by positivity)
  rw [← hproject, ← hproject]
  simp only [h]

private noncomputable def bitMass (q : ℝ) (x : Bool) : ℝ :=
  if x then (1 - q) / 2 else (1 + q) / 2

open Classical in
noncomputable def law (column : I → A) (offset : A) (q : I → ℝ) : A → ℝ :=
  channelOutput (labelKernel (fun x : I → Bool => offset + ∑ i, if x i then column i else 0))
    (fun x => ∏ i, bitMass (q i) (x i))

open Classical in
noncomputable def groupBias (column : I → A) (q : I → ℝ) (c : A) : ℝ :=
  ∏ i with column i = c, q i

open Classical in
theorem moment_factor (two : ∀ x : A, x + x = 0)
    (column : I → A) (offset : A) (q : I → ℝ) (ψ : AddChar A ℂ) :
    moment (law column offset q) ψ =
      sign ψ offset * ∏ c with sign ψ c = -1, groupBias column q c := by
  unfold moment law channelOutput
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hpick (x : I → Bool) :
      (∑ y, labelKernel (fun u : I → Bool => offset + ∑ i, if u i then column i else 0) x y *
        sign ψ y) = sign ψ (offset + ∑ i, if x i then column i else 0) := by
    unfold labelKernel
    rw [Finset.sum_eq_single (offset + ∑ i, if x i then column i else 0)]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
    · simp
  simp_rw [hpick, sign_add two, sign_sum two]
  have hcombine :
      (∑ x : I → Bool, (∏ i, bitMass (q i) (x i)) *
        (sign ψ offset * ∏ i, sign ψ (if x i then column i else 0))) =
      sign ψ offset * ∑ x : I → Bool,
        ∏ i, bitMass (q i) (x i) * sign ψ (if x i then column i else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.prod_mul_distrib]
    ring
  rw [hcombine]
  congr 1
  rw [← Fintype.prod_sum (fun i b => bitMass (q i) b * sign ψ (if b then column i else 0))]
  have hbit (i : I) :
      (∑ b : Bool, bitMass (q i) b * sign ψ (if b then column i else 0)) =
        if sign ψ (column i) = -1 then q i else 1 := by
    have hu : (Finset.univ : Finset Bool) = {false, true} := by decide
    rw [hu]
    rcases value_cases two ψ (column i) with h | h <;> norm_num [sign, bitMass, h] <;> ring
  simp_rw [hbit]
  rw [← Finset.prod_fiberwise Finset.univ column]
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro c _
  by_cases hc : sign ψ c = -1
  · rw [ite_eq_left hc]
    apply Finset.prod_congr rfl
    intro i hi
    simp [(Finset.mem_filter.mp hi).2, hc]
  · rw [ite_eq_right hc]
    apply Finset.prod_eq_one
    intro i hi
    simp [(Finset.mem_filter.mp hi).2, hc]

open Classical in
theorem loginvert (two : ∀ x : A, x + x = 0)
    (column : I → A) (offset : A) (q : I → ℝ) (hq : ∀ i, 0 < q i)
    (a : A) (ha : a ≠ 0) :
    Real.log (groupBias column q a) =
      (-2 / (Fintype.card A : ℝ)) *
      ∑ ψ : AddChar A ℂ, sign ψ a * Real.log |moment (law column offset q) ψ| := by
  have hpos (c : A) : 0 < groupBias column q c := by
    exact Finset.prod_pos fun i _ => hq i
  have hlog (ψ : AddChar A ℂ) :
      Real.log |moment (law column offset q) ψ| =
        ∑ c, (1 - sign ψ c) / 2 * Real.log (groupBias column q c) := by
    have hs : |sign ψ offset| = 1 := by
      rcases value_cases two ψ offset with h | h <;> simp [sign, h]
    rw [moment_factor two, abs_mul, hs, one_mul, abs_of_pos
      (Finset.prod_pos fun c _ => hpos c), Real.log_prod (fun c _ => (hpos c).ne'),
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    rcases value_cases two ψ c with h | h <;> norm_num [sign, h]
  have hsum :
      (∑ ψ : AddChar A ℂ, sign ψ a * Real.log |moment (law column offset q) ψ|) =
        -(Fintype.card A : ℝ) * Real.log (groupBias column q a) / 2 := by
    simp_rw [hlog, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner (c : A) :
        (∑ ψ : AddChar A ℂ, sign ψ a *
          ((1 - sign ψ c) / 2 * Real.log (groupBias column q c))) =
          -(if a = c then (Fintype.card A : ℝ) else 0) *
            Real.log (groupBias column q c) / 2 := by
      simp_rw [show ∀ (u v k : ℝ), u * ((1 - v) / 2 * k) = (u - u * v) * (k / 2)
        by intro u v k; ring, ← Finset.sum_mul, Finset.sum_sub_distrib, sum_sign, orthogonality two,
        ite_eq_right ha]
      ring
    simp_rw [hinner]
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc
      simp [Ne.symm hc]
    · simp
  rw [hsum]
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by positivity
  field_simp

open Classical in
/-- For a fixed affine offset, equality of the output masses is equivalent to
equality of the bias products on all nonzero columns. The log moments recover
these products even when the offset is unknown. -/
theorem affine_law_iff_grouped_bias (two : ∀ x : A, x + x = 0) (column : I → A)
    (offset : A) (q r : I → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1) (hr : ∀ i, 0 < r i ∧ r i < 1) :
    let μ := law column offset q
    let ν := law column offset r
    ((μ = ν) ↔ ∀ a : A, a ≠ 0 → groupBias column q a = groupBias column r a) ∧
      ∀ a : A, a ≠ 0 →
        Real.log (groupBias column q a) =
          (-2 / (Fintype.card A : ℝ)) * ∑ ψ : AddChar A ℂ, sign ψ a * Real.log |moment μ ψ| := by
  intro μ ν
  have hqpos (i : I) := (hq i).1
  have hrpos (i : I) := (hr i).1
  refine ⟨?_, fun a ha => loginvert two column offset q hqpos a ha⟩
  constructor
  · intro heq a ha
    apply Real.log_injOn_pos (Finset.prod_pos fun i _ => hqpos i)
      (Finset.prod_pos fun i _ => hrpos i)
    change Real.log (groupBias column q a) = Real.log (groupBias column r a)
    rw [loginvert two column offset q hqpos a ha, loginvert two column offset r hrpos a ha]
    change _ * _ = _ * ∑ ψ, sign ψ a * Real.log |moment ν ψ|
    rw [← heq]
  · intro heq
    apply law_from_moments two
    intro ψ
    dsimp [μ, ν]
    rw [moment_factor two, moment_factor two]
    congr 1
    apply Finset.prod_congr rfl
    intro a ha
    apply heq a
    intro hz
    have hbad := (Finset.mem_filter.mp ha).2
    norm_num [hz, sign] at hbad

omit [Fintype A] in
open Classical in
/-- The complete vector of bias factors is identifiable exactly when every column
is nonzero and the columns are pairwise distinct. -/
theorem affine_bias_identifiable_iff [Finite A] (two : ∀ x : A, x + x = 0)
    (column : I → A) (offset : A) :
    Set.InjOn (law column offset) {q | ∀ i, 0 < q i ∧ q i < 1} ↔
      (∀ i, column i ≠ 0) ∧ Function.Injective column := by
  classical
  letI := Fintype.ofFinite A
  let baseline : I → ℝ := fun _ => 1 / 2
  let changed (j : I) (i : I) : ℝ := if i = j then 1 / 3 else 1 / 2
  have hbase : ∀ i, 0 < baseline i ∧ baseline i < 1 := by
    intro i
    norm_num [baseline]
  have hchanged (j : I) : ∀ i, 0 < changed j i ∧ changed j i < 1 := by
    intro i
    unfold changed
    split_ifs <;> norm_num
  have hgroup (a : A) (j : I) :
      groupBias column (changed j) a =
        let members := Finset.univ.filter (fun i => column i = a)
        if column j = a then (1 / 2 : ℝ) ^ (members.card - 1) * (1 / 3)
        else (1 / 2 : ℝ) ^ members.card := by
    let members := Finset.univ.filter (fun i => column i = a)
    change (∏ i ∈ members, changed j i) = _
    dsimp only
    by_cases hj : column j = a
    · have hmem : j ∈ members := by simp [members, hj]
      rw [ite_eq_left hj, ← Finset.prod_erase_mul members (changed j) hmem]
      have hprod : (∏ i ∈ members.erase j, changed j i) =
          ∏ _ ∈ members.erase j, (1 / 2 : ℝ) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [changed, Finset.ne_of_mem_erase hi]
      rw [hprod, Finset.prod_const, Finset.card_erase_of_mem hmem]
      simp [changed, members]
    · rw [ite_eq_right hj]
      calc
        _ = ∏ _ ∈ members, (1 / 2 : ℝ) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hij : i ≠ j := fun h => hj (by simpa [members, h] using hi)
          simp [changed, hij]
        _ = _ := Finset.prod_const _
  constructor
  · intro hinj
    constructor
    · intro j hz
      have hs : law column offset baseline = law column offset (changed j) :=
        (affine_law_iff_grouped_bias two column offset baseline (changed j)
          hbase (hchanged j)).1.mpr (by
            intro a ha
            have hja : column j ≠ a := by simpa [hz, eq_comm] using ha
            rw [hgroup a j, ite_eq_right hja]
            exact Finset.prod_const _)
      have hj := congrFun (hinj hbase (hchanged j) hs) j
      norm_num [baseline, changed] at hj
    · intro i j hij
      by_contra hne
      have hs : law column offset (changed i) = law column offset (changed j) :=
        (affine_law_iff_grouped_bias two column offset (changed i) (changed j)
          (hchanged i) (hchanged j)).1.mpr (fun a _ => by
            rw [hgroup a i, hgroup a j, hij])
      have hj := congrFun (hinj (hchanged i) (hchanged j) hs) i
      norm_num [changed, hne] at hj
  · rintro ⟨hnz, hinj⟩ q hq r hr heq
    funext i
    have h := (affine_law_iff_grouped_bias two column offset q r hq hr).1.mp heq (column i) (hnz i)
    have hfiber : Finset.univ.filter (fun j => column j = column i) = {i} := by
      ext j
      simp [hinj.eq_iff]
    simpa [groupBias, hfiber] using h

end D5.S3.TotalVariation.GroupedParityBias
