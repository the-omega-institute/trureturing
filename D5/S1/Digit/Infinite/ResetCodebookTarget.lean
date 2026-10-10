/- GID: D5/S1/Digit/Infinite/ResetCodebookTarget
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/ResetCodebookTarget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original spectral root bounds the rate of every reset codebook. -/

import D5.S1.Digit.Infinite.ResetCodebookWeighted
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.LiminfLimsup
local notation "g_bounds" => And.intro (And.left (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra)) (And.left (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra)))
local notation "g_relation" => (And.left D5.S1.Digit.Infinite.SixWindowForcing.algebra)
local notation "g_eq" => (And.left (And.right (And.right (And.right D5.S1.Digit.Infinite.OddColorThreeSource.golden_relations))))
local notation "t_sq" => (And.right (And.right (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra))))
local notation "t_linear" => (And.left (And.right (And.right (And.right D5.S1.Digit.Infinite.SixWindowForcing.algebra))))
local notation "Factors" => fun (lang : Set (ℤ → Bool)) (N : ℕ) =>
  {w : List Bool // D5.S1.Digit.Infinite.ResetCodebook.Statement.letterWeight w=N ∧ ∃ omega∈lang, D5.S1.Digit.Infinite.ResetCodebook.Statement.factor w omega}
local notation "complexify" => Complex.ofRealHom.mapMatrix
local notation "radius" => fun A => ENNReal.toReal (spectralRadius ℂ (Complex.ofRealHom.mapMatrix A))
local notation "Vertex" => fun (lang : Set (ℤ → Bool)) (n : ℕ) =>
  {v : Fin n → Bool // ∃ w∈lang, ∃ i : ℤ, D5.S1.Digit.Infinite.ResetCodebook.Transfer.history n w i=v}
set_option autoImplicit false
open scoped Matrix.Norms.Operator Topology
namespace D5.S1.Digit.Infinite.ResetCodebook.Spectral
open D5.S1.Digit.Infinite.ResetCodebook D5.S1.Digit.Infinite.ResetCodebook.Transfer
noncomputable section
attribute [local instance] Classical.propDecidable
private lemma two_step_row (K n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hKn : K ≤ n)
    (v : Vertex (Statement.lowerLanguage K n d) n) :
    2 ≤ ∑ u, (lowerMatrix K n d 1 ^ 2) v u := by
  let next := graphNext (Statement.lowerLanguage K n d) n
  let allow := graphAllowed (Statement.lowerLanguage K n d) n
  have hf := allow_false K n d hK hKn v
  have hff := allow_after_false K n d hK hKn v false
  have hft := allow_after_false K n d hK hKn v true
  have he : accepts next allow v [false,false] := ⟨hf,hff,trivial⟩
  have he' : accepts next allow v [false,true] := ⟨hf,hft,trivial⟩
  change 2 ≤ ∑ u, (transfer next allow 1 ^ 2) v u
  rw [←word_mass_eq_row]
  have hs : ({[false,false],[false,true]} : Finset (List Bool)) ⊆ wordSet 2 := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl|rfl <;> exact (mem_wordSet _ _).mpr rfl
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun w _ _ => mass_nonneg next allow 1 (by norm_num) v w)
  have hm := mass_of_accepts next allow 1 v [false,false] he
  have hm' := mass_of_accepts next allow 1 v [false,true] he'
  norm_num [hm,hm'] at hh
  exact hh
end
end D5.S1.Digit.Infinite.ResetCodebook.Spectral
set_option autoImplicit false
open scoped Matrix.Norms.Operator Topology
open Filter
namespace D5.S1.Digit.Infinite.ResetCodebook.Spectral
open D5.S1.Digit.Infinite.ResetCodebook D5.S1.Digit.Infinite.ResetCodebook.Transfer
noncomputable section
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
private lemma transfer_scale_le (next : ι → Bool → ι) (allow : ι → Bool → Prop)
    (x y a : ℝ) (h6 : a*x^6 ≤ y^6) (h20 : a*x^20 ≤ y^20) :
    ∀ i j, (a • transfer next allow x) i j ≤ transfer next allow y i j := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul, transfer, mul_add]
  split_ifs <;> linarith
private lemma transfer_le_scale (next : ι → Bool → ι) (allow : ι → Bool → Prop)
    (x y a : ℝ) (h6 : y^6 ≤ a*x^6) (h20 : y^20 ≤ a*x^20) :
    ∀ i j, transfer next allow y i j ≤ (a • transfer next allow x) i j := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul, transfer, mul_add]
  split_ifs <;> linarith
private lemma transfer_radius_sandwich (next : ι → Bool → ι) (allow : ι → Bool → Prop)
    (x y : ℝ) (hx : 0<x) (hy : 0<y) :
    min ((y/x)^6) ((y/x)^20) * radius (transfer next allow x)
      ≤ radius (transfer next allow y) ∧
    radius (transfer next allow y) ≤
      max ((y/x)^6) ((y/x)^20) * radius (transfer next allow x) := by
  have hq : 0≤y/x := div_nonneg hy.le hx.le
  have he (k : ℕ) : (y/x)^k*x^k=y^k := by rw [div_pow]; field_simp
  have hmin : 0 ≤ min ((y/x)^6) ((y/x)^20) := le_min (pow_nonneg hq _) (pow_nonneg hq _)
  have hmax : 0 ≤ max ((y/x)^6) ((y/x)^20) := (pow_nonneg hq 6).trans (le_max_left _ _)
  constructor
  · rw [←radius_smul _ _ hmin]
    apply radius_mono
    · intro i j
      exact mul_nonneg hmin (transfer_nonneg next allow x hx.le i j)
    · apply transfer_scale_le
      · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hx.le 6)).trans_eq (he 6)
      · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hx.le 20)).trans_eq (he 20)
  · rw [←radius_smul _ _ hmax]
    apply radius_mono _ _ (transfer_nonneg next allow y hy.le)
    apply transfer_le_scale
    · rw [←he 6]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hx.le 6)
    · rw [←he 20]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hx.le 20)
private lemma transfer_radius_continuous_pos (next : ι → Bool → ι) (allow : ι → Bool → Prop) :
    ContinuousOn (fun z : ℝ => radius (transfer next allow z)) (Set.Ioi 0) := by
  intro x hx
  have hx0 : 0<x := hx
  have hratio : ContinuousAt (fun y : ℝ => y/x) x := continuousAt_id.div_const x
  have hlo := ((hratio.pow 6).min (hratio.pow 20)).mul_const (radius (transfer next allow x))
  have hhi := ((hratio.pow 6).max (hratio.pow 20)).mul_const (radius (transfer next allow x))
  have he1 : min ((x/x)^6) ((x/x)^20)*radius (transfer next allow x)=radius (transfer next allow x) := by simp [hx0.ne']
  have he2 : max ((x/x)^6) ((x/x)^20)*radius (transfer next allow x)=radius (transfer next allow x) := by simp [hx0.ne']
  apply ContinuousAt.continuousWithinAt
  have hlo' : Tendsto (fun y : ℝ => min ((y/x)^6) ((y/x)^20) * radius (transfer next allow x))
      (𝓝 x) (𝓝 (radius (transfer next allow x))) := by
    simpa [ContinuousAt, hx0.ne'] using hlo
  have hhi' : Tendsto (fun y : ℝ => max ((y/x)^6) ((y/x)^20) * radius (transfer next allow x))
      (𝓝 x) (𝓝 (radius (transfer next allow x))) := by
    simpa [ContinuousAt, hx0.ne'] using hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo' hhi' 
  · filter_upwards [eventually_gt_nhds hx0] with y hy
    exact (transfer_radius_sandwich next allow x y hx0 hy).1
  · filter_upwards [eventually_gt_nhds hx0] with y hy
    exact (transfer_radius_sandwich next allow x y hx0 hy).2
private lemma transfer_complex_continuous (next : ι → Bool → ι) (allow : ι → Bool → Prop) :
    Continuous (fun z : ℝ => complexify (transfer next allow z)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun z : ℝ => ((transfer next allow z i j : ℝ) : ℂ))
  unfold transfer
  split_ifs <;> fun_prop
private lemma transfer_radius_zero (next : ι → Bool → ι) (allow : ι → Bool → Prop) :
    radius (transfer next allow 0) = 0 := by
  have he : transfer next allow 0 = 0 := by ext i j; simp [transfer]
  simp [he, RingHom.mapMatrix_apply, spectrum.spectralRadius_zero]
private lemma transfer_radius_continuous_zero (next : ι → Bool → ι) (allow : ι → Bool → Prop) :
    ContinuousAt (fun z : ℝ => radius (transfer next allow z)) 0 := by
  have hc : ContinuousAt (fun z : ℝ => ‖complexify (transfer next allow z)‖) 0 :=
    (transfer_complex_continuous next allow).norm.continuousAt
  have he : complexify (transfer next allow 0)=0 := by ext i j; simp [RingHom.mapMatrix_apply,transfer]
  unfold ContinuousAt at hc
  simp only [he, norm_zero] at hc
  change Tendsto (fun z : ℝ => radius (transfer next allow z)) (𝓝 0)
    (𝓝 (radius (transfer next allow 0)))
  rw [transfer_radius_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
  · intro z; exact ENNReal.toReal_nonneg
  · intro z
    exact (ENNReal.toReal_mono ENNReal.coe_ne_top (spectrum.spectralRadius_le_nnnorm _)).trans_eq (by simp)
private lemma transfer_radius_continuous_Icc (next : ι → Bool → ι) (allow : ι → Bool → Prop) :
    ContinuousOn (fun z : ℝ => radius (transfer next allow z)) (Set.Icc 0 1) := by
  intro z hz
  by_cases hz0 : z=0
  · subst z; exact (transfer_radius_continuous_zero next allow).continuousWithinAt
  · have hzpos : z∈Set.Ioi (0:ℝ) := lt_of_le_of_ne hz.1 (Ne.symm hz0)
    exact ((transfer_radius_continuous_pos next allow).continuousAt
      (IsOpen.mem_nhds isOpen_Ioi hzpos)).continuousWithinAt
end
end D5.S1.Digit.Infinite.ResetCodebook.Spectral
set_option autoImplicit false
open scoped Matrix.Norms.Operator Topology
namespace D5.S1.Digit.Infinite.ResetCodebook.Spectral
open D5.S1.Digit.Infinite.ResetCodebook D5.S1.Digit.Infinite.ResetCodebook.Transfer
noncomputable section
attribute [local instance] Classical.propDecidable
private lemma lower_radius_pos (K n : ℕ) (d z : ℝ) (hK : 2 ≤ K) (hKn : K ≤ n) (hz : 0<z) :
    0 < radius (lowerMatrix K n d z) := by
  letI := vertex_nonempty K n d hK
  have hl : z^6 ≤ radius (lowerMatrix K n d z) := by
    apply row_lower_radius _ (transfer_nonneg _ _ z hz.le) _ (pow_nonneg hz.le _)
    intro v
    have hf := allow_false K n d hK hKn v
    unfold transfer
    simp only [Finset.sum_add_distrib]
    have he : (∑ u, if graphAllowed (Statement.lowerLanguage K n d) n v false ∧
        graphNext (Statement.lowerLanguage K n d) n v false=u then z^6 else 0)=z^6 := by
      simp [hf]
    rw [he]
    have hh : 0 ≤ ∑ u, if graphAllowed (Statement.lowerLanguage K n d) n v true ∧
        graphNext (Statement.lowerLanguage K n d) n v true=u then z^20 else 0 := by positivity
    linarith
  exact (pow_pos hz 6).trans_le hl
private lemma lower_radius_one_gt (K n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hKn : K ≤ n) :
    1 < radius (lowerMatrix K n d 1) := by
  letI := vertex_nonempty K n d hK
  have hnn := transfer_nonneg (graphNext (Statement.lowerLanguage K n d) n)
    (graphAllowed (Statement.lowerLanguage K n d) n) 1 (by norm_num)
  have hh := row_lower_radius (lowerMatrix K n d 1 ^ 2) (positive_pow _ hnn 2)
    2 (by norm_num) (two_step_row K n d hK hKn)
  rw [radius_sq] at hh
  have hp := lower_radius_pos K n d 1 hK hKn (by norm_num)
  nlinarith
private lemma lower_radius_strict (K n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hKn : K ≤ n) :
    StrictMonoOn (fun z : ℝ => radius (lowerMatrix K n d z)) (Set.Ioi 0) := by
  letI := vertex_nonempty K n d hK
  intro x hx y hy hxy
  have hq : 1<y/x := (one_lt_div hx).mpr hxy
  have he : min ((y/x)^6) ((y/x)^20)=(y/x)^6 := min_eq_left
    (pow_le_pow_right₀ hq.le (by norm_num))
  have hl := (transfer_radius_sandwich
    (graphNext (Statement.lowerLanguage K n d) n)
    (graphAllowed (Statement.lowerLanguage K n d) n) x y hx hy).1
  rw [he] at hl
  apply lt_of_lt_of_le _ hl
  have hp := lower_radius_pos K n d x hK hKn hx
  exact lt_mul_of_one_lt_left hp (one_lt_pow₀ hq (by norm_num))
theorem original_root_exists_unique (K n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hKn : K ≤ n) :
    ∃! z : ℝ, OriginalSpectralRoot K n d z := by
  letI := vertex_nonempty K n d hK
  have hc : ContinuousOn (fun z : ℝ => radius (lowerMatrix K n d z)) (Set.Icc 0 1) :=
    transfer_radius_continuous_Icc
      (graphNext (Statement.lowerLanguage K n d) n)
      (graphAllowed (Statement.lowerLanguage K n d) n)
  have hz0 : radius (lowerMatrix K n d 0)=0 := transfer_radius_zero _ _
  have hz1 := lower_radius_one_gt K n d hK hKn
  obtain ⟨z,hz,hzr⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hc
    (show (1:ℝ)∈Set.Icc (radius (lowerMatrix K n d 0)) (radius (lowerMatrix K n d 1)) by
      rw [hz0]; exact ⟨by norm_num,hz1.le⟩)
  change radius (lowerMatrix K n d z)=1 at hzr
  have hzp : 0<z := by
    by_contra hh
    have he : z=0 := le_antisymm (le_of_not_gt hh) hz.1
    rw [he,hz0] at hzr
    norm_num at hzr
  have hzl : z<1 := by
    by_contra hh
    have he : z=1 := le_antisymm hz.2 (le_of_not_gt hh)
    rw [he] at hzr
    linarith
  have hs : spectralRadius ℂ (originalLowerComplexMatrix K n d z)=1 := by
    rw [originalLowerComplexMatrix_eq K n d z (by omega) hKn]
    apply (ENNReal.toReal_eq_one_iff _).mp
    exact hzr
  refine ⟨z,⟨hzp,hzl,hs⟩,?_⟩
  intro y hy
  have hyr : radius (lowerMatrix K n d y)=1 := by
    have he := hy.2.2
    rw [originalLowerComplexMatrix_eq K n d y (by omega) hKn] at he
    change (spectralRadius ℂ (lowerComplexMatrix K n d y)).toReal=1
    rw [he]; simp
  exact (lower_radius_strict K n d hK hKn).injOn hy.1 hzp (hyr.trans hzr.symm)
end
end D5.S1.Digit.Infinite.ResetCodebook.Spectral
set_option autoImplicit false
open scoped Matrix.Norms.Operator Topology ENNReal NNReal
open Filter
namespace D5.S1.Digit.Infinite.ResetCodebook.Transfer
/-- A spectral-root matrix has a uniform exponential majorant for every base above one. -/
private lemma spectral_one_power_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) (hs : spectralRadius ℂ T = 1) (q : ℝ) (hq : 1 < q) :
    ∃ C : ℝ, 1  ≤  C ∧ ∀ k : ℕ, ‖T^k‖  ≤  C*q^k := by
  have ht := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius T
  rw [hs] at ht
  have hq' : (1 : ℝ≥0∞) < ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_one] using
      (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0<q)).mpr hq
  have he := ht.eventually (gt_mem_nhds hq')
  have hb : ∀ᶠ k : ℕ in atTop, ‖T^k‖  ≤  q^k := by
    filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with k hk hk0
    have hn : (k : ℝ) ≠ 0 := by positivity
    have hp := ENNReal.rpow_le_rpow hk.le (Nat.cast_nonneg k : (0 : ℝ)  ≤  k)
    rw [← ENNReal.rpow_mul, show (1/(k:ℝ))*(k:ℝ)=1 by field_simp,
      ENNReal.rpow_one, ENNReal.rpow_natCast] at hp
    have hp' := ENNReal.toReal_mono (by simp : (ENNReal.ofReal q)^k≠∞) hp
    simpa only [toReal_coe_nnnorm, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ q)] using hp'
  obtain ⟨k0,hk0⟩ := eventually_atTop.mp hb
  let C : ℝ := 1 + ∑ k ∈ Finset.range k0, ‖T^k‖
  have hC : 1  ≤  C := by
    have hh := Finset.sum_nonneg (fun k (_ : k∈Finset.range k0) => norm_nonneg (T^k))
    dsimp [C]
    linarith
  refine ⟨C,hC,fun k => ?_⟩
  by_cases hk : k0  ≤  k
  · exact (hk0 k hk).trans (le_mul_of_one_le_left (by positivity) hC)
  · have hc : ‖T^k‖  ≤  C := by
      have hh := Finset.single_le_sum (fun i (_ : i∈Finset.range k0) => norm_nonneg (T^i))
        (Finset.mem_range.mpr (by omega : k<k0))
      dsimp [C]
      linarith
    exact hc.trans (le_mul_of_one_le_right (by linarith : 0  ≤  C)
      (one_le_pow₀ hq.le))
/-- A coefficient-to-path-power bound gives the direction needed at a spectral root.
This statement keeps the combinatorial bridge explicit. -/
private theorem coefficient_spectral_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℂ) (c : ℕ → ℕ) (z D : ℝ)
    (hz : 0<z) (hz1 : z<1) (hD : 0 ≤ D) (hs : spectralRadius ℂ T=1)
    (hc : ∀ N : ℕ, (c N:ℝ)*z^N  ≤  D * ∑ k ∈ Finset.range (N+1), ‖T^k‖)
    (hb : IsBoundedUnder (·  ≤  ·) atTop
      (fun N : ℕ => Real.log (max 1 (c N):ℝ)/Real.log 2/(N:ℝ))) :
    limsup (fun N : ℕ => Real.log (max 1 (c N):ℝ)/Real.log 2/(N:ℝ)) atTop
       ≤  -Real.log z/Real.log 2 := by
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hnon : ∀ N : ℕ, 0 ≤ Real.log (max 1 (c N):ℝ)/Real.log 2/(N:ℝ) := by
    intro N
    apply div_nonneg _ (Nat.cast_nonneg N)
    apply div_nonneg _ h2.le
    apply Real.log_nonneg
    exact_mod_cast le_max_left 1 (c N)
  have hco : IsCoboundedUnder (·  ≤  ·) atTop
      (fun N : ℕ => Real.log (max 1 (c N):ℝ)/Real.log 2/(N:ℝ)) := by
    exact isCoboundedUnder_le_of_le atTop hnon
  apply (limsup_le_iff hco hb).mpr
  intro y hy
  let e := y-(-Real.log z/Real.log 2)
  have he : 0<e := sub_pos.mpr hy
  let q := Real.exp (e*Real.log 2/2)
  have hq : 1<q := Real.one_lt_exp_iff.mpr (by positivity)
  obtain ⟨C,hC,hpow⟩ := spectral_one_power_bound T hs q hq
  have hC0 : 0 ≤ C := by linarith
  let E := 1+D*C
  have hE : 0<E := by dsimp [E]; positivity
  have hcount (N : ℕ) : (max 1 (c N):ℝ)*z^N  ≤  E*((N:ℝ)+1)*q^N := by
    have hp : ∑ k ∈ Finset.range (N+1), ‖T^k‖  ≤  ((N:ℝ)+1)*C*q^N := by
      calc
        _  ≤  ∑ k ∈ Finset.range (N+1), C*q^N := by
          apply Finset.sum_le_sum
          intro k hk
          exact (hpow k).trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hq.le (by simpa using Finset.mem_range.mp hk))
            (by linarith))
        _ = _ := by simp; ring
    have hh := (hc N).trans (mul_le_mul_of_nonneg_left hp hD)
    have hzpow : z^N  ≤  1 := pow_le_one₀ hz.le hz1.le
    have hqp : 1 ≤ q^N := one_le_pow₀ hq.le
    have hp' : 1 ≤ ((N:ℝ)+1)*q^N := by nlinarith [show 0 ≤ (N:ℝ) from Nat.cast_nonneg N]
    by_cases hn : 1 ≤ c N
    · rw [max_eq_right (by exact_mod_cast hn)]
      dsimp [E]
      nlinarith [mul_nonneg hD (by linarith : 0 ≤ C)]
    · rw [max_eq_left (by exact_mod_cast le_of_not_ge hn)]
      dsimp [E]
      nlinarith [mul_nonneg hD (by linarith : 0 ≤ C),
        mul_nonneg (mul_nonneg hD (by linarith : 0 ≤ C))
          (mul_nonneg (by positivity : 0 ≤ (N:ℝ)+1) (by positivity : 0 ≤ q^N))]
  have herr : Tendsto (fun N : ℕ =>
      (Real.log E+Real.log ((N:ℝ)+1))/Real.log 2/(N:ℝ)) atTop (𝓝 0) := by
    have hnat : Tendsto (fun N : ℕ => (N:ℝ)+1) atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hlog := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hnat
    have hlog' : Tendsto (fun N : ℕ => Real.log ((N:ℝ)+1)/(N:ℝ)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using hlog
    have hconst := tendsto_const_div_atTop_nhds_zero_nat (Real.log E)
    have hx : Tendsto (fun N : ℕ =>
        (Real.log E/(N:ℝ)+Real.log ((N:ℝ)+1)/(N:ℝ))/Real.log 2) atTop (𝓝 0) := by
      simpa using (hconst.add hlog').div_const (Real.log 2)
    convert hx using 1
    ext N
    ring
  have hevent := herr.eventually (gt_mem_nhds (show (0:ℝ)<e/2 by positivity))
  filter_upwards [hevent,eventually_gt_atTop (0:ℕ)] with N hN hn
  have hn' : 0<(N:ℝ) := by exact_mod_cast hn
  have hmax : 0<(max 1 (c N):ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hh := Real.log_le_log (mul_pos hmax (pow_pos hz N)) (hcount N)
  rw [Real.log_mul hmax.ne' (pow_pos hz N).ne', Real.log_pow,
    Real.log_mul (mul_pos hE (by positivity)).ne' (pow_pos (by linarith : 0<q) N).ne',
    Real.log_mul hE.ne' (by positivity : (N:ℝ)+1≠0), Real.log_pow] at hh
  have hqlog : Real.log q=e*Real.log 2/2 := Real.log_exp _
  rw [hqlog] at hh
  have hdiv := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hh h2.le) hn'.le
  have hnorm :
      (Real.log (max 1 (c N):ℝ)+(N:ℝ)*Real.log z)/Real.log 2/(N:ℝ) =
      Real.log (max 1 (c N):ℝ)/Real.log 2/(N:ℝ)+Real.log z/Real.log 2 := by field_simp
  have hnorm' :
      (Real.log E+Real.log ((N:ℝ)+1)+(N:ℝ)*(e*Real.log 2/2))/Real.log 2/(N:ℝ) =
      (Real.log E+Real.log ((N:ℝ)+1))/Real.log 2/(N:ℝ)+e/2 := by field_simp
  rw [hnorm,hnorm'] at hdiv
  dsimp [e] at hN hdiv
  simp only [neg_div] at hN hdiv
  linarith
end D5.S1.Digit.Infinite.ResetCodebook.Transfer
set_option autoImplicit false
open scoped Matrix.Norms.Operator
namespace D5.S1.Digit.Infinite.ResetCodebook.Transfer
open D5.S1.Digit.Infinite.ResetCodebook
noncomputable section
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (next : ι → Bool → ι) (allow : ι → Bool → Prop)
/-- Finite factor words are counted before any rate or spectral argument. -/
private theorem factor_mass_le_paths
    (lang : Set (ℤ → Bool)) (z : ℝ) (hz : 0 ≤ z) (N : ℕ)
    (ext : ∀ w : Factors lang N, ∃ v : ι, accepts next allow v w.val) :
    (Statement.factorCount lang N:ℝ)*z^N  ≤ 
      ∑ k ∈ Finset.range (N+1), ∑ v, ∑ u, (transfer next allow z ^ k) v u := by
  letI : Finite (Factors lang N) := by
    apply Set.Finite.to_subtype
    apply (List.finite_length_le Bool N).subset
    intro w hw
    exact hw.1 ▸ D5.S1.Digit.Infinite.ResetCodebook.Coding.letter_length_le_weight w
  letI := Fintype.ofFinite (Factors lang N)
  let enc (w : Factors lang N) : List Bool × ι := (w.val,(ext w).choose)
  let total : Finset (List Bool × ι) :=
    (Finset.range (N+1)).biUnion (fun k => (wordSet k) ×ˢ Finset.univ)
  have hinj : Function.Injective enc := by
    intro u v h
    exact Subtype.ext (congrArg Prod.fst h)
  have hmem (w : Factors lang N) : enc w∈total := by
    apply Finset.mem_biUnion.mpr
    refine ⟨w.val.length,?_,?_⟩
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (by simpa only [w.property.1] using D5.S1.Digit.Infinite.ResetCodebook.Coding.letter_length_le_weight w.val))
    · exact Finset.mem_product.mpr ⟨(mem_wordSet w.val _).mpr rfl,Finset.mem_univ _⟩
  have hsum : ∑ w : Factors lang N, mass next allow z (enc w).2 (enc w).1  ≤ 
      ∑ p ∈ total, mass next allow z p.2 p.1 := by
    calc
      _ = ∑ p ∈ Finset.univ.image enc, mass next allow z p.2 p.1 :=
        (Finset.sum_image (by intro u _ v _ h; exact hinj h)).symm
      _  ≤  _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_iff.mpr (fun w _ => hmem w))
        (fun p _ _ => mass_nonneg next allow z hz p.2 p.1)
  have hleft : (∑ w : Factors lang N, mass next allow z (enc w).2 (enc w).1) =
      (Statement.factorCount lang N:ℝ)*z^N := by
    have he (w : Factors lang N) : mass next allow z (enc w).2 (enc w).1=z^N := by
      rw [mass_of_accepts next allow z _ _ (ext w).choose_spec,w.property.1]
    simp_rw [he]
    simp [Statement.factorCount,Nat.card_eq_fintype_card]
  rw [hleft] at hsum
  apply hsum.trans_eq
  rw [Finset.sum_biUnion]
  · simp_rw [Finset.sum_product]
    congr 1
    ext k
    rw [Finset.sum_comm]
    simp_rw [word_mass_eq_row]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    have hi := (mem_wordSet p.1 i).mp (Finset.mem_product.mp hp).1
    have hj := (mem_wordSet p.1 j).mp (Finset.mem_product.mp hp').1
    exact hij (hi.symm.trans hj)
end
end D5.S1.Digit.Infinite.ResetCodebook.Transfer
set_option autoImplicit false
open scoped Matrix.Norms.Operator NNReal ENNReal
namespace D5.S1.Digit.Infinite.ResetCodebook.Transfer
open D5.S1.Digit.Infinite.ResetCodebook
noncomputable section
attribute [local instance] Classical.propDecidable
private lemma lower_factor_mass_le_paths (K n N : ℕ) (d z : ℝ) (hz : 0≤z) :
    (Statement.factorCount (Statement.lowerLanguage K n d) N:ℝ)*z^N ≤
      ∑ k ∈ Finset.range (N+1), ∑ v, ∑ u, (lowerMatrix K n d z ^ k) v u := by
  apply factor_mass_le_paths _ _ _ _ hz N
  intro w
  obtain ⟨u,hu,i,hi⟩ := w.property.2
  exact ⟨vertexAt _ n u hu i,factor_accepts _ n w.val u hu i hi⟩
private lemma lowerComplex_pow (K n k : ℕ) (d z : ℝ) :
    lowerComplexMatrix K n d z ^ k = Complex.ofRealHom.mapMatrix (lowerMatrix K n d z ^ k) := by
  exact (map_pow Complex.ofRealHom.mapMatrix _ k).symm
private lemma lower_row_le_norm (K n k : ℕ) (d z : ℝ) (hz : 0≤z)
    (v : Vertex (Statement.lowerLanguage K n d) n) :
    (∑ u, (lowerMatrix K n d z ^ k) v u) ≤ ‖lowerComplexMatrix K n d z ^ k‖ := by
  have hentry (u : Vertex (Statement.lowerLanguage K n d) n) :
      ‖(lowerComplexMatrix K n d z ^ k) v u‖ = (lowerMatrix K n d z ^ k) v u := by
    rw [lowerComplex_pow]
    change ‖((lowerMatrix K n d z ^ k) v u:ℂ)‖ = _
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    exact transfer_pow_nonneg _ _ z hz k v u
  calc
    _ = ∑ u, ‖(lowerComplexMatrix K n d z ^ k) v u‖ := by simp_rw [hentry]
    _ = ((∑ u, ‖(lowerComplexMatrix K n d z ^ k) v u‖₊):ℝ) := by simp
    _ ≤ (((Finset.univ.sup fun i => ∑ u, ‖(lowerComplexMatrix K n d z ^ k) i u‖₊):ℝ≥0):ℝ) := by
      have hNN :
          (∑ u, ‖(lowerComplexMatrix K n d z ^ k) v u‖₊) ≤
            Finset.univ.sup (fun i : Vertex (Statement.lowerLanguage K n d) n =>
              ∑ u, ‖(lowerComplexMatrix K n d z ^ k) i u‖₊) :=
        Finset.le_sup (f := fun i : Vertex (Statement.lowerLanguage K n d) n =>
          ∑ u, ‖(lowerComplexMatrix K n d z ^ k) i u‖₊) (Finset.mem_univ v)
      simpa only [NNReal.coe_sum] using (NNReal.coe_le_coe.mpr hNN)
    _ = _ := (Matrix.linfty_opNorm_def _).symm
private lemma lower_factor_mass_le_norm_powers (K n N : ℕ) (d z : ℝ) (hz : 0≤z) :
    (Statement.factorCount (Statement.lowerLanguage K n d) N:ℝ)*z^N ≤
      (Fintype.card (Vertex (Statement.lowerLanguage K n d) n):ℝ) *
        ∑ k ∈ Finset.range (N+1), ‖lowerComplexMatrix K n d z ^ k‖ := by
  apply (lower_factor_mass_le_paths K n N d z hz).trans
  calc
    _ ≤ ∑ k ∈ Finset.range (N+1), ∑ _v : Vertex (Statement.lowerLanguage K n d) n,
      ‖lowerComplexMatrix K n d z ^ k‖ := by
      apply Finset.sum_le_sum
      intro k _
      exact Finset.sum_le_sum (fun v _ => lower_row_le_norm K n k d z hz v)
    _ = _ := by simp [←Finset.mul_sum] <;> ring
/-- This direction suffices for 62.18; it needs no Perron eigenvector or irreducibility. -/
private theorem lower_language_rate_le_spectral_gamma (K n : ℕ) (d z : ℝ)
    (hz : SpectralRoot K n d z) :
    Statement.rate (Statement.lowerLanguage K n d) ≤ gamma z := by
  apply coefficient_spectral_bound (lowerComplexMatrix K n d z)
    (Statement.factorCount (Statement.lowerLanguage K n d)) z
    (Fintype.card (Vertex (Statement.lowerLanguage K n d) n)) hz.1 hz.2.1
    (by positivity) hz.2.2
  · intro N
    exact lower_factor_mass_le_norm_powers K n N d z hz.1.le
  · exact D5.S1.Digit.Infinite.ResetCodebook.Coding.weightedReadout_bounded _
end
end D5.S1.Digit.Infinite.ResetCodebook.Transfer
set_option autoImplicit false
namespace D5.S1.Digit.Infinite.ResetCodebook.Transfer
open D5.S1.Digit.Infinite.ResetCodebook
noncomputable section
private theorem original_language_rate_le_spectral_gamma (K n : ℕ) (d z : ℝ)
    (hn : 0<n) (hKn : K≤n) (hz : OriginalSpectralRoot K n d z) :
    Statement.rate (Statement.lowerLanguage K n d) ≤ gamma z := by
  apply lower_language_rate_le_spectral_gamma K n d z
  unfold OriginalSpectralRoot at hz
  rwa [originalLowerComplexMatrix_eq K n d z hn hKn] at hz
end
end D5.S1.Digit.Infinite.ResetCodebook.Transfer
set_option autoImplicit false
set_option maxHeartbeats 1600000
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open scoped Topology
namespace D5.S1.Digit.Infinite.ResetCodebook.Coding
open D5.S1.Digit.Infinite.ResetCodebook
/-- Clause-complete 62.18 in the explicit weighted-language limsup representation. -/
private theorem codebook_language_realization
    (anchor : Bool) (K M N : ℕ) (b d : ℝ)
    (hK : 2 ≤ K) (hM : 1 ≤ M) (hN : 0 < N)
    (hbudget : lambda-g^2*chi^K*h false < b ∧
      b < lambda-g^2*chi^K*(A false/(1-rho*chi^K)))
    (hd : d=(lambda-b)/(g^2*chi^K))
    (hreset : max (max (X false) (Y false)) d < Statement.B M)
    (hne : (Statement.codebook anchor K N d).Nonempty) :
    Statement.target6218Language anchor K M N b d hK hM hN hbudget hd hreset hne := by
  have hr : max (X false) (Y false) < Statement.B M :=
    (le_max_left _ _).trans_lt hreset
  have hr0 : initial false anchor < Statement.B M := by
    cases anchor
    · exact (le_max_left _ _).trans_lt hr
    · exact (le_max_right _ _).trans_lt hr
  obtain ⟨he,hact,n,hKn,hcut,hmem⟩ :=
    reset_complete_family_membership anchor K M N b d hK hM hbudget.1 hd hr
  have hrate := (complete_lower_language_count_and_rate anchor K M N n d hK hM hr0 hcut hne).2
  change (Statement.codebook anchor K N d).Finite ∧ _
  refine ⟨codebook_finite anchor K N d,he,hact,?_,n,hKn,?_,hmem,hrate⟩
  · intro w hw
    have hcm := concatenation_cap_margin anchor K M N d hK hM hr0 w hw
    refine ⟨hcm.1,?_,?_⟩
    · intro i
      simpa only [past_eq_pastRec,state_eq_stateRec] using stateRec_limit w i
    · intro i hi
      simpa only [state_eq_stateRec,initial] using hcm.2 i hi
  · simpa only [initial] using hcut
end D5.S1.Digit.Infinite.ResetCodebook.Coding
set_option autoImplicit false
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open scoped Topology
namespace D5.S1.Digit.Infinite.ResetCodebook.Statement
open D5.S1.Digit.Infinite.ResetCodebook
/-- The root family records precisely the defining equations from 62.15. -/
def RootFamily (K : ℕ) (d : ℝ) := ∀ n : ℕ, K≤n → {z : ℝ // D5.S1.Digit.Infinite.ResetCodebook.Transfer.OriginalSpectralRoot K n d z}
/-- Source-aligned 62.18 with spectral-root gamma. The root family is the original 62.15
notation made explicit, and is not an assumed identification or rate inequality. -/
noncomputable def target6218 (anchor : Bool) (K M N : ℕ) (b d : ℝ)
    (hK : 2 ≤ K) (hM : 1 ≤ M) (hN : 0 < N)
    (hbudget : lambda-g^2*chi^K*h false < b ∧
      b < lambda-g^2*chi^K*(A false/(1-rho*chi^K)))
    (hd : d=(lambda-b)/(g^2*chi^K))
    (hreset : max (max (X false) (Y false)) d < D5.S1.Digit.Infinite.ResetCodebook.Statement.B M)
    (hne : (D5.S1.Digit.Infinite.ResetCodebook.Statement.codebook anchor K N d).Nonempty)
    (roots : RootFamily K d) : Prop :=
  let delta := D5.S1.Digit.Infinite.ResetCodebook.Statement.B M-(if anchor then Y false else X false)
  let eps := chi^(K-1)*delta*g^N
  0<delta ∧ 0<eps ∧
  (D5.S1.Digit.Infinite.ResetCodebook.Statement.codebook anchor K N d).Finite ∧ 0<D5.S1.Digit.Infinite.ResetCodebook.Statement.actualEps anchor K M N b ∧
  D5.S1.Digit.Infinite.ResetCodebook.Statement.finiteActual anchor K M N b d hM ∧
  (∀ omega, D5.S1.Digit.Infinite.ResetCodebook.Statement.concatenation anchor K M N d hM omega →
    D5.S1.Digit.Infinite.ResetCodebook.Statement.cap K omega ∧
    (∀ i, Filter.Tendsto (fun n => D5.S1.Digit.Infinite.ResetCodebook.Statement.past omega i n 0) Filter.atTop
      (nhds (D5.S1.Digit.Infinite.ResetCodebook.Statement.state omega i))) ∧
    ∀ i, D5.S1.Digit.Infinite.ResetCodebook.Statement.high K omega i → chi^(K-1)*d+eps ≤ D5.S1.Digit.Infinite.ResetCodebook.Statement.state omega i) ∧
  ∃ n : ℕ, ∃ hn : K≤n, h false*rho^n<eps ∧
    (∀ omega, D5.S1.Digit.Infinite.ResetCodebook.Statement.concatenation anchor K M N d hM omega →
      D5.S1.Digit.Infinite.ResetCodebook.Transfer.RawGraphLabels K n d omega) ∧
    Real.log (Nat.card {v // v∈D5.S1.Digit.Infinite.ResetCodebook.Statement.codebook anchor K N d}:ℝ)/Real.log 2/(N+20+6*M:ℝ)
      ≤ D5.S1.Digit.Infinite.ResetCodebook.Transfer.gamma (roots n hn).val
end D5.S1.Digit.Infinite.ResetCodebook.Statement
namespace D5.S1.Digit.Infinite.ResetCodebook.Transfer
open D5.S1.Digit.Infinite.ResetCodebook
private theorem spectral_codebook_realization
    (anchor : Bool) (K M N : ℕ) (b d : ℝ)
    (hK : 2 ≤ K) (hM : 1 ≤ M) (hN : 0 < N)
    (hbudget : lambda-g^2*chi^K*h false < b ∧
      b < lambda-g^2*chi^K*(A false/(1-rho*chi^K)))
    (hd : d=(lambda-b)/(g^2*chi^K))
    (hreset : max (max (X false) (Y false)) d < D5.S1.Digit.Infinite.ResetCodebook.Statement.B M)
    (hne : (D5.S1.Digit.Infinite.ResetCodebook.Statement.codebook anchor K N d).Nonempty)
    (roots : D5.S1.Digit.Infinite.ResetCodebook.Statement.RootFamily K d) :
    D5.S1.Digit.Infinite.ResetCodebook.Statement.target6218 anchor K M N b d hK hM hN hbudget hd hreset hne roots := by
  have hold := D5.S1.Digit.Infinite.ResetCodebook.Coding.codebook_language_realization anchor K M N b d hK hM hN hbudget hd hreset hne
  obtain ⟨hfin,he,hact,haux,n,hn,hcut,hmem,hrate⟩ := hold
  have hxy : max (X false) (Y false)<D5.S1.Digit.Infinite.ResetCodebook.Statement.B M :=
    lt_of_le_of_lt (le_max_left _ _) hreset
  have hD : (if anchor then Y false else X false)<D5.S1.Digit.Infinite.ResetCodebook.Statement.B M := by
    cases anchor
    · exact lt_of_le_of_lt (le_max_left _ _) hxy
    · exact lt_of_le_of_lt (le_max_right _ _) hxy
  have hdelta := sub_pos.mpr hD
  have hg : 0<g := by have := g_bounds; linarith
  have heps := mul_pos (mul_pos (pow_pos (parameters false).2.2.1 (K-1)) hdelta)
    (pow_pos hg N)
  have hn0 : 0<n := by omega
  refine ⟨hdelta,heps,hfin,he,hact,haux,n,hn,hcut,?_,?_⟩
  · intro omega ho
    exact (raw_labels_iff_lower_language K n d hn0 hn omega).mpr (hmem omega ho)
  · exact hrate.trans (original_language_rate_le_spectral_gamma K n d _ hn0 hn
      (roots n hn).property)
end D5.S1.Digit.Infinite.ResetCodebook.Transfer
set_option autoImplicit false
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open scoped Topology
namespace D5.S1.Digit.Infinite.ResetCodebook.Spectral
open D5.S1.Digit.Infinite.ResetCodebook
noncomputable section
/-- The uniquely defined lower spectral root. -/
def lowerRoot (K n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hKn : K ≤ n) : ℝ :=
  (original_root_exists_unique K n d hK hKn).choose
private lemma lowerRoot_spec (K n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hKn : K ≤ n) :
    D5.S1.Digit.Infinite.ResetCodebook.Transfer.OriginalSpectralRoot K n d (lowerRoot K n d hK hKn) :=
  (original_root_exists_unique K n d hK hKn).choose_spec.1
def rootFamily (K : ℕ) (d : ℝ) (hK : 2 ≤ K) : Statement.RootFamily K d :=
  fun n hn => ⟨lowerRoot K n d hK hn,lowerRoot_spec K n d hK hn⟩
/-- Original 62.18, with its lower spectral root supplied by the root existence theorem. -/
theorem reset_codebook_common_realization
    (anchor : Bool) (K M N : ℕ) (b d : ℝ)
    (hK : 2 ≤ K) (hM : 1 ≤ M) (hN : 0 < N)
    (hbudget : lambda-g^2*chi^K*h false < b ∧
      b < lambda-g^2*chi^K*(A false/(1-rho*chi^K)))
    (hd : d=(lambda-b)/(g^2*chi^K))
    (hreset : max (max (X false) (Y false)) d < Statement.B M)
    (hne : (Statement.codebook anchor K N d).Nonempty) :
    Statement.target6218 anchor K M N b d hK hM hN hbudget hd hreset hne
      (rootFamily K d hK) := by
  exact D5.S1.Digit.Infinite.ResetCodebook.Transfer.spectral_codebook_realization anchor K M N b d hK hM hN hbudget hd hreset hne (rootFamily K d hK)
end
end D5.S1.Digit.Infinite.ResetCodebook.Spectral
