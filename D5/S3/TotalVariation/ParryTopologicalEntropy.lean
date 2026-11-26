/- GID: D5/S3/TotalVariation/ParryTopologicalEntropy
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParryTopologicalEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The topological entropy of the bilateral forbidden-one-run shift equals the logarithm of its Perron root. -/

import D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy
import D5.S1.Words.AdmissibleWords.KBonacciIntegerInterval
import D5.S0.Tower.DBonacci.PerronRoot
import D5.S3.TotalVariation.ParryBilateralLaw
import Mathlib.Dynamics.TopologicalEntropy.Semiconj

open Set Filter Dynamics SymbolicDynamics
open D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacci.PerronRoot
open D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy
open D5.S1.Words.AdmissibleWords.KBonacciIntegerInterval
open D5.S1.Words.ClosedRunStarts
open scoped Topology

namespace D5.S3.TotalVariation.ParryTopologicalEntropy

/-- The one-sided Boolean subshift with no run of k true bits. -/
private def subshift (k : ℕ) : Set (ℕ → Bool) :=
  {x | ∀ t : ℕ, ∃ j : Fin k, x (t + j.val) = false}

private theorem prefix_card (k n : ℕ) (hk : 0 < k) :
    prefixCount (subshift k) n = Fintype.card (DBonacciName k n) := by
  have exact_prefix : (Set.range fun x : subshift k => fun i : Fin n => x.val i.val) =
      {w | DBonacciAdmissible k n w} := by
    ext w
    change (∃ x : subshift k, (fun i : Fin n => x.val i.val) = w) ↔ DBonacciAdmissible k n w
    rw [scanner_iff_literal k n hk]
    constructor
    · rintro ⟨x, rfl⟩ t he
      obtain ⟨j, hj⟩ := x.property t
      have hlt : t + j.val < n := by have := j.isLt; have := he.1; omega
      have hlo : t ≤ t + j.val := by omega
      have hup : t + j.val < t + k := Nat.add_lt_add_left j.isLt t
      have ht : x.val (t + j.val) = true := he.2 ⟨t + j.val, hlt⟩ hlo hup
      rw [hj] at ht
      exact Bool.false_ne_true ht
    · intro hw
      let x (i : ℕ) := if h : i < n then w ⟨i, h⟩ else false
      refine ⟨⟨x, ?_⟩, ?_⟩
      · intro t
        by_cases ht : t + k ≤ n
        · by_contra! hn
          apply hw t
          refine ⟨ht, fun i hl hr => ?_⟩
          let j : Fin k := ⟨i.val - t, by omega⟩
          have he : t + j.val = i.val := by dsimp [j]; omega
          have h := hn j
          rw [he] at h
          change (if hi : i.val < n then w ⟨i.val, hi⟩ else false) ≠ false at h
          rw [dite_eq_left i.isLt] at h
          exact Bool.eq_true_of_ne_false h
        · have hk' : k - 1 < k := by omega
          refine ⟨⟨k - 1, hk'⟩, ?_⟩
          exact dite_eq_right (show ¬ t + (k - 1) < n by omega)
      · funext i
        exact dite_eq_left i.isLt
  unfold prefixCount
  rw [exact_prefix, Nat.card_eq_fintype_card]
  rfl

private theorem count_bounds (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    dbonacciPerronRoot k ^ n ≤ (Fintype.card (DBonacciName k n) : ℝ) ∧
      (Fintype.card (DBonacciName k n) : ℝ) ≤ 2 ^ k * dbonacciPerronRoot k ^ n := by
  let b := dbonacciPerronRoot k
  have h1 : 1 < b := one_lt_dbonacciPerronRoot k hk
  have h2 : b < 2 := dbonacciPerronRoot_lt_two k hk
  have hp : 0 ≤ b := by linarith
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < k
    · rw [dbonacci_name_card_of_lt k n hn, Nat.cast_pow, Nat.cast_ofNat]
      exact ⟨pow_le_pow_left₀ hp h2.le n,
        (pow_le_pow_right₀ (by norm_num) hn.le).trans (le_mul_of_one_le_right (by positivity)
          (one_le_pow₀ h1.le))⟩
    · let m := n-k
      have he : m+k = n := by dsimp [m]; omega
      rw [← he, dbonacci_name_card_recurrence k m (by omega), Nat.cast_sum]
      have sum_root : ∑ i ∈ Finset.range k, b ^ (m+i) = b ^ (m+k) := by
        calc
          _ = b ^ m * ∑ i ∈ Finset.range k, b ^ i := by simp_rw [pow_add, Finset.mul_sum]
          _ = b ^ (m + k) := by
            rw [pow_add]
            exact congrArg (b ^ m * ·) (dbonacciPerronRoot_characteristic k hk).symm
      constructor
      · rw [← sum_root]
        exact Finset.sum_le_sum fun i hi =>
          (ih (m+i) (by have := Finset.mem_range.mp hi; omega)).1
      · rw [← sum_root, Finset.mul_sum]
        exact Finset.sum_le_sum fun i hi =>
          (ih (m+i) (by have := Finset.mem_range.mp hi; omega)).2

private theorem one_sided_entropy (k : ℕ) (hk : 2 ≤ k) :
    coverEntropy (FullShift.shift (1 : ℕ)) (subshift k) =
      (Real.log (dbonacciPerronRoot k) : EReal) := by
  classical
  let b := dbonacciPerronRoot k
  have hb : 0 < b := lt_trans zero_lt_one (one_lt_dbonacciPerronRoot k hk)
  have hk0 : 0 < k := by omega
  have hS : (subshift k).Nonempty := ⟨fun _ => false, fun t => ⟨⟨0,hk0⟩, rfl⟩⟩
  have hinv : MapsTo (FullShift.shift (1 : ℕ)) (subshift k) (subshift k) := by
    intro x hx t
    obtain ⟨j,hj⟩ := hx (t+1)
    refine ⟨j, ?_⟩
    simpa only [FullShift.shift_apply, ← Nat.add_assoc, Nat.add_comm 1 t] using hj
  obtain ⟨h, _, _, hh, hcover⟩ := prefix_growth_entropy (subshift k) hS hinv
  have hg : Tendsto (fun n : ℕ => Real.log (prefixCount (subshift k) n : ℝ) / n)
      atTop (𝓝 (Real.log b)) := by
    have hu : Tendsto (fun n : ℕ => Real.log b + Real.log ((2 : ℝ)^k) / n)
        atTop (𝓝 (Real.log b)) := by
      simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat
        (Real.log ((2 : ℝ)^k)))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [prefix_card k n hk0, le_div_iff₀ hn']
      have h₁ := Real.log_le_log (pow_pos hb n) (count_bounds k hk n).1
      rw [Real.log_pow] at h₁
      exact (mul_comm _ _).le.trans h₁
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [prefix_card k n hk0, div_le_iff₀ hn']
      have hpos := (pow_pos hb n).trans_le (count_bounds k hk n).1
      calc
        _ ≤ Real.log ((2 : ℝ) ^ k * b ^ n) :=
          Real.log_le_log hpos (count_bounds k hk n).2
        _ = _ := by
          rw [Real.log_mul (by positivity) (pow_ne_zero _ hb.ne'), Real.log_pow b]
          field_simp
          ring
  rw [hcover, tendsto_nhds_unique hh hg]



open D5.S3.TotalVariation.ParryBilateralLaw (Admissible)
open scoped Uniformity

private def cut (L : ℕ) (x : ℤ → Bool) (n : ℕ) : Bool :=
  x ((n : ℤ) - (L : ℤ))

private theorem cut_semiconj (L : ℕ) :
    Function.Semiconj (cut L) (FullShift.shift (1 : ℤ)) (FullShift.shift (1 : ℕ)) := by
  intro x
  funext n
  simp only [FullShift.shift_apply, cut, Nat.cast_add, Nat.cast_one]
  congr 1
  omega

private theorem cut_image (k L : ℕ) (hk : 0 < k) :
    cut L '' {x | Admissible k x} = subshift k := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ t
    obtain ⟨j, hj⟩ := hx ((t : ℤ) - (L : ℤ))
    refine ⟨j, ?_⟩
    simp only [cut, Nat.cast_add]
    rwa [show (t : ℤ) + (j.val : ℤ) - (L : ℤ) =
      (t : ℤ) - (L : ℤ) + (j.val : ℤ) by omega]
  · intro hy
    let x (t : ℤ) := if 0 ≤ t + L then y (t + L).toNat else false
    refine ⟨x, ?_, ?_⟩
    · intro t
      by_cases h : 0 ≤ t + (L : ℤ)
      · obtain ⟨j, hj⟩ := hy (t + L).toNat
        refine ⟨j, ?_⟩
        change (if 0 ≤ t + (j.val : ℤ) + L then y (t + (j.val : ℤ) + L).toNat else false) = false
        rw [ite_eq_left (by omega : 0 ≤ t + (j.val : ℤ) + L),
          show (t + (j.val : ℤ) + L).toNat = (t + L).toNat + j.val by omega]
        exact hj
      · refine ⟨⟨0, hk⟩, ?_⟩
        simp [x, h]
    · funext n
      have he : (n : ℤ) - (L : ℤ) + (L : ℤ) = n := by omega
      simp [cut, x, he]

private abbrev cutUniformity (L : ℕ) : UniformSpace (ℤ → Bool) :=
  UniformSpace.comap (cut L) inferInstance

private theorem cutUniformity_antitone : Antitone cutUniformity := by
  intro L M hLM
  let skip (y : ℕ → Bool) (n : ℕ) := y (n + (M - L))
  have factor : cut L = skip ∘ cut M := by
    funext x n
    simp only [cut, Function.comp_apply, skip, Nat.cast_add]
    rw [Int.natCast_sub hLM]
    congr 1
    omega
  have hu : UniformContinuous skip := Pi.uniformContinuous_precomp' (fun _ : ℕ => Bool)
    (fun n : ℕ => n + (M - L))
  change UniformSpace.comap (cut M) _ ≤ UniformSpace.comap (cut L) _
  rw [factor, UniformSpace.comap_comap]
  exact UniformSpace.comap_mono (uniformContinuous_iff_le_comap.mp hu)

private theorem uniformity_iInf_cut :
    (inferInstance : UniformSpace (ℤ → Bool)) = ⨅ L, cutUniformity L := by
  apply le_antisymm
  · refine le_iInf fun L => uniformContinuous_iff_le_comap.mp ?_
    exact Pi.uniformContinuous_precomp' (fun _ : ℤ => Bool)
      (fun n : ℕ => (n : ℤ) - (L : ℤ))
  · rw [Pi.uniformSpace_eq]
    refine le_iInf fun t => ?_
    let L := (-t).toNat
    let n := (t + (L : ℤ)).toNat
    have he : (n : ℤ) - (L : ℤ) = t := by dsimp [n, L]; omega
    refine (iInf_le cutUniformity L).trans ?_
    have hu := uniformContinuous_iff_le_comap.mp
      (Pi.uniformContinuous_proj (fun _ : ℕ => Bool) n)
    have h := UniformSpace.comap_mono (f := cut L) hu
    dsimp only at h
    rw [← UniformSpace.comap_comap] at h
    simpa only [cutUniformity, Function.comp_def, cut, he] using h

/-- Decide membership in the native bilateral forbidden-run path space. -/
noncomputable def allowedPath (k : ℕ) (x : ℤ → Bool) : Bool := by
  classical
  exact decide (Admissible k x)

/-- The actual bilateral forbidden-one-run shift has Perron logarithmic entropy. -/
theorem bilateral_entropy (k : ℕ) (hk : 2 ≤ k) :
    coverEntropy (FullShift.shift (1 : ℤ)) {x | allowedPath k x = true} =
      (Real.log (dbonacciPerronRoot k) : EReal) := by
  classical
  let S : Set (ℤ → Bool) := {x | Admissible k x}
  have native : {x | allowedPath k x = true} = S := by
    ext x
    simp [allowedPath, S]
  rw [native]
  let T := FullShift.shift (A := Bool) (1 : ℤ)
  have cut_entropy (L : ℕ) : @coverEntropy _ (cutUniformity L) T S =
      (Real.log (dbonacciPerronRoot k) : EReal) := by
    rw [cutUniformity, ← coverEntropy_image_of_comap _ (cut_semiconj L) S,
      show cut L '' S = subshift k from cut_image k L (by omega), one_sided_entropy k hk]
  change @coverEntropy _ inferInstance T S = _
  rw [uniformity_iInf_cut]
  apply le_antisymm
  · refine iSup₂_le fun U hU => ?_
    rw [iInf_uniformity, Filter.mem_iInf_of_directed] at hU
    · obtain ⟨L, hL⟩ := hU
      rw [← cut_entropy L]
      let : UniformSpace (ℤ → Bool) := cutUniformity L
      exact coverEntropyEntourage_le_coverEntropy T S hL
    · intro L M
      exact ⟨max L M, cutUniformity_antitone (le_max_left _ _),
        cutUniformity_antitone (le_max_right _ _)⟩
  · rw [← cut_entropy 0]
    exact coverEntropy_antitone T S (iInf_le cutUniformity 0)

#print axioms bilateral_entropy

end D5.S3.TotalVariation.ParryTopologicalEntropy
