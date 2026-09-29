/- GID: D5/S3/TotalVariation/ParryBilateralMixing
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParryBilateralMixing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual bilateral Parry mixing, ergodicity, and unattained zero selector defect. -/

import D5.S3.TotalVariation.ParryBilateralLaw
import D5.S3.TotalVariation.ParryWindowUpperBound
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.Dynamics.Ergodic.Ergodic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal symmDiff
open D5.S3.TotalVariation.TwistedResetPaths
open D5.S3.TotalVariation.ParryResetLaw
open D5.S3.TotalVariation.ParryBilateralLaw
open D5.S3.TotalVariation.ParryTwistedComparison
open D5.S3.TotalVariation.TwistedPrefixComparison
open D5.S3.TotalVariation.ParryWindowUpperBound
open D5.S3.TotalVariation.Pinsker
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.DataProcessing
open D5.S3.Divergence.ClassicalDPI

namespace D5.S3.TotalVariation.ParryBilateralMixing

/-- The actual bilateral Parry source mixes on every pair of fixed measurable
sets. Its fair anchored extension is ergodic, every measurable relation selector
has positive defect, and the infimum of these defects is zero. The joint block
formula includes every integer origin, zero gap, and forbidden word. -/
theorem bilateral_parry_mixing (k : ℕ) (hk : 2 ≤ k) :
    ∃ (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
      (μ : ProbabilityMeasure (RelationPath k)) (ν : ProbabilityMeasure (ℤ → State k)),
      (∀ (b : Bool) (r : RelationPath k) (t : ℤ),
        ((e (b, r)).val t).1 = signAt b r.val t) ∧
      (∀ (z : Bool × RelationPath k) (t : ℤ),
        let j := ((e z).val t).2.val
        z.2.val (t - (j : ℤ) - 1) = false ∧
        ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true) ∧
      (∀ x : ResetPath k,
        (e.symm x).1 = (x.val 0).1 ∧ (e.symm x).2.val = readRelation x.val) ∧
      (∀ z : Bool × RelationPath k,
        (e (xor z.1 (!z.2.val 0), relationShift z.2)).val =
          fun t => (e z).val (t + 1)) ∧
      (μ : Measure (RelationPath k)).map relationShift = μ ∧
      (ν : Measure (ℤ → State k)).map (fun x t => x (t + 1)) = ν ∧
      (fairAnchor.prod (μ : Measure (RelationPath k))).map
        (fun z => (e z).val) = ν ∧
      (∀ (ell : ℤ) (m : ℕ) (w : Fin (m + 1) → State k),
        (ν : Measure (ℤ → State k))
          {x | (fun i : Fin (m + 1) => x (ell + i.val)) = w} =
          ENNReal.ofReal (parryLaw k (w 0) * ∏ i : Fin m,
            kernel k (parryParameter k) (w i.castSucc) (w i.succ))) ∧
      (∀ (ell : ℤ) (m : ℕ) (v : Fin (m + 1) → Fin k),
        (μ : Measure (RelationPath k))
          {r | (fun i : Fin (m + 1) => ((e (false, r)).val (ell + i.val)).2) = v} =
          ENNReal.ofReal (suffixLaw k (v 0)) * ∏ i : Fin m,
            ENNReal.ofReal (suffixKernel k (v i.castSucc) (v i.succ))) ∧
      (∀ (ell : ℤ) (a b g : ℕ)
        (u : Fin (a + 1) → State k) (v : Fin (b + 1) → State k),
        (ν : Measure (ℤ → State k)).real
          ({x | (fun i : Fin (a + 1) => x (ell + i.val)) = u} ∩
           {x | (fun i : Fin (b + 1) => x (ell + a + g + i.val)) = v}) =
        (parryLaw k (u 0) * ∏ i : Fin a,
          kernel k (parryParameter k) (u i.castSucc) (u i.succ)) *
        (kernel k (parryParameter k) ^ g) (u (Fin.last a)) (v 0) *
        ∏ i : Fin b, kernel k (parryParameter k) (v i.castSucc) (v i.succ)) ∧
      (∀ (ell : ℤ) (a b g : ℕ)
        (A : Finset (Fin (a + 1) → State k)) (B : Finset (Fin (b + 1) → State k)),
        |(ν : Measure (ℤ → State k)).real
          ({x | (fun i : Fin (a + 1) => x (ell + i.val)) ∈ A} ∩
           {x | (fun i : Fin (b + 1) => x (ell + a + g + i.val)) ∈ B}) -
         (ν : Measure (ℤ → State k)).real
           {x | (fun i : Fin (a + 1) => x (ell + i.val)) ∈ A} *
         (ν : Measure (ℤ → State k)).real
           {x | (fun i : Fin (b + 1) => x i.val) ∈ B}| ≤ (3 / 4 : ℝ) ^ (g / 3)) ∧
      (∀ (A B : Set (ℤ → State k)), MeasurableSet A → MeasurableSet B →
        Tendsto (fun n : ℕ => (ν : Measure (ℤ → State k)).real
          (A ∩ ((fun x t => x (t + 1))^[n]) ⁻¹' B)) atTop
          (𝓝 ((ν : Measure (ℤ → State k)).real A * (ν : Measure (ℤ → State k)).real B))) ∧
      (let ρ := fairAnchor.prod (μ : Measure (RelationPath k))
       let T : (Bool × RelationPath k) → Bool × RelationPath k :=
         fun z => (xor z.1 (!z.2.val 0), relationShift z.2)
       (∀ (A B : Set (Bool × RelationPath k)), MeasurableSet A → MeasurableSet B →
         Tendsto (fun n : ℕ => ρ (A ∩ T^[n] ⁻¹' B)) atTop (𝓝 (ρ A * ρ B))) ∧
       Ergodic T ρ ∧
       ∀ h : RelationPath k → Bool, Measurable h →
         (¬ ∀ᵐ r ∂(μ : Measure (RelationPath k)),
           h (relationShift r) = xor (h r) (!r.val 0)) ∧
         0 < (μ : Measure (RelationPath k)).real
           {r | xor (xor (h (relationShift r)) (h r)) (!r.val 0) = true}) ∧
      sInf {d : ℝ | ∃ h : RelationPath k → Bool, Measurable h ∧
        d = (μ : Measure (RelationPath k)).real
          {r | xor (xor (h (relationShift r)) (h r)) (!r.val 0) = true}} = 0 := by
  classical
  let : NeZero k := ⟨by omega⟩
  obtain ⟨e, μ, ν, hsign, hsuffix, hinverse, hcode, hμshift, hνshift, hpush,
    hcyl, hsource⟩ := bilateral_parry_law k hk
  let Q : Matrix (State k) (State k) ℝ := kernel k (parryParameter k)
  let π := parryLaw k
  obtain ⟨_, _, _, hQ, hrow, hπ, hπsum, hstat, _⟩ := parry_stationary_law k hk
  let C (ell : ℤ) (m : ℕ) (w : Fin (m + 1) → State k) : Set (ℤ → State k) :=
    {x | (fun i : Fin (m + 1) => x (ell + i.val)) = w}
  let H (m : ℕ) (w : Fin (m + 1) → State k) : ℝ :=
    ∏ i : Fin m, Q (w i.castSucc) (w i.succ)
  let L (m : ℕ) (w : Fin (m + 1) → State k) : ℝ := π (w 0) * H m w
  have hH (m : ℕ) (w : Fin (m + 1) → State k) : 0 ≤ H m w :=
    Finset.prod_nonneg fun i _ => hQ _ _
  have hL (m : ℕ) (w : Fin (m + 1) → State k) : 0 ≤ L m w :=
    mul_nonneg (hπ _) (hH m w)
  have hC (ell : ℤ) (m : ℕ) (w : Fin (m + 1) → State k) :
      MeasurableSet (C ell m w) :=
    (measurable_pi_lambda _ fun i => measurable_pi_apply (ell + i.val))
      (measurableSet_singleton w)
  have hmass (ell : ℤ) (m : ℕ) (w : Fin (m + 1) → State k) :
      (ν : Measure (ℤ → State k)).real (C ell m w) = L m w := by
    rw [measureReal_def, show (ν : Measure (ℤ → State k)) (C ell m w) =
      ENNReal.ofReal (L m w) from hcyl ell m w, ENNReal.toReal_ofReal (hL m w)]
  have hsnoc (a : ℕ) (u : Fin (a + 1) → State k) (s : State k) :
      L (a + 1) (Fin.snoc u s) = L a u * Q (u (Fin.last a)) s := by
    simp [L, H, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      -Fin.castSucc_succ, Fin.succ_castSucc, mul_assoc]
  have hjoint : ∀ (g : ℕ) (ell : ℤ) (a b : ℕ)
      (u : Fin (a + 1) → State k) (v : Fin (b + 1) → State k),
      (ν : Measure (ℤ → State k)).real
        (C ell a u ∩ C (ell + a + g + 1) b v) =
        L a u * (Q ^ (g + 1)) (u (Fin.last a)) (v 0) * H b v := by
    intro g
    induction g with
    | zero =>
      intro ell a b u v
      let w : Fin (a + (b + 1) + 1) → State k :=
        fun i => Fin.append u v (Fin.cast (by omega) i)
      have wl (i : Fin (a + 1)) : w ⟨i.val, by omega⟩ = u i := by
        exact Fin.append_left u v i
      have wr (i : Fin (b + 1)) : w ⟨a + 1 + i.val, by omega⟩ = v i := by
        exact Fin.append_right u v i
      have he : C ell a u ∩ C (ell + a + 0 + 1) b v = C ell (a + (b + 1)) w := by
        ext x
        simp only [C, Set.mem_inter_iff, Set.mem_ofPred_eq, funext_iff]
        constructor
        · rintro ⟨hu, hv⟩ i
          by_cases hi : i.val < a + 1
          · rw [show i = (⟨i.val, by omega⟩ : Fin (a + (b + 1) + 1)) from rfl,
              wl ⟨i.val, hi⟩]
            exact hu ⟨i.val, hi⟩
          · let j : Fin (b + 1) := ⟨i.val - (a + 1), by omega⟩
            have hij : a + 1 + j.val = i.val := by dsimp [j]; omega
            rw [show i = (⟨a + 1 + j.val, by omega⟩ : Fin (a + (b + 1) + 1)) by
              apply Fin.ext; exact hij.symm, wr j]
            simpa only [show ell + (↑(a + 1 + j.val) : ℤ) =
              ell + a + 0 + 1 + j.val by omega] using hv j
        · intro hx
          constructor
          · intro i
            simpa only [wl i] using hx ⟨i.val, by omega⟩
          · intro i
            simpa only [wr i, show ell + (↑(a + 1 + i.val) : ℤ) =
              ell + a + 0 + 1 + i.val by omega] using hx ⟨a + 1 + i.val, by omega⟩
      simp only [Nat.cast_zero]
      rw [he, hmass]
      have hw : H (a + (b + 1)) w = H a u * (Q (u (Fin.last a)) (v 0) * H b v) := by
        dsimp only [H]
        rw [Fin.prod_univ_add]
        congr 1
        · apply Finset.prod_congr rfl
          intro i _
          rw [show w ((Fin.castAdd (b + 1) i).castSucc) = u i.castSucc from wl i.castSucc,
            show w ((Fin.castAdd (b + 1) i).succ) = u i.succ from wl i.succ]
        · rw [Fin.prod_univ_succ]
          congr 1
          · rw [show w ((Fin.natAdd a (0 : Fin (b + 1))).castSucc) = u (Fin.last a)
                from wl (Fin.last a),
              show w ((Fin.natAdd a (0 : Fin (b + 1))).succ) = v 0 from wr 0]
          · apply Finset.prod_congr rfl
            intro i _
            rw [show w ((Fin.natAdd a i.succ).castSucc) = v i.castSucc from by
                convert wr i.castSucc using 1
                simp only [Nat.add_left_comm, Nat.add_comm]
                congr 1,
              show w ((Fin.natAdd a i.succ).succ) = v i.succ from by
                convert wr i.succ using 1
                simp only [Nat.add_left_comm, Nat.add_comm]
                congr 1]
      dsimp only [L]
      rw [show w 0 = u 0 from wl 0, hw]
      simp [mul_assoc]
    | succ g ih =>
      intro ell a b u v
      have he : C ell a u ∩ C (ell + a + ((g + 1 : ℕ) : ℤ) + 1) b v =
          ⋃ s : State k, C ell (a + 1) (Fin.snoc u s) ∩
            C (ell + ((a + 1 : ℕ) : ℤ) + g + 1) b v := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_iUnion]
        constructor
        · rintro ⟨hu, hv⟩
          refine ⟨x (ell + a + 1), ?_, ?_⟩
          · change (fun i : Fin (a + 1 + 1) => x (ell + i.val)) = Fin.snoc u _
            funext i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · simp [add_assoc]
            · simpa only [Fin.val_castSucc, Fin.snoc_castSucc] using congrFun hu j
          · convert hv using 1; congr 2; omega
        · rintro ⟨s, hu, hv⟩
          constructor
          · funext i
            simpa using congrFun hu i.castSucc
          · convert hv using 1; congr 2; omega
      rw [he, measureReal_iUnion_fintype]
      · simp_rw [ih, hsnoc, Fin.snoc_last]
        conv_rhs => rw [pow_succ', Matrix.mul_apply]
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro s _
        ring
      · intro s t hst
        apply Set.disjoint_left.mpr
        rintro x ⟨hs, _⟩ ⟨ht, _⟩
        apply hst
        have hs' := congrFun hs (Fin.last (a + 1))
        have ht' := congrFun ht (Fin.last (a + 1))
        simpa only [Fin.snoc_last] using hs'.symm.trans ht'
      · intro s
        exact (hC _ _ _).inter (hC _ _ _)
  have hrows : ∀ (m : ℕ) (s : State k), ∑ t, (Q ^ m) s t = 1 := by
    intro m
    induction m with
    | zero => intro s; simp [Matrix.one_apply]
    | succ m ih =>
      intro s
      simp only [pow_succ, Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, show ∀ u, ∑ t, Q u t = 1 from hrow, mul_one, ih]
  have hHs (b : ℕ) (w : Fin (b + 1) → State k) (t : State k) :
      H (b + 1) (Fin.snoc w t) = H b w * Q (w (Fin.last b)) t := by
    simp [H, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      -Fin.castSucc_succ, Fin.succ_castSucc]
  let W (b : ℕ) (s : State k) (v : Fin (b + 1) → State k) : ℝ :=
    if v 0 = s then H b v else 0
  have hWnonneg (b : ℕ) (s : State k) (v : Fin (b + 1) → State k) : 0 ≤ W b s v := by
    dsimp [W]
    split_ifs
    · exact hH b v
    · exact le_rfl
  have hWrow : ∀ (b : ℕ) (s : State k), ∑ v, W b s v = 1 := by
    intro b
    induction b with
    | zero =>
      intro s
      have he := (Equiv.funUnique (Fin 1) (State k)).sum_comp
        (fun t : State k => if t = s then (1 : ℝ) else 0)
      simpa [W, H] using he
    | succ b ih =>
      intro s
      rw [← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (b + 2) => State k)]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk]
      calc
        _ = ∑ w : Fin (b + 1) → State k, W b s w * ∑ t, Q (w (Fin.last b)) t := by
          apply Finset.sum_congr rfl
          intro w _
          have hz (t : State k) : (Fin.snoc w t : Fin (b + 2) → State k) 0 = w 0 := by
            simp
          simp only [W, hz, hHs]
          split_ifs <;> simp [Finset.mul_sum]
        _ = 1 := by simp only [show ∀ u, ∑ t, Q u t = 1 from hrow, mul_one, ih]
  have hWout (b : ℕ) (r : State k → ℝ) :
      channelOutput (W b) r = fun v => r (v 0) * H b v := by
    funext v
    simp [channelOutput, W]
  have hWmass (b : ℕ) (r : State k → ℝ) :
      ∑ v, channelOutput (W b) r v = ∑ s, r s := by
    simp only [channelOutput]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hWrow, mul_one]
  let E (ell : ℤ) (a : ℕ) (A : Finset (Fin (a + 1) → State k)) : Set (ℤ → State k) :=
    {x | (fun i : Fin (a + 1) => x (ell + i.val)) ∈ A}
  have hEmass (ell : ℤ) (a : ℕ) (A : Finset (Fin (a + 1) → State k)) :
      (ν : Measure (ℤ → State k)).real (E ell a A) = ∑ u ∈ A, L a u := by
    change (ν : Measure (ℤ → State k)).real
      ((fun x i => x (ell + i.val)) ⁻¹' (A : Set (Fin (a + 1) → State k))) = _
    rw [← sum_measureReal_preimage_singleton (μ := (ν : Measure (ℤ → State k)))
      A (fun u _ => hC ell a u)]
    exact Finset.sum_congr rfl fun u _ => hmass ell a u
  have hEjoint (ell : ℤ) (a b g : ℕ)
      (A : Finset (Fin (a + 1) → State k)) (B : Finset (Fin (b + 1) → State k)) :
      (ν : Measure (ℤ → State k)).real (E ell a A ∩ E (ell + a + g + 1) b B) =
        ∑ u ∈ A, ∑ v ∈ B, L a u * (Q ^ (g + 1)) (u (Fin.last a)) (v 0) * H b v := by
    let f (x : ℤ → State k) :=
      ((fun i : Fin (a + 1) => x (ell + i.val)),
       (fun i : Fin (b + 1) => x (ell + a + g + 1 + i.val)))
    have hf (w : (Fin (a + 1) → State k) × (Fin (b + 1) → State k)) :
        f ⁻¹' {w} = C ell a w.1 ∩ C (ell + a + g + 1) b w.2 := by
      ext x
      simp [f, C, Prod.ext_iff]
    have he : E ell a A ∩ E (ell + a + g + 1) b B = f ⁻¹' ↑(A ×ˢ B) := by
      ext x
      simp [E, f]
    rw [he, ← sum_measureReal_preimage_singleton (A ×ˢ B)
      (fun w _ => by rw [hf]; exact (hC _ _ _).inter (hC _ _ _)), Finset.sum_product]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [hf]
    exact hjoint g ell a b u v
  have hbound (ell : ℤ) (a b g : ℕ)
      (A : Finset (Fin (a + 1) → State k)) (B : Finset (Fin (b + 1) → State k)) :
      |(ν : Measure (ℤ → State k)).real (E ell a A ∩ E (ell + a + g + 1) b B) -
        (ν : Measure (ℤ → State k)).real (E ell a A) *
        (ν : Measure (ℤ → State k)).real (E 0 b B)| ≤ (3 / 4 : ℝ) ^ ((g + 1) / 3) := by
    let ε : ℝ := (3 / 4 : ℝ) ^ ((g + 1) / 3)
    have hε : 0 ≤ ε := by dsimp [ε]; positivity
    have hb (s : State k) :
        |(∑ v ∈ B, (Q ^ (g + 1)) s (v 0) * H b v) - ∑ v ∈ B, L b v| ≤ ε := by
      have hdpi := total_variation_channel_le (fun t => (Q ^ (g + 1)) s t) π (W b)
        ⟨hWnonneg b, hWrow b⟩
      have htv := (parry_mixing_and_complete_prefix k hk).1 (g + 1) s
      have hm : (∑ v, channelOutput (W b) (fun t => (Q ^ (g + 1)) s t) v) =
          ∑ v, channelOutput (W b) π v := by
        rw [hWmass, hWmass, hrows]
        exact hπsum.symm
      have hevent := (total_variation_eq_sup_event_gap _ _ hm).2 ⟨B, rfl⟩
      simpa only [hWout, L] using hevent.trans (hdpi.trans htv)
    rw [hEjoint, hEmass, hEmass]
    calc
      _ = |∑ u ∈ A, L a u *
          ((∑ v ∈ B, (Q ^ (g + 1)) (u (Fin.last a)) (v 0) * H b v) - ∑ v ∈ B, L b v)| := by
        congr 1
        simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib, mul_sub, mul_assoc]
        congr 1
        exact Finset.sum_comm
      _ ≤ ∑ u ∈ A, |L a u *
          ((∑ v ∈ B, (Q ^ (g + 1)) (u (Fin.last a)) (v 0) * H b v) - ∑ v ∈ B, L b v)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u ∈ A, L a u * ε := by
        apply Finset.sum_le_sum
        intro u _
        rw [abs_mul, abs_of_nonneg (hL a u)]
        exact mul_le_mul_of_nonneg_left (hb _) (hL a u)
      _ = (ν : Measure (ℤ → State k)).real (E ell a A) * ε := by
        rw [hEmass, Finset.sum_mul]
      _ ≤ ε := by
        exact (mul_le_mul_of_nonneg_right measureReal_le_one hε).trans_eq (one_mul ε)
  let S : (ℤ → State k) → (ℤ → State k) := fun x t => x (t + 1)
  have hS : MeasurePreserving S (ν : Measure (ℤ → State k)) ν :=
    ⟨measurable_pi_lambda _ fun t => measurable_pi_apply (t + 1), hνshift⟩
  have hiter (n : ℕ) (x : ℤ → State k) (t : ℤ) : S^[n] x t = x (t + n) := by
    induction n generalizing t with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      change S^[n] x (t + 1) = _
      rw [ih]
      congr 1
      omega
  have hEmeas (ell : ℤ) (a : ℕ) (A : Finset (Fin (a + 1) → State k)) :
      MeasurableSet (E ell a A) :=
    (measurable_pi_lambda _ fun i => measurable_pi_apply (ell + i.val)) A.measurableSet
  have hfinite (A : Set (ℤ → State k))
      (hA : A ∈ measurableCylinders (fun _ : ℤ => State k)) :
      ∃ a : ℕ, ∃ U : Finset (Fin (2 * a + 1) → State k), A = E (-(a : ℤ)) (2 * a) U := by
    obtain ⟨I, V, _, rfl⟩ := (mem_measurableCylinders A).1 hA
    let a : ℕ := I.sup Int.natAbs
    have hI (i : I) : -(a : ℤ) ≤ i.val ∧ i.val ≤ a := by
      have hi : i.val.natAbs ≤ a := Finset.le_sup (f := Int.natAbs) i.property
      have hp := Int.le_natAbs (a := i.val)
      have hn : -i.val ≤ (i.val.natAbs : ℤ) := by
        simpa using (Int.le_natAbs (a := -i.val))
      omega
    let f (w : Fin (2 * a + 1) → State k) (i : I) : State k :=
      w ⟨(i.val + a).toNat, by have := hI i; omega⟩
    refine ⟨a, Finset.univ.filter (fun w => f w ∈ V), ?_⟩
    ext x
    have he : f (fun j : Fin (2 * a + 1) => x (-(a : ℤ) + j.val)) = I.restrict x := by
      funext i
      dsimp [f, Finset.restrict]
      congr 1
      have := hI i
      omega
    simp only [mem_cylinder, E, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ,
      true_and, he]
  have hεlim : Tendsto (fun n : ℕ => (3 / 4 : ℝ) ^ ((n + 1) / 3)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)).comp
      ((Nat.tendsto_div_const_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp
        (tendsto_add_atTop_nat 1))
  have hcmix (A B : Set (ℤ → State k))
      (hA : A ∈ measurableCylinders (fun _ : ℤ => State k))
      (hB : B ∈ measurableCylinders (fun _ : ℤ => State k)) :
      Tendsto (fun n : ℕ => (ν : Measure (ℤ → State k)).real (A ∩ S^[n] ⁻¹' B))
        atTop (𝓝 ((ν : Measure (ℤ → State k)).real A * (ν : Measure (ℤ → State k)).real B)) := by
    obtain ⟨a, U, rfl⟩ := hfinite A hA
    obtain ⟨b, V, rfl⟩ := hfinite B hB
    apply (tendsto_add_atTop_iff_nat (a + b + 1)).1
    apply tendsto_iff_dist_tendsto_zero.2
    have hb (n : ℕ) :
        |(ν : Measure (ℤ → State k)).real
          (E (-(a : ℤ)) (2 * a) U ∩ S^[n + (a + b + 1)] ⁻¹' E (-(b : ℤ)) (2 * b) V) -
          (ν : Measure (ℤ → State k)).real (E (-(a : ℤ)) (2 * a) U) *
          (ν : Measure (ℤ → State k)).real (E (-(b : ℤ)) (2 * b) V)| ≤
          (3 / 4 : ℝ) ^ ((n + 1) / 3) := by
      have he : S^[n + (a + b + 1)] ⁻¹' E (-(b : ℤ)) (2 * b) V =
          E (-(a : ℤ) + (2 * a : ℕ) + n + 1) (2 * b) V := by
        ext x
        change ((fun i : Fin (2 * b + 1) => S^[n + (a + b + 1)] x (-↑b + i.val)) ∈ V) ↔ _
        have hi : (fun i : Fin (2 * b + 1) => S^[n + (a + b + 1)] x (-↑b + i.val)) =
            (fun i : Fin (2 * b + 1) => x (-↑a + (2 * a : ℕ) + n + 1 + i.val)) := by
          funext i
          rw [hiter]
          congr 1
          omega
        rw [hi]
        rfl
      rw [he, show (ν : Measure (ℤ → State k)).real (E (-(b : ℤ)) (2 * b) V) =
        (ν : Measure (ℤ → State k)).real (E 0 (2 * b) V) by rw [hEmass, hEmass]]
      exact hbound (-(a : ℤ)) (2 * a) (2 * b) n U V
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => by simpa [Real.dist_eq] using hb n) hεlim
  have happrox (A : Set (ℤ → State k)) (hA : MeasurableSet A) (δ : ℝ) (hδ : 0 < δ) :
      ∃ C' ∈ measurableCylinders (fun _ : ℤ => State k),
        (ν : Measure (ℤ → State k)).real (C' ∆ A) < δ := by
    have hcover : ∃ D : Set (Set (ℤ → State k)), D.Countable ∧
        D ⊆ measurableCylinders (fun _ : ℤ => State k) ∧
        (ν : Measure (ℤ → State k)) (⋃₀ D)ᶜ = 0 := by
      refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
      · intro t ht
        rcases Set.mem_singleton_iff.mp ht with rfl
        exact univ_mem_measurableCylinders _
      · simp
    obtain ⟨C', hC', he⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := (ν : Measure (ℤ → State k))) isSetRing_measurableCylinders hcover
      generateFrom_measurableCylinders.symm hA (ENNReal.ofReal_pos.mpr hδ)
    exact ⟨C', hC', (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
      ENNReal.ofReal_ne_top).2 he |>.trans_eq (ENNReal.toReal_ofReal hδ.le)⟩
  have hgap (A B : Set (ℤ → State k)) :
      |(ν : Measure (ℤ → State k)).real A - (ν : Measure (ℤ → State k)).real B| ≤
        (ν : Measure (ℤ → State k)).real (A ∆ B) := by
    apply abs_le.mpr
    have h1 : A ⊆ B ∪ (A ∆ B) := by
      intro x hx
      clear * - hx
      simp only [Set.mem_union, Set.mem_symmDiff]
      tauto
    have h2 : B ⊆ A ∪ (A ∆ B) := by
      intro x hx
      clear * - hx
      simp only [Set.mem_union, Set.mem_symmDiff]
      tauto
    have h1' := (measureReal_mono (μ := (ν : Measure (ℤ → State k))) h1).trans
      (measureReal_union_le _ _)
    have h2' := (measureReal_mono (μ := (ν : Measure (ℤ → State k))) h2).trans
      (measureReal_union_le _ _)
    constructor <;> linarith only [h1', h2']
  have hmix (A B : Set (ℤ → State k)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      Tendsto (fun n : ℕ => (ν : Measure (ℤ → State k)).real (A ∩ S^[n] ⁻¹' B))
        atTop (𝓝 ((ν : Measure (ℤ → State k)).real A * (ν : Measure (ℤ → State k)).real B)) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨A', hA', ha⟩ := happrox A hA (ε / 5) (by linarith)
    obtain ⟨B', hB', hb⟩ := happrox B hB (ε / 5) (by linarith)
    have hAm := MeasurableSet.of_mem_measurableCylinders hA'
    have hBm := MeasurableSet.of_mem_measurableCylinders hB'
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hcmix A' B' hA' hB') (ε / 5) (by linarith)
    refine ⟨N, fun n hn => ?_⟩
    have hsymm : (A ∩ S^[n] ⁻¹' B) ∆ (A' ∩ S^[n] ⁻¹' B') ⊆
        (A' ∆ A) ∪ S^[n] ⁻¹' (B' ∆ B) := by
      intro x hx
      simp only [Set.mem_union, Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_preimage] at hx ⊢
      clear * - hx
      tauto
    have hinter := (hgap (A ∩ S^[n] ⁻¹' B) (A' ∩ S^[n] ⁻¹' B')).trans
      ((measureReal_mono hsymm).trans (measureReal_union_le _ _))
    rw [(hS.iterate n).measureReal_preimage (hBm.symmDiff hB).nullMeasurableSet] at hinter
    have hp : |(ν : Measure (ℤ → State k)).real A' * (ν : Measure (ℤ → State k)).real B' -
        (ν : Measure (ℤ → State k)).real A * (ν : Measure (ℤ → State k)).real B| <
        2 * (ε / 5) := by
      have hga := hgap A' A
      have hgb := hgap B' B
      calc
        _ = |((ν : Measure (ℤ → State k)).real A' - (ν : Measure (ℤ → State k)).real A) *
            (ν : Measure (ℤ → State k)).real B' + (ν : Measure (ℤ → State k)).real A *
            ((ν : Measure (ℤ → State k)).real B' - (ν : Measure (ℤ → State k)).real B)| := by
          congr 1; ring
        _ ≤ |(ν : Measure (ℤ → State k)).real A' - (ν : Measure (ℤ → State k)).real A| +
            |(ν : Measure (ℤ → State k)).real B' - (ν : Measure (ℤ → State k)).real B| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg measureReal_nonneg, abs_of_nonneg measureReal_nonneg]
          exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) measureReal_le_one)
            (mul_le_of_le_one_left (abs_nonneg _) measureReal_le_one)
        _ < _ := by linarith only [hga, hgb, ha, hb]
    have hmid := hN n hn
    rw [Real.dist_eq] at hmid ⊢
    have htri := abs_add_le
      ((ν : Measure (ℤ → State k)).real (A ∩ S^[n] ⁻¹' B) -
       (ν : Measure (ℤ → State k)).real (A' ∩ S^[n] ⁻¹' B'))
      ((ν : Measure (ℤ → State k)).real (A' ∩ S^[n] ⁻¹' B') -
       (ν : Measure (ℤ → State k)).real A * (ν : Measure (ℤ → State k)).real B)
    have htri' := abs_add_le
      ((ν : Measure (ℤ → State k)).real (A' ∩ S^[n] ⁻¹' B') -
       (ν : Measure (ℤ → State k)).real A' * (ν : Measure (ℤ → State k)).real B')
      ((ν : Measure (ℤ → State k)).real A' * (ν : Measure (ℤ → State k)).real B' -
       (ν : Measure (ℤ → State k)).real A * (ν : Measure (ℤ → State k)).real B)
    simp only [sub_add_sub_cancel] at htri htri'
    linarith only [ha, hb, hinter, hp, hmid, htri, htri']
  let ρ : Measure (Bool × RelationPath k) := fairAnchor.prod (μ : Measure (RelationPath k))
  let T : (Bool × RelationPath k) → Bool × RelationPath k :=
    fun z => (xor z.1 (!z.2.val 0), relationShift z.2)
  let F (z : Bool × RelationPath k) : ℤ → State k := (e z).val
  have hsupport : MeasurableSet
      {x : ℤ → State k | ∀ t, 0 < kernel k (parryParameter k) (x t) (x (t + 1))} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro t
    have hpair : Measurable (fun x : ℤ → State k => (x t, x (t + 1))) :=
      (measurable_pi_apply t).prodMk (measurable_pi_apply (t + 1))
    have hm : Measurable (fun x : ℤ → State k =>
        kernel k (parryParameter k) (x t) (x (t + 1))) := by
      exact (measurable_of_countable (fun p : State k × State k =>
        kernel k (parryParameter k) p.1 p.2)).comp hpair
    exact hm measurableSet_Ioi
  have hF : MeasurableEmbedding F :=
    (MeasurableEmbedding.subtype_coe hsupport).comp e.measurableEmbedding
  have hFpres : MeasurePreserving F ρ ν := ⟨hF.measurable, hpush⟩
  have hσ : Measurable (relationShift (k := k)) := by
    apply Measurable.subtype_mk
    exact measurable_pi_lambda _ fun t => (measurable_pi_apply (t + 1)).comp measurable_subtype_coe
  have hTmeas : Measurable T := by
    refine Measurable.prodMk ?_ (hσ.comp measurable_snd)
    exact (measurable_of_countable (fun p : Bool × Bool => xor p.1 (!p.2))).comp
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp
        (measurable_subtype_coe.comp measurable_snd)))
  have hsem : Function.Semiconj F T S := hcode
  have hT : MeasurePreserving T ρ ρ := by
    refine ⟨hTmeas, hF.map_injective ?_⟩
    rw [Measure.map_map hF.measurable hTmeas, hsem.comp_eq,
      ← Measure.map_map hS.measurable hF.measurable, hpush, hνshift]
  have hρimage (A : Set (Bool × RelationPath k)) (hA : MeasurableSet A) :
      (ν : Measure (ℤ → State k)) (F '' A) = ρ A := by
    rw [← hpush, hF.map_apply, hF.injective.preimage_image]
  have hρreal (A : Set (Bool × RelationPath k)) (hA : MeasurableSet A) :
      (ν : Measure (ℤ → State k)).real (F '' A) = ρ.real A :=
    congrArg ENNReal.toReal (hρimage A hA)
  have hmixρ (A B : Set (Bool × RelationPath k)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      Tendsto (fun n : ℕ => ρ.real (A ∩ T^[n] ⁻¹' B)) atTop (𝓝 (ρ.real A * ρ.real B)) := by
    have hm := hmix (F '' A) (F '' B)
      (hF.measurableSet_image.mpr hA) (hF.measurableSet_image.mpr hB)
    rw [hρreal A hA, hρreal B hB] at hm
    have he (n : ℕ) :
        (ν : Measure (ℤ → State k)).real (F '' A ∩ S^[n] ⁻¹' (F '' B)) =
          ρ.real (A ∩ T^[n] ⁻¹' B) := by
      rw [← hFpres.measureReal_preimage
        ((hF.measurableSet_image.mpr hA).inter
          ((hS.measurable.iterate n) (hF.measurableSet_image.mpr hB))).nullMeasurableSet]
      congr 1
      ext z
      simp only [Set.mem_preimage, Set.mem_inter_iff, hF.injective.mem_set_image,
        ← (hsem.iterate_right n) z]
    simpa only [he] using hm
  let : IsProbabilityMeasure fairAnchor := by dsimp [fairAnchor]; infer_instance
  let : IsProbabilityMeasure ρ := inferInstanceAs
    (IsProbabilityMeasure (fairAnchor.prod (μ : Measure (RelationPath k))))
  have hmixρENN (A B : Set (Bool × RelationPath k)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      Tendsto (fun n : ℕ => ρ (A ∩ T^[n] ⁻¹' B)) atTop (𝓝 (ρ A * ρ B)) := by
    have hm := ENNReal.tendsto_ofReal (hmixρ A B hA hB)
    simpa only [measureReal_def, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top _ _)] using hm
  have hergodic : Ergodic T ρ := by
    refine ⟨hT, ⟨fun A hA hinv => ?_⟩⟩
    have hi : ∀ n : ℕ, T^[n] ⁻¹' A = A := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ', Set.preimage_comp, hinv, ih]
    have hm := hmixρ A A hA hA
    simp only [hi, Set.inter_self] at hm
    have ha : ρ.real A = ρ.real A * ρ.real A := tendsto_nhds_unique tendsto_const_nhds hm
    have hz : ρ.real A = 0 ∨ ρ.real A = 1 := by
      have hh : ρ.real A * (ρ.real A - 1) = 0 := by nlinarith only [ha]
      simpa only [sub_eq_zero] using mul_eq_zero.mp hh
    rw [eventuallyConst_set]
    rcases hz with hz | ho
    · right
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using
        (measureReal_eq_zero_iff (μ := ρ) (s := A)).1 hz
    · left
      rw [ae_iff]
      have ha1 : ρ A = 1 := (ENNReal.toReal_eq_one_iff _).1 ho
      change ρ Aᶜ = 0
      rw [measure_compl hA (measure_ne_top _ _), measure_univ, ha1, tsub_self]
  have hnosection (h : RelationPath k → Bool) (hh : Measurable h) :
      ¬ ∀ᵐ r ∂(μ : Measure (RelationPath k)), h (relationShift r) = xor (h r) (!r.val 0) := by
    intro heq
    let G : Set (Bool × RelationPath k) := {z | z.1 = h z.2}
    have hG : MeasurableSet G := measurableSet_eq_fun measurable_fst (hh.comp measurable_snd)
    have hGmass : ρ G = (1 / 2 : ℝ≥0∞) := by
      rw [Measure.prod_apply_symm hG]
      have hfiber (r : RelationPath k) : (fun a : Bool => (a, r)) ⁻¹' G = {h r} := rfl
      simp only [hfiber]
      simp [fairAnchor]
    have hGinv : T ⁻¹' G =ᵐ[ρ] G := by
      have hlift : ∀ᵐ z ∂ρ, h (relationShift z.2) = xor (h z.2) (!z.2.val 0) :=
        (Measure.quasiMeasurePreserving_snd (μ := fairAnchor)
          (ν := (μ : Measure (RelationPath k)))).ae heq
      filter_upwards [hlift] with z hz
      change (xor z.1 (!z.2.val 0) = h (relationShift z.2)) = (z.1 = h z.2)
      rw [hz]
      apply propext
      exact Bool.xor_left_inj
    rcases hergodic.quasiErgodic.ae_empty_or_univ₀ hG.nullMeasurableSet hGinv with hzero | hone
    · have hz := measure_congr hzero
      rw [hGmass, measure_empty] at hz
      norm_num at hz
    · have ho := measure_congr hone
      rw [hGmass, measure_univ] at ho
      norm_num at ho
  have hpositive (h : RelationPath k → Bool) (hh : Measurable h) :
      0 < (μ : Measure (RelationPath k)).real
        {r | xor (xor (h (relationShift r)) (h r)) (!r.val 0) = true} := by
    apply lt_of_le_of_ne measureReal_nonneg
    intro hz
    have hz' := (measureReal_eq_zero_iff).1 hz.symm
    have hae : ∀ᵐ r ∂(μ : Measure (RelationPath k)),
        ¬ xor (xor (h (relationShift r)) (h r)) (!r.val 0) = true := by
      simpa only [ae_iff, not_not] using hz'
    apply hnosection h hh
    filter_upwards [hae] with r hr
    clear * - hr
    cases hs : h (relationShift r) <;> cases ht : h r <;> cases hb : r.val 0 <;> simp_all
  let Δ (h : RelationPath k → Bool) : ℝ := (μ : Measure (RelationPath k)).real
    {r | xor (xor (h (relationShift r)) (h r)) (!r.val 0) = true}
  have hpath : ∀ (m : ℕ) (w : Fin (m + 1) → State k),
      pathWeight k (parryParameter k) m (w 0) (Fin.tail w) = H m w := by
    intro m
    induction m with
    | zero => intro w; simp [pathWeight, H]
    | succ m ih =>
      intro w
      simpa +unfoldPartialApp only [H, pathWeight, Fin.tail, Fin.prod_univ_succ,
        Fin.succ_zero_eq_one, Fin.castSucc_zero, Fin.castSucc_succ, Q] using congrArg
          (fun x => kernel k (parryParameter k) (w 0) (w 1) * x) (ih (Fin.tail w))
  have hread (z : Bool × RelationPath k) : readRelation (F z) = z.2.val := by
    simpa only [F, e.symm_apply_apply] using (hinverse (e z)).2.symm
  have hwindow (R : ℕ) (f : (Fin R → Bool) → Bool) :
      ∃ h : RelationPath k → Bool, Measurable h ∧ Δ h = stationaryDefect k R f := by
    let h (r : RelationPath k) := f (fun i : Fin R => r.val (-(R : ℤ) + i.val))
    have hh : Measurable h := (measurable_of_countable f).comp
      (measurable_pi_lambda _ fun i =>
        (measurable_pi_apply (-(R : ℤ) + i.val)).comp measurable_subtype_coe)
    let U : Finset (Fin (R + 1 + 1) → State k) :=
      Finset.univ.filter (fun w => prefixRuleDefect f (w 0, Fin.tail w) = true)
    let D : Set (RelationPath k) :=
      {r | xor (xor (h (relationShift r)) (h r)) (!r.val 0) = true}
    have hD : MeasurableSet D := by
      have hm : Measurable (fun r : RelationPath k =>
          xor (xor (h (relationShift r)) (h r)) (!r.val 0)) :=
        (measurable_of_countable
          (fun p : (Bool × Bool) × Bool => xor (xor p.1.1 p.1.2) (!p.2))).comp
          (((hh.comp hσ).prodMk hh).prodMk ((measurable_pi_apply 0).comp measurable_subtype_coe))
      exact hm (measurableSet_singleton true)
    have hpull : F ⁻¹' E (-(R : ℤ)) (R + 1) U = Prod.snd ⁻¹' D := by
      ext z
      let w (i : Fin (R + 1 + 1)) := F z (-(R : ℤ) + i.val)
      have hr (i : Fin (R + 1)) :
          prefixRelation (w 0, Fin.tail w) i = z.2.val (-(R : ℤ) + i.val) := by
        dsimp only [prefixRelation]
        rw [Fin.cons_self_tail, ← hread z]
        simp only [readRelation, w, Fin.val_castSucc, Fin.val_succ,
          Nat.cast_add, Nat.cast_one, add_assoc]
      change ((fun i : Fin (R + 1 + 1) => F z (-(R : ℤ) + i.val)) ∈ U) ↔ z.2 ∈ D
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      change (prefixRuleDefect f (w 0, Fin.tail w) = true) ↔ _
      simp only [prefixRuleDefect, hr, D, Set.mem_ofPred_eq, h, relationShift,
        Fin.val_succ, Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
      simp only [add_assoc, neg_add_cancel]
    have hmassD : Δ h = (ν : Measure (ℤ → State k)).real (E (-(R : ℤ)) (R + 1) U) := by
      change (μ : Measure (RelationPath k)).real D = _
      rw [← hFpres.measureReal_preimage (hEmeas _ _ _).nullMeasurableSet, hpull]
      exact (measurePreserving_snd (μ := fairAnchor)
        (ν := (μ : Measure (RelationPath k)))).measureReal_preimage hD.nullMeasurableSet |>.symm
    refine ⟨h, hh, hmassD.trans ?_⟩
    rw [hEmass]
    simp only [U, Finset.sum_filter, stationaryDefect]
    rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (R + 1 + 1) => State k)]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.tail_cons, L]
    apply Finset.sum_congr rfl
    intro v _
    rw [← hpath, Fin.cons_zero, Fin.tail_cons]
    rfl
  have hp : 0 ≤ parryParameter k := by
    have hp' := (parry_stationary_law k hk).1.1
    linarith only [hp']
  have hp1 : parryParameter k < 1 :=
    lt_of_le_of_lt (parry_stationary_law k hk).1.2.1
      (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
  let bound (n : ℕ) : ℝ := 1 / (n + 3 : ℕ) + ((n : ℝ) + 3) ^ 2 * parryParameter k ^ n
  have hboundlim : Tendsto bound atTop (𝓝 0) := by
    have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one hp hp1
    have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 hp hp1
    have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 hp hp1
    have hpoly : Tendsto (fun n : ℕ => ((n : ℝ) + 3) ^ 2 * parryParameter k ^ n) atTop (𝓝 0) := by
      convert (h2.add (h1.const_mul 6)).add (h0.const_mul 9) using 1
      · funext n
        ring
      · norm_num
    have hrecip : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 3 : ℕ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 3)
    simpa only [add_zero] using hrecip.add hpoly
  have hsmall (n : ℕ) : ∃ h : RelationPath k → Bool, Measurable h ∧ Δ h ≤ bound n := by
    obtain ⟨order, labels, hf⟩ := (parry_window_upper_bound k hk
      (2 * (n + 1)) (n + 1) (by omega) (by omega) false).1
    obtain ⟨h, hh, he⟩ := hwindow (2 * (n + 1))
      (windowTable (2 * (n + 1)) (n + 1) (by omega) order labels false)
    refine ⟨h, hh, ?_⟩
    rw [he]
    calc
      _ ≤ 1 / (n + 3 : ℕ) + ((n + 3).choose 2 : ℝ) * parryParameter k ^ n := by
        simpa only [show 2 * (n + 1) - (n + 1) + 2 = n + 3 by omega,
          Nat.add_sub_cancel] using hf
      _ ≤ bound n := by
        dsimp only [bound]
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp n)
        have hc := Nat.choose_le_pow (n + 3) 2
        exact_mod_cast hc
  have hinf : sInf {d : ℝ | ∃ h : RelationPath k → Bool, Measurable h ∧ d = Δ h} = 0 := by
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    · exact ⟨Δ (fun _ => false), fun _ => false, measurable_const, rfl⟩
    · rintro d ⟨h, _, rfl⟩
      exact measureReal_nonneg
    · intro ε hε
      obtain ⟨n, hn⟩ := (hboundlim.eventually (gt_mem_nhds hε)).exists
      obtain ⟨h, hh, hsmall'⟩ := hsmall n
      exact ⟨Δ h, ⟨h, hh, rfl⟩, hsmall'.trans_lt hn⟩
  have hjoint0 (ell : ℤ) (a b : ℕ)
      (u : Fin (a + 1) → State k) (v : Fin (b + 1) → State k) :
      (ν : Measure (ℤ → State k)).real (C ell a u ∩ C (ell + a) b v) =
        L a u * (Q ^ 0) (u (Fin.last a)) (v 0) * H b v := by
    by_cases huv : u (Fin.last a) = v 0
    · have hend (x : ℤ → State k) (hx : x ∈ C ell a u) : x (ell + a) = v 0 := by
        simpa only [Fin.val_last] using (congrFun hx (Fin.last a)).trans huv
      simp only [pow_zero, Matrix.one_apply, huv, ↓reduceIte, mul_one]
      cases b with
      | zero =>
        have he : C ell a u ∩ C (ell + a) 0 v = C ell a u := by
          apply Set.inter_eq_left.mpr
          intro x hx
          funext i
          have hi : i = 0 := Fin.ext (by omega)
          subst i
          simpa using hend x hx
        rw [he, hmass]
        simp only [H, Fin.prod_univ_zero, mul_one]
      | succ b =>
        have he : C ell a u ∩ C (ell + a) (b + 1) v =
            C ell a u ∩ C (ell + a + 0 + 1) b (Fin.tail v) := by
          ext x
          constructor
          · rintro ⟨hx, hv⟩
            refine ⟨hx, funext fun i => ?_⟩
            simpa only [Fin.tail, Fin.val_succ, Nat.cast_add, Nat.cast_one, add_zero,
              add_assoc, add_comm, add_left_comm]
              using congrFun hv i.succ
          · rintro ⟨hx, hv⟩
            refine ⟨hx, funext fun i => ?_⟩
            refine Fin.cases ?_ (fun j => ?_) i
            · simpa using hend x hx
            · simpa only [Fin.tail, Fin.val_succ, Nat.cast_add, Nat.cast_one, add_zero,
                add_assoc, add_comm, add_left_comm]
                using congrFun hv j
        rw [he]
        have ht := hjoint 0 ell a b u (Fin.tail v)
        simp only [Nat.cast_zero] at ht
        rw [ht]
        simp only [Nat.zero_add, pow_one, huv, H, Fin.prod_univ_succ,
          Fin.tail, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.castSucc_succ, mul_assoc]
    · have he : C ell a u ∩ C (ell + a) b v = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hv⟩
        apply huv
        have hu := congrFun hx (Fin.last a)
        have hv' := congrFun hv 0
        simpa using hu.symm.trans (by simpa using hv')
      rw [he]
      simp only [measureReal_empty, pow_zero, Matrix.one_apply, huv, ↓reduceIte, mul_zero, zero_mul]
  have hbound0 (ell : ℤ) (a b : ℕ)
      (A : Finset (Fin (a + 1) → State k)) (B : Finset (Fin (b + 1) → State k)) :
      |(ν : Measure (ℤ → State k)).real (E ell a A ∩ E (ell + a) b B) -
        (ν : Measure (ℤ → State k)).real (E ell a A) *
        (ν : Measure (ℤ → State k)).real (E 0 b B)| ≤ 1 := by
    have hprod0 := mul_nonneg
      (measureReal_nonneg (μ := (ν : Measure (ℤ → State k))) (s := E ell a A))
      (measureReal_nonneg (μ := (ν : Measure (ℤ → State k))) (s := E 0 b B))
    have hprod1 : (ν : Measure (ℤ → State k)).real (E ell a A) *
        (ν : Measure (ℤ → State k)).real (E 0 b B) ≤ 1 :=
      (mul_le_mul_of_nonneg_right measureReal_le_one measureReal_nonneg).trans
        (by simp)
    have hi0 : 0 ≤ (ν : Measure (ℤ → State k)).real (E ell a A ∩ E (ell + a) b B) :=
      measureReal_nonneg
    have hi1 : (ν : Measure (ℤ → State k)).real (E ell a A ∩ E (ell + a) b B) ≤ 1 :=
      measureReal_le_one
    apply abs_le.mpr
    constructor <;> linarith only [hprod0, hprod1, hi0, hi1]
  refine ⟨e, μ, ν, hsign, hsuffix, hinverse, hcode, hμshift, hνshift, hpush,
    hcyl, hsource, ?_, ?_, hmix,
    ⟨hmixρENN, hergodic, fun h hh => ⟨hnosection h hh, hpositive h hh⟩⟩, hinf⟩
  · intro ell a b g u v
    cases g with
    | zero => simpa only [Nat.cast_zero, add_zero] using hjoint0 ell a b u v
    | succ g => simpa only [C, Nat.cast_add, Nat.cast_one, add_assoc] using hjoint g ell a b u v
  · intro ell a b g A B
    cases g with
    | zero => simpa only [E, Nat.cast_zero, add_zero, zero_add, Nat.zero_div, pow_zero]
        using hbound0 ell a b A B
    | succ g => simpa only [E, Nat.cast_add, Nat.cast_one, add_assoc, zero_add]
        using hbound ell a b g A B

end D5.S3.TotalVariation.ParryBilateralMixing
