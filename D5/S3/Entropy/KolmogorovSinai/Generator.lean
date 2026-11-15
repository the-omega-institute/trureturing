/- GID: D5/S3/Entropy/KolmogorovSinai/Generator
   generality: G
   mirror-B: D5/B/S3/Entropy/KolmogorovSinai/Generator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kolmogorov-Sinai generator for the full-shift equilibrium proof. -/

/- Copyright (c) 2026 Marcel Morgenstern. Licensed under Apache-2.0.
   Selected source port of marcmorningstar/lean4-ergodic-theory,
   revision 040fec2e0ddf4fcba49af9f76c866d295308dd7f.
   Attribution, source mapping and full license: Library/Entropy/morgenstern2026ks.md.
   Adaptation: current Lean APIs, subject namespaces and live-dependency pruning.
   Retire each ported declaration when an equivalent declaration exists in this
   repository's pinned mathlib revision, replacing consumers by direct imports. -/

/- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30545. -/

import D5.S3.Entropy.KolmogorovSinai.GeneratorConditioning



open MeasureTheory Function Filter Topology ProbabilityTheory MeasurableSpace

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι κ : Type*} {𝒜 ℱ : MeasurableSpace α} [mα : MeasurableSpace α]
  [StandardBorelSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}

section Blocking

private lemma condEntropy_genJoin_pullback_append_le [Fintype ι] (hℱ : ℱ ≤ mα)
    (hT : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) (c a b : ℕ) :
    condEntropy μ ℱ ((ksJoin hT P (a + b)).pullback (hT.iterate c)).cells
      ≤ condEntropy μ ℱ ((ksJoin hT P a).pullback (hT.iterate c)).cells
        + condEntropy μ ℱ ((ksJoin hT P b).pullback (hT.iterate (c + a))).cells := by
  set R : MeasurePartition μ (Fin a → ι) := (ksJoin hT P a).pullback (hT.iterate c) with hR
  set S : MeasurePartition μ (Fin b → ι) := (ksJoin hT P b).pullback (hT.iterate (c + a)) with hS
  
  
  have hcell : ∀ p : (Fin a → ι) × (Fin b → ι),
      ((ksJoin hT P (a + b)).pullback (hT.iterate c)).cells (Fin.appendEquiv a b p)
        = joinCells R.cells S.cells p := by
    rintro ⟨x, y⟩
    simp only [hR, hS, MeasurePartition.pullback_cells, ksJoin_cells, joinCells_apply]
    rw [show (Fin.appendEquiv a b) (x, y) = Fin.append x y from rfl,
      ksJoinCells_append P.cells T a b x y, Set.preimage_inter]
    congr 1
    
    rw [← Set.preimage_comp, ← Function.iterate_add,
      show a + c = c + a from Nat.add_comm a c]
  
  have hreindex : condEntropy μ ℱ ((ksJoin hT P (a + b)).pullback (hT.iterate c)).cells
      = condEntropy μ ℱ (joinCells R.cells S.cells) := by
    rw [condEntropy_def, condEntropy_def]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    refine (Equiv.sum_comp (Fin.appendEquiv a b)
      (fun g => Real.negMulLog
        (@condExpKernel α mα _ μ _ ℱ ω
          (((ksJoin hT P (a + b)).pullback (hT.iterate c)).cells g)).toReal)).symm.trans ?_
    exact Finset.sum_congr rfl fun p _ => by rw [hcell p]
  rw [hreindex]
  exact condEntropy_join_le hℱ R S

private lemma condEntropy_genJoin_block_le [Fintype ι] (hℱ : ℱ ≤ mα)
    (hT : @MeasurePreserving α α mα mα T μ μ) (P : MeasurePartition μ ι) (m r : ℕ) :
    ∀ q : ℕ, condEntropy μ ℱ
        ((ksJoin hT P (q * m + r)).pullback (hT.iterate 0)).cells
      ≤ (∑ j ∈ Finset.range q,
          condEntropy μ ℱ ((ksJoin hT P m).pullback (hT.iterate (j * m))).cells)
        + condEntropy μ ℱ ((ksJoin hT P r).pullback (hT.iterate (q * m))).cells := by
  
  suffices hgen : ∀ q c : ℕ, condEntropy μ ℱ
        ((ksJoin hT P (q * m + r)).pullback (hT.iterate c)).cells
      ≤ (∑ j ∈ Finset.range q,
          condEntropy μ ℱ ((ksJoin hT P m).pullback (hT.iterate (c + j * m))).cells)
        + condEntropy μ ℱ ((ksJoin hT P r).pullback (hT.iterate (c + q * m))).cells by
    intro q
    simpa using hgen q 0
  intro q
  induction q with
  | zero =>
    intro c
    
    have hi : 0 * m + r = r := by ring
    have hs : c + 0 * m = c := by ring
    rw [hi, hs, Finset.range_zero, Finset.sum_empty]
    exact le_of_eq (zero_add _).symm
  | succ k IH =>
    intro c
    
    have hsplit : (k + 1) * m + r = m + (k * m + r) := by ring
    rw [hsplit]
    
    refine (condEntropy_genJoin_pullback_append_le hℱ hT P c m (k * m + r)).trans ?_
    calc condEntropy μ ℱ ((ksJoin hT P m).pullback (hT.iterate c)).cells
          + condEntropy μ ℱ ((ksJoin hT P (k * m + r)).pullback (hT.iterate (c + m))).cells
        ≤ condEntropy μ ℱ ((ksJoin hT P m).pullback (hT.iterate c)).cells
          + ((∑ j ∈ Finset.range k,
              condEntropy μ ℱ ((ksJoin hT P m).pullback (hT.iterate (c + m + j * m))).cells)
            + condEntropy μ ℱ ((ksJoin hT P r).pullback (hT.iterate (c + m + k * m))).cells) := by
          gcongr
          exact IH (c + m)
      _ = (∑ j ∈ Finset.range (k + 1),
              condEntropy μ ℱ ((ksJoin hT P m).pullback (hT.iterate (c + j * m))).cells)
            + condEntropy μ ℱ ((ksJoin hT P r).pullback (hT.iterate (c + (k + 1) * m))).cells := by
          
          rw [Finset.sum_range_succ']
          have hshift : ∀ j ∈ Finset.range k,
              condEntropy μ ℱ ((ksJoin hT P m).pullback (hT.iterate (c + m + j * m))).cells
                = condEntropy μ ℱ ((ksJoin hT P m).pullback (hT.iterate (c + (j + 1) * m))).cells :=
            fun j _ => by rw [show c + m + j * m = c + (j + 1) * m from by ring]
          rw [Finset.sum_congr rfl hshift]
          have hc0 : c + 0 * m = c := by ring
          have hck : c + m + k * m = c + (k + 1) * m := by ring
          rw [hc0, hck]
          ring

variable [Fintype κ]

private lemma condEntropy_genJoin_block_collapse [Fintype ι]
    (hT : @MeasurePreserving α α mα mα T μ μ) (Q : MeasurePartition μ κ) (P : MeasurePartition μ ι)
    (m s n : ℕ) (hsn : s ≤ n) :
    condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n))
        ((ksJoin hT P m).pullback (hT.iterate s)).cells
      ≤ condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q (n - s))) (ksJoin hT P m).cells := by
  have hmα : ∀ k, generatedSigmaAlgebra μ (ksJoin hT Q k) ≤ mα := fun k =>
    generatedSigmaAlgebra_le (ksJoin hT Q k)
  
  have hcomap : MeasurableSpace.comap (T^[s]) (generatedSigmaAlgebra μ (ksJoin hT Q (n - s)))
      ≤ generatedSigmaAlgebra μ (ksJoin hT Q n) := by
    have h := comap_iterate_generatedSigmaAlgebra_ksJoin_le hT Q s (n - s)
    rwa [show s + (n - s) = n from by omega] at h
  calc condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n))
          ((ksJoin hT P m).pullback (hT.iterate s)).cells
      ≤ condEntropy μ
          (MeasurableSpace.comap (T^[s]) (generatedSigmaAlgebra μ (ksJoin hT Q (n - s))))
          ((ksJoin hT P m).pullback (hT.iterate s)).cells :=
        condEntropy_mono_of_le hcomap (hmα n)
          ((ksJoin hT P m).pullback (hT.iterate s))
    _ = condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q (n - s))) (ksJoin hT P m).cells := by
        rw [MeasurePartition.pullback_cells]
        exact condEntropy_comap_pullback (hmα (n - s)) hT s (ksJoin hT P m)

private lemma condEntropy_genJoin_blocking_core [Fintype ι] [Nonempty ι]
    (hT : @MeasurePreserving α α mα mα T μ μ) (Q : MeasurePartition μ κ) (P : MeasurePartition μ ι)
    (m M n : ℕ) (hm : 1 ≤ m) :
    condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n)) (ksJoin hT P n).cells
      ≤ (n / m : ℕ) * condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q M)) (ksJoin hT P m).cells
        + ((M * m + m : ℕ) : ℝ) * Real.log (Fintype.card ι) := by
  set L := Real.log (Fintype.card ι) with hL
  set g := condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q M)) (ksJoin hT P m).cells
  set q := n / m with hq
  set r := n % m with hr
  have hL0 : 0 ≤ L := by
    rw [hL]; exact Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hg0 : 0 ≤ g := condEntropy_nonneg
  have hmα : ∀ k, generatedSigmaAlgebra μ (ksJoin hT Q k) ≤ mα := fun k =>
    generatedSigmaAlgebra_le (ksJoin hT Q k)
  have hnqr : n = q * m + r := by
    rw [hq, hr, Nat.mul_comm (n / m) m]; exact (Nat.div_add_mod n m).symm
  have hrm : r < m := by rw [hr]; exact Nat.mod_lt _ hm
  
  have hblock := condEntropy_genJoin_block_le (hmα n) hT P m r q
  have hp0 : ((ksJoin hT P (q * m + r)).pullback (hT.iterate 0)).cells
      = (ksJoin hT P (q * m + r)).cells := by
    simp only [MeasurePartition.pullback_cells, Function.iterate_zero, Set.preimage_id]
  rw [hp0, ← hnqr] at hblock
  
  
  have hrem : condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n))
      ((ksJoin hT P r).pullback (hT.iterate (q * m))).cells ≤ m * L := by
    refine (condEntropy_genJoin_block_collapse hT Q P r (q * m) n (by omega)).trans ?_
    rw [show n - q * m = r from by omega]
    refine (condEntropy_ksJoin_le_nsmul_log_card (hmα r) hT P r).trans ?_
    have : (r : ℝ) ≤ (m : ℝ) := by exact_mod_cast hrm.le
    exact mul_le_mul_of_nonneg_right this hL0
  
  have hbad : ∀ j ∈ Finset.range q,
      condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n))
          ((ksJoin hT P m).pullback (hT.iterate (j * m))).cells
        ≤ g + (if n - j * m < M then m * L else 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjn : j * m ≤ n := by
      have : j * m ≤ q * m := Nat.mul_le_mul_right m (le_of_lt hj)
      omega
    
    refine (condEntropy_genJoin_block_collapse hT Q P m (j * m) n hjn).trans ?_
    by_cases hbadj : n - j * m < M
    · 
      simp only [hbadj, if_true]
      have huni : condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q (n - j * m)))
          (ksJoin hT P m).cells ≤ m * L :=
        condEntropy_ksJoin_le_nsmul_log_card (hmα (n - j * m)) hT P m
      linarith [huni, hg0]
    · 
      simp only [hbadj, if_false, add_zero]
      have hMle : M ≤ n - j * m := by omega
      exact condEntropy_mono_of_le (generatedSigmaAlgebra_ksJoin_mono hT Q hMle) (hmα (n - j * m))
        (ksJoin hT P m)
  
  have hsum : (∑ j ∈ Finset.range q,
        condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n))
          ((ksJoin hT P m).pullback (hT.iterate (j * m))).cells)
      ≤ q * g + M * (m * L) := by
    calc (∑ j ∈ Finset.range q,
            condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n))
              ((ksJoin hT P m).pullback (hT.iterate (j * m))).cells)
        ≤ ∑ j ∈ Finset.range q, (g + (if n - j * m < M then m * L else 0)) :=
          Finset.sum_le_sum hbad
      _ = q * g + (∑ j ∈ Finset.range q, (if n - j * m < M then m * L else 0)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ q * g + M * (m * L) := by
          gcongr
          
          have hbadset : (Finset.range q).filter (fun j => n - j * m < M)
              ⊆ Finset.Ico (q - M) q := by
            intro j hj
            rw [Finset.mem_filter, Finset.mem_range] at hj
            rw [Finset.mem_Ico]
            obtain ⟨hjq, hbadj⟩ := hj
            refine ⟨?_, hjq⟩
            
            have hjm : j * m ≤ q * m := Nat.mul_le_mul_right m (le_of_lt hjq)
            have h1 : q - j ≤ (q - j) * m := Nat.le_mul_of_pos_right _ (by omega)
            have h2 : (q - j) * m = q * m - j * m := by rw [Nat.sub_mul]
            
            omega
          have hcard : ((Finset.range q).filter (fun j => n - j * m < M)).card ≤ M := by
            calc ((Finset.range q).filter (fun j => n - j * m < M)).card
                ≤ (Finset.Ico (q - M) q).card := Finset.card_le_card hbadset
              _ = q - (q - M) := by rw [Nat.card_Ico]
              _ ≤ M := by omega
          have hmL0 : 0 ≤ (m : ℝ) * L := mul_nonneg (Nat.cast_nonneg m) hL0
          calc (∑ j ∈ Finset.range q, (if n - j * m < M then m * L else 0))
              = ∑ j ∈ (Finset.range q).filter (fun j => n - j * m < M), m * L := by
                rw [← Finset.sum_filter]
            _ = ((Finset.range q).filter (fun j => n - j * m < M)).card * (m * L) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ M * (m * L) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hmL0
  
  calc condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n)) (ksJoin hT P n).cells
      ≤ (∑ j ∈ Finset.range q,
            condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n))
              ((ksJoin hT P m).pullback (hT.iterate (j * m))).cells)
          + condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n))
              ((ksJoin hT P r).pullback (hT.iterate (q * m))).cells := hblock
    _ ≤ (q * g + M * (m * L)) + m * L := add_le_add hsum hrem
    _ = (q : ℕ) * g + ((M * m + m : ℕ) : ℝ) * L := by push_cast; ring

end Blocking

section Limit

variable [Fintype ι] [Fintype κ] [Nonempty ι]

set_option maxHeartbeats 800000 in

private theorem tendsto_condEntropy_genJoin_div (hm : 𝒜 ≤ mα) (hT : MeasurePreserving T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜) (Q : MeasurePartition μ κ) (P : MeasurePartition μ ι)
    (hsat : ⨆ n, generatedSigmaAlgebra μ (ksJoin hT Q n) = 𝒜) :
    Tendsto (fun n => condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n))
        (ksJoin hT P n).cells / (n : ℝ))
      atTop (𝓝 (condKsEntropyPartition hm hT hinv P)) := by
  classical
  set L := Real.log (Fintype.card ι) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  
  set f : ℕ → ℝ := fun n => condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n))
    (ksJoin hT P n).cells
  have hfn : ∀ k, f k = condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q k))
    (ksJoin hT P k).cells := fun k => rfl
  set u : ℕ → ℝ := fun n => f n / (n : ℝ) with hu
  set h := condKsEntropyPartition hm hT hinv P
  
  have hBleA : ∀ n, generatedSigmaAlgebra μ (ksJoin hT Q n) ≤ 𝒜 := fun n => by
    rw [← hsat]
    exact le_iSup (fun k => generatedSigmaAlgebra μ (ksJoin hT Q k)) n
  have hBlemα : ∀ n, generatedSigmaAlgebra μ (ksJoin hT Q n) ≤ mα := fun n =>
    generatedSigmaAlgebra_le (ksJoin hT Q n)
  
  have hu_nonneg : ∀ n, 0 ≤ u n := by
    intro n
    change (0 : ℝ) ≤ condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n))
      (ksJoin hT P n).cells / (n : ℝ)
    exact div_nonneg condEntropy_nonneg (Nat.cast_nonneg n)
  have hu_le : ∀ n, u n ≤ L := by
    intro n
    change condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n)) (ksJoin hT P n).cells / (n : ℝ)
      ≤ L
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, div_zero]; exact hL0
    · rw [div_le_iff₀ (by exact_mod_cast hn)]
      have := condEntropy_ksJoin_le_nsmul_log_card (hBlemα n) hT P n
      rw [← hL] at this
      rw [mul_comm]; exact this
  
  have hbdd_le : IsBoundedUnder (· ≤ ·) atTop u := isBoundedUnder_of_eventually_le
    (Eventually.of_forall hu_le)
  have hbdd_ge : IsBoundedUnder (· ≥ ·) atTop u := isBoundedUnder_of_eventually_ge
    (Eventually.of_forall hu_nonneg)
  
  have hlim_inf : h ≤ liminf u atTop := by
    
    have hcmp : ∀ n, condKsEntropySeq 𝒜 hT P n / (n : ℝ) ≤ u n := by
      intro n
      have hmono : condEntropy μ 𝒜 (ksJoin hT P n).cells ≤ f n :=
        condEntropy_mono_of_le (hBleA n) hm (ksJoin hT P n)
      simp only [hu, condKsEntropySeq]
      gcongr
    
    have hAseq : Tendsto (fun n => condKsEntropySeq 𝒜 hT P n / (n : ℝ)) atTop (𝓝 h) :=
      tendsto_condKsEntropySeq hm hT hinv P
    calc h = liminf (fun n => condKsEntropySeq 𝒜 hT P n / (n : ℝ)) atTop := hAseq.liminf_eq.symm
      _ ≤ liminf u atTop :=
        liminf_le_liminf (Eventually.of_forall hcmp) (hAseq.isBoundedUnder_ge)
          hbdd_le.isCoboundedUnder_ge
  
  have hlim_sup : limsup u atTop ≤ h := by
    
    have hstep1 : ∀ m : ℕ, 1 ≤ m →
        limsup u atTop ≤ condEntropy μ 𝒜 (ksJoin hT P m).cells / (m : ℝ) := by
      intro m hm1
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
      
      have hstep1a : ∀ M : ℕ,
          limsup u atTop
            ≤ condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q M)) (ksJoin hT P m).cells
              / (m : ℝ) := by
        intro M
        set g := condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q M)) (ksJoin hT P m).cells
          with hgeq
        have hg0 : 0 ≤ g := by rw [hgeq]; exact condEntropy_nonneg
        
        set b : ℕ → ℝ := fun n => g / (m : ℝ) + ((M * m + m : ℕ) : ℝ) * L / (n : ℝ) with hb
        have hb_tendsto : Tendsto b atTop (𝓝 (g / (m : ℝ))) := by
          have hz : Tendsto (fun n : ℕ => ((M * m + m : ℕ) : ℝ) * L / (n : ℝ)) atTop (𝓝 0) :=
            tendsto_const_div_atTop_nhds_zero_nat (((M * m + m : ℕ) : ℝ) * L)
          have hc : Tendsto (fun _ : ℕ => g / (m : ℝ)) atTop (𝓝 (g / (m : ℝ))) :=
            tendsto_const_nhds
          have hsum := hc.add hz
          rw [add_zero] at hsum
          simpa only [hb] using hsum
        
        have huleb : ∀ᶠ n in atTop, u n ≤ b n := by
          filter_upwards [eventually_ge_atTop 1] with n hn
          have hnR : (0 : ℝ) < n := by exact_mod_cast hn
          have hcore := condEntropy_genJoin_blocking_core hT Q P m M n hm1
          rw [← hL, ← hgeq, ← hfn n] at hcore
          
          have hdiv : ((n / m : ℕ) : ℝ) ≤ (n : ℝ) / (m : ℝ) := by
            rw [le_div_iff₀ hmR]; exact_mod_cast Nat.div_mul_le_self n m
          have ht1 : ((n / m : ℕ) : ℝ) * g ≤ (n : ℝ) * (g / (m : ℝ)) := by
            calc ((n / m : ℕ) : ℝ) * g ≤ ((n : ℝ) / (m : ℝ)) * g :=
                  mul_le_mul_of_nonneg_right hdiv hg0
              _ = (n : ℝ) * (g / (m : ℝ)) := by ring
          
          have hbn : b n * (n : ℝ)
              = (n : ℝ) * (g / (m : ℝ)) + ((M * m + m : ℕ) : ℝ) * L := by
            rw [hb, add_mul, div_mul_cancel₀ _ (ne_of_gt hnR)]
            ring
          have hub : f n ≤ b n * (n : ℝ) := by
            rw [hbn]
            linarith [hcore, ht1]
          simp only [hu]
          rw [div_le_iff₀ hnR]
          exact hub
        
        calc limsup u atTop
            ≤ limsup b atTop :=
              limsup_le_limsup huleb hbdd_ge.isCoboundedUnder_le hb_tendsto.isBoundedUnder_le
          _ = g / (m : ℝ) := hb_tendsto.limsup_eq
      
      have hLevy : Tendsto
          (fun M => condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q M)) (ksJoin hT P m).cells)
          atTop (𝓝 (condEntropy μ 𝒜 (ksJoin hT P m).cells)) := by
        have h2 := condEntropy_tendsto_iSup
          (fun M => generatedSigmaAlgebra μ (ksJoin hT Q M))
          (fun a b hab => generatedSigmaAlgebra_ksJoin_mono hT Q hab) hBlemα (ksJoin hT P m)
        rwa [hsat] at h2
      
      have hLevy_div : Tendsto
          (fun M => condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q M)) (ksJoin hT P m).cells
            / (m : ℝ)) atTop (𝓝 (condEntropy μ 𝒜 (ksJoin hT P m).cells / (m : ℝ))) :=
        hLevy.div_const _
      exact ge_of_tendsto hLevy_div (Eventually.of_forall hstep1a)
    
    have hAseq : Tendsto (fun m => condEntropy μ 𝒜 (ksJoin hT P m).cells / (m : ℝ)) atTop
        (𝓝 h) := by
      have := tendsto_condKsEntropySeq hm hT hinv P
      simpa only [condKsEntropySeq] using this
    refine ge_of_tendsto hAseq ?_
    filter_upwards [eventually_ge_atTop 1] with m hm1
    exact hstep1 m hm1
  
  exact tendsto_of_le_liminf_of_limsup_le hlim_inf hlim_sup hbdd_le hbdd_ge

private theorem abramovRokhlin_partition (hm : 𝒜 ≤ mα) (hT : MeasurePreserving T μ μ)
    (hinv : MeasurableSpace.comap T 𝒜 ≤ 𝒜) (Q : MeasurePartition μ κ) (P : MeasurePartition μ ι)
    (g : ∀ n, (Fin n → ι) → (Fin n → κ))
    (hrefine : ∀ n f, (ksJoin hT P n).cells f ≤ᵐ[μ] (ksJoin hT Q n).cells (g n f))
    (hsat : ⨆ n, generatedSigmaAlgebra μ (ksJoin hT Q n) = 𝒜) :
    ksEntropyPartition hT P
      = ksEntropyPartition hT Q + condKsEntropyPartition hm hT hinv P := by
  
  have hdefect : Tendsto (fun n => (condEntropy μ (generatedSigmaAlgebra μ (ksJoin hT Q n))
      (ksJoin hT P n).cells - condKsEntropySeq 𝒜 hT P n) / (n : ℝ)) atTop (𝓝 0) := by
    have hmoving := tendsto_condEntropy_genJoin_div hm hT hinv Q P hsat
    have hfixed := tendsto_condKsEntropySeq hm hT hinv P
    have hsub := hmoving.sub hfixed
    rw [sub_self] at hsub
    refine hsub.congr fun n => ?_
    rw [sub_div]
  exact abramovRokhlin_partition_of_defect hm hT hinv Q P g hrefine hdefect

end Limit

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function Filter Topology

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι κ : Type*} [MeasurableSpace α]

private def joinPartition [Fintype ι] [Fintype κ] {μ : Measure α}
    (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) : MeasurePartition μ (ι × κ) where
  cells := joinCells P.cells Q.cells
  measurable := fun p => (P.measurable p.1).inter (Q.measurable p.2)
  aedisjoint := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hpq
    simp only [onFun, joinCells_apply]
    rcases eq_or_ne i i' with hi | hi
    · 
      subst hi
      have hj : j ≠ j' := fun h => hpq (by rw [h])
      exact AEDisjoint.mono (Q.aedisjoint hj) Set.inter_subset_right Set.inter_subset_right
    · 
      exact AEDisjoint.mono (P.aedisjoint hi) Set.inter_subset_left Set.inter_subset_left
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro x 
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (P.cover ▸ Set.mem_univ x)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (Q.cover ▸ Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨(i, j), hi, hj⟩

@[simp]
private lemma joinPartition_cells [Fintype ι] [Fintype κ] {μ : Measure α}
    (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) :
    (joinPartition P Q).cells = joinCells P.cells Q.cells := rfl

omit [MeasurableSpace α] in

private lemma ksJoinCells_joinCells (s : ι → Set α) (t : κ → Set α) (T : α → α) (n : ℕ)
    (f : Fin n → ι × κ) :
    ksJoinCells (joinCells s t) T n f
      = ksJoinCells s T n (fun k => (f k).1) ∩ ksJoinCells t T n (fun k => (f k).2) := by
  simp only [ksJoinCells_apply, joinCells_apply, Set.preimage_inter]
  rw [Set.iInter_inter_distrib]

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function Filter Topology

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι : Type*} [MeasurableSpace α]

private lemma bddBelow_ksEntropySeq_div [Fintype ι] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι) :
    BddBelow (Set.range fun n => ksEntropySeq hT P n / n) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact div_nonneg (ksEntropySeq_nonneg hT P n) (Nat.cast_nonneg n)

lemma ksEntropyPartition_le_ksEntropySeq_div [Fintype ι] {μ : Measure α}
    [IsProbabilityMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (P : MeasurePartition μ ι) {n : ℕ} (hn : 1 ≤ n) :
    ksEntropyPartition hT P ≤ ksEntropySeq hT P n / n :=
  (ksSubadditive hT P).lim_le_div (bddBelow_ksEntropySeq_div hT P) (Nat.one_le_iff_ne_zero.mp hn)

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function Filter Topology

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι κ : Type*} [MeasurableSpace α]

private lemma negMulLog_sum_le_sum_negMulLog {ω : Type*} [Fintype ω] (x : ω → ℝ)
    (hx : ∀ j, 0 ≤ x j) :
    Real.negMulLog (∑ j, x j) ≤ ∑ j, Real.negMulLog (x j) := by
  
  have hterm : ∀ j, x j * Real.log (x j) ≤ x j * Real.log (∑ i, x i) := by
    intro j
    rcases eq_or_lt_of_le (hx j) with hxj | hxj
    · simp [← hxj]
    · have hle : x j ≤ ∑ i, x i := Finset.single_le_sum (fun i _ => hx i) (Finset.mem_univ j)
      exact mul_le_mul_of_nonneg_left (Real.log_le_log hxj hle) (hx j)
  have hsum : ∑ j, x j * Real.log (x j) ≤ ∑ j, x j * Real.log (∑ i, x i) :=
    Finset.sum_le_sum fun j _ => hterm j
  rw [← Finset.sum_mul] at hsum
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  linarith [hsum]

private lemma entropy_le_entropy_join [Fintype ι] [Fintype κ] {μ : Measure α} [IsProbabilityMeasure μ]
    (P : MeasurePartition μ ι) (Q : MeasurePartition μ κ) :
    entropy μ P.cells ≤ entropy μ (joinCells P.cells Q.cells) := by
  
  set p : ι × κ → ℝ := fun x => (μ (P.cells x.1 ∩ Q.cells x.2)).toReal with hp
  have hpnn : ∀ x, 0 ≤ p x := fun _ => ENNReal.toReal_nonneg
  
  have hrow : ∀ i, ∑ j, p (i, j) = (μ (P.cells i)).toReal := by
    intro i
    rw [Q.measure_eq_sum_inter (P.measurable i),
      ENNReal.toReal_sum (fun j _ => measure_ne_top μ _)]
  
  rw [entropy_def, entropy_def, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← hrow i]
  exact negMulLog_sum_le_sum_negMulLog (fun j => p (i, j)) (fun j => hpnn (i, j))

private lemma ksEntropySeq_le_join [Fintype ι] [Fintype κ] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι)
    (Q : MeasurePartition μ κ) (n : ℕ) :
    ksEntropySeq hT P n ≤ ksEntropySeq hT (joinPartition P Q) n := by
  
  set A : MeasurePartition μ (Fin n → ι) := ksJoin hT P n with hA
  set B : MeasurePartition μ (Fin n → κ) := ksJoin hT Q n with hB
  
  have hreindex : ksEntropySeq hT (joinPartition P Q) n
      = entropy μ (joinCells A.cells B.cells) := by
    rw [ksEntropySeq, ksJoin_cells, joinPartition_cells,
      ← entropy_reindex μ (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ι) (fun _ => κ)).symm,
      entropy_def, entropy_def]
    refine Finset.sum_congr rfl fun q _ => ?_
    obtain ⟨g, h⟩ := q
    rw [hA, hB, ksJoin_cells, ksJoin_cells, joinCells_apply]
    have hcell : ksJoinCells (joinCells P.cells Q.cells) T n
        ((Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ι) (fun _ => κ)).symm (g, h))
          = ksJoinCells P.cells T n g ∩ ksJoinCells Q.cells T n h :=
      ksJoinCells_joinCells P.cells Q.cells T n _
    rw [hcell]
  rw [hreindex, ksEntropySeq, ← hA]
  exact entropy_le_entropy_join A B

private lemma ksEntropyPartition_le_join [Fintype ι] [Fintype κ] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : MeasurePreserving T μ μ) (P : MeasurePartition μ ι)
    (Q : MeasurePartition μ κ) :
    ksEntropyPartition hT P ≤ ksEntropyPartition hT (joinPartition P Q) := by
  refine le_of_tendsto_of_tendsto' (tendsto_ksEntropySeq hT P)
    (tendsto_ksEntropySeq hT (joinPartition P Q)) ?_
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_le_div_of_nonneg_right (ksEntropySeq_le_join hT P Q n) hn0.le

end D5.S3.Entropy.KolmogorovSinai

open MeasureTheory Function Filter Topology ProbabilityTheory MeasurableSpace

namespace D5.S3.Entropy.KolmogorovSinai

variable {α : Type*} {ι : Type*} [mα : MeasurableSpace α] [StandardBorelSpace α] [Fintype ι]

private lemma condEntropy_full_eq_zero {μ : Measure α} [IsProbabilityMeasure μ]
    (R : MeasurePartition μ ι) :
    condEntropy μ mα R.cells = 0 := by
  have hσ : SigmaFinite (μ.trim (le_refl mα)) := by rw [trim_eq_self]; infer_instance
  rw [condEntropy_def]
  
  refine integral_eq_zero_of_ae ?_
  
  have hcell : ∀ i : ι, (fun ω => (@condExpKernel α mα _ μ _ mα ω (R.cells i)).toReal)
      =ᵐ[μ] (R.cells i).indicator (fun _ => (1 : ℝ)) := by
    intro i
    
    have h1 : (fun ω => (@condExpKernel α mα _ μ _ mα ω (R.cells i)).toReal)
        =ᵐ[μ] μ⟦R.cells i | mα⟧ := condExpKernel_ae_eq_condExp le_rfl (R.measurable i)
    
    
    have h2 : μ⟦R.cells i | mα⟧ = (R.cells i).indicator (fun _ => (1 : ℝ)) :=
      condExp_of_stronglyMeasurable le_rfl
        ((stronglyMeasurable_const.indicator (R.measurable i)))
        ((integrable_const (1 : ℝ)).indicator (R.measurable i))
    rw [h2] at h1
    exact h1
  
  filter_upwards [ae_all_iff.mpr hcell] with ω hω
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hω i]
  
  by_cases hmem : ω ∈ R.cells i
  · rw [Set.indicator_of_mem hmem, Real.negMulLog_one]
  · rw [Set.indicator_of_notMem hmem, Real.negMulLog_zero]

omit [StandardBorelSpace α] in

private lemma ksJoin_joinPartition_subset {κ : Type*} [Fintype κ] {μ : Measure α} {T : α → α}
    (hT : MeasurePreserving T μ μ) (Q : MeasurePartition μ κ) (P : MeasurePartition μ ι)
    (n : ℕ) (f : Fin n → κ × ι) :
    (ksJoin hT (joinPartition Q P) n).cells f ⊆
      (ksJoin hT P n).cells (fun k => (f k).2) := by
  rw [ksJoin_cells, ksJoin_cells, ksJoinCells_apply, ksJoinCells_apply]
  refine Set.iInter_mono fun k => ?_
  
  rw [joinPartition_cells, joinCells_apply]
  exact Set.preimage_mono Set.inter_subset_right

omit [StandardBorelSpace α] in

private lemma MeasurePartition.index_nonempty {μ : Measure α} [IsProbabilityMeasure μ]
    (R : MeasurePartition μ ι) : Nonempty ι := by
  obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure μ
  obtain ⟨i, _⟩ := Set.mem_iUnion.mp (R.cover ▸ Set.mem_univ x)
  exact ⟨i⟩

private lemma ksEntropyPartition_le_of_generating {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) {n : ℕ} (P : MeasurePartition μ (Fin n))
    (hgen : IsGenerating μ T P) {m : ℕ} (Q : MeasurePartition μ (Fin m)) :
    ksEntropyPartition hT Q ≤ ksEntropyPartition hT P := by
  
  
  set R : MeasurePartition μ (Fin m × Fin n) := joinPartition Q P with hR
  have hinv : MeasurableSpace.comap T mα ≤ mα := hT.measurable.comap_le
  have hne : Nonempty (Fin m × Fin n) := R.index_nonempty
  
  have hsat : (⨆ k, generatedSigmaAlgebra μ (ksJoin hT P k)) = mα := by
    rw [iSup_generatedSigmaAlgebra_ksJoin_eq]; exact hgen
  
  set g : ∀ k, (Fin k → Fin m × Fin n) → (Fin k → Fin n) :=
    fun _ f k => (f k).2 with hg
  have hrefine : ∀ k f, (ksJoin hT R k).cells f ≤ᵐ[μ] (ksJoin hT P k).cells (g k f) := by
    intro k f
    exact Filter.Eventually.of_forall fun x hx =>
      (hR ▸ ksJoin_joinPartition_subset hT Q P k f) hx
  
  have hAR := abramovRokhlin_partition (𝒜 := mα) le_rfl hT hinv P R g hrefine hsat
  
  have hrel_le : condKsEntropyPartition (𝒜 := mα) le_rfl hT hinv R ≤ condEntropy μ mα R.cells :=
    condKsEntropyPartition_le_condEntropy le_rfl hT hinv R
  rw [condEntropy_full_eq_zero R] at hrel_le
  have hrel_ge : 0 ≤ condKsEntropyPartition (𝒜 := mα) le_rfl hT hinv R :=
    condKsEntropyPartition_nonneg le_rfl hT hinv R
  have hrel : condKsEntropyPartition (𝒜 := mα) le_rfl hT hinv R = 0 :=
    le_antisymm hrel_le hrel_ge
  
  have hRP : ksEntropyPartition hT R = ksEntropyPartition hT P := by
    rw [hAR, hrel, add_zero]
  
  calc ksEntropyPartition hT Q
      ≤ ksEntropyPartition hT (joinPartition Q P) := ksEntropyPartition_le_join hT Q P
    _ = ksEntropyPartition hT P := hRP

theorem ksEntropy_eq_ksEntropyPartition_of_generating
    {μ : Measure α} [IsProbabilityMeasure μ] {T : α → α}
    (hT : MeasurePreserving T μ μ) {n : ℕ} (P : MeasurePartition μ (Fin n))
    (hgen : IsGenerating μ T P) :
    ksEntropy hT = ((ksEntropyPartition hT P : ℝ) : EReal) := by
  refine le_antisymm ?_ (le_ksEntropy hT P)
  
  refine iSup_le fun m => iSup_le fun Q => ?_
  rw [EReal.coe_le_coe_iff]
  exact ksEntropyPartition_le_of_generating hT P hgen Q

end D5.S3.Entropy.KolmogorovSinai

