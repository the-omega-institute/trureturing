/- GID: D5/S1/Words/ReturnWords/CassaigneGoldenRecurrence
   generality: I
   mirror-B: D5/B/S1/Words/ReturnWords/CassaigneGoldenRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The golden recurrence quotient is two plus the golden ratio. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26320
admission_basis: escape-witness
escape_witness: golden_rhoStar_eq_sharp
no_short_recurrence_of_periodic: proof_shape: content; escape_witness: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.no_short_recurrence_of_periodic; consumers: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.recurrence_value_lower_of_periodic.
recurrence_value_lower_of_periodic: proof_shape: content; escape_witness: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.no_short_recurrence_of_periodic; consumers: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_rhoStar_ge_sharp.
long_period_recurrence_ratio_tendsto: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_rhoStar_ge_sharp.
golden_rhoStar_ge_sharp: proof_shape: content; escape_witness: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.no_short_recurrence_of_periodic, _private.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.0.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.removed_last_gap_ge_returns; consumers: D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_rhoStar_eq_sharp.
arc_gap_le_of_candidates: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_occurrence_gap_le_fib.
returns_antitone: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_arc_length_lower.
negative_slope_returns: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_arc_length_lower.
golden_arc_length_lower: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_occurrence_gap_le_fib.
golden_small_displacement_candidates: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_occurrence_gap_le_fib.
golden_occurrence_gap_le_fib: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_recurrence_bound_fib.
golden_bound_of_gap_max: proof_shape: content; escape_witness: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_bound_of_gap_max; consumers: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_recurrence_bound_fib.
golden_recurrence_bound_fib: proof_shape: content; escape_witness: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_bound_of_gap_max; consumers: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_recurrence_ratio_le_fib.
fib_recurrence_upper_tendsto: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_rhoStar_le_sharp.
greatestFib_tendsto: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_rhoStar_le_sharp.
golden_recurrence_ratio_le_fib: proof_shape: content; escape_witness: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_bound_of_gap_max; consumers: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_rhoStar_le_sharp.
golden_rhoStar_le_sharp: proof_shape: content; escape_witness: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_bound_of_gap_max; consumers: D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_rhoStar_eq_sharp.
golden_rhoStar_eq_sharp: proof_shape: content; escape_witness: _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.golden_bound_of_gap_max, _private.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.0.D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence.no_short_recurrence_of_periodic, _private.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.0.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.removed_last_gap_ge_returns; consumers: _private.D5.S1.Words.Complexity.CassaigneSturmianCharacterization.0.D5.S1.Words.Complexity.CassaigneSturmianCharacterization.nominated_invariant_values.
-/


import D5.S0.Computability.Coding.BiasedMassFrontier
import D5.S0.Tower.GoldenGapWord
import D5.S1.Phase.ThreeGap.Foundations
import D5.S1.Phase.ThreeGap.Main
import D5.S1.Words.Complexity.CassaigneRecurrenceTransport
import D5.S1.Words.GoldenFactorComplexity
import D5.S1.Words.GoldenMechanicalWord
import D5.S1.Words.GoldenRecurrence
import D5.S1.Words.GoldenUniformRecurrence
import D5.S1.Words.GoldenWord
import D5.S1.Words.Powers.GoldenFourthPower
import D5.S1.Words.ReturnWords.AdjacentGoldenOccurrencesInterface
import D5.S1.Words.ReturnWords.GoldenArcFirstReturn
import D5.S1.Words.ReturnWords.GoldenArcFirstReturnCore
import D5.S1.Words.ReturnWords.GoldenGapFirstReturn
import D5.S1.Words.ReturnWords.GoldenOccurrenceGaps
import D5.S1.Words.ReturnWords.GoldenRankArcs
import D5.S1.Words.ReturnWords.GoldenReturnWords
import D5.S1.Words.ReturnWords.GoldenSharpRepetitions
import D5.S1.Words.ReturnWords.RotationGapArcs
set_option maxHeartbeats 1600000

open D5.S0.Computability.Coding.BiasedMassFrontier

namespace D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence

open Set Filter D5.S1.Words.Complexity D5.S1.Words D5.S1.Words.Mechanical D5.S1.Words.Powers
open ThreeGap GoldenSubstStartSharpness D5.S1.Words.GoldenArcFirstReturnInternal
open scoped ENNReal Topology
open D5.S1.Words.Complexity.CassaigneRecurrenceTransport
open D5.S1.Words.Complexity.CassaigneIndexTransport
open D5.S1.Words.ReturnWords.GoldenSharpRepetitions

private theorem no_short_recurrence_of_periodic (a p L N : ℕ) (hp : 0 < p)
    (hplen : 2*p+1 ≤ L) (hNL : N ≤ L) (hper : GoldenPeriodic a p L) :
    ¬ HasRecurrenceBound goldenWord (p+1) N := by
  classical
  intro hrec
  let n := p+1
  let S := (Finset.range p).image (fun t => goldenFactor n (a+t))
  have hsub : goldenFactorSet n ⊆ S := by
    intro x hx
    obtain ⟨i,rfl⟩ := mem_goldenFactorSet.mp hx
    have hw : (rayPrefix (fun index => goldenWord (a + index)) N) ∈ factorLanguage goldenWord N :=
      ⟨a, rfl⟩
    have hx' : (rayPrefix (fun index => goldenWord (i + index)) n) ∈ factorLanguage goldenWord n :=
      ⟨i, rfl⟩
    have hh := hrec _ hw _ hx'
    obtain ⟨t,ht,hpoint⟩ := hh
    simp only [rayPrefix, List.length_ofFn] at ht
    have hpoint' (r : ℕ) (hr : r < n) : goldenWord (i+r) = goldenWord (a+(t+r)) := by
      have he := hpoint ⟨r, by simpa only [rayPrefix, List.length_ofFn] using hr⟩
      simpa only [rayPrefix, List.getD_eq_getElem, List.length_ofFn, hr,
        show t+r < N by omega, List.getElem_ofFn] using he
    apply Finset.mem_image.mpr
    refine ⟨t%p,Finset.mem_range.mpr (Nat.mod_lt t hp),?_⟩
    apply List.ext_get
    · simp [goldenFactor]
    · intro j hj hj'
      have hjn : j < n := by simpa only [goldenFactor,List.length_ofFn] using hj
      have he := hpoint' j hjn
      have h0 := periodic_mod a p L hper (t+j) (by omega)
      have h1 := periodic_mod a p L hper (t%p+j) (by have hm := Nat.mod_lt t hp; dsimp [n] at hjn; omega)
      have hm : (t%p+j)%p=(t+j)%p := by simp only [Nat.add_mod,Nat.mod_mod]
      rw [hm] at h1
      simp only [goldenFactor,List.get_eq_getElem,List.getElem_ofFn]
      simpa [Nat.add_assoc] using h1.trans (h0.symm.trans he.symm)
  have hc := Finset.card_le_card hsub
  have hs : S.card ≤ p := (Finset.card_image_le).trans (by simp)
  rw [golden_factor_complexity] at hc
  dsimp [n] at hc
  omega

private theorem recurrence_value_lower_of_periodic (a p L : ℕ) (hp : 0 < p)
    (hplen : 2*p+1 ≤ L) (hper : GoldenPeriodic a p L) :
    ((L+1 : ℕ) : ℝ≥0∞) ≤ (fun r : ℕ∞ => (r : ℝ≥0∞)) (recurrenceFunction goldenWord (p+1)) := by
  have hz : (L+1 : ℕ∞) ≤ recurrenceFunction goldenWord (p+1) := by
    apply le_sInf
    rintro r ⟨N,rfl,hN⟩
    have hgt : L < N := by
      by_contra hn
      exact no_short_recurrence_of_periodic a p L N hp hplen (by omega) hper hN
    exact_mod_cast (show L+1 ≤ N by omega)
  have hh := ENat.toENNReal_mono hz
  simpa only [ENat.toENNReal_add,ENat.toENNReal_one,ENat.toENNReal_coe,Nat.cast_add,Nat.cast_one] using hh

private theorem long_period_recurrence_ratio_tendsto :
    Tendsto (fun k : ℕ =>
      ((Nat.fib (k+4)+Nat.fib (k+6)-2+1 : ℕ) : ℝ)/((Nat.fib (k+4)+1 : ℕ) : ℝ))
      atTop (𝓝 (2+Real.goldenRatio)) := by
  have tfib : Tendsto (fun k : ℕ => (Nat.fib (k+4) : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (f := fun k : ℕ => (k : ℝ)) _ tendsto_natCast_atTop_atTop
    intro k
    have hh := index_lt_diagonal_level (k+2)
    rw [fibWord_length] at hh
    simp only [Nat.add_assoc,Nat.reduceAdd] at hh
    exact_mod_cast (show k ≤ Nat.fib (k+4) by omega)
  have hi : Tendsto (fun k : ℕ => ((Nat.fib (k+4) : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tfib
  have ht := (long_period_ratio_tendsto.add hi).div (tendsto_const_nhds.add hi) (by norm_num : (1 : ℝ)+0 ≠ 0)
  convert ht using 1
  · funext k
    have hp : (0 : ℝ) < Nat.fib (k+4) := Nat.cast_pos'.mpr (Nat.fib_pos.mpr (by omega))
    simp only [Pi.div_apply,Pi.add_apply]
    push_cast
    field_simp <;> ring
  · norm_num

private theorem golden_rhoStar_ge_sharp :
    ENNReal.ofReal (2+Real.goldenRatio) ≤ rhoStar goldenWord := by
  apply le_iInf
  intro N
  apply le_of_tendsto (ENNReal.tendsto_ofReal long_period_recurrence_ratio_tendsto)
  filter_upwards [eventually_ge_atTop N] with k hk
  let p := Nat.fib (k+4)
  let L := Nat.fib (k+4)+Nat.fib (k+6)-2
  obtain ⟨a,hper⟩ := golden_fibonacci_long_period_exists (k+4) (by omega)
  have hp : 0 < p := Nat.fib_pos.mpr (by omega)
  have hplen : 2*p+1 ≤ L := by
    have hf : 3 ≤ Nat.fib (k+5) := by
      have hh := Nat.fib_mono (show 4 ≤ k+5 by omega)
      norm_num at hh
      exact hh
    have hs : Nat.fib (k+6)=Nat.fib (k+5)+Nat.fib (k+4) := by have hh := @Nat.fib_add_two (k+4); simp only [Nat.add_assoc,Nat.reduceAdd] at hh; omega
    dsimp [p,L]
    omega
  have hper' : GoldenPeriodic a p L := by simpa [p,L,Nat.add_assoc] using hper
  have hval := recurrence_value_lower_of_periodic a p L hp hplen hper'
  have hr : ENNReal.ofReal (((L+1 : ℕ) : ℝ)/((p+1 : ℕ) : ℝ)) ≤ recurrenceRatio goldenWord (p+1) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_natCast,ENNReal.ofReal_natCast,
      recurrenceRatio,if_neg (Nat.succ_ne_zero p)]
    exact ENNReal.div_le_div_right hval _
  have hn : N ≤ p+1 := by
    have hh := index_lt_diagonal_level (k+2)
    rw [fibWord_length] at hh
    simp only [Nat.add_assoc,Nat.reduceAdd] at hh
    dsimp [p]
    omega
  exact hr.trans (le_iSup_of_le (p+1) (by rw [if_pos hn]))

private theorem arc_gap_le_of_candidates (n : ℕ) (hn : 0 < n) (r : Fin (n+1)) (M : ℕ)
    (hf : ∃ p, 0 < p ∧ p ≤ M ∧ forwardDisplacement goldenMechanicalSlope p <
      rotationCut goldenMechanicalSlope (n+1) r.succ-rotationCut goldenMechanicalSlope (n+1) r.castSucc)
    (hb : ∃ q, 0 < q ∧ q ≤ M ∧ backwardDisplacement goldenMechanicalSlope q <
      rotationCut goldenMechanicalSlope (n+1) r.succ-rotationCut goldenMechanicalSlope (n+1) r.castSucc)
    {d : ℕ} (hd : d ∈ goldenArcFirstReturnGapSet n r) : d ≤ M := by
  let alpha := goldenMechanicalSlope
  let a := rotationCut alpha (n+1) r.castSucc
  let b := rotationCut alpha (n+1) r.succ
  let ell := b-a
  have ha0 : 0 ≤ a := by
    calc
      0 = rotationCut alpha (n+1) 0 := (rotation_cut_zero _ _).symm
      _ ≤ a := (rotationCut _ _).monotone (Fin.zero_le _)
  have hb1 : b ≤ 1 := by
    calc
      b ≤ rotationCut alpha (n+1) (Fin.last (n+1)) := (rotationCut _ _).monotone (Fin.le_last _)
      _ = 1 := rotation_cut_last _ _
  have hellpos : 0 < ell := rotation_gap_arc_pos alpha (n+1) r
  have hellone : ell < 1 := by
    by_cases hr0 : r.val=0
    · have hrs : r.succ < Fin.last (n+1) := by apply Fin.mk_lt_mk.mpr; omega
      have hblt : b < 1 := by
        calc
          b < rotationCut alpha (n+1) (Fin.last (n+1)) := (rotationCut _ _).strictMono hrs
          _ = 1 := rotation_cut_last _ _
      dsimp [ell]
      linarith
    · have hrp : (0 : Fin (n+1+1)) < r.castSucc := by apply Fin.mk_lt_mk.mpr; simpa using Nat.pos_of_ne_zero hr0
      have hal : 0 < a := by
        calc
          0 = rotationCut alpha (n+1) 0 := (rotation_cut_zero _ _).symm
          _ < a := (rotationCut _ _).strictMono hrp
      dsimp [ell]
      linarith
  have hend : a+ell ≤ 1 := by dsimp [ell]; linarith
  obtain ⟨d0,hd0,hbest⟩ := D5.S1.Words.rotation_gap_best_displacement alpha (n+1) (by omega) r
  have hexp : ∃ p, 0 < p ∧ forwardDisplacement alpha p < ell := by obtain ⟨p,hp,_,hpl⟩ := hf; exact ⟨p,hp,hpl⟩
  have hexq : ∃ q, 0 < q ∧ backwardDisplacement alpha q < ell := by obtain ⟨q,hq,_,hql⟩ := hb; exact ⟨q,hq,hql⟩
  let p := Nat.find hexp
  let q := Nat.find hexq
  have hp := Nat.find_spec hexp
  have hq := Nat.find_spec hexq
  have hpf : ∀ k, 0 < k → forwardDisplacement alpha k < ell → p ≤ k := fun k hk hlt => Nat.find_min' hexp ⟨hk,hlt⟩
  have hqf : ∀ k, 0 < k → backwardDisplacement alpha k < ell → q ≤ k := fun k hk hlt => Nat.find_min' hexq ⟨hk,hlt⟩
  have hpM : p ≤ M := by obtain ⟨k,hk,hkM,hkl⟩ := hf; exact (hpf k hk hkl).trans hkM
  have hqM : q ≤ M := by obtain ⟨k,hk,hkM,hkl⟩ := hb; exact (hqf k hk hkl).trans hkM
  have hs := minimal_displacements_sum_of_best golden_mechanical_slope_irrational hellpos hd0
    hp.1 hp.2 hpf hq.1 hq.2 hqf hbest
  have hpair := orbit_arc_first_return_eq_pair golden_mechanical_slope_irrational ha0 hellpos hellone hend
    hp.1 hp.2 hpf hq.1 hq.2 hqf hs
  have he : a+ell=b := by dsimp [ell]; ring
  have hsets : goldenArcFirstReturnGapSet n r = orbitArcFirstReturnGapSet alpha a ell := by
    ext gap
    simp only [goldenArcFirstReturnGapSet,orbitArcFirstReturnGapSet,Set.mem_setOf_eq,rotationGapArc]
    rw [he]
    rfl
  rw [hsets,hpair] at hd
  rcases Set.mem_insert_iff.mp hd with h | h
  · rw [h]
    exact hpM
  · have hh := Set.mem_singleton_iff.mp h
    rw [hh]
    exact hqM

private theorem returns_antitone (a : ℝ) {N M : ℕ}
    (hN : 2 ≤ orbitCard a N) (hM : 2 ≤ orbitCard a M) (hNM : N ≤ M) :
    etaPos a M ≤ etaPos a N ∧ etaNeg a M ≤ etaNeg a N := by
  have hsub : ∀ x, x ∈ orbit a N → x ∈ orbit a M := by
    intro x hx
    obtain ⟨i,hi,he⟩ := (mem_orbit_iff a N x).mp hx
    exact (mem_orbit_iff a M x).mpr ⟨i,hi.trans_le hNM,he⟩
  constructor
  · exact no_orbit_below_etaPos a hM (hsub _ (posOrbit_subset_orbit a N (etaPos_mem a hN))) (etaPos_pos a hN)
  · have hh := le_one_sub_etaNeg a hM
      ((mem_posOrbit_iff a M _).mpr ⟨ne_of_gt (posOrbit_pos a N (max_posOrbit_mem a hN)),hsub _ (posOrbit_subset_orbit a N (max_posOrbit_mem a hN))⟩)
    linarith

private theorem negative_slope_returns (N : ℕ) (h2 : 2 ≤ orbitCard Real.goldenRatio N) :
    etaPos (-goldenMechanicalSlope) N=etaNeg Real.goldenRatio N ∧
      etaNeg (-goldenMechanicalSlope) N=etaPos Real.goldenRatio N := by
  have he : posOrbit (-goldenMechanicalSlope) N=posOrbit (-Real.goldenRatio) N := by simp only [posOrbit,golden_negative_slope_orbit]
  have hp : etaPos (-goldenMechanicalSlope) N=etaPos (-Real.goldenRatio) N := by simp only [etaPos,he]
  have hm : etaNeg (-goldenMechanicalSlope) N=etaNeg (-Real.goldenRatio) N := by simp only [etaNeg,he]
  have hs := negative_returns_swap _ Real.goldenRatio_irrational h2
  exact ⟨hp.trans hs.1,hm.trans hs.2⟩

private theorem golden_arc_length_lower (q n : ℕ) (hq : 3 ≤ q) (hn : 0 < n)
    (hNF : n+1 ≤ Nat.fib (q+1)) (r : Fin (n+1)) :
    Real.goldenRatio⁻¹^q ≤ rotationCut goldenMechanicalSlope (n+1) r.succ-
      rotationCut goldenMechanicalSlope (n+1) r.castSucc := by
  have h2N : 2 ≤ orbitCard (-goldenMechanicalSlope) (n+1) := by
    rw [orbitCard_eq_of_irrational _ golden_mechanical_slope_irrational.neg]
    omega
  have hFM : 2 ≤ Nat.fib (q+1) := by
    have hh := Nat.fib_mono (show 3 ≤ q+1 by omega)
    norm_num at hh
    exact hh
  have h2M : 2 ≤ orbitCard (-goldenMechanicalSlope) (Nat.fib (q+1)) := by
    rw [orbitCard_eq_of_irrational _ golden_mechanical_slope_irrational.neg]
    exact hFM
  have h2g : 2 ≤ orbitCard Real.goldenRatio (Nat.fib (q+1)) := by rw [orbitCard_eq_of_irrational _ Real.goldenRatio_irrational]; exact hFM
  have hs := negative_slope_returns (Nat.fib (q+1)) h2g
  have hm := returns_antitone (-goldenMechanicalSlope) h2N h2M hNF
  have hqpow : Real.goldenRatio⁻¹^q ≤ Real.goldenRatio⁻¹^(q-1) :=
    pow_le_pow_of_le_one (inv_nonneg.mpr Real.goldenRatio_pos.le) (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio).le (by omega)
  have hplus : Real.goldenRatio⁻¹^q ≤ etaPos (-goldenMechanicalSlope) (Nat.fib (q+1)) ∧
      Real.goldenRatio⁻¹^q ≤ etaNeg (-goldenMechanicalSlope) (Nat.fib (q+1)) := by
    rw [hs.1,hs.2]
    have he1 : q-1+2=q+1 := by omega
    have he2 : q-1+1=q := by omega
    rcases Nat.even_or_odd (q-1) with he | ho
    · have hh := golden_eta_even (q-1) (by omega) he
      rw [he1,he2] at hh
      rw [hh.1,hh.2]
      exact ⟨hqpow,le_rfl⟩
    · have hh := golden_eta_odd (q-1) (by omega) ho
      rw [he1,he2] at hh
      rw [hh.1,hh.2]
      exact ⟨le_rfl,hqpow⟩
  have hx := rotation_gap_length_mem_threegap goldenMechanicalSlope (n+1) r
  have hh := gaps_subset_returns (-goldenMechanicalSlope) h2N (by simpa using hx)
  simp only [Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hh with h | h | h
  · rw [h]; exact hplus.1.trans hm.1
  · rw [h]; exact hplus.2.trans hm.2
  · rw [h]
    exact (hplus.1.trans hm.1).trans (le_add_of_nonneg_right (etaNeg_pos _ h2N).le)

private theorem golden_small_displacement_candidates (q : ℕ) (hq : 3 ≤ q) :
    (∃ p, 0 < p ∧ p ≤ Nat.fib (q+2) ∧ forwardDisplacement goldenMechanicalSlope p < Real.goldenRatio⁻¹^q) ∧
    (∃ p, 0 < p ∧ p ≤ Nat.fib (q+2) ∧ backwardDisplacement goldenMechanicalSlope p < Real.goldenRatio⁻¹^q) := by
  have h1 : Real.goldenRatio⁻¹^(q+1)<Real.goldenRatio⁻¹^q :=
    (pow_lt_pow_iff_right_of_lt_one₀ (inv_pos.mpr Real.goldenRatio_pos) (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)).mpr (by omega)
  have h2 : Real.goldenRatio⁻¹^(q+2)<Real.goldenRatio⁻¹^q :=
    (pow_lt_pow_iff_right_of_lt_one₀ (inv_pos.mpr Real.goldenRatio_pos) (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)).mpr (by omega)
  have hp1 : 0 < Nat.fib (q+1) := Nat.fib_pos.mpr (by omega)
  have hp2 : 0 < Nat.fib (q+2) := Nat.fib_pos.mpr (by omega)
  have hle : Nat.fib (q+1) ≤ Nat.fib (q+2) := Nat.fib_mono (by omega)
  rcases Nat.even_or_odd q with he | ho
  · constructor
    · refine ⟨Nat.fib (q+1),hp1,hle,?_⟩
      change Int.fract ((Nat.fib (q+1) : ℝ)*goldenMechanicalSlope)<_
      rw [golden_slope_fract_eq,fract_fib_odd _ he.add_one]
      exact h1
    · refine ⟨Nat.fib (q+2),hp2,le_rfl,?_⟩
      rw [backward_displacement_eq_one_sub_forward golden_mechanical_slope_irrational hp2]
      change 1-Int.fract ((Nat.fib (q+2) : ℝ)*goldenMechanicalSlope)<_
      rw [golden_slope_fract_eq,fract_fib_even _ (by simpa [Nat.add_assoc] using he.add_one.add_one)]
      linarith
  · constructor
    · refine ⟨Nat.fib (q+2),hp2,le_rfl,?_⟩
      change Int.fract ((Nat.fib (q+2) : ℝ)*goldenMechanicalSlope)<_
      rw [golden_slope_fract_eq,fract_fib_odd _ (by simpa [Nat.add_assoc] using ho.add_one.add_one)]
      exact h2
    · refine ⟨Nat.fib (q+1),hp1,hle,?_⟩
      rw [backward_displacement_eq_one_sub_forward golden_mechanical_slope_irrational hp1]
      change 1-Int.fract ((Nat.fib (q+1) : ℝ)*goldenMechanicalSlope)<_
      rw [golden_slope_fract_eq,fract_fib_even _ ho.add_one]
      linarith

private theorem golden_occurrence_gap_le_fib (q n : ℕ) (hq : 3 ≤ q) (hn : 0 < n)
    (hNF : n+1 ≤ Nat.fib (q+1)) {w : List Bool} (hw : w ∈ goldenFactorSet n)
    {d : ℕ} (hd : d ∈ goldenOccurrenceGapSet n w) : d ≤ Nat.fib (q+2) := by
  obtain ⟨i,hi⟩ := mem_goldenFactorSet.mp hw
  have hphase : goldenPhase i ∈ Set.Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  rw [← iUnion_rotation_gap_arc goldenMechanicalSlope (n+1)] at hphase
  obtain ⟨r,hr⟩ := Set.mem_iUnion.mp hphase
  have hrank := (golden_cylinder_rank_iff_mem_rotation_gap_arc n i r).mpr hr
  rw [golden_occurrence_gap_set_eq_rank_first_return_gap_set hi.symm,hrank,
    ← golden_arc_first_return_gap_set_eq_rank_first_return_gap_set n r] at hd
  have hlen := golden_arc_length_lower q n hq hn hNF r
  have hc := golden_small_displacement_candidates q hq
  apply arc_gap_le_of_candidates n hn r (Nat.fib (q+2)) ?_ ?_ hd
  · obtain ⟨p,hp,hpM,hpl⟩ := hc.1
    exact ⟨p,hp,hpM,hpl.trans_le hlen⟩
  · obtain ⟨p,hp,hpM,hpl⟩ := hc.2
    exact ⟨p,hp,hpM,hpl.trans_le hlen⟩

private theorem golden_bound_of_gap_max (n M : ℕ) (hn : 0 < n)
    (hgap : ∀ w, w ∈ goldenFactorSet n → ∀ d, d ∈ goldenOccurrenceGapSet n w → d ≤ M) :
    HasRecurrenceBound goldenWord n (n+M) := by
  classical
  rintro w ⟨a, rfl⟩
  rintro x ⟨i, rfl⟩
  have hx : goldenFactor n i ∈ goldenFactorSet n := mem_goldenFactorSet.mpr ⟨i,rfl⟩
  have hw : goldenFactor (n+M) a ∈ goldenFactorSet (n+M) := mem_goldenFactorSet.mpr ⟨a,rfl⟩
  obtain ⟨b,hb,_,heq⟩ := golden_factor_uniformly_recurrent hw (i+1)
  have hex : ∃ r, b ≤ r ∧ goldenFactor n r=goldenFactor n i := by
    obtain ⟨r,hr,he⟩ := golden_factor_recurrent hx b
    exact ⟨r,hr.le,he.symm⟩
  let r := Nat.find hex
  have hr := Nat.find_spec hex
  let S := (Finset.range r).filter (fun z => goldenFactor n z=goldenFactor n i)
  have hiS : i ∈ S := by apply Finset.mem_filter.mpr; exact ⟨Finset.mem_range.mpr (by omega),rfl⟩
  have hSne : S.Nonempty := ⟨i,hiS⟩
  let l := S.max' hSne
  have hlS : l ∈ S := Finset.max'_mem S hSne
  have hl : l < r ∧ goldenFactor n l=goldenFactor n i := by simpa only [S,Finset.mem_filter,Finset.mem_range] using hlS
  have hlb : l < b := by
    by_contra h
    have hminimal := Nat.find_min hex hl.1
    exact hminimal ⟨by omega,hl.2⟩
  have hadj : AdjacentGoldenOccurrences n (goldenFactor n i) l r := by
    apply (D5.S1.Words.adjacent_golden_occurrences_iff).mpr
    refine ⟨hl.1,hl.2,hr.2,Finset.filter_eq_empty_iff.mpr ?_⟩
    intro z hz hzf
    have hzS : z ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Finset.mem_Ioo.mp hz).2,hzf⟩
    have hzl : z ≤ l := Finset.le_max' S z hzS
    exact (not_lt_of_ge hzl) (Finset.mem_Ioo.mp hz).1
  have hbound := hgap _ hx (r-l) ⟨l,r,hadj,rfl⟩
  have hc : List.IsInfix ((rayPrefix (fun index => goldenWord (i + index)) n)) ((rayPrefix (fun index => goldenWord (b + index)) (n+M))) := by
    rw [contains_block_iff]
    refine ⟨r-b,by omega,?_⟩
    intro j hj
    have he := congrArg (fun z : List Bool => z[j]?) hr.2
    simp only [goldenFactor,List.getElem?_ofFn,hj,↓reduceDIte,Option.some.injEq] at he
    have hh : b+(r-b+j)=r+j := by omega
    rw [hh]
    exact he.symm
  have heq' : (rayPrefix (fun index => goldenWord (a + index)) (n+M))=(rayPrefix (fun index => goldenWord (b + index)) (n+M)) := heq
  change ∃ t : ℕ, t + (rayPrefix (fun index => goldenWord (i + index)) n).length ≤
    (rayPrefix (fun index => goldenWord (a + index)) (n+M)).length ∧
      ∀ j : Fin (rayPrefix (fun index => goldenWord (i + index)) n).length,
        (rayPrefix (fun index => goldenWord (i + index)) n).getD j.1 false =
          (rayPrefix (fun index => goldenWord (a + index)) (n+M)).getD (t+j.1) false
  rw [heq']
  obtain ⟨t, ht, he⟩ := (contains_block_iff _ _ _ _ _ _).mp hc
  refine ⟨t, by simpa only [rayPrefix, List.length_ofFn] using ht, ?_⟩
  intro j
  have hj : j.1 < n := by simpa only [rayPrefix, List.length_ofFn] using j.2
  simpa only [rayPrefix, List.getD_eq_getElem, List.length_ofFn, hj,
    show t+j.1 < n+M by omega, List.getElem_ofFn] using he j.1 hj

private theorem golden_recurrence_bound_fib (q n : ℕ) (hq : 3 ≤ q) (hn : 0 < n)
    (hNF : n+1 ≤ Nat.fib (q+1)) :
    HasRecurrenceBound goldenWord n (n+Nat.fib (q+2)) := by
  apply golden_bound_of_gap_max n _ hn
  intro w hw d hd
  exact golden_occurrence_gap_le_fib q n hq hn hNF hw hd

private theorem fib_recurrence_upper_tendsto :
    Tendsto (fun q : ℕ => (1 : ℝ)+(Nat.fib (q+2) : ℝ)/(Nat.fib q : ℝ))
      atTop (𝓝 (2+Real.goldenRatio)) := by
  have ht := tendsto_fib_succ_div_fib_atTop.const_add (2 : ℝ)
  have heq : (fun q : ℕ => (2 : ℝ)+(Nat.fib (q+1) : ℝ)/(Nat.fib q : ℝ)) =ᶠ[atTop]
      (fun q : ℕ => (1 : ℝ)+(Nat.fib (q+2) : ℝ)/(Nat.fib q : ℝ)) := by
    filter_upwards [eventually_ge_atTop 2] with q hq
    have hp : (Nat.fib q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ((Nat.fib_pos.mpr (by omega)).ne')
    rw [@Nat.fib_add_two q,Nat.cast_add,add_div,div_self hp]
    ring
  exact ht.congr' heq

private theorem greatestFib_tendsto : Tendsto Nat.greatestFib atTop atTop := by
  apply tendsto_atTop.2
  intro q
  exact eventually_atTop.2 ⟨Nat.fib q,fun n hn => Nat.le_greatestFib.mpr hn⟩

private theorem golden_recurrence_ratio_le_fib (n : ℕ) (hn : 2 ≤ n) :
    recurrenceRatio goldenWord n ≤ ENNReal.ofReal
      ((1 : ℝ)+(Nat.fib (Nat.greatestFib n+2) : ℝ)/(Nat.fib (Nat.greatestFib n) : ℝ)) := by
  let q := Nat.greatestFib n
  have hq : 3 ≤ q := by
    apply Nat.le_greatestFib.mpr
    simpa [Nat.fib] using hn
  have hn0 : 0 < n := by omega
  have hq0 : 0 < Nat.fib q := Nat.fib_pos.mpr (by omega)
  have hN : n+1 ≤ Nat.fib (q+1) := Nat.lt_fib_greatestFib_add_one n
  have hbound := golden_recurrence_bound_fib q n hq hn0 hN
  have hR : recurrenceFunction goldenWord n ≤ ((n+Nat.fib (q+2) : ℕ) : ℕ∞) :=
    sInf_le ⟨n+Nat.fib (q+2),rfl,hbound⟩
  have hval := ENat.toENNReal_mono hR
  have hval' : (fun r : ℕ∞ => (r : ℝ≥0∞)) (recurrenceFunction goldenWord n) ≤ ((n+Nat.fib (q+2) : ℕ) : ℝ≥0∞) := by
    simpa only [ENat.toENNReal_coe] using hval
  rw [recurrenceRatio,if_neg hn0.ne']
  calc
    (fun r : ℕ∞ => (r : ℝ≥0∞)) (recurrenceFunction goldenWord n)/(n : ℝ≥0∞) ≤
        ((n+Nat.fib (q+2) : ℕ) : ℝ≥0∞)/(n : ℝ≥0∞) := ENNReal.div_le_div_right hval' _
    _ = ENNReal.ofReal (((n+Nat.fib (q+2) : ℕ) : ℝ)/(n : ℝ)) := by
      rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos'.mpr hn0),ENNReal.ofReal_natCast,ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((1 : ℝ)+(Nat.fib (q+2) : ℝ)/(Nat.fib q : ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [Nat.cast_add,add_div,div_self (Nat.cast_ne_zero.mpr hn0.ne')]
      have hden : (Nat.fib q : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.fib_greatestFib_le n
      have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg (Nat.fib (q+2))) (Nat.cast_pos'.mpr hq0) hden
      linarith

private theorem golden_rhoStar_le_sharp :
    rhoStar goldenWord ≤ ENNReal.ofReal (2+Real.goldenRatio) := by
  have ht := ENNReal.tendsto_ofReal (fib_recurrence_upper_tendsto.comp greatestFib_tendsto)
  have hh : Filter.limsup (recurrenceRatio goldenWord) atTop ≤
      Filter.limsup (fun n => ENNReal.ofReal
        ((1 : ℝ)+(Nat.fib (Nat.greatestFib n+2) : ℝ)/(Nat.fib (Nat.greatestFib n) : ℝ))) atTop := by
    apply Filter.limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact golden_recurrence_ratio_le_fib n hn
  rw [rhoStar_eq_limsup]
  exact hh.trans_eq ht.limsup_eq

theorem golden_rhoStar_eq_sharp :
    rhoStar goldenWord = ENNReal.ofReal (2+Real.goldenRatio) :=
  le_antisymm golden_rhoStar_le_sharp golden_rhoStar_ge_sharp

end D5.S1.Words.ReturnWords.CassaigneGoldenRecurrence
