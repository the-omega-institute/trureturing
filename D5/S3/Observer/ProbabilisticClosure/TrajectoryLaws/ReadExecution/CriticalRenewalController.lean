/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalController
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalController
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The counted renewal controller uses the actual block history and its paid bit clock. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalOneGap
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalPayment
import Mathlib.Probability.ConditionalExpectation

/-! Complete block histories and the literal counted bit execution. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalController
open CriticalRenewalTable CriticalRenewalPaths CriticalRenewalFreshBlocks
open CriticalRenewalOneGap
open D5.S3.Estimation.SequentialDecisionRisk.CriticalRenewalStoppedDrift

abbrev Sample := ℕ × (ℕ → Block)

/-- The initial wait and the first n complete gap and coin blocks. -/
def history (n : ℕ) (ω : Sample) : ℕ × (Fin n → Block) :=
  (ω.1, fun k => ω.2 k)

private lemma measurable_history (n : ℕ) : Measurable (history n) := by
  exact measurable_fst.prodMk (measurable_pi_iff.mpr fun k =>
    (measurable_pi_apply k.val).comp measurable_snd)

/-- The proof filtration retains full past blocks, including their coin traces. -/
def filtration : Filtration ℕ (inferInstance : MeasurableSpace Sample) where
  seq n := MeasurableSpace.comap (history n) inferInstance
  mono' := by
    intro n m hnm s hs
    obtain ⟨t, ht, rfl⟩ := hs
    let R : (ℕ × (Fin m → Block)) → ℕ × (Fin n → Block) :=
      fun v => (v.1,fun k => v.2 ⟨k,lt_of_lt_of_le k.isLt hnm⟩)
    exact ⟨R ⁻¹' t, (by fun_prop : Measurable R) ht, rfl⟩
  le' n := (measurable_history n).comap_le

private lemma next_block_independent {J : ℕ} (w f : PMF ℕ) (t : Tick J) (n : ℕ) :
    IndepFun (fun ω : Sample => ω.2 n) (history n) (sourceLaw w f t) := by
  let ν := Measure.infinitePi (fun _ : ℕ => (blockLaw f t).toMeasure)
  let R : (ℕ → Block) → (Fin n → Block) := fun bs k => bs k
  let X : (ℕ → Block) → Block := fun bs => bs n
  have hR : Measurable R := by fun_prop
  have hX : Measurable X := measurable_pi_apply n
  have hi := (iIndepFun_infinitePi (P := fun _ : ℕ => (blockLaw f t).toMeasure)
    (X := fun _ b => b) (fun _ => measurable_id)).indepFun_finset
      (range n) {n} (by simp) (fun k => measurable_pi_apply k)
  have hi' : IndepFun R X ν := by
    exact hi.comp (measurable_pi_iff.mpr fun k : Fin n =>
      measurable_pi_apply (⟨k,mem_range.mpr k.isLt⟩ : range n))
      (measurable_pi_apply (⟨n,mem_singleton_self n⟩ : ({n} : Finset ℕ)))
  have hjoint : (sourceLaw w f t).map (fun ω => (history n ω,ω.2 n)) =
      (w.toMeasure.prod (ν.map R)).prod (ν.map X) := by
    have he : (fun ω : Sample => (history n ω,ω.2 n)) =
        MeasurableEquiv.prodAssoc.symm ∘ Prod.map id (fun bs => (R bs,X bs)) := rfl
    rw [he, ← Measure.map_map (MeasurableEquiv.measurable _)
      (measurable_id.prodMap (hR.prodMk hX))]
    change ((w.toMeasure.prod ν).map (Prod.map id (fun bs => (R bs,X bs)))).map _ = _
    rw [← Measure.map_prod_map _ _ measurable_id (hR.prodMk hX), Measure.map_id,
      hi'.map_prod_eq_prod_map_map hR.aemeasurable hX.aemeasurable,
      ← Measure.prodAssoc_prod, MeasurableEquiv.map_symm_map]
  have hm : (sourceLaw w f t).map (history n) = w.toMeasure.prod (ν.map R) := by
    change (w.toMeasure.prod ν).map (Prod.map id R) = _
    rw [← Measure.map_prod_map _ _ measurable_id hR, Measure.map_id]
  have hx : (sourceLaw w f t).map (fun ω : Sample => ω.2 n) = ν.map X := by
    change (w.toMeasure.prod ν).map (X ∘ Prod.snd) = _
    rw [← Measure.map_map hX measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul]
  apply IndepFun.symm
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_history n).aemeasurable (by fun_prop)).mpr
  rw [hjoint,hm,hx]

private lemma next_block_conditional {J : ℕ} (w f : PMF ℕ) (t : Tick J)
    (n : ℕ) (a : Block → ℝ) :
    (sourceLaw w f t)[fun ω : Sample => a (ω.2 n) | filtration n] =ᵐ[sourceLaw w f t]
      fun _ => ∫ b, a b ∂(blockLaw f t).toMeasure := by
  have ha : Measurable a := measurable_of_countable _
  have hi := (next_block_independent w f t n).comp ha measurable_id
  have hma : Measurable (fun ω : Sample => a (ω.2 n)) := by fun_prop
  have hc := condExp_indep_eq hma.comap_le (filtration.le n)
    (comap_measurable (fun ω : Sample => a (ω.2 n))).stronglyMeasurable hi
  have hlaw : (sourceLaw w f t).map (fun ω : Sample => ω.2 n) =
      (blockLaw f t).toMeasure := by
    change (w.toMeasure.prod (Measure.infinitePi fun _ : ℕ => (blockLaw f t).toMeasure)).map
      ((fun bs : ℕ → Block => bs n) ∘ Prod.snd) = _
    rw [← Measure.map_map (measurable_pi_apply n) measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]
  have he : (∫ ω : Sample, a (ω.2 n) ∂sourceLaw w f t) =
      ∫ b, a b ∂(blockLaw f t).toMeasure := by
    rw [← hlaw, integral_map (by fun_prop) ha.aestronglyMeasurable]
  simpa only [he] using hc

private lemma score_adapted {J : ℕ} (δ : ℝ) (t : Tick J) :
    StronglyAdapted filtration (fun n (ω : Sample) => score δ t ω.2 n) := by
  intro n
  let F : (ℕ × (Fin n → Block)) → ℝ := fun v =>
    ∑ k : Fin n, (increment t (v.2 k) : ℝ) * δ
  have hF : Measurable F := measurable_of_countable _
  have he : (fun ω : Sample => score δ t ω.2 n) = F ∘ history n := by
    funext ω
    change (∑ k ∈ range n, (increment t (ω.2 k) : ℝ)*δ) =
      ∑ k : Fin n, (increment t (ω.2 k) : ℝ)*δ
    exact (Fin.sum_univ_eq_sum_range (fun k => (increment t (ω.2 k) : ℝ)*δ) n).symm
  change StronglyMeasurable[filtration n] (fun ω : Sample => score δ t ω.2 n)
  rw [he]
  exact (hF.comp (comap_measurable _)).stronglyMeasurable

private lemma score_step {J : ℕ} (δ : ℝ) (t : Tick J) (n : ℕ) (ω : Sample) :
    score δ t ω.2 (n+1) - score δ t ω.2 n = (increment t (ω.2 n) : ℝ)*δ := by
  simp [score,sum_range_succ]

private lemma conditional_pair {J : ℕ} (w f : PMF ℕ) (t : Tick J)
    (n : ℕ) (a : ℕ × ℤ → ℝ) :
    (sourceLaw w f t)[fun ω : Sample =>
      a ((ω.2 n).zeros.length,increment t (ω.2 n)) | filtration n]
      =ᵐ[sourceLaw w f t] fun _ => ∫ ku, a ku ∂(pairLaw f t).toMeasure := by
  have h := next_block_conditional w f t n
    (fun b => a (b.zeros.length,increment t b))
  have he : (∫ b, a (b.zeros.length,increment t b) ∂(blockLaw f t).toMeasure) =
      ∫ ku, a ku ∂(pairLaw f t).toMeasure := by
    rw [← block_pair_law f t, ← PMF.toMeasure_map _ _ (measurable_of_countable _),
      integral_map (by fun_prop) (measurable_of_countable a).aestronglyMeasurable]
  simpa only [he] using h

private lemma score_evidence {J : ℕ} (δ : ℝ) (t : Tick J)
    (bs : ℕ → Block) (n : ℕ) :
    score δ t bs n = (evidence t bs n : ℝ)*δ := by
  simp only [score,evidence,Int.cast_sum,Finset.sum_mul]

private lemma outside_score {H J : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (t : Tick J) (bs : ℕ → Block) (n : ℕ) :
    ¬ inside H (evidence t bs n) ↔ (H : ℝ)*δ ≤ |score δ t bs n| := by
  rw [score_evidence,abs_mul,abs_of_pos hδ,
    mul_le_mul_iff_left₀ hδ,le_abs]
  simp only [inside,not_and_or,not_lt]
  constructor
  · rintro (h | h)
    · right
      have hh : (evidence t bs n : ℝ) ≤ -(H : ℝ) := by exact_mod_cast h
      linarith
    · left
      exact_mod_cast h
  · rintro (h | h)
    · right
      exact_mod_cast h
    · left
      have hh : (evidence t bs n : ℝ) ≤ -(H : ℝ) := by linarith
      exact_mod_cast hh

private lemma exit_eq_gapStop {H J : ℕ} (hH : 0 < H) (δ : ℝ) (hδ : 0 < δ)
    (t : Tick J) (ω : Sample) :
    exitTime (fun n (ω : Sample) => score δ t ω.2 n) ((H : ℝ)*δ) ω =
      gapStop H t ω.2 := by
  have hcond (n : ℕ) :
      (1 ≤ n ∧ (H : ℝ)*δ ≤ |score δ t ω.2 n|) ↔
        ¬ inside H (evidence t ω.2 n) := by
    rw [← outside_score δ hδ]
    constructor
    · exact And.right
    · intro h
      refine ⟨?_,h⟩
      by_contra hn
      have hn0 : n = 0 := by omega
      subst n
      simp [inside,evidence] at h
      omega
  unfold exitTime hittingAfter gapStop
  simp only [Set.mem_ofPred_eq,hcond]
  split_ifs with h
  · congr 1
    rw [Nat.sInf_def (s := {j | ¬ inside H (evidence t ω.2 j)}) h]
    congr 1
  · rfl

private lemma score_conditional_mean {J : ℕ} (w f : PMF ℕ) (δ : ℝ) (t : Tick J)
    (n : ℕ) :
    (sourceLaw w f t)[fun ω : Sample =>
      score δ t ω.2 (n+1)-score δ t ω.2 n | filtration n]
      =ᵐ[sourceLaw w f t] fun _ =>
        ∫ ku : ℕ × ℤ, (ku.2 : ℝ)*δ ∂(pairLaw f t).toMeasure := by
  simpa only [score_step] using conditional_pair w f t n
    (fun ku : ℕ × ℤ => (ku.2 : ℝ)*δ)

private lemma score_conditional_second {J : ℕ} (w f : PMF ℕ) (δ : ℝ) (t : Tick J)
    (n : ℕ) :
    (sourceLaw w f t)[fun ω : Sample =>
      (score δ t ω.2 (n+1)-score δ t ω.2 n)^2 | filtration n]
      =ᵐ[sourceLaw w f t] fun _ =>
        ∫ ku : ℕ × ℤ, ((ku.2 : ℝ)*δ)^2 ∂(pairLaw f t).toMeasure := by
  simpa only [score_step] using conditional_pair w f t n
    (fun ku : ℕ × ℤ => ((ku.2 : ℝ)*δ)^2)

private lemma finite_gap_path {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (ω : Sample) (hf : gapStop H t ω.2 ≠ ⊤) :
    let g := (gapStop H t ω.2).toNat
    gapStop H t ω.2 = (g : ℕ∞) ∧
    paidStop hH t ω.1 ω.2 = (clock ω.1 ω.2 g : ℕ∞) ∧
    run hH t ω.1 ω.2 (clock ω.1 ω.2 g) = target H J (evidence t ω.2 g) ∧
    (run hH t ω.1 ω.2 (clock ω.1 ω.2 g) = label true ↔
      (H : ℤ) ≤ evidence t ω.2 g) ∧
    (run hH t ω.1 ω.2 (clock ω.1 ω.2 g) = label false ↔
      evidence t ω.2 g ≤ -(H : ℤ)) := by
  have hex : ∃ n, ¬ inside H (evidence t ω.2 n) := by
    by_contra hn
    simp [gapStop,hn] at hf
  have hprev : ∀ n < Nat.find hex, inside H (evidence t ω.2 n) := by
    intro n hn
    exact not_not.mp (Nat.find_min hex hn)
  have hp := stopped_prefix_payment hH t ω.1 ω.2 (Nat.find hex)
    (Nat.find_spec hex) hprev
  have hg : (gapStop H t ω.2).toNat = Nat.find hex := by rw [hp.1]; simp
  dsimp only
  rw [hg]
  refine ⟨hp.1,?_,hp.2.2.1,hp.2.2.2.2.2.2.1,hp.2.2.2.2.2.2.2.1⟩
  simpa only [clock,Nat.add_comm 1 ω.1] using hp.2.1

private lemma finite_projection (n : ℕ∞) (hn : n ≠ ⊤) : n.untopA = n.toNat := by
  obtain ⟨m,hm⟩ := ENat.ne_top_iff_exists.mp hn
  rw [← hm]
  simp

private lemma actual_run_bounds {J : ℕ} (w f : Bool → PMF ℕ) (t : Tick J)
    (δ D V I Δ α : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1/2)
    (hD : 0 < D) (hV : 0 < V) (hI : 0 < I) (hΔ : D*I ≤ Δ)
    (hα : 0 < α) (hαhalf : α < 1 / 2)
    (hstep : ∀ z b, |(t.increment z b : ℝ)*δ| ≤ 1)
    (hmean : ∀ i : Bool,
      (∫ ku : ℕ × ℤ, (ku.2 : ℝ)*δ ∂(pairLaw (f i) t).toMeasure) =
        (if i then (1 : ℝ) else -1)*Δ/2)
    (hsecond : ∀ i : Bool,
      (∫ ku : ℕ × ℤ, ((ku.2 : ℝ)*δ)^2 ∂(pairLaw (f i) t).toMeasure) ≤ V*I) :
    let lam := min 1 (D/(2*Real.exp 1*V))
    let A := Real.log (1/α)/lam
    let H := ⌈A/δ⌉₊
    ∃ hH : 0 < H, ∀ i : Bool,
      let μ := sourceLaw (w i) (f i) t
      (∀ᵐ ω ∂μ, gapStop H t ω.2 ≠ ⊤) ∧
      Integrable (fun ω : Sample => ((gapStop H t ω.2).toNat : ℝ)) μ ∧
      (∫ ω : Sample, ((gapStop H t ω.2).toNat : ℝ) ∂μ) ≤ 2*(A+3/2)/Δ ∧
      μ.real {ω : Sample |
        run hH t ω.1 ω.2 (paidStop hH t ω.1 ω.2).toNat = label (!i)} ≤ α := by
  intro lam A H
  have hlam : 0 < lam := lt_min zero_lt_one (div_pos hD (by positivity))
  have hA : 0 < A := div_pos
    (Real.log_pos ((one_lt_div hα).mpr (by linarith))) hlam
  have hH : 0 < H := Nat.ceil_pos.mpr (div_pos hA hδ)
  have hceil : (H : ℝ) = (⌈A/δ⌉ : ℝ) :=
    natCast_ceil_eq_intCast_ceil (div_nonneg hA.le hδ.le)
  let S : ℕ → Sample → ℝ := fun n ω => score δ t ω.2 n
  let μ : Bool → Measure Sample := fun i => sourceLaw (w i) (f i) t
  have hSm : StronglyAdapted filtration S := score_adapted δ t
  have hS0 : ∀ ω, S 0 ω = 0 := fun ω => by simp [S,score]
  have hSstep : ∀ n ω, |S (n+1) ω-S n ω| ≤ 1 := by
    intro n ω
    rw [show S (n+1) ω-S n ω = (increment t (ω.2 n) : ℝ)*δ from score_step δ t n ω]
    exact hstep _ _
  have hcm : ∀ (i : Bool) n,
      (μ i)[fun ω => S (n+1) ω-S n ω | filtration n] =ᵐ[μ i]
        fun _ => (if i then (1 : ℝ) else -1)*Δ/2 := by
    intro i n
    simpa only [hmean i] using score_conditional_mean (w i) (f i) δ t n
  have hcs : ∀ (i : Bool) n,
      (μ i)[fun ω => (S (n+1) ω-S n ω)^2 | filtration n] ≤ᵐ[μ i]
        fun _ => V*I := by
    intro i n
    filter_upwards [score_conditional_second (w i) (f i) δ t n] with ω hω
    exact hω.le.trans (hsecond i)
  have hd := critical_renewal_stopping_risks hSm hS0 hSstep hD hV hI hΔ
    hα hαhalf hδ hδhalf hcm hcs
  change (∀ n ω, _ ∧ _) ∧ ∀ i : Bool, _ at hd
  have he (ω : Sample) : exitTime S ((⌈A/δ⌉ : ℝ)*δ) ω = gapStop H t ω.2 := by
    rw [← hceil]
    exact exit_eq_gapStop hH δ hδ t ω
  refine ⟨hH,?_⟩
  intro i
  obtain ⟨hpred,hid,hfinite,hint,hEG,hexpb,hexpl,hrisk,hriskα⟩ := hd.2 i
  change (∀ᵐ ω ∂μ i, exitTime S ((⌈A/δ⌉ : ℝ)*δ) ω ≠ ⊤) at hfinite
  have hf : ∀ᵐ ω ∂μ i, gapStop H t ω.2 ≠ ⊤ := by
    filter_upwards [hfinite] with ω hω
    rw [he] at hω
    exact hω
  have hproj : (fun ω => ((exitTime S ((⌈A/δ⌉ : ℝ)*δ) ω).untopA : ℝ))
      =ᵐ[μ i] fun ω : Sample => ((gapStop H t ω.2).toNat : ℝ) := by
    filter_upwards [hf] with ω hω
    rw [he,finite_projection _ hω]
  refine ⟨hf,hint.congr hproj,?_,?_⟩
  · rw [← integral_congr_ae hproj]
    exact hEG
  · have hsub : ∀ᵐ ω ∂μ i,
        (run hH t ω.1 ω.2 (paidStop hH t ω.1 ω.2).toNat = label (!i)) →
          (if i then (1 : ℝ) else -1)*stoppedValue S
            (exitTime S ((⌈A/δ⌉ : ℝ)*δ)) ω ≤ -(⌈A/δ⌉ : ℝ)*δ := by
      filter_upwards [hf] with ω hω
      intro hw
      have hp := finite_gap_path hH t ω hω
      have hv : stoppedValue S (exitTime S ((⌈A/δ⌉ : ℝ)*δ)) ω =
          (evidence t ω.2 (gapStop H t ω.2).toNat : ℝ)*δ := by
        change S (exitTime S ((⌈A/δ⌉ : ℝ)*δ) ω).untopA ω = _
        rw [he,finite_projection _ hω]
        exact score_evidence δ t ω.2 _
      rw [hp.2.1,ENat.toNat_natCast] at hw
      rw [hv,← hceil]
      cases i
      · have hh := hp.2.2.2.1.mp hw
        have hh' : (H : ℝ) ≤ (evidence t ω.2 (gapStop H t ω.2).toNat : ℝ) := by
          exact_mod_cast hh
        simp only [Bool.false_eq_true,↓reduceIte]
        nlinarith
      · have hh := hp.2.2.2.2.mp hw
        have hh' : (evidence t ω.2 (gapStop H t ω.2).toNat : ℝ) ≤ -(H : ℝ) := by
          exact_mod_cast hh
        simp only [↓reduceIte,one_mul]
        nlinarith
    apply (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans
    convert hrisk.trans hriskα using 1 <;> dsimp [A,lam,Measure.real] <;> congr 2 <;>
      ext ω <;> simp only [Set.mem_ofPred_eq,neg_mul] <;> rfl

private lemma full_count_bound (r J : ℕ) (hr : 1 ≤ r) (hJ : 1 ≤ J)
    (A : ℝ) (hA : 0 < A) :
    let H := ⌈A/grid r J⌉₊
    (Fintype.card (State H J) : ℝ) ≤ (4*A+4)*(2 : ℝ)^(r*J) := by
  intro H
  let L : ℝ := (2 : ℝ)^(r*J)
  have hL : 0 < L := by positivity
  have hj : 0 < (J : ℝ) := by exact_mod_cast (show 0 < J by omega)
  have hd : 0 < grid r J := div_pos hj hL
  have hH : 0 < H := Nat.ceil_pos.mpr (div_pos hA hd)
  have hJtwo : 2*(J : ℝ) ≤ L := by
    have hh : (2 : ℝ)*(J : ℝ) ≤ (2 : ℝ)^J := by
      exact_mod_cast Nat.mul_le_pow (a := 2) (by decide) J
    exact hh.trans (pow_le_pow_right₀ (by norm_num)
      (Nat.le_mul_of_pos_left J (by omega)))
  have hjone : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJone : (J : ℝ)+1 ≤ 2*(J : ℝ) := by linarith
  have hJpower : (J : ℝ)+1 ≤ L := hJone.trans hJtwo
  have hLone : 1 ≤ L := by linarith
  have hh : (H : ℝ) ≤ A*L/(J : ℝ)+1 := by
    have hh := (Nat.ceil_lt_add_one (div_nonneg hA.le hd.le)).le
    change (H : ℝ) ≤ A/grid r J+1 at hh
    convert hh using 1 <;> dsimp [grid,L] <;> field_simp
  have hratio : ((J : ℝ)+1)/(J : ℝ) ≤ 2 :=
    (div_le_iff₀ hj).mpr (by linarith)
  have hpart : 2*A*L*(((J : ℝ)+1)/(J : ℝ)) ≤ 4*A*L := by
    have hh := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 2*A*L)
    nlinarith only [hh]
  rw [full_state_count H J hH, Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub (by omega : 1 ≤ 2*H), Nat.cast_mul]
  push_cast
  calc
    3+(2*(H : ℝ)-1)*((J : ℝ)+1) ≤
        3+(2*(A*L/(J : ℝ)+1)-1)*((J : ℝ)+1) := by
      nlinarith [mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (J : ℝ)+1)]
    _ = 3+2*A*L*(((J : ℝ)+1)/(J : ℝ))+((J : ℝ)+1) := by ring
    _ ≤ 3+4*A*L+L := by linarith
    _ ≤ (4*A+4)*L := by nlinarith

private lemma scale_information_le_one (r J : ℕ) (hr : 1 ≤ r)
    (s eta : ℝ) (hs : 0 < s) (hsone : s < 1) (heta : eta < 1)
    (hscale : s * (2 : ℝ) ^ J ≤ eta) : s^(2*r)*(J : ℝ) ≤ 1 := by
  have hJpow : (J : ℝ) ≤ (2 : ℝ)^(r*J) := by
    have hlin : 2*(J : ℝ) ≤ (2 : ℝ)^J := by
      exact_mod_cast Nat.mul_le_pow (a := 2) (by decide) J
    have hh : (2 : ℝ)^J ≤ (2 : ℝ)^(r*J) := pow_le_pow_right₀ (by norm_num)
      (Nat.le_mul_of_pos_left J (by omega : 0 < r))
    linarith
  have hp1 : s^r ≤ 1 := pow_le_one₀ hs.le hsone.le
  have hp2 : (s*(2 : ℝ)^J)^r ≤ 1 :=
    pow_le_one₀ (by positivity) (hscale.trans heta.le)
  calc
    s^(2*r)*(J : ℝ) ≤ s^(2*r)*(2 : ℝ)^(r*J) :=
      mul_le_mul_of_nonneg_left hJpow (by positivity)
    _ = s^r*(s*(2 : ℝ)^J)^r := by
      rw [mul_pow,← mul_assoc,← pow_add,← pow_mul,
        show r+r = 2*r by omega,Nat.mul_comm J r]
    _ ≤ 1 := (mul_le_mul_of_nonneg_left hp2 (by positivity)).trans (by simpa using hp1)

set_option maxHeartbeats 1200000 in
-- The source constants and actual-law conclusions have a dependent telescope.
/-- One common literal table, with all constants fixed before every admissible cap,
    has both risks, both finite paid means, exact gap payment and the full state bound. -/
theorem uniform_counted_controller (r : ℕ) (hr : 1 ≤ r) (c : ℝ) (hc : 0 < c)
    (α : ℝ) (hα : 0 < α) (hαhalf : α < 1 / 2) :
    ∃ eta s0 D V C : ℝ,
      0 < eta ∧ eta < 1 ∧ 0 < s0 ∧ s0 < 1 ∧ 0 < D ∧ 0 < V ∧ 0 < C ∧
      let lam := min 1 (D/(2*Real.exp 1*V))
      let A := Real.log (1/α)/lam
      let K := 4*A+4
      ∀ (s : ℝ) (hs : 0 < s), s < s0 → ∀ J : ℕ, 1 ≤ J →
        s * (2 : ℝ) ^ J ≤ eta →
        let f := fun i => CriticalRenewalSource.gapLaw r hr c hc i s hs
        let w := fun i => CriticalRenewalSource.waitLaw r hr c hc i s hs
        let m := fun i => rewardMean r J (f i)
        let theta := (m false+m true)/2
        let Delta := m true-m false
        let delta := grid r J
        let t := roundedTick (reward r J) theta delta
        let H := ⌈A/delta⌉₊
        ∃ hH : 0 < H,
          Fintype.card (State H J) = 3+(2*H-1)*(J+1) ∧
          (Fintype.card (State H J) : ℝ) ≤ K*(2 : ℝ)^(r*J) ∧
          (∀ (bs : ℕ → Block) n,
            (evidence t bs n : ℝ) = score delta t bs n/delta) ∧
          ∀ i : Bool,
            let μ := sourceLaw (w i) (f i) t
            μ.real {ω : Sample |
              run hH t ω.1 ω.2 (paidStop hH t ω.1 ω.2).toNat = label (!i)} ≤ α ∧
            (∀ᵐ ω ∂μ, gapStop H t ω.2 ≠ ⊤) ∧
            (∀ᵐ ω ∂μ, paidStop hH t ω.1 ω.2 ≠ ⊤) ∧
            Integrable (fun ω : Sample => ((gapStop H t ω.2).toNat : ℝ)) μ ∧
            Integrable (fun ω : Sample => ((paidStop hH t ω.1 ω.2).toNat : ℝ)) μ ∧
            (∫ ω : Sample, ((gapStop H t ω.2).toNat : ℝ) ∂μ) ≤
              2*(A+3/2)/Delta ∧
            (∫ ω : Sample, ((paidStop hH t ω.1 ω.2).toNat : ℝ) ∂μ) =
              1+CriticalRenewalSource.beta r c i s+CriticalRenewalSource.mean r c i s*
                ∫ ω : Sample, ((gapStop H t ω.2).toNat : ℝ) ∂μ ∧
            (∫ ω : Sample, ((paidStop hH t ω.1 ω.2).toNat : ℝ) ∂μ) ≤
              C/(s^(2*r+1)*(J : ℝ)) ∧
            (∀ᵐ ω ∂μ,
              paidStop hH t ω.1 ω.2 =
                ((1+ω.1+∑ n ∈ range (gapStop H t ω.2).toNat,
                  ((ω.2 n).zeros.length+1) : ℕ) : ℕ∞) ∧
              run hH t ω.1 ω.2 (paidStop hH t ω.1 ω.2).toNat =
                target H J (evidence t ω.2 (gapStop H t ω.2).toNat)) := by
  obtain ⟨eta,sB,D,Dhi,Cmean,Csecond,V,heta,heta1,hsB,hsB1,
    hD,hDhi,hCm,hCs,hV,hVeq,hB⟩ := uniform_one_gap r hr c hc
  obtain ⟨sA,zm,zp,G,Cmu,Cbeta,hsA,hsA1,hzm,hzp,hG,hCmu,hCbeta,hsrc⟩ :=
    CriticalRenewalSource.common_scalar_neighborhood r hr c hc
  let s0 := min sA sB
  let lam := min 1 (D/(2*Real.exp 1*V))
  let A := Real.log (1/α)/lam
  let C := Cbeta+2*Cmu*(A+3/2)/D
  have hlam : 0 < lam := lt_min zero_lt_one (div_pos hD (by positivity))
  have hA : 0 < A := div_pos
    (Real.log_pos ((one_lt_div hα).mpr (by linarith))) hlam
  refine ⟨eta,s0,D,V,C,heta,heta1,lt_min hsA hsB,
    lt_of_le_of_lt (min_le_left sA sB) hsA1,hD,hV,by dsimp [C]; positivity,?_⟩
  intro lam' A' K' s hs hss J hJ hscale f w m theta Delta delta t H
  have hbs := hB s hs (hss.trans_le (min_le_right sA sB)) J hJ hscale
  rcases hbs with ⟨hI,hdelta,hdeltaHalf,hDelta,hDeltaUpper,htheta0,htheta1,hthetaSq,
    hcontrast,hphases,hphaseLaw,hdata⟩
  have hmean (i : Bool) :
      (∫ ku : ℕ × ℤ, (ku.2 : ℝ)*delta ∂(pairLaw (f i) t).toMeasure) =
        (if i then (1 : ℝ) else -1)*Delta/2 := by
    have hh := (hdata i).2.2.2.2.2.2.2.1
    cases i <;> simpa only [Bool.false_eq_true,↓reduceIte,one_mul,neg_one_mul] using hh
  have hsecond (i : Bool) :
      (∫ ku : ℕ × ℤ, ((ku.2 : ℝ)*delta)^2 ∂(pairLaw (f i) t).toMeasure) ≤
        V*(s^(2*r)*(J : ℝ)) := (hdata i).2.2.2.2.2.2.2.2
  obtain ⟨hH,hrun⟩ := actual_run_bounds w f t delta D V (s^(2*r)*(J : ℝ)) Delta α
    hdelta hdeltaHalf hD hV hI hDelta hα hαhalf
    (fun z b => (hphases z).2.2.2.2 b) hmean hsecond
  have hpay := CriticalRenewalPayment.actual_source_payment r hr c hc s hs hH t
    (fun i => (hrun i).1) (fun i => (hrun i).2.1)
  have hscalar := (hsrc s hs (hss.trans_le (min_le_left sA sB))).1
  have hsone : s < 1 := lt_of_lt_of_le hss (le_trans (min_le_left sA sB) hsA1.le)
  have hIone := scale_information_le_one r J hr s eta hs hsone heta1 hscale
  have hj : 0 < (J : ℝ) := by exact_mod_cast (show 0 < J by omega)
  have hDeltaPos : 0 < Delta := (mul_pos hD hI).trans_le hDelta
  refine ⟨hH,full_state_count H J hH,full_count_bound r J hr hJ A hA,?_,?_⟩
  · intro bs n
    rw [score_evidence]
    exact (mul_div_cancel_right₀ _ hdelta.ne').symm
  · intro i
    have hi := hrun i
    have hp := hpay i
    refine ⟨hi.2.2.2,hi.1,hp.1,hi.2.1,hp.2.1,hi.2.2.1,hp.2.2,?_,?_⟩
    · rw [hp.2.2]
      have hmu := (hscalar i).2.2.1
      have hbeta := (hscalar i).2.2.2
      have hN : 0 ≤ ∫ ω : Sample, ((gapStop H t ω.2).toNat : ℝ)
          ∂sourceLaw (w i) (f i) t := integral_nonneg (fun _ => Nat.cast_nonneg _)
      have hden : 0 < s^(2*r+1)*(J : ℝ) := by positivity
      have hdenle : s^(2*r+1)*(J : ℝ) ≤ s := by
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_left hIone hs.le]
      have hleading : Cbeta/s ≤ Cbeta/(s^(2*r+1)*(J : ℝ)) :=
        div_le_div_of_nonneg_left hCbeta.le hden hdenle
      calc
        1+CriticalRenewalSource.beta r c i s+CriticalRenewalSource.mean r c i s*
            (∫ ω : Sample, ((gapStop H t ω.2).toNat : ℝ) ∂sourceLaw (w i) (f i) t)
            ≤ Cbeta/s+(Cmu/s)*(2*(A+3/2)/Delta) :=
          add_le_add hbeta (mul_le_mul hmu hi.2.2.1 hN (by positivity))
        _ ≤ Cbeta/s+(Cmu/s)*(2*(A+3/2)/(D*(s^(2*r)*(J : ℝ)))) := by
          gcongr
        _ = Cbeta/s+(2*Cmu*(A+3/2)/D)/(s^(2*r+1)*(J : ℝ)) := by
          rw [pow_succ]
          field_simp
        _ ≤ Cbeta/(s^(2*r+1)*(J : ℝ))+
            (2*Cmu*(A+3/2)/D)/(s^(2*r+1)*(J : ℝ)) := by linarith
        _ = C/(s^(2*r+1)*(J : ℝ)) := by dsimp [C]; ring
    · filter_upwards [hi.1] with ω hω
      have hpath := finite_gap_path hH t ω hω
      constructor
      · simpa only [clock,Nat.add_comm 1 ω.1] using hpath.2.1
      · rw [hpath.2.1,ENat.toNat_natCast]
        exact hpath.2.2.1

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalController
