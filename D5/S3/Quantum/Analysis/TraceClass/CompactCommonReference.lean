/- GID: D5/S3/Quantum/Analysis/TraceClass/CompactCommonReference
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/CompactCommonReference
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One continuous genuine spectral-energy reference on a compact convex state family. -/

import D5.S3.Quantum.Analysis.TraceClass.EntropyConcavity
import D5.S3.Quantum.Analysis.TraceClass.OrderedEnergy
import D5.S3.Quantum.Analysis.TraceClass.EnergySublevelCompactness
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology

noncomputable section
open scoped ComplexOrder ENNReal Topology
open Filter Set Metric
set_option backward.isDefEq.respectTransparency false
namespace QuantumLogEnergy
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem entropy_real (r : Reference H) :
    realEntropy r.1 = (spectralEntropy r).toReal := by
  simp only [realEntropy, dif_pos r.2]

private theorem rho_lsc {X : Type*} [TopologicalSpace X] (T : Reference H)
    (r : X → TraceClass H) (hc : Continuous r) (hp : ∀ x, 0 ≤ (r x).1) :
    LowerSemicontinuous (fun x => spectralEnergy T (r x)) := by
  apply lowerSemicontinuousOn_univ_iff.mp
  exact (lowerSemicontinuousOn_spectralEnergy_state T).comp hc.continuousOn
    (fun x _ => hp x)

private theorem gibbs (r s : Reference H)
    (hr : (trace r.1.1 (TraceClass.isTraceClass_coe r.1)).re = 1)
    (hs : (trace s.1.1 (TraceClass.isTraceClass_coe s.1)).re = 1) :
    spectralEntropy r ≤ spectralEnergy s r.1 :=
  (le_add_right le_rfl).trans (spectralEntropy_add_traceNorm_sq_le_energy r s hr hs)

/-- A genuine entropy maximizer controls cross energy on any convex state family. -/
theorem spectralEnergy_le_entropy_of_isMaxOn {C : Set (TraceClass H)}
    (hC : Convex ℝ C)
    (hp : ∀ r ∈ C, 0 ≤ r.1)
    (ht : ∀ r ∈ C, (trace r.1 (TraceClass.isTraceClass_coe r)).re = 1)
    (hf : ∀ (r) (h : r ∈ C), spectralEntropy
      (⟨r, hp r h, density_le_one r (hp r h) (ht r h)⟩ : Reference H) ≠ ∞)
    (g : Reference H) (hg : g.1 ∈ C) (hmax : IsMaxOn realEntropy C g.1)
    (r : TraceClass H) (hr : r ∈ C) : spectralEnergy g r ≤ spectralEntropy g := by
  let q : Reference H := ⟨r, hp r hr, density_le_one r (hp r hr) (ht r hr)⟩
  have hfg : spectralEntropy g ≠ ∞ := by convert hf g.1 hg using 1
  have step (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
      spectralEnergy (mixture g q (ht g.1 hg) (ht r hr)
        (1-t) t (by linarith) ht0.le (by ring)) r ≤ spectralEntropy g := by
    let u := mixture g q (ht g.1 hg) (ht r hr)
      (1-t) t (by linarith) ht0.le (by ring)
    have hu : u.1 ∈ C := by
      change (1-t : ℝ) • g.1 + t • r ∈ C
      exact hC hg hr (by linarith) ht0.le (by ring)
    have hfu : spectralEntropy u ≠ ∞ := by convert hf u.1 hu using 1
    have hSu : spectralEntropy u ≤ spectralEntropy g := by
      apply (ENNReal.toReal_le_toReal hfu hfg).mp
      rw [← entropy_real u, ← entropy_real g]
      exact hmax hu
    have he : ENNReal.ofReal (1-t) * spectralEnergy u g.1 +
        ENNReal.ofReal t * spectralEnergy u r ≤ spectralEntropy g := by
      rw [← spectralEnergy_nonneg_linear u g.1 r g.2.1 (hp r hr)
        (1-t) t (by linarith) ht0.le]
      exact (spectralEnergy_self u).le.trans hSu
    have hgib := gibbs g u (ht g.1 hg) (ht u.1 hu)
    have hsmall : ENNReal.ofReal (1-t) * spectralEntropy g +
        ENNReal.ofReal t * spectralEnergy u r ≤ spectralEntropy g :=
      (add_le_add (by gcongr) le_rfl).trans he
    have hsplit : ENNReal.ofReal (1-t) * spectralEntropy g +
        ENNReal.ofReal t * spectralEntropy g = spectralEntropy g := by
      rw [← add_mul, ← ENNReal.ofReal_add (by linarith) ht0.le]
      simp
    have hsmall := hsmall.trans_eq hsplit.symm
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_ne_zero_iff.mpr ht0)
      ENNReal.ofReal_ne_top).mp ((ENNReal.add_le_add_iff_left
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfg)).mp hsmall)
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have ht0 (n) : 0 < t n := by dsimp [t]; positivity
  have ht1 (n) : t n < 1 := by
    dsimp [t]
    exact (div_lt_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let u : ℕ → Reference H := fun n => mixture g q (ht g.1 hg) (ht r hr)
    (1-t n) (t n) (by linarith [ht1 n]) (ht0 n).le (by ring)
  have htz : Tendsto t atTop (𝓝 0) := by
    simpa only [t, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc,
      show (1 : ℝ) + 1 = 2 by norm_num] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 1)
  have hu : Tendsto u atTop (𝓝 g) := by
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun n => (1-t n) • g.1 + t n • r) atTop (𝓝 g.1)
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub htz).smul_const g.1).add (htz.smul_const r)
    simpa only [sub_zero, one_smul, zero_smul, add_zero] using h
  exact (lowerSemicontinuous_spectralEnergy r (hp r hr)).isClosed_preimage
    (spectralEntropy g) |>.mem_of_tendsto hu (Eventually.of_forall fun n => step _ (ht0 n) (ht1 n))

private theorem lsc_toReal_at {X : Type*} [TopologicalSpace X] {f : X → ℝ≥0∞}
    {x : X} (hl : LowerSemicontinuousAt f x) (hx : f x ≠ ∞)
    (hf : ∀ᶠ y in 𝓝 x, f y ≠ ∞) : LowerSemicontinuousAt (fun y => (f y).toReal) x := by
  intro a ha
  by_cases hneg : a < 0
  · exact Eventually.of_forall fun y => hneg.trans_le ENNReal.toReal_nonneg
  · have hapos : 0 ≤ a := le_of_not_gt hneg
    filter_upwards [hl (ENNReal.ofReal a) ((ENNReal.ofReal_lt_iff_lt_toReal hapos hx).mpr ha), hf]
      with y hy hyf
    exact (ENNReal.ofReal_lt_iff_lt_toReal hapos hyf).mp hy

private structure CenterCover (A : Set (TraceClass H)) (e : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  points : Finset (TraceClass H)
  nonempty : points.Nonempty
  point_mem : ∀ c ∈ points, c ∈ A
  covers : ∀ x ∈ A, ∃ j : {c // c ∈ points}, dist x j.1 < radius
  center : {c // c ∈ points} → Reference H
  center_mem : ∀ j, (center j).1 ∈ A
  center_cell : ∀ j, dist (center j).1 j.1 ≤ radius
  bound : ∀ j x, x ∈ A → dist x j.1 ≤ radius →
    spectralEnergy (center j) x ≤ spectralEntropy (center j)
  oscillation : ∀ j x, x ∈ A → dist x j.1 ≤ radius →
    realEntropy (center j).1 < realEntropy x + e

private theorem exists_centerCover {A : Set (TraceClass H)}
    (hA : IsCompact A) (hne : A.Nonempty) (hcv : Convex ℝ A)
    (hp : ∀ r ∈ A, 0 ≤ r.1)
    (ht : ∀ r ∈ A, (trace r.1 (TraceClass.isTraceClass_coe r)).re = 1)
    (hf : ∀ (r) (h : r ∈ A), spectralEntropy
      (⟨r, hp r h, density_le_one r (hp r h) (ht r h)⟩ : Reference H) ≠ ∞)
    (hc : ContinuousOn realEntropy A) (e : ℝ) (he : 0 < e) :
    Nonempty (CenterCover A e) := by
  classical
  obtain ⟨d, hd, hosc⟩ := Metric.uniformContinuousOn_iff.mp
    (hA.uniformContinuousOn_of_continuous hc) e he
  let r := d/3
  have hr : 0 < r := by dsimp [r]; positivity
  have hr2 : 2*r < d := by dsimp [r]; linarith
  obtain ⟨s, hsA, hsfin, hscover⟩ := hA.finite_cover_balls hr
  let J := hsfin.toFinset
  have hJ (c) : c ∈ J ↔ c ∈ s := hsfin.mem_toFinset
  have hJn : J.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨c, hc, _⟩ := Set.mem_iUnion₂.mp (hscover hx)
    exact ⟨c, (hJ c).mpr hc⟩
  have hlocal (j : {c // c ∈ J}) :
      ∃ g : Reference H, g.1 ∈ A ∩ closedBall j.1 r ∧
        IsMaxOn realEntropy (A ∩ closedBall j.1 r) g.1 := by
    have hcell : IsCompact (A ∩ closedBall j.1 r) := hA.inter_right isClosed_closedBall
    have hcenter : j.1 ∈ A ∩ closedBall j.1 r :=
      ⟨hsA ((hJ _).mp j.2), mem_closedBall_self hr.le⟩
    obtain ⟨g, hg, hmax⟩ := hcell.exists_isMaxOn ⟨_, hcenter⟩
      (hc.mono inter_subset_left)
    exact ⟨⟨g, hp g hg.1, density_le_one g (hp g hg.1) (ht g hg.1)⟩, hg, hmax⟩
  choose g hgm hmax using hlocal
  refine ⟨{ radius := r, radius_pos := hr, points := J, nonempty := hJn
            point_mem := fun c hc => hsA ((hJ c).mp hc)
            covers := ?_, center := g, center_mem := fun j => (hgm j).1
            center_cell := fun j => (hgm j).2, bound := ?_, oscillation := ?_ }⟩
  · intro x hx
    obtain ⟨c, hcs, hxc⟩ := Set.mem_iUnion₂.mp (hscover hx)
    exact ⟨⟨c, (hJ c).mpr hcs⟩, hxc⟩
  · intro j x hx hdist
    exact spectralEnergy_le_entropy_of_isMaxOn
      (hcv.inter (convex_closedBall _ _))
      (fun r hr => hp r hr.1) (fun r hr => ht r hr.1)
      (fun r hr => hf r hr.1) (g j) (hgm j) (hmax j) x ⟨hx, hdist⟩
  · intro j x hx hdist
    have hdist' : dist (g j).1 x < d :=
      (dist_triangle (g j).1 j.1 x).trans_lt
        ((add_le_add (hgm j).2 (by simpa [dist_comm] using hdist)).trans_lt (by linarith [hr2]))
    have hh := hosc (g j).1 (hgm j).1 x hx hdist'
    rw [Real.dist_eq] at hh
    linarith [(abs_lt.mp hh).2]

private def CenterCover.average {A : Set (TraceClass H)} {e : ℝ} (C : CenterCover A e) :
    TraceClass H := ∑ j : {c // c ∈ C.points}, (C.points.card : ℝ)⁻¹ • (C.center j).1

private theorem CenterCover.card_pos {A : Set (TraceClass H)} {e : ℝ}
    (C : CenterCover A e) : 0 < (C.points.card : ℝ) := by
  exact_mod_cast C.nonempty.card_pos

private theorem CenterCover.average_mem {A : Set (TraceClass H)} {e : ℝ}
    (C : CenterCover A e) (hcv : Convex ℝ A) : C.average ∈ A := by
  classical
  apply hcv.sum_mem (fun _ _ => by positivity)
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_coe, mul_inv_cancel₀ (ne_of_gt C.card_pos)]
  · exact fun j _ => C.center_mem j

private theorem positive_smul {r : TraceClass H} (hp : 0 ≤ r.1)
    {a : ℝ} (ha : 0 ≤ a) : 0 ≤ (a • r).1 := by
  change 0 ≤ (a : ℂ) • r.1
  rw [Complex.coe_smul]
  exact smul_nonneg ha hp

private theorem CenterCover.average_dominates {A : Set (TraceClass H)} {e : ℝ}
    (C : CenterCover A e) (j : {c // c ∈ C.points}) :
    ((C.points.card : ℝ)⁻¹ • (C.center j).1).1 ≤ C.average.1 := by
  classical
  change (operatorCLM ((C.points.card : ℝ)⁻¹ • (C.center j).1)) ≤
    operatorCLM (∑ i : {c // c ∈ C.points}, (C.points.card : ℝ)⁻¹ • (C.center i).1)
  rw [map_sum]
  exact Finset.single_le_sum (fun i _ => positive_smul (C.center i).2.1 (by positivity))
    (Finset.mem_univ j)

private def commonWeight (n : ℕ) : ℝ := (1/4) * (1/2)^n

private theorem commonWeight_pos (n : ℕ) : 0 < commonWeight n := by
  dsimp [commonWeight]; positivity

private theorem commonWeight_sum : HasSum commonWeight (1/2) := by
  convert hasSum_geometric_two.mul_left (1/4 : ℝ) using 1 <;>
    first | rfl | norm_num [commonWeight]

private theorem state_norm {A : Set (TraceClass H)}
    (hp : ∀ r ∈ A, 0 ≤ r.1)
    (ht : ∀ r ∈ A, (trace r.1 (TraceClass.isTraceClass_coe r)).re = 1)
    {r : TraceClass H} (hr : r ∈ A) : ‖r‖ = 1 := by
  rw [TraceClass.norm_eq_traceNorm, traceNorm_eq_re_trace _ (hp r hr), ht r hr]

private theorem exists_dominating_mixture {A : Set (TraceClass H)}
    (hA : IsCompact A) (hcv : Convex ℝ A)
    (hp : ∀ r ∈ A, 0 ≤ r.1)
    (ht : ∀ r ∈ A, (trace r.1 (TraceClass.isTraceClass_coe r)).re = 1)
    (g : TraceClass H) (hg : g ∈ A) (a : ℕ → TraceClass H) (ha : ∀ n, a n ∈ A) :
    ∃ s ∈ A, ((1/2 : ℝ) • g).1 ≤ s.1 ∧
      ∀ m, (commonWeight m • a m).1 ≤ s.1 := by
  classical
  have hc := commonWeight_sum
  have hpartial (N : ℕ) : ∑ n ∈ Finset.range N, commonWeight n ≤ 1/2 := by
    rw [← hc.tsum_eq]
    exact hc.summable.sum_le_tsum _ (fun n _ => (commonWeight_pos n).le)
  have hs : Summable (fun n => commonWeight n • a n) :=
    hc.summable.of_norm_bounded fun n => by
      rw [norm_smul, Real.norm_of_nonneg (commonWeight_pos n).le, state_norm hp ht (ha n), mul_one]
  let s := (1/2 : ℝ) • g + ∑' n, commonWeight n • a n
  let p := fun N => (1 - ∑ n ∈ Finset.range N, commonWeight n) • g +
    ∑ n ∈ Finset.range N, commonWeight n • a n
  have hpmem (N : ℕ) : p N ∈ A := by
    let w : Option (Fin N) → ℝ := fun i => i.elim
      (1 - ∑ n ∈ Finset.range N, commonWeight n) (fun i => commonWeight i)
    let z : Option (Fin N) → TraceClass H := fun i => i.elim g (fun i => a i)
    have hh : (∑ i, w i • z i) ∈ A := by
      apply hcv.sum_mem
      · intro i _
        cases i with
        | none => exact sub_nonneg.mpr ((hpartial N).trans (by norm_num))
        | some i => exact (commonWeight_pos i).le
      · simp [w, Fintype.sum_option, Fin.sum_univ_eq_sum_range]
      · intro i _
        cases i with
        | none => exact hg
        | some i => exact ha i
    simp only [w, z, Fintype.sum_option, Option.elim_none, Option.elim_some] at hh
    rw [Fin.sum_univ_eq_sum_range (fun n => commonWeight n • a n) N] at hh
    exact hh
  have hlim : Tendsto p atTop (𝓝 s) := by
    have hh := (((tendsto_const_nhds (x := (1 : ℝ))).sub hc.tendsto_sum_nat).smul_const g).add
      hs.hasSum.tendsto_sum_nat
    convert hh using 1 <;> norm_num [p, s]
  have hsmem : s ∈ A := hA.isClosed.mem_of_tendsto hlim (Eventually.of_forall hpmem)
  have hsumpos : 0 ≤ operatorCLM (∑' n, commonWeight n • a n) := by
    rw [operatorCLM.map_tsum hs]
    exact tsum_nonneg fun n => positive_smul (hp _ (ha n)) (commonWeight_pos n).le
  have hdom (m) : operatorCLM (commonWeight m • a m) ≤
      operatorCLM (∑' n, commonWeight n • a n) := by
    rw [operatorCLM.map_tsum hs]
    exact (hs.mapL operatorCLM).le_tsum m
      (fun n _ => positive_smul (hp _ (ha n)) (commonWeight_pos n).le)
  refine ⟨s, hsmem, ?_, ?_⟩
  · change operatorCLM ((1/2 : ℝ) • g) ≤ operatorCLM s
    change operatorCLM _ ≤ operatorCLM (_ + _)
    rw [map_add]
    exact le_add_of_nonneg_right hsumpos
  · intro m
    change operatorCLM (commonWeight m • a m) ≤ operatorCLM s
    change operatorCLM _ ≤ operatorCLM (_ + _)
    rw [map_add]
    exact (hdom m).trans (le_add_of_nonneg_left (positive_smul (hp _ hg) (by norm_num)))

private theorem energy_continuous_of_covers {A : Set (TraceClass H)}
    (hp : ∀ r ∈ A, 0 ≤ r.1)
    (ht : ∀ r ∈ A, (trace r.1 (TraceClass.isTraceClass_coe r)).re = 1)
    (hf : ∀ (r) (h : r ∈ A), spectralEntropy
      (⟨r, hp r h, density_le_one r (hp r h) (ht r h)⟩ : Reference H) ≠ ∞)
    (C : ∀ m : ℕ, CenterCover A ((1/2 : ℝ)^m))
    (s : Reference H)
    (he : ∀ r ∈ A, spectralEnergy s r ≠ ∞)
    (hw : ∀ m, 0 < commonWeight m / ((C m).points.card : ℝ) ∧
      commonWeight m / ((C m).points.card : ℝ) ≤ 1)
    (hdom : ∀ m j,
      ((commonWeight m / ((C m).points.card : ℝ)) • ((C m).center j).1).1 ≤ s.1.1) :
    ContinuousOn (fun r => (spectralEnergy s r).toReal) A ∧
      ContinuousOn (spectralEnergy s) A := by
  classical
  have hlow : LowerSemicontinuous (fun x : A => (spectralEnergy s x.1).toReal) := by
    intro x
    exact lsc_toReal_at ((rho_lsc s Subtype.val continuous_subtype_val
      (fun y : A => hp y.1 y.2)) x) (he x.1 x.2)
      (Eventually.of_forall fun y : A => he y.1 y.2)
  have hupp : UpperSemicontinuous (fun x : A => (spectralEnergy s x.1).toReal) := by
    intro x b hb
    let eps := b - (spectralEnergy s x.1).toReal
    have heps : 0 < eps := sub_pos.mpr hb
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < eps/3)
      (by norm_num : (1/2 : ℝ) < 1)
    obtain ⟨j, hj⟩ := (C m).covers x.1 x.2
    let g := (C m).center j
    let w := commonWeight m / ((C m).points.card : ℝ)
    let P := scaleReference g w (hw m).1 (hw m).2
    let F : TraceClass H → ℝ≥0∞ := orderedEnergy P s
    have hPQ : P.1.1 ≤ s.1.1 := hdom m j
    have hgf : spectralEntropy g ≠ ∞ := by convert hf g.1 ((C m).center_mem j) using 1
    have hlog : 0 ≤ -Real.log w := neg_nonneg.mpr (Real.log_nonpos (hw m).1.le (hw m).2)
    have hid (y : TraceClass H) (hy : y ∈ A) (hycell : dist y j.1 ≤ (C m).radius) :
        F y ≠ ∞ ∧
          (spectralEnergy g y).toReal - Real.log w =
            (F y).toReal + (spectralEnergy s y).toReal := by
      have hgy : spectralEnergy g y ≠ ∞ := ne_top_of_le_ne_top hgf ((C m).bound j y hy hycell)
      have hscale : spectralEnergy P y = spectralEnergy g y + ENNReal.ofReal (-Real.log w) := by
        rw [spectralEnergy_scaleReference g y (hp y hy) w (hw m).1 (hw m).2,
          ht y hy, ENNReal.ofReal_one, one_mul]
      have hsplit := spectralEnergy_eq_orderedEnergy_add P s hPQ y (hp y hy)
      have hPfin : spectralEnergy P y ≠ ∞ := by
        rw [hscale]
        exact ENNReal.add_ne_top.mpr ⟨hgy, ENNReal.ofReal_ne_top⟩
      have hF : F y ≠ ∞ := (ENNReal.add_ne_top.mp (by rw [← hsplit]; exact hPfin)).1
      refine ⟨hF, ?_⟩
      rw [hscale] at hsplit
      have hh := congrArg ENNReal.toReal hsplit
      rw [ENNReal.toReal_add hgy ENNReal.ofReal_ne_top,
        ENNReal.toReal_add hF (he y hy), ENNReal.toReal_ofReal hlog] at hh
      simpa only [sub_eq_add_neg] using hh
    have hball : ∀ᶠ y : A in 𝓝 x, dist y.1 j.1 < (C m).radius :=
      (isOpen_ball.preimage continuous_subtype_val).mem_nhds hj
    have hidx := hid x.1 x.2 hj.le
    have hlF : LowerSemicontinuousAt (fun y : A => (F y.1).toReal) x :=
      lsc_toReal_at (((lowerSemicontinuous_orderedEnergy P s).comp continuous_subtype_val) x)
        hidx.1 (hball.mono fun y hy => (hid y.1 y.2 hy.le).1)
    have hnear := hlF ((F x.1).toReal - eps/3) (by linarith)
    filter_upwards [hball, hnear] with y hy hFy
    have hidy := (hid y.1 y.2 hy.le).2
    have hgy : (spectralEnergy g y.1).toReal ≤ realEntropy g.1 := by
      rw [entropy_real g]
      exact ENNReal.toReal_mono hgf ((C m).bound j y.1 y.2 hy.le)
    let xr : Reference H := ⟨x.1, hp x.1 x.2, density_le_one x.1 (hp x.1 x.2) (ht x.1 x.2)⟩
    have hgxfin : spectralEnergy g x.1 ≠ ∞ :=
      ne_top_of_le_ne_top hgf ((C m).bound j x.1 x.2 hj.le)
    have hxg : realEntropy x.1 ≤ (spectralEnergy g x.1).toReal := by
      rw [show realEntropy x.1 = (spectralEntropy xr).toReal from entropy_real xr]
      exact ENNReal.toReal_mono hgxfin (gibbs xr g (ht x.1 x.2)
        (ht g.1 ((C m).center_mem j)))
    have hosc := (C m).oscillation j x.1 x.2 hj.le
    dsimp [g] at hgy hxg
    dsimp [eps] at hm hFy
    linarith [hidx.2]
  have hreal : Continuous (fun x : A => (spectralEnergy s x.1).toReal) :=
    continuous_iff_lower_upperSemicontinuous.mpr ⟨hlow, hupp⟩
  refine ⟨continuousOn_iff_continuous_domRestrict.mpr hreal, ?_⟩
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hh := ENNReal.continuous_ofReal.comp hreal
  convert hh using 1
  funext x
  exact (ENNReal.ofReal_toReal (he x.1 x.2)).symm

/-- Every nonempty compact real-convex family of actual positive trace-one operators
with finite continuous spectral entropy contains one reference whose genuine energy
is finite and continuous on that family, bounded by its maximum entropy plus log two. -/
theorem fullCompactCommonReference {A : Set (TraceClass H)}
    (hA : IsCompact A) (hne : A.Nonempty) (hcv : Convex ℝ A)
    (hp : ∀ r ∈ A, 0 ≤ r.1)
    (ht : ∀ r ∈ A, (trace r.1 (TraceClass.isTraceClass_coe r)).re = 1)
    (hf : ∀ (r) (h : r ∈ A), spectralEntropy
      (⟨r, hp r h, density_le_one r (hp r h) (ht r h)⟩ : Reference H) ≠ ∞)
    (hc : ContinuousOn realEntropy A) :
    ∃ gamma ∈ A, IsMaxOn realEntropy A gamma ∧
      ∃ sigma : Reference H, sigma.1 ∈ A ∧
        (∀ r ∈ A, spectralEnergy sigma r ≠ ∞ ∧
          spectralEnergy sigma r ≤ ENNReal.ofReal (realEntropy gamma + Real.log 2) ∧
          (spectralEnergy sigma r).toReal ≤ realEntropy gamma + Real.log 2) ∧
        ContinuousOn (spectralEnergy sigma) A ∧
        ContinuousOn (fun r => (spectralEnergy sigma r).toReal) A := by
  classical
  obtain ⟨gamma, hgamma, hmax⟩ := hA.exists_isMaxOn hne hc
  let g : Reference H := ⟨gamma, hp gamma hgamma,
    density_le_one gamma (hp gamma hgamma) (ht gamma hgamma)⟩
  have hgf : spectralEntropy g ≠ ∞ := hf gamma hgamma
  have hcenter (r) (hr : r ∈ A) : spectralEnergy g r ≤ spectralEntropy g :=
    spectralEnergy_le_entropy_of_isMaxOn hcv hp ht hf g hgamma hmax r hr
  let C : ∀ m : ℕ, CenterCover A ((1/2 : ℝ)^m) := fun m =>
    Classical.choice (exists_centerCover hA hne hcv hp ht hf hc _ (by positivity))
  obtain ⟨s, hsmem, hsg, hsa⟩ := exists_dominating_mixture hA hcv hp ht
    gamma hgamma (fun m => (C m).average) (fun m => (C m).average_mem hcv)
  let sigma : Reference H := ⟨s, hp s hsmem, density_le_one s (hp s hsmem) (ht s hsmem)⟩
  have hw (m) : 0 < commonWeight m / ((C m).points.card : ℝ) ∧
      commonWeight m / ((C m).points.card : ℝ) ≤ 1 := by
    have hcard := (C m).card_pos
    have hcard1 : 1 ≤ ((C m).points.card : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr (C m).nonempty.card_pos)
    have hcm : commonWeight m ≤ 1/2 := by
      rw [← commonWeight_sum.tsum_eq]
      exact commonWeight_sum.summable.le_tsum m (fun n _ => (commonWeight_pos n).le)
    exact ⟨div_pos (commonWeight_pos m) hcard,
      (div_le_one hcard).mpr (by linarith)⟩
  have hdom (m) (j : {c // c ∈ (C m).points}) :
      ((commonWeight m / ((C m).points.card : ℝ)) • ((C m).center j).1).1 ≤ sigma.1.1 := by
    have hh := smul_le_smul_of_nonneg_left ((C m).average_dominates j) (commonWeight_pos m).le
    have heq (a : ℝ) (r : TraceClass H) : (a • r).1 = a • r.1 := by
      change (a : ℂ) • r.1 = a • r.1
      exact Complex.coe_smul a r.1
    rw [← heq, ← heq, smul_smul, ← div_eq_mul_inv] at hh
    exact hh.trans (hsa m)
  have hbound (r) (hr : r ∈ A) :
      spectralEnergy sigma r ≤ ENNReal.ofReal (realEntropy gamma + Real.log 2) := by
    have hdomg : (scaleReference g (1/2) (by norm_num) (by norm_num)).1.1 ≤ sigma.1.1 := hsg
    have hh := spectralEnergy_antitone _ sigma hdomg r (hp r hr)
    rw [spectralEnergy_scaleReference g r (hp r hr) (1/2) (by norm_num) (by norm_num),
      ht r hr, ENNReal.ofReal_one, one_mul] at hh
    have hlog : -Real.log (1/2) = Real.log 2 := by
      rw [one_div, Real.log_inv, neg_neg]
    rw [hlog] at hh
    have hreal : ENNReal.ofReal (realEntropy gamma) = spectralEntropy g := by
      rw [show realEntropy gamma = (spectralEntropy g).toReal from entropy_real g]
      exact ENNReal.ofReal_toReal hgf
    have hgn : 0 ≤ realEntropy gamma := by rw [entropy_real g]; exact ENNReal.toReal_nonneg
    calc
      _ ≤ spectralEnergy g r + ENNReal.ofReal (Real.log 2) := hh
      _ ≤ spectralEntropy g + ENNReal.ofReal (Real.log 2) := add_le_add (hcenter r hr) le_rfl
      _ = _ := by rw [ENNReal.ofReal_add hgn (Real.log_nonneg (by norm_num)), hreal]
  have hfinite (r) (hr : r ∈ A) : spectralEnergy sigma r ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound r hr)
  have hcontinuous := energy_continuous_of_covers hp ht hf C sigma hfinite hw hdom
  refine ⟨gamma, hgamma, hmax, sigma, hsmem, ?_, hcontinuous.2, hcontinuous.1⟩
  intro r hr
  refine ⟨hfinite r hr, hbound r hr, ?_⟩
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound r hr)
  rw [ENNReal.toReal_ofReal (by
    have hgn : 0 ≤ realEntropy gamma := by rw [entropy_real g]; exact ENNReal.toReal_nonneg
    exact add_nonneg hgn (Real.log_nonneg (by norm_num)))] at hh
  exact hh

#print axioms spectralEnergy_le_entropy_of_isMaxOn
#print axioms fullCompactCommonReference

end QuantumLogEnergy
