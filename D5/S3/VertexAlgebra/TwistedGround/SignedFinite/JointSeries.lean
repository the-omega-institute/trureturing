/- GID: D5/S3/VertexAlgebra/TwistedGround/SignedFinite/JointSeries
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/SignedFinite/JointSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local joint scalar coefficient uniqueness and guarded polynomial multiplication. -/
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology ENNReal NNReal
namespace D5.S3.VertexAlgebra.TwistedGround.SignedFinite

/-- A local scalar series with its actual sum, on a derived positive disk. -/
def ScalarSeries (F : ℂ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ u : ℂ, ‖u‖ < R → HasSum (fun p => a p * u ^ p) (F u)

/-- An absolutely regroupable local joint series. HasSum uses the unordered sum. -/
def JointSeries (F : ℂ → ℂ → ℂ) (a : ℕ → ℕ → ℂ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ u v : ℂ, ‖u‖ < R → ‖v‖ < R →
    HasSum (fun pq : ℕ × ℕ => a pq.1 pq.2 * u ^ pq.1 * v ^ pq.2) (F u v)

theorem ScalarSeries.hasFPowerSeriesAt {F a} (h : ScalarSeries F a) :
    HasFPowerSeriesAt F (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
  obtain ⟨R, hR, hh⟩ := h
  let s : ℝ≥0 := ⟨R / 2, by positivity⟩
  have hs : 0 < (s : ℝ) := half_pos hR
  have hsR : (s : ℝ) < R := by
    change R / 2 < R
    linarith
  have hsR' : ‖(s : ℂ)‖ < R := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] using hsR
  have hsum := (hh (s : ℂ) hsR').summable.norm
  have hrad : (s : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℂ a).radius := by
    apply FormalMultilinearSeries.le_radius_of_summable
    simpa only [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] using hsum
  refine ⟨s, ⟨hrad, by exact_mod_cast hs, ?_⟩⟩
  intro u hu
  have hu' : ‖u‖ < (s : ℝ) := by
    rw [← ENNReal.ofReal_coe_nnreal, Metric.eball_ofReal] at hu
    simpa only [Metric.mem_ball, dist_zero_right] using hu
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using
    hh u (hu'.trans (by dsimp [s]; linarith))

theorem ScalarSeries.scalar_unique {F G a b} (ha : ScalarSeries F a) (hb : ScalarSeries G b)
    (he : ∀ᶠ u in 𝓝 (0 : ℂ), F u = G u) : a = b :=
  FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    (ha.hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually hb.hasFPowerSeriesAt he)

private lemma grouped {F : ℂ → ℂ → ℂ} {a : ℕ → ℕ → ℂ} {R : ℝ}
    (h : ∀ u v : ℂ, ‖u‖ < R → ‖v‖ < R →
      HasSum (fun pq : ℕ × ℕ => a pq.1 pq.2 * u ^ pq.1 * v ^ pq.2) (F u v))
    {u v : ℂ} (hu : ‖u‖ < R) (hv : ‖v‖ < R) :
    HasSum (fun p => (∑' q, a p q * v ^ q) * u ^ p) (F u v) := by
  have hh := h u v hu hv
  have he (p : ℕ) : (∑' q, a p q * u ^ p * v ^ q) =
      (∑' q, a p q * v ^ q) * u ^ p := by
    rw [← tsum_mul_right]
    apply tsum_congr
    intro q
    ring
  have hs := hh.summable.prod.hasSum
  rw [← hh.summable.tsum_prod, hh.tsum_eq] at hs
  exact hs.congr_fun (fun p => (he p).symm)

theorem JointSeries.unique {F G a b} (ha : JointSeries F a) (hb : JointSeries G b)
    (he : ∀ u v, F u v = G u v) : a = b := by
  obtain ⟨R, hR, ha⟩ := ha
  obtain ⟨S, hS, hb⟩ := hb
  let T := min R S
  have hT : 0 < T := lt_min hR hS
  have houter (v : ℂ) (hv : ‖v‖ < T) :
      (fun p => ∑' q, a p q * v ^ q) = (fun p => ∑' q, b p q * v ^ q) := by
    apply ScalarSeries.scalar_unique (F := fun u => F u v) (G := fun u => G u v)
    · exact ⟨T, hT, fun u hu => grouped ha (hu.trans_le (min_le_left _ _))
        (hv.trans_le (min_le_left _ _))⟩
    · exact ⟨T, hT, fun u hu => grouped hb (hu.trans_le (min_le_right _ _))
        (hv.trans_le (min_le_right _ _))⟩
    · exact Filter.Eventually.of_forall (fun u => he u v)
  have hrow (c : ℕ → ℕ → ℂ) (H : ℂ → ℂ → ℂ)
      (hc : ∀ u v : ℂ, ‖u‖ < T → ‖v‖ < T →
        HasSum (fun pq : ℕ × ℕ => c pq.1 pq.2 * u ^ pq.1 * v ^ pq.2) (H u v)) (p : ℕ) :
      ScalarSeries (fun v => ∑' q, c p q * v ^ q) (c p) := by
    refine ⟨T, hT, fun v hv => ?_⟩
    let w : ℂ := (T / 2 : ℝ)
    have hw : ‖w‖ < T := by
      simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hT)]
      linarith
    have hw0 : w ^ p ≠ 0 := pow_ne_zero _ (by
      dsimp [w]; exact_mod_cast (half_pos hT).ne')
    have hs := (hc w v hw hv).summable.prod_factor p
    have ht := hs.mul_right ((w ^ p)⁻¹)
    have ht' : Summable (fun q => c p q * v ^ q) := by
      convert ht using 1
      ext q
      field_simp
    exact ht'.hasSum
  funext p
  apply ScalarSeries.scalar_unique (hrow a F (fun u v hu hv =>
      ha u v (hu.trans_le (min_le_left _ _)) (hv.trans_le (min_le_left _ _))) p)
    (hrow b G (fun u v hu hv =>
      hb u v (hu.trans_le (min_le_right _ _)) (hv.trans_le (min_le_right _ _))) p)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hT] with v hv
  have hv' : ‖v‖ < T := by simpa using hv
  exact congrFun (houter v hv') p

/-- Multiplication by a monomial never aliases a natural zero index. -/
def shift (i j : ℕ) (a : ℕ → ℕ → ℂ) (p q : ℕ) : ℂ :=
  if i ≤ p ∧ j ≤ q then a (p - i) (q - j) else 0

def atom (i j : ℕ) (c : ℂ) (p q : ℕ) : ℂ :=
  if p = i ∧ q = j then c else 0

theorem JointSeries.congr_disk {F G a} (h : JointSeries F a) {S : ℝ} (hS : 0 < S)
    (he : ∀ u v : ℂ, ‖u‖ < S → ‖v‖ < S → F u v = G u v) : JointSeries G a := by
  obtain ⟨R, hR, hh⟩ := h
  refine ⟨min R S, lt_min hR hS, fun u v hu hv => ?_⟩
  rw [← he u v (hu.trans_le (min_le_right _ _)) (hv.trans_le (min_le_right _ _))]
  exact hh u v (hu.trans_le (min_le_left _ _)) (hv.trans_le (min_le_left _ _))

theorem JointSeries.add {F G a b} (ha : JointSeries F a) (hb : JointSeries G b) :
    JointSeries (fun u v => F u v + G u v) (fun p q => a p q + b p q) := by
  obtain ⟨R, hR, ha⟩ := ha
  obtain ⟨S, hS, hb⟩ := hb
  refine ⟨min R S, lt_min hR hS, fun u v hu hv => ?_⟩
  convert (ha u v (hu.trans_le (min_le_left _ _)) (hv.trans_le (min_le_left _ _))).add
    (hb u v (hu.trans_le (min_le_right _ _)) (hv.trans_le (min_le_right _ _))) using 1
  ext pq
  ring

theorem JointSeries.sub {F G a b} (ha : JointSeries F a) (hb : JointSeries G b) :
    JointSeries (fun u v => F u v - G u v) (fun p q => a p q - b p q) := by
  obtain ⟨R, hR, ha⟩ := ha
  obtain ⟨S, hS, hb⟩ := hb
  refine ⟨min R S, lt_min hR hS, fun u v hu hv => ?_⟩
  convert (ha u v (hu.trans_le (min_le_left _ _)) (hv.trans_le (min_le_left _ _))).sub
    (hb u v (hu.trans_le (min_le_right _ _)) (hv.trans_le (min_le_right _ _))) using 1
  ext pq
  ring

theorem JointSeries.scale {F a} (h : JointSeries F a) (c : ℂ) :
    JointSeries (fun u v => c * F u v) (fun p q => c * a p q) := by
  obtain ⟨R, hR, hh⟩ := h
  refine ⟨R, hR, fun u v hu hv => ?_⟩
  convert (hh u v hu hv).mul_left c using 1
  ext pq
  ring

theorem JointSeries.mul_monomial {F a} (h : JointSeries F a) (i j : ℕ) :
    JointSeries (fun u v => u ^ i * v ^ j * F u v) (shift i j a) := by
  obtain ⟨R, hR, hh⟩ := h
  refine ⟨R, hR, fun u v hu hv => ?_⟩
  let e : ℕ × ℕ → ℕ × ℕ := fun pq => (pq.1 + i, pq.2 + j)
  have hi : Function.Injective e := by
    rintro ⟨p,q⟩ ⟨k,l⟩ he
    have he' := Prod.mk.inj he
    apply Prod.ext <;> dsimp [e] at * <;> omega
  have hz : ∀ pq, pq ∉ Set.range e →
      SignedFinite.shift i j a pq.1 pq.2 * u ^ pq.1 * v ^ pq.2 = 0 := by
    rintro ⟨p,q⟩ hpq
    have hn : ¬ (i ≤ p ∧ j ≤ q) := by
      intro hp
      exact hpq ⟨(p-i,q-j), by dsimp [e]; apply Prod.ext <;> omega⟩
    simp [SignedFinite.shift, hn]
  apply (hi.hasSum_iff hz).mp
  convert (hh u v hu hv).mul_left (u ^ i * v ^ j) using 1
  ext pq
  simp only [Function.comp_def, e, SignedFinite.shift, Nat.le_add_left, and_self,
    ite_true, Nat.add_sub_cancel, pow_add]
  ring

theorem jointSeries_atom (i j : ℕ) (c : ℂ) :
    JointSeries (fun u v => c * u ^ i * v ^ j) (atom i j c) := by
  refine ⟨1, by norm_num, fun u v _ _ => ?_⟩
  have he : (fun pq : ℕ × ℕ => atom i j c pq.1 pq.2 * u ^ pq.1 * v ^ pq.2) =
      fun pq => if pq = (i,j) then c * u ^ i * v ^ j else 0 := by
    ext pq
    by_cases hh : pq = (i,j)
    · subst pq; simp [atom]
    · have hh' : ¬(pq.1 = i ∧ pq.2 = j) := by simpa [Prod.ext_iff] using hh
      simp [atom, hh, hh']
  rw [he]
  exact hasSum_ite_eq (i,j) _

/-- Absolute scalar sums produce the actual joint source product. -/
theorem ScalarSeries.prod {F G : ℂ → ℂ} {a b : ℕ → ℂ} (ha : ScalarSeries F a) (hb : ScalarSeries G b) :
    JointSeries (fun u v => F u * G v) (fun p q => a p * b q) := by
  obtain ⟨R, hR, ha⟩ := ha
  obtain ⟨S, hS, hb⟩ := hb
  refine ⟨min R S, lt_min hR hS, fun u v hu hv => ?_⟩
  have hf := ha u (hu.trans_le (min_le_left _ _))
  have hg := hb v (hv.trans_le (min_le_right _ _))
  have hnf : Summable (fun p : ℕ => ‖a p*u^p‖) := hf.summable.norm
  have hng : Summable (fun q : ℕ => ‖b q*v^q‖) := hg.summable.norm
  have hmul : Summable (fun pq : ℕ × ℕ => (a pq.1*u^pq.1)*(b pq.2*v^pq.2)) :=
    summable_mul_of_summable_norm (f := fun p => a p*u^p) (g := fun q => b q*v^q) hnf hng
  have hs : HasSum (fun pq : ℕ × ℕ => (a pq.1*u^pq.1)*(b pq.2*v^pq.2)) (F u*G v) :=
    HasSum.mul (f := fun p => a p*u^p) (g := fun q => b q*v^q) hf hg hmul
  have he : (fun pq : ℕ × ℕ => a pq.1 * b pq.2 * u ^ pq.1 * v ^ pq.2) =
      (fun pq : ℕ × ℕ => (a pq.1*u^pq.1)*(b pq.2*v^pq.2)) := by
    funext pq
    ring
  rw [he]
  exact hs

end D5.S3.VertexAlgebra.TwistedGround.SignedFinite
