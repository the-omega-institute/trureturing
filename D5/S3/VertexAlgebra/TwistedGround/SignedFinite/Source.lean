/- GID: D5/S3/VertexAlgebra/TwistedGround/SignedFinite/Source
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/SignedFinite/Source
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite signed source modes with the actual principal negative basepoint. -/
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.JointSeries
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianFiniteCandidateModes
import D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology BigOperators
namespace D5.S3.VertexAlgebra.TwistedGround.SignedFinite
open OriginalGaussianSourceEvaluation OriginalGaussianExternalGenerators
open OriginalGaussianFiniteCandidateModes (a sourceAmplitude_true_finite)

def A (r : ℂ) : ℂ := 1 - r
/-- The actual negative zero-mode binomial branch. -/
def C (r : ℂ) : ℂ := (1 - r) ^ (-1 / 2 : ℂ)
def m (e : Bool) (p : ℕ) (r : ℂ) : ℂ :=
  if e then a p r else C r * (A r)⁻¹ ^ p * a p r

theorem A_ne_zero {r : ℂ} (hr : ‖r‖ < 1) : A r ≠ 0 := by
  intro he
  have he' : r = 1 := (sub_eq_zero.mp he).symm
  rw [he', norm_one] at hr
  exact hr.false

private lemma C_sq (r : ℂ) : C r ^ 2 = (A r)⁻¹ := by
  unfold C A
  rw [← Complex.cpow_mul_nat]
  norm_num [Complex.cpow_neg_one]

private lemma source_basepoint {r : ℂ} (hr : ‖r‖ < 1) :
    sourceMode false 0 r = C r ∧ sourceMode true 0 r = 1 := by
  have hh := sourceAmplitude_generators (u := 0) (x := r) (by simpa using hr)
  constructor
  · simpa [sourceMode, C] using hh.2.tsum_eq
  · simpa [sourceMode] using hh.1.tsum_eq

theorem source_scalarSeries (e : Bool) {r : ℂ} (hr : ‖r‖ < 1) :
    ScalarSeries (fun u => sourceMode e u r) (fun p => sourceAmplitude e p r) := by
  refine ⟨1 - ‖r‖, by linarith, fun u hu => ?_⟩
  exact (sourceAmplitude_mode_hasSum e (by linarith)).summable.hasSum

private lemma source_negative_local {r : ℂ} (hr : ‖r‖ < 1) :
    ∀ᶠ u in 𝓝 (0 : ℂ), sourceMode false u r = C r * sourceMode true (u / A r) r := by
  have hA := A_ne_zero hr
  have hC : C r ≠ 0 := by
    intro he
    have hh := C_sq r
    rw [he, zero_pow (by decide)] at hh
    exact (inv_ne_zero hA) hh.symm
  have hbase := source_basepoint hr
  have hzero : ‖(0 : ℂ)‖ + ‖r‖ < 1 := by simpa using hr
  have hf := (OriginalGaussianExternalSignedCandidate.source_u false hzero).continuousAt
  have hg : ContinuousAt (fun u : ℂ => C r * sourceMode true (u / A r) r) 0 := by
    apply continuousAt_const.mul
    have hh : ContinuousAt (fun w => sourceMode true w r) (0 / A r) := by
      simpa only [zero_div] using
        (OriginalGaussianExternalSignedCandidate.source_u true hzero).continuousAt
    exact hh.comp (f := fun u : ℂ => u / A r) (by fun_prop : ContinuousAt (fun u : ℂ => u / A r) 0)
  have hn : sourceMode false 0 r + C r * sourceMode true (0 / A r) r ≠ 0 := by
    rw [zero_div, hbase.1, hbase.2, mul_one]
    intro he
    apply hC
    linear_combination he / 2
  have hnonzero := (hf.add hg).eventually_ne hn
  have hsmall : ∀ᶠ u in 𝓝 (0 : ℂ), ‖u‖ + ‖r‖ < 1 ∧ ‖u / A r‖ + ‖r‖ < 1 := by
    have h1 : Continuous (fun u : ℂ => ‖u‖ + ‖r‖) := by fun_prop
    have h2 : Continuous (fun u : ℂ => ‖u / A r‖ + ‖r‖) := by fun_prop
    exact (h1.continuousAt.eventually_lt_const hzero).and
      (h2.continuousAt.eventually_lt_const (by simpa using hr))
  filter_upwards [hnonzero, hsmall] with u hne hu
  have hs : sourceMode false u r ^ 2 = (C r * sourceMode true (u / A r) r) ^ 2 := by
    rw [(sourceMode_square hu.1).2, mul_pow, C_sq, (sourceMode_square hu.2).1]
    unfold A at *
    field_simp
    <;> ring
  have hp : (sourceMode false u r - C r * sourceMode true (u / A r) r) *
      (sourceMode false u r + C r * sourceMode true (u / A r) r) = 0 := by
    linear_combination hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hne)

theorem sourceAmplitude_false_finite (p : ℕ) {r : ℂ} (hr : ‖r‖ < 1) :
    sourceAmplitude false p r = C r * (A r)⁻¹ ^ p * a p r := by
  have hA := A_ne_zero hr
  have hnorm : 0 < ‖A r‖ := norm_pos_iff.mpr hA
  have hs : ScalarSeries (fun u => C r * sourceMode true (u / A r) r)
      (fun p => C r * (A r)⁻¹ ^ p * a p r) := by
    refine ⟨(1 - ‖r‖) * ‖A r‖, mul_pos (by linarith) hnorm, fun u hu => ?_⟩
    have hu' : ‖u / A r‖ + ‖r‖ < 1 := by
      rw [norm_div]
      have hd := (div_lt_iff₀ hnorm).mpr hu
      linarith
    have hh := (sourceAmplitude_mode_hasSum true hu').summable.hasSum.mul_left (C r)
    change HasSum _ (C r * ∑' p, sourceAmplitude true p r * (u / A r) ^ p)
    convert hh using 1
    ext p
    simp only [sourceAmplitude_true_finite, div_pow, div_eq_mul_inv, inv_pow]
    ring
  exact congrFun ((source_scalarSeries false hr).unique hs (source_negative_local hr)) p

theorem sourceAmplitude_eq_m (e : Bool) (p : ℕ) {r : ℂ} (hr : ‖r‖ < 1) :
    sourceAmplitude e p r = m e p r := by
  cases e
  · exact sourceAmplitude_false_finite p hr
  · exact sourceAmplitude_true_finite p r

/-- The joint product expansion is inherited from the literal source sums. -/
theorem source_jointSeries (e f : Bool) {r : ℂ} (hr : ‖r‖ < 1) :
    JointSeries (fun u v => sourceMode e u r * sourceMode f v r)
      (fun p q => m e p r * m f q r) := by
  have hs := (source_scalarSeries e hr).prod (source_scalarSeries f hr)
  have he : (fun p q => sourceAmplitude e p r * sourceAmplitude f q r) =
      (fun p q => m e p r * m f q r) := by
    funext p q
    rw [sourceAmplitude_eq_m e p hr, sourceAmplitude_eq_m f q hr]
  rw [he] at hs
  exact hs

end D5.S3.VertexAlgebra.TwistedGround.SignedFinite
