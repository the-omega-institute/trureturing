/- GID: D5/S3/QuadraticForms/ThreeWayPositiveKernel
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/ThreeWayPositiveKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three-way balance is equivalent to a complete minimal complex Hilbert representation, unique on labels. -/

module

public import D5.S3.QuadraticForms.ThreeWayBalance
public import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic

/-! Complete minimal complex Hilbert representations derived on the original additive group. -/

public section

noncomputable section

namespace D5.S3.QuadraticForms.ThreeWayPositiveKernel

open scoped BigOperators ComplexConjugate ComplexOrder
open Finset

universe u v w

private theorem rational_gram_nonneg {A ι : Type*} [AddCommGroup A] [Fintype ι]
    (B : A →ₗ[ℤ] A →ₗ[ℤ] ℝ) (hB : ∀ x, 0 ≤ B x x)
    (x : ι → A) (a : ι → ℚ) :
    0 ≤ ∑ i, ∑ j, (a i : ℝ) * (a j : ℝ) * B (x i) (x j) := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) a
  choose n hn using hd
  have hd0 : (d : ℤ) ≠ 0 := nonZeroDivisors.ne_zero d.property
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  have hnR (i) : (n i : ℝ) = (d : ℝ) * (a i : ℝ) := by
    have h := hn i
    change (n i : ℚ) = (d : ℤ) • a i at h
    exact_mod_cast h
  have hp := hB (∑ i, n i • x i)
  have he : B (∑ i, n i • x i) (∑ i, n i • x i) =
      (d : ℝ)^2 * (∑ i, ∑ j, (a i : ℝ) * (a j : ℝ) * B (x i) (x j)) := by
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
      zsmul_eq_mul]
    rw [Finset.sum_comm]
    simp_rw [hnR]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at hp
  exact nonneg_of_mul_nonneg_right hp (sq_pos_of_ne_zero hdR)

private theorem real_gram_nonneg {A ι : Type*} [AddCommGroup A] [Fintype ι]
    (B : A →ₗ[ℤ] A →ₗ[ℤ] ℝ) (hB : ∀ x, 0 ≤ B x x)
    (x : ι → A) (a : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, a i * a j * B (x i) (x j) := by
  have hd : DenseRange (fun a : ι → ℚ => fun i => (a i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  exact hd.induction_on a (isClosed_le continuous_const (by fun_prop))
    (fun c => rational_gram_nonneg B hB x c)

private def gram {A : Type*} [AddCommGroup A]
    (B : A →ₗ[ℤ] A →ₗ[ℤ] ℝ) (U : A →+ A) (x y : A) : ℂ :=
  ⟨B x y, (B x y + 2 * B (U x) y) / Real.sqrt 3⟩

private theorem gram_hermitian {A : Type*} [AddCommGroup A]
    (B : A →ₗ[ℤ] A →ₗ[ℤ] ℝ) (U : A →+ A)
    (hs : ∀ x y, B x y = B y x)
    (ht : ∀ x y, B (U x) y + B x (U y) = -B x y) :
    Matrix.IsHermitian (gram B U) := by
  ext x y
  apply Complex.ext
  · change B y x = B x y
    exact hs y x
  · change -((B y x + 2 * B (U y) x) / Real.sqrt 3) =
      (B x y + 2 * B (U x) y) / Real.sqrt 3
    rw [← neg_div, hs y x, hs (U y) x]
    congr 1
    linarith [ht x y]

set_option maxHeartbeats 1600000 in
-- The expanded complex-to-real coefficient identity requires polynomial normalization.
private theorem complex_gram_nonneg {A ι : Type*} [AddCommGroup A] [Fintype ι]
    (B : A →ₗ[ℤ] A →ₗ[ℤ] ℝ) (U : A →+ A)
    (hB : ∀ x, 0 ≤ B x x)
    (hv : ∀ x y, B (U x) (U y) = B x y)
    (ht : ∀ x y, B (U x) y + B x (U y) = -B x y)
    (x : ι → A) (z : ι → ℂ) :
    0 ≤ (∑ i, ∑ j, conj (z i) * gram B U (x i) (x j) * z j).re := by
  classical
  let y : ι ⊕ ι → A := Sum.elim x (fun i => U (x i))
  let c : ι ⊕ ι → ℝ := Sum.elim
    (fun i => (z i).re + (z i).im / Real.sqrt 3)
    (fun i => 2 * (z i).im / Real.sqrt 3)
  have hp := real_gram_nonneg B hB y c
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have he (i j : ι) :
      (conj (z i) * gram B U (x i) (x j) * z j).re =
        c (.inl i) * c (.inl j) * B (x i) (x j) +
        c (.inl i) * c (.inr j) * B (x i) (U (x j)) +
        c (.inr i) * c (.inl j) * B (U (x i)) (x j) +
        c (.inr i) * c (.inr j) * B (U (x i)) (U (x j)) := by
    have ht' : B (x i) (U (x j)) = -B (x i) (x j) - B (U (x i)) (x j) := by
      linarith [ht (x i) (x j)]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      gram, c, Sum.elim_inl, Sum.elim_inr]
    rw [hv, ht']
    field_simp
    ring_nf
    simp only [hsq]
    ring
  simp only [Complex.re_sum, he, Finset.sum_add_distrib]
  simp only [y, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_add_distrib] at hp
  convert hp using 1
  ring

private theorem gram_posSemidef {A : Type*} [AddCommGroup A]
    (B : A →ₗ[ℤ] A →ₗ[ℤ] ℝ) (U : A →+ A)
    (hB : ∀ x, 0 ≤ B x x) (hs : ∀ x y, B x y = B y x)
    (hv : ∀ x y, B (U x) (U y) = B x y)
    (ht : ∀ x y, B (U x) y + B x (U y) = -B x y) :
    Matrix.PosSemidef (gram B U) := by
  classical
  have hh := gram_hermitian B U hs ht
  refine ⟨hh, ?_⟩
  intro z
  apply Complex.nonneg_iff.mpr
  constructor
  · have hp := complex_gram_nonneg B U hB hv ht (fun i : z.support => (i : A))
      (fun i => z i)
    have hinner (i : A) : (∑ j : z.support, conj (z i) * gram B U i j * z j) =
        ∑ j ∈ z.support, conj (z i) * gram B U i j * z j :=
      Finset.sum_coe_sort z.support
        (fun j : A => conj (z i) * gram B U i j * z j)
    simp_rw [hinner] at hp
    have houter : (∑ i : z.support, ∑ j ∈ z.support,
        conj (z i) * gram B U i j * z j) =
        ∑ i ∈ z.support, ∑ j ∈ z.support, conj (z i) * gram B U i j * z j :=
      Finset.sum_coe_sort z.support
        (fun i : A => ∑ j ∈ z.support, conj (z i) * gram B U i j * z j)
    rw [houter] at hp
    simpa only [Finsupp.sum, starRingEnd_apply] using hp
  · have hstar : star (z.sum fun i zi => z.sum fun j zj => star zi * gram B U i j * zj) =
        (z.sum fun i zi => z.sum fun j zj => star zi * gram B U i j * zj) := by
      simp only [star_finsuppSum, Pi.star_apply, star_mul, star_star]
      rw [Finsupp.sum_comm]
      unfold Finsupp.sum
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (z i) * (star (gram B U j i) * z j) =
        star (z i) * gram B U i j * z j
      rw [hh.apply]
      ring
    have hi := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at hi
    simp only [Complex.star_def]
    linarith

/-- The fixed primitive third root selected by the source orientation. -/
@[expose] def omega : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

/-- The scalar Gram entry forced by the three-way law, with inner products
conjugate-linear in the first label. -/
@[expose] def complexGram {A : Type*} [AddCommGroup A] (U : A →+ A) (q : A → ℝ)
    (x y : A) : ℂ :=
  let b : A → A → ℝ := fun x y => (q (x + y) - q (x - y)) / 4
  ⟨b x y, (b x y + 2 * b (U x) y) / Real.sqrt 3⟩

/-- The nonnegative universal three-way law on an arbitrary additive group supplies
its forced complex positive kernel, without any scalar or topological structure on A. -/
private theorem three_way_positive_kernel {A : Type*} [AddCommGroup A]
    (U : A →+ A) (q : A → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hT : ∀ x y, q (x + y) + q (x + U y) + q (x + U (U y)) =
      3 * q x + 3 * q y) :
    Matrix.PosSemidef (complexGram U q) ∧
    (∀ x, complexGram U q x x = (q x : ℂ)) ∧
    (∀ x y z, complexGram U q (x + y) z =
      complexGram U q x z + complexGram U q y z) ∧
    (∀ x y, complexGram U q (U x) y = conj omega * complexGram U q x y) := by
  obtain ⟨hi, hD, _, hp, Q, hQ⟩ :=
    ThreeWayBalance.three_way_quadratic_structure U q hq hT
  let B : A →ₗ[ℤ] A →ₗ[ℤ] ℝ := (1 / 2 : ℝ) • Q.polarBilin
  have hb (x y : A) : B x y = (q (x + y) - q (x - y)) / 4 := by
    change (1 / 2 : ℝ) * (Q (x + y) - Q x - Q y) = _
    rw [hQ, hQ, hQ]
    linarith [hp x y]
  have hb' (x y : A) : B x y = (q (x + y) - q x - q y) / 2 := by
    change (1 / 2 : ℝ) * (Q (x + y) - Q x - Q y) = _
    rw [hQ, hQ, hQ]
    ring
  have hs (x y : A) : B x y = B y x := by
    rw [hb', hb', add_comm x y]
    ring
  have hd (x : A) : B x x = q x := by
    change (1 / 2 : ℝ) * QuadraticMap.polar Q x x = _
    rw [Q.polar_self, hQ]
    simp
  have hv (x y : A) : B (U x) (U y) = B x y := by
    rw [hb', hb', ← map_add, hi, hi, hi]
  have hDz (x y : A) : B x (y + U y + U (U y)) = 0 := by
    rw [hb', hD, show q (y + U y + U (U y)) = 0 from by
      have h := hD 0 y
      have hzero : q 0 = 0 := (hQ 0).symm.trans Q.map_zero
      simpa only [zero_add, hzero] using h]
    ring
  have ht (x y : A) : B (U x) y + B x (U y) = -B x y := by
    have h := hDz (U x) y
    simp only [map_add] at h
    rw [hv, hv x (U y)] at h
    linarith
  have hu2 (x y : A) : B (U (U x)) y = -B x y - B (U x) y := by
    have h := hDz y x
    simp only [map_add] at h
    rw [hs y x, hs y (U x), hs y (U (U x))] at h
    linarith
  have hg : complexGram U q = gram B U := by
    funext x y
    simp only [complexGram, gram, hb]
  rw [hg]
  refine ⟨gram_posSemidef B U (fun x => by rw [hd]; exact hq x) hs hv ht, ?_, ?_, ?_⟩
  · intro x
    apply Complex.ext
    · exact hd x
    · change (B x x + 2 * B (U x) x) / Real.sqrt 3 = 0
      have h := ht x x
      rw [← hs (U x) x] at h
      have hz : B x x + 2 * B (U x) x = 0 := by linarith
      rw [hz, zero_div]
  · intro x y z
    apply Complex.ext
    · simp [gram, map_add]
    · simp [gram, map_add]
      ring
  · intro x y
    have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    apply Complex.ext
    · simp only [gram, omega, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      field_simp
      ring
    · simp only [gram, omega, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      rw [hu2]
      field_simp
      ring_nf
      simp only [hsq]
      ring

private def scalarOperator {A : Type*} (K : A → A → ℂ) :
    Matrix A A (ℂ →L[ℂ] ℂ) := fun x y => K x y • ContinuousLinearMap.id ℂ ℂ

private theorem scalarOperator_posSemidef {A : Type*} (K : A → A → ℂ)
    (hK : Matrix.PosSemidef K) : Matrix.PosSemidef (scalarOperator K) := by
  rw [RKHS.posSemidef_iff_re_sum_kernel']
  constructor
  · ext x y
    simp only [Matrix.conjTranspose_apply, scalarOperator, star_smul,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id,
      smul_apply, ContinuousLinearMap.id_apply]
    rw [hK.1.apply]
  · intro z
    have hp := (Complex.nonneg_iff.mp (hK.2 z)).1
    convert hp using 1
    change (z.sum fun x w => z.sum fun x' w' =>
      inner ℂ ((scalarOperator K x' x) w) w').re = _
    congr 1
    apply Finsupp.sum_congr
    intro i zi
    apply Finsupp.sum_congr
    intro j zj
    simp only [scalarOperator, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, inner, star_mul]
    rw [hK.1.apply]
    ring

/-- A complete complex representation with precisely the original additive labels. -/
structure HilbertRepresentation {A : Type u} [AddCommGroup A] (U : A →+ A) (q : A → ℝ) where
  carrier : Type v
  [normed : NormedAddCommGroup carrier]
  [innerProduct : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]
  label : A →+ carrier
  normSq : ∀ x, q x = ‖label x‖ ^ 2
  phase : ∀ x, label (U x) = omega • label x
  minimal : (Submodule.span ℂ (Set.range label)).topologicalClosure = ⊤

attribute [instance] HilbertRepresentation.normed HilbertRepresentation.innerProduct
  HilbertRepresentation.complete

private theorem exists_representation {A : Type u} [AddCommGroup A]
    (U : A →+ A) (q : A → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hT : ∀ x y, q (x + y) + q (x + U y) + q (x + U (U y)) =
      3 * q x + 3 * q y) : Nonempty (HilbertRepresentation.{u, u} U q) := by
  classical
  obtain ⟨hK, hd, ha, hw⟩ := three_way_positive_kernel U q hq hT
  let K := complexGram U q
  change Matrix.PosSemidef K at hK
  change ∀ x, K x x = (q x : ℂ) at hd
  change ∀ x y z, K (x + y) z = K x z + K y z at ha
  change ∀ x y, K (U x) y = conj omega * K x y at hw
  let L := scalarOperator K
  let : Fact (Matrix.PosSemidef L) := ⟨scalarOperator_posSemidef K hK⟩
  let H := RKHS.OfKernel L
  let f : A → H := fun x => RKHS.kerFun H x 1
  have hf (x y : A) : (f y) x = K x y := by
    simp only [f, RKHS.kerFun_apply, H, RKHS.OfKernel.kernel_ofKernel,
      L, scalarOperator, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
  have har (x y z : A) : K z (x + y) = K z x + K z y := by
    calc
      K z (x + y) = star (K (x + y) z) := (hK.1.apply z (x + y)).symm
      _ = K z x + K z y := by rw [ha, star_add, hK.1.apply, hK.1.apply]
  have hwr (x y : A) : K y (U x) = omega * K y x := by
    calc
      K y (U x) = star (K (U x) y) := (hK.1.apply y (U x)).symm
      _ = star (conj omega * K x y) := congrArg star (hw x y)
      _ = omega * K y x := by
        rw [star_mul, starRingEnd_apply, star_star, hK.1.apply]
        ring
  have haa (x y : A) : f (x + y) = f x + f y := by
    apply RKHS.ext
    intro z
    simpa only [RKHS.coe_add, Pi.add_apply, hf] using har x y z
  have hn (x : A) : q x = ‖f x‖ ^ 2 := by
    have hh : inner ℂ (f x) (f x) = (q x : ℂ) := by
      rw [show f x = RKHS.kerFun H x 1 from rfl, RKHS.kerFun_inner]
      simpa only [← show f x = RKHS.kerFun H x 1 from rfl, hf, inner, star_one,
        mul_one, one_mul] using hd x
    calc
      q x = (inner ℂ (f x) (f x)).re := by
        simpa only [Complex.ofReal_re] using (congrArg Complex.re hh).symm
      _ = ‖f x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hp (x : A) : f (U x) = omega • f x := by
    apply RKHS.ext
    intro y
    simpa only [RKHS.coe_smul, Pi.smul_apply, smul_eq_mul, hf] using hwr x y
  have hs : Submodule.span ℂ (Set.range f) =
      Submodule.span ℂ {RKHS.kerFun H x v | (x : A) (v : ℂ)} := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      exact Submodule.subset_span ⟨x, 1, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, v, rfl⟩
      have hv : RKHS.kerFun H x v = v • f x := by
        dsimp only [f]
        rw [← map_smul]
        simp only [smul_eq_mul, mul_one]
      rw [hv]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  refine ⟨{ carrier := H
            label := AddMonoidHom.mk' f haa
            normSq := hn
            phase := hp
            minimal := ?_ }⟩
  change (Submodule.span ℂ (Set.range f)).topologicalClosure = ⊤
  rw [hs]
  exact RKHS.kerFun_dense H

private theorem model_gram {A : Type u} [AddCommGroup A]
    {U : A →+ A} {q : A → ℝ} (R : HilbertRepresentation.{u, v} U q) (x y : A) :
    inner ℂ (R.label x) (R.label y) = complexGram U q x y := by
  let b : A → A → ℝ := fun x y => (q (x + y) - q (x - y)) / 4
  have hb (x y : A) : (inner ℂ (R.label x) (R.label y)).re = b x y := by
    change RCLike.re (inner ℂ (R.label x) (R.label y)) = b x y
    rw [re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℂ)]
    dsimp only [b]
    rw [← map_add, ← map_sub, R.normSq, R.normSq]
    ring
  have h := hb (U x) y
  rw [R.phase, inner_smul_left] at h
  have h' : (-1 / 2 : ℝ) * (inner ℂ (R.label x) (R.label y)).re +
      (Real.sqrt 3 / 2) * (inner ℂ (R.label x) (R.label y)).im = b (U x) y := by
    simpa only [omega, Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul,
      sub_neg_eq_add] using h
  apply Complex.ext
  · exact hb x y
  · change (inner ℂ (R.label x) (R.label y)).im =
      (b x y + 2 * b (U x) y) / Real.sqrt 3
    apply (eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))).mpr
    rw [← hb]
    linarith

@[instance_reducible] private def modelRKHS {A : Type u} [AddCommGroup A]
    {U : A →+ A} {q : A → ℝ} (R : HilbertRepresentation.{u, v} U q) :
    RKHS ℂ R.carrier A ℂ where
  coeCLM := ContinuousLinearMap.pi (fun x => innerSL ℂ (R.label x))
  coeCLM_injective := by
    intro v w h
    have hd : Dense (Submodule.span ℂ (Set.range R.label) : Set R.carrier) :=
      Submodule.dense_iff_topologicalClosure_eq_top.mpr R.minimal
    apply hd.eq_of_inner_right ℂ
    intro z hz
    refine Submodule.span_induction (fun z hz => ?_) (by simp)
      (by simp +contextual [inner_add_left])
      (by simp +contextual [inner_smul_left]) hz
    obtain ⟨x, rfl⟩ := hz
    exact congrFun h x

private theorem model_kerFun {A : Type u} [AddCommGroup A]
    {U : A →+ A} {q : A → ℝ} (R : HilbertRepresentation.{u, v} U q) (x : A) (v : ℂ) :
    let := modelRKHS R
    RKHS.kerFun R.carrier x v = v • R.label x := by
  let := modelRKHS R
  apply ext_inner_right ℂ
  intro w
  rw [RKHS.kerFun_inner, inner_smul_left]
  change inner ℂ v (inner ℂ (R.label x) w) = _
  simp only [inner, starRingEnd_apply]
  ring

private theorem model_kernel {A : Type u} [AddCommGroup A]
    {U : A →+ A} {q : A → ℝ} (R : HilbertRepresentation.{u, v} U q) :
    let := modelRKHS R
    RKHS.kernel R.carrier = scalarOperator (complexGram U q) := by
  let := modelRKHS R
  ext x y
  apply ext_inner_right ℂ
  intro w
  rw [RKHS.kernel_inner, model_kerFun, model_kerFun, inner_smul_left, inner_smul_right,
    model_gram]
  simp only [scalarOperator, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    inner]
  have hc : star (complexGram U q x y) = complexGram U q y x := by
    rw [← model_gram R x y, ← model_gram R y x]
    simpa only [Complex.star_def] using
      (inner_conj_symm (𝕜 := ℂ) (R.label y) (R.label x))
  simp only [map_one, one_mul, mul_one, hc]

private theorem models_unique {A : Type u} [AddCommGroup A]
    {U : A →+ A} {q : A → ℝ}
    (R : HilbertRepresentation.{u, v} U q) (S : HilbertRepresentation.{u, w} U q) :
    ∃! e : R.carrier ≃ₗᵢ[ℂ] S.carrier, ∀ x, e (R.label x) = S.label x := by
  let := modelRKHS R
  let := modelRKHS S
  have hk : RKHS.kernel R.carrier = RKHS.kernel S.carrier :=
    (model_kernel R).trans (model_kernel S).symm
  let e : R.carrier ≃ₗᵢ[ℂ] S.carrier := RKHS.equiv hk
  have he (x : A) : e (R.label x) = S.label x := by
    have h := RKHS.equiv_kerFun hk x 1
    simpa only [model_kerFun, one_smul] using h
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply DFunLike.ext
  intro z
  have hd : Dense (Submodule.span ℂ (Set.range R.label) : Set R.carrier) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr R.minimal
  refine hd.induction (fun z hz => ?_) (isClosed_eq e'.continuous e.continuous) z
  refine Submodule.span_induction (fun z hz => ?_) (by simp)
    (by simp +contextual [map_add]) (by simp +contextual [map_smul]) hz
  obtain ⟨x, rfl⟩ := hz
  exact (he' x).trans (he x).symm

private theorem norm_three_way {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) :
    ‖x + y‖ ^ 2 + ‖x + omega • y‖ ^ 2 + ‖x + (omega ^ 2) • y‖ ^ 2 =
      3 * ‖x‖ ^ 2 + 3 * ‖y‖ ^ 2 := by
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hm : conj omega * omega = 1 := by
    apply Complex.ext <;> simp [omega, Complex.mul_re, Complex.mul_im] <;> nlinarith
  have hs : 1 + omega + omega ^ 2 = 0 := by
    apply Complex.ext <;> simp [omega, pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith
  have hsc : 1 + conj omega + conj (omega ^ 2) = 0 := by
    simpa only [map_add, map_one, map_zero] using congrArg (starRingEnd ℂ) hs
  have hm2 : conj (omega ^ 2) * omega ^ 2 = 1 := by
    rw [map_pow]
    calc
      conj omega ^ 2 * omega ^ 2 = (conj omega * omega) ^ 2 := by ring
      _ = 1 := by rw [hm]; norm_num
  have hi : inner ℂ (x + y) (x + y) + inner ℂ (x + omega • y) (x + omega • y) +
      inner ℂ (x + omega ^ 2 • y) (x + omega ^ 2 • y) =
        (3 : ℂ) * inner ℂ x x + (3 : ℂ) * inner ℂ y y := by
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
    calc
      _ = 3 * inner ℂ x x + (1 + omega + omega ^ 2) * inner ℂ x y +
          (1 + conj omega + conj (omega ^ 2)) * inner ℂ y x +
          (1 + conj omega * omega + conj (omega ^ 2) * omega ^ 2) * inner ℂ y y := by ring
      _ = _ := by rw [hs, hsc, hm, hm2]; ring
  have hn (z : H) : (inner ℂ z z).re = ‖z‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  have h := congrArg Complex.re hi
  simp only [Complex.add_re, Complex.mul_re, hn] at h
  norm_num at h
  exact h

private theorem representation_balance {A : Type u} [AddCommGroup A]
    {U : A →+ A} {q : A → ℝ} (R : HilbertRepresentation.{u, v} U q) :
    ∀ x y, q (x + y) + q (x + U y) + q (x + U (U y)) =
      3 * q x + 3 * q y := by
  intro x y
  simp only [R.normSq, map_add, R.phase, smul_smul]
  simpa only [pow_two] using norm_three_way (R.label x) (R.label y)

/-- Full additive-group characterization, including complete minimal representation,
its converse, and the unique complex-linear label-preserving unitary between any two models. -/
theorem three_way_hilbert_characterization {A : Type u} [AddCommGroup A]
    (U : A →+ A) (q : A → ℝ) (hq : ∀ x, 0 ≤ q x) :
    ((∀ x y, q (x + y) + q (x + U y) + q (x + U (U y)) =
      3 * q x + 3 * q y) ↔ Nonempty (HilbertRepresentation.{u, u} U q)) ∧
    (∀ R : HilbertRepresentation.{u, v} U q, ∀ x y,
      q (x + y) + q (x + U y) + q (x + U (U y)) = 3 * q x + 3 * q y) ∧
    (∀ (R : HilbertRepresentation.{u, v} U q) (S : HilbertRepresentation.{u, w} U q),
      ∃! e : R.carrier ≃ₗᵢ[ℂ] S.carrier, ∀ x, e (R.label x) = S.label x) := by
  exact ⟨⟨exists_representation U q hq, fun ⟨R⟩ => representation_balance R⟩,
    fun R => representation_balance R, fun R S => models_unique R S⟩

end D5.S3.QuadraticForms.ThreeWayPositiveKernel
