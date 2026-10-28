/- GID: D5/S3/Observer/CubicGain/PrimitivePrefix
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/PrimitivePrefix
   mirror-E: none(waiver:uniform-legal-prefix-representation)
   anchors: []
   utility: none
   digest: Whole legal prefix kernels have primitive signed integer levels. -/

import D5.S3.Observer.CubicGain.LegalMatrixMonoid
import D5.S3.Arith.Lattices.CofactorKernel
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace D5.S3.Observer.CubicGain.PrimitivePrefix
open D5.S3.Observer.CubicGain
open D5.S3.Observer.CubicGain.CommonWordSensitivity
open D5.S3.Observer.CubicGain.LegalMatrixMonoid
open FiniteDimensional
open scoped Matrix

/-- Endpoints of three actual chronological forward words, with reads only at
these endpoints. Empty words and arbitrary unread atoms are included. -/
def endpoint (w : Fin 3 → List Bool) : Fin 4 → Mat :=
  ![1, futureProduct (w 0), futureProduct (w 1) * futureProduct (w 0),
    futureProduct (w 2) * (futureProduct (w 1) * futureProduct (w 0))]

/-- Full matrix trace differences at the original three noninitial reads. -/
def prefixValue (A : Fin 4 → Mat) (X : Mat) : Fin 3 → ℝ :=
  fun i => Matrix.trace (A i.succ * X) - Matrix.trace X

/-- The determinant polar on the full real matrix space. -/
def polar (X N : Mat) : ℝ := (X + N).det - X.det - N.det

/-- The positively oriented original kernel line. In dimension two, nonzero
and determinant zero say rank one. No arithmetic or trace premise is included. -/
def OrientedKernel (A : Fin 4 → Mat) (N : Mat) : Prop :=
  N ≠ 0 ∧ N.det = 0 ∧
    (∀ X : Mat, prefixValue A X = 0 ↔ ∃ v : ℝ, X = v • N) ∧
    (∀ S : Mat, (∀ i j, 0 < S i j) → S.det = 0 → 0 < polar S N)

private theorem slope_nonneg (a b : ℝ)
    (h : ∀ x : ℝ, 0 < x → 0 ≤ a + b*x) : 0 ≤ b := by
  by_contra hn
  have hb : b < 0 := lt_of_not_ge hn
  let x := (|a| + 1) / (-b)
  have hx : 0 < x := div_pos (by positivity) (neg_pos.mpr hb)
  have he : b*x = -(|a|+1) := by
    dsimp [x]
    field_simp [ne_of_lt hb]
    <;> ring
  have hh := h x hx
  rw [he] at hh
  have ha := le_abs_self a
  linarith

private theorem affine_nonneg (a b : ℝ)
    (h : ∀ x : ℝ, 0 < x → 0 ≤ a+b*x) : 0 ≤ a ∧ 0 ≤ b := by
  refine ⟨slope_nonneg b a ?_, slope_nonneg a b h⟩
  intro x hx
  have hh := mul_nonneg hx.le (h x⁻¹ (inv_pos.mpr hx))
  have he : x * (a+b*x⁻¹) = b+a*x := by
    field_simp [ne_of_gt hx]
    <;> ring
  rwa [he] at hh

private theorem polar_expand (X N : Mat) :
    polar X N = X 1 1 * N 0 0 + X 0 0 * N 1 1 -
      X 1 0 * N 0 1 - X 0 1 * N 1 0 := by
  simp only [polar, Matrix.det_fin_two, Matrix.add_apply]
  ring

private theorem polar_signs (N : Mat)
    (h : ∀ S : Mat, (∀ i j, 0 < S i j) → S.det = 0 → 0 < polar S N) :
    0 ≤ N 0 0 ∧ 0 ≤ N 1 1 ∧ N 0 1 ≤ 0 ∧ N 1 0 ≤ 0 := by
  have hp (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
      0 ≤ N 0 0 + N 1 1*u*v - N 0 1*v - N 1 0*u := by
    have hh := h !![u*v,u;v,1]
      (by intro i j; fin_cases i <;> fin_cases j <;> simp <;> positivity)
      (by simp [Matrix.det_fin_two])
    rw [polar_expand] at hh
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      one_mul, mul_assoc] using hh.le
  have hv (v : ℝ) (hv : 0 < v) :
      0 ≤ N 0 0 - N 0 1*v ∧ 0 ≤ N 1 1*v - N 1 0 := by
    apply affine_nonneg
    intro u hu
    nlinarith [hp u v hu hv]
  have hd0 := affine_nonneg (N 0 0) (-N 0 1)
    (fun v hv0 => by simpa using (hv v hv0).1)
  have hd1 := affine_nonneg (-N 1 0) (N 1 1)
    (fun v hv0 => by linarith [(hv v hv0).2])
  exact ⟨hd0.1,hd1.2,by linarith [hd0.2],by linarith [hd1.1]⟩

private def Arithmetic (H : Mat) : Prop :=
  (∀ i j, 0 ≤ H i j ∧ ∃ z : ℤ, H i j = (z : ℝ)) ∧
    (H.det = 1 ∨ H.det = -1)

private theorem arithmetic_mul (H K : Mat) (hH : Arithmetic H)
    (hK : Arithmetic K) : Arithmetic (H*K) := by
  classical
  choose Z hZ using fun i j => (hH.1 i j).2
  choose W hW using fun i j => (hK.1 i j).2
  constructor
  · intro i j
    refine ⟨?_, ⟨(Z*W) i j, ?_⟩⟩
    · simp only [Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (hH.1 i k).1 (hK.1 k j).1
    · simp [Matrix.mul_apply, hZ, hW]
  · rw [Matrix.det_mul]
    rcases hH.2 with hh | hh <;> rcases hK.2 with hk | hk <;> simp [hh,hk]

private theorem endpoint_arithmetic (w : Fin 3 → List Bool) (i : Fin 4) :
    Arithmetic (endpoint w i) := by
  have h (j : Fin 3) : Arithmetic (futureProduct (w j)) :=
    (legal_matrix_monoid _).mp ⟨w j,rfl⟩
  fin_cases i
  · constructor
    · intro i j; fin_cases i <;> fin_cases j <;> norm_num [endpoint]
    · simp [endpoint]
  · exact h 0
  · exact arithmetic_mul _ _ (h 1) (h 0)
  · exact arithmetic_mul _ _ (h 2) (arithmetic_mul _ _ (h 1) (h 0))

private theorem triangular_diagonal (H : Mat) (hH : Arithmetic H)
    (hz : H 0 1 = 0 ∨ H 1 0 = 0) : H 0 0 = 1 ∧ H 1 1 = 1 := by
  have hd : H 0 0 * H 1 1 = 1 := by
    have hn := mul_nonneg (hH.1 0 0).1 (hH.1 1 1).1
    rcases hz with hz | hz <;> rcases hH.2 with hd | hd <;>
      simp [Matrix.det_fin_two,hz] at hd <;> linarith
  obtain ⟨a,ha⟩ := (hH.1 0 0).2
  obtain ⟨b,hb⟩ := (hH.1 1 1).2
  have han : (0 : ℤ) ≤ a := by exact_mod_cast (ha ▸ (hH.1 0 0).1)
  have hbn : (0 : ℤ) ≤ b := by exact_mod_cast (hb ▸ (hH.1 1 1).1)
  have hab : a*b = 1 := by rw [ha,hb] at hd; exact_mod_cast hd
  have hap : 1 ≤ a := by by_contra h; have : a = 0 := by omega; simp [this] at hab
  have hbp : 1 ≤ b := by by_contra h; have : b = 0 := by omega; simp [this] at hab
  have haa : a = 1 := by nlinarith
  have hbb : b = 1 := by nlinarith
  simpa [ha,hb,haa,hbb]

private theorem signs_trace (A : Fin 4 → Mat) (hA : ∀ i, Arithmetic (A i))
    (N : Mat) (hN : OrientedKernel A N) :
    0 ≤ N 0 0 ∧ 0 ≤ N 1 1 ∧ N 0 1 ≤ 0 ∧ N 1 0 ≤ 0 ∧
      0 < Matrix.trace N := by
  obtain ⟨hn,hd,hker,hpol⟩ := hN
  obtain ⟨h00,h11,h01,h10⟩ := polar_signs N hpol
  refine ⟨h00,h11,h01,h10,?_⟩
  have hnk : prefixValue A N = 0 := (hker N).mpr ⟨1,by simp⟩
  by_contra ht
  have htr : Matrix.trace N = N 0 0 + N 1 1 := by
    simp [Matrix.trace,Matrix.diag,Fin.sum_univ_two]
  have hd0 : N 0 0 = 0 := by linarith
  have hd1 : N 1 1 = 0 := by linarith
  have hoff : N 0 1 = 0 ∨ N 1 0 = 0 := by
    simpa [Matrix.det_fin_two,hd0,hd1,mul_eq_zero] using hd
  have hdiag (i : Fin 3) : A i.succ 0 0 = 1 ∧ A i.succ 1 1 = 1 := by
    have he := congrFun hnk i
    simp only [prefixValue,Matrix.trace,Matrix.diag,Matrix.mul_apply,
      Fin.sum_univ_two,hd0,hd1,mul_zero,zero_add,add_zero,Pi.zero_apply] at he
    apply triangular_diagonal _ (hA i.succ)
    rcases hoff with h | h
    · have hg : N 1 0 ≠ 0 := by
        intro hg; apply hn; ext i j
        fin_cases i <;> fin_cases j <;> simp [hd0,hd1,h,hg]
      right
      apply (mul_eq_zero.mp he).resolve_right hg
    · have hg : N 0 1 ≠ 0 := by
        intro hg; apply hn; ext i j
        fin_cases i <;> fin_cases j <;> simp [hd0,hd1,h,hg]
      left
      have he' : A i.succ 1 0 * N 0 1 = 0 := by simpa [h] using he
      exact (mul_eq_zero.mp he').resolve_right hg
  have hex : prefixValue A !![1,0;0,0] = 0 := by
    ext i
    simp [prefixValue,Matrix.trace,Matrix.diag,Matrix.mul_apply,
      Fin.sum_univ_two,(hdiag i).1]
  obtain ⟨v,hv⟩ := (hker _).mp hex
  have he := congrArg (fun X : Mat => X 0 0) hv
  simp [hd0] at he

/-- The original quotient as a linear map on full matrices. -/
def prefixMap (A : Fin 4 → Mat) : Mat →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun := prefixValue A
  map_add' X Y := by
    ext i
    simp [prefixValue,Matrix.mul_add,Matrix.trace_add]
    <;> ring
  map_smul' c X := by
    ext i
    simp [prefixValue,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]
    <;> ring

private theorem kernel_rank (A : Fin 4 → Mat) (N : Mat)
    (hN : OrientedKernel A N) :
    Module.finrank ℝ (LinearMap.range (prefixMap A)) = 3 := by
  have hk : LinearMap.ker (prefixMap A) = Submodule.span ℝ {N} := by
    ext X
    simp only [LinearMap.mem_ker,Submodule.mem_span_singleton]
    change (prefixValue A X = 0) ↔ _
    rw [hN.2.2.1 X]
    exact exists_congr fun v => eq_comm
  have hh := (prefixMap A).finrank_range_add_finrank_ker
  rw [hk,finrank_span_singleton hN.1] at hh
  have hdim : Module.finrank ℝ Mat = 4 := by
    simp [Mat,Matrix,Module.finrank_pi]
  omega

private def flatten (N : Mat) : Fin 4 → ℝ := ![N 0 0,N 0 1,N 1 0,N 1 1]
private def unflatten {R : Type*} (v : Fin 4 → R) : Matrix (Fin 2) (Fin 2) R :=
  !![v 0,v 1;v 2,v 3]

private def coefficients {R : Type*} [Ring R]
    (A : Fin 4 → Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 4) R :=
  fun i => ![A i.succ 0 0-1,A i.succ 1 0,A i.succ 0 1,A i.succ 1 1-1]

private theorem coefficients_value (A : Fin 4 → Mat) (N : Mat) :
    coefficients A *ᵥ flatten N = prefixValue A N := by
  ext i
  simp [coefficients,flatten,prefixValue,Matrix.trace,Matrix.diag,
    Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_succ]
  <;> ring

private def traceAugment {R : Type*} [Ring R]
    (B : Matrix (Fin 3) (Fin 4) R) : Matrix (Fin 4) (Fin 4) R :=
  Fin.cases ![1,0,0,1] B

private theorem traceAugment_det (A : Fin 4 → Mat) (N : Mat)
    (hN : OrientedKernel A N) (ht : 0 < Matrix.trace N) :
    (traceAugment (coefficients A)).det ≠ 0 := by
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_col
  apply Matrix.mulVec_injective_iff.mp
  intro x y hxy
  suffices hzero : ∀ z : Fin 4 → ℝ,
      traceAugment (coefficients A) *ᵥ z = 0 → z = 0 by
    exact sub_eq_zero.mp (hzero (x-y) (by rw [Matrix.mulVec_sub,hxy,sub_self]))
  intro z hz
  have hp : prefixValue A (unflatten z) = 0 := by
    have hf : flatten (unflatten z) = z := by ext j; fin_cases j <;> rfl
    rw [← coefficients_value,hf]
    ext i
    exact congrFun hz i.succ
  obtain ⟨v,hv⟩ := (hN.2.2.1 _).mp hp
  have htr : Matrix.trace (unflatten z) = 0 := by
    have he := congrFun hz 0
    simpa [traceAugment,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      unflatten,Matrix.trace,Matrix.diag,Fin.sum_univ_two] using he
  rw [hv,Matrix.trace_smul,smul_eq_mul] at htr
  have hv0 : v = 0 := (mul_eq_zero.mp htr).resolve_right (ne_of_gt ht)
  have hmat : unflatten z = 0 := by simpa [hv0] using hv
  have hflat := congrArg flatten hmat
  ext j
  fin_cases j <;> simpa [flatten,unflatten] using congrFun hflat _

private theorem trace_cofactor (B : Matrix (Fin 3) (Fin 4) ℤ) :
    (D5.S3.Arith.Lattices.CofactorKernel.cofactor B) 0 +
      (D5.S3.Arith.Lattices.CofactorKernel.cofactor B) 3 =
        (traceAugment B).det := by
  symm
  rw [Matrix.det_succ_row_zero]
  simp [traceAugment,D5.S3.Arith.Lattices.CofactorKernel.cofactor,
    Matrix.submatrix,Fin.sum_univ_succ]

private theorem integer_oriented_kernel (w : Fin 3 → List Bool)
    (N : Mat) (hN : OrientedKernel (endpoint w) N) :
    ∃ (K : Matrix (Fin 2) (Fin 2) ℤ) (v : ℝ),
      0 < v ∧ K.map (Int.castRingHom ℝ) = v • N := by
  classical
  have hs := signs_trace (endpoint w) (endpoint_arithmetic w) N hN
  have hnonsing := traceAugment_det (endpoint w) N hN hs.2.2.2.2
  choose Z hZ using fun i j k => ((endpoint_arithmetic w i).1 j k).2
  let B := coefficients Z
  have hB : B.map (Int.castRingHom ℝ) = coefficients (endpoint w) := by
    ext i j
    fin_cases j <;> simp [B,coefficients,hZ]
  let C := D5.S3.Arith.Lattices.CofactorKernel.cofactor B
  have hc : B *ᵥ C = 0 :=
    D5.S3.Arith.Lattices.CofactorKernel.cofactor_mulVec_eq_zero B
  have hcr : coefficients (endpoint w) *ᵥ (fun j => (C j : ℝ)) = 0 := by
    rw [← hB]
    ext i
    have he := RingHom.map_mulVec (Int.castRingHom ℝ) B C i
    simpa [hc] using he.symm
  let K : Matrix (Fin 2) (Fin 2) ℤ := unflatten C
  have hk : prefixValue (endpoint w) (K.map (Int.castRingHom ℝ)) = 0 := by
    rw [← coefficients_value]
    have hf : flatten (K.map (Int.castRingHom ℝ)) = (fun j => (C j : ℝ)) := by
      ext j; fin_cases j <;> rfl
    rwa [hf]
  obtain ⟨v,hv⟩ := (hN.2.2.1 _).mp hk
  have hvn : v ≠ 0 := by
    intro hz
    have hzK : K.map (Int.castRingHom ℝ) = 0 := by simpa [hz] using hv
    have h0 := congrArg (fun X : Mat => X 0 0) hzK
    have h3 := congrArg (fun X : Mat => X 1 1) hzK
    have hdet : (traceAugment B).det = 0 := by
      rw [← trace_cofactor]
      change C 0 + C 3 = 0
      have hc0 : C 0 = 0 := by exact_mod_cast h0
      have hc3 : C 3 = 0 := by exact_mod_cast h3
      simp [hc0,hc3]
    apply hnonsing
    have ht : (traceAugment B).map (Int.castRingHom ℝ) =
        traceAugment (coefficients (endpoint w)) := by
      ext i j
      refine Fin.cases ?_ (fun i => ?_) i
      · fin_cases j <;> simp [traceAugment]
      · exact congrFun (congrFun hB i) j
    rw [← ht,← RingHom.map_det]
    simp [hdet]
  rcases lt_or_gt_of_ne hvn with hvn | hvn
  · refine ⟨-K,-v,neg_pos.mpr hvn,?_⟩
    simp only [Matrix.map_neg,hv,neg_smul]
  · exact ⟨K,v,hvn,hv⟩

private theorem pair_gcd (a b : ℤ) (hg : Int.gcd a b = 1) :
    Finset.univ.gcd (![a,b] : Fin 2 → ℤ) = 1 := by
  have ha : Finset.univ.gcd (![a,b] : Fin 2 → ℤ) ∣ a :=
    Finset.gcd_dvd (Finset.mem_univ (0 : Fin 2))
  have hb : Finset.univ.gcd (![a,b] : Fin 2 → ℤ) ∣ b :=
    Finset.gcd_dvd (Finset.mem_univ (1 : Fin 2))
  have he := Int.gcd_eq_gcd_ab a b
  rw [hg] at he
  have hd : Finset.univ.gcd (![a,b] : Fin 2 → ℤ) ∣ 1 := by
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_left hb _)
  have hh := normalize_eq_one.mpr (isUnit_iff_dvd_one.mpr hd)
  simpa only [Finset.normalize_gcd] using hh

private theorem pair_span (a b x y : ℤ) (hs : 0 < a+b)
    (hg : Int.gcd a b = 1) (he : b*x = a*y) :
    ∃ z : ℤ, x=z*a ∧ y=z*b := by
  let B : Matrix (Fin 1) (Fin 2) ℤ := !![b,-a]
  have hdet : (D5.S3.Arith.Lattices.CofactorKernel.augment B).det ≠ 0 := by
    simp [D5.S3.Arith.Lattices.CofactorKernel.augment,B,Matrix.det_fin_two]
    <;> omega
  have hker : B *ᵥ (![a,b] : Fin 2 → ℤ) = 0 := by
    ext i; fin_cases i
    simp [B,Matrix.mulVec,dotProduct,Fin.sum_univ_two,mul_comm]
  have hxy : B *ᵥ (![x,y] : Fin 2 → ℤ) = 0 := by
    ext i; fin_cases i
    simp [B,Matrix.mulVec,dotProduct,Fin.sum_univ_two,he]
  obtain ⟨z,hz⟩ := D5.S3.Arith.Lattices.CofactorKernel.primitive_kernel_span
    B hdet ![a,b] hker (by simpa [Fin.sum_univ_two] using ne_of_gt hs)
    (pair_gcd a b hg) ![x,y] hxy
  exact ⟨z,hz 0,hz 1⟩

private theorem primitive_pair (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hn : x ≠ 0 ∨ y ≠ 0) :
    ∃ (a b g : ℤ), 0 ≤ a ∧ 0 ≤ b ∧ 0 < g ∧ Int.gcd a b = 1 ∧
      0 < a+b ∧ x=g*a ∧ y=g*b := by
  have hgcd : 0 < Int.gcd x y := Int.gcd_pos_iff.mpr hn
  obtain ⟨g,a,b,hg,hprim,ha,hb⟩ := Int.exists_gcd_one' hgcd
  have hgr : (0 : ℤ) < g := by exact_mod_cast hg
  have hap : 0 ≤ a := nonneg_of_mul_nonneg_right (ha ▸ hx) hgr
  have hbp : 0 ≤ b := nonneg_of_mul_nonneg_right (hb ▸ hy) hgr
  have hsum : 0 < a+b := by
    by_contra hh
    have haa : a=0 := by omega
    have hbb : b=0 := by omega
    rcases hn with hn | hn <;> simp [ha,hb,haa,hbb] at hn
  exact ⟨a,b,g,hap,hbp,hgr,hprim,hsum,by simpa [mul_comm] using ha,
    by simpa [mul_comm] using hb⟩

private theorem nonnegative_rank_one_factor (P Q R S : ℤ)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hdet : P*S = Q*R) (ht : 0 < P+S) :
    ∃ (a b c d g : ℤ),
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 < g ∧
      Int.gcd a b = 1 ∧ Int.gcd c d = 1 ∧ 0 < a*c+b*d ∧
      P=g*(a*c) ∧ Q=g*(a*d) ∧ R=g*(b*c) ∧ S=g*(b*d) := by
  by_cases hn : P ≠ 0 ∨ R ≠ 0
  · obtain ⟨a,b,u,ha,hb,hu,hab,hs,hPu,hRu⟩ := primitive_pair P R hP hR hn
    have hparallel : b*Q = a*S := by
      apply mul_left_cancel₀ (ne_of_gt hu)
      rw [hPu,hRu] at hdet
      nlinarith [hdet]
    obtain ⟨v,hQv,hSv⟩ := pair_span a b Q S hs hab hparallel
    have hv : 0 ≤ v := by
      by_cases hap : a=0
      · have hbp : 0 < b := by omega
        rw [hSv] at hS
        exact nonneg_of_mul_nonneg_right hS hbp
      · have hapos : 0 < a := by omega
        rw [hQv] at hQ
        exact nonneg_of_mul_nonneg_right hQ hapos
    obtain ⟨c,d,g,hc,hd,hg,hcd,hsc,huc,hvd⟩ :=
      primitive_pair u v hu.le hv (Or.inl (ne_of_gt hu))
    refine ⟨a,b,c,d,g,ha,hb,hc,hd,hg,hab,hcd,?_,?_,?_,?_,?_⟩
    · have hh : 0 < g*(a*c+b*d) := by nlinarith [ht]
      exact pos_of_mul_pos_left hh hg.le
    · rw [hPu,huc]; ring
    · rw [hQv,hvd]; ring
    · rw [hRu,huc]; ring
    · rw [hSv,hvd]; ring
  · push_neg at hn
    obtain ⟨hP0,hR0⟩ := hn
    obtain ⟨a,b,g,ha,hb,hg,hab,hs,hQa,hSb⟩ :=
      primitive_pair Q S hQ hS (Or.inr (by omega))
    refine ⟨a,b,0,1,g,ha,hb,by omega,by omega,hg,hab,by norm_num,?_,?_,?_,?_,?_⟩
    · have : 0 < S := by omega
      rw [hSb] at this
      simpa using pos_of_mul_pos_left this hg.le
    · simp [hP0]
    · simpa using hQa
    · simp [hR0]
    · simpa using hSb

end D5.S3.Observer.CubicGain.PrimitivePrefix
