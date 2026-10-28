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
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.Tactic

/-! Primitive signed levels for the original native cumulative prefix. -/

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
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,one_mul] at hh
    nlinarith [hh]
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
    refine ⟨?_, ⟨∑ k, Z i k * W k j, ?_⟩⟩
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
    · intro i j
      change 0 ≤ (1 : Mat) i j ∧ ∃ z : ℤ, (1 : Mat) i j = (z : ℝ)
      by_cases hij : i = j
      · subst j
        exact ⟨by simp, 1, by simp⟩
      · exact ⟨by simp [hij], 0, by simp [hij]⟩
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
  have hap : 1 ≤ a := by
    by_contra h
    have haa : a = 0 := by omega
    simp [haa] at hab
  have hbp : 1 ≤ b := by
    by_contra h
    have hbb : b = 0 := by omega
    simp [hbb] at hab
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
      left
      have he' : A i.succ 0 1 * N 1 0 = 0 := by simpa [h] using he
      exact (mul_eq_zero.mp he').resolve_right hg
    · have hg : N 0 1 ≠ 0 := by
        intro hg; apply hn; ext i j
        fin_cases i <;> fin_cases j <;> simp [hd0,hd1,h,hg]
      right
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
    calc
      Module.finrank ℝ Mat = Fintype.card (Fin 2) * Fintype.card (Fin 2) *
          Module.finrank ℝ ℝ := Module.finrank_matrix (R := ℝ) (M := ℝ) (Fin 2) (Fin 2)
      _ = 4 := by norm_num
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
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,traceAugment,Fin.cases_zero,
      unflatten,Matrix.trace,Matrix.diag,Fin.sum_univ_two] using he
  rw [hv,Matrix.trace_smul,smul_eq_mul] at htr
  have hv0 : v = 0 := (mul_eq_zero.mp htr).resolve_right (ne_of_gt ht)
  have hmat : unflatten z = 0 := by simpa [hv0] using hv
  have hflat := congrArg flatten hmat
  have hf : flatten (unflatten z) = z := by ext j; fin_cases j <;> rfl
  have hz0 : flatten (0 : Mat) = 0 := by ext j; fin_cases j <;> rfl
  rwa [hf,hz0] at hflat

private theorem trace_cofactor (B : Matrix (Fin 3) (Fin 4) ℤ) :
    (D5.S3.Arith.Lattices.CofactorKernel.cofactor B) 0 +
      (D5.S3.Arith.Lattices.CofactorKernel.cofactor B) 3 =
        (traceAugment B).det := by
  symm
  rw [Matrix.det_succ_row_zero]
  have hsub (j : Fin 4) :
      (traceAugment B).submatrix Fin.succ j.succAbove = B.submatrix id j.succAbove := rfl
  simp only [hsub,traceAugment,Fin.cases_zero]
  norm_num [D5.S3.Arith.Lattices.CofactorKernel.cofactor,Fin.sum_univ_succ]

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
    simpa [hc,Function.comp_def] using he.symm
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
    change (C 0:ℝ)=0 at h0
    change (C 3:ℝ)=0 at h3
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
      · change (Int.castRingHom ℝ) ((![1,0,0,1] : Fin 4 → ℤ) j) =
          (![1,0,0,1] : Fin 4 → ℝ) j
        fin_cases j <;> norm_num
      · exact congrFun (congrFun hB i) j
    rw [← ht]
    change ((traceAugment B).map (fun z : ℤ => (z:ℝ))).det=0
    rw [← Int.cast_det,hdet,Int.cast_zero]
  rcases lt_or_gt_of_ne hvn with hvn | hvn
  · refine ⟨-K,-v,neg_pos.mpr hvn,?_⟩
    have hneg : (-K).map (Int.castRingHom ℝ) = -(K.map (Int.castRingHom ℝ)) := by
      ext i j
      change ((-K i j:ℤ):ℝ) = -(K i j:ℝ)
      simp
    rw [hneg,hv,neg_smul]
  · exact ⟨K,v,hvn,hv⟩

private theorem pair_gcd (a b : ℤ) (hg : Int.gcd a b = 1) :
    Finset.univ.gcd (![a,b] : Fin 2 → ℤ) = 1 := by
  have ha : Finset.univ.gcd (![a,b] : Fin 2 → ℤ) ∣ a :=
    Finset.gcd_dvd (Finset.mem_univ (0 : Fin 2))
  have hb : Finset.univ.gcd (![a,b] : Fin 2 → ℤ) ∣ b :=
    Finset.gcd_dvd (Finset.mem_univ (1 : Fin 2))
  have he := Int.gcd_eq_gcd_ab a b
  rw [hg] at he
  norm_num only [Int.cast_one] at he
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
    have he : D5.S3.Arith.Lattices.CofactorKernel.augment B = !![1,1;b,-a] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [he,Matrix.det_fin_two]
    simp
    omega
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
  have hap : 0 ≤ a := nonneg_of_mul_nonneg_left (ha ▸ hx) hgr
  have hbp : 0 ≤ b := nonneg_of_mul_nonneg_left (hb ▸ hy) hgr
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
        exact nonneg_of_mul_nonneg_left hS hbp
      · have hapos : 0 < a := by omega
        rw [hQv] at hQ
        exact nonneg_of_mul_nonneg_left hQ hapos
    obtain ⟨c,d,g,hc,hd,hg,hcd,hsc,huc,hvd⟩ :=
      primitive_pair u v hu.le hv (Or.inl (ne_of_gt hu))
    refine ⟨a,b,c,d,g,ha,hb,hc,hd,hg,hab,hcd,?_,?_,?_,?_,?_⟩
    · rw [hPu,hSv,huc,hvd] at ht
      have hh : 0 < g*(a*c+b*d) := by nlinarith [ht]
      exact pos_of_mul_pos_right hh hg.le
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
      simpa using pos_of_mul_pos_right this hg.le
    · simp [hP0]
    · simpa using hQa
    · simp [hR0]
    · simpa using hSb

/-- The auxiliary signed outer product; it is not an actual positive source. -/
def signedMatrix (a b c d : ℤ) : Mat :=
  !![(a:ℝ)*(c:ℝ),-(a:ℝ)*(d:ℝ);-(b:ℝ)*(c:ℝ),(b:ℝ)*(d:ℝ)]

private theorem primitive_generator (w : Fin 3 → List Bool)
    (N : Mat) (hN : OrientedKernel (endpoint w) N) :
    ∃ (a b c d : ℤ) (s : ℝ),
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
      Int.gcd a b = 1 ∧ Int.gcd c d = 1 ∧ 0 < a*c+b*d ∧
      0 < s ∧ N = s • signedMatrix a b c d := by
  obtain ⟨K,v,hv,hK⟩ := integer_oriented_kernel w N hN
  obtain ⟨hn00,hn11,hn01,hn10,hntr⟩ :=
    signs_trace (endpoint w) (endpoint_arithmetic w) N hN
  have he (i j : Fin 2) : (K i j : ℝ) = v*N i j := congrArg (fun X : Mat => X i j) hK
  have hp : (0 : ℤ) ≤ K 0 0 := by
    exact_mod_cast (by rw [he]; exact mul_nonneg hv.le hn00 : (0:ℝ) ≤ (K 0 0:ℝ))
  have hq : (0 : ℤ) ≤ -K 0 1 := by
    exact_mod_cast (by rw [Int.cast_neg,he]; nlinarith : (0:ℝ) ≤ (-K 0 1:ℤ))
  have hr : (0 : ℤ) ≤ -K 1 0 := by
    exact_mod_cast (by rw [Int.cast_neg,he]; nlinarith : (0:ℝ) ≤ (-K 1 0:ℤ))
  have hs : (0 : ℤ) ≤ K 1 1 := by
    exact_mod_cast (by rw [he]; exact mul_nonneg hv.le hn11 : (0:ℝ) ≤ (K 1 1:ℝ))
  have hdetK : K.det = 0 := by
    have hd : (K.det : ℝ) = 0 := by
      rw [Int.cast_det]
      change (K.map (Int.castRingHom ℝ)).det = 0
      rw [hK,Matrix.det_smul,hN.2.1,mul_zero]
    exact_mod_cast hd
  have hdet : K 0 0 * K 1 1 = (-K 0 1)*(-K 1 0) := by
    simp only [Matrix.det_fin_two] at hdetK
    nlinarith
  have ht : (0 : ℤ) < K 0 0 + K 1 1 := by
    have hh : (0:ℝ) < (K 0 0:ℝ)+(K 1 1:ℝ) := by
      rw [he,he]
      have htr : Matrix.trace N = N 0 0 + N 1 1 := by
        simp [Matrix.trace,Matrix.diag,Fin.sum_univ_two]
      rw [htr] at hntr
      nlinarith [mul_pos hv hntr]
    exact_mod_cast hh
  obtain ⟨a,b,c,d,g,ha,hb,hc,hd,hg,hab,hcd,ht,hP,hQ,hR,hS⟩ :=
    nonnegative_rank_one_factor (K 0 0) (-K 0 1) (-K 1 0) (K 1 1)
      hp hq hr hs hdet ht
  have hfactor : K.map (Int.castRingHom ℝ) = (g:ℝ) • signedMatrix a b c d := by
    ext i j
    fin_cases i <;> fin_cases j
    · change (K 0 0 : ℝ) = (g:ℝ) * ((a:ℝ)*(c:ℝ))
      exact_mod_cast hP
    · change (K 0 1 : ℝ) = (g:ℝ) * (-(a:ℝ)*(d:ℝ))
      have hh : (K 0 1 : ℝ) = -((g:ℝ)*((a:ℝ)*(d:ℝ))) := by
        exact_mod_cast (show K 0 1 = -(g*(a*d)) by omega)
      nlinarith [hh]
    · change (K 1 0 : ℝ) = (g:ℝ) * (-(b:ℝ)*(c:ℝ))
      have hh : (K 1 0 : ℝ) = -((g:ℝ)*((b:ℝ)*(c:ℝ))) := by
        exact_mod_cast (show K 1 0 = -(g*(b*c)) by omega)
      nlinarith [hh]
    · change (K 1 1 : ℝ) = (g:ℝ) * ((b:ℝ)*(d:ℝ))
      exact_mod_cast hS
  refine ⟨a,b,c,d,(g:ℝ)/v,ha,hb,hc,hd,hab,hcd,ht,
    div_pos (by exact_mod_cast hg) hv,?_⟩
  rw [hfactor] at hK
  ext i j
  have hh := congrArg (fun X : Mat => X i j) hK
  simp only [Matrix.smul_apply,smul_eq_mul] at hh ⊢
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (ne_of_gt hv)).mpr
  nlinarith [hh]

/-- Every retained endpoint has an integer level on the primitive lattice line. -/
def HasLevels (w : Fin 3 → List Bool) (a b c d : ℤ) (m : Fin 4 → ℤ) : Prop :=
  m 0 = 0 ∧ ∀ i : Fin 4,
    endpoint w i *ᵥ (![(a:ℝ),-(b:ℝ)] : Fin 2 → ℝ) =
      ![(a:ℝ),-(b:ℝ)] + (m i:ℝ) • ![(d:ℝ),(c:ℝ)]

private theorem primitive_levels (w : Fin 3 → List Bool) (N : Mat)
    (hN : OrientedKernel (endpoint w) N) (a b c d : ℤ) (s : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : Int.gcd c d = 1)
    (ht : 0 < a*c+b*d) (hs : 0 < s)
    (hgen : N = s • signedMatrix a b c d) :
    ∃ m : Fin 4 → ℤ, HasLevels w a b c d m := by
  classical
  have hsum : 0 < c+d := by
    by_contra hh
    have hc0 : c=0 := by omega
    have hd0 : d=0 := by omega
    simp [hc0,hd0] at ht
  have hk : prefixValue (endpoint w) (signedMatrix a b c d) = 0 := by
    apply (hN.2.2.1 _).mpr
    refine ⟨s⁻¹,?_⟩
    rw [hgen,smul_smul,inv_mul_cancel₀ (ne_of_gt hs),one_smul]
  have htrace (i : Fin 4) :
      Matrix.trace (endpoint w i * signedMatrix a b c d) -
        Matrix.trace (signedMatrix a b c d) = 0 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [endpoint]
    · exact congrFun hk j
  choose Z hZ using fun i j k => ((endpoint_arithmetic w i).1 j k).2
  have hsat (i : Fin 4) : ∃ z : ℤ,
      Z i 0 0*a+Z i 0 1*(-b)-a=z*d ∧
      Z i 1 0*a+Z i 1 1*(-b)+b=z*c := by
    have hh := htrace i
    simp only [signedMatrix,Matrix.trace,Matrix.diag,Matrix.mul_apply,
      Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.of_apply] at hh
    simp only [hZ] at hh
    have hr : (c:ℝ)*((Z i 0 0:ℝ)*(a:ℝ)+(Z i 0 1:ℝ)*(-(b:ℝ))-(a:ℝ)) =
        (d:ℝ)*((Z i 1 0:ℝ)*(a:ℝ)+(Z i 1 1:ℝ)*(-(b:ℝ))+(b:ℝ)) := by
      nlinarith [hh]
    have hi : c*(Z i 0 0*a+Z i 0 1*(-b)-a) =
        d*(Z i 1 0*a+Z i 1 1*(-b)+b) := by exact_mod_cast hr
    exact pair_span d c _ _ (by omega) (by simpa [Int.gcd_comm] using hcd) hi
  choose m hm using hsat
  have hlevels (i : Fin 4) :
      endpoint w i *ᵥ (![(a:ℝ),-(b:ℝ)] : Fin 2 → ℝ) =
        ![(a:ℝ),-(b:ℝ)] + (m i:ℝ) • ![(d:ℝ),(c:ℝ)] := by
    ext j
    fin_cases j
    · have hh : (Z i 0 0:ℝ)*(a:ℝ)+(Z i 0 1:ℝ)*(-(b:ℝ))-(a:ℝ)=
          (m i:ℝ)*(d:ℝ) := by exact_mod_cast (hm i).1
      norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_two,hZ]
      linarith [hh]
    · have hh : (Z i 1 0:ℝ)*(a:ℝ)+(Z i 1 1:ℝ)*(-(b:ℝ))+(b:ℝ)=
          (m i:ℝ)*(c:ℝ) := by exact_mod_cast (hm i).2
      norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_two,hZ]
      linarith [hh]
  refine ⟨m,?_,hlevels⟩
  have h0 := congrFun (hlevels 0) 0
  have h1 := congrFun (hlevels 0) 1
  simp [endpoint] at h0 h1
  by_contra hm0
  have hd0 := h0.resolve_left hm0
  have hc0 := h1.resolve_left hm0
  omega

/-- Nonnegative primitive pairs include every zero-component case. -/
def PrimitiveParameters (a b c d : ℤ) : Prop :=
  0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ Int.gcd a b = 1 ∧
    Int.gcd c d = 1 ∧ 0 < a*c+b*d

private theorem levels_converse (w : Fin 3 → List Bool) (N : Mat)
    (a b c d : ℤ) (s : ℝ) (m : Fin 4 → ℤ)
    (hpar : PrimitiveParameters a b c d) (hs : 0 < s)
    (hgen : N = s • signedMatrix a b c d) (hlev : HasLevels w a b c d m)
    (hrank : Module.finrank ℝ (LinearMap.range (prefixMap (endpoint w))) = 3) :
    OrientedKernel (endpoint w) N := by
  obtain ⟨ha,hb,hc,hd,hab,hcd,ht⟩ := hpar
  have ht' : (0:ℝ) < (a:ℝ)*(c:ℝ)+(b:ℝ)*(d:ℝ) := by exact_mod_cast ht
  have htrace : Matrix.trace N = s*((a:ℝ)*(c:ℝ)+(b:ℝ)*(d:ℝ)) := by
    rw [hgen,Matrix.trace_smul]
    simp [signedMatrix,Matrix.trace,Matrix.diag,Fin.sum_univ_two,smul_eq_mul]
  have hn : N ≠ 0 := by
    intro hz
    have hpos := mul_pos hs ht'
    rw [hz,Matrix.trace_zero] at htrace
    linarith [htrace]
  have hdet : N.det = 0 := by
    rw [hgen,Matrix.det_smul]
    have hp : (signedMatrix a b c d).det = 0 := by
      simp [signedMatrix,Matrix.det_fin_two]
      <;> ring
    simp [hp]
  have hker : prefixValue (endpoint w) N = 0 := by
    have hpker : prefixValue (endpoint w) (signedMatrix a b c d) = 0 := by
      ext i
      have h0 := congrFun (hlev.2 i.succ) 0
      have h1 := congrFun (hlev.2 i.succ) 1
      simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.add_apply,
        Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.of_apply] at h0 h1
      simp only [prefixValue,signedMatrix,Matrix.trace,Matrix.diag,Matrix.mul_apply,
        Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.of_apply,Pi.zero_apply]
      linear_combination (c:ℝ)*h0-(d:ℝ)*h1
    change prefixMap (endpoint w) N = 0
    rw [hgen,LinearMap.map_smul]
    change s • prefixValue (endpoint w) (signedMatrix a b c d) = 0
    rw [hpker,smul_zero]
  have hdim := (prefixMap (endpoint w)).finrank_range_add_finrank_ker
  have hfour : Module.finrank ℝ Mat = 4 := by
    calc
      Module.finrank ℝ Mat = Fintype.card (Fin 2) * Fintype.card (Fin 2) *
          Module.finrank ℝ ℝ := Module.finrank_matrix (R := ℝ) (M := ℝ) (Fin 2) (Fin 2)
      _ = 4 := by norm_num
  have hkerdim : Module.finrank ℝ (LinearMap.ker (prefixMap (endpoint w))) = 1 := by omega
  have hkspan := eq_span_singleton_of_mem_of_finrank_eq_one hkerdim hker hn
  refine ⟨hn,hdet,?_,?_⟩
  · intro X
    change X ∈ LinearMap.ker (prefixMap (endpoint w)) ↔ _
    rw [hkspan,Submodule.mem_span_singleton]
    exact exists_congr fun v => eq_comm
  · intro S hS _
    rw [hgen,polar_expand]
    simp only [Matrix.smul_apply,smul_eq_mul,signedMatrix,Matrix.of_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    have hap : (0:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
    have hbp : (0:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
    have hcp : (0:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
    have hdp : (0:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have hcross0 : 0 ≤ (b:ℝ)*(c:ℝ)*S 0 1 :=
      mul_nonneg (mul_nonneg hbp hcp) (hS 0 1).le
    have hcross1 : 0 ≤ (a:ℝ)*(d:ℝ)*S 1 0 :=
      mul_nonneg (mul_nonneg hap hdp) (hS 1 0).le
    have hdiagonal : 0 < (a:ℝ)*(c:ℝ)*S 1 1 + (b:ℝ)*(d:ℝ)*S 0 0 := by
      by_cases hac : (a:ℝ)*(c:ℝ)=0
      · have hbd : 0 < (b:ℝ)*(d:ℝ) := by linarith
        have hh := mul_pos hbd (hS 0 0)
        simpa [hac] using hh
      · have hacpos : 0 < (a:ℝ)*(c:ℝ) := lt_of_le_of_ne (mul_nonneg hap hcp) (Ne.symm hac)
        exact add_pos_of_pos_of_nonneg (mul_pos hacpos (hS 1 1))
          (mul_nonneg (mul_nonneg hbp hdp) (hS 0 0).le)
    have hpos := mul_pos hs (add_pos_of_pos_of_nonneg hdiagonal
      (add_nonneg hcross0 hcross1))
    nlinarith [hpos]

/-- Exact primitive representation on actual cumulative native histories.
The scale retains every positively oriented input generator. -/
theorem whole_word_primitive_representation (w : Fin 3 → List Bool) (N : Mat) :
    OrientedKernel (endpoint w) N ↔
      Module.finrank ℝ (LinearMap.range (prefixMap (endpoint w))) = 3 ∧
      ∃ (a b c d : ℤ) (s : ℝ) (m : Fin 4 → ℤ),
        PrimitiveParameters a b c d ∧ 0 < s ∧
        N = s • signedMatrix a b c d ∧ HasLevels w a b c d m := by
  constructor
  · intro hN
    obtain ⟨a,b,c,d,s,ha,hb,hc,hd,hab,hcd,ht,hs,hgen⟩ := primitive_generator w N hN
    obtain ⟨m,hm⟩ := primitive_levels w N hN a b c d s hc hd hcd ht hs hgen
    exact ⟨kernel_rank _ _ hN,a,b,c,d,s,m,⟨ha,hb,hc,hd,hab,hcd,ht⟩,hs,hgen,hm⟩
  · rintro ⟨hrank,a,b,c,d,s,m,hpar,hs,hgen,hlev⟩
    exact levels_converse w N a b c d s m hpar hs hgen hlev hrank

#print axioms whole_word_primitive_representation

end D5.S3.Observer.CubicGain.PrimitivePrefix
