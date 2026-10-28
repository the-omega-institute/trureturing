/- GID: D5/S3/Observer/CubicGain/PrimitiveKernelLattice
   generality: I
   mirror-B: D5/B/S3/Observer/CubicGain/PrimitiveKernelLattice
   mirror-E: none(waiver:whole-class-primitive-kernel-lattice)
   anchors: [mathlib/module/Mathlib.RingTheory.Localization.Integer, mathlib/module/Mathlib.Data.Int.GCD]
   utility: none
   digest: Primitive signed integer kernel levels on actual cumulative native prefixes. -/

import D5.S3.Observer.CubicGain.PrefixKernelSigns
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Data.Int.GCD

/-! The primitive arithmetic of the original whole prefix class. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.CubicGain.PrimitiveKernelLattice

open D5.S3.Observer.CubicGain
open D5.S3.Observer.CubicGain.CommonWordSensitivity
open D5.S3.Observer.CubicGain.LegalMatrixMonoid
open D5.S3.Observer.CubicGain.PrefixKernelSigns
open scoped Matrix

/-- Primitive nonnegative coordinates; zero coordinates remain allowed. -/
structure PrimitiveCoordinates where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  column_primitive : a.Coprime b
  row_primitive : c.Coprime d
  trace_pos : 0 < a * c + b * d

namespace PrimitiveCoordinates

def column (p : PrimitiveCoordinates) : Fin 2 → ℝ := ![(p.a : ℝ), -(p.b : ℝ)]
def row (p : PrimitiveCoordinates) : Fin 2 → ℝ := ![(p.c : ℝ), -(p.d : ℝ)]
def direction (p : PrimitiveCoordinates) : Fin 2 → ℝ := ![(p.d : ℝ), (p.c : ℝ)]
def matrix (p : PrimitiveCoordinates) : Mat := Matrix.vecMulVec p.column p.row

end PrimitiveCoordinates

private theorem natural_factorization (p q r s : ℕ)
    (hdet : p * s = q * r) (htrace : 0 < p + s) :
    ∃ (u : PrimitiveCoordinates) (k : ℕ), 0 < k ∧
      p = k * u.a * u.c ∧ q = k * u.a * u.d ∧
      r = k * u.b * u.c ∧ s = k * u.b * u.d := by
  by_cases hp : p = 0
  · have hqr : q = 0 ∨ r = 0 := by simpa [hp] using hdet.symm
    rcases hqr with hq | hr
    · have hs : 0 < s := by omega
      have hgs : 0 < r.gcd s := Nat.gcd_pos_of_pos_right r hs
      obtain ⟨g, c, d, hg, hcd, hc, hd⟩ := Nat.exists_coprime' hgs
      have hdpos : 0 < d := by
        apply Nat.pos_of_ne_zero
        intro hz
        simp [hz] at hd
        omega
      refine ⟨⟨0, 1, c, d, by simp, hcd, by simpa using hdpos⟩, g, hg, ?_⟩
      dsimp
      simp only [hp, hq, mul_zero, zero_mul, mul_one, true_and]
      exact ⟨by simpa [mul_comm] using hc, by simpa [mul_comm] using hd⟩
    · have hs : 0 < s := by omega
      obtain ⟨g, a, b, hg, hab, ha, hb⟩ :=
        Nat.exists_coprime' (Nat.gcd_pos_of_pos_right q hs)
      have hbpos : 0 < b := by
        apply Nat.pos_of_ne_zero
        intro hz
        simp [hz] at hb
        omega
      refine ⟨⟨a, b, 0, 1, hab, by simp, by simpa using hbpos⟩, g, hg, ?_⟩
      dsimp
      simp only [hp, hr, mul_zero, zero_mul, mul_one, true_and, and_true]
      exact ⟨by simpa [mul_comm] using ha, by simpa [mul_comm] using hb⟩
  · have hp0 : 0 < p := Nat.pos_of_ne_zero hp
    obtain ⟨g, a, b, hg, hab, hp', hr⟩ :=
      Nat.exists_coprime' (Nat.gcd_pos_of_pos_left r hp0)
    have ha : 0 < a := by
      apply Nat.pos_of_ne_zero
      intro hz
      simp [hz] at hp'
      omega
    have hrel : a * s = q * b := by
      apply mul_left_cancel₀ (Nat.ne_of_gt hg)
      calc
        g * (a * s) = (a*g)*s := by ring
        _ = p*s := by rw [hp']
        _ = q*r := hdet
        _ = g*(q*b) := by rw [hr]; ring
    have haq : a ∣ q := hab.dvd_mul_right.mp ⟨s, hrel.symm⟩
    obtain ⟨D, hD⟩ := haq
    have hs : s = b * D := by
      apply mul_left_cancel₀ (Nat.ne_of_gt ha)
      rw [hrel, hD]
      ring
    obtain ⟨k, c, d, hk, hcd, hc, hd⟩ :=
      Nat.exists_coprime' (Nat.gcd_pos_of_pos_left D hg)
    have ht : 0 < a * c + b * d := by
      by_contra hn
      have hz : a * c + b * d = 0 := by omega
      have hps : p + s = k * (a*c+b*d) := by rw [hp', hs, hc, hd]; ring
      rw [hz] at hps
      simp at hps
      omega
    refine ⟨⟨a,b,c,d,hab,hcd,ht⟩, k, hk, ?_⟩
    dsimp
    rw [hp', hr, hD, hs, hc, hd]
    constructor
    · ring
    constructor
    · ring
    constructor <;> ring

private def rationalDifference (A : Fin 3 → Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix (Fin 2) (Fin 2) ℚ →ₗ[ℚ] (Fin 3 → ℚ) where
  toFun X i := Matrix.trace (Matrix.map (A i) (Int.castRingHom ℚ) * X) - Matrix.trace X
  map_add' X Y := by ext i; simp [Matrix.mul_add, Matrix.trace_add]; ring
  map_smul' c X := by ext i; simp [Matrix.mul_smul, Matrix.trace_smul]; ring

private theorem integer_kernel (w : Fin 3 → List Bool) :
    ∃ H : Matrix (Fin 2) (Fin 2) ℤ, H ≠ 0 ∧
      prefixDifference w (Matrix.map H (Int.castRingHom ℝ)) = 0 := by
  have he (i : Fin 3) (j k : Fin 2) :
      ∃ z : ℤ, prefixMatrix w i.succ j k = (z : ℝ) :=
    ((legal_matrix_monoid (prefixMatrix w i.succ)).mp
      ⟨prefixWord w i.succ, rfl⟩).1 j k |>.2
  choose A hA using he
  obtain ⟨Q, hQ, hQ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := rationalDifference A)
      (by simp [Module.finrank_matrix]))
  change rationalDifference A Q = 0 at hQ
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun ij : Fin 2 × Fin 2 => Q ij.1 ij.2)
  have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.ne_zero b.property
  have hb' (i j : Fin 2) : ∃ z : ℤ, (z : ℚ) = (b : ℤ) • Q i j := hb (i,j)
  choose H hH using hb'
  have heq : Matrix.map H (Int.castRingHom ℚ) = (b : ℤ) • Q := by
    ext i j
    exact hH i j
  have hH0 : H ≠ 0 := by
    intro hz
    have hz' : (b : ℤ) • Q = 0 := by
      rw [← heq, hz]
      ext i j
      simp [Matrix.map]
    have hbq : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hb0
    apply hQ0
    ext i j
    have hij := congrFun (congrFun hz' i) j
    change ((b : ℤ) : ℚ) * Q i j = 0 at hij
    exact (mul_eq_zero.mp hij).resolve_left hbq
  have hker : rationalDifference A (Matrix.map H (Int.castRingHom ℚ)) = 0 := by
    rw [heq]
    rw [map_zsmul, hQ, smul_zero]
  refine ⟨H, hH0, ?_⟩
  ext i
  have hi := congrFun hker i
  change Matrix.trace (prefixMatrix w i.succ * Matrix.map H (Int.castRingHom ℝ)) -
    Matrix.trace (Matrix.map H (Int.castRingHom ℝ)) = 0
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.map, Matrix.of_apply, Int.coe_castRingHom, hA]
  change Matrix.trace (Matrix.map (A i) (Int.castRingHom ℚ) * Matrix.map H (Int.castRingHom ℚ)) -
    Matrix.trace (Matrix.map H (Int.castRingHom ℚ)) = 0 at hi
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.map, Matrix.of_apply, Int.coe_castRingHom] at hi
  exact_mod_cast hi

private theorem integer_level (a b c d : ℕ) (hcd : c.Coprime d) (X Y : ℤ)
    (hlevel : (c : ℤ)*X - (d : ℤ)*Y = (a : ℤ)*c + (b : ℤ)*d) :
    ∃! m : ℤ, X = (a : ℤ) + m*d ∧ Y = -(b : ℤ) + m*c := by
  let α := Nat.gcdA c d
  let β := Nat.gcdB c d
  have hbez : (c : ℤ)*α + (d : ℤ)*β = 1 := by
    simpa [α, β, hcd.gcd_eq_one] using (Nat.gcd_eq_gcd_ab c d).symm
  let m := β*(X-a)+α*(Y+b)
  have hx : X = (a : ℤ)+m*d := by
    dsimp [m]
    linear_combination -(X-a)*hbez + α*hlevel
  have hy : Y = -(b : ℤ)+m*c := by
    dsimp [m]
    linear_combination -(Y+b)*hbez - β*hlevel
  refine ⟨m, ⟨hx,hy⟩, ?_⟩
  intro n hn
  calc
    n = n*((c : ℤ)*α + d*β) := by rw [hbez]; ring
    _ = β*(X-a)+α*(Y+b) := by rw [hn.1,hn.2]; ring
    _ = m := rfl

private theorem oriented_natural_kernel (w : Fin 3 → List Bool) (N : Mat)
    (h : OrientedKernelGenerator w N) :
    ∃ (p q r s : ℕ) (ρ : ℝ), 0 < ρ ∧
      (!![(p:ℝ),-(q:ℝ);-(r:ℝ),(s:ℝ)] : Mat) = ρ • N ∧
      p*s = q*r ∧ 0 < p+s := by
  obtain ⟨H, hH0, hHker⟩ := integer_kernel w
  let K : Mat := H.map (Int.castRingHom ℝ)
  have hK0 : K ≠ 0 := by
    intro hz
    apply hH0
    ext i j
    have hi := congrFun (congrFun hz i) j
    change (H i j : ℝ) = 0 at hi
    exact_mod_cast hi
  obtain ⟨v, hv⟩ := (h.kernel_line K).mp hHker
  have hv0 : v ≠ 0 := by intro hz; simp [hz] at hv; exact hK0 hv
  have horient : ∃ (Z : Matrix (Fin 2) (Fin 2) ℤ) (ρ : ℝ),
      0 < ρ ∧ Z.map (Int.castRingHom ℝ) = ρ • N := by
    by_cases hp : 0 < v
    · exact ⟨H,v,hp,hv⟩
    · refine ⟨-H,-v,by rcases lt_or_gt_of_ne hv0 with hn | hn <;> linarith,?_⟩
      ext i j
      have hij := congrFun (congrFun hv i) j
      simpa [K] using congrArg Neg.neg hij
  obtain ⟨Z,ρ,hρ,hZ⟩ := horient
  obtain ⟨hs,ht,-⟩ := kernel_signs_positive_trace_invertible w N h
  have h00 : 0 ≤ Z 0 0 := by
    have hh := congrFun (congrFun hZ 0) 0
    simp only [Matrix.map, Matrix.of_apply, Int.coe_castRingHom, Pi.smul_apply, smul_eq_mul] at hh
    exact_mod_cast (show (0:ℝ) ≤ (Z 0 0:ℝ) by rw [hh]; exact mul_nonneg hρ.le hs.1)
  have h11 : 0 ≤ Z 1 1 := by
    have hh := congrFun (congrFun hZ 1) 1
    simp only [Matrix.map, Matrix.of_apply, Int.coe_castRingHom, Pi.smul_apply, smul_eq_mul] at hh
    exact_mod_cast (show (0:ℝ) ≤ (Z 1 1:ℝ) by rw [hh]; exact mul_nonneg hρ.le hs.2.1)
  have h01 : 0 ≤ -Z 0 1 := by
    have hh := congrFun (congrFun hZ 0) 1
    simp only [Matrix.map, Matrix.of_apply, Int.coe_castRingHom, Pi.smul_apply, smul_eq_mul] at hh
    have hh' : (0:ℝ) ≤ -(Z 0 1:ℝ) := by
      rw [hh]
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hρ.le hs.2.2.1)
    exact_mod_cast hh'
  have h10 : 0 ≤ -Z 1 0 := by
    have hh := congrFun (congrFun hZ 1) 0
    simp only [Matrix.map, Matrix.of_apply, Int.coe_castRingHom, Pi.smul_apply, smul_eq_mul] at hh
    have hh' : (0:ℝ) ≤ -(Z 1 0:ℝ) := by
      rw [hh]
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hρ.le hs.2.2.2)
    exact_mod_cast hh'
  let p := (Z 0 0).toNat
  let q := (-Z 0 1).toNat
  let r := (-Z 1 0).toNat
  let s := (Z 1 1).toNat
  have hp : (p:ℤ) = Z 0 0 := Int.toNat_of_nonneg h00
  have hq : (q:ℤ) = -Z 0 1 := Int.toNat_of_nonneg h01
  have hr : (r:ℤ) = -Z 1 0 := Int.toNat_of_nonneg h10
  have hss : (s:ℤ) = Z 1 1 := Int.toNat_of_nonneg h11
  let P : Mat := !![(p:ℝ),-(q:ℝ);-(r:ℝ),(s:ℝ)]
  have hpR : (p:ℝ) = (Z 0 0:ℝ) := by exact_mod_cast hp
  have hqR : (q:ℝ) = -(Z 0 1:ℝ) := by exact_mod_cast hq
  have hrR : (r:ℝ) = -(Z 1 0:ℝ) := by exact_mod_cast hr
  have hsR : (s:ℝ) = (Z 1 1:ℝ) := by exact_mod_cast hss
  have hPZ : P = Z.map (Int.castRingHom ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P,Matrix.map,Matrix.of_apply,Int.coe_castRingHom,hpR,hqR,hrR,hsR]
  have hP : P = ρ • N := hPZ.trans hZ
  have hNdet : N.det = 0 := by
    by_contra hn
    have hh := Matrix.rank_of_det_ne_zero hn
    rw [h.rank_one] at hh
    norm_num at hh
  have hPdet : P.det = 0 := by rw [hP, Matrix.det_smul, hNdet, mul_zero]
  have hPtrace : 0 < Matrix.trace P := by rw [hP, Matrix.trace_smul]; exact mul_pos hρ ht
  refine ⟨p,q,r,s,ρ,hρ,hP,?_,?_⟩
  · simp [P, Matrix.det_fin_two] at hPdet
    exact_mod_cast (sub_eq_zero.mp hPdet)
  · have hh : (0:ℝ) < (p:ℝ)+(s:ℝ) := by
      simpa [P, Matrix.trace, Matrix.diag, Fin.sum_univ_two] using hPtrace
    exact_mod_cast hh

private theorem primitive_generator (w : Fin 3 → List Bool) (N : Mat)
    (h : OrientedKernelGenerator w N) :
    ∃ (p : PrimitiveCoordinates) (scale : ℝ), 0 < scale ∧ N = scale • p.matrix := by
  obtain ⟨a,b,c,d,ρ,hρ,hP,hdet,htrace⟩ := oriented_natural_kernel w N h
  obtain ⟨p,k,hk,hcoords⟩ := natural_factorization a b c d hdet htrace
  have heq : (!![(a:ℝ),-(b:ℝ);-(c:ℝ),(d:ℝ)] : Mat) = (k:ℝ) • p.matrix := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PrimitiveCoordinates.matrix,PrimitiveCoordinates.column,PrimitiveCoordinates.row,
        Matrix.vecMulVec, hcoords.1,hcoords.2.1,hcoords.2.2.1,hcoords.2.2.2] <;> ring
  refine ⟨p,(k:ℝ)/ρ,div_pos (by exact_mod_cast hk) hρ,?_⟩
  rw [heq] at hP
  ext i j
  have hh := congrFun (congrFun hP i) j
  change (k:ℝ) * p.matrix i j = ρ * N i j at hh
  change N i j = ((k:ℝ)/ρ) * p.matrix i j
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (ne_of_gt hρ)).mpr
  nlinarith [hh]

private theorem primitive_endpoint_parameters (w : Fin 3 → List Bool)
    (p : PrimitiveCoordinates) (hker : prefixDifference w p.matrix = 0) :
    ∃ m : Fin 4 → ℤ, m 0 = 0 ∧ ∀ i,
      prefixMatrix w i *ᵥ p.column = p.column + (m i : ℝ) • p.direction := by
  have he (i : Fin 3) (j k : Fin 2) :
      ∃ z : ℤ, prefixMatrix w i.succ j k = (z:ℝ) :=
    ((legal_matrix_monoid (prefixMatrix w i.succ)).mp
      ⟨prefixWord w i.succ,rfl⟩).1 j k |>.2
  choose A hA using he
  have hlevels (i : Fin 3) :
      (p.c:ℤ)*(A i 0 0*p.a-A i 0 1*p.b) -
      (p.d:ℤ)*(A i 1 0*p.a-A i 1 1*p.b) = (p.a:ℤ)*p.c+(p.b:ℤ)*p.d := by
    have hi := congrFun hker i
    change Matrix.trace (prefixMatrix w i.succ * p.matrix) - Matrix.trace p.matrix = 0 at hi
    simp [PrimitiveCoordinates.matrix,PrimitiveCoordinates.column,PrimitiveCoordinates.row,
      Matrix.vecMulVec,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two,hA] at hi
    exact_mod_cast (show (p.c:ℝ)*((A i 0 0:ℝ)*p.a-(A i 0 1:ℝ)*p.b) -
      (p.d:ℝ)*((A i 1 0:ℝ)*p.a-(A i 1 1:ℝ)*p.b) = (p.a:ℝ)*p.c+(p.b:ℝ)*p.d by
      linarith [hi])
  have hparams (i : Fin 3) := integer_level p.a p.b p.c p.d p.row_primitive
    (A i 0 0*p.a-A i 0 1*p.b) (A i 1 0*p.a-A i 1 1*p.b) (hlevels i)
  choose m hm using fun i => (hparams i).exists
  refine ⟨Fin.cases 0 m,rfl,?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [prefixMatrix,prefixWord,futureProduct]
  · change prefixMatrix w j.succ *ᵥ p.column = p.column + (m j:ℝ) • p.direction
    ext k
    fin_cases k
    · have hh : (A j 0 0:ℝ)*p.a-(A j 0 1:ℝ)*p.b = (p.a:ℝ)+(m j:ℝ)*p.d :=
        by exact_mod_cast (hm j).1
      simpa [PrimitiveCoordinates.column,PrimitiveCoordinates.direction,Matrix.mulVec,
        dotProduct,Fin.sum_univ_two,hA,sub_eq_add_neg] using hh
    · have hh : (A j 1 0:ℝ)*p.a-(A j 1 1:ℝ)*p.b = -(p.b:ℝ)+(m j:ℝ)*p.c :=
        by exact_mod_cast (hm j).2
      simpa [PrimitiveCoordinates.column,PrimitiveCoordinates.direction,Matrix.mulVec,
        dotProduct,Fin.sum_univ_two,hA,sub_eq_add_neg] using hh

/-- Whole-class primitive representation of an arbitrary real oriented generator,
with positive real scale and the original four chronological endpoint equations. -/
private theorem forward_representation
    (w : Fin 3 → List Bool) (N : Mat) (h : OrientedKernelGenerator w N) :
    ∃ (p : PrimitiveCoordinates) (scale : ℝ), 0 < scale ∧ N = scale • p.matrix ∧
      (∀ X, prefixDifference w X = 0 ↔ ∃ v : ℝ, X = v • p.matrix) ∧
      ∃ m : Fin 4 → ℤ, m 0 = 0 ∧ ∀ i,
        prefixMatrix w i *ᵥ p.column = p.column + (m i:ℝ) • p.direction := by
  obtain ⟨p,scale,hscale,hN⟩ := primitive_generator w N h
  have hk : prefixDifference w p.matrix = 0 := by
    have hNker := (h.kernel_line N).mpr ⟨1,by simp⟩
    rw [hN,map_smul] at hNker
    exact (smul_eq_zero.mp hNker).resolve_left (ne_of_gt hscale)
  refine ⟨p,scale,hscale,hN,?_,primitive_endpoint_parameters w p hk⟩
  intro X
  rw [h.kernel_line X,hN]
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨v*scale,by rw [smul_smul]⟩
  · rintro ⟨v,rfl⟩
    exact ⟨v/scale,by rw [smul_smul,div_mul_cancel₀ _ (ne_of_gt hscale)]⟩



private theorem primitive_trace (p : PrimitiveCoordinates) : 0 < Matrix.trace p.matrix := by
  have ht : (0:ℝ) < (p.a:ℝ)*p.c + (p.b:ℝ)*p.d := by exact_mod_cast p.trace_pos
  simpa [PrimitiveCoordinates.matrix,PrimitiveCoordinates.column,PrimitiveCoordinates.row,
    Matrix.vecMulVec,Matrix.trace,Matrix.diag,Fin.sum_univ_two] using ht

private theorem primitive_nonzero_rank_one (p : PrimitiveCoordinates) :
    p.matrix ≠ 0 ∧ p.matrix.rank = 1 := by
  have ht := primitive_trace p
  have hn : p.matrix ≠ 0 := by intro hz; simp [hz] at ht
  refine ⟨hn,?_⟩
  have hle : p.matrix.rank ≤ 1 := Matrix.rank_vecMulVec_le _ _
  have hdiag : p.matrix 0 0 ≠ 0 ∨ p.matrix 1 1 ≠ 0 := by
    by_contra hh
    push_neg at hh
    simp [Matrix.trace,Matrix.diag,Fin.sum_univ_two,hh.1,hh.2] at ht
  have hminor (j : Fin 2) (hj : p.matrix j j ≠ 0) : 1 ≤ p.matrix.rank := by
    let T := p.matrix.submatrix (fun _ : Fin 1 => j) (fun _ : Fin 1 => j)
    have hdet : T.det ≠ 0 := by simpa [T,Matrix.det_fin_one,Matrix.submatrix] using hj
    have hr := Matrix.rank_of_det_ne_zero hdet
    have hh := Matrix.rank_submatrix_le p.matrix (fun _ : Fin 1 => j) (fun _ : Fin 1 => j)
    change T.rank ≤ p.matrix.rank at hh
    rw [hr] at hh
    simpa using hh
  rcases hdiag with h0 | h1
  · exact Nat.le_antisymm hle (hminor 0 h0)
  · exact Nat.le_antisymm hle (hminor 1 h1)

private theorem primitive_positive_polar (p : PrimitiveCoordinates) (S : Mat)
    (hS : ∀ i j, 0 < S i j) : 0 < determinantPolar S p.matrix := by
  have hcoeff : (0:ℝ) ≤ (p.a:ℝ)*p.c ∧ 0 ≤ (p.b:ℝ)*p.d ∧
      0 ≤ (p.b:ℝ)*p.c ∧ 0 ≤ (p.a:ℝ)*p.d := by
    exact ⟨by positivity, by positivity, by positivity, by positivity⟩
  have ht : (0:ℝ) < (p.a:ℝ)*p.c + (p.b:ℝ)*p.d := by exact_mod_cast p.trace_pos
  have hp : 0 < (p.b:ℝ)*p.d*S 0 0 + (p.b:ℝ)*p.c*S 0 1 +
      (p.a:ℝ)*p.d*S 1 0 + (p.a:ℝ)*p.c*S 1 1 := by
    have h0 := mul_nonneg hcoeff.2.1 (hS 0 0).le
    have h1 := mul_nonneg hcoeff.2.2.1 (hS 0 1).le
    have h2 := mul_nonneg hcoeff.2.2.2 (hS 1 0).le
    have h3 := mul_nonneg hcoeff.1 (hS 1 1).le
    by_cases hac : 0 < (p.a:ℝ)*p.c
    · have hh := mul_pos hac (hS 1 1)
      linarith
    · have hbd : 0 < (p.b:ℝ)*p.d := by linarith
      have hh := mul_pos hbd (hS 0 0)
      linarith
  convert hp using 1
  simp [determinantPolar,PrimitiveCoordinates.matrix,PrimitiveCoordinates.column,
    PrimitiveCoordinates.row,Matrix.vecMulVec,Matrix.det_fin_two]
  ring

/-- The converse keeps the three actual chronological multipliers and rank three.
The lattice equations never supply an unassumed acquisition transition. -/
private theorem cumulative_converse
    (w : Fin 3 → List Bool) (p : PrimitiveCoordinates) (m : Fin 4 → ℤ)
    (hm0 : m 0 = 0)
    (hm : ∀ i, prefixMatrix w i *ᵥ p.column = p.column + (m i:ℝ) • p.direction)
    (hrank : Module.finrank ℝ (LinearMap.range (prefixDifference w)) = 3) :
    OrientedKernelGenerator w p.matrix := by
  obtain ⟨hn,hr⟩ := primitive_nonzero_rank_one p
  have hker : prefixDifference w p.matrix = 0 := by
    ext i
    have hh := hm i.succ
    have h0 := congrFun hh 0
    have h1 := congrFun hh 1
    simp [PrimitiveCoordinates.column,PrimitiveCoordinates.direction,Matrix.mulVec,
      dotProduct,Fin.sum_univ_two] at h0 h1
    change Matrix.trace (prefixMatrix w i.succ * p.matrix) - Matrix.trace p.matrix = 0
    simp [PrimitiveCoordinates.matrix,PrimitiveCoordinates.column,PrimitiveCoordinates.row,
      Matrix.vecMulVec,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two]
    linear_combination (p.c:ℝ)*h0 - (p.d:ℝ)*h1
  have hdim : Module.finrank ℝ (LinearMap.ker (prefixDifference w)) = 1 := by
    have hh := (prefixDifference w).finrank_range_add_finrank_ker
    rw [hrank] at hh
    have hdimMat : Module.finrank ℝ Mat = 4 := by simp [Mat,Module.finrank_matrix]
    rw [hdimMat] at hh
    omega
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim hker hn
  refine ⟨hn,hr,?_,fun S hS => primitive_positive_polar p S hS.1⟩
  intro X
  change X ∈ LinearMap.ker (prefixDifference w) ↔ _
  rw [hspan,Submodule.mem_span_singleton]
  exact exists_congr (fun v => eq_comm)



/-- The original Theorem 3.2, with forward and converse quantifiers kept independent.
An arbitrary real positive orientation carries a positive real scale. -/
theorem whole_class_primitive_lattice :
    (∀ (w : Fin 3 → List Bool) (N : Mat), OrientedKernelGenerator w N →
      ∃ (p : PrimitiveCoordinates) (scale : ℝ), 0 < scale ∧ N = scale • p.matrix ∧
        (∀ X, prefixDifference w X = 0 ↔ ∃ v : ℝ, X = v • p.matrix) ∧
        ∃ m : Fin 4 → ℤ, m 0 = 0 ∧ ∀ i,
          prefixMatrix w i *ᵥ p.column = p.column + (m i:ℝ) • p.direction) ∧
    (∀ (w : Fin 3 → List Bool) (p : PrimitiveCoordinates) (m : Fin 4 → ℤ),
      m 0 = 0 →
      (∀ i, prefixMatrix w i *ᵥ p.column = p.column + (m i:ℝ) • p.direction) →
      Module.finrank ℝ (LinearMap.range (prefixDifference w)) = 3 →
      OrientedKernelGenerator w p.matrix) :=
  ⟨forward_representation,cumulative_converse⟩

#print axioms whole_class_primitive_lattice

end D5.S3.Observer.CubicGain.PrimitiveKernelLattice
