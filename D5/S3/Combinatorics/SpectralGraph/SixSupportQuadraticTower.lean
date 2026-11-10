/- GID: D5/S3/Combinatorics/SpectralGraph/SixSupportQuadraticTower
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportQuadraticTower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual supplied Nikandish tower and finite-root objects, pending current canonical admission. -/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Norm.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic

/-! Task-owned transient exact mathematical check. No publication/admission claimed.
Prospective proof shape: exact coefficient/norm/value/gcd certificates, scalar transport,
Kummer and dimension applications are bind-only checks, used only in this actual tower.
The intended live target is the degree-four generator/minimal-polynomial correspondence.
No external-open waiver or positive finite-instance admission is asserted.
-/
namespace NikandishE3
open Polynomial
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
abbrev P := Polynomial ℚ
local notation "b" => (Polynomial.X : P)
def t : P := b*(b+2)
def A : P := 3*b-1
def B : P := b*(b^2+4*b-1)
def C₀ : P := -((b^2+2*b-1)*(b^2+3*b-1)*(b^3+3*b^2+3*b-1))
def D : P := 12*b^8+92*b^7+233*b^6+172*b^5-154*b^4-172*b^3+161*b^2-44*b+4
def N : P := (b^3+5*b^2+6*b-2)*(3*b^6+8*b^5-6*b^4-36*b^3-28*b^2+40*b-8)
theorem discriminant_certificate : B^2-4*A*C₀ = D := by unfold B A C₀ D; ring
theorem norm_certificate : A*t^4+4*B*t^2+16*C₀ = N := by unfold A t B C₀ N; ring
theorem degree_D : D.natDegree = 8 := by unfold D; compute_degree!
theorem degree_N : N.natDegree = 9 := by unfold N; compute_degree!
theorem coprime_D : IsCoprime D D.derivative := by
  refine ⟨(Polynomial.C (15077458503622003/12603918688 : ℚ) + Polynomial.C (-54128905348874963/12603918688 : ℚ) * X^1 + Polynomial.C (-6246087705771407/3150979672 : ℚ) * X^2 + Polynomial.C (117940112961877943/12603918688 : ℚ) * X^3 + Polynomial.C (145006858328612117/12603918688 : ℚ) * X^4 + Polynomial.C (30779539539563445/6301959344 : ℚ) * X^5 + Polynomial.C (551481433980327/787744918 : ℚ) * X^6 : P), (Polynomial.C (1370677759331121/12603918688 : ℚ) + Polynomial.C (-19934798047738501/25207837376 : ℚ) * X^1 + Polynomial.C (36019683710933693/25207837376 : ℚ) * X^2 + Polynomial.C (8204653143188935/12603918688 : ℚ) * X^3 + Polynomial.C (-44366105575549787/25207837376 : ℚ) * X^4 + Polynomial.C (-47526676857220537/25207837376 : ℚ) * X^5 + Polynomial.C (-1093986370835811/1575489836 : ℚ) * X^6 + Polynomial.C (-551481433980327/6301959344 : ℚ) * X^7 : P), ?_⟩
  apply Polynomial.funext
  intro x
  norm_num [D, N, Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring

theorem coprime_N : IsCoprime N N.derivative := by
  refine ⟨(Polynomial.C (-1551720656793517/69254786592 : ℚ) + Polynomial.C (290115890479151/46169857728 : ℚ) * X^1 + Polynomial.C (6813283610138383/92339715456 : ℚ) * X^2 + Polynomial.C (34122483667637429/554038292736 : ℚ) * X^3 + Polynomial.C (3370077294694969/2216153170944 : ℚ) * X^4 + Polynomial.C (-86652849207243331/4432306341888 : ℚ) * X^5 + Polynomial.C (-39894848329397747/4432306341888 : ℚ) * X^6 + Polynomial.C (-417181352926057/328318988288 : ℚ) * X^7 : P), (Polynomial.C (-1551724985217679/554038292736 : ℚ) + Polynomial.C (13284078298392293/1108076585472 : ℚ) * X^1 + Polynomial.C (-27151801510553/123119620608 : ℚ) * X^2 + Polynomial.C (-13019587671423695/738717723648 : ℚ) * X^3 + Polynomial.C (-1608792935985931/130361951232 : ℚ) * X^4 + Polynomial.C (-192340276236565/492478482432 : ℚ) * X^5 + Polynomial.C (2030298571254023/738717723648 : ℚ) * X^6 + Polynomial.C (9931651975121645/8864612683776 : ℚ) * X^7 + Polynomial.C (417181352926057/2954870894592 : ℚ) * X^8 : P), ?_⟩
  apply Polynomial.funext
  intro x
  norm_num [D, N, Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring

theorem coprime_N_D : IsCoprime N D := by
  refine ⟨(Polynomial.C (-3559310030328403/471932176 : ℚ) + Polynomial.C (6462996085656055/117983044 : ℚ) * X^1 + Polynomial.C (-46657822536661549/471932176 : ℚ) * X^2 + Polynomial.C (-21303192533434097/471932176 : ℚ) * X^3 + Polynomial.C (14356909865819141/117983044 : ℚ) * X^4 + Polynomial.C (61549445215520121/471932176 : ℚ) * X^5 + Polynomial.C (5667971824526075/117983044 : ℚ) * X^6 + Polynomial.C (714366125043951/117983044 : ℚ) * X^7 : P), (Polynomial.C (889827514956041/29495761 : ℚ) + Polynomial.C (-3793513481796410/29495761 : ℚ) * X^1 + Polynomial.C (61458663986279/29495761 : ℚ) * X^2 + Polynomial.C (22274907297181941/117983044 : ℚ) * X^3 + Polynomial.C (15611438025308693/117983044 : ℚ) * X^4 + Polynomial.C (249440883003581/58991522 : ℚ) * X^5 + Polynomial.C (-13899098543371799/471932176 : ℚ) * X^6 + Polynomial.C (-5667971824526075/471932176 : ℚ) * X^7 + Polynomial.C (-714366125043951/471932176 : ℚ) * X^8 : P), ?_⟩
  apply Polynomial.funext
  intro x
  norm_num [D, N, Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring

theorem special_D : eval (1/3 : ℚ) D = 16/729 := by norm_num [D]
section FractionSquare
variable {k : Type*} [Field k]
-- Used on the live D-nonsquare path; no retained generic wrapper is proposed.
theorem nonsquare_of_squarefree (p : k[X]) (hp : Squarefree p) (hdeg : 0 < p.natDegree) :
    ¬ IsSquare (algebraMap k[X] (RatFunc k) p) := by
  rintro ⟨x, hx⟩
  have hint : IsIntegral k[X] (x^2) := by
    rw [pow_two, ← hx]
    exact isIntegral_algebraMap
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := k[X]) (K := RatFunc k) (by norm_num : 0 < (2 : ℕ)) hint
  have hpw : p = w*w := (IsFractionRing.injective k[X] (RatFunc k)) (by
    simpa only [map_mul, hw] using hx)
  have hunit : IsUnit w := hp w ⟨1, by simpa [hpw]⟩
  have hunitp : IsUnit p := hpw ▸ hunit.mul hunit
  have := natDegree_eq_zero_of_isUnit hunitp
  omega
end FractionSquare


-- Simple-pole obstruction: no assumed nonsquare or valuation certificate.
section SimplePole
variable {k : Type*} [Field k]
theorem nonsquare_of_simple_pole (p q : k[X]) (r : k)
    (hp : eval r p = 0) (hdp : eval r p.derivative ≠ 0) (hq : eval r q ≠ 0) :
    ¬ IsSquare (algebraMap k[X] (RatFunc k) q / algebraMap k[X] (RatFunc k) p) := by
  let i := algebraMap k[X] (RatFunc k)
  have hp0 : p ≠ 0 := by intro h; simp [h] at hdp
  have hip : i p ≠ 0 := by simpa only [map_zero] using (IsFractionRing.injective k[X] (RatFunc k)).ne hp0
  rintro ⟨x, hx⟩
  have hs : (i p * x)^2 = i (p*q) := by
    change (i p*x)^2 = i (p*q)
    change i q/i p = x*x at hx
    rw [mul_pow, pow_two x, ← hx, map_mul]
    field_simp
  have hint : IsIntegral k[X] ((i p*x)^2) := by
    rw [hs]
    exact isIntegral_algebraMap
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := k[X]) (K := RatFunc k) (by norm_num : 0 < (2 : ℕ)) hint
  have hw' : w*w = p*q := (IsFractionRing.injective k[X] (RatFunc k)) (by
    change i (w*w) = i (p*q)
    rw [map_mul, hw, ← pow_two, hs])
  have he := congrArg (eval r) hw'
  simp only [eval_mul, hp, zero_mul] at he
  have hew : eval r w = 0 := mul_self_eq_zero.mp he
  have hed := congrArg (fun u : k[X] => eval r u.derivative) hw'
  simp only [derivative_mul, eval_add, eval_mul, hp, hew, mul_zero, zero_mul, zero_add,
    add_zero] at hed
  exact (mul_ne_zero hdp hq) hed.symm
end SimplePole

section ActualTower
variable (k : Type*) [Field k] [CharZero k]
abbrev K := RatFunc k
def pk : P →+* k[X] := Polynomial.mapRingHom (algebraMap ℚ k)
def rf : P →+* K k := (algebraMap k[X] (K k)).comp (pk k)
theorem rf_injective : Function.Injective (rf k) :=
  (IsFractionRing.injective k[X] (K k)).comp
    (Polynomial.map_injective (algebraMap ℚ k) (algebraMap ℚ k).injective)

theorem D_separable : (pk k D).Separable :=
  (show D.Separable from coprime_D).map

theorem D_nonsquare : ¬ IsSquare (rf k D) := by
  apply nonsquare_of_squarefree (pk k D) (D_separable k).squarefree
  have hd : (pk k D).natDegree = 8 := by
    change (D.map (algebraMap ℚ k)).natDegree = 8
    rw [Polynomial.natDegree_map, degree_D]
  omega

instance D_fact : Fact (¬ IsSquare (rf k D)) := ⟨D_nonsquare k⟩
abbrev H := QuadraticAlgebra (K k) (rf k D) 0
instance : Field (H k) := inferInstance

def y : H k := QuadraticAlgebra.omega
def q : H k := ⟨-rf k B/(2*rf k A), (2*rf k A)⁻¹⟩
def f : H k := ⟨(rf k t)^2+2*rf k B/rf k A, -2/rf k A⟩

theorem A_nonzero : rf k A ≠ 0 := by
  rw [← (rf k).map_zero]
  apply (rf_injective k).ne
  intro h
  have he := congrArg (eval (0 : ℚ)) h
  norm_num [A] at he

theorem y_squared : (y k)^2 = algebraMap (K k) (H k) (rf k D) := by
  simp [y, pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]

theorem q_display : q k = (y k-algebraMap (K k) (H k) (rf k B)) /
    (2*algebraMap (K k) (H k) (rf k A)) := by
  have ha : (2*algebraMap (K k) (H k) (rf k A)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by simpa only [map_zero] using (algebraMap (K k) (H k)).injective.ne (A_nonzero k))
  apply (eq_div_iff ha).2
  ext <;> simp [q, y, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;>
    field_simp [A_nonzero k] <;> ring

theorem f_display : f k = (algebraMap (K k) (H k) (rf k t))^2-4*q k := by
  ext <;> simp [f, q, pow_two, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> field_simp [A_nonzero k] <;> ring

theorem norm_f : QuadraticAlgebra.norm (f k) = rf k N/rf k A := by
  have hd := congrArg (rf k) discriminant_certificate
  have hn := congrArg (rf k) norm_certificate
  simp only [map_sub, map_pow, map_mul, map_add, map_ofNat] at hd hn
  simp only [f, QuadraticAlgebra.norm_def, zero_mul, zero_add]
  rw [← hd, ← hn]
  field_simp [A_nonzero k]
  ring

theorem field_norm_eq (u : H k) : Algebra.norm (K k) u = QuadraticAlgebra.norm u := by
  rw [Algebra.norm_apply]
  change (DistribSMul.toLinearMap (K k) (H k) u).det = QuadraticAlgebra.norm u
  exact QuadraticAlgebra.det_toLinearMap_eq_norm u

theorem field_norm_f : Algebra.norm (K k) (f k) = rf k N/rf k A := by
  rw [field_norm_eq,norm_f]

theorem norm_f_nonsquare : ¬ IsSquare (rf k N/rf k A) := by
  apply nonsquare_of_simple_pole (pk k A) (pk k N) (1/3 : k)
  · norm_num [pk, A]
  · norm_num [pk, A]
  · norm_num [pk, N]


-- This is the actual reduced rational-function denominator, not an assumed pole.
theorem norm_ratio_denom : RatFunc.denom (rf k N / rf k A) =
    X-Polynomial.C (1/3 : k) := by
  letI : Infinite k := Infinite.of_injective (fun n : ℕ => (n:k)) Nat.cast_injective
  let x : K k := rf k N / rf k A
  have hA : pk k A ≠ 0 := by
    intro he
    apply A_nonzero k
    change algebraMap k[X] (K k) (pk k A) = 0
    rw [he,map_zero]
  have hcross : x.num * pk k A = pk k N * x.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hA).2 rfl
  have he := congrArg (eval (1/3 : k)) hcross
  have hden : eval (1/3 : k) x.denom = 0 := by
    norm_num [pk,A,N] at he
    exact he
  have hroot : X-Polynomial.C (1/3 : k) ∣ x.denom :=
    (Polynomial.dvd_iff_isRoot).2 hden
  have hdiv : x.denom ∣ pk k A := RatFunc.denom_div_dvd (pk k N) (pk k A)
  have hshape : Polynomial.C (1/3 : k) * pk k A = X-Polynomial.C (1/3 : k) := by
    apply Polynomial.funext
    intro v
    norm_num [pk,A]
    ring
  have hdiv' : x.denom ∣ X-Polynomial.C (1/3 : k) := by
    rw [← hshape]
    exact dvd_mul_of_dvd_right hdiv _
  exact Polynomial.eq_of_monic_of_associated (RatFunc.monic_denom x)
    (Polynomial.monic_X_sub_C _) (associated_of_dvd_dvd hdiv' hroot)

theorem norm_ratio_simple_pole :
    (RatFunc.denom (rf k N / rf k A)).rootMultiplicity (1/3 : k) = 1 := by
  rw [norm_ratio_denom]
  exact Polynomial.rootMultiplicity_X_sub_C_self

theorem f_nonsquare : ¬ IsSquare (f k) := by
  rintro ⟨w, hw⟩
  apply norm_f_nonsquare k
  rw [← field_norm_f k]
  exact ⟨Algebra.norm (K k) w, by rw [hw, map_mul]⟩

instance f_fact : Fact (¬ IsSquare (f k)) := ⟨f_nonsquare k⟩
abbrev F := QuadraticAlgebra (H k) (f k) 0
instance : Field (F k) := inferInstance
instance : IsScalarTower (K k) (H k) (F k) := inferInstance

example : Module.finrank (K k) (H k) = 2 := QuadraticAlgebra.finrank_eq_two _ _
example : Module.finrank (H k) (F k) = 2 := QuadraticAlgebra.finrank_eq_two _ _


instance : FiniteDimensional (K k) (F k) := Module.Finite.trans (H k) (F k)

theorem degree_H : Module.finrank (K k) (H k) = 2 := QuadraticAlgebra.finrank_eq_two _ _
theorem degree_F_H : Module.finrank (H k) (F k) = 2 := QuadraticAlgebra.finrank_eq_two _ _
theorem degree_F : Module.finrank (K k) (F k) = 4 := by
  rw [← Module.finrank_mul_finrank (K k) (H k) (F k), degree_H, degree_F_H]


theorem y_recover_H : y k = 2*algebraMap (K k) (H k) (rf k A)*q k+
    algebraMap (K k) (H k) (rf k B) := by
  ext <;> simp [q,y,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat] <;>
    field_simp [A_nonzero k] <;> ring

theorem q_equation : algebraMap (K k) (H k) (rf k A)*(q k)^2+
    algebraMap (K k) (H k) (rf k B)*q k+
    algebraMap (K k) (H k) (rf k C₀) = 0 := by
  have hd := congrArg (rf k) discriminant_certificate
  simp only [map_sub,map_pow,map_mul,map_ofNat] at hd
  ext <;> simp [q,pow_two] <;> (try rw [← hd]) <;> field_simp [A_nonzero k] <;> ring

def z : F k := QuadraticAlgebra.omega
def a : F k := (algebraMap (K k) (F k) (rf k t)+z k)/2

theorem z_squared : (z k)^2 = algebraMap (H k) (F k) (f k) := by
  simp [z,pow_two,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]

theorem z_recover : z k = 2*a k-algebraMap (K k) (F k) (rf k t) := by
  unfold a
  ring

theorem q_recover : a k*(algebraMap (K k) (F k) (rf k t)-a k) =
    algebraMap (H k) (F k) (q k) := by
  have hf := congrArg (algebraMap (H k) (F k)) (f_display k)
  simp only [map_sub,map_pow,map_mul,map_ofNat,
    ← IsScalarTower.algebraMap_apply (K k) (H k) (F k)] at hf
  have hz := (z_squared k).trans hf
  unfold a
  linear_combination - (1/4 : F k) * hz

theorem y_recover : algebraMap (H k) (F k) (y k) =
    2*algebraMap (K k) (F k) (rf k A)*
      (a k*(algebraMap (K k) (F k) (rf k t)-a k))+
    algebraMap (K k) (F k) (rf k B) := by
  rw [q_recover,y_recover_H,map_add,map_mul,map_mul,map_ofNat]
  simp only [← IsScalarTower.algebraMap_apply (K k) (H k) (F k)]

theorem a_generates : IntermediateField.adjoin (K k) {a k} = ⊤ := by
  let E := IntermediateField.adjoin (K k) {a k}
  have ha : a k ∈ E := IntermediateField.mem_adjoin_simple_self (K k) (a k)
  have hz : z k ∈ E := by
    rw [z_recover]
    exact E.sub_mem (E.mul_mem (E.natCast_mem 2) ha) (E.algebraMap_mem (rf k t))
  have hy : algebraMap (H k) (F k) (y k) ∈ E := by
    rw [y_recover]
    exact E.add_mem (E.mul_mem (E.mul_mem (E.natCast_mem 2) (E.algebraMap_mem (rf k A)))
      (E.mul_mem ha (E.sub_mem (E.algebraMap_mem (rf k t)) ha))) (E.algebraMap_mem (rf k B))
  have hH : ∀ u : H k, algebraMap (H k) (F k) u ∈ E := by
    intro u
    have hu : u = algebraMap (K k) (H k) u.re+algebraMap (K k) (H k) u.im*y k := by
      simpa [y,Algebra.smul_def] using (QuadraticAlgebra.re_smul_add_im_smul u).symm
    rw [hu,map_add,map_mul]
    simp only [← IsScalarTower.algebraMap_apply (K k) (H k) (F k)]
    exact E.add_mem (E.algebraMap_mem u.re) (E.mul_mem (E.algebraMap_mem u.im) hy)
  apply top_unique
  intro v hv
  have hv' : v = algebraMap (H k) (F k) v.re+algebraMap (H k) (F k) v.im*z k := by
    simpa [z,Algebra.smul_def] using (QuadraticAlgebra.re_smul_add_im_smul v).symm
  rw [hv']
  exact E.add_mem (hH v.re) (E.mul_mem (hH v.im) hz)

theorem a_minpoly_degree : (minpoly (K k) (a k)).natDegree = 4 := by
  rw [← degree_F k]
  exact (Field.primitive_element_iff_minpoly_natDegree_eq (K k) (a k)).1 (a_generates k)



-- The actual displayed plane polynomial, with the original rational coefficients mapped to k.
def planeG : (k[X])[X] :=
  Polynomial.C (pk k A)*(Polynomial.C (pk k t)*X-X^2)^2+
  Polynomial.C (pk k B)*(Polynomial.C (pk k t)*X-X^2)+Polynomial.C (pk k C₀)
def g : (K k)[X] :=
  Polynomial.C (rf k A)*(Polynomial.C (rf k t)*X-X^2)^2+
  Polynomial.C (rf k B)*(Polynomial.C (rf k t)*X-X^2)+Polynomial.C (rf k C₀)

theorem quartic_expansion {R : Type*} [CommRing R] (s u v w : R) :
    Polynomial.C u*(Polynomial.C s*X-X^2)^2+
      Polynomial.C v*(Polynomial.C s*X-X^2)+Polynomial.C w =
    Polynomial.C u*X^4+Polynomial.C (-2*u*s)*X^3+
      Polynomial.C (u*s^2-v)*X^2+Polynomial.C (v*s)*X+Polynomial.C w := by
  simp only [map_sub,map_mul,map_pow,map_neg,map_ofNat]
  ring

theorem g_map : (planeG k).map (algebraMap k[X] (K k)) = g k := by
  simp [planeG,g,rf]

theorem g_coeff_four : (g k).coeff 4 = rf k A := by
  unfold g
  rw [quartic_expansion]
  simp only [coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
  norm_num

theorem g_degree : (g k).natDegree = 4 := by
  have hA := A_nonzero k
  unfold g
  rw [quartic_expansion]
  compute_degree <;> simp_all

theorem g_leading : (g k).leadingCoeff = rf k A := by
  change (g k).coeff (g k).natDegree = rf k A
  rw [g_degree,g_coeff_four]

theorem g_aeval : (g k).aeval (a k) = 0 := by
  simp only [g,map_add,map_sub,map_mul,map_pow,Polynomial.aeval_C,Polynomial.aeval_X]
  have hq : algebraMap (K k) (F k) (rf k t)*a k-(a k)^2 =
      algebraMap (H k) (F k) (q k) := by
    convert q_recover k using 1 <;> ring
  rw [hq]
  have he := congrArg (algebraMap (H k) (F k)) (q_equation k)
  simpa only [map_add,map_mul,map_pow,map_zero,
    ← IsScalarTower.algebraMap_apply (K k) (H k) (F k)] using he

def gm : (K k)[X] := Polynomial.C ((rf k A)⁻¹)*g k

theorem gm_monic : (gm k).Monic := by
  simp [gm,Polynomial.Monic,leadingCoeff_mul,g_leading,A_nonzero]

theorem gm_degree : (gm k).natDegree = 4 := by
  rw [gm,Polynomial.natDegree_C_mul (inv_ne_zero (A_nonzero k)),g_degree]

theorem gm_aeval : (gm k).aeval (a k) = 0 := by simp [gm,g_aeval]

theorem gm_minpoly : gm k = minpoly (K k) (a k) := by
  apply minpoly.unique_of_degree_le_degree_minpoly (K k) (a k) (gm_monic k) (gm_aeval k)
  rw [degree_eq_natDegree (gm_monic k).ne_zero,
    degree_eq_natDegree (minpoly.ne_zero_of_finite (K k) (a k)),gm_degree,a_minpoly_degree]

theorem g_irreducible : Irreducible (g k) := by
  have hi : Irreducible (gm k) := by
    rw [gm_minpoly]
    exact minpoly.irreducible (IsIntegral.of_finite (K k) (a k))
  have hu : IsUnit (Polynomial.C ((rf k A)⁻¹) : (K k)[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero (A_nonzero k)))
  exact (irreducible_isUnit_mul hu).mp hi

theorem coprime_A_B : IsCoprime (pk k A) (pk k B) := by
  letI : Infinite k := Infinite.of_injective (fun n : ℕ => (n:k)) Nat.cast_injective
  have hshape : pk k A = Polynomial.C (3:k)*(X-Polynomial.C (1/3:k)) := by
    apply Polynomial.funext
    intro v
    norm_num [pk,A]
    ring
  have hA : Irreducible (pk k A) := by
    apply Polynomial.irreducible_of_degree_eq_one
    rw [hshape,Polynomial.degree_C_mul (by norm_num : (3:k) ≠ 0),Polynomial.degree_X_sub_C]
  apply hA.coprime_iff_not_dvd.mpr
  rintro ⟨v,hv⟩
  have he := congrArg (eval (1/3 : k)) hv
  norm_num [pk,A,B] at he

theorem planeG_primitive : (planeG k).IsPrimitive := by
  intro r hr
  have h4 := (Polynomial.C_dvd_iff_dvd_coeff r (planeG k)).1 hr 4
  have h2 := (Polynomial.C_dvd_iff_dvd_coeff r (planeG k)).1 hr 2
  have hc4 : (planeG k).coeff 4 = pk k A := by
    unfold planeG
    rw [quartic_expansion]
    simp only [coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
    norm_num
  have hc2 : (planeG k).coeff 2 = pk k A*(pk k t)^2-pk k B := by
    unfold planeG
    rw [quartic_expansion]
    simp only [coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]
    norm_num
  rw [hc4] at h4
  rw [hc2] at h2
  have hrA := h4
  have hr2 := h2
  have hrB : r ∣ pk k B := by
    have ht := dvd_mul_of_dvd_left hrA ((pk k t)^2)
    convert dvd_sub ht hr2 using 1 <;> ring
  exact (coprime_A_B k).isUnit_of_dvd' hrA hrB

theorem planeG_irreducible : Irreducible (planeG k) := by
  apply (planeG_primitive k).irreducible_iff_irreducible_map_fraction_map (K := K k) |>.mpr
  rw [g_map]
  exact g_irreducible k



theorem D_kummer_irreducible : Irreducible (X^2-Polynomial.C (rf k D) : (K k)[X]) := by
  apply (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).2
  intro w hw
  exact D_nonsquare k ⟨w, by simpa [pow_two] using hw.symm⟩

theorem f_kummer_irreducible : Irreducible (X^2-Polynomial.C (f k) : (H k)[X]) := by
  apply (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).2
  intro w hw
  exact f_nonsquare k ⟨w, by simpa [pow_two] using hw.symm⟩

theorem y_minpoly : minpoly (K k) (y k) = X^2-Polynomial.C (rf k D) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic (D_kummer_irreducible k)
  · simp [y_squared]
  · exact Polynomial.monic_X_pow_sub_C _ (by norm_num : (2:ℕ) ≠ 0)

theorem z_minpoly : minpoly (H k) (z k) = X^2-Polynomial.C (f k) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic (f_kummer_irreducible k)
  · simp [z_squared]
  · exact Polynomial.monic_X_pow_sub_C _ (by norm_num : (2:ℕ) ≠ 0)

theorem y_generates : IntermediateField.adjoin (K k) {y k} = ⊤ := by
  apply (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
    (IsIntegral.of_finite (K k) (y k)).isAlgebraic).2
  exact QuadraticAlgebra.adjoin_omega_eq_top

theorem z_generates : IntermediateField.adjoin (H k) {z k} = ⊤ := by
  apply (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
    (IsIntegral.of_finite (H k) (z k)).isAlgebraic).2
  exact QuadraticAlgebra.adjoin_omega_eq_top

-- Formal coefficient extension of the actual polynomial A*(a*(t-a))^2+B*a*(t-a)+C.
def actualQuartic : P[X] :=
  Polynomial.C A*(X*(Polynomial.C t-X))^2+
    Polynomial.C B*(X*(Polynomial.C t-X))+Polynomial.C C₀

theorem coefficient_extension : (actualQuartic.map (pk k)) = planeG k := by
  simp [actualQuartic,planeG]
  ring

theorem actual_quartic_irreducible : Irreducible (actualQuartic.map (pk k)) := by
  rw [coefficient_extension]
  exact planeG_irreducible k


end ActualTower

-- All hypotheses are discharged at the algebraically closed scalar extension.
theorem actual_geometric_irreducibility :
    Irreducible (actualQuartic.map (pk (AlgebraicClosure ℚ))) :=
  actual_quartic_irreducible (AlgebraicClosure ℚ)

section ExplicitCorrespondence
variable (k : Type*) [Field k] [CharZero k]

-- Identify the actual quartic quotient over k(b) with the two-quadratic field.
def quarticQuotientEquiv : AdjoinRoot (g k) ≃ₐ[K k] F k := by
  have hg : Associated (g k) (gm k) := by
    apply associated_of_dvd_dvd
    · exact ⟨Polynomial.C ((rf k A)⁻¹), by rw [gm]; ring⟩
    · refine ⟨Polynomial.C (rf k A), ?_⟩
      rw [gm, mul_right_comm, ← Polynomial.C_mul, inv_mul_cancel₀ (A_nonzero k)]
      simp
  have htop : Algebra.adjoin (K k) ({a k} : Set (F k)) = ⊤ :=
    (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
      (IsIntegral.of_finite (K k) (a k)).isAlgebraic).1 (a_generates k)
  exact (AdjoinRoot.algEquivOfAssociated (K k) (g k) (gm k) hg).trans
    ((AdjoinRoot.algEquivOfEq (K k) (gm k) (minpoly (K k) (a k)) (gm_minpoly k)).trans
      ((minpoly.equivAdjoin (IsIntegral.of_finite (K k) (a k))).trans
        ((Subalgebra.equivOfEq _ ⊤ htop).trans Subalgebra.topEquiv)))

theorem quarticQuotientEquiv_root :
    quarticQuotientEquiv k (AdjoinRoot.root (g k)) = a k := by
  simp [quarticQuotientEquiv, AdjoinRoot.algEquivOfEq_root,
    minpoly.coe_equivAdjoin]

-- The actual involution a ↦ t-a fixes exactly the embedded first quadratic field.
theorem involution_a : star (a k) = algebraMap (K k) (F k) (rf k t)-a k := by
  apply QuadraticAlgebra.ext <;>
    simp [a,z,QuadraticAlgebra.norm_def,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat,
      IsScalarTower.algebraMap_apply (K k) (H k) (F k)] <;> ring

theorem involution_fixed_iff (u : F k) :
    star u = u ↔ ∃ h : H k, algebraMap (H k) (F k) h = u := by
  constructor
  · intro he
    have him := congrArg QuadraticAlgebra.im he
    simp only [QuadraticAlgebra.im_star] at him
    have hz : u.im = 0 := by linear_combination - (1/2 : H k) * him
    exact ⟨u.re, by ext <;> simp [hz]⟩
  · rintro ⟨h,rfl⟩
    ext <;> simp
end ExplicitCorrespondence


-- Exact declarations and transitive standard-axiom closure from this source.
set_option pp.universes true

end
end NikandishE3
