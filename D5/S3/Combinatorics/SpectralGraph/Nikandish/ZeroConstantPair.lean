/- GID: D5/S3/Combinatorics/SpectralGraph/ZeroConstantPair
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ZeroConstantPair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete zero-constant repeated-pair family, with its integral denominator obstruction. -/
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionLift
import D5.S3.Combinatorics.SpectralGraph.PairedTensorMinimum
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionDeterminants

/-! Source: four-prime-zero-constant, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02. The entire a>=2,c>=a
family is included, with no coprimality or tail-ordering premise. The
local resonance example is diagnostic; it is not a replacement for this
unbounded polynomial and actual graph proof. General Q3 stays open. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.ZeroConstantPair
open PairedIdealIntersectionObstructions PairedIdealIntersectionDeterminants
open PairedIdealIntersectionLift IdealIntersectionSupport IdealIntersectionObstructions

def tail {R : Type*} [CommRing R] (a : R) : R := (a-1)*(2*a-1)
def N {R : Type*} [CommRing R] (a : R) : R := 4*a^5-4*a^4+a^3-2*a^2+1
def D {R : Type*} [CommRing R] (a : R) : R := 2*a^3-5*a^2+3*a+1

theorem denominator_bezout {R : Type*} [CommRing R] (a : R) :
    (3*a^2-9*a+7)*N a+(-6*a^4+9*a^3-2*a^2+6*a+1)*D a=8 := by
  unfold N D
  ring

private theorem D_positive (a : ℤ) (ha : 2≤a) : 3≤D a := by
  let v:=a-2
  have hv : 0≤v := by dsimp [v]; omega
  have he : D a=2*v^3+7*v^2+7*v+3 := by dsimp [D,v]; ring
  rw [he]
  have h1 : 0≤2*v^3+7*v^2+7*v := by positivity
  linarith

private theorem D_odd (a : ℤ) : D a%2=1 := by
  have h : a%2=0 ∨ a%2=1 := by omega
  rcases h with h | h <;>
    norm_num [D,Int.add_emod,Int.sub_emod,Int.mul_emod,pow_succ,h]

/-- The sole positive rational candidate has a nontrivial denominator at
every integer a>=2. No tail-size bound is assumed. -/
theorem denominator_obstruction (a c : ℤ) (ha : 2≤a) : N a-D a*c≠0 := by
  intro hz
  have hN : D a∣N a := ⟨c,by linarith⟩
  have h8 : D a∣(8:ℤ) := by
    rw [←denominator_bezout a]
    exact dvd_add (dvd_mul_of_dvd_right hN _) (dvd_mul_left _ _)
  obtain ⟨z,hz⟩:=h8
  have hD:=D_positive a ha
  have hodd:=D_odd a
  have hz0 : 0<z := by nlinarith
  have hz2 : z≤2 := by nlinarith
  have hcases : z=1 ∨ z=2 := by omega
  rcases hcases with rfl | rfl <;> omega

/-- Exact root-two factorization of the whole four-cell operator. -/
theorem factor_two {R : Type*} [CommRing R] (a c : R) :
    (tensorK a (tail a) c-(2:R) • 1).det=2*a*(a-1)*c*(N a-D a*c) := by
  rw [det_tensorK_sub_scalar]
  unfold tail N D
  ring

/-- Endpoint two is excluded over all positive integer free tails. -/
theorem two_nonzero (a c : ℤ) (ha : 2≤a) (hc : 0<c) :
    (tensorK a (tail a) c-(2:ℤ) • 1).det≠0 := by
  rw [factor_two]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (by omega)) (by omega)) (by omega)) (denominator_obstruction a c ha)

/-- Negative empty/full principal minor on every real a>=2,c>=a. -/
theorem low_eigenpair (a c : ℝ) (ha : 2≤a) (hc : a≤c) :
    ∃ e : ℝ, 1<e ∧ e<3 ∧ ∃ v : Fin 2 × Fin 2 → ℝ,
      v≠0 ∧ symmetricK a (tail a) c*ᵥv=e • v := by
  let b:=tail a
  have hb : a≤b := by
    have he : b-a=2*(a-2)^2+4*(a-2)+1 := by dsimp [b,tail]; ring
    have hp : 0<b-a := by rw [he]; positivity
    linarith
  let M:=symmetricK a b c-(3:ℝ) • 1
  have hM : M.IsHermitian := (symmetric_hermitian a b c).sub (by simp)
  have hno : ¬M.PosSemidef := by
    intro hp
    let j : Fin 2 → Fin 2 × Fin 2 := fun i => if i=0 then (0,0) else (1,1)
    have hd:=(hp.submatrix j).det_nonneg
    have he : (M.submatrix j j).det =
        -(2*a^3-4*a+4)*(c-a)-(5*a^3-6*a^2+5*a-2) := by
      simp [M,j,symmetricK,E,H,Matrix.det_fin_two,Matrix.submatrix,kroneckerMap_apply]
      ring_nf
      simp [Real.sq_sqrt (by linarith : 0≤b),Real.sq_sqrt (by linarith : 0≤c)]
      dsimp [b,tail]
      ring
    have h1 : 0<2*a^3-4*a+4 := by
      have he : 2*a^3-4*a+4=2*(a-2)^3+12*(a-2)^2+20*(a-2)+12 := by ring
      rw [he]; positivity
    have h2 : 0<5*a^3-6*a^2+5*a-2 := by
      have he : 5*a^3-6*a^2+5*a-2=5*(a-2)^3+24*(a-2)^2+41*(a-2)+24 := by ring
      rw [he]; positivity
    rw [he] at hd
    have h3 : 0≤(2*a^3-4*a+4)*(c-a) := mul_nonneg h1.le (by linarith)
    linarith
  obtain ⟨e,he,v,hv,hve⟩ := negative_eigenpair_of_not_posSemidef M hM hno
  have hS : symmetricK a b c*ᵥv=(e+3) • v := by
    dsimp [M] at hve
    rw [sub_mulVec,smul_mulVec,one_mulVec] at hve
    ext q
    have ht:=congrFun hve q
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at ht ⊢
    linarith
  exact ⟨e+3,symmetric_eigenvalue_gt_one a b c (by linarith)
    (by linarith) (by linarith) _ v hv hS,by linarith,v,hv,hS⟩

/-- Noninteger eigenpair on the genuine K, for the full original natural domain. -/
theorem noninteger_eigenpair (a c : ℕ) (ha : 2≤a) (hc : a≤c) :
    ∃ e : ℝ, 1<e ∧ e<3 ∧ (¬∃ z : ℤ, e=z) ∧
      ∃ h : Fin 2 × Fin 2 → ℝ, h≠0 ∧
        tensorK (a:ℝ) (tail (a:ℝ)) (c:ℝ)*ᵥh=e • h := by
  obtain ⟨e,hel,heu,v,hv,hE⟩:=low_eigenpair (a:ℝ) (c:ℝ)
    (by exact_mod_cast ha) (by exact_mod_cast hc)
  have haR : (2:ℝ)≤a := by exact_mod_cast ha
  have ha0 : (0:ℝ)<a := by linarith
  have hc0 : (0:ℝ)<c := by exact_mod_cast (show 0<c by omega)
  have hb : (0:ℝ)<tail (a:ℝ) := by
    unfold tail
    exact mul_pos (by linarith) (by linarith)
  obtain ⟨h,hh,hT⟩:=tensor_eigenpair_of_symmetric (a:ℝ) (tail (a:ℝ)) (c:ℝ)
    hb (by exact_mod_cast (show 0<c by omega)) e v hv hE
  have hd : (tensorK (a:ℝ) (tail (a:ℝ)) (c:ℝ)-(2:ℝ) • 1).det≠0 := by
    rw [factor_two]
    have hZ:=denominator_obstruction (a:ℤ) (c:ℤ) (by omega)
    have hr : N (a:ℝ)-D (a:ℝ)*(c:ℝ)≠0 := by unfold N D at *; exact_mod_cast hZ
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      ha0.ne') (by linarith)) hc0.ne') hr
  refine ⟨e,hel,heu,?_,h,hh,hT⟩
  rintro ⟨z,hz⟩
  have hz1 : (1:ℤ)<z := by exact_mod_cast (hz ▸ hel)
  have hz3 : z<(3:ℤ) := by exact_mod_cast (hz ▸ heu)
  have hz2 : z=2 := by omega
  have he2 : e=2 := by simpa [hz2] using hz
  apply hh
  apply Matrix.eq_zero_of_mulVec_eq_zero hd
  rw [sub_mulVec,hT,smul_mulVec,one_mulVec,he2,sub_self]

/-- Full original zero-constant family on the actual graph. -/
theorem actual_nonintegral (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a c : ℕ) (ha : 2≤a) (hc : a≤c) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents a ((a-1)*(2*a-1)) c)) := by
  let b : ℕ := (a-1)*(2*a-1)
  have hb : 0<b := by dsimp [b]; exact mul_pos (by omega) (by omega)
  have hbr : (b:ℝ)=tail (a:ℝ) := by
    dsimp [b,tail]
    rw [Nat.cast_mul,Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
    push_cast
    ring
  obtain ⟨e,_,_,hne,h,hh,hT⟩:=noninteger_eigenpair a c ha hc
  rw [←hbr] at hT
  have he:=actual_paired_eigenvalue p hp hinj a b c (by omega) hb (by omega) e h hh hT
  intro H
  obtain ⟨z,hz⟩:=H _ he
  apply hne
  refine ⟨((((a+1)^2*(b+1)*(c+1)-2:ℕ):ℤ)+1-z),?_⟩
  push_cast
  linarith

/-- The full original smallest-root interval, with every real eigenpair in
the minimum comparison. The free tail is only required to be at least a. -/
theorem minimum_window (a c : ℝ) (ha : 2≤a) (hc : a≤c) :
    ∃ e : ℝ, 1<e ∧ e<3 ∧ ∃ h : Fin 2 × Fin 2 → ℝ,
      h≠0 ∧ tensorK a (tail a) c*ᵥh=e • h ∧
      ∀ r : ℝ, ∀ z : Fin 2 × Fin 2 → ℝ, z≠0 → tensorK a (tail a) c*ᵥz=r • z → e≤r := by
  have hb : 0<tail a := by unfold tail; exact mul_pos (by linarith) (by linarith)
  obtain ⟨e,hel,h,hh,hE,hmin⟩:=PairedTensorMinimum.minimum a (tail a) c
    (by linarith) hb (by linarith)
  obtain ⟨r,_,hr,v,hv,hR⟩:=low_eigenpair a c ha hc
  obtain ⟨z,hz,hT⟩:=tensor_eigenpair_of_symmetric a (tail a) c hb (by linarith) r v hv hR
  exact ⟨e,hel,lt_of_le_of_lt (hmin r z hz hT) hr,h,hh,hE,hmin⟩

end D5.S3.Combinatorics.SpectralGraph.ZeroConstantPair
