/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/TwoUnitExponentSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/TwoUnitExponentSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both explicit irrational ideal-graph eigenvalues with two unit exponents. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.RepeatedPairSupport
import Mathlib.NumberTheory.Real.Irrational

/-! Source: PR3 b93becea662a746badeadba42fdc3d3eb3db9382,
paper/sections/pqrk.tex, blob7c91c849ebd0b16c81fd5344f4a210bd077db5b1.
The original full two-dimensional invariant subspace is transported through
the arbitrary-index repeated-pair operator to the actual ideal graph.
This retains both explicit eigenvalues, beyond the stronger already delivered
unit-exponent nonintegrality theorem. No bound on the third exponent is used. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.TwoUnitExponentSpectrum
open RepeatedPairSupport IdealIntersectionSupport IdealIntersectionObstructions

private def value (v : Fin 2 → ℝ) (S : Finset (Fin 1)) : ℝ :=
  if S=∅ then v 0 else v 1

private theorem intertwining (k : ℝ) (v : Fin 2 → ℝ) :
    K 1 (fun _ : Fin 1 => k)*ᵥvalue v =
      value ((!![2*k+3,k;1,2] : Matrix (Fin 2) (Fin 2) ℝ)*ᵥv) := by
  have h2 : (univ : Finset (Finset (Fin 1)))={∅,univ} := by decide
  ext S
  have hS : S∈({∅,univ} : Finset (Finset (Fin 1))) := by rw [←h2];exact mem_univ _
  simp only [mem_insert,mem_singleton] at hS
  rcases hS with rfl|rfl <;>
    norm_num [K,value,diagonalFactor,disjointKernel,Matrix.mulVec,dotProduct,
      h2,Fin.sum_univ_succ,Finset.prod_const] <;> ring <;> simp

private theorem value_nonzero (v : Fin 2 → ℝ) (hv : v ≠ 0) : value v ≠ 0 := by
  intro hz
  apply hv
  ext i
  fin_cases i
  · simpa [value] using congrFun hz ∅
  · simpa [value] using congrFun hz univ

private theorem sqrt_irrational (k : ℕ) (hk : 0<k) :
    Irrational (Real.sqrt (((2 : ℝ)*k+2)^2-3)) := by
  let h : ℤ:=2*(k : ℤ)+1
  have hs:=Real.sq_sqrt (show 0≤((2 : ℝ)*k+2)^2-3 by
    have h : (1 : ℝ)≤k:=by exact_mod_cast hk
    nlinarith)
  have hn:=Real.sqrt_nonneg (((2 : ℝ)*k+2)^2-3)
  have hkR : (1 : ℝ)≤k:=by exact_mod_cast hk
  have hl : (h : ℝ)<Real.sqrt (((2 : ℝ)*k+2)^2-3) := by
    dsimp [h];push_cast;nlinarith
  have hu : Real.sqrt (((2 : ℝ)*k+2)^2-3)<(h : ℝ)+1 := by
    dsimp [h];push_cast;nlinarith
  apply irrational_nrt_of_notint_nrt 2 ((2*(k : ℤ)+2)^2-3)
  · push_cast;exact hs
  · rintro ⟨z,hz⟩
    have hzl : h<z := by exact_mod_cast (show (h : ℝ)<(z : ℝ) by simpa [hz] using hl)
    have hzu : z<h+1 := by exact_mod_cast (show (z : ℝ)<(h : ℝ)+1 by simpa [hz] using hu)
    omega
  · norm_num

/-- Both original irrational eigenvalues, for every positive third exponent
and arbitrary distinct primes on the full three-coordinate set. -/
theorem result (p : Fin 2 ⊕ Fin 1 → ℕ) (hp : ∀i,Nat.Prime (p i))
    (hinj : Function.Injective p) (k : ℕ) (hk : 0<k)
    (sign : ℝ) (hsign : sign=1 ∨ sign= -1) :
    let ell : ℝ:=(6*k+1+sign*Real.sqrt (((2 : ℝ)*k+2)^2-3))/2
    Irrational ell ∧
      HasActualEigenvalue (modulus p (pairExponents 1 (fun _ : Fin 1 => k))) ell := by
  dsimp only
  let q : ℝ:=Real.sqrt (((2 : ℝ)*k+2)^2-3)
  let e : ℝ:=(2*k+5-sign*q)/2
  have hkR : (1 : ℝ)≤k:=by exact_mod_cast hk
  have hq : q^2=((2 : ℝ)*k+2)^2-3:=Real.sq_sqrt (by nlinarith)
  have hs : sign^2=1:=by rcases hsign with h|h <;>simp [h]
  have he : e^2-(2*k+5)*e+3*k+6=0:=by dsimp [e];nlinarith [hq]
  have hv : (![e-2,1] : Fin 2 → ℝ) ≠ 0:=by
    intro hz
    have h:=congrFun hz 1
    norm_num at h
  have hE : K 1 (fun _ : Fin 1 => (k : ℝ))*ᵥvalue ![e-2,1]=e • value ![e-2,1]:=by
    rw [intertwining]
    have hm : (!![2*(k : ℝ)+3,k;1,2] : Matrix (Fin 2) (Fin 2) ℝ)*ᵥ![e-2,1]=e • ![e-2,1]:=by
      ext i
      fin_cases i <;>norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;>nlinarith
    rw [hm]
    ext S
    simp [value,Pi.smul_apply,smul_eq_mul]
  have ha:=actual_paired_eigenvalue p hp hinj 1 (fun _ : Fin 1 => k)
    (by decide) (fun _=>hk) e (value ![e-2,1]) (value_nonzero _ hv)
    (by simpa only [Nat.cast_one] using hE)
  have hc : (((((1+1)^2*(∏ _i : Fin 1,k+1))-2 : ℕ) : ℝ)+1-e)=
      (6*k+1+sign*q)/2 := by
    simp only [Fin.prod_univ_one]
    have hn : 2≤4*(k+1):=by omega
    norm_num only [show (1+1 : ℕ)^2=4 by norm_num,Nat.cast_sub hn,
      Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
    dsimp [e]
    ring
  refine ⟨?_,?_⟩
  swap
  · convert ha using 1
    simpa [q] using hc.symm
  have hi : Irrational q:=sqrt_irrational k hk
  have hrat : (((6*(k : ℚ)+1) : ℚ) : ℝ)=6*(k : ℝ)+1:=by push_cast;rfl
  rcases hsign with h|h <;>rw [h]
  · simp only [one_mul]
    have h:=hi.ratCast_add (6*(k : ℚ)+1)
    rw [hrat] at h
    exact h.div_ratCast (q:=2) (by norm_num)
  · simp only [neg_one_mul]
    have h:=hi.ratCast_sub (6*(k : ℚ)+1)
    rw [hrat] at h
    simpa [q,sub_eq_add_neg] using h.div_ratCast (q:=2) (by norm_num)

end D5.S3.Combinatorics.SpectralGraph.TwoUnitExponentSpectrum
