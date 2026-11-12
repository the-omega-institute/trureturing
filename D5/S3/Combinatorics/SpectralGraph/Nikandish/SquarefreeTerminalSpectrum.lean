/- GID: D5/S3/Combinatorics/SpectralGraph/SquarefreeTerminalSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SquarefreeTerminalSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact odd and even alternating restrictions for every squarefree prime count. -/
import D5.S3.Combinatorics.SpectralGraph.SquarefreeAlternatingSupport
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-! PR3 squarefree.tex, blob 2cd18d52cd3f4581d624bb94006480340756a5c3.
The original odd 2D and even symmetric 3D restrictions are embedded in the
full subset tensor and then the actual ideal graph. No selected prime values
or bounded prime counts are used. Existing unit-entry nonintegrality remains
the supplier for its stronger conclusion. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.SquarefreeTerminalSpectrum
open SquarefreeAlternatingSupport RepeatedPairSupport IdealIntersectionSupport IdealIntersectionObstructions

private def operator {ι : Type*} [Fintype ι] [DecidableEq ι] (d f : ℝ) :
    Matrix (Finset ι) (Finset ι) ℝ :=
  d • E + f • F

private def oneValue (v : Fin 2 → ℝ) (S : Finset (Fin 1)) : ℝ :=
  if S=∅ then v 0 else v 1

private theorem one_intertwine (a s : ℝ) (v : Fin 2 → ℝ) :
    operator a (-s)*ᵥoneValue v=oneValue (!![2*a-s,-s;-s,a]*ᵥv) := by
  have h2 : (univ : Finset (Finset (Fin 1)))={∅,univ} := by decide
  ext S
  have hS : S∈({∅,univ} : Finset (Finset (Fin 1))) := by rw [←h2]; exact mem_univ _
  simp only [mem_insert,mem_singleton] at hS
  rcases hS with rfl|rfl <;>
    norm_num [operator,oneValue,diagonalFactor,disjointKernel,Matrix.mulVec,
      dotProduct,h2,Fin.sum_univ_succ,Finset.prod_const,E,F] <;> ring <;> simp

private theorem one_nonzero (v : Fin 2 → ℝ) (hv : v ≠ 0) : oneValue v ≠ 0 := by
  intro hz
  apply hv
  ext i
  fin_cases i
  · simpa [oneValue] using congrFun hz ∅
  · simpa [oneValue] using congrFun hz univ

private theorem odd_eigenpair (a s e : ℝ) (hs : s^2=1)
    (he : (2*a-s-e)*(a-e)-1=0) :
    operator a (-s)*ᵥoneValue ![a-e,s]=e • oneValue ![a-e,s] := by
  rw [one_intertwine]
  have hv : (!![2*a-s,-s;-s,a] : Matrix (Fin 2) (Fin 2) ℝ)*ᵥ![a-e,s]=e • ![a-e,s] := by
    ext i
    fin_cases i <;> norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> nlinarith
  rw [hv]
  ext S
  simp [oneValue,Pi.smul_apply,smul_eq_mul]

private theorem power_sign (r : ℕ) : ((-1 : ℝ)^r)^2=1 := by
  rcases neg_one_pow_eq_or ℝ r with h|h <;> simp [h]

private theorem odd_gap (r : ℕ) : 3≤(2 : ℝ)^(r+1)-(-1 : ℝ)^(r+1) := by
  cases r with
  | zero => norm_num
  | succ r =>
    have hpow : (4 : ℝ)≤2^(r+1+1) := by
      have h : (1 : ℝ)≤2^r := one_le_pow₀ (by norm_num)
      rw [show r+1+1=r+2 by omega,pow_add]
      norm_num
      linarith
    rcases neg_one_pow_eq_or ℝ (r+1+1) with h|h <;> rw [h] <;> linarith

private theorem odd_sqrt_irrational (r : ℕ) :
    Irrational (Real.sqrt (((2 : ℝ)^(r+1)-(-1 : ℝ)^(r+1))^2+4)) := by
  let h : ℤ:=2^(r+1)-(-1)^(r+1)
  have hc : (h : ℝ)=(2 : ℝ)^(r+1)-(-1 : ℝ)^(r+1) := by simp [h]
  have hh : 3≤(h : ℝ) := by rw [hc]; exact odd_gap r
  have hs:=Real.sq_sqrt (show 0≤(h : ℝ)^2+4 by positivity)
  have hn:=Real.sqrt_nonneg ((h : ℝ)^2+4)
  have hl : (h : ℝ)<Real.sqrt ((h : ℝ)^2+4) := by nlinarith
  have hu : Real.sqrt ((h : ℝ)^2+4)<(h : ℝ)+1 := by nlinarith
  rw [←hc]
  apply irrational_nrt_of_notint_nrt 2 (h^2+4)
  · push_cast; exact hs
  · rintro ⟨z,hz⟩
    have hzl : h<z := by exact_mod_cast (show (h : ℝ)<(z : ℝ) by simpa [hz] using hl)
    have hzu : z<h+1 := by exact_mod_cast (show (z : ℝ)<(h : ℝ)+1 by simpa [hz] using hu)
    omega
  · norm_num

/-- Both explicit irrational eigenvalues of the odd alternating restriction,
for every odd squarefree prime count at least three. The sign parameter
ranges over exactly plus and minus; both are included, not chosen as a premise. -/
theorem odd_spectrum (r : ℕ) (p : Fin 2 ⊕ Index r (Fin 1) → ℕ)
    (hp : ∀ i,Nat.Prime (p i)) (hinj : Function.Injective p)
    (sign : ℝ) (hsgn : sign=1 ∨ sign= -1) :
    let a : ℝ:=2^(r+1)
    let s : ℝ:=(-1)^(r+1)
    let c : ℝ:=(((((1+1)^2*(∏ _i : Index r (Fin 1),(1+1)))-2 : ℕ) : ℝ)+1)
    let ell : ℝ:=(2*c-3*a+s+sign*Real.sqrt ((a-s)^2+4))/2
    Irrational ell ∧ HasActualEigenvalue (modulus p (fun _=>1)) ell := by
  dsimp only
  let a : ℝ:=2^(r+1)
  let s : ℝ:=(-1)^(r+1)
  let cN : ℕ:=(1+1)^2*(∏ _i : Index r (Fin 1),(1+1))-2
  let c : ℝ:=(cN : ℝ)+1
  let q : ℝ:=Real.sqrt ((a-s)^2+4)
  let e : ℝ:=(3*a-s-sign*q)/2
  have hs : s^2=1:=power_sign (r+1)
  have hq : q^2=(a-s)^2+4:=Real.sq_sqrt (by positivity)
  have hsgn2 : sign^2=1 := by rcases hsgn with h|h <;> simp [h]
  have he : (2*a-s-e)*(a-e)-1=0 := by dsimp [e]; nlinarith [hq]
  have hv : (![a-e,s] : Fin 2 → ℝ) ≠ 0 := by
    intro hz
    have h:=congrFun hz 1
    norm_num at h
    nlinarith [hs]
  have hf : ((-1 : ℝ)^r)= -s := by dsimp [s]; rw [pow_succ]; ring
  have hE:=odd_eigenpair a s e hs he
  have hactual:=SquarefreeAlternatingSupport.actual_eigenvalue r p hp hinj e
    (oneValue ![a-e,s]) (one_nonzero _ hv) (by simpa only [reduced,operator,hf] using hE)
  have heq : (2*c-3*a+s+sign*q)/2=c-e := by dsimp [e]; ring
  have hi:=odd_sqrt_irrational r
  have hrat : ((2*(cN : ℚ)+2-3*2^(r+1)+(-1)^(r+1) : ℚ) : ℝ)=2*c-3*a+s := by
    simp [c,a,s]; ring
  have hir : Irrational ((2*c-3*a+s+sign*q)/2) := by
    have hqir : Irrational q:=hi
    rcases hsgn with h|h <;> rw [h]
    · simp only [one_mul]
      have h:=hqir.ratCast_add (2*(cN : ℚ)+2-3*2^(r+1)+(-1)^(r+1))
      rw [hrat] at h
      exact h.div_ratCast (q:=2) (by norm_num)
    · simp only [neg_one_mul]
      have h:=hqir.ratCast_sub (2*(cN : ℚ)+2-3*2^(r+1)+(-1)^(r+1))
      rw [hrat] at h
      simpa [sub_eq_add_neg] using h.div_ratCast (q:=2) (by norm_num)
  refine ⟨hir,?_⟩
  rw [heq]
  simpa [c, cN, show pairExponents 1 (fun _ : Index r (Fin 1) => 1) = (fun _ => 1) by
    funext i; cases i <;> rfl] using hactual

/-- Exact symmetric restriction on the last two tensor coordinates. -/
def evenK (a s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![4*a-s,-s*Real.sqrt 2,-s;
     -s*Real.sqrt 2,2*a-s,0;
     -s,0,a]

private def evenValue (v : Fin 3 → ℝ) (S : Finset (Fin 2)) : ℝ :=
  if S=∅ then v 0 else if S=univ then v 2 else v 1/Real.sqrt 2

private theorem even_intertwine (a s : ℝ) (v : Fin 3 → ℝ) :
    operator a (-s)*ᵥevenValue v=evenValue (evenK a s*ᵥv) := by
  have h4 : (univ : Finset (Finset (Fin 2)))={∅,{0},{1},univ} := by decide
  have hne : (univ : Finset (Fin 2)) ≠ ∅ := by decide
  have hne0 : (univ : Finset (Fin 2)) ≠ {0} := by decide
  have hne1 : (univ : Finset (Fin 2)) ≠ {1} := by decide
  have hc0 : ((univ : Finset (Fin 2)) \ {0}).card = 1 := by decide
  have hc1 : ((univ : Finset (Fin 2)) \ {1}).card = 1 := by decide
  have hs : (Real.sqrt 2)^2=2:=Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0:=by positivity
  ext S
  have hS : S∈({∅,{0},{1},univ} : Finset (Finset (Fin 2))) := by rw [←h4]; exact mem_univ _
  simp only [mem_insert,mem_singleton] at hS
  rcases hS with rfl|rfl|rfl|rfl <;>
    simp (disch := decide) [operator,evenValue,evenK,diagonalFactor,disjointKernel,Matrix.mulVec,
      dotProduct,h4,Fin.sum_univ_succ,Finset.prod_const,E,F,Matrix.diagonal_apply,
      hne,Ne.symm hne,hne0,Ne.symm hne0,hne1,Ne.symm hne1,hc0,hc1] <;>
    field_simp [hn] <;> ring_nf <;> norm_num [Real.sq_sqrt] <;> ring

private theorem even_nonzero (v : Fin 3 → ℝ) (hv : v ≠ 0) : evenValue v ≠ 0 := by
  intro hz
  apply hv
  have h0:=congrFun hz ∅
  have h1:=congrFun hz ({0} : Finset (Fin 2))
  have h2:=congrFun hz univ
  ext i
  fin_cases i <;> norm_num [evenValue] at h0 h1 h2 ⊢ <;> tauto

private theorem even_hermitian (a s : ℝ) : (evenK a s).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenK,conjTranspose_apply]

private theorem even_lower (a s : ℝ) (ha : 2≤a) (hs : s^2=1) :
    (evenK a s-(a-1) • 1).PosDef := by
  have hsl : -1≤s ∧ s≤1:=by constructor <;> nlinarith
  have hd : 0<a+1-s:=by linarith
  have hcoef : 0<3*a-s-2/(a+1-s) := by
    have hprod : 0<(3*a-s)*(a+1-s)-2:=by nlinarith
    exact sub_pos.mpr ((div_lt_iff₀ hd).mpr (by nlinarith [hprod]))
  have hsq : (Real.sqrt 2)^2=2:=Real.sq_sqrt (by norm_num)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact (even_hermitian a s).sub (by simp)
  · intro v hv
    have he : star v ⬝ᵥ ((evenK a s-(a-1) • 1)*ᵥv)=
        (v 2-s*v 0)^2+(a+1-s)*(v 1-s*Real.sqrt 2/(a+1-s)*v 0)^2+
          (3*a-s-2/(a+1-s))*(v 0)^2 := by
      simp [evenK,dotProduct,Matrix.mulVec,Fin.sum_univ_succ]
      rcases sq_eq_one_iff.mp hs with rfl | rfl <;>
        field_simp [hd.ne'] <;> ring_nf <;> norm_num [Real.sq_sqrt] <;> ring
    rw [he]
    by_cases h0 : v 0=0
    · by_cases h1 : v 1=0
      · have h2 : v 2 ≠ 0 := by
          intro h
          apply hv
          ext i
          fin_cases i <;> simp [h0,h1,h]
        simpa [h0,h1] using sq_pos_of_ne_zero h2
      · have hp:=mul_pos hd (sq_pos_of_ne_zero h1)
        simpa [h0] using add_pos_of_nonneg_of_pos (sq_nonneg (v 2)) hp
    · have hp:=mul_pos hcoef (sq_pos_of_ne_zero h0)
      exact add_pos_of_nonneg_of_pos
        (add_nonneg (sq_nonneg _) (mul_nonneg hd.le (sq_nonneg _))) hp

private theorem even_upper (a s : ℝ) (ha : 2≤a) (hs : s^2=1) :
    ¬(evenK a s-a • 1).PosSemidef := by
  intro hp
  have hh:=hp.dotProduct_mulVec_nonneg (![1,0,s*(3*a-s+1)] : Fin 3 → ℝ)
  have he : star (![1,0,s*(3*a-s+1)] : Fin 3 → ℝ) ⬝ᵥ
      ((evenK a s-a • 1)*ᵥ![1,0,s*(3*a-s+1)])= -(3*a-s)-2 := by
    norm_num [evenK,dotProduct,Matrix.mulVec,Fin.sum_univ_succ]
    rcases sq_eq_one_iff.mp hs with rfl | rfl <;> ring
  rw [he] at hh
  nlinarith [hs]

/-- Every eigenvalue of the even restriction is above a-1, and one is
below a. In particular its actual smallest eigenvalue is in (a-1,a). -/
theorem even_window (a s : ℝ) (ha : 2≤a) (hs : s^2=1) :
    (∀ e : ℝ,∀v : Fin 3 → ℝ,v ≠ 0 → evenK a s*ᵥv=e • v → a-1<e) ∧
    ∃ e : ℝ,a-1<e ∧ e<a ∧ ∃v : Fin 3 → ℝ,v ≠ 0 ∧ evenK a s*ᵥv=e • v := by
  have hl (e : ℝ) (v : Fin 3 → ℝ) (hv : v ≠ 0) (he : evenK a s*ᵥv=e • v) : a-1<e:=by
    have hp:=(even_lower a s ha hs).dotProduct_mulVec_pos hv
    have hn : 0<dotProduct v v:=by simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hv
    rw [sub_mulVec,he,smul_mulVec,one_mulVec] at hp
    simp only [star_trivial,dotProduct_sub,dotProduct_smul,smul_eq_mul] at hp
    nlinarith
  refine ⟨hl,?_⟩
  obtain ⟨e,he,v,hv,hE⟩:=PairedIdealIntersectionObstructions.negative_eigenpair_of_not_posSemidef
    (evenK a s-a • 1) ((even_hermitian a s).sub (by simp)) (even_upper a s ha hs)
  have hh : evenK a s*ᵥv=(e+a) • v:=by
    rw [sub_mulVec,smul_mulVec,one_mulVec] at hE
    ext i
    have h:=congrFun hE i
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at h ⊢
    linarith
  exact ⟨e+a,hl _ v hv hh,by linarith,v,hv,hh⟩

/-- The even squarefree construction supplies an actual graph eigenvalue
in the original strict consecutive-integer interval for every even count
at least four, with arbitrary distinct primes. -/
theorem even_spectrum (r : ℕ) (p : Fin 2 ⊕ Index r (Fin 2) → ℕ)
    (hp : ∀i,Nat.Prime (p i)) (hinj : Function.Injective p) :
    let a : ℝ:=2^(r+1)
    let c : ℝ:=(((((1+1)^2*(∏ _i : Index r (Fin 2),(1+1)))-2 : ℕ) : ℝ)+1)
    ∃ ell : ℝ,c-a<ell ∧ ell<c-a+1 ∧
      HasActualEigenvalue (modulus p (fun _=>1)) ell := by
  dsimp only
  let a : ℝ:=2^(r+1)
  let s : ℝ:=(-1)^(r+1)
  have ha : 2≤a:=by
    have h : (1 : ℝ)≤2^r:=one_le_pow₀ (by norm_num)
    dsimp [a]
    rw [pow_succ]
    linarith
  obtain ⟨_,e,hel,heu,v,hv,he⟩:=even_window a s ha (power_sign (r+1))
  have hE : operator a (-s)*ᵥevenValue v=e • evenValue v:=by
    rw [even_intertwine,he]
    ext S
    simp only [evenValue,Pi.smul_apply,smul_eq_mul]
    split_ifs <;> ring
  have hf : ((-1 : ℝ)^r)= -s:=by dsimp [s];rw[pow_succ];ring
  have hactual:=SquarefreeAlternatingSupport.actual_eigenvalue r p hp hinj e (evenValue v)
    (even_nonzero v hv) (by simpa only [reduced,operator,hf] using hE)
  have hactual2 : HasActualEigenvalue (modulus p (fun _ => 1))
      (((4 * ∏ _i : Index r (Fin 2), (2 : ℕ)) - 2 : ℕ) + 1 - e) := by
    simpa only [show pairExponents 1 (fun _ : Index r (Fin 2) => 1) = (fun _ => 1) by
      funext i; cases i <;> rfl] using hactual
  refine ⟨_, ?_, ?_, hactual2⟩ <;> norm_num only [show (1+1:ℕ)=2 by norm_num, show (2:ℕ)^2=4 by norm_num] <;>
    dsimp only [a] at * <;> linarith

end D5.S3.Combinatorics.SpectralGraph.SquarefreeTerminalSpectrum
