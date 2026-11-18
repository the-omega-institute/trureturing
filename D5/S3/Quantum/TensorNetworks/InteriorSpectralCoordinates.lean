/- GID: D5/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/InteriorSpectralCoordinates
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.Eval]
   utility: none
   digest: Literal independent-denominator real spectral coordinates of the actual native data. -/

import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace D5.S3.Quantum.TensorNetworks.InteriorSpectralCoordinates
open Matrix MvPolynomial
open scoped Matrix BigOperators
open PeriodicMPSParentIntersection (Bond)
open OpenBoundaryMPSDensityGenericity (realCoeff imagCoeff coefficient_eval)

abbrev CP := MvPolynomial (Fin 15) ℂ
abbrev RP := MvPolynomial (Fin 15) ℝ

/-- Spectral X,Y occupy 0,1; the unchanged canonical thirteen coordinates follow. -/
def point (x : Fin 13 → ℝ) (e : ℂ) : Fin 15 → ℝ := Fin.append ![e.re,e.im] x

def liftBase (p : OpenBoundaryMPSQ2PolynomialFiber.Poly) : CP := rename (Fin.natAdd 2) p

def root : CP := X 0 + C Complex.I * X 1

def c (i : Fin 5) : CP := liftBase (OpenBoundaryMPSQ2PolynomialFiber.coreVariable i)
def eta : CP := liftBase OpenBoundaryMPSQ2PolynomialFiber.etaVariable

private lemma point_base (x : Fin 13 → ℝ) (e : ℂ) (i : Fin 13) :
    point x e (Fin.natAdd 2 i) = x i := Fin.append_right _ _ _

private lemma eval_liftBase (x : Fin 13 → ℝ) (e : ℂ) (p : OpenBoundaryMPSQ2PolynomialFiber.Poly) :
    eval (fun i => (point x e i : ℂ)) (liftBase p) = OpenBoundaryMPSQ2PolynomialFiber.evaluate x p := by
  rw [liftBase, eval_rename]
  have hv : ((fun i => (point x e i : ℂ)) ∘ Fin.natAdd 2) = (fun i => (x i : ℂ)) := by
    funext i; simp [Function.comp_def, point_base]
  rw [hv]

private lemma eval_c (x : Fin 13 → ℝ) (e : ℂ) (i : Fin 5) :
    eval (fun j => (point x e j : ℂ)) (c i) = OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x i := by
  rw [c, eval_liftBase]
  apply Complex.ext <;> simp [OpenBoundaryMPSQ2PolynomialFiber.evaluate,OpenBoundaryMPSQ2PolynomialFiber.coreVariable,OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates]

private lemma eval_eta (x : Fin 13 → ℝ) (e : ℂ) :
    eval (fun j => (point x e j : ℂ)) eta = OpenBoundaryMPSQ2PolynomialFiber.eta x := by
  rw [eta, eval_liftBase]
  exact OpenBoundaryMPSQ2PolynomialFiber.evaluate_eta x

private lemma eval_root (x : Fin 13 → ℝ) (e : ℂ) :
    eval (fun j => (point x e j : ℂ)) root = e := by
  apply Complex.ext <;> simp [root,point,Fin.append,Fin.addCases]

/-- Ordinary complex polynomial pairs; each real projection has its own norm denominator. -/
structure Frac where
  num : CP
  den : CP

namespace Frac

def ofPoly (p : CP) : Frac := ⟨p,1⟩
def add (a b : Frac) : Frac := ⟨a.num*b.den+b.num*a.den,a.den*b.den⟩
def neg (a : Frac) : Frac := ⟨-a.num,a.den⟩
def sub (a b : Frac) : Frac := add a (neg b)
def mul (a b : Frac) : Frac := ⟨a.num*b.num,a.den*b.den⟩
def inv (a : Frac) : Frac := ⟨a.den,a.num⟩
def div (a b : Frac) : Frac := mul a (inv b)
def pow (a : Frac) : ℕ → Frac
  | 0 => ofPoly 1
  | n+1 => mul (pow a n) a

def Rep (a : Fin 15 → ℝ) (f : Frac) (z : ℂ) : Prop :=
  eval (fun i => (a i : ℂ)) f.den ≠ 0 ∧
    eval (fun i => (a i : ℂ)) f.num / eval (fun i => (a i : ℂ)) f.den = z

private lemma of_rep (a : Fin 15 → ℝ) (p : CP) :
    Rep a (ofPoly p) (eval (fun i => (a i : ℂ)) p) := by simp [Rep,ofPoly]
private lemma add_rep {a : Fin 15 → ℝ} {f g : Frac} {z w : ℂ}
    (hf : Rep a f z) (hg : Rep a g w) : Rep a (add f g) (z+w) := by
  refine ⟨by simpa [add] using mul_ne_zero hf.1 hg.1, ?_⟩
  dsimp [add]
  simp only [map_add,map_mul]
  rw [← hf.2,← hg.2]
  field_simp [hf.1,hg.1]
  <;> ring
private lemma neg_rep {a : Fin 15 → ℝ} {f : Frac} {z : ℂ}
    (hf : Rep a f z) : Rep a (neg f) (-z) := by
  refine ⟨hf.1,?_⟩
  simp only [neg,map_neg]
  rw [neg_div,hf.2]
private lemma sub_rep {a : Fin 15 → ℝ} {f g : Frac} {z w : ℂ}
    (hf : Rep a f z) (hg : Rep a g w) : Rep a (sub f g) (z-w) := by
  simpa [sub,sub_eq_add_neg] using add_rep hf (neg_rep hg)
private lemma mul_rep {a : Fin 15 → ℝ} {f g : Frac} {z w : ℂ}
    (hf : Rep a f z) (hg : Rep a g w) : Rep a (mul f g) (z*w) := by
  refine ⟨by simpa [mul] using mul_ne_zero hf.1 hg.1, ?_⟩
  dsimp [mul]
  simp only [map_mul]
  rw [← hf.2,← hg.2]
  ring
private lemma inv_rep {a : Fin 15 → ℝ} {f : Frac} {z : ℂ}
    (hf : Rep a f z) (hz : z ≠ 0) : Rep a (inv f) z⁻¹ := by
  have hn : eval (fun i => (a i : ℂ)) f.num ≠ 0 := by
    intro h; exact hz (hf.2.symm.trans (by simp [h]))
  refine ⟨hn,?_⟩
  dsimp [inv]
  rw [← hf.2,inv_div]
private lemma div_rep {a : Fin 15 → ℝ} {f g : Frac} {z w : ℂ}
    (hf : Rep a f z) (hg : Rep a g w) (hw : w ≠ 0) : Rep a (div f g) (z/w) :=
  mul_rep hf (inv_rep hg hw)
private lemma pow_rep {a : Fin 15 → ℝ} {f : Frac} {z : ℂ}
    (hf : Rep a f z) (n : ℕ) : Rep a (pow f n) (z^n) := by
  induction n with
  | zero => simpa [pow] using of_rep a 1
  | succ n ih => simpa [pow,pow_succ] using mul_rep ih hf

def realNum (f : Frac) : RP :=
  realCoeff f.num * realCoeff f.den + imagCoeff f.num * imagCoeff f.den

def imagNum (f : Frac) : RP :=
  imagCoeff f.num * realCoeff f.den - realCoeff f.num * imagCoeff f.den

def realDen (f : Frac) : RP := realCoeff f.den ^ 2 + imagCoeff f.den ^ 2

private lemma real_rep {a : Fin 15 → ℝ} {f : Frac} {z : ℂ} (hf : Rep a f z) :
    eval a (realDen f) ≠ 0 ∧
    eval a (realNum f) / eval a (realDen f) = z.re ∧
    eval a (imagNum f) / eval a (realDen f) = z.im := by
  have hn := coefficient_eval f.num a
  have hd := coefficient_eval f.den a
  have hh : eval a (realDen f) = Complex.normSq (eval (fun i => (a i : ℂ)) f.den) := by
    simp only [realDen,map_add,map_pow,hd.1,hd.2,Complex.normSq_apply]
    ring
  refine ⟨by rw [hh]; exact (Complex.normSq_pos.mpr hf.1).ne',?_,?_⟩
  · rw [← hf.2,Complex.div_re]
    simp only [realNum,map_add,map_mul,hn.1,hn.2,hd.1,hd.2,hh]
    ring
  · rw [← hf.2,Complex.div_im]
    simp only [imagNum,map_sub,map_mul,hn.1,hn.2,hd.1,hd.2,hh]
    ring
end Frac

private abbrev FM := Matrix (Fin 2) (Fin 2) Frac
private def mmul (A B : FM) : FM := fun i j =>
  Frac.add (Frac.mul (A i 0) (B 0 j)) (Frac.mul (A i 1) (B 1 j))
private def mdet (A : FM) : Frac :=
  Frac.sub (Frac.mul (A 0 0) (A 1 1)) (Frac.mul (A 0 1) (A 1 0))
private def minv (A : FM) : FM := fun i j =>
  Frac.div (!![A 1 1,Frac.neg (A 0 1);Frac.neg (A 1 0),A 0 0] i j) (mdet A)
private def MRep (a : Fin 15 → ℝ) (f : FM) (A : Bond) : Prop :=
  ∀ i j, Frac.Rep a (f i j) (A i j)
private lemma mmul_rep {a : Fin 15 → ℝ} {f g : FM} {A B : Bond}
    (hf : MRep a f A) (hg : MRep a g B) : MRep a (mmul f g) (A*B) := by
  intro i j
  simpa [mmul,Matrix.mul_apply,Fin.sum_univ_two] using
    Frac.add_rep (Frac.mul_rep (hf i 0) (hg 0 j)) (Frac.mul_rep (hf i 1) (hg 1 j))
private lemma mdet_rep {a : Fin 15 → ℝ} {f : FM} {A : Bond}
    (hf : MRep a f A) : Frac.Rep a (mdet f) A.det := by
  simpa [mdet,det_fin_two] using
    Frac.sub_rep (Frac.mul_rep (hf 0 0) (hf 1 1)) (Frac.mul_rep (hf 0 1) (hf 1 0))
private lemma minv_rep {a : Fin 15 → ℝ} {f : FM} {A : Bond}
    (hf : MRep a f A) (hA : A.det ≠ 0) : MRep a (minv f) A⁻¹ := by
  intro i j
  have ha : Frac.Rep a
      (!![f 1 1,Frac.neg (f 0 1);Frac.neg (f 1 0),f 0 0] i j) (A.adjugate i j) := by
    fin_cases i <;> fin_cases j <;> simp only [adjugate_fin_two,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    · exact hf 1 1
    · exact Frac.neg_rep (hf 0 1)
    · exact Frac.neg_rep (hf 1 0)
    · exact hf 0 0
  have hh := Frac.div_rep ha (mdet_rep hf) hA
  simpa [minv,Matrix.inv_def,Ring.inverse_eq_inv,smul_eq_mul,div_eq_mul_inv,mul_comm] using hh

private def core0 : FM := fun i j => Frac.ofPoly
  (!![c 1,c 2;1-c 0*c 1,-c 0*c 2] i j)
private def lam : Frac := Frac.div (Frac.ofPoly (c 4-c 1+root)) (Frac.ofPoly (2*c 2))
private def mu : Frac := Frac.div (Frac.ofPoly (c 4-c 1-root)) (Frac.ofPoly (2*c 2))
private def frame : FM := mmul core0 !![Frac.ofPoly 1,Frac.ofPoly 1;lam,mu]
private def conjugated : FM := mmul (minv frame) (mmul core0 frame)
private def gap : Frac := Frac.div (Frac.ofPoly (-root)) (Frac.ofPoly (c 2))
private def rho : Frac := Frac.div (Frac.ofPoly (-c 2))
  (Frac.mul (Frac.mul gap (conjugated 0 0)) (conjugated 0 1))
private def gauge : FM := fun i j =>
  if j = 0 then frame i 0 else Frac.mul (frame i 1) rho
private def nativeZ : Frac := Frac.div (Frac.ofPoly (-c 2))
  (Frac.mul gap (Frac.pow (conjugated 0 0) 2))
private def offset : Frac := Frac.div
  (Frac.mul (Frac.mul gap (conjugated 0 1)) (conjugated 1 0)) (Frac.ofPoly (-c 2))
private def right (N : ℕ) (i : Fin 2) : Frac := Frac.mul (Frac.pow (conjugated 0 0) N)
  (Frac.add ((minv gauge) i 0) (Frac.mul ((minv gauge) i 1) (Frac.ofPoly eta)))

/-- Eight complex native coordinates in the original sector, left, right, z order. -/
def nativeTerms (N : ℕ) : Fin 8 → Frac :=
  ![lam,mu,Frac.sub lam offset,Frac.ofPoly 1,rho,right N 0,right N 1,nativeZ]

private lemma nativeTerms_rep (x : Fin 13 → ℝ) (e : ℂ)
    (hc : OpenBoundaryMPSSpectralExtraction.Admissible (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e) (N : ℕ) :
    ∀ i, Frac.Rep (point x e) (nativeTerms N i)
      (![OpenBoundaryMPSSpectralExtraction.lam (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e,OpenBoundaryMPSSpectralExtraction.mu (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e,
        (OpenBoundaryMPSSpectralExtraction.sector (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e).a,
        OpenBoundaryMPSSpectralExtraction.nativeLeft (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e 0,OpenBoundaryMPSSpectralExtraction.nativeLeft (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e 1,
        OpenBoundaryMPSSpectralExtraction.nativeRight (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e N ![1,OpenBoundaryMPSQ2PolynomialFiber.eta x] 0,
        OpenBoundaryMPSSpectralExtraction.nativeRight (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e N ![1,OpenBoundaryMPSQ2PolynomialFiber.eta x] 1,
        OpenBoundaryMPSSpectralExtraction.z (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e] i) := by
  let a := point x e
  let cc := OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x
  have hc2 : cc 2 ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hc.2).1).1).1
  have htwo : 2 * cc 2 ≠ 0 := mul_ne_zero (by norm_num) hc2
  have hcP (p : CP) := Frac.of_rep a p
  have hc' (i : Fin 5) : Frac.Rep a (Frac.ofPoly (c i)) (cc i) := by
    simpa [a,cc,eval_c] using hcP (c i)
  have hl : Frac.Rep a lam (OpenBoundaryMPSSpectralExtraction.lam cc e) := by
    apply Frac.div_rep _ _ htwo
    · simpa [a,OpenBoundaryMPSSpectralExtraction.lam,OpenBoundaryMPSSpectralExtraction.h,eval_c,eval_root] using hcP (c 4-c 1+root)
    · simpa [a,eval_c] using hcP (2*c 2)
  have hm : Frac.Rep a mu (OpenBoundaryMPSSpectralExtraction.mu cc e) := by
    apply Frac.div_rep _ _ htwo
    · simpa [a,OpenBoundaryMPSSpectralExtraction.mu,OpenBoundaryMPSSpectralExtraction.h,eval_c,eval_root] using hcP (c 4-c 1-root)
    · simpa [a,eval_c] using hcP (2*c 2)
  have hA : MRep a core0 (OpenBoundaryMPSSpectralExtraction.A cc 0) := by
    intro i j
    have hh := hcP (!![c 1,c 2;1-c 0*c 1,-c 0*c 2] i j)
    fin_cases i <;> fin_cases j <;>
      simpa [core0,OpenBoundaryMPSSpectralExtraction.A,
        OpenBoundaryMPSTwoSiteMinimality.core,a,cc,eval_c] using hh
  have hT : MRep a frame (OpenBoundaryMPSSpectralExtraction.T cc e) := by
    apply mmul_rep hA
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using hcP 1
    · simpa using hcP 1
    · exact hl
    · exact hm
  have hs := OpenBoundaryMPSSpectralExtraction.spectral_frame hc
  have he : e ≠ 0 := by
    intro he
    have hd : OpenBoundaryMPSSpectralExtraction.D cc ≠ 0 :=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hc.2).1).1).2
    exact hd (by simpa [he] using hc.1.symm)
  have hTi := minv_rep hT (by rw [hs.1]; exact he)
  have hK : MRep a conjugated (OpenBoundaryMPSSpectralExtraction.K cc e) := by
    have hh := mmul_rep hTi (mmul_rep hA hT)
    simpa only [conjugated,OpenBoundaryMPSSpectralExtraction.K,Matrix.mul_assoc] using hh
  have hu : OpenBoundaryMPSSpectralExtraction.u cc e ≠ 0 := hs.2.2.2.2.2.2.1
  have hv : OpenBoundaryMPSSpectralExtraction.v cc e ≠ 0 := hs.2.2.2.2.2.2.2.1
  have hg : OpenBoundaryMPSSpectralExtraction.gap cc e ≠ 0 := hs.2.2.2.2.2.2.2.2.2.2
  have hgap : Frac.Rep a gap (OpenBoundaryMPSSpectralExtraction.gap cc e) := by
    apply Frac.div_rep _ (hc' 2) hc2
    simpa [a,OpenBoundaryMPSSpectralExtraction.gap,eval_root] using hcP (-root)
  have hneg : Frac.Rep a (Frac.ofPoly (-c 2)) (-cc 2) := by
    simpa [a,eval_c] using hcP (-c 2)
  have hrho : Frac.Rep a rho (OpenBoundaryMPSSpectralExtraction.rho cc e) :=
    Frac.div_rep hneg (Frac.mul_rep (Frac.mul_rep hgap (hK 0 0)) (hK 0 1))
      (mul_ne_zero (mul_ne_zero hg hu) hv)
  have hS : MRep a gauge (OpenBoundaryMPSSpectralExtraction.S cc e) := by
    intro i j
    fin_cases j
    · simpa [gauge,OpenBoundaryMPSSpectralExtraction.S,Matrix.mul_apply,Fin.sum_univ_two] using hT i 0
    · simpa [gauge,OpenBoundaryMPSSpectralExtraction.S,Matrix.mul_apply,Fin.sum_univ_two] using
        Frac.mul_rep (hT i 1) hrho
  have hex := OpenBoundaryMPSSpectralExtraction.native_extraction hc
  have hSi := minv_rep hS hex.1
  have hz : Frac.Rep a nativeZ (OpenBoundaryMPSSpectralExtraction.z cc e) :=
    Frac.div_rep hneg (Frac.mul_rep hgap (Frac.pow_rep (hK 0 0) 2))
      (mul_ne_zero hg (pow_ne_zero 2 hu))
  have hoff : Frac.Rep a offset (OpenBoundaryMPSSpectralExtraction.offset cc e) :=
    Frac.div_rep (Frac.mul_rep (Frac.mul_rep hgap (hK 0 1)) (hK 1 0)) hneg
      (neg_ne_zero.mpr hc2)
  have hright (i : Fin 2) : Frac.Rep a (right N i)
      (OpenBoundaryMPSSpectralExtraction.nativeRight cc e N ![1,OpenBoundaryMPSQ2PolynomialFiber.eta x] i) := by
    have hh := Frac.mul_rep (Frac.pow_rep (hK 0 0) N)
      (Frac.add_rep (hSi i 0) (Frac.mul_rep (hSi i 1) (by
        simpa [a,eval_eta] using hcP eta)))
    fin_cases i <;>
      simpa [right,OpenBoundaryMPSSpectralExtraction.nativeRight,OpenBoundaryMPSSpectralExtraction.u,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
        smul_eq_mul] using hh
  have hleft := hex.2.2.2.2.2.2.1
  intro i
  fin_cases i
  · exact hl
  · exact hm
  · exact Frac.sub_rep hl hoff
  · change Frac.Rep a (Frac.ofPoly 1)
      (OpenBoundaryMPSSpectralExtraction.nativeLeft cc e 0)
    rw [hleft]
    simpa using hcP 1
  · change Frac.Rep a rho (OpenBoundaryMPSSpectralExtraction.nativeLeft cc e 1)
    rw [hleft]
    exact hrho
  · exact hright 0
  · exact hright 1
  · exact hz

/-- Literal REAL15 numerator and denominator families; no polynomial division is used. -/
def numerator (N : ℕ) (i : Fin 16) : RP :=
  if i.val % 2 = 0 then (nativeTerms N ⟨i.val/2,by omega⟩).realNum
  else (nativeTerms N ⟨i.val/2,by omega⟩).imagNum

def denominator (N : ℕ) (i : Fin 16) : RP :=
  (nativeTerms N ⟨i.val/2,by omega⟩).realDen

/-- Both physical branches use the same literal families and retain u^N, even at N=0. -/
theorem native_coordinates (x : Fin 13 → ℝ) (e : ℂ)
    (hc : OpenBoundaryMPSSpectralExtraction.Admissible (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e) (N : ℕ) :
    (∀ i, eval (point x e) (denominator N i) ≠ 0) ∧
    (fun i => eval (point x e) (numerator N i) / eval (point x e) (denominator N i)) =
      OpenBoundaryMPSInteriorPolynomial.coordinates (OpenBoundaryMPSSpectralExtraction.sector (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e) (OpenBoundaryMPSSpectralExtraction.nativeLeft (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e)
        (OpenBoundaryMPSSpectralExtraction.nativeRight (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e N ![1,OpenBoundaryMPSQ2PolynomialFiber.eta x]) (OpenBoundaryMPSSpectralExtraction.z (OpenBoundaryMPSQ2PolynomialFiber.coreCoordinates x) e) := by
  have hh (i : Fin 8) := Frac.real_rep (nativeTerms_rep x e hc N i)
  constructor
  · intro i
    exact (hh ⟨i.val/2,by omega⟩).1
  · funext i
    fin_cases i
    · simpa only [numerator,denominator,OpenBoundaryMPSInteriorPolynomial.coordinates,
        OpenBoundaryMPSSpectralExtraction.sector,Fin.reduceFinMk,Nat.reduceMod,Nat.reduceDiv,
        Nat.reduceEqDiff,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Matrix.cons_val] using (hh 0).2.1
    · simpa only [numerator,denominator,OpenBoundaryMPSInteriorPolynomial.coordinates,
        OpenBoundaryMPSSpectralExtraction.sector,Fin.reduceFinMk,Nat.reduceMod,Nat.reduceDiv,
        Nat.reduceEqDiff,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Matrix.cons_val] using (hh 0).2.2
    · simpa only [numerator,denominator,OpenBoundaryMPSInteriorPolynomial.coordinates,
        OpenBoundaryMPSSpectralExtraction.sector,Fin.reduceFinMk,Nat.reduceMod,Nat.reduceDiv,
        Nat.reduceEqDiff,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Matrix.cons_val] using (hh 1).2.1
    · simpa only [numerator,denominator,OpenBoundaryMPSInteriorPolynomial.coordinates,
        OpenBoundaryMPSSpectralExtraction.sector,Fin.reduceFinMk,Nat.reduceMod,Nat.reduceDiv,
        Nat.reduceEqDiff,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Matrix.cons_val] using (hh 1).2.2
    · simpa only [numerator,denominator,OpenBoundaryMPSInteriorPolynomial.coordinates,
        OpenBoundaryMPSSpectralExtraction.sector,Fin.reduceFinMk,Nat.reduceMod,Nat.reduceDiv,
        Nat.reduceEqDiff,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Matrix.cons_val] using (hh 2).2.1
    · simpa only [numerator,denominator,OpenBoundaryMPSInteriorPolynomial.coordinates,
        OpenBoundaryMPSSpectralExtraction.sector,Fin.reduceFinMk,Nat.reduceMod,Nat.reduceDiv,
        Nat.reduceEqDiff,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Matrix.cons_val] using (hh 2).2.2
    · simpa only [numerator,denominator,OpenBoundaryMPSInteriorPolynomial.coordinates,
        OpenBoundaryMPSSpectralExtraction.sector,Fin.reduceFinMk,Nat.reduceMod,Nat.reduceDiv,
        Nat.reduceEqDiff,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Matrix.cons_val] using (hh 3).2.1
    · simpa only [numerator,denominator,OpenBoundaryMPSInteriorPolynomial.coordinates,
        OpenBoundaryMPSSpectralExtraction.sector,Fin.reduceFinMk,Nat.reduceMod,Nat.reduceDiv,
        Nat.reduceEqDiff,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Matrix.cons_val] using (hh 3).2.2
    · simpa only [numerator,denominator,OpenBoundaryMPSInteriorPolynomial.coordinates,
        OpenBoundaryMPSSpectralExtraction.sector,Fin.reduceFinMk,Nat.reduceMod,Nat.reduceDiv,
        Nat.reduceEqDiff,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Matrix.cons_val] using (hh 4).2.1
    · simpa only [numerator,denominator,OpenBoundaryMPSInteriorPolynomial.coordinates,
        OpenBoundaryMPSSpectralExtraction.sector,Fin.reduceFinMk,Nat.reduceMod,Nat.reduceDiv,
        Nat.reduceEqDiff,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Matrix.cons_val] using (hh 4).2.2
    · simpa only [numerator,denominator,OpenBoundaryMPSInteriorPolynomial.coordinates,
        OpenBoundaryMPSSpectralExtraction.sector,Fin.reduceFinMk,Nat.reduceMod,Nat.reduceDiv,
        Nat.reduceEqDiff,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Matrix.cons_val] using (hh 5).2.1
    · simpa only [numerator,denominator,OpenBoundaryMPSInteriorPolynomial.coordinates,
        OpenBoundaryMPSSpectralExtraction.sector,Fin.reduceFinMk,Nat.reduceMod,Nat.reduceDiv,
        Nat.reduceEqDiff,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Matrix.cons_val] using (hh 5).2.2
    · simpa only [numerator,denominator,OpenBoundaryMPSInteriorPolynomial.coordinates,
        OpenBoundaryMPSSpectralExtraction.sector,Fin.reduceFinMk,Nat.reduceMod,Nat.reduceDiv,
        Nat.reduceEqDiff,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Matrix.cons_val] using (hh 6).2.1
    · simpa only [numerator,denominator,OpenBoundaryMPSInteriorPolynomial.coordinates,
        OpenBoundaryMPSSpectralExtraction.sector,Fin.reduceFinMk,Nat.reduceMod,Nat.reduceDiv,
        Nat.reduceEqDiff,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Matrix.cons_val] using (hh 6).2.2
    · simpa only [numerator,denominator,OpenBoundaryMPSInteriorPolynomial.coordinates,
        OpenBoundaryMPSSpectralExtraction.sector,Fin.reduceFinMk,Nat.reduceMod,Nat.reduceDiv,
        Nat.reduceEqDiff,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Matrix.cons_val] using (hh 7).2.1
    · simpa only [numerator,denominator,OpenBoundaryMPSInteriorPolynomial.coordinates,
        OpenBoundaryMPSSpectralExtraction.sector,Fin.reduceFinMk,Nat.reduceMod,Nat.reduceDiv,
        Nat.reduceEqDiff,ite_true,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Matrix.cons_val] using (hh 7).2.2

end D5.S3.Quantum.TensorNetworks.InteriorSpectralCoordinates
