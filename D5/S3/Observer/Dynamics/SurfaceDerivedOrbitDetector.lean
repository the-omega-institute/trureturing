/- GID: D5/S3/Observer/Dynamics/SurfaceDerivedOrbitDetector
   generality: G
   mirror-B: D5/B/S3/Observer/Dynamics/SurfaceDerivedOrbitDetector
   mirror-E: none(waiver:unbounded-marked-orbit-construction)
   anchors: []
   utility: none
   digest: A finite fully invariant matrix quotient separates a second-derived surface-word orbit throughout every prescribed finite time window. -/

import D5.S3.Observer.Dynamics.SurfaceTwistCongruence
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
The surface presentation and the actual twist are reused unchanged. Genus is
extra+3. The chosen word is [[a1,a2],[b1,b3]], with a genuine third handle.
A shifted family of relator-compatible seven-dimensional representations
reads its nth image as I-(t+n)E_{1,7} (one-based indices). Finite simultaneous evaluation gives a
fully invariant kernel. The one-sided modular condition on this full matrix
quotient is intentional: no exact period m is claimed for ALL GL7-valued
representations. Exact period on the unitriangular subfamily and the sharp
class-six lower-central threshold are ordinary theory results, not conclusions
of this file.

No Lean/lake execution, kernel certificate, independent admission review or
first-discovery claim is attached to this source-reviewed candidate. The
matrix identities are checked over arbitrary commutative rings; finite
experiments are diagnostics only. Prior context: Klukowski 2411.06867v2 and
Church--Pixton 0804.3633v2. This does not settle the curve-orbit CSP conjecture.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Matrix BigOperators

namespace D5.S3.Observer.Dynamics.SurfaceDerivedOrbitDetector
open D5.S3.Observer.Dynamics.SurfaceTwistCongruence

/-- Same surface carrier as before, now with at least three handles. -/
abbrev G (extra : ℕ) := Surface (extra + 1)
abbrev Mat (R : Type) := Matrix (Fin 7) (Fin 7) R

/-- A fixed second-derived word; the third-handle generator is essential. -/
def derivedWord (extra : ℕ) : G extra :=
  bracket
    (bracket (generator (extra + 1) (Sum.inl 0))
      (generator (extra + 1) (Sum.inl 2)))
    (bracket (generator (extra + 1) (Sum.inl 1))
      (generator (extra + 1) (Sum.inr (0, 1))))

private def aMat (R : Type) [CommRing R] : Mat R :=
  !![1,1,0,0,0,0,0; 0,1,1,0,0,0,0; 0,0,1,1,0,0,0;
     0,0,0,1,0,0,0; 0,0,0,0,1,1,0; 0,0,0,0,0,1,0; 0,0,0,0,0,0,1]
private def aiMat (R : Type) [CommRing R] : Mat R :=
  !![1,-1,1,-1,0,0,0; 0,1,-1,1,0,0,0; 0,0,1,-1,0,0,0;
     0,0,0,1,0,0,0; 0,0,0,0,1,-1,0; 0,0,0,0,0,1,0; 0,0,0,0,0,0,1]
private def bMat (R : Type) [CommRing R] : Mat R :=
  !![1,0,0,0,0,0,0; 0,1,0,0,0,0,0; 0,0,1,0,0,0,0;
     0,0,0,1,1,0,0; 0,0,0,0,1,0,0; 0,0,0,0,0,1,1; 0,0,0,0,0,0,1]
private def biMat (R : Type) [CommRing R] : Mat R :=
  !![1,0,0,0,0,0,0; 0,1,0,0,0,0,0; 0,0,1,0,0,0,0;
     0,0,0,1,-1,0,0; 0,0,0,0,1,0,0; 0,0,0,0,0,1,-1; 0,0,0,0,0,0,1]
private def pMat {R : Type} [CommRing R] (t s : R) : Mat R :=
  !![1,0,0,0,0,0,0; 0,1,0,0,0,0,0; 0,0,1,0,t,-t,t+s;
     0,0,0,1,0,-t,t; 0,0,0,0,1,0,t; 0,0,0,0,0,1,0; 0,0,0,0,0,0,1]
private def zMat {R : Type} [CommRing R] (t : R) : Mat R :=
  !![1,0,0,0,0,0,t; 0,1,0,0,0,0,0; 0,0,1,0,0,0,0;
     0,0,0,1,0,0,0; 0,0,0,0,1,0,0; 0,0,0,0,0,1,0; 0,0,0,0,0,0,1]

private def aUnit (R : Type) [CommRing R] : (Mat R)ˣ where
  val := aMat R
  inv := aiMat R
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [aMat, aiMat, Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [aMat, aiMat, Matrix.mul_apply, Fin.sum_univ_succ]
private def bUnit (R : Type) [CommRing R] : (Mat R)ˣ where
  val := bMat R
  inv := biMat R
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [bMat, biMat, Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [bMat, biMat, Matrix.mul_apply, Fin.sum_univ_succ]
private def pUnit {R : Type} [CommRing R] (t s : R) : (Mat R)ˣ where
  val := pMat t s
  inv := pMat (-t) (t*t-s)
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [pMat, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [pMat, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
private def zUnit {R : Type} [CommRing R] (t : R) : (Mat R)ˣ where
  val := zMat t
  inv := zMat (-t)
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [zMat, Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [zMat, Matrix.mul_apply, Fin.sum_univ_succ]

abbrev MatrixTarget (m : ℕ) := (Mat (ZMod m))ˣ
abbrev MatrixRep (extra m : ℕ) := G extra →* MatrixTarget m

def matrixEvaluation (extra m : ℕ) : G extra →* (MatrixRep extra m → MatrixTarget m) where
  toFun x ρ := ρ x
  map_one' := by funext ρ; exact map_one ρ
  map_mul' x y := by funext ρ; exact map_mul ρ x y

abbrev MatrixDetector (extra m : ℕ) := (matrixEvaluation extra m).range

def matrixProjection (extra m : ℕ) : G extra →* MatrixDetector extra m :=
  (matrixEvaluation extra m).rangeRestrict

set_option maxHeartbeats 4000000 in
-- The symbolic seven-dimensional commutator expansion needs a larger elaboration budget.
/-- The actual finite quotient separates every pair of orbit times below m.
The all-time conclusion is necessary modular equality, not a converse. The
last clause states complete blindness under the explicit metabelian law. -/
theorem finite_second_derived_orbit_detector (extra m : ℕ) (hm : 0 < m) :
    Finite (MatrixDetector extra m) ∧
    Function.Surjective (matrixProjection extra m) ∧
    (∀ f : G extra →* G extra, ∀ x,
      matrixProjection extra m x = 1 → matrixProjection extra m (f x) = 1) ∧
    (∀ p n : ℕ,
      (∃ z : MatrixDetector extra m,
        matrixProjection extra m (twistPower (extra+1) n (derivedWord extra)) =
          z * matrixProjection extra m (twistPower (extra+1) p (derivedWord extra)) * z⁻¹) →
      (n : ZMod m) = (p : ZMod m)) ∧
    (∀ p n : ℕ, p < m → n < m →
      ((∃ z : MatrixDetector extra m,
        matrixProjection extra m (twistPower (extra+1) n (derivedWord extra)) =
          z * matrixProjection extra m (twistPower (extra+1) p (derivedWord extra)) * z⁻¹) ↔ n = p)) ∧
    (∀ (F : Type) [Group F],
      (∀ a b c d : F, bracket (bracket a b) (bracket c d) = 1) →
      ∀ f : G extra →* F, ∀ n : ℕ, f (twistPower (extra+1) n (derivedWord extra)) = 1) := by
  classical
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let R := ZMod m
  let A := aUnit R
  let B := bUnit R
  let P : R → R → MatrixTarget m := pUnit
  let H : MatrixTarget m := bracket A B
  have hpMul : ∀ t s v w : R, P t s * P v w = P (t+v) (s+w+t*v) := by
    intro t s v w
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, pUnit, pMat, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
  have hpZero : P 0 0 = 1 := by
    apply Units.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp [P, pUnit, pMat]
  have hH : H = P 1 0 := by
    apply Units.ext
    norm_num [H, A, B, bracket, aUnit, bUnit, aMat, aiMat, bMat, biMat,
      P, pUnit, pMat]
  have hpComm : ∀ t s : R, P t s * H = H * P t s := by
    intro t s
    rw [hH, hpMul, hpMul]
    congr 1 <;> ring
  have hpPow : ∀ n : ℕ, H^n = P (n : R) (∑ i ∈ Finset.range n, (i : R)) := by
    intro n
    induction n with
    | zero => simpa using hpZero.symm
    | succ n ih =>
        rw [pow_succ, ih, hH, hpMul]
        simp [Finset.sum_range_succ]
  have hEcho : ∀ t s : R,
      bracket (bracket (P t s * A * (P t s)⁻¹) A)
        (bracket (P t s * B * (P t s)⁻¹) A) = zUnit (-t) := by
    intro t s
    apply Units.ext
    simp [bracket, A, B, P, aUnit, bUnit, pUnit, zUnit,
      aMat, aiMat, bMat, biMat, pMat, zMat]
    repeat' apply And.intro
    all_goals ring
  let images (t : R) : Generator (extra+1) → MatrixTarget m := fun i =>
    match i with
    | Sum.inl j => ![P t 0 * A * (P t 0)⁻¹, P t 0 * B * (P t 0)⁻¹, A, 1] j
    | Sum.inr (j,k) => if j = 0 then ![B,A] k else 1
  have hrel : ∀ t : R, ∀ w ∈ ({surfaceRelator (extra+1)} : Set (FreeGroup (Generator (extra+1)))),
      FreeGroup.lift (images t) w = 1 := by
    intro t w hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    have htail : FreeGroup.lift (images t) (extraWord (extra+1)) = bracket B A := by
      unfold extraWord
      rw [List.finRange_succ, List.map_cons, List.prod_cons, map_mul]
      have hrest : FreeGroup.lift (images t)
          (((List.finRange extra).map Fin.succ).map fun i =>
            bracket (FreeGroup.of (Sum.inr (i,0))) (FreeGroup.of (Sum.inr (i,1)))).prod = 1 := by
        rw [List.map_map]
        generalize List.finRange extra = xs
        induction xs with
        | nil => simp
        | cons i xs ih =>
            simp only [List.map_cons, List.prod_cons, map_mul, ih]
            simp [bracket, images]
      rw [hrest]
      simp [images, bracket]
    have hfirst : bracket (P t 0 * A * (P t 0)⁻¹)
        (P t 0 * B * (P t 0)⁻¹) = H := by
      calc
        _ = P t 0 * H * (P t 0)⁻¹ := by dsimp [H, bracket]; group
        _ = H := by rw [hpComm]; group
    change FreeGroup.lift (images t) (surfaceRelator (extra+1)) = 1
    simp only [surfaceRelator, map_mul, htail]
    simp only [bracket, map_mul, map_inv, FreeGroup.lift_apply_of]
    change bracket (P t 0 * A * (P t 0)⁻¹) (P t 0 * B * (P t 0)⁻¹) *
      bracket A 1 * bracket B A = 1
    rw [hfirst]
    dsimp [H, bracket]
    group
  let ρ (t : R) : MatrixRep extra m := PresentedGroup.toGroup (hrel t)
  have hρGen : ∀ t i, ρ t (generator (extra+1) i) = images t i := by
    intro t i
    exact PresentedGroup.toGroup.of _
  have hρBoundary : ∀ t, ρ t (boundary (extra+1)) = H := by
    intro t
    simp only [boundary, bracket, map_mul, map_inv, hρGen]
    change bracket (P t 0 * A * (P t 0)⁻¹) (P t 0 * B * (P t 0)⁻¹) = H
    calc
      _ = P t 0 * H * (P t 0)⁻¹ := by dsimp [H, bracket]; group
      _ = H := by rw [hpComm]; group
  have hgen : ∀ i, twistHom (extra+1) 1 (generator (extra+1) i) = twistImages (extra+1) 1 i := by
    intro i
    simp only [twistHom, generator, PresentedGroup.toGroup.of]
  have hτBoundary : twistHom (extra+1) 1 (boundary (extra+1)) = boundary (extra+1) := by
    simp only [boundary, bracket, map_mul, map_inv, hgen]
    change bracket
      (boundary (extra+1) * generator (extra+1) (Sum.inl 0) * (boundary (extra+1))⁻¹)
      (boundary (extra+1) * generator (extra+1) (Sum.inl 1) * (boundary (extra+1))⁻¹) = _
    dsimp [boundary, bracket]
    group
  have hpower : ∀ n : ℕ, ∀ i : Generator (extra+1),
      twistPower (extra+1) n (generator (extra+1) i) =
        match i with
        | Sum.inl j => if j.val < 2 then
            boundary (extra+1)^n * generator (extra+1) i * (boundary (extra+1)^n)⁻¹
          else generator (extra+1) i
        | Sum.inr _ => generator (extra+1) i := by
    intro n
    induction n with
    | zero => intro i; cases i <;> simp [twistPower]
    | succ n ih =>
        intro i
        change twistHom (extra+1) 1 (twistPower (extra+1) n (generator (extra+1) i)) = _
        rw [ih]
        rcases i with i | i
        · fin_cases i <;>
            simp [map_mul, map_inv, map_pow, hτBoundary, hgen, twistImages, pow_succ] <;> group
        · simp [hgen, twistImages]
  have heval : ∀ t : R, ∀ n : ℕ,
      ρ t (twistPower (extra+1) n (derivedWord extra)) = zUnit (-((n : R)+t)) := by
    intro t n
    have hA : H^n * (P t 0 * A * (P t 0)⁻¹) * (H^n)⁻¹ =
        P ((n : R)+t) ((∑ i ∈ Finset.range n, (i : R))+(n:R)*t) * A *
          (P ((n : R)+t) ((∑ i ∈ Finset.range n, (i : R))+(n:R)*t))⁻¹ := by
      calc
        _ = (H^n * P t 0) * A * (H^n * P t 0)⁻¹ := by group
        _ = _ := by simp only [hpPow, hpMul, add_zero]
    have hB : H^n * (P t 0 * B * (P t 0)⁻¹) * (H^n)⁻¹ =
        P ((n : R)+t) ((∑ i ∈ Finset.range n, (i : R))+(n:R)*t) * B *
          (P ((n : R)+t) ((∑ i ∈ Finset.range n, (i : R))+(n:R)*t))⁻¹ := by
      calc
        _ = (H^n * P t 0) * B * (H^n * P t 0)⁻¹ := by group
        _ = _ := by simp only [hpPow, hpMul, add_zero]
    have hmap : ∀ x y : G extra,
        ρ t (twistPower (extra+1) n (bracket x y)) =
          bracket (ρ t (twistPower (extra+1) n x)) (ρ t (twistPower (extra+1) n y)) := by
      intro x y
      simp only [bracket, map_mul, map_inv]
    have hEvalGen : ∀ i : Generator (extra+1),
        ρ t (twistPower (extra+1) n (generator (extra+1) i)) =
          match i with
          | Sum.inl j => if j.val < 2 then H^n * images t i * (H^n)⁻¹ else images t i
          | Sum.inr _ => images t i := by
      intro i
      rw [hpower]
      rcases i with i | i
      · by_cases hi : i.val < 2
        · simp only [hi, if_true, map_mul, map_inv, map_pow, hρBoundary, hρGen]
        · simp only [hi, if_false, hρGen]
      · exact hρGen t _
    simp only [derivedWord, hmap, hEvalGen]
    change bracket
      (bracket (H^n * (P t 0 * A * (P t 0)⁻¹) * (H^n)⁻¹) A)
      (bracket (H^n * (P t 0 * B * (P t 0)⁻¹) * (H^n)⁻¹) A) = _
    rw [hA, hB]
    exact hEcho _ _
  have hfRep : Finite (MatrixRep extra m) :=
    Finite.of_injective
      (fun f : MatrixRep extra m => fun i : Generator (extra+1) => f (generator (extra+1) i))
      (by intro f g h; apply PresentedGroup.ext; intro i; exact congrFun h i)
  letI := hfRep
  have hfinite : Finite (MatrixDetector extra m) := inferInstance
  have hsurj : Function.Surjective (matrixProjection extra m) := by
    rintro ⟨y,hy⟩
    obtain ⟨x,rfl⟩ := hy
    exact ⟨x,rfl⟩
  have hinv : ∀ f : G extra →* G extra, ∀ x,
      matrixProjection extra m x = 1 → matrixProjection extra m (f x) = 1 := by
    intro f x hx
    apply Subtype.ext
    funext σ
    exact congrArg (fun z : MatrixDetector extra m => z.1 (σ.comp f)) hx
  have hsep : ∀ p n : ℕ,
      (∃ z : MatrixDetector extra m,
        matrixProjection extra m (twistPower (extra+1) n (derivedWord extra)) =
          z * matrixProjection extra m (twistPower (extra+1) p (derivedWord extra)) * z⁻¹) →
      (n : ZMod m) = (p : ZMod m) := by
    intro p n h
    rcases h with ⟨z,hz⟩
    have hσ := congrArg (fun v : MatrixDetector extra m => v.1 (ρ (-(p:R)))) hz
    change ρ (-(p:R)) (twistPower (extra+1) n (derivedWord extra)) =
      z.1 (ρ (-(p:R))) * ρ (-(p:R)) (twistPower (extra+1) p (derivedWord extra)) *
        (z.1 (ρ (-(p:R))))⁻¹ at hσ
    rw [heval, heval] at hσ
    have hz0 : zUnit (0:R) = 1 := by
      apply Units.ext
      ext i j; fin_cases i <;> fin_cases j <;> simp [zUnit,zMat]
    simp only [add_neg_cancel, neg_zero, hz0, mul_one, mul_inv_cancel] at hσ
    have hc := congrArg (fun U : MatrixTarget m => (U : Mat R) 0 6) hσ
    have he : -((n:R)-(p:R)) = 0 := by simpa [zUnit,zMat,sub_eq_add_neg] using hc
    exact sub_eq_zero.mp (neg_eq_zero.mp he)
  have hwindow : ∀ p n : ℕ, p < m → n < m →
      ((∃ z : MatrixDetector extra m,
        matrixProjection extra m (twistPower (extra+1) n (derivedWord extra)) =
          z * matrixProjection extra m (twistPower (extra+1) p (derivedWord extra)) * z⁻¹) ↔ n=p) := by
    intro p n hp hn
    constructor
    · intro h
      have hh := (ZMod.natCast_eq_natCast_iff' n p m).mp (hsep p n h)
      simpa [Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt hp] using hh
    · rintro rfl
      exact ⟨1,by simp⟩
  have hblind : ∀ (F : Type) [Group F],
      (∀ a b c d : F, bracket (bracket a b) (bracket c d) = 1) →
      ∀ f : G extra →* F, ∀ n : ℕ, f (twistPower (extra+1) n (derivedWord extra)) = 1 := by
    intro F _ hF f n
    simpa only [derivedWord,bracket,map_mul,map_inv] using
      hF (f (twistPower (extra+1) n (generator (extra+1) (Sum.inl 0))))
        (f (twistPower (extra+1) n (generator (extra+1) (Sum.inl 2))))
        (f (twistPower (extra+1) n (generator (extra+1) (Sum.inl 1))))
        (f (twistPower (extra+1) n (generator (extra+1) (Sum.inr (0,1)))))
  exact ⟨hfinite,hsurj,hinv,hsep,hwindow,hblind⟩

#print axioms finite_second_derived_orbit_detector
end D5.S3.Observer.Dynamics.SurfaceDerivedOrbitDetector
