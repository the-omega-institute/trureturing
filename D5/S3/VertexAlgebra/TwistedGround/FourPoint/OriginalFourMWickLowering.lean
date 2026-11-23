/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMWickLowering
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMWickLowering
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Same-puncture Wick contraction and surviving creators in the lowering flow. -/

import D5.S3.VertexAlgebra.TwistedGround.AffineWickConvolution
import D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentWickPolynomial
import Mathlib.Algebra.MvPolynomial.Funext

/-! At one puncture, regroup the finite lowering word by the endpoints
of its contracted pairs. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMWickLowering

open LatticeGeneratingFieldLocality LatticeHalfFock
open HalfFock.OriginalHalfCurrentWickPolynomial (creator pair word word_coeff)
open HalfFock.OriginalHalfCurrentTransport (lowering_normal_order_word)
open AffineOccurrenceWick (wick)
open AffineWickConvolution (partitions wick_add_covariance)

private theorem pair_symm (D : LatticeData) (hu : IsUnit D.G.det) (a b : Index D) :
    pair D a b = pair D b a := by
  have he : word D [a, b] = word D [b, a] := by
    ext k
    rw [← word_coeff, ← word_coeff, ← lowering_normal_order_word D hu,
      ← lowering_normal_order_word D hu]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [mul_comm (MvPolynomial.X a) (MvPolynomial.X b)]
  have hword (x y : Index D) :
      word D [x, y] = creator D x * creator D y + pair D x y := by
    simp [word]
  rw [hword, hword, mul_comm (creator D b) (creator D a)] at he
  exact add_left_cancel he

/-- The scalar weight of two corrected oscillators at one puncture. -/
def pairWeight (D : LatticeData) (θ : ℂ) (a b : Index D) : ℂ :=
  MvPolynomial.constantCoeff ((pair D a b).eval (MvPolynomial.C θ))

private theorem eval_pair (D : LatticeData) (θ : ℂ) (a b : Index D) :
    (pair D a b).eval (MvPolynomial.C θ) = MvPolynomial.C (pairWeight D θ a b) := by
  simp only [pairWeight, pair, Polynomial.eval_monomial, ← map_pow, ← map_mul,
    MvPolynomial.constantCoeff_C]

private theorem wick_zero_covariance {X : Type*} (μ : X → ℂ) (l : List X) :
    wick 0 μ l = (l.map μ).prod := by
  induction l with
  | nil => simp [wick]
  | cons a l ih =>
    simp only [wick, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, ih,
      List.map_cons, List.prod_cons]

private theorem eval_word_as_wick {X : Type*} (D : LatticeData) (θ : ℂ)
    (v : Index D → ℂ) (mode : X → Index D) (l : List X) :
    MvPolynomial.eval v ((word D (l.map mode)).eval (MvPolynomial.C θ)) =
      wick (Matrix.of fun i j => pairWeight D θ (mode i) (mode j))
        (fun i => MvPolynomial.eval v ((creator D (mode i)).eval (MvPolynomial.C θ))) l := by
  let E : Polynomial (Oscillator D) →+* ℂ :=
    (MvPolynomial.eval v).comp (Polynomial.evalRingHom (MvPolynomial.C θ))
  change E (word D (l.map mode)) = _
  induction l using WellFounded.induction (measure List.length).wf with
  | h l ih =>
    cases l with
    | nil => simp [word, wick]
    | cons a l =>
      simp only [List.map_cons, word, wick, map_add, map_mul, map_sum, Matrix.of_apply]
      have hE (x y : Index D) : E (pair D x y) = pairWeight D θ x y := by
        change MvPolynomial.eval v ((pair D x y).eval (MvPolynomial.C θ)) = _
        rw [eval_pair, MvPolynomial.eval_C]
      rw [ih l (Nat.lt_succ_self _)]
      change _ + _ = _ + _
      congr 1
      have hlen : (l.map mode).length = l.length := by simp
      apply Finset.sum_equiv (finCongr hlen)
      · simp
      · intro j _
        let k := (finCongr hlen) j
        change E (pair D (mode a) ((l.map mode).get j)) *
            E (word D ((l.map mode).eraseIdx j)) =
          pairWeight D θ (mode a) (mode (l.get k)) *
            wick _ _ (l.eraseIdx k)
        have he : ((l.map mode).get j) = mode (l.get k) := by
          simp [List.get_eq_getElem, k]
        rw [he, hE, List.eraseIdx_map]
        exact congrArg (fun z => pairWeight D θ (mode a) (mode (l.get k)) * z)
          (ih (l.eraseIdx k) (Nat.lt_succ_of_le (List.length_eraseIdx_le ..)))

/-- The evaluated lowering word at one puncture is the sum over its
correction endpoint sets. The complement contributes the product of the
surviving creators, with repeated modes kept at each occurrence. -/
theorem eval_word_partition {X : Type*} [Finite X] (D : LatticeData) (hu : IsUnit D.G.det)
    (θ : ℂ) (mode : X → Index D) (l : List X) :
    (word D (l.map mode)).eval (MvPolynomial.C θ) =
      ((partitions l).map fun p =>
        MvPolynomial.C (wick (Matrix.of fun i j => pairWeight D θ (mode i) (mode j)) 0 p.1) *
          (p.2.map fun a => (creator D (mode a)).eval (MvPolynomial.C θ)).prod).sum := by
  apply MvPolynomial.funext
  intro v
  rw [eval_word_as_wick D θ v mode l]
  let C : Matrix X X ℂ := Matrix.of fun i j => pairWeight D θ (mode i) (mode j)
  have hC (i j : X) : C i j = C j i := by
    change pairWeight D θ (mode i) (mode j) = pairWeight D θ (mode j) (mode i)
    simp only [pairWeight, pair_symm D hu (mode i) (mode j)]
  let μ (i : X) := MvPolynomial.eval v ((creator D (mode i)).eval (MvPolynomial.C θ))
  have h := wick_add_covariance 0 C μ (fun _ _ => rfl) hC l
  simpa only [zero_add, wick_zero_covariance, map_list_sum, List.map_map, Function.comp_def,
    map_mul, MvPolynomial.eval_C, map_list_prod, C, μ] using h

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMWickLowering
