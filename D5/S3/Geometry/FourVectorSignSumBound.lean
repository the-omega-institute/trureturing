/- GID: D5/S3/Geometry/FourVectorSignSumBound
   generality: G
   mirror-B: D5/B/S3/Geometry/FourVectorSignSumBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four vectors in real three-space satisfy the sharp sign-sum bound. -/



/-
  Private predicate definitions:
  rootEq: proof_shape: bind-only; consumer: roots_exist, roots_pair_positive, root_total_bound.
  signedSum_le_max: proof_shape: bind-only; escape_witness: none.
  maxNorm_nonneg: proof_shape: bind-only; escape_witness: none.
  four_vector_inequality: proof_shape: content; escape_witness: four_vector_inequality.
  admission_basis: escape-witness (four_vector_inequality).
  Direct frozen dependencies:
    D5/S3/Combinatorics/IsingUniquenessSets.sgn
      statement_id: sha256:1589788918111821cb994915047b9b43151423396895fcfd849105cc8fe4d481
  Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14767.
  Utility is none: the main result is a universal analytic construction or extremal
  statement; finite identities serve its proof and are not stand-alone computations.
-/

import D5.S3.Combinatorics.IsingUniquenessSets
import Mathlib.Analysis.InnerProductSpace.GramMatrix

noncomputable section
open D5.S3.Combinatorics.IsingUniquenessSets (sgn)
open scoped BigOperators

namespace D5.S3.Geometry.FourVectorSignSumBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def schurSum (a b d c : ℝ) : ℝ := c / (a + c) + c / (b + c) + c / (d + c)

private theorem root_exists (a b d : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ schurSum a b d c = 1 := by
  let t := a + b + d
  have ht : 0 < t := by dsimp [t]; positivity
  have cont : ContinuousOn (schurSum a b d) (Set.Icc 0 t) := by
    unfold schurSum
    apply ContinuousOn.add
    · apply ContinuousOn.add
      · exact continuousOn_id.div (continuousOn_const.add continuousOn_id)
          (fun x hx => ne_of_gt (by linarith [hx.1]))
      · exact continuousOn_id.div (continuousOn_const.add continuousOn_id)
          (fun x hx => ne_of_gt (by linarith [hx.1]))
    · exact continuousOn_id.div (continuousOn_const.add continuousOn_id)
          (fun x hx => ne_of_gt (by linarith [hx.1]))
  have bound : 1 ≤ schurSum a b d t := by
    have h1 : (1 / 2 : ℝ) ≤ t / (a + t) := by
      apply (le_div_iff₀ (by positivity : 0 < a + t)).2
      dsimp [t]; linarith
    have h2 : (1 / 2 : ℝ) ≤ t / (b + t) := by
      apply (le_div_iff₀ (by positivity : 0 < b + t)).2
      dsimp [t]; linarith
    have h3 : (1 / 2 : ℝ) ≤ t / (d + t) := by
      apply (le_div_iff₀ (by positivity : 0 < d + t)).2
      dsimp [t]; linarith
    unfold schurSum; linarith
  obtain ⟨c, hc, heq⟩ := intermediate_value_Icc ht.le cont (show 1 ∈ Set.Icc
      (schurSum a b d 0) (schurSum a b d t) by constructor; simp [schurSum]; exact bound)
  refine ⟨c, ?_, heq⟩
  rcases hc.1.eq_or_lt with hz | hp
  · subst c; norm_num [schurSum] at heq
  · exact hp

private theorem root_quadratic_nonneg (a b d c v w z : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hc : 0 < c)
    (heq : schurSum a b d c = 1) :
    0 ≤ a * v^2 + b * w^2 + d * z^2 - 2*c*(v*w + v*z + w*z) := by
  have hA : a+c ≠ 0 := by positivity
  have hB : b+c ≠ 0 := by positivity
  have hD : d+c ≠ 0 := by positivity
  have hid : a * v^2 + b * w^2 + d * z^2 - 2*c*(v*w + v*z + w*z) =
      c / ((a+c)*(b+c)) * ((a+c)*v - (b+c)*w)^2 +
      c / ((a+c)*(d+c)) * ((a+c)*v - (d+c)*z)^2 +
      c / ((b+c)*(d+c)) * ((b+c)*w - (d+c)*z)^2 +
      (1-schurSum a b d c) * ((a+c)*v^2 + (b+c)*w^2 + (d+c)*z^2) := by
    unfold schurSum
    field_simp
    <;> ring
  rw [hid, heq]
  simp only [sub_self, zero_mul, add_zero]
  positivity

private theorem root_determinant (a b d c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hc : 0 < c)
    (heq : schurSum a b d c = 1) :
    a*b*d = c^2*(a+b+d) + 2*c^3 := by
  have hA : a+c ≠ 0 := by positivity
  have hB : b+c ≠ 0 := by positivity
  have hD : d+c ≠ 0 := by positivity
  unfold schurSum at heq
  field_simp at heq
  nlinarith [heq]

private theorem triangle_bound (r s t c : ℝ) (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (hc : 0 < c) (heq : schurSum (r^2) (s^2) (t^2) c = 1) :
    (r+s+t)^2 ≤ (9/4:ℝ)*(r^2+s^2+t^2+2*c) := by
  have hp := root_quadratic_nonneg (r^2) (s^2) (t^2) c (1/r) (1/s) (1/t)
    (sq_pos_of_pos hr) (sq_pos_of_pos hs) (sq_pos_of_pos ht) hc heq
  have hsum : 2*c*(r+s+t) ≤ 3*(r*s*t) := by
    field_simp at hp
    have hprod : 0 < r*s*t := by positivity
    nlinarith [hp]
  have hdet := root_determinant (r^2) (s^2) (t^2) c
    (sq_pos_of_pos hr) (sq_pos_of_pos hs) (sq_pos_of_pos ht) hc heq
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 2*c*(r+s+t)) hsum
  have hcancel : c^2 * (4*(r+s+t)^2) ≤ c^2 * (9*(r^2+s^2+t^2+2*c)) := by
    nlinarith [hsq, hdet]
  have h : 4*(r+s+t)^2 ≤ 9*(r^2+s^2+t^2+2*c) :=
    (mul_le_mul_iff_right₀ (sq_pos_of_pos hc)).mp hcancel
  linarith

private theorem triangle_quad_strict (a b d e c C v w z h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (he : 0 < e) (hc : 0 < c)
    (hC : 0 ≤ C) (hCc : C < c) (heq : schurSum a b d c = 1)
    (hdiag : 0 < a*v^2+b*w^2+d*z^2+e*h^2) :
    0 < a*v^2+b*w^2+d*z^2+e*h^2 - 2*C*(v*w+v*z+w*z) := by
  have hroot := root_quadratic_nonneg a b d c v w z ha hb hd hc heq
  have hroot4 : 0 ≤ a*v^2+b*w^2+d*z^2+e*h^2 - 2*c*(v*w+v*z+w*z) := by
    nlinarith [mul_nonneg he.le (sq_nonneg h)]
  have hquot : 0 ≤ C/c := div_nonneg hC hc.le
  have hrest : 0 < 1-C/c := by apply sub_pos.mpr; exact (div_lt_one hc).mpr hCc
  have h1 := mul_nonneg hquot hroot4
  have h2 := mul_pos hrest hdiag
  have hid : C/c*(a*v^2+b*w^2+d*z^2+e*h^2 - 2*c*(v*w+v*z+w*z)) +
      (1-C/c)*(a*v^2+b*w^2+d*z^2+e*h^2) =
      a*v^2+b*w^2+d*z^2+e*h^2 - 2*C*(v*w+v*z+w*z) := by
    field_simp; ring
  linarith

private def plus (k : Fin 4) : Fin 4 → ℝ :=
  ![![1,1,1,1], ![1,-1,-1,1], ![-1,1,-1,1], ![-1,-1,1,1]] k

private def minus (k : Fin 4) : Fin 4 → ℝ :=
  ![![-1,-1,-1,1], ![-1,1,1,1], ![1,-1,1,1], ![1,1,-1,1]] k

private def off (g : Fin 4 → Fin 4 → ℝ) (v : Fin 4 → ℝ) : ℝ :=
  g 0 1 * v 0 * v 1 + g 0 2 * v 0 * v 2 + g 0 3 * v 0 * v 3 +
  g 1 2 * v 1 * v 2 + g 1 3 * v 1 * v 3 + g 2 3 * v 2 * v 3

private def diagQuad (r v : Fin 4 → ℝ) : ℝ := ∑ i, (r i)^2 * (v i)^2

private def pairOff (e v : Fin 4 → ℝ) : ℝ :=
  e 0*e 1*v 0*v 1 + e 0*e 2*v 0*v 2 + e 0*e 3*v 0*v 3 +
  e 1*e 2*v 1*v 2 + e 1*e 3*v 1*v 3 + e 2*e 3*v 2*v 3

private def pairQuad (r v : Fin 4 → ℝ) (C : ℝ) (s t : Fin 4) : ℝ :=
  diagQuad r v - C*(pairOff (plus s) v + pairOff (minus t) v)

private def polarPlus (g : Fin 4 → Fin 4 → ℝ) (C : ℝ) (s : Fin 4) : ℝ :=
  (1 - off g (plus s) / C)/8

private def polarMinus (g : Fin 4 → Fin 4 → ℝ) (C : ℝ) (t : Fin 4) : ℝ :=
  (1 - off g (minus t) / C)/8

private theorem parity_mass (g : Fin 4 → Fin 4 → ℝ) (C : ℝ) :
    (∑ s, polarPlus g C s) = 1/2 ∧ (∑ t, polarMinus g C t) = 1/2 := by
  constructor <;> simp [polarPlus, polarMinus, plus, minus, off, Fin.sum_univ_succ] <;> ring

private theorem polar_decomposition (g : Fin 4 → Fin 4 → ℝ) (C : ℝ) (r v : Fin 4 → ℝ)
    (hc : C ≠ 0) :
    (∑ s, ∑ t, 4*polarPlus g C s*polarMinus g C t*pairQuad r v C s t) =
      diagQuad r v + 2*off g v := by
  simp [polarPlus, polarMinus, pairQuad, plus, minus, off, pairOff, Fin.sum_univ_succ]
  field_simp
  <;> ring

private def rootEq (r : Fin 4 → ℝ) (c : ℝ) (j : Fin 4) : Prop :=
  ![schurSum ((r 1)^2) ((r 2)^2) ((r 3)^2) c,
    schurSum ((r 0)^2) ((r 2)^2) ((r 3)^2) c,
    schurSum ((r 0)^2) ((r 1)^2) ((r 3)^2) c,
    schurSum ((r 0)^2) ((r 1)^2) ((r 2)^2) c] j = 1

private theorem roots_exist (r : Fin 4 → ℝ) (hr : ∀ i, 0 < r i) (j : Fin 4) :
    ∃ c : ℝ, 0 < c ∧ rootEq r c j := by
  fin_cases j
  · simpa [rootEq] using root_exists ((r 1)^2) ((r 2)^2) ((r 3)^2) (sq_pos_of_pos (hr 1)) (sq_pos_of_pos (hr 2)) (sq_pos_of_pos (hr 3))
  · simpa [rootEq] using root_exists ((r 0)^2) ((r 2)^2) ((r 3)^2) (sq_pos_of_pos (hr 0)) (sq_pos_of_pos (hr 2)) (sq_pos_of_pos (hr 3))
  · simpa [rootEq] using root_exists ((r 0)^2) ((r 1)^2) ((r 3)^2) (sq_pos_of_pos (hr 0)) (sq_pos_of_pos (hr 1)) (sq_pos_of_pos (hr 3))
  · simpa [rootEq] using root_exists ((r 0)^2) ((r 1)^2) ((r 2)^2) (sq_pos_of_pos (hr 0)) (sq_pos_of_pos (hr 1)) (sq_pos_of_pos (hr 2))

private theorem roots_pair_positive (r v c : Fin 4 → ℝ) (C : ℝ)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) (hroot : ∀ j, rootEq r (c j) j)
    (hC : 0 ≤ C) (hlt : ∀ j, C < c j) (hdiag : 0 < diagQuad r v)
    (s t : Fin 4) : 0 < pairQuad r v C s t := by
  fin_cases s <;> fin_cases t
  · have hd : 0 < (r 0)^2*(v 0)^2 + (r 1)^2*(v 1)^2 + (r 2)^2*(v 2)^2 + (r 3)^2*(v 3)^2 := by
      convert hdiag using 1 <;> simp [diagQuad, Fin.sum_univ_succ] <;> ring
    have ht := triangle_quad_strict ((r 0)^2) ((r 1)^2) ((r 2)^2) ((r 3)^2)
      (c 3) C (v 0) (v 1) (v 2) (v 3)
      (sq_pos_of_pos (hr 0)) (sq_pos_of_pos (hr 1)) (sq_pos_of_pos (hr 2)) (sq_pos_of_pos (hr 3))
      (hc 3) hC (hlt 3) (by simpa [rootEq] using hroot 3) hd
    convert ht using 1 <;> simp [pairQuad, diagQuad, pairOff, plus, minus, Fin.sum_univ_succ] <;> ring
  · have hd : 0 < (r 1)^2*(v 1)^2 + (r 2)^2*(v 2)^2 + (r 3)^2*(v 3)^2 + (r 0)^2*(v 0)^2 := by
      convert hdiag using 1 <;> simp [diagQuad, Fin.sum_univ_succ] <;> ring
    have ht := triangle_quad_strict ((r 1)^2) ((r 2)^2) ((r 3)^2) ((r 0)^2)
      (c 0) C (v 1) (v 2) (v 3) (v 0)
      (sq_pos_of_pos (hr 1)) (sq_pos_of_pos (hr 2)) (sq_pos_of_pos (hr 3)) (sq_pos_of_pos (hr 0))
      (hc 0) hC (hlt 0) (by simpa [rootEq] using hroot 0) hd
    convert ht using 1 <;> simp [pairQuad, diagQuad, pairOff, plus, minus, Fin.sum_univ_succ] <;> ring
  · have hd : 0 < (r 0)^2*(v 0)^2 + (r 2)^2*(v 2)^2 + (r 3)^2*(v 3)^2 + (r 1)^2*(v 1)^2 := by
      convert hdiag using 1 <;> simp [diagQuad, Fin.sum_univ_succ] <;> ring
    have ht := triangle_quad_strict ((r 0)^2) ((r 2)^2) ((r 3)^2) ((r 1)^2)
      (c 1) C (v 0) (v 2) (v 3) (v 1)
      (sq_pos_of_pos (hr 0)) (sq_pos_of_pos (hr 2)) (sq_pos_of_pos (hr 3)) (sq_pos_of_pos (hr 1))
      (hc 1) hC (hlt 1) (by simpa [rootEq] using hroot 1) hd
    convert ht using 1 <;> simp [pairQuad, diagQuad, pairOff, plus, minus, Fin.sum_univ_succ] <;> ring
  · have hd : 0 < (r 0)^2*(v 0)^2 + (r 1)^2*(v 1)^2 + (r 3)^2*(v 3)^2 + (r 2)^2*(v 2)^2 := by
      convert hdiag using 1 <;> simp [diagQuad, Fin.sum_univ_succ] <;> ring
    have ht := triangle_quad_strict ((r 0)^2) ((r 1)^2) ((r 3)^2) ((r 2)^2)
      (c 2) C (v 0) (v 1) (v 3) (v 2)
      (sq_pos_of_pos (hr 0)) (sq_pos_of_pos (hr 1)) (sq_pos_of_pos (hr 3)) (sq_pos_of_pos (hr 2))
      (hc 2) hC (hlt 2) (by simpa [rootEq] using hroot 2) hd
    convert ht using 1 <;> simp [pairQuad, diagQuad, pairOff, plus, minus, Fin.sum_univ_succ] <;> ring
  · have hd : 0 < (r 1)^2*(-v 1)^2 + (r 2)^2*(-v 2)^2 + (r 3)^2*(v 3)^2 + (r 0)^2*(v 0)^2 := by
      convert hdiag using 1 <;> simp [diagQuad, Fin.sum_univ_succ] <;> ring
    have ht := triangle_quad_strict ((r 1)^2) ((r 2)^2) ((r 3)^2) ((r 0)^2)
      (c 0) C (-v 1) (-v 2) (v 3) (v 0)
      (sq_pos_of_pos (hr 1)) (sq_pos_of_pos (hr 2)) (sq_pos_of_pos (hr 3)) (sq_pos_of_pos (hr 0))
      (hc 0) hC (hlt 0) (by simpa [rootEq] using hroot 0) hd
    convert ht using 1 <;> simp [pairQuad, diagQuad, pairOff, plus, minus, Fin.sum_univ_succ] <;> ring
  · have hd : 0 < (r 0)^2*(v 0)^2 + (r 1)^2*(-v 1)^2 + (r 2)^2*(-v 2)^2 + (r 3)^2*(v 3)^2 := by
      convert hdiag using 1 <;> simp [diagQuad, Fin.sum_univ_succ] <;> ring
    have ht := triangle_quad_strict ((r 0)^2) ((r 1)^2) ((r 2)^2) ((r 3)^2)
      (c 3) C (v 0) (-v 1) (-v 2) (v 3)
      (sq_pos_of_pos (hr 0)) (sq_pos_of_pos (hr 1)) (sq_pos_of_pos (hr 2)) (sq_pos_of_pos (hr 3))
      (hc 3) hC (hlt 3) (by simpa [rootEq] using hroot 3) hd
    convert ht using 1 <;> simp [pairQuad, diagQuad, pairOff, plus, minus, Fin.sum_univ_succ] <;> ring
  · have hd : 0 < (r 0)^2*(v 0)^2 + (r 1)^2*(-v 1)^2 + (r 3)^2*(v 3)^2 + (r 2)^2*(-v 2)^2 := by
      convert hdiag using 1 <;> simp [diagQuad, Fin.sum_univ_succ] <;> ring
    have ht := triangle_quad_strict ((r 0)^2) ((r 1)^2) ((r 3)^2) ((r 2)^2)
      (c 2) C (v 0) (-v 1) (v 3) (-v 2)
      (sq_pos_of_pos (hr 0)) (sq_pos_of_pos (hr 1)) (sq_pos_of_pos (hr 3)) (sq_pos_of_pos (hr 2))
      (hc 2) hC (hlt 2) (by simpa [rootEq] using hroot 2) hd
    convert ht using 1 <;> simp [pairQuad, diagQuad, pairOff, plus, minus, Fin.sum_univ_succ] <;> ring
  · have hd : 0 < (r 0)^2*(v 0)^2 + (r 2)^2*(-v 2)^2 + (r 3)^2*(v 3)^2 + (r 1)^2*(-v 1)^2 := by
      convert hdiag using 1 <;> simp [diagQuad, Fin.sum_univ_succ] <;> ring
    have ht := triangle_quad_strict ((r 0)^2) ((r 2)^2) ((r 3)^2) ((r 1)^2)
      (c 1) C (v 0) (-v 2) (v 3) (-v 1)
      (sq_pos_of_pos (hr 0)) (sq_pos_of_pos (hr 2)) (sq_pos_of_pos (hr 3)) (sq_pos_of_pos (hr 1))
      (hc 1) hC (hlt 1) (by simpa [rootEq] using hroot 1) hd
    convert ht using 1 <;> simp [pairQuad, diagQuad, pairOff, plus, minus, Fin.sum_univ_succ] <;> ring
  · have hd : 0 < (r 0)^2*(-v 0)^2 + (r 2)^2*(-v 2)^2 + (r 3)^2*(v 3)^2 + (r 1)^2*(v 1)^2 := by
      convert hdiag using 1 <;> simp [diagQuad, Fin.sum_univ_succ] <;> ring
    have ht := triangle_quad_strict ((r 0)^2) ((r 2)^2) ((r 3)^2) ((r 1)^2)
      (c 1) C (-v 0) (-v 2) (v 3) (v 1)
      (sq_pos_of_pos (hr 0)) (sq_pos_of_pos (hr 2)) (sq_pos_of_pos (hr 3)) (sq_pos_of_pos (hr 1))
      (hc 1) hC (hlt 1) (by simpa [rootEq] using hroot 1) hd
    convert ht using 1 <;> simp [pairQuad, diagQuad, pairOff, plus, minus, Fin.sum_univ_succ] <;> ring
  · have hd : 0 < (r 0)^2*(-v 0)^2 + (r 1)^2*(v 1)^2 + (r 3)^2*(v 3)^2 + (r 2)^2*(-v 2)^2 := by
      convert hdiag using 1 <;> simp [diagQuad, Fin.sum_univ_succ] <;> ring
    have ht := triangle_quad_strict ((r 0)^2) ((r 1)^2) ((r 3)^2) ((r 2)^2)
      (c 2) C (-v 0) (v 1) (v 3) (-v 2)
      (sq_pos_of_pos (hr 0)) (sq_pos_of_pos (hr 1)) (sq_pos_of_pos (hr 3)) (sq_pos_of_pos (hr 2))
      (hc 2) hC (hlt 2) (by simpa [rootEq] using hroot 2) hd
    convert ht using 1 <;> simp [pairQuad, diagQuad, pairOff, plus, minus, Fin.sum_univ_succ] <;> ring
  · have hd : 0 < (r 0)^2*(-v 0)^2 + (r 1)^2*(v 1)^2 + (r 2)^2*(-v 2)^2 + (r 3)^2*(v 3)^2 := by
      convert hdiag using 1 <;> simp [diagQuad, Fin.sum_univ_succ] <;> ring
    have ht := triangle_quad_strict ((r 0)^2) ((r 1)^2) ((r 2)^2) ((r 3)^2)
      (c 3) C (-v 0) (v 1) (-v 2) (v 3)
      (sq_pos_of_pos (hr 0)) (sq_pos_of_pos (hr 1)) (sq_pos_of_pos (hr 2)) (sq_pos_of_pos (hr 3))
      (hc 3) hC (hlt 3) (by simpa [rootEq] using hroot 3) hd
    convert ht using 1 <;> simp [pairQuad, diagQuad, pairOff, plus, minus, Fin.sum_univ_succ] <;> ring
  · have hd : 0 < (r 1)^2*(v 1)^2 + (r 2)^2*(-v 2)^2 + (r 3)^2*(v 3)^2 + (r 0)^2*(-v 0)^2 := by
      convert hdiag using 1 <;> simp [diagQuad, Fin.sum_univ_succ] <;> ring
    have ht := triangle_quad_strict ((r 1)^2) ((r 2)^2) ((r 3)^2) ((r 0)^2)
      (c 0) C (v 1) (-v 2) (v 3) (-v 0)
      (sq_pos_of_pos (hr 1)) (sq_pos_of_pos (hr 2)) (sq_pos_of_pos (hr 3)) (sq_pos_of_pos (hr 0))
      (hc 0) hC (hlt 0) (by simpa [rootEq] using hroot 0) hd
    convert ht using 1 <;> simp [pairQuad, diagQuad, pairOff, plus, minus, Fin.sum_univ_succ] <;> ring
  · have hd : 0 < (r 0)^2*(-v 0)^2 + (r 1)^2*(-v 1)^2 + (r 3)^2*(v 3)^2 + (r 2)^2*(v 2)^2 := by
      convert hdiag using 1 <;> simp [diagQuad, Fin.sum_univ_succ] <;> ring
    have ht := triangle_quad_strict ((r 0)^2) ((r 1)^2) ((r 3)^2) ((r 2)^2)
      (c 2) C (-v 0) (-v 1) (v 3) (v 2)
      (sq_pos_of_pos (hr 0)) (sq_pos_of_pos (hr 1)) (sq_pos_of_pos (hr 3)) (sq_pos_of_pos (hr 2))
      (hc 2) hC (hlt 2) (by simpa [rootEq] using hroot 2) hd
    convert ht using 1 <;> simp [pairQuad, diagQuad, pairOff, plus, minus, Fin.sum_univ_succ] <;> ring
  · have hd : 0 < (r 0)^2*(-v 0)^2 + (r 2)^2*(v 2)^2 + (r 3)^2*(v 3)^2 + (r 1)^2*(-v 1)^2 := by
      convert hdiag using 1 <;> simp [diagQuad, Fin.sum_univ_succ] <;> ring
    have ht := triangle_quad_strict ((r 0)^2) ((r 2)^2) ((r 3)^2) ((r 1)^2)
      (c 1) C (-v 0) (v 2) (v 3) (-v 1)
      (sq_pos_of_pos (hr 0)) (sq_pos_of_pos (hr 2)) (sq_pos_of_pos (hr 3)) (sq_pos_of_pos (hr 1))
      (hc 1) hC (hlt 1) (by simpa [rootEq] using hroot 1) hd
    convert ht using 1 <;> simp [pairQuad, diagQuad, pairOff, plus, minus, Fin.sum_univ_succ] <;> ring
  · have hd : 0 < (r 1)^2*(-v 1)^2 + (r 2)^2*(v 2)^2 + (r 3)^2*(v 3)^2 + (r 0)^2*(-v 0)^2 := by
      convert hdiag using 1 <;> simp [diagQuad, Fin.sum_univ_succ] <;> ring
    have ht := triangle_quad_strict ((r 1)^2) ((r 2)^2) ((r 3)^2) ((r 0)^2)
      (c 0) C (-v 1) (v 2) (v 3) (-v 0)
      (sq_pos_of_pos (hr 1)) (sq_pos_of_pos (hr 2)) (sq_pos_of_pos (hr 3)) (sq_pos_of_pos (hr 0))
      (hc 0) hC (hlt 0) (by simpa [rootEq] using hroot 0) hd
    convert ht using 1 <;> simp [pairQuad, diagQuad, pairOff, plus, minus, Fin.sum_univ_succ] <;> ring
  · have hd : 0 < (r 0)^2*(-v 0)^2 + (r 1)^2*(-v 1)^2 + (r 2)^2*(v 2)^2 + (r 3)^2*(v 3)^2 := by
      convert hdiag using 1 <;> simp [diagQuad, Fin.sum_univ_succ] <;> ring
    have ht := triangle_quad_strict ((r 0)^2) ((r 1)^2) ((r 2)^2) ((r 3)^2)
      (c 3) C (-v 0) (-v 1) (v 2) (v 3)
      (sq_pos_of_pos (hr 0)) (sq_pos_of_pos (hr 1)) (sq_pos_of_pos (hr 2)) (sq_pos_of_pos (hr 3))
      (hc 3) hC (hlt 3) (by simpa [rootEq] using hroot 3) hd
    convert ht using 1 <;> simp [pairQuad, diagQuad, pairOff, plus, minus, Fin.sum_univ_succ] <;> ring

private theorem root_total_bound (r : Fin 4 → ℝ) (c C : ℝ) (j : Fin 4)
    (hr : ∀ i, 0 < r i) (hc : 0 < c) (heq : rootEq r c j) (hC : c ≤ C) :
    (∑ i, r i)^2 ≤ (13/4:ℝ)*((∑ i, (r i)^2)+2*C) := by
  fin_cases j
  · have ht := triangle_bound (r 1) (r 2) (r 3) c (hr 1) (hr 2) (hr 3) hc
      (by simpa [rootEq] using heq)
    simp [Fin.sum_univ_succ] at *
    nlinarith [sq_nonneg (4*(r 1+r 2+r 3)-9*r 0)]
  · have ht := triangle_bound (r 0) (r 2) (r 3) c (hr 0) (hr 2) (hr 3) hc
      (by simpa [rootEq] using heq)
    simp [Fin.sum_univ_succ] at *
    nlinarith [sq_nonneg (4*(r 0+r 2+r 3)-9*r 1)]
  · have ht := triangle_bound (r 0) (r 1) (r 3) c (hr 0) (hr 1) (hr 3) hc
      (by simpa [rootEq] using heq)
    simp [Fin.sum_univ_succ] at *
    nlinarith [sq_nonneg (4*(r 0+r 1+r 3)-9*r 2)]
  · have ht := triangle_bound (r 0) (r 1) (r 2) c (hr 0) (hr 1) (hr 2) hc
      (by simpa [rootEq] using heq)
    simp [Fin.sum_univ_succ] at *
    nlinarith [sq_nonneg (4*(r 0+r 1+r 2)-9*r 3)]

private theorem algebra_bound (r : Fin 4 → ℝ) (g : Fin 4 → Fin 4 → ℝ) (R : ℝ)
    (hr : ∀ i, 0 < r i)
    (hplus : ∀ s, (∑ i, (r i)^2) + 2*off g (plus s) ≤ R^2)
    (hminus : ∀ t, (∑ i, (r i)^2) + 2*off g (minus t) ≤ R^2)
    (hnull : ∃ v, 0 < diagQuad r v ∧ diagQuad r v + 2*off g v = 0) :
    (∑ i, r i)^2 ≤ (13/4:ℝ)*R^2 := by
  classical
  obtain ⟨v, hdiag, hzero⟩ := hnull
  let C := (R^2 - (∑ i, (r i)^2))/2
  have b0 := hplus 0
  have b1 := hplus 1
  have b2 := hplus 2
  have b3 := hplus 3
  have b4 := hminus 0
  have b5 := hminus 1
  have b6 := hminus 2
  have b7 := hminus 3
  simp [off, plus, minus] at b0 b1 b2 b3 b4 b5 b6 b7
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hp (s) : off g (plus s) ≤ C := by have hh := hplus s; dsimp [C]; linarith
  have hm (t) : off g (minus t) ≤ C := by have hh := hminus t; dsimp [C]; linarith
  have hCp : 0 < C := by
    by_contra hn
    have hz : C = 0 := by linarith
    have htr : R^2 = ∑ i, (r i)^2 := by dsimp [C] at hz; linarith
    have g01 : g 0 1 = 0 := by linarith
    have g02 : g 0 2 = 0 := by linarith
    have g03 : g 0 3 = 0 := by linarith
    have g12 : g 1 2 = 0 := by linarith
    have g13 : g 1 3 = 0 := by linarith
    have g23 : g 2 3 = 0 := by linarith
    simp [off, g01, g02, g03, g12, g13, g23] at hzero
    linarith
  have hpp (s) : 0 ≤ polarPlus g C s := by
    unfold polarPlus
    have h := (div_le_one hCp).mpr (hp s)
    linarith
  have hpm (t) : 0 ≤ polarMinus g C t := by
    unfold polarMinus
    have h := (div_le_one hCp).mpr (hm t)
    linarith
  choose c hc heq using roots_exist r hr
  have hj : ∃ j, c j ≤ C := by
    by_contra hn
    push Not at hn
    have hall := roots_pair_positive r v c C hr hc heq hC hn hdiag
    have havg := polar_decomposition g C r v hCp.ne'
    have ⟨p, hp, hpos⟩ := (Finset.sum_pos_iff_of_nonneg (fun s _ => hpp s)).mp
      (show 0 < ∑ s, polarPlus g C s by rw [(parity_mass g C).1]; norm_num)
    have ⟨q, hq, hqpos⟩ := (Finset.sum_pos_iff_of_nonneg (fun t _ => hpm t)).mp
      (show 0 < ∑ t, polarMinus g C t by rw [(parity_mass g C).2]; norm_num)
    have hnonneg (s t : Fin 4) : 0 ≤ 4*polarPlus g C s*polarMinus g C t*pairQuad r v C s t := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hpp s)) (hpm t)) (hall s t).le
    have hpositive : 0 < ∑ s, ∑ t, 4*polarPlus g C s*polarMinus g C t*pairQuad r v C s t := by
      apply Finset.sum_pos'
      · intro s _; exact Finset.sum_nonneg (fun t _ => hnonneg s t)
      · refine ⟨p, hp, ?_⟩
        apply Finset.sum_pos' (fun t _ => hnonneg p t)
        refine ⟨q, hq, ?_⟩
        exact mul_pos (mul_pos (mul_pos (by norm_num) hpos) hqpos) (hall p q)
    rw [havg, hzero] at hpositive
    linarith
  obtain ⟨j, hj⟩ := hj
  have hbound := root_total_bound r (c j) C j hr (hc j) (heq j) hj
  dsimp [C] at hbound
  linarith

private theorem norm_quad (x : Fin 4 → E) (v : Fin 4 → ℝ) :
    ‖∑ i, v i • x i‖^2 = diagQuad (fun i => ‖x i‖) v + 2*off (Matrix.gram ℝ x) v := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp [diagQuad, off, Matrix.gram, Fin.sum_univ_succ]
  rw [real_inner_comm (x 1) (x 0), real_inner_comm (x 2) (x 0),
    real_inner_comm (x 3) (x 0), real_inner_comm (x 2) (x 1),
    real_inner_comm (x 3) (x 1), real_inner_comm (x 3) (x 2)]
  ring

def signedSum (x : Fin 4 → E) (ε : Fin 4 → Bool) : E := ∑ i, sgn (ε i) • x i

noncomputable def maxNorm (x : Fin 4 → E) : ℝ :=
  (Finset.univ : Finset (Fin 4 → Bool)).sup' Finset.univ_nonempty (fun ε => ‖signedSum x ε‖)

theorem signedSum_le_max (x : Fin 4 → E) (ε : Fin 4 → Bool) : ‖signedSum x ε‖ ≤ maxNorm x := by
  exact Finset.le_sup' (f := fun ε => ‖signedSum x ε‖) (Finset.mem_univ ε)

private theorem maxNorm_nonneg (x : Fin 4 → E) : 0 ≤ maxNorm x :=
  (norm_nonneg _).trans (signedSum_le_max x (fun _ => true))

private theorem signs_bound (x : Fin 4 → E) (e : Fin 4 → ℝ) (he : ∀ i, e i = 1 ∨ e i = -1) :
    ‖∑ i, e i • x i‖ ≤ maxNorm x := by
  let ε : Fin 4 → Bool := fun i => decide (e i = 1)
  have eq (i) : sgn (ε i) = e i := by
    rcases he i with h | h <;> norm_num [sgn, ε, h]
  simpa [signedSum, eq] using signedSum_le_max x ε

private theorem plus_signs (s : Fin 4) (i : Fin 4) : plus s i = 1 ∨ plus s i = -1 := by
  fin_cases s <;> fin_cases i <;> norm_num [plus]

private theorem minus_signs (s : Fin 4) (i : Fin 4) : minus s i = 1 ∨ minus s i = -1 := by
  fin_cases s <;> fin_cases i <;> norm_num [minus]

private theorem sign_diag (r e : Fin 4 → ℝ) (he : ∀ i, e i = 1 ∨ e i = -1) :
    diagQuad r e = ∑ i, (r i)^2 := by
  apply Finset.sum_congr rfl
  intro i _
  rcases he i with h | h <;> simp [h]

private theorem plus_squared_bound (x : Fin 4 → E) (s : Fin 4) :
    (∑ i, ‖x i‖^2) + 2*off (Matrix.gram ℝ x) (plus s) ≤ (maxNorm x)^2 := by
  have h := mul_self_le_mul_self (norm_nonneg _) (signs_bound x (plus s) (plus_signs s))
  simpa only [← pow_two, norm_quad, sign_diag _ _ (plus_signs s)] using h

private theorem minus_squared_bound (x : Fin 4 → E) (s : Fin 4) :
    (∑ i, ‖x i‖^2) + 2*off (Matrix.gram ℝ x) (minus s) ≤ (maxNorm x)^2 := by
  have h := mul_self_le_mul_self (norm_nonneg _) (signs_bound x (minus s) (minus_signs s))
  simpa only [← pow_two, norm_quad, sign_diag _ _ (minus_signs s)] using h

private theorem trace_le_max_squared (x : Fin 4 → E) : ∑ i, ‖x i‖^2 ≤ (maxNorm x)^2 := by
  have b0 := plus_squared_bound x 0
  have b1 := plus_squared_bound x 1
  have b2 := plus_squared_bound x 2
  have b3 := plus_squared_bound x 3
  have b4 := minus_squared_bound x 0
  have b5 := minus_squared_bound x 1
  have b6 := minus_squared_bound x 2
  have b7 := minus_squared_bound x 3
  simp [off, plus, minus] at b0 b1 b2 b3 b4 b5 b6 b7
  linarith

private theorem dependent_nonzero_squared_bound (x : Fin 4 → E)
    (hx : ∀ i, x i ≠ 0) (hdep : ¬ LinearIndependent ℝ x) :
    (∑ i, ‖x i‖)^2 ≤ (13/4:ℝ)*(maxNorm x)^2 := by
  obtain ⟨v, hv, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hr (i) : 0 < ‖x i‖ := norm_pos_iff.mpr (hx i)
  have hdiag : 0 < diagQuad (fun i => ‖x i‖) v := by
    apply Finset.sum_pos' (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    exact ⟨j, Finset.mem_univ j, mul_pos (sq_pos_of_pos (hr j)) (sq_pos_of_ne_zero hj)⟩
  have hzero : diagQuad (fun i => ‖x i‖) v + 2*off (Matrix.gram ℝ x) v = 0 := by
    rw [← norm_quad, hv, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  exact algebra_bound (fun i => ‖x i‖) (Matrix.gram ℝ x) (maxNorm x) hr
    (plus_squared_bound x) (minus_squared_bound x) ⟨v, hdiag, hzero⟩

private theorem zero_column_squared_bound (x : Fin 4 → E) (j : Fin 4) (hj : x j = 0) :
    (∑ i, ‖x i‖)^2 ≤ (13/4:ℝ)*(maxNorm x)^2 := by
  classical
  let S : Finset (Fin 4) := Finset.univ.erase j
  have hsum : (∑ i ∈ S, ‖x i‖) = ∑ i, ‖x i‖ := by
    simp [S, hj]
  have hsum2 : (∑ i ∈ S, ‖x i‖^2) = ∑ i, ‖x i‖^2 := by
    simp [S, hj]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun i => ‖x i‖)
  have hcard : S.card = 3 := by simp [S]
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hcard, Nat.cast_ofNat,
    hsum, hsum2] at hcs
  have htr := trace_le_max_squared x
  nlinarith [sq_nonneg (maxNorm x)]

private theorem four_vector_squared (x : Fin 4 → EuclideanSpace ℝ (Fin 3)) :
    (∑ i, ‖x i‖)^2 ≤ (13/4:ℝ)*(maxNorm x)^2 := by
  by_cases hx : ∀ i, x i ≠ 0
  · apply dependent_nonzero_squared_bound x hx
    intro hi
    have h := hi.fintype_card_le_finrank
    norm_num [finrank_euclideanSpace_fin] at h
  · push Not at hx
    obtain ⟨j, hj⟩ := hx
    exact zero_column_squared_bound x j hj

theorem four_vector_inequality (x : Fin 4 → EuclideanSpace ℝ (Fin 3)) :
    (∑ i, ‖x i‖) ≤ (Real.sqrt 13/2)*maxNorm x := by
  have h := four_vector_squared x
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 13 by norm_num)
  have hp := Real.sqrt_nonneg 13
  have hm := maxNorm_nonneg x
  have ht : 0 ≤ ∑ i, ‖x i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  nlinarith [mul_nonneg hp hm]

end D5.S3.Geometry.FourVectorSignSumBound
