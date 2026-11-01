/- GID: D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianRows
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/InfiniteGaussianRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute countable Gaussian contraction with arbitrary finite external occupations. -/

import D5.S3.VertexAlgebra.TwistedGround.GaussianExternalBlock
import D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientScaling
import Mathlib.Analysis.Normed.Group.Tannery

/-! Positive external scaling transfers the joint Gaussian norm estimate
to each occupation slice. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp
open Filter Topology
namespace D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianRows
open InfiniteGaussianFock GaussianExternalBlock GaussianCoefficientScaling
open FactorialFockMetric (Occupation weight weight_pos)
universe u v w
variable {X : Type u} {I : Type v} {Y : Type w}
variable [Fintype X] [DecidableEq X] [DecidableEq I]

/-- An ordinary external coefficient, without external factorial scaling. -/
def row (P : Matrix X X ℂ) (A : Data I) (R : X → ℓ²(I, ℂ))
    (d : Occupation X) (n : Occupation I) : ℂ :=
  coefficient (kernel P A R) (d.sumElim n)

/-- Restrict the proved joint occupation norm to an injected external slice,
then cancel its positive external factorial and scaling constants. -/
theorem row_square_summable (P : Matrix X X ℂ) (A : Data I)
    (R : X → ℓ²(I, ℂ)) (hP : ∀ x y, P x y = P y x) (d : Occupation X) :
    Summable (fun n : Occupation I => (weight n : ℝ) * ‖row P A R d n‖ ^ 2) := by
  obtain ⟨t,ht,hstrict⟩ := exists_positive_scale P A R
  let D := data P A R hP (t : ℂ) hstrict
  let inj : Occupation I → Occupation (X ⊕ I) := fun n => d.sumElim n
  have hinj : Function.Injective inj := by
    intro n m h
    ext i
    exact congrArg (fun a : Occupation (X ⊕ I) => a (.inr i)) h
  have hs := D.occupation_summable.comp_injective hinj
  have hcoeff (n : Occupation I) :
      coefficient D.kernel (inj n) = (t : ℂ) ^ d.degree * row P A R d n := by
    change coefficient (fun i j => operator P A R (t : ℂ) (lp.single 2 j 1) i)
      (d.sumElim n) = _
    simp_rw [operator_entry]
    exact external_scaling (kernel P A R) (t : ℂ) d n
  have hweight (n : Occupation I) : weight (inj n) = weight d * weight n :=
    Finsupp.prod_sumElim d n (fun _ k => k.factorial)
  have hconst : (weight d : ℝ) * ‖(t : ℂ) ^ d.degree‖ ^ 2 ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (Nat.ne_of_gt (weight_pos d))
    · exact pow_ne_zero _ (norm_ne_zero_iff.mpr (pow_ne_zero _ (by exact_mod_cast ht.ne')))
  apply (summable_mul_left_iff hconst).mp
  convert hs using 1
  funext n
  simp only [Function.comp_apply]
  rw [hcoeff, hweight, Nat.cast_mul, norm_mul, mul_pow]
  ring

variable [Fintype Y] [DecidableEq Y]

/-- Genuine absolute convergence of the internal factorial contraction. The
external blocks and mixed l2 rows are unrestricted, and no full joint
contraction, positivity, commutativity or sewing premise is assumed. -/
theorem contraction_norm_summable (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ)
    (A B : Data I) (R : X → ℓ²(I, ℂ)) (S : Y → ℓ²(I, ℂ))
    (hP : ∀ x y, P x y = P y x) (hQ : ∀ x y, Q x y = Q y x)
    (d : Occupation X) (e : Occupation Y) :
    Summable (fun n : Occupation I =>
      ‖(weight n : ℂ) * row P A R d n * row Q B S e n‖) := by
  have hs := ((row_square_summable P A R hP d).add
    (row_square_summable Q B S hQ e)).div_const 2
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hs
  simp only [norm_mul, Complex.norm_natCast]
  have h := mul_nonneg (Nat.cast_nonneg (weight n) : (0 : ℝ) ≤ _) (sq_nonneg
    (‖row P A R d n‖ - ‖row Q B S e n‖))
  nlinarith

/-- A coordinate cutoff still sums every occupation supported in it. -/
def cutoff (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ)
    (A B : Data I) (R : X → ℓ²(I, ℂ)) (S : Y → ℓ²(I, ℂ))
    (d : Occupation X) (e : Occupation Y) (F : Finset I) : ℂ :=
  ∑' n : {n : Occupation I // n.support ⊆ F},
    (weight n.val : ℂ) * row P A R d n.val * row Q B S e n.val

/-- Absolute convergence gives the whole support-net limit, with neither an
enumeration of the modes nor a particle-number cutoff. -/
theorem cutoff_tendsto (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ)
    (A B : Data I) (R : X → ℓ²(I, ℂ)) (S : Y → ℓ²(I, ℂ))
    (hP : ∀ x y, P x y = P y x) (hQ : ∀ x y, Q x y = Q y x)
    (d : Occupation X) (e : Occupation Y) :
    Tendsto (cutoff P Q A B R S d e) atTop
      (𝓝 (∑' n : Occupation I, (weight n : ℂ) * row P A R d n * row Q B S e n)) := by
  let g (n : Occupation I) := (weight n : ℂ) * row P A R d n * row Q B S e n
  let f (F : Finset I) (n : Occupation I) := if n.support ⊆ F then g n else 0
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (contraction_norm_summable P Q A B R S hP hQ d e) (f := f) (g := g) ?_ ?_
  · convert h using 1
    funext F
    let T : Set (Occupation I) := {n | n.support ⊆ F}
    change (∑' n : T, g n.val) = _
    rw [tsum_subtype T]
    apply tsum_congr
    intro n
    by_cases hn : n.support ⊆ F <;> simp [T, f, Set.indicator, hn]
  · intro n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n.support] with F hF
    simp [f, hF]
  · exact Filter.Eventually.of_forall (fun F n => by
      dsimp [f]
      split_ifs <;> simp [g] <;> positivity)

end D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianRows
