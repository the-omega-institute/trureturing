/- GID: D5/S3/Geometry/Hyperideal/FourCycleEnvelopes
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/FourCycleEnvelopes
   mirror-E: none(waiver:universal-real-inequality)
   anchors: []
   utility: none
   digest: Mixed-coordinate monotonicity for the six-variable hyper-ideal cosine. -/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
Local edge order: (12,13,14,34,24,23). The first and fourth
coordinates are opposite. The four-cycle occupies coordinates 1,2,4,5.

The formula is Zhao, arXiv:2601.15174v2, Lemma 2.2. Division by the two
positive square roots is equivalent to division by sqrt(A*B). The proof
derives adjacent-coordinate monotonicity, including endpoints, from the
explicit derivative numerator. It does not assume monotonicity, a positive
derivative, a pre-existing geometric solution, or an endpoint certificate.

This is the real-analytic part of CFMP_GEOMETRIC_REALIZATION.md Section 16.
It does not construct a tetrahedron, a face pairing, a co-volume function,
a manifold or a Ricci-flow solution. The formula-to-tetrahedron realization
and the global existence argument remain separate ordinary mathematics.

The public comparison is an unbounded real inequality. Numeric endpoint
reductions are internal steps, not standalone finite-instance declarations.
The intended utility classification is none: this is neither bounded
enumeration, a certificate checker, a supplied-numeric-premise reduction,
nor a concrete realized finite instance. Classification remains reviewable.
No additional axiom, sorry or opaque external certificate is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

/-- A squared positive denominator in the hyper-ideal cosine formula. -/
def rad (x y z : ℝ) : ℝ := 2*x*y*z + x^2 + y^2 + z^2 - 1

/-- The original numerator, with all six independently varying coordinates. -/
def numerator (x y z o v w : ℝ) : ℝ :=
  y*z + v*w + x*y*v + x*z*w - (x^2-1)*o

/-- The exact real formula; the two radicands are proved positive below. -/
def cosine (x y z o v w : ℝ) : ℝ :=
  numerator x y z o v w / Real.sqrt (rad x y w) / Real.sqrt (rad x z v)

/-- Mixed-coordinate comparison on the entire real cube. This exposes the
existing derivative proof so subsequent shapes reuse one analytic owner. -/
theorem cosine_mixed_comparison : ∀ x y z o v w Y Z O V W : ℝ,
      x ∈ Set.Icc 1 2 → y ∈ Set.Icc 1 2 → z ∈ Set.Icc 1 2 →
      o ∈ Set.Icc 1 2 → v ∈ Set.Icc 1 2 → w ∈ Set.Icc 1 2 →
      Y ∈ Set.Icc 1 2 → Z ∈ Set.Icc 1 2 → O ∈ Set.Icc 1 2 →
      V ∈ Set.Icc 1 2 → W ∈ Set.Icc 1 2 →
      y ≤ Y → z ≤ Z → O ≤ o → v ≤ V → w ≤ W →
      cosine x y z o v w ≤ cosine x Y Z O V W := by
  -- Positivity is established for the actual radicand, not postulated.
  have hr : ∀ x y z : ℝ, 1 ≤ x → 1 ≤ y → 1 ≤ z → 0 < rad x y z := by
    intro x y z hx hy hz
    have hx2 : 1 ≤ x^2 := by nlinarith [sq_nonneg (x-1)]
    have hy2 : 1 ≤ y^2 := by nlinarith [sq_nonneg (y-1)]
    have hz2 : 1 ≤ z^2 := by nlinarith [sq_nonneg (z-1)]
    have hp : 0 ≤ 2*x*y*z := by positivity
    unfold rad
    linarith
  -- Only one neighbouring coordinate needs calculus; the others follow by
  -- the actual two tetrahedral symmetries established later in this proof.
  have hm : ∀ x z o v w : ℝ,
      x ∈ Set.Icc 1 2 → z ∈ Set.Icc 1 2 → o ∈ Set.Icc 1 2 →
      v ∈ Set.Icc 1 2 → w ∈ Set.Icc 1 2 →
      MonotoneOn (fun y => cosine x y z o v w) (Set.Icc 1 2) := by
    intro x z o v w hx hz ho hv hw
    have hd : ∀ y ∈ Set.Icc (1:ℝ) 2,
        DifferentiableAt ℝ (fun t => cosine x t z o v w) y ∧
        0 ≤ deriv (fun t => cosine x t z o v w) y := by
      intro y hy
      have hA : 0 < rad x y w := hr x y w hx.1 hy.1 hw.1
      have hB : 0 < rad x z v := hr x z v hx.1 hz.1 hv.1
      have hs : 0 < Real.sqrt (rad x y w) := Real.sqrt_pos.2 hA
      have ht : 0 < Real.sqrt (rad x z v) := Real.sqrt_pos.2 hB
      have hs2 : (Real.sqrt (rad x y w))^2 = rad x y w :=
        Real.sq_sqrt hA.le
      have dA : HasDerivAt (fun t : ℝ => rad x t w) (2*x*w+2*y) y := by
        convert ((((((hasDerivAt_id y).const_mul (2*x)).mul_const w).add_const (x^2)).add
          ((hasDerivAt_id y).pow 2)).add_const (w^2)).sub_const 1 using 1
        all_goals try rfl
        all_goals simp only [id_eq, mul_one]
        all_goals ring
      have dP : HasDerivAt (fun t : ℝ => numerator x t z o v w) (z+x*v) y := by
        convert (((((hasDerivAt_id y).mul_const z).add_const (v*w)).add
          (((hasDerivAt_id y).const_mul x).mul_const v)).add_const (x*z*w)).sub_const
          ((x^2-1)*o) using 1
        all_goals try rfl
        all_goals simp only [mul_one, one_mul]
      have dC := (dP.fun_div (dA.sqrt hA.ne') hs.ne').div_const
        (Real.sqrt (rad x z v))
      -- The derivative sign hinges on a genuinely coupled polynomial.
      let Q := x*o*w + x*v + y*o + y*v*w + z*(1-w^2)
      have hxo : 1 ≤ x*o := by
        exact one_le_mul_of_one_le_of_one_le hx.1 ho.1
      have hxv : 1 ≤ x*v := by
        exact one_le_mul_of_one_le_of_one_le hx.1 hv.1
      have hyo : 1 ≤ y*o := by
        exact one_le_mul_of_one_le_of_one_le hy.1 ho.1
      have hyv : 1 ≤ y*v := by
        exact one_le_mul_of_one_le_of_one_le hy.1 hv.1
      have h1 : w ≤ x*o*w := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hxo (by linarith [hw.1])
      have h2 : w ≤ y*v*w := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hyv (by linarith [hw.1])
      have hn : 1-w^2 ≤ 0 := by nlinarith [sq_nonneg (w-1), hw.1]
      have h3 : 2*(1-w^2) ≤ z*(1-w^2) :=
        mul_le_mul_of_nonpos_right hz.2 hn
      have h4 : 0 ≤ (2-w)*(w+1) :=
        mul_nonneg (sub_nonneg.mpr hw.2) (by linarith [hw.1])
      have hQ : 0 ≤ Q := by dsimp [Q]; nlinarith
      have hxq : 0 ≤ x^2-1 := by nlinarith [sq_nonneg (x-1), hx.1]
      have hcore : 0 ≤ (z+x*v)*rad x y w - numerator x y z o v w*(x*w+y) := by
        calc
          0 ≤ (x^2-1)*Q := mul_nonneg hxq hQ
          _ = _ := by dsimp [Q, rad, numerator]; ring
      let r := (z+x*v)*Real.sqrt (rad x y w) -
        numerator x y z o v w*((2*x*w+2*y)/(2*Real.sqrt (rad x y w)))
      have hc : ((2*x*w+2*y)/(2*Real.sqrt (rad x y w))) *
          Real.sqrt (rad x y w) = x*w+y := by
        field_simp [hs.ne']
      have hmultiply : r*Real.sqrt (rad x y w) =
          (z+x*v)*rad x y w - numerator x y z o v w*(x*w+y) := by
        calc
          _ = (z+x*v)*(Real.sqrt (rad x y w))^2 -
              numerator x y z o v w *
                (((2*x*w+2*y)/(2*Real.sqrt (rad x y w)))*Real.sqrt (rad x y w)) := by
                  dsimp [r]; ring
          _ = _ := by rw [hs2, hc]
      have hrnonneg : 0 ≤ r := by
        by_contra h
        have hneg := mul_neg_of_neg_of_pos (lt_of_not_ge h) hs
        rw [hmultiply] at hneg
        exact (not_lt_of_ge hcore) hneg
      have hdC : HasDerivAt (fun t => cosine x t z o v w)
          ((r/(Real.sqrt (rad x y w))^2)/Real.sqrt (rad x z v)) y := by
        simpa only [cosine, r] using dC
      exact ⟨hdC.differentiableAt, by
        rw [hdC.deriv]
        exact div_nonneg (div_nonneg hrnonneg (sq_nonneg _)) ht.le⟩
    exact monotoneOn_of_deriv_nonneg (convex_Icc 1 2)
      (fun t ht => (hd t ht).1.continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).1.differentiableWithinAt)
      (fun t ht => (hd t (interior_subset ht)).2)
  -- Actual symmetries of the rational square-root expression. They do not
  -- identify distinct global edges or impose equality of their lengths.
  have hswap : ∀ x y z o v w : ℝ,
      cosine x y z o v w = cosine x z y o w v := by
    intro x y z o v w
    have hp : numerator x y z o v w = numerator x z y o w v := by
      unfold numerator; ring
    unfold cosine
    rw [hp, div_div, div_div]
    rw [mul_comm (Real.sqrt (rad x y w)) (Real.sqrt (rad x z v))]
  have hflip : ∀ x y z o v w : ℝ,
      cosine x y z o v w = cosine x w v o z y := by
    intro x y z o v w
    have hp : numerator x y z o v w = numerator x w v o z y := by
      unfold numerator; ring
    have ha : rad x y w = rad x w y := by unfold rad; ring
    have hb : rad x z v = rad x v z := by unfold rad; ring
    unfold cosine
    rw [hp, ha, hb]
  have cmp : ∀ x y z o v w Y Z O V W : ℝ,
      x ∈ Set.Icc 1 2 → y ∈ Set.Icc 1 2 → z ∈ Set.Icc 1 2 →
      o ∈ Set.Icc 1 2 → v ∈ Set.Icc 1 2 → w ∈ Set.Icc 1 2 →
      Y ∈ Set.Icc 1 2 → Z ∈ Set.Icc 1 2 → O ∈ Set.Icc 1 2 →
      V ∈ Set.Icc 1 2 → W ∈ Set.Icc 1 2 →
      y ≤ Y → z ≤ Z → O ≤ o → v ≤ V → w ≤ W →
      cosine x y z o v w ≤ cosine x Y Z O V W := by
    intro x y z o v w Y Z O V W hx hy hz ho hv hw hY hZ hO hV hW hyY hzZ hOo hvV hwW
    calc
      cosine x y z o v w ≤ cosine x Y z o v w :=
        hm x z o v w hx hz ho hv hw hy hY hyY
      _ = cosine x z Y o w v := hswap _ _ _ _ _ _
      _ ≤ cosine x Z Y o w v := hm x Y o w v hx hY ho hw hv hz hZ hzZ
      _ = cosine x Y Z o v w := (hswap _ _ _ _ _ _).symm
      _ = cosine x w v o Z Y := hflip _ _ _ _ _ _
      _ = cosine x v w o Y Z := hswap _ _ _ _ _ _
      _ ≤ cosine x V w o Y Z := hm x w o Y Z hx hw ho hY hZ hv hV hvV
      _ = cosine x w V o Z Y := (hswap _ _ _ _ _ _).symm
      _ = cosine x Y Z o V w := (hflip _ _ _ _ _ _).symm
      _ = cosine x w V o Z Y := hflip _ _ _ _ _ _
      _ ≤ cosine x W V o Z Y := hm x V o Z Y hx hV ho hZ hY hw hW hwW
      _ = cosine x Y Z o V W := (hflip _ _ _ _ _ _).symm
      _ ≤ cosine x Y Z O V W := by
        have hs : 0 ≤ x^2-1 := by nlinarith [sq_nonneg (x-1), hx.1]
        have hp : numerator x Y Z o V W ≤ numerator x Y Z O V W := by
          unfold numerator
          nlinarith [mul_nonneg hs (sub_nonneg.mpr hOo)]
        exact div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right hp (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  exact cmp

#print axioms cosine_mixed_comparison

end D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
