/- GID: D5/S3/VertexAlgebra/BRST/GradedLieSplitBracketIdentity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/GradedLieSplitBracketIdentity
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Split Jacobi coefficient and signed Cartan defect for the native BPZ form. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechBRSTRealLie
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldNullMomentum
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOppositeRootBracket
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
The native split-bracket calculation uses the invariant form and the signed
opposite-root bracket. Background: R. E. Borcherds, *A characterization of
generalized Kac–Moody algebras*, J. Algebra 174 (1995), 1073–1079, §3,
and E. Jurisich, *Generalized Kac–Moody Lie algebras, free Lie algebras and the
structure of the Monster Lie algebra*, J. Pure Appl. Algebra 126 (1998),
233–266, §§5–6.

Provenance: model-derived direct-presentation argument, equations (8)–(11)
of the 2026-11-24 oracle answer. Kernel verification pending.

proof_shape: paired_split_bracket, nativeRelativeBPZ_split_bracket,
  nativeRelativeBPZ_split_bracket_tensor_block,
  nativeRelativeBPZ_lie_eq_zero_of_first_coordinate_one,
  momentumRealBPZ_split_bracket: content
admission_basis: escape-witness
escape_witness: Jacobi and invariance yield two pairings of mixed brackets.
The triangular expansion discards the two isotropic pairings and the
Cartan cross terms. The two remaining Cartan pairings give the signed
determinant with the hyperbolic momentum coefficient.

The native coordinates are (m, -n). For oracle degrees (m,n) and (r,s),
the native Cartan form therefore gives -m*s - n*r.

To pass from these coefficients to the full native split tensor, use
opposite-degree detection as in GradedLiePrimitiveGenerators.eq_zero_of_pairing_opposite.
Its direct-sum/annihilator argument applies with momenta as indices and native
momentum selection as orthogonality. On the fixed real side the Cartan source
gives realMomentumWeightSpace_isInternal and realMomentumWeightSpace_finiteDimensional.
One still needs to package each perfect opposite-momentum pairing as a dual
equivalence, choose finite dual bases, and sum the resulting tensors over the
positive pairs of momenta adding to the input momentum. For input momentum p,
supported positive summands have first coordinate in [1, p 0 - 1] and second
coordinate in [p 1 - 1, 1], by the native bound q 0 * q 1 ≤ 1.
-/

set_option autoImplicit false

open scoped DirectSum TensorProduct

namespace D5.S3.VertexAlgebra.GradedLieSplitBracketIdentity

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

private theorem pairing_lie_lie (B : LinearMap.BilinForm R L)
    (hInv : ∀ a b c : L, B ⁅a, b⁆ c = B a ⁅b, c⁆) (x y u v : L) :
    B ⁅x, y⁆ ⁅u, v⁆ = B ⁅x, u⁆ ⁅y, v⁆ - B ⁅y, u⁆ ⁅x, v⁆ := by
  have move (a b c : L) : B ⁅a, b⁆ c = -B b ⁅a, c⁆ := by
    rw [← lie_skew a b, B.neg_left, hInv b a c]
  calc
    B ⁅x, y⁆ ⁅u, v⁆ = B ⁅⁅x, y⁆, u⁆ v := (hInv ⁅x, y⁆ u v).symm
    _ = B ⁅x, u⁆ ⁅y, v⁆ - B ⁅y, u⁆ ⁅x, v⁆ := by
      rw [lie_lie, B.sub_left, move x ⁅y, u⁆ v, move y ⁅x, u⁆ v]
      abel

private theorem pairing_eq_of_triangular (B : LinearMap.BilinForm R L) (hSymm : B.IsSymm)
    (negPart zeroPart posPart : L →ₗ[R] L)
    (hSplit : ∀ a, negPart a + zeroPart a + posPart a = a)
    (hNeg : ∀ a b, B (negPart a) (negPart b) = 0)
    (hPos : ∀ a b, B (posPart a) (posPart b) = 0)
    (hZeroNeg : ∀ a b, B (zeroPart a) (negPart b) = 0)
    (hZeroPos : ∀ a b, B (zeroPart a) (posPart b) = 0)
    (a b : L) :
    B a b = B (negPart a) b + B a (negPart b) + B (zeroPart a) (zeroPart b) := by
  have left (c d : L) :
      B c d = B (negPart c) d + B (zeroPart c) d + B (posPart c) d := by
    rw [← B.add_left, ← B.add_left, hSplit]
  have right (c d : L) :
      B c d = B c (negPart d) + B c (zeroPart d) + B c (posPart d) := by
    rw [← B.add_right, ← B.add_right, hSplit]
  have hCross : B a (negPart b) = B (posPart a) (negPart b) := by
    rw [left a (negPart b), hNeg, hZeroNeg, zero_add, zero_add]
  have hZero : B (zeroPart a) b = B (zeroPart a) (zeroPart b) := by
    rw [right (zeroPart a) b, hZeroNeg, hZeroPos, zero_add, add_zero]
  have hPosCross : B (posPart a) b = B (posPart a) (negPart b) := by
    rw [right (posPart a) b, hSymm.eq (posPart a) (zeroPart b),
      hZeroPos, hPos, add_zero, add_zero]
  rw [left a b, hZero, hPosCross, hCross]
  abel

/-- The split bracket tested against two vectors. The four zero-part formulas are the
projected mixed brackets. The scalar is the pairing of the Cartan vectors attached to x,y. -/
theorem paired_split_bracket (B : LinearMap.BilinForm R L) (hSymm : B.IsSymm)
    (hInv : ∀ a b c : L, B ⁅a, b⁆ c = B a ⁅b, c⁆)
    (negPart zeroPart posPart : L →ₗ[R] L)
    (hSplit : ∀ a, negPart a + zeroPart a + posPart a = a)
    (hNeg : ∀ a b, B (negPart a) (negPart b) = 0)
    (hPos : ∀ a b, B (posPart a) (posPart b) = 0)
    (hZeroNeg : ∀ a b, B (zeroPart a) (negPart b) = 0)
    (hZeroPos : ∀ a b, B (zeroPart a) (posPart b) = 0)
    (x y u v hx hy : L) (k : R) (hCartan : B hx hy = k)
    (hxu : zeroPart ⁅x, u⁆ = B x u • hx) (hyv : zeroPart ⁅y, v⁆ = B y v • hy)
    (hyu : zeroPart ⁅y, u⁆ = B y u • hy) (hxv : zeroPart ⁅x, v⁆ = B x v • hx) :
    B ⁅x, y⁆ ⁅u, v⁆ =
      (B (negPart ⁅x, u⁆) ⁅y, v⁆ + B ⁅x, u⁆ (negPart ⁅y, v⁆)) -
      (B ⁅y, u⁆ (negPart ⁅x, v⁆) + B (negPart ⁅y, u⁆) ⁅x, v⁆) +
      k * (B x u * B y v - B x v * B y u) := by
  have expand :=
    pairing_eq_of_triangular B hSymm negPart zeroPart posPart hSplit hNeg hPos hZeroNeg hZeroPos
  rw [pairing_lie_lie B hInv, expand ⁅x, u⁆ ⁅y, v⁆, expand ⁅y, u⁆ ⁅x, v⁆]
  simp only [hxu, hyv, hyu, hxv, B.smul_left, B.smul_right, hSymm.eq hy hx, hCartan]
  ring

end D5.S3.VertexAlgebra.GradedLieSplitBracketIdentity

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge)
open RelativeCohomology (GradedCycles GradedCohomology ghostOne_eq_zero_of_nonzero_null)
open D5.S3.VertexAlgebra.GradedLieSplitBracketIdentity (paired_split_bracket)

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

local notation "Momentum" => Charge hyperbolicPlane
local notation "firstCoord" => (0 : Fin 2)
local notation "secondCoord" => (1 : Fin 2)
local notation "H" => fun p : Momentum => GradedCohomology planeFrame planeBasis p 1
local notation "incl" => DirectSum.lof ℂ Momentum H
local notation "B" => nativeRelativeBPZ

local instance splitBracketStateAddCommGroup : AddCommGroup ComplexState :=
  TensorProduct.addCommGroup
local instance splitBracketShellAddCommGroup (p : Momentum) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _
local instance splitBracketCyclesAddCommGroup (p : Momentum) :
    AddCommGroup (GradedCycles planeFrame planeBasis p 1) :=
  Submodule.addCommGroup _

/-- Keep the homogeneous summands selected by a predicate on native momenta. -/
def projectMomentum (keep : Momentum → Prop) : MomentumH1 →ₗ[ℂ] MomentumH1 := by
  classical
  exact DirectSum.toModule ℂ Momentum MomentumH1 fun p => if keep p then incl p else 0

private theorem projectMomentum_incl_of_mem (keep : Momentum → Prop) (p : Momentum)
    (a : H p) (hp : keep p) : projectMomentum keep (incl p a) = incl p a := by
  simp only [projectMomentum, DirectSum.toModule_lof, ite_eq_left hp]

private theorem projectMomentum_incl_of_not_mem (keep : Momentum → Prop) (p : Momentum)
    (a : H p) (hp : ¬ keep p) : projectMomentum keep (incl p a) = 0 := by
  simp only [projectMomentum, DirectSum.toModule_lof, ite_eq_right hp, LinearMap.zero_apply]

local notation "Negative" => (fun (p : Momentum) => p firstCoord < 0)
local notation "ZeroMomentum" => (fun (p : Momentum) => p = 0)
local notation "Positive" => (fun (p : Momentum) => 0 < p firstCoord)
local notation "negPart" => projectMomentum Negative
local notation "zeroPart" => projectMomentum ZeroMomentum
local notation "posPart" => projectMomentum Positive

private theorem projectMomentum_triangular (a : MomentumH1) :
    negPart a + zeroPart a + posPart a = a := by
  have h : negPart + zeroPart + posPart = (LinearMap.id : MomentumH1 →ₗ[ℂ] MomentumH1) := by
    apply DirectSum.linearMap_ext
    intro p
    apply LinearMap.ext
    intro x
    change negPart (incl p x) + zeroPart (incl p x) + posPart (incl p x) = incl p x
    rcases lt_trichotomy (p firstCoord) 0 with hp | hp | hp
    · have hn : p ≠ 0 := fun he => (ne_of_lt hp) (congrFun he firstCoord)
      rw [projectMomentum_incl_of_mem Negative p x hp,
        projectMomentum_incl_of_not_mem ZeroMomentum p x hn,
        projectMomentum_incl_of_not_mem Positive p x (not_lt_of_gt hp), add_zero, add_zero]
    · by_cases hz : p = 0
      · rw [projectMomentum_incl_of_not_mem Negative p x (not_lt_of_ge hp.ge),
          projectMomentum_incl_of_mem ZeroMomentum p x hz,
          projectMomentum_incl_of_not_mem Positive p x (not_lt_of_ge hp.le), zero_add, add_zero]
      · have hnull : p firstCoord * p secondCoord = 0 := by rw [hp, zero_mul]
        simp only [ghostOne_eq_zero_of_nonzero_null p hz hnull x, map_zero, add_zero]
    · have hn : p ≠ 0 := fun he => (ne_of_gt hp) (congrFun he firstCoord)
      rw [projectMomentum_incl_of_not_mem Negative p x (not_lt_of_gt hp),
        projectMomentum_incl_of_not_mem ZeroMomentum p x hn,
        projectMomentum_incl_of_mem Positive p x hp,
        zero_add, zero_add]
  exact LinearMap.congr_fun h a

private theorem nativeRelativeBPZ_projectMomentum_eq_zero (P Q : Momentum → Prop)
    (hOpp : ∀ p q, P p → Q q → q ≠ -p) (a b : MomentumH1) :
    B (projectMomentum P a) (projectMomentum Q b) = 0 := by
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | of p x =>
    change B (projectMomentum P (incl p x)) (projectMomentum Q b) = 0
    by_cases hp : P p
    · rw [projectMomentum_incl_of_mem P p x hp]
      induction b using DirectSum.induction_on with
      | zero => simp only [map_zero]
      | of q y =>
        change B (incl p x) (projectMomentum Q (incl q y)) = 0
        by_cases hq : Q q
        · rw [projectMomentum_incl_of_mem Q q y hq]
          exact nativeRelativeBPZ_momentum_selection p q x y (hOpp p q hp hq)
        · rw [projectMomentum_incl_of_not_mem Q q y hq, map_zero]
      | add b c hb hc => simp only [map_add, hb, hc, add_zero]
    · rw [projectMomentum_incl_of_not_mem P p x hp, map_zero, LinearMap.zero_apply]
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc, add_zero]

private theorem projectMomentum_zero_lie_incl (p q : Momentum) (x : H p) (y : H q) :
    zeroPart ⁅incl p x, incl q y⁆ =
      B (incl p x) (incl q y) • RealRootBracket.cartanClass (fun i => (p i : ℂ)) := by
  by_cases hqp : q = -p
  · subst q
    have hfix : zeroPart ⁅incl p x, incl (-p) y⁆ = ⁅incl p x, incl (-p) y⁆ := by
      obtain ⟨a, ha⟩ := lie_incl_neg_incl_mem_zero_momentum p x y
      rw [← ha, projectMomentum_incl_of_mem ZeroMomentum 0 a rfl]
    rw [hfix, lie_incl_neg_incl]
  · have hpq : p + q ≠ 0 := fun h => hqp (eq_neg_of_add_eq_zero_right h)
    change zeroPart (momentumBracket (incl p x) (incl q y)) = _
    rw [momentumBracket_incl, projectMomentum_incl_of_not_mem ZeroMomentum _ _ hpq,
      nativeRelativeBPZ_momentum_selection p q x y hqp, zero_smul]

/-- The native Cartan coefficient in the repository's ordered null coordinates. -/
def momentumCartanCoefficient (p q : Momentum) : ℂ :=
  (p firstCoord : ℂ) * (q secondCoord : ℂ) + (p secondCoord : ℂ) * (q firstCoord : ℂ)

/-- The BPZ coefficient of the split Jacobi identity on arbitrary homogeneous inputs.
In particular, the tests can be any vectors in negative momentum summands. -/
theorem nativeRelativeBPZ_split_bracket (p q r s : Momentum)
    (x : H p) (y : H q) (u : H r) (v : H s) :
    B ⁅incl p x, incl q y⁆ ⁅incl r u, incl s v⁆ =
      (B (negPart ⁅incl p x, incl r u⁆) ⁅incl q y, incl s v⁆ +
        B ⁅incl p x, incl r u⁆ (negPart ⁅incl q y, incl s v⁆)) -
      (B ⁅incl q y, incl r u⁆ (negPart ⁅incl p x, incl s v⁆) +
        B (negPart ⁅incl q y, incl r u⁆) ⁅incl p x, incl s v⁆) +
      momentumCartanCoefficient p q *
        (B (incl p x) (incl r u) * B (incl q y) (incl s v) -
          B (incl p x) (incl s v) * B (incl q y) (incl r u)) := by
  have hNeg : ∀ a b, B (negPart a) (negPart b) = 0 := by
    intro a b
    refine nativeRelativeBPZ_projectMomentum_eq_zero Negative Negative ?_ a b
    intro i j hi hj h
    change i firstCoord < 0 at hi
    change j firstCoord < 0 at hj
    have h0 : j firstCoord = -(i firstCoord) := congrFun h firstCoord
    omega
  have hPos : ∀ a b, B (posPart a) (posPart b) = 0 := by
    intro a b
    refine nativeRelativeBPZ_projectMomentum_eq_zero Positive Positive ?_ a b
    intro i j hi hj h
    change 0 < i firstCoord at hi
    change 0 < j firstCoord at hj
    have h0 : j firstCoord = -(i firstCoord) := congrFun h firstCoord
    omega
  have hZeroOpp (P : Momentum → Prop) (hP : ¬ P 0) (a b : MomentumH1) :
      B (zeroPart a) (projectMomentum P b) = 0 := by
    refine nativeRelativeBPZ_projectMomentum_eq_zero _ _ ?_ a b
    intro i j hi hj h
    change i = 0 at hi
    subst i
    rw [neg_zero] at h
    rw [h] at hj
    exact hP hj
  exact paired_split_bracket B nativeRelativeBPZ_symmetric nativeRelativeBPZ_invariant
    negPart zeroPart posPart projectMomentum_triangular hNeg hPos
    (hZeroOpp Negative (lt_irrefl (0 : ℤ))) (hZeroOpp Positive (lt_irrefl (0 : ℤ)))
    (incl p x) (incl q y) (incl r u) (incl s v)
    (RealRootBracket.cartanClass (fun i => (p i : ℂ)))
    (RealRootBracket.cartanClass (fun i => (q i : ℂ))) (momentumCartanCoefficient p q)
    (nativeRelativeBPZ_cartan _ _)
    (projectMomentum_zero_lie_incl p r x u) (projectMomentum_zero_lie_incl q s y v)
    (projectMomentum_zero_lie_incl q r y u) (projectMomentum_zero_lie_incl p s x v)

/-- The product BPZ functional on the tensor of the two testing slots. -/
def nativeBPZTensorCoefficient (x y : MomentumH1) :
    (MomentumH1 ⊗[ℂ] MomentumH1) →ₗ[ℂ] ℂ :=
  (LinearMap.mul' ℂ ℂ).comp (TensorProduct.map (B x) (B y))

/-- The paired bracket minus the two projected adjoint terms of the split identity. -/
def nativeSplitBracketDefect (x y : MomentumH1) :
    (MomentumH1 ⊗[ℂ] MomentumH1) →ₗ[ℂ] ℂ :=
  let ax := momentumBracket x
  let ay := momentumBracket y
  let pair := TensorProduct.lift B
  (B ⁅x, y⁆).comp (TensorProduct.lift momentumBracket) -
    ((pair.comp (TensorProduct.map (LinearMap.comp negPart ax) ay) +
        pair.comp (TensorProduct.map ax (LinearMap.comp negPart ay))) -
      (pair.comp (TensorProduct.map ay (LinearMap.comp negPart ax)) +
        pair.comp (TensorProduct.map (LinearMap.comp negPart ay) ax)))

private theorem momentumBracket_eq_lie (x y : MomentumH1) :
    momentumBracket x y = ⁅x, y⁆ := rfl

/-- The same identity as a linear map on a tensor of two homogeneous testing spaces. -/
theorem nativeRelativeBPZ_split_bracket_tensor_block (p q r s : Momentum) (x : H p) (y : H q) :
    (nativeSplitBracketDefect (incl p x) (incl q y)).comp
        (TensorProduct.map (incl r) (incl s)) =
      (momentumCartanCoefficient p q •
        (nativeBPZTensorCoefficient (incl p x) (incl q y) -
          nativeBPZTensorCoefficient (incl q y) (incl p x))).comp
        (TensorProduct.map (incl r) (incl s)) := by
  apply TensorProduct.ext'
  intro u v
  simp only [nativeSplitBracketDefect, nativeBPZTensorCoefficient, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, TensorProduct.map_tmul,
    TensorProduct.lift.tmul, LinearMap.mul'_apply, smul_eq_mul, momentumBracket_eq_lie]
  rw [nativeRelativeBPZ_split_bracket p q r s x y u v]
  ring

/-- The coefficient of the dual negative bracket vanishes in first coordinate one. -/
theorem nativeRelativeBPZ_lie_eq_zero_of_first_coordinate_one (p r s : Momentum)
    (hp : p firstCoord = 1) (hr : r firstCoord < 0) (hs : s firstCoord < 0) (x : H p) (u : H r) (v : H s) :
    B (incl p x) ⁅incl r u, incl s v⁆ = 0 := by
  change B (incl p x) (momentumBracket (incl r u) (incl s v)) = 0
  rw [momentumBracket_incl]
  refine nativeRelativeBPZ_momentum_selection p (r + s) x (bracket r s u v) ?_
  intro h
  have h0 : r firstCoord + s firstCoord = -(p firstCoord) := congrFun h firstCoord
  omega

private theorem projectMomentum_conjugation (P : Momentum → Prop) (a : MomentumH1) :
    coefficientConjugationMomentum (projectMomentum P a) =
      projectMomentum P (coefficientConjugationMomentum a) := by
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of p x =>
    change coefficientConjugationMomentum (projectMomentum P (incl p x)) =
      projectMomentum P (coefficientConjugationMomentum (incl p x))
    rw [coefficientConjugationMomentum_incl]
    by_cases hp : P p
    · rw [projectMomentum_incl_of_mem P p x hp,
        projectMomentum_incl_of_mem P p (coefficientConjugationCohomology p x) hp,
        coefficientConjugationMomentum_incl]
    · rw [projectMomentum_incl_of_not_mem P p x hp,
        projectMomentum_incl_of_not_mem P p (coefficientConjugationCohomology p x) hp, map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The first-coordinate negative projection on the fixed real Lie algebra. -/
def projectNegativeMomentumReal : momentumRealLie →ₗ[ℝ] momentumRealLie where
  toFun x := ⟨negPart (momentumRealValue x), by
    change coefficientConjugationMomentum (negPart (momentumRealValue x)) =
      negPart (momentumRealValue x)
    rw [projectMomentum_conjugation, momentumConjugation_realValue]⟩
  map_add' x y := by
    apply Subtype.ext
    change negPart (momentumRealValue x + momentumRealValue y) =
      negPart (momentumRealValue x) + negPart (momentumRealValue y)
    exact LinearMap.map_add negPart _ _
  map_smul' c x := by
    apply Subtype.ext
    change negPart ((c : ℂ) • momentumRealValue x) = (c : ℂ) • negPart (momentumRealValue x)
    exact LinearMap.map_smul negPart _ _

private theorem momentumRealValue_projectNegative (x : momentumRealLie) :
    momentumRealValue (projectNegativeMomentumReal x) = negPart (momentumRealValue x) := rfl

private theorem momentumRealValue_lie (x y : momentumRealLie) :
    momentumRealValue ⁅x, y⁆ = ⁅momentumRealValue x, momentumRealValue y⁆ := rfl

/-- The actual real BPZ coefficient identity. The inclusions in the hypotheses are the
native momentum witnesses supplied by membership in the corresponding real weight spaces. -/
theorem momentumRealBPZ_split_bracket (p q r s : Momentum)
    (x y u v : momentumRealLie) (a : H p) (b : H q) (c : H r) (d : H s)
    (hx : momentumRealValue x = incl p a) (hy : momentumRealValue y = incl q b)
    (hu : momentumRealValue u = incl r c) (hv : momentumRealValue v = incl s d) :
    momentumRealBPZ ⁅x, y⁆ ⁅u, v⁆ =
      (momentumRealBPZ (projectNegativeMomentumReal ⁅x, u⁆) ⁅y, v⁆ +
        momentumRealBPZ ⁅x, u⁆ (projectNegativeMomentumReal ⁅y, v⁆)) -
      (momentumRealBPZ ⁅y, u⁆ (projectNegativeMomentumReal ⁅x, v⁆) +
        momentumRealBPZ (projectNegativeMomentumReal ⁅y, u⁆) ⁅x, v⁆) +
      ((p firstCoord : ℝ) * (q secondCoord : ℝ) + (p secondCoord : ℝ) * (q firstCoord : ℝ)) *
        (momentumRealBPZ x u * momentumRealBPZ y v - momentumRealBPZ x v * momentumRealBPZ y u) := by
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_intCast,
    ofReal_momentumRealBPZ, momentumRealValue_projectNegative, momentumRealValue_lie,
    hx, hy, hu, hv, momentumCartanCoefficient] using nativeRelativeBPZ_split_bracket p q r s a b c d

end

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
