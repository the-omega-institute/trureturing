/- GID: D5/S3/Quantum/Algebra/UnitBridgeLocalization
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/UnitBridgeLocalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Module.LocalizedModule.Basic]
   utility: kind=none
   digest: Square-denominator localization of the same original total relation. -/

import D5.S3.Quantum.Algebra.UnitBridgeRawGeometry
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Evaluation localization with zero-divisor saturation and no linearity assumption on D. -/

noncomputable section

namespace D5.S3.Quantum.Algebra.UnitBridgeRawGeometry

variable {T : Type*} [TopologicalSpace T] {E : Original T}

/-- A central coefficient is an actual original input. -/
def centralInput (E : Original T) (f : scalarAlgebra E) : E.Elem :=
  ⟨central f.val, f.property⟩

/-- Multiplication by a coefficient uses the known original Jordan product. -/
def coefficientScale (f : scalarAlgebra E) (a : E.Elem) : E.Elem :=
  E.product (centralInput E f) a

/-- The source CS assumption on the same original total D. -/
def SquareCompatible (R : Raw E) : Prop :=
  ∀ (f : scalarAlgebra E) (a b : E.Elem),
    R.D a (coefficientScale (f^2) b) = coefficientScale (f^2) (R.D a b)

private theorem input_scale (f : scalarAlgebra E) (x : Vectors E) :
    vectorInput E (f • x) = coefficientScale f (vectorInput E x) := by
  apply Subtype.ext
  ext i t
  fin_cases i <;> simp [vectorInput, coefficientScale, centralInput, Original.product,
    jordan, central]

private theorem K_square_right (R : Raw E) (cs : SquareCompatible R)
    (f : scalarAlgebra E) (x y : Vectors E) :
    K R x ((f^2) • y) = (f^2) • K R x y := by
  have h := cs f (vectorInput E x) (vectorInput E y)
  rw [← input_scale] at h
  funext i
  apply Subtype.ext
  ext t
  have hi := congrArg (fun z : E.Elem => z.val i.succ t) h
  fin_cases i <;> simpa [K, coefficientScale, centralInput, Original.product,
    jordan, central] using hi

private theorem K_skew (R : Raw E) (x y : Vectors E) : K R x y = -K R y x := by
  funext i
  apply Subtype.ext
  exact congrArg (fun z : E.Elem => z.val i.succ) (R.skew _ _)

private theorem K_square_left (R : Raw E) (cs : SquareCompatible R)
    (f : scalarAlgebra E) (x y : Vectors E) :
    K R ((f^2) • x) y = (f^2) • K R x y := by
  rw [K_skew, K_square_right R cs, ← smul_neg, ← K_skew]

private theorem saturated_left (R : Raw E) (cs : SquareCompatible R)
    (u s s' : scalarAlgebra E) (x x' y : Vectors E)
    (h : u • s' • x = u • s • x') :
    (u*s')^2 • K R (s • x) y = (u*s)^2 • K R (s' • x') y := by
  have he : (u*s')^2 • (s • x) = (u*s)^2 • (s' • x') := by
    have hh := congrArg (fun z : Vectors E => (u*s*s') • z) h
    simpa only [smul_smul, pow_two, mul_assoc, mul_comm, mul_left_comm] using hh
  have hk := congrArg (fun z => K R z y) he
  simpa only [K_square_left R cs] using hk

private theorem saturated_right (R : Raw E) (cs : SquareCompatible R)
    (u s s' : scalarAlgebra E) (x x' y : Vectors E)
    (h : u • s' • x = u • s • x') :
    (u*s')^2 • K R y (s • x) = (u*s)^2 • K R y (s' • x') := by
  have he : (u*s')^2 • (s • x) = (u*s)^2 • (s' • x') := by
    have hh := congrArg (fun z : Vectors E => (u*s*s') • z) h
    simpa only [smul_smul, pow_two, mul_assoc, mul_comm, mul_left_comm] using hh
  have hk := congrArg (fun z => K R y z) he
  simpa only [K_square_right R cs] using hk

/-- The actual multiplicative set of coefficients nonzero at the specified point. -/
def evaluationDenominators (E : Original T) (t : T) : Submonoid (scalarAlgebra E) where
  carrier := {f | f.val t ≠ 0}
  one_mem' := by simp
  mul_mem' := by intro f g hf hg; exact mul_ne_zero hf hg

/-- Native module localization of the actual coefficient module. -/
abbrev LocalVectors (E : Original T) (t : T) :=
  LocalizedModule (evaluationDenominators E t) (Vectors E)

/-- The ordinary scalar ring localization, retaining zero-divisor saturation. -/
abbrev LocalScalars (E : Original T) (t : T) := Localization (evaluationDenominators E t)

/-- The ordinary scalar localization acts on the ordinary module localization. -/
instance localVectorsModule (E : Original T) (t : T) :
    Module (LocalScalars E t) (LocalVectors E t) :=
  LocalizedModule.moduleOfIsLocalization _

/-- Evaluation on the actual coefficient algebra. -/
def coefficientEvaluation (E : Original T) (t : T) : scalarAlgebra E →+* ℝ where
  toFun f := f.val t
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Evaluation on ordinary scalar fractions. -/
def localEvaluation (E : Original T) (t : T) : LocalScalars E t →+* ℝ :=
  IsLocalization.lift (M := evaluationDenominators E t) (g := coefficientEvaluation E t)
    (fun s => isUnit_iff_ne_zero.mpr s.property)

instance localScalarsLocalRing (E : Original T) (t : T) : IsLocalRing (LocalScalars E t) := by
  let P := RingHom.ker (coefficientEvaluation E t)
  letI : P.IsPrime := RingHom.ker_isPrime _
  have hs : evaluationDenominators E t = P.primeCompl := by rfl
  letI : IsLocalization.AtPrime (LocalScalars E t) P := by
    change IsLocalization P.primeCompl (LocalScalars E t)
    rw [← hs]
    infer_instance
  exact IsLocalization.AtPrime.isLocalRing _ P

/-- Actual coordinates in the localized coefficient ring, not a point fibre quotient. -/
def localCoordinates (t : T) (z : LocalVectors E t) : Fin 3 → LocalScalars E t :=
  LocalizedModule.liftOn z (fun p i => Localization.mk (p.1 i) p.2) (by
    intro p q h
    obtain ⟨u, hu⟩ := h
    funext i
    apply Localization.mk_eq_mk_iff.mpr
    rw [Localization.r_iff_exists]
    refine ⟨u, ?_⟩
    simpa only [Submonoid.smul_def, Pi.smul_apply, smul_eq_mul, mul_assoc,
      mul_comm, mul_left_comm] using congrFun hu i)

/-- The dot product over the actual local scalar ring. -/
def localDot (t : T) (x y : LocalVectors E t) : LocalScalars E t :=
  dotProduct (localCoordinates t x) (localCoordinates t y)

/-- The localized H row uses its actual local scalar dot product. -/
def localH (t : T) (x y : LocalVectors E t) : LocalVectors E t :=
  localDot t x y • x - localDot t x x • y

private theorem local_mk_add (t : T) (x y : Vectors E)
    (s : evaluationDenominators E t) :
    (LocalizedModule.mk x s : LocalVectors E t) + LocalizedModule.mk y s =
      LocalizedModule.mk (x+y) s := by
  rw [LocalizedModule.mk_add_mk]
  simpa only [smul_add, Submonoid.smul_def] using
    LocalizedModule.mk_cancel_common_left s s (x+y)

private theorem local_mk_sub (t : T) (x y : Vectors E)
    (s : evaluationDenominators E t) :
    (LocalizedModule.mk x s : LocalVectors E t) - LocalizedModule.mk y s =
      LocalizedModule.mk (x-y) s := by
  rw [sub_eq_add_neg, ← LocalizedModule.mk_neg, local_mk_add, ← sub_eq_add_neg]

private theorem localDot_mk (t : T) (x y : Vectors E)
    (s r : evaluationDenominators E t) :
    localDot t (LocalizedModule.mk x s) (LocalizedModule.mk y r) =
      Localization.mk (dotProduct x y) (s*r) := by
  simp only [localDot, localCoordinates, LocalizedModule.liftOn_mk, dotProduct,
    Localization.mk_mul, ← Localization.mk_sum]

private theorem localH_mk (t : T) (x y : Vectors E)
    (s r : evaluationDenominators E t) :
    localH t (LocalizedModule.mk x s) (LocalizedModule.mk y r) =
      LocalizedModule.mk ((dotProduct x y) • x - (dotProduct x x) • y) (s^2*r) := by
  simp only [localH, localDot_mk, Localization.mk_eq_mk', LocalizedModule.mk'_smul_mk]
  have hd : (s*r)*s = (s*s)*r := by ac_rfl
  rw [hd, local_mk_sub, pow_two]

private theorem scalar_localization (t : T) :
    Function.Surjective (coefficientEvaluation E t) ∧
    Function.Surjective (localEvaluation E t) ∧
    (∀ (f : scalarAlgebra E) (s : evaluationDenominators E t),
      localEvaluation E t (Localization.mk f s) = f.val t / s.val.val t ∧
      (IsUnit (Localization.mk f s) ↔ f.val t ≠ 0) ∧
      ∀ hf : f.val t ≠ 0,
        (Localization.mk f s : LocalScalars E t) * Localization.mk s.val ⟨f,hf⟩ = 1) ∧
    RingHom.ker (localEvaluation E t) = IsLocalRing.maximalIdeal (LocalScalars E t) ∧
    Nonempty (IsLocalRing.ResidueField (LocalScalars E t) ≃+* ℝ) := by
  have he : Function.Surjective (coefficientEvaluation E t) := by
    intro r
    exact ⟨algebraMap ℝ (scalarAlgebra E) r, rfl⟩
  have hl : Function.Surjective (localEvaluation E t) := by
    intro r
    obtain ⟨f,hf⟩ := he r
    refine ⟨algebraMap (scalarAlgebra E) (LocalScalars E t) f, ?_⟩
    simpa only [localEvaluation, IsLocalization.lift_eq] using hf
  have hk : RingHom.ker (localEvaluation E t) =
      IsLocalRing.maximalIdeal (LocalScalars E t) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hl)
  refine ⟨he, hl, ?_, hk, ?_⟩
  · intro f s
    have hv : localEvaluation E t (Localization.mk f s) = f.val t / s.val.val t := by
      rw [Localization.mk_eq_mk']
      apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
      change f.val t = s.val.val t * (f.val t / s.val.val t)
      have hs0 : s.val.val t ≠ 0 := s.property
      field_simp [hs0]
    refine ⟨hv, ?_, ?_⟩
    · let P := RingHom.ker (coefficientEvaluation E t)
      letI : P.IsPrime := RingHom.ker_isPrime _
      have hs : evaluationDenominators E t = P.primeCompl := rfl
      letI : IsLocalization.AtPrime (LocalScalars E t) P := by
        change IsLocalization P.primeCompl (LocalScalars E t)
        rw [← hs]
        infer_instance
      simpa [Localization.mk_eq_mk', P, Ideal.mem_primeCompl_iff,
        RingHom.mem_ker, coefficientEvaluation] using
        (IsLocalization.AtPrime.isUnit_mk'_iff (LocalScalars E t) P f
          (⟨s.val,s.property⟩ : P.primeCompl))
    · intro hf
      simpa only [Localization.mk_eq_mk'] using
        (IsLocalization.mk'_mul_mk'_eq_one (S := LocalScalars E t)
          (⟨f,hf⟩ : evaluationDenominators E t) s)
  · change Nonempty ((LocalScalars E t ⧸ IsLocalRing.maximalIdeal (LocalScalars E t)) ≃+* ℝ)
    rw [← hk]
    exact ⟨RingHom.quotientKerEquivOfSurjective hl⟩

private def representative (R : Raw E) (t : T)
    (p q : Vectors E × evaluationDenominators E t) : LocalVectors E t :=
  LocalizedModule.mk (K R (p.2.val • p.1) (q.2.val • q.1)) (p.2^2*q.2^2)

private theorem representative_left (R : Raw E) (cs : SquareCompatible R) (t : T)
    (p p' q : Vectors E × evaluationDenominators E t)
    (h : LocalizedModule.r (evaluationDenominators E t) (Vectors E) p p') :
    representative R t p q = representative R t p' q := by
  obtain ⟨u, hu⟩ := h
  apply LocalizedModule.mk_eq.mpr
  refine ⟨u^2, ?_⟩
  have hk := saturated_left R cs u.val p.2.val p'.2.val p.1 p'.1
    (q.2.val • q.1) (by simpa only [Submonoid.smul_def] using hu)
  have hh := congrArg (fun z : Vectors E => q.2.val^2 • z) hk
  simpa only [Submonoid.smul_def, Submonoid.coe_mul, SubmonoidClass.coe_pow,
    smul_smul, pow_two, mul_assoc, mul_comm, mul_left_comm] using hh

private theorem representative_right (R : Raw E) (cs : SquareCompatible R) (t : T)
    (p q q' : Vectors E × evaluationDenominators E t)
    (h : LocalizedModule.r (evaluationDenominators E t) (Vectors E) q q') :
    representative R t p q = representative R t p q' := by
  obtain ⟨u, hu⟩ := h
  apply LocalizedModule.mk_eq.mpr
  refine ⟨u^2, ?_⟩
  have hk := saturated_right R cs u.val q.2.val q'.2.val q.1 q'.1
    (p.2.val • p.1) (by simpa only [Submonoid.smul_def] using hu)
  have hh := congrArg (fun z : Vectors E => p.2.val^2 • z) hk
  simpa only [Submonoid.smul_def, Submonoid.coe_mul, SubmonoidClass.coe_pow,
    smul_smul, pow_two, mul_assoc, mul_comm, mul_left_comm] using hh

/-- The nonlinear localized map is constructed from the original D and source CS. -/
def localizedK (R : Raw E) (cs : SquareCompatible R) (t : T)
    (x y : LocalVectors E t) : LocalVectors E t :=
  LocalizedModule.liftOn₂ x y (representative R t) (by
    intro p q p' q' hp hq
    exact (representative_left R cs t p p' q hp).trans
      (representative_right R cs t p' q q' hq))

private theorem localizedK_mk (R : Raw E) (cs : SquareCompatible R) (t : T)
    (x y : Vectors E) (s r : evaluationDenominators E t) :
    localizedK R cs t (LocalizedModule.mk x s) (LocalizedModule.mk y r) =
      representative R t (x,s) (y,r) := by
  simp only [localizedK, LocalizedModule.liftOn₂_mk]

private theorem localizedK_square (R : Raw E) (cs : SquareCompatible R) (t : T)
    (x y : Vectors E) (s r : evaluationDenominators E t) :
    localizedK R cs t (LocalizedModule.mk x (s^2)) (LocalizedModule.mk y (r^2)) =
      LocalizedModule.mk (K R x y) (s^2*r^2) := by
  rw [localizedK_mk]
  change LocalizedModule.mk (K R ((s^2).val • x) ((r^2).val • y)) _ = _
  simp only [SubmonoidClass.coe_pow, K_square_left R cs, K_square_right R cs]
  apply LocalizedModule.mk_eq.mpr
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, SubmonoidClass.coe_pow, smul_smul]
  congr 1
  ring

private theorem localizedK_nested (R : Raw E) (cs : SquareCompatible R) (t : T)
    (x y : Vectors E) (s r : evaluationDenominators E t) :
    localizedK R cs t (LocalizedModule.mk x (s^2))
      (localizedK R cs t (LocalizedModule.mk x (s^2)) (LocalizedModule.mk y (r^2))) =
      LocalizedModule.mk ((dotProduct x y) • x - (dotProduct x x) • y) (s^4*r^2) := by
  rw [localizedK_square]
  have hd : s^2*r^2 = (s*r)^2 := (mul_pow s r 2).symm
  rw [hd, localizedK_square, raw_K_nested]
  congr 1
  simp [mul_pow, pow_succ, mul_assoc, mul_left_comm, mul_comm]

private theorem localizedK_kernel (R : Raw E) (cs : SquareCompatible R) (t : T)
    (x y c : Vectors E) (q : evaluationDenominators E t)
    (h : LocalizedModule.mk ((dotProduct x c) • x - (dotProduct x x) • c) (q^6) =
      (0 : LocalVectors E t)) :
    localizedK R cs t (LocalizedModule.mk x (q^2)) (LocalizedModule.mk (y+c) (q^2)) =
      localizedK R cs t (LocalizedModule.mk x (q^2)) (LocalizedModule.mk y (q^2)) := by
  rw [← LocalizedModule.zero_mk (1 : evaluationDenominators E t),
    LocalizedModule.mk_eq] at h
  obtain ⟨u, hu⟩ := h
  have hu0 : u.val • ((dotProduct x c) • x - (dotProduct x x) • c) = 0 := by
    simpa only [one_smul, smul_zero, Submonoid.smul_def] using hu
  have hs : (dotProduct x ((u.val^2) • c)) • x -
      (dotProduct x x) • ((u.val^2) • c) = 0 := by
    have hh := congrArg (fun z : Vectors E => u.val • z) hu0
    funext i
    have hi := congrFun hh i
    simp [dotProduct, Fin.sum_univ_succ, pow_two] at hi ⊢
    linear_combination hi
  have hk := raw_K_kernel_translation R x ((u.val^2) • y) ((u.val^2) • c) hs
  rw [← smul_add, K_square_right R cs, K_square_right R cs] at hk
  rw [localizedK_square, localizedK_square]
  apply LocalizedModule.mk_eq.mpr
  refine ⟨u^2, ?_⟩
  have hh := congrArg (fun z : Vectors E => (q.val^2*q.val^2) • z) hk
  simpa only [Submonoid.smul_def, Submonoid.coe_mul, SubmonoidClass.coe_pow,
    smul_smul, mul_assoc, mul_comm, mul_left_comm] using hh

private theorem square_representation (t : T) (z : LocalVectors E t) :
    ∃ (x : Vectors E) (s : evaluationDenominators E t),
      z = LocalizedModule.mk x (s^2) := by
  induction z using LocalizedModule.induction_on with
  | h x s =>
    exact ⟨s.val • x, s, by
      simpa only [pow_two, Submonoid.smul_def] using
        (LocalizedModule.mk_cancel_common_left s s x).symm⟩

private theorem common_square_representation (t : T) (a b c : LocalVectors E t) :
    ∃ (x y z : Vectors E) (q : evaluationDenominators E t),
      a = LocalizedModule.mk x (q^2) ∧ b = LocalizedModule.mk y (q^2) ∧
      c = LocalizedModule.mk z (q^2) := by
  obtain ⟨x,s,rfl⟩ := square_representation t a
  obtain ⟨y,r,rfl⟩ := square_representation t b
  obtain ⟨z,v,rfl⟩ := square_representation t c
  refine ⟨((r*v)^2).val • x, ((s*v)^2).val • y, ((s*r)^2).val • z, s*r*v, ?_, ?_, ?_⟩
  all_goals
    apply LocalizedModule.mk_eq.mpr
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul,
      SubmonoidClass.coe_pow, smul_smul]
    congr 1
    ring

private theorem localizedK_skew (R : Raw E) (cs : SquareCompatible R) (t : T)
    (a b : LocalVectors E t) : localizedK R cs t a b = -localizedK R cs t b a := by
  obtain ⟨x,s,rfl⟩ := square_representation t a
  obtain ⟨y,r,rfl⟩ := square_representation t b
  rw [localizedK_square, localizedK_square, K_skew, LocalizedModule.mk_neg, mul_comm (r^2)]

private theorem localizedK_real (R : Raw E) (cs : SquareCompatible R) (t : T)
    (a b : LocalVectors E t) (c : ℝ) :
    localizedK R cs t a (c • b) = c • localizedK R cs t a b ∧
    localizedK R cs t (c • a) b = c • localizedK R cs t a b := by
  obtain ⟨x,s,rfl⟩ := square_representation t a
  obtain ⟨y,r,rfl⟩ := square_representation t b
  simp only [LocalizedModule.smul'_mk, localizedK_square,
    (raw_K_geometry R x y).2.2.2 c]
  trivial

private theorem localizedK_geometry (R : Raw E) (cs : SquareCompatible R) (t : T)
    (a b : LocalVectors E t) :
    localDot t (localizedK R cs t a b) a = 0 ∧
    localDot t (localizedK R cs t a b) b = 0 ∧
    localDot t (localizedK R cs t a b) (localizedK R cs t a b) =
      localDot t a a * localDot t b b - localDot t a b ^ 2 := by
  obtain ⟨x,y,z,q,ha,hb,hc⟩ := common_square_representation t a b 0
  rw [ha,hb,localizedK_square]
  have hg := raw_K_geometry R x y
  refine ⟨?_,?_,?_⟩
  · rw [localDot_mk,hg.1,Localization.mk_zero]
  · rw [localDot_mk,hg.2.1,Localization.mk_zero]
  · simp only [localDot_mk]
    rw [hg.2.2.1,cross_dot_cross,dotProduct_comm y x]
    simp only [pow_two, Localization.mk_mul]
    rw [sub_eq_add_neg, Localization.neg_mk, Localization.add_mk_self]
    rfl

private theorem localizedK_NN (R : Raw E) (cs : SquareCompatible R) (t : T)
    (a b : LocalVectors E t) :
    localizedK R cs t a (localizedK R cs t a b) = localH t a b := by
  obtain ⟨x,s,rfl⟩ := square_representation t a
  obtain ⟨y,r,rfl⟩ := square_representation t b
  rw [localizedK_nested,localH_mk]
  congr 1
  simp [← pow_mul]

private theorem localizedK_kernel_total (R : Raw E) (cs : SquareCompatible R) (t : T)
    (a b c : LocalVectors E t) (h : localH t a c = 0) :
    localizedK R cs t a (b+c) = localizedK R cs t a b ∧
    localizedK R cs t (b+c) a = localizedK R cs t b a := by
  have right : localizedK R cs t a (b+c) = localizedK R cs t a b := by
    obtain ⟨x,y,z,q,ha,hb,hc⟩ := common_square_representation t a b c
    rw [ha,hc,localH_mk] at h
    have hq : (q^2)^2*q^2 = q^6 := by simp [← pow_mul, ← pow_add]
    rw [hq] at h
    rw [ha,hb,hc,local_mk_add]
    exact localizedK_kernel R cs t x y z q h
  refine ⟨right, ?_⟩
  rw [localizedK_skew R cs t (b+c) a, right, ← localizedK_skew]

/-- Complete original-to-local extension: ordinary local scalar algebra and residue,
nonlinear square formula, skewness, real homogeneity, dot/area, NN and kernel translation. -/
theorem original_localization (R : Raw E) (cs : SquareCompatible R) (t : T) :
    ∃ k : LocalVectors E t → LocalVectors E t → LocalVectors E t,
      (∀ (x y : Vectors E) (s r : evaluationDenominators E t),
        k (LocalizedModule.mk x (s^2)) (LocalizedModule.mk y (r^2)) =
          LocalizedModule.mk (K R x y) (s^2*r^2)) ∧
      (∀ (x y : Vectors E) (s r : evaluationDenominators E t),
        k (LocalizedModule.mk x (s^2))
          (k (LocalizedModule.mk x (s^2)) (LocalizedModule.mk y (r^2))) =
          LocalizedModule.mk ((dotProduct x y) • x - (dotProduct x x) • y) (s^4*r^2)) ∧
      (∀ (x y c : Vectors E) (q : evaluationDenominators E t),
        LocalizedModule.mk ((dotProduct x c) • x - (dotProduct x x) • c) (q^6) =
          (0 : LocalVectors E t) →
        k (LocalizedModule.mk x (q^2)) (LocalizedModule.mk (y+c) (q^2)) =
          k (LocalizedModule.mk x (q^2)) (LocalizedModule.mk y (q^2))) ∧
      (∀ a b c : LocalVectors E t,
        ∃ (x y z : Vectors E) (q : evaluationDenominators E t),
          a = LocalizedModule.mk x (q^2) ∧ b = LocalizedModule.mk y (q^2) ∧
          c = LocalizedModule.mk z (q^2)) ∧
      Function.Surjective (coefficientEvaluation E t) ∧
      Function.Surjective (localEvaluation E t) ∧
      (∀ (f : scalarAlgebra E) (s : evaluationDenominators E t),
        localEvaluation E t (Localization.mk f s) = f.val t / s.val.val t ∧
        (IsUnit (Localization.mk f s) ↔ f.val t ≠ 0) ∧
        ∀ hf : f.val t ≠ 0,
          (Localization.mk f s : LocalScalars E t) * Localization.mk s.val ⟨f,hf⟩ = 1) ∧
      RingHom.ker (localEvaluation E t) = IsLocalRing.maximalIdeal (LocalScalars E t) ∧
      Nonempty (IsLocalRing.ResidueField (LocalScalars E t) ≃+* ℝ) ∧
      (∀ a b, k a b = -k b a) ∧
      (∀ a b (r : ℝ), k a (r • b) = r • k a b ∧ k (r • a) b = r • k a b) ∧
      (∀ a b, localDot t (k a b) a = 0 ∧ localDot t (k a b) b = 0 ∧
        localDot t (k a b) (k a b) = localDot t a a * localDot t b b - localDot t a b ^ 2) ∧
      (∀ a b, k a (k a b) = localH t a b) ∧
      (∀ a b c, localH t a c = 0 → k a (b+c) = k a b ∧ k (b+c) a = k b a) := by
  obtain ⟨he,hl,hf,hker,hres⟩ := scalar_localization (E := E) t
  exact ⟨localizedK R cs t, localizedK_square R cs t,
    localizedK_nested R cs t, localizedK_kernel R cs t, common_square_representation t,
    he, hl, hf, hker, hres, localizedK_skew R cs t, localizedK_real R cs t,
    localizedK_geometry R cs t, localizedK_NN R cs t, localizedK_kernel_total R cs t⟩

end D5.S3.Quantum.Algebra.UnitBridgeRawGeometry
