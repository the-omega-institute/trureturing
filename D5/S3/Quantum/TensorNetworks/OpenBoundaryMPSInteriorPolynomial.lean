/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorPolynomial
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorPolynomial
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.PDeriv]
   utility: none
   digest: Independent-trial actual interior polynomials and all-length nonzero Jacobian. -/

import D5.S3.Quantum.TensorNetworks.InteriorPolynomialClearance
import D5.S3.Quantum.TensorNetworks.InteriorPolynomialRealCalculus
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversality

/-! The target coordinates and independent trial coordinates have distinct roles. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial

open Matrix MvPolynomial
open scoped Matrix ComplexOrder BigOperators
open PeriodicMPSParentIntersection (Bond Word)
open OpenBoundaryMPSMarginalBirationality (mpsState openBoundaryMPS)
open OpenBoundaryMPSInteriorRootRealization
open OpenBoundaryMPSDensityRecovery (transfer)
open OpenBoundaryMPSInteriorCommonCore (dualTransfer rawInterior)
open OpenBoundaryMPSQuotient (polynomialConjugate polynomialConjugate_eval)
open InteriorPolynomialClearance InteriorPolynomialRealCalculus
open D5.S3.Quantum.Algebra
open OpenBoundaryMPSDensityGenericity (realCoeff coefficient_eval realCoordinates)

abbrev ComplexPoly := PhasePolynomial.Poly (Fin 9)
abbrev RealPoly := MvPolynomial (Fin 2 ⊕ Fin 16) ℝ
abbrev TargetPoly := MvPolynomial (Fin 16) ℝ
abbrev PolyBond := Matrix (Fin 2) (Fin 2) ComplexPoly

def coordinate (i : Fin 9) : ComplexPoly := X (Sum.inl i)
def adjoint (M : PolyBond) : PolyBond := fun i j => polynomialConjugate (M j i)
def gPolynomial (z : ComplexPoly) : PolyBond :=
  !![1,z;coordinate 0-coordinate 2,(coordinate 1-coordinate 2)*z]
def bPolynomial : PolyBond := diagonal ![coordinate 0,coordinate 1]
def corePolynomial : Fin 2 → PolyBond :=
  ![gPolynomial (coordinate 7), bPolynomial*gPolynomial (coordinate 7)]
def jPolynomial : PolyBond :=
  adjugateTwo (coordinate 0-coordinate 2) (coordinate 1-coordinate 2) (coordinate 8)
def wPolynomial : PolyBond :=
  schurWeights (coordinate 0) (coordinate 1)
    (polynomialConjugate (coordinate 0)) (polynomialConjugate (coordinate 1))

def targetLeftPolynomial (p : ℕ) : PolyBond :=
  (fun M => ∑ i : Fin 2, adjoint (corePolynomial i)*M*corePolynomial i)^[p]
    (vecMulVec (fun i => polynomialConjugate (![coordinate 3,coordinate 4] i))
      ![coordinate 3,coordinate 4])
def targetRightInnerPolynomial (q : ℕ) : PolyBond :=
  (fun M => ∑ i : Fin 2, corePolynomial i*M*adjoint (corePolynomial i))^[q]
    (vecMulVec ![coordinate 5,coordinate 6]
      (fun i => polynomialConjugate (![coordinate 5,coordinate 6] i)))
def targetRightPolynomial (q : ℕ) : PolyBond :=
  gPolynomial (coordinate 7)^2 * targetRightInnerPolynomial q *
    adjoint (gPolynomial (coordinate 7)^2)
def clearedLeftPolynomial (p : ℕ) : PolyBond :=
  (fun M => fun i j => wPolynomial j i * (adjoint jPolynomial*M*jPolynomial) i j)^[p]
    (targetLeftPolynomial p)
def clearedRightPolynomial (q : ℕ) : PolyBond :=
  (fun M => jPolynomial*(wPolynomial ⊙ M)*adjoint jPolynomial)^[q]
    (jPolynomial^2 * targetRightPolynomial q * adjoint (jPolynomial^2))

/-- Trial x,y precede the sixteen actual sector, boundary and target coordinates. -/
def cartIndex : Fin 9 ⊕ Fin 9 → Fin 2 ⊕ Fin 16 :=
  Sum.elim (fun i => if h : i.val < 8 then Sum.inr ⟨2*i.val,by omega⟩ else Sum.inl 0)
    (fun i => if h : i.val < 8 then Sum.inr ⟨2*i.val+1,by omega⟩ else Sum.inl 1)
def realify (P : ComplexPoly) : RealPoly :=
  rename cartIndex (realCoeff (PhasePolynomial.toCartesian P))
def FL (p q : ℕ) : RealPoly := realify (clearedLeftPolynomial p).det
def FR (p q : ℕ) : RealPoly := realify (clearedRightPolynomial q).det

def coordinates (s : Sector) (l r : Fin 2 → ℂ) (z₀ : ℂ) : Fin 16 → ℝ :=
  ![s.lambda.re,s.lambda.im,s.mu.re,s.mu.im,s.a.re,s.a.im,
    (l 0).re,(l 0).im,(l 1).re,(l 1).im,(r 0).re,(r 0).im,(r 1).re,(r 1).im,z₀.re,z₀.im]
def actualVariables (s : Sector) (l r : Fin 2 → ℂ) (z₀ z : ℂ) : Fin 9 → ℂ :=
  ![s.lambda,s.mu,s.a,l 0,l 1,r 0,r 1,z₀,z]
abbrev evaluate (v : Fin 9 → ℂ) : ComplexPoly →+* ℂ :=
  eval (Sum.elim v (fun i => star (v i)))

@[simp] private lemma evaluate_coordinate (v : Fin 9 → ℂ) (i : Fin 9) :
    evaluate v (coordinate i) = v i := by simp [evaluate,coordinate]
@[simp] private lemma evaluate_conjugate (v : Fin 9 → ℂ) (P : ComplexPoly) :
    evaluate v (polynomialConjugate P) = star (evaluate v P) :=
  polynomialConjugate_eval P v

private lemma evaluate_adjoint (v : Fin 9 → ℂ) (M : PolyBond) :
    (evaluate v).mapMatrix (adjoint M) = ((evaluate v).mapMatrix M)ᴴ := by
  ext i j
  exact polynomialConjugate_eval (M j i) v

private lemma evaluate_basic (s : Sector) (l r : Fin 2 → ℂ) (z₀ z : ℂ) :
    let E := evaluate (actualVariables s l r z₀ z)
    E.mapMatrix (gPolynomial (coordinate 7)) = G s z₀ ∧
    E.mapMatrix jPolynomial = InteriorPolynomialClearance.J s z ∧ E.mapMatrix wPolynomial = W s ∧
    (∀ i, E.mapMatrix (corePolynomial i) = core s z₀ i) := by
  dsimp only
  have hv (i : Fin 9) : evaluate (actualVariables s l r z₀ z) (coordinate i) =
      actualVariables s l r z₀ z i := by simp [evaluate, coordinate]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [gPolynomial, evaluate_coordinate, actualVariables, G, alpha, beta]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [jPolynomial, adjugateTwo, evaluate_coordinate, actualVariables, InteriorPolynomialClearance.J, alpha, beta]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [wPolynomial, W, schurWeights, evaluate_conjugate, evaluate_coordinate, actualVariables]
  · intro i
    fin_cases i
    · ext j k; fin_cases j <;> fin_cases k <;>
        simp [corePolynomial, core, gPolynomial, evaluate_coordinate, actualVariables, G, alpha, beta]
    · change (evaluate _).mapMatrix (bPolynomial*gPolynomial (coordinate 7)) = B s*G s z₀
      rw [map_mul]
      congr 1
      · ext j k; fin_cases j <;> fin_cases k <;> simp [bPolynomial, B, evaluate_coordinate, actualVariables]
      · ext j k; fin_cases j <;> fin_cases k <;> simp [gPolynomial, evaluate_coordinate, actualVariables, G, alpha, beta]

private lemma evaluate_targets (s : Sector) (l r : Fin 2 → ℂ) (z₀ z : ℂ) (p q : ℕ) :
    let E := evaluate (actualVariables s l r z₀ z)
    E.mapMatrix (targetLeftPolynomial p) = leftTarget s z₀ l p ∧
    E.mapMatrix (targetRightPolynomial q) = rightTarget s z₀ r q := by
  dsimp only
  let E := evaluate (actualVariables s l r z₀ z)
  obtain ⟨hG, hJ, hW, hA⟩ := evaluate_basic s l r z₀ z
  change E.mapMatrix (gPolynomial (coordinate 7)) = G s z₀ at hG
  have hA' (i : Fin 2) : E.mapMatrix (corePolynomial i) = core s z₀ i := hA i
  have hAdj (M : PolyBond) : E.mapMatrix (adjoint M) = (E.mapMatrix M)ᴴ :=
    evaluate_adjoint _ M
  have hl : E.mapMatrix (targetLeftPolynomial p) = leftTarget s z₀ l p := by
    induction p with
    | zero =>
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [targetLeftPolynomial, leftTarget, E, actualVariables,
            RingHom.mapMatrix_apply,vecMulVec_apply]
    | succ p ih =>
        simp only [targetLeftPolynomial, leftTarget, Function.iterate_succ_apply', dualTransfer] at ih ⊢
        simp only [map_sum, map_mul, hAdj, hA', ih]
  have hr : E.mapMatrix (targetRightInnerPolynomial q) =
      (transfer (core s z₀))^[q] (vecMulVec r (star r)) := by
    induction q with
    | zero =>
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [targetRightInnerPolynomial, E, actualVariables,
            RingHom.mapMatrix_apply,vecMulVec_apply]
    | succ q ih =>
        simp only [targetRightInnerPolynomial, Function.iterate_succ_apply', transfer] at ih ⊢
        simp only [map_sum, map_mul, hAdj, hA', ih]
  refine ⟨hl, ?_⟩
  rw [targetRightPolynomial,map_mul,map_mul,hAdj,map_pow,hG,hr]
  rfl

private lemma evaluate_cleared (s : Sector) (l r : Fin 2 → ℂ) (z₀ z : ℂ) (p q : ℕ) :
    let E := evaluate (actualVariables s l r z₀ z)
    E.mapMatrix (clearedLeftPolynomial p) = leftNumerator s z p (leftTarget s z₀ l p) ∧
    E.mapMatrix (clearedRightPolynomial q) = rightNumerator s z q (rightTarget s z₀ r q) := by
  dsimp only
  let E := evaluate (actualVariables s l r z₀ z)
  obtain ⟨hG,hJ,hW,hA⟩ := evaluate_basic s l r z₀ z
  obtain ⟨hP,hH⟩ := evaluate_targets s l r z₀ z p q
  change E.mapMatrix jPolynomial = InteriorPolynomialClearance.J s z at hJ
  change E.mapMatrix (targetLeftPolynomial p) = leftTarget s z₀ l p at hP
  change E.mapMatrix (targetRightPolynomial q) = rightTarget s z₀ r q at hH
  have hAdj (M : PolyBond) : E.mapMatrix (adjoint M) = (E.mapMatrix M)ᴴ :=
    evaluate_adjoint _ M
  have hw (i j : Fin 2) : E (wPolynomial i j) = W s i j := by
    have h := congrFun (congrFun hW i) j
    simpa only [RingHom.mapMatrix_apply,Matrix.map_apply] using h
  have hLi (n : ℕ) (M : PolyBond) :
      E.mapMatrix ((fun M => fun i j => wPolynomial j i * (adjoint jPolynomial*M*jPolynomial) i j)^[n] M) =
        (leftStep s z)^[n] (E.mapMatrix M) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        have hstep (N : PolyBond) :
            E.mapMatrix (fun i j => wPolynomial j i*(adjoint jPolynomial*N*jPolynomial) i j) =
              leftStep s z (E.mapMatrix N) := by
          ext i j
          simp only [RingHom.mapMatrix_apply,Matrix.map_apply,map_mul]
          have hm := congrFun (congrFun (show E.mapMatrix (adjoint jPolynomial*N*jPolynomial) =
            (InteriorPolynomialClearance.J s z)ᴴ*E.mapMatrix N*InteriorPolynomialClearance.J s z by rw [map_mul,map_mul,hAdj,hJ]) i) j
          simp only [RingHom.mapMatrix_apply,Matrix.map_apply] at hm
          rw [hm, hw]
          simp only [leftStep,Wstar,Matrix.transpose_apply,RingHom.mapMatrix_apply]
        rw [hstep, ih]
  have hRi (n : ℕ) (M : PolyBond) :
      E.mapMatrix ((fun M => jPolynomial*(wPolynomial ⊙ M)*adjoint jPolynomial)^[n] M) =
        (rightStep s z)^[n] (E.mapMatrix M) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        simp only [map_mul, hAdj, hJ]
        have hh (N : PolyBond) : E.mapMatrix (wPolynomial ⊙ N) =
            W s ⊙ E.mapMatrix N := by
          ext i j
          simp only [RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.hadamard_apply,map_mul]
          rw [hw]
        rw [hh, ih]
        rfl
  constructor
  · rw [clearedLeftPolynomial, hLi, hP]; rfl
  · rw [clearedRightPolynomial, hRi, map_mul, map_mul, map_pow, hAdj,
      map_pow, hJ, hH]; rfl

private lemma realify_eval (P : ComplexPoly) (s : Sector) (l r : Fin 2 → ℂ) (z₀ z : ℂ) :
    eval (slice (coordinates s l r z₀) z) (realify P) =
      (evaluate (actualVariables s l r z₀ z) P).re := by
  rw [realify, eval_rename]
  have hv : slice (coordinates s l r z₀) z ∘ cartIndex =
      realCoordinates (actualVariables s l r z₀ z) := by
    funext i; rcases i with i | i <;> fin_cases i <;>
      simp [slice, coordinates, cartIndex, actualVariables, realCoordinates]
  rw [hv, (coefficient_eval _ _).1]
  have hc : (fun i => ((realCoordinates (actualVariables s l r z₀ z) i) : ℂ)) =
      PhasePolynomial.cartesian (actualVariables s l r z₀ z) := by
    funext i; cases i <;> rfl
  rw [hc, PhasePolynomial.actual_cartesian]
  rfl

/-- Literal real polynomials clear the native residual with the target held fixed. -/
theorem polynomial_clear (p q : ℕ) (s : Sector) (hs : Regular s)
    (l r : Fin 2 → ℂ) (z₀ z : ℂ) (hz : z ≠ 0) :
    eval (slice (coordinates s l r z₀) z) (FL p q) =
      cL s p z*(residual s p q (leftTarget s z₀ l p) (rightTarget s z₀ r q) z).re ∧
    eval (slice (coordinates s l r z₀) z) (FR p q) =
      cR s q z*(residual s p q (leftTarget s z₀ l p) (rightTarget s z₀ r q) z).im := by
  obtain ⟨hL,hR⟩ := evaluate_cleared s l r z₀ z p q
  have hl : evaluate (actualVariables s l r z₀ z) (clearedLeftPolynomial p).det =
      (leftNumerator s z p (leftTarget s z₀ l p)).det := by rw [RingHom.map_det,hL]
  have hr : evaluate (actualVariables s l r z₀ z) (clearedRightPolynomial q).det =
      (rightNumerator s z q (rightTarget s z₀ r q)).det := by rw [RingHom.map_det,hR]
  simp only [FL, FR, realify_eval, hl, hr]
  exact determinant_clear s hs z hz p q _ _

/-- Substitution is performed after formal differentiation in the independent trial inputs. -/
def atTarget : RealPoly →+* TargetPoly :=
  eval₂Hom C (Sum.elim ![X 14,X 15] X)
def b (p q : ℕ) : TargetPoly := atTarget (trialJacobian (FL p q) (FR p q))

private lemma atTarget_eval (F : RealPoly) (s : Sector) (l r : Fin 2 → ℂ) (z₀ : ℂ) :
    eval (coordinates s l r z₀) (atTarget F) = eval (slice (coordinates s l r z₀) z₀) F := by
  simp only [atTarget,coe_eval₂Hom,eval_eval₂]
  have hc : (eval (coordinates s l r z₀)).comp C = RingHom.id ℝ := by ext a; simp
  rw [hc]
  simp only [eval₂_id]
  have hv : (fun i => eval (coordinates s l r z₀) (Sum.elim ![X 14,X 15] X i)) =
      slice (coordinates s l r z₀) z₀ := by
    funext i
    rcases i with i | i
    · fin_cases i <;> simp [slice,coordinates]
    · simp [slice]
  rw [hv]

private lemma differentiable_factors (s : Sector) (p q : ℕ) (z : ℂ) :
    DifferentiableAt ℝ (cL s p) z ∧ DifferentiableAt ℝ (cR s q) z := by
  constructor
  · unfold cL; simp only [Complex.normSq_apply]; fun_prop
  · unfold cR; simp only [Complex.normSq_apply]; fun_prop

/-- The real determinant uses basisOneI, with no variation of the actual targets. -/
theorem b_eval_derivative (p q : ℕ) (s : Sector) (hs : Regular s)
    (l r : Fin 2 → ℂ) (z₀ : ℂ) (hz₀ : z₀ ≠ 0) (D : ℂ →L[ℝ] ℂ)
    (hd : HasFDerivAt (residual s p q (leftTarget s z₀ l p) (rightTarget s z₀ r q)) D z₀) :
    eval (coordinates s l r z₀) (b p q) =
      cL s p z₀*cR s q z₀*LinearMap.det D.toLinearMap := by
  rw [b,atTarget_eval]
  apply cleared_jacobian
  · exact residual_at_target hs hz₀ p q l r
  · exact hd
  · exact (differentiable_factors s p q z₀).1
  · exact (differentiable_factors s p q z₀).2
  · filter_upwards [eventually_ne_nhds hz₀] with z hz
    exact (polynomial_clear p q s hs l r z₀ z hz).1
  · filter_upwards [eventually_ne_nhds hz₀] with z hz
    exact (polynomial_clear p q s hs l r z₀ z hz).2

/-- The accepted native all-positive-length witness is consumed here. -/
theorem b_nonzero (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    eval (coordinates OpenBoundaryMPSInteriorTransversality.fixedSector
      OpenBoundaryMPSInteriorTransversality.leftBoundary
      OpenBoundaryMPSInteriorTransversality.rightBoundary 1) (b p q) ≠ 0 ∧ b p q ≠ 0 := by
  obtain ⟨_,_,_,_,_,L,C,R,e,u,v,he,hd,hdet,hne,_⟩ :=
    OpenBoundaryMPSInteriorTransversality.interior_q2_fixed_target_witness p q hp hq
  have hs : Regular OpenBoundaryMPSInteriorTransversality.fixedSector := by
    norm_num [Regular,OpenBoundaryMPSInteriorTransversality.fixedSector,delta,alpha,beta,
      Complex.normSq_apply]
  have hD : LinearMap.det e.toContinuousLinearMap.toLinearMap ≠ 0 := by
    rw [real_det]
    simpa [he,Complex.mul_re,Complex.mul_im] using hne
  have hv := b_eval_derivative p q _ hs _ _ 1 (by norm_num) _ hd
  have hpos := clearance_positive _ hs 1 (by norm_num) p q
  have hval : eval (coordinates OpenBoundaryMPSInteriorTransversality.fixedSector
      OpenBoundaryMPSInteriorTransversality.leftBoundary
      OpenBoundaryMPSInteriorTransversality.rightBoundary 1) (b p q) ≠ 0 := by
    rw [hv]
    exact mul_ne_zero (mul_ne_zero hpos.1.ne' hpos.2.ne') hD
  refine ⟨hval, ?_⟩
  intro hb
  simpa [hb] using hval

private lemma right_step_smul (s : Sector) (z c : ℂ) (X : Bond) :
    rightStep s z (c • X) = c • rightStep s z X := by
  unfold rightStep
  have h : W s ⊙ (c • X) = c • (W s ⊙ X) := by
    ext i j; simp [Matrix.hadamard_apply,smul_eq_mul]; ring
  rw [h,mul_smul_comm,smul_mul_assoc]

private lemma right_boundary_scale (s : Sector) (z₀ z : ℂ) (r : Fin 2 → ℂ) (q : ℕ) (a : ℝ) :
    rightNumerator s z q (rightTarget s z₀ (fun i => (a : ℂ)*r i) q) =
      (a : ℂ)^2 • rightNumerator s z q (rightTarget s z₀ r q) := by
  have hout : vecMulVec (fun i => (a : ℂ)*r i) (star (fun i => (a : ℂ)*r i)) =
      (a : ℂ)^2 • vecMulVec r (star r) := by
    ext i j
    simp [vecMulVec_apply,star_mul,smul_eq_mul]
    ring
  have ht : rightTarget s z₀ (fun i => (a : ℂ)*r i) q = (a : ℂ)^2 • rightTarget s z₀ r q := by
    unfold rightTarget
    rw [hout,OpenBoundaryMPSInteriorRootRealization.iterate_smul _
      (OpenBoundaryMPSInteriorRootRealization.transfer_smul _) q,mul_smul_comm,smul_mul_assoc]
  unfold rightNumerator
  rw [ht,mul_smul_comm,smul_mul_assoc,
    OpenBoundaryMPSInteriorRootRealization.iterate_smul _ (right_step_smul s z)]

private lemma row_values (p q : ℕ) (s : Sector) (l r : Fin 2 → ℂ) (z₀ z : ℂ) :
    eval (slice (coordinates s l r z₀) z) (FL p q) =
      (leftNumerator s z p (leftTarget s z₀ l p)).det.re ∧
    eval (slice (coordinates s l r z₀) z) (FR p q) =
      (rightNumerator s z q (rightTarget s z₀ r q)).det.re := by
  obtain ⟨hL,hR⟩ := evaluate_cleared s l r z₀ z p q
  constructor
  · rw [FL,realify_eval,RingHom.map_det,hL]
  · rw [FR,realify_eval,RingHom.map_det,hR]

private lemma jacobian_values (F H : RealPoly) (θ : Fin 16 → ℝ) (z : ℂ) :
    eval (slice θ z) (trialJacobian F H) =
      sliceDerivative F θ z 1 * sliceDerivative H θ z Complex.I -
        sliceDerivative F θ z Complex.I * sliceDerivative H θ z 1 := by
  have hx (P : RealPoly) : sliceDerivative P θ z 1 = eval (slice θ z) (pderiv (Sum.inl 0) P) := by
    simp only [sliceDerivative,ContinuousLinearMap.add_apply,_root_.smul_apply,
      Complex.reCLM_apply,Complex.imCLM_apply,Complex.one_re,Complex.one_im,
      smul_eq_mul,mul_one,mul_zero,add_zero]
  have hy (P : RealPoly) : sliceDerivative P θ z Complex.I = eval (slice θ z) (pderiv (Sum.inl 1) P) := by
    simp only [sliceDerivative,ContinuousLinearMap.add_apply,_root_.smul_apply,
      Complex.reCLM_apply,Complex.imCLM_apply,Complex.I_re,Complex.I_im,
      smul_eq_mul,mul_one,mul_zero,zero_add]
  rw [hx,hx,hy,hy]
  unfold trialJacobian
  rw [(eval (slice θ z)).map_sub,(eval (slice θ z)).map_mul,(eval (slice θ z)).map_mul]

private lemma boundary_b_scale (p q : ℕ) (s : Sector) (l r : Fin 2 → ℂ) (z₀ : ℂ) (a : ℝ) :
    eval (coordinates s l (fun i => (a : ℂ)*r i) z₀) (b p q) =
      a^4 * eval (coordinates s l r z₀) (b p q) := by
  let θ := coordinates s l r z₀
  let θa := coordinates s l (fun i => (a : ℂ)*r i) z₀
  have hL (z : ℂ) : eval (slice θa z) (FL p q) = eval (slice θ z) (FL p q) := by
    rw [(row_values p q s l _ z₀ z).1,(row_values p q s l r z₀ z).1]
  have hR (z : ℂ) : eval (slice θa z) (FR p q) = a^4*eval (slice θ z) (FR p q) := by
    rw [(row_values p q s l _ z₀ z).2,(row_values p q s l r z₀ z).2,
      right_boundary_scale,det_smul]
    simp only [Fintype.card_fin, ← pow_mul]
    rw [← Complex.ofReal_pow]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    ring
  have hdL := (hasFDerivAt_slice (FL p q) θa z₀).unique
    ((hasFDerivAt_slice (FL p q) θ z₀).congr_of_eventuallyEq (Filter.Eventually.of_forall hL))
  have hdR := (hasFDerivAt_slice (FR p q) θa z₀).unique
    (((hasFDerivAt_slice (FR p q) θ z₀).const_mul (a^4)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hR))
  simp only [b,atTarget_eval,jacobian_values]
  change sliceDerivative (FL p q) θa z₀ 1 * sliceDerivative (FR p q) θa z₀ Complex.I -
    sliceDerivative (FL p q) θa z₀ Complex.I * sliceDerivative (FR p q) θa z₀ 1 = _
  rw [hdL,hdR]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

def scaleRight (a : ℝ) (θ : Fin 16 → ℝ) : Fin 16 → ℝ :=
  fun i => if 10 ≤ i.val ∧ i.val < 14 then a*θ i else θ i

private lemma scale_coordinates (s : Sector) (l r : Fin 2 → ℂ) (z₀ : ℂ) (a : ℝ) :
    scaleRight a (coordinates s l r z₀) = coordinates s l (fun i => (a : ℂ)*r i) z₀ := by
  funext i
  fin_cases i <;> simp [scaleRight,coordinates,Complex.mul_re,Complex.mul_im]

/-- The quartic transport law holds on the entire actual real coordinate space. -/
theorem b_right_scale (p q : ℕ) (θ : Fin 16 → ℝ) (a : ℝ) :
    eval (scaleRight a θ) (b p q) = a^4*eval θ (b p q) := by
  let s : Sector := ⟨⟨θ 0,θ 1⟩,⟨θ 2,θ 3⟩,⟨θ 4,θ 5⟩⟩
  let l : Fin 2 → ℂ := ![⟨θ 6,θ 7⟩,⟨θ 8,θ 9⟩]
  let r : Fin 2 → ℂ := ![⟨θ 10,θ 11⟩,⟨θ 12,θ 13⟩]
  let z₀ : ℂ := ⟨θ 14,θ 15⟩
  have hθ : coordinates s l r z₀ = θ := by
    funext i; fin_cases i <;> rfl
  rw [← hθ,scale_coordinates]
  exact boundary_b_scale p q s l r z₀ a

private lemma differentiable_residual (p q : ℕ) (s : Sector) (hs : Regular s)
    (l r : Fin 2 → ℂ) (z₀ : ℂ) (hz₀ : z₀ ≠ 0) :
    DifferentiableAt ℝ
      (residual s p q (leftTarget s z₀ l p) (rightTarget s z₀ r q)) z₀ := by
  let θ := coordinates s l r z₀
  let gL : ℂ → ℝ := fun z => eval (slice θ z) (FL p q) / cL s p z
  let gR : ℂ → ℝ := fun z => eval (slice θ z) (FR p q) / cR s q z
  obtain ⟨hcL,hcR⟩ := differentiable_factors s p q z₀
  obtain ⟨hpL,hpR⟩ := clearance_positive s hs z₀ hz₀ p q
  have hL : DifferentiableAt ℝ gL z₀ := by
    convert! (hasFDerivAt_slice (FL p q) θ z₀).differentiableAt.mul
      (hcL.inv hpL.ne') using 1
  have hR : DifferentiableAt ℝ gR z₀ := by
    convert! (hasFDerivAt_slice (FR p q) θ z₀).differentiableAt.mul
      (hcR.inv hpR.ne') using 1
  have hC : DifferentiableAt ℝ (fun z => (gL z : ℂ) + Complex.I * (gR z : ℂ)) z₀ :=
    (Complex.ofRealCLM.differentiableAt.comp z₀ hL).add
      ((Complex.ofRealCLM.differentiableAt.comp z₀ hR).const_mul Complex.I)
  apply hC.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hz₀] with z hz
  obtain ⟨hF,hH⟩ := polynomial_clear p q s hs l r z₀ z hz
  obtain ⟨hcl,hcr⟩ := clearance_positive s hs z hz p q
  dsimp only [gL,gR,θ]
  rw [hF,hH,mul_div_cancel_left₀ _ hcl.ne',mul_div_cancel_left₀ _ hcr.ne']
  apply Complex.ext <;> simp

/-- The nonzero polynomial locus gives actual whole-interior nonphase ambiguity. -/
theorem nonzero_locus_actual_ambiguity (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (s : Sector) (hs : Regular s) (z₀ : ℂ) (hz₀ : z₀ ≠ 0) (l r : Fin 2 → ℂ)
    (hP : (leftTarget s z₀ l p).PosDef) (hH : (rightTarget s z₀ r q).PosDef)
    (hb : eval (coordinates s l r z₀) (b p q) ≠ 0) :
    ∃ φ : Word ((p + 2) + q) → ℂ,
      φ ∈ openBoundaryMPS ((p + 2) + q) ∧ φ ≠ 0 ∧
      rawInterior p 2 q φ = rawInterior p 2 q
        (mpsState ((p + 2) + q) (core s z₀ 0) (core s z₀ 1) l r) ∧
      ¬ ∃ η : ℂ, ‖η‖ = 1 ∧ φ =
        η • mpsState ((p + 2) + q) (core s z₀ 0) (core s z₀ 1) l r := by
  let f := residual s p q (leftTarget s z₀ l p) (rightTarget s z₀ r q)
  have hf : DifferentiableAt ℝ f z₀ := differentiable_residual p q s hs l r z₀ hz₀
  let D := fderiv ℝ f z₀
  have hdet : D.det ≠ 0 := by
    intro he
    apply hb
    rw [b_eval_derivative p q s hs l r z₀ hz₀ D hf.hasFDerivAt]
    change cL s p z₀ * cR s q z₀ * D.det = 0
    rw [he,mul_zero]
  let e := D.toContinuousLinearEquivOfDetNeZero hdet
  have he : (e : ℂ →L[ℝ] ℂ) = D :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero D hdet
  obtain ⟨ε,R,hε,hεz,hzR,hcircle⟩ :=
    OpenBoundaryMPSInteriorEndpointSigns.annular_residual_negative s hs p hp
      (leftTarget s z₀ l p) hP z₀ hz₀
  apply annular_regular_root_actual_ambiguity p q hp hq s hs z₀ hz₀ l r hP hH
    ε R e hε hεz hzR
  · rw [he]
    exact hf.hasFDerivAt
  · exact hcircle q (rightTarget s z₀ r q)

end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorPolynomial
