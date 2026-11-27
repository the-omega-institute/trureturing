/- GID: D5/S3/Geometry/Lorentz/UnifiedCornerBF4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/UnifiedCornerBF4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unified normal and Yang–Mills current symmetries, Darboux area, and signed Hodge BF reduction. -/
import OmegaBuild.Commands
import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Lie.InvariantForm
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import D5.S3.Geometry.Lorentz.Urbantke
import D5.S3.Geometry.Lorentz.WeylNullScreen
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Kronecker
compile_only_with_mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Geometry.Lorentz.UnifiedCornerBF4D
open scoped TensorProduct Matrix Kronecker
open LieAlgebra LieAlgebra.ExtendScalars Matrix
section Currents
variable {A : Type*} [CommRing A] [Algebra ℝ A]
variable {gYM : Type*} [LieRing gYM] [LieAlgebra ℝ gYM]
abbrev CornerInternal (gYM : Type*) [LieRing gYM] [LieAlgebra ℝ gYM] :=
  SpecialLinear.sl (Fin 2) ℝ × gYM
abbrev CornerCurrent (A gYM : Type*) [CommRing A] [Algebra ℝ A]
    [LieRing gYM] [LieAlgebra ℝ gYM] := A ⊗[ℝ] CornerInternal gYM
/-- Differentiation on the coefficient factor acts by a Lie derivation. -/
def currentDerivation (X : Derivation ℝ A A) :
    LieDerivation ℝ (CornerCurrent A gYM) (CornerCurrent A gYM) where
  toLinearMap := TensorProduct.map X.toLinearMap LinearMap.id
  leibniz' x y := by
    refine x.inductionOn ?_ ?_
    · intro a u
      refine y.inductionOn ?_ ?_
      · intro b v
        simp only [bracket_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
          Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, TensorProduct.add_tmul]
        rw [sub_eq_add_neg, ← TensorProduct.tmul_neg, lie_skew u v]
      · intro y z hy hz
        simp only [lie_add, add_lie, map_add] at *
        rw [hy, hz]
        abel
    · intro x z hx hz
      simp only [add_lie, lie_add, map_add] at *
      rw [hx, hz]
      abel
private theorem currentDerivation_tmul (X : Derivation ℝ A A) (a : A)
    (u : CornerInternal gYM) :
    currentDerivation X (a ⊗ₜ[ℝ] u) = X a ⊗ₜ[ℝ] u := rfl
def cornerDerivationHom (L : LieSubalgebra ℝ (Derivation ℝ A A)) :
    L →ₗ⁅ℝ⁆ LieDerivation ℝ (CornerCurrent A gYM) (CornerCurrent A gYM) where
  toFun X := currentDerivation (X : Derivation ℝ A A)
  map_add' X Y := by
    ext z
    refine z.inductionOn (fun a u => ?_) (fun x y hx hy => ?_)
    · simp [currentDerivation_tmul, TensorProduct.add_tmul]
    · rw [map_add, map_add, hx, hy]
  map_smul' r X := by
    ext z
    refine z.inductionOn (fun a u => ?_) (fun x y hx hy => ?_)
    · simp [currentDerivation_tmul, TensorProduct.smul_tmul']
    · rw [map_add, map_add, hx, hy]
  map_lie' {X Y} := by
    ext z
    refine z.inductionOn (fun a u => ?_) (fun x y hx hy => ?_)
    · simp [currentDerivation_tmul,
        Derivation.commutator_apply, TensorProduct.sub_tmul]
    · rw [map_add, map_add, hx, hy]
abbrev CornerAlgebra (A : Type*) [CommRing A] [Algebra ℝ A]
    (L : LieSubalgebra ℝ (Derivation ℝ A A)) (gYM : Type*) [LieRing gYM]
    [LieAlgebra ℝ gYM] :=
  SemiDirectSum (CornerCurrent A gYM) L (cornerDerivationHom L)
variable {L : LieSubalgebra ℝ (Derivation ℝ A A)}
def P (X : L) : CornerAlgebra A L gYM := SemiDirectSum.inr (cornerDerivationHom L) X
def J (a : A) (u : CornerInternal gYM) : CornerAlgebra A L gYM :=
  SemiDirectSum.inl (cornerDerivationHom L) (a ⊗ₜ[ℝ] u)
/-- The charge maps include the two full current algebras. -/
def G : A ⊗[ℝ] SpecialLinear.sl (Fin 2) ℝ →ₗ⁅ℝ⁆ CornerAlgebra A L gYM :=
  (SemiDirectSum.inl (cornerDerivationHom (gYM := gYM) L)).comp
    (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ A) (LieHom.inl ℝ _ _))
def Y : A ⊗[ℝ] gYM →ₗ⁅ℝ⁆ CornerAlgebra A L gYM :=
  (SemiDirectSum.inl (cornerDerivationHom (gYM := gYM) L)).comp
    (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ A) (LieHom.inr ℝ _ _))
theorem corner_bracket (X Z : L) (a b : A) (u v : CornerInternal gYM) :
    ⁅P (gYM := gYM) X, P (gYM := gYM) Z⁆ = P (gYM := gYM) ⁅X, Z⁆ ∧
    ⁅P (gYM := gYM) X, J (L := L) a u⁆ = J (L := L) ((X : Derivation ℝ A A) a) u ∧
    ⁅J (L := L) a u, J (L := L) b v⁆ = J (L := L) (a*b) ⁅u, v⁆ := by
  refine ⟨(SemiDirectSum.inr (cornerDerivationHom (gYM := gYM) L)).map_lie X Z, ?_, ?_⟩
  · change ⁅(⟨0,X⟩ : CornerAlgebra A L gYM), (⟨a ⊗ₜ[ℝ] u,0⟩ : CornerAlgebra A L gYM)⁆ =
      ⟨(X : Derivation ℝ A A) a ⊗ₜ[ℝ] u,0⟩
    rw [SemiDirectSum.lie_eq_mk]
    simp [cornerDerivationHom, currentDerivation_tmul]
  · have h := ((SemiDirectSum.inl (cornerDerivationHom (gYM := gYM) L)).map_lie
      (a ⊗ₜ[ℝ] u) (b ⊗ₜ[ℝ] v)).symm
    rw [bracket_tmul] at h
    exact h
theorem corner_internal_brackets (X : L)
    (u v : A ⊗[ℝ] SpecialLinear.sl (Fin 2) ℝ) (l η : A ⊗[ℝ] gYM) :
    let d := (X : Derivation ℝ A A).toLinearMap
    let Gg := G (L := L) (gYM := gYM)
    let Yg := Y (L := L)
    ⁅P (gYM := gYM) X, Gg u⁆ = Gg (TensorProduct.map d LinearMap.id u) ∧
    ⁅P (gYM := gYM) X, Yg l⁆ = Yg (TensorProduct.map d LinearMap.id l) ∧
    ⁅Gg u, Gg v⁆ = Gg ⁅u,v⁆ ∧ ⁅Yg l,Yg η⁆ = Yg ⁅l,η⁆ ∧ ⁅Gg u,Yg l⁆ = 0 := by
  dsimp only
  refine ⟨?_, ?_, ((G (L := L) (gYM := gYM)).map_lie u v).symm,
    ((Y (L := L)).map_lie l η).symm, ?_⟩
  · refine u.inductionOn (fun a t => ?_) (fun a b ha hb => ?_)
    · exact (corner_bracket X X a a ((t,0) : CornerInternal gYM) (t,0)).2.1
    · rw [map_add, lie_add, map_add, map_add, ha, hb]
  · refine l.inductionOn (fun a t => ?_) (fun a b ha hb => ?_)
    · exact (corner_bracket X X a a ((0,t) : CornerInternal gYM) (0,t)).2.1
    · rw [map_add, lie_add, map_add, map_add, ha, hb]
  · refine u.inductionOn ?_ ?_
    · intro a t
      refine l.inductionOn ?_ ?_
      · intro b w
        change ⁅J (L := L) a (t,(0:gYM)), J (L := L) b (0,w)⁆ = 0
        rw [(corner_bracket X X a b ((t,0) : CornerInternal gYM) (0,w)).2.2]
        have h : ⁅((t,0) : CornerInternal gYM), ((0,w) : CornerInternal gYM)⁆ = 0 := by
          ext <;> simp
        rw [h]
        simp [J]
      · intro a b ha hb
        rw [map_add, lie_add, ha, hb, add_zero]
    · intro a b ha hb
      rw [map_add, add_lie, ha, hb, add_zero]
theorem corner_jacobi (x y z : CornerAlgebra A L gYM) :
    ⁅x, ⁅y,z⁆⁆ + ⁅y, ⁅z,x⁆⁆ + ⁅z, ⁅x,y⁆⁆ = 0 := by
  rw [leibniz_lie x y z, ← lie_skew z x, ← lie_skew z ⁅x,y⁆, lie_neg]
  abel
attribute [local instance 100] LieRing.ofAssociativeRing
def quantumCharge :
    CornerAlgebra A L gYM →ₗ⁅ℝ⁆ UniversalEnvelopingAlgebra ℝ (CornerAlgebra A L gYM) :=
  UniversalEnvelopingAlgebra.ι ℝ
theorem enveloping_commutators (u v : A ⊗[ℝ] SpecialLinear.sl (Fin 2) ℝ)
    (l η : A ⊗[ℝ] gYM) :
    let Q := quantumCharge (A := A) (L := L) (gYM := gYM)
    let Gg := G (L := L) (gYM := gYM)
    let Yg := Y (L := L)
    ⁅Q (Gg u), Q (Gg v)⁆ = Q (Gg ⁅u,v⁆) ∧
    ⁅Q (Yg l), Q (Yg η)⁆ = Q (Yg ⁅l,η⁆) ∧ ⁅Q (Gg u), Q (Yg l)⁆ = 0 := by
  dsimp only
  obtain ⟨_, _, hg, hy, hc⟩ := corner_internal_brackets (0 : L) u v l η
  refine ⟨?_, ?_, ?_⟩
  · exact ((quantumCharge (L := L)).map_lie _ _).symm.trans (congrArg _ hg)
  · exact ((quantumCharge (L := L)).map_lie _ _).symm.trans (congrArg _ hy)
  · rw [← LieHom.map_lie, hc, map_zero]
end Currents
section Laurent
open LaurentPolynomial
private abbrev LP := LaurentPolynomial ℝ
private def wittLinear (m : ℤ) : LP →ₗ[ℝ] LP :=
  (Finsupp.linearCombination ℝ (fun n : ℤ => (-(n : ℝ)) • (T (m+n) : LP))).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap
private theorem wittLinear_monomial (m n : ℤ) (r : ℝ) :
    wittLinear m (C r * T n) = (-(n : ℝ) * r) • (T (m+n) : LP) := by
  rw [← single_eq_C_mul_T]
  change Finsupp.linearCombination ℝ (fun k : ℤ => (-(k : ℝ)) • (T (m+k) : LP))
    (Finsupp.single n r) = _
  rw [Finsupp.linearCombination_single, smul_smul, mul_comm]
def witt (m : ℤ) : Derivation ℝ LP LP :=
  Derivation.mk' (wittLinear m) fun x y => by
    induction x using LaurentPolynomial.induction_on' with
    | add a b ha hb =>
      simp only [add_mul, map_add, add_smul, smul_add, ha, hb]
      abel
    | C_mul_T n a =>
      induction y using LaurentPolynomial.induction_on' with
      | add b c hb hc =>
        simp only [mul_add, map_add, add_smul, smul_add, hb, hc]
        abel
      | C_mul_T k b =>
        rw [show C a * T n * (C b * T k) = (C (a*b) * T (n+k) : LP) by
          rw [map_mul, T_add]; ring]
        rw [wittLinear_monomial, wittLinear_monomial, wittLinear_monomial]
        simp only [smul_eq_mul, Algebra.mul_smul_comm, ← single_eq_C_mul_T]
        simp only [T, AddMonoidAlgebra.smul_single', AddMonoidAlgebra.single_mul_single]
        rw [show n + (m+k) = m+(n+k) by omega, show k + (m+n) = m+(n+k) by omega,
          ← AddMonoidAlgebra.single_add]
        congr 1
        push_cast
        ring
theorem witt_monomial (m n : ℤ) (r : ℝ) :
    witt m (C r * T n) = (-(n : ℝ)*r) • (T (m+n) : LP) :=
  wittLinear_monomial m n r
theorem witt_bracket (m n : ℤ) :
    ⁅witt m, witt n⁆ = ((m : ℝ) - (n : ℝ)) • witt (m+n) := by
  apply Derivation.ext
  intro x
  rw [Derivation.commutator_apply]
  induction x using LaurentPolynomial.induction_on' with
  | add a b ha hb =>
    simp only [map_add] at *
    rw [← ha, ← hb]
    abel
  | C_mul_T k r =>
    simp only [witt_monomial, Derivation.map_smul, smul_smul, Derivation.smul_apply]
    have ht (l : ℤ) : witt m (T l) = (-(l : ℝ)) • (T (m+l) : LP) := by
      simpa using witt_monomial m l 1
    have ht' (l : ℤ) : witt n (T l) = (-(l : ℝ)) • (T (n+l) : LP) := by
      simpa using witt_monomial n l 1
    rw [ht, ht']
    simp only [smul_smul]
    rw [show m+(n+k) = (m+n)+k by omega, show n+(m+k) = (m+n)+k by omega,
      ← sub_smul]
    congr 1
    push_cast
    ring
theorem laurent_current_modes {gYM : Type*} [LieRing gYM] [LieAlgebra ℝ gYM]
    (m n : ℤ) (u v : CornerInternal gYM) :
    let X : (⊤ : LieSubalgebra ℝ (Derivation ℝ LP LP)) := ⟨witt m, trivial⟩
    ⁅P (gYM := gYM) X, J (L := ⊤) (T n : LP) u⁆ = -(n : ℝ) • J (L := ⊤) (T (m+n) : LP) u ∧
    ⁅J (L := ⊤) (T m : LP) u, J (L := ⊤) (T n : LP) v⁆ = J (L := ⊤) (T (m+n) : LP) ⁅u,v⁆ := by
  dsimp only
  have h (k : ℤ) : witt m (T k) = -(k : ℝ) • (T (m+k) : LP) := by
    simpa using witt_monomial m k 1
  let X : (⊤ : LieSubalgebra ℝ (Derivation ℝ LP LP)) := ⟨witt m, trivial⟩
  obtain ⟨_, hp, hj⟩ := corner_bracket X X (T n) (T n) u v
  constructor
  · change ⁅P X, J (L := ⊤) (T n : LP) u⁆ = _
    rw [hp]
    change J (L := ⊤) (witt m (T n)) u = _
    rw [h, J, J]
    have ht : ((-(n : ℝ)) • (T (m+n) : LP)) ⊗ₜ[ℝ] u =
        (-(n : ℝ)) • ((T (m+n) : LP) ⊗ₜ[ℝ] u) := TensorProduct.smul_tmul' _ _ _
    rw [ht, map_smul]
  · rw [(corner_bracket X X (T m) (T n) u v).2.2, ← T_add]
end Laurent
section Jets
open Polynomial
private def jetIdeal (N : ℕ) : Ideal ℝ[X] := Ideal.span {X ^ N}
abbrev Jet (N : ℕ) := ℝ[X] ⧸ jetIdeal N
private def jetPolynomial (m : ℕ) : Derivation ℝ ℝ[X] ℝ[X] :=
  (-((X : ℝ[X])^(m+1))) • Derivation.mk' Polynomial.derivative (fun a b => by
    simp [Polynomial.derivative_mul, smul_eq_mul, mul_comm]; abel)
private theorem jetPolynomial_pow (m n : ℕ) :
    jetPolynomial m ((X : ℝ[X])^n) = -(C (n : ℝ)) * X^(m+n) := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [jetPolynomial, Derivation.smul_apply, Derivation.coe_mk',
      Polynomial.derivative_X_pow_succ,
      smul_eq_mul]
    rw [show m + (n+1) = (m+1)+n by omega, pow_add]
    push_cast
    ring
private theorem jetPreserved (m N : ℕ) (f : ℝ[X])
    (hf : Ideal.Quotient.mkₐ ℝ (jetIdeal N) f = 0) :
    Ideal.Quotient.mkₐ ℝ (jetIdeal N) (jetPolynomial m f) = 0 := by
  change Ideal.Quotient.mk (jetIdeal N) f = 0 at hf
  change Ideal.Quotient.mk (jetIdeal N) (jetPolynomial m f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, jetIdeal, Ideal.mem_span_singleton] at hf ⊢
  obtain ⟨f,rfl⟩ := hf
  rw [Derivation.leibniz, jetPolynomial_pow, smul_eq_mul, smul_eq_mul]
  apply dvd_add (dvd_mul_right _ _)
  rw [pow_add]
  exact ⟨f * -(C (N : ℝ)) * X^m, by ring⟩
def jetWitt (m N : ℕ) : Derivation ℝ (Jet N) (Jet N) :=
  Derivation.liftOfSurjective (Ideal.Quotient.mkₐ_surjective ℝ (jetIdeal N))
    (jetPreserved m N)
def jetMonomial (N n : ℕ) : Jet N := Ideal.Quotient.mkₐ ℝ (jetIdeal N) (X^n)
theorem jet_rules (m n N : ℕ) :
    jetWitt m N (jetMonomial N n) = -(n : ℝ) • jetMonomial N (m+n) ∧
    jetMonomial N m * jetMonomial N n = jetMonomial N (m+n) ∧
    (N ≤ n → jetMonomial N n = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [jetWitt, jetMonomial, Derivation.liftOfSurjective_apply, jetPolynomial_pow]
    rw [show -C (n : ℝ) * (X : ℝ[X])^(m+n) = (-(n : ℝ)) • (X : ℝ[X])^(m+n) by
      rw [Polynomial.smul_eq_C_mul, map_neg]]
    exact (Ideal.Quotient.mkₐ ℝ (jetIdeal N)).toLinearMap.map_smul _ _
  · simp [jetMonomial, pow_add]
  · intro h
    change Ideal.Quotient.mk (jetIdeal N) (X^n) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, jetIdeal, Ideal.mem_span_singleton]
    exact pow_dvd_pow _ h
end Jets

section Casimir
def gravitationalCasimir (M : LieAlgebra.SpecialLinear.sl (Fin 2) ℝ) : ℝ :=
  Matrix.trace (M.val * M.val) / 2
theorem normal_area_casimir (M : LieAlgebra.SpecialLinear.sl (Fin 2) ℝ) :
    gravitationalCasimir M = -M.val.det ∧
    gravitationalCasimir M = M.val 0 0 ^ 2 + M.val 0 1 * M.val 1 0 := by
  have h : Matrix.trace M.val = 0 := M.property
  rw [Matrix.trace_fin_two] at h
  have h' : M.val 1 1 = -M.val 0 0 := by linarith
  constructor <;> simp [gravitationalCasimir, Matrix.trace_fin_two, Matrix.det_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, h'] <;> ring
theorem normal_area_adjoint_invariant (U M : LieAlgebra.SpecialLinear.sl (Fin 2) ℝ) :
    Matrix.trace (⁅U, M⁆.val * M.val + M.val * ⁅U, M⁆.val) / 2 = 0 := by
  have hc : Matrix.trace ((U.val * M.val) * M.val) =
      Matrix.trace ((M.val * U.val) * M.val) := by
    rw [Matrix.trace_mul_cycle]
  rw [Matrix.trace_add, Matrix.trace_mul_comm M.val, LieAlgebra.SpecialLinear.sl_bracket,
    Matrix.sub_mul, Matrix.trace_sub, hc, sub_self, zero_add, zero_div]
theorem normal_area_variation (U M : LieAlgebra.SpecialLinear.sl (Fin 2) ℝ) (t : ℝ) :
    gravitationalCasimir (M + t • ⁅U, M⁆) =
      gravitationalCasimir M + t ^ 2 * gravitationalCasimir ⁅U, M⁆ := by
  have hc := normal_area_adjoint_invariant U M
  rw [Matrix.trace_add] at hc
  change Matrix.trace ((M.val + t • ⁅U, M⁆.val) * (M.val + t • ⁅U, M⁆.val)) / 2 = _
  simp only [gravitationalCasimir, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  linear_combination t * hc
variable {Y : Type*} [LieRing Y] [LieAlgebra ℝ Y]
def ymCasimir (κ : LinearMap.BilinForm ℝ Y) (ν : Y) : ℝ := κ ν ν
theorem internal_casimir_invariant (κ : LinearMap.BilinForm ℝ Y) (hκ : κ.lieInvariant Y)
    (u ν : Y) (t : ℝ) :
    ymCasimir κ (ν + t • ⁅u, ν⁆) = ymCasimir κ ν + t ^ 2 * ymCasimir κ ⁅u, ν⁆ := by
  simp only [ymCasimir, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hκ u ν ν]
  ring
end Casimir
section PoissonChart
abbrev CornerObservable := ℝ → ℝ → ℝ → ℝ → ℝ
/-- The canonical Poisson bracket using the actual real coordinate derivatives. -/
def cornerPoisson (f g : CornerObservable) (q p Γ area : ℝ) : ℝ :=
  deriv (fun x => f x p Γ area) q * deriv (fun x => g q x Γ area) p -
    deriv (fun x => f q x Γ area) p * deriv (fun x => g x p Γ area) q +
    deriv (fun x => f q p x area) Γ * deriv (fun x => g q p Γ x) area -
    deriv (fun x => f q p Γ x) area * deriv (fun x => g q p x area) Γ
def chartH : CornerObservable := fun _ p _ _ => -2 * p
def chartE : CornerObservable := fun q _ _ _ => Real.exp q
def chartF : CornerObservable := fun q p _ area => (area ^ 2 - p ^ 2) * Real.exp (-q)
def chartRapidity : CornerObservable := fun _ _ Γ _ => Γ
def chartArea : CornerObservable := fun _ _ _ area => area
theorem area_boost_pair (q p Γ area : ℝ) :
    cornerPoisson chartH chartE q p Γ area = 2 * chartE q p Γ area ∧
    cornerPoisson chartH chartF q p Γ area = -2 * chartF q p Γ area ∧
    cornerPoisson chartE chartF q p Γ area = chartH q p Γ area ∧
    (chartH q p Γ area ^ 2 + 4 * chartE q p Γ area * chartF q p Γ area) / 4 = area ^ 2 ∧
    cornerPoisson chartRapidity chartArea q p Γ area = 1 ∧
    cornerPoisson chartRapidity chartF q p Γ area = 2 * area * Real.exp (-q) := by
  have hq : deriv (fun x => Real.exp (-x)) q = -Real.exp (-q) := by
    simpa only [mul_neg_one] using (hasDerivAt_neg' (x := q)).exp.deriv
  have hp : deriv (fun x : ℝ => area ^ 2 - x ^ 2) p = -2 * p := by
    rw [deriv_const_sub, deriv_pow_field]
    norm_num
  have ha : deriv (fun x : ℝ => x ^ 2 - p ^ 2) area = 2 * area := by
    rw [deriv_sub_const, deriv_pow_field]
    norm_num
  simp only [cornerPoisson, chartH, chartE, chartF, chartRapidity, chartArea,
    deriv_const, deriv_const_mul_id, Real.deriv_exp, deriv_const_mul_field,
    deriv_mul_const_field, hp, ha, hq, deriv_id'', zero_mul, mul_zero, sub_zero, zero_sub,
    zero_add, add_zero, mul_one, one_mul]
  have he : Real.exp q * Real.exp (-q) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  refine ⟨by ring, by ring, ?_, ?_, by norm_num, True.intro⟩
  · calc
      _ = -(2 * p) * (Real.exp q * Real.exp (-q)) := by ring
      _ = _ := by rw [he, mul_one]; ring
  · calc
      _ = p ^ 2 + (area ^ 2 - p ^ 2) * (Real.exp q * Real.exp (-q)) := by ring
      _ = _ := by rw [he, mul_one]; ring
def chartMoment (q p Γ area : ℝ) : LieAlgebra.SpecialLinear.sl (Fin 2) ℝ :=
  ⟨!![chartH q p Γ area / 2, chartF q p Γ area;
      chartE q p Γ area, -(chartH q p Γ area / 2)], by
      change Matrix.trace (!![chartH q p Γ area / 2, chartF q p Γ area;
        chartE q p Γ area, -(chartH q p Γ area / 2)] : Matrix (Fin 2) (Fin 2) ℝ) = 0
      simp [Matrix.trace_fin_two]⟩
theorem chart_moment_casimir (q p Γ area : ℝ) :
    gravitationalCasimir (chartMoment q p Γ area) = area ^ 2 := by
  rw [(normal_area_casimir _).2]
  have h := (area_boost_pair q p Γ area).2.2.2.1
  simpa [chartMoment] using (show (chartH q p Γ area / 2) ^ 2 +
      chartF q p Γ area * chartE q p Γ area = area ^ 2 by linear_combination h)
end PoissonChart

section Hodge
open Urbantke (PairIndex W exteriorSquare density urbantke hodge wedgeGram)
private abbrev Metric4 (K : Type*) := Matrix (Fin 4) (Fin 4) K
private abbrev BivectorMatrix (K : Type*) := Matrix PairIndex PairIndex K
private def pairLeft : PairIndex → Fin 4
  | .inl _ => 0
  | .inr i => ![2, 3, 1] i
private def pairRight : PairIndex → Fin 4
  | .inl i => i.succ
  | .inr i => ![3, 1, 2] i
private theorem exterior_apply {K : Type*} [CommRing K] (A : Metric4 K) (p q : PairIndex) :
    exteriorSquare A p q = A (pairLeft p) (pairLeft q) * A (pairRight p) (pairRight q) -
      A (pairLeft p) (pairRight q) * A (pairRight p) (pairLeft q) := rfl
private theorem wedge_sq (K : Type*) [CommRing K] : W K * W K = 1 := by
  simp [W, fromBlocks_multiply, fromBlocks_one]
private theorem wedge_transpose (K : Type*) [CommRing K] : (W K)ᵀ = W K := by
  simp [W, fromBlocks_transpose]
private theorem exterior_transpose {K : Type*} [CommRing K] (g : Metric4 K) :
    exteriorSquare gᵀ = (exteriorSquare g)ᵀ :=
  Matrix.ext fun i j => by simp [exteriorSquare, mul_comm]
private theorem exterior_one {K : Type*} [CommRing K] :
    exteriorSquare (1 : Metric4 K) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [exterior_apply, pairLeft, pairRight, Matrix.one_apply]
private theorem exterior_mul {K : Type*} [CommRing K] (A B : Metric4 K) :
    exteriorSquare (A * B) = exteriorSquare A * exteriorSquare B := by
  ext i j
  simp [Matrix.mul_apply, exterior_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, pairLeft, pairRight]
  ring
set_option maxHeartbeats 1000000 in
private theorem exterior_wedge {K : Type*} [CommRing K] (A : Metric4 K) :
    exteriorSquare A * W K * (exteriorSquare A)ᵀ = det A • W K := by
  classical
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, exterior_apply, W, pairLeft, pairRight,
      Matrix.one_apply, Matrix.det_succ_row_zero A, Matrix.det_fin_three,
      Matrix.submatrix_apply, Fin.succAbove] <;> ring
private theorem exterior_inv {K : Type*} [Field K] (A : Metric4 K) (hA : A.det ≠ 0) :
    exteriorSquare A⁻¹ = (exteriorSquare A)⁻¹ := by
  apply (Matrix.inv_eq_left_inv ?_).symm
  rw [← exterior_mul, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), exterior_one]
def realHodge (g : Metric4 ℝ) : BivectorMatrix ℝ :=
  (Real.sqrt |g.det| • W ℝ) * exteriorSquare g⁻¹
def metricSign (g : Metric4 ℝ) : ℝ := if g.det < 0 then -1 else 1
theorem real_hodge_structure (g : Metric4 ℝ) (hs : gᵀ = g) (hg : g.det ≠ 0) :
    realHodge g = hodge g (Real.sqrt |g.det|) ∧
    (metricSign g = -1 ∨ metricSign g = 1) ∧
    realHodge g ^ 2 = metricSign g • (1 : BivectorMatrix ℝ) ∧
    (realHodge g)ᵀ * W ℝ = W ℝ * realHodge g := by
  have he : (exteriorSquare g⁻¹)ᵀ = exteriorSquare g⁻¹ := by
    rw [← exterior_transpose, transpose_nonsing_inv, hs]
  have hw := exterior_wedge g⁻¹
  rw [he, det_nonsing_inv, Ring.inverse_eq_inv] at hw
  have hsign : |g.det| / g.det = metricSign g := by
    unfold metricSign
    split
    · rw [abs_of_neg ‹g.det < 0›, neg_div, div_self hg]
    · rw [abs_of_nonneg (le_of_not_gt ‹¬g.det < 0›), div_self hg]
  refine ⟨by rw [realHodge, exterior_inv g hg, hodge], by unfold metricSign; split <;> simp, ?_, ?_⟩
  · simp only [pow_two, realHodge, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [Matrix.mul_assoc (W ℝ), ← Matrix.mul_assoc (exteriorSquare g⁻¹), hw,
      Matrix.mul_smul, wedge_sq, smul_smul, ← pow_two, Real.sq_sqrt (abs_nonneg _),
      ← div_eq_mul_inv, hsign]
  · simp [realHodge, transpose_mul, wedge_transpose, he, Matrix.mul_assoc,
      ← Matrix.mul_assoc (W ℝ), wedge_sq]
private theorem exterior_smul {K : Type*} [CommRing K] (c : K) (g : Metric4 K) :
    exteriorSquare (c • g) = c ^ 2 • exteriorSquare g := by
  ext i j
  simp only [exterior_apply, Matrix.smul_apply, smul_eq_mul]
  ring
private theorem exterior_map {K T : Type*} [CommRing K] [CommRing T] (f : K →+* T)
    (g : Metric4 K) : exteriorSquare (g.map f) = (exteriorSquare g).map f :=
  Matrix.ext fun i j => by simp [exterior_apply, Matrix.map_apply]
private theorem map_wedge : (W ℝ).map Complex.ofRealHom = W ℂ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [W, Matrix.one_apply]
private theorem phase_scale (g : Metric4 ℝ) (hg : g.det ≠ 0) (l D : ℂ) (hl : l ≠ 0) :
    hodge (l • Complex.ofRealHom.mapMatrix g) D =
      (D / (l ^ 2 * (Real.sqrt |g.det| : ℝ))) • (realHodge g).map Complex.ofRealHom := by
  let f := Complex.ofRealHom
  let E := exteriorSquare g
  have hE : E⁻¹ * E = 1 := by
    dsimp only [E]
    rw [← exterior_inv g hg, ← exterior_mul, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg), exterior_one]
  have hl2 : l ^ 2 ≠ 0 := pow_ne_zero _ hl
  have hvol : (Real.sqrt |g.det| : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (abs_pos.2 hg))
  have hv : ((Real.sqrt |g.det| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hvol
  have hscaled : (l ^ 2 • E.map f)⁻¹ = (l ^ 2)⁻¹ • E⁻¹.map f := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, hE, Matrix.map_one, smul_smul,
      inv_mul_cancel₀ hl2, one_smul] <;> simp
  unfold hodge realHodge
  change (D • W ℂ) * (exteriorSquare (l • g.map f))⁻¹ = _
  rw [exterior_smul, exterior_map, ← show E = exteriorSquare g from rfl, hscaled]
  rw [Matrix.map_mul, exterior_inv g hg, Matrix.map_smul' _ _ _ (map_mul f), map_wedge]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [show f (Real.sqrt |g.det|) = (Real.sqrt |g.det| : ℝ) from rfl]
  congr 1
  field_simp
/-- Conformal Lorentzian reality fixes the relative phase of the real and chiral Hodge maps. -/
theorem urbantke_lorentz_phase (B : Matrix PairIndex (Fin 3) ℂ)
    (hQ : (wedgeGram B).det ≠ 0) (hr : Bᵀ * W ℂ * B.map star = 0) :
    ∃ (g : Metric4 ℝ) (l phase : ℂ), l ≠ 0 ∧ gᵀ = g ∧ g.det < 0 ∧
      urbantke B = l • Complex.ofRealHom.mapMatrix g ∧
      (phase = Complex.I ∨ phase = -Complex.I) ∧
      hodge (urbantke B) (density B) = phase⁻¹ • (realHodge g).map Complex.ofRealHom ∧
      (realHodge g).map Complex.ofRealHom * B = phase • B := by
  obtain ⟨g, l, hl, hs, hn, hu, _⟩ := Urbantke.urbantke_lorentz_reality B hQ hr
  let v := ((Real.sqrt |g.det| : ℝ) : ℂ)
  let phase := l ^ 2 * v / density B
  have hD : density B ≠ 0 := div_ne_zero hQ (by norm_num)
  have hv : v ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (abs_pos.2 hn.ne)))
  have hphase₀ : phase ≠ 0 := div_ne_zero (mul_ne_zero (pow_ne_zero _ hl) hv) hD
  have hvsq : v ^ 2 = -(g.det : ℂ) := by
    dsimp only [v]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (abs_nonneg _), abs_of_neg hn, Complex.ofReal_neg]
  have hden : density B ^ 2 = l ^ 4 * (g.det : ℂ) := by
    calc
      density B ^ 2 = (urbantke B).det := by
        rw [(Urbantke.urbantke_polynomial_identities B).2.1, density, div_pow]
        norm_num
      _ = l ^ 4 * (g.det : ℂ) := by
        rw [hu, det_smul, Fintype.card_fin, ← Complex.ofRealHom.map_det]
        rfl
  have hsq : phase ^ 2 = Complex.I ^ 2 := by
    rw [Complex.I_sq]
    dsimp only [phase]
    rw [div_pow, mul_pow, ← pow_mul, hvsq, mul_neg, ← hden, neg_div, div_self (pow_ne_zero _ hD)]
  have hphase : hodge (urbantke B) (density B) = phase⁻¹ • (realHodge g).map Complex.ofRealHom := by
    rw [hu, phase_scale g hn.ne l _ hl]
    dsimp only [phase, v]
    rw [inv_div]
  have hfix := ((Urbantke.urbantke_nondegenerate_iff_and_chiral_star B).2 hQ).2.2.2.1
  rw [hphase, Matrix.smul_mul] at hfix
  refine ⟨g, l, phase, hl, hs, hn, hu, sq_eq_sq_iff_eq_or_eq_neg.mp hsq, hphase, ?_⟩
  calc
    _ = phase • (phase⁻¹ • ((realHodge g).map Complex.ofRealHom * B)) := by
      rw [smul_smul, mul_inv_cancel₀ hphase₀, one_smul]
    _ = _ := by rw [hfix]
theorem urbantke_real_hodge (B : Matrix PairIndex (Fin 3) ℝ) (hQ : (wedgeGram B).det ≠ 0) :
    0 < (urbantke B).det ∧ realHodge (urbantke B) ^ 2 = 1 := by
  obtain ⟨hs, hd, _⟩ := Urbantke.urbantke_polynomial_identities B
  have hp : 0 < (urbantke B).det := by rw [hd]; positivity
  exact ⟨hp, by rw [(real_hodge_structure _ hs hp.ne').2.2.1, metricSign, ite_eq_right (not_lt_of_ge hp.le), one_smul]⟩
theorem null_screen_hodge (r : WeylNullScreen.FutureNullRay) :
    let g : Metric4 ℝ := diagonal ![-1, 1, 1, 1]
    realHodge g ^ 2 = -(1 : BivectorMatrix ℝ) ∧
    (∀ a, WeylNullScreen.screenFrame r a ⬝ᵥ
      (g *ᵥ WeylNullScreen.nullGenerator r) = 0) ∧
    (∀ a b, WeylNullScreen.screenFrame r a ⬝ᵥ
      (g *ᵥ WeylNullScreen.screenFrame r b) = if a = b then 1 else 0) := by
  let g : Metric4 ℝ := diagonal ![-1, 1, 1, 1]
  have hs : gᵀ = g := by simp [g]
  have hd : g.det = -1 := by simp [g, det_diagonal, Fin.prod_univ_succ]
  have hpair (u v : Fin 4 → ℝ) : u ⬝ᵥ (g *ᵥ v) = WeylNullScreen.minkowski u v := by
    simp [g, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_succ, WeylNullScreen.minkowski]
    ring
  change realHodge g ^ 2 = _ ∧ _
  refine ⟨by rw [(real_hodge_structure g hs (by rw [hd]; norm_num)).2.2.1,
    metricSign, hd]; norm_num, ?_⟩
  simpa only [← hpair] using WeylNullScreen.screenFrame_spec r
end Hodge

section AuxiliaryBF
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
def bfDensity (W : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (gravity coupling : ℝ) (F B : V) : ℝ :=
  gravity + W B F - coupling ^ 2 / 2 * W B (J B)
def bfStationary (W : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (coupling : ℝ) (F B : V) : Prop :=
  ∀ v, W v (F - coupling ^ 2 • J B) = 0
/-- The exact variation polynomial, including the quadratic coefficient. -/
theorem bf_variation (W : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (hsym : ∀ x y, W x y = W y x) (hadj : ∀ x y, W (J x) y = W x (J y))
    (gravity coupling t : ℝ) (F B v : V) :
    bfDensity W J gravity coupling F (B + t • v) =
      bfDensity W J gravity coupling F B +
        t * W v (F - coupling ^ 2 • J B) -
        coupling ^ 2 / 2 * t ^ 2 * W v (J v) := by
  have cross : W B (J v) = W v (J B) := (hadj B v).symm.trans (hsym _ _)
  simp only [bfDensity, map_add, map_smul, map_sub, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, cross]
  ring
private theorem bf_stationary_equation (W : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (hn : ∀ x, (∀ v, W v x = 0) → x = 0) (g : ℝ) (F B : V) :
    bfStationary W J g F B ↔ g ^ 2 • J B = F := by
  constructor
  · intro h
    exact (sub_eq_zero.mp (hn _ h)).symm
  · intro h v
    change W v (F - g ^ 2 • J B) = 0
    rw [h, sub_self, map_zero]
def bfCritical (J : V →ₗ[ℝ] V) (s g : ℝ) (F : V) : V :=
  (s / g ^ 2) • J F
theorem bf_stationary_iff (W : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (hn : ∀ x, (∀ v, W v x = 0) → x = 0)
    (s g : ℝ) (hs : s ^ 2 = 1) (hj : ∀ x, J (J x) = s • x)
    (hg : g ≠ 0) (F B : V) :
    bfStationary W J g F B ↔ B = bfCritical J s g F := by
  have hgg : g ^ 2 ≠ 0 := pow_ne_zero _ hg
  have hcoef : (s / g ^ 2) * (g ^ 2 * s) = 1 := by field_simp; nlinarith
  have hcoef' : g ^ 2 * (s / g ^ 2 * s) = 1 := by rw [← hcoef]; ring
  rw [bf_stationary_equation W J hn]
  constructor
  · intro h
    have h' := congrArg (fun x => (s / g ^ 2) • J x) h
    simpa only [map_smul, hj, smul_smul, ← mul_assoc, mul_assoc,
      hcoef, one_smul, bfCritical] using h'
  · rintro rfl
    simp only [bfCritical, map_smul, hj, smul_smul, hcoef', one_smul]
/-- Exact elimination of the auxiliary field, for either Hodge signature. -/
theorem bf_complete_square (W : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (hsym : ∀ x y, W x y = W y x) (hadj : ∀ x y, W (J x) y = W x (J y))
    (s g gravity : ℝ) (hs : s ^ 2 = 1) (hj : ∀ x, J (J x) = s • x)
    (hg : g ≠ 0) (F B : V) :
    bfDensity W J gravity g F B =
      gravity + s / (2 * g ^ 2) * W F (J F) -
        g ^ 2 / 2 * W (B - bfCritical J s g F) (J (B - bfCritical J s g F)) := by
  have hc : g ^ 2 * (s / g ^ 2 * s) = 1 := by
    field_simp
    nlinarith
  have hcrit : g ^ 2 • J (bfCritical J s g F) = F := by
    simp only [bfCritical, map_smul, hj, smul_smul, hc, one_smul]
  have hlinear : W (bfCritical J s g F) F = s / g ^ 2 * W F (J F) := by
    simp only [bfCritical, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hsym (J F) F]
  have hquad : g ^ 2 * W (bfCritical J s g F) (J (bfCritical J s g F)) =
      W (bfCritical J s g F) F := by
    have h := congrArg (W (bfCritical J s g F)) hcrit
    simpa only [map_smul, smul_eq_mul] using h
  have hv := bf_variation W J hsym hadj gravity g 1 F (bfCritical J s g F)
    (B - bfCritical J s g F)
  rw [one_smul, add_sub_cancel, hcrit, sub_self, map_zero] at hv
  rw [hv]
  simp only [bfDensity] at *
  have hhalf : s / (2 * g ^ 2) * W F (J F) = W (bfCritical J s g F) F / 2 := by
    rw [hlinear]
    ring
  rw [hhalf]
  linarith only [hquad]
theorem bf_zero_coupling (W : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (hn : ∀ x, (∀ v, W v x = 0) → x = 0) (F B : V) :
    bfStationary W J 0 F B ↔ F = 0 := by
  rw [bf_stationary_equation W J hn]
  simp [eq_comm]
end AuxiliaryBF
section MatrixBF
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private theorem matrix_bf_reduction (W J : Matrix ι ι ℝ)
    (hW : Wᵀ = W) (hd : W.det ≠ 0) (s g gravity : ℝ)
    (hs : s ^ 2 = 1) (hj : J ^ 2 = s • 1) (ha : Jᵀ * W = W * J)
    (hg : g ≠ 0) (F B : ι → ℝ) :
    let w := W.toBilin'
    let j := J.mulVecLin
    (bfStationary w j g F B ↔ B = bfCritical j s g F) ∧
      bfDensity w j gravity g F B =
        gravity + s / (2 * g ^ 2) * w F (j F) -
          g ^ 2 / 2 * w (B - bfCritical j s g F) (j (B - bfCritical j s g F)) := by
  dsimp only
  have hsym : ∀ x y, W.toBilin' x y = W.toBilin' y x :=
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr hW).eq
  have hnd := (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hd).2
  have hstar (x : ι → ℝ) : J.mulVecLin (J.mulVecLin x) = s • x := by
    change J *ᵥ (J *ᵥ x) = s • x
    rw [mulVec_mulVec, ← pow_two, hj, smul_mulVec, one_mulVec]
  have hadj (x y : ι → ℝ) : W.toBilin' (J.mulVecLin x) y =
      W.toBilin' x (J.mulVecLin y) := by
    simp only [Matrix.toBilin'_apply', Matrix.mulVecLin_apply]
    rw [← vecMul_transpose J x, dotProduct_mulVec, vecMul_vecMul, ha,
      ← dotProduct_mulVec, ← mulVec_mulVec]
  exact ⟨bf_stationary_iff _ _ hnd s g hs hstar hg F B,
    bf_complete_square _ _ hsym hadj s g gravity hs hstar hg F B⟩
def colorWedge (κ : Matrix ι ι ℝ) : Matrix (Urbantke.PairIndex × ι) (Urbantke.PairIndex × ι) ℝ :=
  Urbantke.W ℝ ⊗ₖ κ
def colorHodge (metric : Metric4 ℝ) : Matrix (Urbantke.PairIndex × ι) (Urbantke.PairIndex × ι) ℝ :=
  realHodge metric ⊗ₖ (1 : Matrix ι ι ℝ)
theorem urbantke_bf_yang_mills (metric : Metric4 ℝ) (hm : metricᵀ = metric)
    (hd : metric.det ≠ 0) (κ : Matrix ι ι ℝ) (hk : κᵀ = κ) (hκ : κ.det ≠ 0)
    (g gravity : ℝ) (hg : g ≠ 0) (F B : Urbantke.PairIndex × ι → ℝ) :
    let w := (colorWedge κ).toBilin'
    let j := (colorHodge (ι := ι) metric).mulVecLin
    let s := metricSign metric
    (bfStationary w j g F B ↔ B = bfCritical j s g F) ∧
      bfDensity w j gravity g F B =
        gravity + s / (2 * g ^ 2) * w F (j F) -
          g ^ 2 / 2 * w (B - bfCritical j s g F) (j (B - bfCritical j s g F)) := by
  obtain ⟨_, hsign, hsq, hadj⟩ := real_hodge_structure metric hm hd
  have hw : (Urbantke.W ℝ).det ≠ 0 :=
    Matrix.det_ne_zero_of_left_inverse (B := Urbantke.W ℝ) (wedge_sq ℝ)
  apply matrix_bf_reduction
  · unfold colorWedge
    rw [← kroneckerMap_transpose, wedge_transpose, hk]
  · simp [colorWedge, det_kronecker, hw, hκ]
  · rcases hsign with h | h <;> rw [h] <;> norm_num
  · rw [colorHodge, pow_two, ← mul_kronecker_mul, ← pow_two, hsq, one_mul,
      smul_kronecker, one_kronecker_one]
  · unfold colorHodge colorWedge
    rw [← kroneckerMap_transpose, transpose_one, ← mul_kronecker_mul,
      ← mul_kronecker_mul, one_mul, mul_one, hadj]
  · exact hg
theorem urbantke_bf_on_shell (metric : Metric4 ℝ) (hm : metricᵀ = metric)
    (hd : metric.det ≠ 0) (κ : Matrix ι ι ℝ) (hk : κᵀ = κ) (hκ : κ.det ≠ 0)
    (g gravity : ℝ) (hg : g ≠ 0) (F : Urbantke.PairIndex × ι → ℝ) :
    let w := (colorWedge κ).toBilin'
    let j := (colorHodge (ι := ι) metric).mulVecLin
    let B := bfCritical j (metricSign metric) g F
    bfDensity w j gravity g F B =
      if metric.det < 0 then gravity - 1 / (2 * g ^ 2) * w F (j F)
      else gravity + 1 / (2 * g ^ 2) * w F (j F) := by
  dsimp only
  rw [(urbantke_bf_yang_mills metric hm hd κ hk hκ g gravity hg F _).2]
  simp only [sub_self, map_zero, mul_zero, sub_zero, metricSign]
  split <;> ring
end MatrixBF
end D5.S3.Geometry.Lorentz.UnifiedCornerBF4D
