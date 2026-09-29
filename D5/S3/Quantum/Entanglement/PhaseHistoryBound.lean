/- GID: D5/S3/Quantum/Entanglement/PhaseHistoryBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/PhaseHistoryBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual sequential source moments and a common-center phase-history operator bound. -/

import D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Order.Field.GeomSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder
open Complex
namespace D5.S3.Quantum.Entanglement.PhaseHistoryBound

/-- False and true encode the fixed source basis 0 and 1. -/
abbrev Bit := Bool

def bit (i : Bit) : ℝ := if i then 1 else 0

def memory (p : ℝ) (i j : Bit) : ℝ :=
  if i then (if j then 0 else 1) else (if j then Real.sqrt p else Real.sqrt (1-p))

def transition (p : ℝ) (i j : Bit) : ℝ :=
  if i then (if j then 0 else 1) else (if j then p else 1-p)

def step (p γ : ℝ) : Matrix (Bit × Bit) Bit ℂ := fun x i =>
  if x.1 = i then Complex.exp (Complex.I * ((γ * bit i : ℝ) : ℂ)) * memory p i x.2 else 0

/-- A length-n emission path retains n archive bits and the final memory bit. -/
@[reducible] def Path : ℕ → Type
  | 0 => Bit
  | n+1 => Bit × Path n

instance pathFintype : (n : ℕ) → Fintype (Path n)
  | 0 => inferInstanceAs (Fintype Bit)
  | n+1 => by letI := pathFintype n; exact inferInstanceAs (Fintype (Bit × Path n))

instance pathDecidableEq : (n : ℕ) → DecidableEq (Path n)
  | 0 => inferInstanceAs (DecidableEq Bit)
  | n+1 => @instDecidableEqProd Bit (Path n) inferInstance (pathDecidableEq n)

def head : (n : ℕ) → Path n → Bit
  | 0, x => x
  | _+1, x => x.1

def observed : (n : ℕ) → Path n → ℕ → ℝ
  | 0, x, _ => bit x
  | _+1, x, 0 => bit x.1
  | n+1, x, t+1 => observed n x.2 t

def pathMass (p : ℝ) : (n : ℕ) → Path n → ℝ
  | 0, _ => 1
  | n+1, x => transition p x.1 (head n x.2) * pathMass p n x.2

def pathAmplitude (p : ℝ) (φ : ℕ → ℝ) : (n t : ℕ) → Path n → ℂ
  | 0, _, _ => 1
  | n+1, t, x => Complex.exp (Complex.I * ((φ t * bit x.1 : ℝ) : ℂ)) *
      memory p x.1 (head n x.2) * pathAmplitude p φ n (t+1) x.2

/-- Full archive-and-memory coefficients; at zero length this is the identity. -/
def source (p : ℝ) (φ : ℕ → ℝ) (n t : ℕ) : Matrix (Path n) Bit ℂ :=
  fun x i => if head n x = i then pathAmplitude p φ n t x else 0

def expectation (p : ℝ) (n : ℕ) (i : Bit) (f : Path n → ℝ) : ℝ :=
  ∑ x, if head n x = i then pathMass p n x * f x else 0

def mean (p : ℝ) (i : Bit) (t : ℕ) : ℝ :=
  p/(1+p) + (bit i-p/(1+p)) * (-p)^t

def register : (n : ℕ) → Path n ≃ ((Fin n → Bit) × Bit)
  | 0 =>
    { toFun := fun i => (Fin.elim0, i)
      invFun := fun x => x.2
      left_inv := fun _ => rfl
      right_inv := fun x => by ext j; exact Fin.elim0 j; rfl }
  | n+1 =>
    (Equiv.refl Bit).prodCongr (register n) |>.trans
      (D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.headRest n).symm

open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit in
/-- One common memory circuit realizes these coefficients at every length. Its Born weights
are normalized and have the exact nonstationary mean and two-time covariance. -/
theorem actual_source_moments (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (φ : ℕ → ℝ) :
    ∃ U : ℕ → Unitary (Bit × Bit),
      (∀ t i j k, U t (basis (false, i)) (j,k) = step p (φ t) (j,k) i) ∧
      (∀ n t i x, circuit U n t (blankState false n i) (register n x) =
        source p φ n t x i) ∧
      (∀ n t i x, ‖source p φ n t x i‖^2 =
        if head n x = i then pathMass p n x else 0) ∧
      (∀ n i, expectation p n i (fun _ => 1) = 1) ∧
      (∀ n i s, s ≤ n → expectation p n i (fun x => observed n x s) = mean p i s) ∧
      (∀ n i s t, s ≤ t → t ≤ n →
        expectation p n i (fun x => observed n x s * observed n x t) -
          mean p i s * mean p i t =
          (-p)^(t-s) * mean p i s * (1-mean p i s)) := by
  classical
  have hmem (i j : Bit) : memory p i j ^ 2 = transition p i j := by
    cases i <;> cases j <;> simp [memory, transition, Real.sq_sqrt hp.le,
      Real.sq_sqrt (sub_nonneg.mpr hp1.le)]
  have hrows (i : Bit) : ∑ j, transition p i j = 1 := by
    cases i <;> simp [Fintype.sum_bool, transition]
  have hstep (γ : ℝ) : (step p γ).conjTranspose * step p γ = 1 := by
    have he : star (Complex.exp (Complex.I * (γ : ℂ))) *
        Complex.exp (Complex.I * (γ : ℂ)) = 1 := by
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp
    ext i j
    cases i <;> cases j <;>
      simp [step, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        Matrix.one_apply, memory, bit, Complex.star_def, ← Complex.ofReal_mul,
        Real.mul_self_sqrt hp.le, Real.mul_self_sqrt (sub_nonneg.mpr hp1.le)]
    simpa only [Complex.star_def] using he
  have hs0 (i : Bit) (f : Path 0 → ℝ) : expectation p 0 i f = f i := by
    change (∑ x : Bit, if x = i then 1 * f x else 0) = f i
    simp
  have hs (n : ℕ) (i : Bit) (f : Path (n+1) → ℝ) :
      expectation p (n+1) i f =
        ∑ j : Bit, transition p i j * expectation p n j (fun x => f (i,x)) := by
    change (∑ x : Bit × Path n, if x.1 = i then
      (transition p x.1 (head n x.2) * pathMass p n x.2) * f x else 0) = _
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    simp_rw [expectation, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    cases hh : head n x <;> simp [hh, Fintype.sum_bool, mul_assoc]
  have hnorm (n : ℕ) (i : Bit) : expectation p n i (fun _ => 1) = 1 := by
    induction n generalizing i with
    | zero => exact hs0 i _
    | succ n ih => rw [hs]; simp_rw [ih, mul_one]; exact hrows i
  have hlinear (n : ℕ) (i : Bit) (a b : ℝ) (f g : Path n → ℝ) :
      expectation p n i (fun x => a * f x + b * g x) =
        a * expectation p n i f + b * expectation p n i g := by
    simp only [expectation, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  have hconst (n : ℕ) (i : Bit) (a : ℝ) :
      expectation p n i (fun _ => a) = a := by
    have h := hlinear n i a 0 (fun _ => 1) (fun _ => 0)
    simpa [hnorm] using h
  have hmean (n : ℕ) (i : Bit) (s : ℕ) (hsn : s ≤ n) :
      expectation p n i (fun x => observed n x s) = mean p i s := by
    induction n generalizing i s with
    | zero =>
      have hz : s = 0 := by omega
      subst s
      simp [hs0, observed, mean]
    | succ n ih =>
      cases s with
      | zero =>
        rw [hs]
        simp only [observed]
        simp_rw [hconst]
        rw [← Finset.sum_mul, hrows]
        simp [mean]
      | succ s =>
        rw [hs]
        simp only [observed]
        simp_rw [ih _ s (by omega)]
        have hd : 1+p ≠ 0 := by positivity
        cases i <;> simp [Fintype.sum_bool, transition, mean, bit, pow_succ] <;>
          field_simp <;> ring
  have hat0 (n : ℕ) (x : Path n) : observed n x 0 = bit (head n x) := by
    cases n <;> rfl
  have hscale (n : ℕ) (i : Bit) (a : ℝ) (f : Path n → ℝ) :
      expectation p n i (fun x => a * f x) = a * expectation p n i f := by
    simpa using hlinear n i a 0 f (fun _ => 0)
  have htwo (n : ℕ) (i : Bit) (s t : ℕ) (hst : s ≤ t) (htn : t ≤ n) :
      expectation p n i (fun x => observed n x s * observed n x t) =
        mean p i s * (p/(1+p) + (1-p/(1+p)) * (-p)^(t-s)) := by
    induction s generalizing n i t with
    | zero =>
      have hh : expectation p n i (fun x => observed n x 0 * observed n x t) =
          bit i * expectation p n i (fun x => observed n x t) := by
        rw [← hscale]
        unfold expectation
        apply Finset.sum_congr rfl
        intro x _
        split_ifs with hx
        · dsimp only; rw [hat0, hx]
        · rfl
      rw [hh, hmean n i t htn]
      cases i <;> simp [mean, bit]
    | succ s ih =>
      cases n with
      | zero => omega
      | succ n =>
        cases t with
        | zero => omega
        | succ t =>
          rw [hs]
          simp only [observed]
          simp_rw [ih n _ t (by omega) (by omega)]
          simp only [Nat.succ_sub_succ_eq_sub]
          simp_rw [← mul_assoc]
          rw [← Finset.sum_mul]
          have hrec : (∑ j : Bit, transition p i j * mean p j s) = mean p i (s+1) := by
            have h := hmean (n+1) i (s+1) (by omega)
            rw [hs] at h
            simpa only [observed, hmean n _ s (by omega)] using h
          rw [hrec]
  have hcov (n : ℕ) (i : Bit) (s t : ℕ) (hst : s ≤ t) (htn : t ≤ n) :
      expectation p n i (fun x => observed n x s * observed n x t) -
        mean p i s * mean p i t = (-p)^(t-s) * mean p i s * (1-mean p i s) := by
    rw [htwo n i s t hst htn]
    have ht : (-p)^t = (-p)^s * (-p)^(t-s) := by
      rw [← pow_add, Nat.add_sub_of_le hst]
    unfold mean
    rw [ht]
    ring
  have hamp (n t : ℕ) (x : Path n) : ‖pathAmplitude p φ n t x‖^2 = pathMass p n x := by
    induction n generalizing t with
    | zero => simp [pathAmplitude, pathMass]
    | succ n ih =>
      simp only [pathAmplitude, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul,
        Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, hmem, ih, pathMass]
  have hmass (n t : ℕ) (i : Bit) (x : Path n) : ‖source p φ n t x i‖^2 =
      if head n x = i then pathMass p n x else 0 := by
    unfold source
    split_ifs <;> simp [hamp]
  let V (t : ℕ) := matrixIsometry (step p (φ t)) (hstep (φ t))
  have hex (t : ℕ) : ∃ U : Unitary (Bit × Bit), ∀ x,
      U (coordinateEmbedding (blankInjection false (Function.Embedding.refl Bit)) x) = V t x :=
    exists_unitary_agree (coordinateEmbedding (blankInjection false (Function.Embedding.refl Bit))) (V t)
  choose U hU using hex
  have hUb (t : ℕ) (i j k : Bit) : U t (basis (false,i)) (j,k) = step p (φ t) (j,k) i := by
    have h := congrArg (fun z : Space (Bit × Bit) => z (j,k)) (hU t (basis i))
    simpa only [basis, coordinate_embedding_basis, blankInjection, Function.Embedding.refl_apply,
      matrix_isometry_basis, Function.Embedding.coeFn_mk, V] using h
  have hcoeff (n t : ℕ) (i : Bit) (x : Path n) :
      circuit U n t (blankState false n i) (register n x) = source p φ n t x i := by
    induction n generalizing t i with
    | zero =>
      simp [circuit, blankState, register, source, head, pathAmplitude, basis_apply,
        (Subsingleton.elim (Fin.elim0 : Fin 0 → Bit) (fun _ => false))]
      rfl
    | succ n ih =>
      rcases x with ⟨j,x⟩
      change circuit U (n+1) t (blankState false (n+1) i)
        (Fin.cons j (register n x).1, (register n x).2) = _
      rw [circuit_blank_succ]
      simp only [Fin.cons_zero, Fin.tail_cons]
      simp_rw [hUb, ih]
      by_cases hji : j = i
      · subst j
        simp only [step, source, head, pathAmplitude, if_pos rfl]
        change (∑ k : Bit, (Complex.exp (Complex.I * ((φ t * bit i : ℝ) : ℂ)) *
          (memory p i k : ℂ)) * (if head n x = k then pathAmplitude p φ n (t+1) x else 0)) =
          (Complex.exp (Complex.I * ((φ t * bit i : ℝ) : ℂ)) *
            memory p i (head n x)) * pathAmplitude p φ n (t+1) x
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      · simp [step, source, head, pathAmplitude, hji]
  exact ⟨U, hUb, hcoeff, hmass, hnorm, hmean, hcov⟩
def historyConstant (p : ℝ) : ℝ := ((1+p)/(1-p) + 1/(1-p^2))/4

def phaseSum (δ : ℕ → ℝ) (n t : ℕ) (x : Path n) : ℝ :=
  ∑ s : Fin n, δ (t+s.val) * observed n x s.val

def center (p : ℝ) (δ : ℕ → ℝ) (n : ℕ) : ℝ :=
  p/(1+p) * ∑ s : Fin n, δ s.val +
    (1/2-p/(1+p)) * ∑ s : Fin n, δ s.val * (-p)^s.val

def error (p θ : ℝ) (φ : ℕ → ℝ) (n : ℕ) (b : ℝ) : Matrix (Path n) Bit ℂ :=
  source p (fun _ => θ) n 0 - Complex.exp (Complex.I * (b : ℂ)) • source p φ n 0

/-- A single phase center controls both source columns and every finite reference.
The discrepancies may be any real lifts modulo 2π; the bound uses their squared energy. -/
theorem phase_history_bound (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (n : ℕ) (θ : ℝ) (φ δ : ℕ → ℝ)
    (hlift : ∀ t < n, ∃ k : ℤ, θ - φ t = δ t + k * (2 * Real.pi)) :
    ((historyConstant p * ∑ s : Fin n, δ s.val ^ 2 : ℝ) • (1 : Matrix Bit Bit ℂ) -
      (error p θ φ n (center p δ n)).conjTranspose * error p θ φ n (center p δ n)).PosSemidef ∧
    ∀ (J : Type*) [Fintype J] [DecidableEq J],
      ((historyConstant p * ∑ s : Fin n, δ s.val ^ 2 : ℝ) • (1 : Matrix (J × Bit) (J × Bit) ℂ) -
        (Matrix.kronecker (1 : Matrix J J ℂ) (error p θ φ n (center p δ n))).conjTranspose *
        Matrix.kronecker (1 : Matrix J J ℂ) (error p θ φ n (center p δ n))).PosSemidef := by
  classical
  suffices hbase : ((historyConstant p * ∑ s : Fin n, δ s.val ^ 2 : ℝ) • (1 : Matrix Bit Bit ℂ) -
      (error p θ φ n (center p δ n)).conjTranspose * error p θ φ n (center p δ n)).PosSemidef by
    refine ⟨hbase, ?_⟩
    intro J _ _
    have h := (Matrix.PosSemidef.one : (1 : Matrix J J ℂ).PosSemidef).kronecker hbase
    have he (A B : Matrix Bit Bit ℂ) :
        Matrix.kronecker (1 : Matrix J J ℂ) (A-B) =
          Matrix.kronecker (1 : Matrix J J ℂ) A - Matrix.kronecker (1 : Matrix J J ℂ) B := by
      ext i j
      simp [Matrix.kronecker_apply, mul_sub]
    simp only [Matrix.kronecker] at he ⊢
    simpa only [he, Matrix.kronecker_smul, Matrix.one_kronecker_one,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul] using h
  by_cases hn : n = 0
  · subst n
    have hz : error p θ φ 0 (center p δ 0) = 0 := by
      ext x i
      simp [error, center, source, pathAmplitude]
    simp [hz, Matrix.PosSemidef.zero]
  have hδ (t : ℕ) (ht : t < n) : Complex.exp (Complex.I * (θ : ℂ)) =
      Complex.exp (Complex.I * (δ t : ℂ)) * Complex.exp (Complex.I * (φ t : ℂ)) := by
    obtain ⟨k,hk⟩ := hlift t ht
    have he : Complex.I * (θ : ℂ) = Complex.I * (δ t : ℂ) + Complex.I * (φ t : ℂ) +
        (k : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [show θ = δ t + φ t + (k : ℝ) * (2 * Real.pi) by linarith]
      push_cast
      ring
    rw [he, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  obtain ⟨U, hU, hcoeff, hmass, hnorm, hmean, hcov⟩ := actual_source_moments p hp hp1 φ
  have hmassnonneg (m : ℕ) (x : Path m) : 0 ≤ pathMass p m x := by
    induction m with
    | zero => simp [pathMass]
    | succ m ih =>
      apply mul_nonneg _ (ih x.2)
      cases x.1 <;> cases head m x.2 <;> simp [transition, hp.le, hp1.le]
  have hlin (i : Bit) (a b : ℝ) (f g : Path n → ℝ) :
      expectation p n i (fun x => a * f x + b * g x) =
        a * expectation p n i f + b * expectation p n i g := by
    simp only [expectation, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  have hscale (i : Bit) (a : ℝ) (f : Path n → ℝ) :
      expectation p n i (fun x => a * f x) = a * expectation p n i f := by
    simpa using hlin i a 0 f (fun _ => 0)
  have hconst (i : Bit) (a : ℝ) : expectation p n i (fun _ => a) = a := by
    simpa [hnorm] using hscale i a (fun _ => 1)
  have hsum (i : Bit) {ι : Type} (s : Finset ι) (f : ι → Path n → ℝ) :
      expectation p n i (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, expectation p n i (f j) := by
    simp only [expectation, Finset.mul_sum, Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp_all
  have hmono (i : Bit) (f g : Path n → ℝ) (h : ∀ x, f x ≤ g x) :
      expectation p n i f ≤ expectation p n i g := by
    apply Finset.sum_le_sum
    intro x _
    split_ifs
    · exact mul_le_mul_of_nonneg_left (h x) (hmassnonneg n x)
    · rfl
  have hobs (m : ℕ) (x : Path m) (s : ℕ) :
      0 ≤ observed m x s ∧ observed m x s ≤ 1 := by
    induction m generalizing s with
    | zero => cases x <;> simp [observed, bit]
    | succ m ih =>
      cases s with
      | zero => rcases x with ⟨a,x⟩; cases a <;> simp [observed, bit]
      | succ s => exact ih x.2 s
  have hq (i : Bit) (s : Fin n) : 0 ≤ mean p i s.val ∧ mean p i s.val ≤ 1 := by
    rw [← hmean n i s.val (Nat.le_of_lt s.isLt)]
    constructor
    · simpa [hconst] using hmono i (fun _ => 0) (fun x => observed n x s.val)
        (fun x => (hobs n x s.val).1)
    · simpa [hconst] using hmono i (fun x => observed n x s.val) (fun _ => 1)
        (fun x => (hobs n x s.val).2)
  let kernel (s t : Fin n) : ℝ := p ^ (max s.val t.val - min s.val t.val)
  have hksym (s t : Fin n) : kernel s t = kernel t s := by simp [kernel, max_comm, min_comm]
  have hkpos (s t : Fin n) : 0 ≤ kernel s t := pow_nonneg hp.le _
  have hrow (s : Fin n) : ∑ t : Fin n, kernel s t ≤ (1+p)/(1-p) := by
    have hside (A : Finset (Fin n)) (f : Fin n → ℕ)
        (hinj : Set.InjOn f A) (hmem : ∀ t ∈ A, f t ∈ Finset.Ico 1 (n+1)) :
        ∑ t ∈ A, p^(f t) ≤ p/(1-p) := by
      rw [← Finset.sum_image hinj]
      calc
        _ ≤ ∑ k ∈ Finset.Ico 1 (n+1), p^k :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (by intro k hk; obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hk; exact hmem t ht)
            (fun k _ _ => pow_nonneg hp.le k)
        _ ≤ p/(1-p) := by simpa using
          (geom_sum_Ico_le_of_lt_one (m := 1) (n := n+1) hp.le hp1)
    let L := Finset.univ.filter (fun t : Fin n => t.val < s.val)
    let R := Finset.univ.filter (fun t : Fin n => s.val < t.val)
    have hL : ∑ t ∈ L, kernel s t ≤ p/(1-p) := by
      have he : ∀ t ∈ L, kernel s t = p^(s.val-t.val) := by
        intro t ht
        have hts : t.val < s.val := (Finset.mem_filter.mp ht).2
        simp [kernel, max_eq_left hts.le, min_eq_right hts.le]
      simp_rw [Finset.sum_congr rfl he]
      refine hside _ _ ?_ ?_
      · intro a ha b hb hab
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        apply Fin.ext
        dsimp only at hab
        omega
      · intro t ht
        have hts := (Finset.mem_filter.mp ht).2
        simp only [Finset.mem_Ico]
        constructor <;> omega
    have hR : ∑ t ∈ R, kernel s t ≤ p/(1-p) := by
      have he : ∀ t ∈ R, kernel s t = p^(t.val-s.val) := by
        intro t ht
        have hst : s.val < t.val := (Finset.mem_filter.mp ht).2
        simp [kernel, max_eq_right hst.le, min_eq_left hst.le]
      simp_rw [Finset.sum_congr rfl he]
      refine hside _ _ ?_ ?_
      · intro a ha b hb hab
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        apply Fin.ext
        dsimp only at hab
        omega
      · intro t ht
        have hst := (Finset.mem_filter.mp ht).2
        simp only [Finset.mem_Ico]
        constructor <;> omega
    have hsplit : (∑ t : Fin n, kernel s t) =
        (∑ t ∈ L, kernel s t) + 1 + ∑ t ∈ R, kernel s t := by
      have hsone : (1 : ℝ) = ∑ t : Fin n, if t = s then kernel s t else 0 := by
        simp [kernel]
      rw [hsone]
      simp only [L, R, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      rcases lt_trichotomy t.val s.val with h | h | h
      · have hne : t ≠ s := by intro hh; subst t; omega
        simp [h, hne, show ¬s.val < t.val by omega]
      · have he : t = s := Fin.ext h
        subst t
        simp
      · have hne : t ≠ s := by intro hh; subst t; omega
        simp [h, hne, show ¬t.val < s.val by omega]
    rw [hsplit]
    have hd : 1-p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
    have he : (1+p)/(1-p) = p/(1-p) + 1 + p/(1-p) := by field_simp; ring
    rw [he]
    linarith
  let cov (i : Bit) (s t : Fin n) : ℝ :=
    expectation p n i (fun x => observed n x s.val * observed n x t.val) -
      mean p i s.val * mean p i t.val
  have hcabs (i : Bit) (s t : Fin n) : |cov i s t| ≤ kernel s t / 4 := by
    have hord (s t : Fin n) (hst : s.val ≤ t.val) : |cov i s t| ≤ kernel s t / 4 := by
      have hqs := hq i s
      have hv0 : 0 ≤ mean p i s.val * (1-mean p i s.val) := mul_nonneg hqs.1 (sub_nonneg.mpr hqs.2)
      have hv : mean p i s.val * (1-mean p i s.val) ≤ 1/4 := by nlinarith [sq_nonneg (mean p i s.val - 1/2)]
      dsimp only [cov]
      rw [hcov n i s.val t.val hst (Nat.le_of_lt t.isLt)]
      rw [mul_assoc, abs_mul, abs_pow, abs_neg, abs_of_nonneg hp.le, abs_of_nonneg hv0]
      have hk : kernel s t = p^(t.val-s.val) := by simp [kernel, max_eq_right hst, min_eq_left hst]
      rw [hk]
      nlinarith [mul_le_mul_of_nonneg_left hv (pow_nonneg hp.le (t.val-s.val))]
    rcases le_total s.val t.val with hst | hts
    · exact hord s t hst
    · have he : cov i s t = cov i t s := by simp only [cov, mul_comm]
      rw [he, hksym]
      exact hord t s hts
  have hweighted (i : Bit) :
      (∑ s : Fin n, ∑ t : Fin n, δ s.val * δ t.val * cov i s t) ≤
        ((1+p)/(1-p))/4 * ∑ s : Fin n, δ s.val^2 := by
    have hpoint (s t : Fin n) : δ s.val * δ t.val * cov i s t ≤
        (δ s.val^2 + δ t.val^2) / 8 * kernel s t := by
      have hpair : |δ s.val * δ t.val| ≤ (δ s.val^2 + δ t.val^2)/2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|δ s.val| - |δ t.val|), sq_abs (δ s.val), sq_abs (δ t.val)]
      calc
        _ ≤ |δ s.val * δ t.val * cov i s t| := le_abs_self _
        _ = |δ s.val * δ t.val| * |cov i s t| := abs_mul _ _
        _ ≤ |δ s.val * δ t.val| * (kernel s t / 4) :=
          mul_le_mul_of_nonneg_left (hcabs i s t) (abs_nonneg _)
        _ ≤ ((δ s.val^2 + δ t.val^2)/2) * (kernel s t / 4) :=
          mul_le_mul_of_nonneg_right hpair (div_nonneg (hkpos s t) (by norm_num))
        _ = _ := by ring
    have hswap : (∑ s : Fin n, ∑ t : Fin n, δ t.val^2 * kernel s t) =
        ∑ s : Fin n, ∑ t : Fin n, δ s.val^2 * kernel s t := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      rw [hksym]
    have he : (∑ s : Fin n, ∑ t : Fin n, (δ s.val^2 + δ t.val^2)/8 * kernel s t) =
        (1/4) * ∑ s : Fin n, δ s.val^2 * ∑ t : Fin n, kernel s t := by
      calc
        _ = (1/8) * (∑ s : Fin n, ∑ t : Fin n, δ s.val^2 * kernel s t) +
          (1/8) * (∑ s : Fin n, ∑ t : Fin n, δ t.val^2 * kernel s t) := by
            simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro s _
            apply Finset.sum_congr rfl
            intro t _
            ring
        _ = _ := by
          rw [hswap]
          simp only [← Finset.mul_sum]
          ring
    calc
      _ ≤ ∑ s : Fin n, ∑ t : Fin n, (δ s.val^2 + δ t.val^2)/8 * kernel s t := by
        apply Finset.sum_le_sum; intro s _
        apply Finset.sum_le_sum; intro t _
        exact hpoint s t
      _ = _ := he
      _ ≤ (1/4) * ∑ s : Fin n, δ s.val^2 * ((1+p)/(1-p)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro s _
        exact mul_le_mul_of_nonneg_left (hrow s) (sq_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hEsub (i : Bit) (f g : Path n → ℝ) :
      expectation p n i (fun x => f x - g x) = expectation p n i f - expectation p n i g := by
    simpa [sub_eq_add_neg] using hlin i 1 (-1) f g
  have hscaleR (i : Bit) (a : ℝ) (f : Path n → ℝ) :
      expectation p n i (fun x => f x * a) = expectation p n i f * a := by
    simpa only [mul_comm] using hscale i a f
  let fluct (i : Bit) (s : Fin n) (x : Path n) := observed n x s.val - mean p i s.val
  have hfluct (i : Bit) (s t : Fin n) : expectation p n i (fun x => fluct i s x * fluct i t x) = cov i s t := by
    simp only [fluct, sub_mul, mul_sub]
    rw [hEsub, hEsub, hEsub, hscale, hscaleR, hconst,
      hmean n i s.val (Nat.le_of_lt s.isLt), hmean n i t.val (Nat.le_of_lt t.isLt)]
    dsimp only [cov]
    ring
  have hvar (i : Bit) :
      expectation p n i (fun x => (∑ s : Fin n, δ s.val * fluct i s x)^2) ≤
        ((1+p)/(1-p))/4 * ∑ s : Fin n, δ s.val^2 := by
    have he (x : Path n) : (∑ s : Fin n, δ s.val * fluct i s x)^2 =
        ∑ s : Fin n, ∑ t : Fin n, (δ s.val * δ t.val) * (fluct i s x * fluct i t x) := by
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring
    simp only [he]
    rw [hsum]
    simp only [hsum, hscale, hfluct]
    exact hweighted i
  let H : ℝ := ∑ s : Fin n, δ s.val * (-p)^s.val
  have hH : H^2 ≤ (1/(1-p^2)) * ∑ s : Fin n, δ s.val^2 := by
    have hp2 : p^2 < 1 := by nlinarith
    have hgeom : (∑ s : Fin n, ((-p)^s.val)^2) ≤ 1/(1-p^2) := by
      have he (s : ℕ) : ((-p)^s)^2 = (p^2)^s := by rw [← pow_mul, Nat.mul_comm, pow_mul, neg_sq]
      simp_rw [he]
      rw [Fin.sum_univ_eq_sum_range]
      simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := n) (sq_nonneg p) hp2)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun s : Fin n => δ s.val) (fun s => (-p)^s.val)
    apply hcs.trans
    calc
      _ ≤ (∑ s : Fin n, δ s.val^2) * (1/(1-p^2)) :=
        mul_le_mul_of_nonneg_left hgeom (Finset.sum_nonneg (fun s _ => sq_nonneg (δ s.val)))
      _ = _ := mul_comm _ _
  have hcentered (i : Bit) :
      expectation p n i (fun x => (phaseSum δ n 0 x - center p δ n)^2) ≤
        historyConstant p * ∑ s : Fin n, δ s.val^2 := by
    have hm : (∑ s : Fin n, δ s.val * mean p i s.val) - center p δ n = (bit i-1/2)*H := by
      have hms : (∑ s : Fin n, δ s.val * mean p i s.val) =
          p/(1+p) * (∑ s : Fin n, δ s.val) + (bit i-p/(1+p))*H := by
        calc
          _ = ∑ s : Fin n, (p/(1+p)*δ s.val + (bit i-p/(1+p))*(δ s.val*(-p)^s.val)) := by
            apply Finset.sum_congr rfl
            intro s _
            dsimp only [mean]
            ring
          _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [hms]
      dsimp only [center]
      change _ - (p/(1+p) * (∑ s : Fin n, δ s.val) + (1/2-p/(1+p))*H) = _
      ring
    have he (x : Path n) : phaseSum δ n 0 x - center p δ n =
        (∑ s : Fin n, δ s.val * fluct i s x) + (bit i-1/2)*H := by
      simp only [fluct, mul_sub, Finset.sum_sub_distrib, phaseSum, zero_add]
      linarith [hm]
    have hzero : expectation p n i (fun x => ∑ s : Fin n, δ s.val * fluct i s x) = 0 := by
      simp_rw [hsum, hscale, fluct, hEsub, hconst]
      have hh (s : Fin n) := hmean n i s.val (Nat.le_of_lt s.isLt)
      simp [hh]
    have hexp : expectation p n i (fun x => (phaseSum δ n 0 x - center p δ n)^2) =
        expectation p n i (fun x => (∑ s : Fin n, δ s.val * fluct i s x)^2) + H^2/4 := by
      simp_rw [he, add_sq]
      have hadd (f g : Path n → ℝ) : expectation p n i (fun x => f x + g x) =
          expectation p n i f + expectation p n i g := by simpa using hlin i 1 1 f g
      rw [hadd, hadd]
      simp only [mul_assoc]
      rw [hscale, hscaleR, hzero, hconst]
      cases i <;> simp [bit] <;> ring
    rw [hexp]
    have hv := hvar i
    unfold historyConstant
    nlinarith [hH]
  have hphase (t : ℕ) (ht : t < n) (i : Bit) :
      Complex.exp (Complex.I * ((θ * bit i : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((δ t * bit i : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((φ t * bit i : ℝ) : ℂ)) := by
    cases i <;> simp [bit, hδ t ht]
  have hZ (m t : ℕ) (x : Path (m+1)) : phaseSum δ (m+1) t x =
      δ t * bit x.1 + phaseSum δ m (t+1) x.2 := by
    simp only [phaseSum, Fin.sum_univ_succ, Fin.val_zero, add_zero,
      observed, Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    rw [show t + (s.val+1) = t+1+s.val by omega]
  have hratio (m t : ℕ) (ht : t+m ≤ n) (x : Path m) :
      pathAmplitude p (fun _ => θ) m t x =
        Complex.exp (Complex.I * (phaseSum δ m t x : ℂ)) * pathAmplitude p φ m t x := by
    induction m generalizing t with
    | zero => simp [pathAmplitude, phaseSum]
    | succ m ih =>
      rw [pathAmplitude, pathAmplitude, ih (t+1) (by omega), hphase t (by omega), hZ]
      push_cast
      rw [mul_add, Complex.exp_add]
      ring
  have hexpbound (z b : ℝ) :
      ‖Complex.exp (Complex.I * (z : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖^2 ≤ (z-b)^2 := by
    have he : Complex.exp (Complex.I * (z : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
        Complex.exp (Complex.I * (b : ℂ)) * (Complex.exp (Complex.I * ((z-b : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    rw [he, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
    have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := z-b)
    have hs := mul_self_le_mul_self (norm_nonneg _) h
    simpa [pow_two] using hs
  let D := error p θ φ n (center p δ n)
  have hcol (i : Bit) : (∑ x : Path n, ‖D x i‖^2) ≤ historyConstant p * ∑ s : Fin n, δ s.val^2 := by
    apply le_trans _ (hcentered i)
    unfold expectation
    apply Finset.sum_le_sum
    intro x _
    dsimp only [D, error]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, source]
    split_ifs with hx
    · rw [hratio n 0 (by omega), ← sub_mul, norm_mul, mul_pow]
      have hm : ‖pathAmplitude p φ n 0 x‖^2 = pathMass p n x := by
        simpa [source] using hmass n 0 (head n x) x
      rw [hm]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right
        (hexpbound (phaseSum δ n 0 x) (center p δ n)) (hmassnonneg n x)
    · simp
  have hgram : D.conjTranspose * D = Matrix.diagonal (fun i => ((∑ x : Path n, ‖D x i‖^2 : ℝ) : ℂ)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst j
      simp only [if_pos rfl, Matrix.conjTranspose_apply, Complex.star_def,
        ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_sum, ite_true]
    · rw [if_neg hij]
      apply Finset.sum_eq_zero
      intro x _
      have hzero : D x i = 0 ∨ D x j = 0 := by
        by_cases hi : head n x = i
        · right
          have hj : head n x ≠ j := by intro hj; exact hij (hi.symm.trans hj)
          simp [D, error, source, hj]
        · left
          simp [D, error, source, hi]
      rcases hzero with h | h <;> simp [Matrix.conjTranspose_apply, h]
  change ((historyConstant p * ∑ s : Fin n, δ s.val^2 : ℝ) • (1 : Matrix Bit Bit ℂ) - D.conjTranspose * D).PosSemidef
  rw [hgram]
  have hd : ((historyConstant p * ∑ s : Fin n, δ s.val^2 : ℝ) • (1 : Matrix Bit Bit ℂ) -
      Matrix.diagonal (fun i => ((∑ x : Path n, ‖D x i‖^2 : ℝ) : ℂ))) =
      Matrix.diagonal (fun i => ((historyConstant p * ∑ s : Fin n, δ s.val^2 - ∑ x : Path n, ‖D x i‖^2 : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  rw [hd, Matrix.posSemidef_diagonal_iff]
  intro i
  exact_mod_cast sub_nonneg.mpr (hcol i)
end D5.S3.Quantum.Entanglement.PhaseHistoryBound
