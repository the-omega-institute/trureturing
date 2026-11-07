/- GID: D5/S3/Fourier/DiaconisMicloUnimodality
   generality: I
   mirror-B: D5/B/S3/Fourier/DiaconisMicloUnimodality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Fourier/DiaconisMicloUnimodality.claim; result=D5/S3/Fourier/DiaconisMicloUnimodality.result; claim=D5/S3/Fourier/DiaconisMicloUnimodality.claim
   digest: A four-speed walk on ZMod 11 refutes absolute-gap unimodality. -/

/-
result: proof_shape: bind-only; escape_witness: none;
admission_basis: open-problem-resolution (#26482; Refuted).
Direct frozen dependencies: D5/S3/Fourier/FullBispectrumStability.dft_translation
  (statement_id: sha256:8dff866332f234c628278128227cb821558ac734f949efdfe1194d60b06ab90a).
All helper proofs have proof_shape: bind-only and escape_witness: none.
Private proof consumers (prerequisite → consumer):
positionSpeed_apply: fourier_intertwine, block_lift.
dft_translate: fourier_intertwine.
dft_sum: fourier_intertwine.
fourier_intertwine: fourier_reduction.
fourier_nonzero: fourier_reduction.
speeds_card: fourier_zero_sum, trivial_block_eq, literal_block_identity, block_lift_mean_zero.
fourier_zero_sum: fourier_reduction.
fourier_reduction: mean_zero_eigenvalue_block.
trivial_block_eq: mean_zero_eigenvalue_block, a_is_mean_zero_eigenvalue.
mean_zero_eigenvalue_block: endpoint_eigenvalue_bound.
block_lift: lifted_eigenvalue.
char_ne_zero: fourier_characteristic_polynomial, char_trace_cyclotomic, trace_fiber, middle_eigenvalue.
literal_block_identity: fourier_characteristic_polynomial, middle_eigenvalue.
literal_characteristic_polynomial: fourier_characteristic_polynomial, middle_eigenvalue.
char_trace_real: fourier_characteristic_polynomial, char_trace_cyclotomic, trace_fiber, middle_eigenvalue.
fourier_characteristic_polynomial: fourier_root.
eigen_det_zero: finite_mean_zero_eigenvalues, fourier_root.
det_zero_eigenvector: middle_eigenvalue.
finite_mean_zero_eigenvalues: endpoint_gap, middle_gap.
real_cyclotomic_ne_zero: cyclotomic_root_windows, cyclotomic_trace_exhaustive.
cyclotomic_interval_sign: cyclotomic_root_windows, middle_eigenvalue.
cyclotomic_root_windows: endpoint_eigenvalue_bound.
cyclotomic_trace_identity: char_trace_cyclotomic.
char_trace_cyclotomic: cyclotomic_trace_exhaustive, endpoint_eigenvalue_bound.
schur_step: schur4_outside.
schur4_outside: block_roots_inside.
endpoint_schur_one_fifth: endpoint_eigenvalue_bound.
endpoint_schur_three_tenths: endpoint_eigenvalue_bound.
value4_block_scaled: block_roots_inside.
block_roots_inside: endpoint_eigenvalue_bound.
middle_signs: middle_real_root.
middle_real_root: middle_eigenvalue.
trace_fiber: trace_mode_injective.
modeIndex_ne_zero: cyclotomic_trace_exhaustive, middle_eigenvalue.
trace_mode_injective: cyclotomic_trace_exhaustive.
cyclotomic_trace_exhaustive: middle_eigenvalue.
block_lift_mean_zero: lifted_eigenvalue.
lifted_eigenvalue: a_is_mean_zero_eigenvalue, middle_eigenvalue.
a_is_mean_zero_eigenvalue: endpoint_gap.
fourier_root: endpoint_eigenvalue_bound.
endpoint_eigenvalue_bound: endpoint_gap.
middle_eigenvalue: middle_gap.
lambdaM_sSup: endpoint_gap, middle_gap.
endpoint_gap: result.
middle_gap: result.
speeds_generate: result.
Proposition-valued private definitions (classified as bind-only declarations):
RootWindow: proof_shape: bind-only; escape_witness: none; consumer: cyclotomic_root_windows, endpoint_schur_one_fifth, endpoint_schur_three_tenths.
Schur4: proof_shape: bind-only; escape_witness: none; consumers: schur4_outside, endpoint_schur_one_fifth, endpoint_schur_three_tenths, block_roots_inside.
The source position-speed and absolute-gap expressions are retained with subtype carriers written in full.
The uniform weight is inlined in lambdaM; proofs use the closed uniformWeight owner through its one-letter specialization.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import D5.S3.Fourier.FullBispectrumStability
import D5.S3.Arith.Congruence.RestrictedSpineConstantPotential
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.Complex
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace D5.S3.Fourier.DiaconisMicloUnimodality

noncomputable section
open scoped BigOperators




def K {G : Type*} [AddGroup G] (S : Finset G) (a : ℝ)
    (v w : {v : G // v ∈ S}) : ℝ :=
  by
    classical
    exact if h : v = w then (1 - a) * (1 / (S.card : ℝ)) + a else (1 - a) * (1 / (S.card : ℝ))

def positionSpeed {G : Type*} [AddGroup G] (S : Finset G)
    (a : ℝ) : Matrix ((G × {v : G // v ∈ S})) ((G × {v : G // v ∈ S})) ℝ :=
  by
    classical
    exact fun p q => if q.1 = p.1 + p.2.1 then K S a p.2 q.2 else 0

def randomWalk {G : Type*} [AddGroup G] (S : Finset G) : Matrix G G ℝ :=
  by
    classical
    exact fun x y => if h : y - x ∈ S then 1 / (S.card : ℝ) else 0


def meanZero {α : Type*} [Fintype α] (w : α → ℝ) (f : α → ℂ) : Prop :=
  ∑ x, (w x : ℂ) * f x = 0

def eigenvaluesMeanZero {α : Type*} [Fintype α]
    (A : Matrix α α ℝ) (w : α → ℝ) : Set ℂ :=
  {θ | ∃ f : α → ℂ,
      (∃ x, f x ≠ 0) ∧ meanZero w f ∧
      ∀ i, (∑ j, (A i j : ℂ) * f j) = θ * f i}

noncomputable def spectralRadiusOnMeanZero {α : Type*} [Fintype α]
    (A : Matrix α α ℝ) (w : α → ℝ) : ℝ :=
  sSup (Set.image (fun θ : ℂ => ‖θ‖) (eigenvaluesMeanZero A w))

noncomputable def spectralGapOnMeanZero {α : Type*} [Fintype α]
    (A : Matrix α α ℝ) (w : α → ℝ) : ℝ :=
  1 - spectralRadiusOnMeanZero A w


noncomputable def lambdaM {G : Type*} [Fintype G] [AddGroup G]
    (S : Finset G) (a : ℝ) : ℝ :=
  by
    classical
    letI : Fintype ((G × {v : G // v ∈ S})) := Fintype.ofFinite _
    exact spectralGapOnMeanZero (positionSpeed S a) (fun (_p : G × {v : G // v ∈ S}) =>
      1 / ((Fintype.card G * S.card : ℕ) : ℝ))

noncomputable def lambdaL {G : Type*} [Fintype G] [AddGroup G]
    (S : Finset G) : ℝ :=
  spectralGapOnMeanZero (randomWalk S) (fun _ => 1 / (Fintype.card G : ℝ))


def claim : Prop :=
  ∀ (G : Type*) [Fintype G] [AddCommGroup G] (S : Finset G),
    2 ≤ S.card →
    (∀ v, v ∈ S → -v ∈ S) →
    AddSubgroup.closure (S : Set G) = ⊤ →
      ∃ a₀ : ℝ,
        0 ≤ a₀ ∧ a₀ ≤ 1 ∧
        MonotoneOn (fun a => lambdaM S a) (Set.Icc 0 a₀) ∧
        AntitoneOn (fun a => lambdaM S a) (Set.Icc a₀ 1) ∧
        ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧
          c₁ * Real.sqrt (lambdaL S) ≤ lambdaM S a₀ ∧
          lambdaM S a₀ ≤ c₂ * Real.sqrt (lambdaL S)

end
end D5.S3.Fourier.DiaconisMicloUnimodality

namespace D5.S3.Fourier.DiaconisMicloUnimodality
noncomputable section
open scoped BigOperators
open Finset


private def speeds : Finset (ZMod 11) := {1, 2, 9, 10}



private noncomputable def fourierBlock (a : ℝ) (k : (ZMod 11)) : Matrix {v : ZMod 11 // v ∈ speeds} {v : ZMod 11 // v ∈ speeds} ℂ :=
  by
    classical
    exact Matrix.diagonal (fun v : {v : ZMod 11 // v ∈ speeds} => ZMod.stdAddChar (v.1 * k)) *
      Matrix.of (fun v w => (K speeds a v w : ℂ))

private theorem positionSpeed_apply (a : ℝ) (f : (ZMod 11 × {v : ZMod 11 // v ∈ speeds}) → ℂ) (x : (ZMod 11)) (v : {v : ZMod 11 // v ∈ speeds}) :
    (∑ q : (ZMod 11 × {v : ZMod 11 // v ∈ speeds}), (positionSpeed speeds a (x,v) q : ℂ) * f q) =
      ∑ w : {v : ZMod 11 // v ∈ speeds}, (K speeds a v w : ℂ) * f (x+v.1,w) := by
  classical
  simp only [positionSpeed,Fintype.sum_prod_type,apply_ite,Complex.ofReal_zero,
    ite_mul,zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

private theorem dft_translate (f : (ZMod 11) → ℂ) (v k : (ZMod 11)) :
    ZMod.dft (fun x => f (x+v)) k =
      ZMod.stdAddChar (v*k) * ZMod.dft f k := by
  simpa only [sub_neg_eq_add, mul_neg, neg_neg, mul_comm] using
    D5.S3.Fourier.FullBispectrumStability.dft_translation f (-v) k

private theorem dft_sum (F : {v : ZMod 11 // v ∈ speeds} → ZMod 11 → ℂ) (k : ZMod 11) :
    ZMod.dft (fun x => ∑ w, F w x) k = ∑ w, ZMod.dft (F w) k := by
  classical
  exact congrFun (map_sum ZMod.dft F Finset.univ) k

private theorem fourier_intertwine (a : ℝ) (f : (ZMod 11 × {v : ZMod 11 // v ∈ speeds}) → ℂ) (θ : ℂ)
    (hf : ∀ i, (∑ j, (positionSpeed speeds a i j : ℂ) * f j) = θ * f i)
    (k : (ZMod 11)) (v : {v : ZMod 11 // v ∈ speeds}) :
    ∑ w : {v : ZMod 11 // v ∈ speeds}, fourierBlock a k v w * ZMod.dft (fun x : ZMod 11 => f (x,w)) k =
      θ * ZMod.dft (fun x : ZMod 11 => f (x,v)) k := by
  classical
  have hfun : (fun x : (ZMod 11) => ∑ w : {v : ZMod 11 // v ∈ speeds}, (K speeds a v w : ℂ) * f (x+v.1,w)) =
      fun x => θ * f (x,v) := by
    funext x
    rw [← positionSpeed_apply]
    exact hf (x,v)
  calc
    _ = ∑ w : {v : ZMod 11 // v ∈ speeds}, (K speeds a v w : ℂ) *
        (ZMod.stdAddChar (v.1*k) * ZMod.dft (fun x : (ZMod 11) => f (x,w)) k) := by
      apply Finset.sum_congr rfl
      intro w _
      simp only [fourierBlock, Matrix.diagonal_mul, Matrix.of_apply]
      ring
    _ = ∑ w : {v : ZMod 11 // v ∈ speeds}, (K speeds a v w : ℂ) *
        ZMod.dft (fun x : (ZMod 11) => f (x+v.1,w)) k := by
      apply Finset.sum_congr rfl
      intro w _
      exact congrArg (fun z : ℂ => (K speeds a v w : ℂ)*z)
        (dft_translate (fun x : (ZMod 11) => f (x,w)) v.1 k).symm
    _ = ZMod.dft (fun x : (ZMod 11) => ∑ w : {v : ZMod 11 // v ∈ speeds}, (K speeds a v w : ℂ) *
        f (x+v.1,w)) k := by
      rw [dft_sum]
      apply Finset.sum_congr rfl
      intro w _
      exact (congrFun (ZMod.dft_const_mul (K speeds a v w : ℂ) _) k).symm
    _ = θ * ZMod.dft (fun x : ZMod 11 => f (x,v)) k := by
      rw [hfun]
      exact congrFun (ZMod.dft_const_mul θ _) k

private theorem fourier_nonzero (f : (ZMod 11 × {v : ZMod 11 // v ∈ speeds}) → ℂ) (hf : ∃ x, f x ≠ 0) :
    ∃ k v, ZMod.dft (fun x : ZMod 11 => f (x,v)) k ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨⟨x,v⟩, hx⟩ := hf
  have he : ZMod.dft (fun x : (ZMod 11) => f (x,v)) = 0 := by
    exact (Set.eqOn_univ (ZMod.dft fun x => f (x, v)) 0).mp fun ⦃x⦄ _ => hn x v
  have hz : (fun x : (ZMod 11) => f (x,v)) = 0 :=
    ZMod.dft.injective (by simpa using he)
  exact hx (congrFun hz x)

private theorem speeds_card : speeds.card = 4 := by
  exact Eq.symm (Nat.eq_of_beq_eq_true rfl)

private theorem fourier_zero_sum (f : (ZMod 11 × {v : ZMod 11 // v ∈ speeds}) → ℂ) (hf : meanZero ((fun (_p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds})) => (1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ)))) f) :
    ∑ v : {v : ZMod 11 // v ∈ speeds}, ZMod.dft (fun x : ZMod 11 => f (x,v)) 0 = 0 := by
  classical
  have hw : ((1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ) : ℝ) : ℂ) =
      (1/44 : ℂ) := by
    have hcard : Fintype.card (ZMod 11 × {v : ZMod 11 // v ∈ speeds}) =
        Fintype.card (ZMod 11) * speeds.card := by
      simp only [Fintype.card_prod, Fintype.card_coe]
    have howner : D5.S3.Arith.Congruence.RestrictedSpineConstantPotential.uniformWeight
        1 (((0 : ZMod 11), (⟨1, by decide⟩ : {v : ZMod 11 // v ∈ speeds})), PUnit.unit) =
        (1/44 : ℝ) := by
      norm_num [D5.S3.Arith.Congruence.RestrictedSpineConstantPotential.uniformWeight,
        hcard, speeds_card]
    have hc := congrArg Complex.ofReal howner
    push_cast at hc
    simpa only [D5.S3.Arith.Congruence.RestrictedSpineConstantPotential.uniformWeight,
      hcard] using hc
  have hs : ∑ p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds}), f p = 0 := by
    have hh : (1/44 : ℂ) * ∑ p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds}), f p = 0 := by
      simpa only [meanZero, hw, ← Finset.mul_sum] using hf
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
  simp only [ZMod.dft_apply_zero]
  rw [Finset.sum_comm]
  simpa only [Fintype.sum_prod_type] using hs

private theorem fourier_reduction (a : ℝ) (θ : ℂ)
    (hθ : θ ∈ eigenvaluesMeanZero (positionSpeed speeds a) ((fun (_p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds})) => (1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ))))) :
    ∃ k : (ZMod 11), ∃ h : {v : ZMod 11 // v ∈ speeds} → ℂ,
      (∃ v, h v ≠ 0) ∧ (k = 0 → ∑ v, h v = 0) ∧
      ∀ v, ∑ w, fourierBlock a k v w * h w = θ * h v := by
  classical
  obtain ⟨f,hf,hm,he⟩ := hθ
  obtain ⟨k,v,hv⟩ := fourier_nonzero f hf
  refine ⟨k,(fun v => ZMod.dft (fun x : ZMod 11 => f (x,v)) k),⟨v,hv⟩,?_,fourier_intertwine a f θ he k⟩
  intro hk
  subst k
  exact fourier_zero_sum f hm

private theorem trivial_block_eq (a : ℝ) (h : {v : ZMod 11 // v ∈ speeds} → ℂ) (hs : ∑ v, h v = 0) (v : {v : ZMod 11 // v ∈ speeds}) :
    ∑ w, fourierBlock a 0 v w * h w = (a : ℂ) * h v := by
  classical
  have hk (w : {v : ZMod 11 // v ∈ speeds}) : (K speeds a v w : ℂ) =
      ((1-a)/4 : ℂ) + if v = w then (a : ℂ) else 0 := by
    simp only [K, speeds_card]
    split_ifs <;> push_cast <;> ring
  simp only [fourierBlock, Matrix.diagonal_mul, Matrix.of_apply, mul_zero, AddChar.map_zero_eq_one, one_mul, hk,
    add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hs, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, zero_add]

private theorem mean_zero_eigenvalue_block (a : ℝ) (θ : ℂ)
    (hθ : θ ∈ eigenvaluesMeanZero (positionSpeed speeds a) ((fun (_p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds})) => (1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ))))) :
    θ = (a : ℂ) ∨ ∃ k : (ZMod 11), k ≠ 0 ∧ ∃ h : {v : ZMod 11 // v ∈ speeds} → ℂ,
      (∃ v, h v ≠ 0) ∧ ∀ v, ∑ w, fourierBlock a k v w * h w = θ * h v := by
  classical
  obtain ⟨k,h,hn,hs,he⟩ := fourier_reduction a θ hθ
  by_cases hk : k = 0
  · subst k
    left
    obtain ⟨v,hv⟩ := hn
    exact (mul_right_cancel₀ hv ((he v).symm.trans (trivial_block_eq a h (hs rfl) v)))
  · exact Or.inr ⟨k,hk,h,hn,he⟩

private theorem block_lift (a : ℝ) (k : (ZMod 11)) (h : {v : ZMod 11 // v ∈ speeds} → ℂ) (θ : ℂ)
    (he : ∀ v, ∑ w, fourierBlock a k v w * h w = θ * h v) :
    ∀ p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds}), ∑ q : (ZMod 11 × {v : ZMod 11 // v ∈ speeds}), (positionSpeed speeds a p q : ℂ) *
      (ZMod.stdAddChar (q.1*k) * h q.2) =
      θ * (ZMod.stdAddChar (p.1*k) * h p.2) := by
  classical
  rintro ⟨x,v⟩
  rw [positionSpeed_apply]
  simp only [add_mul, AddChar.map_add_eq_mul, mul_assoc]
  calc
    _ = ZMod.stdAddChar (x*k) * ∑ w, fourierBlock a k v w * h w := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      simp only [fourierBlock, Matrix.diagonal_mul, Matrix.of_apply]
      ring
    _ = _ := by rw [he]; ring


end
end D5.S3.Fourier.DiaconisMicloUnimodality

namespace D5.S3.Fourier.DiaconisMicloUnimodality
noncomputable section
open scoped BigOperators

private noncomputable def speedEquiv : Fin 4 ≃ {v : ZMod 11 // v ∈ speeds} :=
  Equiv.ofBijective (fun i => ⟨![1,2,9,10] i, by fin_cases i <;> decide⟩) (by decide)

private def literalBlock (a q : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![q,q^2,(q⁻¹)^2,q⁻¹] *
    (a • (1 : Matrix (Fin 4) (Fin 4) ℂ) + ((1-a)/4) • Matrix.of (fun _ _ => 1))

private def blockPolynomial {𝕜 : Type*} [Field 𝕜] (a t z : 𝕜) : 𝕜 :=
  z^4 - (1+3*a)*(t^2+t-2)*z^3/4 + a*(1+a)*(t^3-2*t+2)*z^2/2 -
    a^2*(3+a)*(t^2+t-2)*z/4 + a^3

private theorem char_ne_zero (k : (ZMod 11)) : ZMod.stdAddChar k ≠ 0 := by
  exact (ZMod.toCircle k).coe_ne_zero

private theorem literal_block_identity (a : ℝ) (k : (ZMod 11)) (i j : Fin 4) :
    fourierBlock a k (speedEquiv i) (speedEquiv j) =
      literalBlock a (ZMod.stdAddChar k) i j := by
  classical
  have h2 : ZMod.stdAddChar (2*k) = ZMod.stdAddChar k ^ 2 := by
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using (ZMod.stdAddChar (N := 11)).map_nsmul_eq_pow 2 k
  have h9 : ZMod.stdAddChar (9*k) = (ZMod.stdAddChar k)⁻¹ ^ 2 := by
    have hh : (9 : (ZMod 11)) = -2 := by exact ZMod.eq_neg_of_valMinAbs_eq_neg_valMinAbs rfl
    rw [hh, neg_mul, AddChar.map_neg_eq_inv, h2, inv_pow]
  have h10 : ZMod.stdAddChar (10*k) = (ZMod.stdAddChar k)⁻¹ := by
    have hh : (10 : (ZMod 11)) = -1 := by exact ZMod.eq_neg_of_valMinAbs_eq_neg_valMinAbs rfl
    rw [hh, neg_mul, one_mul, AddChar.map_neg_eq_inv]
  have hphase : ZMod.stdAddChar ((speedEquiv i).1*k) =
      ![ZMod.stdAddChar k,ZMod.stdAddChar k^2,(ZMod.stdAddChar k)⁻¹^2,(ZMod.stdAddChar k)⁻¹] i := by
    fin_cases i <;> simp [speedEquiv,one_mul,h2,h9,h10]
  have hK : (K speeds a (speedEquiv i) (speedEquiv j) : ℂ) =
      (a:ℂ)*(if i=j then 1 else 0)+(1-(a:ℂ))/4 := by
    by_cases hij : i=j
    · subst j
      simp [K,speeds_card] <;> ring
    · have hv : speedEquiv i ≠ speedEquiv j := speedEquiv.injective.ne hij
      simp [K,speeds_card,hv,hij] <;> ring
  simp only [fourierBlock,literalBlock,Matrix.diagonal_mul, Matrix.of_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,hphase,hK,mul_one]

private theorem literal_characteristic_polynomial (a q z : ℂ) (hq : q ≠ 0) :
    (Matrix.scalar (Fin 4) z - literalBlock a q).det =
      blockPolynomial a (q+q⁻¹) z := by
  classical
  have hm : Matrix.scalar (Fin 4) z - literalBlock a q =
      Matrix.of (fun i j => (if i=j then z else 0) -
        ![q,q^2,(q⁻¹)^2,q⁻¹] i *
          (a*(if i=j then 1 else 0)+(1-a)/4)) := by
    ext i j
    simp [literalBlock, Matrix.diagonal_mul, Matrix.scalar, Matrix.diagonal_apply,
      Matrix.one_apply]
  rw [hm]
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix_apply,
    Matrix.of_apply, Fin.succAbove, blockPolynomial]
  field_simp [hq]
  ring

private theorem char_trace_real (k : (ZMod 11)) :
    ZMod.stdAddChar k + (ZMod.stdAddChar k)⁻¹ =
      (Algebra.trace ℝ ℂ (ZMod.stdAddChar k) : ℂ) := by
  have hc : (ZMod.stdAddChar k)⁻¹ = star (ZMod.stdAddChar k) :=
    Circle.coe_inv_eq_conj (ZMod.toCircle k)
  rw [hc]
  simpa only [Algebra.trace_complex_apply, starRingEnd_apply] using
    Complex.add_conj (ZMod.stdAddChar k)


private theorem fourier_characteristic_polynomial (a : ℝ) (k : (ZMod 11)) (z : ℂ) :
    (fourierBlock a k).charpoly.eval z =
      blockPolynomial (a : ℂ) (Algebra.trace ℝ ℂ (ZMod.stdAddChar k)) z := by
  classical
  rw [Matrix.eval_charpoly]
  rw [← Matrix.det_submatrix_equiv_self speedEquiv (Matrix.scalar {v : ZMod 11 // v ∈ speeds} z-fourierBlock a k)]
  have hm : (Matrix.scalar {v : ZMod 11 // v ∈ speeds} z-fourierBlock a k).submatrix speedEquiv speedEquiv =
      Matrix.scalar (Fin 4) z-literalBlock a (ZMod.stdAddChar k) := by
    ext i j
    simp [Matrix.submatrix_apply,Matrix.scalar,Matrix.diagonal_apply,literal_block_identity]
  rw [hm,literal_characteristic_polynomial _ _ _ (char_ne_zero k),char_trace_real]


end
end D5.S3.Fourier.DiaconisMicloUnimodality

namespace D5.S3.Fourier.DiaconisMicloUnimodality
noncomputable section
open scoped BigOperators

private theorem eigen_det_zero {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (θ : ℂ) (h : n → ℂ) (hn : h ≠ 0)
    (he : ∀ i, ∑ j, A i j*h j=θ*h i) :
    (Matrix.scalar n θ-A).det=0 := by
  have hh : (Matrix.scalar n θ-A).mulVec h=0 := by
    ext i
    simp only [Matrix.sub_mulVec, Matrix.scalar_apply,Matrix.mulVec_diagonal, Pi.sub_apply,
      Pi.zero_apply, sub_eq_zero]
    exact (he i).symm
  by_contra hd
  exact hn (Matrix.eq_zero_of_mulVec_eq_zero hd hh)

private theorem det_zero_eigenvector {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (θ : ℂ) (hd : (Matrix.scalar n θ-A).det=0) :
    ∃ h : n → ℂ, h ≠ 0 ∧ ∀ i, ∑ j, A i j*h j=θ*h i := by
  obtain ⟨h, hn, he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  refine ⟨h, hn, ?_⟩
  rw [Matrix.sub_mulVec,Matrix.scalar_apply] at he
  intro i
  have hi := congrFun he i
  have hz : θ * h i - A.mulVec h i = 0 := by
    simpa only [Pi.sub_apply, Matrix.mulVec_diagonal, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply] using hi
  simpa only [Matrix.mulVec, dotProduct] using (sub_eq_zero.mp hz).symm

private theorem finite_mean_zero_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (w : n → ℝ) : (eigenvaluesMeanZero A w).Finite := by
  let B : Matrix n n ℂ := fun i j => (A i j : ℂ)
  apply (Polynomial.finite_setOfPred_isRoot B.charpoly_monic.ne_zero).subset
  rintro θ ⟨f,hf,_,he⟩
  have hn : f ≠ 0 := Function.ne_iff.mpr hf
  change B.charpoly.eval θ=0
  rw [Matrix.eval_charpoly]
  exact eigen_det_zero B θ f hn he

end
end D5.S3.Fourier.DiaconisMicloUnimodality

namespace D5.S3.Fourier.DiaconisMicloUnimodality
noncomputable section
open scoped BigOperators
open Polynomial

private def rootLo (i : Fin 5) : ℝ :=
  ![16825070656,8308300260,-2846296766,-13097214679,-19189859473] i / 10000000000

private def rootHi (i : Fin 5) : ℝ := rootLo i + 1/10000000000

private def RootWindow (t : ℝ) : Prop := ∃ i : Fin 5, t ∈ Set.Icc (rootLo i) (rootHi i)

private def realCyclotomic : ℝ[X] := X^5+X^4-4*X^3-3*X^2+3*X+1

private theorem real_cyclotomic_ne_zero : realCyclotomic ≠ 0 := by
  intro h
  have hh := congrArg (fun p : ℝ[X] => p.coeff 5) h
  norm_num [realCyclotomic,Polynomial.coeff_X,Polynomial.coeff_one] at hh

private theorem cyclotomic_interval_sign (i : Fin 5) :
    realCyclotomic.eval (rootLo i) * realCyclotomic.eval (rootHi i) < 0 := by
  fin_cases i <;> norm_num [realCyclotomic,rootLo,rootHi]

private theorem cyclotomic_root_windows (t : ℝ) (ht : realCyclotomic.eval t = 0) : RootWindow t := by
  classical
  have hex (i : Fin 5) : ∃ r : ℝ, r ∈ Set.Icc (rootLo i) (rootHi i) ∧ realCyclotomic.eval r=0 := by
    have hi : rootLo i ≤ rootHi i := by unfold rootHi; linarith
    have hc : ContinuousOn (fun r : ℝ => realCyclotomic.eval r) (Set.Icc (rootLo i) (rootHi i)) :=
      realCyclotomic.continuous.continuousOn
    rcases mul_neg_iff.mp (cyclotomic_interval_sign i) with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · exact intermediate_value_Icc' hi hc ⟨hr.le,hl.le⟩
    · exact intermediate_value_Icc hi hc ⟨hl.le,hr.le⟩
  choose r hrange heval using hex
  have hinj : Function.Injective r := by
    intro i j he
    by_contra hij
    rcases hrange i with ⟨hi0,hi1⟩
    rcases hrange j with ⟨hj0,hj1⟩
    rw [he] at hi0 hi1
    fin_cases i <;> fin_cases j <;>
      first | exact hij rfl | (norm_num [rootLo,rootHi] at hi0 hi1 hj0 hj1; linarith only [hi0,hi1,hj0,hj1])
  let rs : Finset ℝ := Finset.univ.image r
  have hrscard : rs.card = 5 := by
    simp [rs,Finset.card_image_of_injective,hinj]
  have hdeg : realCyclotomic.natDegree ≤ 5 := by
    unfold realCyclotomic
    compute_degree
  have hroots : realCyclotomic.roots = rs.val :=
    Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
      (fun x hx => by obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx; exact heval i)
      (by simpa only [hrscard] using hdeg) real_cyclotomic_ne_zero
  have hmem := (Polynomial.mem_roots real_cyclotomic_ne_zero).mpr ht
  rw [hroots] at hmem
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (show t ∈ rs from hmem)
  exact ⟨i,hi ▸ hrange i⟩

private theorem cyclotomic_trace_identity (q : ℂ) (hq : q ≠ 0) :
    (q-1)*q^5*((q+q⁻¹)^5+(q+q⁻¹)^4-4*(q+q⁻¹)^3-3*(q+q⁻¹)^2+3*(q+q⁻¹)+1) =
      q^11-1 := by
  field_simp [hq]
  ring

private theorem char_trace_cyclotomic (k : (ZMod 11)) (hk : k ≠ 0) :
    realCyclotomic.eval (Algebra.trace ℝ ℂ (ZMod.stdAddChar k)) = 0 := by
  have hq := char_ne_zero k
  have hq1 : ZMod.stdAddChar k ≠ 1 := by
    intro he
    apply hk
    apply ZMod.injective_stdAddChar
    simpa only [AddChar.map_zero_eq_one] using he
  have h11 : ZMod.stdAddChar k ^ 11 = 1 := by
    have hh : (11:ℕ) • k = 0 := by exact ZModModule.char_nsmul_eq_zero 11 k
    simpa only [hh,AddChar.map_zero_eq_one] using
      ((ZMod.stdAddChar (N:=11)).map_nsmul_eq_pow 11 k).symm
  have hi := cyclotomic_trace_identity (ZMod.stdAddChar k) hq
  rw [h11,sub_self,char_trace_real] at hi
  have hzero := (mul_eq_zero.mp hi).resolve_left (mul_ne_zero (sub_ne_zero.mpr hq1) (pow_ne_zero 5 hq))
  apply Complex.ofReal_injective
  simpa [realCyclotomic] using hzero

end
end D5.S3.Fourier.DiaconisMicloUnimodality

namespace D5.S3.Fourier.DiaconisMicloUnimodality
noncomputable section
open scoped BigOperators

private theorem schur_step (A B : ℝ) (p r q s z : ℂ)
    (hAB : 0 < A^2-B^2) (hz : 1 ≤ ‖z‖)
    (hq : q ≠ 0) (hqs : ‖s‖ ≤ ‖q‖)
    (hp : (A:ℂ)*p-(B:ℂ)*r=z*q)
    (hr : (A:ℂ)*r-(B:ℂ)*p=s) :
    p ≠ 0 ∧ ‖r‖ ≤ ‖p‖ := by
  have hid : (A^2-B^2)*(‖p‖^2-‖r‖^2) =
      ‖(A:ℂ)*p-(B:ℂ)*r‖^2-‖(A:ℂ)*r-(B:ℂ)*p‖^2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsm : ‖s‖ ≤ ‖z*q‖ := by
    rw [norm_mul]
    calc
      ‖s‖ ≤ ‖q‖ := hqs
      _ ≤ ‖z‖*‖q‖ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hz (norm_nonneg q)
  have hd : 0 ≤ (A^2-B^2)*(‖p‖^2-‖r‖^2) := by
    rw [hid,hp,hr]
    exact sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg s) (norm_nonneg (z*q))).mpr hsm)
  have hnorm : ‖r‖ ≤ ‖p‖ := by
    have hh := nonneg_of_mul_nonneg_right hd hAB
    exact (sq_le_sq₀ (norm_nonneg r) (norm_nonneg p)).mp (sub_nonneg.mp hh)
  refine ⟨?_,hnorm⟩
  intro hp0
  have hr0 : r = 0 := norm_le_zero_iff.mp (by simpa only [hp0,norm_zero] using hnorm)
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
  have hh : z*q=0 := by simpa only [hp0,hr0,mul_zero,sub_zero] using hp.symm
  exact mul_ne_zero hz0 hq hh

private def reduce4 (c : Fin 5 → ℝ) : Fin 4 → ℝ :=
  ![c 4*c 1-c 0*c 3, c 4*c 2-c 0*c 2,
    c 4*c 3-c 0*c 1, c 4*c 4-c 0*c 0]

private def reduce3 (c : Fin 4 → ℝ) : Fin 3 → ℝ :=
  ![c 3*c 1-c 0*c 2, c 3*c 2-c 0*c 1, c 3*c 3-c 0*c 0]

private def reduce2 (c : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![c 2*c 1-c 0*c 1, c 2*c 2-c 0*c 0]

private def Schur4 (c : Fin 5 → ℝ) : Prop :=
  0 < (c 4)^2-(c 0)^2 ∧
  0 < (reduce4 c 3)^2-(reduce4 c 0)^2 ∧
  0 < (reduce3 (reduce4 c) 2)^2-(reduce3 (reduce4 c) 0)^2 ∧
  0 < (reduce2 (reduce3 (reduce4 c)) 1)^2-(reduce2 (reduce3 (reduce4 c)) 0)^2



private theorem schur4_outside (c : Fin 5 → ℝ) (hc : Schur4 c) (z : ℂ) (hz : 1 ≤ ‖z‖) :
    (Polynomial.ofFn 5 c).eval₂ Complex.ofRealHom z ≠ 0 := by
  obtain ⟨h4,h3,h2,h1⟩ := hc
  let b := reduce4 c
  let d := reduce3 b
  let e := reduce2 d
  let f : ℝ := (e 1)^2-(e 0)^2
  have hf : 0 < f := h1
  have hbase : (f:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hf.ne'
  have he := schur_step (e 1) (e 0) ((Polynomial.ofFn 2 e).eval₂ Complex.ofRealHom z) ((Polynomial.ofFn 2 (e ∘ Fin.rev)).eval₂ Complex.ofRealHom z)
      (f:ℂ) (f:ℂ) z h1 hz hbase le_rfl
      (by simp [Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_succ, Function.comp_def, Fin.rev,f]; push_cast; ring)
      (by simp [Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_succ, Function.comp_def, Fin.rev,f]; push_cast; ring)
  have hd := schur_step (d 2) (d 0) ((Polynomial.ofFn 3 d).eval₂ Complex.ofRealHom z) ((Polynomial.ofFn 3 (d ∘ Fin.rev)).eval₂ Complex.ofRealHom z)
      ((Polynomial.ofFn 2 e).eval₂ Complex.ofRealHom z) ((Polynomial.ofFn 2 (e ∘ Fin.rev)).eval₂ Complex.ofRealHom z) z h2 hz he.1 he.2
      (by simp [Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_succ, Function.comp_def, Fin.rev,e,reduce2]; push_cast; ring)
      (by simp [Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_succ, Function.comp_def, Fin.rev,e,reduce2]; push_cast; ring)
  have hb := schur_step (b 3) (b 0) ((Polynomial.ofFn 4 b).eval₂ Complex.ofRealHom z) ((Polynomial.ofFn 4 (b ∘ Fin.rev)).eval₂ Complex.ofRealHom z)
      ((Polynomial.ofFn 3 d).eval₂ Complex.ofRealHom z) ((Polynomial.ofFn 3 (d ∘ Fin.rev)).eval₂ Complex.ofRealHom z) z h3 hz hd.1 hd.2
      (by simp [Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_succ, Function.comp_def, Fin.rev,d,reduce3]; push_cast; ring)
      (by simp [Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_succ, Function.comp_def, Fin.rev,d,reduce3]; push_cast; ring)
  exact (schur_step (c 4) (c 0) ((Polynomial.ofFn 5 c).eval₂ Complex.ofRealHom z) ((Polynomial.ofFn 5 (c ∘ Fin.rev)).eval₂ Complex.ofRealHom z)
      ((Polynomial.ofFn 4 b).eval₂ Complex.ofRealHom z) ((Polynomial.ofFn 4 (b ∘ Fin.rev)).eval₂ Complex.ofRealHom z) z h4 hz hb.1 hb.2
      (by simp [Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_succ, Function.comp_def, Fin.rev,b,reduce4]; push_cast; ring)
      (by simp [Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_succ, Function.comp_def, Fin.rev,b,reduce4]; push_cast; ring)).1

end
end D5.S3.Fourier.DiaconisMicloUnimodality

namespace D5.S3.Fourier.DiaconisMicloUnimodality
noncomputable section
open scoped BigOperators

private def R : ℝ := 239/500

private def blockCoefficients (a t : ℝ) : Fin 5 → ℝ :=
  ![a^3, -a^2*(3+a)*(t^2+t-2)*R/4,
    a*(1+a)*(t^3-2*t+2)*R^2/2,
    -(1+3*a)*(t^2+t-2)*R^3/4, R^4]

private theorem endpoint_schur_one_fifth (t : ℝ) (ht : RootWindow t) :
    Schur4 (blockCoefficients (1/5) t) := by
  have hr2 : (2:ℝ)⁻¹ = ((1/2:ℚ):ℝ) := by norm_num
  have hr4 : (4:ℝ)⁻¹ = ((1/4:ℚ):ℝ) := by norm_num
  have hr5 : (5:ℝ)⁻¹ = ((1/5:ℚ):ℝ) := by norm_num
  have hr10 : (10:ℝ)⁻¹ = ((1/10:ℚ):ℝ) := by norm_num
  have hr100 : (100:ℝ)⁻¹ = ((1/100:ℚ):ℝ) := by norm_num
  have hr500 : (500:ℝ)⁻¹ = ((1/500:ℚ):ℝ) := by norm_num
  have hr20000 : (20000:ℝ)⁻¹ = ((1/20000:ℚ):ℝ) := by norm_num
  have hr10000000000 : (10000000000:ℝ)⁻¹ = ((1/10000000000:ℚ):ℝ) := by norm_num
  obtain ⟨i,ht⟩ := ht
  fin_cases i <;>
    dsimp [Schur4,blockCoefficients,reduce4,reduce3,reduce2,R,rootLo,rootHi] at * <;>
    simp only [div_eq_mul_inv,hr2,hr4,hr5,hr10,hr100,hr500,hr20000,hr10000000000] at * <;>
    refine ⟨?_,?_,?_,?_⟩ <;> dyadic_interval +kernel [prec := 256]

private theorem endpoint_schur_three_tenths (t : ℝ) (ht : RootWindow t) :
    Schur4 (blockCoefficients (3/10) t) := by
  have hr2 : (2:ℝ)⁻¹ = ((1/2:ℚ):ℝ) := by norm_num
  have hr4 : (4:ℝ)⁻¹ = ((1/4:ℚ):ℝ) := by norm_num
  have hr5 : (5:ℝ)⁻¹ = ((1/5:ℚ):ℝ) := by norm_num
  have hr10 : (10:ℝ)⁻¹ = ((1/10:ℚ):ℝ) := by norm_num
  have hr100 : (100:ℝ)⁻¹ = ((1/100:ℚ):ℝ) := by norm_num
  have hr500 : (500:ℝ)⁻¹ = ((1/500:ℚ):ℝ) := by norm_num
  have hr20000 : (20000:ℝ)⁻¹ = ((1/20000:ℚ):ℝ) := by norm_num
  have hr10000000000 : (10000000000:ℝ)⁻¹ = ((1/10000000000:ℚ):ℝ) := by norm_num
  obtain ⟨i,ht⟩ := ht
  fin_cases i <;>
    dsimp [Schur4,blockCoefficients,reduce4,reduce3,reduce2,R,rootLo,rootHi] at * <;>
    simp only [div_eq_mul_inv,hr2,hr4,hr5,hr10,hr100,hr500,hr20000,hr10000000000] at * <;>
    refine ⟨?_,?_,?_,?_⟩ <;> dyadic_interval +kernel [prec := 256]

private theorem value4_block_scaled (a t : ℝ) (z : ℂ) :
    (Polynomial.ofFn 5 (blockCoefficients a t)).eval₂ Complex.ofRealHom (z/(R:ℂ)) = blockPolynomial (a : ℂ) t z := by
  simp [Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_succ, blockCoefficients,blockPolynomial,R,Polynomial.eval₂_pow]
  push_cast
  ring

private theorem block_roots_inside (a t : ℝ) (hc : Schur4 (blockCoefficients a t))
    (z : ℂ) (hp : blockPolynomial (a : ℂ) t z=0) : ‖z‖ < R := by
  by_contra hn
  have hz : 1 ≤ ‖z/(R:ℂ)‖ := by
    rw [norm_div]
    norm_num [R] at *
    linarith
  exact schur4_outside (blockCoefficients a t) hc (z/(R:ℂ)) hz
    ((value4_block_scaled a t z).trans hp)


private theorem middle_signs (t : ℝ) (ht : t ∈ Set.Icc (rootLo 2) (rootHi 2)) :
    33/100 < blockPolynomial (1/4) t (-1) ∧
    blockPolynomial (1/4) t (-R) < -1/20000 := by
  have hr2 : (2:ℝ)⁻¹ = ((1/2:ℚ):ℝ) := by norm_num
  have hr4 : (4:ℝ)⁻¹ = ((1/4:ℚ):ℝ) := by norm_num
  have hr5 : (5:ℝ)⁻¹ = ((1/5:ℚ):ℝ) := by norm_num
  have hr10 : (10:ℝ)⁻¹ = ((1/10:ℚ):ℝ) := by norm_num
  have hr100 : (100:ℝ)⁻¹ = ((1/100:ℚ):ℝ) := by norm_num
  have hr500 : (500:ℝ)⁻¹ = ((1/500:ℚ):ℝ) := by norm_num
  have hr20000 : (20000:ℝ)⁻¹ = ((1/20000:ℚ):ℝ) := by norm_num
  have hr10000000000 : (10000000000:ℝ)⁻¹ = ((1/10000000000:ℚ):ℝ) := by norm_num
  constructor <;> dsimp [blockPolynomial,rootLo,rootHi,R] at * <;>
    simp only [div_eq_mul_inv,hr2,hr4,hr5,hr10,hr100,hr500,hr20000,hr10000000000] at * <;> dyadic_interval +kernel [prec := 80]

private theorem middle_real_root (t : ℝ) (ht : t ∈ Set.Icc (rootLo 2) (rootHi 2)) :
    ∃ z : ℝ, -1 < z ∧ z < -R ∧ blockPolynomial (1/4) t z=0 := by
  have hs := middle_signs t ht
  have hc : ContinuousOn (blockPolynomial (1/4) t) (Set.Icc (-1) (-R)) := by
    unfold blockPolynomial
    fun_prop
  obtain ⟨z,hz,hp⟩ := intermediate_value_Icc' (by norm_num [R] : (-1:ℝ) ≤ -R) hc
    (show (0:ℝ) ∈ Set.Icc (blockPolynomial (1/4) t (-R))
      (blockPolynomial (1/4) t (-1)) from ⟨by linarith,by linarith⟩)
  refine ⟨z,?_,?_,hp⟩
  · have hn : z ≠ -1 := by intro he; rw [he] at hp; linarith
    exact lt_of_le_of_ne hz.1 (Ne.symm hn)
  · have hn : z ≠ -R := by intro he; rw [he] at hp; linarith
    exact lt_of_le_of_ne hz.2 hn

end
end D5.S3.Fourier.DiaconisMicloUnimodality

namespace D5.S3.Fourier.DiaconisMicloUnimodality
noncomputable section
open scoped BigOperators

private theorem trace_fiber (k l : (ZMod 11))
    (h : Algebra.trace ℝ ℂ (ZMod.stdAddChar k) = Algebra.trace ℝ ℂ (ZMod.stdAddChar l)) :
    k = l ∨ k = -l := by
  let q := ZMod.stdAddChar k
  let r := ZMod.stdAddChar l
  have hq : q ≠ 0 := char_ne_zero k
  have hr : r ≠ 0 := char_ne_zero l
  have hh : q+q⁻¹=r+r⁻¹ := by rw [char_trace_real,char_trace_real,h]
  have he : (q-r)*(q*r-1) = 0 := by
    calc
      _ = q*r*((q+q⁻¹)-(r+r⁻¹)) := by field_simp [hq,hr]; ring
      _ = 0 := by rw [hh,sub_self,mul_zero]
  rcases mul_eq_zero.mp he with hkr | hkr
  · exact Or.inl (ZMod.injective_stdAddChar (sub_eq_zero.mp hkr))
  · right
    have hsum : ZMod.stdAddChar (k+l) = ZMod.stdAddChar (0:(ZMod 11)) := by
      rw [AddChar.map_add_eq_mul,AddChar.map_zero_eq_one]
      exact sub_eq_zero.mp hkr
    exact eq_neg_of_add_eq_zero_left (ZMod.injective_stdAddChar hsum)

private def modeIndex (i : Fin 5) : (ZMod 11) := ![1,2,3,4,5] i

private theorem modeIndex_ne_zero (i : Fin 5) : modeIndex i ≠ 0 := by
  fin_cases i <;> decide

private theorem trace_mode_injective :
    Function.Injective (fun i : Fin 5 => Algebra.trace ℝ ℂ (ZMod.stdAddChar (modeIndex i))) := by
  intro i j h
  have hh := trace_fiber _ _ h
  have hcomb : ∀ i j : Fin 5,
      modeIndex i=modeIndex j ∨ modeIndex i= -modeIndex j → i=j := by decide
  exact hcomb i j hh

private theorem cyclotomic_trace_exhaustive (t : ℝ) (ht : realCyclotomic.eval t=0) :
    ∃ i : Fin 5, Algebra.trace ℝ ℂ (ZMod.stdAddChar (modeIndex i)) = t := by
  classical
  let rs : Finset ℝ :=
    Finset.univ.image (fun i => Algebra.trace ℝ ℂ (ZMod.stdAddChar (modeIndex i)))
  have hrscard : rs.card=5 := by
    simp [rs,Finset.card_image_of_injective,trace_mode_injective]
  have hdeg : realCyclotomic.natDegree ≤ 5 := by unfold realCyclotomic; compute_degree
  have hroots : realCyclotomic.roots=rs.val :=
    Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
      (fun x hx => by
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
        exact char_trace_cyclotomic _ (modeIndex_ne_zero i))
      (by simpa only [hrscard] using hdeg) real_cyclotomic_ne_zero
  have hmem := (Polynomial.mem_roots real_cyclotomic_ne_zero).mpr ht
  rw [hroots] at hmem
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (show t ∈ rs from hmem)
  exact ⟨i,hi⟩

end
end D5.S3.Fourier.DiaconisMicloUnimodality

namespace D5.S3.Fourier.DiaconisMicloUnimodality
noncomputable section
open scoped BigOperators

private theorem block_lift_mean_zero (k : (ZMod 11)) (h : {v : ZMod 11 // v ∈ speeds} → ℂ)
    (hk : k ≠ 0 ∨ ∑ v,h v=0) :
    meanZero ((fun (_p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds})) => (1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ)))) (fun p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds}) => ZMod.stdAddChar (p.1*k)*h p.2) := by
  classical
  have hw : ((1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ) : ℝ) : ℂ) =
      (1/44 : ℂ) := by norm_num [speeds_card]
  have he : (∑ p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds}), ((fun (_p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds})) => (1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ))) p : ℂ)*(ZMod.stdAddChar (p.1*k)*h p.2)) =
      (1/44:ℂ)*(∑ x : (ZMod 11),ZMod.stdAddChar (x*k))*(∑ v : {v : ZMod 11 // v ∈ speeds},h v) := by
    calc
      _ = (1/44:ℂ)*(∑ x : (ZMod 11),∑ v : {v : ZMod 11 // v ∈ speeds},ZMod.stdAddChar (x*k)*h v) := by
        simp only [hw,Fintype.sum_prod_type,Finset.mul_sum]
      _ = (1/44:ℂ)*((∑ x : (ZMod 11),ZMod.stdAddChar (x*k))*(∑ v : {v : ZMod 11 // v ∈ speeds},h v)) := by
        rw [Finset.sum_mul_sum]
      _ = _ := (mul_assoc _ _ _).symm
  unfold meanZero
  rw [he]
  rcases hk with hk | hk
  · have hs := AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 11 hk)
    have hh : (∑ x : (ZMod 11),ZMod.stdAddChar (x*k))=0 := by
      simpa only [AddChar.mulShift_apply,mul_comm] using hs
    rw [hh,mul_zero,zero_mul]
  · rw [hk,mul_zero]

private theorem lifted_eigenvalue (a : ℝ) (k : (ZMod 11)) (h : {v : ZMod 11 // v ∈ speeds} → ℂ) (θ : ℂ)
    (hn : ∃ v,h v≠0) (hk : k≠0 ∨ ∑ v,h v=0)
    (he : ∀ v,∑ w,fourierBlock a k v w*h w=θ*h v) :
    θ ∈ eigenvaluesMeanZero (positionSpeed speeds a) ((fun (_p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds})) => (1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ)))) := by
  refine ⟨(fun p => ZMod.stdAddChar (p.1*k)*h p.2),?_,block_lift_mean_zero k h hk,
    block_lift a k h θ he⟩
  obtain ⟨v,hv⟩ := hn
  refine ⟨(0,v),?_⟩
  simpa only [zero_mul,AddChar.map_zero_eq_one,one_mul] using hv

private theorem a_is_mean_zero_eigenvalue (a : ℝ) :
    (a:ℂ) ∈ eigenvaluesMeanZero (positionSpeed speeds a) ((fun (_p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds})) => (1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ)))) := by
  classical
  let h : {v : ZMod 11 // v ∈ speeds} → ℂ := fun v => ![(1:ℂ),-1,0,0] (speedEquiv.symm v)
  have hs : ∑ v,h v=0 := by
    rw [← speedEquiv.sum_comp]
    simp [h,Fin.sum_univ_succ]
  apply lifted_eigenvalue a 0 h a
  · refine ⟨speedEquiv 0,?_⟩
    norm_num [h]
  · exact Or.inr hs
  · exact trivial_block_eq a h hs

end
end D5.S3.Fourier.DiaconisMicloUnimodality

namespace D5.S3.Fourier.DiaconisMicloUnimodality
noncomputable section
open scoped BigOperators

private theorem fourier_root (a : ℝ) (k : (ZMod 11)) (θ : ℂ) (h : {v : ZMod 11 // v ∈ speeds} → ℂ)
    (hn : ∃ v,h v≠0) (he : ∀ v,∑ w,fourierBlock a k v w*h w=θ*h v) :
    blockPolynomial (a : ℂ) (Algebra.trace ℝ ℂ (ZMod.stdAddChar k)) θ=0 := by
  classical
  have hn' : h ≠ 0 := Function.ne_iff.mpr hn
  have hd := eigen_det_zero (fourierBlock a k) θ h hn' he
  rw [← Matrix.eval_charpoly, fourier_characteristic_polynomial] at hd
  exact hd

private theorem endpoint_eigenvalue_bound (a : ℝ) (ha : a=1/5 ∨ a=3/10)
    (θ : ℂ) (hθ : θ ∈ eigenvaluesMeanZero (positionSpeed speeds a) ((fun (_p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds})) => (1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ))))) : ‖θ‖ < R := by
  obtain he | ⟨k,hk,h,hn,he⟩ := mean_zero_eigenvalue_block a θ hθ
  · subst θ
    rcases ha with rfl | rfl <;> norm_num [R]
  · have ht := cyclotomic_root_windows _ (char_trace_cyclotomic k hk)
    have hc : Schur4 (blockCoefficients a (Algebra.trace ℝ ℂ (ZMod.stdAddChar k))) := by
      rcases ha with rfl | rfl
      · exact endpoint_schur_one_fifth _ ht
      · exact endpoint_schur_three_tenths _ ht
    exact block_roots_inside a _ hc θ (fourier_root a k θ h hn he)

private theorem middle_eigenvalue : ∃ θ : ℂ,
    θ ∈ eigenvaluesMeanZero (positionSpeed speeds (1/4)) ((fun (_p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds})) => (1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ)))) ∧ R < ‖θ‖ := by
  classical
  have hi : rootLo 2 ≤ rootHi 2 := by unfold rootHi; linarith
  have hc := realCyclotomic.continuous.continuousOn (s:=Set.Icc (rootLo 2) (rootHi 2))
  have hs := cyclotomic_interval_sign 2
  have hex : ∃ t : ℝ,t ∈ Set.Icc (rootLo 2) (rootHi 2) ∧ realCyclotomic.eval t=0 := by
    rcases mul_neg_iff.mp hs with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · exact intermediate_value_Icc' hi hc ⟨hr.le,hl.le⟩
    · exact intermediate_value_Icc hi hc ⟨hl.le,hr.le⟩
  obtain ⟨t,ht,hpt⟩ := hex
  obtain ⟨i,hi⟩ := cyclotomic_trace_exhaustive t hpt
  let k := modeIndex i
  have hk : k≠0 := modeIndex_ne_zero i
  obtain ⟨z,hz0,hz1,hpz⟩ := middle_real_root t ht
  have hp : blockPolynomial (1/4 : ℂ)
      (Algebra.trace ℝ ℂ (ZMod.stdAddChar k)) (z:ℂ)=0 := by
    rw [hi]
    simpa [blockPolynomial] using congrArg Complex.ofReal hpz
  have hd : (Matrix.scalar (Fin 4) (z:ℂ)-literalBlock (1/4) (ZMod.stdAddChar k)).det=0 := by
    rw [literal_characteristic_polynomial _ _ _ (char_ne_zero k),char_trace_real]
    exact hp
  obtain ⟨h4,hn4,he4⟩ := det_zero_eigenvector (literalBlock (1/4) (ZMod.stdAddChar k)) (z:ℂ) hd
  let h : {v : ZMod 11 // v ∈ speeds} → ℂ := fun v => h4 (speedEquiv.symm v)
  have hn : ∃ v,h v≠0 := by
    have hex : ∃ i,h4 i≠0 := Function.ne_iff.mp hn4
    obtain ⟨j,hj⟩ := hex
    exact ⟨speedEquiv j,by simpa [h] using hj⟩
  have he (v : {v : ZMod 11 // v ∈ speeds}) : ∑ w,fourierBlock (1/4) k v w*h w=(z:ℂ)*h v := by
    have hentry (j : Fin 4) : fourierBlock (1/4) k v (speedEquiv j) =
        literalBlock (1/4) (ZMod.stdAddChar k) (speedEquiv.symm v) j := by
      simpa using literal_block_identity (1/4) k (speedEquiv.symm v) j
    rw [← speedEquiv.sum_comp]
    simpa only [h,Equiv.symm_apply_apply,hentry] using he4 (speedEquiv.symm v)
  refine ⟨z,lifted_eigenvalue (1/4) k h z hn (Or.inl hk) he,?_⟩
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by norm_num [R] at hz1 ⊢; linarith)]
  linarith

private theorem lambdaM_sSup (a : ℝ) : lambdaM speeds a =
    1-sSup (Set.image (fun θ : ℂ => ‖θ‖)
      (eigenvaluesMeanZero (positionSpeed speeds a) ((fun (_p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds})) => (1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ)))))) := by
  exact congrArg (fun I : Fintype (ZMod 11 × {v : ZMod 11 // v ∈ speeds}) =>
    @spectralGapOnMeanZero (ZMod 11 × {v : ZMod 11 // v ∈ speeds}) I (positionSpeed speeds a) ((fun (_p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds})) => (1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ)))))
    (Subsingleton.elim _ _)

private theorem endpoint_gap (a : ℝ) (ha : a=1/5 ∨ a=3/10) : 261/500 < lambdaM speeds a := by
  classical
  let E := eigenvaluesMeanZero (positionSpeed speeds a) ((fun (_p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds})) => (1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ))))
  have hf : (Set.image (fun θ : ℂ => ‖θ‖) E).Finite :=
    (finite_mean_zero_eigenvalues (positionSpeed speeds a) ((fun (_p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds})) => (1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ))))).image _
  have hn : (Set.image (fun θ : ℂ => ‖θ‖) E).Nonempty :=
    ⟨‖(a:ℂ)‖,⟨a,a_is_mean_zero_eigenvalue a,rfl⟩⟩
  have hb : BddAbove (Set.image (fun θ : ℂ => ‖θ‖) E) := hf.bddAbove
  have hr : sSup (Set.image (fun θ : ℂ => ‖θ‖) E) < R :=
    (hf.csSup_lt_iff hn).mpr (by
      rintro r ⟨θ,hθ,rfl⟩
      exact endpoint_eigenvalue_bound a ha θ hθ)
  rw [lambdaM_sSup]
  change 261/500 < 1-sSup (Set.image (fun θ : ℂ => ‖θ‖) E)
  norm_num [R] at hr
  linarith

private theorem middle_gap : lambdaM speeds (1/4) < 261/500 := by
  classical
  obtain ⟨θ,hθ,hR⟩ := middle_eigenvalue
  have hf := (finite_mean_zero_eigenvalues (positionSpeed speeds (1/4)) ((fun (_p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds})) => (1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ))))).image
    (fun θ : ℂ => ‖θ‖)
  have hle := le_csSup hf.bddAbove (Set.mem_image_of_mem (fun θ : ℂ => ‖θ‖) hθ)
  rw [lambdaM_sSup]
  change 1-sSup (Set.image (fun θ : ℂ => ‖θ‖)
    (eigenvaluesMeanZero (positionSpeed speeds (1/4)) ((fun (_p : (ZMod 11 × {v : ZMod 11 // v ∈ speeds})) => (1 / ((Fintype.card (ZMod 11) * speeds.card : ℕ) : ℝ)))))) < 261/500
  norm_num [R] at hR
  linarith

private theorem speeds_generate : AddSubgroup.closure (speeds : Set (ZMod 11))=⊤ := by
  apply top_unique
  intro x _
  have h1 : (1:(ZMod 11)) ∈ AddSubgroup.closure (speeds : Set (ZMod 11)) :=
    AddSubgroup.subset_closure (by decide)
  have hh := AddSubgroup.nsmul_mem (AddSubgroup.closure (speeds : Set (ZMod 11))) h1 x.val
  simpa only [nsmul_eq_mul,mul_one,ZMod.natCast_zmod_val] using hh

theorem result : ¬ claim.{0} := by
  intro hclaim
  obtain ⟨a₀,h0,h1,hm,ha,_⟩ := hclaim (ZMod 11) speeds (by decide) (by decide) speeds_generate
  have hleft := endpoint_gap (1/5) (Or.inl rfl)
  have hmid := middle_gap
  have hright := endpoint_gap (3/10) (Or.inr rfl)
  by_cases hpeak : (1/4:ℝ) ≤ a₀
  · have hh := hm (show (1/5:ℝ) ∈ Set.Icc 0 a₀ from ⟨by norm_num,by linarith⟩)
      (show (1/4:ℝ) ∈ Set.Icc 0 a₀ from ⟨by norm_num,hpeak⟩) (by norm_num : (1/5:ℝ) ≤ 1/4)
    linarith
  · have hh := ha (show (1/4:ℝ) ∈ Set.Icc a₀ 1 from ⟨by linarith,by norm_num⟩)
      (show (3/10:ℝ) ∈ Set.Icc a₀ 1 from ⟨by linarith,by norm_num⟩) (by norm_num : (1/4:ℝ) ≤ 3/10)
    linarith

end
end D5.S3.Fourier.DiaconisMicloUnimodality
