/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalRibbonBoundaryWalsh
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalRibbonBoundaryWalsh
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recover an actual one-vertex ribbon scalar boundary sum from five physical binary diagonal-code moments on torus pairing data. -/

import D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh

open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
section WeightedWalsh
open Finset
open scoped BigOperators
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
variable {E : Type*} [Fintype E] [DecidableEq E]

private theorem weightedExpansion (a b : E → ℝ) (T : Finset E) :
    (∏ e : E, (b e + a e*(if e∈T then (-1:ℝ) else 1))) =
      ∑ S : Finset E, ((∏ e ∈ S, a e)*(∏ e ∈ Sᶜ, b e))*sign S T := by
  classical
  have hc (e : E) :
      b e+a e*(if e∈T then (-1:ℝ) else 1) = a e*(if e∈T then -1 else 1)+b e := by
    ring
  simp_rw [hc]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib,sign_symm,sign_char,Character.char]
  ring

/-- Weighted Fourier evaluation with no denominators on the local weights.
The signed Kauffman weights can be inserted even when some b_e is zero. -/
theorem weighted_walsh (f : Finset E → ℝ) (a b : E → ℝ) :
    (∑ T : Finset E, inverse f T *
      (∏ e : E, (b e + a e*(if e∈T then (-1:ℝ) else 1)))) =
      ∑ S : Finset E, ((∏ e ∈ S, a e)*(∏ e ∈ Sᶜ, b e))*f S := by
  classical
  let w (S : Finset E) := (∏ e ∈ S, a e)*(∏ e ∈ Sᶜ, b e)
  simp_rw [weightedExpansion,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  change (∑ T, inverse f T * (w S*sign S T)) = w S*f S
  have h (T : Finset E) : inverse f T * (w S*sign S T) =
      w S*(inverse f T * sign S T) := by ring
  simp_rw [h]
  rw [←Finset.mul_sum]
  change w S * moment (inverse f) S = _
  rw [inverse_moment]
end WeightedWalsh

section StackedHomologyRank
open LinearMap Submodule
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments

section Rank
variable {F X Y H : Type*} [Field F]
  [AddCommGroup X] [Module F X] [FiniteDimensional F X]
  [AddCommGroup Y] [Module F Y] [AddCommGroup H] [Module F H]

/-- Stacking two observations adds only the rank of the second on the
first observation's kernel; away from that kernel it adds no rank. -/
theorem stacked_rank (A : X →ₗ[F] Y) (B : X →ₗ[F] H) :
    Module.finrank F (A.prod B).range =
      Module.finrank F A.range + Module.finrank F (B.comp A.ker.subtype).range := by
  have h := finrank_range_add_finrank_ker A
  have hs := finrank_range_add_finrank_ker (A.prod B)
  have hk := finrank_range_add_finrank_ker (B.comp A.ker.subtype)
  have he : Module.finrank F (B.comp A.ker.subtype).ker =
      Module.finrank F (A.prod B).ker := by
    rw [← Submodule.finrank_map_subtype_eq A.ker (B.comp A.ker.subtype).ker]
    rw [LinearMap.ker_comp,Submodule.map_comap_subtype,LinearMap.ker_prod]
  rw [he] at hk
  omega

/-- For an incidence map A and edge-label map B, the cycle-label homology
image is W. Quotienting by L cancels exactly the image lying in L. -/
theorem stacked_quotient_rank (A : X →ₗ[F] Y) (B : X →ₗ[F] H)
    (L : Submodule F H) :
    let W := (B.comp A.ker.subtype).range
    Module.finrank F (A.prod (L.mkQ.comp B)).range =
      Module.finrank F A.range + (Module.finrank F W - Module.finrank F ↥(W ⊓ L : Submodule F H)) := by
  let W := (B.comp A.ker.subtype).range
  have h := finrank_range_add_finrank_ker (L.mkQ.comp W.subtype)
  have hr : (L.mkQ.comp W.subtype).range =
      ((L.mkQ.comp B).comp A.ker.subtype).range := by
    rw [LinearMap.range_comp,Submodule.range_subtype,LinearMap.comp_assoc,LinearMap.range_comp]
  have hk : Module.finrank F (L.mkQ.comp W.subtype).ker = Module.finrank F ↥(W ⊓ L : Submodule F H) := by
    rw [← Submodule.finrank_map_subtype_eq W (L.mkQ.comp W.subtype).ker]
    rw [LinearMap.ker_comp,Submodule.map_comap_subtype,Submodule.ker_mkQ]
  rw [hr,hk] at h
  dsimp only
  rw [stacked_rank]
  change Module.finrank F A.range + Module.finrank F ((L.mkQ.comp B).comp A.ker.subtype).range =
    Module.finrank F A.range + (Module.finrank F W - Module.finrank F ↥(W ⊓ L : Submodule F H))
  omega

omit [FiniteDimensional F X] in
theorem coboundary_cancels_on_cycles (A : X →ₗ[F] Y) (B : X →ₗ[F] H)
    (C : Y →ₗ[F] H) :
    ((B+C.comp A).comp A.ker.subtype).range = (B.comp A.ker.subtype).range := by
  congr 1
  ext x
  have hx : A (x : X) = 0 := x.prop
  simp [hx]
end Rank

section Columns
variable {F Y H E : Type*} [Field F]
  [AddCommGroup Y] [Module F Y] [AddCommGroup H] [Module F H]
  [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
private theorem rank_columns (v : E→Y) (S : Finset E) :
    (Fintype.linearCombination F fun i : S => v i).range = columns (F:=F) v S := by
  rw [Fintype.range_linearCombination, columns]
  congr 1
  ext y
  change (∃ i : S, v i = y) ↔ ∃ i, i ∈ (S : Set E) ∧ v i = y
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,i.prop,hi⟩
  · rintro ⟨i,hi,he⟩
    exact ⟨⟨i,hi⟩,he⟩

/-- The physical diagonal state can use the actual stacked columns themselves;
the new span rank is controlled by edge labels on supported cycles only. -/
theorem augmented_column_rank (v : E → Y) (ell : E → H) (L : Submodule F H)
    (S : Finset E) :
    let A := Fintype.linearCombination F fun i : S => v i
    let B := Fintype.linearCombination F fun i : S => ell i
    let W := (B.comp A.ker.subtype).range
    Module.finrank F (columns (F:=F) (fun i => (v i,L.mkQ (ell i))) S) =
      Module.finrank F (columns (F:=F) v S) +
      (Module.finrank F W - Module.finrank F ↥(W ⊓ L : Submodule F H)) := by
  classical
  let A := Fintype.linearCombination F fun i : S => v i
  let B := Fintype.linearCombination F fun i : S => ell i
  have hprod : (Fintype.linearCombination F fun i : S => (v i,L.mkQ (ell i))) =
        A.prod (L.mkQ.comp B) := by
    ext x <;> simp [A,B,Fintype.linearCombination_apply_single]
  dsimp only
  rw [← rank_columns _ S, ← rank_columns _ S, hprod]
  exact stacked_quotient_rank A B L

end Columns
end StackedHomologyRank

section TorusHomologyWalsh
open Finset Matrix
open scoped BigOperators Classical MatrixOrder ComplexOrder
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments

/-- The residual possible increments in the torus when the incidence
columns are augmented by the three line quotients and full homology. -/
inductive TorusRankProfile : ℕ → ℕ → ℕ → ℕ → ℕ → Prop
  | zero : TorusRankProfile 0 0 0 0 0
  | line₁ : TorusRankProfile 0 1 1 1 0
  | line₂ : TorusRankProfile 1 0 1 1 0
  | line₃ : TorusRankProfile 1 1 0 1 0
  | full : TorusRankProfile 1 1 1 2 1

noncomputable def torusMix (q m₀ m₁ m₂ m₃ m₄ : ℝ) : ℝ :=
  (-2*m₀+q*(m₁+m₂+m₃)-2*q*m₄)/(q-2)

theorem torus_quotient_cancellation (q : ℝ) (hq : q ≠ 0) (hq2 : q ≠ 2)
    (r u v w t g : ℕ) (hp : TorusRankProfile u v w t g) :
    torusMix q ((q⁻¹)^r) ((q⁻¹)^(r+u)) ((q⁻¹)^(r+v))
      ((q⁻¹)^(r+w)) ((q⁻¹)^(r+t)) = (q⁻¹)^(r+g) := by
  have hq2' : q-2 ≠ 0 := sub_ne_zero.mpr hq2
  cases hp <;> simp only [torusMix,pow_add,pow_zero,pow_one,mul_one] <;>
    field_simp [hq,hq2'] <;> ring

/-- At q=2, no fixed coefficients for these five moments work on all
zero, line and full homology profiles, even with incidence rank zero. -/
theorem torus_five_moments_no_q_two (a b c d e : ℝ)
    (h₀ : a+b+c+d+e=1)
    (h₁ : a+b+c/2+d/2+e/2=1)
    (h₂ : a+b/2+c+d/2+e/2=1)
    (h₃ : a+b/2+c/2+d+e/2=1)
    (h₄ : a+b/2+c/2+d/2+e/4=1/2) : False := by
  linarith only [h₀,h₁,h₂,h₃,h₄]

section Actual
variable {F V E : Type*} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Fintype (Module.Dual F V)]
  [Fintype E] [DecidableEq E]

/-- Physical input is the actual marginal of a complex diagonal density;
the incidence/quotient encoding is supplied via its ranks. -/
noncomputable def readMoment (v : E → V) (K : ℝ) (S : Finset E) : ℝ :=
  (((mixedMarginal (F:=F) v S)^K).trace).re

theorem actual_torus_moment (v₀ v₁ v₂ v₃ v₄ : E → V) {K : ℝ} (hK : 0<K)
    (q : ℝ) (hq : q ≠ 0) (hq2 : q ≠ 2) (hcal : (Fintype.card F:ℝ)^(1-K)=q⁻¹)
    (S : Finset E) (r u v w t g : ℕ) (hp : TorusRankProfile u v w t g)
    (h₀ : Module.finrank F (columns (F:=F) v₀ S)=r)
    (h₁ : Module.finrank F (columns (F:=F) v₁ S)=r+u)
    (h₂ : Module.finrank F (columns (F:=F) v₂ S)=r+v)
    (h₃ : Module.finrank F (columns (F:=F) v₃ S)=r+w)
    (h₄ : Module.finrank F (columns (F:=F) v₄ S)=r+t) :
    torusMix q (readMoment (F:=F) v₀ K S) (readMoment (F:=F) v₁ K S) (readMoment (F:=F) v₂ K S)
      (readMoment (F:=F) v₃ K S) (readMoment (F:=F) v₄ K S) = (q⁻¹)^(r+g) := by
  simp only [readMoment, actual_column_moment _ _ hK, hcal, h₀, h₁, h₂, h₃, h₄]
  exact torus_quotient_cancellation q hq hq2 r u v w t g hp

private theorem genusBoundary (d : ℝ) (hd : d≠0) (n k c r g : ℕ)
    (h : n+k=c+2*(r+g)) : d^n*d^k*((d^2)⁻¹)^(r+g)=d^c := by
  rw [←pow_add,h,pow_add,inv_pow,←pow_mul]
  rw [mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hd),mul_one]

/-- Conditional exact scalar torus circle sum from a signed mixture of five
actual density-marginal moment inputs. Neither smoothing weight is divided by.
The rank profiles and topological Euler identity are explicit hypotheses. -/
theorem actual_torus_walsh (v₀ v₁ v₂ v₃ v₄ : E → V) {K : ℝ} (hK : 0<K)
    (a b : E → ℝ) (d : ℝ) (hd : d≠0) (hd2 : d^2 ≠ 2)
    (hcal : (Fintype.card F:ℝ)^(1-K)=(d^2)⁻¹)
    (n : ℕ) (c r u v w t g : Finset E → ℕ)
    (hp : ∀ S, TorusRankProfile (u S) (v S) (w S) (t S) (g S))
    (h₀ : ∀ S, Module.finrank F (columns (F:=F) v₀ S)=r S)
    (h₁ : ∀ S, Module.finrank F (columns (F:=F) v₁ S)=r S+u S)
    (h₂ : ∀ S, Module.finrank F (columns (F:=F) v₂ S)=r S+v S)
    (h₃ : ∀ S, Module.finrank F (columns (F:=F) v₃ S)=r S+w S)
    (h₄ : ∀ S, Module.finrank F (columns (F:=F) v₄ S)=r S+t S)
    (hboundary : ∀ S, n+S.card=c S+2*(r S+g S)) :
    let f := fun S => torusMix (d^2) (readMoment (F:=F) v₀ K S) (readMoment (F:=F) v₁ K S)
      (readMoment (F:=F) v₂ K S) (readMoment (F:=F) v₃ K S) (readMoment (F:=F) v₄ K S)
    d^n*(∑ T : Finset E, inverse f T*(∏ e : E, (b e+(d*a e)*(if e∈T then (-1:ℝ) else 1)))) =
      ∑ S : Finset E, ((∏ e ∈ S, a e)*(∏ e ∈ Sᶜ, b e))*d^(c S) := by
  dsimp only
  rw [weighted_walsh,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [actual_torus_moment v₀ v₁ v₂ v₃ v₄ hK _ (pow_ne_zero _ hd) hd2 hcal S
    (r S) (u S) (v S) (w S) (t S) (g S) (hp S) (h₀ S) (h₁ S) (h₂ S) (h₃ S) (h₄ S)]
  rw [Finset.prod_mul_distrib,Finset.prod_const]
  calc
    _ = ((∏ e ∈ S, a e)*(∏ e ∈ Sᶜ, b e)) *
      (d^n*d^S.card*((d^2)⁻¹)^(r S+g S)) := by ring
    _ = _ := by rw [genusBoundary d hd n S.card (c S) (r S) (g S) (hboundary S)]
end Actual
end TorusHomologyWalsh

section TorusStackedWalsh
open LinearMap Submodule Finset Matrix
open scoped BigOperators Classical MatrixOrder ComplexOrder
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments

section Rank
variable {F X Y H H' : Type*} [Field F]
  [AddCommGroup X] [Module F X] [FiniteDimensional F X]
  [AddCommGroup Y] [Module F Y] [AddCommGroup H] [Module F H]
  [AddCommGroup H'] [Module F H']

theorem stacked_postcompose_rank (A : X →ₗ[F] Y) (B : X →ₗ[F] H) (P : H →ₗ[F] H') :
    let W := (B.comp A.ker.subtype).range
    Module.finrank F (A.prod (P.comp B)).range =
      Module.finrank F A.range +
        (Module.finrank F W - Module.finrank F ↥(W ⊓ P.ker : Submodule F H)) := by
  let W := (B.comp A.ker.subtype).range
  have h := finrank_range_add_finrank_ker (P.comp W.subtype)
  have hr : (P.comp W.subtype).range = ((P.comp B).comp A.ker.subtype).range := by
    rw [LinearMap.range_comp,Submodule.range_subtype,LinearMap.comp_assoc,LinearMap.range_comp]
  have hk : Module.finrank F (P.comp W.subtype).ker =
      Module.finrank F ↥(W ⊓ P.ker : Submodule F H) := by
    rw [← Submodule.finrank_map_subtype_eq W (P.comp W.subtype).ker]
    rw [LinearMap.ker_comp,Submodule.map_comap_subtype]
  rw [hr,hk] at h
  dsimp only
  rw [stacked_rank]
  change Module.finrank F A.range + Module.finrank F ((P.comp B).comp A.ker.subtype).range =
    Module.finrank F A.range + (Module.finrank F W - Module.finrank F ↥(W ⊓ P.ker : Submodule F H))
  omega
end Rank

section Columns
variable {F Y H E : Type*} [Field F]
  [AddCommGroup Y] [Module F Y] [AddCommGroup H] [Module F H]
  [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
private theorem col_range (v : E→Y) (S : Finset E) :
    (Fintype.linearCombination F fun i : S => v i).range = columns (F:=F) v S := by
  rw [Fintype.range_linearCombination, columns]
  congr 1
  ext y
  change (∃ i : S, v i = y) ↔ ∃ i, i ∈ (S : Set E) ∧ v i = y
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,i.prop,hi⟩
  · rintro ⟨i,hi,he⟩
    exact ⟨⟨i,hi⟩,he⟩

def cyclesImage (v : E → Y) (ell : E → H) (S : Finset E) : Submodule F H :=
  let A := Fintype.linearCombination F fun i : S => v i
  let B := Fintype.linearCombination F fun i : S => ell i
  (B.comp A.ker.subtype).range

theorem projected_column_rank (v : E → Y) (ell : E → H) (P : H →ₗ[F] H) (S : Finset E) :
    let W := cyclesImage (F:=F) v ell S
    Module.finrank F (columns (F:=F) (fun i => (v i,P (ell i))) S) =
      Module.finrank F (columns (F:=F) v S) +
      (Module.finrank F W - Module.finrank F ↥(W ⊓ P.ker : Submodule F H)) := by
  classical
  let A := Fintype.linearCombination F fun i : S => v i
  let B := Fintype.linearCombination F fun i : S => ell i
  have hprod : (Fintype.linearCombination F fun i : S => (v i,P (ell i))) =
        A.prod (P.comp B) := by
    ext x <;> simp [A,B,Fintype.linearCombination_apply_single]
  dsimp only
  rw [← col_range _ S, ← col_range _ S, hprod]
  exact stacked_postcompose_rank A B P
end Columns

section Torus
variable {F Y H E : Type*} [Field F] [Fintype F] [DecidableEq F]
  [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y]
  [AddCommGroup H] [Module F H] [FiniteDimensional F H] [Fintype (Module.Dual F (Y × H))]
  [Fintype E] [DecidableEq E]

noncomputable def rankInc (W : Submodule F H) (L : Submodule F H) : ℕ :=
  Module.finrank F W - Module.finrank F ↥(W ⊓ L : Submodule F H)

/-- The five inputs are now the actual augmented incidence states, not
independent abstract black boxes with assumed spectra. Only the topological
rank profile and Euler relation are supplied. -/
theorem actual_stacked_torus_walsh
    (v : E → Y) (ell : E → H) (P₁ P₂ P₃ : H →ₗ[F] H)
    {K : ℝ} (hK : 0<K) (a b : E → ℝ) (d : ℝ)
    (hd : d≠0) (hd2 : d^2 ≠ 2) (hcal : (Fintype.card F:ℝ)^(1-K)=(d^2)⁻¹)
    (n : ℕ) (c g : Finset E → ℕ)
    (hp : ∀ S, let W := cyclesImage (F:=F) v ell S
      TorusRankProfile (rankInc W P₁.ker) (rankInc W P₂.ker) (rankInc W P₃.ker)
        (Module.finrank F W) (g S))
    (hboundary : ∀ S, n+S.card=c S+2*(Module.finrank F (columns (F:=F) v S)+g S)) :
    let f := fun S => torusMix (d^2)
      (readMoment (F:=F) (fun i => (v i,(0:H))) K S)
      (readMoment (F:=F) (fun i => (v i,P₁ (ell i))) K S)
      (readMoment (F:=F) (fun i => (v i,P₂ (ell i))) K S)
      (readMoment (F:=F) (fun i => (v i,P₃ (ell i))) K S)
      (readMoment (F:=F) (fun i => (v i,ell i)) K S)
    d^n*(∑ T : Finset E, inverse f T*(∏ e : E, (b e+(d*a e)*(if e∈T then (-1:ℝ) else 1)))) =
      ∑ S : Finset E, ((∏ e ∈ S, a e)*(∏ e ∈ Sᶜ, b e))*d^(c S) := by
  let W := cyclesImage (F:=F) v ell
  let r := fun S => Module.finrank F (columns (F:=F) v S)
  have h₀ S : Module.finrank F (columns (F:=F) (fun i => (v i,(0:H))) S)=r S := by
    have hh := projected_column_rank v ell (0 : H →ₗ[F] H) S
    change Module.finrank F (columns (F:=F) (fun i => (v i,(0:H))) S) =
      r S + (Module.finrank F (W S) -
        Module.finrank F ↥(W S ⊓ LinearMap.ker (0 : H →ₗ[F] H) : Submodule F H)) at hh
    rw [LinearMap.ker_zero,inf_top_eq,Nat.sub_self,add_zero] at hh
    exact hh
  have h₄ S : Module.finrank F (columns (F:=F) (fun i => (v i,ell i)) S)=r S+Module.finrank F (W S) := by
    have hh := projected_column_rank v ell (LinearMap.id : H →ₗ[F] H) S
    change Module.finrank F (columns (F:=F) (fun i => (v i,ell i)) S) =
      r S + (Module.finrank F (W S) -
        Module.finrank F ↥(W S ⊓ LinearMap.ker (LinearMap.id : H →ₗ[F] H) : Submodule F H)) at hh
    rw [LinearMap.ker_id,inf_bot_eq,finrank_bot,Nat.sub_zero] at hh
    exact hh
  exact actual_torus_walsh _ _ _ _ _ hK a b d hd hd2 hcal n c r
    (fun S => rankInc (W S) P₁.ker) (fun S => rankInc (W S) P₂.ker)
    (fun S => rankInc (W S) P₃.ker) (fun S => Module.finrank F (W S)) g hp h₀
    (fun S => projected_column_rank v ell P₁ S) (fun S => projected_column_rank v ell P₂ S)
    (fun S => projected_column_rank v ell P₃ S) h₄ hboundary

end Torus
end TorusStackedWalsh

section BinaryTorusProfiles
open LinearMap Submodule Finset Matrix
open scoped BigOperators Classical MatrixOrder ComplexOrder
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments

abbrev F₂ := ZMod 2
abbrev H₂ := F₂ × F₂

private def a₁ : H₂ := (1,0)
private def a₂ : H₂ := (0,1)
private def a₃ : H₂ := (1,1)
private def L₁ : Submodule F₂ H₂ := F₂ ∙ a₁
private def L₂ : Submodule F₂ H₂ := F₂ ∙ a₂
private def L₃ : Submodule F₂ H₂ := F₂ ∙ a₃

def firstLineProjection : H₂ →ₗ[F₂] H₂ :=
  (0 : H₂ →ₗ[F₂] F₂).prod (LinearMap.snd F₂ F₂ F₂)
def secondLineProjection : H₂ →ₗ[F₂] H₂ :=
  (LinearMap.fst F₂ F₂ F₂).prod 0
def diagonalLineProjection : H₂ →ₗ[F₂] H₂ :=
  (LinearMap.fst F₂ F₂ F₂ - LinearMap.snd F₂ F₂ F₂).prod 0

private theorem elements : ∀ x : H₂, x=0 ∨ x=a₁ ∨ x=a₂ ∨ x=a₃ := by decide
private theorem scalars : ∀ x : F₂, x=0 ∨ x=1 := by decide
private theorem a₁_ne : a₁ ≠ 0 := by decide
private theorem a₂_ne : a₂ ≠ 0 := by decide
private theorem a₃_ne : a₃ ≠ 0 := by decide

private theorem mem_line (x y : H₂) : x ∈ F₂ ∙ y ↔ x=0 ∨ x=y := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨k,hk⟩
    rcases scalars k with h | h <;> subst k
    · exact Or.inl (by simpa using hk.symm)
    · exact Or.inr (by simpa using hk.symm)
  · rintro (rfl | rfl)
    · exact ⟨0,zero_smul _ _⟩
    · exact ⟨1,one_smul _ _⟩

private theorem ker₁ : firstLineProjection.ker = L₁ := by
  ext x
  rw [LinearMap.mem_ker, L₁, mem_line]
  exact (show ∀ x : H₂, firstLineProjection x = 0 ↔ x=0 ∨ x=a₁ by decide) x
private theorem ker₂ : secondLineProjection.ker = L₂ := by
  ext x
  rw [LinearMap.mem_ker, L₂, mem_line]
  exact (show ∀ x : H₂, secondLineProjection x = 0 ↔ x=0 ∨ x=a₂ by decide) x
private theorem ker₃ : diagonalLineProjection.ker = L₃ := by
  ext x
  rw [LinearMap.mem_ker, L₃, mem_line]
  exact (show ∀ x : H₂, diagonalLineProjection x = 0 ↔ x=0 ∨ x=a₃ by decide) x

private theorem lines_inf (x y : H₂) (hxy : x≠y) :
    (F₂ ∙ x) ⊓ (F₂ ∙ y) = ⊥ := by
  ext z
  change (z ∈ F₂ ∙ x ∧ z ∈ F₂ ∙ y) ↔ z ∈ (⊥ : Submodule F₂ H₂)
  rw [mem_line,mem_line,Submodule.mem_bot]
  constructor
  · rintro ⟨hz | hz, hw | hw⟩
    · exact hz
    · exact hz
    · exact hw
    · exact (hxy (hz.symm.trans hw)).elim
  · intro h
    exact ⟨Or.inl h, Or.inl h⟩

private theorem hdim : Module.finrank F₂ H₂=2 := by
  norm_num [Module.finrank_prod,Module.finrank_self]
private theorem d₁ : Module.finrank F₂ L₁=1 := finrank_span_singleton a₁_ne
private theorem d₂ : Module.finrank F₂ L₂=1 := finrank_span_singleton a₂_ne
private theorem d₃ : Module.finrank F₂ L₃=1 := finrank_span_singleton a₃_ne

private theorem classify (W : Submodule F₂ H₂) :
    W=⊥ ∨ W=L₁ ∨ W=L₂ ∨ W=L₃ ∨ W=⊤ := by
  have hle : Module.finrank F₂ W ≤ 2 := by
    have hh := Submodule.finrank_le W
    rw [hdim] at hh
    exact hh
  have hcases : Module.finrank F₂ W=0 ∨ Module.finrank F₂ W=1 ∨ Module.finrank F₂ W=2 := by omega
  rcases hcases with h | h | h
  · exact Or.inl (Submodule.finrank_eq_zero.mp h)
  · have hne : W ≠ ⊥ := by
      intro he; rw [he,finrank_bot] at h; contradiction
    obtain ⟨x,hx,hxne⟩ := W.ne_bot_iff.mp hne
    rcases elements x with he | he | he | he
    · exact (hxne he).elim
    · subst x
      exact Or.inr (Or.inl (Submodule.eq_of_le_of_finrank_eq
        (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) (d₁.trans h.symm)).symm)
    · subst x
      exact Or.inr (Or.inr (Or.inl (Submodule.eq_of_le_of_finrank_eq
        (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) (d₂.trans h.symm)).symm))
    · subst x
      exact Or.inr (Or.inr (Or.inr (Or.inl (Submodule.eq_of_le_of_finrank_eq
        (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) (d₃.trans h.symm)).symm)))
  · have htop : Module.finrank F₂ (⊤ : Submodule F₂ H₂)=2 := by rw [finrank_top,hdim]
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (Submodule.eq_of_le_of_finrank_eq le_top (h.trans htop.symm)))))

noncomputable def binaryTorusGenus (W : Submodule F₂ H₂) : ℕ :=
  if Module.finrank F₂ W=2 then 1 else 0

/-- The three coordinate quotients exhaust all line profiles in binary
two-dimensional homology. No finite enumeration of edge subsets is needed. -/
theorem binary_torus_profile (W : Submodule F₂ H₂) :
    TorusRankProfile (rankInc W firstLineProjection.ker) (rankInc W secondLineProjection.ker)
      (rankInc W diagonalLineProjection.ker) (Module.finrank F₂ W) (binaryTorusGenus W) := by
  rw [ker₁,ker₂,ker₃]
  have i₁₂ : L₁ ⊓ L₂ = ⊥ := lines_inf _ _ (by decide : a₁≠a₂)
  have i₁₃ : L₁ ⊓ L₃ = ⊥ := lines_inf _ _ (by decide : a₁≠a₃)
  have i₂₃ : L₂ ⊓ L₃ = ⊥ := lines_inf _ _ (by decide : a₂≠a₃)
  have i₂₁ : L₂ ⊓ L₁ = ⊥ := (inf_comm _ _).trans i₁₂
  have i₃₁ : L₃ ⊓ L₁ = ⊥ := (inf_comm _ _).trans i₁₃
  have i₃₂ : L₃ ⊓ L₂ = ⊥ := (inf_comm _ _).trans i₂₃
  rcases classify W with h | h | h | h | h <;> subst W
  · simpa [rankInc,binaryTorusGenus,bot_inf_eq,finrank_bot] using TorusRankProfile.zero
  · unfold rankInc binaryTorusGenus
    rw [inf_idem,i₁₂,i₁₃,d₁,finrank_bot]
    exact TorusRankProfile.line₁
  · unfold rankInc binaryTorusGenus
    rw [inf_idem,i₂₁,i₂₃,d₂,finrank_bot]
    exact TorusRankProfile.line₂
  · unfold rankInc binaryTorusGenus
    rw [inf_idem,i₃₁,i₃₂,d₃,finrank_bot]
    exact TorusRankProfile.line₃
  · unfold rankInc binaryTorusGenus
    rw [top_inf_eq,top_inf_eq,top_inf_eq,finrank_top,hdim,d₁,d₂,d₃]
    exact TorusRankProfile.full


private def omega (x y : H₂) : F₂ := x.1*y.2-x.2*y.1

/-- The actual restriction of the standard alternating intersection form
on the binary torus plane to the cycle-label image. -/
def binaryTorusIntersection (W : Submodule F₂ H₂) : W →ₗ[F₂] Module.Dual F₂ W :=
  LinearMap.mk₂ F₂ (fun x y : W => omega x y)
    (by intro x y z; change omega (x.val+y.val) z.val = _; simp [omega]; ring)
    (by intro k x y; change omega (k • x.val) y.val = _; simp [omega,smul_eq_mul]; ring)
    (by intro x y z; change omega x.val (y.val+z.val) = _; simp [omega]; ring)
    (by intro k x y; change omega x.val (k • y.val) = _; simp [omega,smul_eq_mul]; ring)

private theorem zero_pairing_line (z : H₂) :
    binaryTorusIntersection (F₂ ∙ z) = 0 := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change omega x.val y.val = 0
  rcases (mem_line _ _).mp x.prop with hx | hx <;>
    rcases (mem_line _ _).mp y.prop with hy | hy <;> rw [hx,hy] <;> simp [omega,mul_comm]

private theorem zero_pairing_bot :
    binaryTorusIntersection (⊥ : Submodule F₂ H₂) = 0 := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change omega x.val y.val = 0
  have hx : x.val=0 := by simpa only [Submodule.mem_bot] using x.prop
  rw [hx]
  simp [omega]

private theorem pairing_top_injective :
    Function.Injective (binaryTorusIntersection (⊤ : Submodule F₂ H₂)) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  let e₁ : (⊤ : Submodule F₂ H₂) := ⟨a₁,Submodule.mem_top⟩
  let e₂ : (⊤ : Submodule F₂ H₂) := ⟨a₂,Submodule.mem_top⟩
  have h₁ := congrArg (fun l : Module.Dual F₂ (⊤ : Submodule F₂ H₂) => l e₁) hx
  have h₂ := congrArg (fun l : Module.Dual F₂ (⊤ : Submodule F₂ H₂) => l e₂) hx
  change omega x.val a₁ = 0 at h₁
  change omega x.val a₂ = 0 at h₂
  apply Subtype.ext
  exact Prod.ext (by simpa [omega,a₂] using h₂) (by simpa [omega,a₁] using h₁)

/-- Algebraic bridge to surface topology: genus is half the rank of
the actual restricted intersection pairing, not half the homology dimension. -/
theorem binary_torus_intersection_rank (W : Submodule F₂ H₂) :
    Module.finrank F₂ (binaryTorusIntersection W).range = 2 * binaryTorusGenus W := by
  rcases classify W with h | h | h | h | h <;> subst W
  · rw [zero_pairing_bot,LinearMap.range_zero,finrank_bot]
    norm_num [binaryTorusGenus,finrank_bot]
  · rw [show binaryTorusIntersection L₁=0 from zero_pairing_line a₁,
        LinearMap.range_zero,finrank_bot]
    norm_num [binaryTorusGenus,d₁]
  · rw [show binaryTorusIntersection L₂=0 from zero_pairing_line a₂,
        LinearMap.range_zero,finrank_bot]
    norm_num [binaryTorusGenus,d₂]
  · rw [show binaryTorusIntersection L₃=0 from zero_pairing_line a₃,
        LinearMap.range_zero,finrank_bot]
    norm_num [binaryTorusGenus,d₃]
  · rw [LinearMap.finrank_range_of_inj pairing_top_injective,finrank_top,hdim]
    norm_num [binaryTorusGenus,finrank_top,hdim]

section Physical
variable {Y E : Type*} [AddCommGroup Y] [Module F₂ Y] [FiniteDimensional F₂ Y]
  [Fintype (Module.Dual F₂ (Y × H₂))] [Fintype E] [DecidableEq E]

/-- End-to-end conditional physical evaluation. Its only remaining geometric
hypothesis is the scalar circle/column-rank Euler identity with binary genus. -/
theorem actual_binary_torus_walsh
    (v : E → Y) (ell : E → H₂) {K : ℝ} (hK : 0<K) (a b : E → ℝ) (d : ℝ)
    (hd : d≠0) (hd2 : d^2 ≠ 2) (hcal : (Fintype.card F₂:ℝ)^(1-K)=(d^2)⁻¹)
    (n : ℕ) (c : Finset E → ℕ)
    (hboundary : ∀ S, n+S.card=c S+2*(Module.finrank F₂ (columns (F:=F₂) v S) +
        binaryTorusGenus (cyclesImage (F:=F₂) v ell S))) :
    let f := fun S => torusMix (d^2)
      (readMoment (F:=F₂) (fun i => (v i,(0:H₂))) K S)
      (readMoment (F:=F₂) (fun i => (v i,firstLineProjection (ell i))) K S)
      (readMoment (F:=F₂) (fun i => (v i,secondLineProjection (ell i))) K S)
      (readMoment (F:=F₂) (fun i => (v i,diagonalLineProjection (ell i))) K S)
      (readMoment (F:=F₂) (fun i => (v i,ell i)) K S)
    d^n*(∑ T : Finset E, inverse f T*(∏ e : E, (b e+(d*a e)*(if e∈T then (-1:ℝ) else 1)))) =
      ∑ S : Finset E, ((∏ e ∈ S, a e)*(∏ e ∈ Sᶜ, b e))*d^(c S) :=
  actual_stacked_torus_walsh v ell firstLineProjection secondLineProjection diagonalLineProjection
    hK a b d hd hd2 hcal n c _ (fun S => binary_torus_profile (cyclesImage (F:=F₂) v ell S)) hboundary

end Physical
end BinaryTorusProfiles

section RealTorusCalibration
open Finset Matrix
open scoped BigOperators Classical MatrixOrder ComplexOrder
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments

noncomputable def bracketLoop (A : ℝ) : ℝ := -(A^2+(A⁻¹)^2)
noncomputable def bracketOrder (A : ℝ) : ℝ :=
  1+Real.log ((bracketLoop A)^2)/Real.log 2

/-- The loop calibration avoids the exact non-reconstructible q=2, with no
numeric approximation of the entropy order or the bracket parameter. -/
theorem bracket_calibration (A : ℝ) (hA : 0<A) :
    bracketLoop A ≠ 0 ∧ (bracketLoop A)^2 ≠ 2 ∧
      0<bracketOrder A ∧ (Fintype.card F₂:ℝ)^(1-bracketOrder A)=((bracketLoop A)^2)⁻¹ := by
  have hi : A * A⁻¹=1 := mul_inv_cancel₀ hA.ne'
  have hs : 2 ≤ A^2+(A⁻¹)^2 := by nlinarith [sq_nonneg (A-A⁻¹)]
  have hd : bracketLoop A≠0 := by unfold bracketLoop; linarith
  have hq : 4≤(bracketLoop A)^2 := by
    unfold bracketLoop
    nlinarith [mul_nonneg (show 0≤A^2+(A⁻¹)^2-2 by linarith)
      (show 0≤A^2+(A⁻¹)^2+2 by linarith)]
  have hq' : 0<(bracketLoop A)^2 := by linarith
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hc : (Fintype.card F₂:ℝ)=2 := by norm_num [F₂, ZMod.card]
  refine ⟨hd,(by linarith),?_,?_⟩
  · unfold bracketOrder
    have ht := Real.log_nonneg (show 1≤(bracketLoop A)^2 by linarith)
    have hpos := div_nonneg ht hl.le
    linarith
  · rw [hc, Real.rpow_def_of_pos (by norm_num : 0<(2:ℝ))]
    unfold bracketOrder
    have he : Real.log 2*(1-(1+Real.log ((bracketLoop A)^2)/Real.log 2)) =
        -Real.log ((bracketLoop A)^2) := by field_simp [hl.ne']; ring
    rw [he,Real.exp_neg,Real.exp_log hq']

section Physical
variable {Y E : Type*} [AddCommGroup Y] [Module F₂ Y] [FiniteDimensional F₂ Y]
  [Fintype (Module.Dual F₂ (Y × H₂))] [Fintype E] [DecidableEq E]

/-- A single geometric scalar Euler identity now suffices for the real
Kauffman loop parameter family, expressed using the native pairing rank. -/
theorem actual_real_torus_bracket_walsh
    (v : E → Y) (ell : E → H₂) (a b : E → ℝ) (A : ℝ) (hA : 0<A)
    (n : ℕ) (c : Finset E → ℕ)
    (hboundary : ∀ S, n+S.card=c S+2*Module.finrank F₂ (columns (F:=F₂) v S) +
      Module.finrank F₂ (binaryTorusIntersection (cyclesImage (F:=F₂) v ell S)).range) :
    let d := bracketLoop A
    let K := bracketOrder A
    let f := fun S => torusMix (d^2)
      (readMoment (F:=F₂) (fun i => (v i,(0:H₂))) K S)
      (readMoment (F:=F₂) (fun i => (v i,firstLineProjection (ell i))) K S)
      (readMoment (F:=F₂) (fun i => (v i,secondLineProjection (ell i))) K S)
      (readMoment (F:=F₂) (fun i => (v i,diagonalLineProjection (ell i))) K S)
      (readMoment (F:=F₂) (fun i => (v i,ell i)) K S)
    d^n*(∑ T : Finset E, inverse f T*(∏ e : E, (b e+(d*a e)*(if e∈T then (-1:ℝ) else 1)))) =
      ∑ S : Finset E, ((∏ e ∈ S, a e)*(∏ e ∈ Sᶜ, b e))*d^(c S) := by
  obtain ⟨hd,hq,hK,hcal⟩ := bracket_calibration A hA
  dsimp only
  apply actual_binary_torus_walsh v ell hK a b (bracketLoop A) hd hq hcal n c
  intro S
  have hs := hboundary S
  rw [binary_torus_intersection_rank] at hs
  omega

end Physical
end RealTorusCalibration

section BouquetHomologyEuler
open Finset LinearMap Submodule
open scoped BigOperators Classical
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments

variable {n : ℕ} {E : Type*} [Fintype E]

/-- The alternating pairing table is pulled back along the surjective map
from chord coefficients to the span of their binary homology labels. -/
theorem interlacement_rank_is_image_pairing (a b : E→Fin (n+1)) (ell : E→H₂)
    (hPair : ∀ e j, (if interlaces a b e j then (1:F₂) else 0) =
      (ell j).1*(ell e).2-(ell j).2*(ell e).1) :
    let B := Fintype.linearCombination F₂ ell
    Module.finrank F₂ (interlacementMap a b).range =
      Module.finrank F₂ (binaryTorusIntersection B.range).range := by
  classical
  let B := Fintype.linearCombination F₂ ell
  let L := B.rangeRestrict
  let C := (binaryTorusIntersection B.range).compl₁₂ L L
  have hL : Function.Surjective L := LinearMap.range_eq_top.mp B.range_rangeRestrict
  have hC := pullback_pairing_rank L hL (binaryTorusIntersection B.range)
  have hc (z : E→F₂) (e : E) :
      C z (Pi.single e 1)=interlacementMap a b z e := by
    have ht : B (Pi.single e 1)=ell e := by simp [B,Fintype.linearCombination_apply_single]
    rw [interlacementMap_apply]
    change (B z).1*(B (Pi.single e 1)).2-(B z).2*(B (Pi.single e 1)).1 = _
    rw [ht]
    change (Fintype.linearCombination F₂ ell z).1*(ell e).2 -
      (Fintype.linearCombination F₂ ell z).2*(ell e).1 = _
    rw [Fintype.linearCombination_apply]
    simp only [Prod.fst_sum,Prod.snd_sum,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    rw [Finset.sum_mul,Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = z j*((ell j).1*(ell e).2-(ell j).2*(ell e).1) := by ring
      _ = _ := by rw [← hPair e j]; split <;> simp_all
  have hk : LinearMap.ker C = LinearMap.ker (interlacementMap a b) := by
    ext z
    change C z=0 ↔ interlacementMap a b z=0
    constructor
    · intro hz
      funext e
      rw [← hc, hz]
      rfl
    · intro hz
      apply (Pi.basisFun F₂ E).ext
      intro e
      rw [Pi.basisFun_apply,hc,hz]
      rfl
  have h₁ := LinearMap.finrank_range_add_finrank_ker C
  have h₂ := LinearMap.finrank_range_add_finrank_ker (interlacementMap a b)
  rw [hk] at h₁
  change Module.finrank F₂ (interlacementMap a b).range +
    Module.finrank F₂ (interlacementMap a b).ker = Module.finrank F₂ (E→F₂) at h₂
  change Module.finrank F₂ C.range = _ at hC
  dsimp only
  change Module.finrank F₂ (interlacementMap a b).range =
    Module.finrank F₂ (binaryTorusIntersection B.range).range
  exact (Nat.add_right_cancel (h₂.trans h₁.symm)).trans hC

/-- Literal one-vertex ribbon Euler equality when the chord interlacement
is represented by binary torus homology labels. The circle count itself is
not a supplied geometric premise. -/
theorem literal_bouquet_homology_euler (sigma alpha : Equiv.Perm (Fin (n+1)))
    (hsigma : ∀ i, sigma i=cyclicNext i) (ha2 : Function.Involutive alpha)
    (a b : E→Fin (n+1)) (ha : Function.Injective a) (hb : Function.Injective b)
    (hd : ∀ e j, a e≠b j) (hsa : ∀ e, alpha (a e)=b e) (hsb : ∀ e, alpha (b e)=a e)
    (hfix : ∀ i, (∀ e, a e≠i) → (∀ e, b e≠i) → alpha i=i)
    (hord : ∀ e, (a e).val < (b e).val) (ell : E→H₂)
    (hPair : ∀ e j, (if interlaces a b e j then (1:F₂) else 0) =
      (ell j).1*(ell e).2-(ell j).2*(ell e).1) :
    let B := Fintype.linearCombination F₂ ell
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (sigma*alpha))) +
      Module.finrank F₂ (binaryTorusIntersection B.range).range =
      1+Fintype.card E := by
  have hg := literal_bouquet_boundary_interlace sigma alpha hsigma ha2 a b ha hb hd hsa hsb hfix hord
  have hr := interlacement_rank_is_image_pairing a b ell hPair
  dsimp only at hr ⊢
  rw [← hr]
  exact hg
end BouquetHomologyEuler

section ActualBouquetBracket
open Finset LinearMap Submodule Matrix
open scoped BigOperators Classical MatrixOrder ComplexOrder
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments

variable {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
private theorem zero_columns (S : Finset E) :
    Module.finrank F₂ (columns (F:=F₂) (fun _ : E => (0:F₂)) S)=0 := by
  suffices he : columns (F:=F₂) (fun _ : E => (0:F₂)) S = ⊥ by rw [he,finrank_bot]
  unfold columns
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨i,hi,rfl⟩
  exact zero_mem _

private theorem cycle_image_at_zero (ell : E→H₂) (S : Finset E) :
    cyclesImage (F:=F₂) (fun _ : E => (0:F₂)) ell S =
      (Fintype.linearCombination F₂ fun i : S => ell i).range := by
  unfold cyclesImage
  dsimp only
  have hz : Fintype.linearCombination F₂ (fun _ : S => (0:F₂)) = 0 := by
    ext i
    simp [Fintype.linearCombination_apply_single]
  rw [hz,LinearMap.ker_zero,LinearMap.range_comp,Submodule.range_subtype,Submodule.map_top]

/-- A family of actual retained-band matching permutations, with no
unselected band allowed to contribute to the current boundary. -/
structure RibbonSwitches (a b : E→Fin (n+1)) (alpha : Finset E→Equiv.Perm (Fin (n+1))) : Prop where
  involution : ∀ S, Function.Involutive (alpha S)
  left : ∀ S, ∀ i ∈ S, alpha S (a i)=b i
  right : ∀ S, ∀ i ∈ S, alpha S (b i)=a i
  fixed : ∀ S i, (∀ e ∈ S, a e≠i) → (∀ e ∈ S, b e≠i) → alpha S i=i

noncomputable def bouquetCircles (sigma : Equiv.Perm (Fin (n+1)))
    (alpha : Finset E→Equiv.Perm (Fin (n+1))) (S : Finset E) : ℕ :=
  Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (sigma*alpha S)))

theorem actual_bouquet_euler_all (sigma : Equiv.Perm (Fin (n+1)))
    (hsigma : ∀ i, sigma i=cyclicNext i)
    (a b : E→Fin (n+1)) (ha : Function.Injective a) (hb : Function.Injective b)
    (hd : ∀ e j, a e≠b j) (hord : ∀ e, (a e).val < (b e).val)
    (alpha : Finset E → Equiv.Perm (Fin (n+1))) (hAlpha : RibbonSwitches a b alpha)
    (ell : E→H₂)
    (hPair : ∀ e j, (if interlaces a b e j then (1:F₂) else 0) =
      (ell j).1*(ell e).2-(ell j).2*(ell e).1)
    (S : Finset E) :
    1+S.card = bouquetCircles sigma alpha S + 2 * Module.finrank F₂ (columns (F:=F₂)
      (fun _ : E => (0:F₂)) S) + Module.finrank F₂ (binaryTorusIntersection
        (cyclesImage (F:=F₂) (fun _ : E => (0:F₂)) ell S)).range := by
  rw [zero_columns, mul_zero,add_zero,cycle_image_at_zero]
  have H := literal_bouquet_homology_euler sigma (alpha S) hsigma (hAlpha.involution S)
    (fun i : S => a i) (fun i : S => b i)
    (fun x y h => Subtype.ext (ha h)) (fun x y h => Subtype.ext (hb h))
    (fun i j => hd i j) (fun i => hAlpha.left S i i.prop) (fun i => hAlpha.right S i i.prop)
    (fun i hx hy => hAlpha.fixed S i (fun e he => hx ⟨e,he⟩) (fun e he => hy ⟨e,he⟩))
    (fun i => hord i) (fun i : S => ell i)
    (by
      intro i j
      have he : interlaces (fun k : S => a k) (fun k : S => b k) i j ↔
          interlaces a b (i : E) (j : E) := by simp [interlaces]
      by_cases ht : interlaces a b (i : E) (j : E)
      · rw [ite_eq_left (he.mpr ht), ← hPair, ite_eq_left ht]
      · rw [ite_eq_right (fun h => ht (he.mp h)), ← hPair, ite_eq_right ht])
  dsimp only at H
  rw [Fintype.card_coe] at H
  exact H.symm

-- The observation is over a finite space, irrespective of the number of chords.
noncomputable local instance : Fintype (Module.Dual F₂ (F₂ × H₂)) := by
  letI : Finite (Module.Dual F₂ (F₂ × H₂)) :=
    Finite.of_injective (fun f : Module.Dual F₂ (F₂ × H₂) => fun x => f x)
      (fun {_ _} h => LinearMap.ext (congrFun h))
  exact Fintype.ofFinite _

/-- End-to-end literal scalar boundary sum for every real positive Kauffman
parameter on a one-vertex ribbon with a binary torus pairing table. All
five input moments are the actual physical diagonal-code marginals. -/
theorem actual_bouquet_bracket_walsh (sigma : Equiv.Perm (Fin (n+1)))
    (hsigma : ∀ i, sigma i=cyclicNext i)
    (a b : E→Fin (n+1)) (ha : Function.Injective a) (hb : Function.Injective b)
    (hd : ∀ e j, a e≠b j) (hord : ∀ e, (a e).val < (b e).val)
    (alpha : Finset E→Equiv.Perm (Fin (n+1))) (hAlpha : RibbonSwitches a b alpha)
    (ell : E→H₂)
    (hPair : ∀ e j, (if interlaces a b e j then (1:F₂) else 0) =
      (ell j).1*(ell e).2-(ell j).2*(ell e).1)
    (u v : E→ℝ) (A : ℝ) (hA : 0<A) :
    let d := bracketLoop A
    let K := bracketOrder A
    let f := fun S => torusMix (d^2)
      (readMoment (F:=F₂) (fun _ : E => ((0:F₂),(0:H₂))) K S)
      (readMoment (F:=F₂) (fun i => ((0:F₂),firstLineProjection (ell i))) K S)
      (readMoment (F:=F₂) (fun i => ((0:F₂),secondLineProjection (ell i))) K S)
      (readMoment (F:=F₂) (fun i => ((0:F₂),diagonalLineProjection (ell i))) K S)
      (readMoment (F:=F₂) (fun i => ((0:F₂),ell i)) K S)
    d*(∑ T : Finset E, inverse f T*(∏ e : E, (v e+(d*u e)*(if e∈T then (-1:ℝ) else 1)))) =
      ∑ S : Finset E, ((∏ e ∈ S, u e)*(∏ e ∈ Sᶜ, v e))*d^(bouquetCircles sigma alpha S) := by
  have hh := actual_real_torus_bracket_walsh (fun _ : E => (0:F₂)) ell u v A hA 1
    (bouquetCircles sigma alpha) (actual_bouquet_euler_all sigma hsigma a b ha hb hd hord
      alpha hAlpha ell hPair)
  simpa only [pow_one] using hh
end ActualBouquetBracket

section ActualMomentWitness
open Finset Matrix
open scoped BigOperators Classical MatrixOrder ComplexOrder
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments

noncomputable local instance : Fintype (Module.Dual F₂ H₂) := by
  letI : Finite (Module.Dual F₂ H₂) :=
    Finite.of_injective (fun f : Module.Dual F₂ H₂ => fun x => f x)
      (fun {_ _} h => LinearMap.ext (congrFun h))
  exact Fintype.ofFinite _

private def pairColumns (i : Fin 2) : H₂ := if i=0 then (1,0) else (0,1)

private theorem univPairLine (v : Fin 2→H₂) (z : H₂) (hz : z≠0)
    (hv : ∀ i, v i=0 ∨ v i=z) (he : ∃ i, v i=z) :
    Module.finrank F₂ (columns (F:=F₂) v univ)=1 := by
  suffices hs : columns (F:=F₂) v univ = F₂ ∙ z by
    rw [hs]
    exact finrank_span_singleton hz
  unfold columns
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,_,rfl⟩
    rcases hv i with h|h
    · rw [h]; exact zero_mem _
    · rw [h]; exact Submodule.mem_span_singleton_self _
  · apply Submodule.span_le.mpr
    intro x hx
    have hx' : x=z := Set.mem_singleton_iff.mp hx
    obtain ⟨i,hi⟩ := he
    exact Submodule.subset_span ⟨i,by simp,hi.trans hx'.symm⟩

private theorem univPairFull : Module.finrank F₂ (columns (F:=F₂) pairColumns univ)=2 := by
  let Span := columns (F:=F₂) pairColumns (univ : Finset (Fin 2))
  have hv (i : Fin 2) : pairColumns i ∈ Span :=
    Submodule.subset_span ⟨i,by simp,rfl⟩
  have ht : Span=⊤ := by
    apply top_unique
    intro x _
    have h : x=x.1 • pairColumns 0 + x.2 • pairColumns 1 := by
      apply Prod.ext <;> simp [pairColumns]
    rw [h]
    exact Span.add_mem (Span.smul_mem _ (hv 0)) (Span.smul_mem _ (hv 1))
  change Module.finrank F₂ Span=2
  rw [ht,finrank_top]
  norm_num [Module.finrank_prod,Module.finrank_self]

private theorem two_site_rank_zero :
    Module.finrank F₂ (columns (F:=F₂) (fun _ : Fin 2 => (0:H₂)) univ)=0 := by
  suffices h : columns (F:=F₂) (fun _ : Fin 2 => (0:H₂)) univ=⊥ by rw [h,finrank_bot]
  unfold columns
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨i,hi,rfl⟩
  exact zero_mem _

/-- The actual five-readout two-site generator; projection channels are
physical diagonal-code reductions, not externally chosen scalar moments. -/
noncomputable def fullPairObserved (K : ℝ) : ℝ :=
  torusMix ((2:ℝ)^(K-1))
    (readMoment (F:=F₂) (fun _ : Fin 2 => (0:H₂)) K univ)
    (readMoment (F:=F₂) (fun i => firstLineProjection (pairColumns i)) K univ)
    (readMoment (F:=F₂) (fun i => secondLineProjection (pairColumns i)) K univ)
    (readMoment (F:=F₂) (fun i => diagonalLineProjection (pairColumns i)) K univ)
    (readMoment (F:=F₂) pairColumns K univ)

theorem physical_full_pair_readout (K : ℝ) (hK : 0<K)
    (hq2 : (2:ℝ)^(K-1) ≠ 2) :
    let observed := fullPairObserved K
    observed = ((2:ℝ)^(K-1))⁻¹ := by
  have hr₁ := univPairLine (fun i => firstLineProjection (pairColumns i)) (0,1)
    (by decide) (by decide) (by decide)
  have hr₂ := univPairLine (fun i => secondLineProjection (pairColumns i)) (1,0)
    (by decide) (by decide) (by decide)
  have hr₃ := univPairLine (fun i => diagonalLineProjection (pairColumns i)) (1,0)
    (by decide) (by decide) (by decide)
  have hq : 0 < (2:ℝ)^(K-1) := Real.rpow_pos_of_pos (by norm_num) _
  have hcal : (Fintype.card F₂:ℝ)^(1-K)=((2:ℝ)^(K-1))⁻¹ := by
    have hc : (Fintype.card F₂:ℝ)=2 := by norm_num [F₂,ZMod.card]
    rw [hc,← Real.rpow_neg (by norm_num : 0≤(2:ℝ))]
    congr 1
    ring
  simpa only [fullPairObserved,Nat.zero_add,pow_one] using
    actual_torus_moment _ _ _ _ _ hK _ hq.ne' hq2 hcal univ
      0 1 1 1 2 1 TorusRankProfile.full two_site_rank_zero hr₁ hr₂ hr₃ univPairFull

end ActualMomentWitness


end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh
