/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeCoverage
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeCoverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Classify the universal real-order GCE coverage of binary diagonal linear code states. -/

import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.BinaryProjectiveRankPolynomial
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeCoverage
noncomputable section

open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments

open Finset Matrix
open scoped BigOperators ComplexOrder MatrixOrder Classical
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
section

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
def avoidMoment (A : X → Finset I) (S : Finset I) : ℝ :=
  ((univ.filter (fun x => S ⊆ A x)).card : ℝ)/Fintype.card X

theorem avoidance_hit [Nonempty X] (A : X → Finset I) : hitLaw (avoidMoment A) := by
  have h0 : avoidMoment A ∅ = 1 := by
    unfold avoidMoment
    simp [div_self (by positivity : (Fintype.card X : ℝ)≠0)]
  apply (hitLaw_iff _ h0).mpr
  intro T
  unfold inverse
  apply div_nonneg _ (by unfold walshNorm; positivity)
  have he (S : Finset I) :
      avoidMoment A S * sign S T =
      (∑ x : X, if S ⊆ A x then sign S T else 0) / Fintype.card X := by
    unfold avoidMoment
    rw [div_mul_eq_mul_div, ←sum_filter, sum_const,nsmul_eq_mul]
  simp_rw [he]
  rw [←sum_div, sum_comm]
  apply div_nonneg _ (by positivity)
  apply sum_nonneg
  intro x _
  rw [←sum_filter]
  have hs : (univ : Finset (Finset I)).filter (fun S => S ⊆ A x) = (A x).powerset := by
    ext S
    simp
  rw [hs,powerset_sign]
  split <;> positivity

variable {F V : Type*} [Field F] [Fintype F] [DecidableEq F] [AddCommGroup V]
  [Module F V] [FiniteDimensional F V] [Fintype (Module.Dual F V)]
private def zeroSites (n : ℕ) (v : I → V)
    (xs : Fin n → Module.Dual F V) : Finset I :=
  univ.filter fun i => ∀ j, xs j (v i) = 0

private theorem powers_of_fiber {Y : Type*} [Fintype Y] [DecidableEq Y]
    (f : X → Y) (y : Y) (n : ℕ) :
    (univ.filter (fun xs : Fin n → X => ∀ j, f (xs j)=y)).card =
      (univ.filter (fun x : X => f x=y)).card ^ n := by
  let e : (univ.filter (fun xs : Fin n → X => ∀ j, f (xs j)=y) : Finset (Fin n → X)) ≃
      (Fin n → (univ.filter (fun x : X => f x=y) : Finset X)) :=
    ⟨fun xs j => ⟨xs.val j, (by simpa using (mem_filter.mp xs.property).2 j)⟩,
      fun xs => ⟨fun j => (xs j).val, by exact mem_filter.mpr ⟨mem_univ _,fun j => (mem_filter.mp (xs j).property).2⟩⟩,
      fun _ => rfl,fun _ => rfl⟩
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using Fintype.card_congr e

private theorem zero_everywhere (n : ℕ) (v : I → V) (S : Finset I) :
    avoidMoment (zeroSites (F:=F) n v) S =
      ((Fintype.card F : ℝ) ^ (-(n:ℝ))) ^ Module.finrank F (columns (F:=F) v S) := by
  let f := project (F:=F) v S
  have hf (xs : Fin n → Module.Dual F V) :
      S ⊆ zeroSites n v xs ↔ ∀ j, f (xs j)=0 := by
    constructor
    · intro h j
      funext i
      exact (mem_filter.mp (h i.property)).2 j
    · intro h i hi
      apply mem_filter.mpr
      exact ⟨mem_univ _, fun j => congrFun (h j) ⟨i,hi⟩⟩
  unfold avoidMoment
  simp_rw [hf]
  rw [powers_of_fiber f 0 n,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_pow,←div_pow]
  change pushed f 0 ^ n = _
  rw [uniform_range f 0,if_pos (Submodule.zero_mem f.range)]
  rw [Module.card_eq_pow_finrank (K:=F),Nat.cast_pow,projected_rank]
  let b : ℝ := Fintype.card F
  let r := Module.finrank F (columns (F:=F) v S)
  change ((b^r)⁻¹)^n = (b ^ (-(n:ℝ)))^r
  rw [Real.rpow_neg (by positivity : 0≤b),Real.rpow_natCast,←inv_pow,←inv_pow,←pow_mul,←pow_mul,Nat.mul_comm]

theorem actual_integer_hit (v : I → V) (n : ℕ) :
    hitLaw (fun S => (((mixedMarginal (F:=F) v S) ^ ((n:ℝ)+1)).trace).re) := by
  have hm (S : Finset I) :
      (((mixedMarginal (F:=F) v S) ^ ((n:ℝ)+1)).trace).re =
      avoidMoment (zeroSites (F:=F) n v) S := by
    rw [actual_column_moment _ _ (by positivity),zero_everywhere n v S]
    congr 2
    ring
  simpa only [hm] using avoidance_hit (zeroSites (F:=F) n v)

end

open Finset Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.BinaryProjectiveRankPolynomial
section
abbrev Vec (d : ℕ) := Fin d → ZMod 2
abbrev Site (d : ℕ) := {v : Vec d // v ≠ 0}
instance classicalBinaryDualFintype (d : ℕ) : Fintype (Module.Dual (ZMod 2) (Vec d)) := Fintype.ofFinite _
def moment (d : ℕ) (K : ℝ) (S : Finset (Site d)) : ℝ :=
  (((mixedMarginal (F:=ZMod 2) (Subtype.val : Site d → Vec d) S) ^ K).trace).re

private theorem xq (K : ℝ) : (2:ℝ)^(1-K) = ((2:ℝ)^(K-1))⁻¹ := by
  rw [←Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
  congr 1
  ring

private theorem site_image (d : ℕ) :
    (univ : Finset (Site d)).image Subtype.val = (univ : Finset (Vec d)).erase 0 := by
  ext v
  simp only [mem_image,mem_univ,true_and,mem_erase]
  exact ⟨fun ⟨a,ha⟩ => ha ▸ ⟨a.property,trivial⟩,fun h => ⟨⟨v,h.1⟩,rfl⟩⟩

theorem full_numerator (d : ℕ) {K : ℝ} (hK : 0<K) :
    (∑ S : Finset (Site d), (-1:ℝ)^S.card * moment d K S) =
    normalizedRankSum d ((2:ℝ)^(K-1)) := by
  classical
  unfold normalizedRankSum
  rw [←site_image,Finset.powerset_image,Finset.sum_image
    (Finset.image_injOn_powerset_of_injOn Subtype.val_injective.injOn),Finset.powerset_univ]
  apply sum_congr rfl
  intro S _
  rw [moment,actual_column_moment _ _ hK]
  have hc : (S.image Subtype.val).card = S.card :=
    Finset.card_image_of_injective S Subtype.val_injective
  rw [hc]
  have hr : (Fintype.card (ZMod 2) : ℝ) = 2 := by simp
  rw [hr,xq,columns,Finset.coe_image]

theorem full_actual_walsh (d : ℕ) {K : ℝ} (hK : 0<K) :
    inverse (moment d K) univ =
      (∏ j : Fin d, (1-(2:ℝ)^j.val / (2:ℝ)^(K-1))) / walshNorm (Site d) := by
  have hq : 0 < (2:ℝ)^(K-1) := by positivity
  have hf := normalized_factor d ((2:ℝ)^(K-1)) hq.ne'
  change normalizedRankSum d ((2:ℝ)^(K-1)) = _ at hf
  unfold inverse
  have he : (∑ S, moment d K S * sign S univ) =
      ∑ S : Finset (Site d), (-1:ℝ)^S.card * moment d K S := by
    apply sum_congr rfl
    intro S _
    rw [mul_comm,sign_as_power,Finset.univ_inter]
  rw [he,full_numerator d hK,hf]

theorem no_law_band (n : ℕ) {K : ℝ} (hlo : (n:ℝ)<K-1) (hhi : K-1<(n:ℝ)+1) :
    ¬ hitLaw (moment (n+2) K) := by
  have hK : 0<K := by linarith [show (0:ℝ) ≤ (n:ℝ) by positivity]
  have h0 : moment (n+2) K ∅ = 1 := by
    unfold moment
    rw [actual_column_moment _ _ hK,columns]
    have he : (↑(∅ : Finset (Site (n+2))) : Set (Site (n+2))) = ∅ := by ext z; simp
    rw [he,Set.image_empty,Submodule.span_empty,finrank_bot,pow_zero]
  intro hh
  have hn := (hitLaw_iff _ h0).mp hh univ
  rw [full_actual_walsh _ hK,Fin.prod_univ_eq_prod_range (fun j : ℕ =>
    (1:ℝ) - (2:ℝ)^j/(2:ℝ)^(K-1)),Finset.prod_range_succ] at hn
  have hq : 0<(2:ℝ)^(K-1) := by positivity
  have hl : (2:ℝ)^n < (2:ℝ)^(K-1) :=
    (by rw [←Real.rpow_natCast]; exact (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr hlo)
  have hu : (2:ℝ)^(K-1) < (2:ℝ)^(n+1) :=
    (by rw [←Real.rpow_natCast,Nat.cast_add,Nat.cast_one]; exact (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr hhi)
  have hp : 0 < ∏ j ∈ range (n+1), (1-(2:ℝ)^j/(2:ℝ)^(K-1)) := by
    apply prod_pos
    intro j hj
    apply sub_pos.mpr
    rw [div_lt_one hq]
    exact (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (Nat.le_of_lt_succ (mem_range.mp hj))).trans_lt hl
  have hneg := sub_neg.mpr ((one_lt_div hq).2 hu)
  exact (not_lt_of_ge hn) (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hp hneg) (by unfold walshNorm; positivity))

theorem first_band_three_site {K : ℝ} (hl : 1<K) (hu : K<2) :
    Fintype.card (Site 2) = 3 ∧ ¬ hitLaw (moment 2 K) := by
  exact ⟨by decide,no_law_band 0 (by norm_num; linarith) (by norm_num; linarith)⟩

theorem fano_three {K : ℝ} (hK : 0<K) (hq : (2:ℝ)^(K-1)=3) :
    inverse (moment 3 K) univ = -(1:ℝ)/1728 := by
  rw [full_actual_walsh 3 hK,hq,Fin.prod_univ_eq_prod_range (fun j : ℕ =>
    (1:ℝ) - (2:ℝ)^j/3)]
  have hcard : Fintype.card (Site 3) = 7 := by decide
  norm_num [walshNorm,hcard,Finset.prod_range_succ]

end

open Finset Matrix
open scoped MatrixOrder ComplexOrder
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
section

def universalBinaryCode (K : ℝ) : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (d : ℕ) (v : I → Vec d),
    hitLaw (fun S => (((mixedMarginal (F:=ZMod 2) v S) ^ K).trace).re)

/-- No entanglement is needed for the full universal integer-order barrier. -/
theorem binary_classical_coverage_iff (K : ℝ) (hK : 1<K) :
    universalBinaryCode K ↔ ∃ n : ℕ, K=(n:ℝ)+1 := by
  constructor
  · intro h
    let n := ⌊K-1⌋₊
    have hlo : (n:ℝ) ≤ K-1 := Nat.floor_le (by linarith)
    have hhi : K-1 < (n:ℝ)+1 := Nat.lt_floor_add_one _
    rcases hlo.lt_or_eq with hh|hh
    · exact ((no_law_band n hh hhi) (h (Site (n+2)) (n+2) Subtype.val)).elim
    · exact ⟨n, by linarith⟩
  · rintro ⟨n,rfl⟩ I _ _ d v
    exact actual_integer_hit (F:=ZMod 2) v n

def fanoObserved (K : ℝ) : ℝ := inverse (moment 3 K) univ

theorem physical_fano_readout (K : ℝ) (hK : 0<K) :
    let observed := fanoObserved K
    observed = (∏ j : Fin 3, (1-(2:ℝ)^j.val/(2:ℝ)^(K-1))) / walshNorm (Site 3) :=
  full_actual_walsh 3 hK

end

end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeCoverage
