/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateClassicalCoverage
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateClassicalCoverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Classify exactly which real GCE orders universally admit a classical hit law on graph states. -/

import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.BinaryProjectiveRankPolynomial
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateClassicalCoverage
open Matrix
open scoped Classical
local notation "𝔽" => ZMod 2
local notation "cutMatrix" => D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement.cutMatrix
local notation "physicalMoment" => D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement.graphTraceMoment
local notation "physicalMomentRule" => D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement.physical_graph_gce_monotone

private def signBit (b : 𝔽) : ℤ := if b = 0 then 1 else -1

private theorem sign_add : ∀ x y : 𝔽, signBit (x+y) = signBit x * signBit y := by decide +kernel

private theorem binary_double : ∀ x : 𝔽, x+x=0 := by decide +kernel

private theorem walsh_exact {J : Type*} [Fintype J] (v : J → 𝔽) :
    (∑ y : J → 𝔽, signBit (v ⬝ᵥ y)) = if v = 0 then Fintype.card (J → 𝔽) else 0 := by
  let ψ : AddChar (J → 𝔽) ℤ := ⟨fun y => signBit (v ⬝ᵥ y), by simp [signBit],
    fun x y => by simp [dotProduct_add, sign_add]⟩
  change (∑ y, ψ y) = _
  rw [AddChar.sum_eq_ite]
  have eq : ψ = 0 ↔ v = 0 := by
    constructor
    · intro h
      funext j
      by_contra hn
      have hv : ∀ a : 𝔽, a ≠ 0 → a = 1 := by decide +kernel
      have q := congrArg (fun p : AddChar (J → 𝔽) ℤ => p (Pi.single j 1)) h
      change signBit (v ⬝ᵥ Pi.single j 1) = 1 at q
      norm_num [dotProduct_single,hv _ hn,signBit] at q
    · rintro rfl
      ext x
      change signBit (0 ⬝ᵥ x) = 1
      simp [signBit]
  simp [eq]

private theorem kernel_card {I J : Type*} [Fintype I] (B : Matrix J I 𝔽) :
    Nat.card B.mulVecLin.ker = 2 ^ Module.finrank 𝔽 B.mulVecLin.ker := by
  let _ : Fintype B.mulVecLin.ker := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K:=𝔽)]
  simp

private def graphMoment {I : Type*} [Fintype I]
    (A : Matrix I I 𝔽) (K : ℝ) (U : Finset I) : ℝ :=
  (2:ℝ)^((1-K) * (cutMatrix A U (Finset.univ \ U)).rank)

private theorem product_neg_in_band {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (n : ℕ) (q : R) (hlo : (2 : R)^n < q) (hhi : q < (2 : R)^(n+1)) :
    ∏ j ∈ Finset.range (n+2), (1 - (2 : R)^j / q) < 0 := by
  have hq : 0 < q := lt_trans (by positivity) hlo
  rw [show n + 2 = (n + 1) + 1 by rfl, Finset.prod_range_succ]
  apply mul_neg_of_pos_of_neg
  · apply Finset.prod_pos
    intro j hj
    rw [Finset.mem_range] at hj
    apply sub_pos.mpr
    rw [div_lt_one hq]
    exact (pow_le_pow_right₀ (by norm_num : (1 : R) ≤ 2) (Nat.le_of_lt_succ hj)).trans_lt hlo
  · apply sub_neg.mpr
    rwa [one_lt_div hq]

/-- In every open dyadic band, the exact signed rank sum is negative for
the projective configuration of the stated dimension. -/
private theorem native_projective_rank_obstruction
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (n : Nat) (q : R) (hlo : (2 : R)^n < q) (hhi : q < (2 : R)^(n+1)) :
    (∑ U ∈ ((Finset.univ : Finset ((Fin (n+2) → ZMod 2))).erase 0).powerset,
      (-1 : R)^U.card * (q⁻¹) ^
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (U : Set ((Fin (n+2) → ZMod 2))))) < 0 := by
  have hq : 0 < q := lt_trans (by positivity) hlo
  change D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.BinaryProjectiveRankPolynomial.normalizedRankSum (n+2) q < 0
  have hfactor := D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.BinaryProjectiveRankPolynomial.normalized_factor (n+2) q hq.ne'
  change _ = _ at hfactor
  change D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.BinaryProjectiveRankPolynomial.normalizedRankSum (n+2) q =
    ∏ j : Fin (n+2), (1-(2 : R)^j.val/q) at hfactor
  rw [hfactor]
  rw [Fin.prod_univ_eq_prod_range (fun j : Nat => (1 : R) - (2 : R)^j/q)]
  exact product_neg_in_band n q hlo hhi

section
variable {I : Type*} [Fintype I]
abbrev Word (I : Type*) := I → 𝔽

private def char (x u : Word I) : ℝ := signBit (x ⬝ᵥ u)

@[simp] private theorem char_zero (x : Word I) : char x 0 = 1 := by simp [char,signBit]
@[simp] private theorem zero_char (u : Word I) : char 0 u = 1 := by simp [char,signBit]

private theorem char_add (x y u : Word I) : char (x+y) u = char x u * char y u := by
  simp [char,add_dotProduct,sign_add]

private def transform (p : Word I → ℝ) (u : Word I) : ℝ := ∑ x, p x * char x u

private def convolution (p q : Word I → ℝ) (z : Word I) : ℝ :=
  ∑ x, ∑ y, if x+y=z then p x * q y else 0

def Weight (p : Word I → ℝ) : Prop := (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

private theorem transform_convolution (p q : Word I → ℝ) (u : Word I) :
    transform (convolution p q) u = transform p u * transform q u := by
  unfold transform convolution
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [ite_mul,zero_mul]
  simp [char_add]
  ring

private theorem convolution_weight {p q : Word I → ℝ} (hp : Weight p) (hq : Weight q) :
    Weight (convolution p q) := by
  constructor
  · intro z; unfold convolution
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      ite_nonneg (mul_nonneg (hp.1 _) (hq.1 _)) (le_refl _)
  · have hh := transform_convolution p q 0
    simpa [transform,hp.2,hq.2] using hh

private def zeroWeight (x : Word I) : ℝ := if x = 0 then 1 else 0

private theorem zeroWeight_weight : Weight (zeroWeight : Word I → ℝ) := by
  constructor
  · intro x; by_cases h : x=0 <;> simp [zeroWeight,h]
  · simp [zeroWeight]

private theorem transform_zeroWeight (u : Word I) : transform zeroWeight u = 1 := by
  simp [transform,zeroWeight,ite_mul]

private def convolve (p : Word I → ℝ) : ℕ → Word I → ℝ
  | 0 => zeroWeight
  | n+1 => convolution (convolve p n) p

private theorem convolve_weight {p : Word I → ℝ} (hp : Weight p) (n : ℕ) :
    Weight (convolve p n) := by
  induction n with
  | zero => exact zeroWeight_weight
  | succ n ih => exact convolution_weight ih hp

private theorem transform_convolve (p : Word I → ℝ) (n : ℕ) (u : Word I) :
    transform (convolve p n) u = (transform p u)^n := by
  induction n with
  | zero => simp [convolve,transform_zeroWeight]
  | succ n ih => rw [convolve,transform_convolution,ih,pow_succ]

private def restrict (S : Finset I) (x : Word I) : Word S := fun i => x i.val

def hit (S : Finset I) (p : Word I → ℝ) : ℝ :=
  ∑ x, if restrict S x = 0 then 0 else p x

private theorem nonhit_eq_one_sub_hit (S : Finset I) (p : Word I → ℝ) (hp : Weight p) :
    (∑ x, if restrict S x = 0 then p x else 0) = 1 - hit S p := by
  unfold hit
  have h : ∀ x, (if restrict S x = 0 then p x else (0:ℝ)) +
      (if restrict S x = 0 then (0:ℝ) else p x) = p x := by
    intro x; split <;> simp
  apply eq_sub_iff_add_eq.mpr
  rw [← Finset.sum_add_distrib]
  simpa [h] using hp.2

variable {X : Type*} [Fintype X] [Nonempty X]

private def pushUniform (f : X → Word I) (x : Word I) : ℝ :=
  (∑ a : X, if f a = x then (1:ℝ) else 0) / Fintype.card X

private theorem pushUniform_weight (f : X → Word I) : Weight (pushUniform f) := by
  have hpos : (0:ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  constructor
  · intro x
    exact div_nonneg (Finset.sum_nonneg fun a _ => ite_nonneg zero_le_one le_rfl) hpos.le
  · unfold pushUniform
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul,Finset.sum_comm]
    simp [hpos.ne']

omit [Nonempty X] in
private theorem transform_pushUniform (f : X → Word I) (u : Word I) :
    transform (pushUniform f) u = (∑ a, char (f a) u) / (Fintype.card X) := by
  unfold transform pushUniform
  simp_rw [div_mul_eq_mul_div,Finset.sum_mul]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [ite_mul,one_mul,zero_mul]
  simp
end

section
variable {I : Type*} [Fintype I] [LinearOrder I]
private def partitionEquiv (U : Finset I) : (U ⊕ ↥(Finset.univ \ U)) ≃ I :=
  (Equiv.sumCongr (Equiv.refl ↥U)
    (Equiv.subtypeEquivRight (fun x => by simp [Finset.mem_sdiff]))).trans
    (Equiv.sumCompl (fun x => x ∈ U))

@[simp] private theorem partition_inl (U : Finset I) (u : U) :
    partitionEquiv U (.inl u) = u.val := by simp [partitionEquiv]
@[simp] private theorem partition_inr (U : Finset I) (v : (Finset.univ \ U : Finset I)) :
    partitionEquiv U (.inr v) = v.val := by simp [partitionEquiv]

private def together (U : Finset I) (x : U → 𝔽) (y : (Finset.univ \ U : Finset I) → 𝔽) :
    I → 𝔽 := Sum.elim x y ∘ (partitionEquiv U).symm

/-- The odd-degree vertices of the induced graph on the one's support. -/
private def oddDegree (A : Matrix I I 𝔽) (x : Word I) : Word I :=
  fun i => x i * (A *ᵥ x) i

private def mask (U : Finset I) : Word I := fun i => if i ∈ U then 1 else 0

@[simp] private theorem together_in (U : Finset I) (x : Word U) (y : Word (Finset.univ \ U : Finset I))
    (i : U) : together U x y i.val = x i := by
  change Sum.elim x y ((partitionEquiv U).symm i.val) = _
  rw [← partition_inl U i,Equiv.symm_apply_apply]
  rfl

@[simp] private theorem together_out (U : Finset I) (x : Word U) (y : Word (Finset.univ \ U : Finset I))
    (i : (Finset.univ \ U : Finset I)) : together U x y i.val = y i := by
  change Sum.elim x y ((partitionEquiv U).symm i.val) = _
  rw [← partition_inr U i,Equiv.symm_apply_apply]
  rfl

/-- A query of induced odd degrees is exactly its cut-edge parity. -/
private theorem oddDegree_cut_parity (A : Matrix I I 𝔽)
    (hs : ∀ i j, A i j=A j i) (hd : ∀ i,A i i=0) (U : Finset I)
    (x : Word U) (y : Word (Finset.univ \ U : Finset I)) :
    oddDegree A (together U x y) ⬝ᵥ mask U =
      (cutMatrix A U (Finset.univ \ U) *ᵥ x) ⬝ᵥ y := by
  let V := (Finset.univ \ U : Finset I)
  let z := together U x y
  have lhs : oddDegree A z ⬝ᵥ mask U = ∑ i : U, x i * (A *ᵥ z) i.val := by
    unfold dotProduct mask oddDegree
    have h : (∑ i ∈ U, z i*(A *ᵥ z) i) = ∑ i : U, z i.val*(A *ᵥ z) i.val :=
      Finset.sum_subtype U (fun _ => Iff.rfl) (fun i => z i*(A *ᵥ z) i)
    simp_rw [mul_ite,mul_one,mul_zero,← Finset.sum_filter]
    rw [show Finset.univ.filter (fun i => i∈U)=U from by ext i; simp,h]
    apply Finset.sum_congr rfl
    intro i _
    simp [z]
  have rs (i : U) :
      (A *ᵥ z) i.val = (∑ j : U,A i.val j.val * x j) + ∑ j : V,A i.val j.val * y j := by
    unfold Matrix.mulVec dotProduct
    let f (j : I) := A i.val j * z j
    have h := Equiv.sum_comp (partitionEquiv U) f
    rw [Fintype.sum_sum_type] at h
    simp only [partition_inl,partition_inr,f,z,together_in,together_out] at h
    exact h.symm
  rw [lhs]
  change (∑ i : U,x i * (A *ᵥ z) i.val) = (cutMatrix A U V *ᵥ x) ⬝ᵥ y
  simp_rw [rs,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  have hi : (∑ i : U, ∑ j : U, x i * (A i.val j.val * x j)) = 0 := by
    let term (p : U × U) := x p.1 * (A p.1.val p.2.val * x p.2)
    change (∑ i, ∑ j, term (i,j)) = 0
    rw [← Fintype.sum_prod_type term]
    apply Finset.sum_ninvolution (fun p : U × U => p.swap)
    · rintro ⟨i,j⟩
      change x i * (A i.val j.val * x j) + x j * (A j.val i.val * x i) = 0
      rw [hs j.val i.val, show x j * (A i.val j.val * x i) = x i * (A i.val j.val * x j) by ring]
      exact binary_double _
    · rintro ⟨i,j⟩ hn he
      have hij : i = j := (congrArg Prod.fst he).symm
      subst j
      exact hn (by simp [term,hd])
    · simp
    · simp
  rw [hi,zero_add,Finset.sum_comm]
  simp only [Matrix.mulVec,dotProduct,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  change x i * (A i.val j.val * y j) = A j.val i.val * x i * y j
  rw [hs j.val i.val]
  ring
private def splitWord (U : Finset I) : Word U × Word (Finset.univ \ U : Finset I) ≃ Word I where
  toFun p := together U p.1 p.2
  invFun z := (fun i => z i.val,fun j => z j.val)
  left_inv p := Prod.ext (funext fun i => together_in U p.1 p.2 i)
      (funext fun i => together_out U p.1 p.2 i)
  right_inv z := by
    funext i
    obtain ⟨j,rfl⟩ := (partitionEquiv U).surjective i
    cases j with
    | inl j => simp
    | inr j => simp

private theorem oddDegree_word_moment_sum (A : Matrix I I 𝔽) (hs : ∀ i j, A i j=A j i)
    (hd : ∀ i,A i i=0) (U : Finset I) :
    (∑ z : Word I, char (oddDegree A z) (mask U)) =
      ((2:ℝ)^Module.finrank 𝔽 (cutMatrix A U (Finset.univ \ U)).mulVecLin.ker) *
        (2:ℝ) ^ (Finset.univ \ U : Finset I).card := by
  let V := (Finset.univ \ U : Finset I)
  let B := cutMatrix A U V
  let f := fun z : Word I => char (oddDegree A z) (mask U)
  have h := Equiv.sum_comp (splitWord U) f
  rw [Fintype.sum_prod_type] at h
  change (∑ x : Word U, ∑ y : Word V,
    (signBit (oddDegree A (together U x y) ⬝ᵥ mask U) : ℝ)) = (∑ z : Word I, f z) at h
  simp only [oddDegree_cut_parity A hs hd U] at h
  change (∑ z, f z) = _
  rw [← h]
  have hrow (x : Word U) :
      (∑ y : Word V, (signBit ((B *ᵥ x) ⬝ᵥ y) : ℝ)) =
        if B *ᵥ x = 0 then (Fintype.card (Word V) : ℝ) else 0 := by
    have q := congrArg (fun z : ℤ => (z : ℝ)) (walsh_exact (B *ᵥ x))
    push_cast at q
    convert q using 2 <;> congr 2 <;> exact Subsingleton.elim _ _
  change (∑ x : Word U, ∑ y : Word V, (signBit ((B *ᵥ x) ⬝ᵥ y) : ℝ)) = _
  simp_rw [hrow]
  rw [← Finset.sum_filter,Finset.sum_const]
  have hk : (Finset.univ.filter (fun x : Word U => B *ᵥ x = 0)).card = Nat.card B.mulVecLin.ker := by
    have e : {x : Word U // B *ᵥ x = 0} ≃ B.mulVecLin.ker :=
      Equiv.subtypeEquivRight (fun _ => Iff.rfl)
    rw [← Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [hk,kernel_card]
  simp [ZMod.card,V,B,Finset.card_sdiff]

/-- No quantum sampling premise: the random induced odd-degree set has Walsh
moment exactly 2^(-binary cut rank), for every cut. -/
private theorem oddDegree_transform (A : Matrix I I 𝔽) (hs : ∀ i j,A i j=A j i)
    (hd : ∀ i,A i i=0) (U : Finset I) :
    transform (pushUniform (oddDegree A)) (mask U) =
      ((2:ℝ)^(cutMatrix A U (Finset.univ \ U)).rank)⁻¹ := by
  rw [transform_pushUniform,oddDegree_word_moment_sum A hs hd U]
  let V := (Finset.univ \ U : Finset I)
  let B := cutMatrix A U V
  have d := B.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at d
  change B.rank + Module.finrank 𝔽 B.mulVecLin.ker = Fintype.card ↥U at d
  rw [Fintype.card_coe] at d
  have hu := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ U)
  rw [Finset.card_univ] at hu
  have e : Fintype.card I = B.rank + Module.finrank 𝔽 B.mulVecLin.ker + V.card := by
    dsimp [V]
    omega
  change (2:ℝ)^Module.finrank 𝔽 B.mulVecLin.ker * (2:ℝ)^V.card /
    (Fintype.card (Word I) : ℝ) = ((2:ℝ)^B.rank)⁻¹
  rw [Fintype.card_fun,ZMod.card,Nat.cast_pow,Nat.cast_ofNat,e,pow_add,pow_add]
  field_simp

/-- Exact finite graph sampler at integer orders: use n independent induced
odd-degree subsets and XOR them. Each Walsh coefficient follows the actual
CFC trace moment rule for K=n+1. -/
private theorem integer_graph_walsh (A : Matrix I I 𝔽) (hs : ∀ i j,A i j=A j i)
    (hd : ∀ i,A i i=0) (n : ℕ) :
    ∃ p : Word I → ℝ, Weight p ∧ ∀ U : Finset I,
      transform p (mask U) = (((2:ℝ)^(cutMatrix A U (Finset.univ \ U)).rank)⁻¹)^n := by
  refine ⟨convolve (pushUniform (oddDegree A)) n,convolve_weight (pushUniform_weight _) n,?_⟩
  intro U
  rw [transform_convolve,oddDegree_transform A hs hd U]
end

section
variable {I : Type*}
/-- Powerset averaging loses no data when one has all subsystem sizes/subsets. -/
private theorem powersetSum_injective (f g : Finset I → ℝ)
    (h : ∀ S : Finset I, (∑ U ∈ S.powerset,f U) = ∑ U ∈ S.powerset,g U) : f = g := by
  funext S
  induction S using Finset.strongInduction with
  | H S ih =>
    have hs : S ∈ S.powerset := Finset.mem_powerset.mpr (Finset.Subset.refl _)
    have hh : (∑ U ∈ S.powerset.erase S,f U) = ∑ U ∈ S.powerset.erase S,g U := by
      apply Finset.sum_congr rfl
      intro U hu
      obtain ⟨hne,hsub⟩ := Finset.mem_erase.mp hu
      exact ih U (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hsub,hne⟩)
    have eq := h S
    rw [← Finset.sum_erase_add _ _ hs,← Finset.sum_erase_add _ _ hs,hh] at eq
    exact add_left_cancel eq
end

section
variable {I : Type*} [Fintype I] [LinearOrder I]
omit [Fintype I] [LinearOrder I] in
private theorem sign_sum_product (S : Finset I) (v : I → 𝔽) :
    (signBit (∑ i ∈ S,v i) : ℝ) = ∏ i ∈ S,(signBit (v i) : ℝ) := by
  induction S using Finset.induction_on with
  | empty => simp [signBit]
  | @insert i S hi ih => rw [Finset.sum_insert hi,Finset.prod_insert hi,sign_add,Int.cast_mul,ih]

private theorem char_mask (z : Word I) (U : Finset I) :
    char z (mask U) = ∏ i ∈ U,(signBit (z i):ℝ) := by
  unfold char dotProduct mask
  simp_rw [mul_ite,mul_one,mul_zero,← Finset.sum_filter]
  rw [show Finset.univ.filter (fun i => i ∈ U) = U by ext i; simp]
  exact sign_sum_product U z

private theorem unsigned_char_sum (S : Finset I) (z : Word I) :
    (∑ U ∈ S.powerset, char z (mask U)) =
      if restrict S z = 0 then (2:ℝ)^S.card else 0 := by
  simp only [char_mask,← Finset.prod_one_add]
  by_cases h : restrict S z = 0
  · rw [ite_eq_left h]
    calc
      _ = ∏ i ∈ S,(2:ℝ) := by
        apply Finset.prod_congr rfl
        intro i hi
        have e : z i = 0 := congrFun h ⟨i,hi⟩
        norm_num [signBit,e]
      _ = _ := Finset.prod_const _
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ : ∃ i : S, z i.val ≠ 0 := by
      by_contra! h'
      exact h (funext h')
    exact Finset.prod_eq_zero i.property (by norm_num [signBit,hi])

private theorem signed_char_sum_nonneg (S : Finset I) (z : Word I) :
    0 ≤ ∑ U ∈ S.powerset,(-1:ℝ)^U.card * char z (mask U) := by
  have hh (U : Finset I) :
      (-1:ℝ)^U.card * char z (mask U) = ∏ i ∈ U,-(signBit (z i):ℝ) := by
    rw [char_mask,← Finset.prod_const (-1 : ℝ),← Finset.prod_mul_distrib]
    simp
  simp_rw [hh]
  rw [← Finset.prod_one_add]
  apply Finset.prod_nonneg
  intro i _
  by_cases hi : z i = 0 <;> norm_num [signBit,hi]

private theorem signed_transform_sum_nonneg (S : Finset I) {p : Word I → ℝ} (hp : Weight p) :
    0 ≤ ∑ U ∈ S.powerset,(-1:ℝ)^U.card * transform p (mask U) := by
  unfold transform
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro z _
  have h (U : Finset I) : (-1:ℝ)^U.card * (p z * char z (mask U)) =
    p z * ((-1:ℝ)^U.card * char z (mask U)) := by ring
  simp_rw [h,← Finset.mul_sum]
  exact mul_nonneg (hp.1 _) (signed_char_sum_nonneg S z)

private theorem average_transform_eq_nonhit (S : Finset I) {p : Word I → ℝ} (hp : Weight p) :
    1 - (∑ U ∈ S.powerset, transform p (mask U)) / (2:ℝ)^S.card = hit S p := by
  have c : (2:ℝ)^S.card ≠ 0 := by positivity
  have h : (∑ U ∈ S.powerset, transform p (mask U)) =
      (2:ℝ)^S.card * (∑ z, if restrict S z = 0 then p z else 0) := by
    unfold transform
    rw [Finset.sum_comm,Finset.mul_sum]
    refine Finset.sum_congr ?_ ?_
    · ext z; simp
    intro z _
    rw [← Finset.mul_sum,unsigned_char_sum]
    split <;> simp [*,mul_comm]
  rw [h,mul_div_cancel_left₀ _ c]
  have hn : (∑ z : Word I, if restrict S z = 0 then p z else 0) = 1 - hit S p := by
    convert nonhit_eq_one_sub_hit S p hp using 1
    all_goals congr 2
    all_goals exact Subsingleton.elim _ _
  rw [hn,sub_sub_cancel]

/-- A classical hit representation of all the averaged subsystem moments
determines their original Walsh moments, without a physical SWAP premise. -/
private theorem coverage_determines_moments (w : Finset I → ℝ) {p : Word I → ℝ} (hp : Weight p)
    (h : ∀ S : Finset I, 1 - (∑ U ∈ S.powerset,w U) / (2:ℝ)^S.card = hit S p) :
    w = fun U => transform p (mask U) := by
  apply powersetSum_injective
  intro S
  have hpow : (2:ℝ)^S.card ≠ 0 := by positivity
  have hh := (h S).trans (average_transform_eq_nonhit S hp).symm
  exact (div_left_inj' hpow).mp (sub_right_inj.mp hh)
end
private abbrev PV (d : ℕ) := Fin d → 𝔽
private abbrev Vertex (d : ℕ) := PV d ⊕ Fin d

/-- Binary incidence graph. The zero vector is an isolated site; retaining
it causes no change to any queried cut across the nonzero left sites. -/
private def incidence (d : ℕ) : Matrix (Vertex d) (Vertex d) 𝔽
  | .inl v, .inr j => v j
  | .inr j, .inl v => v j
  | _,_ => 0

private theorem incidence_symm (d : ℕ) (i j : Vertex d) :
    incidence d i j = incidence d j i := by
  cases i <;> cases j <;> rfl

private theorem incidence_diag (d : ℕ) (i : Vertex d) : incidence d i i = 0 := by
  cases i <;> rfl

private def chosenLeft {d : ℕ} (S : Finset (PV d)) : Finset (Vertex d) :=
  S.map (Function.Embedding.inl)

private def outsideRight {d : ℕ} (S : Finset (PV d)) (j : Fin d) :
    (Finset.univ \ chosenLeft S : Finset (Vertex d)) :=
  ⟨Sum.inr j, by simp [chosenLeft]⟩

private def rightEmbedding {d : ℕ} (S : Finset (PV d)) :
    PV d →ₗ[𝔽] ((Finset.univ \ chosenLeft S : Finset (Vertex d)) → 𝔽) :=
  LinearMap.pi fun j =>
    match j.val with
    | .inl _ => 0
    | .inr i => LinearMap.proj i

private theorem rightEmbedding_inj {d : ℕ} (S : Finset (PV d)) :
    Function.Injective (rightEmbedding S) := by
  intro x y h
  funext j
  exact congrFun h (outsideRight S j)

private theorem incidence_column_image {d : ℕ} (S : Finset (PV d)) :
    Set.range (cutMatrix (incidence d) (chosenLeft S) (Finset.univ \ chosenLeft S)).col =
      rightEmbedding S '' (S : Set (PV d)) := by
  ext w
  constructor
  · rintro ⟨i,rfl⟩
    have h := i.property
    unfold chosenLeft at h
    obtain ⟨v,hv,he⟩ := Finset.mem_map.mp h
    change Sum.inl v = i.val at he
    refine ⟨v,hv,?_⟩
    funext j
    have eq : rightEmbedding S v j = match j.val with
      | .inl _ => 0
      | .inr k => v k := by
        unfold rightEmbedding
        simp only [LinearMap.pi_apply]
        split <;> simp [ * ]
    rw [eq]
    change _ = incidence d j.val i.val
    rw [← he]
    cases j.val <;> rfl
  · rintro ⟨v,hv,rfl⟩
    let i : chosenLeft S := ⟨Sum.inl v,Finset.mem_map.mpr ⟨v,hv,rfl⟩⟩
    refine ⟨i,?_⟩
    funext j
    change incidence d j.val (Sum.inl v) = rightEmbedding S v j
    unfold rightEmbedding
    simp only [LinearMap.pi_apply]
    split <;> simp [incidence, *]

/-- An actual cut in the binary incidence graph realizes the selected
vector matroid rank, with all residual left-to-left rows forced to zero. -/
private theorem incidence_cut_rank {d : ℕ} (S : Finset (PV d)) :
    (cutMatrix (incidence d) (chosenLeft S) (Finset.univ \ chosenLeft S)).rank =
      Module.finrank 𝔽 (Submodule.span 𝔽 (S : Set (PV d))) := by
  rw [Matrix.rank_eq_finrank_span_cols,incidence_column_image,← Submodule.map_span]
  exact ((Submodule.span 𝔽 (S : Set (PV d))).equivMapOfInjective
    (rightEmbedding S) (rightEmbedding_inj S)).finrank_eq.symm
private theorem chosenLeft_image {d : ℕ} (S : Finset (PV d)) :
    chosenLeft S = S.image (Sum.inl : PV d → Vertex d) := by
  unfold chosenLeft
  rw [Finset.map_eq_image]
  rfl

private theorem rank_rpow (r : ℕ) (K : ℝ) : (2:ℝ)^((1-K)*(r:ℝ)) =
    (((2:ℝ)^(K-1))⁻¹)^r := by
  rw [← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

private theorem incidence_negative_marginal (n : ℕ) (K : ℝ)
    (hlo : (n:ℝ) < K-1) (hhi : K-1 < (n:ℝ)+1) :
    (∑ U ∈ (chosenLeft (d := n+2) (Finset.univ.erase 0)).powerset,
      (-1:ℝ)^U.card * graphMoment (incidence (n+2)) K U) < 0 := by
  let d := n+2
  let P := (Finset.univ : Finset (PV d)).erase 0
  have hi : Set.InjOn (fun S : Finset (PV d) =>
      S.image (Sum.inl : PV d → Vertex d)) P.powerset :=
    Finset.image_injOn_powerset_of_injOn Sum.inl_injective.injOn
  change (∑ U ∈ (chosenLeft P).powerset,
      (-1:ℝ)^U.card * graphMoment (incidence d) K U) < 0
  rw [chosenLeft_image,Finset.powerset_image,Finset.sum_image hi]
  have ht (U : Finset (PV d)) :
      (-1:ℝ)^(U.image (Sum.inl : PV d → Vertex d)).card *
        graphMoment (incidence d) K (U.image Sum.inl) =
      (-1:ℝ)^U.card * (((2:ℝ)^(K-1))⁻¹) ^
        Module.finrank 𝔽 (Submodule.span 𝔽 (U : Set (PV d))) := by
    rw [← chosenLeft_image,graphMoment,rank_rpow]
    have hc : (chosenLeft U).card = U.card := Finset.card_map _
    rw [hc]
    congr 1
    have hb := congrArg (fun r : ℕ => (((2:ℝ)^(K-1))⁻¹)^r) (incidence_cut_rank U)
    convert hb using 2
    all_goals congr 2
    all_goals (ext i; simp [Finset.mem_sdiff])
  simp_rw [ht]
  have hbl : (2:ℝ)^n < (2:ℝ)^(K-1) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr hlo
  have hbu : (2:ℝ)^(K-1) < (2:ℝ)^(n+1) := by
    rw [← Real.rpow_natCast,Nat.cast_add,Nat.cast_one]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr hhi
  exact native_projective_rank_obstruction n ((2:ℝ)^(K-1)) hbl hbu

/-- Every noninteger band contains actual finite graph states whose graph
moments cannot be the marginal Fourier moments of any nonnegative law. -/
private theorem incidence_no_coverage (n : ℕ) [LinearOrder (Vertex (n+2))] (K : ℝ)
    (hlo : (n:ℝ) < K-1) (hhi : K-1 < (n:ℝ)+1) :
    ¬ ∃ p : Word (Vertex (n+2)) → ℝ, Weight p ∧
      ∀ S : Finset (Vertex (n+2)),
        1 - (∑ U ∈ S.powerset,graphMoment (incidence (n+2)) K U) / (2:ℝ)^S.card = hit S p := by
  rintro ⟨p,hp,hrep⟩
  have hm := coverage_determines_moments (graphMoment (incidence (n+2)) K) hp hrep
  have hbad := incidence_negative_marginal n K hlo hhi
  rw [hm] at hbad
  exact not_lt_of_ge (signed_transform_sum_nonneg _ hp) hbad
private theorem physical_eq_graphMoment (N : ℕ) (K : ℝ) (A : Matrix (Fin N) (Fin N) 𝔽)
    (hs : ∀ i j,A i j=A j i) (hd : ∀ i,A i i=0) (hK : 1 < K) (S : Finset (Fin N)) :
    physicalMoment A K S = graphMoment A K S := by
  exact (physicalMomentRule N K A hs hd hK).1 S

private def FinGraphCoverage (K : ℝ) : Prop :=
  ∀ N : ℕ, ∀ A : Matrix (Fin N) (Fin N) 𝔽,
    (∀ i j,A i j=A j i) → (∀ i,A i i=0) →
    ∃ p : Word (Fin N) → ℝ, Weight p ∧ ∀ S : Finset (Fin N),
      1 - (∑ U ∈ S.powerset, graphMoment A K U) / (2:ℝ)^S.card = hit S p

private theorem transportRank {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (A : Matrix I I 𝔽) (U : Finset I) :
    (cutMatrix (reindex e e A) (U.map e.toEmbedding)
      (Finset.univ \ U.map e.toEmbedding)).rank =
      (cutMatrix A U (Finset.univ \ U)).rank := by
  let V := (Finset.univ \ U : Finset I)
  let eU := e.subtypeEquiv (p := fun i => i ∈ U) (q := fun j => j ∈ U.map e.toEmbedding)
    (by intro i; simp)
  let eV := e.subtypeEquiv (p := fun i => i ∈ V)
    (q := fun j => j ∈ (Finset.univ \ U.map e.toEmbedding : Finset J))
    (by intro i; simp [V])
  have he : cutMatrix (reindex e e A) (U.map e.toEmbedding)
      (Finset.univ \ U.map e.toEmbedding) =
      reindex eV eU (cutMatrix A U V) := by
    ext i j
    rfl
  rw [he, Matrix.rank_reindex]

private theorem finCoverage_transfer (K : ℝ) (h : FinGraphCoverage K)
    (I : Type) [Fintype I] [LinearOrder I] (A : Matrix I I 𝔽)
    (hs : ∀ i j,A i j=A j i) (hd : ∀ i,A i i=0) :
    ∃ p : Word I → ℝ, Weight p ∧ ∀ S : Finset I,
      1 - (∑ U ∈ S.powerset, graphMoment A K U) / (2:ℝ)^S.card = hit S p := by
  let e := Fintype.equivFin I
  let : DecidableEq I := Classical.decEq I
  let : DecidableEq (Fin (Fintype.card I)) := Classical.decEq _
  obtain ⟨p,hp,hpS⟩ := h _ (reindex e e A) (fun i j => hs _ _) (fun i => hd _)
  let f : Word I ≃ Word (Fin (Fintype.card I)) := Equiv.arrowCongr e (Equiv.refl _)
  refine ⟨p ∘ f, ⟨fun a => hp.1 _, ?_⟩, ?_⟩
  · change (∑ a, p (f a)) = 1
    exact (Equiv.sum_comp f p).trans hp.2
  · intro S
    have eq := hpS (S.map e.toEmbedding)
    have he (U : Finset I) : U.map e.toEmbedding = U.image e := Finset.map_eq_image _ U
    rw [Finset.card_map, he S, Finset.powerset_image,
      Finset.sum_image (Finset.image_injOn_powerset_of_injOn e.injective.injOn)] at eq
    have hm (U : Finset I) : graphMoment (reindex e e A) K (U.map e.toEmbedding) =
        graphMoment A K U := by
      simp only [graphMoment, transportRank]
    simp_rw [← he,hm] at eq
    rw [eq]
    unfold hit
    rw [← (Equiv.sum_comp f)]
    apply Finset.sum_congr rfl
    intro a _
    have hr : restrict (S.map e.toEmbedding) (f a) = 0 ↔ restrict S a = 0 := by
      constructor
      · intro h
        funext i
        have q := congrFun h ⟨e i.val, Finset.mem_map.mpr ⟨i.val,i.property,rfl⟩⟩
        simpa [restrict,f] using q
      · intro h
        funext j
        obtain ⟨i,hi,he⟩ := Finset.mem_map.mp j.property
        have q := congrFun h ⟨i,hi⟩
        have hj : e.symm j.val = i := by rw [← he]; exact e.symm_apply_apply i
        simpa [restrict,f,hj] using q
    rw [if_congr hr rfl rfl]
    rfl

/-- Full observable family at a fixed real order K. -/
def physicalMomentFamily (K : ℝ) (N : ℕ) (A : Matrix (Fin N) (Fin N) 𝔽) :
    Finset (Fin N) → ℝ := physicalMoment A K

/-- Same integer-order classification using the actual public physical graph-state
moment observation from the separate, unmodified graph-state D5 owner. -/
theorem physical_graph_coverage_iff (K : ℝ) (hK : 1 < K) :
    let observed := physicalMomentFamily K
    (∀ N : ℕ, ∀ A : Matrix (Fin N) (Fin N) 𝔽,
      (∀ i j,A i j=A j i) → (∀ i,A i i=0) →
        ∃ p : Word (Fin N) → ℝ, Weight p ∧ ∀ S : Finset (Fin N),
          1 - (∑ U ∈ S.powerset, observed N A U) / (2:ℝ)^S.card = hit S p)
      ↔ ∃ n : ℕ, K = (n:ℝ)+1 := by
  have ht : (∀ N : ℕ, ∀ A : Matrix (Fin N) (Fin N) 𝔽,
      (∀ i j,A i j=A j i) → (∀ i,A i i=0) →
        ∃ p : Word (Fin N) → ℝ, Weight p ∧ ∀ S : Finset (Fin N),
          1 - (∑ U ∈ S.powerset, physicalMoment A K U) / (2:ℝ)^S.card = hit S p)
      ↔ FinGraphCoverage K := by
    unfold FinGraphCoverage
    constructor
    · intro h N A hs hd
      simpa only [physical_eq_graphMoment N K A hs hd hK] using h N A hs hd
    · intro h N A hs hd
      simpa only [physical_eq_graphMoment N K A hs hd hK] using h N A hs hd
  dsimp only [physicalMomentFamily]
  rw [ht]
  constructor
  · intro h
    let n := ⌊K-1⌋₊
    by_contra hn
    have dlo : (n:ℝ) ≤ K-1 := Nat.floor_le (by linarith)
    have dlo' : (n:ℝ) < K-1 := lt_of_le_of_ne dlo (by intro e; exact hn ⟨n,by linarith⟩)
    have dhi : K-1 < (n:ℝ)+1 := Nat.lt_floor_add_one _
    let : LinearOrder (Vertex (n+2)) := LinearOrder.lift'
      (Fintype.equivFin (Vertex (n+2))) (Fintype.equivFin _).injective
    exact incidence_no_coverage n K dlo' dhi
      (finCoverage_transfer K h _ (incidence (n+2)) (incidence_symm _) (incidence_diag _))
  · rintro ⟨n,rfl⟩ N A hs hd
    obtain ⟨p,hp,hm⟩ := integer_graph_walsh A hs hd n
    refine ⟨p,hp,?_⟩
    intro S
    have eq (U : Finset (Fin N)) : graphMoment A ((n:ℝ)+1) U = transform p (mask U) := by
      rw [hm,graphMoment,rank_rpow]
      simp only [add_sub_cancel_right,Real.rpow_natCast]
      rw [inv_pow,inv_pow,← pow_mul,← pow_mul,Nat.mul_comm]
      congr 6 <;> first | (congr 1; exact Subsingleton.elim _ _) | (ext i; simp [Finset.mem_sdiff])
    simp_rw [eq]
    exact average_transform_eq_nonhit S hp

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateClassicalCoverage
