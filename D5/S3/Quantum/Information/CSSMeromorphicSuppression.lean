/- GID: D5/S3/Quantum/Information/CSSMeromorphicSuppression
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/CSSMeromorphicSuppression
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: CSS meromorphic decoders suppress coherent errors at four stabilizer states. -/

/-
proof_shape: result: bind-only
escape_witness: none; admission uses open-problem-resolution
Private theorem helpers (proof_shape; direct proof-term consumers):
  mem_groupWords: bind-only; decoderDen_eval_neg_one, decoderDen_eval_zero, decoderNum_X_dvd, decoderNum_eval_neg_one, decoderNum_eval_zero, groupWords_card_pos, group_char_sum
  bit_zero_or_one: bind-only; bit_add_one_ne_zero, bit_fourier, dot_one_eq_wt
  bit_add_self: bind-only; bit_add_one_ne_zero, vector_add_self
  bit_add_one_ne_zero: bind-only; wt_add_one
  vector_add_self: bind-only; decoderNum_eval_zero
  wt_zero: bind-only; decoderDen_eval_zero
  wt_eq_zero: bind-only; decoderDen_eval_zero, decoderNum_eval_zero
  wt_le: bind-only; reverseDen_eq_num, reverseNum_eq_den
  wt_add_one: bind-only; even_dual_complement_weight, reverseDen_eq_num, reverseNum_eq_den
  pauliWeight_zero_right: bind-only; logical_X_weight
  pauliWeight_zero_left: bind-only; odd_dual_weight
  logical_X: bind-only; logical_X_weight
  logical_X_weight: bind-only; decoderNum_X_dvd
  groupWords_card_pos: bind-only; decoderNum_ne_zero, neg_one_suppression, one_suppression
  decoderDen_eval_zero: bind-only; decoder_add_one_ne_zero, decoder_sub_one_ne_zero, infinity_suppression, zero_suppression
  decoderNum_eval_zero: bind-only; decoder_add_one_ne_zero, decoder_sub_one_ne_zero, zero_suppression
  decoderNum_eval_one: bind-only; decoderNum_ne_zero, one_suppression
  decoderDen_eval_one: bind-only; one_suppression
  decoderNum_ne_zero: bind-only; zero_suppression
  decoderNum_X_dvd: bind-only; zero_suppression
  zero_suppression: bind-only; infinity_suppression, result
  reverseDen_eq_num: bind-only; infinity_suppression
  reverseNum_eq_den: bind-only; infinity_suppression
  infinity_suppression: bind-only; result
  char_zero: bind-only; bit_fourier, decoder_scaled_add, decoder_scaled_sub, decoder_sub_one_dvd, group_char_sum
  char_one: bind-only; bit_fourier
  char_as_C: bind-only; char_add, char_sum
  char_add: bind-only; coset_fourier, group_char_sum
  char_sum: bind-only; char_dot
  char_dot: bind-only; full_fourier
  monomial_product: bind-only; full_fourier
  kernel_eq: bind-only; kernel_neg_one_dvd, kernel_one_dvd
  sum_bit: bind-only; bit_fourier
  bit_fourier: bind-only; full_fourier
  full_fourier: bind-only; coset_fourier
  group_char_sum: bind-only; coset_fourier
  coset_fourier: bind-only; decoder_scaled_add, decoder_scaled_sub
  decoder_scaled_sub: bind-only; decoder_sub_one_dvd
  decoder_scaled_add: bind-only; decoder_add_one_dvd
  logical_Z_of_odd_dual: bind-only; odd_dual_weight
  odd_dual_weight: bind-only; decoder_sub_one_dvd, even_dual_complement_weight
  one_dot_one: bind-only; even_dual_complement_weight, odd_complement_weight
  even_dual_complement_weight: bind-only; decoder_add_one_dvd
  kernel_one_dvd: bind-only; decoder_sub_one_dvd
  kernel_neg_one_dvd: bind-only; decoder_add_one_dvd
  two_power_unit: bind-only; decoder_add_one_dvd, decoder_sub_one_dvd
  decoder_sub_one_dvd: bind-only; one_suppression
  decoder_add_one_dvd: bind-only; neg_one_suppression
  dot_one_eq_wt: bind-only; even_stabilizer_weight, odd_complement_weight
  even_stabilizer_weight: bind-only; decoderDen_eval_neg_one
  odd_complement_weight: bind-only; decoderNum_eval_neg_one
  decoderDen_eval_neg_one: bind-only; neg_one_suppression
  decoderNum_eval_neg_one: bind-only; neg_one_suppression
  decoder_sub_one_ne_zero: bind-only; one_suppression
  decoder_add_one_ne_zero: bind-only; neg_one_suppression
  one_suppression: bind-only; result
  neg_one_suppression: bind-only; result
admission_basis: open-problem-resolution (#14813; Proved)
escape_audit: unfinished; issue https://github.com/the-omega-institute/trureturing/issues/14883
Direct frozen dependencies:
  D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.SignQuotient.complexSign
    statement_id: sha256:815b3b55d18bbe94631f98e608ed75835a5ed6590c5cb4a958805cade90cb93d
  D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.SignQuotient.complexSign_add
    statement_id: sha256:9299cfc42d5d0ba183be190abb0eaa8f7ca19b25a002ecd815057449aad3e7ad
  D5/S3/VertexAlgebra/LatticeTwistedGroundRealization.sign_sum
    statement_id: sha256:2082dc610c5a4bc79790dad26b2620374206d4061f7a6f0a902c9dfe1fbf632b
The public result settles Burton--Anwar Conjecture 4.8 for the binding CSS conventions.

For ψ_z = (1, z), the CSS codewords satisfy
|0_L⟩ ∝ ∑_{g ∈ G_X} |g⟩ and |1_L⟩ = X^{⊗n}|0_L⟩.
Up to their common normalization, the denominator is
⟨0_L|ψ_z^{⊗n}⟩ = ∑_{g ∈ G_X} z^{wt(g)}, and the numerator is
⟨1_L|ψ_z^{⊗n}⟩ = ∑_{g ∈ G_X} z^{wt(g + one)}.
These amplitudes give the decoder of Theorem 4.4 and Appendix B of
Burton--Anwar, arXiv:2605.06251v1.
-/

import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

open scoped BigOperators Classical
open Polynomial Matrix
set_option maxHeartbeats 2000000
set_option autoImplicit false
namespace D5.S3.Quantum.Information.CSSMeromorphicSuppression

def wt {n : ℕ} (x : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card

def one {n : ℕ} : Fin n → ZMod 2 := fun _ => 1

structure CSSCode (n : ℕ) where
  GX : Submodule (ZMod 2) (Fin n → ZMod 2)
  GZ : Submodule (ZMod 2) (Fin n → ZMod 2)
  commutation : ∀ x ∈ GX, ∀ z ∈ GZ, x ⬝ᵥ z = 0
  evenX : ∀ x ∈ GX, x ⬝ᵥ one = 0
  evenZ : ∀ z ∈ GZ, z ⬝ᵥ one = 0
  one_not_X : one ∉ GX
  one_not_Z : one ∉ GZ
  odd_length : Odd n
  one_qubit : Module.finrank (ZMod 2) GX + Module.finrank (ZMod 2) GZ + 1 = n

def IsLogical {n : ℕ} (C : CSSCode n) (x z : Fin n → ZMod 2) : Prop :=
  (∀ s ∈ C.GZ, x ⬝ᵥ s = 0) ∧
  (∀ s ∈ C.GX, z ⬝ᵥ s = 0) ∧ ¬ (x ∈ C.GX ∧ z ∈ C.GZ)

def pauliWeight {n : ℕ} (x z : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ 0 ∨ z i ≠ 0)).card

def HasDistance {n : ℕ} (C : CSSCode n) (d : ℕ) : Prop :=
  (∃ x z, IsLogical C x z ∧ pauliWeight x z = d) ∧
  ∀ x z, IsLogical C x z → d ≤ pauliWeight x z

private noncomputable def groupWords {n : ℕ} (G : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Finset (Fin n → ZMod 2) := by
  classical
  exact Finset.univ.filter (fun g => g ∈ G)

noncomputable def decoderDen {n : ℕ} (C : CSSCode n) : Polynomial ℂ :=
  ∑ g ∈ groupWords C.GX, X ^ wt g

noncomputable def decoderNum {n : ℕ} (C : CSSCode n) : Polynomial ℂ :=
  ∑ g ∈ groupWords C.GX, X ^ wt (g + one)

private noncomputable def reverseDen {n : ℕ} (C : CSSCode n) : Polynomial ℂ :=
  (decoderDen C).reflect n

private noncomputable def reverseNum {n : ℕ} (C : CSSCode n) : Polynomial ℂ :=
  (decoderNum C).reflect n

noncomputable def suppressionOrder {n : ℕ} (C : CSSCode n) (a : ℂ) : ℕ :=
  (decoderNum C - Polynomial.C a * decoderDen C).rootMultiplicity a

noncomputable def suppressionOrderInf {n : ℕ} (C : CSSCode n) : ℕ :=
  (reverseDen C).rootMultiplicity 0

noncomputable def FixesWith {n : ℕ} (C : CSSCode n) (a : ℂ) : Prop :=
  (decoderDen C).eval a ≠ 0 ∧ (decoderNum C).eval a = a * (decoderDen C).eval a

noncomputable def FixesWithInf {n : ℕ} (C : CSSCode n) : Prop :=
  (reverseNum C).eval 0 ≠ 0

noncomputable def claim : Prop :=
  ∀ (n d : ℕ) (C : CSSCode n), HasDistance C d →
    (∀ a ∈ ({0, 1, -1} : Set ℂ), FixesWith C a ∧ d ≤ suppressionOrder C a) ∧
    FixesWithInf C ∧ d ≤ suppressionOrderInf C


@[simp] private theorem mem_groupWords {n : ℕ} (G : Submodule (ZMod 2) (Fin n → ZMod 2))
    (g : Fin n → ZMod 2) : g ∈ groupWords G ↔ g ∈ G := by
  classical
  simp [groupWords]

private lemma bit_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  exact (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a

private lemma bit_add_self (a : ZMod 2) : a + a = 0 := by
  exact CharTwo.add_self_eq_zero a

private lemma bit_add_one_ne_zero (a : ZMod 2) : a + 1 ≠ 0 ↔ a = 0 := by
  rcases bit_zero_or_one a with rfl | rfl
  · simp
  · rw [bit_add_self]
    simp

@[simp] private lemma vector_add_self {n : ℕ} (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i
  exact bit_add_self (x i)

@[simp] private theorem wt_zero {n : ℕ} : wt (0 : Fin n → ZMod 2) = 0 := by
  simpa only [wt, hammingNorm] using
    (hammingNorm_zero (β := fun _ : Fin n => ZMod 2))

@[simp] private theorem wt_eq_zero {n : ℕ} (x : Fin n → ZMod 2) : wt x = 0 ↔ x = 0 := by
  simpa only [wt, hammingNorm] using (hammingNorm_eq_zero (x := x))

private lemma wt_le {n : ℕ} (x : Fin n → ZMod 2) : wt x ≤ n := by
  simpa only [wt, hammingNorm, Fintype.card_fin] using
    (hammingNorm_le_card_fintype (x := x))

private lemma wt_add_one {n : ℕ} (x : Fin n → ZMod 2) : wt (x + one) = n - wt x := by
  classical
  have bit := bit_add_one_ne_zero
  have he : Finset.univ.filter (fun i : Fin n => (x + (one : Fin n → ZMod 2)) i ≠ 0) =
      Finset.univ.filter (fun i => x i = 0) := by
    ext i
    simp [one, bit]
  rw [wt, he]
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun i => x i ≠ 0)
  simp only [not_not, Finset.card_univ, Fintype.card_fin] at hc
  unfold wt
  omega

@[simp] private theorem pauliWeight_zero_right {n : ℕ} (x : Fin n → ZMod 2) :
    pauliWeight x 0 = wt x := by
  simp [pauliWeight, wt]

@[simp] private theorem pauliWeight_zero_left {n : ℕ} (z : Fin n → ZMod 2) :
    pauliWeight 0 z = wt z := by
  simp [pauliWeight, wt]

private lemma logical_X {n : ℕ} (C : CSSCode n) {g : Fin n → ZMod 2} (hg : g ∈ C.GX) :
    IsLogical C (g + one) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    rw [add_dotProduct, C.commutation g hg s hs, dotProduct_comm one s, C.evenZ s hs]
    simp
  · intro s hs
    simp
  · intro h
    apply C.one_not_X
    have := C.GX.sub_mem h.1 hg
    simpa using this

private lemma logical_X_weight {n d : ℕ} (C : CSSCode n) (hd : HasDistance C d)
    {g : Fin n → ZMod 2} (hg : g ∈ C.GX) : d ≤ wt (g + one) := by
  simpa using hd.2 (g + one) 0 (logical_X C hg)

private lemma groupWords_card_pos {n : ℕ} (G : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    0 < (groupWords G).card := by
  classical
  exact Finset.card_pos.mpr ⟨0, (mem_groupWords G 0).mpr G.zero_mem⟩

private lemma decoderDen_eval_zero {n : ℕ} (C : CSSCode n) : (decoderDen C).eval 0 = 1 := by
  classical
  simp only [decoderDen, eval_finsetSum, eval_pow, eval_X]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro g hg hne
    have hw : wt g ≠ 0 := by simpa using hne
    simp [hw]
  · simp

private lemma decoderNum_eval_zero {n : ℕ} (C : CSSCode n) : (decoderNum C).eval 0 = 0 := by
  classical
  simp only [decoderNum, eval_finsetSum, eval_pow, eval_X]
  apply Finset.sum_eq_zero
  intro g hg
  have hne : g + one ≠ 0 := by
    intro h
    apply C.one_not_X
    have he : g = one := by
      calc
        g = (g + one) + one := by rw [add_assoc, vector_add_self, add_zero]
        _ = one := by rw [h, zero_add]
    rw [← he]
    exact (mem_groupWords _ _).mp hg
  simp [hne]

private lemma decoderNum_eval_one {n : ℕ} (C : CSSCode n) :
    (decoderNum C).eval 1 = ((groupWords C.GX).card : ℂ) := by
  classical
  simp [decoderNum, eval_finsetSum]

private lemma decoderDen_eval_one {n : ℕ} (C : CSSCode n) :
    (decoderDen C).eval 1 = ((groupWords C.GX).card : ℂ) := by
  classical
  simp [decoderDen, eval_finsetSum]

private lemma decoderNum_ne_zero {n : ℕ} (C : CSSCode n) : decoderNum C ≠ 0 := by
  intro h
  have he := decoderNum_eval_one C
  rw [h, eval_zero] at he
  exact (Nat.cast_ne_zero.mpr (groupWords_card_pos C.GX).ne') he.symm

private lemma decoderNum_X_dvd {n d : ℕ} (C : CSSCode n) (hd : HasDistance C d) :
    (X : Polynomial ℂ) ^ d ∣ decoderNum C := by
  classical
  apply Finset.dvd_sum
  intro g hg
  exact pow_dvd_pow X (logical_X_weight C hd ((mem_groupWords _ _).mp hg))

private lemma zero_suppression {n d : ℕ} (C : CSSCode n) (hd : HasDistance C d) :
    FixesWith C 0 ∧ d ≤ suppressionOrder C 0 := by
  constructor
  · simp [FixesWith, decoderDen_eval_zero, decoderNum_eval_zero]
  · simpa [suppressionOrder] using
      (le_rootMultiplicity_iff (decoderNum_ne_zero C)).mpr (by
        simpa using decoderNum_X_dvd C hd)

private lemma reverseDen_eq_num {n : ℕ} (C : CSSCode n) : reverseDen C = decoderNum C := by
  classical
  let r : Polynomial ℂ →+ Polynomial ℂ := {
    toFun := reflect n
    map_zero' := reflect_zero
    map_add' := fun p q => reflect_add p q n }
  change r (∑ g ∈ groupWords C.GX, X ^ wt g) = _
  simp only [map_sum]
  change (∑ g ∈ groupWords C.GX, reflect n (X ^ wt g)) = _
  unfold decoderNum
  apply Finset.sum_congr rfl
  intro g hg
  rw [reflect_monomial, revAt_le (wt_le g), wt_add_one]

private lemma reverseNum_eq_den {n : ℕ} (C : CSSCode n) : reverseNum C = decoderDen C := by
  classical
  let r : Polynomial ℂ →+ Polynomial ℂ := {
    toFun := reflect n
    map_zero' := reflect_zero
    map_add' := fun p q => reflect_add p q n }
  change r (∑ g ∈ groupWords C.GX, X ^ wt (g + one)) = _
  simp only [map_sum]
  change (∑ g ∈ groupWords C.GX, reflect n (X ^ wt (g + one))) = _
  unfold decoderDen
  apply Finset.sum_congr rfl
  intro g hg
  rw [reflect_monomial, revAt_le (wt_le (g + one)), wt_add_one,
    Nat.sub_sub_self (wt_le g)]

private lemma infinity_suppression {n d : ℕ} (C : CSSCode n) (hd : HasDistance C d) :
    FixesWithInf C ∧ d ≤ suppressionOrderInf C := by
  constructor
  · simp [FixesWithInf, reverseNum_eq_den, decoderDen_eval_zero]
  · simpa [suppressionOrderInf, reverseDen_eq_num, suppressionOrder] using
      (zero_suppression C hd).2


open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient


private noncomputable def char (a : ZMod 2) : Polynomial ℂ :=
  Polynomial.C (complexSign a)

@[simp] private lemma char_zero : char 0 = 1 := by simp [char, complexSign]
@[simp] private lemma char_one : char 1 = -1 := by norm_num [char, complexSign]

private lemma char_as_C (a : ZMod 2) : char a = Polynomial.C (complexSign a) := by
  rfl

private lemma char_add (a b : ZMod 2) : char (a + b) = char a * char b := by
  rw [char_as_C, char_as_C, char_as_C, complexSign_add, map_mul]

private lemma char_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    char (∑ i ∈ s, f i) = ∏ i ∈ s, char (f i) := by
  classical
  rw [char_as_C, D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.sign_sum, map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact (char_as_C (f i)).symm

private lemma char_dot {n : ℕ} (g h : Fin n → ZMod 2) :
    char (g ⬝ᵥ h) = ∏ i, char (g i * h i) := by
  exact char_sum Finset.univ (fun i => g i * h i)

private noncomputable def kernel {n : ℕ} (h : Fin n → ZMod 2) : Polynomial ℂ :=
  ∏ i, (1 + char (h i) * X)

private lemma monomial_product {n : ℕ} (g : Fin n → ZMod 2) :
    (∏ i, (if g i = 0 then (1 : Polynomial ℂ) else X)) = X ^ wt g := by
  classical
  rw [Finset.prod_ite]
  simp [wt]

private lemma kernel_eq {n : ℕ} (h : Fin n → ZMod 2) :
    kernel h = (1 + X) ^ (n - wt h) * (1 - X) ^ wt h := by
  classical
  have hc : (Finset.univ.filter (fun i => h i = 0)).card = n - wt h := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun i => h i ≠ 0)
    simp only [not_not, Finset.card_univ, Fintype.card_fin] at this
    unfold wt
    omega
  unfold kernel
  have he (i : Fin n) : (1 + char (h i) * X) =
      if h i = 0 then (1 + X : Polynomial ℂ) else (1 - X) := by
    by_cases hi : h i = 0 <;> simp [char, complexSign, hi, sub_eq_add_neg]
  simp_rw [he]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, hc]
  rfl

private lemma sum_bit {R : Type*} [AddCommMonoid R] (f : ZMod 2 → R) :
    ∑ b, f b = f 0 + f 1 := by
  exact Fin.sum_univ_two f

private lemma bit_fourier (a : ZMod 2) :
    (∑ b : ZMod 2, char (a * b) * (1 + char b * X)) =
      2 * (if a = 0 then (1 : Polynomial ℂ) else X) := by
  rw [sum_bit]
  rcases bit_zero_or_one a with rfl | rfl <;> simp only [zero_mul, one_mul, char_zero, char_one, if_true, if_false, one_ne_zero] <;> ring

private lemma full_fourier {n : ℕ} (g : Fin n → ZMod 2) :
    (∑ h : Fin n → ZMod 2, char (g ⬝ᵥ h) * kernel h) =
      C ((2 : ℂ) ^ n) * X ^ wt g := by
  classical
  calc
    _ = ∑ h : Fin n → ZMod 2, ∏ i,
        (char (g i * h i) * (1 + char (h i) * X)) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [char_dot, kernel, Finset.prod_mul_distrib]
    _ = ∏ i : Fin n, ∑ b : ZMod 2,
        char (g i * b) * (1 + char b * X) := (Fintype.prod_sum (fun i : Fin n => fun b : ZMod 2 =>
        char (g i * b) * (1 + char b * X))).symm
    _ = C ((2 : ℂ) ^ n) * X ^ wt g := by
      simp_rw [bit_fourier]
      rw [Finset.prod_mul_distrib, monomial_product]
      simp [Polynomial.C_ofNat]



private lemma group_char_sum {n : ℕ} (G : Submodule (ZMod 2) (Fin n → ZMod 2))
    (h : Fin n → ZMod 2) :
    (∑ g ∈ groupWords G, char (g ⬝ᵥ h)) =
      if h ∈ G.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2)) then C ((groupWords G).card : ℂ) else 0 := by
  classical
  by_cases hd : h ∈ G.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2))
  · rw [if_pos hd]
    change (∀ g ∈ G, g ⬝ᵥ h = 0) at hd
    have he (g : Fin n → ZMod 2) (hg : g ∈ groupWords G) : char (g ⬝ᵥ h) = 1 := by
      rw [hd g ((mem_groupWords _ _).mp hg), char_zero]
    rw [Finset.sum_congr rfl he]
    simp
  · rw [if_neg hd]
    change ¬ (∀ g ∈ G, g ⬝ᵥ h = 0) at hd
    obtain ⟨a, ha⟩ := not_forall.mp hd
    obtain ⟨haG, haD⟩ := Classical.not_imp.mp ha
    have hchar : char (a ⬝ᵥ h) = -1 := by simp [char, complexSign, haD]
    let : Fintype G := Fintype.ofFinite G
    let psi : AddChar G (Polynomial ℂ) := {
      toFun := fun g => char ((g : Fin n → ZMod 2) ⬝ᵥ h)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by
        intro g g'
        exact (add_dotProduct (g : Fin n → ZMod 2) (g' : Fin n → ZMod 2) h) ▸
          char_add ((g : Fin n → ZMod 2) ⬝ᵥ h) ((g' : Fin n → ZMod 2) ⬝ᵥ h) }
    have hpsi : psi ≠ 0 := by
      intro hp
      have he := congrArg (fun p : AddChar G (Polynomial ℂ) => p ⟨a, haG⟩) hp
      change char (a ⬝ᵥ h) = 1 at he
      rw [hchar] at he
      norm_num at he
    rw [Finset.sum_subtype (groupWords G) (fun g => mem_groupWords G g)
      (fun g => char (g ⬝ᵥ h))]
    exact (AddChar.sum_eq_zero_iff_ne_zero (ψ := psi)).mpr hpsi

private lemma coset_fourier {n : ℕ} (G : Submodule (ZMod 2) (Fin n → ZMod 2))
    (a : Fin n → ZMod 2) :
    C ((2 : ℂ) ^ n) * (∑ g ∈ groupWords G, X ^ wt (g + a)) =
      ∑ h : Fin n → ZMod 2,
        if h ∈ G.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2)) then
          C ((groupWords G).card : ℂ) * char (a ⬝ᵥ h) * kernel h else 0 := by
  classical
  calc
    _ = ∑ g ∈ groupWords G, C ((2 : ℂ) ^ n) * X ^ wt (g + a) := by
      rw [Finset.mul_sum]
    _ = ∑ g ∈ groupWords G, ∑ h : Fin n → ZMod 2,
        char ((g + a) ⬝ᵥ h) * kernel h := by
      apply Finset.sum_congr rfl
      intro g hg
      exact (full_fourier (g + a)).symm
    _ = ∑ h : Fin n → ZMod 2,
        (∑ g ∈ groupWords G, char (g ⬝ᵥ h)) * char (a ⬝ᵥ h) * kernel h := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      simp_rw [add_dotProduct, char_add]
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [group_char_sum]
      split_ifs <;> simp only [zero_mul]

private lemma decoder_scaled_sub {n : ℕ} (C : CSSCode n) :
    Polynomial.C ((2 : ℂ) ^ n) * (decoderNum C - decoderDen C) =
      ∑ h : Fin n → ZMod 2,
        if h ∈ C.GX.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2)) then
          Polynomial.C ((groupWords C.GX).card : ℂ) * (char (one ⬝ᵥ h) - 1) * kernel h
        else 0 := by
  classical
  have hP := coset_fourier C.GX one
  have hQ := coset_fourier C.GX 0
  simp only [add_zero, zero_dotProduct, char_zero, mul_one] at hQ
  rw [mul_sub]
  change Polynomial.C ((2 : ℂ) ^ n) * (∑ g ∈ groupWords C.GX, X ^ wt (g + one)) -
    Polynomial.C ((2 : ℂ) ^ n) * (∑ g ∈ groupWords C.GX, X ^ wt g) = _
  rw [hP, hQ, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  split_ifs <;> ring

private lemma decoder_scaled_add {n : ℕ} (C : CSSCode n) :
    Polynomial.C ((2 : ℂ) ^ n) * (decoderNum C + decoderDen C) =
      ∑ h : Fin n → ZMod 2,
        if h ∈ C.GX.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2)) then
          Polynomial.C ((groupWords C.GX).card : ℂ) * (char (one ⬝ᵥ h) + 1) * kernel h
        else 0 := by
  classical
  have hP := coset_fourier C.GX one
  have hQ := coset_fourier C.GX 0
  simp only [add_zero, zero_dotProduct, char_zero, mul_one] at hQ
  rw [mul_add]
  change Polynomial.C ((2 : ℂ) ^ n) * (∑ g ∈ groupWords C.GX, X ^ wt (g + one)) +
    Polynomial.C ((2 : ℂ) ^ n) * (∑ g ∈ groupWords C.GX, X ^ wt g) = _
  rw [hP, hQ, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  split_ifs <;> ring



private lemma logical_Z_of_odd_dual {n : ℕ} (C : CSSCode n) (h : Fin n → ZMod 2)
    (hdual : h ∈ C.GX.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2))) (hodd : h ⬝ᵥ one ≠ 0) : IsLogical C 0 h := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    simp
  · intro s hs
    rw [dotProduct_comm]
    exact hdual s hs
  · intro hs
    exact hodd (C.evenZ h hs.2)

private lemma odd_dual_weight {n d : ℕ} (C : CSSCode n) (hd : HasDistance C d)
    (h : Fin n → ZMod 2) (hdual : h ∈ C.GX.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2))) (hodd : h ⬝ᵥ one ≠ 0) :
    d ≤ wt h := by
  simpa using hd.2 0 h (logical_Z_of_odd_dual C h hdual hodd)

private lemma one_dot_one {n : ℕ} (C : CSSCode n) :
    (one : Fin n → ZMod 2) ⬝ᵥ one = 1 := by
  simpa [dotProduct, one] using C.odd_length.natCast_zmod_two

private lemma even_dual_complement_weight {n d : ℕ} (C : CSSCode n) (hd : HasDistance C d)
    (h : Fin n → ZMod 2) (hdual : h ∈ C.GX.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2))) (heven : h ⬝ᵥ one = 0) :
    d ≤ n - wt h := by
  change (∀ g ∈ C.GX, g ⬝ᵥ h = 0) at hdual
  have hc : (h + one) ∈ C.GX.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2)) := by
    change ∀ g ∈ C.GX, g ⬝ᵥ (h + one) = 0
    intro g hg
    rw [dotProduct_add, hdual g hg, C.evenX g hg, zero_add]
  have ho : (h + one) ⬝ᵥ one ≠ 0 := by
    rw [add_dotProduct, heven, one_dot_one C, zero_add]
    exact one_ne_zero
  simpa [wt_add_one] using odd_dual_weight C hd (h + one) hc ho

private lemma kernel_one_dvd {n d : ℕ} (h : Fin n → ZMod 2) (hw : d ≤ wt h) :
    (X - Polynomial.C (1 : ℂ)) ^ d ∣ kernel h := by
  have hb : (X - 1 : Polynomial ℂ) ∣ 1 - X := ⟨-1, by ring⟩
  have hp : (X - 1 : Polynomial ℂ) ^ d ∣ (1 - X) ^ wt h :=
    (pow_dvd_pow_of_dvd hb d).trans (pow_dvd_pow (1 - X) hw)
  simpa only [map_one, kernel_eq] using dvd_mul_of_dvd_right hp ((1 + X) ^ (n - wt h))

private lemma kernel_neg_one_dvd {n d : ℕ} (h : Fin n → ZMod 2) (hw : d ≤ n - wt h) :
    (X - Polynomial.C (-1 : ℂ)) ^ d ∣ kernel h := by
  have hp := dvd_mul_of_dvd_left (pow_dvd_pow (1 + X : Polynomial ℂ) hw)
    ((1 - X) ^ wt h)
  simpa only [map_neg, map_one, sub_neg_eq_add, add_comm, kernel_eq] using hp

private lemma two_power_unit (n : ℕ) : IsUnit (Polynomial.C ((2 : ℂ) ^ n)) := by
  apply Polynomial.isUnit_C.mpr
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero n (by norm_num))

private lemma decoder_sub_one_dvd {n d : ℕ} (C : CSSCode n) (hd : HasDistance C d) :
    (X - Polynomial.C (1 : ℂ)) ^ d ∣ decoderNum C - decoderDen C := by
  classical
  apply (two_power_unit n).dvd_mul_left.mp
  rw [decoder_scaled_sub]
  apply Finset.dvd_sum
  intro h hh
  by_cases hu : h ∈ C.GX.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2))
  · rw [if_pos hu]
    by_cases he : h ⬝ᵥ one = 0
    · simp [dotProduct_comm one h, he]
    · exact dvd_mul_of_dvd_right (kernel_one_dvd h (odd_dual_weight C hd h hu he)) _
  · rw [if_neg hu]
    exact dvd_zero _

private lemma decoder_add_one_dvd {n d : ℕ} (C : CSSCode n) (hd : HasDistance C d) :
    (X - Polynomial.C (-1 : ℂ)) ^ d ∣ decoderNum C + decoderDen C := by
  classical
  apply (two_power_unit n).dvd_mul_left.mp
  rw [decoder_scaled_add]
  apply Finset.dvd_sum
  intro h hh
  by_cases hu : h ∈ C.GX.orthogonalBilin (dotProductBilin (ZMod 2) (ZMod 2))
  · rw [if_pos hu]
    by_cases he : h ⬝ᵥ one = 0
    · exact dvd_mul_of_dvd_right
        (kernel_neg_one_dvd h (even_dual_complement_weight C hd h hu he)) _
    · simp [dotProduct_comm one h, char, complexSign, he]
  · rw [if_neg hu]
    exact dvd_zero _

private lemma dot_one_eq_wt {n : ℕ} (x : Fin n → ZMod 2) : x ⬝ᵥ one = (wt x : ZMod 2) := by
  classical
  calc
    _ = ∑ i : Fin n, (if x i ≠ 0 then (1 : ZMod 2) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rcases bit_zero_or_one (x i) with hx | hx <;> simp [one, hx]
    _ = _ := by simp [wt, Finset.sum_ite]

private lemma even_stabilizer_weight {n : ℕ} (C : CSSCode n) (g : Fin n → ZMod 2) (hg : g ∈ C.GX) :
    Even (wt g) := by
  apply (ZMod.natCast_eq_zero_iff_even (n := wt g)).mp
  rw [← dot_one_eq_wt, C.evenX g hg]

private lemma odd_complement_weight {n : ℕ} (C : CSSCode n) (g : Fin n → ZMod 2) (hg : g ∈ C.GX) :
    Odd (wt (g + one)) := by
  apply (ZMod.natCast_eq_one_iff_odd (n := wt (g + one))).mp
  rw [← dot_one_eq_wt, add_dotProduct, C.evenX g hg, one_dot_one C, zero_add]

private lemma decoderDen_eval_neg_one {n : ℕ} (C : CSSCode n) :
    (decoderDen C).eval (-1) = ((groupWords C.GX).card : ℂ) := by
  classical
  simp only [decoderDen, eval_finsetSum, eval_pow, eval_X]
  have he (g : Fin n → ZMod 2) (hg : g ∈ groupWords C.GX) : (-1 : ℂ) ^ wt g = 1 :=
    (even_stabilizer_weight C g ((mem_groupWords _ _).mp hg)).neg_one_pow
  rw [Finset.sum_congr rfl he]
  simp

private lemma decoderNum_eval_neg_one {n : ℕ} (C : CSSCode n) :
    (decoderNum C).eval (-1) = -((groupWords C.GX).card : ℂ) := by
  classical
  simp only [decoderNum, eval_finsetSum, eval_pow, eval_X]
  have he (g : Fin n → ZMod 2) (hg : g ∈ groupWords C.GX) : (-1 : ℂ) ^ wt (g + one) = -1 :=
    (odd_complement_weight C g ((mem_groupWords _ _).mp hg)).neg_one_pow
  rw [Finset.sum_congr rfl he]
  simp

private lemma decoder_sub_one_ne_zero {n : ℕ} (C : CSSCode n) : decoderNum C - decoderDen C ≠ 0 := by
  intro h
  have hh := congrArg (Polynomial.eval 0) h
  simp [decoderNum_eval_zero, decoderDen_eval_zero] at hh

private lemma decoder_add_one_ne_zero {n : ℕ} (C : CSSCode n) : decoderNum C + decoderDen C ≠ 0 := by
  intro h
  have hh := congrArg (Polynomial.eval 0) h
  simp [decoderNum_eval_zero, decoderDen_eval_zero] at hh

private lemma one_suppression {n d : ℕ} (C : CSSCode n) (hd : HasDistance C d) :
    FixesWith C 1 ∧ d ≤ suppressionOrder C 1 := by
  constructor
  · simp [FixesWith, decoderDen_eval_one, decoderNum_eval_one,
      (Nat.cast_ne_zero.mpr (groupWords_card_pos C.GX).ne' : ((groupWords C.GX).card : ℂ) ≠ 0)]
  · simpa [suppressionOrder] using
      (le_rootMultiplicity_iff (decoder_sub_one_ne_zero C)).mpr (decoder_sub_one_dvd C hd)

private lemma neg_one_suppression {n d : ℕ} (C : CSSCode n) (hd : HasDistance C d) :
    FixesWith C (-1) ∧ d ≤ suppressionOrder C (-1) := by
  constructor
  · simp [FixesWith, decoderDen_eval_neg_one, decoderNum_eval_neg_one,
      (Nat.cast_ne_zero.mpr (groupWords_card_pos C.GX).ne' : ((groupWords C.GX).card : ℂ) ≠ 0)]
  · simpa [suppressionOrder] using
      (le_rootMultiplicity_iff (decoder_add_one_ne_zero C)).mpr (decoder_add_one_dvd C hd)


theorem result : claim := by
  intro n d C hd
  refine ⟨?_, (infinity_suppression C hd).1, (infinity_suppression C hd).2⟩
  intro a ha
  rcases ha with h | h | h
  · subst a
    exact zero_suppression C hd
  · subst a
    exact one_suppression C hd
  · subst a
    exact neg_one_suppression C hd


#check result
#print axioms result
end D5.S3.Quantum.Information.CSSMeromorphicSuppression
