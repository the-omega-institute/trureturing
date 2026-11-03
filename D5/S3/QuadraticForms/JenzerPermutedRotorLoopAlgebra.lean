/- GID: D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native scalar traces and ordered Clifford products. -/

/-
Direct frozen dependencies: none (pinned Mathlib only).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22564
admission_basis: escape-witness.
escape_witness: NativeBridge.contract_involute.
Per-declaration proof_shape; names are relative to this module namespace:
AnticommutingUnitFamily: proof_shape: definition. Consumers: JenzerPermutedRotorLoop.scalar_subset_square, JenzerPermutedRotorLoopWords.selected_return_word, JenzerPermutedRotorLoop.full_trace_zero_of_not_odd, JenzerPermutedRotorLoopWords.return_expansion, JenzerPermutedRotorLoop.result, claim, JenzerPermutedRotorLoop.scalar_pair_split, JenzerPermutedRotorLoopWords.subsetProduct_square.
IsBivector: proof_shape: definition. Consumers: JenzerPermutedRotorLoopWords.selected_return_word, NativeGrade.reverse_bivector, AnticommutingUnitFamily, JenzerPermutedRotorLoop.full_trace_zero_of_not_odd, JenzerPermutedRotorLoopWords.return_expansion, NativeGrade.reverse_rotor, JenzerPermutedRotorLoop.scalar_pair_split, JenzerPermutedRotorLoopWords.subsetProduct_square.
NativeBridge.change_involute: proof_shape: content. Consumers: NativeBridge.exterior_equiv_involute.
NativeBridge.contract_involute: proof_shape: content. Consumers: NativeBridge.scalar_vector_involute, NativeBridge.change_involute.
NativeBridge.exterior_augmentation_involute: proof_shape: bind-only. Consumers: NativeBridge.scalar_vector_involute.
NativeBridge.exterior_equiv_involute: proof_shape: content. Consumers: NativeBridge.scalar_vector_involute.
NativeBridge.scalar_contraction_polar: proof_shape: bind-only. Consumers: NativeBridge.scalar_cyclic_vector.
NativeBridge.scalar_cyclic: proof_shape: content. escape_witness: D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.NativeBridge.contract_involute. Consumers: JenzerPermutedRotorLoop.full_trace_zero_of_not_odd, JenzerPermutedRotorLoop.scalar_pair_split.
NativeBridge.scalar_cyclic_vector: proof_shape: content. Consumers: NativeBridge.scalar_cyclic.
NativeBridge.scalar_left_vector: proof_shape: bind-only. Consumers: NativeBridge.scalar_contraction_polar, NativeBridge.scalar_vector_involute.
NativeBridge.scalar_vector_involute: proof_shape: content. Consumers: NativeBridge.scalar_cyclic_vector.
NativeBridge.vector_supercommutator: proof_shape: content. Consumers: NativeBridge.scalar_cyclic_vector.
NativeGrade.exterior_inverse_pair: proof_shape: bind-only. Consumers: NativeGrade.reverse_bivector.
NativeGrade.reverse_bivector: proof_shape: content. Consumers: NativeGrade.reverse_rotor.
NativeGrade.reverse_rotor: proof_shape: content. escape_witness: D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.NativeGrade.reverse_bivector. Consumers: JenzerPermutedRotorLoopWords.return_expansion.
StarCondition: proof_shape: definition.
TraceSupport.anticomm_list_product: proof_shape: bind-only. Consumers: TraceSupport.anticommuting_list_square.
TraceSupport.anticommuting_list_square: proof_shape: bind-only. escape_witness: none. Consumers: JenzerPermutedRotorLoopWords.subsetProduct_square.
TraceSupport.filtered_sort_length: proof_shape: bind-only. Consumers: TraceSupport.tracial_subset_vanishing, TraceSupport.tracial_off_diagonal_zero.
TraceSupport.selective_product_commute: proof_shape: bind-only. Consumers: TraceSupport.selective_trace_zero.
TraceSupport.selective_trace_zero: proof_shape: bind-only. Consumers: TraceSupport.tracial_subset_vanishing, TraceSupport.tracial_off_diagonal_zero.
TraceSupport.tracial_anticomm_zero: proof_shape: bind-only. Consumers: TraceSupport.selective_trace_zero.
TraceSupport.tracial_off_diagonal_zero: proof_shape: bind-only. escape_witness: none. Consumers: JenzerPermutedRotorLoop.scalar_pair_split.
TraceSupport.tracial_subset_vanishing: proof_shape: bind-only. escape_witness: none. Consumers: JenzerPermutedRotorLoop.full_trace_zero_of_not_odd.
a: proof_shape: definition. Consumers: JenzerPermutedRotorLoopWords.coefficient_complement, JenzerPermutedRotorLoopWords.chain_expansion, coefficient_square, JenzerPermutedRotorLoopWords.return_expansion, JenzerPermutedRotorLoop.result, JenzerPermutedRotorLoop.scalar_pair_split.
c: proof_shape: definition. Consumers: cosine_weight, JenzerPermutedRotorLoopWords.coefficient_complement, JenzerPermutedRotorLoopWords.chain_expansion, coefficient_square, JenzerPermutedRotorLoopWords.return_expansion, JenzerPermutedRotorLoop.result, rotor, NativeGrade.reverse_rotor, JenzerPermutedRotorLoop.scalar_pair_split, a.
chain: proof_shape: definition. Consumers: JenzerPermutedRotorLoopWords.chain_expansion, loop, JenzerPermutedRotorLoop.result.
claim: proof_shape: definition.
coefficient_square: proof_shape: bind-only. escape_witness: none. Consumers: JenzerPermutedRotorLoop.result.
cosine_weight: proof_shape: bind-only. Consumers: coefficient_square.
eta: proof_shape: definition. Consumers: JenzerPermutedRotorLoop.result, claim.
inversionCount: proof_shape: definition. Consumers: JenzerPermutedRotorLoopWords.selected_return_word, JenzerPermutedRotorLoop.returnSign, JenzerPermutedRotorLoopWords.ExteriorSum.exterior_return_expansion, JenzerPermutedRotorLoopWords.return_word_inversions, JenzerPermutedRotorLoopWords.GenericReturn.selected_permuted, JenzerPermutedRotorLoopWords.ExteriorSum.signed_top_sum_zero, JenzerPermutedRotorLoopWords.return_expansion, JenzerPermutedRotorLoop.result, claim.
loop: proof_shape: definition. Consumers: JenzerPermutedRotorLoop.result, claim.
returnProduct: proof_shape: definition. Consumers: JenzerPermutedRotorLoopWords.return_expansion, loop, JenzerPermutedRotorLoop.result.
rotor: proof_shape: definition. Consumers: returnProduct, chain, JenzerPermutedRotorLoopWords.return_expansion, NativeGrade.reverse_rotor.
s: proof_shape: definition. Consumers: cosine_weight, JenzerPermutedRotorLoopWords.coefficient_complement, JenzerPermutedRotorLoopWords.chain_expansion, coefficient_square, w, JenzerPermutedRotorLoopWords.return_expansion, JenzerPermutedRotorLoop.result, rotor, NativeGrade.reverse_rotor, JenzerPermutedRotorLoop.scalar_pair_split, a.
scalarProjection: proof_shape: definition. Consumers: StarCondition, NativeBridge.scalar_cyclic_vector, JenzerPermutedRotorLoop.scalar_subset_square, NativeBridge.scalar_contraction_polar, JenzerPermutedRotorLoop.result, claim, NativeBridge.scalar_vector_involute, NativeBridge.scalar_left_vector, NativeBridge.scalar_cyclic, JenzerPermutedRotorLoop.scalar_pair_split.
subsetProduct: proof_shape: definition. Consumers: StarCondition, JenzerPermutedRotorLoop.scalar_subset_square, JenzerPermutedRotorLoopWords.selected_return_word, JenzerPermutedRotorLoopWords.chain_expansion, JenzerPermutedRotorLoopWords.return_expansion, JenzerPermutedRotorLoop.result, JenzerPermutedRotorLoop.scalar_pair_split, JenzerPermutedRotorLoopWords.subsetProduct_square.
w: proof_shape: definition. Consumers: cosine_weight, coefficient_square, JenzerPermutedRotorLoop.result, claim.
The source uses the native grade-zero coefficient and homogeneous bivectors.
The exterior equivalence reads grades and never transports multiplication.
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.CharP.Invertible
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.Tactic.NoncommRing


namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra

noncomputable section


variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- D2.1: the native grade-zero scalar coefficient. The exterior equivalence
is used only as a linear map to read grades, never to transport multiplication. -/
def scalarProjection (q : QuadraticForm ℝ V) (x : CliffordAlgebra q) : ℝ :=
  ExteriorAlgebra.algebraMapInv (CliffordAlgebra.equivExterior q x)

/-- A bivector is a homogeneous grade-two element, not an arbitrary even element. -/
def IsBivector (q : QuadraticForm ℝ V) (x : CliffordAlgebra q) : Prop :=
  CliffordAlgebra.equivExterior q x ∈ ExteriorAlgebra.exteriorPower ℝ 2 V

/-- D3.2, including the source's requirement that the elements be bivectors. -/
def AnticommutingUnitFamily (q : QuadraticForm ℝ V) (k : ℕ)
    (B : Fin k → CliffordAlgebra q) : Prop :=
  (∀ i : Fin k, IsBivector q (B i)) ∧
  (∀ i : Fin k, B i ^ 2 = -1) ∧
  (∀ i j : Fin k, i ≠ j → B i * B j = -(B j * B i))

/-- D2.4: all noncommutative products use increasing indices. -/
def subsetProduct {q : QuadraticForm ℝ V} {k : ℕ}
    (B : Fin k → CliffordAlgebra q) (S : Finset (Fin k)) : CliffordAlgebra q :=
  ((S.sort (· ≤ ·)).map B).prod

/-- D3.3, recorded for fidelity; deliberately absent from `claim`. -/
def StarCondition {q : QuadraticForm ℝ V} {k : ℕ}
    (B : Fin k → CliffordAlgebra q) : Prop :=
  ∀ S : Finset (Fin k), S.Nonempty → scalarProjection q (subsetProduct B S) = 0

def c {k : ℕ} (θ : Fin k → ℝ) (i : Fin k) : ℝ := Real.cos (θ i / 2)
def s {k : ℕ} (θ : Fin k → ℝ) (i : Fin k) : ℝ := Real.sin (θ i / 2)
def w {k : ℕ} (θ : Fin k → ℝ) (i : Fin k) : ℝ := s θ i ^ 2

def a {k : ℕ} (θ : Fin k → ℝ) (S : Finset (Fin k)) : ℝ :=
  (∏ i ∈ S, s θ i) * ∏ i ∈ Finset.univ \ S, c θ i

/-- D2.3: the source's trigonometric rotor, with scalars embedded by algebraMap. -/
def rotor {q : QuadraticForm ℝ V} {k : ℕ}
    (B : Fin k → CliffordAlgebra q) (θ : Fin k → ℝ) (i : Fin k) : CliffordAlgebra q :=
  algebraMap ℝ (CliffordAlgebra q) (c θ i) + s θ i • B i

def chain {q : QuadraticForm ℝ V} {k : ℕ}
    (B : Fin k → CliffordAlgebra q) (θ : Fin k → ℝ) : CliffordAlgebra q :=
  ((List.finRange k).map (rotor B θ)).prod

/-- D5.2: τ lists the return order; reverse is the native Clifford reversion. -/
def returnProduct {q : QuadraticForm ℝ V} {k : ℕ}
    (B : Fin k → CliffordAlgebra q) (θ : Fin k → ℝ)
    (τ : Equiv.Perm (Fin k)) : CliffordAlgebra q :=
  ((List.finRange k).map (fun j => CliffordAlgebra.reverse (rotor B θ (τ j)))).prod

def loop {q : QuadraticForm ℝ V} {k : ℕ}
    (B : Fin k → CliffordAlgebra q) (θ : Fin k → ℝ)
    (τ : Equiv.Perm (Fin k)) : CliffordAlgebra q :=
  chain B θ * returnProduct B θ τ

/-- D5.2: inversions of τ^{-1} restricted to S, as written in the source. -/
def inversionCount {k : ℕ} (τ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) : ℕ :=
  ((S ×ˢ S).filter (fun ij => ij.1 < ij.2 ∧ τ.symm ij.2 < τ.symm ij.1)).card

/-- D5.1, using its literal definition rather than an unproved sign simplification. -/
def eta (m : ℕ) : ℝ := (-1 : ℝ) ^ m * (-1 : ℝ) ^ (m * (m + 1) / 2)

/-- Remark 5.7 in the TeX (rendered Remark 5.5), removing only the star condition
from Theorem 5.5. Fin k is the order-preserving reindexing of {1,...,k}. -/
def claim : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (q : QuadraticForm ℝ V),
    q.Nondegenerate →
    ∀ (k : ℕ), 1 ≤ k →
    ∀ (B : Fin k → CliffordAlgebra q), AnticommutingUnitFamily q k B →
    ∀ (θ : Fin k → ℝ) (τ : Equiv.Perm (Fin k)),
      scalarProjection q (loop B θ τ) =
        ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
          eta S.card * (-1 : ℝ) ^ inversionCount τ S *
            (∏ i ∈ S, w θ i) * ∏ i ∈ Finset.univ \ S, (1 - w θ i)

end

end D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.NativeBridge
noncomputable section
variable {V : Type} [AddCommGroup V] [Module ℝ V]
open CliffordAlgebra

private lemma contract_involute (q : QuadraticForm ℝ V) (d : Module.Dual ℝ V)
    (x : CliffordAlgebra q) :
    contractLeft d (involute x) = -involute (contractLeft d x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | ι_mul x v hx =>
    simp only [map_mul, involute_ι, neg_mul, map_neg, contractLeft_ι_mul,
      hx, map_sub, map_smul]
    simp [sub_eq_add_neg]

private lemma change_involute {q q' : QuadraticForm ℝ V}
    {b : LinearMap.BilinForm ℝ V} (h : b.toQuadraticMap = q' - q)
    (x : CliffordAlgebra q) :
    changeForm h (involute x) = involute (changeForm h x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
    simp only [map_mul, involute_ι, neg_mul, map_neg, changeForm_ι_mul,
      hx, contract_involute, map_sub]
    simp [sub_eq_add_neg, add_comm]

private lemma exterior_augmentation_involute (x : ExteriorAlgebra ℝ V) :
    ExteriorAlgebra.algebraMapInv (involute x) = ExteriorAlgebra.algebraMapInv x := by
  have he : (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra ℝ V →ₐ[ℝ] ℝ).comp
      involute = ExteriorAlgebra.algebraMapInv := by
    ext v
    simp [ExteriorAlgebra.algebraMapInv]
  exact DFunLike.congr_fun he x

private lemma exterior_equiv_involute (q : QuadraticForm ℝ V) (x : CliffordAlgebra q) :
    equivExterior q (involute x) = involute (equivExterior q x) :=
  change_involute (changeForm.associated_neg_proof (Q := q)) x

private lemma vector_supercommutator (q : QuadraticForm ℝ V) (v : V) (x : CliffordAlgebra q) :
    ι q v * x - involute x * ι q v = contractLeft (q.polarBilin v) x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [Algebra.commutes]
  | add x y hx hy =>
    simp only [mul_add, map_add, add_mul]
    rw [← hx, ← hy]
    abel
  | ι_mul x u hx =>
    have hrel := CliffordAlgebra.ι_mul_ι_add_swap (Q := q) v u
    rw [contractLeft_ι_mul]
    simp only [map_mul, involute_ι, neg_mul]
    rw [← hx, Algebra.smul_def]
    have hp : q.polarBilin v u = QuadraticMap.polar q v u := rfl
    rw [hp]
    noncomm_ring [← hrel]

private lemma scalar_left_vector (q : QuadraticForm ℝ V) (v : V) (x : CliffordAlgebra q) :
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q (ι q v * x) =
      ExteriorAlgebra.algebraMapInv
        (contractLeft ((QuadraticMap.associated q) v) (equivExterior q x)) := by
  unfold D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection
  change ExteriorAlgebra.algebraMapInv (changeForm (changeForm.associated_neg_proof (Q := q)) (ι q v * x)) = _
  rw [changeForm_ι_mul]
  simp [ExteriorAlgebra.algebraMapInv, map_neg]

private lemma scalar_vector_involute (q : QuadraticForm ℝ V) (v : V) (x : CliffordAlgebra q) :
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q (ι q v * involute x) =
      -D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q (ι q v * x) := by
  rw [scalar_left_vector, scalar_left_vector, exterior_equiv_involute, contract_involute,
    map_neg, exterior_augmentation_involute]

private lemma scalar_contraction_polar (q : QuadraticForm ℝ V) (v : V) (x : CliffordAlgebra q) :
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q (contractLeft (q.polarBilin v) x) =
      2 * D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q (ι q v * x) := by
  rw [scalar_left_vector]
  unfold D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection
  change ExteriorAlgebra.algebraMapInv (changeForm (changeForm.associated_neg_proof (Q := q)) (contractLeft _ x)) = _
  rw [changeForm_contractLeft]
  rw [← QuadraticMap.two_nsmul_associated ℝ q]
  simp [two_smul, two_mul]

private lemma scalar_cyclic_vector (q : QuadraticForm ℝ V) (v : V) (x : CliffordAlgebra q) :
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q (ι q v * x) =
      D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q (x * ι q v) := by
  have hs := congrArg (D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q)
    (vector_supercommutator q v (involute x))
  rw [involute_involute] at hs
  have hlin (y z : CliffordAlgebra q) :
      D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q (y-z) =
      D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q y -
      D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q z := by
    simp [D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection]
  rw [hlin, scalar_contraction_polar, scalar_vector_involute] at hs
  linarith

lemma scalar_cyclic (q : QuadraticForm ℝ V) (x y : CliffordAlgebra q) :
    D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q (x*y) =
      D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q (y*x) := by
  induction x using CliffordAlgebra.induction generalizing y with
  | algebraMap r => rw [Algebra.commutes]
  | ι v => exact scalar_cyclic_vector q v y
  | mul x z hx hz =>
    calc
      _ = D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q (x*(z*y)) := by rw [mul_assoc]
      _ = D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q ((z*y)*x) := hx _
      _ = D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q (z*(y*x)) := by rw [mul_assoc]
      _ = D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection q ((y*x)*z) := hz _
      _ = _ := by rw [mul_assoc]
  | add x z hx hz =>
    simp only [add_mul, mul_add, D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.scalarProjection, map_add] at *
    rw [hx, hz]
end
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.NativeBridge

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.NativeGrade
noncomputable section
variable {V : Type} [AddCommGroup V] [Module ℝ V]
open CliffordAlgebra

private lemma exterior_inverse_pair (q : QuadraticForm ℝ V) (v w : V) :
    (equivExterior q).symm (ExteriorAlgebra.ι ℝ v * ExteriorAlgebra.ι ℝ w) =
      ι q v * ι q w - algebraMap ℝ _ ((QuadraticMap.associated q) v w) := by
  apply (equivExterior q).injective
  rw [LinearEquiv.apply_symm_apply]
  change _ = changeForm (changeForm.associated_neg_proof (Q := q)) (_ - _)
  rw [map_sub, changeForm_ι_mul_ι, changeForm_algebraMap]
  have hneg : (QuadraticMap.associated (-q)) v w = -((QuadraticMap.associated q) v w) := by
    exact congrArg (fun b : LinearMap.BilinForm ℝ V => b v w)
      (map_neg (QuadraticMap.associated (R := ℝ) (M := V)) q)
  rw [hneg, map_neg]
  simp

private lemma reverse_bivector (q : QuadraticForm ℝ V) (B : CliffordAlgebra q)
    (hB : D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.IsBivector q B) : reverse B = -B := by
  have hh : equivExterior q B ∈
      LinearMap.range (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] ExteriorAlgebra ℝ V) *
      LinearMap.range (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] ExteriorAlgebra ℝ V) := by
    simpa only [D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.IsBivector, ExteriorAlgebra.exteriorPower, pow_two] using hB
  have haux : ∀ y ∈
      LinearMap.range (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] ExteriorAlgebra ℝ V) *
      LinearMap.range (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] ExteriorAlgebra ℝ V),
      reverse ((equivExterior q).symm y) = -((equivExterior q).symm y) := by
    intro y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      obtain ⟨v,rfl⟩ := ha
      obtain ⟨w,rfl⟩ := hb
      rw [exterior_inverse_pair, map_sub, reverse.map_mul, reverse_ι, reverse_ι, reverse.commutes]
      have hrel := CliffordAlgebra.ι_mul_ι_add_swap (Q := q) v w
      have ht : QuadraticMap.polar q v w =
          (QuadraticMap.associated q) v w + (QuadraticMap.associated q) v w := by
        have he := congrArg (fun b : LinearMap.BilinForm ℝ V => b v w)
          (QuadraticMap.two_nsmul_associated ℝ q)
        simpa only [two_smul, LinearMap.add_apply, QuadraticMap.polarBilin_apply_apply] using he.symm
      rw [ht, map_add] at hrel
      rw [show ι q w * ι q v =
        (algebraMap ℝ _ ((QuadraticMap.associated q) v w) +
          algebraMap ℝ _ ((QuadraticMap.associated q) v w)) - ι q v * ι q w from
          eq_sub_of_add_eq' hrel]
      abel
    · intro x y hx hy
      simp only [map_add, hx, hy, neg_add]
  simpa only [LinearEquiv.symm_apply_apply] using haux _ hh

lemma reverse_rotor (q : QuadraticForm ℝ V) {k : ℕ}
    (B : Fin k → CliffordAlgebra q) (hB : ∀ i, D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.IsBivector q (B i))
    (θ : Fin k → ℝ) (i : Fin k) :
    reverse (D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.rotor B θ i) =
      algebraMap ℝ _ (D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.c θ i) -
        D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.s θ i • B i := by
  simp [D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.rotor, reverse_bivector q _ (hB i), sub_eq_add_neg]
end
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.NativeGrade

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra
private lemma cosine_weight {k : ℕ} (θ : Fin k → ℝ) (i : Fin k) :
    c θ i ^ 2 = 1 - w θ i := by
  exact Real.cos_sq' (θ i / 2)

lemma coefficient_square {k : ℕ} (θ : Fin k → ℝ) (S : Finset (Fin k)) :
    a θ S ^ 2 = (∏ i ∈ S, w θ i) *
      ∏ i ∈ Finset.univ \ S, (1 - w θ i) := by
  unfold a
  rw [mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
  simp only [w, cosine_weight]
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.TraceSupport
variable {A : Type*} [Ring A] [Algebra ℝ A]

private lemma tracial_anticomm_zero (t : A →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y, t (x*y) = t (y*x)) (a b : A)
    (hsq : b*b = -1) (hab : a*b = -(b*a)) : t a = 0 := by
  have hba : b*a = -(a*b) := by rw [hab]; simp
  have he : t a = t (-a) := by
    calc
      t a = t (b*(a*b)) := by rw [← mul_assoc, hba, neg_mul, mul_assoc, hsq]; simp
      _ = t ((a*b)*b) := hcyc _ _
      _ = t (-a) := by rw [mul_assoc, hsq, mul_neg, mul_one]
  rw [map_neg] at he
  linarith

private lemma anticomm_list_product {ι : Type*} (B : ι → A) (j : ι) (l : List ι)
    (hanti : ∀ i ∈ l, B j * B i = -(B i * B j)) :
    B j * (l.map B).prod = (-1 : ℝ)^l.length • ((l.map B).prod * B j) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi := hanti i (by simp)
    have hl : ∀ z ∈ l, B j * B z = -(B z * B j) := fun z hz => hanti z (by simp [hz])
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    rw [← mul_assoc, hi, neg_mul, mul_assoc, ih hl, mul_smul_comm,
      ← mul_assoc]
    simp [neg_smul]

end D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.TraceSupport

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.TraceSupport
variable {A : Type*} [Ring A] [Algebra ℝ A]

private lemma selective_product_commute {ι : Type*} [DecidableEq ι] (B : ι → A)
    (hanti : ∀ i j, i ≠ j → B i * B j = -(B j * B i)) (j : ι) (l : List ι) :
    B j * (l.map B).prod =
      (-1 : ℝ)^(l.filter (fun i => i ≠ j)).length • ((l.map B).prod * B j) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    by_cases hi : i = j
    · subst i
      simp only [List.map_cons, List.prod_cons, List.filter_cons, ne_eq,
        not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      calc
        B j * (B j * (l.map B).prod) =
          B j * ((-1 : ℝ)^(l.filter (fun i => i ≠ j)).length • ((l.map B).prod * B j)) := by rw [ih]
        _ = _ := by rw [mul_smul_comm, ← mul_assoc]
    · have hj : j ≠ i := Ne.symm hi
      have hlen : ((i :: l).filter (fun z => z ≠ j)).length =
          (l.filter (fun z => z ≠ j)).length + 1 := by simp [hi]
      simp only [List.map_cons, List.prod_cons]
      rw [hlen, pow_succ]
      rw [← mul_assoc, hanti j i hj, neg_mul, mul_assoc, ih, mul_smul_comm, ← mul_assoc]
      simp [neg_smul]

private lemma selective_trace_zero {ι : Type*} [DecidableEq ι] (t : A →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y, t (x*y) = t (y*x)) (B : ι → A)
    (hsq : ∀ i, B i * B i = -1)
    (hanti : ∀ i j, i ≠ j → B i * B j = -(B j * B i))
    (j : ι) (l : List ι) (ho : Odd (l.filter (fun i => i ≠ j)).length) :
    t (l.map B).prod = 0 := by
  apply tracial_anticomm_zero t hcyc _ (B j) (hsq j)
  have h := selective_product_commute B hanti j l
  rw [ho.neg_one_pow, neg_one_smul] at h
  rw [h]; simp

end D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.TraceSupport

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.TraceSupport
variable {A : Type*} [Ring A] [Algebra ℝ A]

private lemma filtered_sort_length {ι : Type*} [LinearOrder ι] (S : Finset ι) (j : ι) :
    ((S.sort (· ≤ ·)).filter (fun i => i ≠ j)).length = (S.erase j).card := by
  have hn := (S.sort_nodup (· ≤ ·)).filter (fun i => decide (i ≠ j))
  rw [← List.toFinset_card_of_nodup hn, List.toFinset_filter, Finset.sort_toFinset]
  congr 1
  ext i
  simp [and_comm]



end D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.TraceSupport

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.TraceSupport
variable {A : Type*} [Ring A] [Algebra ℝ A]

lemma tracial_off_diagonal_zero {k : ℕ} (t : A →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y, t (x*y) = t (y*x)) (B : Fin k → A)
    (hsq : ∀ i, B i * B i = -1)
    (hanti : ∀ i j, i ≠ j → B i * B j = -(B j * B i))
    (S T : Finset (Fin k)) (hne : S ≠ T)
    (hexception : ¬(Odd k ∧ T = Finset.univ \ S)) :
    t (((S.sort (· ≤ ·)).map B).prod * ((T.sort (· ≤ ·)).map B).prod) = 0 := by
  have hreduce (j : Fin k) (ho : Odd ((S.erase j).card + (T.erase j).card)) :
      t (((S.sort (· ≤ ·)).map B).prod * ((T.sort (· ≤ ·)).map B).prod) = 0 := by
    have he := selective_trace_zero t hcyc B hsq hanti j
      (S.sort (· ≤ ·) ++ T.sort (· ≤ ·))
    have hh : Odd (((S.sort (· ≤ ·) ++ T.sort (· ≤ ·)).filter (fun i => i ≠ j)).length) := by
      simpa only [List.filter_append, List.length_append, filtered_sort_length] using ho
    simpa only [List.map_append, List.prod_append] using he hh
  by_cases ho : Odd (S.card + T.card)
  · have hj : ∃ j, (j ∈ S ∧ j ∈ T) ∨ (j ∉ S ∧ j ∉ T) := by
      by_contra hn
      push_neg at hn
      have heq : T = Finset.univ \ S := by
        ext j
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        have hh := hn j
        tauto
      have hd : Disjoint S T := by rw [heq]; exact Finset.disjoint_sdiff
      have hu : S ∪ T = Finset.univ := by
        rw [heq]
        exact Finset.union_sdiff_of_subset (Finset.subset_univ S)
      have hc : S.card + T.card = k := by
        rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_univ, Fintype.card_fin]
      exact hexception ⟨by simpa only [hc] using ho, heq⟩
    obtain ⟨j, hj⟩ := hj
    apply hreduce j
    rcases hj with ⟨hjS,hjT⟩ | ⟨hjS,hjT⟩
    · rw [Finset.card_erase_of_mem hjS, Finset.card_erase_of_mem hjT]
      have hS : 0 < S.card := Finset.card_pos.mpr ⟨j,hjS⟩
      have hT : 0 < T.card := Finset.card_pos.mpr ⟨j,hjT⟩
      rw [Nat.odd_iff] at *
      omega
    · simpa only [Finset.erase_eq_of_notMem hjS, Finset.erase_eq_of_notMem hjT] using ho
  · have hj : ∃ j, (j ∈ S ∧ j ∉ T) ∨ (j ∉ S ∧ j ∈ T) := by
      by_contra hn
      push_neg at hn
      apply hne
      ext j
      have hh := hn j
      tauto
    obtain ⟨j,hj⟩ := hj
    apply hreduce j
    rcases hj with ⟨hjS,hjT⟩ | ⟨hjS,hjT⟩
    · rw [Finset.card_erase_of_mem hjS, Finset.erase_eq_of_notMem hjT]
      have hS : 0 < S.card := Finset.card_pos.mpr ⟨j,hjS⟩
      rw [Nat.odd_iff] at *
      omega
    · rw [Finset.card_erase_of_mem hjT, Finset.erase_eq_of_notMem hjS]
      have hT : 0 < T.card := Finset.card_pos.mpr ⟨j,hjT⟩
      rw [Nat.odd_iff] at *
      omega


lemma tracial_subset_vanishing {k : ℕ} (t : A →ₗ[ℝ] ℝ)
    (hcyc : ∀ x y, t (x*y) = t (y*x)) (B : Fin k → A)
    (hsq : ∀ i, B i * B i = -1)
    (hanti : ∀ i j, i ≠ j → B i * B j = -(B j * B i))
    (S : Finset (Fin k)) (hne : S.Nonempty)
    (hexception : ¬(S = Finset.univ ∧ Odd k)) :
    t ((S.sort (· ≤ ·)).map B).prod = 0 := by
  have hexc : ¬(Odd k ∧ (∅ : Finset (Fin k)) = Finset.univ \ S) := by
    intro h
    exact hexception ⟨Finset.univ_subset_iff.mp (Finset.sdiff_eq_empty_iff_subset.mp h.2.symm), h.1⟩
  simpa only [Finset.sort_empty, List.map_nil, List.prod_nil, mul_one] using
    tracial_off_diagonal_zero t hcyc B hsq hanti S ∅ hne.ne_empty hexc
end D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.TraceSupport

namespace D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.TraceSupport
variable {A : Type*} [Ring A] [Algebra ℝ A]

lemma anticommuting_list_square {ι : Type*} (B : ι → A)
    (hsq : ∀ i, B i * B i = -1)
    (hanti : ∀ i j, i ≠ j → B i * B j = -(B j * B i))
    (l : List ι) (hn : l.Nodup) :
    (l.map B).prod * (l.map B).prod =
      (-1 : ℝ)^((l.length + 1).choose 2) • (1 : A) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hn' := List.nodup_cons.mp hn
    have hc : B i * (l.map B).prod =
        (-1 : ℝ)^l.length • ((l.map B).prod * B i) := by
      apply anticomm_list_product
      intro j hj
      exact hanti i j (by intro he; subst j; exact hn'.1 hj)
    have hr : (l.map B).prod * B i =
        (-1 : ℝ)^l.length • (B i * (l.map B).prod) := by
      rw [hc, smul_smul, ← mul_pow]
      simp
    have hchoose : (l.length + 1 + 1).choose 2 =
        l.length + 1 + (l.length + 1).choose 2 := by
      rw [show (2 : ℕ) = 1 + 1 from one_add_one_eq_two.symm, Nat.choose_succ_succ']
      simp
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    calc
      (B i * (l.map B).prod) * (B i * (l.map B).prod) =
          B i * ((l.map B).prod * B i) * (l.map B).prod := by simp [mul_assoc]
      _ = (-1 : ℝ)^l.length • ((B i * B i) * ((l.map B).prod * (l.map B).prod)) := by
        rw [hr, mul_smul_comm, smul_mul_assoc]
        simp [mul_assoc]
      _ = (-1 : ℝ)^l.length • (-((-1 : ℝ)^((l.length+1).choose 2) • (1 : A))) := by
        rw [hsq, neg_one_mul, ih hn'.2]
      _ = _ := by
        rw [hchoose, pow_add, pow_add]
        simp [smul_smul, neg_smul, mul_comm]

end D5.S3.QuadraticForms.JenzerPermutedRotorLoopAlgebra.TraceSupport
