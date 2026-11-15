/- GID: D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation
   mirror-E: none(waiver:external-open-problem-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.claim; result=D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.result; claim=D5/S3/FiniteGroups/SubsetProducts/BajnokGolayRestrictedBasisRefutation.claim
   digest: The Golay quotient has a perfect restricted three-basis of size twenty-three. -/


/-
proof_shape: ShortWord, puncturedEncode, puncturedCode, GolayGroup,
  ListedFamily, claim: definition;
  admission_basis: open-problem-resolution (#30733; Refuted).
proof_shape: puncturedEncode_injective: bind-only;
  escape_witness: none; consumer: puncturedCode_card.
proof_shape: puncturedCode_card, golay_group_card: bind-only;
  escape_witness: none; consumer: golay_perfect_restricted_basis, golay_not_listed.
proof_shape: punctured_minimum_weight: bind-only;
  escape_witness: none;
  consumer: golay_perfect_restricted_basis.
proof_shape: golay_perfect_restricted_basis, golay_not_listed, golay_counterexample, result:
  bind-only; escape_witness: none; consumers: golay_counterexample, result;
  external settlement: source-faithful result refutes Conjecture 22 (#30733).
Direct frozen dependencies (declaration statement identities):
D5/S3/Arith/Lattices/Golay/GolayEncoder.encode_injective;
  statement_id sha256:4a8f94972a4283e38bd3ae65eafaad4e49171a8bcb68a61250c726398302bf61;
D5/S3/Arith/Lattices/Golay/GolayEncoder.parity_extension;
  statement_id sha256:0bc2902471caba5cba2cc2319215a0d0a6c2aa4fce021458583a788eda7fa33f;
D5/S3/Arith/Lattices/Golay/GolayEncoder.minimum_weight;
  statement_id sha256:4be4d101d4459429e6f4ef6602bb63818151c307097deec320e1cc438843f296;
D5/S3/Arith/Lattices/Golay/GolayEncoder.encode;
  statement_id sha256:07fc3ac34f41ceae787218d3feb6520115dfaefb307de8b5c5a9cec4df5435fd;
D5/S3/FiniteGroups/BajnokBersonJustPerfectRestrictedBasis.IsPerfectRestrictedBasis;
  statement_id sha256:d6d92226693d885c5361c46cd097699517cff4764304c09b541f5eb4da8c95a8.
The public helper audits remain unfinished: #30740,
https://github.com/the-omega-institute/trureturing/issues/30740.
The designated result : Not claim is exempt from four-slot registration.
-/

import D5.S3.FiniteGroups.SubsetProducts.BinaryCodePerfectRestrictedBasis
import D5.S3.Arith.Lattices.Golay.GolayEncoder
import Mathlib.GroupTheory.Coset.Card

/-! The bounded subset sums are the correctable error syndromes of the binary
Golay code. This identifies an additive quotient group with a perfect restricted
three-basis, in the original sense including the empty sum. -/

noncomputable section

namespace D5.S3.FiniteGroups.SubsetProducts.BajnokGolayRestrictedBasisRefutation

open Finset
open BajnokBersonJustPerfectRestrictedBasis
open BinaryCodePerfectRestrictedBasis

open D5.S3.Arith.Lattices.Golay

attribute [local instance] Classical.propDecidable

abbrev ShortWord := Fin 23 → F2

def puncturedEncode : GolayEncoder.Message →ₗ[F2] ShortWord :=
  (LinearMap.funLeft F2 F2 Fin.castSucc).comp GolayEncoder.encode

def puncturedCode : Submodule F2 ShortWord := LinearMap.range puncturedEncode

abbrev GolayGroup := ShortWord ⧸ puncturedCode

private theorem puncturedEncode_injective : Function.Injective puncturedEncode := by
  intro m n h
  apply GolayEncoder.encode_injective
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change GolayEncoder.encode m 23 = GolayEncoder.encode n 23
    rw [GolayEncoder.parity_extension, GolayEncoder.parity_extension]
    apply sum_congr rfl
    intro j hj
    exact congrFun h j
  · exact congrFun h j

private theorem puncturedCode_card : Nat.card puncturedCode = 4096 := by
  have e := LinearEquiv.ofInjective puncturedEncode puncturedEncode_injective
  rw [show Nat.card puncturedCode = Nat.card GolayEncoder.Message from
    Nat.card_congr e.toEquiv.symm]
  simp [GolayEncoder.Message, GolayEncoder.F2, Nat.card_eq_fintype_card, Fintype.card_pi, ZMod.card]

private theorem punctured_minimum_weight (v : ShortWord) (hv : v ∈ puncturedCode)
    (hn : v ≠ 0) : 6 < weight v := by
  obtain ⟨m, rfl⟩ := hv
  have henc : GolayEncoder.encode m ≠ 0 := by
    intro he
    apply hn
    funext i
    exact congrFun he i.castSucc
  have hmin := GolayEncoder.minimum_weight (GolayEncoder.encode m) ⟨m, rfl⟩ henc
  have hweight : GolayEncoder.weight (GolayEncoder.encode m) ≤ weight (puncturedEncode m) + 1 := by
    rw [GolayEncoder.weight, Fin.sum_univ_castSucc]
    have hsum : (∑ i : Fin 23, if GolayEncoder.encode m i.castSucc = 0 then 0 else 1) =
        weight (puncturedEncode m) := by
      simp only [weight, card_filter]
      apply sum_congr rfl
      intro i hi
      change (if GolayEncoder.encode m i.castSucc = 0 then 0 else 1) =
        if GolayEncoder.encode m i.castSucc ≠ 0 then 1 else 0
      split_ifs <;> simp_all
    rw [hsum]
    split_ifs <;> omega
  omega

theorem golay_group_card : Nat.card GolayGroup = 2048 := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    puncturedCode.toAddSubgroup
  change Nat.card ShortWord = Nat.card GolayGroup * Nat.card puncturedCode at h
  rw [puncturedCode_card] at h
  have hw : Nat.card ShortWord = 8388608 := by
    simp [ShortWord, F2, Nat.card_eq_fintype_card, Fintype.card_pi, ZMod.card]
  rw [hw] at h
  omega

theorem golay_perfect_restricted_basis :
    ∃ A : Finset GolayGroup, A.card = 23 ∧ IsPerfectRestrictedBasis 3 A := by
  apply basis_of_minimum_weight 23 3 puncturedCode (by omega)
  · exact punctured_minimum_weight
  · rw [golay_group_card, card_subsets]
    norm_num [sum_range_succ, Nat.choose]

/-- The last factor parameter records both the printed integer-power family and
the finite binary-power family intended in the companion paper. -/
def ListedFamily (G : Type) [AddCommGroup G] (s m : ℕ)
    (R : Type) [AddCommGroup R] : Prop :=
  Nat.card G = 2 ^ m ∨
    Nonempty (G ≃+ ZMod (2 ^ (s + 1) - 1)) ∨
    Nonempty (G ≃+ (Fin (2 * s) → F2)) ∨
    Nonempty (G ≃+ ((Fin (2 * s - 2) → R) × ZMod 4))

/-- Bajnok's Conjecture 22, preserving the literal printed final family. -/
def claim : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (m s : ℕ),
    2 ≤ m → 2 ≤ s →
      ((∃ A : Finset G, A.card = m ∧ IsPerfectRestrictedBasis s A) ↔
        ListedFamily G s m ℤ)

private theorem golay_not_listed (R : Type) [AddCommGroup R]
    (hR : Nat.card ((Fin 4 → R) × ZMod 4) ≠ 2048) :
    ¬ ListedFamily GolayGroup 3 23 R := by
  intro h
  rcases h with h | h | h | h
  · rw [golay_group_card] at h
    norm_num at h
  · obtain ⟨e⟩ := h
    have hc := Nat.card_congr e.toEquiv
    rw [golay_group_card] at hc
    norm_num [Nat.card_eq_fintype_card] at hc
  · obtain ⟨e⟩ := h
    have hc := Nat.card_congr e.toEquiv
    rw [golay_group_card] at hc
    norm_num [Nat.card_eq_fintype_card, Fintype.card_pi, F2] at hc
  · obtain ⟨e⟩ := h
    apply hR
    exact (Nat.card_congr e.toEquiv).symm.trans golay_group_card

/-- One group answers Question 11 and excludes both versions of the classification. -/
theorem golay_counterexample :
    ∃ A : Finset GolayGroup, A.card = 23 ∧ IsPerfectRestrictedBasis 3 A ∧
      ¬ ListedFamily GolayGroup 3 23 ℤ ∧ ¬ ListedFamily GolayGroup 3 23 F2 := by
  obtain ⟨A, hA, hb⟩ := golay_perfect_restricted_basis
  refine ⟨A, hA, hb, golay_not_listed ℤ ?_, golay_not_listed F2 ?_⟩
  · simp
  · norm_num [Nat.card_eq_fintype_card, Fintype.card_pi, F2]

theorem result : ¬ claim := by
  intro h
  letI : Fintype GolayGroup := Fintype.ofFinite GolayGroup
  obtain ⟨A, hA, hb, hn, _⟩ := golay_counterexample
  exact hn ((h GolayGroup 23 3 (by omega) (by omega)).mp ⟨A, hA, hb⟩)

end D5.S3.FiniteGroups.SubsetProducts.BajnokGolayRestrictedBasisRefutation
