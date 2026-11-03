/- GID: D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostConformalBRSTState
   mirror-E: none(waiver:original-algebraic-ghost-current)
   anchors: []
   utility: none
   digest: Finite original conformal and cubic current states and their literal modes. -/

/-
proof_shape: conformal_modes, current_zero_mode, Qg_signed_derivation: content
proof_shape: current_odd: bind-only helper, consumed by current_zero_mode and Qg_signed_derivation
escape_witness: Actual negative-residue normal products give the literal original
Virasoro coefficients. Finite current contractions and cc antisymmetrization give
both Ward identities; parity composition makes the difference an ordinary
commutant. These facts identify the full original cubic before the zero-iterate
identity supplies its signed derivation on all original homogeneous-state modes.
admission_basis: escape-witness
-/

import D5.S3.Quantum.Fermionic.BcGhostStateFieldIterate
import D5.S3.Quantum.Fermionic.BcGhostBRST

/-! The carrier, state-field map, Virasoro modes and full cubic are the original
ones. The current below is the raw cubic state, without an improvement term.
All infinite-index sums in this module are statewise finite sums.

This module has passed the selected native Lean build. Independent review and
official acceptance remain separate obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostStateField
open D5.S3.Quantum.Fermionic.BcGhostStateFieldIterate
open D5.S3.VertexAlgebra.FieldNormalProduct
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open private signedNormalMinusOne generatingField generatingMode generating_modes
  derivative_modes from D5.S3.Quantum.Fermionic.BcGhostStateField
open private residueClosure negativeResidue from
  D5.S3.Quantum.Fermionic.BcGhostStateFieldIterate
open private normal_finite L_vacuum from D5.S3.Quantum.Fermionic.BcGhostVirasoro
open private c_swap from D5.S3.Quantum.Fermionic.BcGhostCubic

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState

private abbrev B : VertexOperator ℂ Fock := Y (ket {0})
private abbrev C : VertexOperator ℂ Fock := Y (ket {1})
private abbrev DC : VertexOperator ℂ Fock := Y (ket {3})
private abbrev W : Fock := ket {1, 3}

/-- The explicit conformal state in sorted occupation coordinates. -/
def Omega : Fock := (-2 : ℂ) • ket {0, 3} + ket {1, 2}

/-- The raw cubic current, in the actual creator convention. -/
def Jg : Fock := ket {0, 1, 3}

private theorem finite_words :
    b (-2) (c 0 vacuum) = ket {0, 3} ∧
    b (-3) (c 1 vacuum) = -ket {1, 2} ∧
    c 1 (c 0 vacuum) = W ∧ b (-2) W = Jg := by
  norm_num [b, c, vacuum, create_ket, phase, lowerCount, W, Jg,
    Finset.filter_insert, Finset.filter_singleton, Finset.insert_comm]
  congr 1
  decide

private theorem omega_word :
    Omega = (-2 : ℂ) • b (-2) (c 0 vacuum) - b (-3) (c 1 vacuum) := by
  rw [finite_words.1, finite_words.2.1]
  simp [Omega]

private theorem vacuum_interval : Finset.Icc ((-2 : ℤ) + 2) 1 = {0, 1} := by
  ext q
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  omega

private theorem omega_vacuum : Omega = BcGhostVirasoro.L (-2) vacuum := by
  rw [omega_word, L_vacuum, vacuum_interval]
  norm_num [sub_eq_add_neg]

private theorem b_modes (n : ℤ) : (B [[n]]) = b (n - 1) :=
  stateField_creation.2.2.2.1 n

private theorem c_modes (n : ℤ) : (C [[n]]) = c (n + 2) :=
  stateField_creation.2.2.2.2 n

private theorem b_generating : B = generatingField false := by
  apply HVertexOperator.coeff_inj
  funext power
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
    b_modes, generating_modes]
  rfl

private theorem db_modes (n : ℤ) :
    ((dividedDerivative 1 B) [[n]]) = -(n : ℂ) • b (n - 2) := by
  rw [b_generating, derivative_modes, Ring.choose_one_right]
  simp only [generatingMode, Bool.false_eq_true, ite_false]
  congr 1
  · push_cast
    ring
  · congr 1
    omega

private theorem identity_modes (n : ℤ) :
    ((identityField : VertexOperator ℂ Fock) [[n]]) =
      if n = -1 then LinearMap.id else 0 := by
  rw [identityField, VertexOperator.ncoeff_of_coeff]
  simp only [show -n - 1 = 0 ↔ n = -1 by omega]

/- The derivative state is identified by the actual iterate on the vacuum.
This does not assume a state/translation reconstruction certificate. -/
private theorem dc_modes (n : ℤ) : (DC [[n]]) = -(n : ℂ) • c (n + 1) := by
  classical
  have odd : parity (ket {1}) = (-1 : ℂ) ^ 1 • ket {1} := by
    simp [parity_ket]
  have even : parity vacuum = (-1 : ℂ) ^ 0 • vacuum := by
    simp [vacuum, parity_ket]
  have initial : (C [[-2]]) vacuum = ket {3} := by
    rw [c_modes]
    norm_num [c, create_vacuum]
  have square (i : ℕ) : (-1 : ℂ) ^ i * (-1 : ℂ) ^ i = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have weight (i : ℕ) :
      (-1 : ℂ) ^ i * ((Ring.choose (-2 : ℤ) i : ℤ) : ℂ) = (i : ℂ) + 1 := by
    rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, Ring.choose_neg',
      Ring.multichoose_two]
    simp only [Units.smul_def, smul_eq_mul, Int.cast_mul,
      Int.cast_negOnePow_natCast, Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [← mul_assoc, square, one_mul]
  apply LinearMap.ext
  intro v
  have h := (stateField_iterate (ket {1}) vacuum v 1 0 odd even (-2) n).2.2
  dsimp only at h
  rw [initial, stateField_creation.1] at h
  simp only [weight, mul_zero, pow_zero, one_mul,
    show (-1 : ℂ) ^ (-2 : ℤ) = 1 by norm_num, one_smul] at h
  rw [h]
  change _ = -(n : ℂ) • c (n + 1) v
  by_cases hn : n < 0
  · have rightZero : ∀ i : ℕ,
        ((i : ℂ) + 1) • ((identityField : VertexOperator ℂ Fock) [[-2 + n - i]])
          ((C [[i]]) v) = 0 := by
      intro i
      simp [identity_modes, show -2 + n - (i : ℤ) ≠ -1 by omega]
    simp only [rightZero, finsum_zero, sub_zero]
    rw [finsum_eq_single _ (-n - 1).toNat]
    · have hp : 0 ≤ -n - 1 := by omega
      rw [identity_modes, Int.toNat_of_nonneg hp, ite_eq_left (by omega)]
      simp only [LinearMap.id_apply, c_modes]
      rw [show (-2 : ℤ) - (-n - 1) + 2 = n + 1 by omega]
      have castIndex : ((-n - 1).toNat : ℂ) = -(n : ℂ) - 1 := by
        exact_mod_cast (Int.toNat_of_nonneg hp)
      rw [castIndex]
      congr 1
      ring
    · intro i hi
      simp [identity_modes, show n + (i : ℤ) ≠ -1 by omega]
  · have leftZero : ∀ i : ℕ,
        ((i : ℂ) + 1) • (C [[-2 - (i : ℤ)]])
          (((identityField : VertexOperator ℂ Fock) [[n + i]]) v) = 0 := by
      intro i
      simp [identity_modes, show n + (i : ℤ) ≠ -1 by omega]
    simp only [leftZero, finsum_zero, zero_sub]
    by_cases hz : n = 0
    · subst n
      simp only [Int.cast_zero, neg_zero, zero_smul]
      apply neg_eq_zero.mpr
      apply finsum_eq_zero_of_forall_eq_zero
      intro i
      rw [identity_modes, ite_eq_right (show (-2 : ℤ) + 0 - (i : ℤ) ≠ -1 by omega)]
      simp
    · rw [finsum_eq_single _ (n - 1).toNat]
      · have hp : 0 ≤ n - 1 := by omega
        rw [identity_modes, Int.toNat_of_nonneg hp, ite_eq_left (by omega)]
        simp only [LinearMap.id_apply, c_modes]
        rw [show n - 1 + 2 = n + 1 by omega]
        rw [← neg_smul]
        have castIndex : ((n - 1).toNat : ℂ) = (n : ℂ) - 1 := by
          exact_mod_cast (Int.toNat_of_nonneg hp)
        rw [castIndex]
        congr 1
        ring
      · intro i hi
        simp [identity_modes, show (-2 : ℤ) + n - i ≠ -1 by omega]

/- These applications consume the actual private residue suppliers. No supplier
implementation is copied and no candidate Ward identity is an assumption. -/
private theorem negative_product (a d : Fock) (p q k : ℕ)
    (ha : parity a = (-1 : ℂ) ^ p • a)
    (hd : parity d = (-1 : ℂ) ^ q • d) :
    Y (((Y a) [[-(k : ℤ) - 1]]) d) =
      (signedNormalMinusOne ((-1 : ℂ) ^ (p * q))
        (dividedDerivative k (Y a)) (Y d)).1 :=
  (residueClosure a d p q ha hd (-(k : ℤ) - 1)).trans
    (negativeResidue _ a d k)

private theorem normal_product (a d : Fock) (p q : ℕ)
    (ha : parity a = (-1 : ℂ) ^ p • a)
    (hd : parity d = (-1 : ℂ) ^ q • d) :
    Y (((Y a) [[-1]]) d) =
      (signedNormalMinusOne ((-1 : ℂ) ^ (p * q)) (Y a) (Y d)).1 := by
  have hzero : dividedDerivative 0 (Y a) = Y a := by
    apply VertexOperator.ext
    intro v
    simp [dividedDerivative]
  have h := negative_product a d p q 0 ha hd
  norm_num only [Nat.cast_zero, neg_zero, zero_sub] at h
  rw [hzero] at h
  exact h

private theorem bilinear_fields :
    Y (ket {0, 3}) = (signedNormalMinusOne (-1) B DC).1 ∧
    Y (b (-3) (c 1 vacuum)) =
      (signedNormalMinusOne (-1) (dividedDerivative 1 B) C).1 ∧
    Y W = (signedNormalMinusOne (-1) C DC).1 ∧
    Y Jg = (signedNormalMinusOne 1 B (Y W)).1 := by
  have hb : parity (ket {0}) = (-1 : ℂ) ^ 1 • ket {0} := by simp [parity_ket]
  have hc : parity (ket {1}) = (-1 : ℂ) ^ 1 • ket {1} := by simp [parity_ket]
  have hd : parity (ket {3}) = (-1 : ℂ) ^ 1 • ket {3} := by simp [parity_ket]
  have hw : parity W = (-1 : ℂ) ^ 2 • W := by norm_num [W, parity_ket]
  have c0 : c 0 vacuum = ket {3} := by norm_num [c, create_vacuum]
  have c1 : c 1 vacuum = ket {1} := by norm_num [c, create_vacuum]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := normal_product (ket {0}) (ket {3}) 1 1 hb hd
    rw [b_modes] at h
    norm_num at h
    rw [← c0, finite_words.1] at h
    rw [show (-1 : ℂ) ^ (1 * 1 : ℕ) = -1 by norm_num, c0] at h
    exact h
  · have h := negative_product (ket {0}) (ket {1}) 1 1 1 hb hc
    rw [b_modes] at h
    norm_num at h
    rw [← c1] at h
    rw [show (-1 : ℂ) ^ (1 * 1 : ℕ) = -1 by norm_num, c1] at h
    rw [c1]
    exact h
  · have h := normal_product (ket {1}) (ket {3}) 1 1 hc hd
    rw [c_modes] at h
    norm_num at h
    rw [← c0, finite_words.2.2.1] at h
    rw [show (-1 : ℂ) ^ (1 * 1 : ℕ) = -1 by norm_num, c0] at h
    exact h
  · have h := normal_product (ket {0}) W 1 2 hb hw
    rw [b_modes] at h
    norm_num at h
    rw [finite_words.2.2.2, show (-1 : ℂ) ^ (1 * 2 : ℕ) = 1 by norm_num] at h
    exact h

/- Reindex both actual integer half-lines. Finiteness is supplied on the
original state, before the sum is split. -/
private theorem integer_split (f : ℤ → Fock) (hf : Function.HasFiniteSupport f)
    (cut : ℤ) :
    (∑ᶠ q : ℤ, f q) =
      (∑ᶠ i : ℕ, f (cut - i - 1)) + (∑ᶠ i : ℕ, f (cut + i)) := by
  classical
  let lower := Set.range (fun i : ℕ => cut - i - 1)
  let upper := Set.range (fun i : ℕ => cut + i)
  have cover : lower ∪ upper = Set.univ := by
    ext q
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases h : q < cut
    · exact Or.inl ⟨(cut - q - 1).toNat, by dsimp; omega⟩
    · exact Or.inr ⟨(q - cut).toNat, by dsimp; omega⟩
  have separate : Disjoint lower upper := by
    apply Set.disjoint_left.mpr
    rintro q ⟨i, rfl⟩ ⟨j, h⟩
    dsimp at h
    omega
  calc
    _ = ∑ᶠ q ∈ lower ∪ upper, f q := by rw [cover, finsum_mem_univ]
    _ = (∑ᶠ q ∈ lower, f q) + (∑ᶠ q ∈ upper, f q) :=
      finsum_mem_union' separate (hf.inter_of_right _) (hf.inter_of_right _)
    _ = _ := by
      dsimp [lower, upper]
      rw [finsum_mem_range (fun i j h => by omega),
        finsum_mem_range (fun i j h => by omega)]

private theorem u_modes (m : ℤ) (v : Fock) :
    ((Y (ket {0, 3})) [[m + 1]]) v =
      ∑ᶠ q : ℤ, (1 - (q : ℂ)) • BcGhostVirasoro.normal (m - q) q v := by
  have hf := (normal_finite m v).smul_right (fun q : ℤ => 1 - (q : ℂ))
  change Function.HasFiniteSupport (fun q : ℤ => (1 - (q : ℂ)) •
    BcGhostVirasoro.normal (m - q) q v) at hf
  rw [integer_split _ hf (m + 2), bilinear_fields.1,
    (signedNormalMinusOne (-1) B DC).2]
  simp only [b_modes, dc_modes, LinearMap.smul_apply, map_smul, neg_one_smul]
  have lower (i : ℕ) :
      (1 - ((m + 2 - i - 1 : ℤ) : ℂ)) •
          BcGhostVirasoro.normal (m - (m + 2 - i - 1)) (m + 2 - i - 1) v =
        ((m + 1 - i - 1 : ℤ) : ℂ) • c (m + 1 - i - 1 + 1) (b ((i : ℤ) - 1) v) := by
    rw [BcGhostVirasoro.normal, ite_eq_right (by omega)]
    simp only [Module.End.mul_apply, LinearMap.neg_apply, smul_neg, ← neg_smul]
    rw [show m - (m + 2 - (i : ℤ) - 1) = (i : ℤ) - 1 by omega,
      show m + 2 - (i : ℤ) - 1 = m + 1 - i - 1 + 1 by omega]
    congr 1
    push_cast
    ring
  have upper (i : ℕ) :
      (1 - ((m + 2 + i : ℤ) : ℂ)) •
          BcGhostVirasoro.normal (m - (m + 2 + i)) (m + 2 + i) v =
        -((m + 1 + i : ℤ) : ℂ) • b (-(i : ℤ) - 1 - 1) (c (m + 1 + i + 1) v) := by
    rw [BcGhostVirasoro.normal, ite_eq_left (by omega)]
    simp only [Module.End.mul_apply]
    rw [show m - (m + 2 + (i : ℤ)) = -(i : ℤ) - 1 - 1 by omega,
      show m + 2 + (i : ℤ) = m + 1 + i + 1 by omega]
    congr 1
    push_cast
    ring
  simp only [lower, upper, neg_smul, finsum_neg_distrib]
  abel

private theorem v_modes (m : ℤ) (v : Fock) :
    ((Y (b (-3) (c 1 vacuum))) [[m + 1]]) v =
      ∑ᶠ q : ℤ, ((q - m - 2 : ℤ) : ℂ) •
        BcGhostVirasoro.normal (m - q) q v := by
  have hf := (normal_finite m v).smul_right (fun q : ℤ => ((q - m - 2 : ℤ) : ℂ))
  change Function.HasFiniteSupport (fun q : ℤ => ((q - m - 2 : ℤ) : ℂ) •
    BcGhostVirasoro.normal (m - q) q v) at hf
  rw [integer_split _ hf (m + 3), bilinear_fields.2.1,
    (signedNormalMinusOne (-1) (dividedDerivative 1 B) C).2]
  simp only [db_modes, c_modes, LinearMap.smul_apply, map_smul, neg_one_smul]
  have lower (i : ℕ) :
      ((m + 3 - i - 1 - m - 2 : ℤ) : ℂ) •
          BcGhostVirasoro.normal (m - (m + 3 - i - 1)) (m + 3 - i - 1) v =
        (i : ℂ) • c (m + 1 - i - 1 + 2) (b ((i : ℤ) - 2) v) := by
    cases i with
    | zero =>
      rw [show (m + 3 - (0 : ℕ) - 1 - m - 2 : ℤ) = 0 by omega]
      simp
    | succ i =>
      rw [BcGhostVirasoro.normal, ite_eq_right (by omega)]
      simp only [Module.End.mul_apply, LinearMap.neg_apply, smul_neg, ← neg_smul]
      rw [show m - (m + 3 - ((i + 1 : ℕ) : ℤ) - 1) = ((i + 1 : ℕ) : ℤ) - 2 by omega,
        show m + 3 - ((i + 1 : ℕ) : ℤ) - 1 = m + 1 - (i + 1 : ℕ) - 1 + 2 by omega]
      congr 1
      push_cast
      ring
  have upper (i : ℕ) :
      ((m + 3 + i - m - 2 : ℤ) : ℂ) •
          BcGhostVirasoro.normal (m - (m + 3 + i)) (m + 3 + i) v =
        -((-(i : ℤ) - 1 : ℤ) : ℂ) •
          b (-(i : ℤ) - 1 - 2) (c (m + 1 + i + 2) v) := by
    rw [BcGhostVirasoro.normal, ite_eq_left (by omega)]
    simp only [Module.End.mul_apply]
    rw [show m - (m + 3 + (i : ℤ)) = -(i : ℤ) - 1 - 2 by omega,
      show m + 3 + (i : ℤ) = m + 1 + i + 2 by omega]
    congr 1
    push_cast
    ring
  simp only [lower, upper, neg_smul, finsum_neg_distrib]
  abel

/-- Every integer conformal mode is the supplier's literal original normal sum. -/
theorem conformal_modes (m : ℤ) : ((Y Omega) [[m + 1]]) = BcGhostVirasoro.L m := by
  apply LinearMap.ext
  intro v
  have hu := (normal_finite m v).smul_right (fun q : ℤ => 1 - (q : ℂ))
  have hv := (normal_finite m v).smul_right (fun q : ℤ => ((q - m - 2 : ℤ) : ℂ))
  change Function.HasFiniteSupport (fun q : ℤ => (1 - (q : ℂ)) •
    BcGhostVirasoro.normal (m - q) q v) at hu
  change Function.HasFiniteSupport (fun q : ℤ => ((q - m - 2 : ℤ) : ℂ) •
    BcGhostVirasoro.normal (m - q) q v) at hv
  have hstate : Omega = (-2 : ℂ) • ket {0, 3} - b (-3) (c 1 vacuum) := by
    rw [omega_vacuum, L_vacuum, vacuum_interval]
    norm_num [finite_words.1, sub_eq_add_neg]
  rw [hstate, map_sub, map_smul]
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, LinearMap.sub_apply,
    LinearMap.smul_apply]
  rw [u_modes, v_modes, smul_finsum' (-2 : ℂ) hu,
    ← finsum_sub_distrib (hu.fun_comp (smul_zero (-2 : ℂ))) hv]
  change _ = ∑ᶠ q : ℤ, BcGhostVirasoro.summand m q v
  apply finsum_congr
  intro q
  simp only [BcGhostVirasoro.summand, LinearMap.smul_apply, smul_smul, ← sub_smul]
  congr 1
  push_cast
  ring

private theorem w_integer_modes (r : ℤ) (v : Fock) :
    ((Y W) [[r - 2]]) v =
      ∑ᶠ p : ℤ, ((p + 1 - r : ℤ) : ℂ) • (c p * c (r - p)) v := by
  have hf := (BcGhostBRST.cc_finite r v).smul_right
    (fun p : ℤ => ((p + 1 - r : ℤ) : ℂ))
  change Function.HasFiniteSupport (fun p : ℤ => ((p + 1 - r : ℤ) : ℂ) •
    (c p * c (r - p)) v) at hf
  rw [integer_split _ hf 2, bilinear_fields.2.2.1,
    (signedNormalMinusOne (-1) C DC).2]
  simp only [c_modes, dc_modes, LinearMap.smul_apply, map_smul, neg_one_smul]
  have lower (i : ℕ) :
      ((2 - i - 1 + 1 - r : ℤ) : ℂ) •
          (c (2 - i - 1) * c (r - (2 - i - 1))) v =
        -((r - 2 + i : ℤ) : ℂ) •
          c (-(i : ℤ) - 1 + 2) (c (r - 2 + i + 1) v) := by
    simp only [Module.End.mul_apply]
    rw [show (2 : ℤ) - i - 1 = -(i : ℤ) - 1 + 2 by omega,
      show r - (-(i : ℤ) - 1 + 2) = r - 2 + i + 1 by omega]
    congr 1
    push_cast
    ring
  have upper (i : ℕ) :
      ((2 + i + 1 - r : ℤ) : ℂ) • (c (2 + i) * c (r - (2 + i))) v =
        ((r - 2 - i - 1 : ℤ) : ℂ) •
          c (r - 2 - i - 1 + 1) (c ((i : ℤ) + 2) v) := by
    rw [c_swap, LinearMap.neg_apply, Module.End.mul_apply, smul_neg, ← neg_smul]
    rw [show (2 : ℤ) + i = (i : ℤ) + 2 by omega,
      show r - ((i : ℤ) + 2) = r - 2 - i - 1 + 1 by omega]
    congr 1
    push_cast
    ring
  simp only [lower, upper, neg_smul, finsum_neg_distrib]
  abel

private theorem w_modes (r : ℤ) : ((Y W) [[r - 2]]) = BcGhostBRST.R r := by
  apply LinearMap.ext
  intro v
  let pair (p : ℤ) : Fock := (c p * c (r - p)) v
  have hp : Function.HasFiniteSupport pair := BcGhostBRST.cc_finite r v
  let reflect : ℤ ≃ ℤ := {
    toFun p := r - p
    invFun p := r - p
    left_inv p := by dsimp; omega
    right_inv p := by dsimp; omega }
  have antisym : (∑ᶠ p : ℤ, pair p) = -(∑ᶠ p : ℤ, pair p) := by
    calc
      _ = ∑ᶠ p : ℤ, pair (reflect p) := (finsum_comp_equiv reflect).symm
      _ = ∑ᶠ p : ℤ, -pair p := by
        apply finsum_congr
        intro p
        change (c (r - p) * c (r - (r - p))) v = -(c p * c (r - p)) v
        rw [show r - (r - p) = p by omega, c_swap, LinearMap.neg_apply]
      _ = _ := finsum_neg_distrib _
  have pairZero : (∑ᶠ p : ℤ, pair p) = 0 := by
    have twice : (2 : ℂ) • (∑ᶠ p : ℤ, pair p) = 0 := by
      rw [two_smul]
      nth_rw 1 [antisym]
      exact neg_add_cancel _
    exact (smul_eq_zero.mp twice).resolve_left (by norm_num)
  let weight (p : ℤ) : Fock := ((p + 1 - r : ℤ) : ℂ) • pair p
  have hw : Function.HasFiniteSupport weight :=
    hp.smul_right (fun p : ℤ => ((p + 1 - r : ℤ) : ℂ))
  have hc : Function.HasFiniteSupport
      (fun p : ℤ => ((r : ℂ) / 2 - 1) • pair p) := hp.fun_comp (smul_zero _)
  rw [w_integer_modes]
  change (∑ᶠ p : ℤ, weight p) = ∑ᶠ p : ℤ, BcGhostBRST.rTerm r p v
  calc
    _ = (∑ᶠ p : ℤ, weight p) + ((r : ℂ) / 2 - 1) • (∑ᶠ p : ℤ, pair p) := by
      rw [pairZero, smul_zero, add_zero]
    _ = ∑ᶠ p : ℤ, (weight p + ((r : ℂ) / 2 - 1) • pair p) := by
      rw [smul_finsum' _ hp, ← finsum_add_distrib hw hc]
    _ = _ := by
      apply finsum_congr
      intro p
      simp only [weight, pair, BcGhostBRST.rTerm, LinearMap.smul_apply, ← add_smul]
      congr 1
      push_cast
      ring

private theorem c_nonneg_b (i : ℕ) :
    (C [[i]]) (ket {0}) = if i = 0 then vacuum else 0 := by
  rw [c_modes]
  have cut : ¬(i : ℤ) + 2 ≤ 1 := by omega
  by_cases hi : i = 0
  · subst i
    norm_num [c, vacuum, annihilate_ket, phase, lowerCount]
  · simp [c, cut, annihilate_ket, hi]

private theorem c_high_b (q : ℤ) (hq : 2 ≤ q) :
    c q (ket {0}) = if q = 2 then vacuum else 0 := by
  by_cases he : q = 2
  · subst q
    norm_num [c, vacuum, annihilate_ket, phase, lowerCount]
  · have cut : ¬q ≤ 1 := by omega
    have site : 2 * (q - 2).toNat ≠ 0 := by omega
    simp [c, cut, annihilate_ket, he, site]

private theorem c_high_c (q : ℤ) (hq : 2 ≤ q) : c q (ket {1}) = 0 := by
  have cut : ¬q ≤ 1 := by omega
  have site : 2 * (q - 2).toNat ≠ 1 := by omega
  simp [c, cut, annihilate_ket, site]

private theorem dc_nonneg_b (i : ℕ) :
    (DC [[i]]) (ket {0}) = if i = 1 then -vacuum else 0 := by
  rw [dc_modes, LinearMap.smul_apply]
  by_cases hz : i = 0
  · subst i
    simp
  · rw [c_high_b ((i : ℤ) + 1) (by omega)]
    by_cases he : i = 1
    · subst i
      norm_num
    · simp [he, show (i : ℤ) + 1 ≠ 2 by omega]

private theorem dc_nonneg_c (i : ℕ) : (DC [[i]]) (ket {1}) = 0 := by
  rw [dc_modes, LinearMap.smul_apply]
  by_cases hz : i = 0
  · subst i
    simp
  · rw [c_high_c ((i : ℤ) + 1) (by omega), smul_zero]

private theorem w_nonneg_b (i : ℕ) :
    ((Y W) [[i]]) (ket {0}) =
      if i = 0 then (-2 : ℂ) • ket {3} else if i = 1 then -ket {1} else 0 := by
  rw [bilinear_fields.2.2.1, (signedNormalMinusOne (-1) C DC).2]
  have cb0 : (C [[0]]) (ket {0}) = vacuum := by simpa using c_nonneg_b 0
  have db1 : (DC [[1]]) (ket {0}) = -vacuum := by simpa using dc_nonneg_b 1
  have dv : (DC [[-1]]) vacuum = ket {3} := stateField_creation.2.1 _
  have reverse :
      (∑ᶠ j : ℕ, (DC [[(i : ℤ) - j - 1]]) ((C [[j]]) (ket {0}))) =
        (DC [[(i : ℤ) - 1]]) vacuum := by
    rw [finsum_eq_single _ 0]
    · simp only [Nat.cast_zero, sub_zero]
      rw [cb0]
    · intro j hj
      simp [c_nonneg_b, hj]
  rw [reverse, neg_one_smul]
  by_cases hz : i = 0
  · subst i
    rw [finsum_eq_single _ 1]
    · simp only [Nat.cast_zero, zero_add, Nat.cast_one]
      norm_num only
      rw [db1, map_neg, dv, c_modes]
      norm_num [c, create_vacuum]
      module
    · intro j hj
      simp [dc_nonneg_b, hj]
  by_cases ho : i = 1
  · subst i
    rw [finsum_eq_single _ 0]
    · simp only [Nat.cast_zero, add_zero, Nat.cast_one]
      norm_num only
      rw [db1, map_neg, c_modes, stateField_creation.2.2.1 (ket {3}) 0 (by omega)]
      norm_num [c, create_vacuum]
    · intro j hj
      simp only [Nat.cast_one]
      rw [show (1 : ℤ) + j = ((1 + j : ℕ) : ℤ) by omega, dc_nonneg_b]
      simp [hj]
  · have forwardZero : ∀ j : ℕ,
        (C [[-(j : ℤ) - 1]]) ((DC [[(i : ℤ) + j]]) (ket {0})) = 0 := by
      intro j
      rw [show (i : ℤ) + j = ((i + j : ℕ) : ℤ) by omega, dc_nonneg_b]
      simp [show i + j ≠ 1 by omega]
    rw [finsum_eq_zero_of_forall_eq_zero forwardZero,
      stateField_creation.2.2.1 (ket {3}) ((i : ℤ) - 1) (by omega)]
    simp [hz, ho]

private theorem w_nonneg_c (i : ℕ) : ((Y W) [[i]]) (ket {1}) = 0 := by
  rw [bilinear_fields.2.2.1, (signedNormalMinusOne (-1) C DC).2]
  have forwardZero : ∀ j : ℕ,
      (C [[-(j : ℤ) - 1]]) ((DC [[(i : ℤ) + j]]) (ket {1})) = 0 := by
    intro j
    rw [show (i : ℤ) + j = ((i + j : ℕ) : ℤ) by omega, dc_nonneg_c, map_zero]
  have reverseZero : ∀ j : ℕ,
      (DC [[(i : ℤ) - j - 1]]) ((C [[j]]) (ket {1})) = 0 := by
    intro j
    rw [c_modes, c_high_c ((j : ℤ) + 2) (by omega), map_zero]
  simp [forwardZero, reverseZero]

private theorem b_nonneg_b (i : ℕ) : b ((i : ℤ) - 1) (ket {0}) = 0 := by
  have cut : ¬(i : ℤ) - 1 ≤ -2 := by omega
  simp [b, cut, annihilate_ket]

private theorem b_nonneg_c (i : ℕ) :
    b ((i : ℤ) - 1) (ket {1}) = if i = 0 then vacuum else 0 := by
  have cut : ¬(i : ℤ) - 1 ≤ -2 := by omega
  by_cases hi : i = 0
  · subst i
    norm_num [b, vacuum, annihilate_ket, phase, lowerCount, Finset.filter_singleton]
  · simp [b, cut, annihilate_ket, hi]

/- Both candidate Ward inputs are computed from the literal finite current.
In particular neither the target Ward identities nor the target mode equality
is supplied as a hypothesis. -/
private theorem current_on_generators :
    ((Y Jg) [[0]]) (ket {0}) = Omega ∧ ((Y Jg) [[0]]) (ket {1}) = W := by
  classical
  constructor
  · rw [bilinear_fields.2.2.2, (signedNormalMinusOne 1 B (Y W)).2]
    have reverseZero : ∀ i : ℕ,
        ((Y W) [[0 - i - 1]]) ((B [[i]]) (ket {0})) = 0 := by
      intro i
      rw [b_modes, b_nonneg_b, map_zero]
    simp only [reverseZero, finsum_zero, smul_zero, add_zero]
    rw [finsum_eq_sum_of_support_subset _ (s := {0, 1}) (by
      intro i hi
      by_contra hn
      have hi0 : i ≠ 0 := by intro h; exact hn (by simp [h])
      have hi1 : i ≠ 1 := by intro h; exact hn (by simp [h])
      exact hi (by simp [w_nonneg_b, hi0, hi1]))]
    norm_num [w_nonneg_b, b_modes, map_smul, map_neg, Omega,
      b, create_ket, phase, lowerCount, Finset.filter_insert, Finset.filter_singleton,
      Finset.insert_comm]
    congr 1
    decide
  · rw [bilinear_fields.2.2.2, (signedNormalMinusOne 1 B (Y W)).2]
    have forwardZero : ∀ i : ℕ,
        (B [[-(i : ℤ) - 1]]) (((Y W) [[i]]) (ket {1})) = 0 := by
      intro i
      simp [w_nonneg_c]
    simp only [zero_add, forwardZero, finsum_zero, one_smul]
    rw [finsum_eq_single _ 0]
    · simp only [Nat.cast_zero, sub_zero, b_modes]
      have bc0 : b (-1) (ket {1}) = vacuum := by simpa using b_nonneg_c 0
      norm_num only
      rw [bc0, stateField_creation.2.1]
    · intro i hi
      simp [b_modes, b_nonneg_c, hi]

/-- Parity of the actual sorted cubic occupation state. -/
theorem current_odd : parity Jg = (-1 : ℂ) ^ 1 • Jg := by
  norm_num [Jg, parity_ket]

private theorem zero_iterate (a d : Fock) (p q : ℕ)
    (ha : parity a = (-1 : ℂ) ^ p • a)
    (hd : parity d = (-1 : ℂ) ^ q • d) (n : ℤ) :
    ((Y a) [[0]]) * ((Y d) [[n]]) -
        ((-1 : ℂ) ^ (p * q)) • (((Y d) [[n]]) * ((Y a) [[0]])) =
      ((Y (((Y a) [[0]]) d)) [[n]]) := by
  apply LinearMap.ext
  intro v
  have h := (stateField_iterate a d v p q ha hd 0 n).2.2
  dsimp only at h
  have vanish (i : ℕ) (hi : i ≠ 0) : Ring.choose (0 : ℤ) i = 0 :=
    Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)
  rw [finsum_eq_single _ 0 (fun i hi => by simp [vanish i hi]),
    finsum_eq_single _ 0 (fun i hi => by simp [vanish i hi])] at h
  simpa only [Nat.cast_zero, sub_zero, add_zero, zero_add, pow_zero,
    Ring.choose_zero_right, Int.cast_one, mul_one, one_smul,
    zpow_zero, one_mul, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply] using h.symm

private theorem current_ward_b (r : ℤ) :
    ((Y Jg) [[0]]) * b r + b r * ((Y Jg) [[0]]) = BcGhostVirasoro.L r := by
  have h := zero_iterate Jg (ket {0}) 1 1 current_odd (by simp [parity_ket]) (r + 1)
  rw [current_on_generators.1, conformal_modes, b_modes] at h
  simpa using h

private theorem current_ward_c (r : ℤ) :
    ((Y Jg) [[0]]) * c r + c r * ((Y Jg) [[0]]) = BcGhostBRST.R r := by
  have h := zero_iterate Jg (ket {1}) 1 1 current_odd (by simp [parity_ket]) (r - 2)
  rw [current_on_generators.2, w_modes, c_modes] at h
  simpa using h

/-- The full original cubic, with its statewise finite ordered-pair sum. -/
theorem current_zero_mode : ((Y Jg) [[0]]) = BcGhostBRST.Qg := by
  let D : Module.End ℂ Fock := ((Y Jg) [[0]]) - BcGhostBRST.Qg
  have hb (r : ℤ) : D * b r + b r * D = 0 := by
    dsimp [D]
    calc
      _ = (((Y Jg) [[0]]) * b r + b r * ((Y Jg) [[0]])) -
          (BcGhostBRST.Qg * b r + b r * BcGhostBRST.Qg) := by noncomm_ring
      _ = 0 := by rw [current_ward_b, BcGhostBRST.ward_b, sub_self]
  have hc (r : ℤ) : D * c r + c r * D = 0 := by
    dsimp [D]
    calc
      _ = (((Y Jg) [[0]]) * c r + c r * ((Y Jg) [[0]])) -
          (BcGhostBRST.Qg * c r + c r * BcGhostBRST.Qg) := by noncomm_ring
      _ = 0 := by rw [current_ward_c, BcGhostBRST.ward_c, sub_self]
  have ordinary_b (r : ℤ) : (parity * D) * b r = b r * (parity * D) := by
    apply sub_eq_zero.mp
    calc
      _ = parity * (D * b r + b r * D) - (parity * b r + b r * parity) * D := by
        noncomm_ring
      _ = 0 := by rw [hb, (ghost_parity r).1]; simp
  have ordinary_c (r : ℤ) : (parity * D) * c r = c r * (parity * D) := by
    apply sub_eq_zero.mp
    calc
      _ = parity * (D * c r + c r * D) - (parity * c r + c r * parity) * D := by
        noncomm_ring
      _ = 0 := by rw [hc, (ghost_parity r).2]; simp
  obtain ⟨alpha, scalar⟩ := scalar_commutant (parity * D) ordinary_b ordinary_c
  have initial : D vacuum = 0 := by
    simp [D, stateField_creation.2.2.1 Jg 0 (by omega), BcGhostBRST.Qg_vacuum]
  have alphaZero : alpha = 0 := by
    have h := LinearMap.congr_fun scalar vacuum
    change parity (D vacuum) = alpha • vacuum at h
    rw [initial, map_zero] at h
    have nonzero : vacuum ≠ 0 := by simp [vacuum, ket]
    exact (smul_eq_zero.mp h.symm).resolve_right nonzero
  rw [alphaZero, zero_smul] at scalar
  have dzero : D = 0 := by
    calc
      D = (parity * parity) * D := by rw [parity_involution, one_mul]
      _ = parity * (parity * D) := mul_assoc _ _ _
      _ = 0 := by rw [scalar, mul_zero]
  exact sub_eq_zero.mp dzero

/-- Signed derivation on every original mode and every finite-occupation state.
There is no square-zero premise for this anomalous pure-ghost charge. -/
theorem Qg_signed_derivation (a : Fock) (p : ℕ)
    (ha : parity a = (-1 : ℂ) ^ p • a) (n : ℤ) :
    BcGhostBRST.Qg * ((Y a) [[n]]) -
        ((-1 : ℂ) ^ p) • (((Y a) [[n]]) * BcGhostBRST.Qg) =
      ((Y (BcGhostBRST.Qg a)) [[n]]) := by
  have h := zero_iterate Jg a 1 p current_odd ha n
  rw [current_zero_mode] at h
  simpa only [one_mul] using h

end D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState
