/- GID: D5/S3/QuadraticForms/FiniteHermitianCharacterSum
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/FiniteHermitianCharacterSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Hermitian character sums retain their radical factor and signed norm factor. -/

import D5.S3.QuadraticForms.FiniteHermitianCongruence
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import D5.S3.QuadraticForms.SymplecticBasis
import D5.S3.Arith.CharacterSums.LanglandsFirstMainLemma.FiniteField.CharacterAPI

/-! Signed character sums over finite Hermitian spaces, including their radicals. -/

open scoped BigOperators
open Matrix

namespace D5.S3.QuadraticForms.FiniteHermitianCharacterSum

set_option maxHeartbeats 1000000

noncomputable section

variable {K : Type*} [Field K] [Finite K]

private theorem norm_character_sum (σ : K ≃+* K) (hinv : Function.Involutive σ)
    (hne : σ ≠ RingEquiv.refl K)
    (ψ : AddChar (NikolovSegal.UnitaryField.fixedField σ) ℂ) (hψ : ψ ≠ 1) :
    letI : Fintype K := Fintype.ofFinite K
    (∑ z : K, ψ (Algebra.norm (NikolovSegal.UnitaryField.fixedField σ) z)) =
      -(Nat.card (NikolovSegal.UnitaryField.fixedField σ) : ℂ) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let L := NikolovSegal.UnitaryField.fixedField σ
  letI : Fintype L := Fintype.ofFinite L
  let f : Kˣ →* Lˣ := Units.map (Algebra.norm L (S := K))
  have hf : Function.Surjective f := FiniteField.unitsMap_norm_surjective L K
  have hcard (a : Lˣ) : Fintype.card {z : Kˣ // f z = a} = Nat.card L + 1 := by
    have hc := MonoidHom.card_fiber_eq_of_mem_range f (hf a) (hf 1)
    have hc' : Fintype.card {z : Kˣ // f z = a} = Fintype.card f.ker := by
      simpa only [Fintype.card_subtype, MonoidHom.mem_ker] using hc
    rw [hc', ← Nat.card_eq_fintype_card]
    exact NikolovSegal.UnitaryField.card_normOne σ hinv hne
  have hsumunits : (∑ z : Kˣ, ψ (Algebra.norm L (z : K))) =
      (Nat.card L + 1 : ℂ) * (∑ a : Lˣ, ψ (a : L)) := by
    change (∑ z : Kˣ, ψ ((f z : Lˣ) : L)) = _
    rw [← Fintype.sum_fiberwise' f (fun a : Lˣ => ψ (a : L))]
    simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    simp only [Nat.cast_add, Nat.cast_one, Finset.mul_sum]
  have hψunits : (∑ a : Lˣ, ψ (a : L)) = -1 := by
    have h := AddChar.sum_eq_zero_of_ne_one hψ
    rw [Fintype.sum_eq_add_sum_subtype_ne _ 0] at h
    have hu := Equiv.sum_comp (unitsEquivNeZero : Lˣ ≃ {a : L // a ≠ 0})
      (fun a : {a : L // a ≠ 0} => ψ (a : L))
    change (∑ a : Lˣ, ψ (a : L)) = _ at hu
    rw [hu]
    simpa only [AddChar.map_zero_eq_one, eq_neg_iff_add_eq_zero, add_comm] using h
  rw [Fintype.sum_eq_add_sum_subtype_ne _ 0]
  have hu := Equiv.sum_comp (unitsEquivNeZero : Kˣ ≃ {z : K // z ≠ 0})
    (fun z : {z : K // z ≠ 0} => ψ (Algebra.norm L (z : K)))
  change (∑ z : Kˣ, ψ (Algebra.norm L (z : K))) = _ at hu
  rw [← hu, hsumunits, hψunits]
  simp only [Algebra.norm_zero, AddChar.map_zero_eq_one]
  change (1 : ℂ) + (Nat.card L + 1) * (-1) = -(Nat.card L : ℂ)
  ring

/-- The value of a Hermitian matrix lies in the fixed field, without an extra premise. -/
def hermitianValue (σ : K ≃+* K) (hinv : Function.Involutive σ)
    {N : ℕ} (B : Matrix (Fin N) (Fin N) K) (hB : (B.map σ).transpose = B)
    (x : Fin N → K) : NikolovSegal.UnitaryField.fixedField σ :=
  ⟨x ⬝ᵥ (B *ᵥ fun i => σ (x i)), by
    apply (NikolovSegal.UnitaryField.mem_fixedField σ _).mpr
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hentry : σ (B j i) = B i j := congrArg (fun M => M i j) hB
    rw [hentry, hinv]
    ring⟩

/-- The signed sum of any finite Hermitian form, including singular and empty forms. -/
private theorem hermitian_character_sum (σ : K ≃+* K) (hinv : Function.Involutive σ)
    (hne : σ ≠ RingEquiv.refl K) (N : ℕ) (B : Matrix (Fin N) (Fin N) K)
    (hB : (B.map σ).transpose = B)
    (ψ : AddChar (NikolovSegal.UnitaryField.fixedField σ) ℂ) (hψ : ψ ≠ 1) :
    letI : Fintype K := Fintype.ofFinite K
    (∑ x : Fin N → K, ψ (hermitianValue σ hinv B hB x)) =
      (Nat.card K : ℂ) ^ (N - B.rank) *
        (-(Nat.card (NikolovSegal.UnitaryField.fixedField σ) : ℂ)) ^ B.rank := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let L := NikolovSegal.UnitaryField.fixedField σ
  obtain ⟨T, hT, hdiag⟩ :=
    D5.S3.QuadraticForms.FiniteHermitianCongruence.finite_hermitian_congruence
      σ hinv hne N B hB
  obtain ⟨u, hu⟩ := hT
  let e : (Fin N → K) ≃ (Fin N → K) := {
    toFun := fun x => T *ᵥ x
    invFun := fun x => (↑(u⁻¹) : Matrix (Fin N) (Fin N) K) *ᵥ x
    left_inv := by
      intro x
      change (↑(u⁻¹) : Matrix (Fin N) (Fin N) K) *ᵥ (T *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, ← hu, Units.inv_mul, Matrix.one_mulVec]
    right_inv := by
      intro x
      change T *ᵥ ((↑(u⁻¹) : Matrix (Fin N) (Fin N) K) *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, ← hu, Units.mul_inv, Matrix.one_mulVec] }
  have hval (x : Fin N → K) : hermitianValue σ hinv B hB (e x) =
      ∑ i : Fin N, if i.val < B.rank then Algebra.norm L (x i) else 0 := by
    apply Subtype.ext
    change (T *ᵥ x) ⬝ᵥ (B *ᵥ fun i => σ ((T *ᵥ x) i)) = _
    have hmap : (fun i => σ ((T *ᵥ x) i)) = T.map σ *ᵥ (fun i => σ (x i)) := by
      ext i
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    rw [hmap]
    have hv := congrArg (fun M : Matrix (Fin N) (Fin N) K =>
      x ⬝ᵥ (M *ᵥ fun i => σ (x i))) hdiag
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_transpose_mulVec, dotProduct_comm] at hv
    rw [hv]
    change x ⬝ᵥ ((Matrix.diagonal fun i : Fin N => if i.val < B.rank then 1 else 0) *ᵥ
      fun i => σ (x i)) =
        (Subfield.subtype L) (∑ i : Fin N,
          if i.val < B.rank then Algebra.norm L (x i) else 0)
    simp only [Matrix.mulVec_diagonal, dotProduct, map_sum, apply_ite, map_zero]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · simpa only [one_mul, L, Subfield.subtype_apply] using
        (NikolovSegal.UnitaryField.norm_formula σ hinv hne (x i)).symm
    · simp
  have hchar (x : Fin N → K) : ψ (hermitianValue σ hinv B hB (e x)) =
      ∏ i : Fin N, ψ (if i.val < B.rank then Algebra.norm L (x i) else 0) := by
    rw [hval]
    exact congrArg Additive.toMul (map_sum ψ.toAddMonoidHom _ Finset.univ) |>.trans
      (toMul_sum _ _)
  have hcoord (i : Fin N) :
      (∑ z : K, ψ (if i.val < B.rank then Algebra.norm L z else 0)) =
        if i.val < B.rank then -(Nat.card L : ℂ) else (Nat.card K : ℂ) := by
    by_cases hi : i.val < B.rank
    · simp only [hi, ite_true]
      exact norm_character_sum σ hinv hne ψ hψ
    · simp [hi, Nat.card_eq_fintype_card]
  have hr : B.rank ≤ N := by simpa using B.rank_le_card_width
  have hsize : (Finset.univ.filter (fun i : Fin N => i.val < B.rank)).card = B.rank := by
    simpa only [← Fintype.card_subtype] using Fintype.card_fin_lt_of_le hr
  have hsize' : (Finset.univ.filter (fun i : Fin N => ¬ i.val < B.rank)).card = N - B.rank := by
    have hh := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin N => i.val < B.rank)
    rw [hsize, Finset.card_univ, Fintype.card_fin] at hh
    omega
  calc
    _ = ∑ x : Fin N → K, ψ (hermitianValue σ hinv B hB (e x)) :=
      (Equiv.sum_comp e _).symm
    _ = ∑ x : Fin N → K,
        ∏ i : Fin N, ψ (if i.val < B.rank then Algebra.norm L (x i) else 0) := by
      simp_rw [hchar]
    _ = ∏ i : Fin N, ∑ z : K, ψ (if i.val < B.rank then Algebra.norm L z else 0) :=
      (Fintype.prod_sum (fun (i : Fin N) (z : K) =>
        ψ (if i.val < B.rank then Algebra.norm L z else 0))).symm
    _ = ∏ i : Fin N, if i.val < B.rank then -(Nat.card L : ℂ) else (Nat.card K : ℂ) := by
      simp_rw [hcoord]
    _ = _ := by
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, hsize, hsize', mul_comm]

private theorem alternating_rank_even [CharP K 2] {N : ℕ}
    (M : Matrix (Fin N) (Fin N) K) (hs : M.IsSymm) (hd : ∀ i, M i i = 0) :
    Even M.rank := by
  classical
  let V := Fin N → K
  let b := Matrix.toBilin' M
  have hb : b.IsAlt := by
    intro x
    rw [Matrix.toBilin'_apply,
      ← Fintype.sum_prod_type (fun p : Fin N × Fin N => x p.1 * M p.1 p.2 * x p.2)]
    apply Finset.sum_involution (fun p _ => (p.2, p.1))
    · intro p _
      change x p.1 * M p.1 p.2 * x p.2 + x p.2 * M p.2 p.1 * x p.1 = 0
      rw [show M p.2 p.1 = M p.1 p.2 from hs.apply _ _]
      convert CharTwo.add_self_eq_zero (x p.1 * M p.1 p.2 * x p.2) using 1 <;> ring
    · intro p _ hp heq
      apply hp
      have h := congrArg Prod.fst heq
      change p.2 = p.1 at h
      simp [h, hd]
    · intro p _
      exact Finset.mem_univ _
    · intro p _
      rfl
  let R := LinearMap.ker M.mulVecLin
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl R
  have hnd : (b.restrict W).Nondegenerate := by
    apply b.nondegenerate_restrict_of_disjoint_orthogonal hb.isRefl
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    have hR : x ∈ R := by
      change M *ᵥ x = 0
      ext i
      obtain ⟨r, w, hrw, _⟩ := Submodule.existsUnique_add_of_isCompl hW (Pi.single i 1)
      have hw : b w x = 0 := hx.2 w w.property
      have hr : b r x = 0 := by
        have hh : b x r = 0 := by
          rw [Matrix.toBilin'_apply']
          have hz : M *ᵥ (r : V) = 0 := r.property
          rw [hz, dotProduct_zero]
        exact hb.isRefl.eq_iff.mp hh
      have hh : b (Pi.single i 1) x = 0 := by
        rw [← hrw, map_add, LinearMap.add_apply, hr, hw, add_zero]
      change Matrix.toBilin' M (Pi.single i 1) x = 0 at hh
      rw [Matrix.toBilin'_apply'] at hh
      simpa only [single_dotProduct, one_mul, Pi.zero_apply] using hh
    have hbot : x ∈ (⊥ : Submodule K V) := by
      rw [← hW.disjoint.eq_bot]
      exact ⟨hR, hx.1⟩
    exact hbot
  obtain ⟨r, e, _⟩ :=
    D5.S3.QuadraticForms.SymplecticBasis.exists_isSymplecticBasis
      (B := b.restrict W) (fun x => hb x) hnd
  have hdimW : Module.finrank K W = r + r := by
    simpa using Module.finrank_eq_card_basis e
  have hdim := Submodule.finrank_add_eq_of_isCompl hW
  have hrank : M.rank + Module.finrank K R = N := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      M.mulVecLin.finrank_range_add_finrank_ker
  have hdimV : Module.finrank K R + Module.finrank K W = N := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hdim
  exact ⟨r, by omega⟩

/-- The bilinear factor is its actual kernel cardinality, for every finite coefficient field. -/
private theorem bilinear_character_sum (N : ℕ) (M : Matrix (Fin N) (Fin N) K)
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) :
    letI : Fintype K := Fintype.ofFinite K
    (∑ y : Fin N → K, ∑ x : Fin N → K, ψ (x ⬝ᵥ (M *ᵥ y))) =
      (Nat.card K : ℂ) ^ (2 * N - M.rank) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let V := Fin N → K
  have hinner (v : V) : (∑ x : V, ψ (x ⬝ᵥ v)) =
      if v = 0 then (Nat.card K : ℂ)^N else 0 := by
    let χ : AddChar V ℂ :=
      ψ.compAddMonoidHom ((dotProductBilin K K v).toAddMonoidHom)
    have hχ : χ = 1 ↔ v = 0 := by
      constructor
      · intro h
        ext i
        by_contra hi
        have hall (a : K) : ψ (v i * a) = 1 := by
          have hh := DFunLike.congr_fun h (Pi.single i a)
          change ψ (v ⬝ᵥ Pi.single i a) = 1 at hh
          simpa only [dotProduct_single] using hh
        have heq : ψ.mulShift (v i) = 1 := by
          ext a
          exact hall a
        exact (AddChar.IsPrimitive.of_ne_one hψ hi) heq
      · intro h
        subst v
        ext x
        change ψ ((0 : V) ⬝ᵥ x) = 1
        simp
    have he : (∑ x : V, ψ (x ⬝ᵥ v)) = ∑ x : V, χ x := by
      apply Finset.sum_congr rfl
      intro x _
      exact congrArg ψ (dotProduct_comm x v)
    rw [he, AddChar.sum_eq_ite]
    simp only [show (χ = 0 ↔ v = 0) from hχ, V, Fintype.card_fun, Fintype.card_fin,
      Nat.cast_pow, Nat.card_eq_fintype_card]
  change (∑ y : V, ∑ x : V, ψ (x ⬝ᵥ (M *ᵥ y))) = _
  simp_rw [hinner]
  let R := LinearMap.ker M.mulVecLin
  have hdim : Module.finrank K R = N - M.rank := by
    have h := M.mulVecLin.finrank_range_add_finrank_ker
    change M.rank + Module.finrank K R = Module.finrank K (Fin N → K) at h
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  have hcard : Fintype.card R = Nat.card K ^ (N - M.rank) := by
    rw [Module.card_eq_pow_finrank (K := K), hdim, Nat.card_eq_fintype_card]
  have hsum : (∑ y : V, if M *ᵥ y = 0 then (Nat.card K : ℂ)^N else 0) =
      (Fintype.card R : ℂ) * (Nat.card K : ℂ)^N := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hc : Fintype.card R =
        (Finset.univ.filter (fun y : V => M *ᵥ y = 0)).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext y
      simp [R, Matrix.mulVecLin_apply]
    rw [hc]
  rw [hsum, hcard, Nat.cast_pow, ← pow_add]
  have hr : M.rank ≤ N := by simpa using M.rank_le_card_width
  congr 1
  omega

section BinaryGraph

variable [CharP K 2]

/-- The source character-mode matrix over the actual coefficient field. -/
def modeMatrix {N : ℕ} (A : Matrix (Fin N) (Fin N) (ZMod 2)) (lam : Fin N → K) :
    Matrix (Fin N) (Fin N) K :=
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  fun i j => algebraMap (ZMod 2) K (A i j) * (lam i + lam j)

/-- Row normalization of the source character-mode matrix. -/
def graphHermitianMatrix {N : ℕ} (A : Matrix (Fin N) (Fin N) (ZMod 2)) (lam : Fin N → K) :
    Matrix (Fin N) (Fin N) K :=
  fun i j => (lam i)⁻¹ * modeMatrix A lam i j

/-- The upper-triangular character-mode polynomial before pairing with its negative mode. -/
def halfPhase {N : ℕ} (A : Matrix (Fin N) (Fin N) (ZMod 2))
    (lam : Fin N → K) (x y : Fin N → K) : K :=
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  ∑ i : Fin N, ∑ j : Fin N, if i < j then
    algebraMap (ZMod 2) K (A i j) * (1 + lam j / lam i) * x i * y j else 0

private theorem halfPhase_pair {N : ℕ}
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (hA : A.IsSymm)
    (lam : Fin N → K) (hlam : ∀ i, lam i ≠ 0) (x y : Fin N → K) :
    halfPhase A lam x y + halfPhase A (fun i => (lam i)⁻¹) y x =
      (fun i => (lam i)⁻¹ * x i) ⬝ᵥ (modeMatrix A lam *ᵥ y) := by
  classical
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  unfold halfPhase
  conv_lhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change (if i < j then _ else 0) + (if j < i then _ else 0) =
    ((lam i)⁻¹ * x i) * (algebraMap (ZMod 2) K (A i j) * (lam i + lam j) * y j)
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [h, not_lt_of_gt h, ite_true, ite_false, add_zero]
    field_simp [hlam i]
  · simp only [lt_irrefl, ite_false, add_zero, CharTwo.add_self_eq_zero, mul_zero, zero_mul]
  · simp only [h, not_lt_of_gt h, ite_true, ite_false, zero_add]
    rw [hA.apply j i]
    field_simp [hlam i, hlam j]
    <;> ring

/-- Negative, independently variable graph modes give the exact bilinear rank factor. -/
theorem paired_graph_character_sum {N : ℕ}
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (hA : A.IsSymm)
    (lam : Fin N → K) (hlam : ∀ i, lam i ≠ 0)
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) :
    letI : Fintype K := Fintype.ofFinite K
    (∑ y : Fin N → K, ∑ x : Fin N → K,
      ψ (halfPhase A lam x y + halfPhase A (fun i => (lam i)⁻¹) y x)) =
      (Nat.card K : ℂ) ^ (2 * N - (modeMatrix A lam).rank) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  simp_rw [halfPhase_pair A hA lam hlam]
  let e : (Fin N → K) ≃ (Fin N → K) := {
    toFun := fun x i => (lam i)⁻¹ * x i
    invFun := fun x i => lam i * x i
    left_inv := by intro x; ext i; simp [hlam i]
    right_inv := by intro x; ext i; simp [hlam i] }
  have he (y : Fin N → K) :
      (∑ x : Fin N → K, ψ ((fun i => (lam i)⁻¹ * x i) ⬝ᵥ (modeMatrix A lam *ᵥ y))) =
        ∑ x, ψ (x ⬝ᵥ (modeMatrix A lam *ᵥ y)) :=
    Equiv.sum_comp e (fun x => ψ (x ⬝ᵥ (modeMatrix A lam *ᵥ y)))
  simp_rw [he]
  exact bilinear_character_sum N (modeMatrix A lam) ψ hψ

private theorem halfPhase_conjugate {N : ℕ}
    (σ : K ≃+* K) (hinv : Function.Involutive σ)
    (A : Matrix (Fin N) (Fin N) (ZMod 2))
    (lam : Fin N → K) (hσlam : ∀ i, σ (lam i) = (lam i)⁻¹) (x : Fin N → K) :
    σ (halfPhase A lam x (fun i => σ (x i))) =
      halfPhase A (fun i => (lam i)⁻¹) (fun i => σ (x i)) x := by
  classical
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hbase (a : ZMod 2) : σ (algebraMap (ZMod 2) K a) = algebraMap (ZMod 2) K a := by
    obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective a
    simp only [map_natCast]
  simp only [halfPhase, map_sum, apply_ite, map_zero, map_mul, map_add, map_one,
    map_div₀, hbase, hσlam]
  simp only [show ∀ a : K, σ (σ a) = a from hinv]

/-- The source graph matrix has a positive self-paired factor: its even rank removes the sign. -/
private theorem self_paired_graph_character_sum (σ : K ≃+* K) (hinv : Function.Involutive σ)
    (hne : σ ≠ RingEquiv.refl K) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (hA : A.IsSymm)
    (lam : Fin N → K) (hlam : ∀ i, lam i ≠ 0) (hσlam : ∀ i, σ (lam i) = (lam i)⁻¹)
    (ψ : AddChar (NikolovSegal.UnitaryField.fixedField σ) ℂ) (hψ : ψ ≠ 1) :
    letI : Fintype K := Fintype.ofFinite K
    ∃ hB : ((graphHermitianMatrix A lam).map σ).transpose = graphHermitianMatrix A lam,
      (∑ x : Fin N → K, ψ (hermitianValue σ hinv (graphHermitianMatrix A lam) hB x)) =
        (Nat.card K : ℂ) ^ (N - (modeMatrix A lam).rank) *
          (Nat.card (NikolovSegal.UnitaryField.fixedField σ) : ℂ) ^ (modeMatrix A lam).rank := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  let M := modeMatrix A lam
  let B := graphHermitianMatrix A lam
  have hbase (a : ZMod 2) : σ (algebraMap (ZMod 2) K a) = algebraMap (ZMod 2) K a := by
    obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective a
    simp only [map_natCast]
  have hB : (B.map σ).transpose = B := by
    ext i j
    change σ ((lam j)⁻¹ * (algebraMap (ZMod 2) K (A j i) * (lam j + lam i))) =
      (lam i)⁻¹ * (algebraMap (ZMod 2) K (A i j) * (lam i + lam j))
    rw [map_mul, map_inv₀, map_mul, map_add, hbase, hσlam, hσlam, inv_inv,
      show A j i = A i j from hA.apply _ _]
    field_simp [hlam i, hlam j]
    <;> ring
  have hsym : M.IsSymm := by
    ext i j
    change algebraMap (ZMod 2) K (A j i) * (lam j + lam i) =
      algebraMap (ZMod 2) K (A i j) * (lam i + lam j)
    rw [hA.apply j i, add_comm]
  have hdiag (i : Fin N) : M i i = 0 := by
    change algebraMap (ZMod 2) K (A i i) * (lam i + lam i) = 0
    rw [CharTwo.add_self_eq_zero, mul_zero]
  have heven := alternating_rank_even M hsym hdiag
  have hBM : B = Matrix.diagonal (fun i => (lam i)⁻¹) * M := by
    ext i j
    simp only [Matrix.diagonal_mul]
    rfl
  have hdet : IsUnit (Matrix.diagonal (fun i => (lam i)⁻¹)).det := by
    rw [Matrix.det_diagonal]
    apply isUnit_iff_ne_zero.mpr
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => inv_ne_zero (hlam i))
  have hrank : B.rank = M.rank := by
    rw [hBM]
    exact Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet
  refine ⟨hB, ?_⟩
  rw [hermitian_character_sum σ hinv hne N B hB ψ hψ, hrank, heven.neg_pow]

/-- The actual prime-field trace of a self-paired graph polynomial has its positive rank factor. -/
theorem self_paired_trace_graph_sum (σ : K ≃+* K) (hinv : Function.Involutive σ)
    (hne : σ ≠ RingEquiv.refl K) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) (ZMod 2)) (hA : A.IsSymm)
    (lam : Fin N → K) (hlam : ∀ i, lam i ≠ 0) (hσlam : ∀ i, σ (lam i) = (lam i)⁻¹)
    (η : AddChar (ZMod 2) ℂ) (hη : η ≠ 1) :
    letI : Fintype K := Fintype.ofFinite K
    letI : Algebra (ZMod 2) K := ZMod.algebra K 2
    (∑ x : Fin N → K, η (Algebra.trace (ZMod 2) K
      (halfPhase A lam x (fun i => σ (x i))))) =
        (Nat.card K : ℂ) ^ (N - (modeMatrix A lam).rank) *
          (Nat.card (NikolovSegal.UnitaryField.fixedField σ) : ℂ) ^ (modeMatrix A lam).rank := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  let L := NikolovSegal.UnitaryField.fixedField σ
  letI : Algebra (ZMod 2) L := ZMod.algebra L 2
  letI : IsScalarTower (ZMod 2) L K :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let ψ := LanglandsFirstMainLemma.traceAddChar (ZMod 2) L η
  have hψ : ψ ≠ 1 :=
    (LanglandsFirstMainLemma.traceAddChar_ne_one_iff (ZMod 2) L η).mpr hη
  obtain ⟨hB, hcount⟩ := self_paired_graph_character_sum σ hinv hne N A hA lam hlam hσlam ψ hψ
  rw [← hcount]
  apply Finset.sum_congr rfl
  intro x _
  have ht : Algebra.trace L K (halfPhase A lam x (fun i => σ (x i))) =
      hermitianValue σ hinv (graphHermitianMatrix A lam) hB x := by
    apply Subtype.ext
    rw [NikolovSegal.UnitaryField.trace_formula σ hinv hne,
      halfPhase_conjugate σ hinv A lam hσlam,
      halfPhase_pair A hA lam hlam]
    simp only [hermitianValue, dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change ((lam i)⁻¹ * x i) * (modeMatrix A lam i j * σ (x j)) =
      x i * (((lam i)⁻¹ * modeMatrix A lam i j) * σ (x j))
    ring
  change η (Algebra.trace (ZMod 2) K _) = η (Algebra.trace (ZMod 2) L _)
  let tower : IsScalarTower (ZMod 2) L K := inferInstance
  have htt (z : K) : Algebra.trace (ZMod 2) L (Algebra.trace L K z) =
      Algebra.trace (ZMod 2) K z :=
    @Algebra.trace_trace (ZMod 2) L K _ _ _ _ _ _ tower _ _ _ _ z
  rw [← htt, ht]

end BinaryGraph

end
end D5.S3.QuadraticForms.FiniteHermitianCharacterSum
