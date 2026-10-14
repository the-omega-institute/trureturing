/- GID: D5/S3/QuadraticForms/FiniteHermitianCongruence
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/FiniteHermitianCongruence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every finite Hermitian matrix is congruent to an identity block and a zero radical. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryInvolutionField
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal

namespace D5.S3.QuadraticForms.FiniteHermitianCongruence

open Module Matrix

universe u

/-- Every finite Hermitian matrix is congruent to an identity block followed by its radical. -/
theorem finite_hermitian_congruence
    {K : Type u} [Field K] [Finite K]
    (sigma : K ≃+* K) (hinv : Function.Involutive sigma)
    (hne : sigma ≠ RingEquiv.refl K) (N : ℕ)
    (B : Matrix (Fin N) (Fin N) K)
    (hB : (B.map sigma).transpose = B) :
    ∃ T : Matrix (Fin N) (Fin N) K, IsUnit T ∧
      T.transpose * B * T.map sigma =
        Matrix.diagonal (fun i : Fin N => if i.val < B.rank then 1 else 0) := by
  classical
  -- Normalize one nonzero self-pairing and recurse on its orthogonal complement.
  have diagonalize (d : ℕ) : ∀ (V : Type u) [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] (b : V →ₗ[K] V →ₛₗ[sigma.toRingHom] K),
      (∀ x y, sigma (b x y) = b y x) → finrank K V = d →
      ∃ (v : Basis (Fin d) K V) (r : ℕ), r ≤ d ∧
        ∀ i j, b (v i) (v j) = if i = j ∧ i.val < r then 1 else 0 := by
    induction d with
    | zero =>
      intro V _ _ _ b hb hd
      refine ⟨basisOfFinrankZero hd, 0, le_rfl, ?_⟩
      intro i
      exact Fin.elim0 i
    | succ d ih =>
      intro V _ _ _ b hb hd
      -- The zero form contributes only radical vectors.
      by_cases hz : b = 0
      · let v : Basis (Fin (d + 1)) K V := hd ▸ Module.finBasis K V
        refine ⟨v, 0, Nat.zero_le _, ?_⟩
        intro i j
        simp only [hz, LinearMap.zero_apply, Nat.not_lt_zero, and_false, if_false]
      -- A nontrivial involution prevents a nonzero form from having every self-pairing zero.
      have hpivot : ∃ x : V, b x x ≠ 0 := by
        by_contra! hzero
        have hc : ∃ c : K, sigma c ≠ c := by
          by_contra! hh
          apply hne
          ext c
          exact hh c
        obtain ⟨c, hc⟩ := hc
        apply hz
        ext x y
        have hxy := hzero (x + y)
        have hcxy := hzero (x + c • y)
        simp only [map_add, LinearMap.add_apply, map_smulₛₗ,
          LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, hzero, mul_zero,
          add_zero, zero_add] at hxy hcxy
        change c * b y x + sigma c * b x y = 0 at hcxy
        have hmul : (sigma c - c) * b x y = 0 := by
          linear_combination hcxy - c * hxy
        exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hc)
      obtain ⟨x, hx⟩ := hpivot
      -- The fixed-field norm supplies the scalar that makes the pivot equal to one.
      have hfixed : sigma (b x x) = b x x := hb x x
      let a : NikolovSegal.UnitaryField.fixedField sigma :=
        ⟨(b x x)⁻¹, (NikolovSegal.UnitaryField.mem_fixedField sigma _).mpr
          (by rw [map_inv₀]; exact congrArg Inv.inv hfixed)⟩
      obtain ⟨c, hc⟩ := FiniteField.norm_surjective
        (NikolovSegal.UnitaryField.fixedField sigma) K a
      have hnorm : c * sigma c = (b x x)⁻¹ :=
        (NikolovSegal.UnitaryField.norm_formula sigma hinv hne c).symm.trans
          (congrArg Subtype.val hc)
      let e := c • x
      have he : b e e = 1 := by
        change b (c • x) (c • x) = 1
        rw [LinearMap.map_smul₂, map_smulₛₗ, smul_eq_mul, smul_eq_mul]
        change c * (sigma c * b x x) = 1
        rw [← mul_assoc, hnorm, inv_mul_cancel₀ hx]
      let ell : V →ₗ[K] K := b.flip e
      let W : Submodule K V := LinearMap.ker ell
      have hell : ell e = 1 := he
      have hcompl : IsCompl (K ∙ e) W := by
        constructor
        · apply disjoint_iff.mpr
          apply eq_bot_iff.mpr
          intro y hy
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy.1
          have ht : ell (c • e) = 0 := hy.2
          have hc : c = 0 := by simpa only [map_smul, hell, smul_eq_mul, mul_one] using ht
          simp [hc]
        · exact codisjoint_iff.mpr (ell.span_singleton_sup_ker_eq_top
            (by rw [hell]; exact one_ne_zero))
      have edim : finrank K W = d := by
        have hdim := Submodule.finrank_add_eq_of_isCompl hcompl
        have ene : e ≠ 0 := by
          intro h
          apply (zero_ne_one : (0 : K) ≠ 1)
          simpa only [h, LinearMap.map_zero₂] using he
        rw [finrank_span_singleton ene, hd] at hdim
        omega
      let bW := b.domRestrict₁₂ W W
      obtain ⟨vW, r, hr, hvW⟩ := ih W bW (fun x y => hb x y) edim
      have hli : ∀ (c : K), ∀ y ∈ W, c • e + y = 0 → c = 0 := by
        intro c y hy hh
        have ht := congrArg ell hh
        have hy0 : ell y = 0 := hy
        simpa [map_add, map_smul, hell, hy0] using ht
      have hsp : ∀ y : V, ∃ c : K, y + c • e ∈ W := by
        intro y
        refine ⟨-ell y, ?_⟩
        change ell (y + (-ell y) • e) = 0
        simp [map_add, map_smul, hell]
      let v := Basis.mkFinCons e vW hli hsp
      refine ⟨v, r + 1, Nat.succ_le_succ hr, ?_⟩
      intro i j
      change b ((Basis.mkFinCons e vW hli hsp) i)
        ((Basis.mkFinCons e vW hli hsp) j) = _
      simp only [Basis.coe_mkFinCons]
      refine Fin.cases ?_ (fun i => ?_) i <;>
        refine Fin.cases ?_ (fun j => ?_) j
      · simpa using he
      · have hj : b (vW j) e = 0 := (vW j).property
        have ht := hb (vW j) e
        rw [hj, map_zero] at ht
        have hnj : (0 : Fin (d + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
        simpa [hnj] using ht.symm
      · have hi : b (vW i) e = 0 := (vW i).property
        simpa using hi
      · have ht := hvW i j
        change b (vW i) (vW j) = if i = j ∧ i.val < r then 1 else 0 at ht
        simpa [Fin.ext_iff, Nat.succ_lt_succ_iff] using ht
  -- The first argument is linear and the second is sigma-semilinear.
  let b := Matrix.toLinearMapₛₗ₂' K (RingHom.id K) sigma.toRingHom B
  have hb : ∀ x y, sigma (b x y) = b y x := by
    intro x y
    have hentry (i j : Fin N) : sigma (B i j) = B j i :=
      congrArg (fun M : Matrix (Fin N) (Fin N) K => M j i) hB
    simp only [b, Matrix.toLinearMapₛₗ₂'_apply, RingHom.id_apply,
      smul_eq_mul, map_sum, map_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hentry]
    change sigma (x j) * (sigma (sigma (y i)) * B i j) =
      y i * (sigma (x j) * B i j)
    rw [hinv]
    ring
  obtain ⟨v, r, hr, hv⟩ := diagonalize N (Fin N → K) b hb (by simp)
  let T : Matrix (Fin N) (Fin N) K := (Pi.basisFun K (Fin N)).toMatrix v
  let := (Pi.basisFun K (Fin N)).invertibleToMatrix v
  have hT : IsUnit T := isUnit_of_invertible T
  have hdiag : T.transpose * B * T.map sigma =
      Matrix.diagonal (fun i : Fin N => if i.val < r then 1 else 0) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      T, Basis.toMatrix_apply, Pi.basisFun_repr]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have ht := hv i j
    simp only [b, Matrix.toLinearMapₛₗ₂'_apply, RingHom.id_apply, smul_eq_mul] at ht
    convert ht using 1
    · apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      change v i k * B k l * sigma (v j l) = v i k * (sigma (v j l) * B k l)
      ring
    · by_cases hij : i = j <;> simp [hij]
  -- The same basis matrix and its sigma image preserve rank on the two sides.
  have hrank : B.rank = r := by
    have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT
    have hdetleft : IsUnit T.transpose.det := by simpa using hdet
    have hdetright : IsUnit (T.map sigma).det := by
      change IsUnit (sigma.mapMatrix T).det
      rw [← sigma.map_det]
      exact hdet.map sigma.toMonoidHom
    have ht := congrArg Matrix.rank hdiag
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdetright,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdetleft,
      Matrix.rank_diagonal] at ht
    rw [show Fintype.card {i : Fin N // (if i.val < r then (1 : K) else 0) ≠ 0} = r from ?_] at ht
    · exact ht
    · simpa using Fintype.card_fin_lt_of_le hr
  exact ⟨T, hT, hrank ▸ hdiag⟩


end D5.S3.QuadraticForms.FiniteHermitianCongruence
