/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnTorusAlignment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnInnerUNormalization
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-! Actual all-rank diagonal-torus alignment. The weighted matrix average
generalizes the accepted PartIIA2TorusAlignment (rank3) proof, without a
complement-conjugacy or classification assumption. -/
namespace NikolovSegal.SLnTorusAlignment
open Matrix
open NikolovSegal.SLnNormalizer
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F

def Diagonal (g : G) : Prop := ∀ i j : Fin n, i ≠ j → g.val i j = 0

theorem diagonal_eq (g : G) (hg : Diagonal g) :
    g.val = Matrix.diagonal (fun i => g.val i i) := by
  classical
  ext i j
  by_cases h : i = j
  · subst j; simp
  · simp [h, hg i j h]

theorem diagonal_of_eq (g : G) (d : Fin n → F)
    (h : g.val = Matrix.diagonal d) : Diagonal g := by
  intro i j hij
  rw [h]
  exact Matrix.diagonal_apply_ne _ hij

def diagonalTorus (n : ℕ) (F : Type u) [Field F] :
    Subgroup (SpecialLinearGroup (Fin n) F) where
  carrier := {g | Diagonal g}
  one_mem' := by intro i j hij; simp [hij]
  mul_mem' := by
    intro g h hg hh
    apply diagonal_of_eq _ (fun i => g.val i i * h.val i i)
    change g.val * h.val = _
    rw [diagonal_eq g hg, diagonal_eq h hh, Matrix.diagonal_mul_diagonal]
    simp
  inv_mem' := by
    intro g hg
    have hi : (g⁻¹).val = g.val⁻¹ :=
      GeneralLinearGroup.coe_inv (SpecialLinearGroup.toGL g)
    apply diagonal_of_eq _ _
    rw [hi, diagonal_eq g hg, Matrix.inv_diagonal]

theorem mem_diagonalTorus_iff (g : G) :
    g ∈ diagonalTorus n F ↔ ∀ i j : Fin n, i ≠ j → g.val i j = 0 := Iff.rfl

theorem diagonalTorus_le_Borel : diagonalTorus n F ≤ Borel n F := by
  intro g hg i j hij
  exact hg i j (ne_of_gt (show j < i from hij))

theorem upper_diagonal_nonzero (g : G) (hg : Upper g) (i : Fin n) :
    g.val i i ≠ 0 := by
  have ht : g.val.IsUpperTriangular := fun {_ _} h => hg _ _ h
  apply SpecialLinearGroup.diagonal_neZero (fun j => g.val j j) _ i
  rw [Matrix.det_diagonal, ← Matrix.det_of_isUpperTriangular ht]
  exact g.property

/-- One actual Uplus element simultaneously aligns a whole finite triangular
subgroup whenever its genuine order is invertible in the field. -/
theorem upper_finite_subgroup_diagonal_alignment (K : Subgroup G) [Fintype K]
    (ht : ∀ k : K, Upper (k : G)) (hcard : (Fintype.card K : F) ≠ 0) :
    ∃ u : G, u ∈ Uplus n F ∧ ∀ k : K,
      (u⁻¹ * (k : G) * u).val = Matrix.diagonal (fun i => (k : G).val i i) := by
  classical
  let A := fun k : K => (k : G).val
  let N := fun k : K => A k * Matrix.diagonal (fun i => (A k i i)⁻¹)
  let M : Matrix (Fin n) (Fin n) F := (Fintype.card K : F)⁻¹ • ∑ k : K, N k
  have hn : ∀ k i, A k i i ≠ 0 := fun k i => upper_diagonal_nonzero _ (ht k) i
  have hmd : ∀ i, M i i = 1 := by
    intro i
    change (Fintype.card K : F)⁻¹ * ((∑ k : K, N k) i i) = 1
    rw [Matrix.sum_apply i i Finset.univ N]
    simp [N, Matrix.mul_diagonal, hn, hcard]
  have hmt : ∀ i j, j.val < i.val → M i j = 0 := by
    intro i j hij
    change (Fintype.card K : F)⁻¹ * ((∑ k : K, N k) i j) = 0
    rw [Matrix.sum_apply i j Finset.univ N]
    simp [N, A, Matrix.mul_diagonal, ht _ i j hij]
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (show M.IsUpperTriangular from
      fun {_ _} h => hmt _ _ h)]
    simp [hmd]
  let u : G := ⟨M, hdet⟩
  have hup : u.val = M := rfl
  have hN : ∀ h k : K, A h * N k = N (h*k) * Matrix.diagonal (fun i => A h i i) := by
    intro h k
    have hdiag : ∀ i, A (h*k) i i = A h i i * A k i i :=
      fun i => upper_mul_diag (ht h) (ht k) i
    have hAk : A (h*k) = A h * A k := rfl
    ext i j
    simp only [N, hAk, ← Matrix.mul_assoc, Matrix.mul_diagonal]
    rw [← hAk, hdiag]
    field_simp [hn]
  have hM : ∀ h : K, A h * M = M * Matrix.diagonal (fun i => A h i i) := by
    intro h
    calc
      A h * M = (Fintype.card K : F)⁻¹ • ∑ k : K, A h * N k := by
        simp [M, Finset.mul_sum]
      _ = (Fintype.card K : F)⁻¹ • ∑ k : K, N (h*k) * Matrix.diagonal (fun i => A h i i) := by
        simp_rw [hN]
      _ = (Fintype.card K : F)⁻¹ • ((∑ k : K, N (h*k)) * Matrix.diagonal (fun i => A h i i)) := by
        rw [Finset.sum_mul]
      _ = M * Matrix.diagonal (fun i => A h i i) := by
        have he : (∑ k : K, N (h*k)) = ∑ k : K, N k :=
          Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun k => rfl)
        rw [he]
        simp [M]
  refine ⟨u, ⟨hmt, hmd⟩, ?_⟩
  intro k
  change (u⁻¹).val * (k : G).val * u.val = _
  rw [Matrix.mul_assoc, hup, hM]
  rw [← hup, ← Matrix.mul_assoc, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
    SpecialLinearGroup.coe_one, one_mul]

/-- Genuine diagonal-entry embedding of the literal SL torus into units. -/
noncomputable def torusDiagonalUnits : diagonalTorus n F →* (Fin n → Fˣ) where
  toFun t i := Units.mk0 ((t : G).val i i)
    (upper_diagonal_nonzero _ (diagonalTorus_le_Borel t.property) i)
  map_one' := by funext i; apply Units.ext; simp
  map_mul' t s := by
    funext i
    apply Units.ext
    exact upper_mul_diag (diagonalTorus_le_Borel t.property)
      (diagonalTorus_le_Borel s.property) i

theorem torusDiagonalUnits_injective :
    Function.Injective (torusDiagonalUnits (n := n) (F := F)) := by
  intro t s h
  apply Subtype.ext
  apply Subtype.ext
  rw [diagonal_eq _ t.property, diagonal_eq _ s.property]
  apply congrArg Matrix.diagonal
  funext i
  exact congrArg (fun d : Fin n → Fˣ => (d i : F)) h

/-- No order oracle: Lagrange applied to the actual unit-entry embedding. -/
theorem card_torus_dvd_units [Fintype F] :
    Nat.card (diagonalTorus n F) ∣ (Fintype.card F - 1)^n := by
  classical
  have h := Subgroup.card_dvd_of_injective
    (torusDiagonalUnits (n := n) (F := F)) torusDiagonalUnits_injective
  simpa only [Nat.card_eq_fintype_card, Fintype.card_pi_const, Fintype.card_units] using h

theorem card_torus_cast_ne_zero [Fintype F] :
    (Nat.card (diagonalTorus n F) : F) ≠ 0 := by
  classical
  have hf : ((Fintype.card F - 1 : ℕ) : F) = -1 := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr (Fintype.card_pos (α := F))),
      FiniteField.cast_card_eq_zero, Nat.cast_one, zero_sub]
  obtain ⟨k, hk⟩ := card_torus_dvd_units (n := n) (F := F)
  intro h
  have he := congrArg (fun m : ℕ => (m : F)) hk
  simp only [Nat.cast_pow, hf, Nat.cast_mul, h, zero_mul] at he
  exact pow_ne_zero n (neg_ne_zero.mpr one_ne_zero) he

/-- Further correction of an actual U-preserving automorphism by an actual
Uplus element. Its torus-image order and triangularity are derived. -/
theorem U_preserving_torus_alignment [Fintype F] (beta : MulAut G)
    (hU : (Uplus n F).map beta.toMonoidHom = Uplus n F) :
    ∃ u : G, u ∈ Uplus n F ∧
      (Uplus n F).map (MulAut.conj u⁻¹ * beta).toMonoidHom = Uplus n F ∧
      (diagonalTorus n F).map (MulAut.conj u⁻¹ * beta).toMonoidHom = diagonalTorus n F := by
  classical
  have hB : (Borel n F).map beta.toMonoidHom = Borel n F := by
    rw [← normalizer_eq_Borel, Subgroup.map_equiv_normalizer_eq, hU]
  let K := (diagonalTorus n F).map beta.toMonoidHom
  letI : Fintype K := Fintype.ofFinite _
  have ht : ∀ k : K, Upper (k : G) := by
    intro k
    have hm := (Subgroup.map_mono (diagonalTorus_le_Borel (n := n) (F := F))) k.property
    rw [hB] at hm
    exact hm
  have hc : Nat.card K = Nat.card (diagonalTorus n F) :=
    (Nat.card_congr ((diagonalTorus n F).equivMapOfInjective
      beta.toMonoidHom beta.injective).toEquiv).symm
  have hcast : (Fintype.card K : F) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, hc]
    exact card_torus_cast_ne_zero
  obtain ⟨u, hu, hd⟩ := upper_finite_subgroup_diagonal_alignment K ht hcast
  let delta := MulAut.conj u⁻¹ * beta
  have hV : (Uplus n F).map delta.toMonoidHom = Uplus n F := by
    change (Uplus n F).map ((MulAut.conj u⁻¹).toMonoidHom.comp beta.toMonoidHom) = _
    rw [← Subgroup.map_map, hU]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer ((Uplus n F).inv_mem hu))
  have hle : (diagonalTorus n F).map delta.toMonoidHom ≤ diagonalTorus n F := by
    rintro z ⟨t, ht, rfl⟩
    apply diagonal_of_eq _ (fun i => (beta t).val i i)
    simpa [delta, MulAut.mul_apply, MulAut.conj_apply, mul_assoc] using
      hd ⟨beta t, Subgroup.mem_map_of_mem beta.toMonoidHom ht⟩
  have hT : (diagonalTorus n F).map delta.toMonoidHom = diagonalTorus n F := by
    apply Subgroup.eq_of_le_of_card_ge hle
    exact (Nat.card_congr ((diagonalTorus n F).equivMapOfInjective
      delta.toMonoidHom delta.injective).toEquiv).le
  exact ⟨u, hu, hV, hT⟩

variable [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p]
include p

/-- One actual determinant-one inner correction, before all targets,
preserves full Uplus and the literal diagonal torus in every rank. -/
theorem sl_inner_U_T_correction (n : ℕ) (alpha : MulAut (SpecialLinearGroup (Fin n) F)) :
    ∃ c : SpecialLinearGroup (Fin n) F,
      let beta := MulAut.conj c * alpha
      (Uplus n F).map beta.toMonoidHom = Uplus n F ∧
      (diagonalTorus n F).map beta.toMonoidHom = diagonalTorus n F ∧
      (Borel n F).map beta.toMonoidHom = Borel n F ∧
      (∀ g, beta g ∈ Uplus n F ↔ g ∈ Uplus n F) ∧
      (∀ g, beta g ∈ diagonalTorus n F ↔ g ∈ diagonalTorus n F) ∧
      (∀ g, beta g ∈ Borel n F ↔ g ∈ Borel n F) := by
  obtain ⟨c, hU, _, _, _⟩ := InnerUNormalization.sl_inner_U_Borel_correction p n alpha
  obtain ⟨u, _, hV, hT⟩ := U_preserving_torus_alignment (MulAut.conj c * alpha) hU
  let delta := MulAut.conj u⁻¹ * (MulAut.conj c * alpha)
  have hB : (Borel n F).map delta.toMonoidHom = Borel n F := by
    rw [← normalizer_eq_Borel, Subgroup.map_equiv_normalizer_eq, hV]
  have hi : ∀ H : Subgroup (SpecialLinearGroup (Fin n) F),
      H.map delta.toMonoidHom = H → ∀ g, delta g ∈ H ↔ g ∈ H := by
    intro H h g
    have hm := Subgroup.mem_map_iff_mem (f := delta.toMonoidHom) (K := H) (x := g) delta.injective
    rwa [h] at hm
  have he : MulAut.conj (u⁻¹*c) * alpha = delta := by rw [map_mul, mul_assoc]
  refine ⟨u⁻¹*c, ?_⟩
  dsimp only
  rw [he]
  exact ⟨hV, hT, hB, hi _ hV, hi _ hT, hi _ hB⟩

end NikolovSegal.SLnTorusAlignment
