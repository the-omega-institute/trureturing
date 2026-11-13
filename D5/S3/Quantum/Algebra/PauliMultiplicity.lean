/- GID: D5/S3/Quantum/Algebra/PauliMultiplicity
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PauliMultiplicity
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.ProdL2]
   utility: none
   digest: Two anticommuting self-adjoint axes with positive scalar-square radii have simultaneous Hilbert two-copy coordinates. -/

import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace D5.S3.Quantum.Algebra.PauliMultiplicity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

private theorem normalized_coordinates (n m : H →L[ℂ] H)
    (hn : n.toLinearMap.IsSymmetric) (hm : m.toLinearMap.IsSymmetric)
    (hni : ∀ x, n (n x) = x) (hmi : ∀ x, m (m x) = x)
    (ha : ∀ x, n (m x) = -m (n x)) :
    ∃ K : Submodule ℂ H, IsClosed (K : Set H) ∧ Nontrivial K ∧
      ∃ U : WithLp 2 (K × K) ≃ₗᵢ[ℂ] H,
        (∀ p, U p = (p.fst : H) + m p.snd) ∧
        (∀ p, n (U p) = U (WithLp.toLp 2 (p.fst, -p.snd))) ∧
        (∀ p, m (U p) = U (WithLp.toLp 2 (p.snd, p.fst))) := by
  have hns (x y : H) : inner ℂ (n x) y = inner ℂ x (n y) := hn x y
  have hms (x y : H) : inner ℂ (m x) y = inner ℂ x (m y) := hm x y
  let K : Submodule ℂ H := LinearMap.ker (n - 1).toLinearMap
  have hK (x : H) : x ∈ K ↔ n x = x := by
    change n x - x = 0 ↔ n x = x
    exact sub_eq_zero
  have hclosed : IsClosed (K : Set H) := (n - 1).isClosed_ker
  let : CompleteSpace K := hclosed.completeSpace_coe
  have neg_of_orth (z : Kᗮ) : n (z : H) = -(z : H) := by
    have hnz : n (z : H) ∈ Kᗮ := by
      rw [Submodule.mem_orthogonal]
      intro x hx
      rw [← hns x (z : H), (hK x).mp hx]
      exact ((Submodule.mem_orthogonal K (z : H)).mp z.property) x hx
    have hp : (z : H) + n z ∈ K := by
      apply (hK _).mpr
      rw [map_add, hni]
      exact add_comm _ _
    have hpo : (z : H) + n z ∈ Kᗮ := Kᗮ.add_mem z.property hnz
    have hz : (z : H) + n z = 0 :=
      (Submodule.disjoint_def.mp K.orthogonal_disjoint) _ hp hpo
    exact eq_neg_of_add_eq_zero_right hz
  have orth_m (u : K) : m (u : H) ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    have he := hns v (m u)
    rw [(hK v).mp hv, ha, (hK u).mp u.property, inner_neg_right] at he
    linear_combination (1 / 2 : ℂ) * he
  let mi : H →ₗᵢ[ℂ] H := m.toLinearMap.isometryOfInner (by
    intro x y
    change inner ℂ (m x) (m y) = inner ℂ x y
    rw [hms x (m y), hmi])
  let j : K →ₗᵢ[ℂ] Kᗮ :=
    { toLinearMap :=
        { toFun := fun u => ⟨m u, orth_m u⟩
          map_add' := by intros; apply Subtype.ext; simp
          map_smul' := by intros; apply Subtype.ext; simp }
      norm_map' := fun u => mi.norm_map u }
  have hj : Function.Surjective j := by
    intro z
    have hz : m (z : H) ∈ K := by
      apply (hK _).mpr
      rw [ha, neg_of_orth, map_neg, neg_neg]
    exact ⟨⟨m z, hz⟩, Subtype.ext (hmi z)⟩
  let J : K ≃ₗᵢ[ℂ] Kᗮ := LinearIsometryEquiv.ofSurjective j hj
  let U : WithLp 2 (K × K) ≃ₗᵢ[ℂ] H :=
    (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℂ K) J).trans
      K.orthogonalDecomposition.symm
  have hU (p : WithLp 2 (K × K)) : U p = (p.fst : H) + m p.snd := rfl
  have hnontrivial : Nontrivial K := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    let : Subsingleton K := hs
    have hzero (x : H) : x = 0 := by
      obtain ⟨p, rfl⟩ := U.surjective x
      rw [hU]
      have hf : p.fst = 0 := Subsingleton.elim _ _
      have hs' : p.snd = 0 := Subsingleton.elim _ _
      simp [hf, hs']
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    exact hx (hzero x)
  refine ⟨K, hclosed, hnontrivial, U, hU, ?_, ?_⟩
  · intro p
    rw [hU, map_add, (hK p.fst).mp p.fst.property, ha,
      (hK p.snd).mp p.snd.property, hU]
    simp
  · intro p
    rw [hU, map_add, hmi, hU]
    exact add_comm _ _

/-- A Hilbert multiplicity space and one unitary give both actual axis actions. -/
theorem exists_pauli_multiplicity (X Y : H →L[ℂ] H)
    (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hXX : X * X = ((r ^ 2 : ℝ) : ℂ) • 1)
    (hYY : Y * Y = ((s ^ 2 : ℝ) : ℂ) • 1)
    (hXY : X * Y = -(Y * X)) :
    ∃ K : Submodule ℂ H, IsClosed (K : Set H) ∧ Nontrivial K ∧
      ∃ U : WithLp 2 (K × K) ≃ₗᵢ[ℂ] H,
        (∀ p, U p = (p.fst : H) + (s : ℂ)⁻¹ • Y p.snd) ∧
        (∀ p, X (U p) = U (WithLp.toLp 2
          ((r : ℂ) • p.fst, -(r : ℂ) • p.snd))) ∧
        (∀ p, Y (U p) = U (WithLp.toLp 2
          ((s : ℂ) • p.snd, (s : ℂ) • p.fst))) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  let n : H →L[ℂ] H := (r : ℂ)⁻¹ • X
  let m : H →L[ℂ] H := (s : ℂ)⁻¹ • Y
  have hni (x : H) : n (n x) = x := by
    change (r : ℂ)⁻¹ • X ((r : ℂ)⁻¹ • X x) = x
    rw [map_smul, smul_smul, ← mul_apply_eq_comp, hXX]
    simp only [smul_apply, one_apply_eq_self, Complex.ofReal_pow]
    change ((r : ℂ)⁻¹ * (r : ℂ)⁻¹) • ((r : ℂ)^2 • x) = x
    rw [smul_smul]
    have hc : (r : ℂ)⁻¹ * (r : ℂ)⁻¹ * (r : ℂ)^2 = 1 := by field_simp
    rw [hc, one_smul]
  have hmi (x : H) : m (m x) = x := by
    change (s : ℂ)⁻¹ • Y ((s : ℂ)⁻¹ • Y x) = x
    rw [map_smul, smul_smul, ← mul_apply_eq_comp, hYY]
    simp only [smul_apply, one_apply_eq_self, Complex.ofReal_pow]
    change ((s : ℂ)⁻¹ * (s : ℂ)⁻¹) • ((s : ℂ)^2 • x) = x
    rw [smul_smul]
    have hc : (s : ℂ)⁻¹ * (s : ℂ)⁻¹ * (s : ℂ)^2 = 1 := by field_simp
    rw [hc, one_smul]
  have hn : n.toLinearMap.IsSymmetric := by
    exact LinearMap.IsSymmetric.smul (by simp) hX.isSymmetric
  have hm : m.toLinearMap.IsSymmetric := by
    exact LinearMap.IsSymmetric.smul (by simp) hY.isSymmetric
  have ha (x : H) : n (m x) = -m (n x) := by
    have h := congrArg (fun T : H →L[ℂ] H => T x) hXY
    change X (Y x) = -(Y (X x)) at h
    simp only [n, m, smul_apply, map_smul]
    rw [h]
    simp [smul_smul, mul_comm]
  obtain ⟨K, hclosed, hnt, U, hU, hnU, hmU⟩ :=
    normalized_coordinates n m hn hm hni hmi ha
  have hXn (x : H) : X x = (r : ℂ) • n x := by simp [n, smul_smul, hr0]
  have hYm (x : H) : Y x = (s : ℂ) • m x := by simp [m, smul_smul, hs0]
  refine ⟨K, hclosed, hnt, U, hU, ?_, ?_⟩
  · intro p
    rw [hXn, hnU, ← map_smul]
    congr 1
    apply WithLp.ofLp_injective 2
    simp
  · intro p
    rw [hYm, hmU, ← map_smul]
    rfl

#print axioms exists_pauli_multiplicity
end D5.S3.Quantum.Algebra.PauliMultiplicity
