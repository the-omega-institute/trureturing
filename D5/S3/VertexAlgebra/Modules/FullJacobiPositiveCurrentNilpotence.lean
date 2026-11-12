/- GID: D5/S3/VertexAlgebra/Modules/FullJacobiPositiveCurrentNilpotence
   generality: I
   mirror-B: none(source-only-candidate)
   mirror-E: none(source-only-candidate)
   anchors: []
   utility: Literal stable-locus quotient and original positive-current endpoint.
   status: UNCOMPILED source candidate, not kernel evidence.

The original FullJacobiLatticeModule record is imported unchanged. The quotient
field is built from the actual descended coefficients, with truncation proved
on representatives. Each of its three Jacobi supports is separately contained
in the corresponding original support. No vacuum-existence premise is added.
-/
import D5.S3.VertexAlgebra.Modules.FullJacobiCurrentLocus
import Mathlib.LinearAlgebra.Quotient.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.Modules.FullJacobiPositiveCurrentNilpotence
open FullJacobiCurrentTransport FullJacobiCurrentNilpotence
open FullJacobiCurrentVacuum FullJacobiCurrentLocus
open LatticeGeneratingFieldLocality LatticeAllStateField FieldNormalProduct
open scoped BigOperators VertexOperator
noncomputable section
universe u
variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- Actual coefficient maps on the quotient by the pointwise nilpotence locus. -/
def quotientMode (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Fin D.rank) (n : ℤ) (hn : 0 < n) (a : Carrier D) (s : ℤ) :
    Module.End ℂ (M ⧸ powerNilpotenceSubmodule (current J i n)) :=
  (powerNilpotenceSubmodule (current J i n)).mapQ
    (powerNilpotenceSubmodule (current J i n)) (mode J a s)
      (by intro v hv; exact all_source_modes_stable J hD i n hn a s v hv)

@[simp] theorem quotientMode_mk (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Fin D.rank) (n : ℤ) (hn : 0 < n) (a : Carrier D) (s : ℤ) (v : M) :
    quotientMode J hD i n hn a s (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (mode J a s v) := rfl

/-- Truncation is inherited on representatives before forming a vertex operator. -/
def quotientField (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Fin D.rank) (n : ℤ) (hn : 0 < n) (a : Carrier D) :
    VertexOperator ℂ (M ⧸ powerNilpotenceSubmodule (current J i n)) :=
  VertexOperator.of_coeff (fun k => quotientMode J hD i n hn a (-k - 1)) (by
    intro w
    refine Submodule.Quotient.induction_on _ w ?_
    intro v
    obtain ⟨R, hR⟩ := module_truncation J a v
    refine ⟨-R - 1, ?_⟩
    intro k hk
    by_contra h
    have hz : mode J a (-k - 1) v = 0 := hR _ (by omega)
    exact hk (by simp [hz]))

@[simp] theorem quotientField_modes (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Fin D.rank) (n : ℤ) (hn : 0 < n) (a : Carrier D) (s : ℤ) :
    ((quotientField J hD i n hn a)[[s]]) = quotientMode J hD i n hn a s := by
  rw [quotientField, VertexOperator.ncoeff_of_coeff]
  congr 1
  omega

/-- State linearity is checked on actual quotient coefficients. -/
def quotientStateField (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Fin D.rank) (n : ℤ) (hn : 0 < n) :
    Carrier D →ₗ[ℂ] VertexOperator ℂ (M ⧸ powerNilpotenceSubmodule (current J i n)) where
  toFun := quotientField J hD i n hn
  map_add' a b := by
    apply HVertexOperator.coeff_inj
    funext k
    rw [VertexOperator.coeff_eq_ncoeff]
    simp only [map_add, Pi.add_apply, VertexOperator.coeff_eq_ncoeff,
      quotientField_modes]
    apply LinearMap.ext
    intro w
    refine Submodule.Quotient.induction_on _ w ?_
    intro v
    simp [quotientMode_mk, mode]
  map_smul' c a := by
    apply HVertexOperator.coeff_inj
    funext k
    rw [VertexOperator.coeff_eq_ncoeff]
    simp only [map_smul, Pi.smul_apply, VertexOperator.coeff_eq_ncoeff,
      quotientField_modes, RingHom.id_apply]
    apply LinearMap.ext
    intro w
    refine Submodule.Quotient.induction_on _ w ?_
    intro v
    simp [quotientMode_mk, mode]

@[simp] theorem quotientStateField_modes (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Fin D.rank) (n : ℤ) (hn : 0 < n) (a : Carrier D) (s : ℤ) :
    ((quotientStateField J hD i n hn a)[[s]]) = quotientMode J hD i n hn a s :=
  quotientField_modes J hD i n hn a s

/-- All original record fields are inherited literally; the record itself is unchanged. -/
def quotientModule (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Fin D.rank) (n : ℤ) (hn : 0 < n) :
    FullJacobiLatticeModule D (M ⧸ powerNilpotenceSubmodule (current J i n)) where
  stateField := quotientStateField J hD i n hn
  vacuum_field := by
    apply HVertexOperator.coeff_inj
    funext k
    rw [VertexOperator.coeff_eq_ncoeff, quotientStateField_modes]
    apply LinearMap.ext
    intro w
    refine Submodule.Quotient.induction_on _ w ?_
    intro v
    rw [quotientMode_mk]
    have h : mode J (vacuum D) (-k - 1) =
        if k = 0 then LinearMap.id else 0 := by
      simpa only [show -k - 1 = -1 ↔ k = 0 by omega] using vacuum_modes J (-k - 1)
    rw [h]
    by_cases hk : k = 0
    · subst k
      simp [identityField, VertexOperator.coeff_eq_ncoeff,
        VertexOperator.ncoeff_of_coeff]
    · simp [hk, identityField, VertexOperator.coeff_eq_ncoeff,
        VertexOperator.ncoeff_of_coeff]
  borcherds := by
    intro a b w p t r
    refine Submodule.Quotient.induction_on _ w ?_
    intro v
    let N := powerNilpotenceSubmodule (current J i n)
    let F := quotientStateField J hD i n hn
    obtain ⟨hL, hF, hS, h⟩ := J.borcherds a b v p t r
    have eL : jacobiLeft F a b (N.mkQ v) p t r =
        fun j => N.mkQ (jacobiLeft J.stateField a b v p t r j) := by
      funext j
      simp only [jacobiLeft, F, quotientStateField_modes, Submodule.mkQ_apply,
        quotientMode_mk, Submodule.Quotient.mk_smul]
    have eF : jacobiFirst F a b (N.mkQ v) p t r =
        fun j => N.mkQ (jacobiFirst J.stateField a b v p t r j) := by
      funext j
      simp only [jacobiFirst, F, quotientStateField_modes, Submodule.mkQ_apply,
        quotientMode_mk, Submodule.Quotient.mk_smul]
    have eS : jacobiSecond F a b (N.mkQ v) p t r =
        fun j => N.mkQ (jacobiSecond J.stateField a b v p t r j) := by
      funext j
      simp only [jacobiSecond, F, quotientStateField_modes, Submodule.mkQ_apply,
        quotientMode_mk, Submodule.Quotient.mk_smul]
    have lsubset : Function.support (jacobiLeft F a b (N.mkQ v) p t r) ⊆
        Function.support (jacobiLeft J.stateField a b v p t r) := by
      rw [eL]
      intro j hj hz
      exact hj (by simp only [hz, map_zero])
    have fsubset : Function.support (jacobiFirst F a b (N.mkQ v) p t r) ⊆
        Function.support (jacobiFirst J.stateField a b v p t r) := by
      rw [eF]
      intro j hj hz
      exact hj (by simp only [hz, map_zero])
    have ssubset : Function.support (jacobiSecond F a b (N.mkQ v) p t r) ⊆
        Function.support (jacobiSecond J.stateField a b v p t r) := by
      rw [eS]
      intro j hj hz
      exact hj (by simp only [hz, map_zero])
    have lfinite : Function.HasFiniteSupport (jacobiLeft F a b (N.mkQ v) p t r) :=
      hL.subset lsubset
    have ffinite : Function.HasFiniteSupport (jacobiFirst F a b (N.mkQ v) p t r) :=
      hF.subset fsubset
    have sfinite : Function.HasFiniteSupport (jacobiSecond F a b (N.mkQ v) p t r) :=
      hS.subset ssubset
    refine ⟨lfinite, ffinite, sfinite, ?_⟩
    simp_rw [smul_sub] at h ⊢
    change (∑ᶠ j : ℕ, jacobiLeft J.stateField a b v p t r j) =
      ∑ᶠ j : ℕ, (jacobiFirst J.stateField a b v p t r j -
        jacobiSecond J.stateField a b v p t r j) at h
    change (∑ᶠ j : ℕ, jacobiLeft F a b (N.mkQ v) p t r j) =
      ∑ᶠ j : ℕ, (jacobiFirst F a b (N.mkQ v) p t r j -
        jacobiSecond F a b (N.mkQ v) p t r j)
    rw [finsum_sub_distrib hF hS] at h
    rw [finsum_sub_distrib ffinite sfinite, eL, eF, eS]
    rw [← map_finsum N.mkQ hL, ← map_finsum N.mkQ hF,
      ← map_finsum N.mkQ hS, ← map_sub, h]

/-- Quotient currents are precisely the induced ORIGINAL current modes. -/
@[simp] theorem quotient_current_mk (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i h : Fin D.rank) (n s : ℤ) (hn : 0 < n) (v : M) :
    current (quotientModule J hD i n hn) h s (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (current J h s v) := by
  change ((quotientStateField J hD i n hn (currentState D h))[[s]]) _ = _
  rw [quotientStateField_modes, quotientMode_mk]

/-- Injectivity uses exactly Dv in N_D implies v in N_D, with exponent K+1. -/
theorem quotient_current_injective (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Fin D.rank) (n : ℤ) (hn : 0 < n) :
    Function.Injective (current (quotientModule J hD i n hn) i n) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro w hw
  change current (quotientModule J hD i n hn) i n w = 0 at hw
  change w = 0
  revert hw
  refine Submodule.Quotient.induction_on _ w ?_
  intro v hv
  rw [quotient_current_mk, Submodule.Quotient.mk_eq_zero] at hv
  rw [Submodule.Quotient.mk_eq_zero]
  exact current_preimage_locus J i n v hv

/-- The actual quotient is zero: a nonzero class would supply a nonzero current vacuum. -/
theorem current_locus_eq_top (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (i : Fin D.rank) (n : ℤ) (hn : 0 < n) :
    powerNilpotenceSubmodule (current J i n) = ⊤ := by
  classical
  let Q := M ⧸ powerNilpotenceSubmodule (current J i n)
  let JQ := quotientModule J hD i n hn
  have hzero : ∀ w : Q, w = 0 := by
    intro w
    by_contra hw
    obtain ⟨u, hu, hvac⟩ := exists_positive_current_vacuum JQ hD w hw
    have hk : current JQ i n u = 0 := hvac i n hn
    have hinj := quotient_current_injective J hD i n hn
    exact hu (hinj (by simpa only [map_zero] using hk))
  apply top_unique
  intro v hv
  exact (Submodule.Quotient.mk_eq_zero _).mp (hzero (Submodule.Quotient.mk v))

/-- Original positive-current local nilpotence, arbitrary M and rank zero included. -/
theorem positive_current_locally_nilpotent (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    ∀ (i : Fin D.rank) (n : ℤ), 0 < n → ∀ v : M,
      ∃ K : ℕ, 0 < K ∧ (current J i n ^ K) v = 0 := by
  intro i n hn v
  have hv : v ∈ powerNilpotenceSubmodule (current J i n) := by
    rw [current_locus_eq_top J hD i n hn]
    trivial
  exact (mem_powerNilpotenceSubmodule (current J i n) v).mp hv

end
end D5.S3.VertexAlgebra.Modules.FullJacobiPositiveCurrentNilpotence
