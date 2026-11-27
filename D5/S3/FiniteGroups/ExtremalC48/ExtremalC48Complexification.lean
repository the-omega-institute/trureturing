import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Algebra.Star.Pi
import D5.S3.FiniteGroups.CharacterDegreeDivisibility

/-! The complex constituent degrees of a real irreducible representation.
In the P48q branch of the central-charge 48 extremal VOA problem, the rank-48
case supplies a degree divisible by six for the character-degree obstruction. -/

namespace ExtremalC48

open Module
open scoped Matrix

variable {G V ι : Type*} [Monoid G] [AddCommGroup V] [Module ℝ V]
  [Fintype ι] [DecidableEq ι]

/-- Extend the real action matrices in the basis `b` entrywise to complex matrices. -/
noncomputable def complexification (b : Basis ι ℝ V) (ρ : Representation ℝ G V) :
    Representation ℂ G (ι → ℂ) :=
  Matrix.toLinAlgEquiv'.toRingEquiv.toMonoidHom.comp
    ((Complex.ofRealHom.mapMatrix.toMonoidHom).comp
      ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp ρ))

private noncomputable def realCoordinates (b : Basis ι ℝ V) :
    V →ₗ[ℝ] (ι → ℂ) :=
  (LinearMap.pi fun i : ι => Complex.ofRealAm.toLinearMap.comp (LinearMap.proj i)).comp
    b.equivFun.toLinearMap

omit [DecidableEq ι] in
private theorem realCoordinates_apply (b : Basis ι ℝ V) (x : V) (i : ι) :
    realCoordinates b x i = (b.equivFun x i : ℂ) := rfl

private theorem complexification_realCoordinates (b : Basis ι ℝ V)
    (ρ : Representation ℝ G V) (g : G) (x : V) :
    complexification b ρ g (realCoordinates b x) = realCoordinates b (ρ g x) := by
  let M := LinearMap.toMatrixAlgEquiv b (ρ g)
  have h : M *ᵥ b.equivFun x = b.equivFun (ρ g x) := by
    apply b.equivFun.symm.injective
    rw [LinearEquiv.symm_apply_apply]
    change Matrix.toLinAlgEquiv b M x = ρ g x
    exact LinearMap.congr_fun (Matrix.toLinAlgEquiv_toMatrixAlgEquiv b (ρ g)) x
  funext i
  change (Matrix.toLinAlgEquiv' (M.map Complex.ofRealHom) (realCoordinates b x)) i =
    realCoordinates b (ρ g x) i
  rw [Matrix.toLinAlgEquiv'_apply, realCoordinates_apply, ← h]
  exact (Complex.ofRealHom.map_mulVec M (b.equivFun x) i).symm

private theorem complexification_star (b : Basis ι ℝ V) (ρ : Representation ℝ G V)
    (g : G) (z : ι → ℂ) :
    star (complexification b ρ g z) = complexification b ρ g (star z) := by
  let M := (LinearMap.toMatrixAlgEquiv b (ρ g)).map Complex.ofRealHom
  funext i
  change star (Matrix.toLinAlgEquiv' M z i) = Matrix.toLinAlgEquiv' M (star z) i
  rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLinAlgEquiv'_apply]
  classical
  simp [Matrix.mulVec, dotProduct, M, star_mul']

private def conjugate {σ : Representation ℂ G (ι → ℂ)}
    (hσ : ∀ g z, star (σ g z) = σ g (star z)) (W : Subrepresentation σ) :
    Subrepresentation σ where
  toSubmodule := W.toSubmodule.comap (starLinearEquiv ℂ).toLinearMap
  apply_mem_toSubmodule g := by
    intro z hz
    change star z ∈ W at hz
    change star (σ g z) ∈ W
    rw [hσ]
    exact W.apply_mem_toSubmodule g hz

omit [Fintype ι] [DecidableEq ι] in
private theorem finrank_conjugate {σ : Representation ℂ G (ι → ℂ)}
    (hσ : ∀ g z, star (σ g z) = σ g (star z)) (W : Subrepresentation σ) :
    finrank ℂ (conjugate hσ W).toSubmodule = finrank ℂ W.toSubmodule := by
  let e : (conjugate hσ W).toSubmodule ≃ₗ⋆[ℂ] W.toSubmodule :=
    (starLinearEquiv ℂ).ofSubmodule' W.toSubmodule
  exact congrArg Cardinal.toNat
    (rank_eq_of_equiv_equiv star e.toAddEquiv star_involutive.bijective
      (fun r z => e.map_smulₛₗ r z))

omit [Fintype ι] [DecidableEq ι] in
private theorem real_imag_mem {S : Submodule ℂ (ι → ℂ)}
    (hstar : ∀ z ∈ S, star z ∈ S) {z : ι → ℂ} (hz : z ∈ S) :
    (fun i => ((z i).re : ℂ)) ∈ S ∧ (fun i => ((z i).im : ℂ)) ∈ S := by
  have hRe : (fun i => ((z i).re : ℂ)) = (2 : ℂ)⁻¹ • (z + star z) := by
    funext i
    simpa only [div_eq_mul_inv, mul_comm, Pi.smul_apply, Pi.add_apply, Pi.star_apply,
      smul_eq_mul, Complex.star_def] using Complex.re_eq_add_conj (z i)
  have hIm : (fun i => ((z i).im : ℂ)) = (2 * Complex.I)⁻¹ • (z - star z) := by
    funext i
    simpa only [div_eq_mul_inv, mul_comm, Pi.smul_apply, Pi.sub_apply, Pi.star_apply,
      smul_eq_mul, Complex.star_def] using Complex.im_eq_sub_conj (z i)
  exact ⟨hRe ▸ S.smul_mem _ (S.add_mem hz (hstar z hz)),
    hIm ▸ S.smul_mem _ (S.sub_mem hz (hstar z hz))⟩

private theorem eq_top_of_conjugation_stable (b : Basis ι ℝ V) (ρ : Representation ℝ G V)
    [ρ.IsIrreducible] (S : Subrepresentation (complexification b ρ)) (hS : S ≠ ⊥)
    (hstar : ∀ z ∈ S, star z ∈ S) : S = ⊤ := by
  let R : Subrepresentation ρ :=
    { toSubmodule := (S.toSubmodule.restrictScalars ℝ).comap (realCoordinates b)
      apply_mem_toSubmodule := by
        intro g x hx
        change realCoordinates b (ρ g x) ∈ S
        rw [← complexification_realCoordinates b ρ g x]
        exact S.apply_mem_toSubmodule g hx }
  have hparts {z : ι → ℂ} (hz : z ∈ S) :=
    real_imag_mem (S := S.toSubmodule) hstar hz
  have hcoords (v : ι → ℝ) :
      realCoordinates b (b.equivFun.symm v) = fun i => (v i : ℂ) := by
    funext i
    rw [realCoordinates_apply, LinearEquiv.apply_symm_apply]
  have hsplit (z : ι → ℂ) :
      (fun i => ((z i).re : ℂ)) + Complex.I • (fun i => ((z i).im : ℂ)) = z := by
    funext i
    change ((z i).re : ℂ) + Complex.I * ((z i).im : ℂ) = z i
    rw [mul_comm, Complex.re_add_im]
  have hR : R = ⊤ := by
    apply (IsSimpleOrder.eq_bot_or_eq_top R).resolve_left
    intro hbot
    obtain ⟨z, hz, hz₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (show S.toSubmodule ≠ ⊥ from fun h => hS (Subrepresentation.toSubmodule_injective h))
    apply hz₀
    have zeroPart (v : ι → ℝ) (hv : (fun i => (v i : ℂ)) ∈ S) :
        (fun i => (v i : ℂ)) = 0 := by
      rw [← hcoords v]
      have hm : b.equivFun.symm v ∈ R := by
        change realCoordinates b (b.equivFun.symm v) ∈ S
        rwa [hcoords]
      rw [hbot] at hm
      change b.equivFun.symm v ∈ (⊥ : Submodule ℝ V) at hm
      have hzv : b.equivFun.symm v = 0 := (Submodule.mem_bot ℝ).mp hm
      rw [hzv, map_zero]
    rw [← hsplit z, zeroPart _ (hparts hz).1, zeroPart _ (hparts hz).2,
      smul_zero, add_zero]
  apply top_unique
  intro z _
  have memPart (v : ι → ℝ) : (fun i => (v i : ℂ)) ∈ S := by
    rw [← hcoords v]
    have hv : b.equivFun.symm v ∈ (⊤ : Subrepresentation ρ) := trivial
    have hv : b.equivFun.symm v ∈ R := hR.symm ▸ hv
    exact hv
  rw [← hsplit z]
  exact S.toSubmodule.add_mem (memPart _) (S.toSubmodule.smul_mem _ (memPart _))

/-- A real irreducible representation extended to complex coordinates has an irreducible
subrepresentation of full dimension or half dimension. -/
theorem exists_irreducible_complexification (b : Basis ι ℝ V) (ρ : Representation ℝ G V)
    [ρ.IsIrreducible] :
    ∃ W : Subrepresentation (complexification b ρ), W.toRepresentation.IsIrreducible ∧
      (finrank ℂ W.toSubmodule = finrank ℝ V ∨
       2 * finrank ℂ W.toSubmodule = finrank ℝ V) := by
  classical
  let σ := complexification b ρ
  have : Nontrivial V :=
    D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IsIrreducible.nontrivial
      (ρ := ρ) inferInstance
  have : Nonempty ι := b.index_nonempty
  obtain ⟨W, hW⟩ :=
    D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation.exists_isAtom σ
  let W' := conjugate (complexification_star b ρ) W
  have hW' (z : ι → ℂ) : z ∈ W' ↔ star z ∈ W := Iff.rfl
  have htop : W ⊔ W' = ⊤ := by
    apply eq_top_of_conjugation_stable b ρ _ (fun h => hW.1 (sup_eq_bot_iff.mp h).1)
    intro z hz
    change z ∈ W.toSubmodule ⊔ W'.toSubmodule at hz
    change star z ∈ W.toSubmodule ⊔ W'.toSubmodule
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
    rw [star_add]
    have hu' : star u ∈ W' := (hW' (star u)).2 (by
      rw [star_star]
      exact hu)
    exact Submodule.mem_sup.mpr ⟨star v, (hW' v).1 hv, star u, hu', add_comm _ _⟩
  have hdim : finrank ℂ (ι → ℂ) = finrank ℝ V := by
    rw [Module.finrank_eq_card_basis (Pi.basisFun ℂ ι), Module.finrank_eq_card_basis b]
  have hirred : W.toRepresentation.IsIrreducible :=
    open D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation in
    isIrreducible_toRepresentation_of_isAtom hW
  refine ⟨W, hirred, ?_⟩
  rcases hW.le_iff.mp (inf_le_left : W ⊓ W' ≤ W) with hi | hi
  · right
    have hr := Submodule.finrank_sup_add_finrank_inf_eq W.toSubmodule W'.toSubmodule
    change finrank ℂ (W ⊔ W').toSubmodule + finrank ℂ (W ⊓ W').toSubmodule =
      finrank ℂ W.toSubmodule + finrank ℂ W'.toSubmodule at hr
    rw [htop, hi] at hr
    change finrank ℂ (⊤ : Submodule ℂ (ι → ℂ)) + finrank ℂ (⊥ : Submodule ℂ (ι → ℂ)) =
      finrank ℂ W.toSubmodule + finrank ℂ W'.toSubmodule at hr
    rw [finrank_top, finrank_bot, add_zero, hdim,
      show finrank ℂ W'.toSubmodule = finrank ℂ W.toSubmodule from
        finrank_conjugate (complexification_star b ρ) W] at hr
    omega
  · left
    have hle : W ≤ W' := hi ▸ inf_le_right
    have heq : W = W' := le_antisymm hle fun z hz => by
      have hh : star z ∈ W' := hle ((hW' z).1 hz)
      simpa using (hW' (star z)).1 hh
    rw [← heq, sup_idem] at htop
    rw [htop]
    exact (finrank_top ℂ (ι → ℂ)).trans hdim

/-- The rank-48 case used in the P48q obstruction. -/
theorem exists_irreducible_complexification_rank48 (ρ : Representation ℝ G V)
    [FiniteDimensional ℝ V] [ρ.IsIrreducible] (h48 : finrank ℝ V = 48) :
    ∃ W : Subrepresentation (complexification (Module.finBasisOfFinrankEq ℝ V h48) ρ),
      W.toRepresentation.IsIrreducible ∧
        (finrank ℂ W.toSubmodule = 24 ∨ finrank ℂ W.toSubmodule = 48) := by
  obtain ⟨W, hW, hd | hd⟩ :=
    exists_irreducible_complexification (Module.finBasisOfFinrankEq ℝ V h48) ρ
  · exact ⟨W, hW, Or.inr (hd.trans h48)⟩
  · exact ⟨W, hW, Or.inl (by omega)⟩

/-- The real degree divides twice the group order. -/
theorem real_finrank_dvd_two_mul_card {H : Type*} [Group H] [Finite H]
    (ρ : Representation ℝ H V) [FiniteDimensional ℝ V] [ρ.IsIrreducible] :
    finrank ℝ V ∣ 2 * Nat.card H := by
  obtain ⟨W, hW, hd⟩ := exists_irreducible_complexification (Module.finBasis ℝ V) ρ
  let _ : W.toRepresentation.IsIrreducible := hW
  have h := D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_dvd_card
    W.toRepresentation
  rcases hd with hd | hd
  · rw [← hd]
    exact h.trans (dvd_mul_left _ _)
  · rw [← hd]
    exact Nat.mul_dvd_mul_left 2 h

end ExtremalC48

#print axioms ExtremalC48.complexification
#print axioms ExtremalC48.exists_irreducible_complexification
#print axioms ExtremalC48.exists_irreducible_complexification_rank48
#print axioms ExtremalC48.real_finrank_dvd_two_mul_card
