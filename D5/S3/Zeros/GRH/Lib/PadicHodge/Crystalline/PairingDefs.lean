/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/PairingDefs
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/PairingDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.Crystalline.PairingDefs. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/Crystalline/PairingDefs.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.WachGamma.KisinModuleDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Potentially crystalline representations, Hodge–Tate weights, Weil–Deligne Frobenius
(known result; see Lib.PadicHodge.Crystalline.RegularityFrobenius). -/

noncomputable section

namespace Lift

variable {p} [ThePrime p] (O Γ : Type) [CommRing O] [Algebra ℤ_[p] O] [Group Γ]
open Module Submodule GalLattice TensorProduct Polynomial AdjoinRoot IsWeilPair
variable {O Γ} [OverGp Γ p] (F) (K : Γ → _ → Prop) (U : _ → Finset ℤ) (Y L : GalLattice O Γ)
variable {Y L} (P : Pairing Y L)
attribute [-simp] nsmul_eq_mul
attribute [local simp] Pairing.CupBounds Units.smul_def
variable [Module.Finite ℤ_[p] O] {F K U K' U'} (h : InClass F K U Y) (h' :
  InClass F K' U' L)

lemma InClass.of_cyclotomic_pow c (h : ∀ g x, L.ρ g x = χ g ^ c • x := by simp) :
  InClass F ⊥ (fun _ ↦ {-c}) L := ⟨isAdmissible_of_cyclotomicGp_zpow c
  h, by simp [hasJumps_of_cyclotomicGp_zpow c h _, Multiset.mem_replicate]⟩

/-- Let j(Γ) be open and L potentially crystalline. At each embedding γ, the multiplicity of the
jump u of the twisted dual L^∨(1) equals that of the jump −u − 1 of L. -/
lemma jump_tateDual (h : IsPotCrys L.ρ) γ u : jump L.tateDual.ρ γ u = jump L.ρ γ (-u - 1) :=
  jump_eq_of_pairing h 1 1 (by simp)

variable [IsDomain O]

/-- Let j have open image and F be coarser than the filter 'near 1'. A lattice Y with jointly
injective equivariant O-linear maps to finitely many lattices of the class `Lift.InClass` (F,
K, U) belongs to that class. -/
lemma InClass.of_jointly_injective {ι} [Fintype ι] {M : ι → _} (h : ∀ a, InClass F K U (M a)) (f :
  ∀ _, Y →ₗ[O] _)
  (hf : ∀ a g x, f a (Y.ρ g x) = (M a).ρ g (f a x)) (hi : ∀ x, (∀ a, f a x = 0) → x = 0) :
  InClass F K U Y := ⟨.of_jointly_injective (by simp) (h · |>.1) (f ·) (by simp [*]) hi, by grind
  [InClass, isPotCrys, exists_jump_of_jointly_injective _ f hf hi, IsKilledBy.of_jointly_injective _
  (f · |>.restrictScalars _) (.of_forall <| hf ·) hi le_rfl _ map_id (by simp)]⟩

include h h'

omit h' [IsDomain O] in
lemma InClass.dual : InClass F (K ·⁻¹) (U · |>.image (-· - 1)) Y.tateDual :=
  (h.1.of_pairing (by simp) 1 1 (by simp)).imp_right (by grind [InClass, jump_tateDual, isPotCrys,
  inv, inv_inv])

/-- Let j(Γ) be open, and let every set of F contain all g with j(g) near 1. If Y, L are
admissible along F with jumps in U, U' at each embedding (`Lift.InClass`), so is Y ⊗ L with
jumps in U + U', without killing condition. -/
lemma InClass.tensor : InClass F ⊥ (fun g ↦ .image₂ (· + ·) (U g) (U' g)) (Y.tensor L) :=
  ⟨.of_bilinear _ (by tauto) h.1 h'.1 (mapOfCompatibleSMul_surjective O _ _ _ _), fun g _ ↦ by
  obtain ⟨⟨P, k, H, J, -⟩, ⟨Q, l, G, I, -⟩⟩ := h.isPotCrys.exists_isHodgeTateFrame (finBasis ..) g,
    h'.isPotCrys.exists_isHodgeTateFrame (finBasis ..) g, h.2.1 g, h'.2.1 g
  rw [(hasJumps_of_rows (.tensorProduct ..) (kroneckerGL P⁻¹ Q⁻¹) (k · + l ·).uncurry (H.mp (G.mono
    fun g f e ⟨_, _⟩ ⟨_, _⟩ ↦ by
    simpa [Matrix.mul_apply, zpow_add, mul_smul, Finset.sum_mul_sum,
      Fintype.sum_prod_type, LinearMap.toMatrix_apply, mul_comm (_ : O), kroneckerGL,
      mul_mul_mul_comm] using congr($(inv_mul_apply_of_isHodgeTateFrame
      e ..) * $(inv_mul_apply_of_isHodgeTateFrame f ..))))).1]
  simp_all [J _, I _, -Fin.univ_val_map]; grind, nofun⟩

/-- Let j(s) lie in inertia, Y and L be potentially crystalline, and monic q, r in Z_p[X] kill (s,0)
on Y and L. Then a monic e in Z_p[X] of degree ≤ deg q · deg r kills (s⁻¹,0) on Hom(Y ⊗ L, O(1)). -/
lemma exists_isKilledBy_tateDual_tensor {s q r} (hs : IsWeilPair (toGp s) 0) (m : Monic q) (m' :
  Monic r) (k : K s (q.map (algebraMap ℤ_[p] _))) (k' : K' s (r.map (algebraMap ℤ_[p] _))) : ∃ e,
  Monic e ∧ e.natDegree ≤ q.natDegree * r.natDegree ∧
  IsKilledBy (tateDual (Y.tensor L)).ρ s⁻¹ 0 (e.map (algebraMap ℤ_[p] _)) := by
  obtain ⟨⟨u⟩, ⟨v⟩, ⟨a, b, -⟩, t, f⟩ := h.2.2 _ _ k hs, h'.2.2 _ _ k' hs, h.tensor h',
    (h.tensor h').isPotCrys, algEquivMatrix ((powerBasisAux' m).tensorProduct (powerBasisAux' m'))
  let B := (mk O Y L).restrictScalars₁₂ ℤ_[p] ℤ_[p]
  let A := f (.mulLeft _ (root q ⊗ₜ root r))
  refine ⟨_, A.charpoly_monic, by simp, (InClass.dual ⟨a, b, fun _ _ a _ ↦
    a⟩).2.2 _ _ ⟨t, ?_⟩ hs.inv⟩
  let c {Y : GalLattice O Γ} {q} m a := (aeval (linearFrob Y.ρ s 0)).toLinearMap.flip (1 ⊗ₜ a) ∘ₗ
    @modByMonicHom ℤ_[p] _ q m
  obtain _ := fun n ↦ linearFrob_baseChangePairing v (hs.pow n) u B (by tauto) t,
    fun a b ↦ congr(lift ((baseChangePairing
    B).restrictScalars₁₂ ..) (map (c m a) (c m' b) (f.symm $A.aeval_self_charpoly 1)))
  ext z; exact z.inductionOn (by simp_all [coefEnd, A, B, c, baseChangePairing,
    aeval_eq_sum_range, ↓aeval_modByMonic_eq_self_of_root, eval₂_map, ← mk_X, ← aeval_def,
    ← map_pow, DFunLike.ext_iff, ← linearFrob_pow]) (by grind [tmul_add])
