/- GID: D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/LocalCharacters
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/LocalCharacters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.HeckeCharacter.LocalCharacters. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/HeckeCharacter/LocalCharacters.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.HeckeCharacter.CharOfDet
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Algebraic Hecke characters (type A₀); extension of the quadratic character of a CM
field (known result; see Lib.ClassField.HeckeCharacter.SplittingCharExists).

This file: Global characters of the determinant read through local components at chosen places. -/


open Matrix Fintype WeilData Gf Finset
variable {E} [Field E] [CMType E] {n} [Fintype n] {s} {P : Finset _} {μ}
  (𝔠 : SplitTameChar E μ) {k : Gf E n}

@[simp] lemma upsilonU1_det_of_mem_Kf [WeilData E] : k ∈ Kf .. → upsilonU1.1 (detFin s k) = 1 :=
  upsilonU1_hasWeight.apply_det_eq_one

lemma spaceChar_rankTwist [WeilData E]
    {ν : AutChar E} : 2 ∣ card n → (rankTwist ν n).spaceChar (card n) =
  ν.baseChange := by simp_all [dvd_def, AutChar.spaceChar, rankTwist, pow_mul]

lemma atPlaces_of_mem_trivialOn : k ∈ Gf.trivialOn n P → atPlaces P k = 1 := by
  simp [GeneralLinearGroup.ext_iff, atPlace, atPlaces]; aesop

/-- For finite adelic unitary g, `localChar` P ξ k at the determinant of the P-components
of g equals ξ(d)|d|^{k/2}, d the idele that is det g at P and 1 elsewhere. -/
@[simp] lemma localChar_det ξ k (g : Gf E n) :
    localChar P ξ k (atPlaces P g).1.det = ξ.1 (detOn P g.1) * √(ideleAbs (detOn P g.1)) ^ k := by
  erw [detOn_eq_prod, ← prod_attach, MulChar.ofUnitHom_coe _ (atPlaces P g).det,
    ← Circle.coeHom_apply]
  simp [g.1.map_det, atPlaces, atPlace, Real.sqrt_prod, ideleAbs_locFullIdele, prod_zpow]
  tauto

lemma SplitTameChar.exists_atPlaces_eq g : ∃ k ∈ supportedOn n 𝔠.S, atPlaces 𝔠.S k = g :=
  ⟨_, atSplits_mem_supportedOn 𝔠.star_notMem
  (g.map <| Pi.evalRingHom _ ·), by ext : 3; apply congr($(atPlace_atSplits ..) _ _)⟩

lemma SplitTameChar.nu_det_of_mem_Kf (h : k ∈ Kf ..) : 𝔠.ν.1 (detFin s k) =
  𝔠.χ (atPlaces _ k).1.det := by
  simp [nu_apply_of_integral, IsIntMatrix.det_mem (mem_Kf.1 h), RingHom.map_det, atPlaces]
