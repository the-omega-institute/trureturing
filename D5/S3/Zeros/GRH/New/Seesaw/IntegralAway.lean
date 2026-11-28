/- GID: D5/S3/Zeros/GRH/New/Seesaw/IntegralAway
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/IntegralAway
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.IntegralAway. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/IntegralAway.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Seesaw.LatticeAndTorsionDefs
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.ClassReps
import D5.S3.Zeros.GRH.Lib.ClassField.HeckeCharacter.SplittingCharOnU1
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.PairSplitting
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: size bookkeeping for the data of this proof.

Part of: Algebraic Hecke characters (type A₀); extension of the quadratic character of a CM field
(known result; see Lib.ClassField.HeckeCharacter.SplittingCharExists).

Part of: Congruence subgroups and level structures of adelic groups (known result; see
Lib.Adelic.Unitary.CongruenceLevel).

This file: Integrality away from q of quotients; at elements integral above l, the Weil factor and
characters of the determinant are l-adic units. -/


variable {E} [Field E] [CMType E] {q l c d k : ℕ} {n} [Fintype n] [Fact l.Prime] {ι : ℂ →+* ℂ_[l]}
  {g : Gf E n}

lemma div_mem_integralAway (h : c ∣ d * q ^ k) : (d / c : ℂ) ∈ integralAway q := fun l _ c ↦ by
  simp [by simpa [c.norm_natCast_eq_one] using congr(‖($h.choose_spec : ℂ_[l])‖)]; bound
    [natCast_mem (valRingCp l)]

omit [Fact l.Prime] in
lemma localLevel_le_integralAbove_of_coprime (hl : l.Coprime q) : localLevel n {w : FinPlace E
  | ↑q ∉ w.1} ≤ integralAbove n l := fun _ h w ↦ h w ∘ w.2.notMem_of_isCoprime_of_mem hl.cast

lemma Parameters.norm_finMultiplier_eq_one [WeilData E] (hg : g ∈ integralAbove n l) : ‖ι
  (finMultiplier g)‖ = 1 := by simp_all (maxDischargeDepth := 4) [finMultiplier, glMultiplier,
  WeilData.norm_map_chiFin, localLevel, Gf.atPlace, (norm_adeleExtension_eq_iff _ 1).2,
  Sat.v_det_saturatingElem rfl ∘ .of_mem, mem_subring_matrix_iff, mem_intGL]

lemma AutChar.HasWeight.norm_padic_det {a : AutChar E} {e ψ s} [ha : a.HasWeight e ψ] (hg :
  g ∈ integralAbove n l) : ‖ι (a.1 (detFin s g))‖ = 1 := by simp [ha.norm_padic_eq_prod,
  funext_iff, ↓(norm_adeleExtension_eq_iff _ 1).2, mem_intGL_iff_det.1 (hg ..)]
