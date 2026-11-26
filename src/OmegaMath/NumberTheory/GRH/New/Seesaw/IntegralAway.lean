import OmegaMath.NumberTheory.GRH.New.Seesaw.LatticeAndTorsionDefs
import OmegaMath.NumberTheory.GRH.Lib.Adelic.CuspForms.ClassReps
import OmegaMath.NumberTheory.GRH.Lib.ClassField.HeckeCharacter.SplittingCharOnU1
import OmegaMath.NumberTheory.GRH.Lib.Weil.DualPair.PairSplitting
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

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
