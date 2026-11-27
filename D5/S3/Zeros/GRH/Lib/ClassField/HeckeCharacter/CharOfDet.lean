/- GID: D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/CharOfDet
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/CharOfDet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.HeckeCharacter.CharOfDet. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/HeckeCharacter/CharOfDet.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.PairReal
import D5.S3.Zeros.GRH.Lib.ClassField.HeckeCharacter.LineParabolic
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Algebraic Hecke characters (type A₀); extension of the quadratic character of a CM
field (known result; see Lib.ClassField.HeckeCharacter.SplittingCharExists).

This file: Tame Hecke character on determinants of integral adelic points is product of residue
characters. -/

namespace AutChar.HasWeight

open Matrix Prod IsIntMatrix
variable {E n} [Field E] [CMType E] [Fintype n] {μ : AutChar E} {e ψ} {s : n → _}

/-- Let μ have weight e and tame part ψ, trivial outside finitely many distinct places w_i. For
k in the stabiliser K₀ of the standard lattice, μ(det k) = ∏_i ψ_{w_i}(det(k mod w_i)). -/
lemma apply_det_eq_prod (h : μ.HasWeight e ψ) {ι} [Fintype ι] {w : ι → _} (hw : w.Injective) (hψ :
  ∀ u ∉ Set.range w, ψ u = 1) k : μ.1 (detFin s k.1) = ∏ i, ψ (w i) (Kf.reduceAt _ k).1.det := by
  simp +contextual [h.2,
    det_mem (mem_Kf.1 k.2), ↓finprod_tame_eq_prod_reduceU1 (S := .map ⟨w, hw⟩ ⊤), *, reduceU1]
  congr!; convert! RingHom.map_det ..
  simp [det_apply', snd_sum, snd_prod]; rfl

lemma apply_det_eq_one (h : μ.HasWeight e 1) {k} (hk : k ∈ Kf ..) : μ.1 (detFin s k) = 1 := by
  ext; simp [h.2, det_mem (mem_Kf.1 hk), ↓finprod_tame_eq_prod_reduceU1 (S := ∅)]
