/- GID: D5/S3/Observer/Linear/GainRayShortWord
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayShortWord
   mirror-E: none(waiver:rank-deficient-literal-word-obstruction)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank]
   utility: none
   digest: A universally collinear readout successful anywhere needs strictly more reads than whole gain coordinates. -/

import D5.S3.Observer.Linear.GainRayScalarIdentity

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace D5.S3.Observer.Linear.GainRay

/-- Drift consumes a nonzero kernel direction in addition to the d+1 output directions. -/
theorem scalar_identity_read_bound (d : ℕ) (w : List Bool) (C : Readout d w)
    (hb : C.mulVec (fun _ => 1) = 0) (S : Mat) (s : ℝ) (hs : s ≠ 0)
    (he : response d w C S = s • (1 : Matrix _ _ ℝ)) : d+2 ≤ w.length+1 := by
  have hsurj : Function.Surjective C.mulVec := by
    intro y
    refine ⟨(responseMatrix d w S).mulVec (s⁻¹ • y), ?_⟩
    rw [Matrix.mulVec_mulVec]
    change (response d w C S).mulVec (s⁻¹ • y) = y
    rw [he, Matrix.smul_mulVec, Matrix.one_mulVec, smul_inv_smul₀ hs]
  have hr : Module.finrank ℝ (LinearMap.range C.mulVecLin) = d+1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_pi]
    simp
  have hk : 1 ≤ Module.finrank ℝ (LinearMap.ker C.mulVecLin) := by
    apply Submodule.one_le_finrank_iff.mpr
    intro hz
    have hm : (fun _ : Fin (w.length+1) => (1 : ℝ)) ∈ LinearMap.ker C.mulVecLin := hb
    rw [hz, Submodule.mem_bot] at hm
    have := congrFun hm (⟨0, by omega⟩ : Fin (w.length+1))
    norm_num at this
  have hd := C.mulVecLin.finrank_range_add_finrank_ker
  rw [hr, Module.finrank_pi] at hd
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hd
  omega

/-- This covers every rank-deficient short word, including empty and pure words. -/
theorem short_word_no_universal_success (d : ℕ) (hd : 1 ≤ d) (w : List Bool)
    (hw : w.length+1 ≤ d+1) (C : Readout d w)
    (hu : ∀ W : World d, Collinear W.coeff (C.mulVec (readings W w))) :
    ∀ W : World d, ¬ Succeeds W w C := by
  intro W hW
  obtain ⟨hb, he⟩ := universal_scalar_identity d hd w C hu
  have hn := successful_scalar_nonzero w C hb he W hW
  have hr := scalar_identity_read_bound d w C hb W.source
    (scalarFunctional d w C W.source) hn (he W.source)
  omega

#print axioms scalar_identity_read_bound
#print axioms short_word_no_universal_success
end D5.S3.Observer.Linear.GainRay
