/- GID: D5/S3/Combinatorics/SpectralGraph/PairedTensorMinimum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PairedTensorMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Genuine minimum eigenpairs of the full weighted repeated-pair tensor. -/
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionObstructions
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-! The source four-prime repeated-pair notes use a genuine smallest root
of the full symmetrized four-dimensional operator. This owner connects
Mathlib's finite Hermitian eigenbasis to every nonzero eigenpair of the
original weighted tensor. It supplies the balanced, double-pair and
zero-constant consumers, with no compressed Rayleigh spectrum. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.PairedTensorMinimum
open PairedIdealIntersectionObstructions

private theorem symmetric_index (a b c e : ℝ)
    (v : Fin 2 × Fin 2 → ℝ) (hv : v≠0) (he : symmetricK a b c*ᵥv=e • v) :
    ∃ q, (symmetric_hermitian a b c).eigenvalues q=e := by
  have hspec : e∈spectrum ℝ (symmetricK a b c) := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    change (symmetricK a b c).charpoly.eval e=0
    rw [Matrix.eval_charpoly]
    by_contra hd
    apply hv
    apply Matrix.eq_zero_of_mulVec_eq_zero hd
    rw [sub_mulVec,he]
    ext q
    simp [Matrix.scalar,Matrix.mulVec_diagonal]
  rw [(symmetric_hermitian a b c).spectrum_real_eq_range_eigenvalues] at hspec
  exact hspec

private theorem tensor_index (a b c e : ℝ) (hb : 0<b) (hc : 0<c)
    (h : Fin 2 × Fin 2 → ℝ) (hh : h≠0) (he : tensorK a b c*ᵥh=e • h) :
    ∃ q, (symmetric_hermitian a b c).eigenvalues q=e := by
  have hd : (tensorK a b c-e • 1).det=0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨h,hh,?_⟩
    rw [sub_mulVec,he,smul_mulVec,one_mulVec,sub_self]
  have hs : (symmetricK a b c-e • 1).det=0 := by
    rw [tensor_symmetric_det_shift a b c e hb hc]
    exact hd
  obtain ⟨v,hv,hve⟩:=Matrix.exists_mulVec_eq_zero_iff.mpr hs
  have hE : symmetricK a b c*ᵥv=e • v := by
    rw [sub_mulVec,smul_mulVec,one_mulVec] at hve
    exact sub_eq_zero.mp hve
  exact symmetric_index a b c e v hv hE

/-- A genuine nonzero minimum eigenpair, compared against every nonzero
real eigenpair of the same full operator, on all positive real parameters. -/
theorem minimum (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c) :
    ∃ e : ℝ, 1<e ∧ ∃ h : Fin 2 × Fin 2 → ℝ,
      h≠0 ∧ tensorK a b c*ᵥh=e • h ∧
      ∀ r : ℝ, ∀ z : Fin 2 × Fin 2 → ℝ, z≠0 → tensorK a b c*ᵥz=r • z → e≤r := by
  obtain ⟨q,_,hq⟩:=(univ : Finset (Fin 2 × Fin 2)).exists_min_image
    (symmetric_hermitian a b c).eigenvalues univ_nonempty
  let e:=(symmetric_hermitian a b c).eigenvalues q
  let v : Fin 2 × Fin 2 → ℝ:=(symmetric_hermitian a b c).eigenvectorBasis q
  have hv : v≠0 := (WithLp.ofLp_eq_zero 2).ne.mpr
    ((symmetric_hermitian a b c).eigenvectorBasis.orthonormal.ne_zero q)
  have hE : symmetricK a b c*ᵥv=e • v:=(symmetric_hermitian a b c).mulVec_eigenvectorBasis q
  obtain ⟨h,hh,hhe⟩:=tensor_eigenpair_of_symmetric a b c hb hc e v hv hE
  refine ⟨e,symmetric_eigenvalue_gt_one a b c ha hb.le hc.le e v hv hE,h,hh,hhe,?_⟩
  intro r z hz hze
  obtain ⟨u,hu⟩:=tensor_index a b c r hb hc z hz hze
  simpa only [hu] using hq u (mem_univ u)

end D5.S3.Combinatorics.SpectralGraph.PairedTensorMinimum
