/- GID: D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformPerturbedParameters
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/ChoiKiemKye/UniformPerturbedParameters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Perturbation stability and the all-large-dimensions construction. -/

/- Judgement form (implementation assessment; each helper retains its own classification).
   proof_shape: Anchor.largest_root_psd: bind-only; consumer=UniformPerturbedParameters.Anchor.anchor_tail_root_lower.
   proof_shape: Anchor.D_shift: bind-only; consumer=UniformPerturbedParameters.Anchor.anchor_tail_root_lower.
   proof_shape: Anchor.perturbed_kernel_stability: content.
   proof_shape: Anchor.n_ge_17: content.
   escape_witness: Anchor.perturbed_kernel_stability, consumed by Anchor.n_ge_17.
   admission_basis: escape-witness
   Direct frozen dependencies: none; dependencies are pinned Mathlib and same-delivery modules.
   Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor

noncomputable section
namespace D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformPerturbedParameters
open Matrix
open scoped ComplexConjugate ComplexOrder
open D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor
namespace Anchor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem interior_projection_lower {n : ℕ} (hn : 17≤n) (d : ℂ) (u v : ℝ) (hd : ‖d‖=1) (him : 0<d.im) (hu : u≤2) (hv : 1/(288*(n:ℝ))≤v) (hv' : v≤2)
    : d.im/(2304*(n:ℝ)) ≤ ((((d.im/(2304*(n:ℝ)):ℝ):ℂ)+Complex.I)*(-(u:ℂ)-d*(v:ℂ))).re := by
  have hnp : 0<(n:ℝ) := by positivity
  have hvp : 0≤v := (by positivity : 0≤1/(288*(n:ℝ))).trans hv; have hdr : d.re≤1 := (Complex.re_le_norm d).trans_eq hd; have hpart : u+d.re*v≤4 := by
    have ht := mul_le_mul_of_nonneg_right hdr hvp; nlinarith
  have hδ : 0≤d.im/(2304*(n:ℝ)) := by positivity
  have hp := mul_le_mul_of_nonneg_left hpart hδ; have hvbound := mul_le_mul_of_nonneg_left hv him.le; have heq : d.im*(1/(288*(n:ℝ))) - 4*(d.im/(2304*(n:ℝ))) = 4*(d.im/(2304*(n:ℝ))) := by ring
  simp only [Complex.mul_re,Complex.add_re,Complex.ofReal_re,Complex.I_re,add_zero,
    Complex.neg_re,Complex.sub_re,Complex.ofReal_im,Complex.add_im,Complex.I_im,
    zero_add,Complex.neg_im,Complex.sub_im,Complex.mul_im,mul_zero,zero_mul,sub_zero]
  nlinarith
private theorem spike_sum {m : ℕ} (hm : 2≤ m) : ∑ i, D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike m i = (m:ℝ)+1 := by
  have he (i : Fin m) : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike m i=1+(if i.val=1 then 1 else 0) := by
    unfold D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike; split_ifs <;> norm_num
  simp only [he,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]; congr 1; rw [Finset.sum_eq_single (⟨1,by omega⟩:Fin m)]
  · simp
  · intro i hi hne
    have hiv : i.val≠1 := fun h => hne (Fin.ext h); simp [hiv]
  · simp
private theorem coordinate_bounds {m : ℕ} (hm : 15≤ m) {r : ℝ} (hr : 161/32<r) (hsq : r^2≤9*((m+2:ℕ):ℝ)) (i : Fin m) : 1/(288*((m+2:ℕ):ℝ))<D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i ∧ D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i≤2 := by
  have h5 : 5<r := by linarith
  refine ⟨(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.uniform_coordinate_lower (by omega) hr hsq
    (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior_positive m h5 i).2),?_⟩
  exact (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior_upper m h5 i).trans (by
    apply (div_le_iff₀ (by linarith : 0<r-4)).mpr; linarith)
private theorem ell_bounds {m : ℕ} (hm : 15≤ m) {r : ℝ} (hr : 161/32<r) (hsq : r^2≤9*((m+2:ℕ):ℝ)) : 1/576≤ell m r ∧ ell m r≤2*((m+2:ℕ):ℝ) := by
  have hmR : (15:ℝ)≤ m := by exact_mod_cast hm
  have hnR : (0:ℝ)<((m+2:ℕ):ℝ) := by positivity
  constructor
  · have hterm (i : Fin m) : 1/(288*((m+2:ℕ):ℝ))≤D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike m i*(fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r i := by
      have hu : 1/(288*((m+2:ℕ):ℝ))≤(fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r i := (coordinate_bounds hm hr hsq i.rev).1.le; have hs := D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike_lower m i; have hvpos : 0≤(fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r i := (by positivity : 0≤1/(288*((m+2:ℕ):ℝ))).trans hu
      exact hu.trans (by nlinarith)
    have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hterm i); simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs; apply le_trans _ hs
    rw [mul_one_div,div_le_div_iff₀ (by norm_num) (by positivity)]; push_cast; linarith
  · have hterm (i : Fin m) : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike m i*(fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r i≤2*D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike m i := by
      have hu : (fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r i≤2 := (coordinate_bounds hm hr hsq i.rev).2; nlinarith [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike_lower m i]
    have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hterm i); rw [←Finset.mul_sum,spike_sum (by omega)] at hs; unfold ell dotProduct; push_cast; linarith
private theorem U17_value : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior 15 D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.R=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.u := by
  apply Matrix.mulVec_injective_of_isUnit (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.resolvent_isUnit 15 (by norm_num : 5<D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.R)); skip; rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior_solve 15 (by norm_num)]; exact D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.rational_solve.symm
private theorem k17_value : k 15 D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.R=(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.knum:ℝ)/D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.den := by
  rw [k,U17_value,D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.k_value]
private theorem ell17_value : ell 15 D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.R=(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.lnum:ℝ)/D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.den := by
  unfold ell; dsimp only; rw [U17_value,D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.ell_value]
private theorem schur17_negative : (schur 15 D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.R).det.re<0 := by
  have ha : a=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.aa := phase_def.symm.trans D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.aa_anchor.symm; have hs : schur 15 D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.R=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.probeSchur := by
    simp [schur,D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.probeSchur,k17_value,ell17_value,ha]
  rw [hs]; exact D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.schur_det_negative
theorem largest_root_psd {n : ℕ} (hn : 3≤n) (a b : Fin n → ℂ) {r : ℝ} (hr : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot a b r) : (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r).PosSemidef := by
  rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_pencil]; apply D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.largest_root_psd (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_hermitian hn a b 0).neg
  intro s hs; exact hr.2 s (by rwa [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_pencil])
theorem D_shift {n : ℕ} (a b : Fin n → ℂ) (r R : ℝ) : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b R = D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r + ((R-r:ℝ):ℂ) • 1 := by
  ext i j
  by_cases hij : i=j
  · subst j; simp [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D]
  · simp [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D,Matrix.one_apply,hij]
private theorem block_psd_schur (m : ℕ) {r : ℝ} (hr : 5<r) (hb : (block m r).PosSemidef) : (schur m r).PosSemidef := by
  letI := (interior_posDef m hr).isUnit.invertible; have hs := (Matrix.PosDef.fromBlocks₂₂ (endpoints r) ((coupling m)ᴴ) (interior_posDef m hr)).mp
    (by simpa only [block,Matrix.conjTranspose_conjTranspose] using hb)
  simpa only [Matrix.conjTranspose_conjTranspose,schur_eq m hr] using hs
private theorem anchor17_root_lower {r : ℝ} (hr : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha 17) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta 17) r) : 161/32<r := by
  by_contra h
  have hle : r≤161/32 := le_of_not_gt h; have hD := largest_root_psd (by norm_num : 3≤17) _ _ hr; have hR : (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha 17) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta 17) (161/32)).PosSemidef := by
    rw [D_shift _ _ r (161/32)]; exact hD.add (Matrix.PosSemidef.one.smul (show (0:ℂ)≤((161/32-r:ℝ):ℂ) by
      simpa only [Complex.nonneg_iff,Complex.ofReal_re,Complex.ofReal_im,and_true] using sub_nonneg.mpr hle))
  have hb := hR.submatrix (address 15); rw [anchor_reindex 15 (by norm_num)] at hb; have hs := block_psd_schur 15 (by norm_num : 5<D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor17Probe.R) hb; have hnonneg := (Complex.nonneg_iff.mp hs.det_nonneg).1
  exact (not_lt_of_ge hnonneg) schur17_negative
private theorem schur_det (m : ℕ) (r : ℝ) : (schur m r).det = (((r-k m r)^2-‖zeta m r‖^2:ℝ):ℂ) := by
  have he : schur m r=!![((r-k m r:ℝ):ℂ),-conj (zeta m r);-zeta m r,((r-k m r:ℝ):ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [schur,zeta,map_add,map_mul,Complex.conj_ofReal] <;> ring
  rw [he,Matrix.det_fin_two]; simp only [Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Complex.ofReal_sub,Complex.ofReal_pow]; rw [neg_mul_neg,Complex.conj_mul']; ring
private theorem block_det_schur (m : ℕ) {r : ℝ} (hr : 5<r) : (block m r).det=(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior m r).det*(schur m r).det := by
  letI := (interior_posDef m hr).isUnit.invertible; rw [block,Matrix.det_fromBlocks₂₂,Matrix.invOf_eq_nonsing_inv,schur_eq m hr]
private theorem root_schur_identity {m : ℕ} (hm : 4 ≤ m) {r : ℝ} (hr : 5<r) (hroot : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2))
    r) : r-k m r=‖zeta m r‖ := by
  have hD := largest_root_psd (by omega : 3≤ m+2) _ _ hroot; have hb := hD.submatrix (address m); rw [anchor_reindex m hm r] at hb; have hs := block_psd_schur m hr hb; have hd : (block m r).det=0 := by
    rw [←anchor_reindex m hm r,Matrix.det_submatrix_equiv_self]; exact hroot.1
  rw [block_det_schur m hr] at hd; have hnz : (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior m r).det≠0 := by
    exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (interior_posDef m hr).isUnit))
  have hs0 := (mul_eq_zero.mp hd).resolve_left hnz; rw [schur_det] at hs0; have hsq : (r-k m r)^2=‖zeta m r‖^2 := sub_eq_zero.mp (Complex.ofReal_eq_zero.mp hs0); have hdiag := hs.diag_nonneg (i := (0:Fin 2))
  have hpos : 0≤r-k m r := by
    simpa [schur,Complex.nonneg_iff] using hdiag
  nlinarith [norm_nonneg (zeta m r)]
private theorem zeta_norm_upper {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 5<r) : ‖zeta m r‖≤1+ell m r := by
  calc ‖zeta m r‖≤‖(1:ℂ)‖+‖a*(ell m r:ℂ)‖ := norm_add_le _ _
    _ = 1+ell m r := by rw [norm_one,norm_mul,phase_unit,one_mul,Complex.norm_real,
      Real.norm_of_nonneg (ell_positive hm hr).le]
private theorem k_ell_upper {m : ℕ} (hm : 2≤ m) {r : ℝ} (hr : 5<r) : k m r+ell m r ≤ 4*((m:ℝ)+1)/(r-4) := by
  have hterm (i : Fin m) : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike m i*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i+(fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r i)≤
      (4/(r-4))*D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike m i := by
    have hu : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i≤2/(r-4) := D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior_upper m hr i; have hv : (fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r i≤2/(r-4) := D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior_upper m hr i.rev; have ht : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i+(fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r i≤4/(r-4) := by
      have he : 2/(r-4)+2/(r-4)=4/(r-4) := by ring
      linarith
    nlinarith [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike_lower m i]
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hterm i); simp only [mul_add,Finset.sum_add_distrib,←Finset.mul_sum] at hs; rw [spike_sum hm] at hs
  simpa only [k,ell,dotProduct,mul_div_right_comm] using hs
private theorem root_square_upper {m : ℕ} (hm : 15≤ m) {r : ℝ} (hr : 5<r) (hroot : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2))
    r) : r^2≤9*((m+2:ℕ):ℝ) := by
  have heq := root_schur_identity (by omega : 4 ≤ m) hr hroot; have hnorm := zeta_norm_upper (by omega : 0 < m) hr; have hs := k_ell_upper (by omega : 2≤ m) hr; have hdiv : r-1≤4*((m:ℝ)+1)/(r-4) := by linarith
  have hquad := (le_div_iff₀ (by linarith : 0<r-4)).mp hdiv; have hmR : (15:ℝ)≤ m := by exact_mod_cast hm
  push_cast
  by_contra hbad
  have hbad' : 9*((m:ℝ)+2)<r^2 := lt_of_not_ge hbad; have hr12 : 12<r := by nlinarith [sq_nonneg (r-12)]
  have hmul := mul_nonneg (sub_pos.mpr hr12).le (show 0≤r by linarith); nlinarith
private theorem d_formula {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 5<r) : d m r=(a+(ell m r:ℂ))/(‖zeta m r‖:ℂ) := by
  have hb : b m r = zeta m r / (‖zeta m r‖ : ℂ) := by
    simp only [b, NormedSpace.normalize, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
  unfold d; rw [hb]; unfold zeta; simp only [map_div₀,map_add,map_mul,map_one,Complex.conj_ofReal]; rw [←mul_div_assoc,mul_add]; congr 1
  linear_combination (ell m r:ℂ)*phase_mul_conj
private theorem imaginary_bounds {m : ℕ} (hm : 15≤ m) {r : ℝ} (hr : 161/32<r) (hsq : r^2≤9*((m+2:ℕ):ℝ)) : 1/1000≤(b m r).im ∧ 1/(5*((m+2:ℕ):ℝ))≤(d m r).im := by
  have h5 : 5<r := by linarith
  have hell := ell_bounds hm hr hsq; have hn := zeta_norm_pos (by omega : 0 < m) h5; have hu := zeta_norm_upper (by omega : 0 < m) h5; have hlow : (7/10:ℝ)<(D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2.re) := by
    have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num); have hp := Real.sqrt_nonneg 2; dsimp [D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2]; nlinarith
  have hbi : (b m r).im=(D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2.re)*ell m r/‖zeta m r‖ := by
    have hb : b m r = zeta m r / (‖zeta m r‖ : ℂ) := by
      simp only [b, NormedSpace.normalize, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
    rw [hb,Complex.div_ofReal_im,zeta_im]
  have hdi : (d m r).im=(D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2.re)/‖zeta m r‖ := by
    rw [d_formula (by omega : 0 < m) h5,Complex.div_ofReal_im]; simp [a_cartesian]
  rw [hbi,hdi]
  constructor
  · apply (le_div_iff₀ hn).mpr
    nlinarith [ell_positive (by omega : 0 < m) h5]
  · apply (le_div_iff₀ hn).mpr
    have hnR : (17:ℝ)≤((m+2:ℕ):ℝ) := by exact_mod_cast (show 17≤ m+2 by omega)
    have hnP : (0:ℝ)<((m+2:ℕ):ℝ) := by positivity
    have hmult : (1/(5*((m+2:ℕ):ℝ)))*‖zeta m r‖≤
        (1/(5*((m+2:ℕ):ℝ)))*(1+2*((m+2:ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hsmall : (1/(5*((m+2:ℕ):ℝ)))*(1+2*((m+2:ℕ):ℝ))<7/10 := by
      rw [one_div_mul_eq_div]; apply (div_lt_iff₀ (by positivity : 0<5*((m+2:ℕ):ℝ))).mpr; nlinarith
    exact hmult.trans (hsmall.le.trans hlow.le)
private def delta (m : ℕ) (r : ℝ) : ℝ := (d m r).im/(2304*((m+2:ℕ):ℝ))
private def directionAlpha (m : ℕ) (r : ℝ) : ℂ := ((delta m r:ℂ)+Complex.I)*conj (b m r)
private def directionBeta (m : ℕ) (r : ℝ) : ℂ := (delta m r:ℂ)-Complex.I
private def directionEnds (m : ℕ) (r : ℝ) : ℂ := -((b m r).im:ℂ)-Complex.I*(1+(b m r).re:ℝ)
private theorem kernel_address (m : ℕ) (r : ℝ) (s : Fin 2⊕Fin m) : kernel m r (address m s)=kernelBlock m r s := by simp [kernel]
private theorem kernel_ne_zero (m : ℕ) (r : ℝ) : kernel m r≠0 := by
  intro hz; have hh := congrFun hz (address m (Sum.inl 1)); rw [kernel_address] at hh; norm_num [kernelBlock] at hh
private theorem anchor_alpha_address (m : ℕ) (s : Fin 2⊕Fin m) : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2) (address m s)=Sum.elim ![(1:ℂ),-1] (fun _=>a) s  := by
  have hleft (i : Fin 2) : address m (Sum.inl i) =
      if i.val = 0 then ⟨0, by omega⟩ else ⟨m+1, by omega⟩ := by
    fin_cases i <;> apply Fin.ext <;>
      simp [address, finSumFinEquiv, Fin.addCases, Equiv.sumAssoc, Equiv.sumComm]
  have hright (i : Fin m) : address m (Sum.inr i) = ⟨i.val+1, by omega⟩ := by
    apply Fin.ext
    simp [address, finSumFinEquiv, Nat.add_comm]
  cases s with
  | inl i => fin_cases i <;> simp [hleft,hright,D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha]
  | inr i =>
    have hi:=i.isLt; have h0 : i.val+1≠0 := by omega
    have hl : i.val+1+1≠m+2 := by omega
    simp [hleft,hright,D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha,h0,hl,a,Complex.ofReal_div,Complex.ofReal_ofNat,div_eq_mul_inv,mul_assoc] <;> omega
private theorem raw_halfplane_margins {m : ℕ} (hm : 15≤ m) {r : ℝ} (hr : 161/32<r) (hsq : r^2≤9*((m+2:ℕ):ℝ)) : (∀ i : Fin (m+2), i.val+1≠m+2 → delta m r≤
    (directionAlpha m r*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2) i*conj (kernel m r i))).re) ∧ (∀ i : Fin (m+2), i.val≠0 → delta m r≤ (directionBeta m
    r*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2) i*conj (kernel m r i))).re) ∧ (∀ i : Fin (m+2), i.val=0 ∨ i.val+1=m+2 → 1/1000≤ (directionEnds m
    r*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2) i*conj (kernel m r i))).re) := by
  have h5 : 5<r := by linarith
  have hp : 0 < m := by omega
  have hb := b_unit hp h5; have hd := d_unit hp h5; have hdi := d_im_pos hp h5; have hmul : conj (b m r)*b m r=1 := by simpa [hb] using Complex.conj_mul' (b m r)
  have hamul : a*conj (d m r)=b m r := by
    unfold d; simp only [map_mul,Complex.conj_conj]; rw [←mul_assoc,phase_mul_conj,one_mul]
  have hdata (i : Fin m) := coordinate_bounds hm hr hsq i; have hn : 17≤ m+2 := by omega
  refine ⟨?_,?_,?_⟩
  · intro i hi
    obtain ⟨s,rfl⟩ := (address m).surjective i; rw [anchor_alpha_address,kernel_address]
    cases s with
    | inl j =>
      fin_cases j
      · simp [directionAlpha,kernelBlock,hmul,mul_assoc]
      · simp [address,finSumFinEquiv,Fin.addCases,Equiv.sumAssoc,Equiv.sumComm] at hi
    | inr j =>
      have he : directionAlpha m r*(a*conj (kernelBlock m r (Sum.inr j))) =
          ((delta m r:ℂ)+Complex.I)*(-(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r j:ℂ)-d m r*((fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r j:ℂ)) := by
        simp only [directionAlpha,kernelBlock,Sum.elim_inr,map_neg,map_add,map_mul,
          Complex.conj_ofReal,Complex.conj_conj]
        unfold d; have h1 : conj (b m r)*(a*conj a*b m r)=1 := by
          calc _ = (a*conj a)*(conj (b m r)*b m r) := by ring
            _ = 1 := by rw [phase_mul_conj,hmul,mul_one]
        linear_combination -((delta m r:ℂ)+Complex.I)*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r j:ℂ)*h1
      change delta m r≤(directionAlpha m r*(a*conj (kernelBlock m r (Sum.inr j)))).re; rw [he]; exact interior_projection_lower hn (d m r) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r j) ((fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r j) hd hdi
        (hdata j).2 (hdata j.rev).1.le (hdata j.rev).2
  · intro i hi
    obtain ⟨s,rfl⟩ := (address m).surjective i; rw [kernel_address]; simp only [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta,one_mul]
    cases s with
    | inl j =>
      fin_cases j
      · simp [address,finSumFinEquiv,Fin.addCases,Equiv.sumAssoc,Equiv.sumComm] at hi
      · simp [directionBeta,kernelBlock]
    | inr j =>
      have he : (directionBeta m r*conj (kernelBlock m r (Sum.inr j))).re =
          ((((delta m r:ℂ)+Complex.I)*(-((fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r j:ℂ)-d m r*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r j:ℂ)))).re := by
        simp [directionBeta,kernelBlock,d,map_mul,Complex.conj_ofReal,Complex.mul_re,
          Complex.mul_im]; ring
      rw [he]; exact interior_projection_lower hn (d m r) ((fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r j) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r j) hd hdi
        (hdata j.rev).2 (hdata j).1.le (hdata j).2
  · intro i hi
    obtain ⟨s,rfl⟩ := (address m).surjective i; rw [anchor_alpha_address,kernel_address]
    cases s with
    | inl j =>
      fin_cases j <;> convert (imaginary_bounds hm hr hsq).1 using 1 <;>
        simp [directionEnds,kernelBlock,Complex.mul_re,Complex.mul_im] <;> ring
    | inr j => simp [address,finSumFinEquiv,Fin.addCases,Equiv.sumAssoc,Equiv.sumComm] at hi; have hj:=j.isLt; omega
private theorem band_last_sum {m : ℕ} (hm : 2≤ m) : ∑ i : Fin m, D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band (m+1) (Fin.last m) i.castSucc=2 := by
  let p : Fin m := ⟨m-1,by omega⟩; let q : Fin m := ⟨m-2,by omega⟩; have hpq : p≠q := by intro hh; have hv:=congrArg Fin.val hh; dsimp [p,q] at hv; omega
  have he (i : Fin m) : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band (m+1) (Fin.last m) i.castSucc=
      (if i=p then (1:ℝ) else 0)+(if i=q then 1 else 0) := by
    have hi:=i.isLt; have hip : i=p ↔ i.val=m-1 := by simp [p,Fin.ext_iff]
    have hiq : i=q ↔ i.val=m-2 := by simp [q,Fin.ext_iff]
    simp only [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band,Fin.val_last,Fin.val_castSucc,hip,hiq]
    split_ifs <;> norm_num <;> omega
  simp only [he,Finset.sum_add_distrib]; simp <;> ring
private theorem band_total_succ {m : ℕ} (hm : 2≤ m) : (∑ i : Fin (m+1), ∑ j : Fin (m+1), D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band (m+1) i j)= (∑ i : Fin m, ∑ j : Fin m,
    D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m i j)+4 := by
  rw [Fin.sum_univ_castSucc]
  have hcast (i j : Fin m) : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band (m+1) i.castSucc j.castSucc=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m i j := rfl
  simp_rw [Fin.sum_univ_castSucc,hcast]
  rw [Finset.sum_add_distrib,band_last_sum hm]; have he : (∑ i : Fin m, D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band (m+1) i.castSucc (Fin.last m))=2 := by
    have hsym (i : Fin m) : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band (m+1) i.castSucc (Fin.last m)=
        D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band (m+1) (Fin.last m) i.castSucc := by
      simpa [Matrix.conjTranspose_apply] using congrFun (congrFun (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band_hermitian (m+1)) (Fin.last m)) i.castSucc
    simp only [hsym,band_last_sum hm]
  rw [he]; have hz : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band (m+1) (Fin.last m) (Fin.last m)=0 := by simp [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band]
  simp only [hz]; ring
private theorem band_total {m : ℕ} (hm : 2≤ m) : (∑ i : Fin m, ∑ j : Fin m, D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m i j)=4*(m:ℝ)-6 := by
  induction m,hm using Nat.le_induction with
  | base => simp only [Fin.sum_univ_two]; norm_num [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band]
  | succ m hm ih => rw [band_total_succ hm,ih]; push_cast; ring
private def symmetricSpike (m : ℕ) : Fin m→ℝ := fun i=>D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike m i+D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike m i.rev
private theorem symmetricSpike_form {m : ℕ} (hm : 4 ≤ m) (i : Fin m) : symmetricSpike m i=2+(if i.val=1 then 1 else 0)+(if i.val=m-2 then 1 else 0) := by
  have hi:=i.isLt; simp only [symmetricSpike,D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike,Fin.val_rev]
  split_ifs <;> norm_num <;> omega
private theorem symmetricSpike_sq {m : ℕ} (hm : 4 ≤ m) : ∑ i, (symmetricSpike m i)^2=4*(m:ℝ)+10 := by
  let p : Fin m := ⟨1,by omega⟩; let q : Fin m := ⟨m-2,by omega⟩; have he (i : Fin m) : (symmetricSpike m i)^2=4+(if i=p then (5:ℝ) else 0)+(if i=q then 5 else 0) := by
    rw [symmetricSpike_form hm]; have hi:=i.isLt; simp only [Fin.ext_iff,p,q]
    split_ifs <;> norm_num <;> omega
  simp only [he,Finset.sum_add_distrib]; simp <;> ring
private theorem band_spike_row {m : ℕ} (hm : 4 ≤ m) : ∑ j, D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m (⟨1,by omega⟩:Fin m) j=3 := by
  let p : Fin m := ⟨0,by omega⟩; let q : Fin m := ⟨2,by omega⟩; let t : Fin m := ⟨3,by omega⟩; have he (j : Fin m) : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m (⟨1,by omega⟩:Fin m) j =
      (if j=p then (1:ℝ) else 0)+(if j=q then 1 else 0)+(if j=t then 1 else 0) := by
    simp only [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band,Fin.ext_iff,p,q,t]
    split_ifs <;> norm_num <;> omega
  simp only [he,Finset.sum_add_distrib]; simp <;> ring
private theorem band_spike_reverse_row {m : ℕ} (hm : 4 ≤ m) : ∑ j, D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m (⟨m-2,by omega⟩:Fin m) j=3 := by
  have he : (⟨m-2,by omega⟩:Fin m)=(⟨1,by omega⟩:Fin m).rev := by
    apply Fin.ext; simp [Fin.val_rev] <;> omega
  rw [he]
  calc _ = ∑ j : Fin m, D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m (⟨1,by omega⟩:Fin m).rev j.rev :=
      (Equiv.sum_comp Fin.revPerm _).symm
    _ = 3 := by simp only [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band_reverse]; exact band_spike_row hm
private theorem symmetricSpike_energy {m : ℕ} (hm : 6≤ m) : symmetricSpike m ⬝ᵥ (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m *ᵥ symmetricSpike m)=16*(m:ℝ) := by
  let e : Fin m→ℝ := fun _=>1; let p : Fin m := ⟨1,by omega⟩; let q : Fin m := ⟨m-2,by omega⟩; have he : symmetricSpike m=(2:ℝ) • e+Pi.single p 1+Pi.single q 1 := by
    ext i
    rw [symmetricSpike_form (by omega : 4 ≤ m)]; simp [Pi.single_apply,Fin.ext_iff,p,q,e,Pi.smul_apply]
  have hrowp : (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m *ᵥ e) p=3 := by
    simpa [Matrix.mulVec,dotProduct,e,p] using band_spike_row (by omega : 4 ≤ m)
  have hrowq : (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m *ᵥ e) q=3 := by
    simpa [Matrix.mulVec,dotProduct,e,q] using band_spike_reverse_row (by omega : 4 ≤ m)
  have htotal : e ⬝ᵥ (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m *ᵥ e)=4*(m:ℝ)-6 := by
    simpa [e,Matrix.mulVec,dotProduct] using band_total (by omega : 2≤ m)
  have hcol (i : Fin m) : e ⬝ᵥ (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m).col i=
      (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m *ᵥ e) i := by
    simp only [dotProduct,e,one_mul,Matrix.mulVec,mul_one,Matrix.col_apply]; apply Finset.sum_congr rfl
    intro j hj
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band_hermitian m) i) j
  have hpp : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m p p=0 := by simp [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band,p]
  have hqq : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m q q=0 := by simp [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band,q]
  have hpq : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m p q=0 := by simp [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band,p,q]; omega
  have hqp : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m q p=0 := by simp [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band,p,q]; omega
  rw [he]; simp only [Matrix.mulVec_add,Matrix.mulVec_smul,add_dotProduct,dotProduct_add,
    smul_dotProduct,dotProduct_smul,smul_eq_mul,single_dotProduct,one_mul]
  simp only [hcol,hrowp,hrowq,htotal,Matrix.mulVec_single_one,Matrix.col_apply,hpp,hqq,hpq,hqp]; ring
private theorem spike_symmetricSpike {m : ℕ} (hm : 4 ≤ m) : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike m ⬝ᵥ symmetricSpike m=2*(m:ℝ)+5 := by
  let p : Fin m := ⟨1,by omega⟩; let q : Fin m := ⟨m-2,by omega⟩; have he (i : Fin m) : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike m i*symmetricSpike m i =
      2+(if i=p then (4:ℝ) else 0)+(if i=q then 1 else 0) := by
    rw [symmetricSpike_form hm]; simp only [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike,Fin.ext_iff,p,q]
    split_ifs <;> norm_num <;> omega
  simp only [dotProduct,he,Finset.sum_add_distrib]; simp <;> ring
private theorem reverse_spike_symmetricSpike {m : ℕ} (hm : 4 ≤ m) : (fun i=>D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike m i.rev) ⬝ᵥ symmetricSpike m=2*(m:ℝ)+5 := by
  have he (i : Fin m) : symmetricSpike m i.rev=symmetricSpike m i := by
    simp [symmetricSpike,Fin.rev_rev,add_comm]
  calc _ = ∑ i, D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike m i*symmetricSpike m i.rev :=
      by
        simpa only [dotProduct,Fin.revPerm_apply,Fin.rev_rev] using (Equiv.sum_comp Fin.revPerm
          (fun i : Fin m=>D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike m i*symmetricSpike m i.rev))
    _ = _ := by simp only [he]; exact spike_symmetricSpike hm
private theorem block_quadratic (m : ℕ) (r : ℝ) (x : Fin 2→ℂ) (y : Fin m→ℂ) : star (Sum.elim x y) ⬝ᵥ (block m r *ᵥ Sum.elim x y) = star x ⬝ᵥ (endpoints r
    *ᵥ x)+star x ⬝ᵥ ((coupling m)ᴴ *ᵥ y)+ star y ⬝ᵥ (coupling m *ᵥ x)+star y ⬝ᵥ (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior m r *ᵥ y) := by
  rw [block,Matrix.fromBlocks_mulVec,Function.star_sumElim,sumElim_dotProduct_sumElim]; simp only [dotProduct_add,Function.comp_def,Sum.elim_inl,Sum.elim_inr]; ring
private def trial (m : ℕ) : Fin 2⊕Fin m→ℂ := Sum.elim ![conj a,1] ((-1/9:ℂ) • (fun i=>(symmetricSpike m i:ℂ)))
private theorem coupling_trial (m : ℕ) : coupling m *ᵥ ![conj a,1]=fun i=>(symmetricSpike m i:ℂ) := by
  ext i
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,coupling,symmetricSpike,Complex.ofReal_add]
  linear_combination (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.spike m i:ℂ)*phase_mul_conj
private theorem cast_interior_mul (m : ℕ) (r : ℝ) (f : Fin m→ℝ) : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior m r *ᵥ (fun i=>(f i:ℂ))=fun i=>((r*f i+(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m *ᵥ f) i:ℝ):ℂ) := by
  ext i
  have he : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.resolvent m r *ᵥ f=r • f+D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m *ᵥ f := by
    rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.resolvent,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]
  have hh := congrArg Complex.ofReal (congrFun he i)
  simpa [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior,Matrix.mulVec,dotProduct,Complex.ofReal_sum,Complex.ofReal_mul] using hh
private theorem trial_energy {m : ℕ} (hm : 6≤ m) (r : ℝ) : (star (trial m) ⬝ᵥ (block m r *ᵥ trial m)).re= (162*(r-(D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2.re))+(4*r-56)*(m:ℝ)+10*r-180)/81 := by
  let Q : Fin m→ℂ := fun i=>(symmetricSpike m i:ℂ); have hQQ : Q ⬝ᵥ Q=((4*(m:ℝ)+10:ℝ):ℂ) := by
    have hh := congrArg Complex.ofReal (symmetricSpike_sq (by omega : 4 ≤ m))
    simpa [Q,dotProduct,Complex.ofReal_sum,Complex.ofReal_pow,pow_two] using hh
  have hQB : Q ⬝ᵥ (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior m r *ᵥ Q)=((r*(4*(m:ℝ)+10)+16*(m:ℝ):ℝ):ℂ) := by
    rw [show Q=fun i=>(symmetricSpike m i:ℂ) from rfl,cast_interior_mul]; have hh := congrArg Complex.ofReal (symmetricSpike_energy hm)
    simp only [Complex.ofReal_add,Complex.ofReal_mul,dotProduct,mul_add,Finset.sum_add_distrib]; have h1 : (∑ i,(symmetricSpike m i:ℂ)*((r:ℂ)*(symmetricSpike m i:ℂ)))=
        (r:ℂ)*(Q ⬝ᵥ Q) := by
      simp [Q,dotProduct,Finset.mul_sum,Complex.ofReal_mul,mul_comm,mul_left_comm]
    rw [h1,hQQ]; have h2 : (∑ i,(symmetricSpike m i:ℂ)*((D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m *ᵥ symmetricSpike m) i:ℂ))=
        ((16*(m:ℝ):ℝ):ℂ) := by
      simpa [dotProduct,Complex.ofReal_sum,Complex.ofReal_mul] using hh
    rw [h2]; push_cast; ring
  have hsy : star Q=Q := by ext i; simp [Q]
  have hcouple : (coupling m)ᴴ *ᵥ Q=
      ![conj a*((2*(m:ℝ)+5:ℝ):ℂ),((2*(m:ℝ)+5:ℝ):ℂ)] := by
    rw [show Q=fun i=>(symmetricSpike m i:ℂ) from rfl,coupling_real,
      spike_symmetricSpike (by omega : 4 ≤ m),reverse_spike_symmetricSpike (by omega : 4 ≤ m)]
  have hxy : star (![conj a,1]:Fin 2→ℂ) ⬝ᵥ ((coupling m)ᴴ *ᵥ Q)=
      ((4*(m:ℝ)+10:ℝ):ℂ) := by
    rw [hcouple]; simp [dotProduct,Fin.sum_univ_two]; push_cast
    linear_combination ((2:ℂ)*(m:ℂ)+5)*phase_mul_conj
  have hxH : (star (![conj a,1]:Fin 2→ℂ) ⬝ᵥ (endpoints r *ᵥ ![conj a,1])).re=2*r-2*(D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2.re) := by
    have hx : star (![conj a,1]:Fin 2→ℂ) ⬝ᵥ (endpoints r *ᵥ ![conj a,1])=
        ((2*r:ℝ):ℂ)-a-conj a := by
      simp [endpoints,Matrix.mulVec,dotProduct,Fin.sum_univ_two]; push_cast
      linear_combination (r:ℂ)*phase_mul_conj
    rw [hx]; simp only [Complex.sub_re,Complex.ofReal_re,Complex.conj_re]; have haRe : a.re=(D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2.re) := by simp [a_cartesian]
    rw [haRe]; ring
  change (star (Sum.elim ![conj a,1] ((-1/9:ℂ) • Q)) ⬝ᵥ
    (block m r *ᵥ Sum.elim ![conj a,1] ((-1/9:ℂ) • Q))).re=_
  rw [block_quadratic]; simp only [Matrix.mulVec_smul,dotProduct_smul,star_smul,smul_dotProduct,smul_eq_mul]; rw [hxy,hsy,coupling_trial]; change (star (![conj a,1]:Fin 2→ℂ) ⬝ᵥ (endpoints r *ᵥ ![conj a,1])+
    (-1/9:ℂ)*((4*(m:ℝ)+10:ℝ):ℂ)+
    conj (-1/9:ℂ)*(Q ⬝ᵥ Q)+(-1/9:ℂ)*(conj (-1/9:ℂ)*(Q ⬝ᵥ (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior m r *ᵥ Q)))).re=_
  rw [hQQ,hQB]; simp only [Complex.add_re,hxH]; norm_num [Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im]; ring
private theorem trial_negative {m : ℕ} (hm : 16≤ m) : (star (trial m) ⬝ᵥ (block m (161/32) *ᵥ trial m)).re<0 := by
  rw [trial_energy (by omega : 6≤ m)]; have hlow : (7/10:ℝ)<(D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2.re) := by
    have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num); have hp := Real.sqrt_nonneg 2; dsimp [D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2]; nlinarith
  have hmR : (16:ℝ)≤ m := by exact_mod_cast hm
  nlinarith
private theorem anchor_tail_root_lower {m : ℕ} (hm : 16≤ m) {r : ℝ} (hr : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r) : 161/32<r := by
  by_contra h
  have hle : r≤161/32 := le_of_not_gt h; have hD := largest_root_psd (by omega : 3≤ m+2) _ _ hr; have hR : (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) (161/32)).PosSemidef := by
    rw [D_shift _ _ r (161/32)]; exact hD.add (Matrix.PosSemidef.one.smul (show (0:ℂ)≤((161/32-r:ℝ):ℂ) by
      simpa only [Complex.nonneg_iff,Complex.ofReal_re,Complex.ofReal_im,and_true] using sub_nonneg.mpr hle))
  have hb := hR.submatrix (address m); rw [anchor_reindex m (by omega : 4 ≤ m) (161/32)] at hb; exact (not_lt_of_ge (hb.re_dotProduct_nonneg (trial m))) (trial_negative hm)
private theorem anchor_root_lower {m : ℕ} (hm : 15≤ m) {r : ℝ} (hr : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r) : 161/32<r := by
  rcases eq_or_lt_of_le hm with he | ht
  · subst m; exact anchor17_root_lower hr
  · exact anchor_tail_root_lower (by omega : 16≤ m) hr
private theorem block_kernel_span {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 5<r) (heq : r-k m r=‖zeta m r‖) (v : Fin 2⊕Fin m→ℂ) (hv : block m r *ᵥ v=0) : v=v
    (Sum.inl 1) • kernelBlock m r := by
  let x : Fin 2→ℂ := v ∘ Sum.inl; let y : Fin m→ℂ := v ∘ Sum.inr; have hv' : block m r *ᵥ Sum.elim x y=0 := by
    simpa only [x,y,Sum.elim_comp_inl_inr] using hv
  have htop : endpoints r *ᵥ x+(coupling m)ᴴ *ᵥ y=0 := by
    have hh := congrArg (fun f=>f ∘ Sum.inl) hv'
    ext i
    have hi:=congrFun hh i
    simpa only [block,Matrix.fromBlocks_mulVec,Function.comp_def,Sum.elim_inl,Sum.elim_inr,Pi.zero_apply] using hi
  have hbot : coupling m *ᵥ x+D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior m r *ᵥ y=0 := by
    have hh := congrArg (fun f=>f ∘ Sum.inr) hv'
    ext i
    have hi:=congrFun hh i
    simpa only [block,Matrix.fromBlocks_mulVec,Function.comp_def,Sum.elim_inl,Sum.elim_inr,Pi.zero_apply] using hi
  have hy : y=-(inverseCoupling m r *ᵥ x) := by
    apply Matrix.mulVec_injective_of_isUnit (interior_posDef m hr).isUnit; rw [Matrix.mulVec_neg,Matrix.mulVec_mulVec,inverseCoupling_solve m hr]; exact eq_neg_of_add_eq_zero_left (add_comm _ _ |>.trans hbot)
  have hs : schur m r *ᵥ x=0 := by
    rw [←schur_eq m hr,Matrix.sub_mulVec,Matrix.mul_assoc,←Matrix.mulVec_mulVec,
      inverseCoupling_eq m hr]
    simpa only [hy,Matrix.mulVec_neg,sub_eq_add_neg] using htop
  have hs0 := congrFun hs (0:Fin 2); simp only [schur,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Pi.zero_apply] at hs0
  have hzc : (‖zeta m r‖:ℂ)*conj (b m r)=1+conj a*(ell m r:ℂ) := by
    have hz : (‖zeta m r‖ : ℂ) * b m r = zeta m r := by
      simpa only [b, Complex.real_smul] using NormedSpace.norm_smul_normalize (zeta m r)
    simpa only [map_mul, Complex.conj_ofReal, zeta, map_add, map_one] using congrArg conj hz
  rw [heq] at hs0; have hx : x 0=conj (b m r)*x 1 := by
    have hh : (‖zeta m r‖:ℂ)*(x 0-conj (b m r)*x 1)=0 := by
      linear_combination hs0-x 1*hzc
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left
      (by exact_mod_cast (zeta_norm_pos hm hr).ne'))
  have hya (i : Fin m) : y i=-(a*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i:ℂ)*x 0+((fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r i:ℂ)*x 1) := by
    rw [hy]; simp [inverseCoupling,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ext s
  cases s with
  | inl j =>
    fin_cases j
    · change x 0=x 1*conj (b m r)
      rw [hx]; ring
    · simp [kernelBlock,Pi.smul_apply,smul_eq_mul]
  | inr i =>
    change y i=x 1*-(a*conj (b m r)*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i:ℂ)+((fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r i:ℂ)); rw [hya,hx]; ring
private theorem actual_kernel_span {m : ℕ} (hm : 4 ≤ m) {r : ℝ} (hr : 5<r) (heq : r-k m r=‖zeta m r‖) (v : Fin (m+2)→ℂ) (hv : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha
    (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r *ᵥ v=0) : ∃ t : ℂ,v=t • kernel m r := by
  have hh : block m r *ᵥ (v ∘ address m)=0 := by
    rw [←anchor_reindex m hm r,Matrix.submatrix_mulVec_equiv]; have hc : (v ∘ address m) ∘ (address m).symm=v := by
      ext i; simp only [Function.comp_apply,Equiv.apply_symm_apply]
    rw [hc,hv]; rfl
  have hs := block_kernel_span (by omega : 0 < m) hr heq (v ∘ address m) hh; refine ⟨v (address m (Sum.inl 1)),?_⟩
  ext i
  obtain ⟨s,rfl⟩ := (address m).surjective i
  simpa only [kernel_address,Pi.smul_apply,Function.comp_apply] using congrFun hs s
private theorem completed_square (m : ℕ) {r : ℝ} (hr : 5<r) (x : Fin 2→ℂ) (y : Fin m→ℂ) : star (Sum.elim x y) ⬝ᵥ (block m r *ᵥ Sum.elim x y)= star
    (inverseCoupling m r *ᵥ x+y) ⬝ᵥ (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior m r *ᵥ (inverseCoupling m r *ᵥ x+y))+ star x ⬝ᵥ (schur m r *ᵥ x) := by
  letI := (interior_posDef m hr).isUnit.invertible; have hh := Matrix.schur_complement_eq₂₂ (endpoints r) ((coupling m)ᴴ) x y (interior_hermitian m r); simp only [Matrix.conjTranspose_conjTranspose,←dotProduct_mulVec,
    inverseCoupling_eq m hr,schur_eq m hr] at hh
  exact hh
private theorem schur_energy {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 5<r) (heq : r-k m r=‖zeta m r‖) (x : Fin 2→ℂ) : (star x ⬝ᵥ (schur m r *ᵥ x)).re=‖zeta m
    r‖*‖x 0-conj (b m r)*x 1‖^2 := by
  have hz : (‖zeta m r‖:ℂ)*b m r=zeta m r := by
    simpa only [b, Complex.real_smul] using NormedSpace.norm_smul_normalize (zeta m r)
  have hzc := congrArg conj hz; simp only [map_mul,Complex.conj_ofReal] at hzc; have hb : b m r*conj (b m r)=1 := by simpa [b_unit hm hr] using Complex.mul_conj' (b m r)
  have hcomplex : star x ⬝ᵥ (schur m r *ᵥ x)=
      (‖zeta m r‖:ℂ)*(conj (x 0-conj (b m r)*x 1)*(x 0-conj (b m r)*x 1)) := by
    simp only [schur,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.of_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,Pi.star_apply,heq,map_sub,map_mul,Complex.conj_conj]
    have h1 : -1-conj a*(ell m r:ℂ)=-(‖zeta m r‖:ℂ)*conj (b m r) := by
      have hc : conj (zeta m r)=1+conj a*(ell m r:ℂ) := by
        simp only [zeta,map_add,map_mul,Complex.conj_ofReal,map_one]
      rw [hc] at hzc
      linear_combination hzc
    have h2 : -1-a*(ell m r:ℂ)=-(‖zeta m r‖:ℂ)*b m r := by
      change (‖zeta m r‖:ℂ)*b m r=1+a*(ell m r:ℂ) at hz
      linear_combination hz
    rw [h1,h2]; simp only [starRingEnd_apply] at hb ⊢
    linear_combination -(‖zeta m r‖:ℂ)*star (x 1)*x 1*hb
  rw [hcomplex,Complex.conj_mul']; simp only [←Complex.ofReal_pow,←Complex.ofReal_mul,Complex.ofReal_re]
private theorem zeta_norm_lower {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 5<r) : 1≤‖zeta m r‖ := by
  calc
    1≤(zeta m r).re := by
      rw [zeta_re]; have ht:=mul_nonneg h_positive.le (ell_positive hm hr).le; linarith
    _ ≤ ‖zeta m r‖ := Complex.re_le_norm _
private theorem interior_energy_lower (m : ℕ) {r : ℝ} (hr : 5<r) (z : Fin m→ℂ) : ∑ i,‖z i‖^2 ≤ (star z ⬝ᵥ (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior m r *ᵥ z)).re := by
  have hp : (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior m r-1).PosDef := by
    apply D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Path.scaled_dominance_posDef
      ((interior_hermitian m r).sub Matrix.isHermitian_one) (fun _=>1) (by simp)
    intro i; simp only [inv_one,one_mul,mul_one]; have hrow : (∑ j∈Finset.univ.erase i,‖(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior m r-1) i j‖)≤4 := by
      calc _ = ∑ j∈Finset.univ.erase i,‖D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m i j‖ := by
            apply Finset.sum_congr rfl
            intro j hj; have hne := (Finset.mem_erase.mp hj).1; simp [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior,D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.resolvent,Matrix.one_apply,Ne.symm hne,Complex.norm_real]
        _ ≤ ∑ j,‖D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band m i j‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun j hj hj'=>norm_nonneg _)
        _ ≤ 4 := D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band_row_bound m i
    have hdiag : ((D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior m r-1) i i).re=r-1 := by
      simp [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior,D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.resolvent,D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.band]
    rw [hdiag]; linarith
  have he := hp.posSemidef.re_dotProduct_nonneg z; rw [Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub] at he; change 0≤(star z ⬝ᵥ (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior m r *ᵥ z)-star z ⬝ᵥ z).re at he; rw [Complex.sub_re] at he
  have hn : (star z ⬝ᵥ z).re=∑ i,‖z i‖^2 := by
    simp only [dotProduct,Complex.re_sum,Pi.star_apply]; apply Finset.sum_congr rfl
    intro i hi; change (conj (z i)*z i).re=‖z i‖^2; rw [Complex.conj_mul']; simp only [←Complex.ofReal_pow,Complex.ofReal_re]
  rw [hn] at he; linarith
open scoped InnerProductSpace
private theorem block_energy_coercivity {m : ℕ} (hm : 15≤ m) {r : ℝ} (hr : 161/32<r) (hsq : r^2≤9*((m+2:ℕ):ℝ)) (heq : r-k m r=‖zeta m r‖) (v :
    EuclideanSpace ℂ (Fin 2⊕Fin m)) (hv : ⟪WithLp.toLp 2 (kernelBlock m r),v⟫_ℂ=0) : (1/(9*((m+2:ℕ):ℝ)))*‖v‖^2≤(star (WithLp.ofLp v) ⬝ᵥ (block m
    r *ᵥ WithLp.ofLp v)).re := by
  have h5 : 5<r := by linarith
  let x : Fin 2→ℂ := fun i=>v (Sum.inl i); let y : Fin m→ℂ := fun i=>v (Sum.inr i); let δ : ℂ := x 0-conj (b m r)*x 1; let z : Fin m→ℂ := inverseCoupling m r *ᵥ x+y
  let W : EuclideanSpace ℂ (Fin 2⊕Fin m) := WithLp.toLp 2 (kernelBlock m r); let e := v-x 1 • W; have horth : ⟪v,x 1 • W⟫_ℂ=0 := by
    rw [inner_smul_right,←inner_conj_symm]; change x 1*conj ⟪W,v⟫_ℂ=0; rw [show ⟪W,v⟫_ℂ=0 from hv,map_zero,mul_zero]
  have hve : ‖v‖^2≤‖e‖^2 := by
    have hh := norm_sub_sq (𝕜:=ℂ) v (x 1 • W); rw [horth] at hh; change ‖v-x 1 • W‖^2=‖v‖^2-2*Complex.re 0+‖x 1 • W‖^2 at hh; simp only [Complex.zero_re,mul_zero,sub_zero] at hh; dsimp [e]; nlinarith [sq_nonneg ‖x 1 • W‖]
  have he0 : e (Sum.inl 0)=δ := by simp [e,W,kernelBlock,δ,x,PiLp.smul_apply,smul_eq_mul,mul_comm]
  have he1 : e (Sum.inl 1)=0 := by simp [e,W,kernelBlock,x,PiLp.smul_apply,smul_eq_mul]
  have hei (i : Fin m) : e (Sum.inr i)=z i-a*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i:ℂ)*δ := by
    simp [e,W,kernelBlock,z,δ,x,y,inverseCoupling,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
      PiLp.smul_apply,smul_eq_mul]
    ring
  have hU : ∑ i,(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i)^2≤4*(m:ℝ) := by
    calc _ ≤ ∑ _i : Fin m,(4:ℝ) := by
          apply Finset.sum_le_sum
          intro i hi; have hh:=coordinate_bounds hm hr hsq i; have hp:0≤D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i := (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior_positive m h5 i).1.le; nlinarith
      _ = _ := by simp; ring
  have ht (i : Fin m) : ‖z i-a*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i:ℂ)*δ‖^2≤2*‖z i‖^2+2*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i)^2*‖δ‖^2 := by
    have hUp : 0≤D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i := (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior_positive m h5 i).1.le; have hnorm : ‖a*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i:ℂ)*δ‖=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i*‖δ‖ := by
      rw [norm_mul,norm_mul,phase_unit,one_mul,Complex.norm_real,
        Real.norm_of_nonneg hUp]
    have hn:=norm_sub_le (z i) (a*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i:ℂ)*δ); rw [hnorm] at hn; have hs : ‖z i-a*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i:ℂ)*δ‖^2≤(‖z i‖+D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i*‖δ‖)^2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (mul_nonneg hUp (norm_nonneg _)))).mpr hn
    nlinarith [sq_nonneg (‖z i‖-D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i*‖δ‖)]
  have hsum : ∑ i,‖z i-a*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i:ℂ)*δ‖^2≤2*(∑ i,‖z i‖^2)+8*(m:ℝ)*‖δ‖^2 := by
    have hh:=Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>ht i); simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul] at hh; have hu:=mul_le_mul_of_nonneg_right hU (sq_nonneg ‖δ‖); nlinarith
  have henorm : ‖e‖^2=‖δ‖^2+∑ i,‖z i-a*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i:ℂ)*δ‖^2 := by
    rw [EuclideanSpace.norm_sq_eq,Fintype.sum_sum_type,Fin.sum_univ_two,he0,he1]; simp only [norm_zero,zero_pow (by omega : 2≠0),add_zero,hei]
  have heenergy : ‖δ‖^2+∑ i,‖z i‖^2≤
      (star (WithLp.ofLp v) ⬝ᵥ (block m r *ᵥ WithLp.ofLp v)).re := by
    have hvxy : WithLp.ofLp v=Sum.elim x y := by ext s; cases s <;> rfl
    rw [hvxy,completed_square m h5,Complex.add_re,schur_energy (by omega : 0 < m) h5 heq]; have hi:=interior_energy_lower m h5 z; have hz:=mul_le_mul_of_nonneg_right (zeta_norm_lower (by omega : 0 < m) h5) (sq_nonneg ‖δ‖)
    change ∑ i,‖z i‖^2≤(star z ⬝ᵥ (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior m r *ᵥ z)).re at hi; change ‖δ‖^2+∑ i,‖z i‖^2≤(star z ⬝ᵥ (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.interior m r *ᵥ z)).re+‖zeta m r‖*‖δ‖^2; nlinarith
  have hnpos : 0<9*((m+2:ℕ):ℝ) := by positivity
  rw [one_div_mul_eq_div]; apply (div_le_iff₀ hnpos).mpr; have hp : 0≤∑ i,‖z i‖^2 := Finset.sum_nonneg (fun i _=>sq_nonneg _); have hE:=mul_le_mul_of_nonneg_left heenergy hnpos.le; rw [henorm] at hve; push_cast at hE ⊢
  nlinarith [mul_nonneg (by positivity : (0:ℝ)≤ m) hp]
private theorem actual_energy_coercivity {m : ℕ} (hm : 15≤ m) {r : ℝ} (hroot : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r)
    (v : EuclideanSpace ℂ (Fin (m+2))) (hv : ⟪WithLp.toLp 2 (kernel m r),v⟫_ℂ=0) : (1/(9*((m+2:ℕ):ℝ)))*‖v‖^2≤ (star (WithLp.ofLp v) ⬝ᵥ (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D
    (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r *ᵥ WithLp.ofLp v)).re := by
  have hr:=anchor_root_lower hm hroot; have h5 : 5<r := by linarith
  let v' : EuclideanSpace ℂ (Fin 2⊕Fin m) := WithLp.toLp 2 (WithLp.ofLp v ∘ address m); have hkw : kernel m r ∘ address m=kernelBlock m r := by
    ext s; exact kernel_address m r s
  have hv' : ⟪WithLp.toLp 2 (kernelBlock m r),v'⟫_ℂ=0 := by
    change (WithLp.ofLp v ∘ address m) ⬝ᵥ star (kernelBlock m r)=0; rw [←hkw]; have hstar : star (kernel m r ∘ address m)=star (kernel m r) ∘ address m := rfl; rw [hstar,comp_equiv_dotProduct_comp_equiv]; exact hv
  have hnorm : ‖v'‖^2=‖v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]; exact Equiv.sum_comp (address m) (fun i=>‖v i‖^2)
  have henergy : star (WithLp.ofLp v') ⬝ᵥ (block m r *ᵥ WithLp.ofLp v')=
      star (WithLp.ofLp v) ⬝ᵥ (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r *ᵥ WithLp.ofLp v) := by
    rw [←anchor_reindex m (by omega : 4 ≤ m) r]; change star (WithLp.ofLp v ∘ address m) ⬝ᵥ
      ((D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r).submatrix (address m) (address m) *ᵥ
        (WithLp.ofLp v ∘ address m))=_
    rw [Matrix.submatrix_mulVec_equiv]; have hc : (WithLp.ofLp v ∘ address m) ∘ (address m).symm=WithLp.ofLp v := by ext i; simp
    rw [hc]; exact comp_equiv_dotProduct_comp_equiv (star (WithLp.ofLp v))
      (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r *ᵥ WithLp.ofLp v) (address m)
  have hh:=block_energy_coercivity hm hr (root_square_upper hm h5 hroot)
    (root_schur_identity (by omega : 4 ≤ m) h5 hroot) v' hv'
  rwa [hnorm,henergy] at hh
private theorem actual_residual_coercivity {m : ℕ} (hm : 15≤ m) {r : ℝ} (hroot : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r)
    (v : EuclideanSpace ℂ (Fin (m+2))) (hv : ⟪WithLp.toLp 2 (kernel m r),v⟫_ℂ=0) : (1/(9*((m+2:ℕ):ℝ)))*‖v‖≤ ‖Matrix.toEuclideanCLM (n:=Fin (m+2))
    (𝕜:=ℂ) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r) v‖ := by
  have he:=actual_energy_coercivity hm hroot v hv; have hc : (star (WithLp.ofLp v) ⬝ᵥ
      (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r *ᵥ WithLp.ofLp v)).re≤
      ‖v‖*‖Matrix.toEuclideanCLM (n:=Fin (m+2)) (𝕜:=ℂ) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r) v‖ := by
    have hh := re_inner_le_norm (𝕜:=ℂ) v (Matrix.toEuclideanCLM (n:=Fin (m+2)) (𝕜:=ℂ) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r) v)
    change (⟪v,Matrix.toEuclideanCLM (n:=Fin (m+2)) (𝕜:=ℂ) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r) v⟫_ℂ).re≤_ at hh
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,Matrix.ofLp_toEuclideanCLM,dotProduct_comm] using hh
  by_cases hz : v=0
  · subst v; simp
  · have hp:=norm_pos_iff.mpr hz
    nlinarith
private theorem kernel_norm_upper {m : ℕ} (hm : 15≤ m) {r : ℝ} (hr : 161/32<r) (hsq : r^2≤9*((m+2:ℕ):ℝ)) : ‖WithLp.toLp 2 (kernel m r)‖≤4*((m+2:ℕ):ℝ) := by
  have hp : 0 < m := by omega
  have h5 : 5<r := by linarith
  have hpoint (i : Fin (m+2)) : ‖kernel m r i‖≤4 := by
    obtain ⟨s,rfl⟩ := (address m).surjective i; rw [kernel_address]
    cases s with
    | inl j => fin_cases j <;> simp [kernelBlock,Complex.norm_conj,b_unit hp h5]
    | inr j =>
      have hu:=coordinate_bounds hm hr hsq j; have hv:=coordinate_bounds hm hr hsq j.rev; have hUp : 0≤D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r j := (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior_positive m h5 j).1.le; have hv' : (fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r j≤2 := hv.2
      have hVp : 0≤(fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r j := (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior_positive m h5 j.rev).1.le; change ‖-(d m r*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r j:ℂ)+((fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r j:ℂ))‖≤4; rw [norm_neg]
      calc _ ≤ ‖d m r*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r j:ℂ)‖+‖((fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r j:ℂ)‖ := norm_add_le _ _
        _ = D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r j+(fun (m : ℕ) (r : ℝ) (i : Fin m) => D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorInterior m r i.rev) m r j := by rw [norm_mul,d_unit hp h5,one_mul,Complex.norm_real,
          Complex.norm_real,Real.norm_of_nonneg hUp,Real.norm_of_nonneg hVp]
        _ ≤ 4 := by linarith
  have hs : ‖WithLp.toLp 2 (kernel m r)‖^2≤16*((m+2:ℕ):ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    calc _ ≤ ∑ _i : Fin (m+2),(16:ℝ) := by
          apply Finset.sum_le_sum
          intro i hi; nlinarith [hpoint i,norm_nonneg (kernel m r i)]
      _ = _ := by simp; ring
  have hn : (1:ℝ)≤((m+2:ℕ):ℝ) := by exact_mod_cast (show 1≤ m+2 by omega)
  nlinarith [norm_nonneg (WithLp.toLp 2 (kernel m r))]
private theorem direction_bounds {m : ℕ} (hm : 15≤ m) {r : ℝ} (hr : 5<r) : ‖directionAlpha m r‖≤2 ∧ ‖directionBeta m r‖≤2 ∧ ‖directionEnds m r‖≤3 := by
  have hd : |(d m r).im|≤1 := (Complex.abs_im_le_norm _).trans_eq (d_unit (by omega : 0 < m) hr); have hδ : 0≤delta m r ∧ delta m r≤1 := by
    have hn : (1:ℝ)≤((m+2:ℕ):ℝ) := by exact_mod_cast (show 1≤ m+2 by omega)
    unfold delta
    constructor
    · positivity [d_im_pos (by omega : 0 < m) hr]
    · apply (div_le_iff₀ (by positivity : 0<2304*((m+2:ℕ):ℝ))).mpr
      nlinarith [(abs_le.mp hd).2]
  have hb : ‖b m r‖=1 := b_unit (by omega : 0 < m) hr; have hbre : |(b m r).re|≤1 := (Complex.abs_re_le_norm _).trans_eq hb; have hbim : |(b m r).im|≤1 := (Complex.abs_im_le_norm _).trans_eq hb; refine ⟨?_,?_,?_⟩
  · rw [directionAlpha,norm_mul,Complex.norm_conj,hb,mul_one]
    apply (norm_add_le _ _).trans; rw [Complex.norm_real,Real.norm_of_nonneg hδ.1,Complex.norm_I]; linarith
  · unfold directionBeta
    apply (norm_sub_le (delta m r:ℂ) Complex.I).trans; rw [Complex.norm_real,Real.norm_of_nonneg hδ.1,Complex.norm_I]; linarith
  · unfold directionEnds
    calc _ ≤ ‖-((b m r).im:ℂ)‖+‖Complex.I*(1+(b m r).re:ℝ)‖ := norm_sub_le _ _
      _ ≤ 3 := by
        rw [norm_neg,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Complex.norm_real,
          Real.norm_eq_abs,Real.norm_eq_abs]
        have hs:=abs_add_le (1:ℝ) (b m r).re; norm_num at hs; linarith
private theorem delta_lower {m : ℕ} (hm : 15≤ m) {r : ℝ} (hr : 161/32<r) (hsq : r^2≤9*((m+2:ℕ):ℝ)) : 1/(11520*((m+2:ℕ):ℝ)^2)≤delta m r := by
  have hh := (imaginary_bounds hm hr hsq).2; unfold delta; have hn : (0:ℝ)<((m+2:ℕ):ℝ) := by positivity
  have hmul:=div_le_div_of_nonneg_right hh (show 0≤2304*((m+2:ℕ):ℝ) by positivity); have he : 1/(11520*((m+2:ℕ):ℝ)^2)=1/(5*((m+2:ℕ):ℝ))/(2304*((m+2:ℕ):ℝ)) := by
    field_simp <;> ring
  rw [he]; exact hmul
private theorem normalized_projection {ι : Type*} [Fintype ι] (w : EuclideanSpace ℂ ι) (z c : ℂ) (i : ι) : (NormedSpace.normalize z*(c*conj (NormedSpace.normalize w
    i))).re= (z*(c*conj (w i))).re/(‖z‖*‖w‖) := by
  have he : NormedSpace.normalize z*(c*conj (NormedSpace.normalize w i))=
      (z*(c*conj (w i)))/((‖z‖*‖w‖:ℝ):ℂ) := by
    simp only [NormedSpace.normalize,PiLp.smul_apply,Complex.real_smul,Complex.ofReal_inv,map_mul,map_inv₀,
      Complex.conj_ofReal,Complex.ofReal_mul]
    ring
  rw [he,Complex.div_ofReal_re]
private theorem normalized_halfplanes {m : ℕ} (hm : 15≤ m) {r : ℝ} (hr : 161/32<r) (hsq : r^2≤9*((m+2:ℕ):ℝ)) : ∃ zA zB zE : ℂ, ‖zA‖=1 ∧ ‖zB‖=1 ∧ ‖zE‖=1 ∧
    (∀ i : Fin (m+2),i.val+1≠m+2→1/(100000*((m+2:ℕ):ℝ)^3)≤ (zA*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2) i*conj ((fun (m : ℕ) (r : ℝ) => NormedSpace.normalize (WithLp.toLp 2 (kernel m r))) m r i))).re) ∧ (∀ i : Fin
    (m+2),i.val≠0→1/(100000*((m+2:ℕ):ℝ)^3)≤ (zB*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2) i*conj ((fun (m : ℕ) (r : ℝ) => NormedSpace.normalize (WithLp.toLp 2 (kernel m r))) m r i))).re) ∧ (∀ i : Fin (m+2),i.val=0 ∨
    i.val+1=m+2→1/(100000*((m+2:ℕ):ℝ)^3)≤ (zE*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2) i*conj ((fun (m : ℕ) (r : ℝ) => NormedSpace.normalize (WithLp.toLp 2 (kernel m r))) m r i))).re) := by
  have hs := raw_halfplane_margins hm hr hsq; have h5 : 5<r := by linarith
  have hδ : 0<delta m r := div_pos (d_im_pos (by omega : 0 < m) h5) (by positivity); have hza : directionAlpha m r≠0 := by
    intro hh; have hh' := hs.1 (⟨0,by omega⟩:Fin (m+2)) (by simp); rw [hh,zero_mul,Complex.zero_re] at hh'; linarith
  have hzb : directionBeta m r≠0 := by
    intro hh; have hh' := hs.2.1 (⟨m+1,by omega⟩:Fin (m+2)) (by simp); rw [hh,zero_mul,Complex.zero_re] at hh'; linarith
  have hze : directionEnds m r≠0 := by
    intro hh; have hh' := hs.2.2 (⟨0,by omega⟩:Fin (m+2)) (Or.inl rfl); rw [hh,zero_mul,Complex.zero_re] at hh'; norm_num at hh'
  have hW : (WithLp.toLp 2 (kernel m r):EuclideanSpace ℂ (Fin (m+2)))≠0 := by
    intro hh; exact kernel_ne_zero m r (by simpa using congrArg WithLp.ofLp hh)
  have hWp:=norm_pos_iff.mpr hW; have hWu:=kernel_norm_upper hm hr hsq; have hzBounds:=direction_bounds hm h5; have hn : (0:ℝ)<((m+2:ℕ):ℝ) := by positivity
  have hmain (z c : ℂ) (i : Fin (m+2)) (hz : z≠0) (hzu : ‖z‖≤2)
      (hraw : 1/(11520*((m+2:ℕ):ℝ)^2)≤(z*(c*conj (kernel m r i))).re) :
      1/(100000*((m+2:ℕ):ℝ)^3)≤(NormedSpace.normalize z*(c*conj ((fun (m : ℕ) (r : ℝ) => NormedSpace.normalize (WithLp.toLp 2 (kernel m r))) m r i))).re := by
    rw [normalized_projection]; apply (le_div_iff₀ (mul_pos (norm_pos_iff.mpr hz) hWp)).mpr; have hd : ‖z‖*‖WithLp.toLp 2 (kernel m r)‖≤8*((m+2:ℕ):ℝ) := by
      nlinarith [norm_nonneg z,norm_nonneg (WithLp.toLp 2 (kernel m r))]
    have hb := mul_le_mul_of_nonneg_left hd
      (show 0≤1/(100000*((m+2:ℕ):ℝ)^3) by positivity)
    have hnum : 1/(100000*((m+2:ℕ):ℝ)^3)*(8*((m+2:ℕ):ℝ))≤1/(11520*((m+2:ℕ):ℝ)^2) := by
      field_simp; nlinarith [sq_pos_of_pos hn]
    exact hb.trans (hnum.trans hraw)
  refine ⟨NormedSpace.normalize (directionAlpha m r),NormedSpace.normalize (directionBeta m r),
    NormedSpace.normalize (directionEnds m r),NormedSpace.norm_normalize hza,NormedSpace.norm_normalize hzb,
    NormedSpace.norm_normalize hze,?_,?_,?_⟩
  · intro i hi
    exact hmain _ _ i hza hzBounds.1 ((delta_lower hm hr hsq).trans (hs.1 i hi))
  · intro i hi
    exact hmain _ _ i hzb hzBounds.2.1 ((delta_lower hm hr hsq).trans (hs.2.1 i hi))
  · intro i hi
    rw [normalized_projection]; apply (le_div_iff₀ (mul_pos (norm_pos_iff.mpr hze) hWp)).mpr; have hd : ‖directionEnds m r‖*‖WithLp.toLp 2 (kernel m r)‖≤12*((m+2:ℕ):ℝ) := by
      nlinarith [norm_nonneg (directionEnds m r),norm_nonneg (WithLp.toLp 2 (kernel m r))]
    have hb := mul_le_mul_of_nonneg_left hd
      (show 0≤1/(100000*((m+2:ℕ):ℝ)^3) by positivity)
    have hn1 : (1:ℝ)≤((m+2:ℕ):ℝ) := by exact_mod_cast (show 1≤ m+2 by omega)
    have hnum : 1/(100000*((m+2:ℕ):ℝ)^3)*(12*((m+2:ℕ):ℝ))≤1/1000 := by
      field_simp; nlinarith [sq_nonneg (((m+2:ℕ):ℝ)-1),mul_pos hn (sq_pos_of_pos hn)]
    exact hb.trans (hnum.trans (hs.2.2 i hi))
private theorem anchor_sorted_gap {m : ℕ} (hm : 15≤ m) (i : Fin (Fintype.card (Fin (m+2)))) (hi : i.val≠0) : let hh := (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_hermitian (by omega : 3≤ m+2) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) 0).neg
    let k₀ : Fin (Fintype.card (Fin (m+2))) := ⟨0,by simp⟩
    1/(9*((m+2:ℕ):ℝ))≤hh.eigenvalues₀ k₀-hh.eigenvalues₀ i := by
  let H : Matrix (Fin (m+2)) (Fin (m+2)) ℂ := -D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) 0; let hH : H.IsHermitian := (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_hermitian (by omega : 3≤ m+2) _ _ 0).neg
  let k₀ : Fin (Fintype.card (Fin (m+2))) := ⟨0,by simp⟩; let r : ℝ := hH.eigenvalues₀ k₀; let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH; let B := hT.eigenvectorBasis finrank_euclideanSpace
  have hroot : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r := by
    simpa only [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot,←D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_pencil,H,r] using D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.pencil_top_largest (by omega : 0 < m+2) hH
  have heig (j : Fin (Fintype.card (Fin (m+2)))) :
      Matrix.toEuclideanCLM (n:=Fin (m+2)) (𝕜:=ℂ) H (B j)=(hH.eigenvalues₀ j:ℂ) • B j := by
    exact hT.apply_eigenvectorBasis finrank_euclideanSpace j
  have hD (j : Fin (Fintype.card (Fin (m+2)))) :
      Matrix.toEuclideanCLM (n:=Fin (m+2)) (𝕜:=ℂ)
        (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r) (B j)=
        ((r-hH.eigenvalues₀ j:ℝ):ℂ) • B j := by
    rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_pencil]; change Matrix.toEuclideanCLM (n:=Fin (m+2)) (𝕜:=ℂ) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil H r) (B j)=_; simp only [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil,map_sub,map_smul,map_one,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,heig,Complex.ofReal_sub]
    module
  have hk₀ : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r *ᵥ WithLp.ofLp (B k₀)=0 := by
    have hh:=congrArg WithLp.ofLp (hD k₀)
    simpa only [r,sub_self,Complex.ofReal_zero,zero_smul,WithLp.ofLp_zero,Matrix.ofLp_toEuclideanCLM] using hh
  have hr:=anchor_root_lower hm hroot
  obtain ⟨t,ht⟩:=actual_kernel_span (by omega : 4 ≤ m) (by linarith : 5<r)
    (root_schur_identity (by omega : 4 ≤ m) (by linarith : 5<r) hroot) (WithLp.ofLp (B k₀)) hk₀
  have ht' : B k₀=t • WithLp.toLp 2 (kernel m r) := by
    ext j
    exact congrFun ht j
  have htnz : t≠0 := by
    intro hz; rw [hz,zero_smul] at ht'; exact B.orthonormal.ne_zero k₀ ht'
  have hik : i≠k₀ := by intro he; apply hi; exact congrArg Fin.val he
  have horth : ⟪WithLp.toLp 2 (kernel m r),B i⟫_ℂ=0 := by
    have hh:=B.orthonormal.inner_eq_zero (Ne.symm hik); rw [ht',inner_smul_left] at hh; exact (mul_eq_zero.mp hh).resolve_left (by simpa using htnz)
  have hg:=actual_residual_coercivity hm hroot (B i) horth; rw [hD,norm_smul,Complex.norm_real,Real.norm_eq_abs,B.orthonormal.norm_eq_one,mul_one] at hg; have hnonneg : 0≤r-hH.eigenvalues₀ i :=
    sub_nonneg.mpr (hH.eigenvalues₀_antitone (show k₀ ≤ i from Nat.zero_le _))
  rw [abs_of_nonneg hnonneg] at hg
  simpa only [r,mul_one,hH,H,k₀] using hg
private theorem perturbed_sorted_gap {m : ℕ} (hm : 15≤ m) (i : Fin (Fintype.card (Fin (m+2)))) (hi : i.val≠0) : let hh := (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_hermitian (by omega : 3≤ m+2) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) 0).neg
    let k₀ : Fin (Fintype.card (Fin (m+2))) := ⟨0,by simp⟩
    1/(18*((m+2:ℕ):ℝ))≤hh.eigenvalues₀ k₀-hh.eigenvalues₀ i := by
  exact D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.shifted_gap (by omega : 17≤ m+2) (anchor_sorted_gap hm i hi)
    (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.negative_eigenvalue_perturbation (by omega : 3≤ m+2) ⟨0,by simp⟩)
    (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.negative_eigenvalue_perturbation (by omega : 3≤ m+2) i)
private theorem perturbed_top_simple {m : ℕ} (hm : 15≤ m) : let hh := (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_hermitian (by omega : 3≤ m+2) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) 0).neg
    let r := hh.eigenvalues₀ ⟨0,by simp⟩
    D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.SimpleRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r := by
  have hs := D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.top_root_simple (by omega : 0 < m+2)
    (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_hermitian (by omega : 3≤ m+2) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) 0).neg
    (fun i hi=>by
      have hg:=perturbed_sorted_gap hm i hi; have hp : 0<1/(18*((m+2:ℕ):ℝ)) := by positivity
      dsimp only at hg; linarith)
  simpa only [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.SimpleRoot,←D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_pencil] using hs
theorem perturbed_kernel_stability {m : ℕ} (hm : 15≤ m) : ∃ (r r' : ℝ) (q' : EuclideanSpace ℂ (Fin (m+2))), D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot
    (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r ∧ D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r' ∧
    D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.SimpleRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r' ∧ 5<r' ∧ ‖q'‖=1 ∧ D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2))
    r' *ᵥ WithLp.ofLp q'=0 ∧ ‖q'-(fun (m : ℕ) (r : ℝ) => NormedSpace.normalize (WithLp.toLp 2 (kernel m r))) m r‖≤4*(norm ∘ (Matrix.toEuclideanCLM (n := Fin (m+2)) (𝕜 := ℂ))) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) 0-D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D
    (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) 0)/(1/(9*((m+2:ℕ):ℝ))) ∧ ‖q'-(fun (m : ℕ) (r : ℝ) => NormedSpace.normalize (WithLp.toLp 2 (kernel m r))) m
    r‖≤4*(2*Real.pi/(1000000000*((m+2:ℕ):ℝ)^4))/(1/(9*((m+2:ℕ):ℝ))) := by
  let H : Matrix (Fin (m+2)) (Fin (m+2)) ℂ := -D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) 0; let P : Matrix (Fin (m+2)) (Fin (m+2)) ℂ := -D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) 0
  let hH : H.IsHermitian := (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_hermitian (by omega : 3≤ m+2) _ _ 0).neg; let hP : P.IsHermitian := (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_hermitian (by omega : 3≤ m+2) _ _ 0).neg; let k₀ : Fin (Fintype.card (Fin (m+2))) := ⟨0,by simp⟩
  let r := hH.eigenvalues₀ k₀; let r' := hP.eigenvalues₀ k₀; let A := Matrix.toEuclideanCLM (n:=Fin (m+2)) (𝕜:=ℂ) H; let E := Matrix.toEuclideanCLM (n:=Fin (m+2)) (𝕜:=ℂ) P-A; let q := (fun (m : ℕ) (r : ℝ) => NormedSpace.normalize (WithLp.toLp 2 (kernel m r))) m r
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hP; let Q := hT.eigenvectorBasis finrank_euclideanSpace k₀; let g : ℝ := 1/(9*((m+2:ℕ):ℝ)); let e : ℝ := 2*Real.pi/(1000000000*((m+2:ℕ):ℝ)^4)
  have hr : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r := by
    simpa only [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot,←D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_pencil,H,r] using D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.pencil_top_largest (by omega) hH
  have hr' : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r' := by
    simpa only [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot,←D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_pencil,P,r'] using D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.pencil_top_largest (by omega) hP
  have h5 := anchor_root_lower hm hr; have hW : (WithLp.toLp 2 (kernel m r):EuclideanSpace ℂ (Fin (m+2)))≠0 := by
    intro hh; exact kernel_ne_zero m r (by simpa using congrArg WithLp.ofLp hh)
  have hq : ‖q‖=1 := (fun v hv => NormedSpace.norm_normalize hv) _ hW; have hQ : ‖Q‖=1 := (hT.eigenvectorBasis finrank_euclideanSpace).orthonormal.norm_eq_one k₀; have hD (s : ℝ) (v : EuclideanSpace ℂ (Fin (m+2))) :
      Matrix.toEuclideanCLM (n:=Fin (m+2)) (𝕜:=ℂ)
        (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) s) v=(s:ℂ) • v-A v := by
    rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_pencil]; change Matrix.toEuclideanCLM (n:=Fin (m+2)) (𝕜:=ℂ) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil H s) v=_; simp only [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil,map_sub,map_smul,map_one,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,A]
  have hDq : Matrix.toEuclideanCLM (n:=Fin (m+2)) (𝕜:=ℂ)
      (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r) q=0 := by
    simp only [q,NormedSpace.normalize,RCLike.real_smul_eq_coe_smul (K:=ℂ),Complex.ofReal_inv]; rw [map_smul,Matrix.toEuclideanCLM_toLp,actual_kernel (by omega) (by linarith)
      (root_schur_identity (by omega) (by linarith) hr),WithLp.toLp_zero,smul_zero]
  have hker : A q=(r:ℂ) • q := by
    rw [hD] at hDq; exact (sub_eq_zero.mp hDq).symm
  have hgap (v : EuclideanSpace ℂ (Fin (m+2))) (hv : ⟪q,v⟫_ℂ=0) :
      g*‖v‖≤‖A v-(r:ℂ) • v‖ := by
    have hoc : ⟪WithLp.toLp 2 (kernel m r),v⟫_ℂ=0 := by
      simp only [q,NormedSpace.normalize,RCLike.real_smul_eq_coe_smul (K:=ℂ),Complex.ofReal_inv] at hv
      change ⟪((‖WithLp.toLp 2 (kernel m r)‖⁻¹:ℝ):ℂ) • WithLp.toLp 2 (kernel m r),v⟫_ℂ=0 at hv; rw [Complex.ofReal_inv,inner_smul_left] at hv; exact (mul_eq_zero.mp hv).resolve_left (by
        simp only [map_inv₀,Complex.conj_ofReal,inv_ne_zero]
        exact_mod_cast inv_ne_zero (norm_pos_iff.mpr hW).ne')
    have hh:=actual_residual_coercivity hm hr v hoc; rw [hD,norm_sub_rev] at hh; exact hh
  have hPQ : (A+E) Q=(r':ℂ) • Q := by
    have he : A+E=Matrix.toEuclideanCLM (n:=Fin (m+2)) (𝕜:=ℂ) P := by dsimp [E]; abel
    rw [he]; exact hT.apply_eigenvectorBasis finrank_euclideanSpace k₀
  have hE : ‖E‖≤e := by
    have hmat : P-H=-(D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) 0-
        D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) 0) := by dsimp [P,H]; abel
    dsimp only [E,A]; rw [←map_sub,hmat,map_neg,norm_neg]; exact D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.operator_perturbation (by omega : 3≤ m+2) 0
  have hshiftNorm : |r'-r|≤‖E‖ := by
    exact D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.abs_eigenvalue_sub_eigenvalue_le_norm
      (T:=Matrix.toEuclideanCLM (n:=Fin (m+2)) (𝕜:=ℂ) P) (S:=A)
      hT (Matrix.isSymmetric_toEuclideanLin_iff.mpr hH) finrank_euclideanSpace k₀
  have hshift : |r'-r|≤e := hshiftNorm.trans hE
  obtain ⟨z,hz,hstable⟩:=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.phase_aligned_stability A E q Q r r' g ‖E‖ (by positivity) hq hQ hker hPQ hgap hshiftNorm le_rfl; have hnorm : ‖z • Q‖=1 := by rw [norm_smul,hz,hQ,mul_one]
  have hkP : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r' *ᵥ WithLp.ofLp (z • Q)=0 := by
    have hzero : Matrix.toEuclideanCLM (n:=Fin (m+2)) (𝕜:=ℂ)
        (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r') (z • Q)=0 := by
      rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_pencil]; change Matrix.toEuclideanCLM (n:=Fin (m+2)) (𝕜:=ℂ) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil P r') (z • Q)=0; simp only [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil,map_sub,map_smul,map_one,ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,map_smul]
      have heig : Matrix.toEuclideanCLM (n:=Fin (m+2)) (𝕜:=ℂ) P Q=(r':ℂ) • Q :=
        hT.apply_eigenvectorBasis finrank_euclideanSpace k₀
      rw [heig]; module
    simpa only [Matrix.ofLp_toEuclideanCLM,WithLp.ofLp_zero] using congrArg WithLp.ofLp hzero
  have hsmall : e<1/32 := by
    have hs:=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.perturbation_error_small (by omega : 17≤ m+2); have hn : (1:ℝ)≤((m+2:ℕ):ℝ) := by exact_mod_cast (show 1≤ m+2 by omega)
    have ht : 1/(36*((m+2:ℕ):ℝ))≤1/32 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    exact hs.trans_le ht
  have hr5 : 5<r' := by
    have hs:=(abs_le.mp hshift).1; linarith
  have hEnorm : ‖E‖=(norm ∘ (Matrix.toEuclideanCLM (n := Fin (m+2)) (𝕜 := ℂ)))
      (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) 0-
       D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) 0) := by
    have hmat : P-H=-(D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) 0-
        D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) 0) := by dsimp [P,H]; abel
    dsimp only [E,A,Function.comp_apply]; rw [←map_sub,hmat,map_neg,norm_neg]
  have hcap : ‖z • Q-q‖≤4*e/g := hstable.trans (by gcongr)
  exact ⟨r,r',z • Q,hr,hr',perturbed_top_simple hm,hr5,hnorm,hkP,
    by simpa only [hEnorm] using hstable,hcap⟩
private theorem stable_halfplanes {m : ℕ} (hm : 15≤ m) {r : ℝ} (hroot : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) r) (q' :
    EuclideanSpace ℂ (Fin (m+2))) (herr : ‖q'-(fun (m : ℕ) (r : ℝ) => NormedSpace.normalize (WithLp.toLp 2 (kernel m r))) m r‖≤4*(2*Real.pi/(1000000000*((m+2:ℕ):ℝ)^4))/(1/(9*((m+2:ℕ):ℝ)))) : ∃ zA zB zE : ℂ,
    ‖zA‖=1 ∧ ‖zB‖=1 ∧ ‖zE‖=1 ∧ (∀ i : Fin (m+2),i.val+1≠m+2→1/(200000*((m+2:ℕ):ℝ)^3)≤ (zA*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2) i*conj (q' i))).re) ∧ (∀ i :
    Fin (m+2),i.val≠0→1/(200000*((m+2:ℕ):ℝ)^3)≤ (zB*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2) i*conj (q' i))).re) ∧ (∀ i : Fin (m+2),i.val=0 ∨
    i.val+1=m+2→1/(200000*((m+2:ℕ):ℝ)^3)≤ (zE*(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2) i*conj (q' i))).re) := by
  have hr:=anchor_root_lower hm hroot
  obtain ⟨zA,zB,zE,hzA,hzB,hzE,ha,hb,he⟩:=normalized_halfplanes hm hr
    (root_square_upper hm (by linarith : 5<r) hroot)
  have hW : (WithLp.toLp 2 (kernel m r):EuclideanSpace ℂ (Fin (m+2)))≠0 := by
    intro hh; exact kernel_ne_zero m r (by simpa using congrArg WithLp.ofLp hh)
  have hq : ‖(fun (m : ℕ) (r : ℝ) => NormedSpace.normalize (WithLp.toLp 2 (kernel m r))) m r‖=1 := (fun v hv => NormedSpace.norm_normalize hv) _ hW; have hbudget:=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.stability_error_budget (by omega : 17≤ m+2)
    (g:=1/(9*((m+2:ℕ):ℝ))) (e:=2*Real.pi/(1000000000*((m+2:ℕ):ℝ)^4)) le_rfl (by positivity) le_rfl
  have herror (i : Fin (m+2)) : ‖q'-(fun (m : ℕ) (r : ℝ) => NormedSpace.normalize (WithLp.toLp 2 (kernel m r))) m r‖+
      ‖D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2) i-D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha (m+2) i‖≤
      73*Real.pi/(1000000000*((m+2:ℕ):ℝ)^3) :=
    (add_le_add herr (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha_anchor_distance (by omega : 3≤ m+2) i)).trans hbudget
  have herrorB (i : Fin (m+2)) : ‖q'-(fun (m : ℕ) (r : ℝ) => NormedSpace.normalize (WithLp.toLp 2 (kernel m r))) m r‖+
      ‖D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2) i-D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2) i‖≤
      73*Real.pi/(1000000000*((m+2:ℕ):ℝ)^3) := by
    simp only [sub_self,norm_zero,add_zero]; have hphase : 0≤Real.pi*(m+2)*D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.epsilon (m+2) := by positivity [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.epsilon_pos (by omega : 0 < m+2)]
    have hb : ‖q'-(fun (m : ℕ) (r : ℝ) => NormedSpace.normalize (WithLp.toLp 2 (kernel m r))) m r‖≤4*(2*Real.pi/(1000000000*((m+2:ℕ):ℝ)^4))/(1/(9*((m+2:ℕ):ℝ)))+
        Real.pi*((m+2:ℕ):ℝ)*D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.epsilon (m+2) :=
      herr.trans (le_add_of_nonneg_right (by positivity [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.epsilon_pos (by omega : 0 < m+2)]))
    exact hb.trans hbudget
  refine ⟨zA,zB,zE,hzA,hzB,hzE,?_,?_,?_⟩
  · intro i hi
    exact D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.surviving_projection (by omega) _ _ _ _ _ i hzA
      (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha_norm _ i) hq (ha i hi) (herror i)
  · intro i hi
    exact D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.surviving_projection (by omega) _ _ _ _ _ i hzB
      (by simp [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta]) hq (hb i hi) (herrorB i)
  · intro i hi
    exact D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.surviving_projection (by omega) _ _ _ _ _ i hzE
      (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha_norm _ i) hq (he i hi) (herror i)
theorem n_ge_17 {n : ℕ} (hn : 17≤n) : ∃ (r : ℝ) (w : Fin n→ℂ), D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Admissible (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) ∧ 5<r ∧ D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot
    (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r ∧ D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.SimpleRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r ∧ w≠0 ∧ D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n)
    (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r *ᵥ w=0 ∧ D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.StarCondition (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) w ∧ D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.PPT (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.rho (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n)
    (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r) ∧ D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Edge (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.rho (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r) ∧ Matrix.rank (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.rho (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n)
    (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r)=n*n-1 ∧ Matrix.rank (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.rhoGamma (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r)=n*n-2*n+3 := by
  obtain ⟨m,rfl⟩ : ∃ m,n=m+2 := ⟨n-2,by omega⟩; have hm : 15≤ m := by omega
  obtain ⟨r,r',q',hr,hr',hsimple,h5,hq',hk,_herrNorm,herr⟩:=perturbed_kernel_stability hm
  obtain ⟨zA,zB,zE,hzA,hzB,hzE,ha,hb,he⟩:=stable_halfplanes hm hr q' herr; have hmargin : 0<1/(200000*((m+2:ℕ):ℝ)^3) := by positivity
  have hstar : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.StarCondition (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+2)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+2)) (WithLp.ofLp q') :=
    D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.three_halfplanes_star (by omega) _ _ _ zA zB zE
      (fun i hi=>hmargin.trans_le (ha i hi)) (fun i hi=>hmargin.trans_le (hb i hi))
      (fun i hi=>hmargin.trans_le (he i hi))
  have hqne : WithLp.ofLp q'≠0 := by
    intro hz; have hh : q'=0 := WithLp.ofLp_injective 2 hz; rw [hh,norm_zero] at hq'; norm_num at hq'
  have hab:=D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.admissible (by omega : 3≤ m+2); have hp:=D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.proposition61 (m+2) (by omega) _ _ r' (WithLp.ofLp q') hab (by linarith)
    hr' hsimple hqne hk hstar
  exact ⟨r',WithLp.ofLp q',hab,h5,hr',hsimple,hqne,hk,hstar,hp⟩
end Anchor
#print axioms Anchor.anchor_root_lower
#print axioms Anchor.coordinate_bounds
#print axioms Anchor.actual_residual_coercivity
#print axioms Anchor.anchor_sorted_gap
#print axioms Anchor.perturbed_sorted_gap
#print axioms Anchor.perturbed_kernel_stability
#print axioms Anchor.stable_halfplanes
#print axioms Anchor.n_ge_17

end D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformPerturbedParameters
