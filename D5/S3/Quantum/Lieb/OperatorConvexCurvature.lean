/- GID: D5/S3/Quantum/Lieb/OperatorConvexCurvature
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/OperatorConvexCurvature
   mirror-E: none(waiver:classical-finite-matrix-supplier)
   anchors: []
   utility: none
   digest: Two-dimensional CFC affine rigidity and full support of convex Stieltjes curvature. -/
import D5.S3.Quantum.Lieb.LownerHeinzTheorem
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Analytic.Convexity.CurvatureAffineRigidity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-! Classical finite-matrix rigidity for operator-convex functions on the positive ray.
The curvature convention is the actual right-derivative Stieltjes measure on Positive.
This is a necessary supplier for the Hiai–Mosonyi–Tomamichel divergence question
(arXiv:2607.08760v1), not a solution or novelty claim for that classification. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Quantum.Lieb.OperatorConvexCurvature

open Set Matrix MeasureTheory
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

private abbrev M := Matrix (Fin 2) (Fin 2) ℂ

private def block (q c d : ℝ) : M := !![(q : ℂ), (c : ℂ); (c : ℂ), (d : ℂ)]

private lemma block_selfAdjoint (q c d : ℝ) : IsSelfAdjoint (block q c d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block, Matrix.star_apply]

private lemma block_spectrum (q c d x : ℝ) :
    x ∈ spectrum ℝ (block q c d) ↔ (x - q) * (x - d) - c ^ 2 = 0 := by
  rw [← spectrum.algebraMap_mem_iff ℂ, spectrum.mem_iff,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  simp only [Algebra.algebraMap_eq_smul_one, Matrix.det_fin_two,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, block,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    ite_eq_left, ite_false, Fin.zero_ne_one, Ne.symm Fin.zero_ne_one, smul_eq_mul,
    mul_one, mul_zero, zero_sub]
  simp only [Complex.real_smul, mul_one]
  norm_cast
  ring_nf

private lemma block_diag (q w : ℝ) :
    block q 0 w = diagonal (fun i : Fin 2 => ((if i = 0 then q else w : ℝ) : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block, Matrix.diagonal]

private lemma block_sym_spectrum {q β x : ℝ} (hx : x ∈ spectrum ℝ (block q β q)) :
    x = q - β ∨ x = q + β := by
  have h := (block_spectrum q β q x).mp hx
  have hp : (x - (q - β)) * (x - (q + β)) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp hp with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

private lemma block_sym_positive {q β : ℝ} (hβ : 0 < β) (hq : β < q) :
    IsStrictlyPositive (block q β q) := by
  apply (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R := ℝ) _
    (block_selfAdjoint q β q)).2
  intro x hx
  rcases block_sym_spectrum hx with rfl | rfl <;> linarith

private lemma block_diag_positive {q w : ℝ} (hq : 0 < q) (hw : 0 < w) :
    IsStrictlyPositive (block q 0 w) := by
  apply (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R := ℝ) _
    (block_selfAdjoint q 0 w)).2
  intro x hx
  have hx' : (x-q)*(x-w) = 0 := by simpa using (block_spectrum q 0 w x).mp hx
  rcases mul_eq_zero.mp hx' with h | h
  · simpa only [sub_eq_zero.mp h] using hq
  · simpa only [sub_eq_zero.mp h] using hw

private lemma block_mix (q β w t : ℝ) :
    (1-t) • block q 0 w + t • block q β q = block q (t*β) ((1-t)*w+t*q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, Complex.real_smul] <;> ring

private lemma cfc_diag_zero_first (g : ℝ → ℝ) {q w : ℝ} (hq : g q = 0) :
    cfc g (block q 0 w) 0 0 = 0 := by
  rw [block_diag,
    D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal]
  simp [hq]

private lemma zero_of_nonneg_commuting {G : M} {q c d : ℝ}
    (hG : 0 ≤ G) (h00 : G 0 0 = 0) (hc : c ≠ 0)
    (hcomm : Commute G (block q c d)) : G = 0 := by
  have hk : G *ᵥ ![1, 0] = 0 := hG.posSemidef.dotProduct_mulVec_zero_iff.mp (by
    simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec, h00])
  have h10 : G 1 0 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hk 1
  have h01 : G 0 1 = 0 := by
    have h := hG.posSemidef.isHermitian.apply 1 0
    simpa [h10] using congrArg star h
  have he := congrArg (fun T : M => T 0 1) hcomm.eq
  simp [Matrix.mul_apply, Fin.sum_univ_two, block, h00, h01] at he
  have h11 : G 1 1 = 0 := he.resolve_left hc
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

private lemma cfc_mix_zero {g : ℝ → ℝ}
    (hg : ∀ x ∈ Ioi 0, 0 ≤ g x)
    (hconv : LownerHeinzCore.OperatorConvexOn (𝓐 := M) (Ioi 0) g)
    {q β w t : ℝ} (hβ : 0 < β) (hq : β < q) (hw : 0 < w)
    (ht0 : 0 < t) (ht1 : t < 1)
    (gq : g q = 0) (gm : g (q - β) = 0) (gp : g (q + β) = 0) :
    cfc g (block q (t*β) ((1-t)*w+t*q)) = 0 := by
  let A := block q 0 w
  let B := block q β q
  let D := block q (t*β) ((1-t)*w+t*q)
  have hA : IsStrictlyPositive A := block_diag_positive (hβ.trans hq) hw
  have hB : IsStrictlyPositive B := block_sym_positive hβ hq
  have hD : IsStrictlyPositive D := by
    rw [show D = (1-t) • A + t • B from (block_mix q β w t).symm]
    exact (hA.smul (sub_pos.mpr ht1)).add_nonneg (smul_nonneg ht0.le hB.nonneg)
  have hbzero : cfc g B = 0 := by
    rw [← cfc_zero (R := ℝ) B]
    apply cfc_congr
    intro x hx
    rcases block_sym_spectrum hx with rfl | rfl <;> assumption
  have hbound := hconv (A := A) (B := B) (t := t)
    (block_selfAdjoint _ _ _) (block_selfAdjoint _ _ _) ht0.le ht1.le
    (fun x hx => hA.spectrum_pos hx) (fun x hx => hB.spectrum_pos hx)
  change cfc g ((1-t) • A + t • B) ≤ (1-t) • cfc g A + t • cfc g B at hbound
  rw [show (1-t) • A + t • B = D from block_mix q β w t] at hbound
  rw [hbzero, smul_zero, add_zero] at hbound
  have hG : 0 ≤ cfc g D := cfc_nonneg (fun x hx => hg x (hD.spectrum_pos hx))
  have h00 : cfc g D 0 0 = 0 := by
    have h := (Matrix.le_iff.mp hbound).diag_nonneg (i := 0)
    have ha00 : cfc g A 0 0 = 0 := cfc_diag_zero_first g gq
    have hn : cfc g D 0 0 ≤ 0 := by
      simpa only [Matrix.sub_apply, Matrix.smul_apply, ha00, smul_zero,
        zero_sub, neg_nonneg] using h
    exact le_antisymm hn hG.posSemidef.diag_nonneg
  have hc : Commute (cfc g D) D := by
    have h := cfc_commute_cfc g (fun x : ℝ => x) D
    rwa [cfc_id' ℝ D (block_selfAdjoint _ _ _)] at h
  exact zero_of_nonneg_commuting hG h00 (mul_ne_zero ht0.ne' hβ.ne') hc

private lemma zero_everywhere_of_two_dimensional {g : ℝ → ℝ}
    (hg : ∀ x ∈ Ioi 0, 0 ≤ g x)
    (hconv : LownerHeinzCore.OperatorConvexOn (𝓐 := M) (Ioi 0) g)
    {q β : ℝ} (hβ : 0 < β) (hq : β < q)
    (gq : g q = 0) (gm : g (q - β) = 0) (gp : g (q + β) = 0) :
    ∀ z ∈ Ioi 0, g z = 0 := by
  intro z hz
  by_cases hzq : z = q
  · simpa only [hzq] using gq
  have hcont : Continuous (fun t : ℝ => z - (t*β)^2/(z-q) - t*q) := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < z - (t*β)^2/(z-q) - t*q :=
    hcont.continuousAt.eventually (Ioi_mem_nhds (by simpa using hz))
  have hev' : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < t ∧ t < 1 ∧ 0 < z - (t*β)^2/(z-q) - t*q := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      hev.filter_mono nhdsWithin_le_nhds] with t ht ht1 hp
    exact ⟨ht, ht1, hp⟩
  obtain ⟨t, ht0, ht1, hp⟩ := hev'.exists
  let d := z - (t*β)^2/(z-q)
  let w := (d-t*q)/(1-t)
  have hw : 0 < w := div_pos hp (sub_pos.mpr ht1)
  have hd : (1-t)*w+t*q = d := by
    dsimp [w]
    field_simp
    ring
  have hzspec : z ∈ spectrum ℝ (block q (t*β) d) := by
    apply (block_spectrum _ _ _ _).2
    dsimp [d]
    field_simp [sub_ne_zero.mpr hzq]
    ring
  have hzero := cfc_mix_zero hg hconv hβ hq hw ht0 ht1 gq gm gp
  rw [hd] at hzero
  have heq : cfc g (block q (t*β) d) = cfc (fun _ : ℝ => 0) (block q (t*β) d) := by
    simpa using hzero
  exact eqOn_of_cfc_eq_cfc heq
    ((block q (t*β) d).finite_real_spectrum.continuousOn g)
    continuousOn_const (block_selfAdjoint _ _ _) hzspec

private lemma nonneg_of_local_zero {g : ℝ → ℝ} (hg : ConvexOn ℝ (Ioi 0) g)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hz : ∀ x ∈ Ioo a b, g x = 0) :
    ∀ x ∈ Ioi 0, 0 ≤ g x := by
  let p := (2*a+b)/3
  let r := (a+2*b)/3
  have hp : p ∈ Ioo a b := by dsimp [p]; constructor <;> linarith
  have hr : r ∈ Ioo a b := by dsimp [r]; constructor <;> linarith
  have hpr : p < r := by dsimp [p, r]; linarith
  have gp := hz p hp
  have gr := hz r hr
  intro x hx
  by_cases hxp : x < p
  · have hs := hg.slope_mono_adjacent hx (ha.trans hr.1) hxp hpr
    rw [gp, gr, sub_self, zero_div] at hs
    have hs' := (div_le_iff₀ (sub_pos.mpr hxp)).mp hs
    linarith
  · by_cases hrx : r < x
    · have hs := hg.slope_mono_adjacent (ha.trans hp.1) hx hpr hrx
      rw [gp, gr, sub_self, zero_div] at hs
      have hs' := (le_div_iff₀ (sub_pos.mpr hrx)).mp hs
      linarith
    · have hxJ : x ∈ Ioo a b := ⟨hp.1.trans_le (le_of_not_gt hxp),
        (le_of_not_gt hrx).trans_lt hr.2⟩
      exact (hz x hxJ).symm.le

private lemma subtract_affine_convex {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (α β : ℝ) : ConvexOn ℝ (Ioi 0) (fun x => f x - (α*x+β)) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hf.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have hβ := congrArg (fun s : ℝ => s*β) hab
  nlinarith

private lemma cfc_subtract_affine (f : ℝ → ℝ) (α β : ℝ) (A : M)
    (hA : IsSelfAdjoint A) :
    cfc (fun x => f x - (α*x+β)) A = cfc f A - (α • A + algebraMap ℝ M β) := by
  rw [cfc_sub f _ A (A.finite_real_spectrum.continuousOn f)
    (by fun_prop), cfc_add_const β _ A (by fun_prop) hA,
    cfc_const_mul_id α A hA]

private lemma subtract_affine_matrixConvex {f : ℝ → ℝ}
    (hf : LownerHeinzCore.OperatorConvexOn (𝓐 := M) (Ioi 0) f) (α β : ℝ) :
    LownerHeinzCore.OperatorConvexOn (𝓐 := M) (Ioi 0) (fun x => f x - (α*x+β)) := by
  intro A B t hA hB ht0 ht1 hsA hsB
  have h := hf hA hB ht0 ht1 hsA hsB
  have hD : IsSelfAdjoint ((1-t) • A+t • B) :=
    ((IsSelfAdjoint.all (1-t)).smul hA).add ((IsSelfAdjoint.all t).smul hB)
  change cfc (fun x => f x - (α*x+β)) ((1-t) • A+t • B) ≤
    (1-t) • cfc (fun x => f x - (α*x+β)) A + t • cfc (fun x => f x - (α*x+β)) B
  rw [cfc_subtract_affine f α β _ hD, cfc_subtract_affine f α β A hA,
    cfc_subtract_affine f α β B hB]
  have he : (1-t) • (cfc f A - (α • A + algebraMap ℝ M β)) +
      t • (cfc f B - (α • B + algebraMap ℝ M β)) =
      ((1-t) • cfc f A+t • cfc f B) -
        (α • ((1-t) • A+t • B)+algebraMap ℝ M β) := by
    simp only [smul_sub, smul_add, smul_smul, ← add_smul, sub_add_cancel,
      one_smul]
    module
  rw [he]
  exact sub_le_sub_right h _

/-- A genuine two-dimensional matrix-convex function on the positive ray which
is affine on a nonempty open interval is affine on the entire positive ray. -/
theorem affine_of_matrixConvex {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (hconv : LownerHeinzCore.OperatorConvexOn (𝓐 := Matrix (Fin 2) (Fin 2) ℂ) (Ioi 0) f)
    (a b α γ : ℝ) (ha : 0 < a) (hab : a < b)
    (he : ∀ x ∈ Ioo a b, f x = α * x + γ) :
    ∀ x ∈ Ioi 0, f x = α * x + γ := by
  let g := fun x => f x - (α * x + γ)
  have hg : ConvexOn ℝ (Ioi 0) g := subtract_affine_convex hf α γ
  have gz : ∀ x ∈ Ioo a b, g x = 0 := fun x hx => sub_eq_zero.mpr (he x hx)
  let q := (a+b)/2
  let β := (b-a)/4
  have hβ : 0 < β := by dsimp [β]; linarith
  have hq : β < q := by dsimp [β, q]; linarith
  have hqJ : q ∈ Ioo a b := by dsimp [q]; constructor <;> linarith
  have hmJ : q-β ∈ Ioo a b := by dsimp [q, β]; constructor <;> linarith
  have hpJ : q+β ∈ Ioo a b := by dsimp [q, β]; constructor <;> linarith
  have hzero := zero_everywhere_of_two_dimensional (nonneg_of_local_zero hg ha hab gz)
    (subtract_affine_matrixConvex hconv α γ) hβ hq (gz q hqJ) (gz _ hmJ) (gz _ hpJ)
  intro x hx
  exact sub_eq_zero.mp (hzero x hx)

private lemma matrixConvex_of_operatorConvex {f : ℝ → ℝ}
    (hconv : LownerHeinzTheorem.OperatorConvexOnAll.{0} (Ioi 0) f)
    (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] :
    LownerHeinzCore.OperatorConvexOn (𝓐 := Matrix n n ℂ) (Ioi 0) f := by
  let e := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
  have hcfc (A : Matrix n n ℂ) (hA : IsSelfAdjoint A) :
      e (cfc f A) = cfc f (e A) :=
    StarAlgHomClass.map_cfc e f A (A.finite_real_spectrum.continuousOn f)
      (StarAlgEquiv.isometry e).continuous hA (hA.map e)
  have hspec (A : Matrix n n ℂ) : spectrum ℝ (e A) = spectrum ℝ A :=
    AlgEquiv.spectrum_eq (e.toAlgEquiv.restrictScalars ℝ) A
  have hesmul (r : ℝ) (A : Matrix n n ℂ) : e (r • A) = r • e A :=
    (e.toAlgEquiv.restrictScalars ℝ).toLinearEquiv.map_smul r A
  intro A B t hA hB ht0 ht1 hsA hsB
  have hD : IsSelfAdjoint ((1-t) • A+t • B) :=
    ((IsSelfAdjoint.all (1-t)).smul hA).add ((IsSelfAdjoint.all t).smul hB)
  have h := hconv (K := EuclideanSpace ℂ n) (A := e A) (B := e B) (t := t)
    (hA.map e) (hB.map e) ht0 ht1 (hspec A ▸ hsA) (hspec B ▸ hsB)
  change cfc f ((1-t) • e A+t • e B) ≤ (1-t) • cfc f (e A)+t • cfc f (e B) at h
  have h' : e (cfc f ((1-t) • A+t • B)) ≤ e ((1-t) • cfc f A+t • cfc f B) := by
    rw [hcfc _ hD]
    simp only [map_add, hesmul, hcfc A hA, hcfc B hB]
    exact h
  have hback := map_nonneg e.symm (sub_nonneg.mpr h')
  simpa only [map_sub, StarAlgEquiv.symm_apply_apply, sub_nonneg] using hback

/-- Scalar convexity is derived by applying the domain-aware all-Hilbert
predicate to the actual one-dimensional complex Hilbert space. This consumed
helper supplies the convexity proof used in the curvature construction. -/
theorem convexOn_of_operatorConvexOnAll {f : ℝ → ℝ}
    (hconv : LownerHeinzTheorem.OperatorConvexOnAll.{0} (Ioi 0) f) :
    ConvexOn ℝ (Ioi 0) f := by
  let N := Matrix (Fin 1) (Fin 1) ℂ
  have hm := matrixConvex_of_operatorConvex (f := f) (@hconv) (Fin 1)
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hs (r : ℝ) (hr : 0 < r) : spectrum ℝ (algebraMap ℝ N r) ⊆ Ioi 0 := by
    intro z hz
    have hz' : z = r := CFC.spectrum_algebraMap_subset (A := N) r hz
    simpa only [hz', mem_Ioi] using hr
  have h := hm (A := algebraMap ℝ N x) (B := algebraMap ℝ N y) (t := b)
    (cfc_predicate_algebraMap (R := ℝ) (A := N) x)
    (cfc_predicate_algebraMap (R := ℝ) (A := N) y)
    hb (by linarith) (hs x hx) (hs y hy)
  have he : (1-b) • algebraMap ℝ N x+b • algebraMap ℝ N y =
      algebraMap ℝ N (a*x+b*y) := by
    simp only [Algebra.algebraMap_eq_smul_one, smul_smul, ← add_smul]
    rw [show 1-b = a by linarith]
  change cfc f ((1-b) • algebraMap ℝ N x+b • algebraMap ℝ N y) ≤
    (1-b) • cfc f (algebraMap ℝ N x)+b • cfc f (algebraMap ℝ N y) at h
  rw [he, cfc_algebraMap, cfc_algebraMap, cfc_algebraMap] at h
  have h00 := (Matrix.le_iff.mp h).diag_nonneg (i := 0)
  have hre := (Complex.nonneg_iff.mp h00).1
  simp [N, Algebra.algebraMap_eq_smul_one, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.add_re] at hre
  simpa only [smul_eq_mul, show 1-b = a by linarith] using hre

/-- The original nonaffine operator-convex premise alone supplies both scalar
convexity and the resulting actual full-support curvature. -/
theorem operatorConvex_curvature_full_support {f : ℝ → ℝ}
    (hconv : LownerHeinzTheorem.OperatorConvexOnAll.{0} (Ioi 0) f)
    (nonaffine : ¬ ∃ α β : ℝ, ∀ x ∈ Ioi 0, f x = α*x+β) :
    (D5.S3.Analytic.Convexity.CurvatureHingeRepresentation.curvature
      (convexOn_of_operatorConvexOnAll (f := f) (@hconv))).support = univ := by
  let hf := convexOn_of_operatorConvexOnAll (f := f) (@hconv)
  apply D5.S3.Analytic.Convexity.CurvatureAffineRigidity.full_support_of_affine_rigidity hf
    (fun a b α β ha hab he => affine_of_matrixConvex hf
      (matrixConvex_of_operatorConvex (f := f) (@hconv) (Fin 2)) a b α β ha hab he) nonaffine

#print axioms affine_of_matrixConvex
#print axioms convexOn_of_operatorConvexOnAll
#print axioms operatorConvex_curvature_full_support

end D5.S3.Quantum.Lieb.OperatorConvexCurvature
