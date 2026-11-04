/- GID: D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions
   mirror-E: none(waiver:source-only-positive-theorem)
   anchors: []
   utility: none
   digest: Higher-prime obstructions for actual ideal-intersection Laplacians. -/

import D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport
import D5.S3.Weil.ZetaLinear.Sylvester
import Mathlib.Tactic

/-!
Mathematics attributed to `the-omega-institute/ideal-intersection-laplacian`,
commit `b93becea662a746badeadba42fdc3d3eb3db9382`,
`paper/sections/unit-exponent.tex`. Formal proofs are independently authored.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix Finset
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions

section FiniteGraph
variable {v : Type*} [Fintype v] [DecidableEq v]

/-- A real eigenpair of the standard `D - A` graph Laplacian. -/
def HasLaplacianEigenvalue (G : SimpleGraph v) [DecidableRel G.Adj] (e : ℝ) : Prop :=
  ∃ f : v → ℝ, f ≠ 0 ∧ G.lapMatrix ℝ *ᵥ f = e • f

/-- Laplacian integrality, including every real eigenvalue with a nonzero eigenvector. -/
def LaplacianIntegral (G : SimpleGraph v) [DecidableRel G.Adj] : Prop :=
  ∀ e : ℝ, HasLaplacianEigenvalue G e → ∃ z : ℤ, e = z

private lemma lap_apply_all (G : SimpleGraph v) [DecidableRel G.Adj]
    (f : v → ℝ) (x : v) :
    (G.lapMatrix ℝ *ᵥ f) x = ∑ y, if G.Adj x y then f x - f y else 0 := by
  rw [G.lapMatrix_mulVec_apply']
  have h : G.neighborFinset x = univ.filter (fun y => G.Adj x y) := by
    ext y
    simp
  rw [h, Finset.sum_filter]

private lemma lap_complement_apply (G : SimpleGraph v) [DecidableRel G.Adj]
    (f : v → ℝ) (x : v) :
    (G.lapMatrix ℝ *ᵥ f) x + (Gᶜ.lapMatrix ℝ *ᵥ f) x =
      Fintype.card v * f x - ∑ y, f y := by
  classical
  rw [lap_apply_all, lap_apply_all, ← sum_add_distrib]
  have h : (∑ y, ((if G.Adj x y then f x - f y else 0) +
      if Gᶜ.Adj x y then f x - f y else 0)) = ∑ y, (f x - f y) := by
    apply sum_congr rfl
    intro y _
    by_cases hxy : x = y
    · subst y; simp
    · by_cases ha : G.Adj x y <;> simp [SimpleGraph.compl_adj, hxy, ha]
  rw [h, sum_sub_distrib]
  simp [nsmul_eq_mul]

private lemma eigenpair_sum_zero (G : SimpleGraph v) [DecidableRel G.Adj]
    (e : ℝ) (he : e ≠ 0) (f : v → ℝ) (hf : G.lapMatrix ℝ *ᵥ f = e • f) :
    ∑ x, f x = 0 := by
  have h := Matrix.dotProduct_transpose_mulVec (G.lapMatrix ℝ) f (1 : v → ℝ)
  rw [(G.isSymm_lapMatrix ℝ).eq, G.lapMatrix_mulVec_one_eq_zero ℝ, hf] at h
  simp [dotProduct, Pi.smul_apply, mul_sum] at h
  exact (mul_eq_zero.mp (by simpa only [mul_sum] using h.symm)).resolve_left he

private lemma nonintegral_of_gap (G : SimpleGraph v) [DecidableRel G.Adj]
    (q : ℤ) (e : ℝ) (he : HasLaplacianEigenvalue G e)
    (hl : (q : ℝ) < e) (hu : e < (q : ℝ) + 1) : ¬LaplacianIntegral G := by
  intro h
  obtain ⟨z, hz⟩ := h e he
  rw [hz] at hl hu
  have hl' : q < z := by exact_mod_cast hl
  have hu' : z < q + 1 := by exact_mod_cast hu
  omega

private lemma lap_iso_apply {w : Type*} [Fintype w] [DecidableEq w]
    (G : SimpleGraph v) [DecidableRel G.Adj] (H : SimpleGraph w) [DecidableRel H.Adj]
    (e : G ≃g H) (f : w → ℝ) (x : v) :
    (H.lapMatrix ℝ *ᵥ f) (e x) = (G.lapMatrix ℝ *ᵥ (fun y => f (e y))) x := by
  rw [lap_apply_all, lap_apply_all]
  rw [← e.toEquiv.sum_comp (fun y => if H.Adj (e x) y then f (e x) - f y else 0)]
  apply sum_congr rfl
  intro y _
  change (if H.Adj (e x) (e y) then _ else _) = _
  simp only [e.map_adj_iff]
  rfl

private lemma hasEigenvalue_iso {w : Type*} [Fintype w] [DecidableEq w]
    (G : SimpleGraph v) [DecidableRel G.Adj] (H : SimpleGraph w) [DecidableRel H.Adj]
    (e : G ≃g H) (c : ℝ) (hc : HasLaplacianEigenvalue H c) :
    HasLaplacianEigenvalue G c := by
  obtain ⟨f, hf, he⟩ := hc
  refine ⟨fun y => f (e y), ?_, ?_⟩
  · intro h
    apply hf
    ext y
    have hh := congrFun h (e.symm y)
    simpa only [e.apply_symm_apply, Pi.zero_apply] using hh
  · ext x
    rw [← lap_iso_apply G H e f x, he]
    rfl

private lemma star_lap_action (G : SimpleGraph v) [DecidableRel G.Adj]
    (c : v) (L : Finset v) (hc : c ∉ L)
    (hG : ∀ x y, G.Adj x y ↔ (x=c ∧ y∈L) ∨ (y=c ∧ x∈L))
    (f : v → ℝ) (x : v) :
    (G.lapMatrix ℝ *ᵥ f) x =
      if x=c then ∑ y ∈ L, (f c-f y) else if x∈L then f x-f c else 0 := by
  classical
  rw [lap_apply_all]
  by_cases hx : x=c
  · subst x
    simp only [hG, true_and, hc, and_false, or_false, ite_true]
    have h : (univ : Finset v).filter (fun y => y ∈ L) = L := by ext y; simp
    rw [← sum_filter, h]
  · simp only [hG, hx, false_and, false_or, ite_false]
    by_cases hL : x∈L <;> simp [hL]

private lemma star_eigenvalues (G : SimpleGraph v) [DecidableRel G.Adj]
    (c : v) (L : Finset v) (hc : c ∉ L)
    (hG : ∀ x y, G.Adj x y ↔ (x=c ∧ y∈L) ∨ (y=c ∧ x∈L))
    (e : ℝ) (he : HasLaplacianEigenvalue G e) :
    e = 0 ∨ e = 1 ∨ e = (L.card : ℝ)+1 := by
  classical
  obtain ⟨f,hf,he⟩ := he
  by_contra h
  push_neg at h
  obtain ⟨h0,h1,hA⟩ := h
  have hleaf (x : v) (hx : x ∈ L) : (1-e)*f x = f c := by
    have hh := congrFun he x
    rw [star_lap_action G c L hc hG] at hh
    have hxc : x ≠ c := fun he => hc (he ▸ hx)
    simp only [hxc, ite_false, hx, ite_true, Pi.smul_apply, smul_eq_mul] at hh
    linarith
  have hcenter : ((L.card : ℝ)-e)*f c = ∑ x ∈ L, f x := by
    have hh := congrFun he c
    rw [star_lap_action G c L hc hG] at hh
    simp only [ite_true, sum_sub_distrib, sum_const, nsmul_eq_mul,
      Pi.smul_apply, smul_eq_mul] at hh
    linarith
  have hsum : (1-e)*(∑ x ∈ L, f x) = (L.card : ℝ)*f c := by
    calc
      (1-e)*(∑ x ∈ L, f x) = ∑ x ∈ L, (1-e)*f x := mul_sum ..
      _ = ∑ _x ∈ L, f c := sum_congr rfl (fun x hx => hleaf x hx)
      _ = (L.card : ℝ)*f c := by simp
  have hfac : e*(e-((L.card : ℝ)+1))*f c = 0 := by
    rw [← hcenter] at hsum
    nlinarith [hsum]
  have hfc : f c = 0 := by
    exact (mul_eq_zero.mp hfac).resolve_left (mul_ne_zero h0 (sub_ne_zero.mpr hA))
  apply hf
  ext x
  by_cases hx : x=c
  · simpa [hx] using hfc
  by_cases hL : x∈L
  · have hh := hleaf x hL
    rw [hfc] at hh
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr (Ne.symm h1))
  · have hh := congrFun he x
    rw [star_lap_action G c L hc hG] at hh
    simp only [hx, ite_false, hL, Pi.smul_apply, smul_eq_mul] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left h0

end FiniteGraph

section TrialSpectrum
variable {v : Type*} [Fintype v] [DecidableEq v]

private lemma positive_eigenpair_below_of_trial
    (A : Matrix v v ℝ) (hA : A.IsHermitian) (hP : A.PosSemidef)
    (c : ℝ) (f : v → ℝ)
    (horth : ∀ z : v → ℝ, A *ᵥ z = 0 → dotProduct z f = 0)
    (htrial : dotProduct f (A *ᵥ f) ≤ c * dotProduct f f)
    (hstrict : dotProduct f (A *ᵥ f) < c * dotProduct f f ∨ A *ᵥ f ≠ c • f) :
    ∃ e : ℝ, 0 < e ∧ e < c ∧ ∃ z : v → ℝ, z ≠ 0 ∧ A *ᵥ z = e • z := by
  classical
  suffices hh : ∃ i, 0 < hA.eigenvalues i ∧ hA.eigenvalues i < c by
    obtain ⟨i, hi, hic⟩ := hh
    exact ⟨hA.eigenvalues i, hi, hic, _,
      (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero i),
      hA.mulVec_eigenvectorBasis i⟩
  by_contra! hno
  let U : Matrix v v ℝ := hA.eigenvectorUnitary
  let d : v → ℝ := star U *ᵥ f
  have hd0 (i : v) (hi : hA.eigenvalues i = 0) : d i = 0 := by
    have he := hA.mulVec_eigenvectorBasis i
    rw [hi, zero_smul] at he
    have hh := horth _ he
    simpa [d, U, mulVec, dotProduct, Matrix.star_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using hh
  have hform : dotProduct f (A *ᵥ f) = ∑ i, hA.eigenvalues i * (d i)^2 := by
    have hh := RHLinalg.hermForm_specMap hA id f
    rw [RHLinalg.specMap_id] at hh
    simpa [d, U, RHLinalg.hermForm, Real.norm_eq_abs, sq_abs] using hh
  have hnorm : dotProduct f f = ∑ i, (d i)^2 := by
    have hh := RHLinalg.sum_normSq_unitary_mulVec hA f
    simpa [d, U, dotProduct, Real.norm_eq_abs, sq_abs, pow_two] using hh.symm
  have hnn (i : v) : 0 ≤ (hA.eigenvalues i - c) * (d i)^2 := by
    by_cases hi : hA.eigenvalues i = 0
    · rw [hd0 i hi]; simp
    · have hp : 0 < hA.eigenvalues i := (hP.eigenvalues_nonneg i).lt_of_ne' hi
      exact mul_nonneg (sub_nonneg.mpr (hno i hp)) (sq_nonneg _)
  have hsum : (∑ i, (hA.eigenvalues i - c) * (d i)^2) = 0 := by
    apply le_antisymm
    · rw [hform, hnorm, mul_sum] at htrial
      simpa only [sub_mul, sum_sub_distrib] using sub_nonpos.mpr htrial
    · exact sum_nonneg (fun i _ => hnn i)
  have hpoint (i : v) : hA.eigenvalues i * d i = c * d i := by
    have hi := (sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).mp hsum i (mem_univ i)
    rcases mul_eq_zero.mp hi with he | hd
    · have heq := sub_eq_zero.mp he
      rw [heq]
    · have hd' : d i = 0 := (sq_eq_zero_iff).mp hd
      rw [hd']; simp
  have heig : A *ᵥ f = c • f := by
    have hf : U *ᵥ d = f := by
      dsimp [d]
      rw [mulVec_mulVec, Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2,
        one_mulVec]
    have hdiag : diagonal (hA.eigenvalues) *ᵥ d = c • d := by
      ext i
      simpa only [mulVec_diagonal, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] using hpoint i
    calc
      A *ᵥ f = (U * diagonal (hA.eigenvalues) * star U) *ᵥ f := by
        apply congrArg (fun M : Matrix v v ℝ => M *ᵥ f)
        simpa [U, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
      _ = U *ᵥ (diagonal (hA.eigenvalues) *ᵥ d) := by
        simp only [← mulVec_mulVec, d]
      _ = c • f := by rw [hdiag, mulVec_smul, hf]
  rcases hstrict with hlt | hne
  · have hh : dotProduct f (A *ᵥ f) = c * dotProduct f f := by
      rw [heig, dotProduct_smul, smul_eq_mul]
    linarith
  · exact hne heig

end TrialSpectrum

section WeightedSupports
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma sum_supportWeight (k : ι → ℕ) :
    (∑ S : Finset ι, supportWeight k S) = ∏ i, ((k i : ℝ) + 1) := by
  simpa [supportWeight] using
    (Finset.prod_add_one (f := fun i => (k i : ℝ)) (univ : Finset ι)).symm

private lemma sum_supportWeight_subset (k : ι → ℕ) (J : Finset ι) :
    (∑ S : Finset ι, if S ⊆ J then supportWeight k S else 0) =
      ∏ i ∈ J, ((k i : ℝ) + 1) := by
  classical
  have h : (univ : Finset (Finset ι)).filter (fun S => S ⊆ J) = J.powerset := by
    ext S
    simp
  rw [← Finset.sum_filter, h]
  exact (Finset.prod_add_one J).symm

private lemma subset_erase_univ (d : ι) (S : Finset ι) :
    S ⊆ univ.erase d ↔ d ∉ S := by
  constructor
  · intro h hd
    exact (mem_erase.mp (h hd)).1 rfl
  · intro h i hi
    exact mem_erase.mpr ⟨fun he => h (he ▸ hi), mem_univ i⟩

private lemma sum_supportWeight_omit (k : ι → ℕ) (d : ι) :
    (∑ S : Finset ι, if d ∉ S then supportWeight k S else 0) =
      ∏ i ∈ univ.erase d, ((k i : ℝ) + 1) := by
  simpa only [subset_erase_univ] using sum_supportWeight_subset k (univ.erase d)

private def trialCells (d : ι) (x y r₀ r₁ : ℝ) (S : Finset ι) : ℝ :=
  if S = ∅ ∨ S = univ then 0 else
  if S = univ.erase d then x else if S = {d} then y else
  if d ∈ S then r₁ else r₀

private lemma erase_univ_nonempty [Nontrivial ι] (d : ι) :
    (univ.erase d : Finset ι).Nonempty := by
  obtain ⟨i, hi⟩ := exists_ne d
  exact ⟨i, mem_erase.mpr ⟨hi, mem_univ i⟩⟩

private lemma trialCells_expansion [Nontrivial ι] (d : ι)
    (x y r₀ r₁ : ℝ) (S : Finset ι) :
    trialCells d x y r₀ r₁ S = r₁ + (if d ∉ S then r₀-r₁ else 0) +
      (if S = ∅ then -r₀ else 0) + (if S = univ then -r₁ else 0) +
      (if S = univ.erase d then x-r₀ else 0) + (if S = {d} then y-r₁ else 0) := by
  classical
  have hdJ : d ∉ (univ.erase d : Finset ι) := notMem_erase d univ
  have hJ0 := (erase_univ_nonempty d).ne_empty
  have hU0 : (univ : Finset ι) ≠ ∅ := Finset.univ_nonempty.ne_empty
  have hJu : (univ.erase d : Finset ι) ≠ univ := by
    intro h
    have := h ▸ (notMem_erase d (univ : Finset ι))
    exact this (mem_univ d)
  have hZu : ({d} : Finset ι) ≠ univ := by
    intro h
    obtain ⟨i, hi⟩ := erase_univ_nonempty d
    have hid := (mem_erase.mp hi).1
    have him : i ∈ ({d} : Finset ι) := h.symm ▸ mem_univ i
    exact hid (mem_singleton.mp him)
  have hJZ : (univ.erase d : Finset ι) ≠ {d} := by
    intro h
    exact hdJ (by rw [h]; exact mem_singleton_self d)
  by_cases h0 : S = ∅
  · subst S
    simp [trialCells, hJ0, hJ0.symm, hU0, hU0.symm]
    <;> ring
  by_cases hu : S = univ
  · subst S
    simp [trialCells, hJu, hJu.symm, hZu, hZu.symm, hU0, hU0.symm]
  by_cases hJ : S = univ.erase d
  · subst S
    simp [trialCells, hJ0, hJu, hJZ]
    <;> ring
  by_cases hZ : S = {d}
  · subst S
    simp [trialCells, hZu, hJZ, hJZ.symm]
    <;> ring
  by_cases hd : d ∈ S <;>
    simp [trialCells, h0, hu, hJ, hZ, hd] <;> ring

private lemma sum_trialCells [Nontrivial ι] (k : ι → ℕ) (d : ι)
    (x y r₀ r₁ : ℝ) :
    (∑ S : Finset ι, supportWeight k S * trialCells d x y r₀ r₁ S) =
      (∏ i ∈ univ.erase d, (k i : ℝ))*x + (k d : ℝ)*y +
      ((∏ i ∈ univ.erase d, ((k i : ℝ)+1))-1-
        (∏ i ∈ univ.erase d, (k i : ℝ)))*r₀ +
      (k d : ℝ)*((∏ i ∈ univ.erase d, ((k i : ℝ)+1))-1-
        (∏ i ∈ univ.erase d, (k i : ℝ)))*r₁ := by
  classical
  simp_rw [trialCells_expansion, mul_add]
  simp only [sum_add_distrib]
  have ho : (∑ S : Finset ι, supportWeight k S *
      (if d ∉ S then r₀-r₁ else 0)) =
      (∏ i ∈ univ.erase d, ((k i : ℝ)+1))*(r₀-r₁) := by
    rw [← sum_supportWeight_omit k d, sum_mul]
    apply sum_congr rfl
    intro S _
    split_ifs <;> simp
  rw [ho, ← sum_mul, sum_supportWeight]
  simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true, supportWeight,
    prod_empty, prod_singleton, one_mul]
  have hw : (∏ i, (k i : ℝ)) = (k d : ℝ) * ∏ i ∈ univ.erase d, (k i : ℝ) := by
    exact (Finset.mul_prod_erase _ _ (mem_univ d)).symm
  have ht : (∏ i, ((k i : ℝ)+1)) = ((k d : ℝ)+1) *
      ∏ i ∈ univ.erase d, ((k i : ℝ)+1) := by
    exact (Finset.mul_prod_erase _ _ (mem_univ d)).symm
  rw [hw, ht]
  ring

private lemma disjoint_erase_univ (d : ι) (S : Finset ι) (hS : S.Nonempty) :
    Disjoint S (univ.erase d) ↔ S = {d} := by
  constructor
  · intro h
    apply subset_antisymm
    · intro i hi
      apply mem_singleton.mpr
      by_contra hid
      exact Finset.disjoint_left.mp h hi (mem_erase.mpr ⟨hid, mem_univ i⟩)
    · obtain ⟨i, hi⟩ := hS
      have hid : i = d := by
        by_contra hid
        exact Finset.disjoint_left.mp h hi (mem_erase.mpr ⟨hid, mem_univ i⟩)
      simpa [hid] using hi
  · intro h
    subst S
    exact Finset.disjoint_singleton_left.mpr (notMem_erase d univ)

private lemma support_trial_action [Nontrivial ι] (k : ι → ℕ) (d : ι)
    (x y z : ℝ) (S : Finset ι) (hS : S.Nonempty) :
    supportComplementOp k (trialCells d x y z z) S =
      trialCells d
        ((k d : ℝ)*(x-y))
        ((∏ i ∈ univ.erase d, (k i : ℝ))*(y-x) +
          ((∏ i ∈ univ.erase d, ((k i : ℝ)+1))-1-
            (∏ i ∈ univ.erase d, (k i : ℝ)))*(y-z))
        ((k d : ℝ)*(z-y)) 0 S := by
  classical
  let J : Finset ι := univ.erase d
  have hJe : J = univ.erase d := rfl
  have hdJ : d ∉ J := by simp [J]
  have hU0 : (univ : Finset ι) ≠ ∅ := Finset.univ_nonempty.ne_empty
  let A : ℝ := supportWeight k J
  let m : ℝ := k d
  let P : ℝ := ∏ i ∈ J, ((k i : ℝ)+1)
  have hJ0 : J ≠ ∅ := (erase_univ_nonempty d).ne_empty
  have hJu : J ≠ univ := by
    intro h
    exact hdJ (by rw [h]; exact mem_univ d)
  have hZu : ({d} : Finset ι) ≠ univ := by
    intro h
    obtain ⟨i, hi⟩ := erase_univ_nonempty d
    exact (mem_erase.mp hi).1 (mem_singleton.mp (h.symm ▸ mem_univ i))
  have hJZ : J ≠ {d} := by
    intro h
    exact hdJ (by rw [h]; exact mem_singleton_self d)
  have hSu : S = univ ∨ S ≠ univ := em _
  rcases hSu with hSu | hSu
  · subst S
    have hz : supportComplementOp k (trialCells d x y z z) univ = 0 := by
      unfold supportComplementOp
      apply sum_eq_zero
      intro T _
      split_ifs with h
      · obtain ⟨i, hi⟩ := h.1
        exact False.elim (Finset.disjoint_left.mp h.2.2 (mem_univ i) hi)
      · rfl
    rw [hz]
    simp [trialCells]
  have hdisu : ¬Disjoint S (univ : Finset ι) := by
    intro h
    obtain ⟨i, hi⟩ := hS
    exact Finset.disjoint_left.mp h hi (mem_univ i)
  let f := trialCells d x y z z
  have hpoint (T : Finset ι) :
      (if T.Nonempty ∧ T ≠ univ ∧ Disjoint S T then
        supportWeight k T * (f S-f T) else 0) =
      (if Disjoint S T then supportWeight k T*(f S-z) else 0) -
      (if T = ∅ then f S-z else 0) -
      (if T = J then if Disjoint S J then A*(x-z) else 0 else 0) -
      (if T = {d} then if d ∉ S then m*(y-z) else 0 else 0) := by
    by_cases h0 : T = ∅
    · subst T
      simp [supportWeight, J, hJ0, hJ0.symm]
    by_cases hu : T = univ
    · subst T
      simp [hdisu, hJu, hJu.symm, hZu, hZu.symm, hU0]
    by_cases hJ : T = J
    · subst T
      have hn : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hJ0
      by_cases hd : Disjoint S J <;>
        simp [f, trialCells, ← hJe, hn, hJ0, hJu, hJZ, hd, A] <;> ring
    by_cases hZ : T = {d}
    · subst T
      by_cases hd : d ∈ S <;>
        simp [f, trialCells, ← hJe, hZu, hJZ, hJZ.symm, h0, hu, hJ,
          Finset.disjoint_singleton_right, hd, supportWeight, m] <;> ring
    have hn : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
    by_cases hd : Disjoint S T <;>
      simp [f, trialCells, ← hJe, h0, hu, hJ, hZ, hn, hd]
  have hsum : supportComplementOp k f S =
      ((∑ T : Finset ι, if Disjoint S T then supportWeight k T else 0)-1)*(f S-z) -
      (if Disjoint S J then A*(x-z) else 0) -
      (if d ∉ S then m*(y-z) else 0) := by
    unfold supportComplementOp
    simp_rw [hpoint]
    rw [sum_sub_distrib, sum_sub_distrib, sum_sub_distrib]
    simp only [sum_ite_eq', mem_univ, if_true]
    have he : (∑ T : Finset ι, if Disjoint S T then supportWeight k T*(f S-z) else 0) =
        (∑ T : Finset ι, if Disjoint S T then supportWeight k T else 0)*(f S-z) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro T _
      split_ifs <;> simp
    rw [he]
    ring
  change supportComplementOp k f S = trialCells d (m*(x-y))
    (A*(y-x)+(P-1-A)*(y-z)) (m*(z-y)) 0 S
  rw [hsum]
  by_cases hSJ : S = J
  · subst S
    have hD : (∑ T : Finset ι, if Disjoint J T then supportWeight k T else 0) = m+1 := by
      have hh (T : Finset ι) : Disjoint J T ↔ T ⊆ {d} := by
        rw [disjoint_comm]
        constructor
        · intro h i hi
          by_contra hid
          exact Finset.disjoint_left.mp h hi (mem_erase.mpr ⟨by simpa using hid, mem_univ i⟩)
        · intro h
          exact Finset.disjoint_left.mpr (fun i hi hiJ =>
            (mem_erase.mp hiJ).1 (mem_singleton.mp (h hi)))
      simp_rw [hh]
      simpa [m] using sum_supportWeight_subset k {d}
    have hn := Finset.nonempty_iff_ne_empty.mpr hJ0
    have hdd : ¬Disjoint J J := by simpa using hJ0
    simp only [hD]
    simp [f, trialCells, ← hJe, hJ0, hJu, hJZ, hdd, hdJ]
    <;> ring
  by_cases hSZ : S = {d}
  · subst S
    have hD : (∑ T : Finset ι, if Disjoint ({d} : Finset ι) T then supportWeight k T else 0) = P := by
      simpa [P, J] using sum_supportWeight_omit k d
    have hd : Disjoint ({d} : Finset ι) J :=
      Finset.disjoint_singleton_left.mpr (notMem_erase d univ)
    simp only [hD]
    simp [hd, f, trialCells, ← hJe, hZu, hJZ, hJZ.symm, hdJ]
    <;> ring
  have hdisJ : ¬Disjoint S J := by
    simpa [J, disjoint_erase_univ d S hS] using hSZ
  by_cases hd : d ∈ S <;>
    simp [f, trialCells, ← hJe, hS.ne_empty, hSu, hSJ, hSZ, hd, hdisJ] <;> ring

private lemma support_kernel_orthogonal [Nontrivial ι] (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) (f : Finset ι → ℝ) (hu : f univ = 0)
    (hsum : ∑ e : BoxVertex k, supportLift k f e = 0)
    (z : BoxVertex k → ℝ) (hz : (supportGraph k)ᶜ.lapMatrix ℝ *ᵥ z = 0) :
    dotProduct z (supportLift k f) = 0 := by
  classical
  have hc := activeComplement_connected k hk
  let a : ActiveVertex k := Classical.choice hc.nonempty
  have he (e : BoxVertex k) : z e * supportLift k f e = z a.1 * supportLift k f e := by
    by_cases hu' : support e.1 = univ
    · simp [supportLift, hu', hu]
    · have hr := hc ⟨e, hu'⟩ a
      have hm := hr.map (SimpleGraph.Embedding.induce
        {e : BoxVertex k | support e.1 ≠ univ}).toHom
      have hh := ((SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable (supportGraph k)ᶜ).mp hz) e a.1 hm
      rw [hh]
  unfold dotProduct
  simp_rw [he]
  rw [← mul_sum, hsum, mul_zero]

private lemma trialCells_mul (d : ι) (x y r₀ r₁ x' y' s₀ s₁ : ℝ) (S : Finset ι) :
    trialCells d x y r₀ r₁ S * trialCells d x' y' s₀ s₁ S =
      trialCells d (x*x') (y*y') (r₀*s₀) (r₁*s₁) S := by
  unfold trialCells
  split_ifs <;> simp

private lemma trialCells_zero (d : ι) (x y r₀ r₁ : ℝ) :
    trialCells d x y r₀ r₁ ∅ = 0 ∧ trialCells d x y r₀ r₁ univ = 0 := by
  simp [trialCells]

private lemma trial_mean_square_energy [Nontrivial ι] (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) (d : ι) (x y z : ℝ) :
    let A := ∏ i ∈ univ.erase d, (k i : ℝ)
    let B := (∏ i ∈ univ.erase d, ((k i : ℝ)+1))-1-A
    let m := (k d : ℝ)
    let f := supportLift k (trialCells d x y z z)
    (∑ e, f e) = A*x+m*y+(m+1)*B*z ∧
    dotProduct f f = A*x^2+m*y^2+(m+1)*B*z^2 ∧
    dotProduct f ((supportGraph k)ᶜ.lapMatrix ℝ *ᵥ f) =
      m*A*(x-y)^2+m*B*(y-z)^2 := by
  classical
  dsimp only
  let A := ∏ i ∈ univ.erase d, (k i : ℝ)
  let B := (∏ i ∈ univ.erase d, ((k i : ℝ)+1))-1-A
  let m := (k d : ℝ)
  have hm := support_lift_sum k hk (trialCells d x y z z)
    (trialCells_zero d x y z z).1 (trialCells_zero d x y z z).2
  rw [sum_trialCells] at hm
  refine ⟨?_, ?_, ?_⟩
  · simp only [supportLift] at hm ⊢
    rw [hm]
    ring
  · have hs := support_lift_sum k hk (trialCells d (x*x) (y*y) (z*z) (z*z))
      (trialCells_zero d (x*x) (y*y) (z*z) (z*z)).1
      (trialCells_zero d (x*x) (y*y) (z*z) (z*z)).2
    rw [sum_trialCells] at hs
    unfold dotProduct
    simp_rw [supportLift, trialCells_mul]
    rw [hs]
    ring
  · have hs := support_lift_sum k hk
      (trialCells d (x*(m*(x-y))) (y*(A*(y-x)+B*(y-z))) (z*(m*(z-y))) 0)
      (trialCells_zero d _ _ _ _).1 (trialCells_zero d _ _ _ _).2
    rw [sum_trialCells] at hs
    unfold dotProduct
    have he (e : BoxVertex k) :
        supportLift k (trialCells d x y z z) e *
          ((supportGraph k)ᶜ.lapMatrix ℝ *ᵥ supportLift k (trialCells d x y z z)) e =
        trialCells d (x*(m*(x-y))) (y*(A*(y-x)+B*(y-z)))
          (z*(m*(z-y))) 0 (support e.1) := by
      rw [support_complement_intertwining k hk,
        support_trial_action k d x y z _ (support_nonempty k e)]
      simpa only [supportLift, A, B, m, mul_zero] using
        trialCells_mul d x y z z (m*(x-y)) (A*(y-x)+B*(y-z)) (m*(z-y)) 0 (support e.1)
    simp_rw [he]
    rw [hs]
    dsimp [A, B, m]
    ring

private lemma other_weight_positive (k : ι → ℕ) (hk : ∀ i, 0 < k i) (d : ι) :
    0 < ∏ i ∈ univ.erase d, (k i : ℝ) :=
  Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (hk i))

private lemma remaining_weight_positive [Nontrivial ι] (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) (d i j : ι) (hid : i ≠ d) (hjd : j ≠ d) (hij : i ≠ j) :
    0 < (∏ i ∈ univ.erase d, ((k i : ℝ)+1))-1-
      (∏ i ∈ univ.erase d, (k i : ℝ)) := by
  have hS0 : ({i} : Finset ι) ≠ ∅ := (Finset.singleton_nonempty i).ne_empty
  have hSu : ({i} : Finset ι) ≠ univ := by
    intro h
    exact hid ((mem_singleton.mp (h.symm ▸ mem_univ d)).symm)
  have hSJ : ({i} : Finset ι) ≠ univ.erase d := by
    intro h
    have hj : j ∈ ({i} : Finset ι) := h.symm ▸ mem_erase.mpr ⟨hjd, mem_univ j⟩
    exact hij (mem_singleton.mp hj).symm
  have hSZ : ({i} : Finset ι) ≠ {d} := by
    simpa using hid
  have hs := sum_trialCells k d 0 0 1 0
  simp only [mul_zero, zero_add, mul_one, add_zero] at hs
  rw [← hs]
  apply Finset.sum_pos'
  · intro S _
    apply mul_nonneg (Finset.prod_nonneg (fun l _ => Nat.cast_nonneg _))
    unfold trialCells
    split_ifs <;> norm_num
  · refine ⟨{i}, mem_univ _, ?_⟩
    simpa [trialCells, hS0, hSu, hSJ, hSZ, hid, Ne.symm hid, supportWeight] using
      (Nat.cast_pos.mpr (hk i) : (0 : ℝ) < k i)

private lemma h2_trial_algebra (A B m : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hm : 1 ≤ m) (hthreshold : (m^2-1)*B-(m-1) ≤ A) :
    let x := m*(m+1)*B
    let y := (m-1)*(m+1)*B
    let z := -m*(A+m-1)
    A*x+m*y+(m+1)*B*z = 0 ∧ z ≠ 0 ∧
      m*A*(x-y)^2+m*B*(y-z)^2 ≤ A*x^2+m*y^2+(m+1)*B*z^2 := by
  dsimp only
  have hm0 : 0 < m := by linarith
  have hz : -m*(A+m-1) < 0 := by
    have ha : 0 < A+m-1 := by linarith
    nlinarith [mul_pos hm0 ha]
  refine ⟨by ring, hz.ne, ?_⟩
  have ht : (m^2-1)*B-A-(m-1) ≤ 0 := by linarith
  have hfac : 0 ≤ m*A+(m^2-1)*B+m*(m-1) := by
    have hs : 0 ≤ m^2-1 := by nlinarith
    positivity
  have hprod := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg hm0.le hB.le) (mul_nonpos_of_nonpos_of_nonneg ht hfac)
  nlinarith [show
    m*A*(m*(m+1)*B-(m-1)*(m+1)*B)^2 +
      m*B*((m-1)*(m+1)*B- -m*(A+m-1))^2 -
      (A*(m*(m+1)*B)^2+m*((m-1)*(m+1)*B)^2+(m+1)*B*(-m*(A+m-1))^2) =
      m*B*((m^2-1)*B-A-(m-1))*(m*A+(m^2-1)*B+m*(m-1)) by ring]

private lemma trial_not_eigenvector [Nontrivial ι] (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (d i j : ι) (hid : i ≠ d) (hjd : j ≠ d) (hij : i ≠ j)
    (x y z : ℝ) (hz : z ≠ 0) :
    (supportGraph k)ᶜ.lapMatrix ℝ *ᵥ supportLift k (trialCells d x y z z) ≠
      supportLift k (trialCells d x y z z) := by
  classical
  let S : Finset ι := {d, i}
  have hS : S.Nonempty := by simp [S]
  have hSu : S ≠ univ := by
    intro h
    have hj : j ∈ S := h.symm ▸ mem_univ j
    simp only [S, mem_insert, mem_singleton] at hj
    exact hj.elim hjd (fun he => hij he.symm)
  have hSJ : S ≠ univ.erase d := by
    intro h
    have hd : d ∈ S := by simp [S]
    rw [h] at hd
    exact notMem_erase d univ hd
  have hSZ : S ≠ {d} := by
    intro h
    have hi : i ∈ S := by simp [S]
    rw [h] at hi
    exact hid (mem_singleton.mp hi)
  have hf : trialCells d x y z z S = z := by
    simp [trialCells, hS.ne_empty, hSu, hSJ, hSZ, S]
  have hzero : supportComplementOp k (trialCells d x y z z) S = 0 := by
    rw [support_trial_action k d x y z S hS]
    simp [trialCells, hS.ne_empty, hSu, hSJ, hSZ, S]
  have hn : Nonempty {e : BoxVertex k // support e.1 = S} := by
    apply Fintype.card_pos_iff.mp
    rw [← Nat.card_eq_fintype_card, vertex_support_fiber_card k hk S hS hSu]
    exact Finset.prod_pos (fun i _ => hk i)
  obtain ⟨e⟩ := hn
  intro he
  have hh := congrFun he e.1
  rw [support_complement_intertwining k hk, e.2, hzero] at hh
  exact hz (by simpa [supportLift, e.2, hf] using hh.symm)

private lemma threshold_complement_low_eigenpair [Nontrivial ι]
    (k : ι → ℕ) (hk : ∀ i, 0 < k i) (d i j : ι)
    (hid : i ≠ d) (hjd : j ≠ d) (hij : i ≠ j)
    (hthreshold :
      (((k d : ℝ)^2-1)*((∏ i ∈ univ.erase d, ((k i : ℝ)+1))-1-
        (∏ i ∈ univ.erase d, (k i : ℝ)))-((k d : ℝ)-1)) ≤
        ∏ i ∈ univ.erase d, (k i : ℝ)) :
    ∃ e : ℝ, 0 < e ∧ e < 1 ∧
      HasLaplacianEigenvalue (supportGraph k)ᶜ e := by
  classical
  let A : ℝ := ∏ i ∈ univ.erase d, (k i : ℝ)
  let B : ℝ := (∏ i ∈ univ.erase d, ((k i : ℝ)+1))-1-A
  let m : ℝ := k d
  let x := m*(m+1)*B
  let y := (m-1)*(m+1)*B
  let z := -m*(A+m-1)
  let f := supportLift k (trialCells d x y z z)
  have hA := other_weight_positive k hk d
  have hB := remaining_weight_positive k hk d i j hid hjd hij
  have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast hk d
  have ha := h2_trial_algebra A B m hA hB hm hthreshold
  dsimp only at ha
  obtain ⟨hmean, hz, henergy⟩ := ha
  have ht := trial_mean_square_energy k hk d x y z
  change (∑ e, f e) = A*x+m*y+(m+1)*B*z ∧
    dotProduct f f = A*x^2+m*y^2+(m+1)*B*z^2 ∧
    dotProduct f ((supportGraph k)ᶜ.lapMatrix ℝ *ᵥ f) =
      m*A*(x-y)^2+m*B*(y-z)^2 at ht
  have hsum : ∑ e, f e = 0 := ht.1.trans hmean
  have he := positive_eigenpair_below_of_trial ((supportGraph k)ᶜ.lapMatrix ℝ)
    ((supportGraph k)ᶜ.posSemidef_lapMatrix ℝ).1
    ((supportGraph k)ᶜ.posSemidef_lapMatrix ℝ) 1 f
    (support_kernel_orthogonal k hk (trialCells d x y z z)
      (trialCells_zero d x y z z).2 hsum)
    (by rw [ht.2.1, ht.2.2, one_mul]; exact henergy)
    (Or.inr (by
      simpa only [one_smul] using trial_not_eigenvector k hk d i j hid hjd hij x y z hz))
  exact he

private lemma one_sub_sum_mul_prod_le_one (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    (1-∑ i ∈ s, x i)*(∏ i ∈ s, (1+x i)) ≤ 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    have ha := hx a (mem_insert_self _ _)
    have hs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (mem_insert_of_mem hi)
    have hsum : 0 ≤ ∑ i ∈ s, x i := sum_nonneg hs
    have hprod : 0 ≤ ∏ i ∈ s, (1+x i) := prod_nonneg (fun i hi => by linarith [hs i hi])
    rw [sum_insert has, prod_insert has]
    calc
      (1-(x a+∑ i ∈ s, x i))*((1+x a)*∏ i ∈ s, (1+x i)) =
        (1-∑ i ∈ s, x i)*(∏ i ∈ s, (1+x i)) -
          (x a*(∑ i ∈ s, x i)+(x a)^2)*(∏ i ∈ s, (1+x i)) := by ring
      _ ≤ (1-∑ i ∈ s, x i)*(∏ i ∈ s, (1+x i)) := by
        exact sub_le_self _ (mul_nonneg (add_nonneg (mul_nonneg ha hsum) (sq_nonneg _)) hprod)
      _ ≤ 1 := ih hs

private lemma reciprocal_implies_threshold (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (d : ι) (hm : 2 ≤ k d)
    (hs : (∑ i ∈ univ.erase d, 1/(k i : ℝ)) ≤ 1/(k d : ℝ)^2) :
    (((k d : ℝ)^2-1)*((∏ i ∈ univ.erase d, ((k i : ℝ)+1))-1-
      (∏ i ∈ univ.erase d, (k i : ℝ)))-((k d : ℝ)-1)) ≤
      ∏ i ∈ univ.erase d, (k i : ℝ) := by
  let J : Finset ι := univ.erase d
  let A : ℝ := ∏ i ∈ J, (k i : ℝ)
  let P : ℝ := ∏ i ∈ J, ((k i : ℝ)+1)
  let m : ℝ := k d
  have hA : 0 < A := other_weight_positive k hk d
  have hP : 0 < P := prod_pos (fun i _ => by have := hk i; positivity)
  have hm2 : 2 ≤ m := by dsimp [m]; exact_mod_cast hm
  have hm0 : 0 < m := by linarith
  have hmsq : 0 < m^2 := sq_pos_of_pos hm0
  have hp := one_sub_sum_mul_prod_le_one J (fun i => 1/(k i : ℝ))
    (fun i _ => by positivity)
  have he : (∏ i ∈ J, (1+1/(k i : ℝ))) = P/A := by
    dsimp [P, A]
    rw [← prod_div_distrib]
    apply prod_congr rfl
    intro i _
    have hki : (k i : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hk i)).ne'
    field_simp
    <;> ring
  rw [he] at hp
  have hbound : (1-1/m^2)*(P/A) ≤ 1 := by
    calc
      _ ≤ (1-∑ i ∈ J, 1/(k i : ℝ))*(P/A) :=
        mul_le_mul_of_nonneg_right (by dsimp [J,m]; linarith) (div_nonneg hP.le hA.le)
      _ ≤ 1 := hp
  have hmain : (m^2-1)*P ≤ m^2*A := by
    have hh := mul_le_mul_of_nonneg_right hbound (mul_nonneg hmsq.le hA.le)
    have heq : ((1-1/m^2)*(P/A))*(m^2*A) = (m^2-1)*P := by
      field_simp [hA.ne', hm0.ne']
      <;> ring
    rw [heq] at hh
    nlinarith
  change (m^2-1)*(P-1-A)-(m-1) ≤ A
  nlinarith

end WeightedSupports

section ActualGraph
open D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport

/-- Canonical finite enumeration of the actual nonzero proper ideals.
Finiteness comes from their underlying subsets of the finite ring. -/
private def actualVertexFintype (n : ℕ) (hn : n ≠ 0) : Fintype (Vertex n) := by
  letI : NeZero n := ⟨hn⟩
  letI : Fintype (Ideal (ZMod n)) :=
    Fintype.ofInjective (fun I : Ideal (ZMod n) => (I : Set (ZMod n))) SetLike.coe_injective
  exact inferInstance

/-- A nonzero eigenvector of the `D-A` Laplacian on actual nonzero proper ideals.
The finite enumeration is constructed from the nonzero modulus; no graph model
or spectral transport is assumed in this definition. -/
def HasActualEigenvalue (n : ℕ) (e : ℝ) : Prop :=
  ∃ hn : n ≠ 0,
    letI : Fintype (Vertex n) := actualVertexFintype n hn
    HasLaplacianEigenvalue (graph n) e

/-- Integrality of every real Laplacian eigenvalue on the actual ideal graph. -/
def ActualLaplacianIntegral (n : ℕ) : Prop :=
  ∀ e : ℝ, HasActualEigenvalue n e → ∃ z : ℤ, e = z

private lemma actual_nonintegral_of_gap (n : ℕ) (q : ℤ) (e : ℝ)
    (he : HasActualEigenvalue n e) (hl : (q : ℝ) < e) (hu : e < (q : ℝ)+1) :
    ¬ActualLaplacianIntegral n := by
  obtain ⟨hn, hpair⟩ := he
  letI : Fintype (Vertex n) := actualVertexFintype n hn
  intro h
  apply nonintegral_of_gap (graph n) q e hpair hl hu
  intro c hc
  exact h c ⟨hn, hc⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nonzero complement eigenvector in the proved support model lifts to the
actual ideal graph. Zero sum is explicit, and the complement eigenvalue may be
zero: no extra endpoint exclusion is imposed on this transport. -/
theorem actual_eigenvalue_of_support (p : ι → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (k : ι → ℕ) (hk : ∀ i, 0 < k i) [Nonempty ι]
    (e : ℝ) (f : BoxVertex k → ℝ) (hf : f ≠ 0) (hsum : ∑ x, f x = 0)
    (he : (supportGraph k)ᶜ.lapMatrix ℝ *ᵥ f = e • f) :
    HasActualEigenvalue (modulus p k) ((((∏ i, (k i+1))-2 : ℕ) : ℝ)-e) := by
  classical
  have hboxcard : Fintype.card (BoxVertex k) = (∏ i, (k i+1))-2 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_congr (vertexBoxEquiv p hp hinj k)]
    exact actual_vertex_card p hp hinj k hk
  have hnn : modulus p k ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero)
  letI : Fintype (Vertex (modulus p k)) := actualVertexFintype _ hnn
  have hreflect : (supportGraph k).lapMatrix ℝ *ᵥ f =
      ((Fintype.card (BoxVertex k) : ℝ)-e) • f := by
    ext x
    have hh := lap_complement_apply (supportGraph k) f x
    rw [he,hsum] at hh
    simp only [Pi.smul_apply,smul_eq_mul] at hh ⊢
    linarith
  have ha := hasEigenvalue_iso (graph (modulus p k)) (supportGraph k)
    (actualSupportIso p hp hinj k) _ ⟨f,hf,hreflect⟩
  rw [hboxcard] at ha
  exact ⟨hnn,ha⟩

/-- The full distinguished-coordinate threshold obstruction. The weak threshold
includes equality; the strict eigenvalue interval is obtained by excluding the
trial vector from the unit eigenspace. All prime coordinates and positive
exponents remain arbitrary. -/
theorem threshold_obstruction (p : ι → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (hcard : 3 ≤ Fintype.card ι) (d : ι)
    (hthreshold :
      (((k d : ℝ)^2-1)*((∏ i ∈ univ.erase d, ((k i : ℝ)+1))-1-
        (∏ i ∈ univ.erase d, (k i : ℝ)))-((k d : ℝ)-1)) ≤
        ∏ i ∈ univ.erase d, (k i : ℝ)) :
    ∃ e : ℝ, (((∏ i, (k i+1))-2 : ℕ) : ℝ)-1 < e ∧
      e < (((∏ i, (k i+1))-2 : ℕ) : ℝ) ∧
      HasActualEigenvalue (modulus p k) e ∧ ¬ActualLaplacianIntegral (modulus p k) := by
  classical
  letI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hc : 1 < (univ.erase d : Finset ι).card := by
    rw [card_erase_of_mem (mem_univ d), card_univ]
    omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hc
  obtain ⟨e, he0, he1, f, hf, he⟩ := threshold_complement_low_eigenpair k hk d i j
    (mem_erase.mp hi).1 (mem_erase.mp hj).1 hij hthreshold
  have ha := actual_eigenvalue_of_support p hp hinj k hk e f hf
    (eigenpair_sum_zero (supportGraph k)ᶜ e he0.ne' f he) he
  let V : ℕ := (∏ i, (k i+1))-2
  have heactual : HasActualEigenvalue (modulus p k) ((V : ℝ)-e) := ha
  refine ⟨(V : ℝ)-e, by linarith, by linarith, heactual, ?_⟩
  apply actual_nonintegral_of_gap (modulus p k) ((V : ℤ)-1) ((V : ℝ)-e) heactual
  · simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
    linarith
  · simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
    linarith

/-- Every modulus with at least three distinct prime factors and a unit exponent
has a Laplacian eigenvalue strictly between the last two consecutive integers
below the vertex count. The distinguished index can be any coordinate. -/
theorem unit_exponent_obstruction (p : ι → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (hcard : 3 ≤ Fintype.card ι) (d : ι) (hd : k d = 1) :
    ∃ e : ℝ, (((∏ i, (k i+1))-2 : ℕ) : ℝ)-1 < e ∧
      e < (((∏ i, (k i+1))-2 : ℕ) : ℝ) ∧
      HasActualEigenvalue (modulus p k) e ∧ ¬ActualLaplacianIntegral (modulus p k) := by
  apply threshold_obstruction p hp hinj k hk hcard d
  rw [hd]
  norm_num
  exact (other_weight_positive k hk d).le

/-- The reciprocal condition implies the actual graph obstruction through the
full threshold theorem, retaining all equality and universal-vertex boundaries. -/
theorem reciprocal_obstruction (p : ι → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (hcard : 3 ≤ Fintype.card ι) (d : ι) (hm : 2 ≤ k d)
    (hs : (∑ i ∈ univ.erase d, 1/(k i : ℝ)) ≤ 1/(k d : ℝ)^2) :
    ∃ e : ℝ, (((∏ i, (k i+1))-2 : ℕ) : ℝ)-1 < e ∧
      e < (((∏ i, (k i+1))-2 : ℕ) : ℝ) ∧
      HasActualEigenvalue (modulus p k) e ∧ ¬ActualLaplacianIntegral (modulus p k) :=
  threshold_obstruction p hp hinj k hk hcard d (reciprocal_implies_threshold k hk d hm hs)

private lemma support_three_cases (k : ι → ℕ) (d i : ι)
    (huniv : (univ : Finset ι) = {d,i}) (e : BoxVertex k) :
    support e.1 = {d} ∨ support e.1 = {i} ∨ support e.1 = univ := by
  let S := support e.1
  have hS : S.Nonempty := support_nonempty k e
  have hsub : S ⊆ {d,i} := huniv ▸ subset_univ S
  by_cases hd : d ∈ S
  · by_cases hi : i ∈ S
    · right; right
      rw [huniv]
      exact subset_antisymm hsub (by simpa only [insert_subset_iff, singleton_subset_iff] using And.intro hd hi)
    · left
      apply hS.subset_singleton_iff.mp
      intro j hj
      have hji := hsub hj
      simp only [mem_insert, mem_singleton] at hji
      exact mem_singleton.mpr (hji.resolve_right (fun he => hi (he ▸ hj)))
  · right; left
    apply hS.subset_singleton_iff.mp
    intro j hj
    have hji := hsub hj
    simp only [mem_insert, mem_singleton] at hji
    exact mem_singleton.mpr (hji.resolve_left (fun he => hd (he ▸ hj)))

private lemma two_prime_star_structure (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (d i : ι) (hid : i ≠ d) (huniv : (univ : Finset ι) = {d,i}) (hd : k d = 1) :
    ∃ c : BoxVertex k, ∃ L : Finset (BoxVertex k), c ∉ L ∧
      ∀ x y, (supportGraph k)ᶜ.Adj x y ↔ (x=c ∧ y∈L) ∨ (y=c ∧ x∈L) := by
  classical
  have hdu : ({d} : Finset ι) ≠ univ := by
    intro h
    have hi : i ∈ ({d} : Finset ι) := h.symm ▸ mem_univ i
    exact hid (mem_singleton.mp hi)
  have hne : ({d,i} : Finset ι) ≠ {d} := by
    intro he
    exact hid (mem_singleton.mp (he ▸ (show i ∈ ({d,i} : Finset ι) by simp)))
  have hc1 : Fintype.card {e : BoxVertex k // support e.1 = {d}} = 1 := by
    rw [← Nat.card_eq_fintype_card,
      vertex_support_fiber_card k hk {d} (singleton_nonempty d) hdu]
    simpa using hd
  obtain ⟨c, hc⟩ := Fintype.card_eq_one_iff.mp hc1
  have hce (e : BoxVertex k) : support e.1 = {d} ↔ e=c.1 := by
    constructor
    · intro h
      exact congrArg Subtype.val (hc ⟨e,h⟩)
    · intro h
      rw [h]
      exact c.2
  let L : Finset (BoxVertex k) := univ.filter (fun e => support e.1 = {i})
  refine ⟨c.1,L,?_,?_⟩
  · simp only [L, mem_filter, mem_univ, true_and, c.2]
    simpa using Ne.symm hid
  · intro x y
    rw [complement_adj_disjoint]
    simp only [L, mem_filter, mem_univ, true_and, ← hce]
    rcases support_three_cases k d i huniv x with hx | hx | hx <;>
      rcases support_three_cases k d i huniv y with hy | hy | hy <;>
      simp [hx,hy,hid,Ne.symm hid,hdu,huniv,hne,Finset.disjoint_singleton]

/-- The sharp two-prime unit-exponent boundary: every eigenvalue of the actual
ideal-intersection Laplacian is an integer, for either distinguished prime and
an arbitrary positive exponent on the other prime. -/
theorem two_prime_unit_integral (p : ι → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (hcard : Fintype.card ι = 2) (d : ι) (hd : k d = 1) :
    ActualLaplacianIntegral (modulus p k) := by
  classical
  letI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i,hid⟩ := exists_ne d
  have huniv : (univ : Finset ι) = {d,i} := by
    symm
    apply eq_of_subset_of_card_le (subset_univ _)
    simp [hcard,hid,Ne.symm hid]
  obtain ⟨c,L,hc,hG⟩ := two_prime_star_structure k hk d i hid huniv hd
  intro e he
  by_cases he0 : e=0
  · exact ⟨0,by simpa using he0⟩
  obtain ⟨hn,he⟩ := he
  letI : Fintype (Vertex (modulus p k)) := actualVertexFintype _ hn
  have hb := hasEigenvalue_iso (supportGraph k) (graph (modulus p k))
    (actualSupportIso p hp hinj k).symm e he
  obtain ⟨f,hf,hfE⟩ := hb
  have hcomp : (supportGraph k)ᶜ.lapMatrix ℝ *ᵥ f =
      ((Fintype.card (BoxVertex k) : ℝ)-e) • f := by
    have hsum := eigenpair_sum_zero (supportGraph k) e he0 f hfE
    ext x
    have hh := lap_complement_apply (supportGraph k) f x
    rw [hfE,hsum] at hh
    simp only [Pi.smul_apply,smul_eq_mul] at hh ⊢
    linarith
  have hroots := star_eigenvalues (supportGraph k)ᶜ c L hc hG
    ((Fintype.card (BoxVertex k) : ℝ)-e) ⟨f,hf,hcomp⟩
  rcases hroots with h0 | h1 | hA
  · refine ⟨Fintype.card (BoxVertex k),?_⟩
    norm_cast
    linarith
  · refine ⟨(Fintype.card (BoxVertex k) : ℤ)-1,?_⟩
    push_cast
    linarith
  · refine ⟨(Fintype.card (BoxVertex k) : ℤ)-(L.card : ℤ)-1,?_⟩
    push_cast
    linarith

end ActualGraph

end D5.S3.Combinatorics.SpectralGraph.IdealIntersectionObstructions
