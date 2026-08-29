/- GID: D5/S3/Weil/ZetaGamma/ArchimedeanConfinement
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaGamma/ArchimedeanConfinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Confine completed-zeta multiplier sublevels to finitely many symmetric intervals. -/

import D5.S3.Weil.ZetaGamma.AnalyticStirling
import D5.S3.Weil.ZetaGamma.GammaFacts
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.DiscreteSubset

namespace D5.S3.Weil.ZetaGamma.ArchimedeanConfinement

open Filter Set Topology

private theorem mu_analytic : AnalyticOnNhd ℝ Zeta23.mu univ := by
  intro tau _
  have hzmem : (1 / 4 + Complex.I * (tau : ℂ) / 2 : ℂ) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    have hre := congr_arg Complex.re hn
    norm_num at hre
    have hn4 : (4 : ℝ) * (n : ℝ) = 1 := by linarith
    have hn4' : (4 : ℤ) * n = 1 := by exact_mod_cast hn4
    omega
  have hpsi : AnalyticAt ℂ Complex.digamma
      (1 / 4 + Complex.I * (tau : ℂ) / 2) := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [Complex.isOpen_compl_range_intCast.mem_nhds hzmem] with z hz
    exact Zeta23.Stirling.differentiableAt_digamma hz
  have haff : AnalyticAt ℝ
      (fun t : ℝ => (1 / 4 + Complex.I * (t : ℂ) / 2 : ℂ)) tau := by
    have hcast : AnalyticAt ℝ (fun t : ℝ => (t : ℂ)) tau :=
      Complex.ofRealCLM.analyticAt tau
    have hmul : AnalyticAt ℝ (fun t : ℝ => Complex.I * (t : ℂ)) tau :=
      analyticAt_const.mul hcast
    have hdiv : AnalyticAt ℝ (fun t : ℝ => Complex.I * (t : ℂ) / 2) tau :=
      hmul.div_const
    exact analyticAt_const.add hdiv
  have hcomp : AnalyticAt ℝ
      (fun t : ℝ => Complex.digamma (1 / 4 + Complex.I * (t : ℂ) / 2)) tau := by
    exact AnalyticAt.comp (𝕜 := ℝ)
      (f := fun t : ℝ => (1 / 4 + Complex.I * (t : ℂ) / 2 : ℂ))
      hpsi.restrictScalars haff
  have hre : AnalyticAt ℝ
      (fun t : ℝ => (Complex.digamma (1 / 4 + Complex.I * (t : ℂ) / 2)).re) tau :=
    (Complex.reCLM.analyticAt _).comp hcomp
  have hscale : AnalyticAt ℝ
      (fun t : ℝ => (1 / (2 * Real.pi)) *
        (Complex.digamma (1 / 4 + Complex.I * (t : ℂ) / 2)).re) tau :=
    analyticAt_const.mul hre
  have hconstant : AnalyticAt ℝ
      (fun _t : ℝ => Real.log Real.pi / (2 * Real.pi)) tau := analyticAt_const
  change AnalyticAt ℝ (fun t : ℝ => (1 / (2 * Real.pi)) *
    (Complex.digamma (1 / 4 + Complex.I * (t : ℂ) / 2)).re -
      Real.log Real.pi / (2 * Real.pi)) tau
  exact hscale.sub hconstant

private theorem px_analytic (X : ℝ) : AnalyticOnNhd ℝ (Zeta23.PX X) univ := by
  intro tau _
  unfold Zeta23.PX
  fun_prop

private theorem open_bounded_finite_union_Ioo
    {U : Set ℝ} (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (hfrontier : (frontier U).Finite) :
    ∃ intervals : Finset (ℝ × ℝ),
      U = ⋃ p ∈ (intervals : Set (ℝ × ℝ)), Ioo p.1 p.2 := by
  classical
  let intervals :=
    (hfrontier.toFinset.product hfrontier.toFinset).filter
      (fun p => Ioo p.1 p.2 ⊆ U)
  refine ⟨intervals, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    let C := connectedComponentIn U x
    have hCopen : IsOpen C := hUopen.connectedComponentIn
    have hxC : x ∈ C := mem_connectedComponentIn hx
    have hCnonempty : C.Nonempty := ⟨x, hxC⟩
    have hCU : C ⊆ U := connectedComponentIn_subset U x
    have hCbounded : Bornology.IsBounded C := hUbounded.subset hCU
    have hCbelow : BddBelow C := hCbounded.bddBelow
    have hCabove : BddAbove C := hCbounded.bddAbove
    have hCconnected : IsConnected C := isConnected_connectedComponentIn_iff.mpr hx
    have hCeq : C = Ioo (sInf C) (sSup C) := by
      apply Set.Subset.antisymm
      · intro y hy
        have hyIcc := subset_Icc_csInf_csSup hCbelow hCabove hy
        refine ⟨lt_of_le_of_ne hyIcc.1 ?_, lt_of_le_of_ne hyIcc.2 ?_⟩
        · intro heq
          have hnhds : C ∈ 𝓝 y := hCopen.mem_nhds hy
          obtain ⟨l, u, hyIoo, hIooC⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
          obtain ⟨z, hlz, hzy⟩ := exists_between hyIoo.1
          have hzC : z ∈ C := hIooC ⟨hlz, hzy.trans hyIoo.2⟩
          have := csInf_le hCbelow hzC
          rw [heq] at this
          exact (not_lt_of_ge this) hzy
        · intro heq
          have hnhds : C ∈ 𝓝 y := hCopen.mem_nhds hy
          obtain ⟨l, u, hyIoo, hIooC⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
          obtain ⟨z, hyz, hzu⟩ := exists_between hyIoo.2
          have hzC : z ∈ C := hIooC ⟨hyIoo.1.trans hyz, hzu⟩
          have := le_csSup hCabove hzC
          rw [← heq] at this
          exact (not_lt_of_ge this) hyz
      · exact hCconnected.Ioo_csInf_csSup_subset hCbelow hCabove
    have hinfClosure : sInf C ∈ closure U :=
      closure_mono hCU (csInf_mem_closure hCnonempty hCbelow)
    have hsupClosure : sSup C ∈ closure U :=
      closure_mono hCU (csSup_mem_closure hCnonempty hCabove)
    have hinfNot : sInf C ∉ U := by
      intro hinfU
      obtain ⟨l, u, hinfIoo, hIooU⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (hUopen.mem_nhds hinfU)
      obtain ⟨w, hwIoo, hwC⟩ :=
        mem_closure_iff.mp (csInf_mem_closure hCnonempty hCbelow) _ isOpen_Ioo hinfIoo
      have hIooC : Ioo l u ⊆ C := by
        have hcomp : C = connectedComponentIn U w := connectedComponentIn_eq hwC
        rw [hcomp]
        exact isPreconnected_Ioo.subset_connectedComponentIn hwIoo hIooU
      have hinfC : sInf C ∈ C := hIooC hinfIoo
      have hinfC' : sInf C ∈ Ioo (sInf C) (sSup C) := hCeq ▸ hinfC
      exact (lt_irrefl _ hinfC'.1)
    have hsupNot : sSup C ∉ U := by
      intro hsupU
      obtain ⟨l, u, hsupIoo, hIooU⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (hUopen.mem_nhds hsupU)
      obtain ⟨w, hwIoo, hwC⟩ :=
        mem_closure_iff.mp (csSup_mem_closure hCnonempty hCabove) _ isOpen_Ioo hsupIoo
      have hIooC : Ioo l u ⊆ C := by
        have hcomp : C = connectedComponentIn U w := connectedComponentIn_eq hwC
        rw [hcomp]
        exact isPreconnected_Ioo.subset_connectedComponentIn hwIoo hIooU
      have hsupC : sSup C ∈ C := hIooC hsupIoo
      have hsupC' : sSup C ∈ Ioo (sInf C) (sSup C) := hCeq ▸ hsupC
      exact (lt_irrefl _ hsupC'.2)
    have hinfFrontier : sInf C ∈ frontier U := by
      rw [frontier, hUopen.interior_eq]
      exact ⟨hinfClosure, hinfNot⟩
    have hsupFrontier : sSup C ∈ frontier U := by
      rw [frontier, hUopen.interior_eq]
      exact ⟨hsupClosure, hsupNot⟩
    have hpMem : (sInf C, sSup C) ∈ intervals := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hCeq ▸ hCU⟩
      · simpa using hinfFrontier
      · simpa using hsupFrontier
    rw [Set.mem_iUnion]
    refine ⟨(sInf C, sSup C), ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨hpMem, hCeq ▸ hxC⟩
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨p, hpMem, hxp⟩ := hx
    exact (Finset.mem_filter.mp hpMem).2 hxp

private theorem confinement_of_analytic_even_tendsto
    (m : ℝ → ℝ) (a : ℝ) (hm : AnalyticOnNhd ℝ m univ)
    (hmeven : ∀ x, m (-x) = m x) (hmgrowth : Tendsto m (cocompact ℝ) atTop) :
    Bornology.IsBounded {x | m x < a} ∧
      Neg.neg '' {x | m x < a} = {x | m x < a} ∧
      ∃ intervals : Finset (ℝ × ℝ),
        {x | m x < a} = ⋃ p ∈ (intervals : Set (ℝ × ℝ)), Ioo p.1 p.2 := by
  let U : Set ℝ := {x | m x < a}
  have hUopen : IsOpen U := isOpen_lt hm.continuous continuous_const
  have hgood : {x | a ≤ m x} ∈ cocompact ℝ := hmgrowth (eventually_ge_atTop a)
  obtain ⟨K, hKcompact, hKgood⟩ := mem_cocompact.mp hgood
  have hUK : U ⊆ K := by
    intro x hx
    change m x < a at hx
    by_contra hxK
    exact (not_lt_of_ge (hKgood hxK)) hx
  have hUbounded : Bornology.IsBounded U := hKcompact.isBounded.subset hUK
  have hclosureK : closure U ⊆ K := closure_minimal hUK hKcompact.isClosed
  have heventuallyLarge : ∀ᶠ y in cocompact ℝ, a + 1 ≤ m y :=
    hmgrowth (eventually_ge_atTop (a + 1))
  obtain ⟨x, hx⟩ := Filter.Eventually.exists heventuallyLarge
  have hshift : AnalyticOnNhd ℝ (fun y => m y - a) univ := hm.sub analyticOnNhd_const
  have hxne : m x - a ≠ 0 := by linarith
  have hcodiscrete : (fun y => m y - a) ⁻¹' ({0} : Set ℝ)ᶜ ∈ codiscreteWithin univ :=
    hshift.preimage_zero_mem_codiscreteWithin hxne (mem_univ x) isConnected_univ
  have hcodiscreteK :
      (fun y => m y - a) ⁻¹' ({0} : Set ℝ)ᶜ ∈ codiscreteWithin K :=
    Filter.codiscreteWithin_mono (subset_univ K) hcodiscrete
  have hfiniteZeros :
      (K \ (fun y => m y - a) ⁻¹' ({0} : Set ℝ)ᶜ).Finite :=
    hKcompact.finite_sdiff_of_mem_codiscreteWithin hcodiscreteK
  have hfiniteLevel : (K ∩ {y | m y = a}).Finite := by
    convert hfiniteZeros using 1
    ext y
    simp [sub_eq_zero]
  have hfrontier : (frontier U).Finite := hfiniteLevel.subset fun y hy => by
    refine ⟨hclosureK (frontier_subset_closure hy), ?_⟩
    exact (frontier_lt_subset_eq hm.continuous continuous_const) hy
  have hsymmetric : Neg.neg '' U = U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change m (-x) < a
      rwa [hmeven]
    · intro hy
      refine ⟨-y, ?_, neg_neg y⟩
      change m (-y) < a
      rwa [hmeven]
  refine ⟨hUbounded, hsymmetric, ?_⟩
  exact open_bounded_finite_union_Ioo hUopen hUbounded hfrontier

/-- Proper growth of the completed-zeta multiplier confines every strict sublevel set to a
bounded reflection-invariant finite union of open intervals. -/
theorem archimedean_confinement
    (L a : ℝ)
    (multiplier_growth : Tendsto
      (fun xi => 2 * Real.pi * (Zeta23.mu xi + Zeta23.PX (Real.exp (2 * L)) xi))
      (cocompact ℝ) atTop) :
    let dangerousFrequencies := {xi : ℝ | 2 * Real.pi *
      (Zeta23.mu xi + Zeta23.PX (Real.exp (2 * L)) xi) < a}
    Bornology.IsBounded dangerousFrequencies ∧
      Neg.neg '' dangerousFrequencies = dangerousFrequencies ∧
      ∃ intervals : Finset (ℝ × ℝ), dangerousFrequencies =
        ⋃ p ∈ (intervals : Set (ℝ × ℝ)), Ioo p.1 p.2 := by
  dsimp only
  let m : ℝ → ℝ := fun xi => 2 * Real.pi *
    (Zeta23.mu xi + Zeta23.PX (Real.exp (2 * L)) xi)
  have hm : AnalyticOnNhd ℝ m univ := by
    exact analyticOnNhd_const.mul (mu_analytic.add (px_analytic _))
  have hPXeven (xi : ℝ) :
      Zeta23.PX (Real.exp (2 * L)) (-xi) = Zeta23.PX (Real.exp (2 * L)) xi := by
    simp [Zeta23.PX, neg_mul]
  have hmeven (xi : ℝ) : m (-xi) = m xi := by
    simp only [m, Zeta23.mu_even, hPXeven]
  exact confinement_of_analytic_even_tendsto m a hm hmeven multiplier_growth

end D5.S3.Weil.ZetaGamma.ArchimedeanConfinement
