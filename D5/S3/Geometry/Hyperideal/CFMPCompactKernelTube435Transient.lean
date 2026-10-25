import D5.S3.Geometry.Hyperideal.CFMPOriginalCellKernel435Transient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter
open CFMPActualNativeCellMotion435Transient

namespace CFMPCompactKernelTube435Transient
abbrev V := Fin 3 → ℝ

def delta : Set V := {u | referenceSimplex u}

theorem delta_compact : IsCompact delta := by
  have hclosed : IsClosed delta := by
    change IsClosed ({u : V | ∀ i, 0 ≤ u i} ∩ {u | (∑ i, u i) ≤ 1})
    apply IsClosed.inter
    · simpa only [Set.ofPred_forall] using
        isClosed_iInter (fun i : Fin 3 => isClosed_le continuous_const (continuous_apply i))
    · exact isClosed_le (continuous_finset_sum _ (fun i _ => continuous_apply i)) continuous_const
  apply (isCompact_Icc : IsCompact (Icc (0 : V) 1)).of_isClosed_subset hclosed
  intro u hu
  refine ⟨hu.1,?_⟩
  intro i
  exact le_trans (Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)) hu.2

def timeDerivative (F : ℝ × V → ℝ) (z : ℝ × V) : ℝ :=
  fderiv ℝ F z (1,0)

theorem compact_c1_tube (F : Fin 20 → ℝ × V → ℝ) (t : ℝ)
    (T : Set ℝ) (hT : IsOpen T) (htT : t ∈ T)
    (hbase : ∀ n u, u ∈ delta → ContDiffAt ℝ 1 (F n) (t,u)) :
    ∃ ε : ℝ, 0 < ε ∧ Icc (t-ε) (t+ε) ⊆ T ∧
      ∀ n,
        ContinuousOn (F n) (Icc (t-ε) (t+ε) ×ˢ delta) ∧
        ContinuousOn (timeDerivative (F n)) (Icc (t-ε) (t+ε) ×ˢ delta) ∧
        (∀ s ∈ Icc (t-ε) (t+ε), ∀ u ∈ delta,
          HasDerivAt (fun r => F n (r,u)) (timeDerivative (F n) (s,u)) s) ∧
        (∃ C : ℝ, ∀ z ∈ Icc (t-ε) (t+ε) ×ˢ delta, ‖timeDerivative (F n) z‖ ≤ C) := by
  let G : Set (ℝ × V) := {z | z.1 ∈ T ∧ ∀ n, ContDiffAt ℝ 1 (F n) z}
  have hG : IsOpen G := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have htime : ∀ᶠ y in 𝓝 z, y.1 ∈ T :=
      continuous_fst.continuousAt.eventually (hT.mem_nhds hz.1)
    have hreg : ∀ᶠ y in 𝓝 z, ∀ n, ContDiffAt ℝ 1 (F n) y :=
      Filter.eventually_all.mpr (fun n => (hz.2 n).eventually (by simp))
    exact htime.and hreg
  have hbaseG : ({t} : Set ℝ) ×ˢ delta ⊆ G := by
    rintro ⟨s,u⟩ ⟨hs,hu⟩
    have hst : s = t := by simpa only [Set.mem_singleton_iff] using hs
    subst s
    exact ⟨htT,fun n => hbase n u hu⟩
  obtain ⟨U,O,hU,hO,htU,hδO,hUO⟩ :=
    generalized_tube_lemma isCompact_singleton delta_compact hG hbaseG
  have htu : t ∈ U := htU (by simp)
  obtain ⟨ε,hε,hball⟩ := (Metric.nhds_basis_closedBall (x := t)).mem_iff.mp (hU.mem_nhds htu)
  have hI : Icc (t-ε) (t+ε) ⊆ U := by
    simpa only [Real.closedBall_eq_Icc] using hball
  have hsmall : Icc (t-ε) (t+ε) ×ˢ delta ⊆ G :=
    fun z hz => hUO ⟨hI hz.1,hδO hz.2⟩
  refine ⟨ε,hε,?_,?_⟩
  · intro s hs
    have hz : (s,(0 : V)) ∈ G := hsmall ⟨hs,by simp [delta,referenceSimplex]⟩
    exact hz.1
  · intro n
    have hFn : ContDiffOn ℝ 1 (F n) G := fun z hz => (hz.2 n).contDiffWithinAt
    have hDF : ContinuousOn (timeDerivative (F n)) G :=
      (hFn.continuousOn_fderiv_of_isOpen hG le_rfl).clm_apply continuousOn_const
    refine ⟨hFn.continuousOn.mono hsmall,hDF.mono hsmall,?_,?_⟩
    · intro s hs u hu
      have hdiff := ((hsmall (show (s,u) ∈ Icc (t-ε) (t+ε) ×ˢ delta from
        ⟨hs,hu⟩)).2 n).differentiableAt_one.hasFDerivAt
      have hline : HasDerivAt (fun r : ℝ => (r,u)) (1,(0 : V)) s := by
        simpa using (hasDerivAt_id s).prodMk (hasDerivAt_const s u)
      simpa only [Function.comp_def,timeDerivative] using hdiff.comp_hasDerivAt s hline
    · exact (isCompact_Icc.prod delta_compact).exists_bound_of_continuousOn (hDF.mono hsmall)

end CFMPCompactKernelTube435Transient
