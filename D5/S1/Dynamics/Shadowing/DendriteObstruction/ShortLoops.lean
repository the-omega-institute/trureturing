/- GID: D5/S1/Dynamics/Shadowing/DendriteObstruction/ShortLoops
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/DendriteObstruction/ShortLoops
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrarily short repeated pairs in circle-free Hausdorff spaces. -/

import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

/-! The minimum positive repeated-pair gap produces an actual circle injection. -/

open Set Function
open scoped Topology

namespace D5.S1.Dynamics.Shadowing.DendriteObstruction

/-- A repeated continuous path in a Hausdorff space without an embedded circle
has repeated pairs at every positive parameter scale. -/
theorem short_repeated_pair {X : Type*} [TopologicalSpace X] [T2Space X]
    (no_circle : ∀ g : AddCircle (1 : ℝ) → X, Continuous g → ¬ Injective g)
    {h : ℝ → X} (hh : ContinuousOn h (Icc 0 1))
    (hn : ¬ InjOn h (Icc 0 1)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a ∈ Icc (0 : ℝ) 1, ∃ b ∈ Icc (0 : ℝ) 1,
      a < b ∧ b - a < δ ∧ h a = h b := by
  classical
  by_contra hshort
  have lower : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      u < v → h u = h v → δ ≤ v - u := by
    intro u hu v hv huv he
    exact le_of_not_gt (fun hlt => hshort ⟨u, hu, v, hv, huv, hlt, he⟩)
  let K : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc 0 1
  let S : Set (ℝ × ℝ) := {p ∈ K | h p.1 = h p.2} ∩ {p | δ ≤ p.2 - p.1}
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hE : IsClosed {p ∈ K | h p.1 = h p.2} := by
    apply hK.isClosed.isClosed_eq
    · exact hh.comp continuous_fst.continuousOn (fun p hp => hp.1)
    · exact hh.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hS : IsCompact S := by
    apply hK.of_isClosed_subset
    · exact hE.inter (isClosed_le continuous_const (continuous_snd.sub continuous_fst))
    · exact fun p hp => hp.1.1
  have hSne : S.Nonempty := by
    simp only [InjOn, not_forall] at hn
    obtain ⟨u, hu, v, hv, he, hne⟩ := hn
    rcases lt_or_gt_of_ne hne with huv | hvu
    · exact ⟨(u, v), ⟨⟨⟨hu, hv⟩, he⟩, lower u hu v hv huv he⟩⟩
    · exact ⟨(v, u), ⟨⟨⟨hv, hu⟩, he.symm⟩, lower v hv u hu hvu he.symm⟩⟩
  obtain ⟨⟨a, b⟩, habS, habmin⟩ :=
    hS.exists_isMinOn hSne (continuous_snd.sub continuous_fst).continuousOn
  have ha : a ∈ Icc (0 : ℝ) 1 := habS.1.1.1
  have hb : b ∈ Icc (0 : ℝ) 1 := habS.1.1.2
  have he : h a = h b := habS.1.2
  have hab : a < b := by have := habS.2; dsimp at this; linarith
  have minimal : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      u < v → h u = h v → b - a ≤ v - u := by
    intro u hu v hv huv huv_eq
    have hmem : (u, v) ∈ S := ⟨⟨⟨hu, hv⟩, huv_eq⟩, lower u hu v hv huv huv_eq⟩
    exact habmin hmem
  have hi : InjOn h (Ico a b) := by
    intro u hu v hv huv_eq
    by_contra huv_ne
    rcases lt_or_gt_of_ne huv_ne with huv | hvu
    · have := minimal u ⟨ha.1.trans hu.1, (le_of_lt hu.2).trans hb.2⟩
        v ⟨ha.1.trans hv.1, (le_of_lt hv.2).trans hb.2⟩ huv huv_eq
      linarith [hu.1, hv.2]
    · have := minimal v ⟨ha.1.trans hv.1, (le_of_lt hv.2).trans hb.2⟩
        u ⟨ha.1.trans hu.1, (le_of_lt hu.2).trans hb.2⟩ hvu huv_eq.symm
      linarith [hv.1, hu.2]
  let k : ℝ → X := fun t => h (a + (b - a) * t)
  have hk : ContinuousOn k (Icc 0 1) := by
    apply hh.comp (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
    intro t ht
    change 0 ≤ a + (b - a) * t ∧ a + (b - a) * t ≤ 1
    constructor <;> nlinarith [ha.1, hb.2, ht.1, ht.2]
  have hk_end : k 0 = k 1 := by simpa [k] using he
  have hk_inj : InjOn k (Ico 0 1) := by
    intro u hu v hv huv
    have hu' : a + (b - a) * u ∈ Ico a b := by
      constructor <;> nlinarith [hu.1, hu.2]
    have hv' : a + (b - a) * v ∈ Ico a b := by
      constructor <;> nlinarith [hv.1, hv.2]
    have := hi hu' hv' huv
    nlinarith
  apply no_circle (AddCircle.liftIco 1 0 k)
    (AddCircle.liftIco_zero_continuous hk_end hk)
  intro x y hxy
  apply (AddCircle.equivIco 1 0).injective
  apply Subtype.ext
  apply hk_inj
  · simpa using (AddCircle.equivIco 1 0 x).property
  · simpa using (AddCircle.equivIco 1 0 y).property
  · exact hxy

end D5.S1.Dynamics.Shadowing.DendriteObstruction
