/- GID: D5/S3/Quantum/Foundation/OrthogonalJointCompletion
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OrthogonalJointCompletion
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Weak original orthogonal pair properness supplies whole joint triples. -/

import D5.S3.Quantum.Foundation.ExclusionBallFaces
import D5.S3.Quantum.Foundation.WholeExclusionSupport

/-! Entire original exclusion-ball geometry and global three-effect completion. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.OrthogonalJointCompletion

open CircuitBalancedConfirmation FacetZeroGluing WholePairBallConfirmation
open ExclusionBallFaces WholeExclusionSupport

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Only original orthogonal pairs are required to generate a proper face. -/
def weakPair (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ p q : pure C u, excludes C u p q → pairBase C u p q ≠ base C u

/-- The complete original family A_p, without leastness or uniqueness. -/
def common (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p : V)
    (a : V →ₗ[ℝ] ℝ) : Prop :=
  confirms C u p a ∧ ∀ x ∈ exclusion C u p, a x = 0

/-- A finite mathematical measurement distinguishes original pure points.
This asserts no physical menu or device implementation. -/
def measurement (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (n : ℕ) : Prop :=
  ∃ p : Fin n → pure C u, ∃ f : Fin n → (V →ₗ[ℝ] ℝ),
    (∀ i, proper C u (f i)) ∧
    (∀ i j, f i (p j) = if i = j then 1 else 0) ∧ ∑ i, f i = u

/-- All clauses for a specified pair and its third point. -/
def jointThird (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (p q r : pure C u) : Prop :=
  exclusion C u p ∩ exclusion C u q = {(r : V)} ∧
  pairBase C u p q = exclusion C u r ∧
  excludes C u p q ∧ excludes C u p r ∧ excludes C u q r ∧
  ∀ a b : V →ₗ[ℝ] ℝ, common C u p a → common C u q b →
    common C u r (u - a - b) ∧
    a p = 1 ∧ a q = 0 ∧ a r = 0 ∧
    b p = 0 ∧ b q = 1 ∧ b r = 0 ∧
    (u - a - b) p = 0 ∧ (u - a - b) q = 0 ∧ (u - a - b) r = 1 ∧
    a + b + (u - a - b) = u

omit [FiniteDimensional ℝ V] in
private theorem not_self {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (p : pure C u) : (p : V) ∉ exclusion C u p := by
  rintro ⟨_, f, hf, hz⟩
  linarith [hf.2]

private theorem pair_geometry {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) (p q : pure C u) (hpq : excludes C u p q) :
    ∃ r : pure C u, pairBase C u p q = exclusion C u r ∧
      exclusion C u p ∩ exclusion C u q = {(r : V)} := by
  obtain ⟨geom, classify, _⟩ := exclusion_ball_faces hc hs hg hB
  have hp : (p : V) ∈ pairBase C u p q := ⟨pure_mem p, fun _ hp _ => hp⟩
  have hq : (q : V) ∈ pairBase C u p q := ⟨pure_mem q, fun _ _ hq => hq⟩
  have hne : p ≠ q := by
    intro he
    subst q
    exact not_self p ⟨pure_mem p, hpq⟩
  obtain ⟨r, hr⟩ : ∃ r : pure C u, pairBase C u p q = exclusion C u r := by
    rcases classify _ ⟨p, hp⟩ (pair_convex C u p q) (pair_extreme C u p q)
      (hW p q hpq) with ⟨r, he⟩ | hh
    · rw [he] at hp hq
      exact (hne (Subtype.ext (hp.trans hq.symm))).elim
    · exact hh
  have hpr : (p : V) ∈ exclusion C u r := hr ▸ hp
  have hqr : (q : V) ∈ exclusion C u r := hr ▸ hq
  have hrp := (exclusion_symmetric r p).mp hpr
  have hrq := (exclusion_symmetric r q).mp hqr
  have hsub : exclusion C u p ∩ exclusion C u q ⊆ {(r : V)} := by
    by_contra hn
    obtain ⟨x, hx, hxr⟩ := Set.not_subset.mp hn
    have hnon : (exclusion C u p ∩ exclusion C u q).Nontrivial :=
      ⟨x, hx, r, ⟨hrp, hrq⟩, fun he => hxr (Set.mem_singleton_iff.mpr he)⟩
    obtain ⟨b⟩ := hB p
    have he := chart_face_eq b ((geom p).2.2.1.inter (geom q).2.2.1)
      (((geom p).2.2.2.2.1.inter (geom q).2.2.2.2.1).mono
        (geom p).2.2.2.2.1.subset inter_subset_left) hnon
    have hqp : (q : V) ∈ exclusion C u p := ⟨pure_mem q, hpq⟩
    have : (q : V) ∈ exclusion C u p ∩ exclusion C u q := he.symm ▸ hqp
    exact not_self q this.2
  exact ⟨r, hr, Subset.antisymm hsub (by simpa using And.intro hrp hrq)⟩

/-- On an entire pair ball, opposite original zero readings fix both affine
restrictions. This is used only after deriving the whole pair ball from W. -/
private theorem sum_on_pair_ball {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (p q : pure C u) (b : BallChart C u p q)
    (a d : V →ₗ[ℝ] ℝ) (ha : confirms C u p a) (hd : confirms C u q d)
    (haq : a q = 0) (hdp : d p = 0) :
    ∀ x ∈ pairBase C u p q, a x + d x = u x := by
  obtain ⟨n, hn, hnp⟩ := endpoint_coordinates p q b
  have mem (s) (hs : ‖s‖ ≤ 1) : b.param s ∈ pairBase C u p q := by
    rw [← b.whole]
    exact ⟨s, by simpa using hs, rfl⟩
  let f := (u - a).toAffineMap.comp b.param
  have hfpos : ∀ s, ‖s‖ ≤ 1 → 0 ≤ f s := by
    intro s hs
    exact sub_nonneg.mpr (ha.1 _ (mem s hs).1.1).2
  have hfzero : f (-(-n)) = 0 := by
    simp [f, hnp, ha.2, (pure_mem p).2]
  have hf := affine_zero_antipode f (by simpa using hn : ‖-n‖ = 1) hfpos hfzero
  have hfcoeff : f (-n) = 1 := by
    obtain ⟨m, hm, hmq⟩ := b.whole.symm ▸
      (show (q : V) ∈ pairBase C u p q from ⟨pure_mem q, fun _ _ h => h⟩)
    have hmn : ‖m‖ = 1 := chart_pure_norm b (by simpa using hm) (by rw [hmq]; exact q.property)
    have hfm : f m = 1 := by simp [f, hmq, haq, (pure_mem q).2]
    have hfupper : f (-n) ≤ 1 := by
      have hx := mem (-n) (by simp [hn])
      change u (b.param (-n)) - a (b.param (-n)) ≤ 1
      rw [hx.1.2]
      linarith [(ha.1 _ hx.1.1).1]
    have hfcpos : 0 ≤ f (-n) := hfpos _ (by simp [hn])
    have hi : ⟪-n, m⟫ ≤ 1 := by
      simpa [hn, hmn] using real_inner_le_norm (-n) m
    have he := hf m
    rw [hfm] at he
    nlinarith
  obtain ⟨m, hm, hmq⟩ := b.whole.symm ▸
    (show (q : V) ∈ pairBase C u p q from ⟨pure_mem q, fun _ _ h => h⟩)
  have hmn : ‖m‖ = 1 := chart_pure_norm b (by simpa using hm) (by rw [hmq]; exact q.property)
  have he := hf m
  have hfm : f m = 1 := by simp [f, hmq, haq, (pure_mem q).2]
  rw [hfm, hfcoeff] at he
  have hi : ⟪-n, m⟫ = 1 := by linarith
  have hnm : -n = m := (inner_eq_one_iff_of_norm_eq_one (by simpa using hn) hmn).mp hi
  have hdneg : d (b.param (-n)) = 1 := by rw [hnm, hmq]; exact hd.2
  have hdformula := affine_zero_antipode (d.toAffineMap.comp b.param)
    (by simpa using hn : ‖-n‖ = 1)
    (fun s hs => (hd.1 _ (mem s hs).1.1).1)
    (by simpa [hnp] using hdp)
  intro x hx
  obtain ⟨s, hs, rfl⟩ := b.whole.symm ▸ hx
  have h1 := hf s
  have h2 := hdformula s
  change u (b.param s) - a (b.param s) = f (-n) / 2 * (1 + ⟪-n, s⟫) at h1
  change d (b.param s) = d (b.param (-n)) / 2 * (1 + ⟪-n, s⟫) at h2
  rw [hfcoeff] at h1
  rw [hdneg] at h2
  linarith

private theorem complete_pair {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) (p q : pure C u) (hpq : excludes C u p q) :
    ∃! r : pure C u, jointThird C u p q r := by
  obtain ⟨r, hr, hinter⟩ := pair_geometry hc hs hg hB hW p q hpq
  have hrmem : (r : V) ∈ exclusion C u p ∩ exclusion C u q := by rw [hinter]; simp
  have hqmem : (q : V) ∈ exclusion C u p := ⟨pure_mem q, hpq⟩
  have hpmem := (exclusion_symmetric p q).mp hqmem
  refine ⟨r, ⟨hinter, hr, hpq, hrmem.1.2, hrmem.2.2, ?_⟩, ?_⟩
  · intro a b ha hb
    have haq := ha.2 q hqmem
    have hbp := hb.2 p hpmem
    have har := ha.2 r hrmem.1
    have hbr := hb.2 r hrmem.2
    obtain ⟨chart⟩ := hB r
    let chart' : BallChart C u p q :=
      ⟨chart.dim, chart.dim_pos, chart.param, chart.injective, chart.whole.trans hr.symm⟩
    have hsum := sum_on_pair_ball p q chart' a b ha.1 hb.1 haq hbp
    have hzero : ∀ x ∈ exclusion C u r, (u - a - b) x = 0 := by
      intro x hx
      have hh := hsum x (hr.symm ▸ hx)
      simp only [LinearMap.sub_apply]
      linarith
    have hval : (u - a - b) r = 1 := by simp [har, hbr, (pure_mem r).2]
    have hproper := whole_exclusion_support hc hs r (u - a - b) hval (by
      intro x hx
      simp only [LinearMap.sub_apply]
      linarith [(ha.1.1 x hx).1, (hb.1.1 x hx).1]) hzero
    refine ⟨⟨hproper, hzero⟩, ha.1.2, haq, har, hbp, hb.1.2, hbr, ?_, ?_, hval, ?_⟩
    · simp [ha.1.2, hbp, (pure_mem p).2]
    · simp [haq, hb.1.2, (pure_mem q).2]
    · abel
  · intro s hs
    apply Subtype.ext
    have hh : (s : V) ∈ exclusion C u p ∩ exclusion C u q := by rw [hs.1]; simp
    simpa [hinter] using hh

/-- Complete original all-P joint triples and the exclusion of a fourth
pairwise original orthogonal point. No global pair or finiteness assumption. -/
theorem whole_joint_completion [Nontrivial V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hW : weakPair C u) :
    (∀ p q : pure C u, excludes C u p q → ∃! r : pure C u, jointThird C u p q r) ∧
    (∀ p : pure C u, ∃ q r : pure C u, jointThird C u p q r) ∧
    (∀ p q r s : pure C u,
      excludes C u p q → excludes C u p r → excludes C u p s →
      excludes C u q r → excludes C u q s → ¬ excludes C u r s) ∧
    measurement C u 3 ∧ (∀ n, measurement C u n → n ≤ 3) := by
  have hpairs := complete_pair hc hs hg hB hW
  have hevery : ∀ p : pure C u, ∃ q r : pure C u, jointThird C u p q r := by
    intro p
    obtain ⟨geom, _, _⟩ := exclusion_ball_faces hc hs hg hB
    obtain ⟨q, hq⟩ := (geom p).2.1.extremePoints_nonempty (geom p).1.nonempty
    have hpure : q ∈ pure C u := (geom p).2.2.2.2.1.extremePoints_subset_extremePoints hq
    obtain ⟨r, hr, _⟩ := hpairs p ⟨q, hpure⟩ hq.1.2
    exact ⟨⟨q, hpure⟩, r, hr⟩
  have hfour : ∀ p q r s : pure C u,
      excludes C u p q → excludes C u p r → excludes C u p s →
      excludes C u q r → excludes C u q s → ¬ excludes C u r s := by
    intro p q r s hpq hpr hps hqr hqs hrs
    obtain ⟨t, ht, _⟩ := hpairs p q hpq
    have hr : (r : V) = t := by
      have hh : (r : V) ∈ exclusion C u p ∩ exclusion C u q :=
        ⟨⟨pure_mem r, hpr⟩, ⟨pure_mem r, hqr⟩⟩
      simpa [ht.1] using hh
    have hss : (s : V) = t := by
      have hh : (s : V) ∈ exclusion C u p ∩ exclusion C u q :=
        ⟨⟨pure_mem s, hps⟩, ⟨pure_mem s, hqs⟩⟩
      simpa [ht.1] using hh
    have he : r = s := Subtype.ext (hr.trans hss.symm)
    subst s
    exact not_self r ⟨pure_mem r, hrs⟩

  refine ⟨hpairs, hevery, hfour, ?_, ?_⟩
  · have hP : (pure C u).Nonempty := by
      by_contra hn
      have hh := pure_span (base_compact hc hs) hs hg
      rw [Set.not_nonempty_iff_eq_empty.mp hn, Submodule.span_empty] at hh
      exact bot_ne_top hh
    obtain ⟨p, hp⟩ := hP
    let p' : pure C u := ⟨p, hp⟩
    obtain ⟨q, r, hr⟩ := hevery p'
    obtain ⟨geom, _, _⟩ := exclusion_ball_faces hc hs hg hB
    obtain ⟨a, ha, haz⟩ := (geom p').2.2.2.2.2.2
    obtain ⟨b, hb, hbz⟩ := (geom q).2.2.2.2.2.2
    have haA : common C u p' a := ⟨ha, fun x hx => (haz ▸ hx).2⟩
    have hbA : common C u q b := ⟨hb, fun x hx => (hbz ▸ hx).2⟩
    obtain ⟨hcA, hap, haq, har, hbp, hbq, hbr, hcp, hcq, hcr, hsum⟩ :=
      hr.2.2.2.2.2 a b haA hbA
    refine ⟨![p', q, r], ![a, b, u - a - b], ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact ha.1
      · exact hb.1
      · exact hcA.1.1
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [hap, haq, har, hbp, hbq, hbr, hcp, hcq, hcr]
    · simp [Fin.sum_univ_succ, add_assoc]
  · intro n hn
    obtain ⟨p, f, hf, hdelta, _⟩ := hn
    by_contra! hlarge
    have horth (i j : Fin n) (hne : i ≠ j) : excludes C u (p i) (p j) := by
      refine ⟨f i, ⟨hf i, ?_⟩, ?_⟩
      · simpa using hdelta i i
      · simpa [hne] using hdelta i j
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨1, by omega⟩
    let k : Fin n := ⟨2, by omega⟩
    let l : Fin n := ⟨3, by omega⟩
    exact hfour (p i) (p j) (p k) (p l)
      (horth i j (by simp [i, j, k, l, Fin.ext_iff])) (horth i k (by simp [i, j, k, l, Fin.ext_iff])) (horth i l (by simp [i, j, k, l, Fin.ext_iff]))
      (horth j k (by simp [i, j, k, l, Fin.ext_iff])) (horth j l (by simp [i, j, k, l, Fin.ext_iff])) (horth k l (by simp [i, j, k, l, Fin.ext_iff]))

#print axioms whole_joint_completion

end D5.S3.Quantum.Foundation.OrthogonalJointCompletion
