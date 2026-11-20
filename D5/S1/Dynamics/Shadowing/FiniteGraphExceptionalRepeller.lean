/- GID: D5/S1/Dynamics/Shadowing/FiniteGraphExceptionalRepeller
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/FiniteGraphExceptionalRepeller
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exclusion of proper finite totally invariant sets in affine graph dynamics. -/

import D5.S1.Dynamics.Shadowing.FiniteGraphBowenArcs
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Algebra.Order.Field.Pi

/-! Local arms at a finite invariant set and the resulting backward invariant neighborhood. -/

open Set Function Filter
open scoped Topology

namespace D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization

noncomputable section

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

private def edgeAt {u v : V} (h : G.Adj u v) (t : ℝ) : Space G :=
  edgeChart G h (Set.projIcc 0 1 zero_le_one t)

private theorem continuous_edgeAt {u v : V} (h : G.Adj u v) :
    Continuous (edgeAt G h) :=
  (continuous_edgeChart G h).comp continuous_projIcc

private theorem edgeAt_of_mem {u v : V} (h : G.Adj u v) {t : ℝ} (ht : t ∈ Icc 0 1) :
    edgeAt G h t = edgeChart G h ⟨t, ht⟩ := by
  simp [edgeAt, Set.projIcc_of_mem _ ht]

variable [Fintype V]

private structure LocalArms (z : Space G) where
  radius : ℝ
  radius_pos : 0 < radius
  indices : Set V
  path : indices → ℝ → Space G
  continuous_path : ∀ i, Continuous (path i)
  dist_path : ∀ i, ∀ t ∈ Icc 0 radius, dist (path i t) z = t
  cover : ∀ x ∈ Metric.ball z radius, x ≠ z → ∃ i, x = path i (dist x z)
  unique : ∀ i j, ∀ t ∈ Ioc 0 radius, path i t = path j t → i = j

private def vertexArms (u : V) : LocalArms G (vertex G u) := by
  refine ⟨1 / 2, by norm_num, {v | G.Adj u v}, fun i => edgeAt G i.property,
    fun i => continuous_edgeAt G i.property, ?_, ?_, ?_⟩
  · intro i t ht
    rw [edgeAt_of_mem G i.property (⟨ht.1, ht.2.trans (by norm_num)⟩ : t ∈ Icc 0 1),
      ← edgeChart_zero G i.property, dist_edgeChart]
    simpa using abs_of_nonneg ht.1
  · intro x hx hne
    have hx' : x ∈ closedStar G u (1 / 2) := by
      rw [closedStar_eq_closedBall G (by norm_num) (by norm_num)]
      exact Metric.ball_subset_closedBall hx
    rcases (mem_closedStar_iff G (by norm_num) (by norm_num)).mp hx' with
      h | ⟨v, h, t, _, rfl⟩
    · exact (hne h).elim
    · refine ⟨⟨v, h⟩, ?_⟩
      have hd : dist (edgeChart G h t) (vertex G u) = (t : ℝ) := by
        rw [← edgeChart_zero G h, dist_edgeChart]
        simpa using abs_of_nonneg t.2.1
      rw [hd]
      exact (edgeAt_of_mem G h t.2).symm
  · intro i j t ht he
    apply Subtype.ext
    by_contra hn
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.trans (by norm_num)⟩
    have hc := congrArg (fun x => coord G x (i : V)) he
    rw [edgeAt_of_mem G i.property ht', edgeAt_of_mem G j.property ht', coord_edgeChart,
      edgeVector_right i.property.ne, coord_edgeChart,
      edgeVector_other i.property.ne.symm hn] at hc
    exact ht.1.ne' hc

private def interiorArms {u v : V} (h : G.Adj u v) (p : Icc (0 : ℝ) 1)
    (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) < 1) : LocalArms G (edgeChart G h p) := by
  let R := min (p : ℝ) (1 - (p : ℝ))
  have hR : 0 < R := lt_min hp₀ (sub_pos.mpr hp₁)
  let param (i : ({u, v} : Set V)) (t : ℝ) : ℝ :=
    if (i : V) = u then (p : ℝ) - t else (p : ℝ) + t
  have bounds (i : ({u, v} : Set V)) {t : ℝ} (ht : t ∈ Icc 0 R) :
      param i t ∈ Icc 0 1 := by
    have hu : t ≤ (p : ℝ) := ht.2.trans (min_le_left _ _)
    have hv : t ≤ 1 - (p : ℝ) := ht.2.trans (min_le_right _ _)
    unfold param
    split <;> constructor <;> linarith [ht.1]
  refine ⟨R, hR, {u, v}, fun i t => edgeAt G h (param i t), ?_, ?_, ?_, ?_⟩
  · intro i
    apply (continuous_edgeAt G h).comp
    by_cases hi : (i : V) = u
    · simp only [param, ite_eq_left hi]
      exact continuous_const.sub continuous_id
    · simp only [param, ite_eq_right hi]
      exact continuous_const.add continuous_id
  · intro i t ht
    rw [edgeAt_of_mem G h (bounds i ht), dist_edgeChart]
    change |param i t - (p : ℝ)| = t
    by_cases hi : (i : V) = u
    · simp only [param, ite_eq_left hi, show (p : ℝ) - t - p = -t by ring,
        abs_neg, abs_of_nonneg ht.1]
    · simp only [param, ite_eq_right hi, add_sub_cancel_left, abs_of_nonneg ht.1]
  · intro x hx _
    have hxu := (dist_le_pi_dist (x : V → ℝ) (edgeChart G h p : V → ℝ) u)
    have hxv := (dist_le_pi_dist (x : V → ℝ) (edgeChart G h p : V → ℝ) v)
    change dist (coord G x u) (coord G (edgeChart G h p) u) ≤ dist x (edgeChart G h p) at hxu
    change dist (coord G x v) (coord G (edgeChart G h p) v) ≤ dist x (edgeChart G h p) at hxv
    rw [Real.dist_eq, coord_edgeChart, edgeVector_left h.ne, abs_le] at hxu
    rw [Real.dist_eq, coord_edgeChart, edgeVector_right h.ne, abs_le] at hxv
    have hd := Metric.mem_ball.mp hx
    obtain ⟨_, q, rfl⟩ := exists_edgeChart_of_two_pos G h.ne
      (show 0 < coord G x u by linarith [hxu.1, hd.trans_le (min_le_right _ _)])
      (show 0 < coord G x v by linarith [hxv.1, hd.trans_le (min_le_left _ _)])
    rw [dist_edgeChart]
    by_cases hqp : (q : ℝ) ≤ (p : ℝ)
    · refine ⟨⟨u, by simp⟩, ?_⟩
      have he : param ⟨u, by simp⟩ |(q : ℝ) - p| = q := by
        simp only [param, ite_eq_left rfl, abs_of_nonpos (sub_nonpos.mpr hqp)]
        ring
      rw [he]
      exact (edgeAt_of_mem G h q.2).symm
    · refine ⟨⟨v, by simp⟩, ?_⟩
      have he : param ⟨v, by simp⟩ |(q : ℝ) - p| = q := by
        simp only [param, ite_eq_right h.ne.symm, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hqp))]
        ring
      rw [he]
      exact (edgeAt_of_mem G h q.2).symm
  · intro i j t ht he
    have hij := congrArg (fun x => coord G x v) he
    rw [edgeAt_of_mem G h (bounds i ⟨ht.1.le, ht.2⟩),
      edgeAt_of_mem G h (bounds j ⟨ht.1.le, ht.2⟩), coord_edgeChart, coord_edgeChart,
      edgeVector_right h.ne, edgeVector_right h.ne] at hij
    change param i t = param j t at hij
    have hi := (mem_insert_iff.mp i.property)
    have hj := (mem_insert_iff.mp j.property)
    simp only [mem_singleton_iff] at hi hj
    apply Subtype.ext
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact hi.trans hj.symm
    · simp only [param, ite_eq_left hi, ite_eq_right (hj.trans_ne h.ne.symm)] at hij
      linarith [ht.1]
    · simp only [param, ite_eq_right (hi.trans_ne h.ne.symm), ite_eq_left hj] at hij
      linarith [ht.1]
    · exact hi.trans hj.symm

private def localArms (z : Space G) : LocalArms G z := by
  have hz : (∃ u, z = vertex G u) ∨
      ∃ (u v : V) (h : G.Adj u v) (p : Icc (0 : ℝ) 1), z = edgeChart G h p := by
    rcases z.property with hv | he
    · obtain ⟨u, hu⟩ := hv
      exact .inl ⟨u, Subtype.ext hu.symm⟩
    · obtain ⟨⟨⟨u, v⟩, h⟩, p, hp⟩ := mem_iUnion.mp he
      exact .inr ⟨u, v, h, p, Subtype.ext hp.symm⟩
  by_cases hv : ∃ u, z = vertex G u
  · rw [Classical.choose_spec hv]
    exact vertexArms G (Classical.choose hv)
  · have he := hz.resolve_left hv
    let u := Classical.choose he
    let v := Classical.choose (Classical.choose_spec he)
    let h : G.Adj u v := Classical.choose (Classical.choose_spec (Classical.choose_spec he))
    let hp := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec he))
    let p := Classical.choose hp
    have hz' : z = edgeChart G h p := Classical.choose_spec hp
    have hp₀ : 0 < (p : ℝ) := by
      refine lt_of_le_of_ne p.2.1 fun h0 => hv ⟨u, ?_⟩
      rw [hz', show p = ⟨0, le_rfl, zero_le_one⟩ from Subtype.ext h0.symm, edgeChart_zero]
    have hp₁ : (p : ℝ) < 1 := by
      refine lt_of_le_of_ne p.2.2 fun h1 => hv ⟨v, ?_⟩
      rw [hz', show p = ⟨1, zero_le_one, le_rfl⟩ from Subtype.ext h1, edgeChart_one]
    exact hz'.symm ▸ interiorArms G h p hp₀ hp₁

namespace LocalArms

variable {G} {z : Space G} (A : LocalArms G z)

private theorem path_zero (i : A.indices) : A.path i 0 = z :=
  dist_eq_zero.mp (A.dist_path i 0 ⟨le_rfl, A.radius_pos.le⟩)

private def arm (i : A.indices) (r : ℝ) : Set (Space G) :=
  A.path i '' Ioo 0 r

private theorem isOpen_arm (i : A.indices) {r : ℝ} (hr : r ≤ A.radius) :
    IsOpen (A.arm i r) := by
  classical
  let C := {z} ∪ ⋃ j : {j : A.indices // j ≠ i}, A.path j.1 '' Icc 0 A.radius
  have hC : IsClosed C := isClosed_singleton.union
    (isClosed_iUnion_of_finite fun j => (isCompact_Icc.image (A.continuous_path j.1)).isClosed)
  suffices A.arm i r = Metric.ball z r \ C by
    rw [this]
    exact Metric.isOpen_ball.sdiff hC
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hd := A.dist_path i t ⟨ht.1.le, ht.2.le.trans hr⟩
    refine ⟨Metric.mem_ball.mpr (by rw [hd]; exact ht.2), ?_⟩
    rintro (he | he)
    · have hz : A.path i t = z := he
      rw [hz, dist_self] at hd
      exact ht.1.ne hd
    · obtain ⟨j, u, hu, he⟩ := mem_iUnion.mp he
      have htu : t = u := by rw [← hd, ← he, A.dist_path j.1 u hu]
      subst u
      exact j.2 (A.unique j.1 i t ⟨ht.1, ht.2.le.trans hr⟩ he)
  · rintro ⟨hx, hnot⟩
    have hne : x ≠ z := fun he => hnot (Or.inl he)
    have hd : dist x z < r := Metric.mem_ball.mp hx
    obtain ⟨j, hj⟩ := A.cover x (Metric.mem_ball.mpr (hd.trans_le hr)) hne
    have hp : 0 < dist x z := dist_pos.mpr hne
    have he : j = i := by
      by_contra hn
      exact hnot (Or.inr (mem_iUnion.mpr ⟨⟨j, hn⟩, dist x z, ⟨hp.le, hd.le.trans hr⟩, hj.symm⟩))
    subst j
    exact ⟨dist x z, ⟨hp, hd⟩, hj.symm⟩

private theorem preconnected_subset_arm {C : Set (Space G)} (hC : IsPreconnected C)
    (hCn : C.Nonempty) (hsub : C ⊆ Metric.ball z A.radius \ {z}) :
    ∃ i, C ⊆ A.arm i A.radius := by
  obtain ⟨x, hx⟩ := hCn
  have hne : x ≠ z := (hsub hx).2
  obtain ⟨i, hi⟩ := A.cover x (hsub hx).1 hne
  refine ⟨i, hC.subset_of_closure_inter_subset (A.isOpen_arm i le_rfl)
    ⟨x, hx, dist x z, ⟨dist_pos.mpr hne, (hsub hx).1⟩, hi.symm⟩ ?_⟩
  rintro y ⟨hycl, hy⟩
  have hclosed : IsClosed (A.path i '' Icc 0 A.radius) :=
    (isCompact_Icc.image (A.continuous_path i)).isClosed
  obtain ⟨t, ht, rfl⟩ := closure_minimal (image_mono Ioo_subset_Icc_self) hclosed hycl
  have hd := A.dist_path i t ht
  refine ⟨t, ⟨?_, ?_⟩, rfl⟩
  · rw [← hd]
    exact dist_pos.mpr (hsub hy).2
  · rw [← hd]
    exact (hsub hy).1

end LocalArms

private theorem exists_common_collar {ι : Type*} [Finite ι] {P : ι → ℝ → Prop}
    (h : ∀ i, ∃ r > 0, ∀ t ∈ Ioo 0 r, P i t) :
    ∃ r > 0, ∀ i, ∀ t ∈ Ioo 0 r, P i t := by
  choose r hr hp using h
  obtain ⟨b, hb, hbr⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ => (0 : ℝ)) (y := r) hr
  exact ⟨b, hb, fun i t ht => hp i t ⟨ht.1, ht.2.trans (by simpa using hbr i)⟩⟩

private theorem exists_small_image {X : Type*} [MetricSpace X]
    {p : ℝ → X} (hp : Continuous p) {U : Set X} (hU : IsOpen U) (h0 : p 0 ∈ U) :
    ∃ r > 0, ∀ t ∈ Ioo 0 r, p t ∈ U := by
  obtain ⟨r, hr, hmap⟩ := Metric.mem_nhds_iff.mp ((hU.preimage hp).mem_nhds h0)
  refine ⟨r, hr, fun t ht => hmap (Metric.mem_ball.mpr ?_)⟩
  simpa [Real.dist_eq, abs_of_nonneg ht.1.le] using ht.2

private theorem exists_idempotent_iterate {ι : Type*} [Finite ι] (F : ι → ι) :
    ∃ q : ℕ, 0 < q ∧ ∀ i, F^[q] (F^[q] i) = F^[q] i := by
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => F^[n])
  obtain ⟨m, n, hmn, hn⟩ : ∃ m n : ℕ, m < n ∧ F^[m] = F^[n] := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b, h, he⟩
    · exact ⟨b, a, h, he.symm⟩
  let d := n - m
  have hd : 0 < d := Nat.sub_pos_of_lt hmn
  let q := d * (m + 1)
  have hq : 0 < q := Nat.mul_pos hd (Nat.succ_pos _)
  have hmq : m ≤ q := calc
    m ≤ m + 1 := Nat.le_succ _
    _ = 1 * (m + 1) := (one_mul _).symm
    _ ≤ q := Nat.mul_le_mul_right _ hd
  refine ⟨q, hq, fun i => ?_⟩
  have hp : IsPeriodicPt F d (F^[m] i) := by
    change F^[d] (F^[m] i) = F^[m] i
    rw [← iterate_add_apply, show d + m = n from Nat.sub_add_cancel hmn.le, ← hn]
  have hp' := (hp.apply_iterate (q - m)).mul_const (m + 1)
  rw [← iterate_add_apply, Nat.sub_add_cancel hmq] at hp'
  exact hp'.eq

private abbrev Arm (E : Set (Space G)) :=
  Σ e : E, (localArms G e.1).indices

private def armPath {E : Set (Space G)} (i : Arm G E) : ℝ → Space G :=
  (localArms G i.1.1).path i.2

private def armRadius {E : Set (Space G)} (i : Arm G E) : ℝ :=
  (localArms G i.1.1).radius

private theorem armPath_zero {E : Set (Space G)} (i : Arm G E) :
    armPath G i 0 = i.1.1 := (localArms G i.1.1).path_zero i.2

private def MapsArm {E : Set (Space G)} (f : Space G → Space G) (i j : Arm G E) : Prop :=
  f i.1.1 = j.1.1 ∧ ∀ r > 0, ∃ b > 0, ∀ t ∈ Ioo 0 b,
    ∃ s ∈ Ioo 0 (min r (armRadius G j)), f (armPath G i t) = armPath G j s

private theorem mapsArm_choose {f : Space G → Space G} (hf : Continuous f)
    {E : Set (Space G)} (hE : E.Finite) (hinv : f ⁻¹' E = E) (i : Arm G E) :
    ∃ j : Arm G E, MapsArm G f i j := by
  let e : E := i.1
  let d : E := ⟨f e, hinv.symm.subset e.2⟩
  let A := localArms G e.1
  let B := localArms G d.1
  let p := f ∘ armPath G i
  have hp : Continuous p := hf.comp (A.continuous_path i.2)
  have hpd : p 0 = d.1 := by simp [p, armPath_zero, d, e]
  obtain ⟨a, ha, hisol⟩ := Metric.mem_nhds_iff.mp
    ((hE.sdiff (t := {e.1})).isClosed.isOpen_compl.mem_nhds (by simp) :
      (E \ {e.1})ᶜ ∈ 𝓝 e.1)
  obtain ⟨b, hb, hsmall⟩ := exists_small_image hp Metric.isOpen_ball
    (show p 0 ∈ Metric.ball d.1 B.radius by rw [hpd]; exact Metric.mem_ball_self B.radius_pos)
  let c := min a (min b A.radius)
  have hc : 0 < c := lt_min ha (lt_min hb A.radius_pos)
  have hsub : p '' Ioo 0 c ⊆ Metric.ball d.1 B.radius \ {d.1} := by
    rintro _ ⟨t, ht, rfl⟩
    have ht' : t ≤ A.radius :=
      ht.2.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hd := A.dist_path i.2 t ⟨ht.1.le, ht'⟩
    refine ⟨hsmall t ⟨ht.1, ht.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩, ?_⟩
    intro he
    have hmem : armPath G i t ∈ E := hinv.subset (by
      change p t ∈ E
      rw [show p t = d.1 from he]
      exact d.2)
    have hball : armPath G i t ∈ Metric.ball e.1 a := Metric.mem_ball.mpr (by
      rw [show dist (armPath G i t) e.1 = t from hd]
      exact ht.2.trans_le (min_le_left _ _))
    apply hisol hball
    refine ⟨hmem, ?_⟩
    intro he'
    change armPath G i t = e.1 at he'
    rw [show A.path i.2 t = armPath G i t from rfl, he', dist_self] at hd
    exact ht.1.ne hd
  obtain ⟨j, hj⟩ := B.preconnected_subset_arm
    (isPreconnected_Ioo.image p hp.continuousOn) ((nonempty_Ioo.mpr hc).image _) hsub
  refine ⟨⟨d, j⟩, rfl, fun r hr => ?_⟩
  obtain ⟨b', hb', hsmall'⟩ := exists_small_image hp Metric.isOpen_ball
    (show p 0 ∈ Metric.ball d.1 r by rw [hpd]; exact Metric.mem_ball_self hr)
  refine ⟨min c b', lt_min hc hb', fun t ht => ?_⟩
  obtain ⟨s, hs, he⟩ := hj ⟨t, ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩, rfl⟩
  have hdist : dist (p t) d.1 = s := by rw [← he]; exact B.dist_path j s ⟨hs.1.le, hs.2.le⟩
  have htr := Metric.mem_ball.mp (hsmall' t ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩)
  exact ⟨s, ⟨hs.1, lt_min (by rwa [hdist] at htr) hs.2⟩, he.symm⟩

private theorem mapsArm_iterate {f : Space G → Space G} {E : Set (Space G)}
    {F : Arm G E → Arm G E} (hF : ∀ i, MapsArm G f i (F i)) (n : ℕ) (i : Arm G E) :
    MapsArm G (f^[n]) i (F^[n] i) := by
  induction n generalizing i with
  | zero =>
    refine ⟨rfl, fun r hr => ?_⟩
    exact ⟨min r (armRadius G i), lt_min hr (localArms G i.1.1).radius_pos,
      fun t ht => ⟨t, ht, rfl⟩⟩
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ']
    refine ⟨(congrArg f (ih i).1).trans (hF (F^[n] i)).1, fun r hr => ?_⟩
    obtain ⟨b, hb, hmap⟩ := (hF (F^[n] i)).2 r hr
    obtain ⟨c, hc, hmap'⟩ := (ih i).2 b hb
    refine ⟨c, hc, fun t ht => ?_⟩
    obtain ⟨s, hs, he⟩ := hmap' t ht
    obtain ⟨u, hu, he'⟩ := hmap s ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩
    exact ⟨u, hu, (congrArg f he).trans he'⟩

private theorem armPath_dist {E : Set (Space G)} (i : Arm G E)
    {t : ℝ} (ht : t ∈ Icc 0 (armRadius G i)) : dist (armPath G i t) i.1.1 = t :=
  (localArms G i.1.1).dist_path i.2 t ht

private theorem repels_arm {f : Space G → Space G} (hf : Continuous f)
    (hfinite : FinitelyPositiveExpansive f) {q : ℕ} (hq : 0 < q)
    {E : Set (Space G)} {i : Arm G E} (hi : MapsArm G (f^[q]) i i) :
    ∃ b > 0, ∀ t ∈ Ioo 0 b, t < dist (f^[q] (armPath G i t)) i.1.1 := by
  let g := f^[q]
  let z := i.1.1
  let p := armPath G i
  have hp : Continuous p := (localArms G z).continuous_path i.2
  have hz : IsFixedPt g z := hi.1
  have hfixed := finite_ptsOfPeriod_of_finitelyPositiveExpansive hf hfinite hq
  obtain ⟨a, ha, hisol⟩ := Metric.mem_nhds_iff.mp
    ((hfixed.sdiff (t := {z})).isClosed.isOpen_compl.mem_nhds (by simp) :
      (ptsOfPeriod f q \ {z})ᶜ ∈ 𝓝 z)
  obtain ⟨ε, hε, N, _, hB⟩ := hfinite
  obtain ⟨δ, hδ, hBδ⟩ := IntervalObstruction.forwardBowenBound_iterate
    isCompact_univ hf.continuousOn (mapsTo_univ f univ) hε hB hq
  have hR := (localArms G z).radius_pos
  obtain ⟨c, hc, hmap⟩ := hi.2 (armRadius G i) hR
  let b := min a (min c (min δ (armRadius G i)))
  have hb : 0 < b := lt_min ha (lt_min hc (lt_min hδ hR))
  have hbR : b ≤ armRadius G i := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hbδ : b ≤ δ := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hbc : b ≤ c := (min_le_right _ _).trans (min_le_left _ _)
  let diff := fun t => dist (g (p t)) z - t
  have hcont : Continuous diff := (((hf.iterate q).comp hp).dist continuous_const).sub continuous_id
  have hne (t : ℝ) (ht : t ∈ Ioo 0 b) : diff t ≠ 0 := by
    intro he
    obtain ⟨s, hs, hsEq⟩ := hmap t ⟨ht.1, ht.2.trans_le hbc⟩
    have hd : dist (g (p t)) z = s := by
      rw [show g (p t) = p s from hsEq]
      exact armPath_dist G i ⟨hs.1.le, hs.2.le.trans (min_le_right _ _)⟩
    have hst : s = t := by
      simpa only [diff, hd, sub_eq_zero] using he
    have htDist := armPath_dist G i ⟨ht.1.le, ht.2.le.trans hbR⟩
    have htball : p t ∈ Metric.ball z a := Metric.mem_ball.mpr (by
      rw [show dist (p t) z = t from htDist]
      exact ht.2.trans_le (min_le_left _ _))
    refine hisol htball ⟨?_, ?_⟩
    · exact show g (p t) = p t from hst ▸ hsEq
    · intro hpt
      change p t = z at hpt
      have htDist' : dist (p t) z = t := htDist
      rw [hpt, dist_self] at htDist'
      exact ht.1.ne htDist'
  refine ⟨b, hb, fun t ht => ?_⟩
  rcases isPreconnected_Ioo.mapsTo_Ioi_or_Iio hcont.continuousOn hne with hpos | hneg
  · exact sub_pos.mp (hpos ht)
  · exfalso
    let d := b / 2
    have hd : 0 < d := by positivity
    have hdb : d < b := half_lt_self hb
    let S := p '' Icc 0 d
    have hzS : z ∈ S := ⟨0, ⟨le_rfl, hd.le⟩, armPath_zero G i⟩
    have hS : MapsTo g S S := by
      rintro _ ⟨u, hu, rfl⟩
      rcases eq_or_lt_of_le hu.1 with he | hpu
      · rw [← he, show p 0 = z from armPath_zero G i, hz.eq]
        exact hzS
      have hu' : u ∈ Ioo 0 b := ⟨hpu, hu.2.trans_lt hdb⟩
      obtain ⟨s, hs, hsEq⟩ := hmap u ⟨hpu, hu'.2.trans_le hbc⟩
      have hd' : dist (g (p u)) z = s := by
        rw [show g (p u) = p s from hsEq]
        exact armPath_dist G i ⟨hs.1.le, hs.2.le.trans (min_le_right _ _)⟩
      have hlt : dist (g (p u)) z < u := sub_neg.mp (hneg hu')
      exact ⟨s, ⟨hs.1.le, (hd' ▸ hlt).le.trans hu.2⟩, hsEq.symm⟩
    have hSfin : S.Finite := IntervalObstruction.finite_of_all_times_small hBδ
      (subset_univ _) z hzS (fun y hy n => by
        obtain ⟨u, hu, he⟩ := hS.iterate n hy
        rw [hz.iterate n, ← he, dist_comm, armPath_dist G i ⟨hu.1, hu.2.trans (hdb.le.trans hbR)⟩]
        exact hu.2.trans_lt (hdb.trans_le hbδ))
    have hinj : InjOn p (Icc 0 d) := by
      intro u hu v hv huv
      have hu' := armPath_dist G i ⟨hu.1, hu.2.trans (hdb.le.trans hbR)⟩
      have hv' := armPath_dist G i ⟨hv.1, hv.2.trans (hdb.le.trans hbR)⟩
      exact hu'.symm.trans ((congrArg (fun y => dist y z) huv).trans hv')
    exact (Icc_infinite hd |>.image hinj) hSfin

private def nearSet (E : Set (Space G)) (r : ℝ) : Set (Space G) :=
  ⋃ z : E, Metric.ball z.1 r

private theorem nearSet_mono {E : Set (Space G)} {r s : ℝ} (h : r ≤ s) :
    nearSet G E r ⊆ nearSet G E s := by
  rintro x hx
  obtain ⟨z, hz⟩ := mem_iUnion.mp hx
  exact mem_iUnion_of_mem z (Metric.ball_subset_ball h hz)

private theorem subset_nearSet {E : Set (Space G)} {r : ℝ} (hr : 0 < r) :
    E ⊆ nearSet G E r :=
  fun x hx => mem_iUnion_of_mem ⟨x, hx⟩ (Metric.mem_ball_self hr)

private theorem exists_nearSet_subset {E U : Set (Space G)} (hE : E.Finite)
    (hU : IsOpen U) (hEU : E ⊆ U) : ∃ r > 0, nearSet G E r ⊆ U := by
  let _ : Finite E := hE.to_subtype
  choose s hs hsub using fun e : E => Metric.mem_nhds_iff.mp (hU.mem_nhds (hEU e.2))
  obtain ⟨r, hr, hlt⟩ := Pi.exists_forall_pos_add_lt (x := fun _ => (0 : ℝ)) (y := s) hs
  refine ⟨r, hr, fun x hx => ?_⟩
  obtain ⟨e, he⟩ := mem_iUnion.mp hx
  exact hsub e (Metric.ball_subset_ball (by simpa using (hlt e).le) he)

omit [Fintype V] in
private theorem iterate_mem_iff {f : Space G → Space G} {E : Set (Space G)}
    (hinv : f ⁻¹' E = E) (n : ℕ) (x : Space G) : f^[n] x ∈ E ↔ x ∈ E := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply']
    exact (show f (f^[n] x) ∈ E ↔ f^[n] x ∈ E from Set.ext_iff.mp hinv _).trans ih

private theorem same_arm {E : Set (Space G)} {i j : Arm G E} {t s : ℝ}
    (hbase : i.1 = j.1) (ht : t ∈ Ioc 0 (armRadius G i))
    (hs : s ∈ Ioc 0 (armRadius G j)) (he : armPath G i t = armPath G j s) :
    i = j ∧ t = s := by
  have hd₁ := armPath_dist G i ⟨ht.1.le, ht.2⟩
  have hd₂ := armPath_dist G j ⟨hs.1.le, hs.2⟩
  rw [he, hbase, hd₂] at hd₁
  subst s
  refine ⟨?_, rfl⟩
  rcases i with ⟨e, i⟩
  rcases j with ⟨d, j⟩
  change e = d at hbase
  subst d
  exact congrArg (Sigma.mk e) ((localArms G e.1).unique i j t ht he)

private theorem exists_exceptional_repeller {f : Space G → Space G}
    (hf : Continuous f) (hfinite : FinitelyPositiveExpansive f)
    {E : Set (Space G)} (hE : E.Finite) (hinv : f ⁻¹' E = E) :
    ∃ q : ℕ, 0 < q ∧ ∀ U : Set (Space G), IsOpen U → E ⊆ U →
      ∃ W : Set (Space G), IsOpen W ∧ E ⊆ W ∧ W ⊆ U ∧ (f^[q]) ⁻¹' W ⊆ W := by
  classical
  let _ : Finite E := hE.to_subtype
  choose F hF using mapsArm_choose G hf hE hinv
  obtain ⟨q, hq, hQQ⟩ := exists_idempotent_iterate F
  let Q := F^[q]
  let g := f^[q]
  have hg : Continuous g := hf.iterate q
  have hgE (x : Space G) : g x ∈ E ↔ x ∈ E := iterate_mem_iff G hinv q x
  have hQ (i : Arm G E) : MapsArm G g i (Q i) := mapsArm_iterate G hF q i
  refine ⟨q, hq, fun U hU hEU => ?_⟩
  obtain ⟨a, ha, haU⟩ := exists_nearSet_subset G hE hU hEU
  obtain ⟨b, hb, hbR⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : E => (0 : ℝ)) (y := fun e => (localArms G e.1).radius)
    (fun e => (localArms G e.1).radius_pos)
  let P := {p : E × E | p.1 ≠ p.2}
  obtain ⟨c, hc, hdist⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : P => (0 : ℝ))
    (y := fun p => dist p.1.1.1 p.1.2.1 / 2)
    (fun p => half_pos (dist_pos.mpr (fun he => p.2 (Subtype.ext he))))
  let R := min a (min b c)
  have hR : 0 < R := lt_min ha (lt_min hb hc)
  have hRa : R ≤ a := min_le_left _ _
  have hRc : R ≤ c := (min_le_right _ _).trans (min_le_right _ _)
  have hRloc (e : E) : R ≤ (localArms G e.1).radius :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans (by simpa using (hbR e).le)
  have hcenter {e d : E} {x : Space G} (he : dist x e.1 < R)
      (hd : dist x d.1 < R) : e = d := by
    by_contra hn
    have hsep := hdist (⟨(e, d), hn⟩ : P)
    change 0 + c < dist e.1 d.1 / 2 at hsep
    linarith [dist_triangle e.1 x d.1, dist_comm e.1 x]
  have hnotE {i : Arm G E} {t : ℝ} (ht : t ∈ Ioc 0 R) (hlt : t < R) :
      armPath G i t ∉ E := by
    intro he
    have hd := armPath_dist G i ⟨ht.1.le, ht.2.trans (hRloc i.1)⟩
    have he' : (⟨armPath G i t, he⟩ : E) = i.1 :=
      hcenter (x := armPath G i t) (by simpa using hR) (by rwa [hd])
    have hp := congrArg Subtype.val he'
    change armPath G i t = i.1.1 at hp
    rw [hp, dist_self] at hd
    exact ht.1.ne hd
  have hcollar (i : Arm G E) : ∃ l > 0, ∀ t ∈ Ioo 0 l,
      ∃ u ∈ Ioo 0 (min R (armRadius G (Q i))),
        g (armPath G i t) = armPath G (Q i) u ∧ (Q i = i → t < u) := by
    obtain ⟨l, hl, hmap⟩ := (hQ i).2 R hR
    by_cases he : Q i = i
    · obtain ⟨b', hb', hrep⟩ := repels_arm G hf hfinite hq (he ▸ hQ i)
      refine ⟨min l b', lt_min hl hb', fun t ht => ?_⟩
      obtain ⟨u, hu, huEq⟩ := hmap t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
      refine ⟨u, hu, huEq, fun _ => ?_⟩
      have hlt := hrep t ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩
      change t < dist (g (armPath G i t)) i.1.1 at hlt
      rw [huEq, ← show (Q i).1.1 = i.1.1 from congrArg (fun j : Arm G E => j.1.1) he,
        armPath_dist G (Q i) ⟨hu.1.le, hu.2.le.trans (min_le_right _ _)⟩] at hlt
      exact hlt
    · exact ⟨l, hl, fun t ht => by
        obtain ⟨u, hu, huEq⟩ := hmap t ht
        exact ⟨u, hu, huEq, fun contra => (he contra).elim⟩⟩
  obtain ⟨l, hl, hlocal⟩ := exists_common_collar hcollar
  let L := min l (R / 2)
  have hL : 0 < L := lt_min hl (half_pos hR)
  have hLR : L < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have hLsub (i : Arm G E) : L ≤ armRadius G i := hLR.le.trans (hRloc i.1)
  -- Every preimage of a sufficiently small neighborhood of E lies in these collars.
  let S := nearSet G E L
  have hS : IsOpen S := isOpen_iUnion fun _ => Metric.isOpen_ball
  have hES : E ⊆ S := subset_nearSet G hL
  have hclosed : IsClosed (g '' Sᶜ) := (hS.isClosed_compl.isCompact.image hg).isClosed
  have hdisj : E ⊆ (g '' Sᶜ)ᶜ := by
    rintro _ hx ⟨y, hy, rfl⟩
    exact hy (hES ((hgE y).mp hx))
  obtain ⟨s₀, hs₀, hs₀sub⟩ := exists_nearSet_subset G hE hclosed.isOpen_compl hdisj
  let s := min s₀ L
  have hs : 0 < s := lt_min hs₀ hL
  have hsL : s ≤ L := min_le_right _ _
  have hpre : g ⁻¹' nearSet G E s ⊆ S := by
    intro x hx
    have havoid := hs₀sub (nearSet_mono G (min_le_left s₀ L) hx)
    by_contra hn
    exact havoid ⟨x, hn, rfl⟩
  -- The inner collars avoid the image of the compact outer pieces.
  let K := ⋃ i : Arm G E, armPath G i '' Icc s L
  have hK : IsCompact K := isCompact_iUnion fun i =>
    isCompact_Icc.image ((localArms G i.1.1).continuous_path i.2)
  have hKg : E ⊆ (g '' K)ᶜ := by
    rintro _ hx ⟨y, hy, rfl⟩
    obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.mp hy
    exact hnotE ⟨hs.trans_le ht.1, ht.2.trans hLR.le⟩
      (ht.2.trans_lt hLR) ((hgE _).mp hx)
  obtain ⟨r₀, hr₀, hr₀sub⟩ := exists_nearSet_subset G hE
    (hK.image hg).isClosed.isOpen_compl hKg
  let r := min r₀ s
  have hr : 0 < r := lt_min hr₀ hs
  have hrs : r ≤ s := min_le_right _ _
  let width (i : Arm G E) := if Q i = i then r else s
  have hwidth (i : Arm G E) : r ≤ width i ∧ width i ≤ s := by
    dsimp [width]
    split <;> exact ⟨by first | exact le_rfl | exact hrs, by first | exact hrs | exact le_rfl⟩
  let W := E ∪ ⋃ i : Arm G E, (localArms G i.1.1).arm i.2 (width i)
  have hWnear : W ⊆ nearSet G E s := by
    rintro x (hx | hx)
    · exact subset_nearSet G hs hx
    · obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.mp hx
      have hts := ht.2.trans_le (hwidth i).2
      refine mem_iUnion_of_mem i.1 (Metric.mem_ball.mpr ?_)
      change dist (armPath G i t) i.1.1 < s
      rw [armPath_dist G i ⟨ht.1.le, hts.le.trans (hsL.trans (hLsub i))⟩]
      exact hts
  have hnearW : nearSet G E r ⊆ W := by
    intro x hx
    obtain ⟨e, he⟩ := mem_iUnion.mp hx
    by_cases heq : x = e.1
    · exact Or.inl (heq ▸ e.2)
    have hd : dist x e.1 < r := he
    obtain ⟨i, hi⟩ := (localArms G e.1).cover x
      (Metric.mem_ball.mpr (hd.trans_le (hrs.trans (hsL.trans (hLR.le.trans (hRloc e)))))) heq
    let j : Arm G E := ⟨e, i⟩
    exact Or.inr (mem_iUnion_of_mem j ⟨dist x e.1,
      ⟨dist_pos.mpr heq, hd.trans_le (hwidth j).1⟩, hi.symm⟩)
  have hWo : IsOpen W := by
    have heq : W = nearSet G E r ∪ ⋃ i : Arm G E, (localArms G i.1.1).arm i.2 (width i) :=
      le_antisymm (union_subset_union_left _ (subset_nearSet G hr))
        (union_subset hnearW subset_union_right)
    rw [heq]
    exact (isOpen_iUnion fun _ => Metric.isOpen_ball).union
      (isOpen_iUnion fun i => (localArms G i.1.1).isOpen_arm i.2
        ((hwidth i).2.trans (hsL.trans (hLsub i))))
  refine ⟨W, hWo, subset_union_left,
    hWnear.trans ((nearSet_mono G (hsL.trans (hLR.le.trans hRa))).trans haU), ?_⟩
  intro x hx
  have hxs : x ∈ S := hpre (hWnear hx)
  by_cases hxE : x ∈ E
  · exact Or.inl hxE
  obtain ⟨e, he⟩ := mem_iUnion.mp hxs
  have hxe : x ≠ e.1 := fun h => hxE (h ▸ e.2)
  let t := dist x e.1
  have ht : t ∈ Ioo 0 L := ⟨dist_pos.mpr hxe, he⟩
  obtain ⟨i, hi⟩ := (localArms G e.1).cover x
    (Metric.mem_ball.mpr (ht.2.trans_le (hLR.le.trans (hRloc e)))) hxe
  let j : Arm G E := ⟨e, i⟩
  change x = armPath G j t at hi
  obtain ⟨u, hu, hgx, hlt⟩ := hlocal j t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
  have hgx' : g x = armPath G (Q j) u := by rw [hi]; exact hgx
  rcases (show g x ∈ W from hx) with hgE' | hW'
  · exact (hxE ((hgE _).mp hgE')).elim
  obtain ⟨k, v, hv, hvEq⟩ := mem_iUnion.mp hW'
  change armPath G k v = g x at hvEq
  have huR : u < R := hu.2.trans_le (min_le_left _ _)
  have huR' : u ≤ armRadius G (Q j) := hu.2.le.trans (min_le_right _ _)
  have hvS : v < s := hv.2.trans_le (hwidth k).2
  have hvR : v ≤ armRadius G k := hvS.le.trans (hsL.trans (hLsub k))
  have hbase : (Q j).1 = k.1 := hcenter (x := g x)
    (by rw [hgx', armPath_dist G (Q j) ⟨hu.1.le, huR'⟩]; exact huR)
    (by rw [← hvEq, armPath_dist G k ⟨hv.1.le, hvR⟩]; exact hvS.trans_le (hsL.trans hLR.le))
  obtain ⟨hk, huv⟩ := same_arm G hbase ⟨hu.1, huR'⟩ ⟨hv.1, hvR⟩ (hgx'.symm.trans hvEq.symm)
  subst k
  have hvsmall : v < r := by
    have hfix : Q (Q j) = Q j := hQQ j
    simpa [width, hfix] using hv.2
  refine Or.inr (mem_iUnion_of_mem j ⟨t, ⟨ht.1, ?_⟩, hi.symm⟩)
  by_cases hfix : Q j = j
  · rw [show width j = r by simp [width, hfix]]
    exact (hlt hfix).trans (by rwa [huv])
  · rw [show width j = s by simp [width, hfix]]
    by_contra hn
    have htK : x ∈ K := mem_iUnion_of_mem j ⟨t, ⟨le_of_not_gt hn, ht.2.le⟩, hi.symm⟩
    have hgnear : g x ∈ nearSet G E r₀ := by
      refine mem_iUnion_of_mem (Q j).1 (Metric.mem_ball.mpr ?_)
      rw [hgx', armPath_dist G (Q j) ⟨hu.1.le, huR'⟩, huv]
      exact hvsmall.trans_le (min_le_left _ _)
    exact hr₀sub hgnear ⟨x, htK, rfl⟩

/-- A proper finite totally invariant set of a continuous, topologically transitive,
finitely positively expansive map on a finite affine graph is empty. -/
theorem finite_totally_invariant_eq_empty {f : Space G → Space G} (hf : Continuous f)
    (htrans : ∀ A B : Set (Space G), IsOpen A → A.Nonempty → IsOpen B → B.Nonempty →
      ∃ n : ℕ, (f^[n] '' A ∩ B).Nonempty)
    (hfinite : FinitelyPositiveExpansive f) {E : Set (Space G)}
    (hE : E.Finite) (hinv : f ⁻¹' E = E) (hproper : E ≠ univ) : E = ∅ := by
  by_contra hne
  obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.mpr hne
  obtain ⟨a, ha⟩ := nonempty_compl.mpr hproper
  obtain ⟨q, hq, hrep⟩ := exists_exceptional_repeller G hf hfinite hE hinv
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (hE.isClosed.isOpen_compl.mem_nhds ha)
  let K := Metric.closedBall a (ρ / 2)
  have hK : IsCompact K := Metric.isClosed_closedBall.isCompact
  have hKsub : K ⊆ Eᶜ := fun _ hx => hρsub
    (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt (half_lt_self hρ)))
  let U := (⋃ i : Fin q, f^[i.1] '' K)ᶜ
  have hU : IsOpen U := (isClosed_iUnion_of_finite fun i : Fin q =>
    (hK.image (hf.iterate i.1)).isClosed).isOpen_compl
  have hEU : E ⊆ U := by
    intro x hx hbad
    obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hbad
    exact hKsub hy ((iterate_mem_iff G hinv i.1 y).mp hx)
  obtain ⟨W, hW, hEW, hWU, hback⟩ := hrep U hU hEU
  let B := ⋃ i : Fin q, (f^[i.1]) ⁻¹' W
  have hB : IsOpen B := isOpen_iUnion fun i => hW.preimage (hf.iterate i.1)
  have hWB : W ⊆ B := fun x hx => mem_iUnion_of_mem (⟨0, hq⟩ : Fin q) (by simpa using hx)
  have hBback : f ⁻¹' B ⊆ B := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hh : f^[i.1 + 1] x ∈ W := by
      rw [iterate_succ_apply]
      exact hi
    by_cases hlt : i.1 + 1 < q
    · exact mem_iUnion_of_mem (⟨i.1 + 1, hlt⟩ : Fin q) hh
    · have he : i.1 + 1 = q := by omega
      rw [he] at hh
      exact hWB (hback hh)
  have hdisj : Disjoint K B := by
    rw [Set.disjoint_left]
    intro x hx hxB
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxB
    exact hWU hi (mem_iUnion_of_mem i ⟨x, hx, rfl⟩)
  obtain ⟨n, _, ⟨x, hx, rfl⟩, hxB⟩ := htrans (Metric.ball a (ρ / 2)) B
    Metric.isOpen_ball ⟨a, Metric.mem_ball_self (half_pos hρ)⟩ hB ⟨z, hWB (hEW hz)⟩
  have hbackn (n : ℕ) : (f^[n]) ⁻¹' B ⊆ B := by
    induction n with
    | zero => exact subset_rfl
    | succ n ih =>
      intro x hx
      change f^[n + 1] x ∈ B at hx
      rw [iterate_succ_apply'] at hx
      exact ih (hBback hx)
  exact Set.disjoint_left.mp hdisj (Metric.ball_subset_closedBall hx) (hbackn n hxB)

/-- On a finite affine graph with an edge, every finite totally invariant set
of a continuous, topologically transitive, finitely positively expansive map is empty. -/
theorem finite_totally_invariant_eq_empty_of_adj {u v : V} (h : G.Adj u v)
    {f : Space G → Space G} (hf : Continuous f)
    (htrans : ∀ A B : Set (Space G), IsOpen A → A.Nonempty → IsOpen B → B.Nonempty →
      ∃ n : ℕ, (f^[n] '' A ∩ B).Nonempty)
    (hfinite : FinitelyPositiveExpansive f) {E : Set (Space G)}
    (hE : E.Finite) (hinv : f ⁻¹' E = E) : E = ∅ := by
  apply finite_totally_invariant_eq_empty G hf htrans hfinite hE hinv
  intro hAll
  have hinj : InjOn (edgeAt G h) (Icc 0 1) := by
    intro s hs t ht he
    have hc := congrArg (fun x => coord G x v) he
    simpa only [edgeAt_of_mem G h hs, edgeAt_of_mem G h ht, coord_edgeChart,
      edgeVector_right h.ne] using hc
  apply (Icc_infinite (zero_lt_one : (0 : ℝ) < 1)).image hinj
  apply hE.subset
  rw [hAll]
  exact subset_univ _

#print axioms finite_totally_invariant_eq_empty
#print axioms finite_totally_invariant_eq_empty_of_adj

end

end D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization
