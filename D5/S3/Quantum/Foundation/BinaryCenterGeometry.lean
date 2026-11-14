/- GID: D5/S3/Quantum/Foundation/BinaryCenterGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/BinaryCenterGeometry
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Reciprocal original repeated fibers and their common separating effect. -/

import D5.S3.Quantum.Foundation.ActualExclusionBoundary
import D5.S3.Quantum.Foundation.UniqueConfirmationDensity
import D5.S3.Geometry.AffineBallRigidity

/-! Geometry on the entire original base and effect interval. The exclusion
center is the existing `ContinuousFrameSum.center`; no classifier or global
injectivity assumption is added. -/

noncomputable section
open Set
open scoped RealInnerProductSpace BigOperators

namespace D5.S3.Quantum.Foundation.BinaryCenterGeometry

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open OriginalFacePolarity SingleLabelNormalBody ContinuousFrameSum

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- Binary compatibility uses all original endpoints and independent weights,
including repeated endpoints and zero weights. -/
def binaryCompatible (hB : exclusionBalls C u) : Prop :=
  ∀ (p q r s : pure C u) (t v : ℝ), t ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 →
    t • (p : V) + (1-t) • (q : V) = v • (r : V) + (1-v) • (s : V) →
    t • center hB p + (1-t) • center hB q =
      v • center hB r + (1-v) • center hB s

variable (hc : IsClosed (C : Set V))
  (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
  (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)

include hc hs hg hB in
/-- Both complete label fibers are the opposite original pure spheres.
The partner is determined from any original pure point of the first ball. -/
theorem repeated_partner_fibers (p s q : pure C u) (hps : p ≠ s)
    (hsp : exclusion C u s = exclusion C u p) (hq : (q : V) ∈ exclusion C u p) :
    (∀ r : pure C u, exclusion C u r = exclusion C u q ↔
      (r : V) ∈ exclusion C u p) ∧
    (∀ r : pure C u, exclusion C u r = exclusion C u p ↔
      (r : V) ∈ exclusion C u q) ∧
    Disjoint (exclusion C u p) (exclusion C u q) := by
  have hpq := (exclusion_symmetric p q).mp hq
  have hsq := (exclusion_symmetric s q).mp (hsp.symm ▸ hq)
  have forward (r : pure C u) (hr : (r : V) ∈ exclusion C u p) :
      exclusion C u r = exclusion C u q := by
    apply equal_of_two_points hc hs hg hB r q (Subtype.val_injective.ne hps)
    · exact ⟨(exclusion_symmetric p r).mp hr, hpq⟩
    · exact ⟨(exclusion_symmetric s r).mp (hsp.symm ▸ hr), hsq⟩
  have hfirst : ∀ r : pure C u, exclusion C u r = exclusion C u q ↔
      (r : V) ∈ exclusion C u p := by
    intro r
    constructor
    · intro he
      exact (exclusion_symmetric p r).mpr (he.symm ▸ hpq)
    · exact forward r
  have hsecond : ∀ r : pure C u, exclusion C u r = exclusion C u p ↔
      (r : V) ∈ exclusion C u q := by
    intro r
    constructor
    · intro he
      exact (exclusion_symmetric r q).mp (he.symm ▸ hq)
    · intro hr
      obtain ⟨a, b, ha, hb, hab⟩ := pure_pair_in_ball hc hs hg hB p
      have ha' := (exclusion_symmetric a r).mp ((forward a ha).symm ▸ hr)
      have hb' := (exclusion_symmetric b r).mp ((forward b hb).symm ▸ hr)
      exact equal_of_two_points hc hs hg hB r p (Subtype.val_injective.ne hab)
        ⟨ha', ha⟩ ⟨hb', hb⟩
  refine ⟨hfirst, hsecond, ?_⟩
  rcases ActualExclusionBoundary.repeated_ball_isolated hc hs hg hB p s hps hsp q
      with he | hd
  · have hself : (p : V) ∈ exclusion C u p := he.symm ▸ hpq
    obtain ⟨_, f, hf, hz⟩ := hself
    exact (by linarith [hf.2] : False).elim
  · exact hd

include hc hs hg in
/-- A nonnegative original annihilator of the first sphere attains its
maximum on the actual opposite ball. -/
private theorem annihilator_maximum_on_partner (p q : pure C u)
    (hq : (q : V) ∈ exclusion C u p)
    (g : V →ₗ[ℝ] ℝ) (hg0 : g ≠ 0) (hpos : ∀ x ∈ C, 0 ≤ g x)
    (hzero : ∀ x ∈ exclusion C u p, g x = 0) :
    ∃ r : pure C u, (r : V) ∈ exclusion C u q ∧
      0 < g r ∧ ∀ x ∈ base C u, g x ≤ g r := by
  obtain ⟨r, hr, hgr, hmax⟩ :=
    positive_annihilator_maximum hc hs hg q g hg0 hpos (hzero q hq)
  exact ⟨r, hr, hgr, hmax⟩

include hc hs hg hB in
/-- The repeated pair has one original effect whose entire zero and one
faces are precisely the two whole original balls. -/
theorem repeated_pair_separating_effect (p s q : pure C u) (hps : p ≠ s)
    (hsp : exclusion C u s = exclusion C u p) (hq : (q : V) ∈ exclusion C u p) :
    ∃ e : V →ₗ[ℝ] ℝ, proper C u e ∧
      {x | x ∈ base C u ∧ e x = 0} = exclusion C u p ∧
      {x | x ∈ base C u ∧ e x = 1} = exclusion C u q := by
  classical
  have hfib := repeated_partner_fibers hc hs hg hB p s q hps hsp hq
  let b := (hB q).some
  have : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
  obtain ⟨n, hn⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin b.dim)) zero_le_one
  have hbd := chart_boundary hc hs hg hB q b
  have hplus : b.param n ∈ exclusion C u q ∩ pure C u :=
    hbd.symm ▸ ⟨n, by simpa using hn, rfl⟩
  have hminus : b.param (-n) ∈ exclusion C u q ∩ pure C u :=
    hbd.symm ▸ ⟨-n, by simpa using hn, rfl⟩
  let a : pure C u := ⟨b.param n, hplus.2⟩
  let d : pure C u := ⟨b.param (-n), hminus.2⟩
  have ha : exclusion C u a = exclusion C u p := (hfib.2.1 a).mpr hplus.1
  have hd : exclusion C u d = exclusion C u p := (hfib.2.1 d).mpr hminus.1
  obtain ⟨f, hf, hfzero⟩ := (exclusion_ball_faces hc hs hg hB).1 a |>.2.2.2.2.2.2
  obtain ⟨g, hgg, hgzero⟩ := (exclusion_ball_faces hc hs hg hB).1 d |>.2.2.2.2.2.2
  have fzero (x) (hx : x ∈ exclusion C u p) : f x = 0 :=
    (show x ∈ {x | x ∈ base C u ∧ f x = 0} from hfzero ▸ ha.symm ▸ hx).2
  have gzero (x) (hx : x ∈ exclusion C u p) : g x = 0 :=
    (show x ∈ {x | x ∈ base C u ∧ g x = 0} from hgzero ▸ hd.symm ▸ hx).2
  have mem (z) (hz : ‖z‖ ≤ 1) : b.param z ∈ base C u :=
    (show b.param z ∈ exclusion C u q from b.whole ▸ ⟨z, by simpa using hz, rfl⟩).1
  have hu (z) : u (b.param z) = 1 := by
    rw [show b.param z = b.param.linear z + b.param 0 from congrFun b.param.decomp z,
      map_add, chart_unit_linear b z, (mem 0 (by simp)).2, zero_add]
  let α : ℝ := (1 - f (b.param (-n))) / 2
  let β : ℝ := (1 - g (b.param n)) / 2
  have hα : 0 ≤ α ∧ α ≤ 1/2 := by
    have h := hf.1 _ hminus.1.1.1
    rw [hminus.1.1.2] at h
    dsimp [α]; constructor <;> linarith
  have hβ : 0 ≤ β ∧ β ≤ 1/2 := by
    have h := hgg.1 _ hplus.1.1.1
    rw [hplus.1.1.2] at h
    dsimp [β]; constructor <;> linarith
  have fformula (z) : f (b.param z) = 1 - α + α * ⟪n, z⟫ := by
    have h := WholePairBallConfirmation.affine_zero_antipode
      ((u-f).toAffineMap.comp b.param) (show ‖-n‖ = 1 by simpa using hn)
      (fun z hz => sub_nonneg.mpr (hf.1 _ (mem z hz).1).2)
      (by simp [a, hf.2, (pure_mem a).2]) z
    change u (b.param z) - f (b.param z) =
      (u (b.param (-n)) - f (b.param (-n))) / 2 * (1 + ⟪-n, z⟫) at h
    rw [hu, hu] at h
    simp only [inner_neg_left] at h
    dsimp [α]
    linarith
  have gformula (z) : g (b.param z) = 1 - β - β * ⟪n, z⟫ := by
    have h := WholePairBallConfirmation.affine_zero_antipode
      ((u-g).toAffineMap.comp b.param) hn
      (fun z hz => sub_nonneg.mpr (hgg.1 _ (mem z hz).1).2)
      (by change u (b.param (-n)) - g (b.param (-n)) = 0
          rw [(pure_mem d).2, hgg.2]; ring) z
    change u (b.param z) - g (b.param z) =
      (u (b.param n) - g (b.param n)) / 2 * (1 + ⟪n, z⟫) at h
    rw [hu, hu] at h
    dsimp [β]
    linarith
  have construct (l : V →ₗ[ℝ] ℝ) (hlpos : ∀ x ∈ C, 0 ≤ l x)
      (hlzero : ∀ x ∈ exclusion C u p, l x = 0) (k : ℝ) (hk : 0 < k)
      (hlconst : ∀ x ∈ exclusion C u q, l x = k) :
      ∃ e : V →ₗ[ℝ] ℝ, proper C u e ∧
        {x | x ∈ base C u ∧ e x = 0} = exclusion C u p ∧
        {x | x ∈ base C u ∧ e x = 1} = exclusion C u q := by
    have hl0 : l ≠ 0 := by
      intro he
      have h := hlconst p ((exclusion_symmetric p q).mp hq)
      simp [he] at h
      linarith
    obtain ⟨r, hr, _, hmax⟩ := annihilator_maximum_on_partner hc hs hg p q hq
      l hl0 hlpos hlzero
    let e : V →ₗ[ℝ] ℝ := k⁻¹ • l
    have he : proper C u e := cone_bound (base_compact hc hs) hs (fun t => by
      change 0 ≤ k⁻¹ * l t ∧ k⁻¹ * l t ≤ 1
      refine ⟨mul_nonneg (inv_nonneg.mpr hk.le) (hlpos t (pure_mem t).1), ?_⟩
      rw [← div_eq_inv_mul, div_le_one hk]
      exact (hmax t (pure_mem t)).trans_eq (hlconst r hr))
    have ezero (x) (hx : x ∈ exclusion C u p) : e x = 0 := by simp [e, hlzero x hx]
    have eone (x) (hx : x ∈ exclusion C u q) : e x = 1 := by simp [e, hlconst x hx, hk.ne']
    refine ⟨e, he, Set.ext fun x => ?_, Set.ext fun x => ?_⟩
    · constructor
      · rintro ⟨hx, hz⟩
        exact ⟨hx, e, ⟨he, eone p ((exclusion_symmetric p q).mp hq)⟩, hz⟩
      · intro hx
        exact ⟨hx.1, ezero x hx⟩
    · constructor
      · rintro ⟨hx, ho⟩
        refine ⟨hx, u-e, ⟨?_, ?_⟩, ?_⟩
        · intro y hy
          have h := he y hy
          change 0 ≤ u y - e y ∧ u y - e y ≤ u y
          constructor <;> linarith
        · change u q - e q = 1
          rw [(pure_mem q).2, ezero q hq]; ring
        · change u x - e x = 0
          rw [hx.2, ho]; ring
      · intro hx
        exact ⟨hx.1, eone x hx⟩
  by_cases hα0 : α = 0
  · apply construct f (fun x hx => (hf.1 x hx).1) fzero 1 zero_lt_one
    rintro x hx
    obtain ⟨z, _, rfl⟩ := b.whole.symm ▸ hx
    simp [fformula, hα0]
  by_cases hβ0 : β = 0
  · apply construct g (fun x hx => (hgg.1 x hx).1) gzero 1 zero_lt_one
    rintro x hx
    obtain ⟨z, _, rfl⟩ := b.whole.symm ▸ hx
    simp [gformula, hβ0]
  apply construct (β • f + α • g) (fun x hx =>
    add_nonneg (mul_nonneg hβ.1 (hf.1 x hx).1) (mul_nonneg hα.1 (hgg.1 x hx).1))
    (by intro x hx; simp [fzero x hx, gzero x hx]) (α + β - 2*α*β)
  · have hapos := lt_of_le_of_ne hα.1 (Ne.symm hα0)
    have hbpos := lt_of_le_of_ne hβ.1 (Ne.symm hβ0)
    nlinarith [mul_nonneg hα.1 (show 0 ≤ 1-2*β by linarith)]
  · rintro x hx
    obtain ⟨z, _, rfl⟩ := b.whole.symm ▸ hx
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, fformula, gformula]
    ring

/-- Choice-independent equality of the existing original centers. -/
theorem center_eq_of_exclusion_eq (p q : pure C u)
    (he : exclusion C u p = exclusion C u q) : center hB p = center hB q := by
  have decomp (r : pure C u) (x) :
      (hB r).some.param x = (hB r).some.param 0 +
        (hB r).some.param.linear.toContinuousLinearMap x := by
    simpa [add_comm] using congrFun (hB r).some.param.decomp x
  apply D5.S3.Geometry.AffineBallRigidity.center_eq_of_ball_eq
    (center hB p) (center hB q) (hB p).some.param.linear.toContinuousLinearMap
    (hB q).some.param.linear.toContinuousLinearMap
  simpa only [ContinuousFrameSum.center, ← decomp] using
    (hB p).some.whole.trans (he.trans (hB q).some.whole.symm)

/-- Original centers are relative interior points of their own whole balls. -/
private theorem center_interior (p : pure C u) :
    center hB p ∈ intrinsicInterior ℝ (exclusion C u p) := by
  rw [MixedExclusionGeometry.chart_intrinsic p (hB p).some]
  exact ⟨0, by simp, rfl⟩

include hc hs hg hB in
/-- A strict mixture of centers of disjoint whole original balls belongs
to no original exclusion. -/
private theorem center_chord_not_excluded (p q r : pure C u)
    (hd : Disjoint (exclusion C u p) (exclusion C u q))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1-t) • center hB p + t • center hB q ∉ exclusion C u r := by
  intro hz
  have all := (exclusion_ball_faces hc hs hg hB).1
  have cp := intrinsicInterior_subset (center_interior hB p)
  have cq := intrinsicInterior_subset (center_interior hB q)
  have hseg : (1-t) • center hB p + t • center hB q ∈
      openSegment ℝ (center hB p) (center hB q) :=
    ⟨1-t, t, by linarith [ht.2], ht.1, by ring, rfl⟩
  have hp := (all r).2.2.2.2.1.left_mem_of_mem_openSegment cp.1 cq.1 hz hseg
  have hq := (all r).2.2.2.2.1.right_mem_of_mem_openSegment cp.1 cq.1 hz hseg
  obtain ⟨f, hf, hzero⟩ := (all r).2.2.2.2.2.2
  have fp : f (center hB p) = 0 := (hzero ▸ hp).2
  have fq : f (center hB q) = 0 := (hzero ▸ hq).2
  have hFp : exclusion C u p ⊆ exclusion C u r := by
    intro x hx
    rw [hzero]
    exact ⟨hx.1, UniqueConfirmationDensity.zero_on_exclusion_of_zero_interior hB p f
      (fun x hx => (hf.1 x hx).1) (center_interior hB p) fp x hx⟩
  have hFq : exclusion C u q ⊆ exclusion C u r := by
    intro x hx
    rw [hzero]
    exact ⟨hx.1, UniqueConfirmationDensity.zero_on_exclusion_of_zero_interior hB q f
      (fun x hx => (hf.1 x hx).1) (center_interior hB q) fq x hx⟩
  have hpr := chart_face_eq (hB r).some (all p).2.2.1
    ((all p).2.2.2.2.1.mono (all r).2.2.2.2.1.subset hFp) (all p).1
  have hqr := chart_face_eq (hB r).some (all q).2.2.1
    ((all q).2.2.2.2.1.mono (all r).2.2.2.2.1.subset hFq) (all q).1
  exact Set.disjoint_left.mp hd cp (hqr.symm ▸ hpr ▸ cp)

include hc hs hg hB in
/-- Every finite mixture relation inside the actual repeated block preserves
the original centers; zero coefficients and repeated labels remain in scope. -/
theorem repeated_block_finite_compatibility (p s q : pure C u) (hps : p ≠ s)
    (hsp : exclusion C u s = exclusion C u p) (hq : (q : V) ∈ exclusion C u p) :
    ∀ (n m : ℕ) (a : Fin n → pure C u) (b : Fin m → pure C u)
      (w : Fin n → ℝ) (v : Fin m → ℝ),
      (∀ i, (a i : V) ∈ exclusion C u p ∪ exclusion C u q) →
      (∀ j, (b j : V) ∈ exclusion C u p ∪ exclusion C u q) →
      (∑ i, w i) = 1 → (∑ j, v j) = 1 →
      (∑ i, w i • (a i : V)) = (∑ j, v j • (b j : V)) →
      (∑ i, w i • center hB (a i)) = (∑ j, v j • center hB (b j)) := by
  obtain ⟨e, he, ez, eo⟩ := repeated_pair_separating_effect hc hs hg hB p s q hps hsp hq
  have fibers := repeated_partner_fibers hc hs hg hB p s q hps hsp hq
  let J (x : V) := center hB q + e x • (center hB p - center hB q)
  have agrees (r : pure C u) (hr : (r : V) ∈ exclusion C u p ∪ exclusion C u q) :
      center hB r = J r := by
    rcases hr with hr | hr
    · have hzr : e r = 0 := (show (r : V) ∈ {x | x ∈ base C u ∧ e x = 0}
        from ez.symm ▸ hr).2
      simpa [J, hzr] using center_eq_of_exclusion_eq hB r q ((fibers.1 r).mpr hr)
    · have hor : e r = 1 := (show (r : V) ∈ {x | x ∈ base C u ∧ e x = 1}
        from eo.symm ▸ hr).2
      simpa [J, hor] using center_eq_of_exclusion_eq hB r p ((fibers.2.1 r).mpr hr)
  have sums {n : ℕ} (a : Fin n → pure C u) (w : Fin n → ℝ)
      (hw : (∑ i, w i) = 1) :
      (∑ i, w i • J (a i)) = J (∑ i, w i • (a i : V)) := by
    simp only [J, smul_add, smul_smul, Finset.sum_add_distrib,
      ← Finset.sum_smul, hw, one_smul, map_sum, map_smul, smul_eq_mul]
  intro n m a b w v ha hb hw hv hab
  simp_rw [agrees _ (ha _), agrees _ (hb _)]
  rw [sums a w hw, sums b v hv, hab]

include hc hs hg hB in
/-- Binary compatibility excludes one outside endpoint and three endpoints
of the same actual repeated block, with both mixing parameters strictly active. -/
theorem repeated_block_one_outside (hBC : binaryCompatible hB)
    (p s q : pure C u) (hps : p ≠ s)
    (hsp : exclusion C u s = exclusion C u p) (hq : (q : V) ∈ exclusion C u p)
    (r a b d : pure C u) (t v : ℝ)
    (hr : (r : V) ∉ exclusion C u p ∪ exclusion C u q)
    (ha : (a : V) ∈ exclusion C u p ∪ exclusion C u q)
    (hb : (b : V) ∈ exclusion C u p ∪ exclusion C u q)
    (hd : (d : V) ∈ exclusion C u p ∪ exclusion C u q)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    t • (r : V) + (1-t) • (a : V) ≠ v • (b : V) + (1-v) • (d : V) := by
  intro hab
  obtain ⟨e, he, ez, eo⟩ := repeated_pair_separating_effect hc hs hg hB p s q hps hsp hq
  have fibers := repeated_partner_fibers hc hs hg hB p s q hps hsp hq
  let J (x : V) := center hB q + e x • (center hB p - center hB q)
  have agrees (z : pure C u) (hz : (z : V) ∈ exclusion C u p ∪ exclusion C u q) :
      center hB z = J z := by
    rcases hz with hz | hz
    · have hzero : e z = 0 := (show (z : V) ∈ {x | x ∈ base C u ∧ e x = 0}
        from ez.symm ▸ hz).2
      simpa [J, hzero] using center_eq_of_exclusion_eq hB z q ((fibers.1 z).mpr hz)
    · have hone : e z = 1 := (show (z : V) ∈ {x | x ∈ base C u ∧ e x = 1}
        from eo.symm ▸ hz).2
      simpa [J, hone] using center_eq_of_exclusion_eq hB z p ((fibers.2.1 z).mpr hz)
  have combo (x y : V) (w : ℝ) :
      J (w • x + (1-w) • y) = w • J x + (1-w) • J y := by
    simp only [J, map_add, map_smul, smul_eq_mul]
    module
  have jEq : t • J r + (1-t) • J a = v • J b + (1-v) • J d := by
    rw [← combo, ← combo, hab]
  have cb := hBC r a b d t v ⟨ht.1.le, ht.2.le⟩ ⟨hv.1.le, hv.2.le⟩ hab
  rw [agrees a ha, agrees b hb, agrees d hd] at cb
  have cr : center hB r = J r :=
    (smul_right_injective V ht.1.ne') (add_right_cancel (cb.trans jEq.symm))
  have er : e r ∈ Ioo (0 : ℝ) 1 := by
    have hbound := he r (pure_mem r).1
    rw [(pure_mem r).2] at hbound
    constructor
    · apply lt_of_le_of_ne hbound.1
      intro hz
      exact hr (Or.inl (ez ▸ (show (r : V) ∈ {x | x ∈ base C u ∧ e x = 0}
        from ⟨pure_mem r, hz.symm⟩)))
    · apply lt_of_le_of_ne hbound.2
      intro ho
      exact hr (Or.inr (eo ▸ (show (r : V) ∈ {x | x ∈ base C u ∧ e x = 1}
        from ⟨pure_mem r, ho⟩)))
  apply center_chord_not_excluded hc hs hg hB q p r fibers.2.2.symm (e r) er
  have hmem := intrinsicInterior_subset (center_interior hB r)
  rw [cr] at hmem
  convert hmem using 1 <;> dsimp [J] <;> module

end D5.S3.Quantum.Foundation.BinaryCenterGeometry
