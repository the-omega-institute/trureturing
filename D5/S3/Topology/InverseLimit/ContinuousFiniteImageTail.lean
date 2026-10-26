/- GID: D5/S3/Topology/InverseLimit/ContinuousFiniteImageTail
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/ContinuousFiniteImageTail
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Original whole Dirac capture and proper-stage finite-image obstruction. -/

/- Same-path private tail preparation; no event or history existence is asserted. -/
import D5.S3.Topology.InverseLimit.SignedBirthEnumeration
import D5.S3.Topology.InverseLimit.SignedOrdinalHistory
import D5.S3.Topology.InverseLimit.CountableClopenReflection
import D5.S3.Topology.Separation.DisjointCopyTower
import Mathlib.Topology.InductiveDimension.Classes

/-! A continuous clopen preimage contradicts the original proper-stage F law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Function MeasureTheory CategoryTheory CategoryTheory.Limits Opposite
open scoped Topology Ordinal

namespace D5.S3.Topology.InverseLimit.ContinuousFiniteImageTail

open SignedProperLimit SignedBirthEnumeration

universe u

attribute [local instance] Classical.propDecidable

/-- This uses the continuous preimage, never the image of a source clopen. -/
private theorem exists_ambient_clopen_preimage {X : Type u}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [ZeroDimensionalSpace X]
    (A : Set X) (hA : IsClosed A) (f : A → X) (hf : Continuous f)
    (C : Set X) (hC : IsClopen C) :
    ∃ D : Set X, IsClopen D ∧ ∀ x : A, x.val ∈ D ↔ f x ∈ C := by
  let E : Set A := f ⁻¹' C
  have hE : IsClopen E := hC.preimage hf
  have hclosed : IsClosed ((Subtype.val : A → X) '' E) :=
    hA.isClosedEmbedding_subtypeVal.isClosedMap _ hE.isClosed
  have hclosed' : IsClosed ((Subtype.val : A → X) '' Eᶜ) :=
    hA.isClosedEmbedding_subtypeVal.isClosedMap _ hE.compl.isClosed
  have hdis : (Subtype.val : A → X) '' E ⊆ ((Subtype.val : A → X) '' Eᶜ)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have he : y = x := Subtype.ext hxy
    subst y
    exact hy hx
  obtain ⟨D, hD, hED, hDsub⟩ :=
    exists_clopen_of_closed_subset_open hclosed hclosed'.isOpen_compl hdis
  refine ⟨D, hD, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    by_contra hfx
    exact hDsub hx ⟨x, hfx, rfl⟩
  · intro hfx
    exact hED ⟨x, hfx, rfl⟩

/-- The finite error is deleted from each original reservoir separately.
The split pools need not cover J exactly. -/
private theorem infinite_original_pools (J : Set ℕ) (N M : Bool → Set ℕ)
    (hB : Disjoint (N false) (N true))
    (hC : ∀ e, (J ∩ N e).Infinite)
    (hM : ∀ e, M e ⊆ N e)
    (hDJ : AlmostSubset J (M false ∪ M true)) :
    ∀ e, (J ∩ M e).Infinite := by
  have hfinite : {n : ℕ | ¬ (n ∈ J → n ∈ M false ∪ M true)}.Finite :=
    Filter.mem_cofinite.mp hDJ
  intro e
  apply ((hC e).sdiff hfinite).mono
  rintro n ⟨⟨hnJ, hnN⟩, hnerr⟩
  have hnM : n ∈ M false ∪ M true := by
    by_contra hh
    exact hnerr (by intro h; exact hh (h hnJ))
  refine ⟨hnJ, ?_⟩
  cases e with
  | false =>
    rcases hnM with h | h
    · exact h
    · exact False.elim (Set.disjoint_left.mp hB hnN (hM true h))
  | true =>
    rcases hnM with h | h
    · exact False.elim (Set.disjoint_left.mp hB (hM false h) hnN)
    · exact h

/-- A single proper-stage filter cannot converge on two infinite pools with
opposite indicator values. The reference is chosen after the sequence. -/
private theorem not_tendsto_of_two_infinite_pools
    (J M0 M1 : Set ℕ) (g : ℕ → ℝ)
    (h0 : (J ∩ M0).Infinite) (h1 : (J ∩ M1).Infinite)
    (hg0 : ∀ n ∈ M0, g n = 1) (hg1 : ∀ n ∈ M1, g n = 0) :
    ¬ ∃ L : ℝ, Tendsto g (along J) (𝓝 L) := by
  rintro ⟨L, hL⟩
  have heps := Metric.tendsto_nhds.mp hL (1 / 3) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_inf_principal.mp heps)
  obtain ⟨n0, hn0, hN0⟩ := h0.exists_gt N
  obtain ⟨n1, hn1, hN1⟩ := h1.exists_gt N
  have ha := hN n0 hN0.le hn0.1
  have hb := hN n1 hN1.le hn1.1
  rw [hg0 n0 hn0.2, Real.dist_eq] at ha
  rw [hg1 n1 hn1.2, Real.dist_eq] at hb
  have hc := abs_add_le (1 - L) (L - 0)
  rw [abs_sub_comm 0 L] at hb
  have he : (1 - L) + (L - 0) = (1 : ℝ) := by ring
  rw [he] at hc
  norm_num at ha hb hc
  linarith

/-- The original every-selection F law evaluated on the entire original
source Dirac lift, with a reference chosen after that lift. -/
private theorem dirac_test_tendsto
    {l : Ordinal.{0}} (H : Prefix l) (D : H.Data) (laws : H.Laws D)
    (r d c : Coord l) (hwr : ω ≤ r.1) (hrc : r < c) (hdc : d < c)
    (z : ℕ → H.Space c)
    (hsource : ∀ n, (D.nu r ⟨d.1, d.2.trans D.proper⟩ n).1 =
      (Measure.dirac (H.map r c hrc.le (z n))).toSignedMeasure)
    (Dc : Set (H.Space c)) (hDc : IsClopen Dc) :
    ∃ L : ℝ, Tendsto (fun n => if z n ∈ Dc then (1 : ℝ) else 0)
      (along (D.J r d c)) (𝓝 L) := by
  classical
  letI : Countable (Coord c.1) :=
    (Cardinal.countable_Iio_of_lt_omega_one (c.2.trans D.proper)).to_subtype
  letI : MetricSpace (H.Space c) := TopologicalSpace.metrizableSpaceMetric _
  let sigma : ℕ → RegularSigned (H.Space c) := fun n => regularPoint (z n)
  have hmass (n : ℕ) : (sigma n).1.totalVariation univ = 1 := by
    simp [sigma, regularPoint, SignedMeasure.totalVariation,
      JordanDecomposition.toJordanDecomposition_toSignedMeasure, pointJordan]
  have hmap (n : ℕ) : (sigma n).1.map (H.map r c hrc.le) =
      (Measure.dirac (H.map r c hrc.le (z n))).toSignedMeasure := by
    change ((pointJordan (z n)).toSignedMeasure).map (H.map r c hrc.le) = _
    simp only [pointJordan, JordanDecomposition.toSignedMeasure,
      Measure.toSignedMeasure_zero, sub_zero]
    ext B hB
    rw [VectorMeasure.map_apply _ (H.map r c hrc.le).continuous.measurable hB,
      Measure.toSignedMeasure_apply_measurable ((H.map r c hrc.le).continuous.measurable hB),
      Measure.toSignedMeasure_apply_measurable hB]
    change ((Measure.dirac (z n)) ((H.map r c hrc.le) ⁻¹' B)).toReal = _
    rw [← Measure.map_apply (H.map r c hrc.le).continuous.measurable hB,
      Measure.map_dirac' (H.map r c hrc.le).continuous.measurable]
    rfl
  have hclass (n : ℕ) : H.OldClass D r d c hrc.le n (sigma n) :=
    ⟨hmass n, (hmap n).trans (hsource n).symm⟩
  obtain ⟨mu, _, hconv⟩ := laws.F r d c hrc hwr hdc sigma hclass
  let g := (LocallyConstant.charFn ℝ hDc).toContinuousMap
  have heval := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hconv) g
  change Tendsto (fun n => Measures.NormPreservingLifts.signedFunctional (sigma n).1 g)
    (along (D.J r d c)) (𝓝 (Measures.NormPreservingLifts.signedFunctional mu.1 g)) at heval
  have htest : Tendsto (fun n => (sigma n).1 Dc) (along (D.J r d c)) (𝓝 (mu.1 Dc)) := by
    simpa only [g, Measures.ClopenCauchyConvergence.signedFunctional_charFn] using heval
  have hvalue (n : ℕ) : (sigma n).1 Dc = if z n ∈ Dc then (1 : ℝ) else 0 := by
    change (pointJordan (z n)).toSignedMeasure Dc = _
    simp [pointJordan, JordanDecomposition.toSignedMeasure,
      Measure.toSignedMeasure_apply_measurable hDc.isClosed.measurableSet,
      Measure.real, Measure.dirac_apply' _ hDc.isClosed.measurableSet]
    split_ifs with hn
    · rw [Set.indicator_of_mem hn]
      norm_num
    · rw [Set.indicator_of_notMem hn]
      norm_num
  exact ⟨mu.1 Dc, by simpa only [hvalue] using htest⟩

/-- The original proper-stage laws alone force a clopen dichotomy for every
all-n Dirac lift of an original whole birth sequence. No split event or pool
replacement is a premise of this conclusion. -/
theorem proper_F_clopen_dichotomy
    {l : Ordinal.{0}} (H : Prefix l) (D : H.Data) (laws : H.Laws D)
    (r d c : Coord l) (hwr : ω ≤ r.1) (hrc : r < c) (hdc : d < c)
    (z : ℕ → H.Space c)
    (hsource : ∀ n, (D.nu r ⟨d.1, d.2.trans D.proper⟩ n).1 =
      (Measure.dirac (H.map r c hrc.le (z n))).toSignedMeasure) :
    ∀ Dc : Set (H.Space c), IsClopen Dc →
      (D.J r d c ∩ {n | z n ∈ Dc}).Finite ∨
      (D.J r d c ∩ {n | z n ∉ Dc}).Finite := by
  classical
  intro Dc hDc
  obtain ⟨L, hL⟩ := dirac_test_tendsto H D laws r d c hwr hrc hdc z hsource Dc hDc
  by_contra h
  have h0 : (D.J r d c ∩ {n | z n ∈ Dc}).Infinite := fun h0 => h (Or.inl h0)
  have h1 : (D.J r d c ∩ {n | z n ∉ Dc}).Infinite := fun h1 => h (Or.inr h1)
  exact not_tendsto_of_two_infinite_pools (D.J r d c) {n | z n ∈ Dc} {n | z n ∉ Dc}
    (fun n => if z n ∈ Dc then (1 : ℝ) else 0) h0 h1
    (fun n hn => if_pos hn) (fun n hn => if_neg hn) ⟨L, hL⟩

/-- The two original reservoirs survive the actual finite DJ error. -/
private theorem proper_F_excludes_split_dirac_lifts
    {l : Ordinal.{0}} (H : Prefix l) (D : H.Data) (laws : H.Laws D)
    (r d b c : Coord l) (hwr : ω ≤ r.1)
    (hrb : r < b) (hdb : d < b) (hbc : b ≤ c)
    (M : Bool → Set ℕ)
    (hM : ∀ e, M e ⊆ D.N r d e)
    (hJb : D.J r d b = M false ∪ M true)
    (z : ℕ → H.Space c)
    (hsource : ∀ n, (D.nu r ⟨d.1, d.2.trans D.proper⟩ n).1 =
      (Measure.dirac (H.map r c (hrb.le.trans hbc) (z n))).toSignedMeasure)
    (Dc : Set (H.Space c)) (hDc : IsClopen Dc)
    (hzero : ∀ n ∈ M false, z n ∈ Dc)
    (hone : ∀ n ∈ M true, z n ∉ Dc) : False := by
  have hrc : r < c := hrb.trans_le hbc
  have hdc : d < c := hdb.trans_le hbc
  have hDJ : AlmostSubset (D.J r d c) (M false ∪ M true) := by
    rw [← hJb]
    exact laws.DJ r d b c hwr hrb hdb hbc
  have hpools := infinite_original_pools (D.J r d c) (D.N r d) M
    (laws.B r d hwr) (fun e => laws.C r d c e hwr hrc hdc) hM hDJ
  rcases proper_F_clopen_dichotomy H D laws r d c hwr hrc hdc z hsource Dc hDc with h0 | h1
  · exact hpools false (h0.subset (fun n hn => ⟨hn.1, hzero n hn.2⟩))
  · exact hpools true (h1.subset (fun n hn => ⟨hn.1, hone n hn.2⟩))

/-- At a proper stage obeying the original every-selection F law, no continuous
map on a closed domain separates the two pools of any historical J replacement.
The pools and original reservoirs are arbitrary actual input sets; no delayed
event, final history, or finite-image endpoint is postulated by this theorem. -/
theorem no_continuous_pool_separation
    {l : Ordinal.{0}} (H : Prefix l) (D : H.Data) (laws : H.Laws D)
    (r d b c : Coord l) (hwr : ω ≤ r.1)
    (hrb : r < b) (hdb : d < b) (hbc : b ≤ c)
    (M : Bool → Set ℕ) (hM : ∀ e, M e ⊆ D.N r d e)
    (hJb : D.J r d b = M false ∪ M true)
    (A : Set (H.Space c)) (hA : IsClosed A)
    (x : ℕ → A)
    (hsource : ∀ n, (D.nu r ⟨d.1, d.2.trans D.proper⟩ n).1 =
      (Measure.dirac (H.map r c (hrb.le.trans hbc) (x n).val)).toSignedMeasure)
    (f : A → H.Space c) (hf : Continuous f)
    (C : Set (H.Space c)) (hC : IsClopen C) :
    ¬ ((∀ n ∈ M false, f (x n) ∈ C) ∧
       (∀ n ∈ M true, f (x n) ∉ C)) := by
  intro hsplit
  obtain ⟨Dc, hDc, htrace⟩ := exists_ambient_clopen_preimage A hA f hf C hC
  exact proper_F_excludes_split_dirac_lifts H D laws r d b c hwr hrb hdb hbc M hM hJb
    (fun n => (x n).val) hsource Dc hDc
    (fun n hn => (htrace (x n)).mpr (hsplit.1 n hn))
    (fun n hn hmem => hsplit.2 n hn ((htrace (x n)).mp hmem))

private def properSlice (H : Prefix (ω₁ : Ordinal.{0})) (l : Label) : Prefix l.1 where
  carrier a := H.carrier ⟨a.1, lt_trans (α := Ordinal.{0}) a.2 l.2⟩
  closed a := H.closed ⟨a.1, lt_trans (α := Ordinal.{0}) a.2 l.2⟩
  nonempty a := H.nonempty ⟨a.1, lt_trans (α := Ordinal.{0}) a.2 l.2⟩
  compatible a b h x := H.compatible _ _ h x
  onto a b h y := H.onto _ _ h y

/-- Internal final-carrier consumer: the same original whole Dirac sequence
is read in a proper slice after one ambient clopen has been reflected. The
reservoirs remain the actual input pools; no delayed event is manufactured.
The raw-history connection and actual producer selection are still WIP. -/
private theorem final_no_continuous_pool_separation
    (H : Prefix (ω₁ : Ordinal.{0}))
    (Qnu : (r : Label) → Label → ℕ → RegularSigned (H.Space r))
    (QJ : Label → Label → Label → Set ℕ)
    (QN : Label → Label → Bool → Set ℕ)
    (data : (l : Label) → (properSlice H l).Data)
    (laws : ∀ l, (properSlice H l).Laws (data l))
    (hnu : ∀ (l : Label) (r : Coord l.1) (d : Label) (n : ℕ),
      ((data l).nu r d n).1 =
        (Qnu ⟨r.1, lt_trans (α := Ordinal.{0}) r.2 l.2⟩ d n).1)
    (hJ : ∀ (l : Label) (r d b : Coord l.1),
      (data l).J r d b = QJ ⟨r.1, lt_trans (α := Ordinal.{0}) r.2 l.2⟩
        ⟨d.1, lt_trans (α := Ordinal.{0}) d.2 l.2⟩
        ⟨b.1, lt_trans (α := Ordinal.{0}) b.2 l.2⟩)
    (hN : ∀ (l : Label) (r d : Coord l.1) (e : Bool),
      (data l).N r d e = QN ⟨r.1, lt_trans (α := Ordinal.{0}) r.2 l.2⟩
        ⟨d.1, lt_trans (α := Ordinal.{0}) d.2 l.2⟩ e)
    (r d b : Label) (hwr : ω ≤ r.1) (hrb : r < b) (hdb : d < b)
    (M : Bool → Set ℕ) (hM : ∀ e, M e ⊆ QN r d e)
    (hJb : QJ r d b = M false ∪ M true)
    (A : Set H.LimitSpace) (hA : IsClosed A) (x : ℕ → A)
    (hsource : ∀ n, (Qnu r d n).1 =
      (Measure.dirac (H.projection r (x n).val)).toSignedMeasure)
    (f : A → H.LimitSpace) (hf : Continuous f)
    (C : Set H.LimitSpace) (hC : IsClopen C) :
    ¬ ((∀ n ∈ M false, f (x n) ∈ C) ∧
       (∀ n ∈ M true, f (x n) ∉ C)) := by
  classical
  intro hsplit
  obtain ⟨D, hD, htrace⟩ := exists_ambient_clopen_preimage A hA f hf C hC
  letI : ∀ j, Nonempty (H.diagram.obj j) :=
    fun j => inferInstanceAs (Nonempty (H.Space j.unop))
  have hl : Order.IsSuccLimit (ω₁ : Ordinal.{0}) := Cardinal.isSuccLimit_omega 1
  have hs : ∀ {i j} (g : i ⟶ j), Surjective (H.diagram.map g) := by
    intro i j g y
    obtain ⟨z, hz⟩ := H.onto j.unop i.unop (leOfHom g.unop) y
    exact ⟨z, Subtype.ext hz⟩
  obtain ⟨c, hbc, B, hB, hDB, _, _⟩ :=
    CountableClopenReflection.exists_common_stage H.diagram H.cone
      (H.coneIsLimit hl) hs b (fun _ : Unit => D) (fun _ => hD)
  have htracec (z : A) : H.projection c z.val ∈ B () ↔ f z ∈ C := by
    have hz := htrace z
    rw [hDB ()] at hz
    exact hz
  let l : Label := ⟨Order.succ c.1, hl.succ_lt c.2⟩
  have hrc : r.1 < c.1 := hrb.trans_le hbc
  have hdc : d.1 < c.1 := hdb.trans_le hbc
  let r' : Coord l.1 := ⟨r.1, hrc.trans (Order.lt_succ c.1)⟩
  let d' : Coord l.1 := ⟨d.1, hdc.trans (Order.lt_succ c.1)⟩
  let b' : Coord l.1 := ⟨b.1, lt_of_le_of_lt (show b.1 ≤ c.1 from hbc) (Order.lt_succ c.1)⟩
  let c' : Coord l.1 := ⟨c.1, Order.lt_succ c.1⟩
  have hM' (e : Bool) : M e ⊆ (data l).N r' d' e := by
    rw [hN]
    exact hM e
  have hJb' : (data l).J r' d' b' = M false ∪ M true := by
    rw [hJ]
    exact hJb
  have hsource' (n : ℕ) :
      ((data l).nu r' ⟨d'.1, d'.2.trans (data l).proper⟩ n).1 =
      (Measure.dirac ((properSlice H l).map r' c'
        (show r' ≤ c' from hrc.le) (H.projection c (x n).val))).toSignedMeasure := by
    rw [hnu]
    have hprojection : (properSlice H l).map r' c'
        (show r' ≤ c' from hrc.le) (H.projection c (x n).val) =
        H.projection r (x n).val := by
      ext i
      rfl
    rw [hprojection]
    exact hsource n
  exact proper_F_excludes_split_dirac_lifts (properSlice H l) (data l) (laws l)
    r' d' b' c' hwr hrb hdb hbc M hM' hJb'
    (fun n => H.projection c (x n).val) hsource' (B ()) (hB ())
    (fun n hn => (htracec (x n)).mpr (hsplit.1 n hn))
    (fun n hn hmem => hsplit.2 n hn ((htracec (x n)).mp hmem))

/-- A homeomorphism into a disjoint subspace has exactly that subspace as its
ambient range, so the finite-image law makes both subspaces finite. -/
private theorem finite_disjoint_homeomorphic_of_finite_image {X : Type u}
    [TopologicalSpace X]
    (hFI : ∀ (A : Set X), IsClosed A → ∀ (f : A → X), Continuous f →
      Disjoint A (Set.range f) → (Set.range f).Finite)
    (A B : Set X) (hA : IsClosed A) (e : A ≃ₜ B) (hdisj : Disjoint A B) :
    A.Finite ∧ B.Finite := by
  let f : A → X := (Subtype.val : B → X) ∘ e
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hrange : Set.range f = B := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact (e a).property
    · intro hx
      obtain ⟨a, ha⟩ := e.surjective ⟨x, hx⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  have hB : B.Finite := by
    have hfinite := hFI A hA f hf (by rw [hrange]; exact hdisj)
    rwa [hrange] at hfinite
  letI : Finite B := hB.to_subtype
  letI : Finite A := Finite.of_injective e e.injective
  exact ⟨Set.toFinite A, hB⟩

/-- A nonempty compact binary-copy tower would give disjoint infinite closed
homeomorphic subspaces, contradicting the finite-image law. -/
private theorem no_compact_binary_copy_tower_of_finite_image {X : Type u}
    [TopologicalSpace X] [T2Space X]
    (hFI : ∀ (A : Set X), IsClosed A → ∀ (f : A → X), Continuous f →
      Disjoint A (Set.range f) → (Set.range f).Finite)
    (K : ℕ → Set X) (hcompact : ∀ n, IsCompact (K n))
    (hne : ∀ n, (K n).Nonempty)
    (hcopies : ∀ n, ∃ A B : Set X, A ⊆ K n ∧ B ⊆ K n ∧ Disjoint A B ∧
      Nonempty (K (n + 1) ≃ₜ A) ∧ Nonempty (K (n + 1) ≃ₜ B)) : False := by
  obtain ⟨A, B, hA, _, _, hBi, hdisj, ⟨e⟩⟩ :=
    Separation.DisjointCopyTower.exists_disjoint_infinite_closed_copies K hcompact hne hcopies
  exact hBi (finite_disjoint_homeomorphic_of_finite_image hFI A B hA e hdisj).2

/-- Whole signed sequences supported on disjoint clopens have distinct original
labels when the target sequence consists of Dirac measures. -/
private theorem whole_dirac_source_target_labels_ne {X : Type u}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (nu : Label → ℕ → SignedMeasure X) (s t : Label)
    (C D : TopologicalSpace.Clopens X) (hCD : Disjoint (C : Set X) (D : Set X))
    (y : ℕ → X) (hy : ∀ n, y n ∈ D)
    (targetDirac : ∀ n, nu t n = (Measure.dirac (y n)).toSignedMeasure)
    (sourceNull : ∀ n, (nu s n).totalVariation (C : Set X)ᶜ = 0) :
    s ≠ t := by
  intro hst
  have hyC : y 0 ∈ (C : Set X)ᶜ := by
    intro hyC
    exact Set.disjoint_left.mp hCD hyC (hy 0)
  have hnull := sourceNull 0
  rw [hst, targetDirac 0, SignedMeasure.totalVariation_eq_variation,
    Measure.variation_toSignedMeasure,
    Measure.dirac_apply' _ C.isClopen.isClosed.measurableSet.compl,
    Set.indicator_of_mem hyC] at hnull
  exact one_ne_zero hnull

open SignedOrdinalHistoryState SignedOrdinalHistoryEvent SignedOrdinalHistoryTask
    SignedOrdinalSuccessor in
/-- Original whole-birth data fix one pair code and force arbitrarily late
execution with the same selected result, certificate and original supports. -/
private theorem whole_birth_delayed_cofinal
    (hCH : Cardinal.continuum.{0} = Cardinal.aleph 1)
    (θ : Stage) (s t base : Label)
    (C0 C1 : TopologicalSpace.Clopens (K (SignedOrdinalHistory.run hCH θ).H))
    (hdis : Disjoint (C0 : Set (K (SignedOrdinalHistory.run hCH θ).H))
      (C1 : Set (K (SignedOrdinalHistory.run hCH θ).H)))
    (y : ℕ → K (SignedOrdinalHistory.run hCH θ).H)
    (hinV : ∀ n, y n ∈ (SignedOrdinalHistory.run hCH θ).birth.V.clopen n)
    (hinC1 : ∀ n, y n ∈ C1)
    (targetDirac : ∀ n, (SignedOrdinalHistory.run hCH θ).birth.measure t n =
      (Measure.dirac (y n)).toSignedMeasure)
    (sourceNull : ∀ n, ((SignedOrdinalHistory.run hCH θ).birth.measure s n).totalVariation
      (C0 : Set (K (SignedOrdinalHistory.run hCH θ).H))ᶜ = 0) :
    let f := SignedOrdinalHistory.run hCH
    ∃ k : ℕ, (f θ).birth.B (decode k).1 = C0 ∧
      (f θ).birth.B (decode k).2 = C1 ∧
      ∃ a : Stage, base < a.1 ∧ θ < a ∧ s.1 < ord a ∧ t.1 < ord a ∧
        (CofinalTaskSchedule.reservation a.1).1 = .inr (θ.1, s, t, k) ∧
        ∃ (D : DelayedTask (f a).event.Q)
          (R : Result (f a).H a.2 (f a).P
            (scheduledLaunch (f a).H a.2 (f a).P) (f a).event.Q ⟨D.row, oldCol D.target⟩)
          (hc : DelayedCertificate (f a).event.Q D R),
          (f a).event.selected = .delayed D R hc ∧
            Matches (f a).event.Q (f a).event.oldB θ.1 s t k D ∧
            HEq D.sourceSupport C0 ∧ HEq D.targetSupport C1 := by
  classical
  let f := SignedOrdinalHistory.run hCH
  obtain ⟨j, hj⟩ := (f θ).birth.Bonto C0
  obtain ⟨l, hl⟩ := (f θ).birth.Bonto C1
  let k := decode.symm (j, l)
  have hdecode : decode k = (j, l) := decode.apply_symm_apply (j, l)
  have hC0 : (f θ).birth.B (decode k).1 = C0 := by
    simpa only [hdecode] using hj
  have hC1 : (f θ).birth.B (decode k).2 = C1 := by
    simpa only [hdecode] using hl
  have hne : s ≠ t := whole_dirac_source_target_labels_ne
    (f θ).birth.measure s t C0 C1 hdis y hinC1 targetDirac sourceNull
  have valid : Intrinsic (f θ).birth s t k := by
    refine ⟨hne, ?_, y, hinV, ?_, targetDirac, ?_⟩
    · simpa only [hC0, hC1] using hdis
    · simpa only [hC1] using hinC1
    · simpa only [hC0] using sourceNull
  obtain ⟨a, hbase, hθ, hs, ht, hres, D, R, hc, hselected, hmatches, hsource, htarget⟩ :=
    SignedOrdinalHistory.delayed_cofinal hCH θ s t base k valid
  refine ⟨k, hC0, hC1, a, hbase, hθ, hs, ht, hres, D, R, hc,
    hselected, hmatches, ?_, ?_⟩
  · exact hsource.trans (heq_of_eq hC0)
  · exact htarget.trans (heq_of_eq hC1)

end D5.S3.Topology.InverseLimit.ContinuousFiniteImageTail
