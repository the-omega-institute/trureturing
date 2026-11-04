/- GID: D5/S3/Topology/InverseLimit/ContinuousFiniteImageTail
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/ContinuousFiniteImageTail
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: CH finite continuous images and copy obstructions on the identical actual limit. -/

/- Continuous finite-image obstructions on the literal CH limit. -/
import D5.S3.Topology.InverseLimit.SignedBirthEnumeration
import D5.S3.Topology.InverseLimit.SignedOrdinalRealizationEvents
import D5.S3.Topology.InverseLimit.ContinuousFiniteImageCapture
import D5.S3.Topology.InverseLimit.CountableClopenReflection
import D5.S3.Topology.Separation.DisjointCopyTower
import Mathlib.Topology.InductiveDimension.Classes

/-! A continuous clopen preimage contradicts the original proper-stage F law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

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
Only eligible row and historical-set readbacks are required. -/
private theorem final_no_continuous_pool_separation
    (H : Prefix (ω₁ : Ordinal.{0}))
    (Qnu : (r : Label) → Label → ℕ → RegularSigned (H.Space r))
    (QJ : Label → Label → Label → Set ℕ)
    (QN : Label → Label → Bool → Set ℕ)
    (data : (l : Label) → (properSlice H l).Data)
    (laws : ∀ l, (properSlice H l).Laws (data l))
    (hnu : ∀ (l : Label) (r : Coord l.1), ω ≤ r.1 → ∀ (d : Label) (n : ℕ),
      ((data l).nu r d n).1 =
        (Qnu ⟨r.1, lt_trans (α := Ordinal.{0}) r.2 l.2⟩ d n).1)
    (hJ : ∀ (l : Label) (r d b : Coord l.1), ω ≤ r.1 → r < b → d < b →
      (data l).J r d b = QJ ⟨r.1, lt_trans (α := Ordinal.{0}) r.2 l.2⟩
        ⟨d.1, lt_trans (α := Ordinal.{0}) d.2 l.2⟩
        ⟨b.1, lt_trans (α := Ordinal.{0}) b.2 l.2⟩)
    (hN : ∀ (l : Label) (r d : Coord l.1), ω ≤ r.1 → ∀ (e : Bool),
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
    rw [hN l r' d' hwr]
    exact hM e
  have hJb' : (data l).J r' d' b' = M false ∪ M true := by
    rw [hJ l r' d' b' hwr hrb hdb]
    exact hJb
  have hsource' (n : ℕ) :
      ((data l).nu r' ⟨d'.1, d'.2.trans (data l).proper⟩ n).1 =
      (Measure.dirac ((properSlice H l).map r' c'
        (show r' ≤ c' from hrc.le) (H.projection c (x n).val))).toSignedMeasure := by
    rw [hnu l r' hwr]
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


open SignedOrdinalHistoryState SignedOrdinalHistoryBirth SignedOrdinalHistoryEvent
    SignedOrdinalHistoryTask SignedOrdinalSuccessor

local instance carrierMeasurable {a : Ordinal.{0}} (C : Set (Cube a)) :
    MeasurableSpace C := borel C
local instance carrierBorel {a : Ordinal.{0}} (C : Set (Cube a)) :
    BorelSpace C := ⟨rfl⟩

private theorem cast_V_mem {a : Ordinal.{0}} {C D : Set (Cube a)}
    (h : C = D) (W : BirthPack C) (n : ℕ) (x : D) :
    x ∈ (BirthPack.cast h W).V.clopen n ↔
      Homeomorph.setCongr h.symm x ∈ W.V.clopen n := by
  subst D
  rfl

private theorem cast_U_mem {a : Ordinal.{0}} {C D : Set (Cube a)}
    (h : C = D) (W : BirthPack C) (i : Label) (n : ℕ) (x : D) :
    x ∈ ((BirthPack.cast h W).U i).clopen n ↔
      Homeomorph.setCongr h.symm x ∈ (W.U i).clopen n := by
  subst D
  rfl

private theorem cast_measure_dirac {a : Ordinal.{0}} {C D : Set (Cube a)}
    (h : C = D) (W : BirthPack C) (d : Label) (n : ℕ) (y : D)
    (hm : (BirthPack.cast h W).measure d n = (Measure.dirac y).toSignedMeasure) :
    W.measure d n = (Measure.dirac (Homeomorph.setCongr h.symm y)).toSignedMeasure := by
  subst D
  exact hm

private theorem cast_measure_null {a : Ordinal.{0}} {C D : Set (Cube a)}
    (h : C = D) (W : BirthPack C) (d : Label) (n : ℕ)
    (B : TopologicalSpace.Clopens D)
    (hm : ((BirthPack.cast h W).measure d n).totalVariation (B : Set D)ᶜ = 0) :
    (W.measure d n).totalVariation
      (Homeomorph.setCongr h ⁻¹' (B : Set D))ᶜ = 0 := by
  subst D
  exact hm

private theorem measure_read_dirac {a : Ordinal.{0}} {C D : Set (Cube a)}
    (h : C = D) (mu : SignedMeasure D) (nu : SignedMeasure C) (y : C)
    (hm : HEq mu nu) (hy : nu = (Measure.dirac y).toSignedMeasure) :
    mu = (Measure.dirac (Homeomorph.setCongr h y)).toSignedMeasure := by
  subst D
  exact (eq_of_heq hm).trans hy

private theorem prepared_launch_readback {a : Ordinal.{0}} {H : Prefix (Order.succ a)}
    {ha : ω ≤ a} {P : Predecessor H ha} {launch : Launch a}
    (Q : Prepared H ha P launch) (r : Rows a) (i : Label)
    (hr : r ≠ newRow a ha) (hl : launch = ⟨r, i⟩) (n : ℕ) :
    ((Q.V (newRow a ha)).clopen n : Set (K H)) =
      (projection H r) ⁻¹' ((P.U r hr i).clopen n : Set (Base H r)) := by
  subst launch
  have h := congrArg (fun f : ℕ → TopologicalSpace.Clopens (K H) =>
    (f n : Set (K H))) Q.launch_eq
  simpa only [dite_eq_right hr, TopologicalSpace.Clopens.coe_mk] using h

private theorem oldN_congr {a : Ordinal.{0}} {H : Prefix (Order.succ a)}
    {ha : ω ≤ a} (P : Predecessor H ha) {r r' : Rows a}
    {hr : r ≠ newRow a ha} {hr' : r' ≠ newRow a ha} {d d' : Coord a}
    (hrow : r = r') (hcol : d = d') (e : Fin 2) :
    P.oldN r hr d e = P.oldN r' hr' d' e := by
  subst r'
  subst d'
  rfl

/-- Every ordinary reservation, not just a separately chosen cofinal witness,
launches the original support family on the literal final carrier. -/
private theorem actual_launch_readback
    (hCH : Cardinal.continuum.{0} = Cardinal.aleph 1)
    (b i a : Label) (hwb : ω ≤ b.1) (hba : b < a) (hi : i < a)
    (he : (CofinalTaskSchedule.reservation a).1 = .inl (b, i)) :
    (SignedOrdinalRealization.wholeBirth hCH ⟨a, hwb.trans hba.le⟩).V =
      ((SignedOrdinalRealization.wholeBirth hCH ⟨b, hwb⟩).U i).pullback
        ((SignedOrdinalRealization.finalPrefix hCH).map b a hba.le)
        (fun y => by
          obtain ⟨x, hx⟩ := (SignedOrdinalRealization.finalPrefix hCH).onto b a hba.le y
          exact ⟨x, Subtype.ext hx⟩) := by
  classical
  let θ : Stage := ⟨b, hwb⟩
  let A : Stage := ⟨a, hwb.trans hba.le⟩
  let X := SignedOrdinalHistory.run hCH A
  let r := oldRow (show θ < A from hba) (newRow (ord θ) θ.2)
  let hr := oldRow_ne (show θ < A from hba) (newRow (ord θ) θ.2)
  have hv : CofinalTaskSchedule.OrdinaryValid a b i := ⟨hwb, hba.le, hi.le⟩
  have hex : CofinalTaskSchedule.execute a (fun _ _ _ _ => False) = (b, i) := by
    simp only [CofinalTaskSchedule.execute, he, ite_eq_left hv]
  have hlaunch : scheduledLaunch X.H A.2 X.P = ⟨r, i⟩ := by
    have hrow : (scheduledLaunch X.H A.2 X.P).row = r := by
      simp only [scheduledLaunch, hex, r, oldRow, θ, A, ord]
    have hindex : (scheduledLaunch X.H A.2 X.P).supportIndex = i := by
      simp only [scheduledLaunch, hex, A]
    exact congrArg₂ (fun r i => (⟨r, i⟩ : Launch (ord A))) hrow hindex
  have hs := prepared_launch_readback X.event.Q r i hr hlaunch
  have hclopen (n : ℕ) :
      (SignedOrdinalRealization.wholeBirth hCH A).V.clopen n =
      ((((SignedOrdinalRealization.wholeBirth hCH θ).U i).pullback
        ((SignedOrdinalRealization.finalPrefix hCH).map b a hba.le)
        (fun y => by
          obtain ⟨x, hx⟩ := (SignedOrdinalRealization.finalPrefix hCH).onto b a hba.le y
          exact ⟨x, Subtype.ext hx⟩)).clopen n) := by
    apply SetLike.coe_injective
    ext x
    change (x ∈ (SignedOrdinalRealization.wholeBirth hCH A).V.clopen n) ↔
      (SignedOrdinalRealization.finalPrefix hCH).map b a hba.le x ∈
        ((SignedOrdinalRealization.wholeBirth hCH θ).U i).clopen n
    unfold SignedOrdinalRealization.wholeBirth
    rw [cast_V_mem, cast_U_mem]
    have hlocal := eq_iff_iff.mp (congrArg (fun S : Set (K X.H) =>
      Homeomorph.setCongr (SignedOrdinalRealization.top_read hCH A) x ∈ S) (hs n))
    change _ ↔ projection X.H r _ ∈ ((X.oldBirth r hr).U i).clopen n at hlocal
    rw [(SignedOrdinalHistory.coherent hCH θ A hba).birth] at hlocal
    rw [cast_U_mem] at hlocal
    exact hlocal
  have hfun := funext hclopen
  generalize (SignedOrdinalRealization.wholeBirth hCH A).V = V at hfun ⊢
  generalize (((SignedOrdinalRealization.wholeBirth hCH θ).U i).pullback
    ((SignedOrdinalRealization.finalPrefix hCH).map b a hba.le) _) = W at hfun ⊢
  cases V
  cases W
  cases hfun
  rfl

/-- The original capture and the very same delayed result force finite image
on the actual omega-one limit, using only CH. -/
private theorem actual_continuous_finite_image
    (hCH : Cardinal.continuum.{0} = Cardinal.aleph 1)
    (A : Set (SignedOrdinalRealization.finalPrefix hCH).LimitSpace) (hA : IsClosed A)
    (f : A → (SignedOrdinalRealization.finalPrefix hCH).LimitSpace) (hf : Continuous f)
    (hdisj : Disjoint A (range f)) : (range f).Finite := by
  classical
  let H := SignedOrdinalRealization.finalPrefix hCH
  let W := SignedOrdinalRealization.wholeBirth hCH
  by_contra hinf
  obtain ⟨b0, i, theta, _, hwb, hbt, _, _, x, s, t, k0,
    hdis, hsource, htarget, hin, hnull, _⟩ :=
    ContinuousFiniteImageCapture.exists_original_dirac_capture H
      (fun b hb => (W ⟨b, hb⟩).U) (fun b hb => (W ⟨b, hb⟩).Uonto)
      (fun b hb => (W ⟨b, hb⟩).V) (fun b hb => (W ⟨b, hb⟩).nu)
      (fun b hb => (W ⟨b, hb⟩).nuonto)
      (fun b hb => (W ⟨b, hb⟩).B) (fun b hb => (W ⟨b, hb⟩).Bonto)
      decode (actual_launch_readback hCH) initialStage.1 A hA f hf hinf hdisj
  let θ : Stage := ⟨theta, hwb.trans hbt.le⟩
  have hwt : ω ≤ theta.1 := θ.2
  let e := Homeomorph.setCongr (SignedOrdinalRealization.top_read hCH θ)
  let C0 := (W θ).B (decode k0).1
  let C1 := (W θ).B (decode k0).2
  let C0r : TopologicalSpace.Clopens (K (SignedOrdinalHistory.run hCH θ).H) :=
    ⟨e.symm ⁻¹' (C0 : Set _), C0.isClopen.preimage e.symm.continuous⟩
  let C1r : TopologicalSpace.Clopens (K (SignedOrdinalHistory.run hCH θ).H) :=
    ⟨e.symm ⁻¹' (C1 : Set _), C1.isClopen.preimage e.symm.continuous⟩
  let y := fun n => H.projection theta (f (x n))
  have hdisr : Disjoint (C0r : Set (K (SignedOrdinalHistory.run hCH θ).H))
      (C1r : Set (K (SignedOrdinalHistory.run hCH θ).H)) := hdis.preimage e.symm
  have hVr (n : ℕ) : e (y n) ∈ (SignedOrdinalHistory.run hCH θ).birth.V.clopen n :=
    (cast_V_mem (SignedOrdinalRealization.top_read hCH θ).symm _ n (y n)).mp (hin n).1
  have hC1r (n : ℕ) : e (y n) ∈ C1r := by
    change e.symm (e (y n)) ∈ C1
    simpa using (hin n).2
  have htr (n : ℕ) : (SignedOrdinalHistory.run hCH θ).birth.measure t n =
      (Measure.dirac (e (y n))).toSignedMeasure :=
    cast_measure_dirac (SignedOrdinalRealization.top_read hCH θ).symm _ t n (y n) (htarget n)
  have hnr (n : ℕ) : ((SignedOrdinalHistory.run hCH θ).birth.measure s n).totalVariation
      (C0r : Set _)ᶜ = 0 :=
    cast_measure_null (SignedOrdinalRealization.top_read hCH θ).symm _ s n C0 (hnull n)
  obtain ⟨k, _, _, a, _, hθ, hs, ht, _, D, R, hc, hselected, hm, _, _⟩ :=
    whole_birth_delayed_cofinal hCH θ s t theta C0r C1r hdisr (fun n => e (y n))
      hVr hC1r htr hnr
  have hrow : D.row = oldRow hθ (newRow (ord θ) θ.2) := Subtype.ext hm.1
  have hsourceCol : D.source = ⟨s.1, hs⟩ := Subtype.ext hm.2.1
  have htargetCol : oldCol D.target = ⟨t.1, ht.le⟩ := Subtype.ext hm.2.2.1
  have htargetRead (n : ℕ) :
      (SignedOrdinalHistory.run hCH a).event.Q.measure D.row (oldCol D.target) n =
        (Measure.dirac (Homeomorph.setCongr
          (SignedOrdinalRealization.carrier_read hCH a (rowIndex D.row))
          (H.projection ⟨D.row.1, D.row.2.2.trans_lt a.1.2⟩ (f (x n))))).toSignedMeasure := by
    rw [hrow, htargetCol]
    exact measure_read_dirac (SignedOrdinalRealization.carrier_read hCH a
      (rowIndex (oldRow hθ (newRow (ord θ) θ.2)))) _ _ _
      (SignedOrdinalRealizationEvents.prepared_measure_read hCH θ a hθ t ht.le n)
      (htarget n)
  have hy (n : ℕ) : D.y n = Homeomorph.setCongr
      (SignedOrdinalRealization.carrier_read hCH a (rowIndex D.row))
      (H.projection ⟨D.row.1, D.row.2.2.trans_lt a.1.2⟩ (f (x n))) :=
    MeasureTheory.injective_dirac (Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
      ((D.dirac n).symm.trans (htargetRead n)))
  obtain ⟨M, hJM, _, hMN, ⟨C, hC0, hC1⟩, _⟩ := hc
  have hcarrier : (SignedOrdinalHistory.run hCH a).event.result.coordinates.carrier =
      R.coordinates.carrier := by
    change (Selected.result (SignedOrdinalHistory.run hCH a).event.selected).coordinates.carrier = _
    rw [hselected]
    rfl
  let ep := (SignedOrdinalRealization.successorHomeomorph hCH a).trans
    (Homeomorph.setCongr hcarrier)
  let p : C(H.LimitSpace, R.coordinates.carrier) :=
    (⟨ep, ep.continuous⟩ : C(H.Space (nextStage a).1, R.coordinates.carrier)).comp
      (H.projection (nextStage a).1)
  let Cf : Set H.LimitSpace := p ⁻¹' (C : Set _)
  have hCf : IsClopen Cf := C.isClopen.preimage p.continuous
  have hrestrict (n : ℕ) :
      restrict (D.row.2.2.trans (Order.le_succ (ord a))) (p (f (x n))).1 = (D.y n).1 := by
    have hp := congrArg Subtype.val
      (SignedOrdinalRealizationEvents.selected_projection hCH a D.row (f (x n)))
    rw [← hy n] at hp
    have hv := (SignedOrdinalHistory.run hCH a).event.result.coordinates.restrict_inverse
      D.row.1 D.row.2.2
      (SignedOrdinalRealization.successorHomeomorph hCH a
        (H.projection (nextStage a).1 (f (x n))))
    exact hv.trans hp
  let Qnu : (r : Label) → Label → ℕ → RegularSigned (H.Space r) := fun r d n =>
    if hr : ω ≤ r.1 then ((W ⟨r, hr⟩).nu d).1 n
    else ⟨0, by
      simp only [SignedMeasure.toJordanDecomposition_zero,
        JordanDecomposition.zero_posPart, JordanDecomposition.zero_negPart]
      exact ⟨inferInstance, inferInstance⟩⟩
  let QJ : Label → Label → Label → Set ℕ := fun r d b =>
    if hr : ω ≤ r.1 then
      if hb : max r d < b then SignedOrdinalRealization.historicalJ hCH ⟨r, hr⟩ d ⟨b, hb⟩
      else ∅
    else ∅
  let QN : Label → Label → Bool → Set ℕ := fun r d e =>
    if hr : ω ≤ r.1 then SignedOrdinalRealization.reservoir hCH ⟨r, hr⟩ d e else ∅
  have hnuRead (l : Label) (r : Coord l.1) (hr : ω ≤ r.1) (d : Label) (n : ℕ) :
      ((SignedOrdinalRealization.properData hCH l.2).nu r d n).1 =
        (Qnu ⟨r.1, lt_trans (α := Ordinal.{0}) r.2 l.2⟩ d n).1 := by
    simpa only [Qnu, dite_eq_left hr, W, BirthPack.measure] using SignedOrdinalRealization.slice_nu hCH l.2 r hr d n
  have hJRead (l : Label) (r d b : Coord l.1) (hr : ω ≤ r.1)
      (hrb : r < b) (hdb : d < b) :
      (SignedOrdinalRealization.properData hCH l.2).J r d b =
        QJ ⟨r.1, lt_trans (α := Ordinal.{0}) r.2 l.2⟩ ⟨d.1, lt_trans (α := Ordinal.{0}) d.2 l.2⟩ ⟨b.1, lt_trans (α := Ordinal.{0}) b.2 l.2⟩ := by
    have helig : max (⟨r.1, lt_trans (α := Ordinal.{0}) r.2 l.2⟩ : Label) ⟨d.1, lt_trans (α := Ordinal.{0}) d.2 l.2⟩ <
        ⟨b.1, lt_trans (α := Ordinal.{0}) b.2 l.2⟩ := max_lt hrb hdb
    simp only [QJ, dif_pos hr, dif_pos helig]
    exact SignedOrdinalRealization.slice_J hCH l.2
      ⟨⟨b.1, lt_trans (α := Ordinal.{0}) b.2 l.2⟩, hr.trans hrb.le⟩ b.2
      ⟨r.1, hr, hrb.le⟩ (by
        intro he
        exact (ne_of_lt (show r.1 < b.1 from hrb))
          (congrArg (fun q : Rows b.1 => q.1) he)) ⟨d.1, hdb⟩
  have hNRead (l : Label) (r d : Coord l.1) (hr : ω ≤ r.1) (e : Bool) :
      (SignedOrdinalRealization.properData hCH l.2).N r d e =
        QN ⟨r.1, lt_trans (α := Ordinal.{0}) r.2 l.2⟩ ⟨d.1, lt_trans (α := Ordinal.{0}) d.2 l.2⟩ e := by
    simpa only [QN, dif_pos hr] using SignedOrdinalRealization.slice_N hCH l.2 r d hr e
  let Mb : Bool → Set ℕ := fun e => M (if e then 1 else 0)
  have hMb (e : Bool) : Mb e ⊆ QN theta s e := by
    intro n hn
    have hnN := (hMN (if e then 1 else 0) hn).2
    rw [oldN_congr (SignedOrdinalHistory.run hCH a).P
      (hr' := oldRow_ne hθ _) hrow hsourceCol (if e then 1 else 0)] at hnN
    have hN := SignedOrdinalRealization.reservoir_incoming hCH θ s a hθ hs e
    simp only [QN, dite_eq_left hwt]
    change n ∈ SignedOrdinalRealization.reservoir hCH θ s e
    rw [hN]
    exact hnN
  have hJb : QJ theta s (nextStage a).1 = Mb false ∪ Mb true := by
    have helig : max theta s < (nextStage a).1 :=
      (max_le (show ord θ ≤ ord a from hθ.le) hs.le).trans_lt (Order.lt_succ _)
    simp only [QJ, dite_eq_left hwt, dif_pos helig]
    have hj := SignedOrdinalRealizationEvents.successor_J hCH a θ hθ.le s hs.le
    change SignedOrdinalRealization.historicalJ hCH θ s _ =
      (Selected.result (SignedOrdinalHistory.run hCH a).event.selected).J _ _ at hj
    rw [hselected] at hj
    rw [hj]
    have hrow' : D.row = ⟨ord θ, θ.2, hθ.le⟩ := Subtype.ext hm.1
    have hsource' : oldCol D.source = ⟨s.1, hs.le⟩ := Subtype.ext hm.2.1
    change R.J ⟨ord θ, θ.2, hθ.le⟩ ⟨s.1, hs.le⟩ = Mb false ∪ Mb true
    exact (congrArg₂ (fun r d => R.J r d) hrow' hsource').symm.trans hJM
  exact final_no_continuous_pool_separation H Qnu QJ QN
    (fun l => SignedOrdinalRealization.properData hCH l.2)
    (fun l => SignedOrdinalRealization.properLaws hCH l.2)
    hnuRead hJRead hNRead theta s (nextStage a).1 θ.2
    ((show theta.1 < ord a from hθ).trans (Order.lt_succ (ord a)))
    (hs.trans (Order.lt_succ (ord a))) Mb hMb hJb A hA x
    (fun n => by simpa only [Qnu, dite_eq_left hwt] using hsource n)
    f hf Cf hCf ⟨fun n hn => hC0 n hn (p (f (x n))) (hrestrict n),
      fun n hn => hC1 n hn (p (f (x n))) (hrestrict n)⟩

/-- CH alone gives all three obstructions on the identical constructed limit. -/
theorem actual_CH_finite_image_and_copy_obstructions
    (hCH : Cardinal.continuum.{0} = Cardinal.aleph 1) :
    let K := (SignedOrdinalRealization.finalPrefix hCH).LimitSpace
    (∀ (A : Set K), IsClosed A → ∀ (f : A → K), Continuous f →
      Disjoint A (range f) → (range f).Finite) ∧
    (∀ (A B : Set K), IsClosed A → (A ≃ₜ B) → Disjoint A B → A.Finite ∧ B.Finite) ∧
    (∀ (T : ℕ → Set K), (∀ n, IsCompact (T n)) → (∀ n, (T n).Nonempty) →
      (∀ n, ∃ A B : Set K, A ⊆ T n ∧ B ⊆ T n ∧ Disjoint A B ∧
        Nonempty (T (n + 1) ≃ₜ A) ∧ Nonempty (T (n + 1) ≃ₜ B)) → False) := by
  have hFI := actual_continuous_finite_image hCH
  exact ⟨hFI, finite_disjoint_homeomorphic_of_finite_image hFI,
    no_compact_binary_copy_tower_of_finite_image hFI⟩

end D5.S3.Topology.InverseLimit.ContinuousFiniteImageTail
