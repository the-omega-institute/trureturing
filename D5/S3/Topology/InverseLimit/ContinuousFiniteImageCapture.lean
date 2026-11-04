/- GID: D5/S3/Topology/InverseLimit/ContinuousFiniteImageCapture
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/ContinuousFiniteImageCapture
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Original whole Dirac capture and proper-stage finite-image obstruction. -/

/- Preparation against immutable d1c68a19 only. No new raw-history type is
introduced here. The inputs are an actual SignedProperLimit.Prefix, original
onto birth tables, and the defining equality at original ordinary launches.
This source is not a claim of compilation, admission, or a completed history. -/
import D5.S3.Topology.InverseLimit.SignedBirthEnumeration
import D5.S3.Topology.InverseLimit.CountableClopenReflection
import D5.S3.Topology.InverseLimit.CofinalTaskSchedule
import D5.S3.Topology.Separation.SynchronizedClopenSupports

/-! Original launch capture for continuous maps on the literal limit carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Set Function MeasureTheory TopologicalSpace
open scoped Ordinal ENNReal

namespace D5.S3.Topology.InverseLimit.ContinuousFiniteImageCapture

open SignedProperLimit SignedBirthEnumeration CountableClopenReflection

/-- Source preparation: simultaneous original whole-sequence capture, rather
than termwise labels or an assumed delayed event. The only launch premise is
its literal support-family readback, not a conclusion about the candidate map.
The original decoder is supplied unchanged. -/
theorem exists_original_dirac_capture
    (H : Prefix (ω₁ : Ordinal.{0}))
    (U : ∀ b : Label, ω ≤ b.1 → Label → SupportFamily (H.Space b))
    (hU : ∀ b hb, Surjective (U b hb))
    (V : ∀ b : Label, ω ≤ b.1 → SupportFamily (H.Space b))
    (nu : ∀ (b : Label) (hb : ω ≤ b.1), Label → BornData (V b hb))
    (hnu : ∀ b hb, Surjective (nu b hb))
    (P : ∀ b : Label, ω ≤ b.1 → ℕ → Clopens (H.Space b))
    (hP : ∀ b hb, Surjective (P b hb))
    (decode : ℕ ≃ ℕ × ℕ)
    (hlaunch : ∀ (b i theta : Label) (hwb : ω ≤ b.1) (hbt : b < theta),
      i < theta →
      (CofinalTaskSchedule.reservation theta).1 = Sum.inl (b, i) →
      V theta (hwb.trans hbt.le) = (U b hwb i).pullback (H.map b theta hbt.le)
        (fun y => by obtain ⟨x, hx⟩ := H.onto b theta hbt.le y
                     exact ⟨x, Subtype.ext hx⟩))
    (base : Label) (A : Set H.LimitSpace) (hA : IsClosed A)
    (f : A → H.LimitSpace) (hf : Continuous f)
    (hinf : (range f).Infinite) (hdisj : Disjoint A (range f)) :
    ∃ b i theta : Label, base ≤ b ∧ ∃ hwb : ω ≤ b.1, ∃ hbt : b < theta, i < theta ∧
      (CofinalTaskSchedule.reservation theta).1 = Sum.inl (b, i) ∧
      ∃ x : ℕ → A, ∃ s t : Label, ∃ k : ℕ,
        Disjoint (P theta (hwb.trans hbt.le) (decode k).1 : Set (H.Space theta))
          (P theta (hwb.trans hbt.le) (decode k).2 : Set (H.Space theta)) ∧
        (∀ n, ((nu theta (hwb.trans hbt.le) s).1 n).1 =
          (Measure.dirac (H.projection theta (x n).val)).toSignedMeasure) ∧
        (∀ n, ((nu theta (hwb.trans hbt.le) t).1 n).1 =
          (Measure.dirac (H.projection theta (f (x n)))).toSignedMeasure) ∧
        (∀ n, H.projection theta (f (x n)) ∈
          ((V theta (hwb.trans hbt.le)).clopen n : Set (H.Space theta)) ∩ (P theta (hwb.trans hbt.le) (decode k).2 : Set (H.Space theta))) ∧
        (∀ n, (((nu theta (hwb.trans hbt.le) s).1 n).1).totalVariation
          (P theta (hwb.trans hbt.le) (decode k).1 : Set (H.Space theta))ᶜ = 0) ∧
        (∀ y : ℕ → H.Space theta,
          (∀ n, ((nu theta (hwb.trans hbt.le) t).1 n).1 = (Measure.dirac (y n)).toSignedMeasure) →
          y = fun n => H.projection theta (f (x n))) := by
  classical
  letI : ∀ a : Label, Countable (Coord a.1) := fun a =>
    (Cardinal.countable_Iio_of_lt_omega_one a.2).to_subtype
  letI : ∀ j, Nonempty (H.diagram.obj j) := fun j => inferInstanceAs (Nonempty (H.Space j.unop))
  have hl : Order.IsSuccLimit (ω₁ : Ordinal.{0}) := Cardinal.isSuccLimit_omega 1
  obtain ⟨R, hR, hAR, hfR, x, W, hW, hWdis, hxW⟩ :=
    Separation.SynchronizedClopenSupports.exists_synchronized_clopen_supports
      A hA f hf hinf hdisj
  let T : Bool ⊕ ℕ → Set H.LimitSpace :=
    Sum.elim (fun e => if e then Rᶜ else R) W
  have hT : ∀ j, IsClopen (T j) := by
    intro j
    rcases j with e | n
    · cases e with
      | false => exact hR
      | true => exact hR.compl
    · exact hW n
  let b0 : Label := max base ⟨ω, Ordinal.omega0_lt_omega_one⟩
  have hs : ∀ {i j} (g : i ⟶ j), Surjective (H.diagram.map g) := by
    intro i j g y
    obtain ⟨z, hz⟩ := H.onto j.unop i.unop (leOfHom g.unop) y
    exact ⟨z, Subtype.ext hz⟩
  obtain ⟨b, hb0, B, hB, hTB, hBne, hBdis⟩ :=
    CountableClopenReflection.exists_common_stage H.diagram H.cone
      (H.coneIsLimit hl) hs b0 T hT
  have hb : base ≤ b := (le_max_left _ _).trans hb0
  have hwb : ω ≤ b.1 := (le_max_right base
    (⟨ω, Ordinal.omega0_lt_omega_one⟩ : Label)).trans hb0
  let S : SupportFamily (H.Space b) :=
    ⟨fun n => ⟨B (.inr n), hB _⟩,
      fun n => (hBne _).mpr ⟨(x n).val, (hxW n).1⟩,
      fun m n hmn => (hBdis _ _).mpr (hWdis hmn)⟩
  obtain ⟨i, hi⟩ := hU b hwb S
  obtain ⟨theta, ht, hres⟩ := CofinalTaskSchedule.exists_reservation_above
    (.inl (b, i)) (max b i)
  have hbt : b < theta := lt_of_le_of_lt (le_max_left _ _) ht
  have hit : i < theta := lt_of_le_of_lt (le_max_right _ _) ht
  have hwt : ω ≤ theta.1 := hwb.trans hbt.le
  let q := H.map b theta hbt.le
  let Rb : Clopens (H.Space b) := ⟨B (.inl false), hB _⟩
  let Qb : Clopens (H.Space b) := ⟨B (.inl true), hB _⟩
  let Rt : Clopens (H.Space theta) := ⟨q ⁻¹' (Rb : Set (H.Space b)),
    Rb.isClopen.preimage q.continuous⟩
  let Qt : Clopens (H.Space theta) := ⟨q ⁻¹' (Qb : Set (H.Space b)),
    Qb.isClopen.preimage q.continuous⟩
  have hrow (n : ℕ) : ((V theta hwt).clopen n : Set (H.Space theta)) =
      q ⁻¹' (S.clopen n : Set (H.Space b)) := by
    rw [hlaunch b i theta hwb hbt hit hres, hi]
    rfl
  have hsrc (n : ℕ) : H.projection theta (x n).val ∈ (V theta hwt).clopen n := by
    change H.projection theta (x n).val ∈ ((V theta hwt).clopen n : Set (H.Space theta))
    rw [hrow]
    change H.projection b (x n).val ∈ B (.inr n)
    have hh := (hxW n).1
    change (x n).val ∈ T (.inr n) at hh
    rwa [hTB (.inr n)] at hh
  have htgt (n : ℕ) : H.projection theta (f (x n)) ∈ (V theta hwt).clopen n := by
    change H.projection theta (f (x n)) ∈ ((V theta hwt).clopen n : Set (H.Space theta))
    rw [hrow]
    change H.projection b (f (x n)) ∈ B (.inr n)
    have hh := (hxW n).2
    change f (x n) ∈ T (.inr n) at hh
    rwa [hTB (.inr n)] at hh
  have hsrcR (n : ℕ) : H.projection theta (x n).val ∈ Rt := by
    change H.projection b (x n).val ∈ B (.inl false)
    have hh := hAR (x n).property
    change (x n).val ∈ T (.inl false) at hh
    rwa [hTB (.inl false)] at hh
  have htgtQ (n : ℕ) : H.projection theta (f (x n)) ∈ Qt := by
    change H.projection b (f (x n)) ∈ B (.inl true)
    have hh := hfR (mem_range_self (x n))
    change f (x n) ∈ T (.inl true) at hh
    rwa [hTB (.inl true)] at hh
  have hRQ : Disjoint (Rt : Set (H.Space theta)) (Qt : Set (H.Space theta)) := by
    exact ((hBdis (.inl false) (.inl true)).mpr
      (show Disjoint R Rᶜ from disjoint_compl_right)).preimage q
  let src := pointBornData (V theta hwt) (fun n => H.projection theta (x n).val) hsrc
  let tgt := pointBornData (V theta hwt) (fun n => H.projection theta (f (x n))) htgt
  obtain ⟨s, hs⟩ := hnu theta hwt src
  obtain ⟨t, htt⟩ := hnu theta hwt tgt
  obtain ⟨j, hj⟩ := hP theta hwt Rt
  obtain ⟨l, hll⟩ := hP theta hwt Qt
  let k := decode.symm (j, l)
  have hk : decode k = (j, l) := decode.apply_symm_apply (j, l)
  have hsrc_eq (n : ℕ) : ((nu theta hwt s).1 n).1 =
      (Measure.dirac (H.projection theta (x n).val)).toSignedMeasure := by
    rw [hs]
    simp [src, pointBornData, regularPoint, pointJordan, JordanDecomposition.toSignedMeasure]
  have htgt_eq (n : ℕ) : ((nu theta hwt t).1 n).1 =
      (Measure.dirac (H.projection theta (f (x n)))).toSignedMeasure := by
    rw [htt]
    simp [tgt, pointBornData, regularPoint, pointJordan, JordanDecomposition.toSignedMeasure]
  refine ⟨b, i, theta, hb, hwb, hbt, hit, hres, x, s, t, k, ?_,
    hsrc_eq, htgt_eq, ?_, ?_, ?_⟩
  · simpa only [hk, hj, hll] using hRQ
  · intro n
    simp only [hk, hll]
    exact ⟨htgt n, htgtQ n⟩
  · intro n
    simp only [hk, hj]
    rw [hs]
    change (regularPoint (H.projection theta (x n).val)).1.totalVariation
      (Rt : Set (H.Space theta))ᶜ = 0
    simp only [regularPoint, SignedMeasure.totalVariation,
      JordanDecomposition.toJordanDecomposition_toSignedMeasure, pointJordan, add_zero]
    rw [Measure.dirac_apply' _ Rt.isClopen.isClosed.measurableSet.compl,
      Set.indicator_of_notMem (not_not.mpr (hsrcR n))]
  · intro y hy
    funext n
    exact MeasureTheory.injective_dirac
      (Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp ((hy n).symm.trans (htgt_eq n)))

end D5.S3.Topology.InverseLimit.ContinuousFiniteImageCapture
