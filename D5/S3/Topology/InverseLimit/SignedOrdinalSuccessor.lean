/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalSuccessor
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalSuccessor
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Actual ordinal successor execution and arrival-entry reservoir births. -/

import D5.S3.Topology.InverseLimit.SignedBirthEnumeration
import D5.S3.Topology.InverseLimit.SignedSuccessorCoordinates
import D5.S3.Topology.Measures.SignedSplitSuccessor

/-! A partial predecessor is extended by an executed local split. Reservoirs are
read from arrival entries at succ(max(row,label)); launch and treatment differ. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor

open SignedProperLimit SignedBirthEnumeration
open D5.S3.Topology.Measures
open SignedSplitSuccessor

abbrev Rows (a : Ordinal.{0}) : Type 1 :=
  {r : Ordinal.{0} // (ω : Ordinal.{0}) ≤ r ∧ r ≤ a}
abbrev Cols (a : Ordinal.{0}) : Type 1 := {d : Ordinal.{0} // d ≤ a}

abbrev top (a : Ordinal.{0}) : Coord (Order.succ a) := ⟨a, Order.lt_succ a⟩
abbrev index {a : Ordinal.{0}} (b : Cols a) : Coord (Order.succ a) :=
  ⟨b.1, lt_of_le_of_lt b.2 (Order.lt_succ a)⟩
abbrev rowIndex {a : Ordinal.{0}} (r : Rows a) : Coord (Order.succ a) :=
  index ⟨r.1, r.2.2⟩
abbrev oldCol {a : Ordinal.{0}} (d : Coord a) : Cols a :=
  ⟨d.1, by
    change d.1 ≤ a
    have hd : d.1 < a := d.2
    exact hd.le⟩
abbrev lastCol (a : Ordinal.{0}) : Cols a := ⟨a, by change a ≤ a; exact le_rfl⟩
abbrev newRow (a : Ordinal.{0}) (ha : ω ≤ a) : Rows a := ⟨a, ha, le_rfl⟩

/-- Only born pairs occur in a historical arrival entry. The index b names the
outgoing stage; its entry is available at succ b, not in the strict prefix b. -/
def PastBirths (a : Ordinal.{0}) :=
  (b : Coord a) → (r d : Ordinal.{0}) → ω ≤ r → max r d = b.1 → Fin 2 → Set ℕ

/-- Permanent readback always selects the unique birth stage. -/
def PastBirths.read {a : Ordinal.{0}} (P : PastBirths a)
    (r d : Ordinal.{0}) (hr : ω ≤ r) (hb : max r d < a) : Fin 2 → Set ℕ :=
  P ⟨max r d, hb⟩ r d hr rfl

/-- Support launch syntax has a support-enumeration index, not a measure label. -/
structure Launch (a : Ordinal.{0}) where
  row : Rows a
  supportIndex : Label

/-- Whole-sequence treatment has its own row and signed-sequence label. -/
structure Treatment (a : Ordinal.{0}) where
  row : Rows a
  label : Cols a

variable {a : Ordinal.{0}} (H : Prefix (Order.succ a))

abbrev K : Type 1 := H.Space (top a)
abbrev Base (r : Rows a) : Type 1 := H.Space (rowIndex r)

instance kCompact : CompactSpace (K H) := H.spaceCompact (top a)
instance baseCompact (r : Rows a) : CompactSpace (Base H r) := H.spaceCompact (rowIndex r)
instance kMeasurable : MeasurableSpace (K H) := H.spaceMeasurable (top a)
instance kBorel : BorelSpace (K H) := H.spaceBorel (top a)
instance baseMeasurable (r : Rows a) : MeasurableSpace (Base H r) := H.spaceMeasurable (rowIndex r)
instance baseBorel (r : Rows a) : BorelSpace (Base H r) := H.spaceBorel (rowIndex r)

def projection (r : Rows a) : C(K H, Base H r) :=
  H.map (rowIndex r) (top a) r.2.2

theorem projection_onto (r : Rows a) : Surjective (projection H r) := by
  intro y
  obtain ⟨x, hx⟩ := H.onto (rowIndex r) (top a) r.2.2 y
  exact ⟨x, Subtype.ext hx⟩

/-- All input obligations are on the actually available partial predecessor.
No complete history, successor supplier, or proposed final object occurs. -/
structure Predecessor (ha : ω ≤ a) where
  proper : a < ω₁
  base_onto : Surjective (fun x : K H => restrict ha x.1)
  births : PastBirths a
  U : ∀ r : Rows a, r ≠ newRow a ha → Label → SupportFamily (Base H r)
  Uonto : ∀ r hr, Surjective (U r hr)
  V : ∀ r : Rows a, r ≠ newRow a ha → SupportFamily (Base H r)
  nu : ∀ (r : Rows a) (hr : r ≠ newRow a ha), Label → BornData (V r hr)
  nuonto : ∀ r hr, Surjective (nu r hr)
  I : ∀ r : Rows a, r ≠ newRow a ha → Set ℕ
  J : ∀ r : Rows a, r ≠ newRow a ha → Coord a → Set ℕ
  A : ∀ r hr d, J r hr d ⊆ I r hr
  B : ∀ (r : Rows a) (hr : r ≠ newRow a ha) (d : Coord a), Disjoint
    (births.read r.1 d.1 r.2.1 (max_lt (lt_of_le_of_ne r.2.2
      (fun h => hr (Subtype.ext h))) d.2) 0)
    (births.read r.1 d.1 r.2.1 (max_lt (lt_of_le_of_ne r.2.2
      (fun h => hr (Subtype.ext h))) d.2) 1)
  C : ∀ r hr (d : Coord a) e, (J r hr d ∩
    births.read r.1 d.1 r.2.1 (max_lt (lt_of_le_of_ne r.2.2
      (fun h => hr (Subtype.ext h))) d.2) e).Infinite
  E : ∀ r hr (c : Coord a), ∀ᶠ n in along (I r hr), ∀ x y : K H,
    projection H r x ∈ (V r hr).clopen n → projection H r y ∈ (V r hr).clopen n →
    projection H r x = projection H r y → x.1 c = y.1 c
  F : ∀ r hr (d : Coord a) (s : ℕ → SignedMeasure (K H)),
    (∀ n, (s n).map (projection H r) = ((nu r hr ⟨d.1, d.2.trans proper⟩).1 n).1) →
    (∀ n, (s n).totalVariation univ = 1) →
    ∃ mu : SignedMeasure (K H), Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (s n)).toWeakDual)
      (along (J r hr d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual)

namespace Predecessor

variable {H} {ha : ω ≤ a} (P : Predecessor H ha)

def oldN (r : Rows a) (hr : r ≠ newRow a ha) (d : Coord a) : Fin 2 → Set ℕ :=
  P.births.read r.1 d.1 r.2.1
    (max_lt (lt_of_le_of_ne r.2.2 (fun h => hr (Subtype.ext h))) d.2)

end Predecessor

/-- Current U and P are chosen before the row launch, then its entire legal
signed enumeration is born before any treatment is executed. -/
structure Prepared (ha : ω ≤ a) (P : Predecessor H ha) (launch : Launch a) where
  U : Label → SupportFamily (K H)
  Uonto : Surjective U
  B : ℕ → Clopens (K H)
  Bonto : Surjective B
  V : ∀ r : Rows a, SupportFamily (Base H r)
  oldV : ∀ r hr, V r = P.V r hr
  launch_eq : (V (newRow a ha)).clopen =
    fun n => ⟨projection H launch.row ⁻¹'
      ((if hr : launch.row = newRow a ha then
          (by rw [hr]; exact U launch.supportIndex)
        else P.U launch.row hr launch.supportIndex).clopen n : Set (Base H launch.row)),
      ((if hr : launch.row = newRow a ha then
          (by rw [hr]; exact U launch.supportIndex)
        else P.U launch.row hr launch.supportIndex).clopen n).isClopen.preimage
          (projection H launch.row).continuous⟩
  nu : ∀ r : Rows a, Label → BornData (V r)
  nuonto : ∀ r, Surjective (nu r)
  oldNu : ∀ r hr d n, ((nu r d).1 n).1 = ((P.nu r hr d).1 n).1

theorem exists_prepared (H : Prefix (Order.succ a)) (ha : ω ≤ a) (P : Predecessor H ha)
    (launch : Launch a) (hCH : Cardinal.continuum.{0} = ℵ₁) :
    Nonempty (Prepared H ha P launch) := by
  classical
  letI : Countable (Coord a) := (Cardinal.countable_Iio_of_lt_omega_one P.proper).to_subtype
  letI : Encodable (Coord a) := Encodable.ofCountable _
  letI : MetricSpace (K H) := TopologicalSpace.metrizableSpaceMetric _
  let p : C(K H, Cube (ω : Ordinal.{0})) :=
    ⟨fun x => restrict ha x.1, (Pi.continuous_precomp' _).comp continuous_subtype_val⟩
  obtain ⟨⟨U, hU⟩, B, hB⟩ := exists_clopen_enumerations p P.base_onto hCH
  let W : SupportFamily (Base H launch.row) :=
    if hr : launch.row = newRow a ha then (by rw [hr]; exact U launch.supportIndex)
    else P.U launch.row hr launch.supportIndex
  let Vnew : SupportFamily (K H) := W.pullback (projection H launch.row)
    (projection_onto H launch.row)
  let V : ∀ r : Rows a, SupportFamily (Base H r) := fun r =>
    if hr : r = newRow a ha then (by rw [hr]; exact Vnew) else P.V r hr
  have hVnew : V (newRow a ha) = Vnew := by simp [V]
  obtain ⟨nuNew, hNuNew⟩ := exists_signed_enumeration Vnew hCH
  let nu : ∀ r : Rows a, Label → BornData (V r) := fun r d =>
    if hr : r = newRow a ha then (by
      subst r
      exact ⟨(nuNew d).1, by simpa only [hVnew] using (nuNew d).2⟩)
    else ⟨(P.nu r hr d).1, by
      simpa only [V, dite_eq_right hr] using (P.nu r hr d).2⟩
  refine ⟨⟨U, hU, B, hB, V, ?_, ?_, nu, ?_, ?_⟩⟩
  · intro r hr
    simp [V, hr]
  · simp only [hVnew]
    rfl
  · intro r v
    by_cases hr : r = newRow a ha
    · subst r
      let v' : BornData Vnew := ⟨v.1, by simpa only [hVnew] using v.2⟩
      obtain ⟨d, hd⟩ := hNuNew v'
      refine ⟨d, Subtype.ext ?_⟩
      simpa [nu, v'] using congrArg Subtype.val hd
    · let v' : BornData (P.V r hr) :=
        ⟨v.1, by simpa only [V, dite_eq_right hr] using v.2⟩
      obtain ⟨d, hd⟩ := P.nuonto r hr v'
      refine ⟨d, Subtype.ext ?_⟩
      simpa [nu, hr, v'] using congrArg Subtype.val hd
  · intro r hr d n
    simp [nu, hr]


namespace Prepared

variable {H} {ha : ω ≤ a} {P : Predecessor H ha} {launch : Launch a}
  (Q : Prepared H ha P launch)

def measure (r : Rows a) (d : Cols a) (n : ℕ) : SignedMeasure (Base H r) :=
  ((Q.nu r ⟨d.1, d.2.trans_lt P.proper⟩).1 n).1

theorem mass (r : Rows a) (d : Cols a) (n : ℕ) :
    (Q.measure r d n).totalVariation univ = 1 :=
  ((Q.nu r ⟨d.1, d.2.trans_lt P.proper⟩).2 n).1

theorem null (r : Rows a) (d : Cols a) (n : ℕ) :
    (Q.measure r d n).totalVariation ((Q.V r).clopen n : Set (Base H r))ᶜ = 0 := by
  exact ((Q.nu r ⟨d.1, d.2.trans_lt P.proper⟩).2 n).2.1

end Prepared

/-- All four birth cases share one executed split and its literal ordinal
insertion. F and G quantify over every signed lift, on this split presentation. -/
structure Result (ha : ω ≤ a) (P : Predecessor H ha) (launch : Launch a)
    (Q : Prepared H ha P launch) (t : Treatment a) where
  Y : Set (K H)
  Z : Set (K H)
  closed : IsClosed (splitCarrier Y Z)
  closedY : IsClosed Y
  closedZ : IsClosed Z
  cover : Y ∪ Z = univ
  coordinates : SignedSuccessorCoordinates.Result H Y Z
  I : Rows a → Set ℕ
  J : Rows a → Cols a → Set ℕ
  N : Rows a → Cols a → Fin 2 → Set ℕ
  rho : ℕ → Coord a
  rho_cofinal : ∀ d (e : Fin 2), {q | rho q = d ∧ q % 2 = (e : ℕ)}.Infinite
  column : ℕ → OrderedColumn (Rows a) (K H)
  k_mono : StrictMono (fun q => (column q).n)
  oldN : ∀ r hr (d : Coord a) e, N r (oldCol d) e = P.oldN r hr d e
  newN : ∀ (d : Coord a) e, N (newRow a ha) (oldCol d) e =
    {n | ∃ q, 0 < q ∧ rho q = d ∧ q % 2 = (e : ℕ) ∧
      (column q).m (newRow a ha) = n}
  residualN : Rows a → Fin 2 → Set ℕ
  residual_eq : ∀ r e, N r (lastCol a) e = residualN r e
  residual_subset : ∀ r e, residualN r e ⊆ J r (lastCol a)
  A : ∀ r d, J r d ⊆ I r
  B : ∀ r d, Disjoint (N r d 0) (N r d 1)
  C : ∀ r d e, (J r d ∩ N r d e).Infinite
  I_infinite : ∀ r, (I r).Infinite
  oldI : ∀ r hr, I r ⊆ P.I r hr
  oldJ : ∀ r hr (d : Coord a), J r (oldCol d) ⊆ P.J r hr d
  E : ∀ r (A : Set (K H)), IsClopen A → ∀ᶠ n in along (I r),
    ∀ x y : splitCarrier Y Z,
      projection H r x.1.1 ∈ (Q.V r).clopen n →
      projection H r y.1.1 ∈ (Q.V r).clopen n →
      projection H r x.1.1 = projection H r y.1.1 →
      (x.1.1 ∈ A ↔ y.1.1 ∈ A) ∧ x.1.2 = y.1.2
  F : letI : CompactSpace (splitCarrier Y Z) :=
      isCompact_iff_compactSpace.mp closed.isCompact
    ∀ r d, ∃ mu : SignedMeasure (splitCarrier Y Z),
      mu.totalVariation.real univ ≤ 1 ∧
      Measure.Regular mu.toJordanDecomposition.posPart ∧
      Measure.Regular mu.toJordanDecomposition.negPart ∧
      ∀ sigma : ℕ → SignedMeasure (splitCarrier Y Z),
        (∀ n, (sigma n).map (fun x => projection H r x.1.1) = Q.measure r d n) →
        (∀ n, (sigma n).totalVariation univ = 1) →
        Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
          (along (J r d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual)
  G : ∀ q (s : SignedMeasure (splitCarrier Y Z)),
    s.map (fun x => projection H t.row x.1.1) = Q.measure t.row t.label (column q).n →
    s.totalVariation univ = 1 →
    (q % 2 = 0 → (1 : ℝ) / 6 < s {x | x.1.2 = true}) ∧
    (q % 2 ≠ 0 → s {x | x.1.2 = true} = 0)

theorem exists_codes (ha : ω ≤ a) (hc : a < ω₁) :
    ∃ (code : Rows a → ℕ) (rho : ℕ → Coord a), Injective code ∧
      code (newRow a ha) = 0 ∧
      ∀ d (e : Fin 2), {q | rho q = d ∧ q % 2 = (e : ℕ)}.Infinite := by
  classical
  letI : Countable (Coord a) := (Cardinal.countable_Iio_of_lt_omega_one hc).to_subtype
  letI : Countable (Coord (Order.succ a)) :=
    (Cardinal.countable_Iio_of_lt_omega_one ((Cardinal.isSuccLimit_omega 1).succ_lt hc)).to_subtype
  letI : Countable (Rows a) := (show Injective (@rowIndex a) from
    fun x y h => Subtype.ext (congrArg (fun z : Coord (Order.succ a) => z.1) h)).countable
  letI : Encodable (Rows a) := Encodable.ofCountable _
  letI : Encodable (Coord a × ℕ) := Encodable.ofCountable _
  let code : Rows a → ℕ := fun r => if r = newRow a ha then 0 else Encodable.encode r + 1
  have hi : Injective code := by
    intro r s h
    by_cases hr : r = newRow a ha <;> by_cases hs : s = newRow a ha
    · exact hr.trans hs.symm
    · simp [code, hr, hs] at h
    · simp [code, hr, hs] at h
    · simpa [code, hr, hs] using h
  let zero : Coord a := ⟨0, Ordinal.omega0_pos.trans_le ha⟩
  let f : ℕ → Coord a × ℕ := fun n => (Encodable.decode n).getD (zero, 0)
  let rho : ℕ → Coord a := fun q => (f (q / 2)).1
  refine ⟨code, rho, hi, by simp [code], ?_⟩
  intro d e
  let g : ℕ → ℕ := fun k => 2 * Encodable.encode (d, k) + (e : ℕ)
  have hg : Injective g := by
    intro j k h
    have he : Encodable.encode (d, j) = Encodable.encode (d, k) := by dsimp [g] at h; omega
    exact (Prod.mk.inj (Encodable.encode_injective he)).2
  apply (Set.infinite_range_of_injective hg).mono
  rintro _ ⟨k, rfl⟩
  have he : (e : ℕ) < 2 := e.2
  have hd : g k / 2 = Encodable.encode (d, k) := by dsimp [g]; omega
  constructor
  · simp [rho, hd, f]
  · dsimp [g]; omega

namespace Prepared

variable {H} {ha : ω ≤ a} {P : Predecessor H ha} {launch : Launch a}
  (Q : Prepared H ha P launch)

private theorem old_measure (r : Rows a) (hr : r ≠ newRow a ha) (d : Coord a) (n : ℕ) :
    Q.measure r (oldCol d) n = ((P.nu r hr ⟨d.1, d.2.trans P.proper⟩).1 n).1 :=
  Q.oldNu r hr _ n

theorem old_f (r : Rows a) (hr : r ≠ newRow a ha) (d : Coord a)
    (s : ℕ → SignedMeasure (K H))
    (hm : ∀ n, (s n).map (projection H r) = Q.measure r (oldCol d) n)
    (hn : ∀ n, (s n).totalVariation univ = (Q.measure r (oldCol d) n).totalVariation univ) :
    ∃ mu : SignedMeasure (K H), Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (s n)).toWeakDual)
      (along (P.J r hr d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) :=
  P.F r hr d s (fun n => (hm n).trans (Q.old_measure r hr d n))
    (fun n => (hn n).trans (Q.mass r _ n))

theorem old_e (r : Rows a) (hr : r ≠ newRow a ha) (c : Coord a) :
    ∀ᶠ n in along (P.I r hr), ∀ x y : K H,
      projection H r x ∈ (Q.V r).clopen n → projection H r y ∈ (Q.V r).clopen n →
      projection H r x = projection H r y → x.1 c = y.1 c := by
  simpa only [Q.oldV r hr] using P.E r hr c

private theorem positive (r : Rows a) (d : Cols a) (n : ℕ) :
    (1 : ℝ) / 2 ≤ (Q.measure r d n).toJordanDecomposition.posPart.real univ := by
  have h := ENNReal.toReal_mono
    (measure_ne_top (Q.measure r d n).toJordanDecomposition.posPart univ)
    (((Q.nu r ⟨d.1, d.2.trans_lt P.proper⟩).2 n).2.2)
  simpa only [Measure.real, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using h

end Prepared

set_option maxHeartbeats 1600000 in
-- The supplier assembly checks the dependent old/new row and residual cases together.
theorem exists_ordinary (ha : ω ≤ a) (P : Predecessor H ha)
    (launch : Launch a) (Q : Prepared H ha P launch) (t : Treatment a) :
    Nonempty (Result H ha P launch Q t) := by
  classical
  letI : Countable (Coord a) := (Cardinal.countable_Iio_of_lt_omega_one P.proper).to_subtype
  letI : MetricSpace (K H) := TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨code, rho, hcode, hzero, hrho⟩ := exists_codes ha P.proper
  let coord : Coord a → C(K H, Bool) := fun c =>
    ⟨fun x => x.1 c, (continuous_apply c).comp continuous_subtype_val⟩
  have hsep : Injective (fun x : K H => fun c => coord c x) := by
    intro x y h
    exact Subtype.ext (funext (congrFun h))
  let nuR := fun (r : Rows a) (d : Coord a) => Q.measure r (oldCol d)
  let nuA := fun r => Q.measure r (lastCol a)
  choose sR hsRmap hsRmass using fun r d n =>
    NormPreservingLiftExistence.exists_norm_preserving_lift (projection H r)
      (projection H r).continuous
      (projection_onto H r) (nuR r d n)
  choose muR hmuR using fun r hr d => Q.old_f r hr d (sR r d) (hsRmap r d) (hsRmass r d)
  let pool : Set ℕ := if hr : t.row = newRow a ha then univ else P.I t.row hr
  have hpool : pool.Infinite := by
    by_cases hr : t.row = newRow a ha
    · simpa [pool, hr] using Set.infinite_univ (α := ℕ)
    · have h := P.C t.row hr ⟨0, Ordinal.omega0_pos.trans_le ha⟩ 0
      exact h.mono (inter_subset_left.trans (P.A t.row hr _)) |>.mono (by simp [pool, hr])
  have htargetE : ∀ c, ∀ᶠ n in along pool, ∀ x y : K H,
      projection H t.row x ∈ (Q.V t.row).clopen n →
      projection H t.row y ∈ (Q.V t.row).clopen n →
      projection H t.row x = projection H t.row y → coord c x = coord c y := by
    intro c
    by_cases hr : t.row = newRow a ha
    · have hp : Injective (projection H t.row) := by
        rw [hr]
        intro x y h
        exact h
      exact Eventually.of_forall (fun _ x y _ _ h => congrArg (coord c) (hp h))
    · simpa [coord, pool, hr] using Q.old_e t.row hr c
  choose s hsmap hsmass using fun n =>
    NormPreservingLiftExistence.exists_norm_preserving_lift (projection H t.row)
      (projection H t.row).continuous
      (projection_onto H t.row)
      (Q.measure t.row t.label n)
  obtain ⟨S, vP, hSsub, hSinf, htv, birthS, birthMu, hbirthS, hbirthMu,
    hist, c, hhist, hspec, hc, hm, htests, havoid,
    Y, Z, hclosed, hY, hZ, hcover, hZdef, hYdef, hclosed', honto,
    haux, htarget, hnewAux, hnewTarget, hG, hGinf, hFuniform,
    I, J0, N0, hI, hJ, hNold, hNnew, hA, hB, hC, hIinf, hIold, hJold, hE, hF,
    JA, NA, muA, hResidual⟩ :=
    exists_measured_dynamic_split code hcode (newRow a ha) hzero coord hsep Q.B Q.Bonto rho hrho
      pool hpool (projection H t.row) (projection H t.row).continuous
      (fun n => ((Q.V t.row).clopen n : Set (Base H t.row)))
      (fun n => ((Q.V t.row).clopen n).isClopen)
      (Q.measure t.row t.label) s hsmap hsmass (Q.mass _ _) (Q.null _ _)
      (fun n => ((Q.nu t.row _).1 n).2.1) (fun n => ((Q.nu t.row _).1 n).2.2)
      (Q.positive _ _) htargetE (Base H) (fun r => projection H r)
      (fun r => (projection H r).continuous)
      (fun r => projection_onto H r)
      (fun r n => ((Q.V r).clopen n : Set (Base H r)))
      (fun r n => ((Q.V r).clopen n).isClopen) t.row (fun _ => rfl) (fun _ _ h => h)
      nuR (fun r d n => by simp [nuR, Measure.real, Q.mass]) sR muR hsRmap hsRmass
      (fun r d => Q.null r (oldCol d)) nuA
      (fun r n => by simp [nuA, Measure.real, Q.mass]) (fun r => Q.null r (lastCol a))
      P.I (by intro hr; simp [pool, hr]) P.J P.oldN P.A P.B P.C
      (fun r hr => Q.old_e r hr) hmuR (fun _ _ h => h)
      (fun r _ _ h => ((Q.V r).disjoint h).preimage (projection H r))
      (fun _ _ h => ((Q.V t.row).disjoint h).preimage (projection H t.row))
  obtain ⟨geometry⟩ := SignedSuccessorCoordinates.exists_successor_coordinates H Y Z hY hZ hcover
  let J : Rows a → Cols a → Set ℕ := fun r d =>
    if hd : d.1 < a then J0 r ⟨d.1, hd⟩ else JA r
  let N : Rows a → Cols a → Fin 2 → Set ℕ := fun r d =>
    if hd : d.1 < a then N0 r ⟨d.1, hd⟩ else NA r
  refine ⟨{
    Y := Y, Z := Z, closed := hclosed, closedY := hY, closedZ := hZ, cover := hcover
    coordinates := geometry, I := I, J := J, N := N, rho := rho, rho_cofinal := hrho
    column := c, k_mono := hc
    oldN := ?_, newN := ?_, residualN := NA, residual_eq := ?_, residual_subset := ?_
    A := ?_, B := ?_, C := ?_, I_infinite := hIinf, oldI := hIold, oldJ := ?_, E := hE
    F := ?_, G := ?_ }⟩
  · intro r hr d e
    have hd : d.1 < a := d.2
    simpa [N, hd] using hNold r hr d e
  · intro d e
    have hd : d.1 < a := d.2
    simpa [N, hd, hzero] using hNnew d e
  · intro r e
    simp [N]
  · intro r e
    simpa [J] using (hResidual r).2.2.1 e
  · intro r d
    by_cases hd : d.1 < a
    · simpa [J, hd] using hA r ⟨d.1, hd⟩
    · simpa [J, hd] using (hResidual r).1
  · intro r d
    by_cases hd : d.1 < a
    · simpa [N, hd] using hB r ⟨d.1, hd⟩
    · simpa [N, hd] using (hResidual r).2.1
  · intro r d e
    by_cases hd : d.1 < a
    · simpa [J, N, hd] using hC r ⟨d.1, hd⟩ e
    · simpa [J, N, hd] using (hResidual r).2.2.2.1 e
  · intro r hr d
    have hd : d.1 < a := d.2
    simpa [J, hd] using hJold r hr d
  · letI : CompactSpace (splitCarrier Y Z) := isCompact_iff_compactSpace.mp hclosed.isCompact
    intro r d
    by_cases hd : d.1 < a
    · obtain ⟨mu, hb, hp, hn, hconv⟩ := hF r ⟨d.1, hd⟩
      refine ⟨mu, hb, hp, hn, ?_⟩
      intro sigma hmap hmass
      simpa [J, hd, along] using hconv sigma hmap (fun n => (hmass n).trans (Q.mass r d n).symm)
    · have he : d = (lastCol a) := Subtype.ext (le_antisymm d.2 (le_of_not_gt hd))
      subst d
      exact ⟨muA r, (hResidual r).2.2.2.2.1, (hResidual r).2.2.2.2.2.1,
        (hResidual r).2.2.2.2.2.2.1, fun sigma hmap hmass => by
          simpa [J, along] using (hResidual r).2.2.2.2.2.2.2 sigma hmap
            (fun n => (hmass n).trans (Q.mass r _ n).symm)⟩
  · intro q s hmap hmass
    exact hG q s hmap (hmass.trans (Q.mass t.row t.label _).symm)


namespace Result

variable {H} {ha : ω ≤ a} {P : Predecessor H ha} {launch : Launch a}
  {Q : Prepared H ha P launch} {t : Treatment a} (R : Result H ha P launch Q t)

/-- Append only the newly produced arrival pack. Earlier entries are unchanged. -/
noncomputable def arrival : PastBirths (Order.succ a) := by
  classical
  intro b r d hr hm
  exact if hb : b.1 < a then P.births ⟨b.1, hb⟩ r d hr hm else
    R.N ⟨r, hr, (le_max_left r d).trans (hm.le.trans (Order.le_of_lt_succ b.2))⟩
      ⟨d, (le_max_right r d).trans (hm.le.trans (Order.le_of_lt_succ b.2))⟩

/-- Readback on every born pair uses its one permanent arrival entry, including
the two boundary cases where the row or the label has just been born. -/
theorem birth_readback (r : Rows a) (d : Cols a) (e : Fin 2) :
    R.arrival.read r.1 d.1 r.2.1
      (lt_of_le_of_lt (max_le r.2.2 d.2) (Order.lt_succ a)) e = R.N r d e := by
  classical
  dsimp only [PastBirths.read, arrival]
  split_ifs with h
  · have hr : r ≠ newRow a ha := by
      intro he
      have hlt := (lt_of_le_of_lt (le_max_left r.1 d.1) h)
      exact (ne_of_lt hlt) (congrArg Subtype.val he)
    have hd : d.1 < a := lt_of_le_of_lt (le_max_right r.1 d.1) h
    exact (R.oldN r hr ⟨d.1, hd⟩ e).symm
  · rfl

/-- The entire older birth pack, not just a later N value, is retained. -/
theorem arrival_retains (b : Coord a) (r d : Ordinal.{0}) (hr : ω ≤ r)
    (hm : max r d = b.1) (e : Fin 2) :
    R.arrival ⟨b.1, b.2.trans (Order.lt_succ a)⟩ r d hr hm e =
      P.births b r d hr hm e := by
  classical
  have hb : b.1 < a := b.2
  simp [arrival, hb]

/-- The actual inserted cube projection, expressed through its certified split
presentation; restrict_inverse identifies it with literal ordinal restriction. -/
def literalProjection (r : Rows a) : C(R.coordinates.carrier, Base H r) := by
  with_unfolding_all
    let p : C(splitCarrier R.Y R.Z, K H) :=
      ⟨fun x => x.1.1, continuous_fst.comp continuous_subtype_val⟩
    let e : C(R.coordinates.carrier, splitCarrier R.Y R.Z) :=
      ⟨R.coordinates.equiv.symm, R.coordinates.equiv.symm.continuous⟩
    exact (projection H r).comp (p.comp e)

private theorem literal_projection_read (r : Rows a) (x : R.coordinates.carrier) :
    (R.literalProjection r x).1 = restrict (r.2.2.trans (Order.le_succ a)) x.1 := by
  exact (R.coordinates.restrict_inverse r.1 r.2.2 x).symm

instance literalMeasurable : MeasurableSpace R.coordinates.carrier := borel _
instance literalBorel : BorelSpace R.coordinates.carrier := ⟨rfl⟩

/-- One clopen in the actual literal successor cube. -/
def quantitativeClopen : Clopens R.coordinates.carrier :=
  ⟨{x | x.1 ⟨a, Order.lt_succ a⟩ = true},
    (isClopen_discrete ({true} : Set Bool)).preimage
      ((continuous_apply (⟨a, Order.lt_succ a⟩ : Coord (Order.succ a))).comp
        continuous_subtype_val)⟩

private theorem variation_homeomorph {X X' : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X']
    (e : X ≃ₜ X') (s : SignedMeasure X) :
    SignedMeasure.totalVariation (s.map e) = s.totalVariation.map e := by
  simpa only [SignedMeasure.totalVariation_eq_variation] using
    e.measurableEmbedding.variation_map (μ := s)

private theorem jordan_homeomorph {X X' : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X']
    (e : X ≃ₜ X') (s : SignedMeasure X) :
    SignedMeasure.toJordanDecomposition (s.map e) =
      { posPart := s.toJordanDecomposition.posPart.map e
        negPart := s.toJordanDecomposition.negPart.map e
        mutuallySingular := e.toMeasurableEquiv.measurableEmbedding.mutuallySingular_map
          s.toJordanDecomposition.mutuallySingular } := by
  apply SignedMeasure.toJordanDecomposition_eq
  apply VectorMeasure.ext
  intro A hA
  rw [VectorMeasure.map_apply _ e.continuous.measurable hA,
    SignedMeasure.apply_eq_posPart_real_sub_negPart_real s (e.continuous.measurable hA),
    JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply hA]
  simp only [Measure.real, Measure.map_apply e.continuous.measurable hA]

private theorem functional_homeomorph {X X' : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X'] [CompactSpace X']
    (e : X ≃ₜ X') (s : SignedMeasure X) (f : C(X', ℝ)) :
    NormPreservingLifts.signedFunctional (s.map e) f =
      NormPreservingLifts.signedFunctional s (f.comp ⟨e, e.continuous⟩) := by
  change (∫ᵛ y, f y ∂•(s.map e)) = ∫ᵛ x, f (e x) ∂•s
  exact e.toMeasurableEquiv.measurableEmbedding.integral_map_vectorMeasure

set_option backward.isDefEq.respectTransparency false in
/-- On the actual literal successor, one regular norm-bounded reference measure
is chosen before every sequence of norm-one lifts of the original measures. -/
theorem literal_f :
    letI : CompactSpace R.coordinates.carrier :=
      isCompact_iff_compactSpace.mp R.coordinates.closed.isCompact
    ∀ r d, ∃ mu : SignedMeasure R.coordinates.carrier,
      mu.totalVariation.real univ ≤ 1 ∧
      Measure.Regular mu.toJordanDecomposition.posPart ∧
      Measure.Regular mu.toJordanDecomposition.negPart ∧
      ∀ sigma : ℕ → SignedMeasure R.coordinates.carrier,
        (∀ n, (sigma n).map (R.literalProjection r) = Q.measure r d n) →
        (∀ n, (sigma n).totalVariation univ = 1) →
        Tendsto (fun n => (NormPreservingLifts.signedFunctional (sigma n)).toWeakDual)
          (along (R.J r d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
  with_unfolding_all
    letI : CompactSpace R.coordinates.carrier :=
      isCompact_iff_compactSpace.mp R.coordinates.closed.isCompact
    letI : CompactSpace (splitCarrier R.Y R.Z) :=
      isCompact_iff_compactSpace.mp R.closed.isCompact
    let E : splitCarrier R.Y R.Z ≃ₜ R.coordinates.carrier := R.coordinates.equiv
    intro r d
    obtain ⟨mu, hb, hp, hn, hconv⟩ := R.F r d
    refine ⟨mu.map E, ?_, ?_, ?_, ?_⟩
    · simpa only [Measure.real, variation_homeomorph, Measure.map_apply E.continuous.measurable
        MeasurableSet.univ, preimage_univ] using hb
    · rw [jordan_homeomorph]
      letI := hp
      exact Measure.Regular.map E
    · rw [jordan_homeomorph]
      letI := hn
      exact Measure.Regular.map E
    · intro sigma hmap hmass
      let tau : ℕ → SignedMeasure (splitCarrier R.Y R.Z) := fun n => (sigma n).map E.symm
      have hm (n : ℕ) :
          (tau n).map (fun x => projection H r x.1.1) = Q.measure r d n := by
        refine Eq.trans ?_ (hmap n)
        apply VectorMeasure.ext
        intro A hA
        let p : C(splitCarrier R.Y R.Z, Base H r) :=
          ⟨fun x => projection H r x.1.1,
            (projection H r).continuous.comp (continuous_fst.comp continuous_subtype_val)⟩
        calc
          (tau n).map p A = tau n (p ⁻¹' A) :=
            VectorMeasure.map_apply _ p.continuous.measurable hA
          _ = sigma n (E.symm ⁻¹' (p ⁻¹' A)) :=
            VectorMeasure.map_apply _ E.symm.continuous.measurable
              (p.continuous.measurable hA)
          _ = (sigma n).map (R.literalProjection r) A :=
            (VectorMeasure.map_apply _ (R.literalProjection r).continuous.measurable hA).symm
      have ht (n : ℕ) : (tau n).totalVariation univ = 1 := by
        rw [variation_homeomorph, Measure.map_apply E.symm.continuous.measurable
          MeasurableSet.univ, preimage_univ]
        exact hmass n
      have hc := hconv tau hm ht
      apply tendsto_iff_forall_eval_tendsto_topDualPairing.mpr
      intro f
      have hf := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hc)
        (f.comp ⟨E, E.continuous⟩)
      change Tendsto (fun n => NormPreservingLifts.signedFunctional (sigma n) f)
        (along (R.J r d)) (𝓝 (NormPreservingLifts.signedFunctional (mu.map E) f))
      have he (n : ℕ) :
          NormPreservingLifts.signedFunctional (tau n) (f.comp ⟨E, E.continuous⟩) =
            NormPreservingLifts.signedFunctional (sigma n) f := by
        rw [functional_homeomorph]
        congr 1
        ext x
        exact congrArg f (E.apply_symm_apply x)
      change Tendsto
        (fun n => NormPreservingLifts.signedFunctional (tau n) (f.comp ⟨E, E.continuous⟩))
        (along (R.J r d))
        (𝓝 (NormPreservingLifts.signedFunctional mu (f.comp ⟨E, E.continuous⟩))) at hf
      rw [functional_homeomorph]
      simpa only [he] using hf

set_option backward.isDefEq.respectTransparency false in
/-- Every literal successor coordinate is eventually constant on each original
support fibre, including the newly inserted sheet coordinate. -/
theorem literal_e (r : Rows a) (c : Coord (Order.succ a)) :
    ∀ᶠ n in along (R.I r), ∀ x y : R.coordinates.carrier,
      R.literalProjection r x ∈ (Q.V r).clopen n →
      R.literalProjection r y ∈ (Q.V r).clopen n →
      R.literalProjection r x = R.literalProjection r y → x.1 c = y.1 c := by
  with_unfolding_all
    by_cases hc : c.1 < a
    · let A : Set (K H) := {x | x.1 ⟨c.1, hc⟩ = true}
      have hA : IsClopen A := (isClopen_discrete ({true} : Set Bool)).preimage
        ((continuous_apply (⟨c.1, hc⟩ : Coord a)).comp continuous_subtype_val)
      filter_upwards [R.E r A hA] with n hn x y hx hy hxy
      have h := (hn (R.coordinates.equiv.symm x) (R.coordinates.equiv.symm y) hx hy hxy).1
      have hxread := R.coordinates.insert (R.coordinates.equiv.symm x) c
      have hyread := R.coordinates.insert (R.coordinates.equiv.symm y) c
      simp only [Homeomorph.apply_symm_apply, dite_eq_left hc] at hxread hyread
      change ((R.coordinates.equiv.symm x).1.1.1 ⟨c.1, hc⟩ = true ↔
        (R.coordinates.equiv.symm y).1.1.1 ⟨c.1, hc⟩ = true) at h
      rw [← hxread, ← hyread] at h
      exact Bool.eq_iff_iff.mpr h
    · have he : c = top a := Subtype.ext
        (le_antisymm (Order.le_of_lt_succ c.2) (le_of_not_gt hc))
      subst c
      filter_upwards [R.E r univ isClopen_univ] with n hn x y hx hy hxy
      have h := (hn (R.coordinates.equiv.symm x) (R.coordinates.equiv.symm y) hx hy hxy).2
      calc
        x.1 (top a) = (R.coordinates.equiv.symm x).1.2 := by
          rw [R.coordinates.inverse_sheet]; rfl
        _ = (R.coordinates.equiv.symm y).1.2 := h
        _ = y.1 (top a) := by rw [R.coordinates.inverse_sheet]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- Transport an arbitrary signed clopen readout through this exact event's
coordinate equivalence, preserving its whole measure label and column. -/
theorem quantitative_transport (predicate : ℝ → Prop)
    (q : ℕ) (s : SignedMeasure R.coordinates.carrier)
    (hmap : s.map (R.literalProjection t.row) = Q.measure t.row t.label (R.column q).n)
    (hmass : s.totalVariation univ = 1)
    (h : ∀ sigma : SignedMeasure (splitCarrier R.Y R.Z),
      sigma.map (fun x => projection H t.row x.1.1) = Q.measure t.row t.label (R.column q).n →
      sigma.totalVariation univ = 1 → predicate (sigma {x | x.1.2 = true})) :
    predicate (s R.quantitativeClopen) := by
  with_unfolding_all
    let E : splitCarrier R.Y R.Z ≃ₜ R.coordinates.carrier := R.coordinates.equiv
    let p : C(splitCarrier R.Y R.Z, Base H t.row) :=
      ⟨fun x => projection H t.row x.1.1,
        (projection H t.row).continuous.comp (continuous_fst.comp continuous_subtype_val)⟩
    let sigma : SignedMeasure (splitCarrier R.Y R.Z) := s.map E.symm
    have hm : sigma.map (fun x => projection H t.row x.1.1) =
        Q.measure t.row t.label (R.column q).n := by
      refine Eq.trans ?_ hmap
      apply VectorMeasure.ext
      intro A hA
      calc
        sigma.map p A = sigma (p ⁻¹' A) :=
          VectorMeasure.map_apply sigma p.continuous.measurable hA
        _ = s (E.symm ⁻¹' (p ⁻¹' A)) :=
          VectorMeasure.map_apply s E.symm.continuous.measurable
            (p.continuous.measurable hA)
        _ = s.map (R.literalProjection t.row) A :=
          (VectorMeasure.map_apply s (R.literalProjection t.row).continuous.measurable hA).symm
    have hn : sigma.totalVariation univ = 1 := by
      have hv : (s.map E.symm).variation = s.variation.map E.symm :=
        E.symm.toMeasurableEquiv.measurableEmbedding.variation_map
      change SignedMeasure.totalVariation (s.map E.symm) univ = 1
      rw [SignedMeasure.totalVariation_eq_variation, hv,
        Measure.map_apply E.symm.continuous.measurable MeasurableSet.univ, preimage_univ,
        ← SignedMeasure.totalVariation_eq_variation, hmass]
    have he : sigma {x | x.1.2 = true} = s R.quantitativeClopen := by
      have hsheet : MeasurableSet ({x | x.1.2 = true} : Set (splitCarrier R.Y R.Z)) :=
        ((isClopen_discrete ({true} : Set Bool)).preimage
          (continuous_snd.comp continuous_subtype_val)).1.measurableSet
      calc
        sigma {x | x.1.2 = true} = s (E.symm ⁻¹' {x | x.1.2 = true}) :=
          VectorMeasure.map_apply s E.symm.continuous.measurable hsheet
        _ = s R.quantitativeClopen := by
          congr 1
          ext x
          change (E.symm x).1.2 = true ↔ x.1 ⟨a, Order.lt_succ a⟩ = true
          rw [R.coordinates.inverse_sheet x]
          rfl
    simpa only [he] using h sigma hm hn

set_option backward.isDefEq.respectTransparency false in
/-- Quantitative G is retained on the actual cube carrier with one fixed
strictly increasing sequence, for every original signed norm-one lift. -/
theorem quantitative_g (q : ℕ) (s : SignedMeasure R.coordinates.carrier)
    (hmap : s.map (R.literalProjection t.row) = Q.measure t.row t.label (R.column q).n)
    (hmass : s.totalVariation univ = 1) :
    (q % 2 = 0 → (1 : ℝ) / 6 < s R.quantitativeClopen) ∧
    (q % 2 ≠ 0 → s R.quantitativeClopen = 0) := by
  exact R.quantitative_transport
    (fun value => (q % 2 = 0 → (1 : ℝ) / 6 < value) ∧ (q % 2 ≠ 0 → value = 0))
    q s hmap hmass (R.G q)

end Result

/-- A genuine ordinary successor on literal ordinal cubes, with all legal
current births constructed before treatment and permanent arrival readback. -/
theorem exists_successor (ha : ω ≤ a) (P : Predecessor H ha)
    (launch : Launch a) (t : Treatment a) (hCH : Cardinal.continuum.{0} = ℵ₁) :
    ∃ (Q : Prepared H ha P launch) (R : Result H ha P launch Q t),
      (∀ (r : Rows a) (d : Cols a) (e : Fin 2),
        R.arrival.read r.1 d.1 r.2.1
          (lt_of_le_of_lt (max_le r.2.2 d.2) (Order.lt_succ a)) e = R.N r d e) ∧
      (∀ (b : Coord a) (r d : Ordinal.{0}) (hr : ω ≤ r) (hm : max r d = b.1) (e : Fin 2),
        R.arrival ⟨b.1, b.2.trans (Order.lt_succ a)⟩ r d hr hm e = P.births b r d hr hm e) ∧
      (∀ (r : Rows a) (x : R.coordinates.carrier),
        (R.literalProjection r x).1 = restrict (r.2.2.trans (Order.le_succ a)) x.1) ∧
      (∀ (q : ℕ) (s : SignedMeasure R.coordinates.carrier),
        s.map (R.literalProjection t.row) = Q.measure t.row t.label (R.column q).n →
        s.totalVariation univ = 1 →
        (q % 2 = 0 → (1 : ℝ) / 6 < s R.quantitativeClopen) ∧
        (q % 2 ≠ 0 → s R.quantitativeClopen = 0)) := by
  obtain ⟨Q⟩ := exists_prepared H ha P launch hCH
  obtain ⟨R⟩ := exists_ordinary H ha P launch Q t
  exact ⟨Q, R, R.birth_readback, R.arrival_retains, R.literal_projection_read, R.quantitative_g⟩

end D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor
