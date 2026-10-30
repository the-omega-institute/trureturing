/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalPredecessor
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalPredecessor
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Actual old-carrier enumeration and arrival data for the next predecessor. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor

/-! The old carriers are literally equal. Transport therefore retains whole
support and regular signed-sequence enumerations on their full Label domains.
The original Q and R remain the birth data; arrival stores only N entries. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalPredecessor

open SignedProperLimit SignedBirthEnumeration SignedOrdinalSuccessor
open D5.S3.Topology.Measures

variable {a : Ordinal.{0}} {H : Prefix (Order.succ a)} {ha : ω ≤ a}
  {P : Predecessor H ha} {launch : Launch a} {Q : Prepared H ha P launch}
  {t : Treatment a} (R : Result H ha P launch Q t)

/-- An old next-stage row is precisely a current row. -/
def previousRow (ha : ω ≤ a) (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a))) : Rows a :=
  ⟨r.1, r.2.1, Order.le_of_lt_succ
    (lt_of_le_of_ne r.2.2 (fun h => hr (Subtype.ext h)))⟩

/-- No new measure label is needed at the next stage. -/
private def previousCol (d : Coord (Order.succ a)) : Cols a :=
  ⟨d.1, Order.le_of_lt_succ d.2⟩

theorem old_carrier (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a))) :
    R.coordinates.extended.carrier (rowIndex r) =
      H.carrier (rowIndex (previousRow ha r hr)) :=
  R.coordinates.old_carrier (rowIndex (previousRow ha r hr))

/-- Equality transport, rather than a replacement support enumeration. -/
private def familyEquiv {b : Ordinal.{0}} {C D : Set (Cube b)} (h : C = D) :
    SupportFamily C ≃ SupportFamily D := by
  subst D
  exact Equiv.refl _

/-- Equality transport includes regularity and all BornData certificates. -/
private def bornEquiv {b : Ordinal.{0}} {C D : Set (Cube b)} (h : C = D)
    (V : SupportFamily C) :
    @BornData C _ (borel C) V ≃ @BornData D _ (borel D) (familyEquiv h V) := by
  subst D
  exact Equiv.refl _

private def signedEquiv {b : Ordinal.{0}} {C D : Set (Cube b)} (h : C = D) :
    @SignedMeasure C (borel C) ≃ @SignedMeasure D (borel D) := by
  subst D
  exact Equiv.refl _

private theorem bornEquiv_readback {b : Ordinal.{0}} {C D : Set (Cube b)}
    (h : C = D) (V : SupportFamily D) (nu : @BornData D _ (borel D) V) (n : ℕ) :
    signedEquiv h (((bornEquiv h.symm V nu).1 n).1) = ((nu.1 n).1) := by
  subst D
  rfl

private theorem familyEquiv_mem {b : Ordinal.{0}} {C D : Set (Cube b)}
    (h : C = D) (V : SupportFamily D) (n : ℕ) (x : C) :
    x ∈ (familyEquiv h.symm V).clopen n ↔
      Homeomorph.setCongr h x ∈ V.clopen n := by
  subst D
  rfl

private theorem signedEquiv_mass {b : Ordinal.{0}} {C D : Set (Cube b)}
    (h : C = D) (mu : @SignedMeasure C (borel C)) :
    letI : MeasurableSpace C := borel C
    letI : MeasurableSpace D := borel D
    (signedEquiv h mu).totalVariation univ = mu.totalVariation univ := by
  subst D
  rfl

private theorem signedEquiv_map {b c : Ordinal.{0}}
    {C C' : Set (Cube b)} {D D' : Set (Cube c)} (hC : C = C') (hD : D = D')
    (f : C → D) (g : C' → D')
    (hf : ∀ x, Homeomorph.setCongr hD (f x) = g (Homeomorph.setCongr hC x))
    (mu : @SignedMeasure C (borel C)) :
    letI : MeasurableSpace C := borel C
    letI : MeasurableSpace C' := borel C'
    letI : MeasurableSpace D := borel D
    letI : MeasurableSpace D' := borel D'
    (signedEquiv hC mu).map g = signedEquiv hD (mu.map f) := by
  subst C'
  subst D'
  have hfg : f = g := funext hf
  subst g
  rfl

private theorem signedEquiv_symm {b : Ordinal.{0}} {C D : Set (Cube b)}
    (h : C = D) (mu : @SignedMeasure D (borel D)) :
    signedEquiv h (signedEquiv h.symm mu) = mu := by
  subst D
  rfl

private theorem signedEquiv_tendsto {b : Ordinal.{0}} {C D : Set (Cube b)}
    [CompactSpace C] [CompactSpace D] (h : C = D)
    (s : ℕ → @SignedMeasure C (borel C)) (mu : @SignedMeasure C (borel C))
    (L : Filter ℕ) :
    letI : MeasurableSpace C := borel C
    letI : BorelSpace C := ⟨rfl⟩
    letI : MeasurableSpace D := borel D
    letI : BorelSpace D := ⟨rfl⟩
    Tendsto (fun n => (NormPreservingLifts.signedFunctional
      (signedEquiv h (s n))).toWeakDual) L
      (𝓝 (NormPreservingLifts.signedFunctional (signedEquiv h mu)).toWeakDual) ↔
    Tendsto (fun n => (NormPreservingLifts.signedFunctional (s n)).toWeakDual) L
      (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
  subst D
  rfl

noncomputable def currentU (r : Rows a) : Label → SupportFamily (Base H r) := by
  classical
  exact if h : r = newRow a ha then (by rw [h]; exact Q.U) else P.U r h

private theorem currentU_onto (r : Rows a) : Surjective (currentU (Q := Q) r) := by
  classical
  unfold currentU
  split_ifs with h
  · subst r
    exact Q.Uonto
  · exact P.Uonto r h

private noncomputable def nextU (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a))) :
    Label → SupportFamily (Base R.coordinates.extended r) :=
  (familyEquiv (old_carrier R r hr).symm) ∘ currentU (Q := Q) (previousRow ha r hr)

private theorem nextU_onto (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a))) :
    Surjective (nextU R r hr) :=
  (familyEquiv (old_carrier R r hr).symm).surjective.comp (currentU_onto _)

private def nextV (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a))) :
    SupportFamily (Base R.coordinates.extended r) :=
  familyEquiv (old_carrier R r hr).symm (Q.V (previousRow ha r hr))

private def nextNu (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a))) :
    Label → BornData (nextV R r hr) :=
  (bornEquiv (old_carrier R r hr).symm (Q.V (previousRow ha r hr))) ∘
    Q.nu (previousRow ha r hr)

private theorem nextNu_onto (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a))) :
    Surjective (nextNu R r hr) :=
  (bornEquiv (old_carrier R r hr).symm (Q.V (previousRow ha r hr))).surjective.comp
    (Q.nuonto (previousRow ha r hr))

private def nextI (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a))) : Set ℕ :=
  R.I (previousRow ha r hr)

private def nextJ (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a)))
    (d : Coord (Order.succ a)) : Set ℕ :=
  R.J (previousRow ha r hr) (previousCol d)

private theorem nextA (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a)))
    (d : Coord (Order.succ a)) : nextJ R r hr d ⊆ nextI R r hr :=
  R.A (previousRow ha r hr) (previousCol d)

private theorem next_birth (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a)))
    (d : Coord (Order.succ a)) (e : Fin 2) :
    R.arrival.read r.1 d.1 r.2.1
      (max_lt (lt_of_le_of_ne r.2.2 (fun h => hr (Subtype.ext h))) d.2) e =
      R.N (previousRow ha r hr) (previousCol d) e :=
  R.birth_readback (previousRow ha r hr) (previousCol d) e

private theorem nextB (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a)))
    (d : Coord (Order.succ a)) : Disjoint
    (R.arrival.read r.1 d.1 r.2.1
      (max_lt (lt_of_le_of_ne r.2.2 (fun h => hr (Subtype.ext h))) d.2) 0)
    (R.arrival.read r.1 d.1 r.2.1
      (max_lt (lt_of_le_of_ne r.2.2 (fun h => hr (Subtype.ext h))) d.2) 1) := by
  rw [next_birth R r hr d 0, next_birth R r hr d 1]
  exact R.B (previousRow ha r hr) (previousCol d)

private theorem nextC (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a)))
    (d : Coord (Order.succ a)) (e : Fin 2) :
    (nextJ R r hr d ∩ R.arrival.read r.1 d.1 r.2.1
      (max_lt (lt_of_le_of_ne r.2.2 (fun h => hr (Subtype.ext h))) d.2) e).Infinite := by
  rw [next_birth R r hr d e]
  exact R.C (previousRow ha r hr) (previousCol d) e

private theorem next_proper (P : Predecessor H ha) : Order.succ a < ω₁ :=
  (Cardinal.isSuccLimit_omega 1).succ_lt P.proper

private def topEquiv : K R.coordinates.extended ≃ₜ R.coordinates.carrier :=
  Homeomorph.setCongr R.coordinates.top_carrier

private def baseEquiv (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a))) :
    Base R.coordinates.extended r ≃ₜ Base H (previousRow ha r hr) :=
  Homeomorph.setCongr (old_carrier R r hr)

/-- Both sides read the same original ordinal coordinates. -/
private theorem projection_cast (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a)))
    (x : K R.coordinates.extended) :
    baseEquiv R r hr (projection R.coordinates.extended r x) =
      R.literalProjection (previousRow ha r hr) (topEquiv R x) := by
  apply Subtype.ext
  exact R.coordinates.restrict_inverse r.1 (previousRow ha r hr).2.2 (topEquiv R x)

private theorem nextV_mem (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a)))
    (n : ℕ) (x : Base R.coordinates.extended r) :
    x ∈ (nextV R r hr).clopen n ↔
      baseEquiv R r hr x ∈ (Q.V (previousRow ha r hr)).clopen n :=
  familyEquiv_mem (old_carrier R r hr) (Q.V (previousRow ha r hr)) n x

private theorem nextNu_readback (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a)))
    (d : Label) (n : ℕ) :
    signedEquiv (old_carrier R r hr) (((nextNu R r hr d).1 n).1) =
      (((Q.nu (previousRow ha r hr) d).1 n).1) :=
  bornEquiv_readback (old_carrier R r hr) (Q.V (previousRow ha r hr))
    (Q.nu (previousRow ha r hr) d) n

private theorem next_map_cast (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a)))
    (s : SignedMeasure (K R.coordinates.extended)) :
    (signedEquiv R.coordinates.top_carrier s).map
      (R.literalProjection (previousRow ha r hr)) =
    signedEquiv (old_carrier R r hr) (s.map (projection R.coordinates.extended r)) :=
  signedEquiv_map R.coordinates.top_carrier (old_carrier R r hr)
    (projection R.coordinates.extended r) (R.literalProjection (previousRow ha r hr))
    (projection_cast R r hr) s

private theorem next_base_onto :
    Surjective (fun x : K R.coordinates.extended =>
      restrict (ha.trans (Order.le_succ a)) x.1) := by
  intro y
  obtain ⟨x, hx⟩ := P.base_onto y
  let r : Coord (Order.succ (Order.succ a)) :=
    ⟨a, (Order.lt_succ a).trans (Order.lt_succ (Order.succ a))⟩
  have hcarrier : R.coordinates.extended.carrier r = H.carrier (top a) :=
    R.coordinates.old_carrier (top a)
  have hxmem : x.1 ∈ R.coordinates.extended.carrier r := hcarrier.symm ▸ x.2
  obtain ⟨z, hz⟩ := R.coordinates.extended.onto r (top (Order.succ a))
    (Order.le_succ a) ⟨x.1, hxmem⟩
  refine ⟨z, ?_⟩
  exact (congrArg (restrict ha) hz).trans hx

private theorem nextE (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a)))
    (c : Coord (Order.succ a)) :
    ∀ᶠ n in along (nextI R r hr), ∀ x y : K R.coordinates.extended,
      projection R.coordinates.extended r x ∈ (nextV R r hr).clopen n →
      projection R.coordinates.extended r y ∈ (nextV R r hr).clopen n →
      projection R.coordinates.extended r x = projection R.coordinates.extended r y →
      x.1 c = y.1 c := by
  filter_upwards [R.literal_e (previousRow ha r hr) c] with n hn x y hx hy hxy
  have hx' : R.literalProjection (previousRow ha r hr) (topEquiv R x) ∈
      (Q.V (previousRow ha r hr)).clopen n := by
    rw [← projection_cast R r hr x]
    exact (nextV_mem R r hr n _).mp hx
  have hy' : R.literalProjection (previousRow ha r hr) (topEquiv R y) ∈
      (Q.V (previousRow ha r hr)).clopen n := by
    rw [← projection_cast R r hr y]
    exact (nextV_mem R r hr n _).mp hy
  have hp : R.literalProjection (previousRow ha r hr) (topEquiv R x) =
      R.literalProjection (previousRow ha r hr) (topEquiv R y) :=
    (projection_cast R r hr x).symm.trans
      ((congrArg (baseEquiv R r hr) hxy).trans (projection_cast R r hr y))
  exact hn (topEquiv R x) (topEquiv R y) hx' hy' hp

set_option backward.isDefEq.respectTransparency false in
private theorem nextF (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a)))
    (d : Coord (Order.succ a)) (s : ℕ → SignedMeasure (K R.coordinates.extended))
    (hm : ∀ n, (s n).map (projection R.coordinates.extended r) =
      (((nextNu R r hr ⟨d.1, d.2.trans (next_proper P)⟩).1 n).1))
    (hn : ∀ n, (s n).totalVariation univ = 1) :
    ∃ mu : SignedMeasure (K R.coordinates.extended), Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (s n)).toWeakDual)
      (along (nextJ R r hr d)) (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
  with_unfolding_all
    let : CompactSpace R.coordinates.carrier :=
      isCompact_iff_compactSpace.mp R.coordinates.closed.isCompact
    obtain ⟨mu, _, _, _, hconv⟩ := R.literal_f (previousRow ha r hr) (previousCol d)
    let sigma : ℕ → SignedMeasure R.coordinates.carrier :=
      fun n => signedEquiv R.coordinates.top_carrier (s n)
    have hm' (n : ℕ) : (sigma n).map (R.literalProjection (previousRow ha r hr)) =
        Q.measure (previousRow ha r hr) (previousCol d) n := by
      dsimp only [sigma]
      exact (next_map_cast R r hr (s n)).trans
        ((congrArg (signedEquiv (old_carrier R r hr)) (hm n)).trans
          (nextNu_readback R r hr _ n))
    have hn' (n : ℕ) : (sigma n).totalVariation univ = 1 :=
      (signedEquiv_mass R.coordinates.top_carrier (s n)).trans (hn n)
    have hc := hconv sigma hm' hn'
    refine ⟨signedEquiv R.coordinates.top_carrier.symm mu, ?_⟩
    apply (signedEquiv_tendsto R.coordinates.top_carrier s
      (signedEquiv R.coordinates.top_carrier.symm mu) (along (nextJ R r hr d))).mp
    simpa only [signedEquiv_symm, sigma, nextJ] using hc

/-- An executed original split supplies the actual next predecessor. The
original Q/R objects retain the complete birth data for historical use. -/
noncomputable def nextP :
    Predecessor R.coordinates.extended (ha.trans (Order.le_succ a)) where
  proper := next_proper P
  base_onto := next_base_onto R
  births := R.arrival
  U := nextU R
  Uonto := nextU_onto R
  V := nextV R
  nu := nextNu R
  nuonto := nextNu_onto R
  I := nextI R
  J := nextJ R
  A := nextA R
  B := nextB R
  C := nextC R
  E := nextE R
  F := nextF R

private theorem family_transport_heq {b : Ordinal.{0}} {C D : Set (Cube b)}
    (h : C = D) (U : Label → SupportFamily C) :
    HEq ((familyEquiv h) ∘ U) U := by
  subst D
  rfl

private theorem born_transport_heq {b : Ordinal.{0}} {C D : Set (Cube b)}
    (h : C = D) (V : SupportFamily C) (nu : Label → @BornData C _ (borel C) V) :
    HEq ((bornEquiv h V) ∘ nu) nu := by
  subst D
  rfl

/-- The next predecessor reads the same entire support enumeration. -/
theorem next_U_readback (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a))) :
    HEq ((nextP R).U r hr) (currentU (Q := Q) (previousRow ha r hr)) :=
  family_transport_heq (old_carrier R r hr).symm _

/-- The row support family is transported by literal carrier equality. -/
theorem next_V_readback (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a))) :
    HEq ((nextP R).V r hr) (Q.V (previousRow ha r hr)) := by
  change HEq (familyEquiv (old_carrier R r hr).symm _) _
  generalize (old_carrier R r hr).symm = h
  exact (show ∀ {b : Ordinal.{0}} {C D : Set (Cube b)} (h : C = D)
    (V : SupportFamily C), HEq (familyEquiv h V) V from by
      intro b C D h V; subst D; rfl) h _

/-- Every measure label retains its original whole BornData. -/
theorem next_nu_readback (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a))) :
    HEq ((nextP R).nu r hr) (Q.nu (previousRow ha r hr)) :=
  born_transport_heq (old_carrier R r hr).symm _ _


private theorem signedEquiv_regular_bound {b : Ordinal.{0}} {C D : Set (Cube b)}
    (h : C = D) (mu : @SignedMeasure C (borel C)) :
    letI : MeasurableSpace C := borel C
    letI : MeasurableSpace D := borel D
    mu.totalVariation.real univ ≤ 1 →
    Measure.Regular mu.toJordanDecomposition.posPart →
    Measure.Regular mu.toJordanDecomposition.negPart →
    (signedEquiv h mu).totalVariation.real univ ≤ 1 ∧
      Measure.Regular (signedEquiv h mu).toJordanDecomposition.posPart ∧
      Measure.Regular (signedEquiv h mu).toJordanDecomposition.negPart := by
  subst D
  exact fun hb hp hn => ⟨hb, hp, hn⟩

set_option backward.isDefEq.respectTransparency false in
/-- A history consumer retains the regular bounded F of the very same R.
The weaker Predecessor.F field is unchanged. -/
theorem next_regular_f (r : Rows (Order.succ a))
    (hr : r ≠ newRow (Order.succ a) (ha.trans (Order.le_succ a)))
    (d : Coord (Order.succ a)) (s : ℕ → SignedMeasure (K R.coordinates.extended))
    (hm : ∀ n, (s n).map (projection R.coordinates.extended r) =
      ((((nextP R).nu r hr ⟨d.1, d.2.trans (nextP R).proper⟩).1 n).1))
    (hn : ∀ n, (s n).totalVariation univ = 1) :
    ∃ mu : SignedMeasure (K R.coordinates.extended),
      mu.totalVariation.real univ ≤ 1 ∧
      Measure.Regular mu.toJordanDecomposition.posPart ∧
      Measure.Regular mu.toJordanDecomposition.negPart ∧ Tendsto
        (fun n => (NormPreservingLifts.signedFunctional (s n)).toWeakDual)
        (along ((nextP R).J r hr d))
        (𝓝 (NormPreservingLifts.signedFunctional mu).toWeakDual) := by
  with_unfolding_all
    let : CompactSpace R.coordinates.carrier :=
      isCompact_iff_compactSpace.mp R.coordinates.closed.isCompact
    obtain ⟨mu, hb, hp, hneg, hconv⟩ := R.literal_f (previousRow ha r hr) (previousCol d)
    let sigma : ℕ → SignedMeasure R.coordinates.carrier :=
      fun n => signedEquiv R.coordinates.top_carrier (s n)
    have hm' (n : ℕ) : (sigma n).map (R.literalProjection (previousRow ha r hr)) =
        Q.measure (previousRow ha r hr) (previousCol d) n := by
      dsimp only [sigma]
      exact (next_map_cast R r hr (s n)).trans
        ((congrArg (signedEquiv (old_carrier R r hr)) (hm n)).trans
          (nextNu_readback R r hr _ n))
    have hn' (n : ℕ) : (sigma n).totalVariation univ = 1 :=
      (signedEquiv_mass R.coordinates.top_carrier (s n)).trans (hn n)
    have hc := hconv sigma hm' hn'
    have hh := signedEquiv_regular_bound R.coordinates.top_carrier.symm mu hb hp hneg
    refine ⟨signedEquiv R.coordinates.top_carrier.symm mu, hh.1, hh.2.1, hh.2.2, ?_⟩
    apply (signedEquiv_tendsto R.coordinates.top_carrier s
      (signedEquiv R.coordinates.top_carrier.symm mu) (along (nextJ R r hr d))).mp
    simpa only [signedEquiv_symm, sigma, nextJ] using hc

end D5.S3.Topology.InverseLimit.SignedOrdinalPredecessor
