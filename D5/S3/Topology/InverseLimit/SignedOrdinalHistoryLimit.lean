/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalHistoryLimit
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalHistoryLimit
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: The actual proper-limit event consumes the unique strict past archive. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalHistoryPast
import D5.S3.Topology.InverseLimit.SignedOrdinalLimit

/-! No birth, whole enumeration or extension is supplied from the future. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalHistoryLimit

open SignedProperLimit SignedBirthEnumeration SignedOrdinalSuccessor
open SignedOrdinalHistoryEvent SignedOrdinalHistoryBirth SignedOrdinalHistoryState
open SignedOrdinalHistoryPast
open D5.S3.Topology.Measures

local instance carrierMeasurable {b : Ordinal.{0}} (C : Set (Cube b)) :
    MeasurableSpace C := borel C
local instance carrierBorel {b : Ordinal.{0}} (C : Set (Cube b)) :
    BorelSpace C := ⟨rfl⟩

variable (a : Stage) (past : ∀ b : Stage, b < a → State b)
  (coherent : ∀ b c hb hc hbc, Coherent hbc (past b hb) (past c hc))
  (hw : ω < ord a) (hl : Order.IsSuccLimit (ord a))

/-- Every entry is the one selected result at its unique outgoing birth index.
At this proper limit its arrival is strictly earlier than the new stage. -/
private noncomputable def strictBirths : PastBirths (ord a) := fun b r d hr hm =>
  let B : Stage := ⟨⟨b.1, b.2.trans a.1.2⟩,
    hr.trans ((le_max_left r d).trans hm.le)⟩
  let before : Order.succ (ord B) < ord a := hl.succ_lt b.2
  (past B ((Order.lt_succ (ord B)).trans before)).event.result.N
    ⟨r, hr, (le_max_left r d).trans hm.le⟩
    ⟨d, (le_max_right r d).trans hm.le⟩

/-- The archive consists solely of exact canonical Q/R readouts of this past. -/
noncomputable def archive : SignedOrdinalLimit.Archive
    (strictPrefix a.1.2 past coherent) hw where
  proper := a.1.2
  base_onto := by
    intro y
    refine ⟨⟨y, ?_⟩, rfl⟩
    change y ∈ pastCarrier a.1.2 past ⟨ω, hw⟩
    simp only [pastCarrier, dite_eq_left (le_refl (ω : Ordinal.{0}))]
    rw [(past initialStage hw).initial_carriers (top ω) le_rfl]
    exact mem_univ y
  pastBirths := strictBirths a past hl
  U := fun r => (bornPack a.1.2 past coherent r.1 r.2).U
  Uonto := fun r => (bornPack a.1.2 past coherent r.1 r.2).Uonto
  V := fun r => (bornPack a.1.2 past coherent r.1 r.2).V
  nu := fun r => (bornPack a.1.2 past coherent r.1 r.2).nu
  nuonto := fun r => (bornPack a.1.2 past coherent r.1 r.2).nuonto
  I := (strictData a.1.2 past coherent hl).I
  J := (strictData a.1.2 past coherent hl).J

private theorem archive_data : (archive a past coherent hw hl).data =
    strictData a.1.2 past coherent hl := by
  classical
  rfl

private theorem archive_laws : (strictPrefix a.1.2 past coherent).Laws
    (archive a past coherent hw hl).data := by
  rw [archive_data]
  exact strictLaws a.1.2 past coherent hl

/-- Execute the actual approved constructor once, retaining its full Extension. -/
noncomputable def result : SignedOrdinalLimit.Result (archive a past coherent hw hl) :=
  SignedOrdinalLimit.construct (archive a past coherent hw hl) hl
    (archive_laws a past coherent hw hl)

variable {a past coherent hw hl}
  (R : SignedOrdinalLimit.Result (archive a past coherent hw hl))

private noncomputable def oldPack (r : Rows (ord a)) (hr : r ≠ newRow (ord a) a.2) :
    BirthPack (R.extended.carrier (rowIndex r)) :=
  BirthPack.cast (R.old_carrier (SignedOrdinalLimit.bornRow hw r hr).1).symm
    (bornPack a.1.2 past coherent (SignedOrdinalLimit.bornRow hw r hr).1 r.2.1)

private noncomputable def oldB : OldClopens R.extended a.2 := fun r hr => (oldPack R r hr).B

private theorem oldPack_readback (r : Rows (ord a)) (hr : r ≠ newRow (ord a) a.2) :
    predecessorPack (P := R.predecessor) (oldB R)
      (fun r hr => (oldPack R r hr).Bonto) r hr = oldPack R r hr := by
  have h := (archive a past coherent hw hl).predecessor_whole_readback R.extension r hr
  apply (BirthPack.eq_cast (R.old_carrier (SignedOrdinalLimit.bornRow hw r hr).1).symm
    (bornPack a.1.2 past coherent (SignedOrdinalLimit.bornRow hw r hr).1 r.2.1)
    (predecessorPack (P := R.predecessor) (oldB R)
      (fun r hr => (oldPack R r hr).Bonto) r hr) ?_ ?_ ?_ ?_).symm
  · exact h.1.symm
  · exact (BirthPack.cast_B_heq _ _).symm
  · exact h.2.1.symm
  · exact h.2.2.symm

private theorem extension_regular_f {l : Ordinal.{0}} {H : Prefix l} {hw : ω < l}
    (A : SignedOrdinalLimit.Archive H hw) (E : H.Extension A.data)
    (r : SignedOrdinalLimit.BornRows l) (d : Coord l)
    {C : Set (Cube l)} {B : Set (Cube r.1.1)} [CompactSpace C]
    (hC : C = H.limitCarrier) (hB : B = H.carrier r.1)
    (nu : ℕ → SignedMeasure B)
    (hnu : ∀ n, HEq (nu n) (((A.nu r ⟨d.1, d.2.trans A.proper⟩).1 n).1))
    (p : C(C, B)) (hp : ∀ x, (p x).1 = restrict r.1.2.le x.1)
    (s : ℕ → RegularSigned C) (hm : ∀ n, (s n).1.map p = nu n)
    (hn : ∀ n, (s n).1.totalVariation univ = 1) :
    ∃ mu : RegularSigned C, mu.1.totalVariation.real univ ≤ 1 ∧ Tendsto
      (fun n => (NormPreservingLifts.signedFunctional (s n).1).toWeakDual)
      (along (E.J r.1 d)) (𝓝 (NormPreservingLifts.signedFunctional mu.1).toWeakDual) := by
  subst C
  subst B
  have hmap : p = H.projection r.1 := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (hp x)
  apply E.F r.1 d r.2 s
  intro n
  refine ⟨hn n, ?_⟩
  have hm' : (s n).1.map (H.projection r.1) =
      ((A.nu r ⟨d.1, d.2.trans A.proper⟩).1 n).1 :=
    (by simpa only [hmap] using hm n).trans (eq_of_heq (hnu n))
  simpa only [Prefix.NewClass, SignedOrdinalLimit.Archive.data, dite_eq_left r.2] using hm'

private theorem regular : RegularCurrent R.extended a.2 R.predecessor := by
  intro r hr d s hm hn
  have hpack : HEq (predecessorPack (P := R.predecessor) (oldB R)
      (fun r hr => (oldPack R r hr).Bonto) r hr)
      (bornPack a.1.2 past coherent (SignedOrdinalLimit.bornRow hw r hr).1 r.2.1) :=
    (heq_of_eq (oldPack_readback R r hr)).trans (BirthPack.cast_heq _ _)
  have hnu := fun n => BirthPack.heq_measure
    (R.old_carrier (SignedOrdinalLimit.bornRow hw r hr).1) _ _ hpack
      ⟨d.1, d.2.trans a.1.2⟩ n
  have hf := extension_regular_f (archive a past coherent hw hl) R.extension
    (SignedOrdinalLimit.bornRow hw r hr) d R.top_carrier
    (R.old_carrier (SignedOrdinalLimit.bornRow hw r hr).1)
    (fun n => ((R.predecessor.nu r hr ⟨d.1, d.2.trans a.1.2⟩).1 n).1) hnu
    (projection R.extended r) (fun _ => rfl) s hm hn
  simpa only [R.J_eq] using hf

variable (hCH : Cardinal.continuum.{0} = ℵ₁)

/-- The actual limit state retains this same R.extension, then prepares and
executes one actual outgoing event on its new predecessor. -/
noncomputable def limitState : State a where
  H := R.extended
  P := R.predecessor
  initial_carriers := by
    intro c hc
    have hcl : c.1 < ord a := hc.trans_lt hw
    refine (R.old_carrier ⟨c.1, hcl⟩).trans ?_
    change pastCarrier a.1.2 past ⟨c.1, hcl⟩ = univ
    classical
    by_cases hω : ω ≤ c.1
    · simp only [pastCarrier, dite_eq_left hω]
      exact (past ⟨⟨c.1, hcl.trans a.1.2⟩, hω⟩ hcl).initial_carriers (top c.1) hc
    · simp only [pastCarrier, dite_eq_right hω]
  incoming := .limit a.2 hl (strictPrefix a.1.2 past coherent)
    (archive a past coherent hw hl).data (archive_laws a past coherent hw hl)
    R.extension R.extended R.predecessor R.top_carrier R.old_carrier R.I_eq R.J_eq
  regular := regular R
  event := execute R.extended a.2 R.predecessor
    (scheduledLaunch R.extended a.2 R.predecessor) (oldB R) hCH
  oldBonto := fun r hr => (oldPack R r hr).Bonto

theorem limit_coherent (b : Stage) (hb : b < a) :
    Coherent hb (past b hb) (limitState R hCH) where
  carrier := fun c => (R.old_carrier
    ⟨c.1, (Order.le_of_lt_succ c.2).trans_lt hb⟩).trans
      (carrier_read a.1.2 past coherent b hb c)
  birth := by
    change predecessorPack (P := R.predecessor) (oldB R) _ _ _ = _
    rw [oldPack_readback]
    change BirthPack.cast _ (BirthPack.cast _ (past b hb).birth) = _
    exact BirthPack.cast_cast _ _ _
  arrival := by
    intro r d hr hm e
    change (strictBirths a past hl) ⟨ord b, hb⟩ r d hr hm e = _
    rfl
  DI := by
    intro r hr
    have hrc : r.1 < ord b := lt_of_le_of_ne r.2.2 (fun he => hr (Subtype.ext he))
    have hd := R.extension.DI ⟨r.1, r.2.2.trans_lt hb⟩ ⟨ord b, hb⟩ r.2.1 hrc
    rw [archive_data, I_read] at hd
    simpa only [limitState, R.I_eq, SignedOrdinalLimit.bornRow, oldRow] using hd
  DJ := by
    intro r hr d
    have hrc : r.1 < ord b := lt_of_le_of_ne r.2.2 (fun he => hr (Subtype.ext he))
    have hd := R.extension.DJ ⟨r.1, r.2.2.trans_lt hb⟩
      ⟨d.1, d.2.trans hb⟩ ⟨ord b, hb⟩ r.2.1 hrc d.2
    rw [archive_data, J_read] at hd
    simpa only [limitState, R.J_eq, SignedOrdinalLimit.bornRow, oldRow] using hd

end D5.S3.Topology.InverseLimit.SignedOrdinalHistoryLimit
