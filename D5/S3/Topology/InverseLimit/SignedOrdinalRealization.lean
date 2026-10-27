/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalRealization
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalRealization
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Literal omega-one realization and every proper slice of the same executed run. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalHistory
import D5.S3.Topology.InverseLimit.SignedBallHistoryCapture

/-! The final cube reads a single completed run; only proper slices have Data. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory TopologicalSpace
open scoped Ordinal Cardinal Topology ENNReal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalRealization

open SignedProperLimit SignedBirthEnumeration SignedOrdinalSuccessor
open SignedOrdinalHistoryEvent SignedOrdinalHistoryBirth SignedOrdinalHistoryState
open SignedOrdinalHistorySuccessor
open D5.S3.Topology.Measures

variable (hCH : Cardinal.continuum.{0} = ℵ₁)

/-- All carriers are read from the one fixed well-founded run. -/
noncomputable def finalPrefix : Prefix (ω₁ : Ordinal.{0}) :=
  SignedOrdinalHistoryPast.strictPrefix le_rfl
    (fun b _ => SignedOrdinalHistory.run hCH b)
    (fun b c _ _ hbc => SignedOrdinalHistory.coherent hCH b c hbc)

/-- The post-run proper slice has the same literal carriers and restrictions. -/
noncomputable def properSlice {l : Ordinal.{0}} (hl : l < ω₁) : Prefix l where
  carrier := fun c => (finalPrefix hCH).carrier ⟨c.1, c.2.trans hl⟩
  closed := fun c => (finalPrefix hCH).closed ⟨c.1, c.2.trans hl⟩
  nonempty := fun c => (finalPrefix hCH).nonempty ⟨c.1, c.2.trans hl⟩
  compatible := fun a b h x => (finalPrefix hCH).compatible
    ⟨a.1, a.2.trans hl⟩ ⟨b.1, b.2.trans hl⟩ h x
  onto := fun a b h y => (finalPrefix hCH).onto
    ⟨a.1, a.2.trans hl⟩ ⟨b.1, b.2.trans hl⟩ h y

/-- Every proper cutoff includes the actual whole birth at its last row. -/
noncomputable def properData {l : Ordinal.{0}} (hl : l < ω₁) :
    (properSlice hCH hl).Data :=
  SignedOrdinalHistoryPast.postData hl
    (fun b _ => SignedOrdinalHistory.run hCH b)
    (fun b c _ _ hbc => SignedOrdinalHistory.coherent hCH b c hbc)

theorem properLaws {l : Ordinal.{0}} (hl : l < ω₁) :
    (properSlice hCH hl).Laws (properData hCH hl) :=
  SignedOrdinalHistoryPast.postLaws hl
    (fun b _ => SignedOrdinalHistory.run hCH b)
    (fun b c _ _ hbc => SignedOrdinalHistory.coherent hCH b c hbc)

theorem slice_carrier {l : Ordinal.{0}} (hl : l < ω₁) (c : Coord l) :
    (properSlice hCH hl).carrier c =
      (finalPrefix hCH).carrier ⟨c.1, c.2.trans hl⟩ := rfl

/-- The final carrier at every proper stage is literally the actual run carrier. -/
theorem carrier_read (b : Stage) (c : Coord (Order.succ (ord b))) :
    (finalPrefix hCH).carrier
      ⟨c.1, (show c.1 ≤ ord b from Order.le_of_lt_succ c.2).trans_lt
        (show ord b < ω₁ from b.1.2)⟩ =
      (SignedOrdinalHistory.run hCH b).H.carrier c :=
  SignedOrdinalHistoryPast.carrier_read le_rfl
    (fun b _ => SignedOrdinalHistory.run hCH b)
    (fun b c _ _ hbc => SignedOrdinalHistory.coherent hCH b c hbc) b b.1.2 c

theorem top_read (b : Stage) :
    (finalPrefix hCH).carrier b.1 =
      (SignedOrdinalHistory.run hCH b).H.carrier (top (ord b)) :=
  carrier_read hCH b (top (ord b))

theorem initial_carrier (c : Label) (hc : c.1 ≤ ω) :
    (finalPrefix hCH).carrier c = univ := by
  exact (carrier_read hCH initialStage
    ⟨c.1, hc.trans_lt (Order.lt_succ ω)⟩).trans
      ((SignedOrdinalHistory.run hCH initialStage).initial_carriers _ hc)

/-- The whole Q at theta is transported only by equality of literal carriers. -/
noncomputable def wholeBirth (θ : Stage) : BirthPack ((finalPrefix hCH).carrier θ.1) :=
  BirthPack.cast (top_read hCH θ).symm (SignedOrdinalHistory.run hCH θ).birth

theorem wholeBirth_read (θ : Stage) :
    HEq (wholeBirth hCH θ) (SignedOrdinalHistory.run hCH θ).birth :=
  BirthPack.cast_heq _ _

theorem whole_measure (θ : Stage) (d : Label) (n : ℕ) :
    HEq ((wholeBirth hCH θ).measure d n)
      ((SignedOrdinalHistory.run hCH θ).birth.measure d n) :=
  BirthPack.heq_measure (top_read hCH θ) _ _ (wholeBirth_read hCH θ) d n

/-- Slice whole measures retain the original labels, even beyond the cutoff. -/
theorem slice_nu {l : Ordinal.{0}} (hl : l < ω₁) (r : Coord l)
    (hr : ω ≤ r.1) (d : Label) (n : ℕ) :
    ((properData hCH hl).nu r d n).1 =
      (wholeBirth hCH ⟨⟨r.1, r.2.trans hl⟩, hr⟩).measure d n := by
  classical
  simp only [properData, SignedOrdinalHistoryPast.postData, dite_eq_left hr]
  rfl

theorem slice_J {l : Ordinal.{0}} (hl : l < ω₁) (b : Stage) (hb : ord b < l)
    (r : Rows (ord b)) (hr : r ≠ newRow (ord b) b.2) (d : Coord (ord b)) :
    (properData hCH hl).J ⟨r.1, r.2.2.trans_lt hb⟩
      ⟨d.1, d.2.trans hb⟩ ⟨ord b, hb⟩ =
      (SignedOrdinalHistory.run hCH b).P.J r hr d :=
  SignedOrdinalHistoryPast.postJ_read hl
    (fun b _ => SignedOrdinalHistory.run hCH b)
    (fun b c _ _ hbc => SignedOrdinalHistory.coherent hCH b c hbc) b hb r hr d

/-- The outgoing R at a is the incoming literal carrier at succ(a). -/
theorem successor_carrier (a : Stage) :
    (finalPrefix hCH).carrier (nextStage a).1 =
      (SignedOrdinalHistory.run hCH a).event.result.coordinates.carrier := by
  rw [top_read, SignedOrdinalHistory.successor_execution]
  exact (SignedOrdinalHistory.run hCH a).event.result.coordinates.top_carrier

noncomputable def successorHomeomorph (a : Stage) :
    (finalPrefix hCH).Space (nextStage a).1 ≃ₜ
      (SignedOrdinalHistory.run hCH a).event.result.coordinates.carrier :=
  Homeomorph.setCongr (successor_carrier hCH a)

/-- Final projections and every old row use the identical restriction map. -/
theorem projection_factor (b c : Label) (h : b ≤ c) :
    ((finalPrefix hCH).map b c h).comp ((finalPrefix hCH).projection c) =
      (finalPrefix hCH).projection b := by
  ext x i
  rfl

/-- The initial countable Boolean cube remains an onto image of this same final cube. -/
theorem initial_onto : Surjective
    (fun x : (finalPrefix hCH).LimitSpace => restrict
      (show (ω : Ordinal.{0}) ≤ ω₁ from Ordinal.omega0_lt_omega_one.le) x.1) := by
  intro y
  let w : (finalPrefix hCH).Space initialStage.1 :=
    ⟨y, by
      change y ∈ (finalPrefix hCH).carrier initialStage.1
      rw [initial_carrier hCH initialStage.1 le_rfl]
      exact mem_univ y⟩
  obtain ⟨x, hx⟩ := (finalPrefix hCH).projection_surjective
    (Cardinal.isSuccLimit_omega 1) initialStage.1 w
  exact ⟨x, congrArg Subtype.val hx⟩

/-- Each permanent reservoir is the original R at the unique outgoing maximum. -/
noncomputable def reservoir (θ : Stage) (d : Label) (e : Bool) : Set ℕ :=
  let m : Stage := ⟨max θ.1 d, θ.2.trans (le_max_left (ord θ) d.1)⟩
  (SignedOrdinalHistory.run hCH m).event.result.N
    ⟨ord θ, θ.2, le_max_left _ _⟩ ⟨d.1, le_max_right _ _⟩ (if e then 1 else 0)

theorem slice_N {l : Ordinal.{0}} (hl : l < ω₁) (r d : Coord l)
    (hr : ω ≤ r.1) (e : Bool) :
    (properData hCH hl).N r d e =
      reservoir hCH ⟨⟨r.1, r.2.trans hl⟩, hr⟩ ⟨d.1, d.2.trans hl⟩ e := by
  classical
  change (if h : ω ≤ r.1 then _ else ∅) = _
  rw [dite_eq_left hr]
  rfl

/-- At each eligible carrier the permanent N equals the actual incoming N. -/
theorem reservoir_incoming (θ : Stage) (d : Label) (c : Stage)
    (hθ : θ < c) (hd : d.1 < ord c) (e : Bool) :
    reservoir hCH θ d e =
      (SignedOrdinalHistory.run hCH c).P.oldN
        (oldRow hθ (newRow (ord θ) θ.2)) (oldRow_ne hθ _)
        ⟨d.1, hd⟩ (if e then 1 else 0) := by
  let m : Stage := ⟨max θ.1 d, θ.2.trans (le_max_left (ord θ) d.1)⟩
  have hm : m < c := max_lt (show ord θ < ord c from hθ) hd
  exact ((SignedOrdinalHistory.coherent hCH m c hm).arrival
    (ord θ) d.1 θ.2 rfl (if e then 1 else 0)).symm

/-- Original eligible J is read from the incoming predecessor at the carrier. -/
noncomputable def historicalJ (θ : Stage) (d : Label)
    (c : SignedBallHistoryCapture.Eligible θ d) : Set ℕ :=
  let C : Stage := ⟨c.1, θ.2.trans ((le_max_left (ord θ) d.1).trans c.2.le)⟩
  let hθ : θ < C := (le_max_left (ord θ) d.1).trans_lt c.2
  (SignedOrdinalHistory.run hCH C).P.J
    (oldRow hθ (newRow (ord θ) θ.2)) (oldRow_ne hθ _)
    ⟨d.1, (le_max_right (ord θ) d.1).trans_lt c.2⟩

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

/-- The launch row is the actual outgoing a, while its archive time is succ(a). -/
theorem launch (θ : Stage) (i base : Label) :
    ∃ (a : Stage) (hθ : θ < a), base < a.1 ∧
      ∀ n, (wholeBirth hCH a).V.clopen n =
        ⟨(finalPrefix hCH).map θ.1 a.1 hθ.le ⁻¹'
            (((wholeBirth hCH θ).U i).clopen n : Set _),
          (((wholeBirth hCH θ).U i).clopen n).isClopen.preimage
            ((finalPrefix hCH).map θ.1 a.1 hθ.le).continuous⟩ := by
  obtain ⟨a, hθ, hb, _, hv⟩ := SignedOrdinalHistory.launch_cofinal hCH θ i base
  refine ⟨a, hθ, hb, ?_⟩
  intro n
  apply SetLike.coe_injective
  ext x
  change (x ∈ (wholeBirth hCH a).V.clopen n) ↔
    (finalPrefix hCH).map θ.1 a.1 hθ.le x ∈ ((wholeBirth hCH θ).U i).clopen n
  unfold wholeBirth
  rw [cast_V_mem, cast_U_mem]
  have hx := congrArg (fun S : Set (K (SignedOrdinalHistory.run hCH a).H) =>
    Homeomorph.setCongr (top_read hCH a) x ∈ S) (hv n)
  exact eq_iff_iff.mp hx

end D5.S3.Topology.InverseLimit.SignedOrdinalRealization
