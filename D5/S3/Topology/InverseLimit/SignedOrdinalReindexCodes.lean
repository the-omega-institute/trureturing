/- GID: D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SignedOrdinalReindexCodes
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Birth-local injective first-reservation codes and cofinal hole colors. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalHistory

/-! First valid reservation codes use only one original whole birth. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function
open scoped Ordinal Cardinal

namespace D5.S3.Topology.InverseLimit.SignedOrdinalReindexCodes

open SignedProperLimit SignedBirthEnumeration SignedOrdinalHistoryBirth
open SignedOrdinalHistoryState SignedOrdinalHistoryTask CofinalTaskSchedule

/-- The distinguished original ordinary label. -/
def zeroLabel : Label := ⟨0, Ordinal.omega0_pos.trans Ordinal.omega0_lt_omega_one⟩

variable {θ : Stage} {C : Set (Cube (ord θ))} (W : BirthPack C)

/-- Delayed tags contain precisely an intrinsic test on this single birth. -/
abbrev Tag := Label ⊕ {p : Label × Label × ℕ // Intrinsic W p.1 p.2.1 p.2.2}

def zeroTag : Tag W := .inl zeroLabel

def taskSyntax (z : Tag W) : Task :=
  match z with
  | .inl d => .inl (θ.1, d)
  | .inr p => .inr (θ.1, p.1.1, p.1.2.1, p.1.2.2)

/-- The original measure label, including the delayed target rather than source. -/
def target (z : Tag W) : Label :=
  match z with
  | .inl d => d
  | .inr p => p.1.2.1

def ValidAt (z : Tag W) (a : Label) : Prop :=
  match z with
  | .inl d => OrdinaryValid a θ.1 d
  | .inr p => DelayedValid a θ.1 p.1.1 p.1.2.1

def Occurs (z : Tag W) (a : Label) : Prop :=
  (reservation a).1 = taskSyntax W z ∧ ValidAt W z a

theorem taskSyntax_injective : Injective (taskSyntax W) := by
  intro x y h
  cases x with
  | inl d =>
    cases y with
    | inl e => exact congrArg Sum.inl (Prod.mk.inj (Sum.inl.inj h)).2
    | inr q => cases h
  | inr p =>
    cases y with
    | inl e => cases h
    | inr q =>
      apply congrArg Sum.inr
      apply Subtype.ext
      exact (Prod.mk.inj (Sum.inr.inj h)).2

/-- Every intrinsic tag has syntactically valid occurrences above any bound. -/
theorem occurs_cofinal (z : Tag W) (base : Label) :
    ∃ a : Label, base < a ∧ Occurs W z a := by
  cases z with
  | inl d =>
    obtain ⟨a, hb, hv, he, _⟩ :=
      CofinalTaskSchedule.ordinary_cofinal θ.1 d base θ.2 (fun _ _ _ _ => False)
    exact ⟨a, hb, he, hv⟩
  | inr p =>
    obtain ⟨a, hb, hv, he, _⟩ := CofinalTaskSchedule.delayed_cofinal
      θ.1 p.1.1 p.1.2.1 base p.1.2.2 θ.2 (fun _ _ _ _ => True) trivial
    exact ⟨a, hb, he, hv⟩

private theorem occurs_nonempty (z : Tag W) : {a | Occurs W z a}.Nonempty := by
  obtain ⟨a, _, ha⟩ := occurs_cofinal W z zeroLabel
  exact ⟨a, ha⟩

private noncomputable def first (z : Tag W) : Label :=
  wellFounded_lt.min {a | Occurs W z a} (occurs_nonempty W z)

private theorem first_occurs (z : Tag W) : Occurs W z (first W z) :=
  (wellFounded_lt : WellFounded ((· < ·) : Label → Label → Prop)).min_mem
    {a | Occurs W z a} (occurs_nonempty W z)

/-- Ordinary zero stays zero; all other tags use their first valid reservation. -/
noncomputable def code (z : Tag W) : Label := by
  classical
  exact if z = zeroTag W then zeroLabel else first W z

theorem code_zero : code W (zeroTag W) = zeroLabel := by
  classical
  simp [code]

theorem code_occurs (z : Tag W) (hz : z ≠ zeroTag W) : Occurs W z (code W z) := by
  classical
  simpa only [code, ite_eq_right hz] using first_occurs W z

theorem row_le_code (z : Tag W) (hz : z ≠ zeroTag W) : θ.1 ≤ code W z := by
  have hv := (code_occurs W z hz).2
  cases z with
  | inl d => exact hv.2.1
  | inr p => exact hv.2.1.le

theorem target_le_code (z : Tag W) : target W z ≤ code W z := by
  classical
  by_cases hz : z = zeroTag W
  · subst z
    rw [code_zero]
    exact le_rfl
  · have hv := (code_occurs W z hz).2
    cases z with
    | inl d => exact hv.2.2
    | inr p => exact hv.2.2.2.le

theorem code_le_occurrence (z : Tag W) (a : Label) (ha : Occurs W z a) :
    code W z ≤ a := by
  classical
  by_cases hz : z = zeroTag W
  · subst z
    rw [code_zero]
    exact show (0 : Ordinal.{0}) ≤ a.1 from bot_le
  · rw [code, ite_eq_right hz]
    exact le_of_not_gt
      ((wellFounded_lt : WellFounded ((· < ·) : Label → Label → Prop)).not_lt_min
        {b | Occurs W z b} ha)

theorem code_eq_zero_iff (z : Tag W) : code W z = zeroLabel ↔ z = zeroTag W := by
  constructor
  · intro he
    by_contra hz
    have hh := θ.2.trans (row_le_code W z hz)
    rw [he] at hh
    exact (not_le_of_gt Ordinal.omega0_pos) hh
  · rintro rfl
    exact code_zero W

/-- A reservation has one syntax, so distinct nonzero tags cannot share a code. -/
theorem code_injective : Injective (code W) := by
  intro x y he
  by_cases hx : x = zeroTag W
  · subst x
    have hy : code W y = zeroLabel := he.symm.trans (code_zero W)
    exact ((code_eq_zero_iff W y).mp hy).symm
  · have hy : y ≠ zeroTag W := by
      intro hy
      subst y
      exact hx ((code_eq_zero_iff W x).mp (he.trans (code_zero W)))
    apply taskSyntax_injective W
    exact (code_occurs W x hx).1.symm.trans
      ((congrArg (fun a => (reservation a).1) he).trans (code_occurs W y hy).1)

/-- Two prescribed successive reservation fibers are simultaneously cofinal. -/
theorem double_reservation_cofinal (outer inner : Task) (base : Label) :
    ∃ a : Label, base < a ∧ (reservation a).1 = outer ∧
      (reservation (reservation a).2).1 = inner := by
  classical
  let g : Label → Label := fun ξ =>
    reservation.symm (outer, reservation.symm (inner, ξ))
  have hg : Injective g := by
    intro x y h
    have hi := (Prod.mk.inj (reservation.symm.injective h)).2
    exact (Prod.mk.inj (reservation.symm.injective hi)).2
  by_contra h
  have hb : ∀ ξ : Label, (g ξ).1 ≤ base.1 := by
    intro ξ
    by_contra hh
    apply h
    exact ⟨g ξ, lt_of_not_ge hh, by simp [g], by simp [g]⟩
  let f : Label → Set.Iio (Order.succ base.1) := fun ξ =>
    ⟨(g ξ).1, (Order.lt_succ_iff).mpr (hb ξ)⟩
  have hf : Injective f := fun x y hxy =>
    hg (Subtype.ext (congrArg (fun z : Set.Iio (Order.succ base.1) => z.1) hxy))
  let : Countable (Set.Iio (Order.succ base.1)) :=
    (Cardinal.countable_Iio_of_lt_omega_one
      ((Cardinal.isSuccLimit_omega 1).succ_lt base.2)).to_subtype
  let : Countable Label := hf.countable
  have hh := Cardinal.mk_le_aleph0 (α := Label)
  have hc : Cardinal.mk Label = ℵ₁ := by
    simp [Label, Cardinal.mk_Iio_ordinal, Ordinal.card_omega]
  rw [hc] at hh
  exact (not_le_of_gt Cardinal.aleph0_lt_aleph_one) hh

/-- A second reservation supplies a color independently of all birth data. -/
noncomputable def color (a : Label) : Label :=
  match (reservation (reservation a).2).1 with
  | .inl (_, d) => d
  | .inr _ => zeroLabel

def Hole (δ : Label) : Prop := δ ∉ Set.range (code W)

/-- Only ordinary-zero occurrences can carry colors outside the code image. -/
noncomputable def ordinaryIndex (d a : Label) : Label := by
  classical
  exact if d = zeroLabel then
    if color a ≤ a ∧ (color a = zeroLabel ∨ Hole W (color a)) then color a else zeroLabel
  else code W (.inl d)

theorem ordinaryIndex_le (d a : Label) (ha : Occurs W (.inl d) a) :
    ordinaryIndex W d a ≤ a := by
  classical
  unfold ordinaryIndex
  split_ifs with hd hc
  · exact hc.1
  · exact show (0 : Ordinal.{0}) ≤ a.1 from bot_le
  · exact code_le_occurrence W (.inl d) a ha

/-- Every hole, as well as zero, colors cofinally many valid ordinary-zero stages. -/
theorem hole_cofinal (δ base : Label) (hδ : δ = zeroLabel ∨ Hole W δ) :
    ∃ a : Label, base < a ∧ θ.1 < a ∧ δ < a ∧
      Occurs W (zeroTag W) a ∧ ordinaryIndex W zeroLabel a = δ := by
  classical
  obtain ⟨a, hb, ho, hi⟩ := double_reservation_cofinal
    (.inl (θ.1, zeroLabel)) (.inl (fallback.1, δ)) (max base (max θ.1 δ))
  have hθ : θ.1 < a :=
    ((le_max_left θ.1 δ).trans (le_max_right base _)).trans_lt hb
  have hd : δ < a :=
    ((le_max_right θ.1 δ).trans (le_max_right base _)).trans_lt hb
  have hcolor : color a = δ := by simp [color, hi]
  refine ⟨a, (le_max_left base _).trans_lt hb, hθ, hd,
    ⟨ho, θ.2, hθ.le, show (0 : Ordinal.{0}) ≤ a.1 from bot_le⟩, ?_⟩
  simp [ordinaryIndex, hcolor, hd.le, hδ]

end D5.S3.Topology.InverseLimit.SignedOrdinalReindexCodes
