/- GID: D5/S3/Combinatorics/CayleySumCodes/DihedralCentralConstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/DihedralCentralConstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full inverse-closed-transversal central-half-turn dihedral construction. -/

import D5.S3.Combinatorics.CayleySumCodes.DihedralConstructions
import D5.S3.Combinatorics.CayleySumCodes.PerfectCodeTransversal

/-!
Jun-Yang Zhang, arXiv:2210.03336v1, Example 5.8. These are the retained
constructions, with arbitrary inverse-closed transversals; no exhaustive
classification is asserted. The half-turn and parity hypotheses are proved
for the source's entire n = 4k+2, k>=1 domain by the current
transient exact application checks.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.DihedralCentralConstruction

open DihedralGroup
open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

variable {n : ℕ}

/-- The actual order-two subgroup in the rotation coordinates. -/
def halfAdd (h : ZMod n) (hh : h + h = 0) : AddSubgroup (ZMod n) where
  carrier := {i | i = 0 ∨ i = h}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro i j (rfl | rfl) (rfl | rfl) <;> simp [hh]
  neg_mem' := by
    rintro i (rfl | rfl)
    · exact Or.inl neg_zero
    · right; exact neg_eq_iff_add_eq_zero.mpr hh

/-- The same subgroup as actual dihedral group elements. -/
def halfGroup (h : ZMod n) (hh : h + h = 0) : Subgroup (DihedralGroup n) where
  carrier := {g | g = 1 ∨ g = r h}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> simp [r_mul_r, hh]
  inv_mem' := by
    rintro a (rfl | rfl)
    · exact Or.inl inv_one
    · right; rw [inv_r, neg_eq_iff_add_eq_zero.mpr hh]

private theorem transversal_pair (h : ZMod n) (hh : h + h = 0) (hn : h ≠ 0)
    (Z : Set (ZMod n)) (hz : AddSubgroup.IsComplement Z (halfAdd h hh))
    (i : ZMod n) : i ∈ Z ↔ i + h ∉ Z := by
  have nh : -h = h := neg_eq_iff_add_eq_zero.mpr hh
  have comp := AddSubgroup.isComplement_iff_existsUnique_neg_add_mem.mp hz
  constructor
  · intro hi hih
    obtain ⟨z, _, hu⟩ := comp i
    have h1 : -i + i ∈ halfAdd h hh := Or.inl (neg_add_cancel i)
    have h2 : -(i + h) + i ∈ halfAdd h hh := Or.inr (by rw [neg_add]; simp [nh])
    have he := congrArg Subtype.val ((hu ⟨i, hi⟩ h1).trans (hu ⟨i+h, hih⟩ h2).symm)
    apply hn
    change i = i + h at he
    linear_combination -he
  · intro hi
    obtain ⟨z, hzH, _⟩ := comp i
    rcases hzH with hzH | hzH
    · have he : (z : ZMod n) = i := by linear_combination -hzH
      exact he ▸ z.2
    · have he : (z : ZMod n) = i + h := by rw [← nh]; linear_combination -hzH
      exact (hi (he ▸ z.2)).elim

/-- Remove the old internal representative, then insert the half-turn. -/
def selected (h : ZMod n) (Z : Set (ZMod n)) : Set (ZMod n) :=
  {i | (i ∈ Z ∧ i ≠ 0 ∧ i ≠ h) ∨ i = h}

private theorem selected_pair (h : ZMod n) (hh : h + h = 0) (hn : h ≠ 0)
    (Z : Set (ZMod n)) (hz : AddSubgroup.IsComplement Z (halfAdd h hh))
    (i : ZMod n) : i ∈ selected h Z ↔ i+h ∉ selected h Z := by
  by_cases hi0 : i = 0
  · subst i; simp [selected, hn, Ne.symm hn]
  by_cases hih : i = h
  · subst i; simp [selected, hh, hn, Ne.symm hn]
  have hs0 : i+h ≠ 0 := by intro he; apply hih; linear_combination he - hh
  have hsh : i+h ≠ h := by simpa using hi0
  simpa [selected, hi0, hih, hs0, hsh] using transversal_pair h hh hn Z hz i

/-- The exact total-code connection: a reflection class, the transversal
rotations outside the half-turn subgroup, and the central half-turn. -/
def connection (h : ZMod n) (Z : Set (ZMod n)) (e : ZMod n →+ ZMod 2)
    (c : ZMod 2) : Set (DihedralGroup n)
  | r i => i ∈ selected h Z
  | sr i => e i = c

@[simp] private theorem mem_connection_r (h : ZMod n) (Z : Set (ZMod n))
    (e : ZMod n →+ ZMod 2) (c : ZMod 2) (i : ZMod n) :
    r i ∈ connection h Z e c ↔ i ∈ selected h Z := Iff.rfl

@[simp] private theorem mem_connection_sr (h : ZMod n) (Z : Set (ZMod n))
    (e : ZMod n →+ ZMod 2) (c : ZMod 2) (i : ZMod n) :
    sr i ∈ connection h Z e c ↔ e i = c := Iff.rfl

private theorem neg_two (x : ZMod 2) : -x = x := ZMod.neg_eq_self_mod_two x

theorem connection_normal (h : ZMod n) (hh : h+h = 0)
    (Z : Set (ZMod n)) (hz : ∀ i ∈ Z, -i ∈ Z)
    (e : ZMod n →+ ZMod 2) (c : ZMod 2) :
    NormalSubset (connection h Z e c) := by
  have nh : -h = h := neg_eq_iff_add_eq_zero.mpr hh
  have negsel (i : ZMod n) (hi : i ∈ selected h Z) : -i ∈ selected h Z := by
    rcases hi with ⟨hi, hi0, hih⟩ | rfl
    · left
      refine ⟨hz i hi, neg_ne_zero.mpr hi0, ?_⟩
      intro he
      apply hih
      simpa [nh] using congrArg Neg.neg he
    · exact Or.inr nh
  rintro (i | i) (j | j) hj <;>
    simp only [inv_r, inv_sr, r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr,
      mem_connection_r, mem_connection_sr, map_add, map_sub, map_neg] at *
  · simpa using hj
  · simpa only [sub_eq_add_neg, neg_two, CharTwo.add_cancel_right] using hj
  · simpa using negsel j hj
  · simp only [sub_eq_add_neg, neg_two]
    rw [add_comm (e j) (e i), CharTwo.add_cancel_left]
    exact hj

/-- Every original inverse-closed transversal works, including either
choice of its internal representative. Both reflection classes are allowed. -/
theorem total (h : ZMod n) (hh : h+h = 0) (hn : h ≠ 0)
    (Z : Set (ZMod n)) (hz : AddSubgroup.IsComplement Z (halfAdd h hh))
    (hzneg : ∀ i ∈ Z, -i ∈ Z) (e : ZMod n →+ ZMod 2)
    (he : e h = 1) (c : ZMod 2) :
    IsTotalPerfectCode
      (sumGraph (connection h Z e c) (connection_normal h hh Z hzneg e c))
      (halfGroup h hh) := by
  classical
  intro g
  have hsel : h ∈ selected h Z := Or.inr rfl
  have hzero : (0 : ZMod n) ∉ selected h Z := by simp [selected, Ne.symm hn]
  cases g with
  | r i =>
    by_cases hi : i ∈ selected h Z
    · refine ⟨1, ⟨Or.inl rfl, ?_⟩, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro heq; exact hzero (r.inj heq ▸ hi)
        · simpa [connection] using hi
      · rintro a ⟨ha, hne, hm⟩
        rcases ha with rfl | rfl
        · rfl
        · change i+h ∈ selected h Z at hm
          exact ((selected_pair h hh hn Z hz i).mp hi hm).elim
    · refine ⟨r h, ⟨Or.inr rfl, ?_⟩, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro heq; exact hi ((r.inj heq).symm ▸ hsel)
        · change i+h ∈ selected h Z
          by_contra hx
          exact hi ((selected_pair h hh hn Z hz i).mpr hx)
      · rintro a ⟨ha, hne, hm⟩
        rcases ha with rfl | rfl
        · exact (hi (by simpa [connection] using hm)).elim
        · rfl
  | sr i =>
    have flip_general : ∀ x y : ZMod 2, x + 1 = y ↔ x ≠ y := by decide +kernel
    have flip : e i + 1 = c ↔ e i ≠ c := flip_general _ _
    by_cases hi : e i = c
    · refine ⟨1, ⟨Or.inl rfl, ?_⟩, ?_⟩
      · refine ⟨?_, ?_⟩
        · change sr i ≠ r 0
          intro heq
          cases heq
        · simpa using hi
      · rintro a ⟨ha, hne, hm⟩
        rcases ha with rfl | rfl
        · rfl
        · change e (i+h) = c at hm
          exact ((flip.mp (by simpa [map_add, he] using hm)) hi).elim
    · refine ⟨r h, ⟨Or.inr rfl, by
        refine ⟨by simp, ?_⟩
        change e (i+h) = c
        simpa [map_add, he] using flip.mpr hi⟩, ?_⟩
      rintro a ⟨ha, hne, hm⟩
      rcases ha with rfl | rfl
      · exact (hi (by simpa [connection] using hm)).elim
      · rfl

instance half_normal (h : ZMod n) (hh : h+h = 0) : (halfGroup h hh).Normal where
  conj_mem := by
    intro g hg a
    rcases hg with rfl | rfl
    · exact Or.inl (by simp)
    · right
      have nh : -h = h := neg_eq_iff_add_eq_zero.mpr hh
      cases a with
      | r i => simp only [inv_r, r_mul_r]; congr 1; abel
      | sr i => simp only [inv_sr, sr_mul_r, sr_mul_sr]; congr 1; linear_combination -hh

/-- The original perfect-code connection is obtained by removing all
internal subgroup elements from the total-code connection. -/
def perfectConnection (h : ZMod n) (hh : h+h = 0) (Z : Set (ZMod n))
    (e : ZMod n →+ ZMod 2) (c : ZMod 2) : Set (DihedralGroup n) :=
  connection h Z e c \ (halfGroup h hh : Set (DihedralGroup n))

theorem perfectConnection_normal (h : ZMod n) (hh : h+h = 0)
    (Z : Set (ZMod n)) (hzneg : ∀ i ∈ Z, -i ∈ Z)
    (e : ZMod n →+ ZMod 2) (c : ZMod 2) :
    NormalSubset (perfectConnection h hh Z e c) := by
  intro a x hx
  refine ⟨connection_normal h hh Z hzneg e c a x hx.1, ?_⟩
  intro hm
  apply hx.2
  have hb := Subgroup.Normal.conj_mem
    (inferInstance : (halfGroup h hh).Normal) (a*x*a⁻¹) hm a⁻¹
  simpa [mul_assoc] using hb

/-- The retained perfect-code construction on exactly the same source
transversal and reflection class, without a total-code hypothesis. -/
theorem perfect (h : ZMod n) (hh : h+h = 0) (hn : h ≠ 0)
    (Z : Set (ZMod n)) (hz : AddSubgroup.IsComplement Z (halfAdd h hh))
    (hzneg : ∀ i ∈ Z, -i ∈ Z) (e : ZMod n →+ ZMod 2)
    (he : e h = 1) (c : ZMod 2) :
    PerfectCodeTransversal.IsPerfectCode
      (sumGraph (perfectConnection h hh Z e c)
        (perfectConnection_normal h hh Z hzneg e c)) (halfGroup h hh) := by
  let H := halfGroup h hh
  have ht := total h hh hn Z hz hzneg e he c
  intro g
  by_cases hg : g ∈ H
  · refine ⟨g, ⟨hg, Or.inl rfl⟩, ?_⟩
    rintro x ⟨hx, hsame | hedge⟩
    · exact hsame.symm
    · exact (hedge.2.2 (H.mul_mem hg hx)).elim
  · obtain ⟨x, ⟨hx, hedge⟩, hu⟩ := ht g
    have hprod : g*x ∉ H := by
      intro hp
      apply hg
      have hm := H.mul_mem hp (H.inv_mem hx)
      simpa [mul_assoc] using hm
    refine ⟨x, ⟨hx, Or.inr ⟨hedge.1, hedge.2, hprod⟩⟩, ?_⟩
    rintro y ⟨hy, hsame | hedge⟩
    · exact (hg (hsame.symm ▸ hy)).elim
    · exact hu y ⟨hy, hedge.1, hedge.2.1⟩

end D5.S3.Combinatorics.CayleySumCodes.DihedralCentralConstruction
