/- GID: D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraHeightEnvelope
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: Finite unit-edge integer grids admit attained extremum envelopes. -/

/-
Adapted from Chakshu Gupta, https://github.com/ChakshuGupta13/lab,
math/gupta2026degseq/lean, source tree 8beb89d4466cb8551abc92d0405972edc2edf116.
Basic.lean: be1cc632964016d8f144d053bc0cca60a1fece5a.
Envelope.lean: 7c08595853dcf1b5860ea6cbd7b60dd84fed40c1.
SequelEd.lean: 0f95aba54002836654f9b836359d6d392295fd74.
Licensed CC BY 4.0; full terms and attribution: docs/reports/miura-suppliers/.
The finite declarations retain their proof bodies; namespaces and imports are adapted.
Retire this transplant when the project's pinned mathlib supplies equivalent finite
unit-edge grid envelope and normalized-height finiteness declarations, using those
pinned declarations directly in the consumers.
-/

module

public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto

/-! Finite attained envelopes and finiteness of normalized integer heights. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraHeightEnvelope

variable {m n : ℕ}

abbrev Cell (m n : ℕ) := Fin m × Fin n


def gdist (p q : Cell m n) : ℤ :=
  ((((p.1.val : ℤ) - q.1.val).natAbs + ((p.2.val : ℤ) - q.2.val).natAbs : ℕ) : ℤ)

lemma gdist_nonneg (p q : Cell m n) : 0 ≤ gdist p q := by unfold gdist; omega

lemma gdist_self (p : Cell m n) : gdist p p = 0 := by unfold gdist; omega

lemma gdist_comm (p q : Cell m n) : gdist p q = gdist q p := by unfold gdist; omega

lemma gdist_triangle (a b c : Cell m n) : gdist a c ≤ gdist a b + gdist b c := by
  unfold gdist; omega

lemma gdist_eq_zero {p q : Cell m n} : gdist p q = 0 ↔ p = q := by
  constructor
  · intro h
    unfold gdist at h
    have e1 : p.1.val = q.1.val := by omega
    have e2 : p.2.val = q.2.val := by omega
    exact Prod.ext_iff.2 ⟨Fin.ext e1, Fin.ext e2⟩
  · intro h; subst h; exact gdist_self p


def adj (p q : Cell m n) : Prop := gdist p q = 1


def IsHeight (h : Cell m n → ℤ) : Prop := ∀ p q, adj p q → |h p - h q| = 1


def IsStrictLocalMax (h : Cell m n → ℤ) (q : Cell m n) : Prop :=
  ∀ u, adj q u → h u = h q - 1


def IsStrictLocalMin (h : Cell m n → ℤ) (p : Cell m n) : Prop :=
  ∀ u, adj p u → h u = h p + 1


lemma exists_step_toward {p q : Cell m n} (hpq : p ≠ q) :
    ∃ p', adj p p' ∧ gdist p' q = gdist p q - 1 := by
  have hcoord : p.1.val ≠ q.1.val ∨ p.2.val ≠ q.2.val := by
    by_contra h
    push Not at h
    exact hpq (Prod.ext_iff.2 ⟨Fin.ext h.1, Fin.ext h.2⟩)
  rcases hcoord with hrow | hcol
  · rcases lt_or_gt_of_ne hrow with hlt | hgt
    · have hb : p.1.val + 1 < m := by have := q.1.isLt; omega
      refine ⟨(⟨p.1.val + 1, hb⟩, p.2), ?_, ?_⟩
      · simp only [adj, gdist]; omega
      · simp only [gdist]; omega
    · have hb : p.1.val - 1 < m := by have := p.1.isLt; omega
      refine ⟨(⟨p.1.val - 1, hb⟩, p.2), ?_, ?_⟩
      · simp only [adj, gdist]; omega
      · simp only [gdist]; omega
  · rcases lt_or_gt_of_ne hcol with hlt | hgt
    · have hb : p.2.val + 1 < n := by have := q.2.isLt; omega
      refine ⟨(p.1, ⟨p.2.val + 1, hb⟩), ?_, ?_⟩
      · simp only [adj, gdist]; omega
      · simp only [gdist]; omega
    · have hb : p.2.val - 1 < n := by have := p.2.isLt; omega
      refine ⟨(p.1, ⟨p.2.val - 1, hb⟩), ?_, ?_⟩
      · simp only [adj, gdist]; omega
      · simp only [gdist]; omega


lemma height_lipschitz {h : Cell m n → ℤ} (hh : IsHeight h) :
    ∀ (k : ℕ) (a b : Cell m n), gdist a b ≤ k → |h a - h b| ≤ gdist a b := by
  intro k
  induction k with
  | zero =>
    intro a b hk
    have hz : gdist a b = 0 := le_antisymm hk (gdist_nonneg a b)
    have hab : a = b := gdist_eq_zero.1 hz
    subst hab; simp [gdist_self]
  | succ k ih =>
    intro a b hk
    by_cases hab : a = b
    · subst hab; simp [gdist_self]
    · obtain ⟨a', ha', hd⟩ := exists_step_toward hab
      have hb' : gdist a' b ≤ k := by rw [hd]; omega
      have hih := ih a' b hb'
      have h1 : |h a - h a'| = 1 := hh a a' ha'
      have htri : |h a - h b| ≤ |h a - h a'| + |h a' - h b| := abs_sub_le _ _ _
      rw [hd] at hih
      linarith

lemma exists_descent_to_min {h : Cell m n → ℤ} (hh : IsHeight h) (v : Cell m n) :
    ∃ p, IsStrictLocalMin h p ∧ h v = h p + gdist p v := by
  have : Nonempty (Cell m n) := ⟨v⟩
  obtain ⟨w0, hw0⟩ := Finite.exists_min h

  suffices key : ∀ (k : ℕ) (v : Cell m n), (h v - h w0).toNat ≤ k →
      ∃ p, IsStrictLocalMin h p ∧ h v = h p + gdist p v by
    exact key (h v - h w0).toNat v le_rfl
  intro k
  induction k with
  | zero =>
    intro v hk
    have hmin0 : h v = h w0 := by have := hw0 v; omega
    have hvmin : IsStrictLocalMin h v := by
      intro u hu
      have hle := hw0 u
      have h1 := hh v u hu
      rcases (abs_eq (by norm_num : (0:ℤ) ≤ 1)).1 h1 with h2 | h2 <;> omega
    exact ⟨v, hvmin, by simp [gdist_self]⟩
  | succ k ih =>
    intro v hk
    by_cases hvmin : IsStrictLocalMin h v
    · exact ⟨v, hvmin, by simp [gdist_self]⟩
    · simp only [IsStrictLocalMin, not_forall] at hvmin
      obtain ⟨u, hu⟩ := hvmin
      have hadj : adj v u := by tauto
      have hune : h u ≠ h v + 1 := by tauto
      have h1 := hh v u hadj
      have hdown : h u = h v - 1 := by
        rcases (abs_eq (by norm_num : (0:ℤ) ≤ 1)).1 h1 with h2 | h2
        · omega
        · exact absurd (by omega : h u = h v + 1) hune
      have hdefu : (h u - h w0).toNat ≤ k := by have := hw0 u; omega
      obtain ⟨p, hpmin, hpu⟩ := ih u hdefu

      have htri := gdist_triangle p u v
      have huv : gdist u v = 1 := by rw [gdist_comm]; exact hadj
      have hlip : |h p - h v| ≤ gdist p v :=
        height_lipschitz hh (gdist p v).toNat p v
          (le_of_eq (Int.toNat_of_nonneg (gdist_nonneg p v)).symm)
      have hge0 := gdist_nonneg p u
      have hpv : gdist p v = gdist p u + 1 := by
        rw [abs_le] at hlip; omega
      exact ⟨p, hpmin, by omega⟩


lemma envelope_le {h : Cell m n → ℤ} (hh : IsHeight h) (p v : Cell m n) :
    h v ≤ h p + gdist p v := by
  have hlip : |h v - h p| ≤ gdist v p :=
    height_lipschitz hh (gdist v p).toNat v p
      (le_of_eq (Int.toNat_of_nonneg (gdist_nonneg v p)).symm)
  rw [gdist_comm v p, abs_le] at hlip
  omega


theorem envelope_min {h : Cell m n → ℤ} (hh : IsHeight h) (v : Cell m n) :
    (∃ p, IsStrictLocalMin h p ∧ h v = h p + gdist p v)
      ∧ (∀ p, IsStrictLocalMin h p → h v ≤ h p + gdist p v) :=
  ⟨exists_descent_to_min hh v, fun p _ => envelope_le hh p v⟩


theorem envelope_max {h : Cell m n → ℤ} (hh : IsHeight h) (v : Cell m n) :
    (∃ q, IsStrictLocalMax h q ∧ h v = h q - gdist q v)
      ∧ (∀ q, IsStrictLocalMax h q → h q - gdist q v ≤ h v) := by
  have hh' : IsHeight (fun w => -h w) := by
    intro a b hab
    have := hh a b hab
    rw [show (-h a) - (-h b) = -(h a - h b) by ring, abs_neg]; exact this
  obtain ⟨⟨p, hpmin, hpeq⟩, hple⟩ := envelope_min hh' v
  constructor
  · refine ⟨p, ?_, ?_⟩
    · intro u hu
      have := hpmin u hu; linarith
    · have := hpeq; linarith
  · intro q hq
    have hq' : IsStrictLocalMin (fun w => -h w) q := by
      intro u hu; have := hq u hu; linarith
    have := hple q hq'; linarith

def IsCanonicalHeight (h : Cell m n → ℤ) : Prop :=
  IsHeight h ∧ ∀ p : Cell m n, p.1.val = 0 → p.2.val = 0 → h p = 0


def CanonicalHeights (m n : ℕ) : Set (Cell m n → ℤ) :=
  { h | IsCanonicalHeight h }

theorem CanonicalHeights_finite (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (CanonicalHeights m n).Finite := by
  set B : ℕ := m + n - 2 with hB_def

  have h_bounded_finite :
      {h : Cell m n → ℤ | ∀ p, h p ∈ Set.Icc (-(B : ℤ)) (B : ℤ)}.Finite :=
    Set.Finite.pi' (fun _ => Set.finite_Icc _ _)
  refine h_bounded_finite.subset ?_
  unfold CanonicalHeights IsCanonicalHeight
  rintro h ⟨hh_height, hh_zero⟩ p

  let origin : Cell m n := (⟨0, hm⟩, ⟨0, hn⟩)

  have h_origin_zero : h origin = 0 := hh_zero origin rfl rfl

  have hp1 : p.1.val ≤ m - 1 := Nat.le_sub_one_of_lt p.1.isLt
  have hp2 : p.2.val ≤ n - 1 := Nat.le_sub_one_of_lt p.2.isLt
  have h_gdist_bound : gdist origin p ≤ (B : ℤ) := by
    change (((((⟨0, hm⟩ : Fin m)).val : ℤ) - (p.1.val : ℤ)).natAbs
          + (((⟨0, hn⟩ : Fin n).val : ℤ) - (p.2.val : ℤ)).natAbs : ℕ) ≤ (B : ℤ)
    have hn1 : ((((⟨0, hm⟩ : Fin m)).val : ℤ) - (p.1.val : ℤ)).natAbs = p.1.val := by
      simp
    have hn2 : ((((⟨0, hn⟩ : Fin n)).val : ℤ) - (p.2.val : ℤ)).natAbs = p.2.val := by
      simp
    rw [hn1, hn2]
    push_cast
    omega

  have h_gd_nonneg : (0 : ℤ) ≤ gdist origin p := gdist_nonneg _ _
  have h_toNat : ((gdist origin p).toNat : ℤ) = gdist origin p :=
    Int.toNat_of_nonneg h_gd_nonneg
  have h_lip : |h origin - h p| ≤ gdist origin p :=
    height_lipschitz hh_height (gdist origin p).toNat origin p (by rw [h_toNat])
  rw [h_origin_zero, zero_sub, abs_neg] at h_lip

  rw [Set.mem_Icc]
  have h_abs : |h p| ≤ (B : ℤ) := le_trans h_lip h_gdist_bound
  exact abs_le.mp h_abs

end D5.S3.Combinatorics.Geometry.MiuraHeightEnvelope
