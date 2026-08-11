/- GID: D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore
   generality: I
   mirror-B: none(waiver:formal-kernel-first-return-spectrum)
   mirror-E: none(waiver:kernel-symbolic-rotation-first-return)
   anchors: []
   digest: Internal first-return analysis for irrational rotations of an interval. -/

import D5.S1.Words.ReturnWords.GoldenGapFirstReturn
import D5.S1.Words.ReturnWords.GoldenRankArcs
import Mathlib.Data.Nat.Find
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

namespace D5.S1.Words

open Set

namespace GoldenArcFirstReturnInternal

private noncomputable def orbitPhase (alpha : Real) (i : Nat) : Real :=
  Int.fract (((i + 1 : Nat) : Real) * alpha)

private noncomputable def localOrbitPhase (alpha a : Real) (i : Nat) : Real :=
  Int.fract (((i + 1 : Nat) : Real) * alpha - a)

private theorem irrational_nat_mul_fract_ne_zero {alpha : Real} (halpha : Irrational alpha)
    {k : Nat} (hk : 0 < k) : Int.fract ((k : Real) * alpha) ≠ 0 := by
  rw [Int.fract_ne_zero_iff]
  rintro ⟨z, hz⟩
  have hi : Irrational ((k : Real) * alpha) := halpha.natCast_mul (by omega)
  exact hi.ne_int z hz.symm

theorem exists_positive_fract_lt {alpha ell : Real} (halpha : Irrational alpha)
    (hellpos : 0 < ell) (hellone : ell ≤ 1) :
    ∃ k : Nat, 0 < k ∧ Int.fract ((k : Real) * alpha) < ell := by
  have hz : DenseRange (fun z : Int => z • ((alpha : Real) : AddCircle (1 : Real))) := by
    rw [AddCircle.denseRange_zsmul_coe_iff]
    simpa using halpha
  have hn : DenseRange (fun q : Nat => q • ((alpha : Real) : AddCircle (1 : Real))) :=
    denseRange_zsmul_iff_nsmul.mp hz
  let U : Set (AddCircle (1 : Real)) :=
    ((fun x : Real => (x : AddCircle (1 : Real))) '' Ioo (0 : Real) ell)
  have hUopen : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hUne : U.Nonempty := by
    refine ⟨((ell / 2 : Real) : AddCircle (1 : Real)), ell / 2, ?_, rfl⟩
    constructor <;> linarith
  obtain ⟨q, x, hx, hxq⟩ := hn.exists_mem_open hUopen hUne
  have hfract_mem : Int.fract ((q : Real) * alpha) ∈ Ico (0 : Real) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hx_mem : x ∈ Ico (0 : Real) 1 := ⟨hx.1.le, hx.2.trans_le hellone⟩
  have hfract : Int.fract ((q : Real) * alpha) = x := by
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : Real)) (p := (1 : Real))
      (by simpa only [zero_add] using hfract_mem)
      (by simpa only [zero_add] using hx_mem)).mp
    rw [AddCircle.coe_fract]
    simpa [nsmul_eq_mul] using hxq.symm
  have hq : 0 < q := by
    by_contra hq
    have : q = 0 := Nat.eq_zero_of_not_pos hq
    subst q
    norm_num at hfract
    exact (ne_of_gt hx.1) hfract.symm
  exact ⟨q, hq, by simpa [hfract] using hx.2⟩

private theorem local_orbit_phase_eq_of_phase_ge {alpha a : Real} (i : Nat)
    (ha0 : 0 ≤ a) (hge : a ≤ orbitPhase alpha i) :
    localOrbitPhase alpha a i = orbitPhase alpha i - a := by
  change a ≤ Int.fract (((i + 1 : Nat) : Real) * alpha) at hge
  rw [localOrbitPhase, orbitPhase, Int.fract_eq_iff]
  constructor
  · exact sub_nonneg.mpr hge
  constructor
  · linarith [Int.fract_lt_one (((i + 1 : Nat) : Real) * alpha)]
  · refine ⟨⌊((i + 1 : Nat) : Real) * alpha⌋, ?_⟩
    calc
      ((i + 1 : Nat) : Real) * alpha - a -
          (Int.fract (((i + 1 : Nat) : Real) * alpha) - a) =
          ((i + 1 : Nat) : Real) * alpha -
            Int.fract (((i + 1 : Nat) : Real) * alpha) := by ring
      _ = (↑⌊((i + 1 : Nat) : Real) * alpha⌋ : Real) := Int.self_sub_fract _

private theorem local_orbit_phase_eq_of_phase_lt {alpha a : Real} (i : Nat)
    (_ha0 : 0 ≤ a) (ha1 : a < 1) (hlt : orbitPhase alpha i < a) :
    localOrbitPhase alpha a i = orbitPhase alpha i - a + 1 := by
  change Int.fract (((i + 1 : Nat) : Real) * alpha) < a at hlt
  rw [localOrbitPhase, orbitPhase, Int.fract_eq_iff]
  constructor
  · linarith [Int.fract_nonneg (((i + 1 : Nat) : Real) * alpha)]
  constructor
  · linarith
  · refine ⟨⌊((i + 1 : Nat) : Real) * alpha⌋ - 1, ?_⟩
    calc
      ((i + 1 : Nat) : Real) * alpha - a -
          (Int.fract (((i + 1 : Nat) : Real) * alpha) - a + 1) =
          (((i + 1 : Nat) : Real) * alpha -
            Int.fract (((i + 1 : Nat) : Real) * alpha)) - 1 := by ring
      _ = (↑⌊((i + 1 : Nat) : Real) * alpha⌋ : Real) - 1 := by
        rw [Int.self_sub_fract]
      _ = (↑(⌊((i + 1 : Nat) : Real) * alpha⌋ - 1) : Real) := by norm_num

private theorem local_orbit_phase_lt_iff_mem {alpha a ell : Real} (i : Nat)
    (ha0 : 0 ≤ a) (hellpos : 0 < ell) (hend : a + ell ≤ 1) :
    localOrbitPhase alpha a i < ell ↔ orbitPhase alpha i ∈ Ico a (a + ell) := by
  have ha1 : a < 1 := by linarith
  constructor
  · intro hlocal
    by_cases hge : a ≤ orbitPhase alpha i
    · rw [local_orbit_phase_eq_of_phase_ge i ha0 hge] at hlocal
      exact ⟨hge, by linarith⟩
    · have hlt : orbitPhase alpha i < a := lt_of_not_ge hge
      rw [local_orbit_phase_eq_of_phase_lt i ha0 ha1 hlt] at hlocal
      have hphase0 : 0 ≤ orbitPhase alpha i := Int.fract_nonneg _
      linarith
  · rintro ⟨hge, hlt⟩
    rw [local_orbit_phase_eq_of_phase_ge i ha0 hge]
    linarith

private theorem local_orbit_phase_add (alpha a : Real) (i d : Nat) :
    localOrbitPhase alpha a (i + d) =
      Int.fract (localOrbitPhase alpha a i + (d : Real) * alpha) := by
  simp only [localOrbitPhase]
  rw [Int.fract_eq_fract]
  refine ⟨⌊((i + 1 : Nat) : Real) * alpha - a⌋, ?_⟩
  calc
    (((i + d + 1 : Nat) : Real) * alpha - a) -
        (Int.fract (((i + 1 : Nat) : Real) * alpha - a) + (d : Real) * alpha) =
        (((i + 1 : Nat) : Real) * alpha - a) -
          Int.fract (((i + 1 : Nat) : Real) * alpha - a) := by
            push_cast
            ring
    _ = (↑⌊((i + 1 : Nat) : Real) * alpha - a⌋ : Real) := Int.self_sub_fract _

noncomputable def forwardDisplacement (alpha : Real) (k : Nat) : Real :=
  Int.fract ((k : Real) * alpha)

noncomputable def backwardDisplacement (alpha : Real) (k : Nat) : Real :=
  Int.fract ((k : Real) * (-alpha))

theorem forward_displacement_pos {alpha : Real} (halpha : Irrational alpha)
    {k : Nat} (hk : 0 < k) : 0 < forwardDisplacement alpha k := by
  exact lt_of_le_of_ne (Int.fract_nonneg _)
    (Ne.symm (irrational_nat_mul_fract_ne_zero halpha hk))

private theorem forward_displacement_lt_one (alpha : Real) (k : Nat) :
    forwardDisplacement alpha k < 1 := Int.fract_lt_one _

theorem backward_displacement_pos {alpha : Real} (halpha : Irrational alpha)
    {k : Nat} (hk : 0 < k) : 0 < backwardDisplacement alpha k := by
  exact forward_displacement_pos halpha.neg hk

theorem backward_displacement_lt_one (alpha : Real) (k : Nat) :
    backwardDisplacement alpha k < 1 := Int.fract_lt_one _

theorem backward_displacement_eq_one_sub_forward {alpha : Real}
    (halpha : Irrational alpha) {k : Nat} (hk : 0 < k) :
    backwardDisplacement alpha k = 1 - forwardDisplacement alpha k := by
  rw [backwardDisplacement, forwardDisplacement,
    show (k : Real) * -alpha = -((k : Real) * alpha) by ring,
    Int.fract_neg (irrational_nat_mul_fract_ne_zero halpha hk)]

private theorem fract_add_displacement (alpha x : Real) (k : Nat) :
    Int.fract (x + (k : Real) * alpha) =
      Int.fract (x + forwardDisplacement alpha k) := by
  rw [Int.fract_eq_fract]
  refine ⟨⌊(k : Real) * alpha⌋, ?_⟩
  calc
    (x + (k : Real) * alpha) - (x + forwardDisplacement alpha k) =
        (k : Real) * alpha - Int.fract ((k : Real) * alpha) := by
          rw [forwardDisplacement]
          ring
    _ = (↑⌊(k : Real) * alpha⌋ : Real) := Int.self_sub_fract _

private theorem fract_add_displacement_of_no_wrap {alpha x : Real} (k : Nat)
    (hx0 : 0 ≤ x) (hnowrap : x + forwardDisplacement alpha k < 1) :
    Int.fract (x + (k : Real) * alpha) = x + forwardDisplacement alpha k := by
  rw [fract_add_displacement]
  exact Int.fract_eq_self.mpr
    ⟨add_nonneg hx0 (Int.fract_nonneg _), hnowrap⟩

private theorem fract_add_displacement_of_wrap {alpha x : Real} (halpha : Irrational alpha)
    {k : Nat} (hk : 0 < k) (hx1 : x < 1)
    (hwrap : 1 ≤ x + forwardDisplacement alpha k) :
    Int.fract (x + (k : Real) * alpha) = x - backwardDisplacement alpha k := by
  have hback := backward_displacement_eq_one_sub_forward halpha hk
  calc
    Int.fract (x + (k : Real) * alpha) =
        Int.fract (x + forwardDisplacement alpha k) := fract_add_displacement alpha x k
    _ = Int.fract ((x + forwardDisplacement alpha k) - 1) :=
      (Int.fract_sub_one _).symm
    _ = (x + forwardDisplacement alpha k) - 1 := by
      rw [Int.fract_eq_self]
      constructor
      · linarith
      · linarith [forward_displacement_lt_one alpha k]
    _ = x - backwardDisplacement alpha k := by rw [hback]; ring

private theorem return_displacement_cases {alpha ell x : Real}
    (halpha : Irrational alpha) (hellone : ell < 1) {k : Nat} (hk : 0 < k)
    (hx : x ∈ Ico (0 : Real) ell)
    (hreturn : Int.fract (x + (k : Real) * alpha) ∈ Ico (0 : Real) ell) :
    (forwardDisplacement alpha k < ell ∧
      Int.fract (x + (k : Real) * alpha) = x + forwardDisplacement alpha k) ∨
    (backwardDisplacement alpha k < ell ∧ backwardDisplacement alpha k ≤ x ∧
      Int.fract (x + (k : Real) * alpha) = x - backwardDisplacement alpha k) := by
  by_cases hnowrap : x + forwardDisplacement alpha k < 1
  · left
    have heq := fract_add_displacement_of_no_wrap k hx.1 hnowrap
    rw [heq] at hreturn
    exact ⟨by linarith [hreturn.2, hx.1], heq⟩
  · right
    have hwrap : 1 ≤ x + forwardDisplacement alpha k := le_of_not_gt hnowrap
    have heq := fract_add_displacement_of_wrap halpha hk (hx.2.trans hellone) hwrap
    have hback := backward_displacement_eq_one_sub_forward halpha hk
    rw [heq] at hreturn
    refine ⟨?_, ?_, heq⟩
    · linarith [hreturn.1, hx.2]
    · linarith

theorem forward_displacement_sub {alpha : Real} {u v : Nat} (huv : u < v)
    (hdisp : forwardDisplacement alpha u < forwardDisplacement alpha v) :
    forwardDisplacement alpha (v - u) =
      forwardDisplacement alpha v - forwardDisplacement alpha u := by
  rw [forwardDisplacement, Int.fract_eq_iff]
  constructor
  · linarith
  constructor
  · have hu0 : 0 ≤ forwardDisplacement alpha u := Int.fract_nonneg _
    linarith [forward_displacement_lt_one alpha v]
  · refine ⟨⌊(v : Real) * alpha⌋ - ⌊(u : Real) * alpha⌋, ?_⟩
    rw [Int.cast_sub]
    calc
      ((v - u : Nat) : Real) * alpha -
          (Int.fract ((v : Real) * alpha) - Int.fract ((u : Real) * alpha)) =
          ((v : Real) * alpha - Int.fract ((v : Real) * alpha)) -
            ((u : Real) * alpha - Int.fract ((u : Real) * alpha)) := by
              rw [Nat.cast_sub (Nat.le_of_lt huv)]
              ring
      _ = (↑⌊(v : Real) * alpha⌋ : Real) - ↑⌊(u : Real) * alpha⌋ := by
        rw [Int.self_sub_fract, Int.self_sub_fract]

private theorem forward_displacement_add_of_wrap (alpha : Real) (u v : Nat)
    (hwrap : 1 ≤ forwardDisplacement alpha u + forwardDisplacement alpha v) :
    forwardDisplacement alpha (u + v) =
      forwardDisplacement alpha u + forwardDisplacement alpha v - 1 := by
  rw [forwardDisplacement, Int.fract_eq_iff]
  constructor
  · linarith
  constructor
  · have hu1 := forward_displacement_lt_one alpha u
    have hv1 := forward_displacement_lt_one alpha v
    linarith
  · refine ⟨⌊(u : Real) * alpha⌋ + ⌊(v : Real) * alpha⌋ + 1, ?_⟩
    rw [Int.cast_add, Int.cast_add, Int.cast_one]
    calc
      ((u + v : Nat) : Real) * alpha -
          (Int.fract ((u : Real) * alpha) + Int.fract ((v : Real) * alpha) - 1) =
          ((u : Real) * alpha - Int.fract ((u : Real) * alpha)) +
            ((v : Real) * alpha - Int.fract ((v : Real) * alpha)) + 1 := by
              push_cast
              ring
      _ = (↑⌊(u : Real) * alpha⌋ : Real) + ↑⌊(v : Real) * alpha⌋ + 1 := by
        rw [Int.self_sub_fract, Int.self_sub_fract]

private theorem backward_displacement_neg (alpha : Real) (k : Nat) :
    backwardDisplacement (-alpha) k = forwardDisplacement alpha k := by
  simp [backwardDisplacement, forwardDisplacement]

private theorem forward_displacement_neg (alpha : Real) (k : Nat) :
    forwardDisplacement (-alpha) k = backwardDisplacement alpha k := rfl

private theorem backward_ge_of_minimal_forward {alpha ell : Real}
    (halpha : Irrational alpha) {p q e : Nat}
    (hpmin : ∀ k, 0 < k → k < p → ¬forwardDisplacement alpha k < ell)
    (hqpos : 0 < q) (hqlt : backwardDisplacement alpha q < ell)
    (hqe : q ≤ e) (hep : e < p) :
    backwardDisplacement alpha q ≤ backwardDisplacement alpha e := by
  by_contra hnot
  have heq : q < e := lt_of_le_of_ne hqe fun heq => by
    subst e
    exact hnot le_rfl
  have hqback := backward_displacement_eq_one_sub_forward halpha hqpos
  have hepos : 0 < e := hqpos.trans_le hqe
  have heback := backward_displacement_eq_one_sub_forward halpha hepos
  have hforward : forwardDisplacement alpha q < forwardDisplacement alpha e := by
    linarith [lt_of_not_ge hnot]
  have hsub := forward_displacement_sub heq hforward
  have hebackpos := backward_displacement_pos halpha hepos
  apply hpmin (e - q) (by omega) (by omega)
  rw [hsub]
  linarith [hqback, heback, hqlt, hebackpos, lt_of_not_ge hnot]

private theorem forward_ge_of_minimal_backward {alpha ell : Real}
    (halpha : Irrational alpha) {p q e : Nat}
    (hqmin : ∀ k, 0 < k → k < q → ¬backwardDisplacement alpha k < ell)
    (hppos : 0 < p) (hplt : forwardDisplacement alpha p < ell)
    (hpe : p ≤ e) (heq : e < q) :
    forwardDisplacement alpha p ≤ forwardDisplacement alpha e := by
  by_contra hnot
  have hpe' : p < e := lt_of_le_of_ne hpe fun heq' => by
    subst e
    exact hnot le_rfl
  have hpback := backward_displacement_eq_one_sub_forward halpha hppos
  have hepos : 0 < e := hppos.trans_le hpe
  have heback := backward_displacement_eq_one_sub_forward halpha hepos
  have hbackward :
      forwardDisplacement (-alpha) p < forwardDisplacement (-alpha) e := by
    change backwardDisplacement alpha p < backwardDisplacement alpha e
    linarith [lt_of_not_ge hnot]
  have hsub := forward_displacement_sub (alpha := -alpha) hpe' hbackward
  have heforwardpos := forward_displacement_pos halpha hepos
  apply hqmin (e - p) (by omega) (by omega)
  change forwardDisplacement (-alpha) (e - p) < ell
  rw [hsub]
  change backwardDisplacement alpha e - backwardDisplacement alpha p < ell
  linarith [hpback, heback, hplt, heforwardpos, lt_of_not_ge hnot]

private theorem minimal_sum_of_forward_best {alpha ell : Real} {d p q : Nat}
    (halpha : Irrational alpha) (_hellpos : 0 < ell) (hdpos : 0 < d)
    (hppos : 0 < p) (hplt : forwardDisplacement alpha p < ell)
    (hpfirst : ∀ k, 0 < k → forwardDisplacement alpha k < ell → p ≤ k)
    (hqpos : 0 < q) (hqlt : backwardDisplacement alpha q < ell)
    (hqfirst : ∀ k, 0 < k → backwardDisplacement alpha k < ell → q ≤ k)
    (hbest : ∀ k, 0 < k → k < d → ell ≤ forwardDisplacement alpha k)
    (horient : ell = forwardDisplacement alpha d) :
    ell = forwardDisplacement alpha p + backwardDisplacement alpha q := by
  have hdp : d < p := by
    have hnot : ¬p < d := by
      intro hpd
      exact (not_lt_of_ge (hbest p hppos hpd)) hplt
    have hne : p ≠ d := by
      intro hpd
      subst p
      linarith
    omega
  let q0 := p - d
  have hq0pos : 0 < q0 := by dsimp [q0]; omega
  have hdback := backward_displacement_eq_one_sub_forward halpha hdpos
  have hpback := backward_displacement_eq_one_sub_forward halpha hppos
  have hbacklt :
      forwardDisplacement (-alpha) d < forwardDisplacement (-alpha) p := by
    change backwardDisplacement alpha d < backwardDisplacement alpha p
    rw [hdback, hpback]
    linarith
  have hsub := forward_displacement_sub (alpha := -alpha) hdp hbacklt
  have hq0eq : backwardDisplacement alpha q0 = ell - forwardDisplacement alpha p := by
    change forwardDisplacement (-alpha) q0 = ell - forwardDisplacement alpha p
    dsimp [q0]
    rw [hsub]
    change backwardDisplacement alpha p - backwardDisplacement alpha d =
      ell - forwardDisplacement alpha p
    rw [hdback, hpback, horient]
    ring
  have hq0lt : backwardDisplacement alpha q0 < ell := by
    rw [hq0eq]
    linarith [forward_displacement_pos halpha hppos]
  have hqle : q ≤ q0 := hqfirst q0 hq0pos hq0lt
  have hqeq : q = q0 := by
    apply le_antisymm hqle
    by_contra hnot
    have hqq0 : q < q0 := lt_of_not_ge hnot
    have hdq : d + q < p := by dsimp [q0] at hqq0; omega
    have hqback := backward_displacement_eq_one_sub_forward halpha hqpos
    have hwrap :
        1 ≤ forwardDisplacement alpha d + forwardDisplacement alpha q := by
      linarith [hqback, hqlt, horient]
    have hadd := forward_displacement_add_of_wrap alpha d q hwrap
    have hsmall : forwardDisplacement alpha (d + q) < ell := by
      rw [hadd, ← horient]
      have hqbackpos := backward_displacement_pos halpha hqpos
      linarith [hqback]
    exact (not_le_of_gt hdq) (hpfirst (d + q) (by omega) hsmall)
  rw [hqeq, hq0eq]
  ring

theorem minimal_displacements_sum_of_best {alpha ell : Real} {d p q : Nat}
    (halpha : Irrational alpha) (hellpos : 0 < ell) (hdpos : 0 < d)
    (hppos : 0 < p) (hplt : forwardDisplacement alpha p < ell)
    (hpfirst : ∀ k, 0 < k → forwardDisplacement alpha k < ell → p ≤ k)
    (hqpos : 0 < q) (hqlt : backwardDisplacement alpha q < ell)
    (hqfirst : ∀ k, 0 < k → backwardDisplacement alpha k < ell → q ≤ k)
    (horient :
      (ell = forwardDisplacement alpha d ∧
        ∀ k, 0 < k → k < d → ell ≤ forwardDisplacement alpha k) ∨
      (ell = backwardDisplacement alpha d ∧
        ∀ k, 0 < k → k < d → ell ≤ backwardDisplacement alpha k)) :
    ell = forwardDisplacement alpha p + backwardDisplacement alpha q := by
  rcases horient with ⟨hforward, hbest⟩ | ⟨hbackward, hbest⟩
  · exact minimal_sum_of_forward_best halpha hellpos hdpos hppos hplt hpfirst hqpos
      hqlt hqfirst hbest hforward
  · have h := minimal_sum_of_forward_best (alpha := -alpha) (d := d) (p := q)
      (q := p) halpha.neg hellpos hdpos hqpos hqlt (by
        intro k hk hlt
        exact hqfirst k hk hlt) hppos (by
          simpa [backward_displacement_neg] using hplt) (by
            intro k hk hlt
            apply hpfirst k hk
            simpa [backward_displacement_neg] using hlt) (by
              intro k hk hkd
              exact hbest k hk hkd) hbackward
    simpa [forward_displacement_neg, backward_displacement_neg, add_comm] using h

private def IsLocalFirstReturn (alpha ell x : Real) (d : Nat) : Prop :=
  x ∈ Ico (0 : Real) ell ∧ 0 < d ∧
    Int.fract (x + (d : Real) * alpha) ∈ Ico (0 : Real) ell ∧
    ∀ e, 0 < e → e < d →
      Int.fract (x + (e : Real) * alpha) ∉ Ico (0 : Real) ell

private theorem local_first_return_time_unique {alpha ell x : Real} {d e : Nat}
    (hd : IsLocalFirstReturn alpha ell x d)
    (he : IsLocalFirstReturn alpha ell x e) : d = e := by
  rcases hd with ⟨_, hdpos, hdreturn, hdfirst⟩
  rcases he with ⟨_, hepos, hereturn, hefirst⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hde | hed
  · exact (hefirst d hdpos hde) hdreturn
  · exact (hdfirst e hepos hed) hereturn

private theorem left_local_first_return {alpha ell x : Real}
    (halpha : Irrational alpha) (hellone : ell < 1) {p q : Nat}
    (hppos : 0 < p) (_hplt : forwardDisplacement alpha p < ell)
    (hpfirst : ∀ k, 0 < k → forwardDisplacement alpha k < ell → p ≤ k)
    (hqpos : 0 < q) (hqlt : backwardDisplacement alpha q < ell)
    (hqfirst : ∀ k, 0 < k → backwardDisplacement alpha k < ell → q ≤ k)
    (hsum : ell = forwardDisplacement alpha p + backwardDisplacement alpha q)
    (hx : x ∈ Ico (0 : Real) ell) (hxleft : x < backwardDisplacement alpha q) :
    IsLocalFirstReturn alpha ell x p := by
  have hpmin : ∀ k, 0 < k → k < p → ¬forwardDisplacement alpha k < ell := by
    intro k hk hkp hsmall
    exact (not_le_of_gt hkp) (hpfirst k hk hsmall)
  have hnowrap : x + forwardDisplacement alpha p < 1 := by
    linarith
  have hpreturn := fract_add_displacement_of_no_wrap p hx.1 hnowrap
  refine ⟨hx, hppos, ?_, ?_⟩
  · rw [hpreturn]
    exact ⟨add_nonneg hx.1 (Int.fract_nonneg _), by linarith⟩
  · intro e hepos hep hereturn
    rcases return_displacement_cases halpha hellone hepos hx hereturn with hforward | hbackward
    · exact (not_le_of_gt hep) (hpfirst e hepos hforward.1)
    · have hqe : q ≤ e := hqfirst e hepos hbackward.1
      have hge := backward_ge_of_minimal_forward halpha hpmin hqpos hqlt hqe hep
      linarith [hbackward.2.1]

private theorem right_local_first_return {alpha ell x : Real}
    (halpha : Irrational alpha) (hellone : ell < 1) {p q : Nat}
    (hppos : 0 < p) (hplt : forwardDisplacement alpha p < ell)
    (hpfirst : ∀ k, 0 < k → forwardDisplacement alpha k < ell → p ≤ k)
    (hqpos : 0 < q) (_hqlt : backwardDisplacement alpha q < ell)
    (hqfirst : ∀ k, 0 < k → backwardDisplacement alpha k < ell → q ≤ k)
    (hsum : ell = forwardDisplacement alpha p + backwardDisplacement alpha q)
    (hx : x ∈ Ico (0 : Real) ell) (hxright : backwardDisplacement alpha q ≤ x) :
    IsLocalFirstReturn alpha ell x q := by
  have hqmin : ∀ k, 0 < k → k < q → ¬backwardDisplacement alpha k < ell := by
    intro k hk hkq hsmall
    exact (not_le_of_gt hkq) (hqfirst k hk hsmall)
  have hqback := backward_displacement_eq_one_sub_forward halpha hqpos
  have hwrap : 1 ≤ x + forwardDisplacement alpha q := by linarith
  have hqreturn := fract_add_displacement_of_wrap halpha hqpos
    (hx.2.trans hellone) hwrap
  refine ⟨hx, hqpos, ?_, ?_⟩
  · rw [hqreturn]
    constructor
    · exact sub_nonneg.mpr hxright
    · have hxlt := hx.2
      have hetapos := backward_displacement_pos halpha hqpos
      linarith
  · intro e hepos heq hereturn
    rcases return_displacement_cases halpha hellone hepos hx hereturn with hforward | hbackward
    · have hpe : p ≤ e := hpfirst e hepos hforward.1
      have hge := forward_ge_of_minimal_backward halpha hqmin hppos hplt hpe heq
      rw [hforward.2] at hereturn
      linarith [hereturn.2]
    · exact (not_le_of_gt heq) (hqfirst e hepos hbackward.1)

private theorem exists_orbit_phase_mem_Ioo {alpha a b : Real} (halpha : Irrational alpha)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ i, orbitPhase alpha i ∈ Ioo a b := by
  have hz : DenseRange (fun z : Int => z • ((alpha : Real) : AddCircle (1 : Real))) := by
    rw [AddCircle.denseRange_zsmul_coe_iff]
    simpa using halpha
  have hn : DenseRange (fun q : Nat => q • ((alpha : Real) : AddCircle (1 : Real))) :=
    denseRange_zsmul_iff_nsmul.mp hz
  let U : Set (AddCircle (1 : Real)) :=
    ((fun x : Real => (x : AddCircle (1 : Real))) '' Ioo a b)
  have hUopen : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hUne : U.Nonempty := by
    refine ⟨(((a + b) / 2 : Real) : AddCircle (1 : Real)), (a + b) / 2, ?_, rfl⟩
    constructor <;> linarith
  obtain ⟨q, x, hx, hxq⟩ := hn.exists_mem_open hUopen hUne
  have hfract_mem : Int.fract ((q : Real) * alpha) ∈ Ico (0 : Real) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hx_mem : x ∈ Ico (0 : Real) 1 := ⟨(ha.trans_lt hx.1).le, hx.2.trans_le hb⟩
  have hfract : Int.fract ((q : Real) * alpha) = x := by
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : Real)) (p := (1 : Real))
      (by simpa only [zero_add] using hfract_mem)
      (by simpa only [zero_add] using hx_mem)).mp
    rw [AddCircle.coe_fract]
    simpa [nsmul_eq_mul] using hxq.symm
  have hq : 0 < q := by
    by_contra hq
    have : q = 0 := Nat.eq_zero_of_not_pos hq
    subst q
    exact (ha.trans_lt hx.1).ne (by simpa using hfract)
  refine ⟨q - 1, ?_⟩
  rw [orbitPhase, Nat.sub_add_cancel hq]
  simpa [hfract] using hx

private theorem local_first_return_iff_arc {alpha a ell : Real}
    (ha0 : 0 ≤ a) (hellpos : 0 < ell) (hend : a + ell ≤ 1)
    (i d : Nat) :
    IsLocalFirstReturn alpha ell (localOrbitPhase alpha a i) d ↔
      0 < d ∧ orbitPhase alpha i ∈ Ico a (a + ell) ∧
      orbitPhase alpha (i + d) ∈ Ico a (a + ell) ∧
      ∀ e, 0 < e → e < d → orbitPhase alpha (i + e) ∉ Ico a (a + ell) := by
  have hlocal0 : 0 ≤ localOrbitPhase alpha a i := Int.fract_nonneg _
  constructor
  · rintro ⟨hstartLocal, hdpos, hdreturn, hfirst⟩
    refine ⟨hdpos, (local_orbit_phase_lt_iff_mem i ha0 hellpos hend).mp ?_,
      (local_orbit_phase_lt_iff_mem (i + d) ha0 hellpos hend).mp ?_, ?_⟩
    · exact hstartLocal.2
    · rw [local_orbit_phase_add]
      exact hdreturn.2
    · intro e hepos hed harc
      apply hfirst e hepos hed
      rw [← local_orbit_phase_add]
      exact ⟨Int.fract_nonneg _, (local_orbit_phase_lt_iff_mem (i + e) ha0 hellpos hend).mpr
        harc⟩
  · rintro ⟨hdpos, hstart, hreturn, hfirst⟩
    refine ⟨⟨hlocal0, (local_orbit_phase_lt_iff_mem i ha0 hellpos hend).mpr hstart⟩,
      hdpos, ?_, ?_⟩
    · rw [← local_orbit_phase_add]
      exact ⟨Int.fract_nonneg _, (local_orbit_phase_lt_iff_mem (i + d) ha0 hellpos hend).mpr
        hreturn⟩
    · intro e hepos hed hlocal
      apply hfirst e hepos hed
      apply (local_orbit_phase_lt_iff_mem (i + e) ha0 hellpos hend).mp
      rw [local_orbit_phase_add]
      exact hlocal.2

def orbitArcFirstReturnGapSet (alpha a ell : Real) : Set Nat :=
  {d | 0 < d ∧ ∃ i, orbitPhase alpha i ∈ Ico a (a + ell) ∧
    orbitPhase alpha (i + d) ∈ Ico a (a + ell) ∧
    ∀ e, 0 < e → e < d → orbitPhase alpha (i + e) ∉ Ico a (a + ell)}

theorem orbit_arc_first_return_eq_pair {alpha a ell : Real}
    (halpha : Irrational alpha) (ha0 : 0 ≤ a) (hellpos : 0 < ell)
    (hellone : ell < 1) (hend : a + ell ≤ 1) {p q : Nat}
    (hppos : 0 < p) (hplt : forwardDisplacement alpha p < ell)
    (hpfirst : ∀ k, 0 < k → forwardDisplacement alpha k < ell → p ≤ k)
    (hqpos : 0 < q) (hqlt : backwardDisplacement alpha q < ell)
    (hqfirst : ∀ k, 0 < k → backwardDisplacement alpha k < ell → q ≤ k)
    (hsum : ell = forwardDisplacement alpha p + backwardDisplacement alpha q) :
    orbitArcFirstReturnGapSet alpha a ell = {p, q} := by
  ext d
  constructor
  · rintro ⟨hdpos, i, hstart, hreturn, hfirst⟩
    have hdlocal : IsLocalFirstReturn alpha ell (localOrbitPhase alpha a i) d :=
      (local_first_return_iff_arc ha0 hellpos hend i d).mpr
        ⟨hdpos, hstart, hreturn, hfirst⟩
    have hx : localOrbitPhase alpha a i ∈ Ico (0 : Real) ell :=
      ⟨Int.fract_nonneg _, (local_orbit_phase_lt_iff_mem i ha0 hellpos hend).mpr hstart⟩
    by_cases hxleft : localOrbitPhase alpha a i < backwardDisplacement alpha q
    · have hp := left_local_first_return halpha hellone hppos hplt hpfirst hqpos hqlt
        hqfirst hsum hx hxleft
      have : d = p := local_first_return_time_unique hdlocal hp
      simp [this]
    · have hq := right_local_first_return halpha hellone hppos hplt hpfirst hqpos hqlt
        hqfirst hsum hx (le_of_not_gt hxleft)
      have : d = q := local_first_return_time_unique hdlocal hq
      simp [this]
  · intro hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with hdp | hdq
    · subst d
      obtain ⟨i, hi⟩ := exists_orbit_phase_mem_Ioo (alpha := alpha) (a := a)
        (b := a + backwardDisplacement alpha q) halpha ha0
        (by linarith [backward_displacement_pos halpha hqpos])
        (by linarith [hqlt, hend])
      have hstart : orbitPhase alpha i ∈ Ico a (a + ell) := by
        exact ⟨hi.1.le, hi.2.trans (by linarith)⟩
      have hx : localOrbitPhase alpha a i ∈ Ico (0 : Real) ell :=
        ⟨Int.fract_nonneg _, (local_orbit_phase_lt_iff_mem i ha0 hellpos hend).mpr hstart⟩
      have hxleft : localOrbitPhase alpha a i < backwardDisplacement alpha q := by
        rw [local_orbit_phase_eq_of_phase_ge i ha0 hi.1.le]
        linarith [hi.2]
      have harc := (local_first_return_iff_arc ha0 hellpos hend i p).mp
        (left_local_first_return halpha hellone hppos hplt hpfirst hqpos hqlt hqfirst
          hsum hx hxleft)
      exact ⟨hppos, i, harc.2⟩
    · subst d
      obtain ⟨i, hi⟩ := exists_orbit_phase_mem_Ioo (alpha := alpha)
        (a := a + backwardDisplacement alpha q) (b := a + ell) halpha
        (by linarith [ha0, backward_displacement_pos halpha hqpos])
        (by linarith [hsum, forward_displacement_pos halpha hppos])
        (by linarith [hend])
      have hstart : orbitPhase alpha i ∈ Ico a (a + ell) :=
        ⟨by linarith [hi.1, backward_displacement_pos halpha hqpos], hi.2⟩
      have hx : localOrbitPhase alpha a i ∈ Ico (0 : Real) ell :=
        ⟨Int.fract_nonneg _, (local_orbit_phase_lt_iff_mem i ha0 hellpos hend).mpr hstart⟩
      have hxright : backwardDisplacement alpha q ≤ localOrbitPhase alpha a i := by
        rw [local_orbit_phase_eq_of_phase_ge i ha0 hstart.1]
        linarith [hi.1]
      have harc := (local_first_return_iff_arc ha0 hellpos hend i q).mp
        (right_local_first_return halpha hellone hppos hplt hpfirst hqpos hqlt hqfirst
          hsum hx hxright)
      exact ⟨hqpos, i, harc.2⟩

end GoldenArcFirstReturnInternal

end D5.S1.Words
