/- GID: D5/S1/Words/Complexity/MechanicalSubshiftIntercept
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/MechanicalSubshiftIntercept
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   digest: Irrational mechanical subshifts ignore intercepts; equality classifies slopes. -/

import D5.S1.Words.Complexity.MechanicalSubshiftMinimality
import D5.S1.Words.Complexity.MechanicalSubshiftSlopeRigidity
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

namespace D5.S1.Words.Complexity.MechanicalSubshiftIntercept

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.SubshiftHausdorffDimension
open D5.S1.Words.Complexity.MechanicalSubshiftMinimality
open D5.S1.Words.Complexity.MechanicalSubshiftSlopeRigidity
open D5.S1.Words.Mechanical
open Set

noncomputable section

/-- Floor of a shifted point splits off the fractional part. -/
private theorem floor_add_sub_floor (x t : Real) :
    ⌊x + t⌋ - ⌊x⌋ = ⌊Int.fract x + t⌋ := by
  have hx : (⌊x⌋ : Real) + (Int.fract x + t) = x + t := by
    calc
      (⌊x⌋ : Real) + (Int.fract x + t) = ((⌊x⌋ : Real) + Int.fract x) + t := by ring
      _ = x + t := by rw [Int.floor_add_fract]
  rw [← hx, Int.floor_intCast_add]
  omega

/-- The window-count profile seen from a phase `x`. -/
noncomputable def phaseFloor (alpha x : Real) (m : Nat) : Int := ⌊x + (m : Real) * alpha⌋

/-- NOVEL STEP 1: the letters at `i + k` depend on the intercept only through the phase. -/
theorem letter_eq_phaseFloor_sub (alpha rho : Real) (i k : Nat) :
    lowerMechanicalLetter alpha rho (i + k) =
      phaseFloor alpha (Int.fract (rho + (i : Real) * alpha)) (k + 1) -
        phaseFloor alpha (Int.fract (rho + (i : Real) * alpha)) k := by
  have key : ∀ m : Nat, ⌊rho + ((i + m : Nat) : Real) * alpha⌋ =
      ⌊rho + (i : Real) * alpha⌋ +
        phaseFloor alpha (Int.fract (rho + (i : Real) * alpha)) m := by
    intro m
    have h := floor_add_sub_floor (rho + (i : Real) * alpha) ((m : Real) * alpha)
    have hsum : rho + (i : Real) * alpha + (m : Real) * alpha
        = rho + ((i + m : Nat) : Real) * alpha := by push_cast; ring
    rw [hsum] at h
    simp only [phaseFloor]
    omega
  have h1 := key (k + 1)
  have h2 := key k
  have hcast : ((i + k + 1 : Nat) : Real) = ((i + (k + 1) : Nat) : Real) := by push_cast; ring
  simp only [lowerMechanicalLetter]
  rw [show i + k + 1 = i + (k + 1) by omega] at *
  push_cast at h1 h2 ⊢
  omega

/-- Transcribed from the frozen modules (private there): floor with an indicator. -/
private theorem floor_fract_add_indicator (x t : Real) :
    ⌊Int.fract x + t⌋ = ⌊t⌋ + if 1 - Int.fract t ≤ Int.fract x then 1 else 0 := by
  have hdecomp : (⌊t⌋ : Real) + (Int.fract x + Int.fract t) = Int.fract x + t := by
    calc
      (⌊t⌋ : Real) + (Int.fract x + Int.fract t) =
          Int.fract x + ((⌊t⌋ : Real) + Int.fract t) := by ring
      _ = Int.fract x + t := by rw [Int.floor_add_fract]
  rw [← hdecomp, Int.floor_intCast_add]
  congr 1
  by_cases h : 1 - Int.fract t ≤ Int.fract x
  · rw [if_pos h, Int.floor_eq_iff]
    norm_num
    constructor
    · linarith
    · linarith [Int.fract_lt_one x, Int.fract_lt_one t]
  · rw [if_neg h, Int.floor_eq_iff]
    norm_num
    constructor
    · linarith [Int.fract_nonneg x, Int.fract_nonneg t]
    · linarith [Int.fract_lt_one x, Int.fract_nonneg t, lt_of_not_ge h]

/-- The breakpoint of window length `m`. -/
noncomputable def phaseBreakpoint (alpha : Real) (m : Nat) : Real :=
  1 - Int.fract ((m : Real) * alpha)

/-- NOVEL STEP 2: agreeing on all breakpoint sides gives an equal count profile. -/
theorem phaseFloor_eq_of_sides {alpha x y : Real} (hx : x ∈ Ico (0 : Real) 1)
    (hy : y ∈ Ico (0 : Real) 1) {n : Nat}
    (hside : ∀ m ≤ n, (phaseBreakpoint alpha m ≤ x ↔ phaseBreakpoint alpha m ≤ y))
    {m : Nat} (hm : m ≤ n) :
    phaseFloor alpha x m = phaseFloor alpha y m := by
  have hfx : Int.fract x = x := Int.fract_eq_self.mpr hx
  have hfy : Int.fract y = y := Int.fract_eq_self.mpr hy
  simp only [phaseFloor]
  rw [show x + (m : Real) * alpha = Int.fract x + (m : Real) * alpha by rw [hfx],
    show y + (m : Real) * alpha = Int.fract y + (m : Real) * alpha by rw [hfy],
    floor_fract_add_indicator, floor_fract_add_indicator, hfx, hfy]
  have h := hside m hm
  simp only [phaseBreakpoint] at h
  by_cases hxb : 1 - Int.fract ((m : Real) * alpha) ≤ x
  · rw [if_pos hxb, if_pos (h.mp hxb)]
  · rw [if_neg hxb, if_neg (fun hc => hxb (h.mpr hc))]

/-- NOVEL STEP 3 (cross-intercept): equal phase cells give literally equal factors. -/
theorem lowerMechanicalFactor_eq_of_sides {alpha rho sigma : Real} {n i j : Nat}
    (hside : ∀ m ≤ n,
      (phaseBreakpoint alpha m ≤ Int.fract (rho + (i : Real) * alpha) ↔
        phaseBreakpoint alpha m ≤ Int.fract (sigma + (j : Real) * alpha))) :
    lowerMechanicalFactor alpha rho n i = lowerMechanicalFactor alpha sigma n j := by
  have hx : Int.fract (rho + (i : Real) * alpha) ∈ Ico (0 : Real) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hy : Int.fract (sigma + (j : Real) * alpha) ∈ Ico (0 : Real) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  unfold lowerMechanicalFactor
  congr 1
  funext k
  have hk : (k : Nat) < n := k.isLt
  have hb := phaseFloor_eq_of_sides hx hy hside (Nat.le_of_lt hk)
  have hb' := phaseFloor_eq_of_sides hx hy hside (Nat.succ_le_of_lt hk)
  have hl := letter_eq_phaseFloor_sub alpha rho i k
  have hr := letter_eq_phaseFloor_sub alpha sigma j k
  simp only [lowerMechanicalWord]
  rw [hl, hr, hb, hb']

/-- A right-stable cell above `x`: no breakpoint of index at most `n` is crossed. -/
theorem exists_stable_right {alpha x : Real} (hx : x < 1) (n : Nat) :
    ∃ b : Real, x < b ∧ b ≤ 1 ∧ ∀ y ∈ Ioo x b, ∀ m ≤ n,
      (phaseBreakpoint alpha m ≤ x ↔ phaseBreakpoint alpha m ≤ y) := by
  classical
  let points : Finset Real := (Finset.range (n + 1)).image (phaseBreakpoint alpha)
  let above : Finset Real := points.filter (x < ·)
  have hzero : phaseBreakpoint alpha 0 = 1 := by
    simp [phaseBreakpoint]
  have habove : above.Nonempty := by
    refine ⟨phaseBreakpoint alpha 0, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos n), rfl⟩
    · rw [hzero]; exact hx
  set c := above.min' habove with hc
  have hcAbove : c ∈ above := above.min'_mem habove
  have hxc : x < c := (Finset.mem_filter.mp hcAbove).2
  have hc1 : c ≤ 1 := by
    obtain ⟨m, _, hmc⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hcAbove).1
    rw [← hmc, phaseBreakpoint]
    linarith [Int.fract_nonneg ((m : Real) * alpha)]
  refine ⟨(x + c) / 2, by linarith, by linarith, ?_⟩
  intro y hy m hm
  constructor
  · intro hmx
    exact hmx.trans hy.1.le
  · intro hmy
    by_contra hmx
    have hxm : x < phaseBreakpoint alpha m := lt_of_not_ge hmx
    have hmAbove : phaseBreakpoint alpha m ∈ above :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (by omega), rfl⟩, hxm⟩
    have hcle : c ≤ phaseBreakpoint alpha m := above.min'_le _ hmAbove
    have hyc : y < c := hy.2.trans_le (by linarith)
    exact (not_le_of_gt hyc) (hcle.trans hmy)

/-- Irrational rotation orbits meet every nondegenerate subinterval of the unit interval. -/
theorem exists_phase_mem_Ioo {alpha rho a b : Real} (halpha : Irrational alpha)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ i : Nat, Int.fract (rho + (i : Real) * alpha) ∈ Ioo a b := by
  have hz : DenseRange (fun z : Int => z • ((alpha : Real) : AddCircle (1 : Real))) := by
    rw [AddCircle.denseRange_zsmul_coe_iff]
    simpa using halpha
  have hn : DenseRange (fun q : Nat => q • ((alpha : Real) : AddCircle (1 : Real))) :=
    denseRange_zsmul_iff_nsmul.mp hz
  let translate : AddCircle (1 : Real) → AddCircle (1 : Real) :=
    fun x => (rho : AddCircle (1 : Real)) + x
  have htranslate : Function.Surjective translate := by
    intro y
    exact ⟨y - (rho : AddCircle (1 : Real)), by simp [translate]⟩
  have htranslate_continuous : Continuous translate := by
    dsimp [translate]
    fun_prop
  have htranslated : DenseRange (fun q : Nat =>
      (rho : AddCircle (1 : Real)) + q • ((alpha : Real) : AddCircle (1 : Real))) := by
    simpa [translate, Function.comp_def] using
      htranslate.denseRange.comp hn htranslate_continuous
  let U : Set (AddCircle (1 : Real)) :=
    ((fun x : Real => (x : AddCircle (1 : Real))) '' Ioo a b)
  have hUopen : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hUne : U.Nonempty := by
    refine ⟨(((a + b) / 2 : Real) : AddCircle (1 : Real)), (a + b) / 2, ?_, rfl⟩
    constructor <;> linarith
  obtain ⟨q, x, hx, hxq⟩ := htranslated.exists_mem_open hUopen hUne
  have hfract_mem : Int.fract (rho + (q : Real) * alpha) ∈ Ico (0 : Real) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hx_mem : x ∈ Ico (0 : Real) 1 := ⟨(ha.trans_lt hx.1).le, hx.2.trans_le hb⟩
  have hfract : Int.fract (rho + (q : Real) * alpha) = x := by
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : Real)) (p := (1 : Real))
      (by simpa only [zero_add] using hfract_mem)
      (by simpa only [zero_add] using hx_mem)).mp
    rw [AddCircle.coe_fract]
    simpa [nsmul_eq_mul] using hxq.symm
  exact ⟨q, by simpa [hfract] using hx⟩

/-- Every factor of one intercept occurs in every other intercept of the same slope. -/
theorem lowerMechanicalFactor_mem_factorSet {alpha : Real} (halpha : Irrational alpha)
    (rho sigma : Real) (n j : Nat) :
    lowerMechanicalFactor alpha sigma n j ∈ lowerMechanicalFactorSet alpha rho n := by
  set x := Int.fract (sigma + (j : Real) * alpha) with hxdef
  have hx0 : 0 ≤ x := Int.fract_nonneg _
  have hx1 : x < 1 := Int.fract_lt_one _
  obtain ⟨b, hxb, hb1, hstable⟩ := exists_stable_right (alpha := alpha) hx1 n
  obtain ⟨i, hi⟩ := exists_phase_mem_Ioo (rho := rho) halpha hx0 hxb hb1
  refine mem_lowerMechanicalFactorSet.mpr ⟨i, ?_⟩
  refine (lowerMechanicalFactor_eq_of_sides (rho := sigma) (sigma := rho) (i := j) (j := i) ?_)
  intro m hm
  exact hstable _ hi m hm

/-- The prefix language of one intercept sits inside the subshift of any other. -/
theorem mem_wordSubshift_of_intercept {alpha : Real} (halpha : Irrational alpha)
    (rho sigma : Real) :
    lowerMechanicalWord alpha sigma ∈ wordSubshift (lowerMechanicalWord alpha rho) := by
  intro n
  obtain ⟨i, hi⟩ :=
    mem_lowerMechanicalFactorSet.mp (lowerMechanicalFactor_mem_factorSet halpha rho sigma n 0)
  refine mem_wordFactorSet.mpr ⟨i, ?_⟩
  have hfun : (fun k : Fin n => lowerMechanicalWord alpha sigma (0 + k)) =
      fun k : Fin n => lowerMechanicalWord alpha rho (i + k) :=
    List.ofFn_inj.mp hi
  funext k
  simpa [wordFactor] using congrFun hfun k

/-- INTERCEPT INDEPENDENCE: one canonical Sturmian subshift per irrational slope. -/
theorem wordSubshift_intercept_independent {alpha : Real} (halpha0 : 0 ≤ alpha)
    (halpha1 : alpha < 1) (halpha : Irrational alpha) (rho sigma : Real) :
    wordSubshift (lowerMechanicalWord alpha sigma) =
      wordSubshift (lowerMechanicalWord alpha rho) :=
  wordSubshift_eq_of_mem_mechanical_wordSubshift halpha0 halpha1 halpha
    (mem_wordSubshift_of_intercept halpha rho sigma)

/-- The factor language itself is intercept-free. -/
theorem lowerMechanicalFactorSet_intercept_independent {alpha : Real}
    (halpha : Irrational alpha) (rho sigma : Real) (n : Nat) :
    lowerMechanicalFactorSet alpha rho n = lowerMechanicalFactorSet alpha sigma n := by
  ext w
  constructor
  · intro hw
    obtain ⟨i, rfl⟩ := mem_lowerMechanicalFactorSet.mp hw
    exact lowerMechanicalFactor_mem_factorSet halpha sigma rho n i
  · intro hw
    obtain ⟨i, rfl⟩ := mem_lowerMechanicalFactorSet.mp hw
    exact lowerMechanicalFactor_mem_factorSet halpha rho sigma n i

/-- CLASSIFICATION: two mechanical subshifts coincide exactly when their slopes do. -/
theorem wordSubshift_eq_iff_slope_eq {alpha beta : Real} (halpha0 : 0 ≤ alpha)
    (halpha1 : alpha < 1) (halpha : Irrational alpha) (hbeta0 : 0 ≤ beta)
    (hbeta1 : beta < 1) (rho sigma : Real) :
    wordSubshift (lowerMechanicalWord alpha rho) =
      wordSubshift (lowerMechanicalWord beta sigma) ↔ alpha = beta := by
  constructor
  · intro hsub
    exact mechanical_wordSubshift_slope_eq_of_eq halpha0 halpha1 hbeta0 hbeta1 hsub
  · rintro rfl
    exact (wordSubshift_intercept_independent halpha0 halpha1 halpha rho sigma).symm

#print axioms letter_eq_phaseFloor_sub
#print axioms lowerMechanicalFactor_eq_of_sides
#print axioms lowerMechanicalFactor_mem_factorSet
#print axioms wordSubshift_intercept_independent
#print axioms lowerMechanicalFactorSet_intercept_independent
#print axioms wordSubshift_eq_iff_slope_eq

end

end D5.S1.Words.Complexity.MechanicalSubshiftIntercept
