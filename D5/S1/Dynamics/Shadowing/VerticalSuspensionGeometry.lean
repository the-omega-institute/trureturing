/- GID: D5/S1/Dynamics/Shadowing/VerticalSuspensionGeometry
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/VerticalSuspensionGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Artanh, mathlib/module/Mathlib.Topology.Constructions]
   utility: none
   digest: Signed quotient infrastructure for the full integer vertical suspension crossing selector. -/

import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic
/-! The quotient carrier and its vertical phase homeomorphism. -/

noncomputable section

open Set Function Topology Filter

namespace D5.S1.Dynamics.Shadowing.VerticalSuspensionSelector

abbrev Height := Set.Icc (-1 : ℝ) 1

/-- Only an end face forgets its K-coordinate. -/
def suspensionSetoid (K : Type*) : Setoid (K × Height) where
  r p q := p.2 = q.2 ∧ ((p.2 : ℝ) = -1 ∨ (p.2 : ℝ) = 1 ∨ p.1 = q.1)
  iseqv := {
    refl := fun _ => ⟨rfl, Or.inr (Or.inr rfl)⟩
    symm := by
      rintro p q ⟨hv, h⟩
      refine ⟨hv.symm, ?_⟩
      rcases h with h | h | h
      · exact Or.inl (hv ▸ h)
      · exact Or.inr (Or.inl (hv ▸ h))
      · exact Or.inr (Or.inr h.symm)
    trans := by
      rintro p q r ⟨hpq, h⟩ ⟨hqr, h'⟩
      refine ⟨hpq.trans hqr, ?_⟩
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · rcases h' with h' | h' | h'
        · exact Or.inl (hpq.symm ▸ h')
        · exact Or.inr (Or.inl (hpq.symm ▸ h'))
        · exact Or.inr (Or.inr (h.trans h')) }

/-- Native quotient, carrying the quotient topology, with arbitrary K. -/
abbrev Suspension (K : Type*) [TopologicalSpace K] := Quotient (suspensionSetoid K)

variable {K : Type*} [TopologicalSpace K]

def point (u : K) (v : Height) : Suspension K := Quotient.mk _ (u, v)

def height : Suspension K → Height := Quotient.lift Prod.snd (fun _ _ h => h.1)

theorem height_point (u : K) (v : Height) : height (point u v) = v := rfl

theorem continuous_point : Continuous (fun p : K × Height => point p.1 p.2) :=
  continuous_quotient_mk'

theorem continuous_height : Continuous (height : Suspension K → Height) :=
  continuous_snd.quotient_lift _

theorem point_eq_point (u v : K) (a b : Height) :
    point u a = point v b ↔ a = b ∧ ((a : ℝ) = -1 ∨ (a : ℝ) = 1 ∨ u = v) :=
  Quotient.eq

theorem point_bottom (u v : K) :
    point u ⟨-1, by constructor <;> norm_num⟩ = point v ⟨-1, by constructor <;> norm_num⟩ :=
  (point_eq_point _ _ _ _).2 ⟨rfl, Or.inl rfl⟩

theorem point_top (u v : K) :
    point u ⟨1, by constructor <;> norm_num⟩ = point v ⟨1, by constructor <;> norm_num⟩ :=
  (point_eq_point _ _ _ _).2 ⟨rfl, Or.inr (Or.inl rfl)⟩

theorem point_injective (a : Height) (ha : (a : ℝ) ∈ Ioo (-1 : ℝ) 1) :
    Injective (fun u : K => point u a) := by
  intro u v h
  rcases (point_eq_point _ _ _ _).1 h with ⟨_, h | h | h⟩
  · linarith [ha.1]
  · linarith [ha.2]
  · exact h

/-- A label is read only on the open interior of the quotient. -/
abbrev Interior := {z : Suspension K // (height z : ℝ) ∈ Ioo (-1 : ℝ) 1}

def label (z : Interior (K := K)) : K := z.1.out.1

theorem point_label (z : Interior (K := K)) :
    point (label z) (height z.1) = z.1 := by
  have ho := Quotient.out_eq z.1
  have hh : z.1.out.2 = height z.1 := congrArg height ho
  change point z.1.out.1 z.1.out.2 = z.1 at ho
  rw [hh] at ho
  exact ho

theorem label_point (u : K) (a : Height) (ha : (a : ℝ) ∈ Ioo (-1 : ℝ) 1) :
    label ⟨point u a, ha⟩ = u := by
  apply point_injective a ha
  exact point_label ⟨point u a, ha⟩

theorem continuous_label : Continuous (label : Interior (K := K) → K) := by
  let U : Set (Suspension K) := {z | (height z : ℝ) ∈ Ioo (-1 : ℝ) 1}
  have hU : IsOpen U := isOpen_Ioo.preimage (continuous_subtype_val.comp continuous_height)
  have hq := (isQuotientMap_quotient_mk' (s := suspensionSetoid K)).restrictPreimage_isOpen hU
  apply hq.continuous_iff.mpr
  have he : (label ∘ U.restrictPreimage (@Quotient.mk' (K × Height) (suspensionSetoid K))) =
      fun p => p.1.1 := by
    funext p
    exact label_point p.1.1 p.1.2 p.2
  rw [he]
  exact continuous_fst.comp continuous_subtype_val

def mobius (c v : ℝ) : ℝ := (v + c) / (1 + c * v)

theorem mobius_den_pos {c : ℝ} (hc : c ∈ Ioo (-1 : ℝ) 1) (v : Height) :
    0 < 1 + c * (v : ℝ) := by
  have ha : |c| < 1 := abs_lt.mpr hc
  have hv : |(v : ℝ)| ≤ 1 := abs_le.mpr v.2
  have hm : |c * (v : ℝ)| < 1 := by
    rw [abs_mul]
    calc
      |c| * |(v : ℝ)| ≤ |c| * 1 := mul_le_mul_of_nonneg_left hv (abs_nonneg _)
      _ < 1 := by simpa using ha
  linarith [(abs_lt.mp hm).1]

def mobiusHeight (c : ℝ) (hc : c ∈ Ioo (-1 : ℝ) 1) (v : Height) : Height :=
  ⟨mobius c v, by
    have hd := mobius_den_pos hc v
    constructor
    · apply (le_div_iff₀ hd).2
      have hp := mul_nonneg (by linarith [hc.1] : 0 ≤ 1 + c)
        (by linarith [v.2.1] : 0 ≤ 1 + (v : ℝ))
      nlinarith
    · apply (div_le_iff₀ hd).2
      have hp := mul_nonneg (by linarith [hc.2] : 0 ≤ 1 - c)
        (by linarith [v.2.2] : 0 ≤ 1 - (v : ℝ))
      nlinarith⟩

theorem continuous_mobiusHeight (c : ℝ) (hc : c ∈ Ioo (-1 : ℝ) 1) :
    Continuous (mobiusHeight c hc) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.add continuous_const).div
    (continuous_const.add (continuous_const.mul continuous_subtype_val))
    (fun v => ne_of_gt (mobius_den_pos hc v))

theorem mobiusHeight_bottom (c : ℝ) (hc : c ∈ Ioo (-1 : ℝ) 1) :
    mobiusHeight c hc ⟨-1, by constructor <;> norm_num⟩ =
      ⟨-1, by constructor <;> norm_num⟩ := by
  apply Subtype.ext
  dsimp [mobiusHeight, mobius]
  apply (div_eq_iff (by linarith [hc.2] : 1 + c * -1 ≠ 0)).2
  ring

theorem mobiusHeight_top (c : ℝ) (hc : c ∈ Ioo (-1 : ℝ) 1) :
    mobiusHeight c hc ⟨1, by constructor <;> norm_num⟩ =
      ⟨1, by constructor <;> norm_num⟩ := by
  apply Subtype.ext
  dsimp [mobiusHeight, mobius]
  apply (div_eq_iff (by linarith [hc.1] : 1 + c * 1 ≠ 0)).2
  ring

theorem mobiusHeight_inverse (c : ℝ) (hc : c ∈ Ioo (-1 : ℝ) 1) (v : Height) :
    mobiusHeight (-c) (by constructor <;> linarith [hc.1, hc.2]) (mobiusHeight c hc v) = v := by
  apply Subtype.ext
  have hd := ne_of_gt (mobius_den_pos hc v)
  have hi := ne_of_gt (mobius_den_pos
    (show -c ∈ Ioo (-1 : ℝ) 1 by constructor <;> linarith [hc.1, hc.2])
    (mobiusHeight c hc v))
  apply (div_eq_iff hi).2
  change ((v : ℝ) + c) / (1 + c * v) + -c =
    (v : ℝ) * (1 + -c * (((v : ℝ) + c) / (1 + c * v)))

  nlinarith only [div_mul_cancel₀ ((v : ℝ) + c) hd]

/-- The exact height homeomorphism (v+tanh(1))/(1+tanh(1)v). -/
def verticalHeight : Height ≃ₜ Height where
  toFun := mobiusHeight (Real.tanh 1) ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
  invFun := mobiusHeight (-Real.tanh 1) (by
    constructor <;> linarith [Real.neg_one_lt_tanh (1 : ℝ), Real.tanh_lt_one (1 : ℝ)])
  left_inv := mobiusHeight_inverse _ _
  right_inv v := by simpa using mobiusHeight_inverse (-Real.tanh 1) _ v
  continuous_toFun := continuous_mobiusHeight _ _
  continuous_invFun := continuous_mobiusHeight _ _

theorem verticalHeight_relation (p q : K × Height)
    (h : (suspensionSetoid K).r p q) :
    (suspensionSetoid K).r (p.1, verticalHeight p.2) (q.1, verticalHeight q.2) := by
  refine ⟨congrArg verticalHeight h.1, ?_⟩
  rcases h.2 with h | h | h
  · left
    have he : p.2 = ⟨-1, by constructor <;> norm_num⟩ := Subtype.ext h
    rw [he]
    exact congrArg (fun x : Height => (x : ℝ)) (mobiusHeight_bottom _ (by
      constructor <;> linarith [Real.neg_one_lt_tanh (1 : ℝ), Real.tanh_lt_one (1 : ℝ)]))
  · right; left
    have he : p.2 = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext h
    rw [he]
    exact congrArg (fun x : Height => (x : ℝ)) (mobiusHeight_top _ (by
      constructor <;> linarith [Real.neg_one_lt_tanh (1 : ℝ), Real.tanh_lt_one (1 : ℝ)]))
  · exact Or.inr (Or.inr h)

theorem verticalHeight_symm_relation (p q : K × Height)
    (h : (suspensionSetoid K).r p q) :
    (suspensionSetoid K).r (p.1, verticalHeight.symm p.2)
      (q.1, verticalHeight.symm q.2) := by
  refine ⟨congrArg verticalHeight.symm h.1, ?_⟩
  rcases h.2 with h | h | h
  · left
    have he : p.2 = ⟨-1, by constructor <;> norm_num⟩ := Subtype.ext h
    rw [he]
    exact congrArg (fun x : Height => (x : ℝ)) (mobiusHeight_bottom _ (by
      constructor <;> linarith [Real.neg_one_lt_tanh (1 : ℝ), Real.tanh_lt_one (1 : ℝ)]))
  · right; left
    have he : p.2 = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext h
    rw [he]
    exact congrArg (fun x : Height => (x : ℝ)) (mobiusHeight_top _ (by
      constructor <;> linarith [Real.neg_one_lt_tanh (1 : ℝ), Real.tanh_lt_one (1 : ℝ)]))
  · exact Or.inr (Or.inr h)

/-- Vertical dynamics descends to the actual suspension quotient. -/
def vertical : Suspension K ≃ₜ Suspension K where
  toFun := Quotient.map' (fun p => (p.1, verticalHeight p.2)) verticalHeight_relation
  invFun := Quotient.map' (fun p => (p.1, verticalHeight.symm p.2))
    verticalHeight_symm_relation
  left_inv := by
    intro z
    induction z using Quotient.inductionOn with | _ p =>
      change point p.1 (verticalHeight.symm (verticalHeight p.2)) = point p.1 p.2
      rw [verticalHeight.symm_apply_apply]
  right_inv := by
    intro z
    induction z using Quotient.inductionOn with | _ p =>
      change point p.1 (verticalHeight (verticalHeight.symm p.2)) = point p.1 p.2
      rw [verticalHeight.apply_symm_apply]
  continuous_toFun := (continuous_fst.prodMk
    (verticalHeight.continuous.comp continuous_snd)).quotient_map' _
  continuous_invFun := (continuous_fst.prodMk
    (verticalHeight.symm.continuous.comp continuous_snd)).quotient_map' _

theorem continuous_tanh : Continuous Real.tanh := by
  have he : Real.tanh = fun t => Real.sinh t / Real.cosh t :=
    funext (fun t => Real.tanh_eq_sinh_div_cosh t)
  rw [he]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun t => ne_of_gt (Real.cosh_pos t))

def phasePoint (u : K) (t : ℝ) : Suspension K :=
  point u ⟨Real.tanh t, (Real.abs_tanh_lt_one t).le |> abs_le.mp⟩

theorem continuous_phasePoint : Continuous (fun p : K × ℝ => phasePoint p.1 p.2) :=
  continuous_point.comp (continuous_fst.prodMk
    ((continuous_tanh.comp continuous_snd).subtype_mk _))

theorem strictMono_tanh : StrictMono Real.tanh := by
  intro a b hab
  apply (Real.artanh_lt_artanh_iff
    ⟨Real.neg_one_lt_tanh a, Real.tanh_lt_one a⟩
    ⟨Real.neg_one_lt_tanh b, Real.tanh_lt_one b⟩).mp
  simpa only [Real.artanh_tanh] using hab

theorem vertical_phasePoint (u : K) (t : ℝ) :
    vertical (phasePoint u t) = phasePoint u (t + 1) := by
  change point u (verticalHeight _) = point u _
  congr 1
  apply Subtype.ext
  change mobius (Real.tanh 1) (Real.tanh t) = Real.tanh (t + 1)
  have hd := ne_of_gt (mobius_den_pos
    ⟨Real.neg_one_lt_tanh (1 : ℝ), Real.tanh_lt_one (1 : ℝ)⟩
    ⟨Real.tanh t, ⟨(Real.neg_one_lt_tanh t).le, (Real.tanh_lt_one t).le⟩⟩)
  apply (div_eq_iff hd).2
  simp only [Real.tanh_eq_sinh_div_cosh, Real.sinh_add, Real.cosh_add]
  have hsum : Real.cosh t * Real.cosh 1 + Real.sinh t * Real.sinh 1 ≠ 0 := by
    rw [← Real.cosh_add]
    exact ne_of_gt (Real.cosh_pos _)
  field_simp [ne_of_gt (Real.cosh_pos t), ne_of_gt (Real.cosh_pos (1 : ℝ)), hsum]
  <;> ring


end D5.S1.Dynamics.Shadowing.VerticalSuspensionSelector
