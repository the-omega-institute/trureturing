/- GID: D5/S1/Dynamics/Shadowing/VerticalSuspensionSelector
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/VerticalSuspensionSelector
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

/-!
The carrier is the actual quotient of K × [-1,1], with the two end faces
collapsed separately. Integer histories below have every original closed
link constraint. No finite window or canonical family replaces that domain.
The intended selector is the crossing construction in the supplied public
mathematical source; this module does not assert LEC implies ANR.
-/

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

private theorem height_point (u : K) (v : Height) : height (point u v) = v := rfl

private theorem continuous_point : Continuous (fun p : K × Height => point p.1 p.2) :=
  continuous_quotient_mk'

private theorem continuous_height : Continuous (height : Suspension K → Height) :=
  continuous_snd.quotient_lift _

private theorem point_eq_point (u v : K) (a b : Height) :
    point u a = point v b ↔ a = b ∧ ((a : ℝ) = -1 ∨ (a : ℝ) = 1 ∨ u = v) :=
  Quotient.eq

private theorem point_bottom (u v : K) :
    point u ⟨-1, by constructor <;> norm_num⟩ = point v ⟨-1, by constructor <;> norm_num⟩ :=
  (point_eq_point _ _ _ _).2 ⟨rfl, Or.inl rfl⟩

private theorem point_top (u v : K) :
    point u ⟨1, by constructor <;> norm_num⟩ = point v ⟨1, by constructor <;> norm_num⟩ :=
  (point_eq_point _ _ _ _).2 ⟨rfl, Or.inr (Or.inl rfl)⟩

private theorem point_injective (a : Height) (ha : (a : ℝ) ∈ Ioo (-1 : ℝ) 1) :
    Injective (fun u : K => point u a) := by
  intro u v h
  rcases (point_eq_point _ _ _ _).1 h with ⟨_, h | h | h⟩
  · linarith [ha.1]
  · linarith [ha.2]
  · exact h

/-- A label is read only on the open interior of the quotient. -/
abbrev Interior := {z : Suspension K // (height z : ℝ) ∈ Ioo (-1 : ℝ) 1}

def label (z : Interior (K := K)) : K := z.1.out.1

private theorem point_label (z : Interior (K := K)) :
    point (label z) (height z.1) = z.1 := by
  have ho := Quotient.out_eq z.1
  have hh : z.1.out.2 = height z.1 := congrArg height ho
  change point z.1.out.1 z.1.out.2 = z.1 at ho
  rw [hh] at ho
  exact ho

private theorem label_point (u : K) (a : Height) (ha : (a : ℝ) ∈ Ioo (-1 : ℝ) 1) :
    label ⟨point u a, ha⟩ = u := by
  apply point_injective a ha
  exact point_label ⟨point u a, ha⟩

private theorem continuous_label : Continuous (label : Interior (K := K) → K) := by
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

private def mobius (c v : ℝ) : ℝ := (v + c) / (1 + c * v)

private theorem mobius_den_pos {c : ℝ} (hc : c ∈ Ioo (-1 : ℝ) 1) (v : Height) :
    0 < 1 + c * (v : ℝ) := by
  have ha : |c| < 1 := abs_lt.mpr hc
  have hv : |(v : ℝ)| ≤ 1 := abs_le.mpr v.2
  have hm : |c * (v : ℝ)| < 1 := by
    rw [abs_mul]
    calc
      |c| * |(v : ℝ)| ≤ |c| * 1 := mul_le_mul_of_nonneg_left hv (abs_nonneg _)
      _ < 1 := by simpa using ha
  linarith [(abs_lt.mp hm).1]

private def mobiusHeight (c : ℝ) (hc : c ∈ Ioo (-1 : ℝ) 1) (v : Height) : Height :=
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

private theorem continuous_mobiusHeight (c : ℝ) (hc : c ∈ Ioo (-1 : ℝ) 1) :
    Continuous (mobiusHeight c hc) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.add continuous_const).div
    (continuous_const.add (continuous_const.mul continuous_subtype_val))
    (fun v => ne_of_gt (mobius_den_pos hc v))

private theorem mobiusHeight_bottom (c : ℝ) (hc : c ∈ Ioo (-1 : ℝ) 1) :
    mobiusHeight c hc ⟨-1, by constructor <;> norm_num⟩ =
      ⟨-1, by constructor <;> norm_num⟩ := by
  apply Subtype.ext
  dsimp [mobiusHeight, mobius]
  apply (div_eq_iff (by linarith [hc.2] : 1 + c * -1 ≠ 0)).2
  ring

private theorem mobiusHeight_top (c : ℝ) (hc : c ∈ Ioo (-1 : ℝ) 1) :
    mobiusHeight c hc ⟨1, by constructor <;> norm_num⟩ =
      ⟨1, by constructor <;> norm_num⟩ := by
  apply Subtype.ext
  dsimp [mobiusHeight, mobius]
  apply (div_eq_iff (by linarith [hc.1] : 1 + c * 1 ≠ 0)).2
  ring

private theorem mobiusHeight_inverse (c : ℝ) (hc : c ∈ Ioo (-1 : ℝ) 1) (v : Height) :
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

private theorem verticalHeight_relation (p q : K × Height)
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

private theorem verticalHeight_symm_relation (p q : K × Height)
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

private theorem continuous_tanh : Continuous Real.tanh := by
  have he : Real.tanh = fun t => Real.sinh t / Real.cosh t :=
    funext (fun t => Real.tanh_eq_sinh_div_cosh t)
  rw [he]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun t => ne_of_gt (Real.cosh_pos t))

def phasePoint (u : K) (t : ℝ) : Suspension K :=
  point u ⟨Real.tanh t, (Real.abs_tanh_lt_one t).le |> abs_le.mp⟩

private theorem continuous_phasePoint : Continuous (fun p : K × ℝ => phasePoint p.1 p.2) :=
  continuous_point.comp (continuous_fst.prodMk
    ((continuous_tanh.comp continuous_snd).subtype_mk _))

private theorem strictMono_tanh : StrictMono Real.tanh := by
  intro a b hab
  apply (Real.artanh_lt_artanh_iff
    ⟨Real.neg_one_lt_tanh a, Real.tanh_lt_one a⟩
    ⟨Real.neg_one_lt_tanh b, Real.tanh_lt_one b⟩).mp
  simpa only [Real.artanh_tanh] using hab

private theorem vertical_phasePoint (u : K) (t : ℝ) :
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

/-- The three identities refer to one continuous connector on one open W. -/
structure LocalEquiconnection (K : Type*) [TopologicalSpace K] where
  domain : Set (K × K)
  isOpen_domain : IsOpen domain
  diagonal : ∀ u, (u, u) ∈ domain
  connect : domain × Set.Icc (0 : ℝ) 1 → K
  continuous_connect : Continuous connect
  left : ∀ p : domain, connect (p, ⟨0, by constructor <;> norm_num⟩) = p.1.1
  right : ∀ p : domain, connect (p, ⟨1, by constructor <;> norm_num⟩) = p.1.2
  refl : ∀ u t, connect (⟨(u, u), diagonal u⟩, t) = u

/-- All integers and non-strict errors, with the inherited full product topology. -/
abbrev ClosedPseudoOrbit {X : Type*} [PseudoMetricSpace X] (f : X → X) (δ : ℝ) :=
  {x : ℤ → X // ∀ j : ℤ, dist (f (x j)) (x (j + 1)) ≤ δ}

private theorem closed_pseudoOrbit {X : Type*} [PseudoMetricSpace X]
    {f : X → X} (hf : Continuous f) (δ : ℝ) :
    IsClosed {x : ℤ → X | ∀ j : ℤ, dist (f (x j)) (x (j + 1)) ≤ δ} := by
  simp only [ofPred_forall]
  apply isClosed_iInter (fun j => ?_)
  exact isClosed_le ((hf.comp (continuous_apply j)).dist (continuous_apply (j + 1)))
    continuous_const

/-- Translation by any integer stays on exactly the same closed domain. -/
def shift {X : Type*} [PseudoMetricSpace X] (f : X → X) (δ : ℝ) (n : ℤ) :
    ClosedPseudoOrbit f δ ≃ₜ ClosedPseudoOrbit f δ where
  toFun x := ⟨fun j => x.1 (j + n), fun j => by
    simpa only [add_assoc, add_comm, add_left_comm] using x.2 (j + n)⟩
  invFun x := ⟨fun j => x.1 (j - n), fun j => by
    simpa only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using x.2 (j - n)⟩
  left_inv x := by ext j; simp
  right_inv x := by ext j; simp
  continuous_toFun := (continuous_pi (fun j =>
    (continuous_apply (j + n)).comp
      (continuous_subtype_val : Continuous (fun x : ClosedPseudoOrbit f δ => x.1)))).subtype_mk _
  continuous_invFun := (continuous_pi (fun j =>
    (continuous_apply (j - n)).comp
      (continuous_subtype_val : Continuous (fun x : ClosedPseudoOrbit f δ => x.1)))).subtype_mk _

/-- The weak crossing convention retains both charts at a zero seam. -/
def Crossing (v : ℤ → ℝ) (j : ℤ) : Prop := v j ≤ 0 ∧ 0 ≤ v (j + 1)

private def ForwardSign (v : ℤ → ℝ) : Prop := ∀ j, 0 ≤ v j → 0 < v (j + 1)

private theorem nonnegative_after {v : ℤ → ℝ} (hv : ForwardSign v)
    {i j : ℤ} (hij : i ≤ j) (hi : 0 ≤ v i) : 0 ≤ v j := by
  have hn : ∀ n : ℕ, 0 ≤ v (i + n) := by
    intro n
    induction n with
    | zero => simpa using hi
    | succ n ih => simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using (hv _ ih).le
  have he : i + ((j - i).toNat : ℤ) = j := by
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hij)]
    ring
  simpa only [he] using hn (j - i).toNat

private theorem positive_after {v : ℤ → ℝ} (hv : ForwardSign v)
    {i j : ℤ} (hij : i < j) (hi : 0 ≤ v i) : 0 < v j := by
  have hp := hv (j - 1) (nonnegative_after hv (show i ≤ j - 1 by omega) hi)
  simpa using hp

private theorem negative_before {v : ℤ → ℝ} (hv : ForwardSign v)
    {i j : ℤ} (hij : i < j) (hj : v j ≤ 0) : v i < 0 := by
  by_contra hi
  exact (not_lt_of_ge hj) (positive_after hv hij (le_of_not_gt hi))

private theorem crossing_classification {v : ℤ → ℝ} (hv : ForwardSign v) :
    (∀ j, v j < 0) ∨ (∀ j, 0 < v j) ∨ ∃ j, Crossing v j := by
  classical
  by_cases hn : ∀ j, v j < 0
  · exact Or.inl hn
  right
  by_cases hp : ∀ j, 0 < v j
  · exact Or.inl hp
  right
  push_neg at hn hp
  obtain ⟨s, hs⟩ := hn
  obtain ⟨r, hr⟩ := hp
  by_cases hz : v r = 0
  · exact ⟨r, hz.le, (hv r hz.ge).le⟩
  have hr' : v r < 0 := lt_of_le_of_ne hr hz
  obtain ⟨k, hk, hmin⟩ := Int.exists_least_of_bdd
    (P := fun k => 0 ≤ v k)
    ⟨r, by
      intro k hk
      by_contra hkr
      have := nonnegative_after hv (show k ≤ r by omega) hk
      linarith⟩ ⟨s, hs⟩
  refine ⟨k - 1, ?_, by simpa using hk⟩
  have hneg : v (k - 1) < 0 := by
    by_contra h
    have := hmin (k - 1) (le_of_not_gt h)
    omega
  exact hneg.le

private theorem crossing_separation {v : ℤ → ℝ} (hv : ForwardSign v)
    {i j : ℤ} (hi : Crossing v i) (hj : Crossing v j) :
    i = j ∨ (i + 1 = j ∧ v j = 0) ∨ (j + 1 = i ∧ v i = 0) := by
  have hupper : j ≤ i + 1 := by
    by_contra h
    have := positive_after hv (show i + 1 < j by omega) hi.2
    linarith [hj.1]
  have hlower : i ≤ j + 1 := by
    by_contra h
    have := positive_after hv (show j + 1 < i by omega) hj.2
    linarith [hi.1]
  rcases lt_trichotomy i j with h | h | h
  · right; left
    have he : i + 1 = j := by omega
    exact ⟨he, le_antisymm hj.1 (he ▸ hi.2)⟩
  · exact Or.inl h
  · right; right
    have he : j + 1 = i := by omega
    exact ⟨he, le_antisymm hi.1 (he ▸ hj.2)⟩

private theorem crossing_local_range {v : ℤ → ℝ} (hv : ForwardSign v)
    {a b j : ℤ} (ha : v a < 0) (hb : 0 < v b) (hj : Crossing v j) :
    a ≤ j ∧ j < b := by
  constructor
  · by_contra h
    have := nonnegative_after hv (show j + 1 ≤ a by omega) hj.2
    linarith
  · by_contra h
    have := nonnegative_after hv (show b ≤ j by omega) hb.le
    rcases eq_or_lt_of_le (show b ≤ j by omega) with he | he
    · subst j
      linarith [hj.1]
    · have := positive_after hv he hb.le
      linarith [hj.1]

private theorem continuous_artanh_interior :
    Continuous (fun v : Ioo (-1 : ℝ) 1 => Real.artanh v) := by
  have he : (fun v : Ioo (-1 : ℝ) 1 => Real.artanh v) =
      fun v : Ioo (-1 : ℝ) 1 => (1 / 2 : ℝ) * Real.log ((1 + (v : ℝ)) / (1 - (v : ℝ))) := by
    funext v
    exact Real.artanh_eq_half_log ⟨v.2.1.le, v.2.2.le⟩
  rw [he]
  apply continuous_const.mul
  apply Continuous.log
  · exact (continuous_const.add continuous_subtype_val).div
      (continuous_const.sub continuous_subtype_val) (fun v => by linarith [v.2.2])
  · intro v
    exact ne_of_gt (div_pos (by linarith [v.2.1]) (by linarith [v.2.2]))

/-- This contains interior and W checks, rather than postulating a selector. -/
structure ValidCrossing (H : LocalEquiconnection K) (z w : Suspension K) : Prop where
  left_interior : (height z : ℝ) ∈ Ioo (-1 : ℝ) 1
  right_interior : (height w : ℝ) ∈ Ioo (-1 : ℝ) 1
  labels : (label ⟨z, left_interior⟩, label ⟨w, right_interior⟩) ∈ H.domain

/-- An auxiliary full-history domain used to assemble the explicit formula.
The compact link bound maps every admitted metric pseudoorbit into this domain. -/
abbrev AdmissibleHistory (H : LocalEquiconnection K) :=
  {x : ℤ → Suspension K //
    ForwardSign (fun j => (height (x j) : ℝ)) ∧
    ∀ j, Crossing (fun k => (height (x k) : ℝ)) j → ValidCrossing H (x j) (x (j + 1))}

private def historyHeight {H : LocalEquiconnection K} (x : AdmissibleHistory H) (j : ℤ) : ℝ :=
  height (x.1 j)

private def crossingFraction {H : LocalEquiconnection K} (x : AdmissibleHistory H)
    (j : ℤ) : ℝ :=
  -Real.artanh (historyHeight x j) /
    (Real.artanh (historyHeight x (j + 1)) - Real.artanh (historyHeight x j))

private theorem crossingFraction_mem {H : LocalEquiconnection K}
    (x : AdmissibleHistory H) (j : ℤ) (hj : Crossing (historyHeight x) j) :
    crossingFraction x j ∈ Icc (0 : ℝ) 1 := by
  have hvalid := x.2.2 j hj
  have hlt : historyHeight x j < historyHeight x (j + 1) := by
    by_cases hz : historyHeight x j = 0
    · exact hz ▸ x.2.1 j hz.ge
    · exact lt_of_lt_of_le (lt_of_le_of_ne hj.1 hz) hj.2
  have hclock := (Real.artanh_lt_artanh_iff hvalid.left_interior
    hvalid.right_interior).2 hlt
  have hA := Real.artanh_nonpos hj.1
  have hB := Real.artanh_nonneg hj.2
  dsimp [crossingFraction, historyHeight] at hA hB ⊢
  constructor
  · exact div_nonneg (neg_nonneg.mpr hA) (sub_pos.mpr hclock).le
  · apply (div_le_iff₀ (sub_pos.mpr hclock)).2
    linarith

private def crossingPair {H : LocalEquiconnection K} (x : AdmissibleHistory H)
    (j : ℤ) (hj : Crossing (historyHeight x) j) : H.domain :=
  let hc := x.2.2 j hj
  ⟨(label ⟨x.1 j, hc.left_interior⟩, label ⟨x.1 (j + 1), hc.right_interior⟩), hc.labels⟩

/-- The formula uses the actual labels and arctanh heights of this history. -/
def chartValue {H : LocalEquiconnection K} (x : AdmissibleHistory H)
    (j : ℤ) (hj : Crossing (historyHeight x) j) : Suspension K :=
  phasePoint (H.connect (crossingPair x j hj, ⟨crossingFraction x j, crossingFraction_mem x j hj⟩))
    (-(j : ℝ) - crossingFraction x j)

private theorem chartValue_adjacent {H : LocalEquiconnection K}
    (x : AdmissibleHistory H) (j : ℤ) (hj : Crossing (historyHeight x) j)
    (hk : Crossing (historyHeight x) (j + 1)) :
    chartValue x j hj = chartValue x (j + 1) hk := by
  have hz : historyHeight x (j + 1) = 0 := le_antisymm hk.1 hj.2
  have hneg : historyHeight x j < 0 := negative_before x.2.1 (by omega) hz.le
  have hA : Real.artanh (historyHeight x j) ≠ 0 :=
    ne_of_lt (Real.artanh_neg ⟨(x.2.2 j hj).left_interior.1, hneg⟩)
  have hs : crossingFraction x j = 1 := by
    simp only [crossingFraction, hz, Real.artanh_zero, zero_sub]
    exact div_self (neg_ne_zero.mpr hA)
  have ht : crossingFraction x (j + 1) = 0 := by
    simp only [crossingFraction, hz, Real.artanh_zero, neg_zero, zero_div]
  have hs' : (⟨crossingFraction x j, crossingFraction_mem x j hj⟩ : Icc (0 : ℝ) 1) =
      ⟨1, by constructor <;> norm_num⟩ := Subtype.ext hs
  have ht' : (⟨crossingFraction x (j + 1), crossingFraction_mem x (j + 1) hk⟩ :
      Icc (0 : ℝ) 1) = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext ht
  unfold chartValue
  rw [hs', ht', H.right, H.left, hs, ht]
  congr 1 <;> push_cast <;> ring

/-- Every possible weak crossing gives the same point in the actual quotient. -/
private theorem chart_value_independent {H : LocalEquiconnection K}
    (x : AdmissibleHistory H) (i j : ℤ) (hi : Crossing (historyHeight x) i)
    (hj : Crossing (historyHeight x) j) : chartValue x i hi = chartValue x j hj := by
  rcases crossing_separation x.2.1 hi hj with he | ⟨he, _⟩ | ⟨he, _⟩
  · subst j; rfl
  · subst j; exact chartValue_adjacent x i hi hj
  · subst i; exact (chartValue_adjacent x j hj hi).symm

variable [Nonempty K]

def north : Suspension K := point (Classical.arbitrary K) ⟨-1, by constructor <;> norm_num⟩

def south : Suspension K := point (Classical.arbitrary K) ⟨1, by constructor <;> norm_num⟩

/-- All-sign histories use the poles; every other history uses its actual weak crossing. -/
def selector {H : LocalEquiconnection K} (x : AdmissibleHistory H) : Suspension K :=
  by
    classical
    exact if h : ∃ j, Crossing (historyHeight x) j then chartValue x h.choose h.choose_spec
    else if ∀ j, historyHeight x j < 0 then north else south

private theorem selector_at_crossing {H : LocalEquiconnection K}
    (x : AdmissibleHistory H) (j : ℤ) (hj : Crossing (historyHeight x) j) :
    selector x = chartValue x j hj := by
  classical
  unfold selector
  rw [dif_pos ⟨j, hj⟩]
  exact chart_value_independent _ _ _ _ _

private theorem selector_negative {H : LocalEquiconnection K}
    (x : AdmissibleHistory H) (hx : ∀ j, historyHeight x j < 0) : selector x = north := by
  classical
  have hn : ¬∃ j, Crossing (historyHeight x) j := by
    rintro ⟨j, hj⟩
    linarith [hx (j + 1), hj.2]
  simp only [selector, dif_neg hn, if_pos hx]

private theorem selector_positive {H : LocalEquiconnection K}
    (x : AdmissibleHistory H) (hx : ∀ j, 0 < historyHeight x j) : selector x = south := by
  classical
  have hn : ¬∃ j, Crossing (historyHeight x) j := by
    rintro ⟨j, hj⟩
    linarith [hx j, hj.1]
  have hnn : ¬∀ j, historyHeight x j < 0 := by
    intro h
    linarith [hx 0, h 0]
  simp only [selector, dif_neg hn, if_neg hnn]

private theorem continuous_historyHeight {H : LocalEquiconnection K} (j : ℤ) :
    Continuous (fun x : AdmissibleHistory H => historyHeight x j) :=
  continuous_subtype_val.comp (continuous_height.comp
    ((continuous_apply j).comp continuous_subtype_val))

private abbrev Chart (H : LocalEquiconnection K) (j : ℤ) :=
  {x : AdmissibleHistory H // Crossing (historyHeight x) j}

private theorem crossing_clock_pos {H : LocalEquiconnection K}
    (x : AdmissibleHistory H) (j : ℤ) (hj : Crossing (historyHeight x) j) :
    0 < Real.artanh (historyHeight x (j + 1)) - Real.artanh (historyHeight x j) := by
  have hc := x.2.2 j hj
  have hlt : historyHeight x j < historyHeight x (j + 1) := by
    by_cases hz : historyHeight x j = 0
    · rw [hz]
      exact x.2.1 j hz.ge
    · exact lt_of_lt_of_le (lt_of_le_of_ne hj.1 hz) hj.2
  exact sub_pos.mpr ((Real.artanh_lt_artanh_iff hc.left_interior hc.right_interior).2 hlt)

private theorem continuous_chartValue {H : LocalEquiconnection K} (j : ℤ) :
    Continuous (fun x : Chart H j => chartValue x.1 j x.2) := by
  have hL : Continuous (fun x : Chart H j =>
      (⟨x.1.1 j, (x.1.2.2 j x.2).left_interior⟩ : Interior (K := K))) :=
    ((continuous_apply j).comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  have hR : Continuous (fun x : Chart H j =>
      (⟨x.1.1 (j + 1), (x.1.2.2 j x.2).right_interior⟩ : Interior (K := K))) :=
    ((continuous_apply (j + 1)).comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  have hA : Continuous (fun x : Chart H j => Real.artanh (historyHeight x.1 j)) :=
    continuous_artanh_interior.comp
      (((continuous_historyHeight j).comp continuous_subtype_val).subtype_mk
        (fun x : Chart H j => (x.1.2.2 j x.2).left_interior))
  have hB : Continuous (fun x : Chart H j => Real.artanh (historyHeight x.1 (j + 1))) :=
    continuous_artanh_interior.comp
      (((continuous_historyHeight (j + 1)).comp continuous_subtype_val).subtype_mk
        (fun x : Chart H j => (x.1.2.2 j x.2).right_interior))
  have hs : Continuous (fun x : Chart H j => crossingFraction x.1 j) :=
    hA.neg.div (hB.sub hA) (fun x => ne_of_gt (crossing_clock_pos x.1 j x.2))
  have hp : Continuous (fun x : Chart H j => crossingPair x.1 j x.2) :=
    ((continuous_label.comp hL).prodMk (continuous_label.comp hR)).subtype_mk _
  exact continuous_phasePoint.comp
    ((H.continuous_connect.comp (hp.prodMk (hs.subtype_mk _))).prodMk
      (continuous_const.sub hs))

private theorem continuousAt_selector_crossing {H : LocalEquiconnection K}
    (x : AdmissibleHistory H) (j : ℤ) (hj : Crossing (historyHeight x) j) :
    ContinuousAt selector x := by
  classical
  let U : Set (AdmissibleHistory H) :=
    {y | historyHeight y (j - 1) < 0 ∧ 0 < historyHeight y (j + 2)}
  have hU : IsOpen U :=
    (isOpen_lt (continuous_historyHeight _) continuous_const).inter
      (isOpen_lt continuous_const (continuous_historyHeight _))
  have hx : x ∈ U := ⟨negative_before x.2.1 (by omega) hj.1,
    positive_after x.2.1 (by omega) hj.2⟩
  let C : Icc (j - 1) (j + 1) → Set U :=
    fun k => {y | Crossing (historyHeight y.1) k}
  have hcover : (⋃ k, C k) = univ := by
    apply eq_univ_of_forall
    intro y
    rcases crossing_classification (v := historyHeight y.1) y.1.2.1 with hn | hp | ⟨k, hk⟩
    · exact (not_lt_of_ge (hn (j + 2)).le y.2.2).elim
    · exact (not_lt_of_ge (hp (j - 1)).le y.2.1).elim
    · have hb := crossing_local_range y.1.2.1 y.2.1 y.2.2 hk
      exact mem_iUnion.mpr ⟨⟨k, hb.1, by omega⟩, hk⟩
  have hclosed : ∀ k, IsClosed (C k) := by
    intro k
    exact (isClosed_le ((continuous_historyHeight k).comp continuous_subtype_val)
      continuous_const).inter (isClosed_le continuous_const
        ((continuous_historyHeight (k + 1)).comp continuous_subtype_val))
  have hcontinuous : ∀ k, ContinuousOn (fun y : U => selector y.1) (C k) := by
    intro k
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hm : Continuous (fun y : C k => (⟨y.1.1, y.2⟩ : Chart H k)) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    apply ((continuous_chartValue k).comp hm).congr
    intro y
    exact (selector_at_crossing y.1.1 k y.2).symm
  have hc : Continuous (fun y : U => selector y.1) :=
    (locallyFinite_of_finite C).continuous hcover hclosed hcontinuous
  exact (continuousOn_iff_continuous_domRestrict.mpr hc x hx).continuousAt (hU.mem_nhds hx)

private theorem tendsto_tanh_top : Tendsto Real.tanh atTop (𝓝 (1 : ℝ)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r, hr, hr1⟩ := exists_between (max_lt ha (by norm_num : (-1 : ℝ) < 1))
    have hra : a < r := (le_max_left _ _).trans_lt hr
    have hrm : -1 < r := (le_max_right _ _).trans_lt hr
    apply (eventually_gt_atTop (Real.artanh r)).mono
    intro t ht
    have h := strictMono_tanh ht
    rw [Real.tanh_artanh ⟨hrm, hr1⟩] at h
    exact hra.trans h
  · intro b hb
    exact Eventually.of_forall (fun t => (Real.tanh_lt_one t).trans hb)

private theorem tendsto_tanh_bottom : Tendsto Real.tanh atBot (𝓝 (-1 : ℝ)) := by
  have h := (tendsto_tanh_top.comp tendsto_neg_atBot_atTop).neg
  simpa only [Function.comp_def, Real.tanh_neg, neg_neg] using h

private theorem uniform_cap [CompactSpace K] (p : Height) (N : Suspension K)
    (hp : ∀ u, point u p = N) (O : Set (Suspension K)) (hO : IsOpen O) (hN : N ∈ O) :
    ∃ V : Set Height, IsOpen V ∧ p ∈ V ∧ ∀ u v, v ∈ V → point u v ∈ O := by
  have hpre : IsOpen ((fun z : K × Height => point z.1 z.2) ⁻¹' O) :=
    hO.preimage continuous_point
  have hsub : (univ : Set K) ×ˢ ({p} : Set Height) ⊆
      (fun z : K × Height => point z.1 z.2) ⁻¹' O := by
    rintro ⟨u, v⟩ ⟨_, hv⟩
    have hv' : v = p := mem_singleton_iff.mp hv
    subst v
    simpa only [mem_preimage, hp u] using hN
  obtain ⟨U, V, _, hV, hKU, hpV, hUV⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hpre hsub
  refine ⟨V, hV, hpV (mem_singleton p), fun u v hv => ?_⟩
  exact hUV (show (u, v) ∈ U ×ˢ V from ⟨hKU (mem_univ u), hv⟩)

private theorem negative_phase_cap [CompactSpace K] (O : Set (Suspension K))
    (hO : IsOpen O) (hN : north ∈ O) :
    ∃ A : ℤ, ∀ u t, t ≤ -(A : ℝ) → phasePoint u t ∈ O := by
  obtain ⟨V, hV, hpV, hcap⟩ := uniform_cap
    (⟨-1, by constructor <;> norm_num⟩ : Height) north
    (fun u => point_bottom u _) O hO hN
  have ht : Tendsto (fun t => (⟨Real.tanh t,
      ⟨(Real.neg_one_lt_tanh t).le, (Real.tanh_lt_one t).le⟩⟩ : Height)) atBot
      (𝓝 ⟨-1, by constructor <;> norm_num⟩) :=
    tendsto_subtype_rng.mpr tendsto_tanh_bottom
  obtain ⟨T, hT⟩ := eventually_atBot.mp (ht.eventually (hV.mem_nhds hpV))
  obtain ⟨A, hA⟩ := exists_int_ge (-T)
  exact ⟨A, fun u t ht => hcap u _ (hT t (by linarith))⟩

private theorem positive_phase_cap [CompactSpace K] (O : Set (Suspension K))
    (hO : IsOpen O) (hN : south ∈ O) :
    ∃ A : ℤ, ∀ u t, (A : ℝ) ≤ t → phasePoint u t ∈ O := by
  obtain ⟨V, hV, hpV, hcap⟩ := uniform_cap
    (⟨1, by constructor <;> norm_num⟩ : Height) south
    (fun u => point_top u _) O hO hN
  have ht : Tendsto (fun t => (⟨Real.tanh t,
      ⟨(Real.neg_one_lt_tanh t).le, (Real.tanh_lt_one t).le⟩⟩ : Height)) atTop
      (𝓝 ⟨1, by constructor <;> norm_num⟩) :=
    tendsto_subtype_rng.mpr tendsto_tanh_top
  obtain ⟨T, hT⟩ := eventually_atTop.mp (ht.eventually (hV.mem_nhds hpV))
  obtain ⟨A, hA⟩ := exists_int_ge T
  exact ⟨A, fun u t ht => hcap u _ (hT t (by linarith))⟩

private theorem continuousAt_selector_negative [CompactSpace K] {H : LocalEquiconnection K}
    (x : AdmissibleHistory H) (hx : ∀ j, historyHeight x j < 0) :
    ContinuousAt selector x := by
  rw [ContinuousAt, selector_negative x hx]
  apply tendsto_nhds.mpr
  intro O hO hN
  obtain ⟨A, hA⟩ := negative_phase_cap O hO hN
  have hnb : ∀ᶠ y in 𝓝 x, historyHeight y A < 0 :=
    (isOpen_lt (continuous_historyHeight A) continuous_const).mem_nhds (hx A)
  apply hnb.mono
  intro y hy
  rcases crossing_classification (v := historyHeight y) y.2.1 with hn | hp | ⟨j, hj⟩
  · simpa only [selector_negative y hn] using hN
  · exact (not_lt_of_ge (hp A).le hy).elim
  · rw [selector_at_crossing y j hj]
    apply hA
    have hjA : A ≤ j := by
      by_contra h
      have := nonnegative_after (v := historyHeight y) y.2.1 (show j + 1 ≤ A by omega) hj.2
      linarith
    have hcast : (A : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjA
    have hs := (crossingFraction_mem y j hj).1
    linarith

private theorem continuousAt_selector_positive [CompactSpace K] {H : LocalEquiconnection K}
    (x : AdmissibleHistory H) (hx : ∀ j, 0 < historyHeight x j) :
    ContinuousAt selector x := by
  rw [ContinuousAt, selector_positive x hx]
  apply tendsto_nhds.mpr
  intro O hO hS
  obtain ⟨A, hA⟩ := positive_phase_cap O hO hS
  have hnb : ∀ᶠ y in 𝓝 x, 0 < historyHeight y (-A) :=
    (isOpen_lt continuous_const (continuous_historyHeight (-A))).mem_nhds (hx (-A))
  apply hnb.mono
  intro y hy
  rcases crossing_classification (v := historyHeight y) y.2.1 with hn | hp | ⟨j, hj⟩
  · exact (not_lt_of_ge (hn (-A)).le hy).elim
  · simpa only [selector_positive y hp] using hS
  · rw [selector_at_crossing y j hj]
    apply hA
    have hjA : j < -A := by
      by_contra h
      rcases eq_or_lt_of_le (show -A ≤ j by omega) with he | he
      · subst j; linarith [hj.1]
      · have := positive_after (v := historyHeight y) y.2.1 he hy.le
        linarith [hj.1]
    have hcast : (j : ℝ) + 1 ≤ -(A : ℝ) := by exact_mod_cast (show j + 1 ≤ -A by omega)
    have hs := (crossingFraction_mem y j hj).2
    linarith

/-- Includes every nonconstant strict-sign history, using uniform quotient cap neighborhoods. -/
private theorem continuous_selector [CompactSpace K] (H : LocalEquiconnection K) :
    Continuous (selector : AdmissibleHistory H → Suspension K) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rcases crossing_classification (v := historyHeight x) x.2.1 with hn | hp | ⟨j, hj⟩
  · exact continuousAt_selector_negative x hn
  · exact continuousAt_selector_positive x hp
  · exact continuousAt_selector_crossing x j hj

private theorem height_vertical (z : Suspension K) :
    height (vertical z) = verticalHeight (height z) := by
  induction z using Quotient.inductionOn with | _ p => rfl

private theorem verticalHeight_fixed_bottom :
    verticalHeight ⟨-1, by constructor <;> norm_num⟩ =
      ⟨-1, by constructor <;> norm_num⟩ :=
  mobiusHeight_bottom _ ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩

private theorem verticalHeight_fixed_top :
    verticalHeight ⟨1, by constructor <;> norm_num⟩ =
      ⟨1, by constructor <;> norm_num⟩ :=
  mobiusHeight_top _ ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩

private theorem vertical_interior (z : Interior (K := K)) :
    (height (vertical z.1) : ℝ) ∈ Ioo (-1 : ℝ) 1 := by
  constructor
  · apply lt_of_le_of_ne (height (vertical z.1)).2.1
    intro he
    have hh : height (vertical z.1) = ⟨-1, by constructor <;> norm_num⟩ := Subtype.ext he.symm
    rw [height_vertical, ← verticalHeight_fixed_bottom] at hh
    have := congrArg (fun v : Height => (v : ℝ)) (verticalHeight.injective hh)
    linarith [z.2.1]
  · apply lt_of_le_of_ne (height (vertical z.1)).2.2
    intro he
    have hh : height (vertical z.1) = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext he
    rw [height_vertical, ← verticalHeight_fixed_top] at hh
    have := congrArg (fun v : Height => (v : ℝ)) (verticalHeight.injective hh)
    linarith [z.2.2]

private theorem label_vertical (z : Interior (K := K)) :
    label ⟨vertical z.1, vertical_interior z⟩ = label z := by
  have he : vertical z.1 = point (label z) (verticalHeight (height z.1)) := by
    rw [← point_label z]
    rfl
  have hp := label_point (label z) (verticalHeight (height z.1)) (by
    simpa only [height_vertical] using vertical_interior z)
  simpa only [he] using hp

private theorem vertical_crossing_valid (H : LocalEquiconnection K) (z : Suspension K)
    (hz : (height z : ℝ) ≤ 0) (hw : 0 ≤ (height (vertical z) : ℝ)) :
    ValidCrossing H z (vertical z) := by
  have hi : (height z : ℝ) ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · apply lt_of_le_of_ne (height z).2.1
      intro he
      have hb : height z = ⟨-1, by constructor <;> norm_num⟩ := Subtype.ext he.symm
      rw [height_vertical, hb, verticalHeight_fixed_bottom] at hw
      norm_num at hw
    · linarith
  refine ⟨hi, vertical_interior ⟨z, hi⟩, ?_⟩
  rw [label_vertical ⟨z, hi⟩]
  exact H.diagonal _

private theorem vertical_positive (z : Suspension K) (hz : 0 ≤ (height z : ℝ)) :
    0 < (height (vertical z) : ℝ) := by
  rw [height_vertical]
  change 0 < mobius (Real.tanh 1) (height z)
  apply div_pos
  · have hc : 0 < Real.tanh 1 := by simpa using strictMono_tanh (by norm_num : (0 : ℝ) < 1)
    linarith
  · exact mobius_den_pos ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩ _

private theorem isOpen_validCrossing (H : LocalEquiconnection K) :
    IsOpen {p : Suspension K × Suspension K | ValidCrossing H p.1 p.2} := by
  let U : Set (Suspension K) := {z | (height z : ℝ) ∈ Ioo (-1 : ℝ) 1}
  have hU : IsOpen U := isOpen_Ioo.preimage (continuous_subtype_val.comp continuous_height)
  let V : Set (Interior (K := K) × Interior (K := K)) :=
    {p | (label p.1, label p.2) ∈ H.domain}
  have hV : IsOpen V := H.isOpen_domain.preimage
    ((continuous_label.comp continuous_fst).prodMk (continuous_label.comp continuous_snd))
  have hm : IsOpenMap (fun p : Interior (K := K) × Interior (K := K) =>
      (p.1.1, p.2.1)) := hU.isOpenMap_subtype_val.prodMap hU.isOpenMap_subtype_val
  have he : {p : Suspension K × Suspension K | ValidCrossing H p.1 p.2} =
      (fun p : Interior (K := K) × Interior (K := K) => (p.1.1, p.2.1)) '' V := by
    ext p
    constructor
    · intro h
      exact ⟨(⟨p.1, h.left_interior⟩, ⟨p.2, h.right_interior⟩), h.labels, rfl⟩
    · rintro ⟨⟨z, w⟩, h, rfl⟩
      exact ⟨z.2, w.2, h⟩
  rw [he]
  exact hm V hV

private theorem exists_closed_link_tolerance [CompactSpace K]
    (H : LocalEquiconnection K) (m : MetricSpace (Suspension K))
    (hm : (inferInstance : TopologicalSpace (Suspension K)) = m.toUniformSpace.toTopologicalSpace) :
    letI := m.replaceTopology hm
    ∃ δ > 0, ∀ z w : Suspension K, dist (vertical z) w ≤ δ →
      (0 ≤ (height z : ℝ) → 0 < (height w : ℝ)) ∧
      ((height z : ℝ) ≤ 0 → 0 ≤ (height w : ℝ) → ValidCrossing H z w) := by
  letI := m.replaceTopology hm
  let G : Set (Suspension K × Suspension K) :=
    {p | ((height p.1 : ℝ) < 0 ∨ 0 < (height p.2 : ℝ)) ∧
      (0 < (height p.1 : ℝ) ∨ (height p.2 : ℝ) < 0 ∨ ValidCrossing H p.1 p.2)}
  have hc1 : Continuous (fun p : Suspension K × Suspension K => (height p.1 : ℝ)) :=
    continuous_subtype_val.comp (continuous_height.comp continuous_fst)
  have hc2 : Continuous (fun p : Suspension K × Suspension K => (height p.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_height.comp continuous_snd)
  have hG : IsOpen G :=
    ((isOpen_lt hc1 continuous_const).union (isOpen_lt continuous_const hc2)).inter
      ((isOpen_lt continuous_const hc1).union
        ((isOpen_lt hc2 continuous_const).union (isOpen_validCrossing H)))
  have hgraph : ∀ z, (z, vertical z) ∈ G := by
    intro z
    constructor
    · by_cases hz : (height z : ℝ) < 0
      · exact Or.inl hz
      · exact Or.inr (vertical_positive z (le_of_not_gt hz))
    · by_cases hz : 0 < (height z : ℝ)
      · exact Or.inl hz
      right
      by_cases hw : (height (vertical z) : ℝ) < 0
      · exact Or.inl hw
      · exact Or.inr (vertical_crossing_valid H z (le_of_not_gt hz) (le_of_not_gt hw))
  have herror : Continuous (fun p : Suspension K × Suspension K => dist (vertical p.1) p.2) :=
    (vertical.continuous.comp continuous_fst).dist continuous_snd
  obtain ⟨ε, hε, hbound⟩ := hG.isClosed_compl.isCompact.exists_forall_le'
    herror.continuousOn (a := (0 : ℝ)) (by
      intro p hp
      apply dist_pos.mpr
      intro he
      apply hp
      simpa only [he] using hgraph p.1)
  refine ⟨ε / 2, half_pos hε, fun z w hzw => ?_⟩
  have hgood : (z, w) ∈ G := by
    by_contra hbad
    have := hbound (z, w) hbad
    linarith
  constructor
  · intro hz
    rcases hgood.1 with h | h
    · linarith
    · exact h

  · intro hz hw
    rcases hgood.2 with h | h | h
    · linarith
    · linarith
    · exact h

private def translateHistory {H : LocalEquiconnection K} (n : ℤ) (x : AdmissibleHistory H) :
    AdmissibleHistory H :=
  ⟨fun j => x.1 (j + n), by
    constructor
    · intro j hj
      simpa only [add_assoc, add_comm, add_left_comm] using x.2.1 (j + n) hj
    · intro j hj
      have hc : Crossing (historyHeight x) (j + n) := by
        simpa only [Crossing, historyHeight, add_assoc, add_comm, add_left_comm] using hj
      simpa only [add_assoc, add_comm, add_left_comm] using x.2.2 (j + n) hc⟩

private theorem crossing_translate {H : LocalEquiconnection K} (n : ℤ)
    (x : AdmissibleHistory H) (j : ℤ) :
    Crossing (historyHeight (translateHistory n x)) j ↔ Crossing (historyHeight x) (j + n) := by
  simp only [Crossing, historyHeight, translateHistory, add_assoc, add_comm, add_left_comm]

private theorem vertical_zpow_phasePoint (u : K) (t : ℝ) (n : ℤ) :
    ((vertical : Suspension K ≃ₜ Suspension K) ^ n) (phasePoint u t) =
      phasePoint u (t + (n : ℝ)) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [show (n : ℤ) + 1 = 1 + n by omega, zpow_add, zpow_one, Homeomorph.mul_apply,
      ih, vertical_phasePoint]
    congr 1 <;> push_cast <;> ring
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -n by omega, zpow_add, zpow_neg_one, Homeomorph.mul_apply,
      Homeomorph.inv_apply, ih]
    apply vertical.injective
    rw [Homeomorph.apply_symm_apply, vertical_phasePoint]
    congr 1 <;> push_cast <;> ring

private theorem vertical_north : vertical (north : Suspension K) = north := by
  change point _ (verticalHeight _) = point _ _
  rw [verticalHeight_fixed_bottom]

private theorem vertical_south : vertical (south : Suspension K) = south := by
  change point _ (verticalHeight _) = point _ _
  rw [verticalHeight_fixed_top]

private theorem vertical_zpow_pole (p : Suspension K) (hp : vertical p = p) (n : ℤ) :
    ((vertical : Suspension K ≃ₜ Suspension K) ^ n) p = p := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [show (n : ℤ) + 1 = 1 + n by omega, zpow_add, zpow_one, Homeomorph.mul_apply, ih, hp]
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -n by omega, zpow_add, zpow_neg_one,
      Homeomorph.mul_apply, Homeomorph.inv_apply, ih]
    apply vertical.injective
    rw [Homeomorph.apply_symm_apply, hp]

private theorem chartValue_translate {H : LocalEquiconnection K} (n : ℤ)
    (x : AdmissibleHistory H) (j : ℤ) (hj : Crossing (historyHeight x) (j + n)) :
    chartValue (translateHistory n x) j ((crossing_translate n x j).mpr hj) =
      ((vertical : Suspension K ≃ₜ Suspension K) ^ n) (chartValue x (j + n) hj) := by
  have hf : crossingFraction (translateHistory n x) j = crossingFraction x (j + n) := by
    simp only [crossingFraction, historyHeight, translateHistory,
      add_assoc, add_comm, add_left_comm]
  have hp : crossingPair (translateHistory n x) j ((crossing_translate n x j).mpr hj) =
      crossingPair x (j + n) hj := by
    apply Subtype.ext
    simp only [crossingPair, translateHistory, add_assoc, add_comm, add_left_comm]
  unfold chartValue
  rw [vertical_zpow_phasePoint, hp]
  have hs : (⟨crossingFraction (translateHistory n x) j,
      crossingFraction_mem _ _ ((crossing_translate n x j).mpr hj)⟩ : Icc (0 : ℝ) 1) =
      ⟨crossingFraction x (j + n), crossingFraction_mem _ _ hj⟩ := Subtype.ext hf
  rw [hs, hf]
  congr 1 <;> push_cast <;> ring

private theorem selector_translate {H : LocalEquiconnection K} (n : ℤ)
    (x : AdmissibleHistory H) :
    selector (translateHistory n x) =
      ((vertical : Suspension K ≃ₜ Suspension K) ^ n) (selector x) := by
  rcases crossing_classification (v := historyHeight x) x.2.1 with hn | hp | ⟨j, hj⟩
  · have ht : ∀ k, historyHeight (translateHistory n x) k < 0 := fun k => hn (k + n)
    rw [selector_negative _ ht, selector_negative _ hn, vertical_zpow_pole _ vertical_north]
  · have ht : ∀ k, 0 < historyHeight (translateHistory n x) k := fun k => hp (k + n)
    rw [selector_positive _ ht, selector_positive _ hp, vertical_zpow_pole _ vertical_south]
  · have hj' : Crossing (historyHeight x) (j - n + n) := by simpa using hj
    rw [selector_at_crossing _ (j - n) ((crossing_translate n x (j - n)).mpr hj'),
      chartValue_translate n x (j - n) hj']
    simpa only [sub_add_cancel] using congrArg
      ((vertical : Suspension K ≃ₜ Suspension K) ^ n) (selector_at_crossing x j hj).symm

private theorem vertical_orbit_step (z : Suspension K) (j : ℤ) :
    ((vertical : Suspension K ≃ₜ Suspension K) ^ (j + 1)) z =
      vertical (((vertical : Suspension K ≃ₜ Suspension K) ^ j) z) := by
  rw [add_comm j 1, zpow_add, zpow_one, Homeomorph.mul_apply]

private def orbitHistory (H : LocalEquiconnection K) (z : Suspension K) : AdmissibleHistory H :=
  ⟨fun j => ((vertical : Suspension K ≃ₜ Suspension K) ^ j) z, by
    constructor
    · intro j hj
      change 0 < (height (((vertical : Suspension K ≃ₜ Suspension K) ^ (j + 1)) z) : ℝ)
      rw [vertical_orbit_step]
      exact vertical_positive _ hj
    · intro j hj
      change ValidCrossing H (((vertical : Suspension K ≃ₜ Suspension K) ^ j) z)
        (((vertical : Suspension K ≃ₜ Suspension K) ^ (j + 1)) z)
      rw [vertical_orbit_step]
      apply vertical_crossing_valid H _ hj.1
      simpa only [vertical_orbit_step] using hj.2⟩

private theorem height_phasePoint (u : K) (t : ℝ) :
    (height (phasePoint u t) : ℝ) = Real.tanh t := rfl

private theorem selector_orbit_phasePoint (H : LocalEquiconnection K) (u : K) (t : ℝ) :
    selector (orbitHistory H (phasePoint u t)) = phasePoint u t := by
  let j : ℤ := ⌊-t⌋
  let x := orbitHistory H (phasePoint u t)
  have hh (k : ℤ) : historyHeight x k = Real.tanh (t + (k : ℝ)) := by
    change (height (((vertical : Suspension K ≃ₜ Suspension K) ^ k) (phasePoint u t)) : ℝ) = _
    rw [vertical_zpow_phasePoint, height_phasePoint]
  have hj0 : t + (j : ℝ) ≤ 0 := by have := Int.floor_le (-t); dsimp [j]; linarith
  have hj1 : 0 ≤ t + ((j + 1 : ℤ) : ℝ) := by
    have := Int.lt_floor_add_one (-t)
    dsimp [j]
    push_cast
    linarith
  have hj : Crossing (historyHeight x) j := by
    constructor
    · rw [hh]
      simpa only [Real.tanh_zero] using strictMono_tanh.monotone hj0
    · rw [hh]
      simpa only [Real.tanh_zero] using strictMono_tanh.monotone hj1
  have hf : crossingFraction x j = -(t + (j : ℝ)) := by
    unfold crossingFraction
    rw [hh, hh, Real.artanh_tanh, Real.artanh_tanh]
    push_cast
    have he : t + ((j : ℝ) + 1) - (t + (j : ℝ)) = 1 := by ring
    rw [he, div_one]
  have hp : crossingPair x j hj = ⟨(u, u), H.diagonal u⟩ := by
    apply Subtype.ext
    dsimp [crossingPair, x, orbitHistory]
    simp only [vertical_zpow_phasePoint]
    simp only [phasePoint]
    apply Prod.ext <;> apply label_point
  rw [selector_at_crossing x j hj]
  unfold chartValue
  rw [hp, H.refl]
  congr 1
  rw [hf]
  ring

private theorem selector_orbit (H : LocalEquiconnection K) (z : Suspension K) :
    selector (orbitHistory H z) = z := by
  induction z using Quotient.inductionOn with | _ p =>
    rcases p with ⟨u, v⟩
    by_cases hb : (v : ℝ) = -1
    · have hp : point u v = (north : Suspension K) := by
        have hv : v = ⟨-1, by constructor <;> norm_num⟩ := Subtype.ext hb
        rw [hv]
        exact point_bottom _ _
      change selector (orbitHistory H (point u v)) = point u v
      rw [hp]
      apply selector_negative
      intro j
      change (height (((vertical : Suspension K ≃ₜ Suspension K) ^ j) north) : ℝ) < 0
      rw [vertical_zpow_pole _ vertical_north]
      norm_num [north, height_point]
    · by_cases ht : (v : ℝ) = 1
      · have hp : point u v = (south : Suspension K) := by
          have hv : v = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext ht
          rw [hv]
          exact point_top _ _
        change selector (orbitHistory H (point u v)) = point u v
        rw [hp]
        apply selector_positive
        intro j
        change 0 < (height (((vertical : Suspension K ≃ₜ Suspension K) ^ j) south) : ℝ)
        rw [vertical_zpow_pole _ vertical_south]
        norm_num [south, height_point]
      · have hi : (v : ℝ) ∈ Ioo (-1 : ℝ) 1 := by
          exact ⟨lt_of_le_of_ne v.2.1 (Ne.symm hb), lt_of_le_of_ne v.2.2 ht⟩
        have hp : phasePoint u (Real.artanh v) = point u v := by
          unfold phasePoint
          congr 1
          apply Subtype.ext
          exact Real.tanh_artanh hi
        change selector (orbitHistory H (point u v)) = point u v
        rw [← hp]
        exact selector_orbit_phasePoint H u _

/-- The entire true orbit, with negative iterates and zero link errors. -/
def orbit {X : Type*} [PseudoMetricSpace X] (f : X ≃ₜ X) (δ : ℝ) (hδ : 0 ≤ δ)
    (z : X) : ClosedPseudoOrbit f δ :=
  ⟨fun j => (f ^ j) z, by
    intro j
    have he : (f ^ (j + 1)) z = f ((f ^ j) z) := by
      rw [add_comm j 1, zpow_add, zpow_one, Homeomorph.mul_apply]
    simpa only [he, dist_self] using hδ⟩

/-- The selector contract has the actual full closed integer domain. -/
structure IntegerSelector {X : Type*} [PseudoMetricSpace X] (f : X ≃ₜ X)
    (δ : ℝ) (hδ : 0 ≤ δ) where
  map : ClosedPseudoOrbit f δ → X
  continuous_map : Continuous map
  closed_domain : IsClosed {x : ℤ → X | ∀ j : ℤ, dist (f (x j)) (x (j + 1)) ≤ δ}
  fixes_orbit : ∀ z, map (orbit f δ hδ z) = z
  integer_equivariant : ∀ n : ℤ, ∀ x : ClosedPseudoOrbit f δ,
    map (shift f δ n x) = (f ^ n) (map x)

private def restrictIntegerSelector {X : Type*} [PseudoMetricSpace X] (f : X ≃ₜ X)
    (δ ε : ℝ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hδε : δ ≤ ε)
    (R : IntegerSelector f ε hε) : IntegerSelector f δ hδ where
  map x := R.map ⟨x.1, fun j => (x.2 j).trans hδε⟩
  continuous_map := R.continuous_map.comp (continuous_subtype_val.subtype_mk _)
  closed_domain := closed_pseudoOrbit f.continuous δ
  fixes_orbit z := by
    change R.map _ = z
    convert R.fixes_orbit z using 1
    apply congrArg R.map
    exact Subtype.ext rfl
  integer_equivariant n x := by
    convert R.integer_equivariant n ⟨x.1, fun j => (x.2 j).trans hδε⟩ using 1
    apply congrArg R.map
    exact Subtype.ext rfl

/-- One full-domain selector and its literal restrictions to every smaller positive tolerance.
The metric is explicitly required to induce the native quotient topology. -/
theorem compact_lec_crossing_selector [CompactSpace K] [TopologicalSpace.MetrizableSpace K]
    (H : LocalEquiconnection K) (m : MetricSpace (Suspension K))
    (hm : (inferInstance : TopologicalSpace (Suspension K)) = m.toUniformSpace.toTopologicalSpace) :
    letI := m.replaceTopology hm
    ∃ δstar : ℝ, ∃ hδstar : 0 < δstar,
      ∃ Rstar : IntegerSelector (vertical : Suspension K ≃ₜ Suspension K) δstar hδstar.le,
        ∀ δ : ℝ, ∀ hδ : 0 < δ, ∀ hbound : δ ≤ δstar,
          ∃ R : IntegerSelector (vertical : Suspension K ≃ₜ Suspension K) δ hδ.le,
            ∀ x, R.map x = Rstar.map ⟨x.1, fun j => (x.2 j).trans hbound⟩ := by
  letI := m.replaceTopology hm
  obtain ⟨δstar, hδstar, hlink⟩ := exists_closed_link_tolerance H m hm
  let liftHistory : ClosedPseudoOrbit (vertical : Suspension K → Suspension K) δstar →
      AdmissibleHistory H := fun x => ⟨x.1, by
    constructor
    · intro j hj
      exact (hlink (x.1 j) (x.1 (j + 1)) (x.2 j)).1 hj
    · intro j hj
      exact (hlink (x.1 j) (x.1 (j + 1)) (x.2 j)).2 hj.1 hj.2⟩
  have hcont : Continuous liftHistory := continuous_subtype_val.subtype_mk _
  let Rstar : IntegerSelector (vertical : Suspension K ≃ₜ Suspension K) δstar hδstar.le := {
    map := fun x => selector (liftHistory x)
    continuous_map := (continuous_selector H).comp hcont
    closed_domain := closed_pseudoOrbit vertical.continuous δstar
    fixes_orbit := by
      intro z
      have he : liftHistory (orbit vertical δstar hδstar.le z) = orbitHistory H z :=
        Subtype.ext rfl
      change selector (liftHistory _) = z
      rw [he]
      exact selector_orbit H z
    integer_equivariant := by
      intro n x
      have he : liftHistory (shift vertical δstar n x) = translateHistory n (liftHistory x) :=
        Subtype.ext rfl
      change selector (liftHistory _) = (vertical ^ n) (selector (liftHistory x))
      rw [he]
      exact selector_translate n (liftHistory x) }
  refine ⟨δstar, hδstar, Rstar, fun δ hδ hbound => ?_⟩
  refine ⟨restrictIntegerSelector (X := Suspension K)
    (vertical : Suspension K ≃ₜ Suspension K) δ δstar hδ.le hδstar.le hbound Rstar, ?_⟩
  intro x
  rfl

end D5.S1.Dynamics.Shadowing.VerticalSuspensionSelector
