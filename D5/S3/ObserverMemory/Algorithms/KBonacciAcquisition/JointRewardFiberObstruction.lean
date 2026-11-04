/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction
   mirror-E: none(waiver:symbolic-finite-measures)
   anchors: []
   utility: none
   digest: Complete stopped rewards force disjoint baseline and numerical support in the three-bit obstruction. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.JointRewardFiberObstruction

abbrev Word (L : ℕ) := Fin L → Bool

def point {L : ℕ} (a : Word L) (t : ℝ) (b : Word L) : ℝ := if b = a then t else 0

def reading {L : ℕ} (μ : Word L → ℝ) (s : Schedule L) (c : Fin 3) : ℝ :=
  ∑ b, if cell s b = c then μ b else 0

/-- Every schedule, including empty and singleton schedules, and every cell. -/
def SameReadings {L : ℕ} (μ ν : Word L → ℝ) : Prop :=
  ∀ s c, reading μ s c = reading ν s c

/-- Original first-zero class; address i has numerical output label i+1. -/
def FirstZero {L : ℕ} (b : Word L) (i : Fin L) : Prop :=
  b i = false ∧ ∀ h : Fin L, h < i → b h = true

/-- A/C/P are independent nonnegative coefficients on every nonterminal word.
Their values at the terminal are normalized to zero; T is its sole coefficient. -/
structure FullScore (L : ℕ) where
  A : Word L → ℝ
  C : Word L → ℝ
  P : Word L → ℝ
  T : ℝ
  nonnegA : ∀ b, 0 ≤ A b
  nonnegC : ∀ b, 0 ≤ C b
  nonnegP : ∀ b, 0 ≤ P b
  nonnegT : 0 ≤ T
  terminalA : A (fun _ => true) = 0
  terminalC : C (fun _ => true) = 0
  terminalP : P (fun _ => true) = 0

def baseline {L : ℕ} (y : FullScore L) (b : Word L) : ℝ :=
  y.A b + y.P b + if b = (fun _ => true) then y.T else 0

def numerical {L : ℕ} (y : FullScore L) (i : Fin L) (b : Word L) : ℝ :=
  if FirstZero b i then y.C b + y.P b else 0

def coefficientMass {L : ℕ} (y : FullScore L) : ℝ :=
  (∑ b, y.A b + y.C b + y.P b) + y.T

def beta {L : ℕ} (y : FullScore L) (i : Fin L) : ℝ :=
  ∑ b, if FirstZero b i then y.C b - y.A b else 0

/-- All original output labels before maximization, together with beta. -/
def SameFiber {L : ℕ} (y z : FullScore L) : Prop :=
  beta y = beta z ∧ SameReadings (baseline y) (baseline z) ∧
    ∀ i, SameReadings (numerical y i) (numerical z i)

private theorem reading_point {L : ℕ} (a : Word L) (t : ℝ)
    (s : Schedule L) (c : Fin 3) :
    reading (point a t) s c = if cell s a = c then t else 0 := by
  classical
  simp only [reading, point]
  simp_rw [ite_comm (cell s _ = c) (_ = a)]
  simp

private theorem zero_of_zero_reading {L : ℕ} (μ : Word L → ℝ)
    (hn : ∀ b, 0 ≤ μ b) (s : Schedule L) (c : Fin 3)
    (hz : reading μ s c = 0) (b : Word L) (hb : cell s b = c) : μ b = 0 := by
  classical
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun w (_ : w ∈ Finset.univ) =>
    show 0 ≤ (if cell s w = c then μ w else 0) from by split <;> positivity)).mp hz b
      (Finset.mem_univ b)
  simpa [hb] using h

private theorem total_eq {L : ℕ} {μ ν : Word L → ℝ} (h : SameReadings μ ν) :
    (∑ b, μ b) = ∑ b, ν b := by
  simpa [reading, cell] using h (.inl ()) 0

private theorem unary_eq {L : ℕ} {μ ν : Word L → ℝ} (h : SameReadings μ ν)
    (i : Fin L) : (∑ b, if b i then μ b else 0) = ∑ b, if b i then ν b else 0 := by
  simpa [reading, cell] using h (.inr (.inl i)) 1

private theorem binary_eq {L : ℕ} {μ ν : Word L → ℝ} (h : SameReadings μ ν)
    (i j : Fin L) (hij : i < j) :
    (∑ b, if b i && b j then μ b else 0) = ∑ b, if b i && b j then ν b else 0 := by
  have h' := h (.inr (.inr ⟨(i,j),hij⟩)) 2
  simpa only [reading, cell] using h'

private theorem point_rigid {L : ℕ} (μ : Word L → ℝ) (a : Word L) (t : ℝ)
    (hn : ∀ b, 0 ≤ μ b) (h : SameReadings μ (point a t)) : μ = point a t := by
  classical
  have off (b : Word L) (hb : b ≠ a) : μ b = 0 := by
    obtain ⟨i,hi⟩ : ∃ i, b i ≠ a i := Function.ne_iff.mp hb
    let c : Fin 3 := if b i then 1 else 0
    have diff : cell (.inr (.inl i)) a ≠ c := by
      cases hbi : b i <;> cases hai : a i <;> simp_all [cell,c]
    apply zero_of_zero_reading μ hn (.inr (.inl i)) c _ b
    · rw [h, reading_point, if_neg diff]
    · cases hbi : b i <;> simp [cell,c,hbi]
  have ht := total_eq h
  have ha : μ a = t := by
    rw [Finset.sum_eq_single a (fun b _ hb => off b hb) (by simp)] at ht
    simpa [point] using ht
  funext b
  by_cases hb : b = a
  · subst b; simp [point,ha]
  · simp [point,hb,off b hb]

private def barrier {L : ℕ} (j k l : Fin L) (b : Word L) : ℝ :=
  1 - (if b j then 1 else 0) - (if b k then 1 else 0) - (if b l then 1 else 0) +
    (if b j && b k then 1 else 0) + (if b j && b l then 1 else 0) +
    (if b k && b l then 1 else 0)

private theorem barrier_nonneg {L : ℕ} (j k l : Fin L) (b : Word L) :
    0 ≤ barrier j k l b := by
  cases hj : b j <;> cases hk : b k <;> cases hl : b l <;>
    norm_num [barrier,hj,hk,hl]

private theorem barrier_eq {L : ℕ} {μ ν : Word L → ℝ} (h : SameReadings μ ν)
    (j k l : Fin L) (hjk : j < k) (hkl : k < l) :
    (∑ b, μ b * barrier j k l b) = ∑ b, ν b * barrier j k l b := by
  classical
  simp_rw [barrier,mul_add,mul_sub,mul_one,mul_ite,mul_zero,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [total_eq h, unary_eq h j, unary_eq h k, unary_eq h l,
    binary_eq h j k hjk, binary_eq h j l (hjk.trans hkl), binary_eq h k l hkl]

/-- Three selected suffix bits are zero; all other bits except n are one. -/
def baseWord {L : ℕ} (n j k l : Fin L) : Word L :=
  fun i => decide (i ≠ n ∧ i ≠ j ∧ i ≠ k ∧ i ≠ l)

def singletonWord {L : ℕ} (n j k l a : Fin L) : Word L :=
  Function.update (baseWord n j k l) a true

def threePoints {L : ℕ} (n j k l : Fin L) (t : ℝ) (b : Word L) : ℝ :=
  point (singletonWord n j k l j) t b + point (singletonWord n j k l k) t b +
    point (singletonWord n j k l l) t b

private theorem numerical_base_zero {L : ℕ} (ν : Word L → ℝ)
    (n j k l : Fin L) (t : ℝ) (hjk : j < k) (hkl : k < l)
    (hn : ∀ b, 0 ≤ ν b) (h : SameReadings ν (threePoints n j k l t)) :
    ν (baseWord n j k l) = 0 := by
  classical
  have hz := barrier_eq h j k l hjk hkl
  have hzero : (∑ b, threePoints n j k l t b * barrier j k l b) = 0 := by
    simp [threePoints,point,add_mul,Finset.sum_add_distrib,singletonWord,
      barrier,baseWord,ne_of_lt hjk,ne_of_lt hkl,ne_of_lt (hjk.trans hkl),
      Ne.symm (ne_of_lt hjk),Ne.symm (ne_of_lt hkl),Ne.symm (ne_of_lt (hjk.trans hkl))]
  rw [hzero] at hz
  have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun b (_ : b ∈ Finset.univ) =>
    mul_nonneg (hn b) (barrier_nonneg j k l b))).mp hz (baseWord n j k l)
      (Finset.mem_univ _)
  simpa [barrier,baseWord] using hb

/-- The common nonnegative mass is zero on the entire cube, although its
competitor measures are arbitrary real nonnegative measures on that cube. -/
theorem shared_mass_vanishes {L : ℕ} (U V p : Word L → ℝ)
    (n j k l : Fin L) (t : ℝ) (hjk : j < k) (hkl : k < l)
    (hU : ∀ b, 0 ≤ U b) (hV : ∀ b, 0 ≤ V b) (hp : ∀ b, 0 ≤ p b)
    (pU : ∀ b, p b ≤ U b) (pV : ∀ b, p b ≤ V b)
    (readU : SameReadings U (point (baseWord n j k l) t))
    (readV : SameReadings V (threePoints n j k l t)) : ∀ b, p b = 0 := by
  have hu := point_rigid U (baseWord n j k l) t hU readU
  have hv := numerical_base_zero V n j k l t hjk hkl hV readV
  intro b
  by_cases hb : b = baseWord n j k l
  · subst b; exact le_antisymm (by simpa [hv] using pV _) (hp _)
  · have hz : U b = 0 := by rw [hu]; simp [point,hb]
    exact le_antisymm (by simpa [hz] using pU b) (hp b)

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.JointRewardFiberObstruction
