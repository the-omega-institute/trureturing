/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction
   mirror-E: none(waiver:symbolic-finite-measures)
   anchors: []
   utility: none
   digest: Complete stopped rewards force disjoint baseline and numerical support in the three-bit obstruction. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization

/-! Complete stopped-cell readings and the shared-support obstruction of Proposition 213.10. -/

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

open Classical in
def numerical {L : ℕ} (y : FullScore L) (i : Fin L) (b : Word L) : ℝ :=
  if FirstZero b i then y.C b + y.P b else 0

def coefficientMass {L : ℕ} (y : FullScore L) : ℝ :=
  (∑ b, (y.A b + y.C b + y.P b)) + y.T

open Classical in
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
  unfold reading
  rw [Finset.sum_eq_single a]
  · simp [point]
  · intro b _ hb; simp [point,hb]
  · simp

private theorem zero_of_zero_reading {L : ℕ} (μ : Word L → ℝ)
    (hn : ∀ b, 0 ≤ μ b) (s : Schedule L) (c : Fin 3)
    (hz : reading μ s c = 0) (b : Word L) (hb : cell s b = c) : μ b = 0 := by
  classical
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun w (_ : w ∈ Finset.univ) =>
    show 0 ≤ (if cell s w = c then μ w else 0) from by split; exact hn w; exact le_rfl)).mp hz b
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
  have hc (f : Word L → ℝ) (b : Word L) :
      (if cell (.inr (.inr (⟨(i,j),hij⟩ : Pair L))) b = 2 then f b else 0) =
        (if b i && b j then f b else 0) := by
    cases hi : b i <;> cases hj : b j <;> simp [cell,hi,hj]
  simpa only [reading,hc] using h'

private theorem point_rigid {L : ℕ} (μ : Word L → ℝ) (a : Word L) (t : ℝ)
    (hn : ∀ b, 0 ≤ μ b) (h : SameReadings μ (point a t)) : μ = point a t := by
  classical
  have off (b : Word L) (hb : b ≠ a) : μ b = 0 := by
    obtain ⟨i,hi⟩ : ∃ i, b i ≠ a i := Function.ne_iff.mp hb
    let c : Fin 3 := if b i then 1 else 0
    have diff : cell (.inr (.inl i)) a ≠ c := by
      cases hbi : b i <;> cases hai : a i <;> simp_all [cell,c]
    exact zero_of_zero_reading μ hn (.inr (.inl i)) c
      (by rw [h, reading_point, ite_eq_right diff]) b
      (by cases hbi : b i <;> simp [cell,c,hbi])
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
  simp only [mul_one]
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

private theorem point_integral {L : ℕ} (a : Word L) (t : ℝ) (f : Word L → ℝ) :
    (∑ b, point a t b * f b) = t * f a := by
  classical
  rw [Finset.sum_eq_single a]
  · simp [point]
  · intro b _ hb; simp [point,hb]
  · simp

private theorem numerical_base_zero {L : ℕ} (ν : Word L → ℝ)
    (n j k l : Fin L) (t : ℝ) (hjk : j < k) (hkl : k < l)
    (hn : ∀ b, 0 ≤ ν b) (h : SameReadings ν (threePoints n j k l t)) :
    ν (baseWord n j k l) = 0 := by
  classical
  have hz := barrier_eq h j k l hjk hkl
  have hzero : (∑ b, threePoints n j k l t b * barrier j k l b) = 0 := by
    simp only [threePoints,add_mul,Finset.sum_add_distrib]
    rw [point_integral,point_integral,point_integral]
    simp [singletonWord,barrier,baseWord,ne_of_lt hjk,ne_of_lt hkl,
      ne_of_lt (hjk.trans hkl),Ne.symm (ne_of_lt hjk),Ne.symm (ne_of_lt hkl),
      Ne.symm (ne_of_lt (hjk.trans hkl))]
  rw [hzero] at hz
  have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun b (_ : b ∈ Finset.univ) =>
    mul_nonneg (hn b) (barrier_nonneg j k l b))).mp hz (baseWord n j k l)
      (Finset.mem_univ _)
  simpa [barrier,baseWord] using hb

/-- The common nonnegative mass is zero on the entire cube, although its
competitor measures are arbitrary real nonnegative measures on that cube. -/
private theorem shared_mass_vanishes {L : ℕ} (U V p : Word L → ℝ)
    (n j k l : Fin L) (t : ℝ) (hjk : j < k) (hkl : k < l)
    (hU : ∀ b, 0 ≤ U b) (hV : ∀ b, 0 ≤ V b) (hp : ∀ b, 0 ≤ p b)
    (pU : ∀ b, p b ≤ U b) (pV : p (baseWord n j k l) ≤ V (baseWord n j k l))
    (readU : SameReadings U (point (baseWord n j k l) t))
    (readV : SameReadings V (threePoints n j k l t)) : ∀ b, p b = 0 := by
  have hu := point_rigid U (baseWord n j k l) t hU readU
  have hv := numerical_base_zero V n j k l t hjk hkl hV readV
  intro b
  by_cases hb : b = baseWord n j k l
  · subst b; exact le_antisymm (by simpa [hv] using pV) (hp _)
  · have hz : U b = 0 := by rw [hu]; simp [point,hb]
    exact le_antisymm (by simpa [hz] using pU b) (hp b)

private theorem firstZero_unique {L : ℕ} {b : Word L} {i j : Fin L}
    (hi : FirstZero b i) (hj : FirstZero b j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := hj.2 i h; simp [hi.1] at this
  · exact h
  · have := hi.2 j h; simp [hj.1] at this

private theorem firstZero_exists {L : ℕ} (b : Word L) (hb : b ≠ (fun _ => true)) :
    ∃ i, FirstZero b i := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, b i = false := by
    by_contra h
    push Not at h
    apply hb
    funext i
    cases hbi : b i <;> simp_all
  let s := Finset.univ.filter (fun i => b i = false)
  have hs : s.Nonempty := ⟨i,by simp [s,hi]⟩
  let m := s.min' hs
  have hm : b m = false := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  refine ⟨m,hm,?_⟩
  intro a ha
  cases hba : b a
  · have hle : m ≤ a := Finset.min'_le s a (by simp [s,hba])
    exact False.elim (not_le_of_gt ha hle)
  · rfl

private theorem numerical_total {L : ℕ} (y : FullScore L) (b : Word L) :
    (∑ i, numerical y i b) = y.C b + y.P b := by
  classical
  by_cases hb : b = (fun _ => true)
  · subst b
    simp [numerical,FirstZero,y.terminalC,y.terminalP]
  · obtain ⟨i,hi⟩ := firstZero_exists b hb
    rw [Finset.sum_eq_single i]
    · simp [numerical,hi]
    · intro j _ hji
      have hj : ¬FirstZero b j := fun hj => hji (firstZero_unique hj hi)
      simp [numerical,hj]
    · simp

private theorem mass_identity {L : ℕ} (y : FullScore L) :
    coefficientMass y = (∑ b, baseline y b) + (∑ i, ∑ b, numerical y i b) - ∑ b, y.P b := by
  classical
  rw [Finset.sum_comm]
  simp_rw [numerical_total,baseline,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  unfold coefficientMass
  simp only [Finset.sum_add_distrib]
  ring

private theorem base_firstZero {L : ℕ} (n j k l : Fin L)
    (hnj : n < j) (hjk : j < k) (hkl : k < l) : FirstZero (baseWord n j k l) n := by
  refine ⟨by simp [baseWord],?_⟩
  intro i hi
  have hin : i ≠ n := ne_of_lt hi
  have hij : i ≠ j := ne_of_lt (hi.trans hnj)
  have hik : i ≠ k := ne_of_lt (hi.trans (hnj.trans hjk))
  have hil : i ≠ l := ne_of_lt (hi.trans (hnj.trans (hjk.trans hkl)))
  simp [baseWord,hin,hij,hik,hil]

private theorem singleton_firstZero {L : ℕ} (n j k l a : Fin L)
    (hnj : n < j) (hjk : j < k) (hkl : k < l) (hna : n < a) :
    FirstZero (singletonWord n j k l a) n := by
  have h := base_firstZero n j k l hnj hjk hkl
  constructor
  · simpa [singletonWord,ne_of_lt hna] using h.1
  · intro i hi
    have hia := ne_of_lt (hi.trans hna)
    simpa [singletonWord,hia] using h.2 i hi

/-- Full competitors are constrained only by their actual label-cell rewards.
No cell-to-moment equivalence is a hypothesis. -/
private theorem full_score_rigidity {L : ℕ} (y : FullScore L) (n j k l : Fin L)
    (t : ℝ) (hnj : n < j) (hjk : j < k) (hkl : k < l)
    (readU : SameReadings (baseline y) (point (baseWord n j k l) t))
    (readV : ∀ i, SameReadings (numerical y i)
      (if i = n then threePoints n j k l t else fun _ => 0)) :
    (∀ b, y.P b = 0) ∧ y.T = 0 ∧ y.A (baseWord n j k l) = t ∧
      coefficientMass y = 4 * t := by
  classical
  have hU : ∀ b, 0 ≤ baseline y b := by
    intro b
    have := y.nonnegA b; have := y.nonnegP b; have := y.nonnegT
    unfold baseline; split <;> linarith
  have hV : ∀ b, 0 ≤ numerical y n b := by
    intro b
    have := y.nonnegC b; have := y.nonnegP b
    unfold numerical; split <;> linarith
  have hn : FirstZero (baseWord n j k l) n := base_firstZero n j k l hnj hjk hkl
  have hp := shared_mass_vanishes (baseline y) (numerical y n) y.P n j k l t hjk hkl
    hU hV y.nonnegP (by
      intro b
      have := y.nonnegA b; have := y.nonnegT
      unfold baseline; split <;> linarith)
    (by simp only [numerical,ite_eq_left hn]; exact le_add_of_nonneg_left (y.nonnegC _))
    readU (by simpa using readV n)
  have hu := point_rigid (baseline y) (baseWord n j k l) t hU readU
  have hbase : baseWord n j k l ≠ (fun _ => true) := by
    intro h
    have := congrFun h n
    simp [baseWord] at this
  have hT : y.T = 0 := by
    have h := congrFun hu (fun _ => true)
    simpa [baseline,point,y.terminalA,y.terminalP,Ne.symm hbase] using h
  have hA : y.A (baseWord n j k l) = t := by
    have h := congrFun hu (baseWord n j k l)
    simpa [baseline,point,hp,hT] using h
  refine ⟨hp,hT,hA,?_⟩
  have ht : (∑ b, baseline y b) = t := by
    simpa [point] using total_eq readU
  have hv (i : Fin L) : (∑ b, numerical y i b) = if i = n then 3 * t else 0 := by
    have h := total_eq (readV i)
    by_cases hin : i = n
    · simp only [hin,ite_true,threePoints,Finset.sum_add_distrib] at h ⊢
      simp only [point,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h
      linarith
    · simpa [hin] using h
  rw [mass_identity,ht]
  simp_rw [hv,hp]
  simp
  ring

private theorem firstZero_not_terminal {L : ℕ} {b : Word L} {n : Fin L}
    (h : FirstZero b n) : b ≠ (fun _ => true) := by
  intro he
  have := congrFun he n
  simp [h.1] at this

/-- The actual four-word score, with no restriction on competitor support. -/
def witnessScore {L : ℕ} (n j k l : Fin L) (hnj : n < j) (hjk : j < k)
    (hkl : k < l) (t : ℝ) (ht : 0 ≤ t) : FullScore L where
  A := point (baseWord n j k l) t
  C := threePoints n j k l t
  P := fun _ => 0
  T := 0
  nonnegA := by intro b; unfold point; split <;> positivity
  nonnegC := by intro b; unfold threePoints point; split_ifs <;> positivity
  nonnegP := by simp
  nonnegT := le_rfl
  terminalA := by
    have h := firstZero_not_terminal (base_firstZero n j k l hnj hjk hkl)
    simp [point,Ne.symm h]
  terminalC := by
    have hj := firstZero_not_terminal (singleton_firstZero n j k l j hnj hjk hkl hnj)
    have hk := firstZero_not_terminal
      (singleton_firstZero n j k l k hnj hjk hkl (hnj.trans hjk))
    have hl := firstZero_not_terminal
      (singleton_firstZero n j k l l hnj hjk hkl (hnj.trans (hjk.trans hkl)))
    simp [threePoints,point,Ne.symm hj,Ne.symm hk,Ne.symm hl]
  terminalP := rfl

open Classical in
private theorem mask_point {L : ℕ} (w : Word L) (n i : Fin L) (t : ℝ)
    (hw : FirstZero w n) (b : Word L) :
    (if FirstZero b i then point w t b else 0) =
      if i = n then point w t b else 0 := by
  classical
  by_cases hb : b = w
  · subst b
    have hc : FirstZero w i ↔ i = n :=
      ⟨fun h => firstZero_unique h hw,fun h => h ▸ hw⟩
    simp [hc]
  · simp [point,hb]

private theorem witness_baseline {L : ℕ} (n j k l : Fin L)
    (hnj : n < j) (hjk : j < k) (hkl : k < l) (t : ℝ) (ht : 0 ≤ t) :
    baseline (witnessScore n j k l hnj hjk hkl t ht) = point (baseWord n j k l) t := by
  funext b
  simp [baseline,witnessScore]

private theorem witness_numerical {L : ℕ} (n j k l : Fin L)
    (hnj : n < j) (hjk : j < k) (hkl : k < l) (t : ℝ) (ht : 0 ≤ t) (i : Fin L) :
    numerical (witnessScore n j k l hnj hjk hkl t ht) i =
      if i = n then threePoints n j k l t else fun _ => 0 := by
  classical
  funext b
  have hj := mask_point (singletonWord n j k l j) n i t
    (singleton_firstZero n j k l j hnj hjk hkl hnj) b
  have hk := mask_point (singletonWord n j k l k) n i t
    (singleton_firstZero n j k l k hnj hjk hkl (hnj.trans hjk)) b
  have hl := mask_point (singletonWord n j k l l) n i t
    (singleton_firstZero n j k l l hnj hjk hkl (hnj.trans (hjk.trans hkl))) b
  simp only [numerical,witnessScore,add_zero]
  change (if FirstZero b i then threePoints n j k l t b else 0) =
    (if i = n then threePoints n j k l t else fun _ => 0) b
  have hd : (if FirstZero b i then threePoints n j k l t b else 0) =
      (if FirstZero b i then point (singletonWord n j k l j) t b else 0) +
      (if FirstZero b i then point (singletonWord n j k l k) t b else 0) +
      (if FirstZero b i then point (singletonWord n j k l l) t b else 0) := by
    by_cases h : FirstZero b i <;> simp [h,threePoints]
  rw [hd,hj,hk,hl]
  by_cases hin : i = n <;> simp [hin,threePoints]

private theorem untouched_cell {L : ℕ} (n j k l : Fin L)
    (hjk : j < k) (hkl : k < l) (s : Schedule L) :
    cell s (singletonWord n j k l j) = cell s (baseWord n j k l) ∨
    cell s (singletonWord n j k l k) = cell s (baseWord n j k l) ∨
    cell s (singletonWord n j k l l) = cell s (baseWord n j k l) := by
  classical
  cases s with
  | inl => simp [cell]
  | inr s =>
    cases s with
    | inl i =>
      by_cases hij : i = j
      · right; left
        have hik : i ≠ k := by subst i; exact ne_of_lt hjk
        simp [cell,singletonWord,hik]
      · left; simp [cell,singletonWord,hij]
    | inr a =>
      have hchoose : (a.val.1 ≠ j ∧ a.val.2 ≠ j) ∨
          (a.val.1 ≠ k ∧ a.val.2 ≠ k) ∨ (a.val.1 ≠ l ∧ a.val.2 ≠ l) := by
        by_cases hj : a.val.1 = j
        · by_cases hk : a.val.2 = k
          · right; right
            exact ⟨by simpa [hj] using ne_of_lt (hjk.trans hkl),
              by simpa [hk] using ne_of_lt hkl⟩
          · right; left
            exact ⟨by simpa [hj] using ne_of_lt hjk,hk⟩
        · by_cases hbj : a.val.2 = j
          · by_cases hk : a.val.1 = k
            · right; right
              exact ⟨by simpa [hk] using ne_of_lt hkl,
                by simpa [hbj] using ne_of_lt (hjk.trans hkl)⟩
            · right; left
              exact ⟨hk,by simpa [hbj] using ne_of_lt hjk⟩
          · left; exact ⟨hj,hbj⟩
      rcases hchoose with h | h | h
      · left; simp [cell,singletonWord,h.1,h.2]
      · right; left; simp [cell,singletonWord,h.1,h.2]
      · right; right; simp [cell,singletonWord,h.1,h.2]

/-- Cellwise numerical dominance is compatible with a global obstruction to
removing A. The rewards are the actual complete stopped cells before maximization. -/
private theorem witness_cell_dominance {L : ℕ} (n j k l : Fin L)
    (hjk : j < k) (hkl : k < l) (t : ℝ) (ht : 0 ≤ t)
    (s : Schedule L) (c : Fin 3) :
    reading (point (baseWord n j k l) t) s c ≤ reading (threePoints n j k l t) s c := by
  classical
  have hread : reading (threePoints n j k l t) s c =
      reading (point (singletonWord n j k l j) t) s c +
      reading (point (singletonWord n j k l k) t) s c +
      reading (point (singletonWord n j k l l) t) s c := by
    unfold reading
    have hd (b : Word L) : (if cell s b = c then threePoints n j k l t b else 0) =
        (if cell s b = c then point (singletonWord n j k l j) t b else 0) +
        (if cell s b = c then point (singletonWord n j k l k) t b else 0) +
        (if cell s b = c then point (singletonWord n j k l l) t b else 0) := by
      by_cases h : cell s b = c <;> simp [h,threePoints]
    simp_rw [hd,Finset.sum_add_distrib]
  rw [hread]
  simp only [reading_point]
  have hm := untouched_cell n j k l hjk hkl s
  by_cases hb : cell s (baseWord n j k l) = c
  · rcases hm with h | h | h <;> rw [ite_eq_left hb] <;>
      simp only [h,hb,ite_true] <;> split_ifs <;> linarith
  · rw [ite_eq_right hb]
    split_ifs <;> linarith

/-- Proposition 213.10's universal coefficient obstruction, for arbitrary late
class n and arbitrary real nonnegative full competitors in its complete fiber. -/
theorem proposition21310_rigidity {L : ℕ} (n j k l : Fin L)
    (hnj : n < j) (hjk : j < k) (hkl : k < l) (t : ℝ) (ht : 0 < t)
    (y : FullScore L)
    (hy : SameFiber y (witnessScore n j k l hnj hjk hkl t ht.le)) :
    (∀ b, y.P b = 0) ∧ y.T = 0 ∧ y.A (baseWord n j k l) = t ∧
      coefficientMass y = 4 * t ∧ ¬(∀ b, y.A b = 0) ∧
      ∀ (s : Schedule L) (c : Fin 3),
        reading (baseline (witnessScore n j k l hnj hjk hkl t ht.le)) s c ≤
          reading (numerical (witnessScore n j k l hnj hjk hkl t ht.le) n) s c := by
  have hu : SameReadings (baseline y) (point (baseWord n j k l) t) := by
    simpa only [witness_baseline] using hy.2.1
  have hv : ∀ i, SameReadings (numerical y i)
      (if i = n then threePoints n j k l t else fun _ => 0) := by
    intro i
    simpa only [witness_numerical] using hy.2.2 i
  obtain ⟨hp,hT,hA,hK⟩ := full_score_rigidity y n j k l t hnj hjk hkl hu hv
  refine ⟨hp,hT,hA,hK,?_,?_⟩
  · intro h
    have := h (baseWord n j k l)
    linarith
  · intro s c
    simpa only [witness_baseline,witness_numerical,ite_true] using
      witness_cell_dominance n j k l hjk hkl t ht.le s c


/-- Original N cells in order 00,01,10,11; unused short-schedule cells are empty. -/
def fullCell {L : ℕ} : Schedule L → Word L → Fin 4
  | .inl _, _ => 0
  | .inr (.inl i), b => if b i then 1 else 0
  | .inr (.inr a), b =>
      if b a.val.1 then (if b a.val.2 then 3 else 2) else (if b a.val.2 then 1 else 0)

/-- The complete N and O partitions, with empty cells padded by zero. -/
def catalogCell {L : ℕ} (stop : Bool) (s : Schedule L) (b : Word L) : Fin 4 :=
  if stop then (cell s b).castSucc else fullCell s b

def catalogReading {L : ℕ} (stop : Bool) (μ : Word L → ℝ)
    (s : Schedule L) (c : Fin 4) : ℝ :=
  ∑ b, if catalogCell stop s b = c then μ b else 0

/-- All original labels: zero and the numerical labels i+1. -/
def labelReading {L : ℕ} (stop : Bool) (y : FullScore L) (s : Schedule L)
    (c : Fin 4) (r : Fin (L + 1)) : ℝ :=
  Fin.cases (catalogReading stop (baseline y) s c)
    (fun i => catalogReading stop (numerical y i) s c) r

def scheduleReward {L : ℕ} (stop : Bool) (y : FullScore L)
    (s : Schedule L) (a : Fin 4 → Fin (L + 1)) : ℝ :=
  ∑ c, labelReading stop y s c (a c)

/-- Maximization over every cell-label table of every short or distinct-pair schedule. -/
def completeSupport {L : ℕ} (stop : Bool) (y : FullScore L) : ℝ :=
  sSup (Set.range (fun a : Schedule L × (Fin 4 → Fin (L + 1)) =>
    scheduleReward stop y a.1 a.2))

open Classical in
/-- The original head-pair anchor, with original numerical index i+1 at address i. -/
def anchor {L : ℕ} (y : FullScore L) : ℝ :=
  (∑ b, ∑ i, if FirstZero b i then
    (if 2 ≤ i.val then y.A b else y.C b) else 0) + (∑ b, y.P b) + y.T

def completeCost {L : ℕ} (stop : Bool) (y : FullScore L) : ℝ :=
  completeSupport stop y - anchor y

private theorem point_total {L : ℕ} (w : Word L) (t : ℝ) :
    (∑ b, point w t b) = t := by
  classical
  simp [point]

private theorem witness_beta {L : ℕ} (n j k l : Fin L)
    (hnj : n < j) (hjk : j < k) (hkl : k < l) (t : ℝ) (ht : 0 ≤ t) :
    beta (witnessScore n j k l hnj hjk hkl t ht) = fun i => if i = n then 2*t else 0 := by
  classical
  funext i
  have hmask (w : Word L) (hw : FirstZero w n) :
      (∑ b, if FirstZero b i then point w t b else 0) = if i = n then t else 0 := by
    simp_rw [mask_point w n i t hw]
    split_ifs <;> simp [point_total]
  have ha := hmask (baseWord n j k l) (base_firstZero n j k l hnj hjk hkl)
  have hj := hmask (singletonWord n j k l j) (singleton_firstZero n j k l j hnj hjk hkl hnj)
  have hk := hmask (singletonWord n j k l k)
    (singleton_firstZero n j k l k hnj hjk hkl (hnj.trans hjk))
  have hl := hmask (singletonWord n j k l l)
    (singleton_firstZero n j k l l hnj hjk hkl (hnj.trans (hjk.trans hkl)))
  have expand (b : Word L) :
      (if FirstZero b i then threePoints n j k l t b - point (baseWord n j k l) t b else 0) =
      (if FirstZero b i then point (singletonWord n j k l j) t b else 0) +
      (if FirstZero b i then point (singletonWord n j k l k) t b else 0) +
      (if FirstZero b i then point (singletonWord n j k l l) t b else 0) -
      (if FirstZero b i then point (baseWord n j k l) t b else 0) := by
    split_ifs <;> simp [threePoints]
  simp only [beta,witnessScore,expand,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [ha,hj,hk,hl]
  split_ifs <;> ring

private theorem witness_anchor {L : ℕ} (n j k l : Fin L)
    (hnj : n < j) (hjk : j < k) (hkl : k < l) (hlate : 2 ≤ n.val)
    (t : ℝ) (ht : 0 ≤ t) :
    anchor (witnessScore n j k l hnj hjk hkl t ht) = t := by
  classical
  have hclass (w : Word L) (hw : FirstZero w n) (b : Word L) :
      (∑ i, if FirstZero b i then (if 2 ≤ i.val then point w t b else 0) else 0) =
        point w t b := by
    by_cases hb : b = w
    · subst b
      rw [Finset.sum_eq_single n]
      · simp [hw,hlate]
      · intro i _ hi
        simp [show ¬FirstZero w i from fun h => hi (firstZero_unique h hw)]
      · simp
    · simp [point,hb]
  have hearly (w : Word L) (hw : FirstZero w n) (b : Word L) :
      (∑ i, if FirstZero b i then (if 2 ≤ i.val then 0 else point w t b) else 0) = 0 := by
    by_cases hb : b = w
    · subst b
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : FirstZero w i
      · have := firstZero_unique hi hw
        subst i
        simp [hlate]
      · simp [hi]
    · simp [point,hb]
  have splitrow (b : Word L) :
      (∑ i, if FirstZero b i then
        (if 2 ≤ i.val then point (baseWord n j k l) t b else threePoints n j k l t b) else 0) =
      point (baseWord n j k l) t b := by
    have distribute (i : Fin L) :
        (if FirstZero b i then
          (if 2 ≤ i.val then point (baseWord n j k l) t b else threePoints n j k l t b) else 0) =
        (if FirstZero b i then (if 2 ≤ i.val then point (baseWord n j k l) t b else 0) else 0) +
        (if FirstZero b i then (if 2 ≤ i.val then 0 else point (singletonWord n j k l j) t b) else 0) +
        (if FirstZero b i then (if 2 ≤ i.val then 0 else point (singletonWord n j k l k) t b) else 0) +
        (if FirstZero b i then (if 2 ≤ i.val then 0 else point (singletonWord n j k l l) t b) else 0) := by
      split_ifs <;> simp [threePoints]
    simp_rw [distribute,Finset.sum_add_distrib]
    rw [hclass _ (base_firstZero n j k l hnj hjk hkl),
      hearly _ (singleton_firstZero n j k l j hnj hjk hkl hnj),
      hearly _ (singleton_firstZero n j k l k hnj hjk hkl (hnj.trans hjk)),
      hearly _ (singleton_firstZero n j k l l hnj hjk hkl (hnj.trans (hjk.trans hkl)))]
    ring
  simp only [anchor,witnessScore,splitrow,Finset.sum_const_zero,add_zero]
  exact point_total _ _

private theorem catalog_point {L : ℕ} (stop : Bool) (w : Word L) (t : ℝ)
    (s : Schedule L) (c : Fin 4) :
    catalogReading stop (point w t) s c = if catalogCell stop s w = c then t else 0 := by
  classical
  unfold catalogReading
  rw [Finset.sum_eq_single w]
  · simp [point]
  · intro b _ hb; simp [point,hb]
  · simp

private theorem full_untouched {L : ℕ} (n j k l : Fin L)
    (hjk : j < k) (hkl : k < l) (s : Schedule L) :
    fullCell s (singletonWord n j k l j) = fullCell s (baseWord n j k l) ∨
    fullCell s (singletonWord n j k l k) = fullCell s (baseWord n j k l) ∨
    fullCell s (singletonWord n j k l l) = fullCell s (baseWord n j k l) := by
  classical
  cases s with
  | inl => simp [fullCell]
  | inr s =>
    cases s with
    | inl i =>
      by_cases hij : i = j
      · right; left
        have hik : i ≠ k := by subst i; exact ne_of_lt hjk
        simp [fullCell,singletonWord,hik]
      · left; simp [fullCell,singletonWord,hij]
    | inr a =>
      have hchoose : (a.val.1 ≠ j ∧ a.val.2 ≠ j) ∨
          (a.val.1 ≠ k ∧ a.val.2 ≠ k) ∨ (a.val.1 ≠ l ∧ a.val.2 ≠ l) := by
        by_cases hj : a.val.1 = j
        · by_cases hk : a.val.2 = k
          · right; right
            exact ⟨by simpa [hj] using ne_of_lt (hjk.trans hkl),
              by simpa [hk] using ne_of_lt hkl⟩
          · right; left
            exact ⟨by simpa [hj] using ne_of_lt hjk,hk⟩
        · by_cases hbj : a.val.2 = j
          · by_cases hk : a.val.1 = k
            · right; right
              exact ⟨by simpa [hk] using ne_of_lt hkl,
                by simpa [hbj] using ne_of_lt (hjk.trans hkl)⟩
            · right; left
              exact ⟨hk,by simpa [hbj] using ne_of_lt hjk⟩
          · left; exact ⟨hj,hbj⟩
      rcases hchoose with h | h | h
      · left; simp [fullCell,singletonWord,h.1,h.2]
      · right; left; simp [fullCell,singletonWord,h.1,h.2]
      · right; right; simp [fullCell,singletonWord,h.1,h.2]

private theorem catalog_dominance {L : ℕ} (stop : Bool) (n j k l : Fin L)
    (hjk : j < k) (hkl : k < l) (t : ℝ) (ht : 0 ≤ t)
    (s : Schedule L) (c : Fin 4) :
    catalogReading stop (point (baseWord n j k l) t) s c ≤
      catalogReading stop (threePoints n j k l t) s c := by
  classical
  have hm :
      catalogCell stop s (singletonWord n j k l j) = catalogCell stop s (baseWord n j k l) ∨
      catalogCell stop s (singletonWord n j k l k) = catalogCell stop s (baseWord n j k l) ∨
      catalogCell stop s (singletonWord n j k l l) = catalogCell stop s (baseWord n j k l) := by
    cases stop
    · exact full_untouched n j k l hjk hkl s
    · rcases untouched_cell n j k l hjk hkl s with h | h | h
      · exact Or.inl (congrArg Fin.castSucc h)
      · exact Or.inr (Or.inl (congrArg Fin.castSucc h))
      · exact Or.inr (Or.inr (congrArg Fin.castSucc h))
  have hd :
      catalogReading stop (threePoints n j k l t) s c =
      catalogReading stop (point (singletonWord n j k l j) t) s c +
      catalogReading stop (point (singletonWord n j k l k) t) s c +
      catalogReading stop (point (singletonWord n j k l l) t) s c := by
    unfold catalogReading
    have expand (b : Word L) :
        (if catalogCell stop s b = c then threePoints n j k l t b else 0) =
        (if catalogCell stop s b = c then point (singletonWord n j k l j) t b else 0) +
        (if catalogCell stop s b = c then point (singletonWord n j k l k) t b else 0) +
        (if catalogCell stop s b = c then point (singletonWord n j k l l) t b else 0) := by
      split_ifs <;> simp [threePoints]
    simp_rw [expand,Finset.sum_add_distrib]
  rw [hd]
  simp only [catalog_point]
  by_cases hb : catalogCell stop s (baseWord n j k l) = c
  · rcases hm with h | h | h <;> rw [ite_eq_left hb] <;>
      simp only [h,hb,ite_true] <;> split_ifs <;> linarith
  · rw [ite_eq_right hb]
    split_ifs <;> linarith

private theorem catalog_total {L : ℕ} (stop : Bool) (μ : Word L → ℝ) (s : Schedule L) :
    (∑ c, catalogReading stop μ s c) = ∑ b, μ b := by
  classical
  unfold catalogReading
  rw [Finset.sum_comm]
  simp

private theorem witness_support {L : ℕ} (stop : Bool) (n j k l : Fin L)
    (hnj : n < j) (hjk : j < k) (hkl : k < l) (t : ℝ) (ht : 0 ≤ t) :
    completeSupport stop (witnessScore n j k l hnj hjk hkl t ht) = 3*t := by
  classical
  let y := witnessScore n j k l hnj hjk hkl t ht
  have hn (s : Schedule L) (c : Fin 4) :
      0 ≤ catalogReading stop (numerical y n) s c := by
    apply Finset.sum_nonneg
    intro b _
    have h : 0 ≤ numerical y n b := by
      rw [witness_numerical]
      simp only [ite_true]
      unfold threePoints point
      split_ifs <;> positivity
    split_ifs <;> linarith
  have total (s : Schedule L) :
      (∑ c, catalogReading stop (numerical y n) s c) = 3*t := by
    rw [catalog_total,witness_numerical]
    simp [threePoints,Finset.sum_add_distrib,point_total]
    ring
  have upper (s : Schedule L) (a : Fin 4 → Fin (L + 1)) :
      scheduleReward stop y s a ≤ 3*t := by
    rw [← total s]
    apply Finset.sum_le_sum
    intro c _
    unfold labelReading
    refine Fin.cases ?_ (fun i => ?_) (a c)
    · simpa only [Fin.cases_zero,y,witness_baseline,witness_numerical,ite_true] using
        catalog_dominance stop n j k l hjk hkl t ht s c
    · by_cases hi : i = n
      · subst i; exact le_rfl
      · simpa [y,witness_numerical,hi,catalogReading] using hn s c
  have attained :
      scheduleReward stop y (.inl ()) (fun _ => n.succ) = 3*t := by
    simpa only [scheduleReward,labelReading,Fin.cases_succ] using total (.inl ())
  apply IsGreatest.csSup_eq
  exact ⟨⟨⟨.inl (),fun _ => n.succ⟩,attained⟩,
    by rintro r ⟨⟨s,a⟩,rfl⟩; exact upper s a⟩

/-- Exact signed totals, original late anchor, complete N/O costs and
cellwise dominance for the four-word score on the entire cube. -/
theorem proposition21310_costs {L : ℕ} (n j k l : Fin L)
    (hnj : n < j) (hjk : j < k) (hkl : k < l) (hlate : 2 ≤ n.val)
    (t : ℝ) (ht : 0 < t) :
    let y := witnessScore n j k l hnj hjk hkl t ht.le
    beta y = (fun i => if i = n then 2*t else 0) ∧ anchor y = t ∧
    (∀ stop, completeSupport stop y = 3*t ∧ completeCost stop y = 2*t) ∧
    ∀ stop s c, catalogReading stop (baseline y) s c ≤
      catalogReading stop (numerical y n) s c := by
  dsimp only
  refine ⟨witness_beta n j k l hnj hjk hkl t ht.le,
    witness_anchor n j k l hnj hjk hkl hlate t ht.le,?_,?_⟩
  · intro stop
    have hB := witness_support stop n j k l hnj hjk hkl t ht.le
    refine ⟨hB,?_⟩
    rw [completeCost,hB,witness_anchor n j k l hnj hjk hkl hlate]
    ring
  · intro stop s c
    simpa only [witness_baseline,witness_numerical,ite_true] using
      catalog_dominance stop n j k l hjk hkl t ht.le s c


/-- Constant, singleton and ordered pair-product coordinates on the original cube. -/
def feature {L : ℕ} : Schedule L → Word L → ℝ
  | .inl _, _ => 1
  | .inr (.inl i), b => if b i then 1 else 0
  | .inr (.inr a), b => if b a.val.1 && b a.val.2 then 1 else 0

def moments {L : ℕ} (μ : Word L → ℝ) : Schedule L → ℝ :=
  fun d => ∑ b, μ b * feature d b

/-- Membership includes one nonnegative representing measure on the entire
first-zero class, with all its original coordinates. -/
def MomentCone {L : ℕ} (i : Fin L) (v : Schedule L → ℝ) : Prop :=
  ∃ μ : Word L → ℝ, (∀ b, 0 ≤ μ b) ∧
    (∀ b, ¬FirstZero b i → μ b = 0) ∧ moments μ = v

open Classical in
def classBaselineMass {L : ℕ} (y : FullScore L) (i : Fin L) : ℝ :=
  ∑ b, if FirstZero b i then y.A b + y.P b else 0

/-- Literal coupled constraints (213.9). The same p is subtracted from both
reward vectors, and the baseline equation is on the common full cube. -/
structure CoupledFeasible {L : ℕ} (y : FullScore L)
    (x p : Fin L → Schedule L → ℝ) : Prop where
  shared : ∀ i, MomentCone i (p i)
  baselineResidual : ∀ i, MomentCone i (x i - p i)
  numericalResidual : ∀ i, MomentCone i (moments (numerical y i) - p i)
  classMass : ∀ i, x i (.inl ()) = classBaselineMass y i
  aggregate : ∀ d, (∑ i, x i d) + y.T * feature d (fun _ => true) =
    moments (baseline y) d

def commonMassSet {L : ℕ} (y : FullScore L) : Set ℝ :=
  {r | ∃ x p, CoupledFeasible y x p ∧ r = ∑ i, p i (.inl ())}

def jointMaximum {L : ℕ} (y : FullScore L) : ℝ := sSup (commonMassSet y)

def coefficientFloor {L : ℕ} (y : FullScore L) : ℝ :=
  y.T + ∑ i, max (classBaselineMass y i) (moments (numerical y i) (.inl ()))

def fiberMassSet {L : ℕ} (y : FullScore L) : Set ℝ :=
  {r | ∃ z, SameFiber z y ∧ coefficientMass z = r}

def coefficientMinimum {L : ℕ} (y : FullScore L) : ℝ := sInf (fiberMassSet y)

private def momentReading {L : ℕ} (m : Schedule L → ℝ)
    (s : Schedule L) (c : Fin 3) : ℝ :=
  match s with
  | .inl _ => if c = 0 then m (.inl ()) else 0
  | .inr (.inl i) =>
      if c = 0 then m (.inl ()) - m (.inr (.inl i))
      else if c = 1 then m (.inr (.inl i)) else 0
  | .inr (.inr a) =>
      if c = 0 then m (.inl ()) - m (.inr (.inl a.val.1))
      else if c = 1 then m (.inr (.inl a.val.1)) - m (.inr (.inr a))
      else m (.inr (.inr a))


private theorem reading_moments {L : ℕ} (μ : Word L → ℝ) (s : Schedule L) (c : Fin 3) :
    reading μ s c = momentReading (moments μ) s c := by
  classical
  cases s with
  | inl u => fin_cases c <;> simp [reading,cell,momentReading,moments,feature]
  | inr s =>
    cases s with
    | inl i =>
      fin_cases c <;> simp [momentReading,moments,feature,mul_ite]
      · change (∑ b, if cell (.inr (.inl i)) b = (0 : Fin 3) then μ b else 0) =
          (∑ b, μ b) - ∑ b, if b i then μ b else 0
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro b _
        by_cases hb : b i = true <;> simp [cell,hb]
      · change (∑ b, if cell (.inr (.inl i)) b = (1 : Fin 3) then μ b else 0) =
          ∑ b, if b i then μ b else 0
        apply Finset.sum_congr rfl
        intro b _
        by_cases hb : b i = true <;> simp [cell,hb]
      · change (∑ b, if cell (.inr (.inl i)) b = (2 : Fin 3) then μ b else 0) = 0
        apply Finset.sum_eq_zero
        intro b _
        by_cases hb : b i = true <;> simp [cell,hb]
    | inr a =>
      fin_cases c <;> simp [momentReading,moments,feature,mul_ite]
      · change (∑ b, if cell (.inr (.inr a)) b = (0 : Fin 3) then μ b else 0) =
          (∑ b, μ b) - ∑ b, if b a.val.1 then μ b else 0
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro b _
        by_cases hi : b a.val.1 = true <;> by_cases hj : b a.val.2 = true <;>
          simp [cell,hi,hj]
      · change (∑ b, if cell (.inr (.inr a)) b = (1 : Fin 3) then μ b else 0) =
          (∑ b, if b a.val.1 then μ b else 0) -
            ∑ b, if b a.val.1 = true ∧ b a.val.2 = true then μ b else 0
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro b _
        by_cases hi : b a.val.1 = true <;> by_cases hj : b a.val.2 = true <;>
          simp [cell,hi,hj]
      · change (∑ b, if cell (.inr (.inr a)) b = (2 : Fin 3) then μ b else 0) =
          ∑ b, if b a.val.1 = true ∧ b a.val.2 = true then μ b else 0
        apply Finset.sum_congr rfl
        intro b _
        by_cases hi : b a.val.1 = true <;> by_cases hj : b a.val.2 = true <;>
          simp [cell,hi,hj]

private theorem moments_readings {L : ℕ} {μ ν : Word L → ℝ}
    (h : moments μ = moments ν) : SameReadings μ ν := by
  intro s c
  rw [reading_moments,reading_moments,h]

private theorem moments_add {L : ℕ} (μ ν : Word L → ℝ) :
    moments (μ + ν) = moments μ + moments ν := by
  funext d
  simp [moments,add_mul,Finset.sum_add_distrib]

private theorem cone_zero {L : ℕ} (i : Fin L) :
    MomentCone i 0 := by
  refine ⟨0,by simp,by simp,?_⟩
  funext d
  simp [moments]

private theorem point_cone {L : ℕ} (w : Word L) (i : Fin L) (t : ℝ)
    (ht : 0 ≤ t) (hw : FirstZero w i) : MomentCone i (moments (point w t)) := by
  refine ⟨point w t,?_,?_,rfl⟩
  · intro b; unfold point; split_ifs <;> positivity
  · intro b hb
    have hne : b ≠ w := by rintro rfl; exact hb hw
    simp [point,hne]

private theorem numerical_cone {L : ℕ} (y : FullScore L) (i : Fin L) :
    MomentCone i (moments (numerical y i)) := by
  refine ⟨numerical y i,?_,?_,rfl⟩
  · intro b; unfold numerical; split_ifs
    · exact add_nonneg (y.nonnegC b) (y.nonnegP b)
    · exact le_rfl
  · intro b hb; simp [numerical,hb]

private theorem witness_classMass {L : ℕ} (n j k l : Fin L)
    (hnj : n < j) (hjk : j < k) (hkl : k < l) (t : ℝ) (ht : 0 ≤ t) (i : Fin L) :
    classBaselineMass (witnessScore n j k l hnj hjk hkl t ht) i =
      if i = n then t else 0 := by
  classical
  simp only [classBaselineMass,witnessScore,add_zero]
  simp_rw [mask_point _ n i t (base_firstZero n j k l hnj hjk hkl)]
  by_cases hi : i = n <;> simp [hi,point_total]

private theorem witness_common_feasible {L : ℕ} (n j k l : Fin L)
    (hnj : n < j) (hjk : j < k) (hkl : k < l) (t : ℝ) (ht : 0 ≤ t) :
    CoupledFeasible (witnessScore n j k l hnj hjk hkl t ht)
      (fun i => if i = n then moments (point (baseWord n j k l) t) else 0)
      (fun _ => 0) := by
  classical
  constructor
  · intro i; exact cone_zero i
  · intro i
    simp only [sub_zero]
    by_cases hi : i = n
    · subst i
      simp only [ite_true]
      exact point_cone _ n t ht (base_firstZero n j k l hnj hjk hkl)
    · simpa [hi] using cone_zero i
  · intro i
    simpa using numerical_cone (witnessScore n j k l hnj hjk hkl t ht) i
  · intro i
    rw [witness_classMass]
    by_cases hi : i = n <;> simp [hi,moments,feature,point_total]
  · intro d
    rw [witness_baseline]
    change (∑ i, (if i = n then moments (point (baseWord n j k l) t) else 0) d) +
      0 * feature d (fun _ => true) = _
    have atcoord (i : Fin L) :
        (if i = n then moments (point (baseWord n j k l) t) else 0) d =
          if i = n then moments (point (baseWord n j k l) t) d else 0 := by
      split_ifs <;> rfl
    simp_rw [atcoord]
    simp

private theorem feasible_shared_zero {L : ℕ} (n j k l : Fin L)
    (hnj : n < j) (hjk : j < k) (hkl : k < l) (t : ℝ) (ht : 0 ≤ t)
    (x p : Fin L → Schedule L → ℝ)
    (h : CoupledFeasible (witnessScore n j k l hnj hjk hkl t ht) x p) :
    ∀ i, p i = 0 := by
  classical
  choose P hP hPsupp hPM using h.shared
  choose A hA hAsupp hAM using h.baselineResidual
  choose C hC hCsupp hCM using h.numericalResidual
  let U : Word L → ℝ := fun b => ∑ i, (P i b + A i b)
  let V : Fin L → Word L → ℝ := fun i b => P i b + C i b
  have mx (i : Fin L) : moments (P i + A i) = x i := by
    rw [moments_add,hPM i,hAM i]
    abel
  have mv (i : Fin L) : moments (V i) =
      moments (numerical (witnessScore n j k l hnj hjk hkl t ht) i) := by
    change moments (P i + C i) = _
    rw [moments_add,hPM i,hCM i]
    abel
  have mU : moments U = moments (point (baseWord n j k l) t) := by
    funext d
    have hsum : moments U d = ∑ i, x i d := by
      simp only [moments,U,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact congrFun (mx i) d
    rw [hsum]
    have ha := h.aggregate d
    rw [witness_baseline] at ha
    change (∑ i, x i d) + 0 * feature d (fun _ => true) = _ at ha
    simpa only [zero_mul,add_zero] using ha
  have readU := moments_readings mU
  have hnU : ∀ b, 0 ≤ U b := by
    intro b; exact Finset.sum_nonneg (fun i _ => add_nonneg (hP i b) (hA i b))
  have vanish (i : Fin L) : ∀ b, P i b = 0 := by
    have hnV : ∀ b, 0 ≤ V i b := fun b => add_nonneg (hP i b) (hC i b)
    by_cases hi : i = n
    · subst i
      apply shared_mass_vanishes U (V n) (P n) n j k l t hjk hkl hnU hnV (hP n)
      · intro b
        have hs := Finset.single_le_sum
          (fun i (_ : i ∈ Finset.univ) => add_nonneg (hP i b) (hA i b))
          (Finset.mem_univ n)
        exact (le_add_of_nonneg_right (hA n b)).trans hs
      · exact le_add_of_nonneg_right (hC n _)
      · exact readU
      · have hv := moments_readings (mv n)
        simpa only [witness_numerical,ite_true] using hv
    · have hv := total_eq (moments_readings (mv i))
      have hz : (∑ b, V i b) = 0 := by
        simpa only [witness_numerical,hi,ite_false,Finset.sum_const_zero] using hv
      intro b
      have vb : V i b = 0 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun b (_ : b ∈ Finset.univ) => hnV b)).mp hz b (Finset.mem_univ b)
      exact le_antisymm (by have := hC i b; dsimp [V] at vb; linarith) (hP i b)
  intro i
  rw [← hPM i]
  funext d
  simp [moments,vanish]

/-- Every actual feasible coupled pair has zero objective; the explicitly
shared zero measure attains it. The fiber minimum is attained by the source. -/
theorem proposition21310_cone_minimum {L : ℕ} (n j k l : Fin L)
    (hnj : n < j) (hjk : j < k) (hkl : k < l) (t : ℝ) (ht : 0 < t) :
    let y := witnessScore n j k l hnj hjk hkl t ht.le
    IsGreatest (commonMassSet y) 0 ∧ jointMaximum y = 0 ∧
    (∀ x p, CoupledFeasible y x p → ∀ i, p i = 0) ∧
    IsLeast (fiberMassSet y) (4*t) ∧ coefficientMinimum y = 4*t ∧
    coefficientFloor y = 3*t ∧ coefficientFloor y < coefficientMinimum y := by
  classical
  dsimp only
  let y := witnessScore n j k l hnj hjk hkl t ht.le
  have greatest : IsGreatest (commonMassSet y) 0 := by
    constructor
    · refine ⟨_,fun _ => 0,witness_common_feasible n j k l hnj hjk hkl t ht.le,?_⟩
      simp
    · rintro r ⟨x,p,h,rfl⟩
      simp [feasible_shared_zero n j k l hnj hjk hkl t ht.le x p h]
  have self : SameFiber y y := ⟨rfl,fun _ _ => rfl,fun _ _ _ => rfl⟩
  have sourceK := (proposition21310_rigidity n j k l hnj hjk hkl t ht y self).2.2.2.1
  have least : IsLeast (fiberMassSet y) (4*t) := by
    refine ⟨⟨y,self,sourceK⟩,?_⟩
    rintro r ⟨z,hz,rfl⟩
    exact le_of_eq (proposition21310_rigidity n j k l hnj hjk hkl t ht z hz).2.2.2.1.symm
  have floor : coefficientFloor y = 3*t := by
    have numericMass (i : Fin L) :
        moments (numerical y i) (.inl ()) = if i = n then 3*t else 0 := by
      rw [witness_numerical]
      by_cases hi : i = n <;>
        simp [hi,moments,feature,threePoints,Finset.sum_add_distrib,point_total]
      ring
    have cm (i : Fin L) : classBaselineMass y i = if i = n then t else 0 :=
      witness_classMass n j k l hnj hjk hkl t ht.le i
    change 0 + (∑ i, max (classBaselineMass y i) (moments (numerical y i) (.inl ()))) = _
    simp_rw [cm,numericMass]
    have hm : max t (3*t) = 3*t := max_eq_right (by linarith)
    have each (i : Fin L) : max (if i = n then t else 0) (if i = n then 3*t else 0) =
        if i = n then 3*t else 0 := by
      by_cases hi : i = n <;> simp [hi,hm]
    simp_rw [each]
    simp
  refine ⟨greatest,greatest.csSup_eq,
    feasible_shared_zero n j k l hnj hjk hkl t ht.le,least,least.csInf_eq,floor,?_⟩
  rw [show coefficientMinimum y = 4*t from least.csInf_eq,floor]
  linarith

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.JointRewardFiberObstruction
