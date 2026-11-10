/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberCatalog
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

theorem total_eq {L : ℕ} {μ ν : Word L → ℝ} (h : SameReadings μ ν) :
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
theorem shared_mass_vanishes {L : ℕ} (U V p : Word L → ℝ)
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

theorem firstZero_unique {L : ℕ} {b : Word L} {i j : Fin L}
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

theorem base_firstZero {L : ℕ} (n j k l : Fin L)
    (hnj : n < j) (hjk : j < k) (hkl : k < l) : FirstZero (baseWord n j k l) n := by
  refine ⟨by simp [baseWord],?_⟩
  intro i hi
  have hin : i ≠ n := ne_of_lt hi
  have hij : i ≠ j := ne_of_lt (hi.trans hnj)
  have hik : i ≠ k := ne_of_lt (hi.trans (hnj.trans hjk))
  have hil : i ≠ l := ne_of_lt (hi.trans (hnj.trans (hjk.trans hkl)))
  simp [baseWord,hin,hij,hik,hil]

theorem singleton_firstZero {L : ℕ} (n j k l a : Fin L)
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
theorem mask_point {L : ℕ} (w : Word L) (n i : Fin L) (t : ℝ)
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

theorem witness_baseline {L : ℕ} (n j k l : Fin L)
    (hnj : n < j) (hjk : j < k) (hkl : k < l) (t : ℝ) (ht : 0 ≤ t) :
    baseline (witnessScore n j k l hnj hjk hkl t ht) = point (baseWord n j k l) t := by
  funext b
  simp [baseline,witnessScore]

theorem witness_numerical {L : ℕ} (n j k l : Fin L)
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

theorem untouched_cell {L : ℕ} (n j k l : Fin L)
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

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables

/-- The output function evaluated on the whole Boolean cube. -/
def evaluate {L : ℕ} (stop : Bool) (s : Schedule L) (a : Fin 4 → Fin (L + 1)) :
    Word L → Fin (L + 1) := fun b => a (catalogCell stop s b)

private theorem full_pair_fibers {L : ℕ} (a : Pair L) (b c : Word L)
    (h : fullCell (.inr (.inr a)) b = fullCell (.inr (.inr a)) c) :
    b a.val.1 = c a.val.1 ∧ b a.val.2 = c a.val.2 := by
  cases h₁ : b a.val.1 <;> cases h₂ : b a.val.2 <;>
    cases h₃ : c a.val.1 <;> cases h₄ : c a.val.2 <;>
    simp_all [fullCell]

theorem evaluated_in_catalog {L : ℕ} (stop : Bool) (s : Schedule L)
    (a : Fin 4 → Fin (L + 1)) : InCatalog stop L (evaluate stop s a) := by
  cases stop
  · refine ⟨addresses s, ?_, ?_, by simp, ?_⟩
    · cases s with
      | inl => simp [addresses]
      | inr s => cases s <;> simp [addresses]
    · intro i hi
      cases s with
      | inl => simp [addresses] at hi
      | inr s =>
        cases s with
        | inl j =>
            simp [addresses] at hi
            subst i
            exact j.isLt
        | inr p =>
          simp [addresses] at hi
          rcases hi with rfl | rfl
          · exact p.val.1.isLt
          · exact p.val.2.isLt
    · intro b c h
      apply congrArg a
      cases s with
      | inl => rfl
      | inr s =>
        cases s with
        | inl i =>
          have he : b i = c i := by simpa [addresses, view, lowReply] using h
          simp [catalogCell, fullCell, he]
        | inr p =>
          have he : b p.val.1 = c p.val.1 ∧ b p.val.2 = c p.val.2 := by
            simpa [addresses, view, lowReply] using h
          simp [catalogCell, fullCell, he.1, he.2]
  · have eqtable : evaluate true s a = (table s (a 0, a 1, a 2)).val := by
      funext b
      simp only [evaluate, catalogCell, ite_true, table]
      generalize cell s b = k
      fin_cases k <;> simp [label]
    rw [eqtable]
    exact (table s (a 0, a 1, a 2)).property

private theorem nonstop_represented {L : ℕ} (f : Catalog false L) :
    ∃ s a, evaluate false s a = f.val := by
  classical
  obtain ⟨xs,hlen,hlow,_,hc⟩ := f.property
  have finish (s : Schedule L)
      (h : f.val.FactorsThrough (catalogCell false s)) :
      ∃ s a, evaluate false s a = f.val := by
    obtain ⟨a,ha⟩ := (Function.factorsThrough_iff f.val).mp h
    exact ⟨s,a,ha.symm⟩
  cases xs with
  | nil =>
      apply finish (.inl ())
      intro b c _
      exact hc b c rfl
  | cons i xs =>
      have hi : i < L := hlow i (by simp)
      let ii : Fin L := ⟨i,hi⟩
      cases xs with
      | nil =>
          apply finish (.inr (.inl ii))
          intro b c h
          have he : b ii = c ii := by
            cases hb : b ii <;> cases hb' : c ii <;> simp_all [catalogCell, fullCell]
          apply hc
          simp [view, lowReply, hi, ← he, ii]
      | cons j xs =>
          cases xs with
          | cons k xs => simp at hlen
          | nil =>
              have hj : j < L := hlow j (by simp)
              let jj : Fin L := ⟨j,hj⟩
              by_cases heq : i = j
              · subst j
                apply finish (.inr (.inl ii))
                intro b c h
                have he : b ii = c ii := by
                  cases hb : b ii <;> cases hb' : c ii <;> simp_all [catalogCell, fullCell]
                apply hc
                simp [view, lowReply, hi, ← he, ii]
              · by_cases hij : i < j
                · let p : Pair L := ⟨(ii,jj),hij⟩
                  apply finish (.inr (.inr p))
                  intro b c h
                  have he := full_pair_fibers p b c h
                  apply hc
                  simpa [view, lowReply, hi, hj, ii, jj] using he
                · have hji : j < i := by omega
                  let p : Pair L := ⟨(jj,ii),hji⟩
                  apply finish (.inr (.inr p))
                  intro b c h
                  have he := full_pair_fibers p b c h
                  apply hc
                  simpa [view, lowReply, hi, hj, p, ii, jj, and_comm] using he

/-- Equality of whole-function ranges, with no injectivity assertion about representations. -/
theorem catalog_range {L : ℕ} (stop : Bool) (f : Word L → Fin (L + 1)) :
    InCatalog stop L f ↔ ∃ s a, evaluate stop s a = f := by
  constructor
  · intro hf
    cases stop
    · exact nonstop_represented ⟨f,hf⟩
    · obtain ⟨s,t,he⟩ := represented (⟨f,hf⟩ : Catalog true L)
      refine ⟨s,(fun c => if c = 0 then t.1 else if c = 1 then t.2.1 else t.2.2),?_⟩
      have eqval := congrArg Subtype.val he
      change (table s t).val = f at eqval
      rw [← eqval]
      funext b
      simp only [evaluate, catalogCell, ite_true, table]
      generalize cell s b = k
      fin_cases k <;> simp [label]
  · rintro ⟨s,a,rfl⟩
    exact evaluated_in_catalog stop s a

/-- FullScore's original reward: output zero receives A+P and terminal T;
output i+1 receives C+P precisely in first-zero class i. -/
def fullReward {L : ℕ} (y : FullScore L) (f : Word L → Fin (L + 1)) : ℝ :=
  ∑ b, Fin.cases (baseline y b) (fun i => numerical y i b) (f b)

private theorem label_reading_sum {L : ℕ} (stop : Bool) (y : FullScore L)
    (s : Schedule L) (c : Fin 4) (r : Fin (L + 1)) :
    labelReading stop y s c r =
      ∑ b, if catalogCell stop s b = c then
        Fin.cases (baseline y b) (fun i => numerical y i b) r else 0 := by
  induction r using Fin.cases <;> simp [labelReading, catalogReading]

/-- The local cell sum is the original functional of the entire output function. -/
theorem schedule_reward_eq {L : ℕ} (stop : Bool) (y : FullScore L)
    (s : Schedule L) (a : Fin 4 → Fin (L + 1)) :
    scheduleReward stop y s a = fullReward y (evaluate stop s a) := by
  classical
  simp only [scheduleReward, label_reading_sum]
  rw [Finset.sum_comm]
  simp [fullReward, evaluate]

/-- Supremum over the original complete catalog of output functions. -/
def completeSupport {L : ℕ} (stop : Bool) (y : FullScore L) : ℝ :=
  sSup (Set.range (fun f : Catalog stop L => fullReward y f.val))

theorem complete_support_eq_local {L : ℕ} (stop : Bool) (y : FullScore L) :
    completeSupport stop y = sSup (Set.range
      (fun a : Schedule L × (Fin 4 → Fin (L + 1)) => scheduleReward stop y a.1 a.2)) := by
  unfold completeSupport
  congr 1
  ext r
  constructor
  · rintro ⟨f,rfl⟩
    obtain ⟨s,a,ha⟩ := (catalog_range stop f.val).mp f.property
    exact ⟨(s,a),by simpa [ha] using schedule_reward_eq stop y s a⟩
  · rintro ⟨⟨s,a⟩,rfl⟩
    exact ⟨⟨evaluate stop s a,evaluated_in_catalog stop s a⟩,
      (schedule_reward_eq stop y s a).symm⟩
open Classical in
/-- The original reference head returns the first zero among addresses zero and one,
and returns zero if neither available head address is false. -/
def referenceHead {L : ℕ} (b : Word L) : Fin (L + 1) :=
  if h : ∃ i : Fin L, FirstZero b i ∧ i.val < 2 then h.choose.succ else 0

private def headSchedule (L : ℕ) (hL : 2 ≤ L) : Schedule L :=
  .inr (.inr ⟨(⟨0,by omega⟩,⟨1,by omega⟩),by change (0 : ℕ) < 1; omega⟩)

private def headLabels (L : ℕ) (hL : 2 ≤ L) (stop : Bool) (c : Fin 4) : Fin (L + 1) :=
  if stop then
    if c = 0 then ⟨1,by omega⟩ else if c = 1 then ⟨2,by omega⟩ else 0
  else if c = 0 ∨ c = 1 then ⟨1,by omega⟩ else if c = 2 then ⟨2,by omega⟩ else 0

private theorem reference_head_evaluate {L : ℕ} (hL : 2 ≤ L) (stop : Bool) :
    evaluate stop (headSchedule L hL) (headLabels L hL stop) = referenceHead := by
  classical
  let i : Fin L := ⟨0,by omega⟩
  let j : Fin L := ⟨1,by omega⟩
  funext b
  by_cases hb : b i = false
  · have hz : FirstZero b i := ⟨hb,by intro k hk; change k.val < 0 at hk; omega⟩
    have he : ∃ k : Fin L, FirstZero b k ∧ k.val < 2 := ⟨i,hz,by change (0 : ℕ) < 2; omega⟩
    have chosen : he.choose = i := firstZero_unique he.choose_spec.1 hz
    rw [referenceHead,dite_eq_left he,chosen]
    cases stop <;> simp [evaluate,catalogCell,headSchedule,headLabels,cell,fullCell,i,hb]
  · have hbi : b i = true := Bool.eq_true_of_not_eq_false hb
    by_cases hc : b j = false
    · have hz : FirstZero b j := ⟨hc,by
        intro k hk
        have eq : k = i := by apply Fin.ext; change k.val = 0; change k.val < 1 at hk; omega
        simpa [eq] using hbi⟩
      have he : ∃ k : Fin L, FirstZero b k ∧ k.val < 2 := ⟨j,hz,by change (1 : ℕ) < 2; omega⟩
      have chosen : he.choose = j := firstZero_unique he.choose_spec.1 hz
      rw [referenceHead,dite_eq_left he,chosen]
      cases stop <;> simp [evaluate,catalogCell,headSchedule,headLabels,cell,fullCell,i,j,hbi,hc]
    · have hcj : b j = true := Bool.eq_true_of_not_eq_false hc
      have no : ¬∃ k : Fin L, FirstZero b k ∧ k.val < 2 := by
        rintro ⟨k,hk,hle⟩
        have eq : k = i ∨ k = j := by
          have : k.val = 0 ∨ k.val = 1 := by omega
          rcases this with h | h
          · left; apply Fin.ext; exact h
          · right; apply Fin.ext; exact h
        rcases eq with rfl | rfl
        · have fail := hk.1; simp [hbi] at fail
        · have fail := hk.1; simp [hcj] at fail
      rw [referenceHead,dite_eq_right no]
      cases stop <;> simp [evaluate,catalogCell,headSchedule,headLabels,cell,fullCell,i,j,hbi,hcj]

/-- The original reference head-pair anchor, with the available short-head extension. -/
def anchor {L : ℕ} (y : FullScore L) : ℝ :=
  if hL : 2 ≤ L then scheduleReward true y (headSchedule L hL) (headLabels L hL true)
  else fullReward y referenceHead

private theorem anchor_eq_reference {L : ℕ} (y : FullScore L) :
    anchor y = fullReward y referenceHead := by
  unfold anchor
  split_ifs with hL
  · rw [schedule_reward_eq,reference_head_evaluate]
  · rfl

open Classical in
theorem anchor_eq_formula {L : ℕ} (y : FullScore L) :
    anchor y = (∑ b, ∑ i, if FirstZero b i then
      (if 2 ≤ i.val then y.A b else y.C b) else 0) + (∑ b, y.P b) + y.T := by
  classical
  have each (b : Word L) :
      Fin.cases (baseline y b) (fun i => numerical y i b) (referenceHead b) =
        (∑ i, if FirstZero b i then (if 2 ≤ i.val then y.A b else y.C b) else 0) +
          y.P b + if b = (fun _ => true) then y.T else 0 := by
    by_cases hb : b = (fun _ => true)
    · subst b
      have no : ¬∃ i : Fin L, FirstZero (fun _ => true) i ∧ i.val < 2 := by
        simp [FirstZero]
      simp [referenceHead,no,baseline,FirstZero,y.terminalA,y.terminalP]
    · obtain ⟨i,hi⟩ := firstZero_exists b hb
      have sum : (∑ k, if FirstZero b k then (if 2 ≤ k.val then y.A b else y.C b) else 0) =
          if 2 ≤ i.val then y.A b else y.C b := by
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro k _ hk
          simp [show ¬FirstZero b k from fun h => hk (firstZero_unique h hi)]
        · simp
      rw [sum]
      by_cases he : i.val < 2
      · have hex : ∃ k : Fin L, FirstZero b k ∧ k.val < 2 := ⟨i,hi,he⟩
        have chosen : hex.choose = i := firstZero_unique hex.choose_spec.1 hi
        rw [referenceHead, dite_eq_left hex, chosen, Fin.cases_succ]
        simp [numerical,hi,show ¬2 ≤ i.val by omega,hb]
      · have no : ¬∃ k : Fin L, FirstZero b k ∧ k.val < 2 := by
          rintro ⟨k,hk,hlt⟩
          have := firstZero_unique hk hi
          subst k
          exact he hlt
        rw [referenceHead, dite_eq_right no, Fin.cases_zero]
        simp [baseline,hb,show 2 ≤ i.val by omega]
  rw [anchor_eq_reference]
  simp only [fullReward, each, Finset.sum_add_distrib]
  simp

def completeCost {L : ℕ} (stop : Bool) (y : FullScore L) : ℝ :=
  completeSupport stop y - anchor y

/-- Each native output fiber is the union of precisely its assigned local cells. -/
theorem catalog_fiber_sum {L : ℕ} (stop : Bool) (μ : Word L → ℝ)
    (s : Schedule L) (a : Fin 4 → Fin (L + 1)) (r : Fin (L + 1)) :
    (∑ b, if evaluate stop s a b = r then μ b else 0) =
      ∑ c, if a c = r then catalogReading stop μ s c else 0 := by
  classical
  symm
  calc
    _ = ∑ c, ∑ b, if catalogCell stop s b = c then
        (if a c = r then μ b else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases h : a c = r <;> simp [h,catalogReading]
    _ = _ := by
      rw [Finset.sum_comm]
      simp [evaluate]
      rfl

/-- Individual stopped-cell readings agree exactly when every original Catalog
output fiber has the same mass. This also includes dimension zero. -/
theorem same_readings_iff_catalog {L : ℕ} (μ ν : Word L → ℝ) :
    SameReadings μ ν ↔ ∀ f : Catalog true L, ∀ r,
      (∑ b, if f.val b = r then μ b else 0) = ∑ b, if f.val b = r then ν b else 0 := by
  classical
  constructor
  · intro h f r
    obtain ⟨s,a,ha⟩ := (catalog_range true f.val).mp f.property
    rw [← ha,catalog_fiber_sum,catalog_fiber_sum]
    apply Finset.sum_congr rfl
    intro c _
    by_cases he : a c = r
    · simp only [ite_eq_left he]
      by_cases hc : c.val < 3
      · let d : Fin 3 := ⟨c.val,hc⟩
        have eq : d.castSucc = c := by apply Fin.ext; rfl
        rw [← eq]
        simpa only [catalogReading,catalogCell,ite_true,Fin.castSucc_inj,reading] using h s d
      · have eq : c = (3 : Fin 4) := by
          apply Fin.ext
          have := c.isLt
          change c.val = 3
          omega
        subst c
        have empty (w : Word L) : (cell s w).castSucc ≠ (3 : Fin 4) := by
          exact (by decide : ∀ k : Fin 3, k.castSucc ≠ (3 : Fin 4)) (cell s w)
        simp [catalogReading,catalogCell,empty]
    · simp [he]
  · intro h
    by_cases hL : 0 < L
    · intro s c
      let a : Fin 4 → Fin (L + 1) := fun k => if k = c.castSucc then 0 else (⟨0,hL⟩ : Fin L).succ
      have eq := h ⟨evaluate true s a, evaluated_in_catalog true s a⟩ 0
      simpa [evaluate,a,catalogCell,reading] using eq
    · have eq := h (⟨fun _ => 0,[],by simp,by simp,by simp,by simp⟩ : Catalog true L) 0
      have total : (∑ b, μ b) = ∑ b, ν b := by simpa using eq
      have zero : L = 0 := by omega
      subst L
      intro s c
      cases s with
      | inl => fin_cases c <;> simpa [reading,cell] using total
      | inr s =>
        cases s with
        | inl i => exact Fin.elim0 i
        | inr a => exact Fin.elim0 a.val.1

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.JointRewardFiberObstruction
