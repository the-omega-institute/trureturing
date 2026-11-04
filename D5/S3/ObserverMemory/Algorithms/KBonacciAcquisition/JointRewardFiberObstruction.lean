/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/JointRewardFiberObstruction
   mirror-E: none(waiver:symbolic-finite-measures)
   anchors: []
   utility: none
   digest: Complete stopped rewards force disjoint baseline and numerical support in the three-bit obstruction. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.JointRewardFiberCatalog

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.JointRewardFiberObstruction

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
  rw [anchor_eq_formula]
  simp only [witnessScore,splitrow,Finset.sum_const_zero,add_zero]
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
  rw [complete_support_eq_local]
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

private theorem native_dominance {L : ℕ} (stop : Bool) (n j k l : Fin L)
    (hjk : j < k) (hkl : k < l) (t : ℝ) (ht : 0 ≤ t)
    (f : Catalog stop L) (r : Fin (L + 1)) :
    (∑ b, if f.val b = r then point (baseWord n j k l) t b else 0) ≤
      ∑ b, if f.val b = r then threePoints n j k l t b else 0 := by
  classical
  obtain ⟨s,a,ha⟩ := (catalog_range stop f.val).mp f.property
  rw [← ha,catalog_fiber_sum,catalog_fiber_sum]
  apply Finset.sum_le_sum
  intro c _
  split_ifs
  · exact catalog_dominance stop n j k l hjk hkl t ht s c
  · exact le_rfl

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
    classical
    let a : Fin 4 → Fin (L + 1) := fun k => if k = c then 0 else n.succ
    have h := native_dominance stop n j k l hjk hkl t ht.le
      ⟨evaluate stop s a, evaluated_in_catalog stop s a⟩ 0
    simpa [evaluate,a,catalogReading,witness_baseline,witness_numerical] using h


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

open Classical in
def fiberMassSet {L : ℕ} (y : FullScore L) : Set ℝ :=
  {r | ∃ z : FullScore L, (beta z = beta y ∧
    (∀ f : Catalog true L, ∀ a,
      (∑ b, if f.val b = a then baseline z b else 0) =
        ∑ b, if f.val b = a then baseline y b else 0) ∧
    (∀ i, ∀ f : Catalog true L, ∀ a,
      (∑ b, if f.val b = a then numerical z i b else 0) =
        ∑ b, if f.val b = a then numerical y i b else 0)) ∧ coefficientMass z = r}

private theorem fiber_mass_set_eq_local {L : ℕ} (y : FullScore L) :
    fiberMassSet y = {r | ∃ z, SameFiber z y ∧ coefficientMass z = r} := by
  classical
  ext r
  simp only [fiberMassSet,Set.mem_setOf_eq,SameFiber,same_readings_iff_catalog]


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
    rw [fiber_mass_set_eq_local]
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
