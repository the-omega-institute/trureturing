/- GID: D5/S3/Arith/Primes/ProfiniteObservationClock
   generality: G
   mirror-B: D5/B/S3/Arith/Primes/ProfiniteObservationClock
   mirror-E: none(waiver:exact-cofinal-clock)
   anchors: []
   utility: none
   digest: Absolute-time labels identify exact cofinal observation clocks with the profinite adding machine. -/

import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Exact cofinal observation clocks

Exact eventual collision kernels label states by absolute time, even when
individual observation thresholds differ. A divisibility-cofinal directed
tower then reconstructs every compatible residue clock, and native
advancement agrees with addition by one.
-/

namespace WSSProfiniteClock

universe u v

/-- The compatibility direction is from a finer observation j to a
coarser observation i. Values are exact representatives, not chosen origins. -/
structure Labels {I : Type u} (P : I → ℕ) (refines : I → I → Prop) where
  value : ∀ i, Fin (P i)
  compatible : ∀ {i j}, refines i j → (value j).val ≡ (value i).val [MOD P i]

namespace Labels
variable {I : Type u} {P : I → ℕ} {refines : I → I → Prop}

@[ext] theorem ext' {x y : Labels P refines} (h : ∀ i, x.value i = y.value i) : x = y := by
  cases x with | mk xv hc =>
  cases y with | mk yv hd =>
  have he : xv = yv := funext h
  subst yv
  rfl

/-- Absolute label shift by n, including the finite adding-machine action. -/
def shift (pos : ∀ i, 0 < P i) (divides : ∀ {i j}, refines i j → P i ∣ P j)
    (x : Labels P refines) (n : ℕ) : Labels P refines where
  value i := ⟨((x.value i).val+n) % P i, Nat.mod_lt _ (pos i)⟩
  compatible {_i _j} h :=
    (((Nat.mod_modEq _ _).of_dvd (divides h)).trans ((x.compatible h).add_right n)).trans
      (Nat.mod_modEq _ _).symm

theorem shift_add (pos : ∀ i, 0 < P i) (divides : ∀ {i j}, refines i j → P i ∣ P j)
    (x : Labels P refines) (n k : ℕ) :
    shift pos divides (shift pos divides x n) k = shift pos divides x (n+k) := by
  apply ext'
  intro i
  apply Fin.ext
  change ((((x.value i).val+n) % P i+k) % P i) = ((x.value i).val+(n+k)) % P i
  rw [← Nat.add_assoc]
  exact (Nat.mod_modEq _ _).add_right k

theorem shift_zero (pos : ∀ i, 0 < P i) (divides : ∀ {i j}, refines i j → P i ∣ P j)
    (x : Labels P refines) : shift pos divides x 0 = x := by
  apply ext'
  intro i
  apply Fin.ext
  change ((x.value i).val+0) % P i = (x.value i).val
  rw [Nat.add_zero, Nat.mod_eq_of_lt (x.value i).isLt]

end Labels

/-- All positive moduli, with the ordinary divisibility reductions.
This is the underlying set of the profinite integer clock. -/
abbrev Positive := {n : ℕ // 0 < n}
abbrev EveryClock := Labels (fun m : Positive => m.val) (fun m n => m.val ∣ n.val)

/-- An observation tower with a common upper observation for every pair.
Its periods are positive, monotone along refinement, and divisibility-cofinal. -/
structure CofinalTower {I : Type u} (P : I → ℕ) (refines : I → I → Prop) where
  positive : ∀ i, 0 < P i
  directed : ∀ i j, ∃ k, refines i k ∧ refines j k
  divides : ∀ {i j}, refines i j → P i ∣ P j
  cofinal : ∀ m : Positive, ∃ i, m.val ∣ P i

namespace CofinalTower
variable {I : Type u} {P : I → ℕ} {refines : I → I → Prop}

private theorem agree_at_divisor (C : CofinalTower P refines) (x : Labels P refines)
    {i j : I} {m : ℕ} (hi : m ∣ P i) (hj : m ∣ P j) :
    (x.value i).val ≡ (x.value j).val [MOD m] := by
  obtain ⟨k, hik, hjk⟩ := C.directed i j
  exact ((x.compatible hik).of_dvd hi).symm.trans ((x.compatible hjk).of_dvd hj)

/-- Restrict an all-moduli time to the observation periods. -/
def restrict (C : CofinalTower P refines) (x : EveryClock) : Labels P refines where
  value i := x.value ⟨P i, C.positive i⟩
  compatible {i j} h := x.compatible (i := ⟨P i, C.positive i⟩)
    (j := ⟨P j, C.positive j⟩) (C.divides h)

/-- Extend uniquely by reducing from any observation with divisible
period. Choice independence is proved by the common refinement. -/
noncomputable def extend (C : CofinalTower P refines) (x : Labels P refines) : EveryClock where
  value m := ⟨(x.value (Classical.choose (C.cofinal m))).val % m.val, Nat.mod_lt _ m.prop⟩
  compatible {m n} h := by
    let a := Classical.choose (C.cofinal m)
    let b := Classical.choose (C.cofinal n)
    have ha : m.val ∣ P a := Classical.choose_spec (C.cofinal m)
    have hb : n.val ∣ P b := Classical.choose_spec (C.cofinal n)
    have hba := agree_at_divisor C x (dvd_trans h hb) ha
    exact (((Nat.mod_modEq _ _).of_dvd h).trans hba).trans (Nat.mod_modEq _ _).symm

theorem restrict_extend (C : CofinalTower P refines) (x : Labels P refines) :
    C.restrict (C.extend x) = x := by
  apply Labels.ext'
  intro i
  apply Fin.ext
  let m : Positive := ⟨P i, C.positive i⟩
  have hc := agree_at_divisor C x (Classical.choose_spec (C.cofinal m)) (dvd_refl (P i))
  exact Eq.trans hc (Nat.mod_eq_of_lt (x.value i).isLt)

theorem extend_restrict (C : CofinalTower P refines) (x : EveryClock) :
    C.extend (C.restrict x) = x := by
  apply Labels.ext'
  intro m
  apply Fin.ext
  have hc := x.compatible (i := m)
    (j := ⟨P (Classical.choose (C.cofinal m)), C.positive _⟩)
    (Classical.choose_spec (C.cofinal m))
  exact Eq.trans hc (Nat.mod_eq_of_lt (x.value m).isLt)

/-- Cofinal restrictions lose no compatible absolute time data. -/
noncomputable def equiv (C : CofinalTower P refines) : EveryClock ≃ Labels P refines where
  toFun := C.restrict
  invFun := C.extend
  left_inv := C.extend_restrict
  right_inv := C.restrict_extend

/-- Advancement commutes exactly with cofinal restriction. -/
theorem restrict_shift (C : CofinalTower P refines) (x : EveryClock) (n : ℕ) :
    C.restrict (Labels.shift (fun m : Positive => m.prop) (fun h => h) x n) =
      Labels.shift C.positive C.divides (C.restrict x) n := by
  apply Labels.ext'
  intro i
  apply Fin.ext
  rfl

end CofinalTower

/-- One eventual observation cycle, without choosing an origin at the
threshold A. -/
def TailState {S : Type v} (observe : ℕ → S) (A : ℕ) :=
  {s : S // ∃ n, A ≤ n ∧ observe n = s}

namespace TailState
variable {S : Type v} {observe : ℕ → S} {A P : ℕ}

def atTime (observe : ℕ → S) (A n : ℕ) (hn : A ≤ n) : TailState observe A :=
  ⟨observe n, n, hn, rfl⟩

/-- The time representative is an absolute observation index. -/
noncomputable def label (pos : 0 < P) (s : TailState observe A) : Fin P :=
  ⟨Classical.choose s.prop % P, Nat.mod_lt _ pos⟩

theorem label_eq_of_observed (pos : 0 < P)
    (kernel : ∀ n m, A ≤ n → A ≤ m → (observe n = observe m ↔ n ≡ m [MOD P]))
    (s : TailState observe A) {n : ℕ} (hn : A ≤ n) (he : observe n = s.val) :
    (s.label pos).val = n % P := by
  apply (kernel (Classical.choose s.prop) n (Classical.choose_spec s.prop).1 hn).mp
  exact (Classical.choose_spec s.prop).2.trans he.symm

theorem label_atTime (pos : 0 < P)
    (kernel : ∀ n m, A ≤ n → A ≤ m → (observe n = observe m ↔ n ≡ m [MOD P]))
    {n : ℕ} (hn : A ≤ n) :
    (label pos (atTime observe A n hn)).val = n % P :=
  label_eq_of_observed pos kernel _ hn rfl

/-- Exact finite clock: the eventual observation image is precisely Fin P. -/
noncomputable def equiv (pos : 0 < P)
    (kernel : ∀ n m, A ≤ n → A ≤ m → (observe n = observe m ↔ n ≡ m [MOD P])) :
    TailState observe A ≃ Fin P := by
  apply Equiv.ofBijective (label pos)
  constructor
  · intro s t h
    have hc : Classical.choose s.prop ≡ Classical.choose t.prop [MOD P] :=
      congrArg Fin.val h
    have he := (kernel _ _ (Classical.choose_spec s.prop).1
      (Classical.choose_spec t.prop).1).mpr hc
    apply Subtype.ext
    exact (Classical.choose_spec s.prop).2.symm.trans
      (he.trans (Classical.choose_spec t.prop).2)
  · intro k
    let n := k.val + P*A
    have hA : A ≤ P*A := by
      simpa using (Nat.mul_le_mul_right A (show 1 ≤ P from pos))
    have hn : A ≤ n := by dsimp [n]; omega
    have hk : n % P = k.val := by
      simp [n, Nat.add_mod, Nat.mod_eq_of_lt k.isLt]
    refine ⟨atTime observe A n hn, Fin.ext ?_⟩
    exact (label_atTime pos kernel hn).trans hk

/-- A clock difference depends only on the absolute label, not the late
time representative. This gives the finite shift cocycle. -/
theorem added_time_label (pos : 0 < P)
    (kernel : ∀ n m, A ≤ n → A ≤ m → (observe n = observe m ↔ n ≡ m [MOD P]))
    (n k : ℕ) (hn : A ≤ n) :
    (label pos (atTime observe A (n+k) (by omega))).val =
      ((label pos (atTime observe A n hn)).val+k) % P := by
  rw [label_atTime pos kernel, label_atTime pos kernel hn]
  exact ((Nat.mod_modEq _ _).add_right k).symm

end TailState

/-- Exact kernels plus observation reduction force period divisibility.
The eventual thresholds need not be monotone. -/
theorem period_dvd_of_refinement {S T : Type v}
    (f : ℕ → S) (g : ℕ → T) (reduce : T → S)
    (A B P Q : ℕ)
    (kf : ∀ n m, A ≤ n → A ≤ m → (f n = f m ↔ n ≡ m [MOD P]))
    (kg : ∀ n m, B ≤ n → B ≤ m → (g n = g m ↔ n ≡ m [MOD Q]))
    (hred : ∀ n, reduce (g n) = f n) : P ∣ Q := by
  let n := max A B
  have hA : A ≤ n := le_max_left _ _
  have hB : B ≤ n := le_max_right _ _
  have hle : n ≤ n+Q := by omega
  have hg := (kg n (n+Q) hB (hB.trans hle)).mpr
    ((Nat.modEq_iff_dvd' hle).mpr (by simp))
  have hf : f n = f (n+Q) := by rw [← hred n, ← hred (n+Q), hg]
  have hh := (Nat.modEq_iff_dvd' hle).mp ((kf n (n+Q) hA (hA.trans hle)).mp hf)
  simpa using hh

namespace TailState
variable {S : Type v} {observe : ℕ → S} {A P : ℕ}

/-- A limit coordinate has arbitrarily late exact realizations, not
merely one clock representative near its starting threshold. -/
theorem late_representative (pos : 0 < P)
    (kernel : ∀ n m, A ≤ n → A ≤ m → (observe n = observe m ↔ n ≡ m [MOD P]))
    (s : TailState observe A) (B : ℕ) :
    ∃ n, A ≤ n ∧ B ≤ n ∧ observe n = s.val := by
  obtain ⟨a,ha,he⟩ := s.prop
  let n := a + P*B
  have hB : B ≤ P*B := by simpa using (Nat.mul_le_mul_right B (show 1 ≤ P from pos))
  have hle : a ≤ n := by dsimp [n]; omega
  have hn : A ≤ n := ha.trans hle
  have hBa : B ≤ n := by dsimp [n]; omega
  have hmod : a ≡ n [MOD P] :=
    (Nat.modEq_iff_dvd' hle).mpr (by dsimp [n]; simp)
  exact ⟨n, hn, hBa, ((kernel a n ha hn).mpr hmod).symm.trans he⟩

end TailState

/-- Exact eventually periodic observations, retaining their native
reduction maps and potentially different transient thresholds. -/
structure ObservationSystem {I : Type u} (P : I → ℕ) (refines : I → I → Prop) where
  State : I → Type v
  observe : ∀ i, ℕ → State i
  threshold : I → ℕ
  positive : ∀ i, 0 < P i
  kernel : ∀ i n m, threshold i ≤ n → threshold i ≤ m →
    (observe i n = observe i m ↔ n ≡ m [MOD P i])
  reduce : ∀ {i j}, refines i j → State j → State i
  reduce_observe : ∀ {i j} (h : refines i j) n, reduce h (observe j n) = observe i n

namespace ObservationSystem
variable {I : Type u} {P : I → ℕ} {refines : I → I → Prop}

theorem divides (O : ObservationSystem P refines) {i j : I} (h : refines i j) :
    P i ∣ P j :=
  period_dvd_of_refinement _ _ (O.reduce h) _ _ _ _ (O.kernel i) (O.kernel j)
    (O.reduce_observe h)

theorem tower (O : ObservationSystem P refines)
    (directed : ∀ i j, ∃ k, refines i k ∧ refines j k)
    (cofinal : ∀ m : Positive, ∃ i, m.val ∣ P i) : CofinalTower P refines :=
  ⟨O.positive, directed, O.divides, cofinal⟩

/-- Inverse-limit state families with finite coordinates in the exact
eventual observation cycles. -/
structure Family (O : ObservationSystem P refines) where
  state : ∀ i, TailState (O.observe i) (O.threshold i)
  compatible : ∀ {i j} (h : refines i j), O.reduce h (state j).val = (state i).val

@[ext] theorem Family.ext' {O : ObservationSystem P refines} {x y : O.Family}
    (h : ∀ i, x.state i = y.state i) : x = y := by
  cases x with | mk xs hx =>
  cases y with | mk ys hy =>
  have he : xs = ys := funext h
  subst ys
  rfl

noncomputable def toLabels (O : ObservationSystem P refines) (x : O.Family) : Labels P refines where
  value i := TailState.label (O.positive i) (x.state i)
  compatible {i j} h := by
    obtain ⟨n, hnj, hni, he⟩ := TailState.late_representative
      (O.positive j) (O.kernel j) (x.state j) (O.threshold i)
    have hi : O.observe i n = (x.state i).val := by
      rw [← O.reduce_observe h n, he, x.compatible h]
    rw [TailState.label_eq_of_observed (O.positive j) (O.kernel j) _ hnj he,
      TailState.label_eq_of_observed (O.positive i) (O.kernel i) _ hni hi]
    exact ((Nat.mod_modEq _ _).of_dvd (O.divides h)).trans (Nat.mod_modEq _ _).symm

noncomputable def fromLabels (O : ObservationSystem P refines) (x : Labels P refines) : O.Family where
  state i := (TailState.equiv (O.positive i) (O.kernel i)).symm (x.value i)
  compatible {i j} h := by
    let sj := (TailState.equiv (O.positive j) (O.kernel j)).symm (x.value j)
    let si := (TailState.equiv (O.positive i) (O.kernel i)).symm (x.value i)
    obtain ⟨n, hnj, hni, he⟩ := TailState.late_representative
      (O.positive j) (O.kernel j) sj (O.threshold i)
    have hlabelj : (TailState.label (O.positive j) sj).val = (x.value j).val :=
      congrArg Fin.val ((TailState.equiv (O.positive j) (O.kernel j)).apply_symm_apply _)
    have hnmod := TailState.label_eq_of_observed (O.positive j) (O.kernel j) sj hnj he
    have hxij : n ≡ (x.value i).val [MOD P i] := by
      have hc := x.compatible h
      rw [← hlabelj, hnmod] at hc
      exact (((Nat.mod_modEq n (P j)).of_dvd (O.divides h)).symm).trans hc
    have hh : TailState.atTime (O.observe i) (O.threshold i) n hni = si := by
      apply (TailState.equiv (O.positive i) (O.kernel i)).injective
      apply Fin.ext
      change (TailState.label (O.positive i) (TailState.atTime (O.observe i) (O.threshold i) n hni)).val =
        (TailState.label (O.positive i) si).val
      rw [TailState.label_atTime (O.positive i) (O.kernel i) hni]
      have hi : (TailState.label (O.positive i) si).val = (x.value i).val :=
        congrArg Fin.val ((TailState.equiv (O.positive i) (O.kernel i)).apply_symm_apply _)
      exact Eq.trans hxij ((Nat.mod_eq_of_lt (x.value i).isLt).trans hi.symm)
    change O.reduce h sj.val = si.val
    rw [← he, O.reduce_observe]
    exact congrArg Subtype.val hh

/-- Inverse-limit eventual states and compatible period labels are
naturally equivalent, with no arbitrary finite origin shifts. -/
noncomputable def familyEquiv (O : ObservationSystem P refines) : O.Family ≃ Labels P refines where
  toFun := O.toLabels
  invFun := O.fromLabels
  left_inv x := by
    apply Family.ext'
    intro i
    exact (TailState.equiv (O.positive i) (O.kernel i)).symm_apply_apply _
  right_inv x := by
    apply Labels.ext'
    intro i
    exact (TailState.equiv (O.positive i) (O.kernel i)).apply_symm_apply _

noncomputable def allClockEquiv (O : ObservationSystem P refines)
    (directed : ∀ i j, ∃ k, refines i k ∧ refines j k)
    (cofinal : ∀ m : Positive, ∃ i, m.val ∣ P i) : EveryClock ≃ O.Family :=
  (O.tower directed cofinal).equiv.trans O.familyEquiv.symm

/-- Every inverse-limit state family is realized arbitrarily late on
an entire coarse cylinder with one common finer observation. -/
theorem late_cone (O : ObservationSystem P refines) (x : O.Family)
    (j : I) (B : ℕ) :
    ∃ n, B ≤ n ∧ O.observe j n = (x.state j).val ∧
      ∀ i, ∀ _h : refines i j, O.observe i n = (x.state i).val := by
  obtain ⟨n, _, hnB, hnj⟩ := TailState.late_representative
    (O.positive j) (O.kernel j) (x.state j) B
  exact ⟨n, hnB, hnj, fun i h => ((O.reduce_observe h n).symm.trans
    (congrArg (O.reduce h) hnj)).trans (x.compatible h)⟩

end ObservationSystem

namespace Labels
variable {I : Type u} {P : I → ℕ} {refines : I → I → Prop}

private theorem predecessor_delta (pos : ∀ i, 0 < P i)
    (divides : ∀ {i j}, refines i j → P i ∣ P j) {i j : I} (h : refines i j) :
    P j-1 ≡ P i-1 [MOD P i] := by
  apply Nat.ModEq.add_right_cancel' 1
  rw [Nat.sub_add_cancel (show 1 ≤ P j from pos j),
    Nat.sub_add_cancel (show 1 ≤ P i from pos i)]
  exact (divides h).modEq_zero_nat.trans (dvd_refl (P i)).modEq_zero_nat.symm

/-- Subtract one compatibly, without assuming that any label is positive. -/
def previous (pos : ∀ i, 0 < P i) (divides : ∀ {i j}, refines i j → P i ∣ P j)
    (x : Labels P refines) : Labels P refines where
  value i := ⟨((x.value i).val+(P i-1)) % P i, Nat.mod_lt _ (pos i)⟩
  compatible {_i _j} h :=
    (((Nat.mod_modEq _ _).of_dvd (divides h)).trans
      ((x.compatible h).add (predecessor_delta pos divides h))).trans (Nat.mod_modEq _ _).symm

private theorem add_period_modEq (x P : ℕ) : x+P ≡ x [MOD P] :=
  Nat.ModEq.add_left x (dvd_refl P).modEq_zero_nat

theorem previous_next (pos : ∀ i, 0 < P i) (divides : ∀ {i j}, refines i j → P i ∣ P j)
    (x : Labels P refines) : previous pos divides (shift pos divides x 1) = x := by
  apply ext'
  intro i
  apply Fin.ext
  let a := (x.value i).val
  change (((a+1) % P i+(P i-1)) % P i) = a
  have h := (Nat.mod_modEq (a+1) (P i)).add_right (P i-1)
  rw [show a+1+(P i-1) = a+P i by have := pos i; omega] at h
  exact Eq.trans (h.trans (add_period_modEq a (P i))) (Nat.mod_eq_of_lt (x.value i).isLt)

theorem next_previous (pos : ∀ i, 0 < P i) (divides : ∀ {i j}, refines i j → P i ∣ P j)
    (x : Labels P refines) : shift pos divides (previous pos divides x) 1 = x := by
  apply ext'
  intro i
  apply Fin.ext
  let a := (x.value i).val
  change (((a+(P i-1)) % P i+1) % P i) = a
  have h := (Nat.mod_modEq (a+(P i-1)) (P i)).add_right 1
  rw [show a+(P i-1)+1 = a+P i by have := pos i; omega] at h
  exact Eq.trans (h.trans (add_period_modEq a (P i))) (Nat.mod_eq_of_lt (x.value i).isLt)

/-- Translation by one is a bijection even at the inverse limit. -/
def nextEquiv (pos : ∀ i, 0 < P i) (divides : ∀ {i j}, refines i j → P i ∣ P j) :
    Labels P refines ≃ Labels P refines where
  toFun x := shift pos divides x 1
  invFun := previous pos divides
  left_inv := previous_next pos divides
  right_inv := next_previous pos divides

end Labels

def EveryClock.next : EveryClock ≃ EveryClock :=
  Labels.nextEquiv (fun m : Positive => m.prop) (fun h => h)

namespace ObservationSystem
variable {I : Type u} {P : I → ℕ} {refines : I → I → Prop}

/-- Shift the inverse-limit observation family by one native time step. -/
noncomputable def next (O : ObservationSystem P refines) : O.Family ≃ O.Family :=
  (O.familyEquiv.trans (Labels.nextEquiv O.positive O.divides)).trans O.familyEquiv.symm

/-- The cofinal clock equivalence intertwines actual time advancement. -/
theorem allClock_next (O : ObservationSystem P refines)
    (directed : ∀ i j, ∃ k, refines i k ∧ refines j k)
    (cofinal : ∀ m : Positive, ∃ i, m.val ∣ P i) (x : EveryClock) :
    O.allClockEquiv directed cofinal (EveryClock.next x) =
      O.next (O.allClockEquiv directed cofinal x) := by
  apply O.familyEquiv.injective
  simp only [allClockEquiv, next, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact (O.tower directed cofinal).restrict_shift x 1

/-- If the original observations are generated by a native update,
the abstract shift agrees with that update on every coordinate. -/
theorem next_is_native (O : ObservationSystem P refines)
    (step : ∀ i, O.State i → O.State i)
    (recurrence : ∀ i n, O.observe i (n+1) = step i (O.observe i n))
    (x : O.Family) (i : I) :
    ((O.next x).state i).val = step i (x.state i).val := by
  obtain ⟨n, hn, _, he⟩ := TailState.late_representative
    (O.positive i) (O.kernel i) (x.state i) 0
  let t := TailState.atTime (O.observe i) (O.threshold i) (n+1) (by omega)
  have hv : (O.next x).state i = t := by
    apply (TailState.equiv (O.positive i) (O.kernel i)).injective
    apply Fin.ext
    have hEq : O.familyEquiv (O.next x) = Labels.nextEquiv O.positive O.divides (O.familyEquiv x) := by
      simp only [next, Equiv.trans_apply, Equiv.apply_symm_apply]
    have hz := congrArg (fun y : Labels P refines => (y.value i).val) hEq
    change (TailState.label (O.positive i) ((O.next x).state i)).val =
      (((TailState.label (O.positive i) (x.state i)).val+1) % P i) at hz
    change (TailState.label (O.positive i) ((O.next x).state i)).val =
      (TailState.label (O.positive i) t).val
    rw [hz, TailState.label_eq_of_observed (O.positive i) (O.kernel i) _ hn he]
    dsimp [t]
    rw [TailState.label_atTime (O.positive i) (O.kernel i)]
    exact (Nat.mod_modEq n (P i)).add_right 1
  rw [hv]
  change O.observe i (n+1) = step i (x.state i).val
  rw [recurrence, he]

end ObservationSystem

end WSSProfiniteClock

namespace D5.S3.Arith.Primes.ProfiniteObservationClock
open WSSProfiniteClock
universe u v

/-- The exact absolute-label equivalence on the finite eventual image. -/
noncomputable def finiteClock {S : Type v} (f : ℕ → S) (A P : ℕ)
    (pos : 0 < P)
    (kernel : ∀ n m, A ≤ n → A ≤ m → (f n = f m ↔ n ≡ m [MOD P])) :
    TailState f A ≃ Fin P :=
  TailState.equiv pos kernel

/-- The compatible observation family is the all-moduli clock. -/
noncomputable def cofinalClock {I : Type u} {P : I → ℕ} {refines : I → I → Prop}
    (O : ObservationSystem P refines)
    (directed : ∀ i j, ∃ k, refines i k ∧ refines j k)
    (cofinal : ∀ m : Positive, ∃ i, m.val ∣ P i) :
    EveryClock ≃ O.Family :=
  O.allClockEquiv directed cofinal

/-- The cofinal equivalence carries addition by one to observation advancement. -/
theorem cofinalClock_next {I : Type u} {P : I → ℕ} {refines : I → I → Prop}
    (O : ObservationSystem P refines)
    (directed : ∀ i j, ∃ k, refines i k ∧ refines j k)
    (cofinal : ∀ m : Positive, ∃ i, m.val ∣ P i) (x : EveryClock) :
    cofinalClock O directed cofinal (EveryClock.next x) =
      O.next (cofinalClock O directed cofinal x) :=
  O.allClock_next directed cofinal x

end D5.S3.Arith.Primes.ProfiniteObservationClock
