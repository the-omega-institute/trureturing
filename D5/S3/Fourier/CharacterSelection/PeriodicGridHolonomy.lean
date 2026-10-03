/- GID: D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/PeriodicGridHolonomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary flat grid labels split into a vertex differential and two seams. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy

open Finset

private def cycleIntegral {n : ℕ} [NeZero n] (f : Fin n → ZMod 2) (i : Fin n) :
    ZMod 2 := ∑ k ∈ Iio i, f k

private theorem cycleIntegral_step {n : ℕ} [NeZero n] (f : Fin n → ZMod 2)
    (i : Fin n) (hi : i.val + 1 < n) :
    cycleIntegral f (i + 1) = cycleIntegral f i + f i := by
  have hinterval : (Iio (i + 1) : Finset (Fin n)) = Iic i := by
    ext k
    simp only [mem_Iio, mem_Iic]
    change k.val < (i + 1).val ↔ k.val ≤ i.val
    simp [Fin.val_add, Nat.mod_eq_of_lt hi]
  rw [cycleIntegral, hinterval, Finset.Iic_eq_cons_Iio, Finset.sum_cons]
  simp [cycleIntegral, add_comm]

private theorem cycleIntegral_wrap {n : ℕ} [NeZero n] (f : Fin n → ZMod 2)
    (i : Fin n) (hi : i.val + 1 = n) :
    cycleIntegral f (i + 1) + cycleIntegral f i =
      f i + ∑ k : Fin n, f k := by
  have hsucc : i + 1 = (0 : Fin n) := by
    apply Fin.ext
    simp [Fin.val_add, hi]
  have hall : (∑ k : Fin n, f k) = cycleIntegral f i + f i := by
    have hset : (Finset.univ : Finset (Fin n)) = Iic i := by
      ext k
      simp only [mem_univ, mem_Iic, true_iff]
      change k.val ≤ i.val
      omega
    rw [hset, Finset.Iic_eq_cons_Iio, Finset.sum_cons]
    simp [cycleIntegral, add_comm]
  have hzero : cycleIntegral f 0 = 0 := by
    simp [cycleIntegral, show (0 : Fin n) = ⊥ from rfl, Finset.Iio_bot]
  rw [hsucc, hzero, hall]
  simp only [zero_add]
  calc
    cycleIntegral f i = cycleIntegral f i + (f i + f i) := by
      rw [ZModModule.add_self, add_zero]
    _ = f i + (cycleIntegral f i + f i) := by abel

private theorem cycleIntegral_next {n : ℕ} [NeZero n] (f : Fin n → ZMod 2)
    (i : Fin n) :
    cycleIntegral f (i + 1) + cycleIntegral f i =
      f i + (if i.val + 1 = n then ∑ k : Fin n, f k else 0) := by
  by_cases hi : i.val + 1 = n
  · simpa only [if_pos hi] using cycleIntegral_wrap f i hi
  · have hlt : i.val + 1 < n := by omega
    rw [if_neg hi, cycleIntegral_step f i hlt]
    simp only [add_zero]
    calc
      cycleIntegral f i + f i + cycleIntegral f i =
          f i + (cycleIntegral f i + cycleIntegral f i) := by abel
      _ = f i := by rw [ZModModule.add_self, add_zero]

structure EdgeLabel (M N : ℕ) where
  horizontal : Fin M → Fin N → ZMod 2
  vertical : Fin M → Fin N → ZMod 2

noncomputable instance edgeLabelFintype (M N : ℕ) : Fintype (EdgeLabel M N) :=
  Fintype.ofEquiv
    ((Fin M → Fin N → ZMod 2) × (Fin M → Fin N → ZMod 2))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun y => (y.horizontal, y.vertical)
      left_inv := by intro p; cases p; rfl
      right_inv := by intro y; cases y; rfl }

def plaquette {M N : ℕ} [NeZero M] [NeZero N] (y : EdgeLabel M N)
    (i : Fin M) (j : Fin N) : ZMod 2 :=
  y.horizontal i j + y.vertical i (j + 1) +
    y.horizontal (i + 1) j + y.vertical i j

def Flat {M N : ℕ} [NeZero M] [NeZero N] (y : EdgeLabel M N) : Prop :=
  ∀ i j, plaquette y i j = 0

def rowHolonomy {M N : ℕ} (y : EdgeLabel M N) (i : Fin M) : ZMod 2 :=
  ∑ j : Fin N, y.horizontal i j

def columnHolonomy {M N : ℕ} (y : EdgeLabel M N) (j : Fin N) : ZMod 2 :=
  ∑ i : Fin M, y.vertical i j

def gradient {M N : ℕ} [NeZero M] [NeZero N]
    (x : Fin M → Fin N → ZMod 2) : EdgeLabel M N where
  horizontal i j := x i (j + 1) + x i j
  vertical i j := x (i + 1) j + x i j

def seam {M N : ℕ} [NeZero M] [NeZero N] (h v : ZMod 2) : EdgeLabel M N where
  horizontal _ j := if j.val + 1 = N then h else 0
  vertical i _ := if i.val + 1 = M then v else 0

private theorem sum_plaquette_row {M N : ℕ} [NeZero M] [NeZero N]
    (y : EdgeLabel M N) (i : Fin M) :
    (∑ j : Fin N, plaquette y i j) =
      rowHolonomy y i + rowHolonomy y (i + 1) := by
  simp only [plaquette, rowHolonomy, Finset.sum_add_distrib]
  have hshift : (∑ j : Fin N, y.vertical i (j + 1)) =
      ∑ j : Fin N, y.vertical i j :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin N))
      (fun j => y.vertical i (j + 1)) (y.vertical i) (fun _ => rfl)
  rw [hshift]
  let a := ∑ j : Fin N, y.horizontal i j
  let b := ∑ j : Fin N, y.vertical i j
  let c := ∑ j : Fin N, y.horizontal (i + 1) j
  change a + b + c + b = a + c
  calc
    a + b + c + b = a + c + (b + b) := by abel
    _ = a + c := by rw [ZModModule.add_self, add_zero]

private theorem sum_plaquette_column {M N : ℕ} [NeZero M] [NeZero N]
    (y : EdgeLabel M N) (j : Fin N) :
    (∑ i : Fin M, plaquette y i j) =
      columnHolonomy y j + columnHolonomy y (j + 1) := by
  simp only [plaquette, columnHolonomy, Finset.sum_add_distrib]
  have hshift : (∑ i : Fin M, y.horizontal (i + 1) j) =
      ∑ i : Fin M, y.horizontal i j :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin M))
      (fun i => y.horizontal (i + 1) j) (fun i => y.horizontal i j) (fun _ => rfl)
  rw [hshift]
  let a := ∑ i : Fin M, y.vertical i j
  let b := ∑ i : Fin M, y.horizontal i j
  let c := ∑ i : Fin M, y.vertical i (j + 1)
  change b + c + b + a = a + c
  calc
    b + c + b + a = a + c + (b + b) := by abel
    _ = a + c := by rw [ZModModule.add_self, add_zero]

private theorem cycle_constant {n : ℕ} [NeZero n]
    (f : Fin n → ZMod 2) (hf : ∀ i, f (i + 1) = f i) :
    ∀ i, f i = f 0 := by
  intro i
  have hn : 0 < n := NeZero.pos n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    refine ⟨n - 1, ?_⟩
    omega
  refine Fin.induction ?_ ?_ i
  · rfl
  · intro j ih
    have heq : (Fin.castSucc j : Fin (k + 1)) + 1 = j.succ := by
      apply Fin.ext
      simp
    rw [← heq, hf, ih]

theorem flat_holonomy_constant {M N : ℕ} [NeZero M] [NeZero N]
    (y : EdgeLabel M N) (hy : Flat y) :
    (∀ i, rowHolonomy y i = rowHolonomy y 0) ∧
      (∀ j, columnHolonomy y j = columnHolonomy y 0) := by
  constructor
  · apply cycle_constant
    intro i
    have hp := sum_plaquette_row y i
    have hz : (∑ j : Fin N, plaquette y i j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact hy i j
    rw [hz] at hp
    have hh : rowHolonomy y i + rowHolonomy y (i + 1) = 0 := hp.symm
    have hc := ZModModule.add_self (rowHolonomy y i)
    exact add_left_cancel (hh.trans hc.symm)
  · apply cycle_constant
    intro j
    have hp := sum_plaquette_column y j
    have hz : (∑ i : Fin M, plaquette y i j) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact hy i j
    rw [hz] at hp
    have hh : columnHolonomy y j + columnHolonomy y (j + 1) = 0 := hp.symm
    have hc := ZModModule.add_self (columnHolonomy y j)
    exact add_left_cancel (hh.trans hc.symm)

private def lastIndex (n : ℕ) [NeZero n] : Fin n :=
  ⟨n - 1, by have hn := NeZero.pos n; omega⟩

private theorem cycleIntegral_boundary {n : ℕ} [NeZero n]
    (f : Fin n → ZMod 2) :
    ∀ j, cycleIntegral (fun k => f (k + 1) + f k) j = f j + f 0 := by
  intro j
  have hn : 0 < n := NeZero.pos n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    refine ⟨n - 1, ?_⟩
    omega
  refine Fin.induction ?_ ?_ j
  · simp [cycleIntegral, show (0 : Fin (m + 1)) = ⊥ from rfl,
      Finset.Iio_bot, ZModModule.add_self]
  · intro k ih
    have heq : (Fin.castSucc k : Fin (m + 1)) + 1 = k.succ := by
      apply Fin.ext
      simp
    have hstep : cycleIntegral (fun t : Fin (m + 1) => f (t + 1) + f t) k.succ =
        cycleIntegral (fun t : Fin (m + 1) => f (t + 1) + f t) k.castSucc +
          (f k.succ + f k.castSucc) := by
      rw [← heq]
      have hk : (k.castSucc : Fin (m + 1)).val + 1 < m + 1 := by
        simp
      simpa [heq] using cycleIntegral_step
        (fun t : Fin (m + 1) => f (t + 1) + f t) k.castSucc hk
    rw [hstep, ih]
    have hc := ZModModule.add_self (f k.castSucc)
    calc
      f k.castSucc + f 0 + (f k.succ + f k.castSucc) =
          f k.succ + f 0 + (f k.castSucc + f k.castSucc) := by abel
      _ = f k.succ + f 0 := by rw [hc, add_zero]

private def reconstructedVertex {M N : ℕ} [NeZero M] [NeZero N]
    (y : EdgeLabel M N) (i : Fin M) (j : Fin N) : ZMod 2 :=
  cycleIntegral (fun k => y.vertical k 0) i + cycleIntegral (y.horizontal i) j

theorem flat_decomposition {M N : ℕ} [NeZero M] [NeZero N]
    (y : EdgeLabel M N) (hy : Flat y) :
    ∃ x : Fin M → Fin N → ZMod 2,
      x 0 0 = 0 ∧
      (∀ i j, y.horizontal i j =
        (gradient x).horizontal i j +
          (seam (rowHolonomy y 0) (columnHolonomy y 0)).horizontal i j) ∧
      (∀ i j, y.vertical i j =
        (gradient x).vertical i j +
          (seam (rowHolonomy y 0) (columnHolonomy y 0)).vertical i j) := by
  refine ⟨reconstructedVertex y, ?_, ?_, ?_⟩
  · simp [reconstructedVertex, cycleIntegral,
      show (0 : Fin M) = ⊥ from rfl, show (0 : Fin N) = ⊥ from rfl,
      Finset.Iio_bot]
  · intro i j
    have hrow := (flat_holonomy_constant y hy).1 i
    have hcyc := cycleIntegral_next (y.horizontal i) j
    dsimp [gradient, seam, reconstructedVertex]
    rw [← hrow]
    let v := cycleIntegral (fun k => y.vertical k 0) i
    let a := cycleIntegral (y.horizontal i) (j + 1)
    let b := cycleIntegral (y.horizontal i) j
    let e := if j.val + 1 = N then rowHolonomy y i else 0
    have hcyc' : a + b = y.horizontal i j + e := hcyc
    change y.horizontal i j = (v + a) + (v + b) + e
    have hv := ZModModule.add_self v
    calc
      y.horizontal i j = (y.horizontal i j + e) + e :=
        by rw [add_assoc, ZModModule.add_self, add_zero]
      _ = (a + b) + e := by rw [hcyc']
      _ = ((a + b) + (v + v)) + e := by rw [hv, add_zero]
      _ = (v + a) + (v + b) + e := by abel
  · intro i j
    have hcyc := cycleIntegral_next (fun k => y.vertical k 0) i
    have htransport :
        cycleIntegral (y.horizontal (i + 1)) j +
            cycleIntegral (y.horizontal i) j =
          y.vertical i j + y.vertical i 0 := by
      calc
        cycleIntegral (y.horizontal (i + 1)) j +
            cycleIntegral (y.horizontal i) j =
          cycleIntegral
            (fun k => y.horizontal (i + 1) k + y.horizontal i k) j := by
              simp [cycleIntegral, Finset.sum_add_distrib]
        _ = cycleIntegral
            (fun k => y.vertical i (k + 1) + y.vertical i k) j := by
              congr 1
              funext k
              have hp := hy i k
              dsimp [plaquette] at hp
              have hx :
                  (y.horizontal i k + y.vertical i (k + 1) +
                    y.horizontal (i + 1) k + y.vertical i k) +
                    (y.vertical i (k + 1) + y.vertical i k) =
                    y.horizontal (i + 1) k + y.horizontal i k := by
                calc
                  _ = y.horizontal (i + 1) k + y.horizontal i k +
                      (y.vertical i (k + 1) + y.vertical i (k + 1)) +
                      (y.vertical i k + y.vertical i k) := by abel
                  _ = _ := by rw [ZModModule.add_self, ZModModule.add_self]; simp
              calc
                y.horizontal (i + 1) k + y.horizontal i k =
                    (y.horizontal i k + y.vertical i (k + 1) +
                      y.horizontal (i + 1) k + y.vertical i k) +
                      (y.vertical i (k + 1) + y.vertical i k) := hx.symm
                _ = _ := by rw [hp, zero_add]
        _ = _ := cycleIntegral_boundary (y.vertical i) j
    dsimp [gradient, seam, reconstructedVertex]
    let a := cycleIntegral (fun k => y.vertical k 0) (i + 1)
    let b := cycleIntegral (fun k => y.vertical k 0) i
    let c := cycleIntegral (y.horizontal (i + 1)) j
    let d := cycleIntegral (y.horizontal i) j
    let e := if i.val + 1 = M then columnHolonomy y 0 else 0
    let v := y.vertical i 0
    have hcyc' : a + b = v + e := hcyc
    have htransport' : c + d = y.vertical i j + v := htransport
    change y.vertical i j = (a + c) + (b + d) + e
    have hv := ZModModule.add_self v
    have he := ZModModule.add_self e
    calc
      y.vertical i j = (y.vertical i j + (v + v)) + (e + e) := by
        rw [hv, he]
        simp
      _ = (v + e) + (y.vertical i j + v) + e := by abel
      _ = (a + b) + (c + d) + e := by rw [hcyc', htransport']
      _ = (a + c) + (b + d) + e := by abel

theorem gradient_flat {M N : ℕ} [NeZero M] [NeZero N]
    (x : Fin M → Fin N → ZMod 2) : Flat (gradient x) := by
  intro i j
  let a := x i (j + 1)
  let b := x i j
  let c := x (i + 1) (j + 1)
  let d := x (i + 1) j
  change (a + b) + (c + a) + (c + d) + (d + b) = 0
  calc
    (a + b) + (c + a) + (c + d) + (d + b) =
        (a + a) + (b + b) + (c + c) + (d + d) := by abel
    _ = 0 := by simp [ZModModule.add_self]

theorem seam_flat {M N : ℕ} [NeZero M] [NeZero N]
    (h v : ZMod 2) : Flat (seam (M := M) (N := N) h v) := by
  intro i j
  let a := if j.val + 1 = N then h else 0
  let b := if i.val + 1 = M then v else 0
  change a + b + a + b = 0
  calc
    a + b + a + b = (a + a) + (b + b) := by abel
    _ = 0 := by simp [ZModModule.add_self]

theorem gradient_holonomy_zero {M N : ℕ} [NeZero M] [NeZero N]
    (x : Fin M → Fin N → ZMod 2) :
    (∀ i, rowHolonomy (gradient x) i = 0) ∧
      (∀ j, columnHolonomy (gradient x) j = 0) := by
  constructor
  · intro i
    simp only [rowHolonomy, gradient, Finset.sum_add_distrib]
    have hshift : (∑ j : Fin N, x i (j + 1)) = ∑ j : Fin N, x i j :=
      Fintype.sum_equiv (Equiv.addRight (1 : Fin N))
        (fun j => x i (j + 1)) (x i) (fun _ => rfl)
    rw [hshift]
    exact ZModModule.add_self _
  · intro j
    simp only [columnHolonomy, gradient, Finset.sum_add_distrib]
    have hshift : (∑ i : Fin M, x (i + 1) j) = ∑ i : Fin M, x i j :=
      Fintype.sum_equiv (Equiv.addRight (1 : Fin M))
        (fun i => x (i + 1) j) (fun i => x i j) (fun _ => rfl)
    rw [hshift]
    exact ZModModule.add_self _

theorem seam_holonomy {M N : ℕ} [NeZero M] [NeZero N]
    (h v : ZMod 2) :
    (∀ i, rowHolonomy (seam (M := M) (N := N) h v) i = h) ∧
      (∀ j, columnHolonomy (seam (M := M) (N := N) h v) j = v) := by
  have hlast {n : ℕ} [NeZero n] (i : Fin n) :
      i.val + 1 = n ↔ i = lastIndex n := by
    constructor
    · intro hi
      apply Fin.ext
      change i.val = n - 1
      omega
    · intro hi
      rw [hi]
      change n - 1 + 1 = n
      have hn := NeZero.pos n
      omega
  constructor
  · intro i
    simp only [rowHolonomy, seam]
    simp_rw [hlast]
    simp
  · intro j
    simp only [columnHolonomy, seam]
    simp_rw [hlast]
    simp

theorem flat_exact_iff {M N : ℕ} [NeZero M] [NeZero N]
    (y : EdgeLabel M N) (hy : Flat y) :
    (∃ x : Fin M → Fin N → ZMod 2, gradient x = y) ↔
      rowHolonomy y 0 = 0 ∧ columnHolonomy y 0 = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(gradient_holonomy_zero x).1 0,
      (gradient_holonomy_zero x).2 0⟩
  · rintro ⟨hh, hv⟩
    obtain ⟨x, _, hs, hu⟩ := flat_decomposition y hy
    refine ⟨x, ?_⟩
    have hs' : (gradient x).horizontal = y.horizontal := by
      funext i j
      have h := hs i j
      simpa [seam, hh] using h.symm
    have hu' : (gradient x).vertical = y.vertical := by
      funext i j
      have h := hu i j
      simpa [seam, hv] using h.symm
    cases y with
    | mk s u =>
      cases hg : gradient x with
      | mk a b =>
        have hsa : a = s := by simpa only [hg] using hs'
        have hbu : b = u := by simpa only [hg] using hu'
        cases hsa
        cases hbu
        rfl

theorem horizontal_seam_counterexample (M N : ℕ)
    [NeZero M] [NeZero N] (_hM : 3 ≤ M) (_hN : 3 ≤ N) :
    Flat (seam (M := M) (N := N) 1 0) ∧
      rowHolonomy (seam (M := M) (N := N) 1 0) 0 = 1 ∧
      columnHolonomy (seam (M := M) (N := N) 1 0) 0 = 0 ∧
      ¬ ∃ x : Fin M → Fin N → ZMod 2,
        gradient x = seam (M := M) (N := N) 1 0 := by
  have hf := seam_flat (M := M) (N := N) 1 0
  have hh := (seam_holonomy (M := M) (N := N) 1 0).1 0
  have hv := (seam_holonomy (M := M) (N := N) 1 0).2 0
  refine ⟨hf, hh, hv, ?_⟩
  intro hex
  have hz := (flat_exact_iff _ hf).mp hex
  have hone : (1 : ZMod 2) ≠ 0 := by decide
  exact hone (hh.symm.trans hz.1)

def combinedLabel {M N : ℕ} [NeZero M] [NeZero N]
    (x : Fin M → Fin N → ZMod 2) (h v : ZMod 2) : EdgeLabel M N where
  horizontal i j := (gradient x).horizontal i j + (seam h v).horizontal i j
  vertical i j := (gradient x).vertical i j + (seam h v).vertical i j

private theorem cycleIntegral_seam_zero {n : ℕ} [NeZero n]
    (z : ZMod 2) (i : Fin n) :
    cycleIntegral (fun k : Fin n => if k.val + 1 = n then z else 0) i = 0 := by
  unfold cycleIntegral
  apply Finset.sum_eq_zero
  intro k hk
  have hki : k < i := Finset.mem_Iio.mp hk
  have hneq : k.val + 1 ≠ n := by
    have hi := i.isLt
    omega
  simp [hneq]

private theorem reconstructed_combined {M N : ℕ} [NeZero M] [NeZero N]
    (x : Fin M → Fin N → ZMod 2) (h v : ZMod 2)
    (hx : x 0 0 = 0) (i : Fin M) (j : Fin N) :
    reconstructedVertex (combinedLabel x h v) i j = x i j := by
  have hv : cycleIntegral (fun k => (combinedLabel x h v).vertical k 0) i =
      x i 0 + x 0 0 := by
    calc
      cycleIntegral (fun k => (combinedLabel x h v).vertical k 0) i =
        cycleIntegral (fun k => x (k + 1) 0 + x k 0) i +
          cycleIntegral (fun k : Fin M => if k.val + 1 = M then v else 0) i := by
            simp [cycleIntegral, combinedLabel, gradient, seam, Finset.sum_add_distrib]
      _ = x i 0 + x 0 0 := by
        rw [cycleIntegral_boundary (fun k => x k 0) i,
          cycleIntegral_seam_zero, add_zero]
  have hh : cycleIntegral ((combinedLabel x h v).horizontal i) j =
      x i j + x i 0 := by
    calc
      cycleIntegral ((combinedLabel x h v).horizontal i) j =
        cycleIntegral (fun k => x i (k + 1) + x i k) j +
          cycleIntegral (fun k : Fin N => if k.val + 1 = N then h else 0) j := by
            simp [cycleIntegral, combinedLabel, gradient, seam, Finset.sum_add_distrib]
      _ = x i j + x i 0 := by
        rw [cycleIntegral_boundary (x i) j, cycleIntegral_seam_zero, add_zero]
  dsimp [reconstructedVertex]
  rw [hv, hh, hx]
  have hc := ZModModule.add_self (x i 0)
  calc
    x i 0 + 0 + (x i j + x i 0) = x i j + (x i 0 + x i 0) := by abel
    _ = x i j := by rw [hc, add_zero]

noncomputable def flatLabelEquiv {M N : ℕ} [NeZero M] [NeZero N] :
    {y : EdgeLabel M N // Flat y} ≃
      ({x : Fin M → Fin N → ZMod 2 // x 0 0 = 0} ×
        (ZMod 2 × ZMod 2)) where
  toFun y :=
    (⟨reconstructedVertex y.1, by
      simp [reconstructedVertex, cycleIntegral,
        show (0 : Fin M) = ⊥ from rfl, show (0 : Fin N) = ⊥ from rfl,
        Finset.Iio_bot]⟩,
      (rowHolonomy y.1 0, columnHolonomy y.1 0))
  invFun z :=
    ⟨combinedLabel z.1.1 z.2.1 z.2.2,
      by
        intro i j
        have hsum : plaquette (combinedLabel z.1.1 z.2.1 z.2.2) i j =
            plaquette (gradient z.1.1) i j + plaquette (seam z.2.1 z.2.2) i j := by
          simp only [plaquette, combinedLabel]
          abel
        rw [hsum, gradient_flat z.1.1 i j, seam_flat z.2.1 z.2.2 i j]
        simp⟩
  left_inv y := by
    apply Subtype.ext
    change combinedLabel (reconstructedVertex y.1)
      (rowHolonomy y.1 0) (columnHolonomy y.1 0) = y.1
    obtain ⟨x, hx, hs, hu⟩ := flat_decomposition y.1 y.2
    have heq : combinedLabel x (rowHolonomy y.1 0) (columnHolonomy y.1 0) = y.1 := by
      have hs' : (combinedLabel x (rowHolonomy y.1 0)
          (columnHolonomy y.1 0)).horizontal = y.1.horizontal := by
        funext i j
        exact (hs i j).symm
      have hu' : (combinedLabel x (rowHolonomy y.1 0)
          (columnHolonomy y.1 0)).vertical = y.1.vertical := by
        funext i j
        exact (hu i j).symm
      exact congrArg₂ EdgeLabel.mk hs' hu'
    have hrec : reconstructedVertex y.1 = x := by
      rw [← heq]
      funext i j
      exact reconstructed_combined x _ _ hx i j
    rw [hrec]
    exact heq
  right_inv z := by
    rcases z with ⟨⟨x, hx⟩, ⟨h, v⟩⟩
    apply Prod.ext
    · apply Subtype.ext
      funext i j
      exact reconstructed_combined x h v hx i j
    · apply Prod.ext
      · simp only [rowHolonomy, combinedLabel, Finset.sum_add_distrib]
        change rowHolonomy (gradient x) 0 + rowHolonomy (seam h v) 0 = h
        rw [(gradient_holonomy_zero x).1 0, (seam_holonomy h v).1 0]
        simp
      · simp only [columnHolonomy, combinedLabel, Finset.sum_add_distrib]
        change columnHolonomy (gradient x) 0 + columnHolonomy (seam h v) 0 = v
        rw [(gradient_holonomy_zero x).2 0, (seam_holonomy h v).2 0]
        simp

noncomputable instance flatLabelFintype {M N : ℕ} [NeZero M] [NeZero N] :
    Fintype {y : EdgeLabel M N // Flat y} := Fintype.ofFinite _

noncomputable def anchoredVertexEquiv {M N : ℕ} [NeZero M] [NeZero N] :
    {x : Fin M → Fin N → ZMod 2 // x 0 0 = 0} ≃
      ({q : Fin M × Fin N // q ≠ (0, 0)} → ZMod 2) := by
  classical
  let e : (Fin M → Fin N → ZMod 2) ≃
      ZMod 2 × ({q : Fin M × Fin N // q ≠ (0, 0)} → ZMod 2) :=
    (Equiv.curry (Fin M) (Fin N) (ZMod 2)).symm.trans
      (Equiv.funSplitAt (0, 0) (ZMod 2))
  let e' : {x : Fin M → Fin N → ZMod 2 // x 0 0 = 0} ≃
      {p : ZMod 2 × ({q : Fin M × Fin N // q ≠ (0, 0)} → ZMod 2) // p.1 = 0} :=
    Equiv.subtypeEquiv e (fun _ => Iff.rfl)
  refine e'.trans ?_
  refine
    { toFun := fun p => p.1.2
      invFun := fun f => ⟨(0, f), rfl⟩
      left_inv := ?_
      right_inv := by intro; rfl }
  intro p
  rcases p with ⟨⟨a, f⟩, ha⟩
  simp only at ha
  subst a
  rfl

theorem anchored_vertex_card (M N : ℕ) [NeZero M] [NeZero N] :
    Fintype.card {x : Fin M → Fin N → ZMod 2 // x 0 0 = 0} =
      2 ^ (M * N - 1) := by
  classical
  rw [Fintype.card_congr (anchoredVertexEquiv (M := M) (N := N))]
  rw [Fintype.card_fun]
  have hindex : Fintype.card {q : Fin M × Fin N // q ≠ (0, 0)} =
      M * N - 1 := by
    rw [Fintype.card_subtype_compl (fun q : Fin M × Fin N => q = (0, 0))]
    simp
  rw [hindex]
  simp [ZMod.card]

theorem flat_label_card (M N : ℕ) [NeZero M] [NeZero N] :
    Fintype.card {y : EdgeLabel M N // Flat y} =
      2 ^ (M * N + 1) := by
  classical
  rw [Fintype.card_congr (flatLabelEquiv (M := M) (N := N))]
  simp only [Fintype.card_prod, anchored_vertex_card, ZMod.card]
  have hmn : 1 ≤ M * N := by
    have hm := NeZero.pos M
    have hn := NeZero.pos N
    exact Nat.mul_pos hm hn
  calc
    2 ^ (M * N - 1) * (2 * 2) =
        2 ^ (M * N - 1) * 2 ^ 2 := by rfl
    _ = 2 ^ ((M * N - 1) + 2) := by rw [← pow_add]
    _ = 2 ^ (M * N + 1) := by congr 1; omega

noncomputable def holonomySectorEquiv {M N : ℕ} [NeZero M] [NeZero N]
    (h v : ZMod 2) :
    {y : EdgeLabel M N // Flat y ∧ rowHolonomy y 0 = h ∧ columnHolonomy y 0 = v} ≃
      {x : Fin M → Fin N → ZMod 2 // x 0 0 = 0} where
  toFun y := ⟨reconstructedVertex y.1, by
    simp [reconstructedVertex, cycleIntegral,
      show (0 : Fin M) = ⊥ from rfl, show (0 : Fin N) = ⊥ from rfl,
      Finset.Iio_bot]⟩
  invFun x :=
    ⟨combinedLabel x.1 h v,
      ⟨by
          intro i j
          have hsum : plaquette (combinedLabel x.1 h v) i j =
              plaquette (gradient x.1) i j + plaquette (seam h v) i j := by
            simp only [plaquette, combinedLabel]
            abel
          rw [hsum, gradient_flat x.1 i j, seam_flat h v i j]
          simp,
        by
          simp only [rowHolonomy, combinedLabel, Finset.sum_add_distrib]
          change rowHolonomy (gradient x.1) 0 + rowHolonomy (seam h v) 0 = h
          rw [(gradient_holonomy_zero x.1).1 0, (seam_holonomy h v).1 0]
          simp,
        by
          simp only [columnHolonomy, combinedLabel, Finset.sum_add_distrib]
          change columnHolonomy (gradient x.1) 0 + columnHolonomy (seam h v) 0 = v
          rw [(gradient_holonomy_zero x.1).2 0, (seam_holonomy h v).2 0]
          simp⟩⟩
  left_inv y := by
    apply Subtype.ext
    have heq := (flatLabelEquiv (M := M) (N := N)).left_inv ⟨y.1, y.2.1⟩
    have hval := congrArg Subtype.val heq
    change combinedLabel (reconstructedVertex y.1)
      (rowHolonomy y.1 0) (columnHolonomy y.1 0) = y.1 at hval
    rw [y.2.2.1, y.2.2.2] at hval
    exact hval
  right_inv x := by
    apply Subtype.ext
    funext i j
    exact reconstructed_combined x.1 h v x.2 i j

noncomputable instance holonomySectorFintype {M N : ℕ} [NeZero M] [NeZero N]
    (h v : ZMod 2) :
    Fintype {y : EdgeLabel M N //
      Flat y ∧ rowHolonomy y 0 = h ∧ columnHolonomy y 0 = v} :=
  Fintype.ofFinite _

theorem holonomy_sector_card (M N : ℕ) [NeZero M] [NeZero N]
    (h v : ZMod 2) :
    Fintype.card {y : EdgeLabel M N //
      Flat y ∧ rowHolonomy y 0 = h ∧ columnHolonomy y 0 = v} =
      2 ^ (M * N - 1) := by
  classical
  rw [Fintype.card_congr (holonomySectorEquiv (M := M) (N := N) h v)]
  exact anchored_vertex_card M N

theorem holonomy_surjective (M N : ℕ) [NeZero M] [NeZero N] :
    ∀ h v : ZMod 2, ∃ y : EdgeLabel M N,
      Flat y ∧ rowHolonomy y 0 = h ∧ columnHolonomy y 0 = v := by
  intro h v
  exact ⟨seam h v, seam_flat h v,
    (seam_holonomy h v).1 0, (seam_holonomy h v).2 0⟩

def PlaquetteRelation {M N : ℕ} [NeZero M] [NeZero N]
    (coeff : Fin M → Fin N → ZMod 2) : Prop :=
  ∀ y : EdgeLabel M N,
    (∑ i : Fin M, ∑ j : Fin N, coeff i j * plaquette y i j) = 0

theorem plaquette_relation_rank_one {M N : ℕ} [NeZero M] [NeZero N]
    (coeff : Fin M → Fin N → ZMod 2) :
    PlaquetteRelation coeff ↔ ∀ i j, coeff i j = coeff 0 0 := by
  classical
  constructor
  · intro hrel
    have hH (i : Fin M) (j : Fin N) :
        coeff (i + 1) j = coeff i j := by
      let y : EdgeLabel M N :=
        ⟨(fun a b => if a = i + 1 then if b = j then 1 else 0 else 0),
          fun _ _ => 0⟩
      have hz := hrel y
      have hcoef :
          (∑ a : Fin M, ∑ b : Fin N, coeff a b * plaquette y a b) =
            coeff (i + 1) j + coeff i j := by
        simp [y, plaquette, mul_add, Finset.sum_add_distrib,
          Finset.sum_ite_eq']
      rw [hcoef] at hz
      have hc := ZModModule.add_self (coeff i j)
      exact add_right_cancel (hz.trans hc.symm)
    have hV (i : Fin M) (j : Fin N) :
        coeff i (j + 1) = coeff i j := by
      let y : EdgeLabel M N :=
        ⟨(fun _ _ => 0),
          (fun a b => if a = i then if b = j + 1 then 1 else 0 else 0)⟩
      have hz := hrel y
      have hcoef :
          (∑ a : Fin M, ∑ b : Fin N, coeff a b * plaquette y a b) =
            coeff i (j + 1) + coeff i j := by
        simp [y, plaquette, mul_add, Finset.sum_add_distrib,
          Finset.sum_ite_eq']
        abel
      rw [hcoef] at hz
      have hc := ZModModule.add_self (coeff i j)
      exact add_right_cancel (hz.trans hc.symm)
    intro i j
    calc
      coeff i j = coeff 0 j := cycle_constant (fun k => coeff k j) (fun k => hH k j) i
      _ = coeff 0 0 := cycle_constant (coeff 0) (hV 0) j
  · intro hc y
    have htotal : (∑ i : Fin M, ∑ j : Fin N, plaquette y i j) = 0 := by
      simp_rw [sum_plaquette_row]
      calc
        (∑ i : Fin M, (rowHolonomy y i + rowHolonomy y (i + 1))) =
            ∑ i : Fin M, (rowHolonomy y (i + 1) + rowHolonomy y i) := by
              apply Finset.sum_congr rfl
              intro i _
              exact add_comm _ _
        _ = 0 := by
          rw [Finset.sum_add_distrib]
          have hshift : (∑ i : Fin M, rowHolonomy y (i + 1)) =
              ∑ i : Fin M, rowHolonomy y i :=
            Fintype.sum_equiv (Equiv.addRight (1 : Fin M))
              (fun i => rowHolonomy y (i + 1)) (rowHolonomy y) (fun _ => rfl)
          rw [hshift]
          exact ZModModule.add_self _
    calc
      (∑ i : Fin M, ∑ j : Fin N, coeff i j * plaquette y i j) =
          coeff 0 0 * (∑ i : Fin M, ∑ j : Fin N, plaquette y i j) := by
            simp_rw [hc]
            simp only [Finset.mul_sum]
      _ = 0 := by rw [htotal, mul_zero]

theorem plaquette_relation_card (M N : ℕ) [NeZero M] [NeZero N] :
    Nat.card {coeff : Fin M → Fin N → ZMod 2 // PlaquetteRelation coeff} = 2 := by
  let e : {coeff : Fin M → Fin N → ZMod 2 // PlaquetteRelation coeff} ≃ ZMod 2 :=
    { toFun := fun coeff => coeff.1 0 0
      invFun := fun c => ⟨fun _ _ => c,
        (plaquette_relation_rank_one _).mpr (by intros; rfl)⟩
      left_inv := by
        intro coeff
        apply Subtype.ext
        funext i j
        exact (plaquette_relation_rank_one coeff.1).mp coeff.2 i j |>.symm
      right_inv := by intro c; rfl }
  rw [Nat.card_congr e]
  simpa only [Nat.card_eq_fintype_card] using (ZMod.card 2)

theorem edge_label_card (M N : ℕ) :
    Fintype.card (EdgeLabel M N) = 2 ^ (2 * M * N) := by
  classical
  let e : EdgeLabel M N ≃
      (Fin M → Fin N → ZMod 2) × (Fin M → Fin N → ZMod 2) :=
    { toFun := fun y => (y.horizontal, y.vertical)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := by intro y; cases y; rfl
      right_inv := by intro p; cases p; rfl }
  rw [Fintype.card_congr e, Fintype.card_prod]
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  simp only [← pow_mul]
  calc
    2 ^ (N * M) * 2 ^ (N * M) =
        2 ^ ((N * M) + (N * M)) := (pow_add _ _ _).symm
    _ = 2 ^ (2 * M * N) := by congr 1; ring

noncomputable instance exactLabelFintype {M N : ℕ} [NeZero M] [NeZero N] :
    Fintype {y : EdgeLabel M N // ∃ x : Fin M → Fin N → ZMod 2, gradient x = y} :=
  Fintype.ofFinite _

theorem exact_label_card (M N : ℕ) [NeZero M] [NeZero N] :
    Fintype.card {y : EdgeLabel M N //
      ∃ x : Fin M → Fin N → ZMod 2, gradient x = y} =
      2 ^ (M * N - 1) := by
  classical
  let e : {y : EdgeLabel M N //
      ∃ x : Fin M → Fin N → ZMod 2, gradient x = y} ≃
      {y : EdgeLabel M N //
        Flat y ∧ rowHolonomy y 0 = 0 ∧ columnHolonomy y 0 = 0} :=
    Equiv.subtypeEquivRight (fun y => by
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨gradient_flat x, (gradient_holonomy_zero x).1 0,
          (gradient_holonomy_zero x).2 0⟩
      · rintro ⟨hy, hh, hv⟩
        exact (flat_exact_iff y hy).mpr ⟨hh, hv⟩)
  rw [Fintype.card_congr e]
  exact holonomy_sector_card M N 0 0

abbrev EdgeSpace (M N : ℕ) :=
  (Fin M → Fin N → ZMod 2) × (Fin M → Fin N → ZMod 2)

def plaquetteLinear (M N : ℕ) [NeZero M] [NeZero N] :
    EdgeSpace M N →ₗ[ZMod 2] (Fin M → Fin N → ZMod 2) where
  toFun y i j := y.1 i j + y.2 i (j + 1) + y.1 (i + 1) j + y.2 i j
  map_add' := by
    intro y z
    funext i j
    dsimp
    abel
  map_smul' := by
    intro a y
    funext i j
    dsimp
    simp only [mul_add]

def flatSubspace (M N : ℕ) [NeZero M] [NeZero N] :
    Submodule (ZMod 2) (EdgeSpace M N) :=
  LinearMap.ker (plaquetteLinear M N)

theorem periodic_grid_linear_statistics (M N : ℕ) [NeZero M] [NeZero N] :
    Module.finrank (ZMod 2) (LinearMap.range (plaquetteLinear M N)) = M * N - 1 ∧
    Module.finrank (ZMod 2) (flatSubspace M N) = M * N + 1 ∧
    0 < (Fintype.card {y : EdgeLabel M N // Flat y} : ℚ) ∧
    0 < (Fintype.card (EdgeLabel M N) : ℚ) ∧
    (Fintype.card {y : EdgeLabel M N //
      ∃ x : Fin M → Fin N → ZMod 2, gradient x = y} : ℚ) /
        (Fintype.card {y : EdgeLabel M N // Flat y} : ℚ) = 1 / 4 ∧
    (Fintype.card {y : EdgeLabel M N // Flat y} : ℚ) /
        (Fintype.card (EdgeLabel M N) : ℚ) =
          1 / (2 : ℚ) ^ (M * N - 1) ∧
    (Fintype.card {y : EdgeLabel M N //
      ∃ x : Fin M → Fin N → ZMod 2, gradient x = y} : ℚ) /
        (Fintype.card (EdgeLabel M N) : ℚ) =
          1 / (2 : ℚ) ^ (M * N + 1) := by
  classical
  let e : ↥(flatSubspace M N) ≃ {y : EdgeLabel M N // Flat y} :=
    { toFun := fun y => ⟨⟨y.1.1, y.1.2⟩, by
          intro i j
          have hy := congrFun (congrFun (LinearMap.mem_ker.mp y.2) i) j
          exact hy⟩
      invFun := fun y => ⟨(y.1.horizontal, y.1.vertical), by
          apply LinearMap.mem_ker.mpr
          funext i j
          exact y.2 i j⟩
      left_inv := by intro y; apply Subtype.ext; cases y.1; rfl
      right_inv := by intro y; apply Subtype.ext; cases y.1; rfl }
  have hkerCard : Fintype.card ↥(flatSubspace M N) = 2 ^ (M * N + 1) := by
    rw [Fintype.card_congr e]
    exact flat_label_card M N
  have hkerPow : 2 ^ Module.finrank (ZMod 2) (flatSubspace M N) =
      2 ^ (M * N + 1) := by
    calc
      2 ^ Module.finrank (ZMod 2) (flatSubspace M N) =
          Fintype.card ↥(flatSubspace M N) := by
            simpa only [ZMod.card] using
              (Module.card_eq_pow_finrank (K := ZMod 2)
                (V := ↥(flatSubspace M N))).symm
      _ = _ := hkerCard
  have hdim : Module.finrank (ZMod 2) (flatSubspace M N) = M * N + 1 :=
    Nat.pow_right_injective (by omega : 2 ≤ 2) hkerPow
  have hspaceDim : Module.finrank (ZMod 2) (EdgeSpace M N) = 2 * M * N := by
    simp only [EdgeSpace, Module.finrank_prod]
    simp only [Module.finrank_pi_fintype]
    simp
    ring
  have hrankNullity := (plaquetteLinear M N).finrank_range_add_finrank_ker
  change Module.finrank (ZMod 2) (LinearMap.range (plaquetteLinear M N)) +
      Module.finrank (ZMod 2) (flatSubspace M N) =
        Module.finrank (ZMod 2) (EdgeSpace M N) at hrankNullity
  have hpositive : 1 ≤ M * N := Nat.mul_pos (NeZero.pos M) (NeZero.pos N)
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (plaquetteLinear M N)) =
      M * N - 1 := by
    rw [hdim, hspaceDim] at hrankNullity
    have hmul : 2 * M * N = M * N + M * N := by ring
    rw [hmul] at hrankNullity
    omega
  have hflat : 0 < (Fintype.card {y : EdgeLabel M N // Flat y} : ℚ) := by
    rw [flat_label_card]
    positivity
  have hedge : 0 < (Fintype.card (EdgeLabel M N) : ℚ) := by
    rw [edge_label_card]
    positivity
  have hfirst : (2 : ℚ) ^ (M * N + 1) = (2 : ℚ) ^ (M * N - 1) * 4 := by
    rw [show M * N + 1 = (M * N - 1) + 2 by omega, pow_add]
    norm_num
  have hsecond : (2 : ℚ) ^ (2 * M * N) =
      (2 : ℚ) ^ (M * N + 1) * (2 : ℚ) ^ (M * N - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hthird : (2 : ℚ) ^ (2 * M * N) =
      (2 : ℚ) ^ (M * N - 1) * (2 : ℚ) ^ (M * N + 1) := by
    rw [← pow_add]
    congr 1
    omega
  refine ⟨hrank, hdim, hflat, hedge, ?_, ?_, ?_⟩
  · rw [exact_label_card, flat_label_card]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [hfirst]
    have hp : (2 : ℚ) ^ (M * N - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  · rw [flat_label_card, edge_label_card]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [hsecond]
    have hp : (2 : ℚ) ^ (M * N + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hq : (2 : ℚ) ^ (M * N - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  · rw [exact_label_card, edge_label_card]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [hthird]
    have hp : (2 : ℚ) ^ (M * N + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hq : (2 : ℚ) ^ (M * N - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp

#print axioms flat_holonomy_constant
#print axioms flat_decomposition
#print axioms gradient_flat
#print axioms seam_flat
#print axioms gradient_holonomy_zero
#print axioms seam_holonomy
#print axioms flat_exact_iff
#print axioms horizontal_seam_counterexample
#print axioms anchored_vertex_card
#print axioms flat_label_card
#print axioms holonomy_sector_card
#print axioms holonomy_surjective
#print axioms plaquette_relation_rank_one
#print axioms plaquette_relation_card
#print axioms edge_label_card
#print axioms exact_label_card
#print axioms periodic_grid_linear_statistics

end D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
