/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/AsymmetricThreeLabelCost
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/AsymmetricThreeLabelCost
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Arbitrary asymmetric three-label INITIAL phase sets have exact paid cost. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.FiveLabelSeamCost

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe z

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.AsymmetricThreeLabelCost

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open D5.S3.ObserverMemory.Algorithms.KBonacciIrreversibleAcquisition
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S0.Tower.DBonacci.Names
open LiteralModel EndpointCells OriginalNarrowCost OriginalExecutionBridge
open WindowChargeInverse PhysicalWindowDecoder OriginalAcquiredTrace
open scoped BigOperators

private def pulse (g u : ℕ) (S : Finset ℕ) : Fin (g*u) → Bool :=
  fun i => decide (∃ t ∈ S, i.val+1=t*g)

private theorem pulse_head (g u : ℕ) (hg : 2 ≤ g) (hu : 1 ≤ u) (S : Finset ℕ)
    (support : ∀ t ∈ S, 1 ≤ t) : pulse g u S ⟨0, by nlinarith⟩ = false := by
  simp only [pulse, Fin.val_mk, Nat.zero_add, decide_eq_false_iff_not]
  rintro ⟨t,ht,eq⟩
  have := support t ht
  nlinarith

private theorem pulse_charge (g u p : ℕ) (hg : 2 ≤ g) (hu : 1 ≤ u) (hup : u < p)
    (S : Finset ℕ) (support : ∀ t ∈ S, 1 ≤ t ∧ t ≤ u)
    (j : ℕ) (hj : j < p) :
    wordIncrement (g*p-1) (-((j*g : ℕ) : ZMod (g*p-1+1))) (pulse g u S) =
      if j ∈ S then 1 else 0 := by
  have hT : g*p-1+1=g*p := by
    have : 0<g*p := by positivity
    omega
  have small : j*g < g*p-1+1 := by rw [hT]; nlinarith
  have hk : 3 ≤ g*p-1 := by nlinarith
  have short : g*u < g*p-1 := by nlinarith
  rw [increment_derivative _ hk _ short]
  rw [ZMod.val_natCast_of_lt small]
  have atVertex : extendedBit (pulse g u S) (j*g)=0 := by
    unfold extendedBit
    split_ifs with inside
    · simp only [bitScalar, pulse, Fin.val_mk]
      have absent : ¬∃ t ∈ S, j*g+1=t*g := by
        rintro ⟨t,ht,eq⟩
        have dv : g ∣ 1 := by
          have a : g ∣ j*g+1 := eq ▸ dvd_mul_left g t
          exact (Nat.dvd_add_iff_right (dvd_mul_left g j)).mpr a
        have := Nat.le_of_dvd (by decide : 0<1) dv
        omega
      simp [absent]
    · rfl
  rw [atVertex,zero_add]
  by_cases zero : j=0
  · subst j
    have absent : 0 ∉ S := by intro h; have := (support 0 h).1; omega
    simp [absent]
  · have jpos : 1 ≤ j := by omega
    rw [if_neg (by nlinarith : j*g ≠ 0)]
    by_cases inside : j*g-1 < g*u
    · have pos : 1 ≤ j*g := by nlinarith
      have eqs : (∃ t ∈ S, (j*g-1)+1=t*g) ↔ j ∈ S := by
        rw [Nat.sub_add_cancel pos]
        constructor
        · rintro ⟨t,ht,e⟩
          have : j=t := by nlinarith
          simpa only [this] using ht
        · intro h; exact ⟨j,h,rfl⟩
      simp [extendedBit, inside, bitScalar, pulse, eqs]
    · have absent : j ∉ S := by
        intro h
        have le := Nat.mul_le_mul_right g (support j h).2
        nlinarith
      simp [extendedBit, inside, absent]

private theorem shifted_charge (g u p h r : ℕ) (hg : 2 ≤ g) (hu : 3 ≤ u)
    (hup : u < p) (hp : p=h*u+r) (hr : 1 ≤ r) (hru : r<u)
    (S : Finset ℕ) (support : ∀ t ∈ S, 1 ≤ t ∧ t ≤ u-r)
    (j : ℕ) (hj : j<p) :
    wordIncrement (g*p-1)
      (-((j*g : ℕ) : ZMod (g*p-1+1))+((h*(g*u) : ℕ) : ZMod (g*p-1+1)))
      (pulse g u (S.image (r+·))) = if j ∈ S then 1 else 0 := by
  have hh : 1 ≤ h := by
    by_contra hn
    have : h=0 := by omega
    simp_all
    omega
  have hT : g*p-1+1=g*p := by
    have : 0<g*p := by positivity
    omega
  have full : ((g*p : ℕ) : ZMod (g*p-1+1))=0 := by rw [← hT]; simp
  have stepNat : h*(g*u)+r*g=g*p := by rw [hp]; ring
  have step : ((h*(g*u) : ℕ) : ZMod (g*p-1+1))+((r*g : ℕ) : ZMod (g*p-1+1))=0 := by
    rw [← Nat.cast_add,stepNat,full]
  have shiftedSupport : ∀ t ∈ S.image (r+·), 1 ≤ t ∧ t ≤ u := by
    intro t ht
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
    have := support x hx
    omega
  by_cases nowrap : j+r<p
  · have phase : -((j*g : ℕ) : ZMod (g*p-1+1))+((h*(g*u) : ℕ) : ZMod (g*p-1+1)) =
        -(((j+r)*g : ℕ) : ZMod (g*p-1+1)) := by
      push_cast at step ⊢
      linear_combination step
    rw [phase,pulse_charge g u p hg (by omega) hup _ shiftedSupport _ nowrap]
    have mem : j+r ∈ S.image (r+·) ↔ j ∈ S := by
      constructor
      · rintro ht
        obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp ht
        have : x=j := by omega
        simpa only [this] using hx
      · intro ht; exact Finset.mem_image.mpr ⟨j,ht,by omega⟩
    simp only [mem]
  · have low : p ≤ j+r := by omega
    have small : j+r-p<p := by omega
    have phase : -((j*g : ℕ) : ZMod (g*p-1+1))+((h*(g*u) : ℕ) : ZMod (g*p-1+1)) =
        -(((j+r-p)*g : ℕ) : ZMod (g*p-1+1)) := by
      rw [Nat.cast_mul,Nat.cast_sub low]
      push_cast at step full ⊢
      linear_combination step - full
    rw [phase,pulse_charge g u p hg (by omega) hup _ shiftedSupport _ small]
    have absent : j ∉ S := by
      intro ht
      have := support j ht
      have : u ≤ h*u := by nlinarith
      omega
    have shiftedAbsent : j+r-p ∉ S.image (r+·) := by
      intro ht
      obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp ht
      have := support x hx
      omega
    simp [absent,shiftedAbsent]

private def words (g u h r : ℕ) (HB HC : Finset ℕ) : List (Fin (g*u) → Bool) :=
  pulse g u HC :: List.replicate (h-1) (fun _ => false) ++ [pulse g u (HB.image (r+·))]

private def label {Y : Type z} (HB HC : Finset ℕ) (A B C : Y) (j : ℕ) : Y :=
  if j ∈ HB then B else if j ∈ HC then C else A

private def decode {Y : Type z} {g u : ℕ} (A B C : Y) (v : ZMod 2)
    (archive : NarrowWindowCost.Archive (g*u)) : Y :=
  if (archive.head?).map Prod.snd = some (some (v+1)) then C
  else if ((archive.getLast?).map Prod.snd) =
    ((archive.head?).map Prod.snd).map (Option.map (·+1)) then B else A

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.AsymmetricThreeLabelCost
