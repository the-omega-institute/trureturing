/- GID: D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/MerminMeasurementDependence/Coordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Even-Y coordinates and complement reduction of the even-party scenario. -/
/-
Direct frozen dependencies: none.
computational_content.kind: none; general mathematical statements, not an executable API.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.QuantumBounds.MerminMeasurementDependence.Model
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.QuantumBounds.MerminMeasurementDependence
noncomputable section



def bitSign (z : ZMod 2) : ℝ := boolSign ((fun z : ZMod 2 => decide (z = 1)) z)

def tableParity {n : ℕ} (lambda : Strategy n) : ZMod 2 :=
  ∑ i, (fun b : Bool => (b.toNat : ZMod 2)) (lambda i).1

def tableGamma {n : ℕ} (lambda : Strategy n) (i : Fin n) : ZMod 2 :=
  (fun b : Bool => (b.toNat : ZMod 2)) (lambda i).1 + (fun b : Bool => (b.toNat : ZMod 2)) (lambda i).2

def evenExtension {d : ℕ} (x : Fin d → ZMod 2) : Fin (d+1) → Bool :=
  Fin.snoc (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i)) ((fun z : ZMod 2 => decide (z = 1)) (∑ i, x i))

def evenSetting {d : ℕ} (x : Fin d → ZMod 2) : Setting (d+1) := by
  have bit_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
    have hv : z.val < 2 := ZMod.val_lt z
    have hz : z.val = 0 ∨ z.val = 1 := by omega
    rcases hz with hz | hz
    · left
      rw [← ZMod.natCast_zmod_val z,hz]
      simp
    · right
      rw [← ZMod.natCast_zmod_val z,hz]
      simp
  have boolBit_bitBool (z : ZMod 2) : (fun b : Bool => (b.toNat : ZMod 2)) ((fun z : ZMod 2 => decide (z = 1)) z) = z :=
    by rcases bit_cases z with rfl | rfl <;> simp []
  have settingWeight_eq_sum {n : ℕ} (x : Fin n → Bool) :
      (fun x => hammingDist x (fun _ => false)) x = ∑ i, (x i).toNat := by
    classical
    dsimp only
    unfold hammingDist
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i hi
    cases x i <;> simp
  have parity_sum {n : ℕ} (x : Fin n → Bool) :
      ∑ i, (fun b : Bool => (b.toNat : ZMod 2)) (x i) = ((fun x => hammingDist x (fun _ => false)) x : ZMod 2) := by
    rw [settingWeight_eq_sum, Nat.cast_sum]
  have evenExtension_parity {d : ℕ} (x : Fin d → ZMod 2) :
      (fun x => hammingDist x (fun _ => false)) (evenExtension x) % 2 = 0 := by
    have hz : ((fun x => hammingDist x (fun _ => false)) (evenExtension x) : ZMod 2) = 0 := by
      rw [← parity_sum,Fin.sum_univ_castSucc]
      simp only [evenExtension,Fin.snoc_castSucc,Fin.snoc_last,boolBit_bitBool]
      dsimp only at *
      exact CharTwo.add_self_eq_zero _
    have hdvd : 2 ∣ (fun x => hammingDist x (fun _ => false)) (evenExtension x) :=
      (ZMod.natCast_eq_zero_iff _ _).mp hz
    exact Nat.mod_eq_zero_of_dvd hdvd
  exact ⟨evenExtension x,evenExtension_parity x⟩

def lastAdjustedFrequency {d : ℕ} (lambda : Strategy (d+1)) (i : Fin d) : ZMod 2 :=
  tableGamma lambda i.castSucc + tableGamma lambda (Fin.last d)

def freeSetting {d : ℕ} (x : Setting (d+1)) : Fin d → ZMod 2 :=
  fun i => (fun b : Bool => (b.toNat : ZMod 2)) (x.1 i.castSucc)

def settingEquiv (d : ℕ) : Setting (d+1) ≃ (Fin d → ZMod 2) := by
  have settingWeight_eq_sum {n : ℕ} (x : Fin n → Bool) :
      (fun x => hammingDist x (fun _ => false)) x = ∑ i, (x i).toNat := by
    classical
    dsimp only
    unfold hammingDist
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i hi
    cases x i <;> simp
  have parity_sum {n : ℕ} (x : Fin n → Bool) :
      ∑ i, (fun b : Bool => (b.toNat : ZMod 2)) (x i) = ((fun x => hammingDist x (fun _ => false)) x : ZMod 2) := by
    rw [settingWeight_eq_sum, Nat.cast_sum]
  have setting_parity {n : ℕ} (x : Setting n) : ∑ i, (fun b : Bool => (b.toNat : ZMod 2)) (x.1 i) = 0 := by
    rw [parity_sum, ZMod.natCast_eq_zero_iff_even]
    exact (even_iff_two_dvd).mpr (Nat.dvd_of_mod_eq_zero x.2)
  have evenSetting_freeSetting {d : ℕ} (x : Setting (d+1)) :
      evenSetting (freeSetting x) = x := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [evenSetting,evenExtension,Fin.snoc_last,freeSetting]
      have h := setting_parity x
      rw [Fin.sum_univ_castSucc] at h
      have hs : (∑ j : Fin d, (fun b : Bool => (b.toNat : ZMod 2)) (x.1 j.castSucc)) = (fun b : Bool => (b.toNat : ZMod 2)) (x.1 (Fin.last d)) := by
        have hz := CharTwo.add_self_eq_zero ((fun b : Bool => (b.toNat : ZMod 2)) (x.1 (Fin.last d)))
        linear_combination h-hz
      dsimp only at hs
      simp only [hs]
      have hc (b : Bool) : decide ((b.toNat : ZMod 2) = 1) = b := by cases b <;> decide
      exact hc _
    · simp only [evenSetting,evenExtension,Fin.snoc_castSucc,freeSetting]
      have hc (b : Bool) : decide ((b.toNat : ZMod 2) = 1) = b := by cases b <;> decide
      exact hc _
  have bit_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
    have hv : z.val < 2 := ZMod.val_lt z
    have hz : z.val = 0 ∨ z.val = 1 := by omega
    rcases hz with hz | hz
    · left
      rw [← ZMod.natCast_zmod_val z,hz]
      simp
    · right
      rw [← ZMod.natCast_zmod_val z,hz]
      simp
  have boolBit_bitBool (z : ZMod 2) : (fun b : Bool => (b.toNat : ZMod 2)) ((fun z : ZMod 2 => decide (z = 1)) z) = z :=
    by rcases bit_cases z with rfl | rfl <;> simp []
  have freeSetting_evenSetting {d : ℕ} (x : Fin d → ZMod 2) :
      freeSetting (evenSetting x) = x := by
    funext i
    simp [freeSetting,evenSetting,evenExtension,boolBit_bitBool]
  exact {
    toFun := freeSetting
    invFun := evenSetting
    left_inv := evenSetting_freeSetting
    right_inv := freeSetting_evenSetting }

def addX {d : ℕ} (x : Setting d) : Setting (d+1) := by
  have settingWeight_eq_sum {n : ℕ} (x : Fin n → Bool) :
      (fun x => hammingDist x (fun _ => false)) x = ∑ i, (x i).toNat := by
    classical
    dsimp only
    unfold hammingDist
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i hi
    cases x i <;> simp
  have settingWeight_snoc {d : ℕ} (x : Fin d → Bool) (b : Bool) :
      (fun x => hammingDist x (fun _ => false)) (Fin.snoc x b) = (fun x => hammingDist x (fun _ => false)) x + b.toNat := by
    rw [settingWeight_eq_sum,Fin.sum_univ_castSucc,settingWeight_eq_sum]
    simp
  exact ⟨Fin.snoc x.1 false,by simpa [settingWeight_snoc] using x.2⟩

def flipSetting {n : ℕ} (hn : Even n) (x : Setting n) : Setting n := by
  have settingWeight_eq_sum {n : ℕ} (x : Fin n → Bool) :
      (fun x => hammingDist x (fun _ => false)) x = ∑ i, (x i).toNat := by
    classical
    dsimp only
    unfold hammingDist
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i hi
    cases x i <;> simp
  have weight_not_add_weight {n : ℕ} (x : Fin n → Bool) :
      (fun x => hammingDist x (fun _ => false)) (fun i => !(x i)) + (fun x => hammingDist x (fun _ => false)) x = n := by
    rw [settingWeight_eq_sum,settingWeight_eq_sum,← Finset.sum_add_distrib]
    have hp (i : Fin n) : (!(x i)).toNat + (x i).toNat = 1 := by cases x i <;> rfl
    simp_rw [hp]
    simp
  exact ⟨fun i => !(x.1 i),by
      have hw := weight_not_add_weight x.1
      have hx := x.2
      obtain ⟨k,hk⟩ := hn
      omega⟩

def evenRepresentative (k : ℕ) (x : Setting (2*k+2)) : Setting (2*k+2) :=
  if x.1 (Fin.last (2*k+1)) then flipSetting (show Even (2*k+2) from ⟨k+1,by omega⟩) x else x

def evenReduced (k : ℕ) (x : Setting (2*k+2)) : Setting (2*k+1) := by
  have evenRepresentative_last (k : ℕ) (x : Setting (2*k+2)) :
      (evenRepresentative k x).1 (Fin.last (2*k+1)) = false := by
    cases hx : x.1 (Fin.last (2*k+1)) <;> simp [evenRepresentative,hx,flipSetting]
  have settingWeight_eq_sum {n : ℕ} (x : Fin n → Bool) :
      (fun x => hammingDist x (fun _ => false)) x = ∑ i, (x i).toNat := by
    classical
    dsimp only
    unfold hammingDist
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i hi
    cases x i <;> simp
  have parity_sum {n : ℕ} (x : Fin n → Bool) :
      ∑ i, (fun b : Bool => (b.toNat : ZMod 2)) (x i) = ((fun x => hammingDist x (fun _ => false)) x : ZMod 2) := by
    rw [settingWeight_eq_sum, Nat.cast_sum]
  have setting_parity {n : ℕ} (x : Setting n) : ∑ i, (fun b : Bool => (b.toNat : ZMod 2)) (x.1 i) = 0 := by
    rw [parity_sum, ZMod.natCast_eq_zero_iff_even]
    exact (even_iff_two_dvd).mpr (Nat.dvd_of_mod_eq_zero x.2)
  exact ⟨fun i => (evenRepresentative k x).1 i.castSucc,by
      have h := setting_parity (evenRepresentative k x)
      rw [Fin.sum_univ_castSucc,evenRepresentative_last] at h
      simp only [ Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one,Bool.false_eq_true,ite_false,add_zero] at h
      have hw : ((fun x => hammingDist x (fun _ => false)) (fun i : Fin (2*k+1) =>
          (evenRepresentative k x).1 i.castSucc) : ZMod 2) = 0 := by
        rw [← parity_sum]
        exact h
      exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp hw)⟩

def evenFactor (k : ℕ) (x : Setting (2*k+2)) : ℝ :=
  if x.1 (Fin.last (2*k+1)) then bitSign ((k+1 : ℕ) : ZMod 2) else 1
end
end D5.S3.QuantumBounds.MerminMeasurementDependence
