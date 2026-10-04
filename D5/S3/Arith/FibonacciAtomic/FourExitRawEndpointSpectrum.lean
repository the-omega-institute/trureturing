/- GID: D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The four-exit right-comb family and its raw endpoint menu interface. -/

import D5.S3.Arith.FibonacciAtomic.ActualJointResponseCostCore
import D5.S3.Arith.FibonacciAtomic.ActualImageSevenLeafSeparation
import D5.S3.Arith.FibonacciAtomic.SourceTransportCentralizer
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.FourExitRawEndpointSpectrum

open GenealogicalFiberTransport (Source substitution)
open scoped BigOperators
open ActualTreeReadoutAcquisition
open ActualJointResponseCostCore

abbrev Row := Fin 4
abbrev Index (k : Nat) := Unit ⊕ (Fin k × Row)

open ActualImageSevenLeafSeparation (thirdImage)

def b : Source := .mul (.of false) (.of true)
def t : Source := .mul (.of true) (.of false)
def w : Source := .mul b (.of false)
def h : Source := .mul t (.of true)
def y : Source := .mul w (.of true)
def z : Source := .mul (.of false) b
def r₀ : Source := .mul t b
def rₐ : Source := .mul t z

def E : Source := .mul (.of false) (.of true)
def A : Source := thirdImage (.of true)
def C : Source := thirdImage (.of false)
def B : Source := thirdImage b
def T : Source := thirdImage t
def W₁ : Source := thirdImage w
def H : Source := thirdImage h
def Y : Source := thirdImage y
def Z : Source := thirdImage z
def R₀ : Source := thirdImage r₀
def Rₐ : Source := thirdImage rₐ

def comb : (n : Nat) → (Fin n → Source) → Source → Source
  | 0, _, q => q
  | n + 1, f, q => .mul (f (Fin.last n))
      (comb n (fun i => f i.castSucc) q)

def preActive (_k : Nat) (_j : Fin _k) (r : Row) : Source :=
  match r.1 with
  | 0 => .of true
  | 1 => y
  | 2 => h
  | _ => z

def preComp (r : Row) : Source :=
  match r.1 with
  | 0 => rₐ
  | 1 => b
  | 2 => z
  | _ => h

def active (r : Row) : Source :=
  match r.1 with
  | 0 => A
  | 1 => Y
  | 2 => H
  | _ => Z

def comp (r : Row) : Source :=
  match r.1 with
  | 0 => Rₐ
  | 1 => B
  | 2 => Z
  | _ => H

def baselinePre (k : Nat) : Source := comb k (fun _ => b) r₀

def preFamily (k : Nat) : Index k → Source
  | Sum.inl _ => baselinePre k
  | Sum.inr ⟨j, r⟩ => comb k (fun i => if i = j then preActive k j r else b) (preComp r)

def family (k : Nat) : Index k → Source
  | Sum.inl _ => comb k (fun _ => B) R₀
  | Sum.inr ⟨j, r⟩ => comb k (fun i => if i = j then active r else B) (comp r)

def endpoint (k : Nat) (i : Index k) : Index k → Nat := fun j =>
  if j = i then 0 else 1

def endpointWith (k : Nat) (j : Fin k) (b : Row) : Index k → Nat := fun i =>
  if i = Sum.inr ⟨j, 0⟩ then 0
  else if i = Sum.inr ⟨j, b⟩ then 2
  else 1

def menu (k : Nat) : Set (Index k → Nat) :=
  Set.range (fun u : Unit => endpoint k (Sum.inl u)) ∪
    Set.range (fun p : Fin k × Fin 3 => endpoint k (Sum.inr ⟨p.1, Fin.succ p.2⟩)) ∪
    Set.range (fun p : Fin k × Fin 3 => endpointWith k p.1 (Fin.succ p.2))

theorem result (k : Nat) (hk : 1 ≤ k) :
    (∀ i : Index k, Positive (family k i)) ∧
    (∀ i : Index k, (family k i).length = 8 * k + 16) ∧
    (menu k).Nonempty := by
  classical
  have third_comb : ∀ (n : Nat) (f : Fin n → Source) (q : Source),
      thirdImage (comb n f q) =
        comb n (fun i => thirdImage (f i)) (thirdImage q) := by
    intro n
    induction n with
    | zero => intro f q; rfl
    | succ n ih =>
        intro f q
        rw [comb]
        change FreeMagma.mul (thirdImage (f (Fin.last n)))
          (thirdImage (comb n (fun i => f i.castSucc) q)) =
          FreeMagma.mul (thirdImage (f (Fin.last n)))
            (comb n (fun i => thirdImage (f i.castSucc)) (thirdImage q))
        rw [ih]
  have comb_len : ∀ (n : Nat) (f : Fin n → Source) (q : Source),
      (comb n f q).length = (∑ i : Fin n, (f i).length) + q.length := by
    intro n
    induction n with
    | zero => intro f q; simp [comb]
    | succ n ih =>
        intro f q
        rw [comb, FreeMagma.length, ih]
        have hs := Fin.sum_univ_castSucc (fun i : Fin (n + 1) => (f i).length)
        rw [hs]
        omega
  have hA : A.length = 3 := by decide
  have hB : B.length = 8 := by decide
  have hW : W₁.length = 13 := by decide
  have hH : H.length = 11 := by decide
  have hY : Y.length = 16 := by decide
  have hZ : Z.length = 13 := by decide
  have hR₀ : R₀.length = 16 := by decide
  have hRₐ : Rₐ.length = 21 := by decide
  have sum_replace : ∀ (x : Source) (c : Nat), x.length = c → ∀ j : Fin k,
      (∑ i : Fin k, (if i = j then x else B).length) = 8 * k - 8 + c := by
    intro x c hx j
    have ht : ∀ i : Fin k, (if i = j then x else B).length =
        if i = j then c else 8 := by
      intro i
      by_cases h : i = j <;> simp [h, hx, hB]
    simp_rw [ht]
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin k)) _
      (Finset.mem_univ j)]
    have herase : (∑ i ∈ (Finset.univ : Finset (Fin k)).erase j,
        (if i = j then c else 8)) =
        ∑ _i ∈ (Finset.univ : Finset (Fin k)).erase j, 8 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hne : i ≠ j := (Finset.mem_erase.mp hi).1
      simp [hne]
    rw [herase]
    simp [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j)]
    omega
  constructor
  · intro i
    cases i with
    | inl u =>
        refine ⟨baselinePre k, ?_⟩
        change thirdImage (comb k (fun _ => b) r₀) = _
        rw [third_comb]
        rfl
    | inr p =>
        rcases p with ⟨j, r⟩
        refine ⟨comb k (fun i => if i = j then preActive k j r else b) (preComp r), ?_⟩
        change thirdImage (comb k (fun i => if i = j then preActive k j r else b)
          (preComp r)) = _
        rw [third_comb]
        have hpreActive : thirdImage (preActive k j r) = active r := by
          fin_cases r <;> rfl
        have hpreComp : thirdImage (preComp r) = comp r := by
          fin_cases r <;> rfl
        change comb k (fun i => thirdImage (if i = j then preActive k j r else b))
            (thirdImage (preComp r)) =
          comb k (fun i => if i = j then active r else B) (comp r)
        rw [hpreComp]
        apply congrArg (fun f : Fin k → Source => comb k f (comp r))
        funext i
        by_cases hij : i = j
        · simp [hij, hpreActive]
        · simp [hij, B, b, thirdImage]
  constructor
  · intro i
    cases i with
    | inl u =>
        change (comb k (fun _ : Fin k => B) R₀).length = _
        rw [comb_len]
        simp [hB, hR₀]
        omega
    | inr p =>
        rcases p with ⟨j, r⟩
        change (comb k (fun i => if i = j then active r else B) (comp r)).length = _
        rw [comb_len]
        fin_cases r
        · simp only [active, comp]
          rw [sum_replace A 3 hA]
          simp [hRₐ]
          omega
        · simp only [active, comp]
          rw [sum_replace Y 16 hY]
          simp [hB]
          omega
        · simp only [active, comp]
          rw [sum_replace H 11 hH]
          simp [hZ]
          omega
        · simp only [active, comp]
          rw [sum_replace Z 13 hZ]
          simp [hH]
          omega
  · exact ⟨endpoint k (Sum.inl ()), by simp [menu]⟩

end D5.S3.Arith.FibonacciAtomic.FourExitRawEndpointSpectrum
