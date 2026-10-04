/- GID: D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Literal four-exit trees and the zero-to-two raw-cost obstruction. -/

import D5.S3.Arith.FibonacciAtomic.ActualJointResponseCostCore
import D5.S3.Arith.FibonacciAtomic.ActualImageSevenLeafSeparation
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

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

local notation "b₀" => ActualImageSevenLeafSeparation.E
def t : Source := .mul (.of true) (.of false)
def w : Source := .mul b₀ (.of false)
def h : Source := .mul t (.of true)
def y : Source := .mul w (.of true)
def z : Source := .mul (.of false) b₀
def r₀ : Source := .mul t b₀
def rₐ : Source := .mul t z

local notation "A" => ActualImageSevenLeafSeparation.A
local notation "C" => ActualImageSevenLeafSeparation.C
def B : Source := thirdImage b₀
def T : Source := thirdImage t
def W₁ : Source := thirdImage w
def H : Source := thirdImage h
def Y : Source := thirdImage y
def Z : Source := thirdImage z
def R₀ : Source := thirdImage r₀
def Rₐ : Source := thirdImage rₐ

def comb : (n : Nat) → (Fin n → Source) → Source → Source
  | 0, _, q => q
  | n + 1, f, q => .mul (f 0)
      (comb n (fun i => f i.succ) q)

def preActive (_k : Nat) (_j : Fin _k) (r : Row) : Source :=
  match r.1 with
  | 0 => .of true
  | 1 => y
  | 2 => h
  | _ => z

def preComp (r : Row) : Source :=
  match r.1 with
  | 0 => rₐ
  | 1 => b₀
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

def baselinePre (k : Nat) : Source := comb k (fun _ => b₀) r₀

def preFamily (k : Nat) : Index k → Source
  | Sum.inl _ => baselinePre k
  | Sum.inr ⟨j, r⟩ => comb k (fun i => if i = j then preActive k j r else b₀) (preComp r)

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


/-- A zero-excess A row forces a second nonleaf report on a sibling row. -/
private theorem local_two_excess (k : Nat) (j : Fin k) (pi : Strategy)
    (hz : cost pi (family k (.inr (j, 0))) = 8 * k + 16) :
    ∃ r : Fin 3, 8 * k + 18 ≤ cost pi (family k (.inr (j, r.succ))) := by
  classical
  let F : Fin 4 → Source := fun r => family k (.inr (j, r))
  have rho_comb : ∀ (n : Nat) (f : Fin n → Source) (q : Source),
      thirdImage (comb n f q) =
        comb n (fun i => thirdImage (f i)) (thirdImage q) := by
    intro n
    induction n with
    | zero => intro f q; rfl
    | succ n ih =>
      intro f q
      change thirdImage (.mul (f 0) (comb n (fun i => f i.succ) q)) = _
      rw [show thirdImage (.mul (f 0) (comb n (fun i => f i.succ) q)) =
          .mul (thirdImage (f 0)) (thirdImage (comb n (fun i => f i.succ) q)) from
        Function.Semiconj₂.iterate
          (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
            fun s t => substitution.map_mul s t) 3 _ _]
      rw [ih]
      rfl
  have positive : ∀ r, Positive (F r) := by
    intro r
    refine ⟨preFamily k (.inr (j, r)), ?_⟩
    change thirdImage (comb k (fun i => if i = j then preActive k j r else b₀)
      (preComp r)) = _
    rw [rho_comb]
    change comb k (fun i => thirdImage (if i = j then preActive k j r else b₀))
      (thirdImage (preComp r)) = _
    have ha : thirdImage (preActive k j r) = active r := by fin_cases r <;> rfl
    have hc : thirdImage (preComp r) = comp r := by fin_cases r <;> rfl
    rw [hc]
    congr 1
    funext i
    by_cases hij : i = j <;> simp [hij, ha, B]
  have comb_len : ∀ (n : Nat) (f : Fin n → Source) (q : Source),
      (comb n f q).length = (∑ i : Fin n, (f i).length) + q.length := by
    intro n
    induction n with
    | zero => intro f q; simp [comb]
    | succ n ih =>
      intro f q
      rw [comb, FreeMagma.length, ih, Fin.sum_univ_succ]
      omega
  have len : ∀ r, (F r).length = 8 * k + 16 := by
    have blocklen : ∀ r : Row, (active r).length + (comp r).length = 24 := by
      intro r; fin_cases r <;> rfl
    have blen : B.length = 8 := by decide
    intro r
    change (comb k (fun i => if i = j then active r else B) (comp r)).length = _
    rw [comb_len]
    have hs : (∑ i : Fin k, (if i = j then active r else B).length) =
        (active r).length + (k - 1) * 8 := by
      rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin k)) _ (Finset.mem_univ j)]
      have ht : ∀ i ∈ (Finset.univ : Finset (Fin k)).erase j,
          (if i = j then active r else B).length = 8 := by
        intro i hi
        simp [(Finset.mem_erase.mp hi).1, blen]
      rw [Finset.sum_congr rfl ht]
      simp [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j),
        Nat.add_comm]
    rw [hs]
    have hk : 1 ≤ k := Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt j.isLt)
    have hb := blocklen r
    omega
  have comb_inj : ∀ (n : Nat) (f g : Fin n → Source) (q t : Source),
      comb n f q = comb n g t → ∀ i, f i = g i := by
    intro n
    induction n with
    | zero => intro f g q t he i; exact Fin.elim0 i
    | succ n ih =>
      intro f g q t he i
      change FreeMagma.mul (f 0) (comb n (fun i => f i.succ) q) =
        FreeMagma.mul (g 0) (comb n (fun i => g i.succ) t) at he
      have hp : f 0 = g 0 ∧ comb n (fun i => f i.succ) q = comb n (fun i => g i.succ) t := by
        injection he with h₁ h₂
        exact ⟨h₁,h₂⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hp.1
      · exact ih _ _ _ _ hp.2 i
  have inj : Function.Injective F := by
    intro r s he
    have ha := comb_inj k _ _ _ _ he j
    simp only [ite_true] at ha
    have distinct : ∀ r s : Row, active r = active s → r = s := by
      intro r s
      fin_cases r <;> fin_cases s <;> decide
    exact distinct r s ha
  have plain : ∀ (n : Nat) (f : Fin n → Source) (q : Row → Source) (u : Address),
      (∃ y, ∀ r, readout u (comb n f (q r)) = y) ∨
      (∃ v, ∀ r, readout u (comb n f (q r)) = readout v (q r)) := by
    intro n
    induction n with
    | zero => intro f q u; exact Or.inr ⟨u, fun _ => rfl⟩
    | succ n ih =>
      intro f q u
      cases u with
      | nil => exact Or.inl ⟨.branch, fun _ => rfl⟩
      | cons d u =>
        cases d with
        | false => exact Or.inl ⟨readout u (f 0), fun _ => rfl⟩
        | true => exact ih (fun i => f i.succ) q u
  -- Each query either stays common to the four rows, reaches their active
  -- blocks, or reaches their compensation blocks.
  have decompose : ∀ (n : Nat) (f : Fin n → Source) (q : Row → Source)
      (j : Fin n) (u : Address),
      (∃ y, ∀ r, readout u (comb n (fun i => if i = j then active r else f i) (q r)) = y) ∨
      (∃ v, ∀ r, readout u (comb n (fun i => if i = j then active r else f i) (q r)) =
        readout v (active r)) ∨
      (∃ v, ∀ r, readout u (comb n (fun i => if i = j then active r else f i) (q r)) =
        readout v (q r)) := by
    intro n
    induction n with
    | zero => intro f q j; exact Fin.elim0 j
    | succ n ih =>
      intro f q j u
      cases u with
      | nil => exact Or.inl ⟨.branch, fun _ => rfl⟩
      | cons d u =>
        cases d with
        | false =>
          by_cases hj : j = 0
          · subst j
            exact Or.inr (Or.inl ⟨u, fun _ => by simp [comb, readout]⟩)
          · exact Or.inl ⟨readout u (f 0), fun _ => by simp [comb, readout, Ne.symm hj]⟩
        | true =>
          refine Fin.cases ?_ (fun j => ?_) j
          · rcases plain n (fun i => f i.succ) q u with ⟨y,hy⟩ | ⟨v,hv⟩
            · left; refine ⟨y, ?_⟩; intro r
              simpa [comb, readout] using hy r
            · right; right; refine ⟨v, ?_⟩; intro r
              simpa [comb, readout] using hv r
          · simpa only [comb, readout, Fin.succ_inj] using
              ih (fun i => f i.succ) q j u
  have block_nc : ∀ (r s : Row),
      ActualImageSevenLeafSeparation.Nonconflict (active r) (active s) ∧
      ActualImageSevenLeafSeparation.Nonconflict (comp r) (comp s) := by
    intro r s; fin_cases r <;> fin_cases s <;>
      simp only [active, comp, B, H, Y, Z, Rₐ, thirdImage,
        rₐ, t, w, h, y, z, ActualImageSevenLeafSeparation.E,
        ActualImageSevenLeafSeparation.A,
        ActualImageSevenLeafSeparation.Nonconflict]
    all_goals trivial
  have agree : ∀ P Q : Source, ActualImageSevenLeafSeparation.Nonconflict P Q →
      ∀ u, chi (readout u P) = 0 → chi (readout u Q) = 0 → readout u P = readout u Q := by
    intro P Q hn u hp hq
    have hl := (ActualImageSevenLeafSeparation.seven_leaf_separation.2.1 P Q).2.2.mp hn
    cases heP : readout u P <;> cases heQ : readout u Q <;>
      simp only [heP, chi] at hp <;> simp only [heQ, chi] at hq
    all_goals try contradiction
    all_goals try rfl
    · have h := hl u true false (by simp [ActualImageSevenLeafSeparation.leafLabel, heP])
        (by simp [ActualImageSevenLeafSeparation.leafLabel, heQ])
      cases h
    · have h := hl u false true (by simp [ActualImageSevenLeafSeparation.leafLabel, heP])
        (by simp [ActualImageSevenLeafSeparation.leafLabel, heQ])
      cases h
  have nc : ∀ u r s, chi (readout u (F r)) = 0 →
      chi (readout u (F s)) = 0 → readout u (F r) = readout u (F s) := by
    intro u r s hr hs
    rcases decompose k (fun _ => B) comp j u with ⟨y, hy⟩ | ⟨v, hv⟩ | ⟨v, hv⟩
    · exact (hy r).trans (hy s).symm
    · exact (hv r).trans ((agree _ _ (block_nc r s).1 v
        (by simpa [F, family, hv] using hr) (by simpa [F, family, hv] using hs)).trans (hv s).symm)
    · exact (hv r).trans ((agree _ _ (block_nc r s).2 v
        (by simpa [F, family, hv] using hr) (by simpa [F, family, hv] using hs)).trans (hv s).symm)
  have block_pair : ∀ (u : Address), chi (readout u (F 0)) = 0 →
      (∀ r : Fin 3, readout u (F r.succ) = readout u (F 0)) ∨
      ∃ r s : Fin 3, r ≠ s ∧ readout u (F r.succ) = readout u (F s.succ) ∧
        chi (readout u (F r.succ)) = 1 := by
    intro u hu
    rcases decompose k (fun _ => B) comp j u with ⟨y, hy⟩ | ⟨v, hv⟩ | ⟨v, hv⟩
    · left; intro r; exact (hy _).trans (hy _).symm
    all_goals
      simp only [F, family] at hu ⊢
      simp_rw [hv] at hu ⊢
      have leaf : ∀ V v, chi (readout v V) = 0 → v ∈ leaves V := by
        intro V v hz
        apply List.mem_toFinset.mp
        apply (ActualImageSevenLeafSeparation.seven_leaf_separation.1 V).2 v |>.mpr
        cases hr : readout v V <;> simp [hr, chi] at hz
        · exact ⟨true, by simp [ActualImageSevenLeafSeparation.leafLabel, hr]⟩
        · exact ⟨false, by simp [ActualImageSevenLeafSeparation.leafLabel, hr]⟩
      have hmem := leaf _ _ hu
      simp only [active, comp, Fin.val_zero] at hmem
      first
      | change v ∈ [[false, false], [false, true], [true]] at hmem
      | change v ∈ [
          [false, false, false, false],
          [false, false, false, true],
          [false, false, true],
          [false, true, false, false, false],
          [false, true, false, false, true],
          [false, true, false, true],
          [false, true, true, false],
          [false, true, true, true],
          [true, false, false, false, false],
          [true, false, false, false, true],
          [true, false, false, true],
          [true, false, true, false],
          [true, false, true, true],
          [true, true, false, false, false, false],
          [true, true, false, false, false, true],
          [true, true, false, false, true],
          [true, true, false, true, false],
          [true, true, false, true, true],
          [true, true, true, false, false],
          [true, true, true, false, true],
          [true, true, true, true]] at hmem
      all_goals
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        repeat' rcases hmem with hmem | hmem
        all_goals decide
  have child_gain (S : Finset (Fin 4)) (a : Fin 4 → Reply)
      (next : ∀ y : Reply, (survivors S a y).Nonempty → Recipe F (survivors S a y))
      (u v : Reply) (hu : (survivors S a u).Nonempty) (hv : (survivors S a v).Nonempty)
      (he : u = v) (i : Fin 4) : gain (next u hu) i = gain (next v hv) i := by
    subst v
    rfl
  have one_zero : ∀ {S : Finset (Fin 4)} (r : Recipe F S) (i l : Fin 4),
      i ∈ S → l ∈ S → gain r i = 0 → gain r l = 0 → i = l := by
    intro S r
    induction r with
    | singleton s =>
      intro i l hi hl _ _
      exact (Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hl).symm
    | split S a hsplit next ih =>
      intro i l hi hl hgi hgl
      obtain ⟨u, hu⟩ := a.property
      have hz_i : chi (a.val i) = 0 := by
        have h := hgi
        simp only [gain, hi, ↓reduceDIte] at h
        omega
      have hz_l : chi (a.val l) = 0 := by
        have h := hgl
        simp only [gain, hl, ↓reduceDIte] at h
        omega
      have he : a.val i = a.val l := by
        rw [← hu]
        exact nc u i l (by simpa only [← hu, vector] using hz_i) (by simpa only [← hu, vector] using hz_l)
      have hmi : i ∈ survivors S a.val (a.val i) := by simp [survivors, hi]
      have hml : l ∈ survivors S a.val (a.val i) := by simp [survivors, hl, he]
      apply ih (a.val i) ⟨i, hmi⟩ i l hmi hml
      · simpa [gain, hi, hz_i] using hgi
      · have hchild : gain (next (a.val l) ⟨l, by simp [survivors, hl]⟩) l = 0 := by
          simpa only [gain, hl, ↓reduceDIte, hz_l, Nat.zero_add] using hgl
        exact (child_gain S a.val next (a.val i) (a.val l) ⟨i,hmi⟩
          ⟨l,by simp [survivors, hl]⟩ he l).trans hchild
  have obstruction : ∀ {S : Finset (Fin 4)} (r : Recipe F S),
      (∀ i, i ∈ S) → gain r 0 = 0 → ∃ b : Fin 3, 2 ≤ gain r b.succ := by
    intro S r
    induction r with
    | singleton i =>
      intro hS _
      have h0 := Finset.mem_singleton.mp (hS 0)
      have h1 := Finset.mem_singleton.mp (hS 1)
      exact False.elim (by have := h0.trans h1.symm; exact (by decide : (0 : Fin 4) ≠ 1) this)
    | split S a hsplit next ih =>
      intro hS hz
      obtain ⟨u, hu⟩ := a.property
      have hz0 : chi (a.val 0) = 0 := by
        have h := hz
        simp only [gain, hS, ↓reduceDIte] at h
        omega
      have hg0 : gain (next (a.val 0) ⟨0, by simp [survivors, hS]⟩) 0 = 0 := by
        simpa [gain, hS, hz0] using hz
      rcases block_pair u (by simpa [← hu, vector] using hz0) with common | ⟨b,c,hbc,he,hchi⟩
      · have common' : ∀ i : Fin 4, a.val i = a.val 0 := by
          intro i
          refine Fin.cases rfl (fun i => ?_) i
          simpa [← hu, vector] using common i
        have allmem : ∀ i, i ∈ survivors S a.val (a.val 0) := by
          intro i; simp [survivors, hS, common']
        obtain ⟨b,hb⟩ := ih (a.val 0) ⟨0, allmem 0⟩ allmem hg0
        refine ⟨b, ?_⟩
        have hh : gain (Recipe.split S a hsplit next) b.succ =
            gain (next (a.val 0) ⟨0, allmem 0⟩) b.succ := by
          simp only [gain, hS, ↓reduceDIte]
          rw [child_gain S a.val next (a.val b.succ) (a.val 0)
            ⟨b.succ,by simp [survivors, hS]⟩ ⟨0,allmem 0⟩ (common' b.succ) b.succ]
          rw [common' b.succ, hz0, Nat.zero_add]
        rw [hh]
        exact hb
      · have he' : a.val b.succ = a.val c.succ := by simpa [← hu, vector] using he
        have hc' : chi (a.val b.succ) = 1 := by simpa [← hu, vector] using hchi
        have mb : b.succ ∈ survivors S a.val (a.val b.succ) := by simp [survivors, hS]
        have mc : c.succ ∈ survivors S a.val (a.val b.succ) := by simp [survivors, hS, he']
        by_cases hb : gain (next (a.val b.succ) ⟨b.succ, mb⟩) b.succ = 0
        · have hc : 1 ≤ gain (next (a.val b.succ) ⟨b.succ, mb⟩) c.succ := by
            by_contra hh
            have hz := one_zero _ b.succ c.succ mb mc hb (by omega)
            exact hbc (Fin.succ_injective _ hz)
          refine ⟨c, ?_⟩
          have hh : gain (Recipe.split S a hsplit next) c.succ =
              1 + gain (next (a.val b.succ) ⟨b.succ, mb⟩) c.succ := by
            simp only [gain, hS, ↓reduceDIte]
            rw [child_gain S a.val next (a.val c.succ) (a.val b.succ)
              ⟨c.succ,by simp [survivors, hS]⟩ ⟨b.succ,mb⟩ he'.symm c.succ]
            rw [← he', hc']
          rw [hh]
          exact Nat.add_le_add_left hc 1
        · refine ⟨b, ?_⟩
          simpa only [gain, hS, ↓reduceDIte, hc'] using
            Nat.add_le_add_left (show 1 ≤ gain (next (a.val b.succ) ⟨b.succ, mb⟩) b.succ by omega) 1
  have supply := ActualJointResponseCostCore.result 4 (by decide) F positive inj
  obtain ⟨v, ⟨r, hr⟩, hv⟩ := supply.2.2.2.1 pi
  have leaflen : ∀ i, (leaves (F i)).length = 8 * k + 16 := by
    intro i
    have lone := ActualJointResponseCostCore.result 1 (by decide) (fun _ => F i)
      (fun _ => positive i) (fun x y _ => Subsingleton.elim x y)
    obtain ⟨v,hv⟩ := lone.2.1
    obtain ⟨q,p,hp,hfacts⟩ := lone.2.2.1 v hv
    obtain ⟨hc,hpaid,hvec,haddr,hroute,hcount,hsum,htotal⟩ := hfacts 0
    have nil : routeTrace q 0 = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [nil] at hpaid htotal
    simp only [paid, List.map_nil, List.toFinset_nil, Finset.empty_union,
      Finset.empty_sdiff, Finset.card_empty, Nat.add_zero] at hpaid htotal
    have card := (ActualImageSevenLeafSeparation.seven_leaf_separation.1 (F i)).1
    have ceq : cost p (F i) = (leaves (F i)).toFinset.card := by
      exact congrArg Finset.card hpaid
    exact htotal.symm.trans (ceq.trans (card.trans (len i)))
  have hzero : gain r 0 = 0 := by
    have h0 := hv 0
    rw [hr 0, leaflen 0] at h0
    change _ ≤ cost pi (family k (.inr (j, 0))) at h0
    omega
  obtain ⟨b,hb⟩ := obstruction r (fun _ => Finset.mem_univ _) hzero
  refine ⟨b, ?_⟩
  have h := hv b.succ
  rw [hr b.succ, leaflen b.succ] at h
  exact le_trans (by omega) h

end D5.S3.Arith.FibonacciAtomic.FourExitRawEndpointSpectrum
