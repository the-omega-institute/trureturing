/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/PairedRibbonMask
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/PairedRibbonMask
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: From literal interlaced signed ribbon masks to normalized conditional Bell amplitudes. -/
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
import Mathlib.Logic.Equiv.Fin.Rotate
import OmegaBuild.Commands

compile_only_with_mathlib

noncomputable section

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonOneBit

namespace PairedBellSign

abbrev I := Fin 4

def bitSign (n : ℕ) : ℤ := if n % 2 = 0 then 1 else -1

def quantumBell (a x : I) : ℤ :=
  if ((x.val/2+a.val/2)%2 = x.val%2) then bitSign ((a.val%2)*(x.val/2)) else 0

def pt (a x y : I) : ℤ :=
  quantumBell a ⟨2*(x.val/2)+(y.val%2),by omega⟩ *
  quantumBell a ⟨2*(y.val/2)+(x.val%2),by omega⟩

def bellSign (a b : I) : ℤ :=
  bitSign (((a.val/2+b.val/2)%2)*((a.val%2+b.val%2)%2))

end PairedBellSign

namespace PairedSpectralTrace

/-- Index space for one site at 0, followed by one paired site per successor. -/
def Sites : ℕ → Type
  | 0 => Fin 4
  | n+1 => Fin 4 × Sites n

instance (n : ℕ) : Fintype (Sites n) := by
  induction n with
  | zero => change Fintype (Fin 4); infer_instance
  | succ n ih =>
    letI : Fintype (Sites n) := ih
    change Fintype (Fin 4 × Sites n)
    infer_instance

instance (n : ℕ) : DecidableEq (Sites n) := by
  induction n with
  | zero => change DecidableEq (Fin 4); infer_instance
  | succ n ih =>
    letI : DecidableEq (Sites n) := ih
    change DecidableEq (Fin 4 × Sites n)
    infer_instance

instance (n : ℕ) : Nonempty (Sites n) := by
  induction n with
  | zero => change Nonempty (Fin 4); exact ⟨0⟩
  | succ n ih =>
    obtain ⟨x⟩ := ih
    change Nonempty (Fin 4 × Sites n)
    exact ⟨(0,x)⟩

end PairedSpectralTrace

section
open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonFlagGeometry
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonStateActions
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure

namespace LiteralPairedRibbon

abbrev Band (q : ℕ) := Fin (q+1) × Fin 2
abbrev Carrier (q : ℕ) := Flag (4*q+3)

def portA {q : ℕ} (e:Band q) : D (4*q+3) := ⟨4*e.1.val+e.2.val, by omega⟩
def portB {q : ℕ} (e:Band q) : D (4*q+3) := ⟨4*e.1.val+e.2.val+2, by omega⟩

def mark {q : ℕ} (f:BandFlag (Band q)) : Carrier q :=
  (if f.2.1 then portB f.1 else portA f.1, f.2.2)

def cap {q : ℕ} (x:Carrier q) : Carrier q := (x.1,!x.2)

def gap {q : ℕ} (x:Carrier q) : Carrier q :=
   if x.2 then ((finRotate (4*q+4)) x.1,false)
   else ((finRotate (4*q+4)).symm x.1,true)

private theorem portA_inj {q : ℕ} : Function.Injective (portA (q:=q)) := by
  rintro ⟨i,e⟩ ⟨j,f⟩ h
  have H := congrArg Fin.val h
  change 4*i.val+e.val=4*j.val+f.val at H
  refine Prod.ext ?_ ?_
  · change i=j; exact Fin.ext (by omega)
  · change e=f; exact Fin.ext (by omega)

private theorem portB_inj {q : ℕ} : Function.Injective (portB (q:=q)) := by
  rintro ⟨i,e⟩ ⟨j,f⟩ h
  have H := congrArg Fin.val h
  change 4*i.val+e.val+2=4*j.val+f.val+2 at H
  refine Prod.ext ?_ ?_
  · change i=j; exact Fin.ext (by omega)
  · change e=f; exact Fin.ext (by omega)

private theorem separated {q : ℕ} (e f:Band q) : portA e ≠ portB f := by
  intro h
  have H := congrArg Fin.val h
  change 4*e.1.val+e.2.val=4*f.1.val+f.2.val+2 at H
  omega

private theorem mark_inj {q : ℕ} : Function.Injective (mark (q:=q)) := by
  rintro ⟨e,a,b⟩ ⟨f,c,d⟩ h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  change b=d at h₂
  subst d
  cases a <;> cases c
  · simp only [mark, Bool.false_eq_true, ite_false] at h₁
    rw [portA_inj h₁]
  · exact (separated _ _ h₁).elim
  · exact (separated _ _ h₁.symm).elim
  · simp only [mark, ite_true] at h₁
    rw [portB_inj h₁]

def chartTwist {q : ℕ} (u:Fin (q+1) → Bool) (e:Band q) : Bool :=
  if e.2=0 then true else u e.1

def rawTwist {q : ℕ} (u:Fin (q+1) → Bool) (e:Band q) : Bool := !chartTwist u e

def alternating (q:ℕ) : AlternatingFlagChart (gap (q:=q)) (cap (q:=q)) where
  n := 4*q+3
  chart := Equiv.refl _
  base _ := rfl
  gap i := by
    change ((finRotate (4*q+4)) i,false)=(cyclicNext i,false)
    congr 1
    apply Fin.ext
    rw [finRotate_apply]
    simp [Fin.add_def, cyclicNext, wrap]

noncomputable def literal {q : ℕ} (u:Fin (q+1) → Bool) :
    SignedMarkedChart (gap (q:=q)) cap (markedAction cap mark (rawTwist u) (fun _ => true))
      (Band q) (fun e x => ∃ r : Bool×Bool, x=mark (e,r)) where
  C := alternating q
  ports := ⟨portA,portB,portA_inj,portB_inj,separated,fun e => by
    change 4*e.1.val+e.2.val<4*e.1.val+e.2.val+2; omega⟩
  twist := chartTwist u
  membership e x := by
    change (∃ r : Bool×Bool, x=mark (e,r)) ↔ x.1=portA e ∨ x.1=portB e
    constructor
    · rintro ⟨⟨a,b⟩,rfl⟩
      cases a <;> simp [mark]
    · intro h
      rcases x with ⟨i,b⟩
      rcases h with h|h
      · exact ⟨(false,b),Prod.ext h rfl⟩
      · exact ⟨(true,b),Prod.ext h rfl⟩
  in_alternative e := by
    change markedAction cap mark (rawTwist u) (fun _ => true) (mark (e,false,false)) =
      (if chartTwist u e then inFlag (portB e) else outFlag (portB e))
    rw [markedAction_apply_mark _ _ mark_inj]
    cases h:chartTwist u e <;> simp [rawTwist,h,bandCode,mark,inFlag,outFlag]
  out_alternative e := by
    change markedAction cap mark (rawTwist u) (fun _ => true) (mark (e,false,true)) =
      (if chartTwist u e then outFlag (portB e) else inFlag (portB e))
    rw [markedAction_apply_mark _ _ mark_inj]
    cases h:chartTwist u e <;> simp [rawTwist,h,bandCode,mark,inFlag,outFlag]

open Classical in
private theorem literal_interlace {q:ℕ} (e f : Band q) :
    interlaces portA portB e f ↔ e.1=f.1 ∧ e.2≠f.2 := by
  rcases e with ⟨i,a⟩
  rcases f with ⟨j,b⟩
  by_cases h : i=j
  · subst j
    have h₁ : a.val=0 ∨ a.val=1 := by omega
    have h₂ : b.val=0 ∨ b.val=1 := by omega
    simp only [interlaces,between,portA,portB,true_and]
    rcases h₁ with h₁|h₁ <;> rcases h₂ with h₂|h₂ <;>
      simp [h₁,h₂,Fin.ext_iff]
  · have hne : i.val≠j.val := fun a=>h (Fin.ext a)
    simp only [interlaces,between,portA,portB,h,false_and,iff_false]
    omega

end LiteralPairedRibbon
end

section
open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary (twistDiagonal twistDiagonal_apply)
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonStateActions
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.SignedBouquetMomentReconstruction
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh
open scoped BigOperators
open Finset

namespace LiteralPairedRibbon

noncomputable def phaseForm {q:ℕ} (u:Fin (q+1)→Bool) : LinearMap.BilinForm K (Band q→K) :=
  signedBilin (literal u).ports.a (literal u).ports.b (literal u).twist

def pairVec {q:ℕ} (x c:Fin (q+1)→K) (e:Band q) : K :=
  if e.2=0 then x e.1 else c e.1

def tau (b:Bool) : K := if b then 1 else 0

private theorem interlacement_slot {q:ℕ} (z:Band q→K) (i:Fin (q+1)) (a b:Fin 2) (hab : a≠b) :
    interlacementMap portA portB z (i,a) = z (i,b) := by
  classical
  rw [interlacementMap_apply, Finset.sum_eq_single (i,b)]
  · simp [literal_interlace,hab]
  · rintro ⟨j,d⟩ _ hne
    have hn : ¬(i=j ∧ a≠d) := by
      rintro ⟨rfl,hd⟩
      have e : d=b := by
        apply Fin.ext
        have h₁ : a.val≠b.val := fun h=>hab (Fin.ext h)
        have h₂ : a.val≠d.val := fun h=>hd (Fin.ext h)
        omega
      exact hne (Prod.ext rfl e)
    simp [literal_interlace,hn]
  · simp

private theorem paired_phase_formula {q:ℕ} (u:Fin (q+1)→Bool)
    (x y c d:Fin (q+1)→K) :
    phaseForm u (pairVec x c) (pairVec y d) =
      ∑ i, (x i*y i+x i*d i+y i*c i+tau (u i)*c i*d i) := by
  classical
  change (∑ e:Band q, pairVec y d e * (((interlacementMap (@portA q) (@portB q) +
    twistDiagonal (chartTwist u)) : (Band q→K) →ₗ[K] (Band q→K)) (pairVec x c)) e) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.sum_univ_two, LinearMap.add_apply, Pi.add_apply]
  rw [interlacement_slot _ i 0 1 (by decide),interlacement_slot _ i 1 0 (by decide)]
  simp [twistDiagonal_apply,chartTwist,pairVec,tau]
  split_ifs <;> ring

def kept {q:ℕ} : Finset (Band q) := univ.filter (fun e=>e.2=0)

def keptVec {q:ℕ} (x : Fin (q+1)→K) : Bits (kept (q:=q)) :=
  fun e=>x e.val.1

def lostVec {q:ℕ} (x : Fin (q+1)→K) : Bits (kept (q:=q))ᶜ :=
  fun e=>x e.val.1

private theorem ins_pair {q:ℕ} (x c:Fin (q+1)→K) :
    ins kept (keptVec x)+ins keptᶜ (lostVec c) = pairVec x c := by
  ext e
  change (if h : e∈kept then keptVec x ⟨e,h⟩ else 0) +
    (if h : e∈keptᶜ then lostVec c ⟨e,h⟩ else 0) = pairVec x c e
  by_cases h : e.2=0
  · have hm : e∈kept := by simp [kept,h]
    have hn : e∉keptᶜ := by simpa using hm
    simp [hm,hn,pairVec,keptVec,h]
  · have hm : e∉kept := by simp [kept,h]
    have hn : e∈keptᶜ := by simpa using hm
    simp [hm,hn,pairVec,lostVec,h]

private theorem literal_mask_phase {q:ℕ} (u:Fin (q+1)→Bool)
    (x y c d:Fin (q+1)→K) :
    total (mask (phaseForm u) kept) (keptVec x) (keptVec y) (lostVec c) (lostVec d) =
      ∑ i, (x i*y i+x i*d i+y i*c i+tau (u i)*c i*d i) := by
  rw [fixed_graph_split,ins_pair,ins_pair,paired_phase_formula]

private theorem literal_mask_sign {q:ℕ} (u:Fin (q+1)→Bool)
    (x y c d:Fin (q+1)→K) :
    sign (total (mask (phaseForm u) kept) (keptVec x) (keptVec y) (lostVec c) (lostVec d)) =
      ∏ i, sign (x i*y i+x i*d i+y i*c i+tau (u i)*c i*d i) := by
  rw [literal_mask_phase]
  classical
  generalize (Finset.univ : Finset (Fin (q+1))) = s
  induction s using Finset.induction_on with
  | empty => simp [sign_zero]
  | insert i s hi ih => simp [hi,sign_mul,ih]

end LiteralPairedRibbon
end

section
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
open PairedSpectralTrace
open scoped BigOperators

namespace LiteralPairedRibbon

def firstBit (a:Fin 4) : K := (a.val/2 : ℕ)
def secondBit (a:Fin 4) : K := (a.val%2 : ℕ)
def fuse (a b:K) : Fin 4 := ⟨2*a.val+b.val,by have := a.val_lt; have := b.val_lt; omega⟩

private theorem fuse_inv : ∀ i : Fin 4, fuse (firstBit i) (secondBit i)=i := by decide
private theorem first_fuse : ∀ a b : K, firstBit (fuse a b)=a := by decide
private theorem second_fuse : ∀ a b : K, secondBit (fuse a b)=b := by decide

def labelBits : Fin 4 ≃ (K×K) where
  toFun i := (firstBit i,secondBit i)
  invFun i := fuse i.1 i.2
  left_inv := fuse_inv
  right_inv _i := Prod.ext (first_fuse _ _) (second_fuse _ _)

def siteCoords : (q:ℕ) → Sites q ≃ (Fin (q+1)→Fin 4)
  | 0 => {
      toFun := fun v _=>v
      invFun := fun v=>v 0
      left_inv := fun _=>rfl
      right_inv := fun v=>funext fun i=>congrArg v (Fin.ext (by omega)) }
  | q+1 => {
      toFun := fun v=>Fin.cons v.1 (siteCoords q v.2)
      invFun := fun v=>(v 0,(siteCoords q).symm (Fin.tail v))
      left_inv := fun v=>by
        apply Prod.ext
        · rfl
        · simp
      right_inv := fun v=>by
        funext i
        refine Fin.cases ?_ (fun j=> ?_) i
        · rfl
        · simp [Fin.tail] }

def splitCoords (q:ℕ) : Sites q ≃ ((Fin (q+1)→K)×(Fin (q+1)→K)) :=
  (siteCoords q).trans <|
    (Equiv.arrowCongr (Equiv.refl _) labelBits).trans {
      toFun a := (fun i=>(a i).1,fun i=>(a i).2)
      invFun a := fun i=>(a.1 i,a.2 i)
      left_inv _ := rfl
      right_inv _ := rfl }

private theorem coordinate_first (q:ℕ) (j:Sites q) (i:Fin (q+1)) :
    (splitCoords q j).1 i=firstBit (siteCoords q j i) := rfl

private theorem coordinate_second (q:ℕ) (j:Sites q) (i:Fin (q+1)) :
    (splitCoords q j).2 i=secondBit (siteCoords q j i) := rfl

end LiteralPairedRibbon
end

section
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
open PairedSpectralTrace PairedBellSign
open scoped BigOperators

namespace LiteralPairedRibbon

def loc (u:Bool) (x y c d:K) : K := x*y+x*d+y*c+tau u*c*d

def intSign (a:K) : ℤ := if a=0 then 1 else -1

private theorem real_cast_sign (a:K) : (intSign a : ℝ)=sign a := by
  unfold intSign sign
  split_ifs <;> norm_num

private theorem local_real_numerator : ∀ (u:Bool) (l j:Fin 4),
    (intSign (loc u (firstBit j) 0 (firstBit l) (secondBit l)) +
      intSign (secondBit j) *
        intSign (loc u (firstBit j) 1 (firstBit l) (secondBit l))) =
      2 * intSign (tau u*firstBit l*secondBit l) * quantumBell l j := by decide

def projectedLoc (u:Bool) (l j:Fin 4) (y:K) : ℝ :=
  sign (y*secondBit j) * sign (loc u (firstBit j) y (firstBit l) (secondBit l)) /
    (2*Real.sqrt 2)

def localAmplitude (u:Bool) (l j:Fin 4) : ℝ := ∑ y : K, projectedLoc u l j y

private theorem zmod2_sum {A:Type*} [AddCommMonoid A] (f:K→A) : ∑ y:K,f y = f 0+f 1 := by
  rw [← Equiv.sum_comp (ZMod.finEquiv 2).toEquiv f,Fin.sum_univ_two]
  rfl

private theorem local_amplitude_formula (u:Bool) (l j:Fin 4) :
    localAmplitude u l j =
      sign (tau u*firstBit l*secondBit l) * (quantumBell l j : ℝ) / Real.sqrt 2 := by
  unfold localAmplitude
  rw [zmod2_sum]
  have h := congrArg (Int.cast : ℤ→ℝ) (local_real_numerator u l j)
  push_cast at h
  simp only [real_cast_sign] at h
  unfold projectedLoc
  simp only [zero_mul,one_mul,sign_zero,one_mul]
  rw [← add_div, h]
  have hpos : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

/-- The retained conditional amplitude of the fixed literal graph, measured
on the erased mask and then acted on by the right product Hadamard. -/
def ribbonAmplitude {q:ℕ} (u:Fin (q+1)→Bool) (l j:Sites q) : ℝ :=
  let (c,d) := splitCoords q l
  let (x,z) := splitCoords q j
  ∑ y : Fin (q+1)→K,
    (∏ i, (sign (y i*z i) / (2*Real.sqrt 2))) *
    sign (total (mask (phaseForm u) kept) (keptVec x) (keptVec y) (lostVec c) (lostVec d))

private theorem literal_hadamard_tensor {q:ℕ} (u:Fin (q+1)→Bool) (l j:Sites q) :
    ribbonAmplitude u l j =
      ∏ i, localAmplitude (u i) (siteCoords q l i) (siteCoords q j i) := by
  unfold ribbonAmplitude
  simp only [literal_mask_sign,coordinate_first,coordinate_second]
  rw [show (∏ i, localAmplitude (u i) (siteCoords q l i) (siteCoords q j i)) =
      ∏ i, ∑ y:K, projectedLoc (u i) (siteCoords q l i) (siteCoords q j i) y from rfl, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  unfold projectedLoc loc
  ring

end LiteralPairedRibbon
end

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonOneBit

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonMask

open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonOneBit
open PairedBellSign PairedSpectralTrace LiteralPairedRibbon
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonErasure
open scoped BigOperators

/-- The actual measured register of one constructed literal ribbon carrier,
after the right local Hadamards, is the tensor of its signed Bell amplitudes.
Each erased twist enters only the scalar sign of the corresponding site. -/
theorem literal_tensor_transport {q:ℕ} (u:Fin (q+1)→Bool) :
    (∀ l j : Sites q,
      ribbonAmplitude u l j =
        ∏ i, localAmplitude (u i) (siteCoords q l i) (siteCoords q j i)) ∧
    (∀ (v:Bool) (l j:Fin 4),
      localAmplitude v l j = sign (tau v*firstBit l*secondBit l) *
        (quantumBell l j : ℝ) / Real.sqrt 2) :=
  ⟨literal_hadamard_tensor u, local_amplitude_formula⟩

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.PairedRibbonMask
