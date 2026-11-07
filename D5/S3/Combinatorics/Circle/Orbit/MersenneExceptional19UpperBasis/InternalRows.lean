/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19UpperBasis/InternalRows
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Module.Basic]
   utility: none
   digest: Integral exceptional19 UpperBasis InternalRows on original physical labels. -/
/- UNCOMPILED. Physical upper-to-upper bit transport and the integral inverse.
   The only group hypotheses below are induction invariants and annihilation
   of the ACTUAL selected masks. No proposed row formula is assumed. -/
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.Correction
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.Readout
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.HighRows
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Binary
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.CarryRows
import D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19Stabilizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
open scoped BigOperators
open MersenneExceptional19Stabilizer (degree base)
open MersenneExceptional19PermutationStabilizer
  (aa bb ss eighth eighth_facts parameter_parities digit read block)
open private digit_cases
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.Binary
open private gPoint fPoint hPoint gPoint_data fPoint_data hPoint_data eighth_power four_eighth_power
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19PermutationStabilizer.CarryRows
open private digit_period
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.Readout
open private g_selected_read f_selected_read h_selected_read
  from D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis.HighRows
open MersenneExceptional19Stabilizer (floor_unique)

private theorem two_pow_dvd (i j : ℕ) (h : i≤j) : (2 : ℤ)^i ∣ (2 : ℤ)^j := by
  refine ⟨(2 : ℤ)^(j-i),?_⟩
  rw [← pow_add,Nat.add_sub_of_le h]

private theorem digit_add_dvd (z t : ℤ) (j : ℕ)
    (ht : (2 : ℤ)^(j+1) ∣ t) : digit (z+t) j=digit z j := by
  obtain ⟨k,rfl⟩ := ht
  exact digit_period (j+1) j z k (by omega)

/-- Complementing an integer changes bit j to 1-bit j once a lower bit is
nonzero. The lower-modulus premise is discharged by a,b odd or s=2 mod 4. -/
private theorem digit_negative (z : ℤ) (n j : ℕ) (hnj : n≤j)
    (hn : z%(2 : ℤ)^n≠0) : digit (-z) j=1-digit z j := by
  have hp : 0<(2 : ℤ)^j := by positivity
  have hr0 : 0≤z%(2 : ℤ)^j := Int.emod_nonneg _ (by positivity)
  have hr1 : z%(2 : ℤ)^j<(2 : ℤ)^j := Int.emod_lt_of_pos _ hp
  have hrne : z%(2 : ℤ)^j≠0 := by
    intro he
    have hmod := Int.emod_emod_of_dvd z (two_pow_dvd n j hnj)
    rw [he,Int.zero_emod] at hmod
    exact hn hmod.symm
  have hrp : 0<z%(2 : ℤ)^j := by omega
  have he := Int.emod_add_mul_ediv z ((2 : ℤ)^j)
  have hq : (-z)/(2 : ℤ)^j= -(z/(2 : ℤ)^j)-1 := by
    apply floor_unique hp <;> nlinarith only [he,hrp,hr1]
  unfold digit
  rw [hq]
  omega

/-- Exact low-endpoint bit signatures for the THREE ACTUAL internal upper
row differences. The lower endpoint here is another SELECTED UPPER row. -/
theorem actual_internal_bits (r j : ℕ) (hj : 2≤j ∧ j≤degree r-4) :
    digit (4*eighth r+bb r) j=digit (bb r) j ∧
    digit (4*eighth r) j=0 ∧
    digit (4*eighth r-aa r) j=1-digit (aa r) j ∧
    digit (fPoint r (j+1)+bb r) j=0 ∧
    digit (fPoint r (j+1)) j=1-digit (bb r) j ∧
    digit (fPoint r (j+1)-aa r) j=1-digit (ss r) j ∧
    digit (hPoint r (j+1)+bb r) j=digit (ss r) j ∧
    digit (hPoint r (j+1)) j=digit (aa r) j ∧
    digit (hPoint r (j+1)-aa r) j=0 := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  obtain ⟨ha,hb,hs⟩ := parameter_parities r
  have h4 : (2 : ℤ)^(j+1) ∣ 4*eighth r := by
    rw [four_eighth_power]
    exact two_pow_dvd _ _ (by omega)
  have h8 : (2 : ℤ)^(j+1) ∣ 8*eighth r := by
    have hB := (eighth_facts r).1
    rw [← hB]
    have hp : (base r : ℤ)=(2 : ℤ)^degree r := by simp [base]
    rw [hp]
    exact two_pow_dvd _ _ (by omega)
  have hF : (2 : ℤ)^(j+1) ∣ 8*eighth r-(2 : ℤ)^(j+1) :=
    dvd_sub h8 (dvd_refl _)
  have hH : (2 : ℤ)^(j+1) ∣ 4*eighth r-(2 : ℤ)^(j+1) :=
    dvd_sub h4 (dvd_refl _)
  have na := digit_negative (aa r) 1 j (by omega) (by norm_num; omega)
  have nb := digit_negative (bb r) 1 j (by omega) (by norm_num; omega)
  have ns := digit_negative (ss r) 2 j (by omega) (by norm_num; omega)
  have z4 := digit_add_dvd 0 (4*eighth r) j h4
  have zF := digit_add_dvd 0 (8*eighth r-(2 : ℤ)^(j+1)) j hF
  have zH := digit_add_dvd 0 (4*eighth r-(2 : ℤ)^(j+1)) j hH
  simp only [zero_add,digit,Int.zero_ediv,Int.zero_emod] at z4 zF zH
  have fdef : fPoint r (j+1)=8*eighth r-bb r-(2 : ℤ)^(j+1) := by
    simp [fPoint,show j+1≠degree r-2 by omega]
  have hdef : hPoint r (j+1)=4*eighth r+aa r-(2 : ℤ)^(j+1) := rfl
  refine ⟨?_,z4,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [add_comm] using digit_add_dvd (bb r) _ j h4
  · simpa only [sub_eq_add_neg,add_comm] using
      (digit_add_dvd (-aa r) _ j h4).trans na
  · simpa only [fdef,show 8*eighth r-bb r-(2 : ℤ)^(j+1)+bb r=
        8*eighth r-(2 : ℤ)^(j+1) by ring] using zF
  · simpa only [fdef,show 8*eighth r-bb r-(2 : ℤ)^(j+1)=
        -bb r+(8*eighth r-(2 : ℤ)^(j+1)) by ring] using
      (digit_add_dvd (-bb r) _ j hF).trans nb
  · simpa only [fdef,show 8*eighth r-bb r-(2 : ℤ)^(j+1)-aa r=
        -ss r+(8*eighth r-(2 : ℤ)^(j+1)) by dsimp [ss]; ring] using
      (digit_add_dvd (-ss r) _ j hF).trans ns
  · simpa only [hdef,show 4*eighth r+aa r-(2 : ℤ)^(j+1)+bb r=
        ss r+(4*eighth r-(2 : ℤ)^(j+1)) by dsimp [ss]; ring] using
      digit_add_dvd (ss r) _ j hH
  · simpa only [hdef,show 4*eighth r+aa r-(2 : ℤ)^(j+1)=
        aa r+(4*eighth r-(2 : ℤ)^(j+1)) by ring] using
      digit_add_dvd (aa r) _ j hH
  · simpa only [hdef,show 4*eighth r+aa r-(2 : ℤ)^(j+1)-aa r=
        4*eighth r-(2 : ℤ)^(j+1) by ring] using zH

variable {A : Type*} [AddCommGroup A]

/-- Word readout for three blocks, used on the explicitly corrected labels. -/
def wordRead (r : ℕ) (Y : Fin 3 → ℕ → A) (M : ℤ) : A :=
  read (degree r) (Y 0) (M+bb r)+read (degree r) (Y 1) M+
    read (degree r) (Y 2) (M-aa r)

/-- Actual synchronous addition of 2^j in all three original words, with
valid d-bit endpoints proved from the sealed physical ranges. -/
theorem actual_internal_readouts (r j : ℕ) (Y : Fin 3 → ℕ → A)
    (hj : 2≤j ∧ j≤degree r-4)
    (hdbl : ∀ p i, j < i → i < degree r →
      Y p i=(2 : ℤ)^(i-j-1) • Y p (j+1))
    (hsum : Y 0 (j+1)+Y 1 (j+1)+Y 2 (j+1)=0) :
    let α := digit (aa r) j
    let β := digit (bb r) j
    let σ := digit (ss r) j
    let T := Y 0 j+Y 1 j+Y 2 j
    let F := (2 : ℤ) • Y 0 j-Y 0 (j+1)
    let G := (2 : ℤ) • Y 1 j-Y 1 (j+1)
    wordRead r Y (gPoint r j)-wordRead r Y (4*eighth r)=
        (2*α-1) • T+(1-α-β) • F+(1-α) • G ∧
    wordRead r Y (fPoint r j)-wordRead r Y (fPoint r (j+1))=
        (2*σ-1) • T+(1-σ) • F+(β-σ) • G ∧
    wordRead r Y (hPoint r j)-wordRead r Y (hPoint r (j+1))=
        T-σ • F-α • G := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,b8⟩ := actual_internal_bits r j hj
  have hgb : MersenneExceptional19PermutationStabilizer.affineRange r (4*eighth r) := by
    obtain ⟨hB,hE,hemod⟩ := eighth_facts r
    obtain ⟨ha0,ha1,hb0,hb1,hs0,hs1⟩ :=
      MersenneExceptional19PermutationStabilizer.parameter_margins r
    exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  have rangeG := (gPoint_data r j
    ⟨by omega,by omega,by omega⟩).1
  have rangeF := (fPoint_data r (j+1)
    ⟨by omega,by omega⟩).1
  have rangeH := (hPoint_data r (j+1)
    ⟨by omega,by omega⟩).1
  have rangeF' := (fPoint_data r j
    ⟨by omega,by omega⟩).1
  have rangeH' := (hPoint_data r j
    ⟨by omega,by omega⟩).1
  have eg : gPoint r j=4*eighth r+(2 : ℤ)^j := by
    simp [gPoint,show j≠degree r-1 by omega,show j≠degree r-2 by omega]
  have ef : fPoint r j=fPoint r (j+1)+(2 : ℤ)^j := by
    simp only [fPoint,show j≠degree r-2 by omega,
      show j+1≠degree r-2 by omega,ite_false,pow_succ]
    ring
  have eh : hPoint r j=hPoint r (j+1)+(2 : ℤ)^j := by
    simp only [hPoint,pow_succ]
    ring
  have step (p : Fin 3) (m m' : ℤ) (he : m'=m+(2 : ℤ)^j)
      (hm : 0≤m ∧ m<base r) (hm' : 0≤m' ∧ m'<base r) :
      read (degree r) (Y p) m'-read (degree r) (Y p) m=
        (1-2*digit m j) • Y p j+digit m j • Y p (j+1) := by
    rw [he]
    apply read_add_power _ _ _ _ (by omega)
    · simpa only [← he,show (2 : ℤ)^degree r=(base r : ℤ) by simp [base]] using
        And.intro hm.1 hm'.2
    · exact hdbl p
  obtain ⟨bg0,bg1,bg2,bgC⟩ :=
    MersenneExceptional19PermutationStabilizer.affine_digits r _ hgb
  obtain ⟨gg0,gg1,gg2,ggC⟩ :=
    MersenneExceptional19PermutationStabilizer.affine_digits r _ rangeG
  obtain ⟨ff0,ff1,ff2,ffC⟩ :=
    MersenneExceptional19PermutationStabilizer.affine_digits r _ rangeF
  obtain ⟨ff0',ff1',ff2',ffC'⟩ :=
    MersenneExceptional19PermutationStabilizer.affine_digits r _ rangeF'
  obtain ⟨hh0,hh1,hh2,hhC⟩ :=
    MersenneExceptional19PermutationStabilizer.affine_digits r _ rangeH
  obtain ⟨hh0',hh1',hh2',hhC'⟩ :=
    MersenneExceptional19PermutationStabilizer.affine_digits r _ rangeH'
  have g0 := step 0 _ _ (by rw [eg]; ring) bg0 gg0
  have g1 := step 1 _ _ eg bg1 gg1
  have g2 := step 2 _ _ (by rw [eg]; ring) bg2 gg2
  have f0 := step 0 _ _ (by rw [ef]; ring) ff0 ff0'
  have f1 := step 1 _ _ ef ff1 ff1'
  have f2 := step 2 _ _ (by rw [ef]; ring) ff2 ff2'
  have h0 := step 0 _ _ (by rw [eh]; ring) hh0 hh0'
  have h1 := step 1 _ _ eh hh1 hh1'
  have h2 := step 2 _ _ (by rw [eh]; ring) hh2 hh2'
  rw [b0] at g0
  rw [b1] at g1
  rw [b2] at g2
  rw [b3] at f0
  rw [b4] at f1
  rw [b5] at f2
  rw [b6] at h0
  rw [b7] at h1
  rw [b8] at h2
  dsimp only [wordRead]
  refine ⟨?_,?_,?_⟩
  · linear_combination (norm := module) g0+g1+g2+
      (1-digit (aa r) j) • hsum
  · linear_combination (norm := module) f0+f1+f2+
      (1-digit (ss r) j) • hsum
  · linear_combination (norm := module) h0+h1+h2

/-- The inverse is a polynomial integer identity for arbitrary idempotent
bits. It is consumed by selected_internal_step, not left as a certificate. -/
private theorem invert_internal (α β σ : ℤ) (T F G rG rF rH : A)
    (ha : α*α=α) (hb : β*β=β) (hs : σ*σ=σ)
    (hg : rG=(2*α-1) • T+(1-α-β) • F+(1-α) • G)
    (hf : rF=(2*σ-1) • T+(1-σ) • F+(β-σ) • G)
    (hh : rH=T-σ • F-α • G) :
    let e := α+σ-2*α*σ
    let τ := 1-β-e
    let ω := β-e
    let L := rG-(2*α-1) • rH
    let M := rF-(2*σ-1) • rH
    F=M-ω • L ∧ G=L-τ • M ∧ T=rH+σ • F+α • G := by
  dsimp only
  let e := α+σ-2*α*σ
  let τ := 1-β-e
  let ω := β-e
  have he : e*e=e := by
    have hid : e*e-e=(α*α-α)*(2*σ-1)^2+(σ*σ-σ) := by
      dsimp [e]
      ring
    rw [ha,hs,sub_self,sub_self,zero_mul,zero_add] at hid
    omega
  have hτω : τ*ω=0 := by
    dsimp [τ,ω]
    nlinarith only [hb,he]
  have hL : rG-(2*α-1) • rH=τ • F+G := by
    calc
      _=((1-α-β)+(2*α-1)*σ) • F+((1-α)+(2*α-1)*α) • G := by
        rw [hg,hh]
        module
      _=τ • F+G := by
        rw [show (1-α)+(2*α-1)*α=1 by nlinarith only [ha]]
        dsimp [τ,e]
        module
  have hM : rF-(2*σ-1) • rH=F+ω • G := by
    calc
      _=((1-σ)+(2*σ-1)*σ) • F+((β-σ)+(2*σ-1)*α) • G := by
        rw [hf,hh]
        module
      _=F+ω • G := by
        rw [show (1-σ)+(2*σ-1)*σ=1 by nlinarith only [hs]]
        dsimp [ω,e]
        module
  change F=_ ∧ G=_ ∧ T=_
  rw [hL,hM]
  refine ⟨?_,?_,?_⟩
  · calc
      F=F-(ω*τ) • F := by rw [mul_comm ω τ,hτω,zero_smul,sub_zero]
      _=(F+ω • G)-ω • (τ • F+G) := by module
  · calc
      G=G-(τ*ω) • G := by rw [hτω,zero_smul,sub_zero]
      _=(τ • F+G)-τ • (F+ω • G) := by module
  · rw [hh]
    module

/-- A genuine physical step of the upper-only presentation. The row formulas
are derived above, and the inverse is applied to the actual vanishing rows. -/
theorem selected_internal_step (r j : ℕ) (X : Fin (3*degree r) → A) (θ : A)
    (hX : SelectedAnnihilates r X) (hj : 2≤j ∧ j≤degree r-4)
    (hdbl : ∀ p i, j < i → i < degree r →
      correctedBlock r X θ p i=(2 : ℤ)^(i-j-1) • correctedBlock r X θ p (j+1))
    (hsum : correctedBlock r X θ 0 (j+1)+correctedBlock r X θ 1 (j+1)+
      correctedBlock r X θ 2 (j+1)=0) :
    (∀ p, correctedBlock r X θ p (j+1)=(2 : ℤ) • correctedBlock r X θ p j) ∧
    correctedBlock r X θ 0 j+correctedBlock r X θ 1 j+correctedBlock r X θ 2 j=0 := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  let Y := correctedBlock r X θ
  obtain ⟨eG,eF,eH⟩ := actual_internal_readouts r j Y hj hdbl hsum
  have pres (M : ℤ) (hM : MersenneExceptional19PermutationStabilizer.affineRange r M) :
      wordRead r Y M=affineRead r X M := corrected_affine_read r X θ M hM
  have gbase := g_selected_read r (degree r-1) X hX ⟨by omega,by omega,by omega⟩
  simp only [gPoint,ite_true] at gbase
  have gzero := g_selected_read r j X hX ⟨by omega,by omega,by omega⟩
  have fzero := f_selected_read r j X hX ⟨by omega,by omega⟩
  have fnext := f_selected_read r (j+1) X hX ⟨by omega,by omega⟩
  have hzero := h_selected_read r j X hX ⟨by omega,by omega⟩
  have hnext := h_selected_read r (j+1) X hX ⟨by omega,by omega⟩
  have rangebase : MersenneExceptional19PermutationStabilizer.affineRange r (4*eighth r) := by
    simpa only [gPoint,ite_true] using
      (gPoint_data r (degree r-1) ⟨by omega,by omega,by omega⟩).1
  have rG : wordRead r Y (gPoint r j)-wordRead r Y (4*eighth r)=0 := by
    rw [pres _ (gPoint_data r j ⟨by omega,by omega,by omega⟩).1,
      pres _ rangebase,gzero,gbase,sub_self]
  have rF : wordRead r Y (fPoint r j)-wordRead r Y (fPoint r (j+1))=0 := by
    rw [pres _ (fPoint_data r j ⟨by omega,by omega⟩).1,
      pres _ (fPoint_data r (j+1) ⟨by omega,by omega⟩).1,fzero,fnext,sub_self]
  have rH : wordRead r Y (hPoint r j)-wordRead r Y (hPoint r (j+1))=0 := by
    rw [pres _ (hPoint_data r j ⟨by omega,by omega⟩).1,
      pres _ (hPoint_data r (j+1) ⟨by omega,by omega⟩).1,hzero,hnext,sub_self]
  have idem (z : ℤ) : digit z j*digit z j=digit z j := by
    rcases digit_cases z j with he | he <;> rw [he] <;> norm_num
  obtain ⟨iF,iG,iT⟩ := invert_internal (digit (aa r) j) (digit (bb r) j)
    (digit (ss r) j) (Y 0 j+Y 1 j+Y 2 j)
    ((2 : ℤ) • Y 0 j-Y 0 (j+1)) ((2 : ℤ) • Y 1 j-Y 1 (j+1))
    _ _ _ (idem _) (idem _) (idem _) eG eF eH
  simp only [rG,rF,rH,zero_smul,smul_zero,zero_sub,sub_zero,sub_self,add_zero,zero_add] at iF iG iT
  have HF : (2 : ℤ) • Y 0 j-Y 0 (j+1)=0 := iF
  have HG : (2 : ℤ) • Y 1 j-Y 1 (j+1)=0 := iG
  have HT : Y 0 j+Y 1 j+Y 2 j=0 := by simpa only [HF,HG,smul_zero,add_zero] using iT
  refine ⟨?_,HT⟩
  intro p
  fin_cases p
  · exact (sub_eq_zero.mp HF).symm
  · exact (sub_eq_zero.mp HG).symm
  · linear_combination (norm := module) hsum-(2 : ℤ) • HT+HF+HG

/-- All corrected levels j>=2 form a geometric ladder, and every corrected
triple at these levels sums to zero. This descent uses only selected uppers. -/
theorem selected_corrected_ladders (r : ℕ) (X : Fin (3*degree r) → A)
    (hX : SelectedAnnihilates r X) :
    let Y := correctedBlock r X (highTheta r X)
    (∀ p j, 2≤j → j < degree r → Y p j=(2 : ℤ)^(j-2) • Y p 2) ∧
    (∀ j, 2≤j → j < degree r → Y 0 j+Y 1 j+Y 2 j=0) := by
  have hd : 12≤degree r := by dsimp [degree]; omega
  let Y := correctedBlock r X (highTheta r X)
  obtain ⟨b1,b2,bT⟩ := selected_corrected_high r X hX
  have descent (v : ℕ) : ∀ j, 2≤j → j≤degree r-3 → degree r-3-j=v →
      (∀ p i, j≤i → i < degree r → Y p i=(2 : ℤ)^(i-j) • Y p j) ∧
      (∀ i, j≤i → i < degree r → Y 0 i+Y 1 i+Y 2 i=0) := by
    induction v using Nat.strong_induction_on with
    | h v ih =>
      intro j hj hjtop heq
      by_cases ht : j=degree r-3
      · subst j
        refine ⟨?_,?_⟩
        · intro p i hi hid
          have cases : i=degree r-3 ∨ i=degree r-2 ∨ i=degree r-1 := by omega
          rcases cases with rfl | rfl | rfl
          · simp
          · simpa only [show degree r-2-(degree r-3)=1 by omega,pow_one] using b1 p
          · simpa only [show degree r-1-(degree r-3)=2 by omega] using b2 p
        · intro i hi hid
          have cases : i=degree r-3 ∨ i=degree r-2 ∨ i=degree r-1 := by omega
          rcases cases with rfl | rfl | rfl
          · exact bT
          · rw [b1 0,b1 1,b1 2,← smul_add,← smul_add,bT,smul_zero]
          · rw [b2 0,b2 1,b2 2,← smul_add,← smul_add,bT,smul_zero]
      · obtain ⟨hn,hT⟩ := ih (degree r-3-(j+1)) (by omega) (j+1)
          (by omega) (by omega) rfl
        have hs := selected_internal_step r j X (highTheta r X) hX
          ⟨hj,by omega⟩ (by
            intro p i hji hid
            simpa only [show i-(j+1)=i-j-1 by omega] using hn p i (by omega) hid)
          (hT (j+1) le_rfl (by omega))
        refine ⟨?_,?_⟩
        · intro p i hji hid
          by_cases he : i=j
          · subst i
            simp
          · rw [hn p i (by omega) hid,hs.1 p,smul_smul]
            congr 1
            rw [show i-j=(i-(j+1))+1 by omega,pow_succ]
        · intro i hji hid
          by_cases he : i=j
          · subst i
            exact hs.2
          · exact hT i (by omega) hid
  have final := descent (degree r-3-2) 2 le_rfl (by omega) rfl
  exact ⟨fun p j hj hjd => final.1 p j hj hjd,final.2⟩

end D5.S3.Combinatorics.Circle.MersenneExceptional19UpperBasis
