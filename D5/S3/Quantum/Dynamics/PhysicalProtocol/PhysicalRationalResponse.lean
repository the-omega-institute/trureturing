/- GID: D5/S3/Quantum/Dynamics/PhysicalProtocol/PhysicalRationalResponse
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/PhysicalProtocol/PhysicalRationalResponse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full complex partition fixes a unique ordinary reduced binary response. -/

/- Utility: this is an unbounded physical representation and execution law for
   every raw clause family. It proves existence, uniqueness and symbolic length
   bounds from the actual trace, then consumes the all-word machine theorem.
   It supplies no finite certificate checker, bounded enumeration, certified
   finite instance or conditional numerical estimate. The other utility fields
   are not applicable for kind none. -/

import D5.S3.Quantum.Dynamics.ClauseHamiltonian
import D5.S0.Computability.RationalResponseRefinement
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PredictiveThermodynamic
open Turing StateTransition Lax51Proofs.RamToTM Physical

/-- Ordinary numerator, slash and denominator. Both components are reduced by Rat. -/
def rationalResponseWord (r : Rat) : List ResponseSymbol :=
  binaryWord r.num.natAbs.bits.reverse ++ .slash :: binaryWord r.den.bits.reverse

/-- The oracle relation refers only to the full complex trace and its positive rational spelling. -/
def PhysicalReply {n : Nat} (F : Formula n) (w : List ResponseSymbol) : Prop :=
  ∃ r : Rat, 0 < r ∧ (r : Complex) = fullPartition F ∧ w = rationalResponseWord r

/-- Concrete response data for the zero-variable, one-empty-clause physical query. -/
def dummyReply : List ResponseSymbol := [.one,.one,.slash,.one,.zero,.zero]

/-- The full physical trace supplies unique reduced syntax, the ordinary response
length bound, and a clean native run recovering the independently defined count. -/
theorem physical_reply_run {n : Nat} (F : Formula n) :
    ∃ w : List ResponseSymbol, PhysicalReply F w ∧
      (∀ w', PhysicalReply F w' → w' = w) ∧
      w.length ≤ n + 2*((n+1)*F.length) + 5 ∧
      suitableResponse w ∧
      Nonempty (TM2OutputsInTime postMachine w (some (binaryWord (totalPostOutput w)))
        (3*w.length+10)) ∧
      msbValue (totalPostOutput w) = satisfyingCount F := by
  classical
  let K := (n+1)*F.length
  let S := partitionNumerator F
  have sPositive : 0 < S := by
    apply Finset.sum_pos
    · intro a _; exact pow_pos (by decide) _
    · exact Finset.univ_nonempty
  have sBound : S ≤ 2^(n+K) := by
    calc
      S ≤ ∑ _a : Assignment n, 2^K := by
        apply Finset.sum_le_sum
        intro a _
        apply Nat.pow_le_pow_right (by decide)
        dsimp [K]
        exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 2^(n+K) := by simp [pow_add, Assignment]
  have denNonzero : 2^(K+1) ≠ (0 : Nat) := by positivity
  let r := Rat.normalize (3*S : Int) (2^(K+1)) denNonzero
  have rQuotient : r = (3*S : Rat)/2^(K+1) := by
    dsimp [r]
    rw [Rat.normalize_eq_mkRat, ←Rat.divInt_ofNat, Rat.divInt_eq_div]
    push_cast
    rfl
  have rPositive : 0 < r := by rw [rQuotient]; positivity
  have physical : (r : Complex) = fullPartition F := by
    rw [rQuotient, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow,
      Rat.cast_ofNat]
    exact (clause_partition_recovery F).1.1.symm
  obtain ⟨c,cNonzero,numFactor,denFactor⟩ :=
    Rat.normalize_num_den' (3*S : Int) (2^(K+1)) denNonzero
  change (3*S : Int) = r.num * (c : Int) at numFactor
  change 2^(K+1) = r.den*c at denFactor
  have cPositive : 0 < c := Nat.pos_of_ne_zero cNonzero
  have numPositive : 0 < r.num := by
    have cp : (0 : Int) < c := by exact_mod_cast cPositive
    have sp : (0 : Int) < S := by exact_mod_cast sPositive
    nlinarith [numFactor]
  have numCast : (r.num.natAbs : Int) = r.num := by
    simpa [Int.natCast_natAbs,abs_of_pos numPositive]
  let p := r.num.natAbs
  let q := r.den
  have pPositive : 0 < p := by
    have h : (0 : Int) < (p : Int) := by simpa only [p,numCast] using numPositive
    exact_mod_cast h
  have qPositive : 0 < q := r.pos
  have naturalFactor : 3*S = p*c := by
    exact_mod_cast (show (3*S : Int) = (p : Int)*c by simpa [p,numCast] using numFactor)
  have qDivides : q ∣ 2^(K+1) := ⟨c,denFactor⟩
  obtain ⟨e,eBound,qPower⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp qDivides
  have cDivides : c ∣ 2^(K+1) := ⟨q,by simpa [Nat.mul_comm] using denFactor⟩
  have noThree : ¬3 ∣ c := by
    intro hc
    have hd := dvd_trans hc cDivides
    have bad := (Nat.prime_three.dvd_of_dvd_pow hd)
    norm_num at bad
  have pThree : 3 ∣ p := by
    have hp : 3 ∣ p*c := by rw [←naturalFactor]; exact dvd_mul_right _ _
    exact (Nat.prime_three.dvd_mul.mp hp).resolve_right noThree
  have pOdd : 0 < e → Odd p := by
    intro he
    have noTwo : ¬2 ∣ p := by
      intro hp
      have hq : 2 ∣ q := by
        rw [qPower]
        exact dvd_pow_self 2 (Nat.ne_of_gt he)
      have impossible := Nat.dvd_gcd hp hq
      rw [show Nat.gcd p q = 1 from r.reduced] at impossible
      norm_num at impossible
    exact Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using noTwo)
  have bitValue : ∀ z : Nat, msbValue z.bits.reverse = z := by
    have representation : ∀ bs : List Bool,
        bitsValue bs = Nat.ofDigits 2 (bs.map fun b => cond b 1 0) := by
      intro bs
      induction bs with
      | nil => rfl
      | cons b bs ih =>
        cases b <;> simp [bitsValue,Nat.bit_val,Nat.ofDigits_cons,ih,Nat.add_comm]
    intro z
    rw [msbValue_reverse,representation,←Nat.digits_two_eq_bits,Nat.ofDigits_digits]
  have startsOne : ∀ z : Nat, 0 < z → ∃ xs : List Bool, z.bits.reverse = true::xs := by
    intro z
    induction z using Nat.binaryRecFromOne with
    | zero => intro h; omega
    | one => intro _; exact ⟨[],by simp⟩
    | bit b z hn ih =>
      intro _
      obtain ⟨xs,hxs⟩ := ih (Nat.pos_of_ne_zero hn)
      refine ⟨xs++[b],?_⟩
      rw [Nat.bits_append_bit z b (fun h => (hn h).elim),List.reverse_cons,hxs]
      rfl
  obtain ⟨xs,pSpelling⟩ := startsOne p pPositive
  have denominatorSpelling : (2^e : Nat).bits.reverse = true::List.replicate e false := by
    have all : ∀ e : Nat, (2^e : Nat).bits.reverse = true::List.replicate e false := by
      intro e
      induction e with
      | zero => simp
      | succ e ih =>
        rw [pow_succ, Nat.mul_comm, Nat.bit0_bits _ (by positivity),List.reverse_cons,ih]
        simp [List.replicate_succ']
    exact all e
  let w := rationalResponseWord r
  have spelling : w = responseWord xs e := by
    change binaryWord p.bits.reverse ++ .slash :: binaryWord q.bits.reverse = responseWord xs e
    rw [pSpelling,qPower,denominatorSpelling]
    simp [responseWord,binaryWord,List.map_append,bitSymbol]
  have pValue : msbValue (true::xs) = p := by rw [←pSpelling]; exact bitValue p
  have suitable : suitableResponse w := ⟨xs,e,spelling,by rwa [pValue],by rwa [pValue]⟩
  have pBound : p < 2^(n+K+2) := by
    have pLe : p ≤ 3*S := by nlinarith [naturalFactor]
    calc
      p ≤ 3*S := pLe
      _ ≤ 3*2^(n+K) := Nat.mul_le_mul_left _ sBound
      _ < 2^(n+K+2) := by
        have h : 0 < 2^(n+K) := by positivity
        rw [pow_add 2 (n+K) 2]
        norm_num
        omega
  have qBound : q < 2^(K+2) := by
    have qLe : q ≤ 2^(K+1) := by nlinarith [denFactor]
    calc
      q ≤ 2^(K+1) := qLe
      _ < 2^(K+2) := by
        have hp : 0 < 2^(K+1) := by positivity
        rw [show K+2 = (K+1)+1 by omega,pow_succ]
        omega
  have lengthBound : w.length ≤ n+2*K+5 := by
    have hp := Nat.size_le.mpr pBound
    have hq := Nat.size_le.mpr qBound
    change (binaryWord p.bits.reverse ++ .slash :: binaryWord q.bits.reverse).length ≤ n+2*K+5
    simp only [List.length_append,List.length_cons,binaryWord,List.length_map,
      List.length_reverse,Nat.size_eq_bits_len]
    omega
  obtain ⟨run,recover,_,_⟩ := post_word_run w
  have count : msbValue (totalPostOutput w) = satisfyingCount F := by
    have arithmetic := recover xs e spelling (by rwa [pValue]) (by rwa [pValue])
    rw [pValue] at arithmetic
    have rationalReal : (fullPartition F).re = (p : Real)/q := by
      rw [←physical,Complex.ratCast_re,Rat.cast_def]
      change (r.num : Real)/(q : Real) = (p : Real)/(q : Real)
      congr 1
      have h : (p : Int) = r.num := numCast
      exact_mod_cast h.symm
    have floorCount := (clause_partition_recovery F).1.2
    rw [rationalReal,qPower] at floorCount
    have pExact : p = 3*(p/3) := by omega
    cases e with
    | zero =>
      simp only [pow_zero,Nat.cast_one,div_one] at floorCount
      have normalized : (2/3 : Real)*(p : Real) = (2*(p/3) : Nat) := by
        nth_rw 1 [pExact]
        push_cast
        ring
      rw [normalized,Int.floor_natCast] at floorCount
      simp only [Nat.zero_eq,ite_true] at arithmetic
      exact arithmetic.trans (Int.natCast_inj.mp floorCount)
    | succ e =>
      have normalized : (2/3 : Real)*(p : Real)/(2:Real)^(e+1) =
          (p/3 : Nat)/(2:Real)^e := by
        nth_rw 1 [pExact]
        push_cast
        rw [pow_succ]
        field_simp <;> ring
      have denominatorCast : ((2^e : Nat) : Real) = (2 : Real)^e := by norm_cast
      rw [Nat.cast_pow, Nat.cast_ofNat, ←mul_div_assoc,normalized,←denominatorCast,
        Int.floor_div_natCast, Int.floor_natCast] at floorCount
      norm_cast at floorCount
      simpa [arithmetic] using floorCount
  refine ⟨w,⟨r,rPositive,physical,rfl⟩,?_,lengthBound,suitable,run,count⟩
  intro w' ⟨r',_,same,spell⟩
  have rr : r' = r := Rat.cast_injective (same.trans physical.symm)
  simpa [rr,w] using spell

end PredictiveThermodynamic
