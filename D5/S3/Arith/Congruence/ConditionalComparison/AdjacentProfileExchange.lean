/- GID: D5/S3/Arith/Congruence/ConditionalComparison/AdjacentProfileExchange
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/ConditionalComparison/AdjacentProfileExchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Adjacent prime-height bounds permit a strict global covering exchange. -/

import D5.S3.Arith.Congruence.ConditionalComparison.ArithmeticCoordinates
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Erdos7

set_option maxHeartbeats 1000000 in
-- One proof combines radix decoding, full CRT transport, and finite cover reconstruction.
/-- Bounds above and at a prime-height cut permit one global exchange with
strictly fewer classes and a strictly smaller modulus sum. The same output
preserves distinctness and oddness whenever the input has those properties. -/
theorem adjacent_profile_exchange {L p q H G W k A B : ℕ}
    (modulus residue : Fin L → ℕ)
    (hcover : ∀ x : ℕ, ∃ i, x ≡ residue i [MOD modulus i])
    (hnonunit : ∀ i, 1 < modulus i)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpodd : Odd p)
    (hW : Nat.Coprime W (p * q))
    (hperiod : ∀ i, modulus i ∣ p ^ H * q ^ G * W)
    (htail : ∀ i, k < (modulus i).factorization q →
      (modulus i).factorization p ≤ A)
    (hcut : ∀ i, (modulus i).factorization q = k →
      (modulus i).factorization p ≤ B)
    (donor : Fin L) (hpure : modulus donor = q ^ (k + 1))
    (hsize : p ^ (A + B + 1) < q) :
    ∃ L' : ℕ, ∃ modulus' residue' : Fin L' → ℕ,
      (∀ x : ℕ, ∃ i, x ≡ residue' i [MOD modulus' i]) ∧
      (∀ i, 1 < modulus' i) ∧ L' < L ∧
      (∑ i : Fin L', modulus' i) < ∑ i : Fin L, modulus i ∧
      (Function.Injective modulus → Function.Injective modulus') ∧
      ((∀ i, Odd (modulus i)) → ∀ i, Odd (modulus' i)) := by
  classical
  have hp2 := hp.two_le
  have hpq : p < q := lt_of_le_of_lt (by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by omega : 1 ≤ p) (by omega : 1 ≤ A+B+1))) hsize
  have hpne : p ≠ q := ne_of_lt hpq
  have hqp : Nat.Coprime q p := (Nat.coprime_primes hq hp).mpr (Ne.symm hpne)
  have hqW : Nat.Coprime q W := (Nat.coprime_mul_iff_right.mp hW).2.symm
  have hqR : Nat.Coprime q (p^H*W) := (hqp.pow_right H).mul_right hqW
  have hWpos : 0 < W := by
    by_contra h
    have hzero : W = 0 := by omega
    rw [hzero, Nat.coprime_zero_left] at hW
    have := hp.two_le
    have := hq.two_le
    nlinarith
  -- Factor each actual original at the two distinguished primes.
  have hdecomp : ∀ i, ∃ a e m, a ≤ H ∧ e ≤ G ∧ m ∣ W ∧ 0 < m ∧
      Nat.Coprime m (p*q) ∧ modulus i = p^a*q^e*m := by
    intro i
    have hd : modulus i ∣ p^H*(q^G*W) := by
      simpa only [mul_assoc] using hperiod i
    obtain ⟨u,v,hu,hv,huv⟩ := exists_dvd_and_dvd_of_dvd_mul hd
    obtain ⟨a,ha,haeq⟩ := (Nat.dvd_prime_pow hp).mp hu
    obtain ⟨w,m,hw,hm,hwm⟩ := exists_dvd_and_dvd_of_dvd_mul hv
    obtain ⟨e,he,heeq⟩ := (Nat.dvd_prime_pow hq).mp hw
    refine ⟨a,e,m,ha,he,hm,?_,hW.coprime_dvd_left hm,?_⟩
    · exact Nat.pos_of_dvd_of_pos hm hWpos
    · rw [huv,haeq,hwm,heeq]; ring
  choose a e m ha he hm hmpos hmco hdeq using hdecomp
  have vals {a e m : ℕ} (hm : Nat.Coprime m (p*q)) (hmpos : 0 < m) :
      (p^a*q^e*m).factorization p = a ∧
      (p^a*q^e*m).factorization q = e := by
    have hpm : ¬p∣m := hp.coprime_iff_not_dvd.mp
      (Nat.coprime_mul_iff_right.mp hm).1.symm
    have hqm : ¬q∣m := hq.coprime_iff_not_dvd.mp
      (Nat.coprime_mul_iff_right.mp hm).2.symm
    constructor <;>
      simp [Nat.factorization_mul, hp.ne_zero, hq.ne_zero, Nat.ne_of_gt hmpos,
        Nat.factorization_pow, hp.factorization, hq.factorization, hpne, Ne.symm hpne,
        Nat.factorization_eq_zero_of_not_dvd hpm,
        Nat.factorization_eq_zero_of_not_dvd hqm]
  have hvals : ∀ i, (modulus i).factorization p = a i ∧
      (modulus i).factorization q = e i := by
    intro i; rw [hdeq]; exact vals (hmco i) (hmpos i)
  have htail' : ∀ i, k < e i → a i ≤ A := by
    intro i hi
    simpa only [(hvals i).1] using htail i (by simpa only [(hvals i).2] using hi)
  have hcut' : ∀ i, e i = k → a i ≤ B := by
    intro i hi
    simpa only [(hvals i).1] using hcut i (by simpa only [(hvals i).2] using hi)
  have hdonore : e donor = k+1 := by
    have hh := (hvals donor).2
    rw [hpure] at hh
    simpa [Nat.factorization_pow,hq.factorization] using hh.symm
  have hkG : k+1 ≤ G := hdonore ▸ he donor
  -- The first alphabet skips the donor digit; every subsequent block has A+1 digits.
  let R := p^(A+B+1)
  let C := p^(A+1)
  let delta := (residue donor / q^k)%q
  have hRpos : 0 < R := pow_pos hp.pos _
  have hCpos : 0 < C := pow_pos hp.pos _
  have hCq : C < q := lt_of_le_of_lt
    (pow_le_pow_right₀ (by omega : 1 ≤ p) (by omega : A+1 ≤ A+B+1)) hsize
  let first : ℕ → ℕ := fun x => if x%R < delta then x%R else x%R+1
  have hfirst : ∀ x, first x < q := by
    intro x
    have := Nat.mod_lt x hRpos
    dsimp [first]
    split_ifs <;> dsimp [R] at * <;> omega
  have havoid : ∀ x, first x ≠ delta := by
    intro x; dsimp [first]; split_ifs <;> omega
  have hinitial : ∀ x y, first x = first y → x%R=y%R := by
    intro x y hh
    dsimp [first] at hh
    split_ifs at hh <;> omega
  let word : ℕ → Word q (G-k) := fun x i =>
    if hi : i.val = 0 then ⟨first x, hfirst x⟩
    else ⟨x/R/C^(i.val-1)%C, (Nat.mod_lt _ hCpos).trans hCq⟩
  let f : ℕ → ℕ := fun x => embeddedWordValue q (word x)
  have hffirst : ∀ x, f x % q = first x := by
    intro x
    have hdigits : ∀ z ∈ List.ofFn (fun i => (word x i : ℕ)), z < q := by
      intro z hz
      simp only [List.mem_ofFn] at hz
      obtain ⟨i,rfl⟩ := hz
      exact (word x i).isLt
    have htake := Nat.ofDigits_mod_pow_eq_ofDigits_take 1 hq.pos
      (List.ofFn fun i => (word x i : ℕ)) hdigits
    change Nat.ofDigits q (List.ofFn fun i => (word x i : ℕ))%q=first x
    rw [pow_one] at htake
    rw [htake, ← Fin.ofFn_take_eq_take_ofFn (by omega : 1 ≤ G-k)]
    simp [Fin.take,word,List.ofFn_succ,Nat.ofDigits_cons]
  have hdigits : ∀ (j x y : ℕ),
      (∀ i, i<j → x/C^i%C=y/C^i%C) → x%C^j=y%C^j := by
    intro j
    induction j with
    | zero => intro x y hxy; simp only [pow_zero,Nat.mod_one]
    | succ j ih =>
      intro x y hxy
      rw [Nat.mod_pow_succ (x := x) (b := C),
        Nat.mod_pow_succ (x := y) (b := C),
        ih x y (fun i hi => hxy i (by omega)),hxy j (by omega)]
  have hfsep : ∀ t, 1 ≤ t → t ≤ G-k → ∀ x y,
      f x ≡ f y [MOD q^t] → x ≡ y [MOD p^(B+t*(A+1))] := by
    intro t ht htN x y hxy
    have hpre := embeddedWordValue_prefix_eq hq.one_lt le_rfl htN (word x) (word y) hxy
    have hfirstxy : first x = first y := by
      have hh := congrArg Fin.val (hpre ⟨0,by omega⟩)
      simpa [word,Fin.take] using hh
    have hroot := hinitial x y hfirstxy
    have htailxy : x/R%C^(t-1)=y/R%C^(t-1) := by
      apply hdigits
      intro i hi
      have hh := congrArg Fin.val (hpre ⟨i+1,by omega⟩)
      simpa [word,Fin.take] using hh
    have hmod : x%(R*C^(t-1))=y%(R*C^(t-1)) := by
      rw [Nat.mod_mul,Nat.mod_mul,hroot,htailxy]
    have hpow : R*C^(t-1)=p^(B+t*(A+1)) := by
      dsimp [R,C]
      rw [←pow_mul,←pow_add]
      congr 1
      have ht' : t=(t-1)+1 := by omega
      conv_rhs => rw [ht']
      ring
    simpa only [Nat.ModEq,hpow] using hmod
  -- The common source preserves the full old p-height, independent of code depth.
  let source : ℕ → ℕ := fun x =>
    (Nat.chineseRemainder (hqR.pow_left G) (x%q^k+q^k*f x) x).val
  have hsourceq : ∀ x, source x ≡ x%q^k+q^k*f x [MOD q^G] := fun x =>
    (Nat.chineseRemainder (hqR.pow_left G) (x%q^k+q^k*f x) x).property.1
  have hsourceR : ∀ x, source x ≡ x [MOD p^H*W] := fun x =>
    (Nat.chineseRemainder (hqR.pow_left G) (x%q^k+q^k*f x) x).property.2
  have hsourceparent : ∀ x, source x ≡ x [MOD q^k] := by
    intro x
    exact ((hsourceq x).of_dvd (pow_dvd_pow q (by omega))).trans (by simp [Nat.ModEq])
  have hretained : ∀ i, e i ≤ k → ∀ x, source x ≡ x [MOD modulus i] := by
    intro i hi x
    have hfull := (Nat.modEq_and_modEq_iff_modEq_mul (hqR.pow_left k)).mp
      ⟨hsourceparent x,hsourceR x⟩
    apply hfull.of_dvd
    rw [hdeq]
    have hd := Nat.mul_dvd_mul (Nat.mul_dvd_mul (pow_dvd_pow p (ha i))
      (pow_dvd_pow q hi)) (hm i)
    convert hd using 1; ring
  have hsourcemiss : ∀ x, ¬source x ≡ residue donor [MOD modulus donor] := by
    intro x hx
    have hparent : x%q^k=residue donor%q^k :=
      (hsourceparent x).symm.trans
        (hx.of_dvd (by rw [hpure]; exact pow_dvd_pow q (by omega)))
    have hcode : x%q^k+q^k*f x ≡ residue donor [MOD q^(k+1)] :=
      ((hsourceq x).of_dvd (pow_dvd_pow q hkG)).symm.trans (by simpa only [hpure] using hx)
    have hleft : (x%q^k+q^k*f x)%q^(k+1) = x%q^k+q^k*(f x%q) := by
      rw [pow_succ,Nat.mod_mul,Nat.add_mul_mod_self_left]
      have hu : x%q^k < q^k := Nat.mod_lt _ (pow_pos hq.pos _)
      simp [Nat.mod_eq_of_lt hu,Nat.div_eq_of_lt hu,Nat.add_mul_div_left,pow_pos hq.pos]
    have hright : residue donor%q^(k+1) =
        residue donor%q^k+q^k*((residue donor/q^k)%q) := Nat.mod_mul (a:=q^k) (b:=q)
    have hmod : (x%q^k+q^k*f x)%q^(k+1)=residue donor%q^(k+1) := hcode
    rw [hleft,hright,hparent,hffirst] at hmod
    apply havoid x
    dsimp [delta]
    nlinarith [pow_pos hq.pos k]
  let exponent : Fin L → ℕ := fun i => B+1+(e i-k-1)*(A+1)+a i
  let label : Fin L → ℕ := fun i => p^(exponent i)*q^k*m i
  let inverse : Fin L → ℕ → Prop := fun i x => source x ≡ residue i [MOD modulus i]
  let Has : Fin L → Prop := fun i => ∃ x, inverse i x
  let chosen : Fin L → ℕ := fun i => if h : Has i then h.choose else 0
  have hchosen : ∀ i, Has i → inverse i (chosen i) := by
    intro i hi; simpa only [chosen,dif_pos hi] using hi.choose_spec
  -- Recover equal variable parents before cancelling the transported q-tail.
  have enclosure : ∀ i, k<e i → ∀ x y, inverse i x → inverse i y →
      x ≡ y [MOD label i] := by
    intro i hi x y hx hy
    have hsource : source x ≡ source y [MOD modulus i] := hx.trans hy.symm
    have hqdvd : q^(e i) ∣ modulus i := by
      rw [hdeq]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    have hsourcee := hsource.of_dvd hqdvd
    have hparent : x ≡ y [MOD q^k] := (hsourceparent x).symm.trans
      ((hsourcee.of_dvd (pow_dvd_pow q (by omega))).trans (hsourceparent y))
    have hparenteq : x%q^k=y%q^k := hparent
    have hcoords : x%q^k+q^k*f x ≡ y%q^k+q^k*f y [MOD q^(e i)] :=
      ((hsourceq x).of_dvd (pow_dvd_pow q (he i))).symm.trans
        (hsourcee.trans ((hsourceq y).of_dvd (pow_dvd_pow q (he i))))
    rw [hparenteq] at hcoords
    have hmul := Nat.ModEq.add_left_cancel (Nat.ModEq.refl (y%q^k)) hcoords
    have hf : f x ≡ f y [MOD q^(e i-k)] := by
      apply Nat.ModEq.mul_left_cancel' (pow_ne_zero _ hq.ne_zero)
      convert hmul using 1
      rw [←pow_add]; congr 1; omega
    have hpref := hfsep (e i-k) (by omega) (by have := he i; omega) x y hf
    have hexple : exponent i ≤ B+(e i-k)*(A+1) := by
      have ht := htail' i hi
      have heq : e i-k=(e i-k-1)+1 := by omega
      dsimp [exponent]
      conv_rhs => rw [heq]
      nlinarith
    have hpref' : x ≡ y [MOD p^(exponent i)] := hpref.of_dvd (pow_dvd_pow p hexple)
    have hpqco : Nat.Coprime (p^(exponent i)) (q^k) :=
      Nat.coprime_pow_primes _ _ hp hq hpne
    have hprefix := (Nat.modEq_and_modEq_iff_modEq_mul hpqco).mp ⟨hpref',hparent⟩
    have hmR : m i ∣ p^H*W := dvd_mul_of_dvd_right (hm i) _
    have hmsource : source x ≡ source y [MOD m i] := hsource.of_dvd (by
      rw [hdeq]; exact dvd_mul_left _ _)
    have hmxy := ((hsourceR x).of_dvd hmR).symm.trans
      (hmsource.trans ((hsourceR y).of_dvd hmR))
    have hpm : Nat.Coprime p (m i) := (Nat.coprime_mul_iff_right.mp (hmco i)).1.symm
    have hqm : Nat.Coprime q (m i) := (Nat.coprime_mul_iff_right.mp (hmco i)).2.symm
    exact (Nat.modEq_and_modEq_iff_modEq_mul
      (Nat.coprime_mul_iff_left.mpr ⟨hpm.pow_left _,hqm.pow_left _⟩)).mp ⟨hprefix,hmxy⟩
  have hlabelbound : ∀ i, k<e i → 1<label i ∧ label i<modulus i := by
    intro i hi
    have hexppos : 0 < exponent i := by dsimp [exponent]; omega
    have hlabelpos : 1 < p^(exponent i) := one_lt_pow₀ hp.one_lt (by omega)
    constructor
    · exact lt_of_lt_of_le hlabelpos (by
        dsimp [label]
        simpa only [mul_assoc] using Nat.le_mul_of_pos_right (p^(exponent i))
          (mul_pos (pow_pos hq.pos _) (hmpos i)))
    · have hBq : p^(B+1)<q := lt_of_le_of_lt
        (pow_le_pow_right₀ (by omega : 1 ≤ p) (by omega : B+1 ≤ A+B+1)) hsize
      have htailpow : (p^(A+1))^(e i-k-1) ≤ q^(e i-k-1) :=
        Nat.pow_le_pow_left hCq.le _
      have hcost : p^(B+1)*(p^(A+1))^(e i-k-1)<q^(e i-k) := by
        calc
          p^(B+1)*(p^(A+1))^(e i-k-1)
            ≤ p^(B+1)*q^(e i-k-1) := Nat.mul_le_mul_left _ htailpow
          _ < q*q^(e i-k-1) :=
            (Nat.mul_lt_mul_right (pow_pos hq.pos _)).mpr hBq
          _ = q^(e i-k) := by rw [←pow_succ']; congr 1; omega
      have hcommonpos : 0<p^(a i)*q^k*m i :=
        mul_pos (mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)) (hmpos i)
      calc
        label i = (p^(B+1)*(p^(A+1))^(e i-k-1))*(p^(a i)*q^k*m i) := by
          dsimp [label,exponent]
          rw [pow_add,pow_add,pow_mul]; ring
        _ < q^(e i-k)*(p^(a i)*q^k*m i) := (Nat.mul_lt_mul_right hcommonpos).mpr hcost
        _ = modulus i := by
          rw [hdeq]
          have hei : e i=(e i-k)+k := by omega
          nth_rw 2 [hei]
          rw [pow_add]; ring
  -- New labels encode the old height as the remainder modulo A+1.
  have hlabelinj : ∀ i j, k<e i → k<e j → label i=label j → modulus i=modulus j := by
    intro i j hi hj hij
    have hv := congrArg (fun n : ℕ => n.factorization p) hij
    change (p^(exponent i)*q^k*m i).factorization p =
      (p^(exponent j)*q^k*m j).factorization p at hv
    rw [(vals (hmco i) (hmpos i)).1,(vals (hmco j) (hmpos j)).1] at hv
    have hrem : a i=a j := by
      have hh := congrArg (fun n : ℕ => n%(A+1))
        (Nat.add_left_cancel (show (B+1)+((e i-k-1)*(A+1)+a i) =
          (B+1)+((e j-k-1)*(A+1)+a j) by simpa [exponent,Nat.add_assoc] using hv))
      simpa [Nat.add_mod,Nat.mod_eq_of_lt (by have := htail' i hi; omega : a i<A+1),
        Nat.mod_eq_of_lt (by have := htail' j hj; omega : a j<A+1)] using hh
    have hmul : (e i-k-1)*(A+1)=(e j-k-1)*(A+1) := by
      dsimp [exponent] at hv; omega
    have heq : e i=e j := by
      have hh := Nat.eq_of_mul_eq_mul_right (by omega : 0<A+1) hmul
      omega
    have hmeq : m i=m j := by
      apply Nat.eq_of_mul_eq_mul_left (mul_pos (pow_pos hp.pos (exponent i)) (pow_pos hq.pos k))
      simpa only [label,hv] using hij
    rw [hdeq i,hdeq j,hrem,heq,hmeq]
  have hlabelne : ∀ i j, label i≠modulus j := by
    intro i j hij
    have hqval := congrArg (fun n : ℕ => n.factorization q) hij
    change (p^(exponent i)*q^k*m i).factorization q = (modulus j).factorization q at hqval
    rw [(vals (hmco i) (hmpos i)).2,(hvals j).2] at hqval
    have hpval := congrArg (fun n : ℕ => n.factorization p) hij
    change (p^(exponent i)*q^k*m i).factorization p = (modulus j).factorization p at hpval
    rw [(vals (hmco i) (hmpos i)).1,(hvals j).1] at hpval
    have hb := hcut' j hqval.symm
    dsimp [exponent] at hpval
    omega
  let active : Fin L → Prop := fun i => e i≤k ∨ Has i
  let newmod : Fin L → ℕ := fun i => if k<e i then label i else modulus i
  let newres : Fin L → ℕ := fun i => if k<e i then chosen i else residue i
  have hdonorinactive : ¬active donor := by
    rintro (hlo | ⟨x,hx⟩)
    · rw [hdonore] at hlo; omega
    · exact hsourcemiss x hx
  have hnewcover : ∀ x, ∃ i, active i ∧ x ≡ newres i [MOD newmod i] := by
    intro x
    obtain ⟨i,hi⟩ := hcover (source x)
    by_cases hei : k<e i
    · have hhas : Has i := ⟨x,hi⟩
      refine ⟨i,Or.inr hhas,?_⟩
      simpa only [newres,newmod,if_pos hei] using
        enclosure i hei x (chosen i) hi (hchosen i hhas)
    · have hlo : e i≤k := by omega
      refine ⟨i,Or.inl hlo,?_⟩
      simpa only [newres,newmod,if_neg hei] using (hretained i hlo x).symm.trans hi
  have hnewgt : ∀ i, 1<newmod i := by
    intro i; dsimp [newmod]; split_ifs with hi
    · exact (hlabelbound i hi).1
    · exact hnonunit i
  have hweight : ∀ i, (if active i then newmod i else 0)≤modulus i := by
    intro i; split_ifs with hi
    · dsimp [newmod]; split_ifs with hei
      · exact (hlabelbound i hei).2.le
      · exact le_rfl
    · exact Nat.zero_le _
  -- A single subtype enumeration carries coverage, strict count, and strict weight.
  let Active := {i : Fin L // active i}
  let n := Fintype.card Active
  let enum : Fin n ≃ Active := (Fintype.equivFin Active).symm
  have hsum : (∑ i : Fin n, newmod (enum i).val) =
      ∑ i : Fin L, if active i then newmod i else 0 := by
    rw [enum.sum_comp (fun i : Active => newmod i.val)]
    calc
      (∑ i : Active, newmod i.val) = ∑ i ∈ Finset.univ.filter active, newmod i :=
        (Finset.sum_subtype _ (by simp) newmod).symm
      _ = ∑ i : Fin L, if active i then newmod i else 0 := Finset.sum_filter _ _
  refine ⟨n,(fun i => newmod (enum i).val),(fun i => newres (enum i).val),?_,?_,?_,?_,?_,?_⟩
  · intro x
    obtain ⟨i,hi,hx⟩ := hnewcover x
    refine ⟨enum.symm ⟨i,hi⟩,?_⟩
    simpa only [Equiv.apply_symm_apply] using hx
  · intro i; exact hnewgt _
  · simpa only [Fintype.card_fin] using Fintype.card_subtype_lt hdonorinactive
  · rw [hsum]
    apply Finset.sum_lt_sum (fun i _ => hweight i)
    refine ⟨donor,Finset.mem_univ _,?_⟩
    rw [if_neg hdonorinactive]
    exact lt_trans Nat.zero_lt_one (hnonunit donor)
  · intro hold i j hij
    apply enum.injective
    apply Subtype.ext
    apply hold
    have hh : newmod (enum i).val=newmod (enum j).val := hij
    by_cases hi : k<e (enum i).val <;> by_cases hj : k<e (enum j).val
    · exact hlabelinj _ _ hi hj (by simpa only [newmod,if_pos hi,if_pos hj] using hh)
    · exact False.elim (hlabelne _ _
        (by simpa only [newmod,if_pos hi,if_neg hj] using hh))
    · exact False.elim (hlabelne _ _
        (by simpa only [newmod,if_pos hj,if_neg hi] using hh.symm))
    · simpa only [newmod,if_neg hi,if_neg hj] using hh
  · intro hold i
    dsimp only
    by_cases hi : k<e (enum i).val
    · have hmOdd : Odd (m (enum i).val) :=
        (Nat.odd_mul.mp (by simpa only [hdeq] using hold (enum i).val)).2
      have hqOdd : Odd q := hq.odd_of_ne_two (by have := hp.two_le; omega)
      simpa only [newmod,if_pos hi,label] using (hpodd.pow.mul hqOdd.pow).mul hmOdd
    · simpa only [newmod,if_neg hi] using hold (enum i).val

end Erdos7
