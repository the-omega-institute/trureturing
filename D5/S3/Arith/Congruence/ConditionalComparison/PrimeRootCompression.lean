/- GID: D5/S3/Arith/Congruence/ConditionalComparison/PrimeRootCompression
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/ConditionalComparison/PrimeRootCompression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual prime-root avoidance compresses a distinct odd whole cover. -/

import D5.S3.Arith.Congruence.ConditionalComparison.ArithmeticCoordinates
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos7.OddDistinctCoveringSystem

/-- One injective choice of actual roots avoiding mixed classes and numerical
collision pairs transports the whole cover and deletes its pure-prime donor. -/
theorem prime_root_compression {n p q : ℕ} (F : OddDistinctCoveringSystem n)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (donor guard : Fin n) (hdonor : F.modulus donor = p) (hguard : F.modulus guard = q)
    (sigma : {b : Fin q // b.val ≠ F.residue guard % q} → Fin p)
    (hinj : Function.Injective sigma)
    (hmixed : ∀ (b : {b : Fin q // b.val ≠ F.residue guard % q}) (i : Fin n),
      p ∣ F.modulus i → q ∣ F.modulus i → F.residue i % q = b.val.val →
        (sigma b).val ≠ F.residue i % p)
    (hcollision : ∀ (b : {b : Fin q // b.val ≠ F.residue guard % q})
        (i j : Fin n) (u : ℕ), Nat.Coprime u (p * q) →
      F.modulus i = p * u → F.modulus j = q * u →
        (sigma b).val ≠ F.residue i % p) :
    ∃ N : ℕ, ∃ _G : OddDistinctCoveringSystem N, N < n := by
  classical
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hqodd : Odd q := hguard ▸ F.modulus_odd guard
  have hpodd : Odd p := hdonor ▸ F.modulus_odd donor
  obtain ⟨A, R, hpRnot, hperiodEq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd F.commonModulus_ne_zero p hp.ne_one
  have hpR : Nat.Coprime p R := hp.coprime_iff_not_dvd.mpr hpRnot
  have hperiod : ∀ i, F.modulus i ∣ p^A*R := by
    intro i; rw [← hperiodEq]; exact F.modulus_dvd_commonModulus i
  have hRpos : 0 < R := by
    have hh := F.commonModulus_ne_zero
    rw [hperiodEq] at hh
    exact Nat.pos_of_ne_zero (right_ne_zero_of_mul hh)
  have hA : 1 ≤ A := by
    by_contra hh
    have hAzero : A = 0 := by omega
    have hd := hperiod donor
    rw [hdonor, hAzero, pow_zero, one_mul] at hd
    exact hpRnot hd
  have hqR : q ∣ R := by
    apply (hcop.symm.pow_right A).dvd_of_dvd_mul_left
    simpa only [hguard] using hperiod guard
  have hfree : ∀ i, ¬p ∣ F.modulus i → F.modulus i ∣ R := by
    intro i hi
    exact ((hp.coprime_iff_not_dvd.mpr hi).symm.pow_right A).dvd_of_dvd_mul_left (hperiod i)
  have hdecomp : ∀ i, ∃ a u, a ≤ A ∧ u ∣ R ∧ 0 < u ∧ Nat.Coprime p u ∧
      F.modulus i = p^a*u := by
    intro i
    obtain ⟨v,u,hv,hu,hvu⟩ := exists_dvd_and_dvd_of_dvd_mul (hperiod i)
    obtain ⟨a,ha,hva⟩ := (Nat.dvd_prime_pow hp).mp hv
    exact ⟨a,u,ha,hu,Nat.pos_of_dvd_of_pos hu hRpos,hpR.coprime_dvd_right hu,
      by rw [hvu,hva]⟩
  choose a u ha hu hupos hpu hmod using hdecomp
  have hapos : ∀ i, p ∣ F.modulus i → 1 ≤ a i := by
    intro i hi
    by_contra hh
    have hz : a i = 0 := by omega
    rw [hmod i,hz,pow_zero,one_mul] at hi
    exact (hp.coprime_iff_not_dvd.mp (hpu i)) hi
  let B := {b : Fin q // b.val ≠ F.residue guard % q}
  let X := {x : ℕ // x%q ≠ F.residue guard % q}
  let root : X → B := fun x => ⟨⟨x.val%q,Nat.mod_lt _ hq.pos⟩,x.property⟩
  let source : X → ℕ := fun x =>
    (Nat.chineseRemainder (hpR.pow_left A) ((sigma (root x)).val+p*x.val) x.val).val
  have hsourceP (x : X) : source x ≡ (sigma (root x)).val+p*x.val [MOD p^A] :=
    (Nat.chineseRemainder (hpR.pow_left A) ((sigma (root x)).val+p*x.val) x.val).property.1
  have hsourceR (x : X) : source x ≡ x.val [MOD R] :=
    (Nat.chineseRemainder (hpR.pow_left A) ((sigma (root x)).val+p*x.val) x.val).property.2
  have hfirst (x : X) : source x % p = (sigma (root x)).val := by
    have hh := (hsourceP x).of_dvd (show p ∣ p^A by simpa only [pow_one] using pow_dvd_pow p hA)
    change source x % p = _
    have hhEq : source x % p = ((sigma (root x)).val+p*x.val)%p := hh
    simpa [Nat.add_mod,Nat.mod_eq_of_lt (sigma (root x)).isLt] using hhEq
  have hmixedMiss (i : Fin n) (hpi : p ∣ F.modulus i) (hqi : q ∣ F.modulus i)
      (x : X) : ¬source x ≡ F.residue i [MOD F.modulus i] := by
    intro hx
    have hrq : F.residue i % q = (root x).val.val :=
      (hx.of_dvd hqi).symm.trans ((hsourceR x).of_dvd hqR)
    have hrp : (sigma (root x)).val = F.residue i % p :=
      (hfirst x).symm.trans (hx.of_dvd hpi)
    exact hmixed (root x) i hpi hqi hrq hrp
  have hdonorMiss (x : X) : ¬source x ≡ F.residue donor [MOD F.modulus donor] := by
    intro hx
    have hrp : (sigma (root x)).val = F.residue donor % p :=
      (hfirst x).symm.trans (by simpa only [hdonor,Nat.ModEq] using hx)
    exact hcollision (root x) donor guard 1 (Nat.coprime_one_left _)
      (by simpa only [mul_one] using hdonor) (by simpa only [mul_one] using hguard) hrp
  let Has : Fin n → Prop := fun i => ∃ x : X, source x ≡ F.residue i [MOD F.modulus i]
  let chosen : Fin n → ℕ := fun i => if h : Has i then h.choose.val else 0
  have hchosen (i : Fin n) (hi : Has i) : ∃ x : X, x.val = chosen i ∧
      source x ≡ F.residue i [MOD F.modulus i] := by
    exact ⟨hi.choose,by simp only [chosen,dif_pos hi],hi.choose_spec⟩
  let label : Fin n → ℕ := fun i => q*p^(a i-1)*u i
  have enclosure (i : Fin n) (hpi : p ∣ F.modulus i) (hqi : ¬q ∣ F.modulus i)
      (x y : X) (hx : source x ≡ F.residue i [MOD F.modulus i])
      (hy : source y ≡ F.residue i [MOD F.modulus i]) :
      x.val ≡ y.val [MOD label i] := by
    have haa := hapos i hpi
    have hs := hx.trans hy.symm
    have hrootEq : sigma (root x) = sigma (root y) := by
      apply Fin.ext
      have hsame : source x % p = source y % p := hs.of_dvd hpi
      exact (hfirst x).symm.trans (hsame.trans (hfirst y))
    have hxyq : x.val ≡ y.val [MOD q] := congrArg (fun b : B => b.val.val) (hinj hrootEq)
    have hpdvd : p^(a i) ∣ F.modulus i := by rw [hmod i]; exact dvd_mul_right _ _
    have hpp : (sigma (root x)).val+p*x.val ≡ (sigma (root y)).val+p*y.val [MOD p^(a i)] :=
      ((hsourceP x).of_dvd (pow_dvd_pow p (ha i))).symm.trans
        ((hs.of_dvd hpdvd).trans ((hsourceP y).of_dvd (pow_dvd_pow p (ha i))))
    rw [hrootEq] at hpp
    have hmul := Nat.ModEq.add_left_cancel (Nat.ModEq.refl (sigma (root y)).val) hpp
    have hxyp : x.val ≡ y.val [MOD p^(a i-1)] := by
      apply Nat.ModEq.mul_left_cancel' hp.ne_zero
      convert hmul using 1
      rw [←pow_succ']; congr 1; omega
    have hudvd : u i ∣ F.modulus i := by rw [hmod i]; exact dvd_mul_left _ _
    have hxyu : x.val ≡ y.val [MOD u i] :=
      ((hsourceR x).of_dvd (hu i)).symm.trans
        ((hs.of_dvd hudvd).trans ((hsourceR y).of_dvd (hu i)))
    have hqu : Nat.Coprime q (u i) := hq.coprime_iff_not_dvd.mpr
      (fun hh => hqi (hh.trans hudvd))
    have hxypu := (Nat.modEq_and_modEq_iff_modEq_mul ((hpu i).pow_left _)).mp ⟨hxyp,hxyu⟩
    have hqpU : Nat.Coprime q (p^(a i-1)*u i) := (hcop.symm.pow_right _).mul_right hqu
    simpa only [label,mul_assoc] using
      (Nat.modEq_and_modEq_iff_modEq_mul hqpU).mp ⟨hxyq,hxypu⟩
  have label_eq (i : Fin n) (hpi : p ∣ F.modulus i) : p*label i=q*F.modulus i := by
    have hpow : p^(a i) = p*p^(a i-1) := by
      rw [←pow_succ']; congr 1; have := hapos i hpi; omega
    rw [hmod i,hpow]
    dsimp only [label]
    ring
  have label_gt (i : Fin n) : 1 < label i := by
    have hpow : 0 < p^(a i-1) := pow_pos hp.pos _
    have hqle : q ≤ q*(p^(a i-1)*u i) := Nat.le_mul_of_pos_right q (mul_pos hpow (hupos i))
    exact hq.one_lt.trans_le (by simpa only [label,mul_assoc] using hqle)
  have label_odd (i : Fin n) : Odd (label i) := by
    have huodd : Odd (u i) := (F.modulus_odd i).of_dvd_nat (by rw [hmod i]; exact dvd_mul_left _ _)
    exact (hqodd.mul hpodd.pow).mul huodd
  let active : Fin n → Prop := fun i => ¬p ∣ F.modulus i ∨ Has i
  let newMod : Fin n → ℕ := fun i => if p ∣ F.modulus i then label i else F.modulus i
  let newRes : Fin n → ℕ := fun i => if p ∣ F.modulus i then chosen i else F.residue i
  have active_qfree (i : Fin n) (hi : active i) (hpi : p ∣ F.modulus i) : ¬q ∣ F.modulus i := by
    intro hqi
    rcases hi with hfreei | ⟨x,hx⟩
    · exact hfreei hpi
    · exact hmixedMiss i hpi hqi x hx
  have hnewcover (x : ℕ) : ∃ i, active i ∧ x ≡ newRes i [MOD newMod i] := by
    by_cases hxguard : x%q = F.residue guard%q
    · have hpg : ¬p ∣ F.modulus guard := by
        rw [hguard]; exact hp.coprime_iff_not_dvd.mp hcop
      exact ⟨guard, Or.inl hpg, by
        simpa only [newMod,newRes,if_neg hpg,hguard,Nat.ModEq] using hxguard⟩
    · let xx : X := ⟨x,hxguard⟩
      obtain ⟨i,hi⟩ := F.covers (source xx)
      by_cases hpi : p ∣ F.modulus i
      · have hhas : Has i := ⟨xx,hi⟩
        have hact : active i := Or.inr hhas
        obtain ⟨y,hyval,hy⟩ := hchosen i hhas
        have hout := enclosure i hpi (active_qfree i hact hpi) xx y hi hy
        exact ⟨i,hact,by simpa only [newMod,newRes,if_pos hpi,hyval] using hout⟩
      · have hsame := (hsourceR xx).of_dvd (hfree i hpi)
        exact ⟨i,Or.inl hpi,by simpa only [newMod,newRes,if_neg hpi] using hsame.symm.trans hi⟩
  have hnewinj : ∀ i j, active i → active j → newMod i = newMod j → i=j := by
    intro i j hi hj heq
    by_cases hpi : p ∣ F.modulus i <;> by_cases hpj : p ∣ F.modulus j
    · have hh : label i = label j := by simpa only [newMod,if_pos hpi,if_pos hpj] using heq
      apply F.modulus_injective
      apply Nat.eq_of_mul_eq_mul_left hq.pos
      rw [←label_eq i hpi,←label_eq j hpj,hh]
    · have hh : label i = F.modulus j := by simpa only [newMod,if_pos hpi,if_neg hpj] using heq
      have hai : a i = 1 := by
        have hap := hapos i hpi
        by_contra hne
        have hdeep : 1 ≤ a i-1 := by omega
        have hd : p ∣ label i := dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_right (by simpa only [pow_one] using pow_dvd_pow p hdeep) q) (u i)
        exact hpj (hh ▸ hd)
      have hui : Nat.Coprime (u i) (p*q) := (hpu i).symm.mul_right
        (hq.coprime_iff_not_dvd.mpr (fun hd => (active_qfree i hi hpi)
          (hd.trans (by rw [hmod i]; exact dvd_mul_left _ _)))).symm
      have hm_i : F.modulus i = p*u i := by simpa only [hai,pow_one] using hmod i
      have hm_j : F.modulus j = q*u i := by
        simpa only [label,hai,Nat.sub_self,pow_zero,mul_one] using hh.symm
      have hhas : Has i := hi.resolve_left (fun hn => hn hpi)
      obtain ⟨x,hx⟩ := hhas
      have hrp : (sigma (root x)).val = F.residue i % p := (hfirst x).symm.trans (hx.of_dvd hpi)
      exact False.elim (hcollision (root x) i j (u i) hui hm_i hm_j hrp)
    · have hh : label j = F.modulus i := by simpa only [newMod,if_pos hpj,if_neg hpi] using heq.symm
      have haj : a j = 1 := by
        have hap := hapos j hpj
        by_contra hne
        have hdeep : 1 ≤ a j-1 := by omega
        have hd : p ∣ label j := dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_right (by simpa only [pow_one] using pow_dvd_pow p hdeep) q) (u j)
        exact hpi (hh ▸ hd)
      have huj : Nat.Coprime (u j) (p*q) := (hpu j).symm.mul_right
        (hq.coprime_iff_not_dvd.mpr (fun hd => (active_qfree j hj hpj)
          (hd.trans (by rw [hmod j]; exact dvd_mul_left _ _)))).symm
      have hm_j : F.modulus j = p*u j := by simpa only [haj,pow_one] using hmod j
      have hm_i : F.modulus i = q*u j := by
        simpa only [label,haj,Nat.sub_self,pow_zero,mul_one] using hh.symm
      have hhas : Has j := hj.resolve_left (fun hn => hn hpj)
      obtain ⟨x,hx⟩ := hhas
      have hrp : (sigma (root x)).val = F.residue j % p := (hfirst x).symm.trans (hx.of_dvd hpj)
      exact False.elim (hcollision (root x) j i (u j) huj hm_j hm_i hrp)
    · exact F.modulus_injective (by simpa only [newMod,if_neg hpi,if_neg hpj] using heq)
  have hdonorInactive : ¬active donor := by
    rintro (hno | ⟨x,hx⟩)
    · exact hno (by rw [hdonor])
    · exact hdonorMiss x hx
  let Active := {i : Fin n // active i}
  let N := Fintype.card Active
  let enum : Fin N ≃ Active := (Fintype.equivFin Active).symm
  let G : OddDistinctCoveringSystem N := {
    modulus := fun i => newMod (enum i).val
    residue := fun i => newRes (enum i).val
    covers := by
      intro x
      obtain ⟨i,hi,hx⟩ := hnewcover x
      exact ⟨enum.symm ⟨i,hi⟩,by simpa only [Equiv.apply_symm_apply] using hx⟩
    modulus_one_lt := by
      intro i
      dsimp only [newMod]
      split_ifs
      · exact label_gt _
      · exact F.modulus_one_lt _
    modulus_odd := by
      intro i
      dsimp only [newMod]
      split_ifs
      · exact label_odd _
      · exact F.modulus_odd _
    modulus_injective := by
      intro i j heq
      apply enum.injective
      apply Subtype.ext
      exact hnewinj _ _ (enum i).property (enum j).property heq }
  exact ⟨N,G,by simpa only [N,Active,Fintype.card_fin] using
    Fintype.card_subtype_lt hdonorInactive⟩

end Erdos7.OddDistinctCoveringSystem

namespace Erdos7.OddDistinctCoveringSystem

/-- Fewer forbidden incidences than available roots cannot block an injection,
provided that the number of requests does not exceed the number of roots. -/
theorem exists_injective_avoiding_of_forbidden_sum_lt
    {ι α : Type*} [Fintype ι]
    (R : Finset α) (F : ι → Finset α)
    (hsize : Fintype.card ι ≤ R.card)
    (hbudget : (∑ i, (F i).card) < R.card) :
    ∃ f : ι → α, Function.Injective f ∧
      ∀ i, f i ∈ R ∧ f i ∉ F i := by
  classical
  let allowed : ι → Finset α := fun i => R \ F i
  have hall : ∀ S : Finset ι, S.card ≤ (S.biUnion allowed).card := by
    intro S
    by_contra hfail
    have hsmall : (S.biUnion allowed).card < S.card := by omega
    let N := S.biUnion allowed
    have hNR : N ⊆ R := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_sdiff.mp hxi).1
    have hSsize : S.card ≤ R.card :=
      (Finset.card_le_card (Finset.subset_univ S)).trans (by simpa using hsize)
    have hcard : (R \ N).card + N.card = R.card :=
      Finset.card_sdiff_add_card_eq_card hNR
    have hNsmall : N.card < S.card := hsmall
    have hmissing : 0 < (R \ N).card := by omega
    have hrectangle : R.card ≤ S.card * (R \ N).card := by
      calc
        R.card = N.card + (R \ N).card := by omega
        _ ≤ N.card * (R \ N).card + (R \ N).card :=
          Nat.add_le_add_right (Nat.le_mul_of_pos_right N.card hmissing) _
        _ = (N.card + 1) * (R \ N).card := by rw [Nat.add_mul, one_mul]
        _ ≤ S.card * (R \ N).card :=
          Nat.mul_le_mul_right _ (by omega)
    have hforbidden : ∀ i ∈ S, R \ N ⊆ F i := by
      intro i hi x hx
      obtain ⟨hxR, hxN⟩ := Finset.mem_sdiff.mp hx
      by_contra hxF
      exact hxN (Finset.mem_biUnion.mpr
        ⟨i, hi, Finset.mem_sdiff.mpr ⟨hxR, hxF⟩⟩)
    have hcount : S.card * (R \ N).card ≤ ∑ i, (F i).card := by
      calc
        S.card * (R \ N).card = ∑ i ∈ S, (R \ N).card := by simp
        _ ≤ ∑ i ∈ S, (F i).card :=
          Finset.sum_le_sum (fun i hi => Finset.card_le_card (hforbidden i hi))
        _ ≤ ∑ i, (F i).card := Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    exact (not_le_of_gt hbudget) (hrectangle.trans hcount)
  obtain ⟨f, hinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' allowed).mp hall
  exact ⟨f, hinj, fun i => Finset.mem_sdiff.mp (hf i)⟩

end Erdos7.OddDistinctCoveringSystem

namespace Erdos7.OddDistinctCoveringSystem

/-- A globally count-minimal odd distinct whole cover with actual prime labels
`p > q` needs at least `p - q + 2` labels divisible by `q`. -/
theorem prime_bearing_count_lower
    {n p q : ℕ} (F : OddDistinctCoveringSystem n)
    (countMin : ∀ {N : ℕ}, OddDistinctCoveringSystem N → n ≤ N)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hqp : q < p)
    (donor guard : Fin n)
    (hdonor : F.modulus donor = p) (hguard : F.modulus guard = q) :
    p-q+2 ≤ (Finset.univ.filter fun i => q ∣ F.modulus i).card := by
  classical
  let S := Finset.univ.filter fun i => q ∣ F.modulus i
  let C := S.filter fun i => ¬p ∣ F.modulus i
  let M := S.filter fun i => p ∣ F.modulus i
  let B := {b : Fin q // b.val ≠ F.residue guard % q}
  let pRoot : Fin n → Fin p := fun i => ⟨F.residue i % p, Nat.mod_lt _ hp.pos⟩
  let qRoot : Fin n → Fin q := fun i => ⟨F.residue i % q, Nat.mod_lt _ hq.pos⟩
  let mate : Fin n → Fin n := fun j =>
    if h : ∃ i, F.modulus i = p*(F.modulus j/q) then h.choose else donor
  let T := C.image fun j => pRoot (mate j)
  let R := (Finset.univ : Finset (Fin p)) \ T
  let fiber : Fin q → Finset (Fin n) := fun b => M.filter fun i => qRoot i = b
  let forbidden : B → Finset (Fin p) := fun b => (fiber b.val).image pRoot
  have hpq : p ≠ q := Ne.symm (Nat.ne_of_lt hqp)
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hsplit : M.card + C.card = S.card :=
    Finset.card_filter_add_card_filter_not (s := S) (fun i => p ∣ F.modulus i)
  have hT : T.card ≤ C.card := Finset.card_image_le
  have hR : R.card + T.card = p := by
    simpa only [R,Finset.card_univ,Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  have hforbidden : (∑ b, (forbidden b).card) ≤ M.card := by
    calc
      (∑ b, (forbidden b).card) ≤ ∑ b : B, (fiber b.val).card :=
        Finset.sum_le_sum (fun b _ => Finset.card_image_le)
      _ ≤ ∑ b : Fin q, (fiber b).card := by
        have h := Fintype.sum_subtype_add_sum_subtype
          (fun b : Fin q => b.val ≠ F.residue guard % q) (fun b => (fiber b).card)
        change (∑ b : B, (fiber b.val).card) ≤ _
        exact Nat.le.intro h
      _ = M.card := by
        simpa only [fiber,Finset.mem_univ,Finset.filter_true] using
          Finset.sum_card_fiberwise_eq_card_filter M Finset.univ qRoot
  have hB : Fintype.card B < q := by
    simpa only [B,Fintype.card_fin] using
      (Fintype.card_subtype_lt
        (x := (⟨F.residue guard % q,Nat.mod_lt _ hq.pos⟩ : Fin q))
        (show ¬((F.residue guard % q) ≠ F.residue guard % q) from not_not.mpr rfl))
  by_contra hfail
  have hS : S.card ≤ p-q+1 := by change ¬p-q+2 ≤ S.card at hfail; omega
  have hSmall : S.card < p := by have := hq.two_le; omega
  have hsize : Fintype.card B ≤ R.card := by omega
  have hbudget : (∑ b, (forbidden b).card) < R.card := by omega
  obtain ⟨sigma,hinj,havoid⟩ :=
    exists_injective_avoiding_of_forbidden_sum_lt R forbidden hsize hbudget
  have hmixed : ∀ (b : B) (i : Fin n),
      p ∣ F.modulus i → q ∣ F.modulus i → F.residue i % q = b.val.val →
      (sigma b).val ≠ F.residue i % p := by
    intro b i hpi hqi hrq heq
    have hiM : i ∈ M := by
      simp only [M,S,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hqi,hpi⟩
    have hifiber : i ∈ fiber b.val :=
      Finset.mem_filter.mpr ⟨hiM,Fin.ext hrq⟩
    have hmem : sigma b ∈ forbidden b := by
      exact Finset.mem_image.mpr ⟨i,hifiber,(Fin.ext heq).symm⟩
    exact (havoid b).2 hmem
  have hcollision : ∀ (b : B) (i j : Fin n) (u : ℕ),
      Nat.Coprime u (p*q) → F.modulus i = p*u → F.modulus j = q*u →
      (sigma b).val ≠ F.residue i % p := by
    intro b i j u hu hi hj heq
    have hpu : ¬p ∣ u :=
      hp.coprime_iff_not_dvd.mp (hu.coprime_dvd_right (dvd_mul_right p q)).symm
    have hpj : ¬p ∣ F.modulus j := by
      intro hd
      rw [hj] at hd
      exact hpu (hcop.dvd_of_dvd_mul_left hd)
    have hqj : q ∣ F.modulus j := by rw [hj]; exact dvd_mul_right q u
    have hjC : j ∈ C := by
      simp only [C,S,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hqj,hpj⟩
    have hquot : F.modulus j/q = u := by rw [hj,Nat.mul_div_cancel_left u hq.pos]
    have hmateExists : ∃ a, F.modulus a = p*(F.modulus j/q) := by
      exact ⟨i,by rw [hquot,hi]⟩
    have hmate : F.modulus (mate j) = p*(F.modulus j/q) := by
      simp only [mate,dif_pos hmateExists]
      exact hmateExists.choose_spec
    have hmati : mate j = i := by
      apply F.modulus_injective
      rw [hmate,hquot,hi]
    have hmem : sigma b ∈ T := by
      apply Finset.mem_image.mpr
      exact ⟨j,hjC,by rw [hmati]; exact (Fin.ext heq).symm⟩
    exact (Finset.mem_sdiff.mp (havoid b).1).2 hmem
  obtain ⟨N,G,hN⟩ := prime_root_compression F hp hq hpq donor guard hdonor hguard
    sigma hinj hmixed hcollision
  exact (not_lt_of_ge (countMin G)) hN

end Erdos7.OddDistinctCoveringSystem
