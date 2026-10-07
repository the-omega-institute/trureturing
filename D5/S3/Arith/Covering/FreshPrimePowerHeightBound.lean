/- GID: D5/S3/Arith/Covering/FreshPrimePowerHeightBound
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/FreshPrimePowerHeightBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fresh prime-power repairs bound pure heights through one actual private source. -/

import D5.S3.Arith.Covering.ConcentratedPrimeSingleton
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos7.OddDistinctCoveringSystem

/- A pure-power instance of the classical private suffix supplier argument.
All digits are changed at one actual private source and its complete period. -/
private theorem pure_power_private_suffix_fan
    {n r a H : ℕ} (F : OddDistinctCoveringSystem n)
    (hr : Nat.Prime r) (haH : a < H)
    (top : Fin n) (htop : F.modulus top = r ^ H)
    (x : ℕ) (hx : Private F top x) :
    ∃ packet : (Unit ⊕ (Fin (H - a) × Fin (r - 1))) ↪ Fin n,
      (∀ i, r ^ (a + 1) ∣ F.modulus (packet i)) ∧
      (∀ i, F.residue (packet i) ≡ x [MOD r ^ a]) := by
  classical
  obtain ⟨G, M, hrMnot, hQ⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd F.commonModulus_ne_zero r hr.ne_one
  have hrM : Nat.Coprime r M := hr.coprime_iff_not_dvd.mpr hrMnot
  have hperiod (i : Fin n) : F.modulus i ∣ r ^ G * M := by
    rw [← hQ]
    exact F.modulus_dvd_commonModulus i
  have hHG : H ≤ G := by
    have hd : r ^ H ∣ r ^ G * M := by simpa only [htop] using hperiod top
    have hd' : r ^ H ∣ r ^ G := (hrM.pow_left H).dvd_of_dvd_mul_right hd
    exact (Nat.pow_dvd_pow_iff_le_right hr.one_lt).mp hd'
  have hdecomp (i : Fin n) : ∃ e v : ℕ,
      e ≤ G ∧ v ∣ M ∧ F.modulus i = r ^ e * v := by
    obtain ⟨u, v, hu, hv, hi⟩ := exists_dvd_and_dvd_of_dvd_mul (hperiod i)
    obtain ⟨e, he, hue⟩ := (Nat.dvd_prime_pow hr).mp hu
    exact ⟨e, v, he, hv, by simpa only [hue] using hi⟩
  choose e v he hv hlabel using hdecomp
  let Digit := Fin (H - a) × Fin (r - 1)
  let depth (z : Digit) : ℕ := a + z.1.val
  have hdepth (z : Digit) : a ≤ depth z ∧ depth z < H := by
    have := z.1.isLt
    dsimp only [depth]
    omega
  have hdigit (z : Digit) : 0 < z.2.val + 1 ∧ z.2.val + 1 < r := by
    have := z.2.isLt
    have := hr.two_le
    omega
  let y (z : Digit) : ℕ :=
    (Nat.chineseRemainder (hrM.pow_left G) (x + r ^ depth z * (z.2.val + 1)) x).val
  have hyR (z : Digit) : y z ≡ x + r ^ depth z * (z.2.val + 1) [MOD r ^ G] :=
    (Nat.chineseRemainder (hrM.pow_left G) (x + r ^ depth z * (z.2.val + 1)) x).property.1
  have hyM (z : Digit) : y z ≡ x [MOD M] :=
    (Nat.chineseRemainder (hrM.pow_left G) (x + r ^ depth z * (z.2.val + 1)) x).property.2
  have hylow (z : Digit) : y z ≡ x [MOD r ^ depth z] := by
    apply ((hyR z).of_dvd (pow_dvd_pow r (by have := hdepth z; omega))).trans
    simp [Nat.ModEq]
  have hyhigh (z : Digit) : ¬y z ≡ x [MOD r ^ (depth z + 1)] := by
    intro hbad
    have hshift : x + r ^ depth z * (z.2.val + 1) ≡ x [MOD r ^ (depth z + 1)] :=
      ((hyR z).of_dvd (pow_dvd_pow r (by have := hdepth z; omega))).symm.trans hbad
    have hprod : r ^ depth z * (z.2.val + 1) ≡ r ^ depth z * 0
        [MOD r ^ depth z * r] := by
      simpa only [pow_succ, mul_zero, add_zero] using
        (Nat.ModEq.refl x).add_left_cancel hshift
    have ht : z.2.val + 1 ≡ 0 [MOD r] :=
      hprod.mul_left_cancel' (pow_ne_zero _ hr.ne_zero)
    have ht' : z.2.val + 1 = 0 := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hdigit z).2, Nat.zero_mod] using ht
    omega
  choose supplier hsupplier using (fun z : Digit => F.covers (y z))
  have hnotop (z : Digit) : supplier z ≠ top := by
    intro heq
    have hytop : y z ≡ F.residue top [MOD r ^ H] := by
      simpa only [heq, htop] using hsupplier z
    have hxtop : x ≡ F.residue top [MOD r ^ H] := by
      simpa only [htop] using hx.1
    exact hyhigh z ((hytop.trans hxtop.symm).of_dvd
      (pow_dvd_pow r (by have := hdepth z; omega)))
  have hsupplierHigh (z : Digit) : depth z < e (supplier z) := by
    by_contra hle
    have hle' : e (supplier z) ≤ depth z := by omega
    have hyr : y z ≡ x [MOD r ^ e (supplier z)] :=
      (hylow z).of_dvd (pow_dvd_pow r hle')
    have hyv : y z ≡ x [MOD v (supplier z)] := (hyM z).of_dvd (hv (supplier z))
    have hco := (hrM.coprime_dvd_right (hv (supplier z))).pow_left (e (supplier z))
    have hym : y z ≡ x [MOD F.modulus (supplier z)] := by
      rw [hlabel]
      exact (Nat.modEq_and_modEq_iff_modEq_mul hco).mp ⟨hyr, hyv⟩
    exact hx.2 (supplier z) (hnotop z) (hym.symm.trans (hsupplier z))
  have hsupplierDvd (z : Digit) : r ^ (depth z + 1) ∣ F.modulus (supplier z) := by
    rw [hlabel]
    exact (pow_dvd_pow r (hsupplierHigh z)).trans (dvd_mul_right _ _)
  have hsupInjective : Function.Injective supplier := by
    intro z w heq
    have hsameZ : y z ≡ y w [MOD r ^ (depth z + 1)] := by
      have hw : y w ≡ F.residue (supplier z) [MOD F.modulus (supplier z)] := by
        simpa only [heq] using hsupplier w
      exact ((hsupplier z).trans hw.symm).of_dvd (hsupplierDvd z)
    have hsameW : y w ≡ y z [MOD r ^ (depth w + 1)] := by
      have hz : y z ≡ F.residue (supplier w) [MOD F.modulus (supplier w)] := by
        simpa only [heq] using hsupplier z
      exact ((hsupplier w).trans hz.symm).of_dvd (hsupplierDvd w)
    have hd : depth z = depth w := by
      apply Nat.le_antisymm
      · by_contra hlt
        have hwz : depth w + 1 ≤ depth z := by omega
        exact hyhigh w (hsameW.trans ((hylow z).of_dvd (pow_dvd_pow r hwz)))
      · by_contra hlt
        have hzw : depth z + 1 ≤ depth w := by omega
        exact hyhigh z (hsameZ.trans ((hylow w).of_dvd (pow_dvd_pow r hzw)))
    have hzR := (hyR z).of_dvd (pow_dvd_pow r
      (by have := hdepth z; omega : depth z + 1 ≤ G))
    have hwR := (hyR w).of_dvd (pow_dvd_pow r
      (by have := hdepth z; omega : depth z + 1 ≤ G))
    have hshift : x + r ^ depth z * (z.2.val + 1) ≡
        x + r ^ depth z * (w.2.val + 1) [MOD r ^ (depth z + 1)] := by
      simpa only [← hd] using hzR.symm.trans (hsameZ.trans hwR)
    have hprod : r ^ depth z * (z.2.val + 1) ≡
        r ^ depth z * (w.2.val + 1) [MOD r ^ depth z * r] := by
      simpa only [pow_succ] using (Nat.ModEq.refl x).add_left_cancel hshift
    have ht := hprod.mul_left_cancel' (pow_ne_zero _ hr.ne_zero)
    have ht' : z.2.val + 1 = w.2.val + 1 := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hdigit z).2,
        Nat.mod_eq_of_lt (hdigit w).2] using ht
    apply Prod.ext
    · apply Fin.ext
      dsimp only [depth] at hd
      omega
    · apply Fin.ext
      omega
  let packet : Unit ⊕ Digit → Fin n := Sum.elim (fun _ => top) supplier
  have hpacketInj : Function.Injective packet := by
    rintro (u | z) (v | w) heq
    · exact congrArg Sum.inl (Subsingleton.elim u v)
    · exact False.elim (hnotop w heq.symm)
    · exact False.elim (hnotop z heq)
    · exact congrArg Sum.inr (hsupInjective heq)
  refine ⟨⟨packet, hpacketInj⟩, ?_, ?_⟩
  · rintro (u | z)
    · change r ^ (a + 1) ∣ F.modulus top
      rw [htop]
      exact pow_dvd_pow r haH
    · exact (pow_dvd_pow r (by have := hdepth z; omega)).trans (hsupplierDvd z)
  · rintro (u | z)
    · exact hx.1.symm.of_dvd (by rw [htop]; exact pow_dvd_pow r haH.le)
    · have hd : r ^ a ∣ F.modulus (supplier z) :=
        (pow_dvd_pow r (by have := hdepth z; omega)).trans (hsupplierDvd z)
      exact ((hsupplier z).of_dvd hd).symm.trans
        ((hylow z).of_dvd (pow_dvd_pow r (hdepth z).1))

/- Existing private-repair mathematics, formalized through the actual suffix
packet and a whole-cover construction. No repair coverage is assumed. -/
theorem fresh_prime_power_height_bound
    {n p r a H : ℕ} (F : OddDistinctCoveringSystem n)
    (countMin : ∀ {N : ℕ}, OddDistinctCoveringSystem N → n ≤ N)
    (hp : Nat.Prime p) (hr : Nat.Prime r) (hne : p ≠ r)
    (ownerP ownerA ownerH : Fin n)
    (hP : F.modulus ownerP = p)
    (hA : F.modulus ownerA = r ^ a)
    (hH : F.modulus ownerH = r ^ H)
    (x : ℕ) (hx : Private F ownerH x)
    (height : Fin (p - 1) → ℕ) (hheightInj : Function.Injective height)
    (hheightPos : ∀ j, 1 ≤ height j) (hheightLe : ∀ j, height j ≤ a)
    (hfresh : ∀ j i, F.modulus i ≠ p * r ^ height j) :
    H ≤ a + (p - 3) / (r - 1) := by
  classical
  have hpOdd : Odd p := hP ▸ F.modulus_odd ownerP
  have haPos : 0 < a := by
    by_contra hnot
    have ha0 : a = 0 := by omega
    have hunit := F.modulus_one_lt ownerA
    rw [hA, ha0, pow_zero] at hunit
    omega
  have hrOdd : Odd r := (F.modulus_odd ownerA).of_dvd_nat (by
    rw [hA]
    exact dvd_pow_self r (Nat.ne_of_gt haPos))
  by_contra hbound
  have hupper : a + (p - 3) / (r - 1) < H := Nat.lt_of_not_ge hbound
  have haH : a < H := (Nat.le_add_right a ((p - 3) / (r - 1))).trans_lt hupper
  have hp3 : 3 ≤ p := by
    obtain ⟨k, hk⟩ := hpOdd
    have := hp.two_le
    omega
  have hr1 : 0 < r - 1 := by have := hr.two_le; omega
  have hdelta : (p - 3) / (r - 1) < H - a := by omega
  have hprod : p - 3 < (H - a) * (r - 1) :=
    (Nat.div_lt_iff_lt_mul hr1).mp hdelta
  have hsize : p - 1 < 1 + (H - a) * (r - 1) := by
    obtain ⟨u, hu⟩ := hpOdd
    obtain ⟨v, hv⟩ := hrOdd
    have hrpred : r - 1 = v + v := by omega
    have heven : (H - a) * (r - 1) = (H - a) * v + (H - a) * v := by
      rw [hrpred, Nat.mul_add]
    omega
  obtain ⟨packet, hpacketDvd, hpacketPhase⟩ :=
    pure_power_private_suffix_fan F hr haH ownerH hH x hx
  let I := Unit ⊕ (Fin (H - a) × Fin (r - 1))
  have hparentNotRemoved : ownerA ∉ Set.range (packet : I → Fin n) := by
    rintro ⟨i, hi⟩
    have hd := hpacketDvd i
    rw [hi, hA] at hd
    have := (Nat.pow_dvd_pow_iff_le_right hr.one_lt).mp hd
    omega
  have hpr : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr hne
  have hownerNe : ownerP ≠ ownerA := by
    intro heq
    have hprpow : p = r ^ a := hP.symm.trans ((congrArg F.modulus heq).trans hA)
    have hdiv : p ∣ r := hp.dvd_of_dvd_pow (by rw [← hprpow])
    rcases (Nat.dvd_prime hr).mp hdiv with hbad | hbad
    · exact hp.ne_one hbad
    · exact hne hbad
  let pOwnerRoot : Fin p := ⟨F.residue ownerP % p, Nat.mod_lt _ hp.pos⟩
  let Roots := {b : Fin p // b ≠ pOwnerRoot}
  have hRoots : Fintype.card Roots = p - 1 := by
    simp [Roots, Fintype.card_subtype_compl]
  let rootEnum : Roots ≃ Fin (p - 1) := (Fintype.equivFin Roots).trans (finCongr hRoots)
  let Rem := {i : Fin n // i ∉ Set.range (packet : I → Fin n)}
  let newMod : Roots ⊕ Rem → ℕ := Sum.elim
    (fun b => p * r ^ height (rootEnum b))
    (fun i => F.modulus i.val)
  let newRes : Roots ⊕ Rem → ℕ := Sum.elim
    (fun b => (Nat.chineseRemainder (hpr.pow_right (height (rootEnum b)))
      b.val.val (F.residue ownerA)).val)
    (fun i => if i.val = ownerA then x else F.residue i.val)
  have hnewInj : Function.Injective newMod := by
    rintro (b | i) (c | j) heq
    · apply congrArg Sum.inl
      apply rootEnum.injective
      apply hheightInj
      apply Nat.pow_right_injective hr.two_le
      exact Nat.eq_of_mul_eq_mul_left hp.pos heq
    · exact False.elim (hfresh (rootEnum b) j.val heq.symm)
    · exact False.elim (hfresh (rootEnum c) i.val heq)
    · exact congrArg Sum.inr (Subtype.ext (F.modulus_injective heq))
  have hnewCover (z : ℕ) : ∃ i, z ≡ newRes i [MOD newMod i] := by
    by_cases hz : Private F ownerA z
    · let b : Roots := ⟨⟨z % p, Nat.mod_lt _ hp.pos⟩, by
        intro heq
        apply hz.2 ownerP hownerNe
        rw [hP]
        exact congrArg Fin.val heq⟩
      refine ⟨Sum.inl b, ?_⟩
      apply Nat.chineseRemainder_modEq_unique (hpr.pow_right (height (rootEnum b)))
      · change z % p = (z % p) % p
        exact (Nat.mod_mod _ _).symm
      · exact hz.1.of_dvd (by rw [hA]; exact pow_dvd_pow r (hheightLe _))
    · obtain ⟨k, hka, hzk⟩ : ∃ k, k ≠ ownerA ∧
          z ≡ F.residue k [MOD F.modulus k] := by
        by_cases hza : z ≡ F.residue ownerA [MOD F.modulus ownerA]
        · by_contra hother
          exact hz ⟨hza, fun k hka hzk => hother ⟨k, hka, hzk⟩⟩
        · obtain ⟨k, hzk⟩ := F.covers z
          exact ⟨k, fun heq => hza (heq ▸ hzk), hzk⟩
      by_cases hk : k ∈ Set.range (packet : I → Fin n)
      · obtain ⟨i, rfl⟩ := hk
        refine ⟨Sum.inr ⟨ownerA, hparentNotRemoved⟩, ?_⟩
        have hzparent : z ≡ x [MOD r ^ a] :=
          (hzk.of_dvd ((pow_dvd_pow r (by omega : a ≤ a + 1)).trans
            (hpacketDvd i))).trans (hpacketPhase i)
        simpa only [newMod, newRes, Sum.elim_inr, if_pos rfl, if_true, hA] using hzparent
      · exact ⟨Sum.inr ⟨k, hk⟩, by
          simpa only [newMod, newRes, Sum.elim_inr, if_neg hka] using hzk⟩
  let eOld : I ⊕ Rem ≃ Fin n :=
    (Equiv.sumCongr (Equiv.ofInjective packet packet.injective) (Equiv.refl Rem)).trans
      (Equiv.sumCompl (fun i => i ∈ Set.range (packet : I → Fin n)))
  have hOldCard : Fintype.card I + Fintype.card Rem = n := by
    simpa using Fintype.card_congr eOld
  have hICard : Fintype.card I = 1 + (H - a) * (r - 1) := by
    simp [I]
  let N := Fintype.card (Roots ⊕ Rem)
  let enum : Fin N ≃ Roots ⊕ Rem := (Fintype.equivFin _).symm
  let G : OddDistinctCoveringSystem N := {
    modulus := fun i => newMod (enum i)
    residue := fun i => newRes (enum i)
    covers := by
      intro z
      obtain ⟨i, hi⟩ := hnewCover z
      exact ⟨enum.symm i, by simpa only [Equiv.apply_symm_apply] using hi⟩
    modulus_one_lt := by
      intro i
      cases enum i with
      | inl b =>
        have hpow : 1 < r ^ height (rootEnum b) :=
          one_lt_pow₀ hr.one_lt (by have := hheightPos (rootEnum b); omega)
        have hpPos := hp.pos
        change 1 < p * r ^ height (rootEnum b)
        nlinarith
      | inr i => exact F.modulus_one_lt i.val
    modulus_odd := by
      intro i
      cases enum i with
      | inl b => exact hpOdd.mul hrOdd.pow
      | inr i => exact F.modulus_odd i.val
    modulus_injective := hnewInj.comp enum.injective }
  have hNlt : N < n := by
    change Fintype.card (Roots ⊕ Rem) < n
    rw [Fintype.card_sum, hRoots]
    omega
  exact (Nat.not_lt_of_ge (countMin G)) hNlt


end Erdos7.OddDistinctCoveringSystem
