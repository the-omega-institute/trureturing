/- GID: D5/S3/Arith/Congruence/ConditionalComparison/PrimeAbsorption
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/ConditionalComparison/PrimeAbsorption
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One-source height-coded prime absorption strictly reduces a whole odd cover. -/

import D5.S3.Arith.Congruence.ConditionalComparison.ArithmeticCoordinates
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace Erdos7.OddDistinctCoveringSystem

/-- A sufficiently large pure prime can be absorbed into fresh heights of a smaller prime,
with one output progression for each nonempty original inverse image. -/
theorem prime_absorption {L p q H G M : ℕ} (S : OddDistinctCoveringSystem L)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hpo : Odd p) (_hqo : Odd q) (_hH : 0 < H) (hG : 0 < G)
    (hM : Nat.Coprime M (p * q))
    (hperiod : S.commonModulus = p ^ H * q ^ G * M)
    (hpure : ∃ j, S.modulus j = q) (hsize : p ^ (2 * H + 1) < q) :
    ∃ L' < L, Nonempty (OddDistinctCoveringSystem L') := by
  classical
  have codeExists {R B q r : ℕ} (hR : 0 < R) (hRq : R < q)
      (hB : 0 < B) (hBq : B ≤ q) (N : ℕ) :
      ∃ f : ℕ → ℕ,
        (∀ x, f x < q ^ (N + 1)) ∧
        (∀ x, f x % q ≠ r) ∧
        (∀ e ≤ N, ∀ x y,
          (f x ≡ f y [MOD q ^ (e + 1)]) ↔
            (x ≡ y [MOD R * B ^ e])) := by
    have hq : 0 < q := lt_trans hR hRq
    have splitMod : ∀ {b n x y : ℕ}, 0 < b →
        (x ≡ y [MOD b * n] ↔ x % b = y % b ∧ x / b ≡ y / b [MOD n]) := by
      intro b n x y hb
      constructor
      · intro h
        have hm : x % b = y % b := h.of_dvd (dvd_mul_right b n)
        refine ⟨hm, Nat.ModEq.mul_left_cancel' (Nat.ne_of_gt hb) ?_⟩
        have hc : x % b ≡ y % b [MOD b * n] := congrArg (fun z => z % (b * n)) hm
        apply hc.add_left_cancel
        simpa only [Nat.mod_add_div] using h
      · rintro ⟨hm, hd⟩
        have hc : x % b ≡ y % b [MOD b * n] := congrArg (fun z => z % (b * n)) hm
        simpa only [Nat.mod_add_div] using hc.add (hd.mul_left' b)
    induction N with
    | zero =>
        let skip : ℕ → ℕ := fun t => if t < r then t else t + 1
        have hb : ∀ x, skip (x % R) < q := by
          intro x
          have hx := Nat.mod_lt x hR
          dsimp [skip]
          split_ifs <;> omega
        have hav : ∀ x, skip (x % R) ≠ r := by
          intro x
          dsimp [skip]
          split_ifs <;> omega
        have hinj : ∀ u v, skip u = skip v ↔ u = v := by
          intro u v
          dsimp [skip]
          split_ifs <;> omega
        refine ⟨fun x => skip (x % R), ?_, ?_, ?_⟩
        · simpa using hb
        · intro x
          simpa only [Nat.mod_eq_of_lt (hb x)] using hav x
        · intro e he x y
          have he0 : e = 0 := by omega
          subst e
          simp only [zero_add, pow_one, pow_zero, mul_one, Nat.ModEq,
            Nat.mod_eq_of_lt (hb x), Nat.mod_eq_of_lt (hb y)]
          exact hinj _ _
    | succ n ih =>
        obtain ⟨f, hfb, hfa, hfp⟩ := ih
        let c := R * B ^ n
        have hc : 0 < c := mul_pos hR (pow_pos hB _)
        let Q := q ^ (n + 1)
        have hQ : 0 < Q := pow_pos hq _
        let g : ℕ → ℕ := fun x => f x + Q * (x / c % B)
        have hgb : ∀ x, g x < q ^ (n + 1 + 1) := by
          intro x
          have hd := Nat.mod_lt (x / c) hB
          have hf := hfb x
          change f x + Q * (x / c % B) < q ^ (n + 1) * q
          change f x < Q at hf
          change f x + Q * (x / c % B) < Q * q
          nlinarith
        have hgf : ∀ e ≤ n, ∀ x, g x ≡ f x [MOD q ^ (e + 1)] := by
          intro e he x
          have hd : q ^ (e + 1) ∣ Q := pow_dvd_pow q (by omega)
          change f x + Q * (x / c % B) ≡ f x [MOD q ^ (e + 1)]
          exact Nat.ModEq.add_right_cancel' 0 (by
            simpa using (Nat.ModEq.refl (f x)).add
              (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hd _)))
        refine ⟨g, hgb, ?_, ?_⟩
        · intro x
          have h := hgf 0 (by omega) x
          simp only [zero_add, pow_one, Nat.ModEq] at h
          rw [h]
          exact hfa x
        · intro e he x y
          by_cases hen : e ≤ n
          · exact ⟨fun h => (hfp e hen x y).mp
              ((hgf e hen x).symm.trans (h.trans (hgf e hen y))),
              fun h => (hgf e hen x).trans
                (((hfp e hen x y).mpr h).trans (hgf e hen y).symm)⟩
          · have heq : e = n + 1 := by omega
            subst e
            have hgEq : (g x ≡ g y [MOD q ^ (n + 1 + 1)]) ↔ g x = g y :=
              ⟨fun h => h.eq_of_lt_of_lt (hgb x) (hgb y), fun h => h ▸ Nat.ModEq.refl _⟩
            rw [hgEq]
            have hcB : R * B ^ (n + 1) = c * B := by
              simp only [c, pow_succ, mul_assoc]
            rw [hcB, splitMod hc]
            constructor
            · intro h
              have hf : f x = f y := by
                have hh := congrArg (fun t => t % Q) h
                simpa only [g, Nat.add_mul_mod_self_left,
                  Nat.mod_eq_of_lt (show f x < Q from hfb x),
                  Nat.mod_eq_of_lt (show f y < Q from hfb y)] using hh
              have hx : x % c = y % c := (hfp n le_rfl x y).mp
                (hf ▸ Nat.ModEq.refl _)
              refine ⟨hx, ?_⟩
              have hh : Q * (x / c % B) = Q * (y / c % B) := by
                dsimp [g] at h
                rw [hf] at h
                exact Nat.add_left_cancel h
              exact Nat.eq_of_mul_eq_mul_left hQ hh
            · rintro ⟨hx, hd⟩
              have hf : f x = f y :=
                ((hfp n le_rfl x y).mpr hx).eq_of_lt_of_lt (hfb x) (hfb y)
              change f x + Q * (x / c % B) = f y + Q * (y / c % B)
              rw [hf, hd]
  -- A replacement height remembers both original prime exponents.
  have labels {p H a a' e e' m m' : ℕ}
      (hp : Nat.Prime p) (ha : a ≤ H) (ha' : a' ≤ H)
      (hm : ¬ p ∣ m) (hm' : ¬ p ∣ m')
      (heq : p ^ ((H + 1) * e + a) * m = p ^ ((H + 1) * e' + a') * m') :
      a = a' ∧ e = e' ∧ m = m' := by
    have hm0 : m ≠ 0 := by intro h; subst m; exact hm (dvd_zero p)
    have hm'0 : m' ≠ 0 := by intro h; subst m'; exact hm' (dvd_zero p)
    have ht := congrArg (fun n : ℕ => n.factorization p) heq
    simp only [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0,
      Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm'0,
      Finsupp.add_apply, Nat.factorization_pow_self hp,
      Nat.factorization_eq_zero_of_not_dvd hm,
      Nat.factorization_eq_zero_of_not_dvd hm', Nat.add_zero] at ht
    have haa : a = a' := by
      have hmod := congrArg (fun n : ℕ => n % (H + 1)) ht
      simpa [Nat.add_mod, Nat.mod_eq_of_lt (show a < H + 1 by omega),
        Nat.mod_eq_of_lt (show a' < H + 1 by omega)] using hmod
    have hee : e = e' := by
      rw [haa] at ht
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < H + 1) (Nat.add_right_cancel ht)
    refine ⟨haa, hee, ?_⟩
    rw [haa, hee] at heq
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) heq
  -- Split each original numerical label using prime factorization.
  have decompose {p q H G M d : ℕ}
      (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
      (hM0 : M ≠ 0) (hpM : Nat.Coprime p M) (hqM : Nat.Coprime q M)
      (hd : d ∣ p ^ H * q ^ G * M) :
      ∃ a e m, a ≤ H ∧ e ≤ G ∧ m ∣ M ∧
        ¬p ∣ m ∧ ¬q ∣ m ∧ d = p ^ a * q ^ e * m := by
    have hQ0 : p ^ H * q ^ G * M ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)) hM0
    have hd0 : d ≠ 0 := by
      intro h
      rw [h, zero_dvd_iff] at hd
      exact hQ0 hd
    obtain ⟨a, r, hpr, hdr⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 p hp.ne_one
    have hr0 : r ≠ 0 := by intro h; subst r; exact hpr (dvd_zero p)
    obtain ⟨e, m, hqm, hrm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hr0 q hq.ne_one
    have hdm : d = p ^ a * q ^ e * m := by rw [hdr, hrm, mul_assoc]
    have hpm : ¬ p ∣ m := by
      intro h
      apply hpr
      rw [hrm]
      exact dvd_mul_of_dvd_right h _
    have hm0 : m ≠ 0 := by intro h; subst m; exact hpm (dvd_zero p)
    have hpdq : ¬ p ∣ q := by
      intro h
      exact hpq ((hq.dvd_iff_eq hp.ne_one).mp h).symm
    have hqdp : ¬ q ∣ p := by
      intro h
      exact hpq ((hp.dvd_iff_eq hq.ne_one).mp h)
    have hpdM : ¬ p ∣ M := hp.coprime_iff_not_dvd.mp hpM
    have hqdM : ¬ q ∣ M := hq.coprime_iff_not_dvd.mp hqM
    have hfac := (Nat.factorization_le_iff_dvd hd0 hQ0).mpr hd
    have ha : a ≤ H := by
      have hb := hfac p
      rw [hdm] at hb
      simpa [Nat.factorization_mul, hp.ne_zero, hq.ne_zero, hm0, hM0,
        Nat.factorization_pow, hp.factorization,
        Nat.factorization_eq_zero_of_not_dvd hpdq,
        Nat.factorization_eq_zero_of_not_dvd hpm,
        Nat.factorization_eq_zero_of_not_dvd hpdM] using hb
    have he : e ≤ G := by
      have hb := hfac q
      rw [hdm] at hb
      simpa [Nat.factorization_mul, hp.ne_zero, hq.ne_zero, hm0, hM0,
        Nat.factorization_pow, hq.factorization,
        Nat.factorization_eq_zero_of_not_dvd hqdp,
        Nat.factorization_eq_zero_of_not_dvd hqm,
        Nat.factorization_eq_zero_of_not_dvd hqdM] using hb
    have hmd : m ∣ d := by rw [hdm]; exact dvd_mul_left m _
    have hmQ : m ∣ p ^ H * q ^ G * M := hmd.trans hd
    have hmcop : Nat.Coprime m (p ^ H * q ^ G) :=
      ((hp.coprime_iff_not_dvd.mpr hpm).symm.pow_right H).mul_right
        ((hq.coprime_iff_not_dvd.mpr hqm).symm.pow_right G)
    exact ⟨a, e, m, ha, he, hmcop.dvd_of_dvd_mul_left hmQ, hpm, hqm, hdm⟩
  -- The new numerical labels stay odd and nontrivial.
  have goodness {p q H a e m : ℕ}
      (hp : Nat.Prime p) (hpo : Odd p) (hm : ¬ p ∣ m)
      (hd : 1 < p ^ a * q ^ e * m) (hdo : Odd (p ^ a * q ^ e * m)) :
      1 < p ^ ((H + 1) * e + a) * m ∧ Odd (p ^ ((H + 1) * e + a) * m) := by
    have hm0 : m ≠ 0 := by intro h; subst m; exact hm (dvd_zero p)
    constructor
    · by_cases he : e = 0
      · simpa [he] using hd
      · have hpow : 1 < p ^ ((H + 1) * e + a) :=
          one_lt_pow₀ hp.one_lt (by positivity)
        exact hpow.trans_le (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hm0))
    · exact hpo.pow.mul (hdo.of_dvd_nat (dvd_mul_left m _))
  -- The fixed source avoids the actual pure-prime root.
  obtain ⟨j, hj⟩ := hpure
  have hM0 : M ≠ 0 := by
    intro h
    apply S.commonModulus_ne_zero
    rw [hperiod, h, mul_zero]
  have hpM : Nat.Coprime p M := (Nat.coprime_mul_iff_right.mp hM).1.symm
  have hqM : Nat.Coprime q M := (Nat.coprime_mul_iff_right.mp hM).2.symm
  have hpq' : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr (by
    intro h
    exact hpq ((hq.dvd_iff_eq hp.ne_one).mp h).symm)
  have hbq : p ^ (H + 1) ≤ q :=
    (Nat.pow_le_pow_right hp.one_le (by omega : H + 1 ≤ 2 * H + 1)).trans hsize.le
  obtain ⟨f, hfb, hfa, hfp⟩ := codeExists
    (R := p ^ (2 * H + 1)) (B := p ^ (H + 1)) (q := q)
    (r := S.residue j % q) (pow_pos hp.pos _) hsize
    (pow_pos hp.pos _) hbq (G - 1)
  have code_prefix : ∀ e, 0 < e → e ≤ G → ∀ x y,
      (f x ≡ f y [MOD q ^ e]) ↔ (x ≡ y [MOD p ^ (H + (H + 1) * e)]) := by
    intro e he heG x y
    have he1 : e - 1 + 1 = e := Nat.sub_add_cancel he
    have hexp : 2 * H + 1 + (H + 1) * (e - 1) = H + (H + 1) * e := by
      nth_rw 2 [← he1]
      ring
    have h := hfp (e - 1) (by omega) x y
    simpa only [he1, ← pow_mul, ← pow_add, hexp] using h
  have hcrt : Nat.Coprime (p ^ H * M) (q ^ G) :=
    (hpq'.pow_left H |>.mul_left hqM.symm).pow_right G
  let source : ℕ → ℕ := fun z => Nat.chineseRemainder hcrt z (f z)
  have source_old : ∀ z, source z ≡ z [MOD p ^ H * M] :=
    fun z => (Nat.chineseRemainder hcrt z (f z)).property.1
  have source_code : ∀ z, source z ≡ f z [MOD q ^ G] :=
    fun z => (Nat.chineseRemainder hcrt z (f z)).property.2
  have factors : ∀ i : Fin L, ∃ a e m, a ≤ H ∧ e ≤ G ∧ m ∣ M ∧
      ¬p ∣ m ∧ ¬q ∣ m ∧ S.modulus i = p ^ a * q ^ e * m := by
    intro i
    exact decompose hp hq hpq hM0 hpM hqM (hperiod ▸ S.modulus_dvd_commonModulus i)
  choose a e m ha he hm hpm hqm hfactor using factors
  let outputModulus : Fin L → ℕ := fun i => p ^ ((H + 1) * e i + a i) * m i
  have output_injective : Function.Injective outputModulus := by
    intro i k hik
    obtain ⟨haa, hee, hmm⟩ := labels hp (ha i) (ha k) (hpm i) (hpm k) hik
    apply S.modulus_injective
    rw [hfactor i, hfactor k, haa, hee, hmm]
  have output_good : ∀ i, 1 < outputModulus i ∧ Odd (outputModulus i) := by
    intro i
    apply goodness hp hpo (hpm i)
    · rw [← hfactor i]
      exact S.modulus_one_lt i
    · rw [← hfactor i]
      exact S.modulus_odd i
  let survives : Fin L → Prop := fun i => ∃ z, source z ≡ S.residue i [MOD S.modulus i]
  have missing : ¬ survives j := by
    rintro ⟨z, hz⟩
    have hqG : q ∣ q ^ G := dvd_pow_self q (by omega : G ≠ 0)
    have hqz : f z ≡ S.residue j [MOD q] :=
      ((source_code z).of_dvd hqG).symm.trans (by simpa [hj] using hz)
    exact hfa z hqz
  let Survivor := { i : Fin L // survives i }
  let chosen : Survivor → ℕ := fun i => Classical.choose i.property
  have chosen_source : ∀ i : Survivor,
      source (chosen i) ≡ S.residue i.val [MOD S.modulus i.val] :=
    fun i => Classical.choose_spec i.property
  have exact_fiber : ∀ i : Survivor, ∀ z,
      (source z ≡ S.residue i.val [MOD S.modulus i.val]) ↔
      (z ≡ chosen i [MOD (if e i.val = 0 then p ^ a i.val
        else p ^ (H + (H + 1) * e i.val)) * m i.val]) := by
    intro i z
    let k := i.val
    have hcop : Nat.Coprime (p ^ a k) (q ^ e k * m k) :=
      (hpq'.pow_right _ |>.mul_right (hp.coprime_iff_not_dvd.mpr (hpm k))).pow_left _
    have hmcp : Nat.Coprime (p ^ (H + (H + 1) * e k)) (m k) :=
      (hp.coprime_iff_not_dvd.mpr (hpm k)).pow_left _
    have hsmall : p ^ a k * m k ∣ p ^ H * M :=
      Nat.mul_dvd_mul (pow_dvd_pow p (ha k)) (hm k)
    have hdq : q ^ e k ∣ S.modulus k := by
      rw [hfactor k]
      exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    have hdm : m k ∣ S.modulus k := by
      rw [hfactor k]
      exact dvd_mul_left _ _
    have hqa : q ^ e k ∣ q ^ G := pow_dvd_pow q (he k)
    have hpold : p ^ a k ∣ p ^ H * M :=
      (pow_dvd_pow p (ha k)).trans (dvd_mul_right _ _)
    have hmold : m k ∣ p ^ H * M := (hm k).trans (dvd_mul_left _ _)
    have hcompare : (source z ≡ S.residue k [MOD S.modulus k]) ↔
        (source z ≡ source (chosen i) [MOD S.modulus k]) :=
      ⟨fun h => h.trans (chosen_source i).symm,
        fun h => h.trans (chosen_source i)⟩
    change (source z ≡ S.residue k [MOD S.modulus k]) ↔
      (z ≡ chosen i [MOD (if e k = 0 then p ^ a k
        else p ^ (H + (H + 1) * e k)) * m k])
    rw [hcompare]
    by_cases he0 : e k = 0
    · simp only [he0, if_pos]
      have hdk : S.modulus k = p ^ a k * m k := by simp [hfactor k, he0]
      rw [hdk]
      exact ⟨fun h => ((source_old z).of_dvd hsmall).symm.trans
        (h.trans ((source_old (chosen i)).of_dvd hsmall)),
        fun h => ((source_old z).of_dvd hsmall).trans
          (h.trans ((source_old (chosen i)).of_dvd hsmall).symm)⟩
    · rw [if_neg he0]
      rw [← Nat.modEq_and_modEq_iff_modEq_mul hmcp]
      constructor
      · intro h
        have hcode : f z ≡ f (chosen i) [MOD q ^ e k] :=
          ((source_code z).of_dvd hqa).symm.trans
            ((h.of_dvd hdq).trans ((source_code (chosen i)).of_dvd hqa))
        refine ⟨(code_prefix _ (by omega) (he k) _ _).mp hcode, ?_⟩
        exact ((source_old z).of_dvd hmold).symm.trans
          ((h.of_dvd hdm).trans ((source_old (chosen i)).of_dvd hmold))
      · rintro ⟨hhigh, hcofactor⟩
        have hpa : z ≡ chosen i [MOD p ^ a k] := hhigh.of_dvd
          (pow_dvd_pow p ((ha k).trans (Nat.le_add_right H _)))
        have hsp : source z ≡ source (chosen i) [MOD p ^ a k] :=
          ((source_old z).of_dvd hpold).trans
            (hpa.trans ((source_old (chosen i)).of_dvd hpold).symm)
        have hsq : source z ≡ source (chosen i) [MOD q ^ e k] :=
          ((source_code z).of_dvd hqa).trans
            (((code_prefix _ (by omega) (he k) _ _).mpr hhigh).trans
              ((source_code (chosen i)).of_dvd hqa).symm)
        have hsm : source z ≡ source (chosen i) [MOD m k] :=
          ((source_old z).of_dvd hmold).trans
            (hcofactor.trans ((source_old (chosen i)).of_dvd hmold).symm)
        rw [hfactor k, mul_assoc]
        apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
        refine ⟨hsp, ?_⟩
        exact (Nat.modEq_and_modEq_iff_modEq_mul
          ((hq.coprime_iff_not_dvd.mpr (hqm k)).pow_left _)).mp ⟨hsq, hsm⟩
  have enclosure : ∀ i : Survivor, ∀ z,
      source z ≡ S.residue i.val [MOD S.modulus i.val] →
      z ≡ chosen i [MOD outputModulus i.val] := by
    intro i z hz
    apply ((exact_fiber i z).mp hz).of_dvd
    apply Nat.mul_dvd_mul_right
    by_cases h : e i.val = 0
    · simp [h]
    · rw [if_neg h]
      apply pow_dvd_pow
      have := ha i.val
      omega
  let n := Fintype.card Survivor
  let enumerate : Fin n ≃ Survivor := (Fintype.equivFin Survivor).symm
  refine ⟨n, ?_, ⟨{
    residue := fun i => chosen (enumerate i)
    modulus := fun i => outputModulus (enumerate i).val
    covers := ?_
    modulus_one_lt := fun i => (output_good _).1
    modulus_odd := fun i => (output_good _).2
    modulus_injective := ?_
  }⟩⟩
  · simpa only [Fintype.card_fin] using Fintype.card_subtype_lt missing
  · intro z
    obtain ⟨i, hi⟩ := S.covers (source z)
    let survivor : Survivor := ⟨i, z, hi⟩
    refine ⟨enumerate.symm survivor, ?_⟩
    simpa only [Equiv.apply_symm_apply] using enclosure survivor z hi
  · intro i k hik
    apply enumerate.injective
    apply Subtype.ext
    exact output_injective hik

end Erdos7.OddDistinctCoveringSystem
