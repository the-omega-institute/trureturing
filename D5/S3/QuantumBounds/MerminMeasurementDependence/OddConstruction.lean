/- GID: D5/S3/QuantumBounds/MerminMeasurementDependence/OddConstruction
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/MerminMeasurementDependence/OddConstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quadratic Walsh signs produce faithful models attaining the staircase. -/
/-
proof_shape: odd_construction: content
escape_witness: odd_construction: Fourier inversion constructs normalized positive sign rows; parity lifting and data processing give the sharp variation.
admission_basis: escape-witness
Direct frozen dependencies:
  D5/S3/Analytic/ReflectedSpectrum/ParityConditionedMoments.parity_conditioned_moments; statement_id: sha256:ed62d76fc6e827a0d18046b242595731953b80a695e773091de995a23517a93c
  D5/S3/TotalVariation/DataProcessing.total_variation_channel_le; statement_id: sha256:0fcf09f55b7d4d7d738c0302dadae43da45df416b2af70f466e283909e162ec6
  D5/S3/TotalVariation/Pinsker.totalVariation; statement_id: sha256:417383b2f5f4a4f7c56881e521c516e431c6f287d2d24996ca4ec3797e2e61f3
  D5/S3/Divergence/ClassicalDPI.channelOutput; statement_id: sha256:bb11b45a5bb58d49bd779aa75b68940ca4390a1dc69947eb5336eed0279521e5
computational_content.kind: none; general mathematical statements, not an executable API.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.QuantumBounds.MerminMeasurementDependence.SpectralLowerBound
import D5.S3.QuantumBounds.MerminMeasurementDependence.FiberLift
import D5.S3.QuantumBounds.MerminMeasurementDependence.SignDesign
import D5.S3.TotalVariation.DataProcessing
import D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace D5.S3.QuantumBounds.MerminMeasurementDependence
noncomputable section

def oddGamma (k : ℕ) (a : (Fin (2*k) → ZMod 2)) : Fin (2*k+1) → ZMod 2 := Fin.snoc a 0

def oddRow (k : ℕ) (x : Setting (2*k+1)) (a : (Fin (2*k) → ZMod 2)) : ℝ :=
  spectralRow k (freeSetting x) a

private def oddDensity (k : ℕ) (x : Setting (2*k+1)) : Strategy (2*k+1) → ℝ :=
  liftedDensity (walshParity k) (oddGamma k)
    (designDensity (oddRow k) ((2 : ℝ)^k) x)

set_option maxHeartbeats 1000000 in
-- Fourier inversion, sign counts and the parity lift are verified in one declaration.
theorem odd_construction (k : ℕ) (hk : 1 ≤ k) :
    ∃ rho : Setting (2*k+1) → Strategy (2*k+1) → ℝ,
      Faithful rho ∧ F rho = floorValue (2*k+1) := by
  have lifted_faithful {d : ℕ} {C : Type} [Fintype C]
      (P : C → ZMod 2) (gamma : C → Fin (d+1) → ZMod 2)
      (p : Setting (d+1) → C → ℝ)
      (hpos : ∀ x c, 0 ≤ p x c) (hnorm : ∀ x, ∑ c, p x c = 1)
      (hfull : ∀ x, ∑ c, p x c * classResponse P gamma x c = target x) :
      Faithful (fun x => liftedDensity P gamma (p x)) := by
    have card_fiber (d : ℕ) (P : ZMod 2) : Fintype.card (AlphaFiber (d+1) P) = 2^d := by
      rw [Fintype.card_congr (fiberEquiv d P)]
      simp
    have fiberMixture_normalized {d : ℕ} {C : Type _} [Fintype C]
        (P : C → ZMod 2) (p : C → ℝ) (hp : ∑ c, p c = 1) :
        ∑ z, fiberMixture (d := d) P p z = 1 := by
      rw [Fintype.sum_sigma]
      unfold fiberMixture
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_fiber,Nat.cast_pow,Nat.cast_ofNat]
      have hz : (2 : ℝ)^d ≠ 0 := by positivity
      simp_rw [mul_div_cancel₀ _ hz]
      exact hp
    have pushDensity_expect {A B : Type _} [Fintype A] [Fintype B] [DecidableEq B]
        (map : A → B) (p : A → ℝ) (f : B → ℝ) :
        (∑ b, (fun map p => D5.S3.Divergence.ClassicalDPI.channelOutput (fun a b => if map a=b then 1 else 0) p) map p b * f b) = ∑ a, p a * f (map a) := by
      dsimp only
      unfold D5.S3.Divergence.ClassicalDPI.channelOutput
      simp only [mul_ite, mul_one, mul_zero]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      have point : ∀ b, (if map a = b then p a else 0) * f b =
          if map a = b then p a * f b else 0 := by intro b;split_ifs <;> ring
      simp_rw [point]
      simp
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
    have bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
      rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
        simp [bitSign,boolSign,show (1 : ZMod 2) + 1 = 0 from by decide]
    have boolBit_bitBool (z : ZMod 2) : (fun b : Bool => (b.toNat : ZMod 2)) ((fun z : ZMod 2 => decide (z = 1)) z) = z :=
      by rcases bit_cases z with rfl | rfl <;> simp []
    have bitSign_boolBit (b : Bool) : bitSign ((fun b : Bool => (b.toNat : ZMod 2)) b) = boolSign b := by
      cases b <;> simp [bitSign,boolSign]
    have prod_boolSign {n : ℕ} (x : Fin n → Bool) (I : Finset (Fin n)) :
        (∏ i ∈ I, boolSign (x i)) = bitSign (∑ i ∈ I, (fun b : Bool => (b.toNat : ZMod 2)) (x i)) := by
      classical
      induction I using Finset.induction_on with
      | empty => simp [bitSign,boolSign]
      | @insert i I hi ih =>
          rw [Finset.prod_insert hi, Finset.sum_insert hi, bitSign_add, bitSign_boolBit, ih]
    have subset_response_formula {n : ℕ} (alpha gamma : Fin n → ZMod 2)
        (x : Setting n) (I : Finset (Fin n)) :
        response (tableOfAlphaGamma alpha gamma) x I =
          bitSign (∑ i ∈ I, alpha i) * bitSign (∑ i ∈ I, gamma i * (fun b : Bool => (b.toNat : ZMod 2)) (x.1 i)) := by
      rw [response,prod_boolSign]
      have formula : ∀ i, (fun b : Bool => (b.toNat : ZMod 2)) (responseBit (tableOfAlphaGamma alpha gamma) x i) =
          alpha i + gamma i * (fun b : Bool => (b.toNat : ZMod 2)) (x.1 i) := by
        intro i
        cases hx : x.1 i <;>
          simp only [responseBit,tableOfAlphaGamma,hx,Bool.false_eq_true,ite_false,ite_true,boolBit_bitBool] <;>
          norm_num []
      simp_rw [formula]
      rw [Finset.sum_add_distrib,bitSign_add]
    have lifted_full_correlator {d : ℕ} {C : Type _} [Fintype C]
        (P : C → ZMod 2) (gamma : C → Fin (d+1) → ZMod 2) (p : C → ℝ)
        (x : Setting (d+1)) :
        (∑ lambda, liftedDensity P gamma p lambda * response lambda x Finset.univ) =
          ∑ c, p c * classResponse P gamma x c := by
      rw [liftedDensity,pushDensity_expect,Fintype.sum_sigma]
      unfold fiberMixture liftClassTable
      simp_rw [subset_response_formula]
      have hf (c : C) (alpha : AlphaFiber (d+1) (P c)) :
          (∑ i : Fin (d+1), alpha.1 i) = P c := alpha.2
      simp_rw [hf]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_fiber,
        Nat.cast_pow,Nat.cast_ofNat]
      unfold classResponse
      apply Finset.sum_congr rfl
      intro c hc
      have hz : (2 : ℝ)^d ≠ 0 := by positivity
      field_simp
    let si (z : ZMod 2) : ℤ := if z = 1 then -1 else 1
    have si_cast (z : ZMod 2) : (si z : ℝ) = bitSign z := by
      by_cases h : z = 1 <;> simp [si, bitSign, boolSign, h]
    have si_add (a b : ZMod 2) : si (a+b) = si a * si b := by
      rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;> simp [si, show (1 : ZMod 2)+1=0 from by decide]
    have si_sum {n : ℕ} (I : Finset (Fin n)) (a : Fin n → ZMod 2) :
        si (∑ i ∈ I, a i) = ∏ i ∈ I, si (a i) := by
      classical
      induction I using Finset.induction_on with
      | empty => simp [si]
      | @insert i I hi ih => simp [hi, si_add, ih]
    have si_cases (z : ZMod 2) : si z = -1 ∨ si z = 1 := by
      unfold si; split_ifs <;> simp
    have si_inj : Function.Injective si := by
      intro a b h
      rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;> simp [si] at h ⊢
    let reviewFlip (z : ZMod 2) : Fin 2 := (ZMod.finEquiv 2).symm ((1 : ZMod 2)-z)
    let unflip (z : Fin 2) : ZMod 2 := (1 : ZMod 2)-(ZMod.finEquiv 2) z
    have flip_unflip (z : Fin 2) : reviewFlip (unflip z)=z := by simp [reviewFlip, unflip]
    have unflip_flip (z : ZMod 2) : unflip (reviewFlip z)=z := by simp [reviewFlip, unflip]
    have ps_flip (z : ZMod 2) : D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments.paritySign (reviewFlip z) = si z := by
      rcases bit_cases z with rfl | rfl <;> norm_num [reviewFlip, ZMod.finEquiv, D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments.paritySign, si]


    have parity_fiber_cancellation (n : ℕ) (P : ZMod 2) (I : Finset (Fin n))
        (hne : I.Nonempty) (hproper : I ≠ Finset.univ) :
        ∑ alpha : AlphaFiber n P, bitSign (∑ i ∈ I, alpha.1 i) = 0 := by
      classical
      have hn : 0 < n := by obtain ⟨i, hi⟩ := hne; exact Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      have memflip (a : Fin (k+1) → ZMod 2) :
          (fun i => reviewFlip (a i)) ∈ D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments.parityFiber (k+1) (si P) ↔ ∑ i, a i = P := by
        simp only [D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments.parityFiber, Finset.mem_filter, Finset.mem_univ, true_and, ps_flip]
        rw [← si_sum]
        exact si_inj.eq_iff
      let e : AlphaFiber (k+1) P ≃ {x : Fin (k+1) → Fin 2 // x ∈ D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments.parityFiber (k+1) (si P)} :=
        { toFun := fun a => ⟨fun i => reviewFlip (a.1 i), (memflip a.1).mpr a.2⟩
          invFun := fun x => ⟨fun i => unflip (x.1 i), by
            have h := (memflip (fun i => unflip (x.1 i))).mp ?_
            · exact h
            · simpa only [flip_unflip] using x.2⟩
          left_inv := by intro a; apply Subtype.ext; funext i; exact unflip_flip _
          right_inv := by intro x; apply Subtype.ext; funext i; exact flip_unflip _ }
      have hzero := (D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments.parity_conditioned_moments k (si P) (si_cases P)).2.1 I hne hproper
      have hcast : (∑ x ∈ D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments.parityFiber (k+1) (si P), (∏ i ∈ I, D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments.paritySign (x i) : ℤ) : ℝ) = 0 := by
        exact_mod_cast hzero
      have sumsub :
          (∑ x : {x : Fin (k+1) → Fin 2 // x ∈ D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments.parityFiber (k+1) (si P)},
            ((∏ i ∈ I, D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments.paritySign (x.1 i) : ℤ) : ℝ)) = 0 := by
        exact (Finset.sum_subtype
          (D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments.parityFiber (k+1) (si P))
          (fun _ => Iff.rfl)
          (fun x : Fin (k+1) → Fin 2 => ((∏ i ∈ I, D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments.paritySign (x i) : ℤ) : ℝ))).symm.trans hcast
      have matchsign (a : AlphaFiber (k+1) P) :
          ((∏ i ∈ I, D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments.paritySign ((e a).1 i) : ℤ) : ℝ) = bitSign (∑ i ∈ I, a.1 i) := by
        change ((∏ i ∈ I, D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments.paritySign (reviewFlip (a.1 i)) : ℤ) : ℝ) = _
        simp only [ps_flip, ← si_sum, si_cast]
      calc
        _ = ∑ a : AlphaFiber (k+1) P, ((∏ i ∈ I, D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments.paritySign ((e a).1 i) : ℤ) : ℝ) := by
          apply Finset.sum_congr rfl; intro a _; exact (matchsign a).symm
        _ = _ := (Fintype.sum_equiv e _ _ (fun a => rfl)).trans sumsub

    have mixed_subset_fiber_cancellation {n : ℕ} (P : ZMod 2) (gamma : Fin n → ZMod 2)
        (x : Setting n) (I : Finset (Fin n)) (hnonempty : I.Nonempty) (hproper : I ≠ Finset.univ) :
        ∑ alpha : AlphaFiber n P, response (tableOfAlphaGamma alpha.1 gamma) x I = 0 := by
      simp_rw [subset_response_formula]
      rw [← Finset.sum_mul,parity_fiber_cancellation n P I hnonempty hproper,zero_mul]
    have lifted_proper_correlator {d : ℕ} {C : Type _} [Fintype C]
        (P : C → ZMod 2) (gamma : C → Fin (d+1) → ZMod 2) (p : C → ℝ)
        (x : Setting (d+1)) (I : Finset (Fin (d+1)))
        (hnonempty : I.Nonempty) (hproper : I ≠ Finset.univ) :
        (∑ lambda, liftedDensity P gamma p lambda * response lambda x I) = 0 := by
      rw [liftedDensity,pushDensity_expect,Fintype.sum_sigma]
      unfold fiberMixture liftClassTable
      simp_rw [← Finset.mul_sum,mixed_subset_fiber_cancellation _ _ _ _ hnonempty hproper,mul_zero]
      simp
    have pushDensity_nonneg {A B : Type _} [Fintype A] [DecidableEq B]
        (map : A → B) (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) :
        ∀ b, 0 ≤ (fun map p => D5.S3.Divergence.ClassicalDPI.channelOutput (fun a b => if map a=b then 1 else 0) p) map p b := by
      intro b
      dsimp only
      unfold D5.S3.Divergence.ClassicalDPI.channelOutput
      simp only [mul_ite, mul_one, mul_zero]
      apply Finset.sum_nonneg
      intro a ha
      split_ifs
      · exact hp a
      · exact le_rfl
    have pushDensity_sum {A B : Type _} [Fintype A] [Fintype B] [DecidableEq B]
        (map : A → B) (p : A → ℝ) :
        ∑ b, (fun map p => D5.S3.Divergence.ClassicalDPI.channelOutput (fun a b => if map a=b then 1 else 0) p) map p b = ∑ a, p a := by
      dsimp only
      unfold D5.S3.Divergence.ClassicalDPI.channelOutput
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_comm]
      simp
    refine ⟨⟨?_,?_⟩,?_,?_⟩
    · intro x
      apply pushDensity_nonneg
      intro z
      exact div_nonneg (hpos x z.1) (by positivity)
    · intro x
      change (∑ lambda, liftedDensity P gamma (p x) lambda) = 1
      rw [liftedDensity,pushDensity_sum]
      exact fiberMixture_normalized P (p x) (hnorm x)
    · intro x
      unfold correlator
      rw [lifted_full_correlator]
      exact hfull x
    · intro x I hi hp
      exact lifted_proper_correlator P gamma (p x) x I hi hp

  have boolSign_cases (b : Bool) : boolSign b = 1 ∨ boolSign b = -1 := by
    cases b <;> simp [boolSign]
  have designDensity_nonneg {X C : Type _} [Fintype C]
      (c : X → C → ℝ) (R : ℝ) (hR : 0 < R)
      (hsign : ∀ x a, c x a = 1 ∨ c x a = -1) :
      ∀ x a, 0 ≤ designDensity c R x a := by
    intro x a
    unfold designDensity
    apply div_nonneg
    · rcases hsign x a with h | h <;> rw [h] <;> norm_num
    · positivity
  have designDensity_normalized {X C : Type _} [Fintype C]
      (c : X → C → ℝ) (R : ℝ) (hR : 0 < R)
      (hsum : ∀ x, ∑ a, c x a = R) :
      ∀ x, ∑ a, designDensity c R x a = 1 := by
    intro x
    unfold designDensity
    rw [← Finset.sum_div,Finset.sum_add_distrib,hsum]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    exact div_self (by positivity)
  have design_full_expectation {X C : Type _} [Fintype C]
      (r c : X → C → ℝ) (t : X → ℝ) (R : ℝ) (hR : 0 < R)
      (ht : ∀ x, t x = 1 ∨ t x = -1)
      (hr : ∀ x a, r x a = 1 ∨ r x a = -1)
      (hc : ∀ x a, c x a = t x * r x a)
      (hsum : ∀ x, ∑ a, c x a = R) :
      ∀ x, ∑ a, designDensity c R x a * r x a = t x := by
    intro x
    have point (a : C) :
        designDensity c R x a * r x a = designDensity c R x a * t x := by
      unfold designDensity
      rw [hc]
      rcases ht x with h | h <;> rcases hr x a with h' | h' <;> rw [h,h'] <;> ring
    simp_rw [point]
    rw [← Finset.sum_mul,designDensity_normalized c R hR hsum,one_mul]
  have odd_class_response (k : ℕ) (x : Setting (2*k+1)) (a : (Fin (2*k) → ZMod 2)) :
      classResponse (walshParity k) (oddGamma k) x a =
        bitSign (walshParity k a) * character a (freeSetting x) := by
    unfold classResponse oddGamma
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc,Fin.snoc_last,zero_mul,add_zero]
    rw [character]
    rfl
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
  have settingWeight_snoc {d : ℕ} (x : Fin d → Bool) (b : Bool) :
      (fun x => hammingDist x (fun _ => false)) (Fin.snoc x b) = (fun x => hammingDist x (fun _ => false)) x + b.toNat := by
    rw [settingWeight_eq_sum,Fin.sum_univ_castSucc,settingWeight_eq_sum]
    simp
  have evenExtension_weight {d : ℕ} (x : Fin d → ZMod 2) :
      (fun x => hammingDist x (fun _ => false)) (evenExtension x) =
        (fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i)) + ((fun z : ZMod 2 => decide (z = 1)) (∑ i, x i)).toNat := by
    exact settingWeight_snoc _ _
  have bitSign_natCast (w : ℕ) :
      bitSign (w : ZMod 2) = boolSign (decide (w % 2 = 1)) := by
    simp [bitSign,ZMod.natCast_eq_one_iff_odd,Nat.odd_iff]
  have choose_even_cast (k : ℕ) :
      (Nat.choose (2 * k) 2 : ZMod 2) = (k : ZMod 2) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : Nat.choose (2*k+1) 2 = 2*k + Nat.choose (2*k) 2 := by
        simpa using Nat.choose_succ_succ' (2*k) 1
      have h2 : Nat.choose (2*k+2) 2 = (2*k+1) + Nat.choose (2*k+1) 2 := by
        simpa using Nat.choose_succ_succ' (2*k+1) 1
      have e : 2 * (k+1) = 2*k+2 := by omega
      rw [e,h2,h1]
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,ih]
      simp [show (2 : ZMod 2) = 0 from by decide,add_comm]
  have target_eq_choose {n : ℕ} (x : Setting n) :
      target x = bitSign (Nat.choose ((fun x => hammingDist x (fun _ => false)) x.1) 2 : ZMod 2) := by
    have he : (fun x => hammingDist x (fun _ => false)) x.1 = 2 * ((fun x => hammingDist x (fun _ => false)) x.1 / 2) := by have := x.2; omega
    rw [he,choose_even_cast]
    unfold target
    rw [he]
    simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    exact (bitSign_natCast _).symm
  have even_target_parity_adjustment {d : ℕ} (x : Fin d → ZMod 2) :
      target (evenSetting x) =
        bitSign ((Nat.choose ((fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i))) 2 : ZMod 2) + ∑ i, x i) := by
    rw [target_eq_choose]
    change bitSign (Nat.choose ((fun x => hammingDist x (fun _ => false)) (evenExtension x)) 2 : ZMod 2) = _
    rw [evenExtension_weight]
    have hparity : ∑ i, x i = ((fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i)) : ZMod 2) := by
      rw [← parity_sum]
      simp only [boolBit_bitBool]
    have hcast :
        (Nat.choose ((fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i)) + ((fun z : ZMod 2 => decide (z = 1)) (∑ i, x i)).toNat) 2 : ZMod 2) =
          (Nat.choose ((fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i))) 2 : ZMod 2) + ∑ i, x i := by
      rcases bit_cases (∑ i, x i) with h | h
      · simp [h]
      · simp only [h,decide_true,if_true,Bool.toNat_true]
        have hchoose : Nat.choose ((fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i)) + 1) 2 =
            (fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i)) + Nat.choose ((fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i))) 2 := by
          simpa using Nat.choose_succ_succ' ((fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i))) 1
        simp only [] at hchoose hparity
        rw [hchoose,Nat.cast_add,← hparity,h]
        ring
    rw [hcast]
  have target_eq_qFree {d : ℕ} (x : Fin d → ZMod 2) :
      target (evenSetting x)=bitSign (qFree x) := even_target_parity_adjustment x
  have target_freeSetting (k : ℕ) (x : Setting (2*k+1)) :
      target x = bitSign (qFree (freeSetting x)) := by
    rw [← evenSetting_freeSetting x,target_eq_qFree]
    rw [freeSetting_evenSetting]
  have odd_row_consistency (k : ℕ) (x : Setting (2*k+1)) (a : (Fin (2*k) → ZMod 2)) :
      oddRow k x a = target x * classResponse (walshParity k) (oddGamma k) x a := by
    rw [target_freeSetting,odd_class_response]
    unfold oddRow spectralRow
    ring
  have spectralRow_sign (k : ℕ) (x a : (Fin (2*k) → ZMod 2)) :
      spectralRow k x a = 1 ∨ spectralRow k x a = -1 := by
    have hf := boolSign_cases ((fun z : ZMod 2 => decide (z = 1)) (qFree x))
    have hp := boolSign_cases ((fun z : ZMod 2 => decide (z = 1)) (walshParity k a))
    have hc := boolSign_cases ((fun z : ZMod 2 => decide (z = 1)) (∑ i, a i*x i))
    unfold spectralRow bitSign
    change character a x=1 ∨ character a x= -1 at hc
    rcases hf with hf | hf <;> rcases hp with hp | hp <;> rcases hc with hc | hc <;>
      simp [hf,hp,hc]
  have walsh_factor (k : ℕ) (a : Fin (2*k) → ZMod 2) :
      walsh a = (2 : ℝ)^k * bitSign (walshParity k a) := by
    have h := qFree_walsh_square k a
    have hp : (2 : ℝ)^(2*k)=((2 : ℝ)^k)^2 := by rw [mul_comm 2 k,pow_mul]
    rw [hp] at h
    unfold walshParity
    split_ifs with hn
    · norm_num [bitSign,boolSign]
      have hr : 0 < (2 : ℝ)^k := by positivity
      nlinarith
    · norm_num [bitSign,boolSign]
      have hr : 0 < (2 : ℝ)^k := by positivity
      have ha := le_of_not_gt hn
      nlinarith
  have bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
    rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
      simp [bitSign,boolSign,show (1 : ZMod 2) + 1 = 0 from by decide]
  have bitSign_injective : Function.Injective bitSign := by
    intro a b h
    rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
      simp [bitSign,boolSign] at h ⊢ <;> norm_num at h
  have character_sum {d : ℕ} (a : Fin d → ZMod 2) :
      ∑ x, character a x = if a=0 then (2 : ℝ)^d else 0 := by
    classical
    let ch : AddChar (Fin d → ZMod 2) ℝ :=
      { toFun := character a
        map_zero_eq_one' := by simp [character,bitSign,boolSign]
        map_add_eq_mul' := by
          intro x y
          simp only [character,Pi.add_apply,mul_add,Finset.sum_add_distrib,bitSign_add] }
    have he : ch=0 ↔ a=0 := by
      constructor
      · intro h
        funext i
        have hi := congrArg (fun t : AddChar (Fin d → ZMod 2) ℝ => t (Pi.single i 1)) h
        change character a (Pi.single i 1)=1 at hi
        have ha : bitSign (a i)=bitSign 0 := by
          simpa [character,Pi.single_apply,bitSign,boolSign] using hi
        exact bitSign_injective ha
      · intro h
        ext x
        simp [ch,character,h,bitSign,boolSign]
    have hc := AddChar.sum_eq_ite ch
    change (∑ x, character a x) = if ch=0 then _ else _ at hc
    simpa only [he,Fintype.card_fun,ZMod.card,Nat.cast_pow,Nat.cast_ofNat,Fintype.card_fin] using hc
  have character_orthogonality {d : ℕ} (x y : Fin d → ZMod 2) :
      ∑ a, character a x * character a y = if x=y then (2 : ℝ)^d else 0 := by
    have hp (a : Fin d → ZMod 2) : character a x*character a y=character (x+y) a := by
      unfold character
      rw [← bitSign_add,← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Pi.add_apply]
      ring
    simp_rw [hp]
    rw [character_sum]
    have he : x+y=0 ↔ x=y := by
      constructor
      · intro h
        have hy : y+y=0 := by funext i;exact CharTwo.add_self_eq_zero (y i)
        exact add_right_cancel (h.trans hy.symm)
      · rintro rfl
        funext i
        exact CharTwo.add_self_eq_zero (x i)
    simp only [he]
  have walsh_reconstruction {d : ℕ} (x : Fin d → ZMod 2) :
      (2 : ℝ)^d * bitSign (qFree x) = ∑ a, walsh a * character a x := by
    unfold walsh
    simp_rw [bitSign_add,Finset.sum_mul]
    rw [Finset.sum_comm]
    have hp (y a : Fin d → ZMod 2) :
        (bitSign (qFree y)*bitSign (∑ i, a i*y i))*character a x =
        bitSign (qFree y)*(character a y*character a x) := by exact mul_assoc _ _ _
    simp_rw [hp]
    simp_rw [← Finset.mul_sum,character_orthogonality]
    have he (y : Fin d → ZMod 2) :
        bitSign (qFree y)*(if y=x then (2 : ℝ)^d else 0) =
        if y=x then bitSign (qFree x)*(2 : ℝ)^d else 0 := by
      split_ifs with h
      · rw [h]
      · simp
    simp_rw [he]
    simp [mul_comm]
  have spectralRow_sum (k : ℕ) (x : (Fin (2*k) → ZMod 2)) :
      ∑ a, spectralRow k x a = (2 : ℝ)^k := by
    have h := walsh_reconstruction x
    simp_rw [walsh_factor] at h
    simp_rw [mul_assoc] at h
    rw [← Finset.mul_sum] at h
    have hp : (2 : ℝ)^(2*k) = ((2 : ℝ)^k)^2 := by rw [mul_comm 2 k,pow_mul]
    rw [hp] at h
    have hz : (2 : ℝ)^k ≠ 0 := by positivity
    have hc : ∑ a, bitSign (walshParity k a) * character a x =
        (2 : ℝ)^k * bitSign (qFree x) := by
      apply mul_left_cancel₀ hz
      calc
        _ = ((2 : ℝ)^k)^2 * bitSign (qFree x) := h.symm
        _ = _ := by ring
    unfold spectralRow
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum,hc]
    have hs : bitSign (qFree x) * bitSign (qFree x) = 1 := by
      rcases boolSign_cases ((fun z : ZMod 2 => decide (z = 1)) (qFree x)) with h | h <;> simp [bitSign,h]
    calc
      _ = (2 : ℝ)^k * (bitSign (qFree x) * bitSign (qFree x)) := by ring
      _ = _ := by rw [hs,mul_one]
  have oddDensity_faithful (k : ℕ) : Faithful (oddDensity k) := by
    apply lifted_faithful
    · apply designDensity_nonneg _ _ (by positivity)
      exact fun x a => spectralRow_sign k (freeSetting x) a
    · apply designDensity_normalized _ _ (by positivity)
      exact fun x => spectralRow_sum k (freeSetting x)
    · apply design_full_expectation _ _ _ _ (by positivity)
      · intro x
        exact boolSign_cases _
      · intro x a
        unfold classResponse
        rcases boolSign_cases ((fun z : ZMod 2 => decide (z = 1)) (walshParity k a)) with h | h <;>
          rcases boolSign_cases ((fun z : ZMod 2 => decide (z = 1)) (∑ i, oddGamma k a i * (fun b : Bool => (b.toNat : ZMod 2)) (x.1 i))) with h' | h' <;>
          simp [bitSign,h,h']
      · exact odd_row_consistency k
      · exact fun x => spectralRow_sum k (freeSetting x)
  have F_le_of_pairwise {n : ℕ} (rho : Setting n → Strategy n → ℝ) (c : ℝ)
      (h : ∀ x y, D5.S3.TotalVariation.Pinsker.totalVariation (rho x) (rho y) ≤ c) : F rho ≤ c := by
    classical
    let zero : Setting n := ⟨fun _ => false,by simp [hammingDist, Bool.not_eq_false]⟩
    haveI : Nonempty (Setting n) := ⟨zero⟩
    unfold F M
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply csSup_le (Set.range_nonempty _)
    rintro r ⟨⟨x,y⟩,rfl⟩
    have hp := h x y
    unfold D5.S3.TotalVariation.Pinsker.totalVariation at hp
    linarith
  have sign_abs_difference (a b : ℝ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
      |a-b| = 1-a*b := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num
  have designDensity_tv {X C : Type _} [Fintype C]
      (c : X → C → ℝ) (R : ℝ) (hR : 0 < R)
      (hsign : ∀ x a, c x a = 1 ∨ c x a = -1) (x y : X) :
      D5.S3.TotalVariation.Pinsker.totalVariation (designDensity c R x) (designDensity c R y) =
        ((Fintype.card C : ℝ) - ∑ a, c x a * c y a) /
          (2*((Fintype.card C : ℝ) + R)) := by
    unfold D5.S3.TotalVariation.Pinsker.totalVariation designDensity
    have hD : 0 < (Fintype.card C : ℝ) + R := by positivity
    have point (a : C) :
        |(1+c x a)/((Fintype.card C : ℝ)+R) -
            (1+c y a)/((Fintype.card C : ℝ)+R)| =
          (1-c x a*c y a)/((Fintype.card C : ℝ)+R) := by
      rw [← sub_div,show 1+c x a-(1+c y a)=c x a-c y a by ring,
        abs_div,abs_of_pos hD,sign_abs_difference _ _ (hsign x a) (hsign y a)]
    simp_rw [point]
    rw [← Finset.sum_div,Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    field_simp
  have designDensity_tv_le {X C : Type _} [Fintype C]
      (c : X → C → ℝ) (R : ℝ) (hR : 0 < R)
      (hsign : ∀ x a, c x a = 1 ∨ c x a = -1)
      (hcross : ∀ x y, 0 ≤ ∑ a, c x a * c y a) (x y : X) :
      D5.S3.TotalVariation.Pinsker.totalVariation (designDensity c R x) (designDensity c R y) ≤
        (Fintype.card C : ℝ) / (2*((Fintype.card C : ℝ) + R)) := by
    rw [designDensity_tv c R hR hsign]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [hcross x y]
  have card_fiber (d : ℕ) (P : ZMod 2) : Fintype.card (AlphaFiber (d+1) P) = 2^d := by
    rw [Fintype.card_congr (fiberEquiv d P)]
    simp
  have fiberMixture_tv {d : ℕ} {C : Type _} [Fintype C]
      (P : C → ZMod 2) (p q : C → ℝ) :
      D5.S3.TotalVariation.Pinsker.totalVariation (fiberMixture (d := d) P p) (fiberMixture P q) = D5.S3.TotalVariation.Pinsker.totalVariation p q := by
    unfold D5.S3.TotalVariation.Pinsker.totalVariation
    congr 1
    rw [Fintype.sum_sigma]
    unfold fiberMixture
    simp_rw [← sub_div,abs_div]
    have hz : 0 < (2 : ℝ)^d := by positivity
    simp only [abs_of_pos hz,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_fiber,Nat.cast_pow,Nat.cast_ofNat]
    simp_rw [mul_div_cancel₀ _ hz.ne']
  have pushDensity_tv_le {A B : Type _} [Fintype A] [Fintype B] [DecidableEq B]
      (map : A → B) (p q : A → ℝ) :
      D5.S3.TotalVariation.Pinsker.totalVariation ((fun map p => D5.S3.Divergence.ClassicalDPI.channelOutput (fun a b => if map a=b then 1 else 0) p) map p) ((fun map p => D5.S3.Divergence.ClassicalDPI.channelOutput (fun a b => if map a=b then 1 else 0) p) map q) ≤ D5.S3.TotalVariation.Pinsker.totalVariation p q := by
    classical
    let W : A → B → ℝ := fun a b => if map a=b then 1 else 0
    have hW : (∀ a b, 0 ≤ W a b) ∧ ∀ a, ∑ b, W a b = 1 := by
      constructor
      · intro a b
        unfold W
        split_ifs <;> norm_num
      · intro a
        simp [W]
    have output (r : A → ℝ) :
        D5.S3.Divergence.ClassicalDPI.channelOutput W r = (fun map p => D5.S3.Divergence.ClassicalDPI.channelOutput (fun a b => if map a=b then 1 else 0) p) map r := by
      rfl
    have h := D5.S3.TotalVariation.DataProcessing.total_variation_channel_le p q W hW
    rw [output p,output q] at h
    simpa only [D5.S3.TotalVariation.Pinsker.totalVariation,D5.S3.TotalVariation.Pinsker.totalVariation,div_eq_mul_inv,mul_comm,one_mul]
      using h
  have lifted_tv_le {d : ℕ} {C : Type _} [Fintype C]
      (P : C → ZMod 2) (gamma : C → Fin (d+1) → ZMod 2) (p q : C → ℝ) :
      D5.S3.TotalVariation.Pinsker.totalVariation (liftedDensity P gamma p) (liftedDensity P gamma q) ≤ D5.S3.TotalVariation.Pinsker.totalVariation p q := by
    unfold liftedDensity
    exact (pushDensity_tv_le _ _ _).trans_eq (fiberMixture_tv P p q)
  have spectralRow_cross (k : ℕ) (x y : (Fin (2*k) → ZMod 2)) :
      ∑ a, spectralRow k x a * spectralRow k y a =
        if x=y then (2 : ℝ)^(2*k) else 0 := by
    classical
    have point (a : (Fin (2*k) → ZMod 2)) :
        spectralRow k x a * spectralRow k y a =
          (bitSign (qFree x) * bitSign (qFree y)) *
            (character a x * character a y) := by
      have hs : bitSign (walshParity k a) * bitSign (walshParity k a) = 1 := by
        rcases boolSign_cases ((fun z : ZMod 2 => decide (z = 1)) (walshParity k a)) with h | h <;> simp [bitSign,h]
      unfold spectralRow
      calc
        _ = (bitSign (qFree x) * bitSign (qFree y)) *
            (bitSign (walshParity k a) * bitSign (walshParity k a)) *
            (character a x * character a y) := by ring
        _ = _ := by rw [hs,mul_one]
    simp_rw [point]
    rw [← Finset.mul_sum]
    rw [character_orthogonality]
    by_cases he : x=y
    · subst y
      simp only [if_true]
      have hs : bitSign (qFree x) * bitSign (qFree x) = 1 := by
        rcases boolSign_cases ((fun z : ZMod 2 => decide (z = 1)) (qFree x)) with h | h <;> simp [bitSign,h]
      rw [hs,one_mul]
    · simp [he]
  have spectral_fraction (k : ℕ) :
      (2 : ℝ)^(2*k) / (2*((2 : ℝ)^(2*k)+(2 : ℝ)^k)) =
        (2 : ℝ)^k / (2*((2 : ℝ)^k+1)) := by
    have hp : (2 : ℝ)^(2*k) = ((2 : ℝ)^k)^2 := by rw [mul_comm 2 k,pow_mul]
    rw [hp]
    field_simp <;> ring
  have oddDensity_upper (k : ℕ) : F (oddDensity k) ≤ floorValue (2*k+1) := by
    apply F_le_of_pairwise
    intro x y
    have hcross (x y : Setting (2*k+1)) : 0 ≤ ∑ a, oddRow k x a * oddRow k y a := by
      unfold oddRow
      rw [spectralRow_cross]
      split_ifs <;> positivity
    have h := (lifted_tv_le (walshParity k) (oddGamma k)
      (designDensity (oddRow k) ((2 : ℝ)^k) x)
      (designDensity (oddRow k) ((2 : ℝ)^k) y)).trans
        (designDensity_tv_le (oddRow k) ((2 : ℝ)^k) (by positivity)
          (fun x a => spectralRow_sign k (freeSetting x) a) hcross x y)
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card] at h
    push_cast at h
    rw [spectral_fraction] at h
    have he : ((2*k+1)-1)/2=k := by omega
    simpa [oddDensity,floorValue,ratio,he] using h
  refine ⟨oddDensity k,oddDensity_faithful k,le_antisymm (oddDensity_upper k) ?_⟩
  exact staircase_lower (2*k+1) (by omega) _ (oddDensity_faithful k)


end
end D5.S3.QuantumBounds.MerminMeasurementDependence
