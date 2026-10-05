/- GID: D5/S3/QuantumBounds/MerminMeasurementDependence/SpectralLowerBound
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/MerminMeasurementDependence/SpectralLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quadratic Walsh signs produce faithful models attaining the staircase. -/
/-
proof_shape: staircase_lower: content
escape_witness: staircase_lower: embed an odd-dimensional setting cube and bound every deterministic satisfaction count by affine_agreement_bound.
admission_basis: escape-witness
Direct frozen dependencies: none.
computational_content.kind: none; general mathematical statements, not an executable API.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.QuantumBounds.MerminMeasurementDependence.Walsh
import D5.S3.QuantumBounds.MerminMeasurementDependence.OverlapBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace D5.S3.QuantumBounds.MerminMeasurementDependence
noncomputable section
def spectralRow (k : ℕ) (x a : (Fin (2*k) → ZMod 2)) : ℝ :=
  bitSign (qFree x) * bitSign (walshParity k a) * character a x

def capValue (k : ℕ) : ℕ := (2^(2*k) + 2^k)/2

theorem staircase_lower (n : ℕ) (hn : 3 ≤ n)
    (rho : Setting n → Strategy n → ℝ) (hfaith : Faithful rho) :
    floorValue n ≤ F rho := by
  have addX_full_response {d : ℕ} (lambda : Strategy (d+1)) (x : Setting d) :
      response lambda (addX x) Finset.univ =
        response (Fin.init lambda) x Finset.univ * boolSign (lambda (Fin.last d)).1 := by
    unfold response
    rw [Fin.prod_univ_castSucc]
    simp only [responseBit,addX,Fin.snoc_castSucc,Fin.snoc_last,Bool.false_eq_true,ite_false]
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
  have settingWeight_snoc {d : ℕ} (x : Fin d → Bool) (b : Bool) :
      (fun x => hammingDist x (fun _ => false)) (Fin.snoc x b) = (fun x => hammingDist x (fun _ => false)) x + b.toNat := by
    rw [settingWeight_eq_sum,Fin.sum_univ_castSucc,settingWeight_eq_sum]
    simp
  have addX_target {d : ℕ} (x : Setting d) : target (addX x) = target x := by
    simp [target,addX,settingWeight_snoc]
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
  have bitSign_boolBit (b : Bool) : bitSign ((fun b : Bool => (b.toNat : ZMod 2)) b) = boolSign b := by
    cases b <;> simp [bitSign,boolSign]
  have boolBit_bitBool (z : ZMod 2) : (fun b : Bool => (b.toNat : ZMod 2)) ((fun z : ZMod 2 => decide (z = 1)) z) = z :=
    by rcases bit_cases z with rfl | rfl <;> simp []
  have prod_boolSign {n : ℕ} (x : Fin n → Bool) (I : Finset (Fin n)) :
      (∏ i ∈ I, boolSign (x i)) = bitSign (∑ i ∈ I, (fun b : Bool => (b.toNat : ZMod 2)) (x i)) := by
    classical
    induction I using Finset.induction_on with
    | empty => simp [bitSign,boolSign]
    | @insert i I hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi, bitSign_add, bitSign_boolBit, ih]
  have full_response_signed_character {n : ℕ} (lambda : Strategy n) (x : Setting n) :
      response lambda x Finset.univ =
        bitSign (tableParity lambda + ∑ i, tableGamma lambda i * (fun b : Bool => (b.toNat : ZMod 2)) (x.1 i)) := by
    rw [response, prod_boolSign]
    congr 1
    unfold tableParity tableGamma
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    unfold responseBit
    cases x.1 i <;> cases (lambda i).1 <;> cases (lambda i).2 <;> norm_num [] <;> decide
  have even_full_response {d : ℕ} (lambda : Strategy (d+1)) (x : Fin d → ZMod 2) :
      response lambda (evenSetting x) Finset.univ =
        bitSign (tableParity lambda + ∑ i, lastAdjustedFrequency lambda i * x i) := by
    rw [full_response_signed_character]
    apply congrArg bitSign
    congr 1
    rw [Fin.sum_univ_castSucc]
    simp only [evenSetting,evenExtension,Fin.snoc_castSucc,Fin.snoc_last,boolBit_bitBool]
    rw [Finset.mul_sum]
    unfold lastAdjustedFrequency
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
  have bitSign_injective : Function.Injective bitSign := by
    intro a b h
    rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
      simp [bitSign,boolSign] at h ⊢ <;> norm_num at h
  have cap_from_affine {n : ℕ} (k : ℕ)
      (embed : (Fin (2*k) → ZMod 2) → Setting n)
      (htarget : ∀ x, target (embed x) = bitSign (qFree x))
      (hresponse : ∀ lambda : Strategy n, ∃ (b : ZMod 2) (a : Fin (2*k) → ZMod 2), ∀ x,
        response lambda (embed x) Finset.univ = bitSign ((b + ∑ i, a i*x i))) :
      ∀ lambda : Strategy n,
        (Finset.univ.filter fun x => response lambda (embed x) Finset.univ = target (embed x)).card ≤
          capValue k := by
    classical
    intro lambda
    obtain ⟨b,a,h⟩ := hresponse lambda
    have sets :
        (Finset.univ.filter fun x => response lambda (embed x) Finset.univ = target (embed x)) =
          Finset.univ.filter fun x => qFree x = (b + ∑ i, a i*x i) := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,h x,htarget x,bitSign_injective.eq_iff]
      exact eq_comm
    rw [sets]
    have bound := affine_agreement_bound k b a
    have hc : 2 * (Finset.univ.filter fun x : (Fin (2*k) → ZMod 2) =>
        qFree x = (b + ∑ i, a i*x i)).card ≤ 2^(2*k) + 2^k := by
      exact_mod_cast (show (2 : ℝ) * (Finset.univ.filter fun x : (Fin (2*k) → ZMod 2) =>
        qFree x = (b + ∑ i, a i*x i)).card ≤ (2 : ℝ)^(2*k) + (2 : ℝ)^k by linarith)
    unfold capValue
    omega
  have cube_card_ge_two (k : ℕ) (hk : 1 ≤ k) : 2 ≤ Fintype.card ((Fin (2*k) → ZMod 2)) := by
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    have he : 1 ≤ 2*k := by omega
    have h := pow_le_pow_right₀ (show 1 ≤ (2 : ℕ) by omega) he
    simpa using h
  have sharp_fraction (k : ℕ) (hk : 1 ≤ k) :
      ((2 : ℝ)^(2*k) - ((2^(2*k) + 2^k) / 2 : ℕ)) / ((2 : ℝ)^(2*k) - 1) =
        (2 : ℝ)^k / (2*((2 : ℝ)^k + 1)) := by
    have hR : 1 < (2 : ℝ)^k := by
      have htwo : (2 : ℝ)^1 ≤ (2 : ℝ)^k := pow_le_pow_right₀ (by norm_num) hk
      norm_num at htwo
      linarith
    have hpow : (2 : ℝ)^(2*k) = ((2 : ℝ)^k)^2 := by rw [mul_comm 2 k,pow_mul]
    have hdvd : 2 ∣ (2^(2*k) + 2^k) := by
      apply dvd_add
      · exact dvd_pow_self 2 (by omega)
      · exact dvd_pow_self 2 (by omega)
    have hnum : (((2^(2*k) + 2^k) / 2 : ℕ) : ℝ) =
        ((2 : ℝ)^(2*k) + (2 : ℝ)^k) / 2 := by
      exact_mod_cast Nat.cast_div hdvd (by norm_num : (2 : ℝ) ≠ 0)
    rw [hnum,hpow]
    have hden : ((2 : ℝ)^k)^2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring
  have lower_via_bent {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
      (embed : (Fin (2*k) → ZMod 2) → Setting n)
      (htarget : ∀ x, target (embed x) = bitSign (qFree x))
      (hresponse : ∀ lambda : Strategy n, ∃ (b : ZMod 2) (a : Fin (2*k) → ZMod 2), ∀ x,
        response lambda (embed x) Finset.univ = bitSign ((b + ∑ i, a i*x i)))
      (rho : Setting n → Strategy n → ℝ) (hfaith : Faithful rho) :
      (2 : ℝ)^k / (2*((2 : ℝ)^k+1)) ≤ F rho := by
    have lower := literal_index_lower embed (capValue k) (cube_card_ge_two k hk)
      (cap_from_affine k embed htarget hresponse) rho hfaith
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card] at lower
    push_cast at lower
    have formula := sharp_fraction k hk
    change ((2 : ℝ)^(2*k) - (capValue k : ℝ)) / ((2 : ℝ)^(2*k) - 1) ≤ F rho at lower
    unfold capValue at lower
    rw [formula] at lower
    exact lower
  have evenExtension_weight {d : ℕ} (x : Fin d → ZMod 2) :
      (fun x => hammingDist x (fun _ => false)) (evenExtension x) =
        (fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i)) + ((fun z : ZMod 2 => decide (z = 1)) (∑ i, x i)).toNat := by
    exact settingWeight_snoc _ _
  have parity_sum {n : ℕ} (x : Fin n → Bool) :
      ∑ i, (fun b : Bool => (b.toNat : ZMod 2)) (x i) = ((fun x => hammingDist x (fun _ => false)) x : ZMod 2) := by
    rw [settingWeight_eq_sum, Nat.cast_sum]
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
  have even_lower (k : ℕ) (hk : 1 ≤ k)
      (rho : Setting (2*k+2) → Strategy (2*k+2) → ℝ) (hfaith : Faithful rho) :
      floorValue (2*k+2) ≤ F rho := by
    have he : ((2*k+2)-1)/2=k := by omega
    have hv : floorValue (2*k+2) = (2 : ℝ)^k / (2*((2 : ℝ)^k+1)) := by
      unfold floorValue ratio
      rw [he]
      norm_cast
    rw [hv]
    apply lower_via_bent k hk (fun x => addX (evenSetting x)) ?_ ?_ rho hfaith
    · intro x
      rw [addX_target,target_eq_qFree]
    · intro lambda
      refine ⟨tableParity (Fin.init lambda) + (fun b : Bool => (b.toNat : ZMod 2)) (lambda (Fin.last (2*k+1))).1,
        lastAdjustedFrequency (Fin.init lambda),?_⟩
      intro x
      rw [addX_full_response,even_full_response,← bitSign_boolBit,← bitSign_add]
      congr 1
      simp only []
      ring
  have odd_lower (k : ℕ) (hk : 1 ≤ k)
      (rho : Setting (2*k+1) → Strategy (2*k+1) → ℝ) (hfaith : Faithful rho) :
      floorValue (2*k+1) ≤ F rho := by
    have he : ((2*k+1)-1)/2=k := by omega
    have hv : floorValue (2*k+1) = (2 : ℝ)^k / (2*((2 : ℝ)^k+1)) := by
      unfold floorValue ratio
      rw [he]
      norm_cast
    rw [hv]
    apply lower_via_bent k hk evenSetting target_eq_qFree ?_ rho hfaith
    intro lambda
    refine ⟨tableParity lambda,lastAdjustedFrequency lambda,?_⟩
    intro x
    simpa [] using even_full_response lambda x
  obtain ⟨k,hk,he⟩ : ∃ k : ℕ, 1 ≤ k ∧ (n = 2*k+1 ∨ n = 2*k+2) := by
    refine ⟨(n-1)/2,?_,?_⟩ <;> omega
  rcases he with he | he
  · subst n
    exact odd_lower k hk rho hfaith
  · subst n
    exact even_lower k hk rho hfaith


end
end D5.S3.QuantumBounds.MerminMeasurementDependence
