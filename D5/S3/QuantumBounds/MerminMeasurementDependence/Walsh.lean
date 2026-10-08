/- GID: D5/S3/QuantumBounds/MerminMeasurementDependence/Walsh
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/MerminMeasurementDependence/Walsh
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A complete quadratic has a flat Walsh spectrum in every even dimension. -/
/-
proof_shape: qFree_polar: content
escape_witness: qFree_polar: induction on d produces the complete-quadratic polar identity.
admission_basis: escape-witness
proof_shape: qFree_walsh_square: content
escape_witness: qFree_walsh_square: translation of the double Walsh sum and annihilation off the trivial radical.
admission_basis: escape-witness
proof_shape: affine_agreement_bound: content
escape_witness: affine_agreement_bound: count agreements via the signed Walsh sum and its exact squared magnitude.
admission_basis: escape-witness
Direct frozen dependencies: none.
computational_content.kind: none; general mathematical statements, not an executable API.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates
import Mathlib.Algebra.Group.AddChar

set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.QuantumBounds.MerminMeasurementDependence
noncomputable section

def qFree {d : ℕ} (x : Fin d → ZMod 2) : ZMod 2 :=
  (Nat.choose ((fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i))) 2 : ZMod 2) + ∑ i, x i

def walsh {d : ℕ} (a : Fin d → ZMod 2) : ℝ :=
  ∑ x : Fin d → ZMod 2, bitSign (qFree x + ∑ i, a i * x i)

theorem qFree_polar {d : ℕ} (x y : Fin d → ZMod 2) :
    qFree (x+y) + qFree x + qFree y =
      (∑ i, x i*y i) + (∑ i, x i)*(∑ i, y i) := by
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
  have qFree_snoc {d : ℕ} (x : Fin d → ZMod 2) (b : ZMod 2) :
      qFree (Fin.snoc x b) = qFree x + b * ((∑ i, x i) + 1) := by
    have hw : (fun x => hammingDist x (fun _ => false)) (fun i : Fin (d+1) => (fun z : ZMod 2 => decide (z = 1)) ((Fin.snoc x b : Fin (d+1) → ZMod 2) i)) =
        (fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i)) + ((fun z : ZMod 2 => decide (z = 1)) b).toNat := by
      rw [settingWeight_eq_sum,Fin.sum_univ_castSucc,settingWeight_eq_sum]
      simp only [Fin.snoc_castSucc,Fin.snoc_last]
    have hs : ((fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i)) : ZMod 2) = ∑ i, x i := by
      rw [← parity_sum]
      simp only [boolBit_bitBool]
    unfold qFree
    rw [hw,Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc,Fin.snoc_last]
    rcases bit_cases b with rfl | rfl
    · simp []
    · have hc : Nat.choose ((fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i)) + 1) 2 =
          (fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i)) + Nat.choose ((fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i))) 2 := by
        simpa using Nat.choose_succ_succ' ((fun x => hammingDist x (fun _ => false)) (fun i => (fun z : ZMod 2 => decide (z = 1)) (x i))) 1
      simp only [decide_true, Bool.toNat_true]
      rw [hc,Nat.cast_add,hs]
      ring
  induction d with
  | zero => simp [qFree,hammingDist, Bool.not_eq_false]
  | succ d ih =>
    let a : Fin d → ZMod 2 := fun i => x i.castSucc
    let b : Fin d → ZMod 2 := fun i => y i.castSucc
    have hx : x = Fin.snoc a (x (Fin.last d)) := (Fin.snoc_init_self x).symm
    have hy : y = Fin.snoc b (y (Fin.last d)) := (Fin.snoc_init_self y).symm
    have hxy : x+y = Fin.snoc (a+b) (x (Fin.last d)+y (Fin.last d)) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [a,b]
    rw [hxy,qFree_snoc,hx,hy,qFree_snoc,qFree_snoc]
    simp only [Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,
      Pi.add_apply,Finset.sum_add_distrib]
    have hi := ih a b
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2)=0 from by decide])) hi

def character {d : ℕ} (a x : Fin d → ZMod 2) : ℝ := bitSign (∑ i, a i*x i)

theorem qFree_walsh_square (k : ℕ) (a : Fin (2*k) → ZMod 2) :
    walsh a ^ 2 = (2 : ℝ)^(2*k) := by
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
  classical
  have sym (x y : Fin (2*k) → ZMod 2) : character x y=character y x := by
    unfold character
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have trans (x u : Fin (2*k) → ZMod 2) :
      bitSign (qFree x+∑ i, a i*x i)*bitSign (qFree (x+u)+∑ i, a i*(x+u) i) =
      bitSign (qFree u+∑ i, a i*u i) *
        character (fun i => u i+∑ j, u j) x := by
    unfold character
    rw [← bitSign_add,← bitSign_add]
    apply congrArg bitSign
    have hq := qFree_polar x u
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib,← Finset.mul_sum]
    have hm : (∑ i, x i*u i)=(∑ i, u i*x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hm] at hq
    have hz1 := CharTwo.add_self_eq_zero (qFree x)
    have hz2 := CharTwo.add_self_eq_zero (∑ i, a i*x i)
    linear_combination (norm := (ring_nf; simp [show (2 : ZMod 2)=0 from by decide])) hq + hz1 + hz2
  have hr (u : Fin (2*k) → ZMod 2) : (fun i => u i+∑ j, u j)=0 ↔ u=0 := by
    constructor
    · intro h
      have hc (i : Fin (2*k)) : u i=∑ j, u j := by
        have hi := congrFun h i
        change u i+(∑ j, u j)=0 at hi
        have hz := CharTwo.add_self_eq_zero (∑ j, u j)
        exact add_right_cancel (hi.trans hz.symm)
      have hs : (∑ i, u i)=0 := by
        calc
          _ = ∑ _ : Fin (2*k), ∑ j, u j := Finset.sum_congr rfl fun i hi => hc i
          _ = 0 := by simp [nsmul_eq_mul,show (2 : ZMod 2)=0 from by decide]
      funext i
      exact (hc i).trans hs
    · rintro rfl
      funext i
      simp
  unfold walsh at *
  rw [pow_two,Finset.sum_mul]
  have reindex (x : Fin (2*k) → ZMod 2) :
      bitSign (qFree x+∑ i, a i*x i) *
        (∑ y : Fin (2*k) → ZMod 2, bitSign (qFree y+∑ i, a i*y i)) =
      ∑ u : Fin (2*k) → ZMod 2,
        bitSign (qFree u+∑ i, a i*u i)*character (fun i => u i+∑ j, u j) x := by
    rw [Finset.mul_sum]
    rw [← Equiv.sum_comp (Equiv.addLeft x)]
    exact Finset.sum_congr rfl fun u hu => trans x u
  simp_rw [reindex]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,character_sum,hr]
  simp [qFree,hammingDist, Bool.not_eq_false,bitSign,boolSign]

def walshParity (k : ℕ) (a : Fin (2*k) → ZMod 2) : ZMod 2 :=
  if walsh a < 0 then 1 else 0

theorem affine_agreement_bound (k : ℕ) (b : ZMod 2) (a : Fin (2*k) → ZMod 2) :
    ((Finset.univ.filter fun x : Fin (2*k) → ZMod 2 =>
      qFree x = b + ∑ i, a i*x i).card : ℝ) ≤
      ((2 : ℝ)^(2*k)+(2 : ℝ)^k)/2 := by
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
  have boolSign_cases (b : Bool) : boolSign b = 1 ∨ boolSign b = -1 := by
    cases b <;> simp [boolSign]
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
  classical
  let A := Finset.univ.filter fun x : Fin (2*k) → ZMod 2 => qFree x=b+∑ i, a i*x i
  have point (x : Fin (2*k) → ZMod 2) :
      bitSign (qFree x+(b+∑ i, a i*x i))=if x∈A then 1 else -1 := by
    rcases bit_cases (qFree x) with hq | hq <;>
      rcases bit_cases (b+∑ i, a i*x i) with hb | hb <;>
      simp [A,hq,hb,bitSign,boolSign,show (1 : ZMod 2)+1=0 from by decide]
  have sumA : (∑ x : Fin (2*k) → ZMod 2,
      bitSign (qFree x+(b+∑ i, a i*x i)))=2*(A.card : ℝ)-(2 : ℝ)^(2*k) := by
    have hp (x : Fin (2*k) → ZMod 2) :
        (if x∈A then (1 : ℝ) else -1)=(if x∈A then 2 else 0)-1 := by
      split_ifs <;> norm_num
    simp_rw [point,hp]
    rw [Finset.sum_sub_distrib,Finset.sum_ite]
    simp [Finset.filter_mem_eq_inter,mul_comm]
  have hs : (∑ x : Fin (2*k) → ZMod 2,
      bitSign (qFree x+(b+∑ i, a i*x i)))=bitSign b*walsh a := by
    unfold walsh
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← bitSign_add]
    congr 1
    ring
  have hb := boolSign_cases ((fun z : ZMod 2 => decide (z = 1)) b)
  have hw := boolSign_cases ((fun z : ZMod 2 => decide (z = 1)) (walshParity k a))
  rw [walsh_factor] at hs
  rw [sumA] at hs
  change bitSign b=1 ∨ bitSign b= -1 at hb
  change bitSign (walshParity k a)=1 ∨ bitSign (walshParity k a)= -1 at hw
  change (A.card : ℝ) ≤ _
  rcases hb with hb | hb <;> rcases hw with hw | hw <;> rw [hb,hw] at hs <;>
    nlinarith [show 0<(2 : ℝ)^k by positivity]
end
end D5.S3.QuantumBounds.MerminMeasurementDependence
