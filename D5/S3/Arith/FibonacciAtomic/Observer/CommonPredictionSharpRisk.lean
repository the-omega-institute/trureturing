/- GID: D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionSharpRisk
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/CommonPredictionSharpRisk
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The sharp simultaneous prediction risk for the two-layer priority-teacher family. -/

import D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionSelector
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum


/-!
The common two-layer priority-teacher problem on independent complete windows.
All prefix lengths and all rare-count classes are included.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CommonPrediction

attribute [local instance] Classical.propDecidable


section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input teacher)
open scoped BigOperators
namespace SharpRisk
noncomputable section
open CommonSelector ExteriorCounts
open WordCounts (rareN)
attribute [local instance] Classical.propDecidable
private lemma rare_le {n : ℕ} (x : Input n) : rareN x ≤ n := by
  have hp (a : LiteralWindowEnd.Window) : WordCounts.rb a ≤ 1 := by cases a <;> decide
  calc
    rareN x ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum (fun i _ => hp (x i))
    _ = n := by simp

private def risk {m : ℕ} (w : ℕ → ℝ) (f : Input (m+3) → Fin 3) (t : Bool × Fin m) : ℝ :=
  ∑ x : Input (m+3), w (rareN x)*(MajorityGeometry.err (label t.1 t.2 x) (f x):ℝ)
private lemma weighted_counts {m : ℕ} (w : ℕ → ℝ) (f : Input (m+3) → Fin 3) (t : Bool × Fin m) :
    risk w f t=∑ z ∈ Finset.range (m+4), w z*(errorCount z t.1 t.2 f:ℝ) := by
  unfold risk
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.range (m+4)) (g := @rareN (m+3))
    (fun x _ => by
      simp only [Finset.mem_range]
      have h := rare_le x
      omega)
    (fun x => w (rareN x)*(MajorityGeometry.err (label t.1 t.2 x) (f x):ℝ))]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_filter]
  simp only [errorCount, Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : rareN x=z <;> simp [h]

private lemma balanced_risks {m : ℕ} (w : ℕ → ℝ) (f : Input (m+3) → Fin 3)
    (hbal : ∀ z, ∀ i j : Fin m, errorCount z false i f=errorCount z false j f ∧
      errorCount z false i f=errorCount z true j f) (t u : Bool × Fin m) :
    risk w f t=risk w f u := by
  rw [weighted_counts, weighted_counts]
  apply Finset.sum_congr rfl
  intro z hz
  congr 2
  rcases t with ⟨a,i⟩
  rcases u with ⟨b,j⟩
  cases a <;> cases b
  · exact (hbal z i j).1
  · exact (hbal z i j).2
  · exact (hbal z j i).2.symm
  · exact (hbal z i i).2.symm.trans (hbal z i j).2

private lemma point_loss {m : ℕ} (f : Input (m+3) → Fin 3) (x : Input (m+3)) :
    (∑ t : Bool × Fin m, (MajorityGeometry.err (label t.1 t.2 x) (f x):ℝ))=
      2*m-(actualVotes x (f x):ℝ) := by
  have hi (i : Fin m) :
      (MajorityGeometry.err (label true i x) (f x) : ℝ) +
        (MajorityGeometry.err (label false i x) (f x) : ℝ) =
      2 - (((if teacher (TeacherLabels.leftRoles i) x = f x then 1 else 0) +
        (if teacher (TeacherLabels.rightRoles i) x = f x then 1 else 0) : ℕ) : ℝ) := by
    by_cases hl : teacher (TeacherLabels.leftRoles i) x = f x
    <;> by_cases hr : teacher (TeacherLabels.rightRoles i) x = f x
    <;> norm_num [label, MajorityGeometry.err, hl, hr]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    actualVotes, Nat.cast_sum]
  ring

private def barrier (m : ℕ) (w : ℕ → ℝ) : ℝ :=
  (∑ x : Input (m+3), w (rareN x)*(2*m-(actualVotes x (exteriorSelector x):ℝ))) / (2*m)
private lemma total_risk {m : ℕ} (w : ℕ → ℝ) (f : Input (m+3) → Fin 3) :
    (∑ t, risk w f t)=∑ x : Input (m+3), w (rareN x)*(2*m-(actualVotes x (f x):ℝ)) := by
  unfold risk
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum, point_loss]
private lemma lower_bound {m : ℕ} (w : ℕ → ℝ) (hw : ∀ z, 0 ≤ w z)
    (f : Input (m+3) → Fin 3) :
    (∑ x : Input (m+3), w (rareN x)*(2*m-(actualVotes x (exteriorSelector x):ℝ))) ≤
      ∑ t, risk w f t := by
  have hl (x : Input (m+3)) : (2*m:ℝ)-(actualVotes x (exteriorSelector x):ℝ) ≤
      ∑ t : Bool × Fin m, (MajorityGeometry.err (label t.1 t.2 x) (f x):ℝ) := by
    rw [point_loss]
    have h := exterior_majority x (f x)
    have hr : (actualVotes x (f x):ℝ) ≤ actualVotes x (exteriorSelector x) := by exact_mod_cast h
    linarith
  calc
    _ ≤ ∑ x : Input (m+3), w (rareN x) *
        (∑ t : Bool × Fin m, (MajorityGeometry.err (label t.1 t.2 x) (f x) : ℝ)) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hl x) (hw _))
    _ = ∑ t, risk w f t := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      rfl

private theorem sharp_class_weighted (m : ℕ) (hm : 0 < m) (w : ℕ → ℝ) (hw : ∀ z, 0 ≤ w z) :
    (∃ f : Input (m+3) → Fin 3, ∀ t, risk w f t=barrier m w) ∧
    (∀ ε : ℝ, (∃ f : Input (m+3) → Fin 3, ∀ t, risk w f t ≤ ε) ↔ barrier m w ≤ ε) := by
  obtain ⟨f,hmax,hbal⟩ := uniform_mass_balanced m hm
  let t₀ : Bool × Fin m := (false,⟨0,hm⟩)
  have heq (t : Bool × Fin m) := balanced_risks w f hbal t t₀
  have hmaxeq (x : Input (m+3)) : actualVotes x (f x)=actualVotes x (exteriorSelector x) :=
    Nat.le_antisymm (exterior_majority x (f x)) (hmax x (exteriorSelector x))
  have hs : (2*m:ℝ)*risk w f t₀=
      ∑ x : Input (m+3), w (rareN x)*(2*m-(actualVotes x (exteriorSelector x):ℝ)) := by
    have hh := total_risk w f
    simp_rw [heq, hmaxeq] at hh
    simpa [Fintype.card_prod] using hh
  have hpos : (0:ℝ)<2*m := by exact_mod_cast (show 0<2*m by omega)
  have hatt (t : Bool × Fin m) : risk w f t=barrier m w := by
    rw [heq]
    unfold barrier
    exact (eq_div_iff (ne_of_gt hpos)).mpr (by simpa [mul_comm] using hs)
  refine ⟨⟨f,hatt⟩,?_⟩
  intro ε
  constructor
  · rintro ⟨g,hg⟩
    have hb := lower_bound w hw g
    have hu : (∑ t, risk w g t) ≤ (2*m:ℝ)*ε := by
      calc
        _ ≤ ∑ _t : Bool × Fin m, ε := Finset.sum_le_sum (fun t _ => hg t)
        _ = _ := by simp [Fintype.card_prod] <;> ring
    have hid : (2*m:ℝ)*barrier m w=
        ∑ x : Input (m+3), w (rareN x)*(2*m-(actualVotes x (exteriorSelector x):ℝ)) := by
      unfold barrier
      field_simp
    nlinarith
  · intro h
    exact ⟨f,fun t => (hatt t).le.trans h⟩
end
end SharpRisk
end

section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input)
open scoped BigOperators
namespace SharpRisk
noncomputable section
open WordCounts (rareN rb)
open CommonSelector ExteriorCounts
private lemma product_mass {n : ℕ} (s : ℝ) (x : Input n) :
    (∏ i, HeterogeneousTeacherSeparation.extremal s (x i))=
      s^rareN x*((1-3*s)/2)^(n-rareN x) := by
  have hpoint (a : LiteralWindowEnd.Window) :
      HeterogeneousTeacherSeparation.extremal s a=s^rb a*((1-3*s)/2)^(1-rb a) := by
    cases a <;> simp [rb, HeterogeneousTeacherSeparation.extremal]
  have hsmall (i : Fin n) : rb (x i)+(1-rb (x i))=1 := by
    cases x i <;> decide
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl (fun i _ => hsmall i)
  rw [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hs
  have hdiff : (∑ i : Fin n, (1-rb (x i)))=n-rareN x := by
    change rareN x+_ = n at hs
    omega
  simp_rw [hpoint]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, hdiff]
  rfl

private def classWeight (m : ℕ) (s : ℝ) (z : ℕ) : ℝ := s^z*((1-3*s)/2)^(m+3-z)
private def productRisk {m : ℕ} (s : ℝ) (f : Input (m+3) → Fin 3) (t : Bool × Fin m) : ℝ :=
  ∑ x : Input (m+3), (∏ i, HeterogeneousTeacherSeparation.extremal s (x i))*
    (MajorityGeometry.err (label t.1 t.2 x) (f x):ℝ)
private lemma product_risk_eq_class_risk {m : ℕ} (s : ℝ) (f : Input (m+3) → Fin 3) (t : Bool × Fin m) :
    productRisk s f t=risk (classWeight m s) f t := by
  unfold productRisk risk classWeight
  simp_rw [product_mass]
private lemma class_weight_nonneg (m : ℕ) (s : ℝ) (hs : 0 ≤ s) (hu : s ≤ 1/3) (z : ℕ) :
    0 ≤ classWeight m s z := by
  unfold classWeight
  have ha : 0 ≤ (1-3*s)/2 := by linarith
  positivity

private theorem sharp_product (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 0 < s) (hu : s ≤ 1/5) :
    (∃ f : Input (m+3) → Fin 3, ∀ t, productRisk s f t=barrier m (classWeight m s)) ∧
    (∀ ε : ℝ, (∃ f : Input (m+3) → Fin 3, ∀ t, productRisk s f t ≤ ε) ↔
      barrier m (classWeight m s) ≤ ε) := by
  simp_rw [product_risk_eq_class_risk]
  exact sharp_class_weighted m hm (classWeight m s)
    (class_weight_nonneg m s hs.le (by linarith))
end
end SharpRisk
end

section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open scoped BigOperators
namespace SharpRisk
noncomputable section
open MajorityGeometry
private def rawLoss (m k : ℕ) (q r v : Window) : ℕ :=
  min (2*m-vt m k q r v 0) (min (2*m-vt m k q r v 1) (2*m-vt m k q r v 2))
private lemma loss_first_top (m k : ℕ) (q r v : Window) :
    2*m-vt m k q r v (firstTop m k q r v)=rawLoss m k q r v := by
  have h0 := first_top_majority m k q r v 0
  have h1 := first_top_majority m k q r v 1
  have h2 := first_top_majority m k q r v 2
  have hc : firstTop m k q r v=0 ∨ firstTop m k q r v=1 ∨ firstTop m k q r v=2 := by omega
  rcases hc with hc | hc | hc <;> simp only [hc, rawLoss] at * <;> omega
private lemma loss_selector (m k : ℕ) (q r v : Window) (b : Bool) :
    2*m-vt m k q r v (selector m k q r v b)=rawLoss m k q r v := by
  have h₁ := first_top_majority m k q r v (selector m k q r v b)
  have h₂ := selector_majority m k q r v b (firstTop m k q r v)
  have he := Nat.le_antisymm h₁ h₂
  rw [he, loss_first_top]

private def anchorType : Window → Window → Window → ℕ
  | .zero, .low, .zero => 1
  | .zero, .low, .low => 1
  | .zero, .low, .middle => 1
  | .zero, .low, .ends => 1
  | .zero, .low, .high => 1
  | .zero, .ends, .zero => 1
  | .zero, .ends, .low => 3
  | .zero, .ends, .middle => 1
  | .zero, .ends, .ends => 3
  | .zero, .ends, .high => 1
  | .zero, .high, .low => 3
  | .zero, .high, .ends => 3
  | .low, .zero, .zero => 1
  | .low, .zero, .low => 1
  | .low, .zero, .middle => 1
  | .low, .zero, .ends => 1
  | .low, .zero, .high => 1
  | .low, .low, .zero => 2
  | .low, .low, .low => 2
  | .low, .low, .middle => 2
  | .low, .low, .ends => 2
  | .low, .low, .high => 2
  | .low, .middle, .zero => 1
  | .low, .middle, .low => 1
  | .low, .middle, .middle => 1
  | .low, .middle, .ends => 1
  | .low, .middle, .high => 1
  | .low, .ends, .zero => 2
  | .low, .ends, .low => 4
  | .low, .ends, .middle => 2
  | .low, .ends, .ends => 4
  | .low, .ends, .high => 2
  | .low, .high, .zero => 1
  | .low, .high, .low => 3
  | .low, .high, .middle => 1
  | .low, .high, .ends => 3
  | .low, .high, .high => 1
  | .middle, .low, .zero => 1
  | .middle, .low, .low => 1
  | .middle, .low, .middle => 1
  | .middle, .low, .ends => 1
  | .middle, .low, .high => 1
  | .middle, .ends, .zero => 1
  | .middle, .ends, .low => 3
  | .middle, .ends, .middle => 1
  | .middle, .ends, .ends => 3
  | .middle, .ends, .high => 1
  | .middle, .high, .low => 3
  | .middle, .high, .ends => 3
  | .ends, .zero, .zero => 1
  | .ends, .zero, .low => 1
  | .ends, .zero, .middle => 1
  | .ends, .zero, .ends => 1
  | .ends, .zero, .high => 1
  | .ends, .low, .zero => 4
  | .ends, .low, .low => 4
  | .ends, .low, .middle => 4
  | .ends, .low, .ends => 4
  | .ends, .low, .high => 4
  | .ends, .middle, .zero => 1
  | .ends, .middle, .low => 1
  | .ends, .middle, .middle => 1
  | .ends, .middle, .ends => 1
  | .ends, .middle, .high => 1
  | .ends, .ends, .zero => 4
  | .ends, .ends, .low => 2
  | .ends, .ends, .middle => 4
  | .ends, .ends, .ends => 2
  | .ends, .ends, .high => 4
  | .ends, .high, .zero => 1
  | .ends, .high, .low => 3
  | .ends, .high, .middle => 1
  | .ends, .high, .ends => 3
  | .ends, .high, .high => 1
  | .high, .low, .zero => 3
  | .high, .low, .low => 3
  | .high, .low, .middle => 3
  | .high, .low, .ends => 3
  | .high, .low, .high => 3
  | .high, .ends, .zero => 3
  | .high, .ends, .low => 1
  | .high, .ends, .middle => 3
  | .high, .ends, .ends => 1
  | .high, .ends, .high => 3
  | .high, .high, .low => 3
  | .high, .high, .ends => 3
  | _, _, _ => 0
private def normalLoss (m k : ℕ) (q r v : Window) : ℕ :=
  match anchorType q r v with
  | 1 => k
  | 2 => 2*min k (m-k)
  | 3 => m
  | 4 => (m-k)+min (2*k) (m-k)
  | _ => 0
set_option maxHeartbeats 1000000 in
private lemma anchor_normal (m k : ℕ) (hkm : k ≤ m) (q r v : Window) :
    rawLoss m k q r v=normalLoss m k q r v := by
  cases q <;> cases r <;> cases v <;>
    simp [rawLoss, normalLoss, anchorType, vt, aLabel, bLabel, first, last] <;> omega

private lemma anchor_loss_sum (m k : ℕ) (hkm : k ≤ m) (s : ℝ) :
    (∑ q : Window, ∑ r : Window, ∑ v : Window,
      HeterogeneousTeacherSeparation.extremal s q *
      HeterogeneousTeacherSeparation.extremal s r *
      HeterogeneousTeacherSeparation.extremal s v * (rawLoss m k q r v:ℝ)) =
      (8*s^2-8*s^3)*m+(4*s-14*s^2+4*s^3)*k+
        4*s^2*(min k (m-k):ℝ)+2*s^2*(min (2*k) (m-k):ℝ) := by
  simp_rw [anchor_normal m k hkm]
  have hsum (F : Window → ℝ) : (∑ a : Window, F a) =
      F .zero + F .low + F .middle + F .ends + F .high := by
    simp [Finset.univ, Fintype.elems, add_assoc]
  simp_rw [hsum]
  dsimp only [normalLoss, anchorType, HeterogeneousTeacherSeparation.extremal]
  simp only [Nat.cast_min, Nat.cast_sub hkm, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring
end
end SharpRisk
end

section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window last)
open scoped BigOperators Polynomial
namespace SharpRisk
noncomputable section
open WordCounts (highN hb)
private def prefixMass {m : ℕ} (s : ℝ) (p : Fin m → Window) : ℝ :=
  ∏ i, HeterogeneousTeacherSeparation.extremal s (p i)
private def prefixBw {m : ℕ} (s : ℝ) (p : Fin m → Window) : Polynomial ℝ :=
  Polynomial.C (prefixMass s p)*Polynomial.X^highN p
private lemma prefix_bw_product {m : ℕ} (s : ℝ) (p : Fin m → Window) :
    prefixBw s p=∏ i, Polynomial.C (HeterogeneousTeacherSeparation.extremal s (p i))*
      Polynomial.X^hb (p i) := by
  unfold prefixBw prefixMass highN
  rw [map_prod, ←Finset.prod_pow_eq_pow_sum, Finset.prod_mul_distrib]
private lemma prefix_generating (m : ℕ) (s : ℝ) :
    (∑ p : Fin m → Window, prefixBw s p)=
      (Polynomial.C (1-2*s)+Polynomial.C (2*s)*Polynomial.X)^m := by
  simp_rw [prefix_bw_product]
  rw [←Fintype.prod_sum (fun (_ : Fin m) (a : Window) =>
    Polynomial.C (HeterogeneousTeacherSeparation.extremal s a) * Polynomial.X^hb a)]
  have hl : (∑ a : Window, Polynomial.C (HeterogeneousTeacherSeparation.extremal s a)*
      Polynomial.X^hb a)=Polynomial.C (1-2*s)+Polynomial.C (2*s)*Polynomial.X := by
    have he : ((1-3*s)/2)+((1-3*s)/2)+s=1-2*s := by ring
    have hh : s+s=2*s := by ring
    calc
      _ = Polynomial.C (((1-3*s)/2)+((1-3*s)/2)+s)+
          Polynomial.C (s+s)*Polynomial.X := by
        have hsum (F : Window → Polynomial ℝ) : (∑ a : Window, F a) =
            F .zero + F .low + F .middle + F .ends + F .high := by
          simp [Finset.univ, Fintype.elems, add_assoc]
        rw [hsum]
        change Polynomial.C ((1-3*s)/2)*Polynomial.X^0 +
            Polynomial.C s*Polynomial.X^0 +
            Polynomial.C ((1-3*s)/2)*Polynomial.X^0 + Polynomial.C s*Polynomial.X^1 +
            Polynomial.C s*Polynomial.X^1 = _
        simp only [pow_zero, pow_one, mul_one, map_add]
        ring
      _ = _ := by rw [he, hh]
  simp_rw [hl]
  simp

private def binomialMass (m k : ℕ) (s : ℝ) : ℝ :=
  (m.choose k:ℝ)*(2*s)^k*(1-2*s)^(m-k)
private lemma prefix_binomial (m k : ℕ) (s : ℝ) :
    (∑ p : Fin m → Window, if highN p=k then prefixMass s p else 0)=binomialMass m k s := by
  classical
  have hs := congrArg (fun P : Polynomial ℝ => P.coeff k) (prefix_generating m s)
  rw [Polynomial.finsetSum_coeff] at hs
  have hc : (Polynomial.C (1-2*s)+Polynomial.C (2*s)*Polynomial.X)^m=
      ((Polynomial.X+Polynomial.C (1-2*s))^m).comp (Polynomial.C (2*s)*Polynomial.X) := by
    simp only [Polynomial.pow_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
    rw [add_comm]
  rw [hc, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_X_add_C_pow] at hs
  calc
    _ = ∑ p : Fin m → Window, (prefixBw s p).coeff k := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases h : highN p=k
      · simp [prefixBw, Polynomial.coeff_C_mul_X_pow, h]
      · simp [prefixBw, Polynomial.coeff_C_mul_X_pow, h, Ne.symm h]
    _ = _ := by rw [hs]; unfold binomialMass; ring
private lemma prefix_total (m : ℕ) (s : ℝ) : (∑ p : Fin m → Window, prefixMass s p)=1 := by
  have hs := congrArg (fun P : Polynomial ℝ => P.eval 1) (prefix_generating m s)
  simpa [prefixBw, Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_mul,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X] using hs
private lemma prefix_mean (m : ℕ) (s : ℝ) :
    (∑ p : Fin m → Window, prefixMass s p*(highN p:ℝ))=(m:ℝ)*(2*s) := by
  have hs := congrArg (fun P : Polynomial ℝ => P.derivative.eval 1) (prefix_generating m s)
  simpa [prefixBw, Polynomial.derivative_sum, Polynomial.eval_finsetSum,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_add,
    Polynomial.derivative_C, Polynomial.derivative_X] using hs
private lemma prefix_expectation (m : ℕ) (s : ℝ) (F : ℕ → ℝ) :
    (∑ p : Fin m → Window, prefixMass s p*F (highN p))=
      ∑ k ∈ Finset.range (m+1), binomialMass m k s*F k := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.range (m+1)) (g := @highN m)
    (fun p _ => by
      simp only [Finset.mem_range]
      have h := WordCounts.high_n_le p
      omega)
    (fun p => prefixMass s p*F (highN p))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_filter, ← prefix_binomial m k s, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : highN p=k <;> simp [h]

end
end SharpRisk
end

section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window)
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input)
open scoped BigOperators
namespace SharpRisk
noncomputable section
open MajorityGeometry ExteriorCounts
open WordCounts (highN rareN)
private lemma vt_le (m k : ℕ) (hkm : k ≤ m) (q r v : Window) (c : Fin 3) :
    vt m k q r v c ≤ 2*m := by
  have ha : (if aLabel false q r=c then 1 else 0)+(if bLabel false r v=c then 1 else 0) ≤ 2 := by
    split_ifs <;> omega
  have hb : (if aLabel true q r=c then 1 else 0)+(if bLabel true r v=c then 1 else 0) ≤ 2 := by
    split_ifs <;> omega
  unfold vt
  have hm : m-k+k=m := Nat.sub_add_cancel hkm
  nlinarith [Nat.mul_le_mul_left (m-k) ha, Nat.mul_le_mul_left k hb]
private lemma loss_real_append {m : ℕ} (p : Fin m → Window) (q r v : Window) :
    (2*m:ℝ)-(actualVotes (Fin.append p ![q,r,v])
      (exteriorSelector (Fin.append p ![q,r,v])):ℝ)=(rawLoss m (highN p) q r v:ℝ) := by
  rw [actual_votes_append, exterior_append]
  let b := if highN p=0 then anchorCoin q r v else WordCounts.prefixCoin p
  have hc := congrArg (fun a : ℕ => (a:ℝ)) (loss_selector m (highN p) q r v b)
  rw [Nat.cast_sub (vt_le m (highN p) (WordCounts.high_n_le p) q r v _)] at hc
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hc
private lemma mass_append {m : ℕ} (s : ℝ) (p : Fin m → Window) (q r v : Window) :
    (∏ i, HeterogeneousTeacherSeparation.extremal s (Fin.append p ![q,r,v] i))=
      prefixMass s p*HeterogeneousTeacherSeparation.extremal s q*
        HeterogeneousTeacherSeparation.extremal s r*HeterogeneousTeacherSeparation.extremal s v := by
  simp [Fin.prod_univ_add, Fin.prod_univ_three, prefixMass, mul_assoc]
private lemma word_sum_real (m : ℕ) (F : Input (m+3) → ℝ) :
    (∑ x, F x)=∑ p : Fin m → Window, ∑ q : Window, ∑ r : Window, ∑ v : Window,
      F (Fin.append p ![q,r,v]) := by
  have h := Equiv.sum_comp (wordEquiv m).symm F
  change (∑ t : (Fin m → Window) × Window × Window × Window,
    F (Fin.append t.1 ![t.2.1,t.2.2.1,t.2.2.2]))=∑ x, F x at h
  simpa only [Fintype.sum_prod_type] using h.symm

private def numerator (m : ℕ) (s : ℝ) : ℝ :=
  ∑ x : Input (m+3), classWeight m s (rareN x)*(2*m-(actualVotes x (exteriorSelector x):ℝ))
private lemma numerator_nested (m : ℕ) (s : ℝ) :
    numerator m s=∑ p : Fin m → Window, prefixMass s p*(
      ∑ q : Window, ∑ r : Window, ∑ v : Window,
        HeterogeneousTeacherSeparation.extremal s q*
        HeterogeneousTeacherSeparation.extremal s r*
        HeterogeneousTeacherSeparation.extremal s v*(rawLoss m (highN p) q r v:ℝ)) := by
  unfold numerator classWeight
  simp_rw [←product_mass s]
  rw [word_sum_real]
  simp_rw [mass_append, loss_real_append]
  apply Finset.sum_congr rfl
  intro p hp
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro v hv
  ring

private def G (m k : ℕ) : ℝ := 2*(min k (m-k):ℝ)+(min (2*k) (m-k):ℝ)
/-- Sharp common prediction threshold, including the complete binomial correction. -/
def T (m : ℕ) (s : ℝ) : ℝ :=
  8*s^2-18*s^3+4*s^4+(s^2/m)*(∑ k ∈ Finset.range (m+1), binomialMass m k s*G m k)
private lemma numerator_formula (m : ℕ) (s : ℝ) :
    numerator m s=2*m*(8*s^2-18*s^3+4*s^4)+
      2*s^2*(∑ k ∈ Finset.range (m+1), binomialMass m k s*G m k) := by
  rw [numerator_nested]
  simp_rw [anchor_loss_sum m _ (WordCounts.high_n_le _) s]
  calc
    _ = ((8*s^2-8*s^3)*m)*(∑ p : Fin m → Window, prefixMass s p)+
        (4*s-14*s^2+4*s^3)*(∑ p : Fin m → Window, prefixMass s p*(highN p:ℝ))+
        2*s^2*(∑ p : Fin m → Window, prefixMass s p*G m (highN p)) := by
      simp_rw [Finset.mul_sum]
      rw [←Finset.sum_add_distrib, ←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      unfold G
      ring
    _ = _ := by rw [prefix_total, prefix_mean, prefix_expectation]; ring
private lemma barrier_eq_t (m : ℕ) (hm : 0 < m) (s : ℝ) :
    barrier m (classWeight m s)=T m s := by
  change numerator m s/(2*m)=T m s
  rw [numerator_formula]
  unfold T
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  field_simp [hm0] <;> ring

private theorem sharp_risk_reduced (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 0 < s) (hu : s ≤ 1/5) :
    (∃ f : Input (m+3) → Fin 3, ∀ t, productRisk s f t=T m s) ∧
    (∀ ε : ℝ, (∃ f : Input (m+3) → Fin 3, ∀ t, productRisk s f t ≤ ε) ↔ T m s ≤ ε) := by
  simpa only [barrier_eq_t m hm s] using sharp_product m hm s hs hu
end
end SharpRisk
end

section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window)
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input)
open scoped BigOperators
namespace SharpRisk
noncomputable section
open CommonSelector ExteriorCounts
attribute [local instance] Classical.propDecidable
variable {m : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
local notation "Unused" e => ({j : J // j ∉ Set.range e})
private def indexEquiv (e : Fin (m+3) ↪ J) : Fin (m+3) ⊕ Unused e ≃ J :=
  (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun j => j ∈ Set.range e))
private def splitWord (e : Fin (m+3) ↪ J) : (J → Window) ≃ Input (m+3) × (Unused e → Window) :=
  (Equiv.arrowCongr (indexEquiv e).symm (Equiv.refl Window)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)
private lemma join_inl (e : Fin (m+3) ↪ J) (xy : Input (m+3) × (Unused e → Window)) (i : Fin (m+3)) :
    (splitWord e).symm xy (e i)=xy.1 i := by
  change Sum.elim xy.1 xy.2 ((indexEquiv e).symm ((indexEquiv e) (Sum.inl i))) = _
  rw [Equiv.symm_apply_apply]
  rfl
private lemma join_inr (e : Fin (m+3) ↪ J) (xy : Input (m+3) × (Unused e → Window)) (j : Unused e) :
    (splitWord e).symm xy j.val=xy.2 j := by
  change Sum.elim xy.1 xy.2 ((indexEquiv e).symm ((indexEquiv e) (Sum.inr j))) = _
  rw [Equiv.symm_apply_apply]
  rfl
private lemma join_core (e : Fin (m+3) ↪ J) (xy : Input (m+3) × (Unused e → Window)) :
    ((splitWord e).symm xy) ∘ e=xy.1 := by funext i; exact join_inl e xy i

/-- Product of the common five-window masses over every coordinate. -/
def lawMass {I : Type*} [Fintype I] (s : ℝ) (x : I → Window) : ℝ :=
  ∏ i, HeterogeneousTeacherSeparation.extremal s (x i)
private lemma mass_sum (I : Type*) [Fintype I] [DecidableEq I] (s : ℝ) :
    (∑ x : I → Window, lawMass s x)=1 := by
  unfold lawMass
  rw [←Fintype.prod_sum]
  have hl : (∑ a : Window, HeterogeneousTeacherSeparation.extremal s a)=1 := by
    simp [HeterogeneousTeacherSeparation.extremal, Finset.univ, Fintype.elems]
    ring
  simp_rw [hl]
  simp
private lemma law_mass_nonneg {I : Type*} [Fintype I] (s : ℝ) (hs : 0 ≤ s) (hu : s ≤ 1/3)
    (x : I → Window) : 0 ≤ lawMass s x := by
  apply Finset.prod_nonneg
  intro i hi
  cases x i <;> simp only [HeterogeneousTeacherSeparation.extremal] <;> linarith
private lemma mass_join (e : Fin (m+3) ↪ J) (s : ℝ) (xy : Input (m+3) × (Unused e → Window)) :
    lawMass s ((splitWord e).symm xy)=lawMass s xy.1*lawMass s xy.2 := by
  unfold lawMass
  rw [←Equiv.prod_comp (indexEquiv e) (fun j => HeterogeneousTeacherSeparation.extremal s ((splitWord e).symm xy j))]
  rw [Fintype.prod_sum_type]
  change (∏ i, HeterogeneousTeacherSeparation.extremal s ((splitWord e).symm xy (e i))) *
    (∏ j : Unused e, HeterogeneousTeacherSeparation.extremal s
      ((splitWord e).symm xy j.val)) = _
  simp only [join_inl, join_inr]
private lemma full_sum (e : Fin (m+3) ↪ J) (F : (J → Window) → ℝ) :
    (∑ x, F x)=∑ a : Input (m+3), ∑ b : Unused e → Window, F ((splitWord e).symm (a,b)) := by
  have h := Equiv.sum_comp (splitWord e).symm F
  simpa only [Fintype.sum_prod_type] using h.symm
private lemma marginalize (e : Fin (m+3) ↪ J) (s : ℝ) (F : Input (m+3) → ℝ) :
    (∑ x : J → Window, lawMass s x*F (x ∘ e))=
      ∑ a : Input (m+3), lawMass s a*F a := by
  classical
  rw [full_sum e]
  simp_rw [mass_join, join_core]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    _ = (lawMass s a*F a)*(∑ b : Unused e → Window, lawMass s b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = _ := by rw [mass_sum]; ring

private def fullRisk (e : Fin (m+3) ↪ J) (s : ℝ) (f : (J → Window) → Fin 3) (t : Bool × Fin m) : ℝ :=
  ∑ x : J → Window, lawMass s x*(MajorityGeometry.err (label t.1 t.2 (x ∘ e)) (f x):ℝ)
private lemma full_risk_lift (e : Fin (m+3) ↪ J) (s : ℝ) (f : Input (m+3) → Fin 3) (t : Bool × Fin m) :
    fullRisk e s (fun x => f (x ∘ e)) t=productRisk s f t := by
  exact marginalize e s (fun a => (MajorityGeometry.err (label t.1 t.2 a) (f a):ℝ))
private lemma full_lower (e : Fin (m+3) ↪ J) (s : ℝ) (hs : 0 ≤ s) (hu : s ≤ 1/3)
    (f : (J → Window) → Fin 3) : numerator m s ≤ ∑ t, fullRisk e s f t := by
  have hmarg := marginalize e s (fun a => (2*m:ℝ)-(actualVotes a (exteriorSelector a):ℝ))
  have hnum : numerator m s=∑ x : J → Window,
      lawMass s x*((2*m:ℝ)-(actualVotes (x ∘ e) (exteriorSelector (x ∘ e)):ℝ)) := by
    rw [hmarg]
    unfold numerator lawMass classWeight
    simp_rw [product_mass]
  rw [hnum]
  have hl (x : J → Window) : (2*m:ℝ)-(actualVotes (x ∘ e) (exteriorSelector (x ∘ e)):ℝ) ≤
      ∑ t : Bool × Fin m, (MajorityGeometry.err (label t.1 t.2 (x ∘ e)) (f x):ℝ) := by
    have h := point_loss (fun _ => f x) (x ∘ e)
    rw [h]
    have hb := exterior_majority (x ∘ e) (f x)
    have hbr : (actualVotes (x ∘ e) (f x):ℝ) ≤ actualVotes (x ∘ e) (exteriorSelector (x ∘ e)) := by
      exact_mod_cast hb
    linarith
  calc
    _ ≤ ∑ x : J → Window, lawMass s x*
        (∑ t : Bool × Fin m, (MajorityGeometry.err (label t.1 t.2 (x ∘ e)) (f x):ℝ)) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hl x)
        (law_mass_nonneg s hs hu x))
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      rfl

private theorem sharp_with_unused (e : Fin (m+3) ↪ J) (hm : 0 < m) (s : ℝ) (hs : 0 < s) (hu : s ≤ 1/5) :
    (∃ f : (J → Window) → Fin 3, ∀ t, fullRisk e s f t=T m s) ∧
    (∀ ε : ℝ, (∃ f : (J → Window) → Fin 3, ∀ t, fullRisk e s f t ≤ ε) ↔ T m s ≤ ε) := by
  obtain ⟨⟨f,hf⟩,_⟩ := sharp_risk_reduced m hm s hs hu
  have hpos : (0:ℝ)<2*m := by exact_mod_cast (show 0<2*m by omega)
  have hT : numerator m s=(2*m:ℝ)*T m s := by
    have h := barrier_eq_t m hm s
    change numerator m s/(2*m)=T m s at h
    exact (div_eq_iff (ne_of_gt hpos)).mp h |>.trans (mul_comm _ _)
  have hatt (t : Bool × Fin m) : fullRisk e s (fun x => f (x ∘ e)) t=T m s := by
    rw [full_risk_lift]
    exact hf t
  refine ⟨⟨_,hatt⟩,?_⟩
  intro ε
  constructor
  · rintro ⟨g,hg⟩
    have hb := full_lower e s hs.le (by linarith) g
    have hu : (∑ t, fullRisk e s g t) ≤ (2*m:ℝ)*ε := by
      calc
        _ ≤ ∑ _t : Bool × Fin m, ε := Finset.sum_le_sum (fun t _ => hg t)
        _ = _ := by simp [Fintype.card_prod] <;> ring
    rw [hT] at hb
    nlinarith
  · intro h
    exact ⟨_,fun t => (hatt t).le.trans h⟩
end
end SharpRisk
end

section
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window)
open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher (Input Roles teacher)
open scoped BigOperators
namespace SharpRisk
noncomputable section
open CommonSelector
attribute [local instance] Classical.propDecidable

private def coreEmbedding {n : ℕ} (q r v : Fin n) (qr : q < r) (rv : r < v) : Fin (q.val+3) ↪ Fin n where
  toFun i := if h : i.val < q.val then ⟨i.val,lt_trans h q.isLt⟩ else
    if i.val=q.val then q else if i.val=q.val+1 then r else v
  inj' := by
    intro i j hij
    apply Fin.ext
    have hqr : q.val<r.val := qr
    have hrv : r.val<v.val := rv
    have hi := i.isLt
    have hj := j.isLt
    dsimp only at hij
    split_ifs at hij <;> have hv := congrArg Fin.val hij <;>
      try dsimp only at hv
    all_goals omega

/-- A left-layer teacher at arbitrary ordered anchors in the full input. -/
def leftGapped {n : ℕ} (q r : Fin n) (qr : q < r) (i : Fin q.val) : Roles n where
  p := ⟨i.val,lt_trans i.isLt q.isLt⟩
  q := q
  r := r
  pq := i.isLt
  qr := qr

/-- A right-layer teacher at arbitrary ordered anchors in the full input. -/
def rightGapped {n : ℕ} (q r v : Fin n) (qr : q < r) (rv : r < v) (i : Fin q.val) : Roles n where
  p := ⟨i.val,lt_trans i.isLt q.isLt⟩
  q := r
  r := v
  pq := lt_trans i.isLt qr
  qr := rv

private lemma left_restrict {n : ℕ} (q r v : Fin n) (qr : q < r) (rv : r < v)
    (i : Fin q.val) (x : Input n) :
    teacher (TeacherLabels.leftRoles i) (x ∘ coreEmbedding q r v qr rv)=teacher (leftGapped q r qr i) x := by
  have he (j : Fin (q.val+3)) : coreEmbedding q r v qr rv j =
      (if h : j.val < q.val then ⟨j.val, lt_trans h q.isLt⟩ else
        if j.val=q.val then q else if j.val=q.val+1 then r else v) := rfl
  simp [teacher, LegalPriorityTeacher.gate, TeacherLabels.leftRoles, leftGapped,
    Function.comp_def, he, i.isLt]
private lemma right_restrict {n : ℕ} (q r v : Fin n) (qr : q < r) (rv : r < v)
    (i : Fin q.val) (x : Input n) :
    teacher (TeacherLabels.rightRoles i) (x ∘ coreEmbedding q r v qr rv)=teacher (rightGapped q r v qr rv i) x := by
  have he (j : Fin (q.val+3)) : coreEmbedding q r v qr rv j =
      (if h : j.val < q.val then ⟨j.val, lt_trans h q.isLt⟩ else
        if j.val=q.val then q else if j.val=q.val+1 then r else v) := rfl
  simp [teacher, LegalPriorityTeacher.gate, TeacherLabels.rightRoles, rightGapped,
    Function.comp_def, he, i.isLt]

/-- Original zero-one teacher risk under the full independent complete-window law. -/
def gappedRisk {n : ℕ} (q r v : Fin n) (qr : q < r) (rv : r < v) (s : ℝ)
    (f : Input n → Fin 3) (t : Bool × Fin q.val) : ℝ :=
  ∑ x : Input n, lawMass s x*(MajorityGeometry.err
    (if t.1 then teacher (rightGapped q r v qr rv t.2) x else teacher (leftGapped q r qr t.2) x) (f x):ℝ)
private lemma full_risk_eq_gapped {n : ℕ} (q r v : Fin n) (qr : q < r) (rv : r < v) (s : ℝ)
    (f : Input n → Fin 3) (t : Bool × Fin q.val) :
    fullRisk (coreEmbedding q r v qr rv) s f t=gappedRisk q r v qr rv s f t := by
  unfold fullRisk gappedRisk label
  simp_rw [left_restrict, right_restrict]

/-- One classifier attains the same sharp risk for all teachers; every classifier meets the worst-teacher bound. -/
theorem sharp_risk_full {n : ℕ} (q r v : Fin n) (hq : 0 < q.val) (qr : q < r) (rv : r < v)
    (s : ℝ) (hs : 0 < s) (hu : s ≤ 1/5) :
    (∃ f : Input n → Fin 3, ∀ t, gappedRisk q r v qr rv s f t=T q.val s) ∧
    (∀ f : Input n → Fin 3, ∃ t, T q.val s ≤ gappedRisk q r v qr rv s f t) ∧
    (∀ ε : ℝ, (∃ f : Input n → Fin 3, ∀ t, gappedRisk q r v qr rv s f t ≤ ε) ↔ T q.val s ≤ ε) := by
  have h := sharp_with_unused (coreEmbedding q r v qr rv) hq s hs hu
  simp_rw [full_risk_eq_gapped] at h
  refine ⟨h.1,?_,h.2⟩
  intro f
  letI : Nonempty (Fin q.val) := ⟨⟨0,hq⟩⟩
  obtain ⟨t,ht,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Bool × Fin q.val))
    (gappedRisk q r v qr rv s f) Finset.univ_nonempty
  refine ⟨t,(h.2 _).mp ⟨f,?_⟩⟩
  intro u
  exact hmax u (Finset.mem_univ u)
end
end SharpRisk
end

end D5.S3.Arith.FibonacciAtomic.CommonPrediction
