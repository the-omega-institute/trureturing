import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactMaskCut

/-! Signed Huang pair operators along alternating contact walks. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ThreeMaskCutSign

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip IsBalanced)
open BalancedCubeGirth (flip_comm)
open Q9IsotropicHuang (flipSign parity weightedLinear)
open Q9WeightedSaturation (defect signedBiadjacency)
open Placement.Q9ContactMaskCut (cutMasks)
open private cutPairs mask translate translate_comm cutMasks_swap contact_of_mask parity_translate
  two_contact_row cutTerm other_contact_of_three_mask_cut no_alternating_square_of_small_cut
  transport_from_companion from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactMaskCut
open private direction direction_apply direction_square direction_anticommute from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang

/-- A crossing pair oriented from the axis shore `A` to its complement. -/
abbrev CrossingPair (A : Set (Fin 9)) :=
  {p : Fin 9 × Fin 9 // p.1 ∈ A ∧ p.2 ∉ A}

namespace CrossingPair

variable {R : Type*} [CommRing R] {A : Set (Fin 9)}

local notation "D" => (direction (R := R))

def operator (p : CrossingPair A) : Module.End R (Q 9 → R) := D p.1.1 * D p.1.2

private theorem right_ne_left (p q : CrossingPair A) : p.1.2 ≠ q.1.1 := by
  intro h
  apply p.2.2
  rw [h]
  exact q.2.1

private theorem direction_swap {i j : Fin 9} (h : i ≠ j) :
    D i * D j = -(D j * D i) := by
  simpa only [add_assoc, add_neg_cancel, add_zero, zero_add] using
    congrArg (fun z : Module.End R (Q 9 → R) => z + -(D j * D i))
      (direction_anticommute (R := R) h)

private theorem direction_pair_same_first {i j k : Fin 9} (h : j ≠ i) :
    (D i * D j) * (D i * D k) = -(D j * D k) := by
  calc
    _ = D i * ((D j * D i) * D k) := by simp only [mul_assoc]
    _ = -((D i * D i) * (D j * D k)) := by
      simp only [direction_swap (R := R) h, neg_mul, mul_neg, mul_assoc]
    _ = _ := by rw [direction_square, one_mul]

private theorem direction_pair_same_second {i j k : Fin 9} (h : j ≠ k) :
    (D i * D j) * (D k * D j) = -(D i * D k) := by
  calc
    _ = D i * ((D j * D k) * D j) := by simp only [mul_assoc]
    _ = -((D i * D k) * (D j * D j)) := by
      simp only [direction_swap (R := R) h, neg_mul, mul_neg, mul_assoc]
    _ = _ := by rw [direction_square, mul_one]

private theorem direction_mul_pair {i j k : Fin 9} (hij : i ≠ j) (hik : i ≠ k) :
    D i * (D j * D k) = (D j * D k) * D i := by
  calc
    _ = (D i * D j) * D k := (mul_assoc _ _ _).symm
    _ = -(D j * (D i * D k)) := by
      rw [direction_swap (R := R) hij, neg_mul, mul_assoc]
    _ = _ := by
      rw [direction_swap (R := R) hik]
      simp only [mul_neg, neg_neg, mul_assoc]

theorem operator_square (p : CrossingPair A) :
    operator (R := R) p * operator p = -1 := by
  unfold operator
  rw [direction_pair_same_first (R := R) (right_ne_left p p), direction_square]

/-- For oriented pairs, inequalities on the two corresponding shores imply disjointness. -/
theorem operator_commute (p q : CrossingPair A)
    (hl : p.1.1 ≠ q.1.1) (hr : p.1.2 ≠ q.1.2) :
    operator (R := R) p * operator q = operator q * operator p := by
  unfold operator
  calc
    _ = D p.1.1 * (D p.1.2 * (D q.1.1 * D q.1.2)) := mul_assoc _ _ _
    _ = ((D q.1.1 * D q.1.2) * D p.1.1) * D p.1.2 := by
      rw [direction_mul_pair (R := R) (right_ne_left p q) hr,
        ← mul_assoc (D p.1.1) (D q.1.1 * D q.1.2) (D p.1.2),
        direction_mul_pair (R := R) hl (right_ne_left q p).symm]
    _ = _ := mul_assoc _ _ _

/-- Distinct oriented pairs share exactly one axis if a corresponding endpoint agrees. -/
theorem operator_anticommute (p q : CrossingPair A) (hne : p ≠ q)
    (h : p.1.1 = q.1.1 ∨ p.1.2 = q.1.2) :
    operator (R := R) p * operator q = -(operator q * operator p) := by
  rcases h with hl | hr
  · have hr : p.1.2 ≠ q.1.2 := fun hr => hne (Subtype.ext (Prod.ext hl hr))
    simp only [operator, ← hl]
    rw [direction_pair_same_first (R := R) (right_ne_left p p),
      direction_pair_same_first (R := R) (right_ne_left q p), direction_swap (R := R) hr]
  · have hl : p.1.1 ≠ q.1.1 := fun hl => hne (Subtype.ext (Prod.ext hl hr))
    simp only [operator, ← hr]
    rw [direction_pair_same_second (R := R) (right_ne_left p q),
      direction_pair_same_second (R := R) (right_ne_left p p), direction_swap (R := R) hl]

/-- The sign incurred by exchanging the operators of distinct crossing pairs. -/
def exchangeSign (p q : CrossingPair A) : R :=
  if p.1.1 = q.1.1 ∨ p.1.2 = q.1.2 then -1 else 1

theorem operator_exchange (p q : CrossingPair A) (hne : p ≠ q) :
    operator (R := R) p * operator q =
      exchangeSign (R := R) p q • (operator q * operator p) := by
  by_cases h : p.1.1 = q.1.1 ∨ p.1.2 = q.1.2
  · simpa only [exchangeSign, ite_eq_left h, neg_one_smul] using
      operator_anticommute (R := R) p q hne h
  · have hl : p.1.1 ≠ q.1.1 := fun e => h (Or.inl e)
    have hr : p.1.2 ≠ q.1.2 := fun e => h (Or.inr e)
    simpa only [exchangeSign, ite_eq_right h, one_smul] using operator_commute (R := R) p q hl hr

/-- The square of the operator word for the cycle order `p,r,q,p,r,q`. -/
theorem operator_cycle_square (p r q : CrossingPair A) (hqp : q ≠ p) (hrp : r ≠ p)
    (hqr : q ≠ r) :
    (operator (R := R) p * operator r * operator q) ^ 2 =
      -(exchangeSign (R := R) q p * (exchangeSign r p * exchangeSign q r)) •
        (1 : Module.End R (Q 9 → R)) := by
  let P := operator (R := R) p
  let T := operator (R := R) r
  let Q' := operator (R := R) q
  let a : R := exchangeSign q p
  let b : R := exchangeSign r p
  let c : R := exchangeSign q r
  have hQP : Q' * P = a • (P * Q') := operator_exchange q p hqp
  have hTP : T * P = b • (P * T) := operator_exchange r p hrp
  have hQT : Q' * T = c • (T * Q') := operator_exchange q r hqr
  change (P * T * Q') ^ 2 = -(a * (b * c)) • (1 : Module.End R (Q 9 → R))
  calc
    _ = P * (T * ((Q' * P) * (T * Q'))) := by simp only [pow_two, mul_assoc]
    _ = a • (P * ((T * P) * ((Q' * T) * Q'))) := by
      rw [hQP]
      simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
    _ = (a * (b * c)) • ((P * P) * ((T * T) * (Q' * Q'))) := by
      rw [hTP, hQT]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc, mul_comm c b]
    _ = _ := by
      have hP : P * P = -1 := operator_square p
      have hT : T * T = -1 := operator_square r
      have hQ : Q' * Q' = -1 := operator_square q
      rw [hP, hT, hQ]
      simp only [mul_neg, mul_one, neg_neg, smul_neg, neg_smul]

end CrossingPair

open CrossingPair

private def step {A : Set (Fin 9)} (p : CrossingPair A) (x : Q 9) : Q 9 :=
  flip (flip x p.1.1) p.1.2

private theorem step_involution {A : Set (Fin 9)} (p : CrossingPair A) (x : Q 9) :
    step p (step p x) = x := by
  unfold step
  rw [flip_comm (flip x p.1.1) p.1.2 p.1.1,
    BalancedCriticalSpectrum.flip_flip, BalancedCriticalSpectrum.flip_flip]

private theorem step_comm {A : Set (Fin 9)} (p q : CrossingPair A) (x : Q 9) :
    step p (step q x) = step q (step p x) := by
  unfold step
  rw [flip_comm (flip x q.1.1) q.1.2 p.1.1, flip_comm x q.1.1 p.1.1,
    flip_comm (flip (flip x p.1.1) q.1.1) q.1.2 p.1.2,
    flip_comm (flip x p.1.1) q.1.1 p.1.2]

private def coefficient {A : Set (Fin 9)} (p : CrossingPair A) (x : Q 9) : ℝ :=
  (flipSign p.1.1 x : ℝ) * (flipSign p.1.2 (flip x p.1.1) : ℝ)

private theorem operator_eval {A : Set (Fin 9)} (p : CrossingPair A) (g : Q 9 → ℝ) (x : Q 9) :
    operator p g x = coefficient p x * g (step p x) := by
  simp only [operator, Module.End.mul_apply, direction_apply, mul_assoc, coefficient, step]

private theorem operator_congr_at {A : Set (Fin 9)} (p : CrossingPair A) (x : Q 9)
    {f g : Q 9 → ℝ} (h : f (step p x) = g (step p x)) :
    operator p f x = operator p g x := by
  simp only [operator_eval, h]

private theorem return_of_zero_row {A : Set (Fin 9)} (p q : CrossingPair A)
    (g : Q 9 → ℝ) (x : Q 9) (h : operator (R := ℝ) p g x + operator (R := ℝ) q g x = 0) :
    (operator (R := ℝ) p * operator (R := ℝ) q) g (step p x) = g (step p x) := by
  have hn : operator (R := ℝ) q g x = -operator (R := ℝ) p g x := by linarith only [h]
  calc
    _ = -((operator (R := ℝ) p * operator (R := ℝ) p) g (step p x)) := by
      simp only [Module.End.mul_apply, operator_eval p _ (step p x), step_involution, hn, mul_neg]
    _ = _ := by rw [operator_square]; simp

/-- Three two-term cancelling rows along the alternating walk force the
product of the three exchange signs to be minus one. The returning
two-edge operators fix the nonzero switching amplitude at the first
opposite-shore vertex. -/
theorem exchange_sign_product_of_zero_rows
    {A : Set (Fin 9)} (p r q : CrossingPair A) (hpr : p ≠ r) (hpq : p ≠ q) (hrq : r ≠ q)
    (g : Q 9 → ℝ) (x : Q 9) (hg : g (step p x) ≠ 0)
    (h₀ : operator (R := ℝ) q g x + operator (R := ℝ) p g x = 0)
    (h₂ : let z := step r (step p x)
      operator (R := ℝ) r g z + operator (R := ℝ) q g z = 0)
    (h₄ : let z := step p (step q (step r (step p x)))
      operator (R := ℝ) p g z + operator (R := ℝ) r g z = 0) :
    exchangeSign (R := ℝ) p r * (exchangeSign q r * exchangeSign p q) = -1 := by
  let y₁ := step p x
  let x₂ := step r y₁
  let y₃ := step q x₂
  let x₄ := step p y₃
  let y₅ := step r x₄
  have h₁ : (operator (R := ℝ) r * operator (R := ℝ) q) g y₁ = g y₁ := by
    simpa only [x₂, step_involution] using return_of_zero_row r q g x₂ h₂
  have h₃ : (operator (R := ℝ) p * operator (R := ℝ) r) g y₃ = g y₃ := by
    simpa only [x₄, step_involution] using return_of_zero_row p r g x₄ h₄
  have hclose : step q x = y₅ := by
    change step q x = step r (step p (step q (step r (step p x))))
    rw [step_comm r p, step_comm r q, step_involution, step_comm p q, step_involution]
  have h₅ : (operator (R := ℝ) q * operator (R := ℝ) p) g y₅ = g y₅ :=
    hclose ▸ return_of_zero_row q p g x h₀
  have hcycle : ((operator (R := ℝ) r * operator (R := ℝ) q * operator (R := ℝ) p) ^ 2) g y₁ = g y₁ := by
    calc
      _ = ((operator (R := ℝ) r * operator (R := ℝ) q) * (operator (R := ℝ) p * operator (R := ℝ) r) *
        (operator (R := ℝ) q * operator (R := ℝ) p)) g y₁ := by
        simp only [pow_two, mul_assoc]
      _ = ((operator (R := ℝ) r * operator (R := ℝ) q) * (operator (R := ℝ) p * operator (R := ℝ) r)) g y₁ := by
        change operator (R := ℝ) r (operator (R := ℝ) q (operator (R := ℝ) p (operator (R := ℝ) r
          ((operator (R := ℝ) q * operator (R := ℝ) p) g)))) y₁ =
          operator (R := ℝ) r (operator (R := ℝ) q (operator (R := ℝ) p (operator (R := ℝ) r g))) y₁
        exact operator_congr_at r y₁ (operator_congr_at q x₂
          (operator_congr_at p y₃ (operator_congr_at r x₄ h₅)))
      _ = (operator (R := ℝ) r * operator (R := ℝ) q) g y₁ := by
        change operator (R := ℝ) r (operator (R := ℝ) q ((operator (R := ℝ) p * operator (R := ℝ) r) g)) y₁ =
          operator (R := ℝ) r (operator (R := ℝ) q g) y₁
        exact operator_congr_at r y₁ (operator_congr_at q x₂ h₃)
      _ = _ := h₁
  rw [operator_cycle_square r q p hpr hrq.symm hpq] at hcycle
  change -(exchangeSign (R := ℝ) p r * (exchangeSign q r * exchangeSign p q)) * g y₁ =
    g y₁ at hcycle
  have h := (mul_left_inj' hg).mp (hcycle.trans (one_mul (g y₁)).symm)
  linarith only [h]

private theorem crossing_pair_mem {A : Finset (Fin 9)} (p : CrossingPair (A : Set (Fin 9))) :
    p.val ∈ cutPairs A :=
  Finset.mem_product.mpr ⟨p.property.1,
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, p.property.2⟩⟩

open Classical in
private theorem exchange_product_of_companion
    {C D : Finset (Q 9)} {b : Bool} {A : Finset (Fin 9)}
    {p q r : CrossingPair (A : Set (Fin 9))} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hcut : cutMasks C D b A = {mask p.val, mask q.val, mask r.val})
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    {x : Q 9} (hx : x ∈ C) (hxb : parity x = b)
    (hpx : step p x ∈ D) (hqx : step q x ∈ D) :
    exchangeSign (R := ℝ) p r * (exchangeSign q r * exchangeSign p q) = -1 := by
  have hp := crossing_pair_mem p
  have hq := crossing_pair_mem q
  have hr := crossing_pair_mem r
  have hpq' : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
  have hpr' : p.val ≠ r.val := fun h => hpr (Subtype.ext h)
  have hqr' : q.val ≠ r.val := fun h => hqr (Subtype.ext h)
  have hcard : (cutMasks C D b A).card ≤ 3 := hcut.symm ▸ Finset.card_le_three
  have hsep' (u : Q 9) (hu : u ∈ D) (v : Q 9) (hv : v ∈ C) :
      2 ≤ hammingDist u v := by
    rw [hammingDist_comm]
    exact hsep v hv u hu
  have hswap : cutMasks D C b A = {mask p.val, mask q.val, mask r.val} :=
    (cutMasks_swap D C b A).trans hcut
  let y := step p x
  let z := step r y
  have hyb : parity y = b := (parity_translate p.val _).trans hxb
  have hyp : step p y ∈ C := step_involution p x ▸ hx
  have hz : z ∈ C :=
    Or.resolve_left (other_contact_of_three_mask_cut hsep' hrC hbC hpx hyb hp hq hr hswap hyp)
      (no_alternating_square_of_small_cut hsep hrD hcD hbD hdetD hx hxb hcard hp hq hpq' hpx hqx)
  have hzb : parity z = b := (parity_translate r.val _).trans hyb
  have hzr : step r z ∈ D := step_involution r y ▸ hpx
  have hzp : step p z ∉ D := by
    intro h
    have hback : step p (step r z) ∈ C := by
      change step p (step r (step r y)) ∈ C
      rw [step_involution]
      exact hyp
    exact no_alternating_square_of_small_cut hsep hrD hcD hbD hdetD
      hz hzb hcard hr hp hpr'.symm hzr h hback
  have hcutR : cutMasks C D b A = {mask r.val, mask p.val, mask q.val} := by
    rw [hcut]
    ext s
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hzq : step q z ∈ D :=
    Or.resolve_left (other_contact_of_three_mask_cut hsep hrD hbD hz hzb hr hp hq hcutR hzr) hzp
  let t := step p (step q z)
  have htEq : t = step q (step r x) := by
    change step p (step q (step r (step p x))) = _
    rw [step_comm p q, step_comm p r, step_involution]
  have ht : t ∈ C := htEq.symm ▸
    (transport_from_companion hsep hrC hrD hcD hbC hbD hdetD hx hxb hp hq hr
      hpq' hpr' hqr' hcut hpx hqx).1
  have htb : parity t = b := htEq.symm ▸
    (parity_translate q.val _).trans ((parity_translate r.val _).trans hxb)
  have htp : step p t ∈ D := step_involution p (step q z) ▸ hzq
  have htr : step r t ∈ D := by
    change step r (step p (step q (step r (step p x)))) ∈ D
    rw [step_comm r p, step_comm r q, step_involution, step_comm p q, step_involution]
    exact hqx
  obtain ⟨σ, hσ⟩ := hbD
  let g := BalancedCriticalSpectrum.switchingVector D σ
  have hgout (v : Q 9) (hv : v ∉ D) : g v = 0 := by
    simp [g, BalancedCriticalSpectrum.switchingVector, hv]
  have hAg (v : Q 9) (hv : v ∉ D) : weightedLinear (fun _ => 1) g v = 0 := by
    rw [Q9SignedContactCells.unit_weight]
    calc
      _ = (3 : ℝ) * g v :=
        congrFun (BalancedCriticalSpectrum.ambient_eigenvector (d := 3) D σ hrD hσ) v
      _ = 0 := by rw [hgout v hv, mul_zero]
  have hg : g (step p x) ≠ 0 := by
    rcases hσ.1 _ hpx with h | h <;> simp [g, BalancedCriticalSpectrum.switchingVector, hpx, h]
  have hrow {v : Q 9} (hv : v ∈ C) (hvb : parity v = b)
      (a c : CrossingPair (A : Set (Fin 9))) (hac : a.val ≠ c.val)
      (hva : step a v ∈ D) (hvc : step c v ∈ D) :
      operator (R := ℝ) a g v + operator (R := ℝ) c g v = 0 := by
    simpa only [operator, cutTerm, translate, Module.End.mul_apply, direction_apply, one_mul] using
      two_contact_row hsep hrD ⟨σ, hσ⟩ hv hvb hcard hgout hAg
        (crossing_pair_mem a) (crossing_pair_mem c) hac hva hvc
  exact exchange_sign_product_of_zero_rows p r q hpr hpq hqr.symm g x hg
    (hrow hx hxb q p hpq'.symm hqx hpx) (hrow hz hzb r q hqr'.symm hzr hzq)
    (hrow ht htb p r hpr' htp htr)

open Classical in
/-- In a cut with three realized masks, an odd number of the three unordered
mask pairs share an axis. -/
theorem three_mask_cut_odd_shared_axes
    {C D : Finset (Q 9)} {b : Bool} {A : Finset (Fin 9)}
    (p q r : CrossingPair (A : Set (Fin 9))) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hcut : cutMasks C D b A =
      {{p.val.1, p.val.2}, {q.val.1, q.val.2}, {r.val.1, r.val.2}})
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0) :
    Odd ((if p.val.1 = q.val.1 ∨ p.val.2 = q.val.2 then 1 else 0) +
      (if p.val.1 = r.val.1 ∨ p.val.2 = r.val.2 then 1 else 0) +
      (if q.val.1 = r.val.1 ∨ q.val.2 = r.val.2 then 1 else 0) : ℕ) := by
  have hp := crossing_pair_mem p
  have hq := crossing_pair_mem q
  have hr := crossing_pair_mem r
  have hpM : mask p.val ∈ cutMasks C D b A := by
    rw [hcut]
    simp [mask]
  obtain ⟨x, hx, hxb, hpx⟩ := contact_of_mask hp hpM
  have hsign : exchangeSign (R := ℝ) p r * (exchangeSign q r * exchangeSign p q) = -1 := by
    rcases other_contact_of_three_mask_cut hsep hrD hbD hx hxb hp hq hr hcut hpx with h | h
    · exact exchange_product_of_companion hpq hpr hqr hcut hsep hrC hrD hcD hbC hbD hdetD
        hx hxb hpx h
    · have hcut' : cutMasks C D b A = {mask p.val, mask r.val, mask q.val} := by
        rw [show cutMasks C D b A = {mask p.val, mask q.val, mask r.val} from hcut,
          Finset.pair_comm (mask q.val) (mask r.val)]
      have he := exchange_product_of_companion hpr hpq hqr.symm hcut'
        hsep hrC hrD hcD hbC hbD hdetD hx hxb hpx h
      have hs : exchangeSign (R := ℝ) r q = exchangeSign q r := by
        unfold exchangeSign
        simp only [eq_comm]
      rw [hs] at he
      linear_combination he
  by_cases hpqS : p.val.1 = q.val.1 ∨ p.val.2 = q.val.2 <;>
    by_cases hprS : p.val.1 = r.val.1 ∨ p.val.2 = r.val.2 <;>
    by_cases hqrS : q.val.1 = r.val.1 ∨ q.val.2 = r.val.2 <;>
    norm_num [exchangeSign, hpqS, hprS, hqrS] at hsign <;>
    norm_num [hpqS, hprS, hqrS]

#print axioms three_mask_cut_odd_shared_axes

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ThreeMaskCutSign
