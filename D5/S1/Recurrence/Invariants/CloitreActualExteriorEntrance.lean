/- GID: D5/S1/Recurrence/Invariants/CloitreActualExteriorEntrance
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/CloitreActualExteriorEntrance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional actual exterior entrance, joint clocks, and physical natural-cap rows. -/

import D5.S1.Recurrence.Invariants.CloitreActualLeftPlateau

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S1.Recurrence.Invariants.CloitreActualExteriorEntrance

open D5.S1.Recurrence.Invariants.CloitreActualRightProfile
open D5.S1.Recurrence.Invariants.CloitreActualLeftPlateau

local notation "F" => Nat.fib
local notation "G" => D5.S1.Phase.SelfReference.GoldenShellRecurrence.g

/-- Literal quadratic cap coefficient, with its separate ninth-order value. -/
def capBudget (j : ℕ) : ℕ :=
  if j = 9 then 13 else ((j - 2) ^ 2 / 3 + 30) - 3 * j

/- The source's two additional height-deficit conditions. -/
structure Hyp31_1 (U : ℕ → ℕ) : Prop extends Hyp24_1 U where
  positiveHeight : ∀ j t : ℕ, 9 ≤ j → t ≤ F (j - 2) →
    0 < heightDeficit j t → t ≤
      capBudget j * heightDeficit j t
  descentHeight : ∀ j t : ℕ, 8 ≤ j → t ≤ F (j - 2) →
    heightDeficit j t ≤ 2 * t / 3

def naturalCap (y : ℕ) : ℕ :=
  F (Nat.greatestFib y) - C y

/-- Full original target; this definition supplies no proof of its clauses. -/
def full31_3_statement (U : ℕ → ℕ) (_h : Hyp31_1 U) : Prop := by
  exact (
    ∀ k v : ℕ, 23 ≤ k → v ≤ F (k - 4) / 2 →
      let N := F k - v
      let A := F (k - 1)
      let B := F (k - 2)
      let J := F (k - 4)
      let I := Set.Icc (A - v) A
      let σ := heightDeficit k (v + 1)
      let P := capBudget (k - 1)
      let L := (2 * (k - 1) / 3 : ℕ) - 3
      let q : ℝ := (P : ℝ) / Real.goldenRatio⁻¹
      let γ : ℝ :=
        ((L : ℝ) + ((P : ℝ) - 1) * (v : ℝ) + 1) / Real.goldenRatio⁻¹
      let β : ℝ :=
        Real.log (1 +
            ((P : ℝ) - Real.goldenRatio⁻¹) * ((J : ℝ) - (v : ℝ)) /
              ((L : ℝ) + ((P : ℝ) - 1) * (v : ℝ) + 1)) /
          Real.log ((P : ℝ) / Real.goldenRatio⁻¹)
      ∃ R θ μ : ℕ, R ≥ 2 ∧ θ = 2 * R ∧
        X N θ ∈ I ∧ (∀ i : ℕ, i < θ → X N i ∉ I) ∧
        X N μ ∈ Function.periodicPts (T N) ∧
        (∀ i : ℕ, i < μ → X N i ∉ Function.periodicPts (T N)) ∧
        θ ≤ μ ∧ μ ≤ d N ∧
        d N = A - σ ∧ σ ≤ v ∧ v + 1 ≤ B ∧ v - σ ≤ J ∧
        X N 1 = B - v + σ ∧
        X N 2 = A + (J - v + heightDeficit (k - 2) (v - σ)) ∧
        J - v ≤ J - v + heightDeficit (k - 2) (v - σ) ∧
        J - v + heightDeficit (k - 2) (v - σ) ≤ J ∧
        (∀ r : ℕ, 1 ≤ r → r < R →
          let a := (X N (2 * r) : ℤ) - (A : ℤ);
          let b := A - X N (2 * r + 1);
          let an := X N (2 * (r + 1));
          1 ≤ a ∧ a ≤ (J : ℤ) ∧ a = (a.toNat : ℤ) ∧
          1 ≤ a.toNat ∧ a.toNat ≤ J ∧
          b = v + (C (A + a.toNat) - B) ∧
          v < b ∧ b ≤ v + J ∧ v + J ≤ F (k - 3) ∧
          b ≤ F ((k - 1) - 2) ∧
          X N (2 * r + 1) = A - b ∧
          (an : ℤ) - (A : ℤ) = (heightDeficit (k - 1) b : ℤ) - (v : ℤ) ∧
          3 * ((an : ℤ) - (A : ℤ)) ≤ 2 * a - (v : ℤ) ∧
          (a : ℝ) < q * (((an : ℤ) - (A : ℤ) : ℤ) : ℝ) + γ) ∧
        (∀ r s : ℕ, 1 ≤ r → r < s → s < R →
          (X N (2 * s) : ℤ) - (A : ℤ) < (X N (2 * r) : ℤ) - (A : ℤ)) ∧
        (let aR : ℤ := (X N (2 * R) : ℤ) - (A : ℤ);
         -(v : ℤ) ≤ aR ∧ aR ≤ 0) ∧
        (∀ r : ℕ, 1 ≤ r → r < R - 1 →
          v < heightDeficit (k - 1) (A - X N (2 * r + 1))) ∧
        heightDeficit (k - 1) (A - X N (2 * (R - 1) + 1)) ≤ v ∧
        v < A - X N (2 * (R - 1) + 1) ∧
        A - X N (2 * (R - 1) + 1) ≤ L + P * v ∧
        (((X N (2 * (R - 1)) : ℤ) - (A : ℤ)) : ℝ) < γ ∧
        A - X N θ = v - heightDeficit (k - 1)
          (A - X N (2 * (R - 1) + 1)) ∧
        (0 : ℤ) ≤ (A : ℤ) - (X N θ : ℤ) ∧
        v - heightDeficit (k - 1) (A - X N (2 * (R - 1) + 1)) ≤ v ∧
        Set.InjOn (fun r : ℕ => X N (2 * r)) (Set.Ico 1 R) ∧
        ((Finset.Ico 1 R).image (fun r => X N (2 * r))).card = R - 1 ∧
        (∀ r : ℕ, 1 ≤ r → r < R →
          let y := X N (2 * r);
          (∀ j : ℕ, 2 ≤ j → y ≠ F j) ∧
          A < y ∧ y ≤ A + J ∧ A + J < N - 1 ∧ N - 1 < N ∧
          y < N - 1 ∧ y < N ∧
          naturalCap y = heightDeficit k (F k - y) ∧
          F (k - 5) ≤ naturalCap y ∧
          (N : ℝ) / 13 ≤ (F (k - 5) : ℝ)) ∧
        (R - 1 : ℝ) > β ∧
        (θ : ℝ) > 2 + 2 * β ∧
        (∀ r : ℕ, 1 ≤ r → r < R → 2 * r < d N)
  )

set_option maxHeartbeats 4000000 in
-- Actual-pair induction and signed/real arithmetic share the clock and row witnesses.
/-- The complete original conditional exterior entrance theorem. -/
theorem full31_3 (U : ℕ → ℕ) (h31 : Hyp31_1 U) : full31_3_statement U h31 := by
  unfold full31_3_statement
  intro k v hk hv
  let N := F k - v
  let A := F (k - 1)
  let B := F (k - 2)
  let J := F (k - 4)
  let H := F (k - 5)
  let σ := heightDeficit k (v + 1)
  have h24 := h31.toHyp24_1
  have h21 := h24.toHyp21_1
  have platform := (full24_3 U h24).1
  have fibStep : ∀ m : ℕ, 2 ≤ m → F m = F (m - 1) + F (m - 2) := by
    intro m hm
    have hf := Nat.fib_add_two (n := m - 2)
    rw [show m - 2 + 2 = m by omega, show m - 2 + 1 = m - 1 by omega] at hf
    omega
  have fK : F k = A + B := fibStep k (by omega)
  have fA : A = B + F (k - 3) := by
    simpa only [A, B, Nat.sub_sub] using fibStep (k - 1) (by omega)
  have fB : B = F (k - 3) + J := by
    simpa only [B, J, Nat.sub_sub] using fibStep (k - 2) (by omega)
  have fJ : F (k - 3) = J + H := by
    simpa only [J, H, Nat.sub_sub] using fibStep (k - 3) (by omega)
  have jTwo : J ≤ 2 * H := by
    have hf := fibStep (k - 4) (by omega)
    have hm := Nat.fib_mono (show k - 6 ≤ k - 5 by omega)
    dsimp [J, H]
    change J = H + F (k - 6) at hf
    omega
  have hJ : 18 ≤ J := by
    have hp := Nat.le_fib_add_one (k - 4)
    dsimp [J]
    omega
  have hH : 17 ≤ H := by
    have hp := Nat.le_fib_add_one (k - 5)
    dsimp [H]
    omega
  have twoV : 2 * v ≤ J := by dsimp [J]; omega
  have collar : v + J ≤ F (k - 3) := by omega
  have hN : 3 ≤ N := by dsimp [N]; omega
  have hA : 1 ≤ A := by omega
  have σdomain : v + 1 ≤ F (k - 2) := by change v + 1 ≤ B; omega
  have σcap := platform k (v + 1) (by omega) σdomain
  have σle : σ ≤ v := by
    by_cases hsmall : v ≤ 1
    · have hz : heightDeficit k (v + 1) = 0 := σcap.2.1.mpr (by
        unfold platformWidth
        omega)
      dsimp [σ]
      omega
    · have hd := h31.descentHeight k (v + 1) (by omega) σdomain
      dsimp [σ]
      omega
  have dEq : d N = A - σ := by
    have hrow : N - 1 = F k - (v + 1) := by dsimp [N]; omega
    dsimp [d]
    rw [hrow]
    dsimp [σ, heightDeficit, A]
    omega
  have step : ∀ i : ℕ, X N (i + 1) = N - C (X N i) := by
    intro i
    exact Function.iterate_succ_apply' (T N) i (N - 1)
  have x1 : X N 1 = B - v + σ := by
    have hs := step 0
    change X N 1 = N - d N at hs
    rw [dEq] at hs
    simp only [N, A, B, J, H, σ, Nat.sub_sub] at *
    omega
  have qdomain : v - σ ≤ F ((k - 2) - 2) := by
    rw [Nat.sub_sub]
    change v - σ ≤ J
    omega
  have qcap := platform (k - 2) (v - σ) (by omega) qdomain
  have qdrop := h31.descentHeight (k - 2) (v - σ) (by omega) qdomain
  let a1 := J - v + heightDeficit (k - 2) (v - σ)
  have a1bounds : J - v ≤ a1 ∧ a1 ≤ J ∧ 1 ≤ a1 := by dsimp [a1]; omega
  have x2 : X N 2 = A + a1 := by
    have row : X N 1 = F (k - 2) - (v - σ) := by rw [x1]; dsimp [B]; omega
    have hs := step 1
    rw [row] at hs
    dsimp [heightDeficit] at qdrop
    rw [Nat.sub_sub] at qdrop qcap
    change C (B - (v - σ)) ≤ F (k - 3) ∧ _ at qcap
    change X N 2 = N - C (B - (v - σ)) at hs
    dsimp [N, a1, heightDeficit]
    simp only [N, A, B, J, H, σ, Nat.sub_sub] at *
    norm_num only at *
    omega
  have goldenMono : Monotone G := by
    intro a b hab
    unfold D5.S1.Phase.SelfReference.GoldenShellRecurrence.g
    apply Nat.floor_mono
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast Nat.add_le_add_right hab 1
    · exact le_of_lt (inv_pos.mpr Real.goldenRatio_pos)
  have right : ∀ a : ℕ, 1 ≤ a → a ≤ J →
      let ι := C (A + a) - B
      1 ≤ ι ∧ ι ≤ a ∧ C (A + a) = B + ι := by
    intro a ha haj
    have hb := h21.bounds (A + a) (by omega)
    have hg := goldenMono (show A + 1 ≤ A + a by omega)
    have hp := (h21.plusOne (k - 1) (by omega)).1
    change G (A + 1) = B + 1 at hp
    rw [hp] at hg
    have hu := h21.uPiece (k - 1) (A + a) (by omega) (by omega) (by
      rw [show k - 1 + 1 = k by omega, fK]
      omega)
    rw [Nat.sub_sub] at hu
    have hm : U (A + a) ≤ A + a - F (k - 3) := by rw [hu]; exact min_le_left _ _
    dsimp
    omega
  have pair : ∀ r a : ℕ, 1 ≤ a → a ≤ J → X N (2 * r) = A + a →
      let b := A - X N (2 * r + 1)
      b = v + (C (A + a) - B) ∧ v < b ∧ b ≤ v + J ∧
      X N (2 * r + 1) = A - b ∧
      (X N (2 * (r + 1)) : ℤ) - A = (heightDeficit (k - 1) b : ℤ) - v ∧
      3 * ((X N (2 * (r + 1)) : ℤ) - A) ≤ 2 * (a : ℤ) - v ∧
      A - v ≤ X N (2 * (r + 1)) := by
    intro r a ha haj hx
    obtain ⟨hi, hia, hci⟩ := right a ha haj
    have oddEq : X N (2 * r + 1) = A - (v + (C (A + a) - B)) := by
      rw [step, hx, hci]
      dsimp [N]
      omega
    let b := A - X N (2 * r + 1)
    have bEq : b = v + (C (A + a) - B) := by dsimp [b]; rw [oddEq]; omega
    have bd : b ≤ F ((k - 1) - 2) := by
      change b ≤ F (k - 3)
      omega
    have cp := platform (k - 1) b (by omega) bd
    have drop := h31.descentHeight (k - 1) b (by omega) bd
    have oddRow : X N (2 * r + 1) = A - b := by dsimp [b]; rw [oddEq]; omega
    have evenEq : X N (2 * (r + 1)) = N - C (A - b) := by
      rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega, step, oddRow]
    change C (A - b) ≤ B ∧ _ at cp
    have deficitEq : heightDeficit (k - 1) b = B - C (A - b) := by
      simp only [heightDeficit, Nat.sub_sub, A, B]
    rw [deficitEq] at drop
    dsimp [N] at evenEq
    have signed : (X N (2 * (r + 1)) : ℤ) - A =
        (heightDeficit (k - 1) b : ℤ) - v := by
      rw [deficitEq]
      simp only [N, A, B, J, H, σ, Nat.sub_sub] at *
      norm_num only at *
      omega
    refine ⟨bEq, by omega, by omega, oddRow, signed, ?_, by omega⟩
    rw [signed, deficitEq]
    omega
  have captured : ∃ i : ℕ, X N i ∈ Set.Icc (A - v) A := by
    have dom := actual_foundations.1 N 0 hN
    change N - 1 ∈ D N at dom
    have hc := h24.negativeCapture (k - 1) v (N - 1) (by omega) (by
      change v ≤ B
      omega)
    rw [show k - 1 + 1 = k by omega] at hc
    obtain ⟨i, hi⟩ := hc dom
    exact ⟨i, hi.1⟩
  let θ := Nat.find captured
  have entered : X N θ ∈ Set.Icc (A - v) A := Nat.find_spec captured
  have least : ∀ i : ℕ, i < θ → X N i ∉ Set.Icc (A - v) A := by
    intro i hi
    exact Nat.find_min captured hi
  have θgt : 2 < θ := by
    have zero : X N 0 = N - 1 := rfl
    by_contra hh
    have he : θ = 0 ∨ θ = 1 ∨ θ = 2 := by omega
    rcases he with he | he | he
    · rw [he, zero] at entered
      dsimp [N] at entered
      change A - v ≤ F k - v - 1 ∧ F k - v - 1 ≤ A at entered
      omega
    · rw [he, x1] at entered
      change A - v ≤ B - v + σ ∧ _ at entered
      omega
    · rw [he, x2] at entered
      change A - v ≤ A + a1 ∧ A + a1 ≤ A at entered
      omega
  have pairedPrefix : ∀ r : ℕ, 1 ≤ r → 2 * r < θ →
      ∃ a : ℕ, 1 ≤ a ∧ a ≤ J ∧ X N (2 * r) = A + a := by
    intro r
    induction r with
    | zero => intro hr; omega
    | succ r ih =>
      intro hr ht
      by_cases hz : r = 0
      · subst r
        exact ⟨a1, a1bounds.2.2, a1bounds.2.1, x2⟩
      · obtain ⟨a, ha, haj, hx⟩ := ih (by omega) (by omega)
        have pp := pair r a ha haj hx
        have hn := least (2 * (r + 1)) ht
        change ¬(A - v ≤ X N (2 * (r + 1)) ∧ X N (2 * (r + 1)) ≤ A) at hn
        have positive : A < X N (2 * (r + 1)) := by omega
        refine ⟨X N (2 * (r + 1)) - A, by omega, ?_, by omega⟩
        have contraction := pp.2.2.2.2.2.1
        omega
  have θeven : θ % 2 = 0 := by
    by_contra ho
    let r := θ / 2
    have ht : θ = 2 * r + 1 := by dsimp [r]; omega
    obtain ⟨a, ha, haj, hx⟩ := pairedPrefix r (by dsimp [r]; omega) (by omega)
    have pp := pair r a ha haj hx
    rw [ht] at entered
    have oo := pp.2.2.2.1
    have bb := pp.2.1
    change A - v ≤ X N (2 * r + 1) ∧ _ at entered
    omega
  let R := θ / 2
  have θEq : θ = 2 * R := by dsimp [R]; omega
  have hR : 2 ≤ R := by omega
  let a := fun r : ℕ => (X N (2 * r) : ℤ) - (A : ℤ)
  let b := fun r : ℕ => A - X N (2 * r + 1)
  let P := capBudget (k - 1)
  let L := 2 * (k - 1) / 3 - 3
  let α : ℝ := Real.goldenRatio⁻¹
  let q : ℝ := (P : ℝ) / α
  let γ : ℝ := ((L : ℝ) + ((P : ℝ) - 1) * v + 1) / α
  let β : ℝ := Real.log (1 + ((P : ℝ) - α) * ((J : ℝ) - v) /
    ((L : ℝ) + ((P : ℝ) - 1) * v + 1)) / Real.log q
  have ha0 : 0 < α := inv_pos.mpr Real.goldenRatio_pos
  have ha1 : α < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have widthEq : platformWidth (k - 1) = L := by
    dsimp [platformWidth, L]
    omega
  have budgetBound : ∀ j : ℕ, 9 ≤ j → platformWidth j + 2 ≤ capBudget j := by
    intro j hj
    by_cases hj9 : j = 9
    · subst j
      norm_num [platformWidth, capBudget]
    · let w := j - 2
      have jw : j = w + 2 := by dsimp [w]; omega
      have db : w ^ 2 < 3 * (w ^ 2 / 3 + 1) := Nat.lt_mul_div_succ _ (by omega)
      have wb : 3 * platformWidth j ≤ 2 * j - 9 := by unfold platformWidth; omega
      have wbExact : 3 * platformWidth j + 9 ≤ 2 * j := by omega
      have square : 11 * w ≤ w ^ 2 + 31 := by
        have si : (11 : ℤ) * w ≤ (w : ℤ) ^ 2 + 31 := by
          nlinarith [sq_nonneg (2 * (w : ℤ) - 11)]
        exact_mod_cast si
      have nontruncation : 3 * j + platformWidth j + 2 ≤ w ^ 2 / 3 + 30 := by nlinarith
      rw [capBudget, if_neg hj9]
      change platformWidth j + 2 ≤ w ^ 2 / 3 + 30 - 3 * j
      omega
  have pLarge : 2 ≤ P := by
    have hb := budgetBound (k - 1) (by omega)
    change platformWidth (k - 1) + 2 ≤ P at hb
    omega
  have pReal : (2 : ℝ) ≤ P := by exact_mod_cast pLarge
  have qOne : 1 < q := (lt_div_iff₀ ha0).mpr (by linarith)
  have paPos : 0 < (P : ℝ) - α := by linarith
  have denomPos : 0 < (L : ℝ) + ((P : ℝ) - 1) * v + 1 := by
    have hv0 : (0 : ℝ) ≤ v := by positivity
    have hL0 : (0 : ℝ) ≤ L := by positivity
    nlinarith
  have γpos : 0 < γ := div_pos denomPos ha0
  have enclosure : ∀ t : ℕ, t ≤ F (k - 3) →
      t ≤ L + P * heightDeficit (k - 1) t := by
    intro t ht
    have td : t ≤ F ((k - 1) - 2) := by simpa only [Nat.sub_sub] using ht
    by_cases hz : heightDeficit (k - 1) t = 0
    · have hw := (platform (k - 1) t (by omega) td).2.1.mp hz
      rw [widthEq] at hw
      omega
    · have hp := h31.positiveHeight (k - 1) t (by omega) td (by omega)
      change t ≤ P * heightDeficit (k - 1) t at hp
      omega
  have rightLower : ∀ z : ℕ, 1 ≤ z → z ≤ J →
      α * (z : ℝ) - 1 < (C (A + z) - B : ℕ) := by
    intro z hz hzj
    obtain ⟨_, _, hci⟩ := right z hz hzj
    have hc := (h21.bounds (A + z) (by omega)).2.1
    have hgA := (h21.anchors (k - 1) (by omega)).2.2
    change G A = B at hgA
    have lo := Nat.floor_le (show 0 ≤ ((A : ℝ) + 1) * α by positivity)
    change (G A : ℝ) ≤ ((A : ℝ) + 1) * α at lo
    rw [hgA] at lo
    have hi' := Nat.lt_floor_add_one ((((A + z : ℕ) : ℝ) + 1) * α)
    change (((A + z : ℕ) : ℝ) + 1) * α < (G (A + z) : ℝ) + 1 at hi'
    have hc' : (G (A + z) : ℝ) ≤ C (A + z) := by exact_mod_cast hc
    have ci' : (C (A + z) : ℝ) = (B : ℝ) + (C (A + z) - B : ℕ) := by
      exact_mod_cast hci
    push_cast at hi'
    nlinarith
  have pairFacts : ∀ r : ℕ, 1 ≤ r → r < R →
      1 ≤ a r ∧ a r ≤ (J : ℤ) ∧ a r = ((a r).toNat : ℤ) ∧
      1 ≤ (a r).toNat ∧ (a r).toNat ≤ J ∧
      b r = v + (C (A + (a r).toNat) - B) ∧
      v < b r ∧ b r ≤ v + J ∧
      X N (2 * r + 1) = A - b r ∧
      a (r + 1) = (heightDeficit (k - 1) (b r) : ℤ) - v ∧
      3 * a (r + 1) ≤ 2 * a r - v ∧
      (a r : ℝ) < q * (a (r + 1) : ℝ) + γ := by
    intro r hr hrr
    obtain ⟨z, hz, hzj, hx⟩ := pairedPrefix r hr (by omega)
    have pp := pair r z hz hzj hx
    have az : a r = (z : ℤ) := by dsimp [a]; rw [hx]; omega
    have iz : (a r).toNat = z := by rw [az, Int.toNat_natCast]
    have lower := rightLower z hz hzj
    have bd : b r ≤ F (k - 3) := by dsimp [b]; omega
    have enc := enclosure (b r) bd
    have bEq : b r = v + (C (A + z) - B) := pp.1
    have signed : a (r + 1) = (heightDeficit (k - 1) (b r) : ℤ) - v := pp.2.2.2.2.1
    have signedR : (a (r + 1) : ℝ) = (heightDeficit (k - 1) (b r) : ℝ) - v := by
      exact_mod_cast signed
    have encR : (b r : ℝ) ≤ (L : ℝ) + (P : ℝ) * heightDeficit (k - 1) (b r) := by
      exact_mod_cast enc
    have bEqR : (b r : ℝ) = (v : ℝ) + (C (A + z) - B : ℕ) := by exact_mod_cast bEq
    have affine : (z : ℝ) < q * (a (r + 1) : ℝ) + γ := by
      apply (mul_lt_mul_iff_of_pos_left ha0).mp
      dsimp [q, γ]
      field_simp
      nlinarith
    refine ⟨by omega, by omega, by rw [iz]; exact az,
      by omega, by omega, ?_, pp.2.1, pp.2.2.1, pp.2.2.2.1,
      signed, ?_, ?_⟩
    · rw [iz]
      exact bEq
    · rw [az]
      exact pp.2.2.2.2.2.1
    · rw [az]
      exact affine
  have terminal : -(v : ℤ) ≤ a R ∧ a R ≤ 0 := by
    have hi : A - v ≤ X N θ ∧ X N θ ≤ A := entered
    dsimp [a]
    rw [← θEq]
    simp only [N, A, B, J, H, σ, Nat.sub_sub] at *
    norm_num only at *
    omega
  have decrease : ∀ r s : ℕ, 1 ≤ r → r < s → s < R → a s < a r := by
    intro r s hr hrs hs
    induction s with
    | zero => omega
    | succ s ih =>
      have ps := pairFacts s (by omega) (by omega)
      have stepLt : a (s + 1) < a s := by omega
      by_cases he : r = s
      · subst s
        exact stepLt
      · exact stepLt.trans (ih (by omega) (by omega))
  have earlyStop : ∀ r : ℕ, 1 ≤ r → r < R - 1 → v < heightDeficit (k - 1) (b r) := by
    intro r hr hrr
    have ps := pairFacts r hr (by omega)
    have pn := pairFacts (r + 1) (by omega) (by omega)
    omega
  have last := pairFacts (R - 1) (by omega) (by omega)
  have lastIndex : R - 1 + 1 = R := by omega
  have lastStop : heightDeficit (k - 1) (b (R - 1)) ≤ v := by
    rw [lastIndex] at last
    omega
  have lastBound : b (R - 1) ≤ L + P * v := by
    have enc := enclosure (b (R - 1)) (by omega)
    exact enc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left P lastStop) L)
  have lastAffine : (a (R - 1) : ℝ) < γ := by
    have af := last.2.2.2.2.2.2.2.2.2.2.2
    rw [lastIndex] at af
    have terR : (a R : ℝ) ≤ 0 := by exact_mod_cast terminal.2
    have hq0 : 0 ≤ q := le_of_lt (lt_trans (by norm_num) qOne)
    nlinarith
  have gap : A - X N θ = v - heightDeficit (k - 1) (b (R - 1)) := by
    have eq := last.2.2.2.2.2.2.2.2.2.1
    rw [lastIndex] at eq
    dsimp [a] at eq
    rw [← θEq] at eq
    simp only [N, A, B, J, H, σ, Nat.sub_sub] at *
    norm_num only at *
    omega
  obtain ⟨μ, periodic, beforePeriodic, μdepth⟩ := h21.depthEntry N hN
  have μI : X N μ ∈ Set.Icc (A - v) A := by
    have inter := h24.intersection (k - 1) v (X N μ) (by omega) (by
      change v ≤ B
      omega)
    rw [show k - 1 + 1 = k by omega] at inter
    have hb := inter (actual_foundations.1 N μ hN) periodic
    change A - v ≤ X N μ ∧ X N μ ≤ A
    exact ⟨(le_max_right _ _).trans hb.1, hb.2.trans (min_le_left _ _)⟩
  have θμ : θ ≤ μ := Nat.find_min' captured μI
  have uses : ∀ r : ℕ, 1 ≤ r → r < R → 2 * r < d N := by
    intro r hr hrr
    omega
  have monoAffine : Monotone (fun z : ℝ => q * z + γ) := by
    intro z w hzw
    exact add_le_add
      (mul_le_mul_of_nonneg_left hzw (show 0 ≤ q from le_trans (by norm_num) qOne.le)) le_rfl
  have reversed : (a 1 : ℝ) < arithGeom q γ 0 (R - 1) := by
    have seq := monoAffine.seq_pos_lt_seq_of_lt_of_le
      (x := fun i : ℕ => (a (R - i) : ℝ)) (y := arithGeom q γ 0)
      (show 0 < R - 1 by omega)
      (by simp only [Nat.sub_zero, arithGeom_zero]; exact_mod_cast terminal.2)
      (by
        intro i hi
        have rpos : 1 ≤ R - (i + 1) := by omega
        have rlt : R - (i + 1) < R := by omega
        have pf := pairFacts (R - (i + 1)) rpos rlt
        have af := pf.2.2.2.2.2.2.2.2.2.2.2
        have ri : R - (i + 1) + 1 = R - i := by omega
        simpa only [ri] using af)
      (by intro i hi; exact le_of_eq (arithGeom_succ i).symm)
    simpa only [show R - (R - 1) = 1 by omega] using seq
  have firstA : a 1 = (a1 : ℤ) := by dsimp [a]; rw [x2]; omega
  have firstLower : (J : ℝ) - v ≤ (a 1 : ℝ) := by
    have hz : (J : ℤ) - v ≤ a 1 := by rw [firstA]; omega
    exact_mod_cast hz
  have reverseBound : (J : ℝ) - v < γ * (q ^ (R - 1) - 1) / (q - 1) := by
    rw [arithGeom_zero_eq_mul_div qOne.ne'] at reversed
    exact firstLower.trans_lt reversed
  have ratioEq : γ / (q - 1) =
      ((L : ℝ) + ((P : ℝ) - 1) * v + 1) / ((P : ℝ) - α) := by
    dsimp [q, γ]
    field_simp
  have logInput : 1 + ((P : ℝ) - α) * ((J : ℝ) - v) /
      ((L : ℝ) + ((P : ℝ) - 1) * v + 1) < q ^ (R - 1) := by
    rw [← div_mul_eq_mul_div, ratioEq] at reverseBound
    have bound := (lt_div_iff₀ paPos).mp (show (J : ℝ) - v <
      (((L : ℝ) + ((P : ℝ) - 1) * v + 1) * (q ^ (R - 1) - 1)) /
        ((P : ℝ) - α) by
      simpa only [div_mul_eq_mul_div] using reverseBound)
    have divBound := (div_lt_iff₀ denomPos).mpr
      (show ((P : ℝ) - α) * ((J : ℝ) - v) <
        (q ^ (R - 1) - 1) * ((L : ℝ) + ((P : ℝ) - 1) * v + 1) by
          nlinarith)
    linarith
  have logInputPos : 0 < 1 + ((P : ℝ) - α) * ((J : ℝ) - v) /
      ((L : ℝ) + ((P : ℝ) - 1) * v + 1) := by
    have jv : (0 : ℝ) ≤ (J : ℝ) - v := by
      have hle : (v : ℝ) ≤ (J : ℝ) := by exact_mod_cast (show v ≤ J by omega)
      linarith
    positivity
  have clock : β < (R : ℝ) - 1 := by
    have hl := Real.log_lt_log logInputPos logInput
    rw [Real.log_pow] at hl
    have hd := Real.log_pos qOne
    dsimp [β]
    apply (div_lt_iff₀ hd).mpr
    have castR : (R - 1 : ℕ) = (R : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [castR] at hl
    exact hl
  have clockθ : 2 + 2 * β < (θ : ℝ) := by
    have ht : (θ : ℝ) = 2 * (R : ℝ) := by exact_mod_cast θEq
    linarith
  have injectiveRows : Set.InjOn (fun r : ℕ => X N (2 * r)) (Set.Ico 1 R) := by
    intro r hr s hs he
    change X N (2 * r) = X N (2 * s) at he
    by_contra hne
    have alt : r < s ∨ s < r := by omega
    rcases alt with hrs | hsr
    · have hd := decrease r s hr.1 hrs hs.2
      dsimp [a] at hd
      rw [he] at hd
      omega
    · have hd := decrease s r hs.1 hsr hr.2
      dsimp [a] at hd
      rw [he] at hd
      omega
  have cardRows : ((Finset.Ico 1 R).image (fun r => X N (2 * r))).card = R - 1 := by
    rw [Finset.card_image_of_injOn, Nat.card_Ico]
    simpa only [Finset.coe_Ico] using injectiveRows
  have physical : ∀ r : ℕ, 1 ≤ r → r < R →
      let y := X N (2 * r)
      (∀ j : ℕ, 2 ≤ j → y ≠ F j) ∧
      A < y ∧ y ≤ A + J ∧ A + J < N - 1 ∧ N - 1 < N ∧
      y < N - 1 ∧ y < N ∧
      naturalCap y = heightDeficit k (F k - y) ∧
      F (k - 5) ≤ naturalCap y ∧ (N : ℝ) / 13 ≤ (F (k - 5) : ℝ) := by
    intro r hr hrr
    obtain ⟨z, hz, hzj, hx⟩ := pairedPrefix r hr (by omega)
    have yLower : A < X N (2 * r) := by rw [hx]; omega
    have yUpper : X N (2 * r) ≤ A + J := by rw [hx]; omega
    have sumBefore : A + J < N - 1 := by dsimp [N]; omega
    have predLess : N - 1 < N := by omega
    have yBefore : X N (2 * r) < N - 1 := yUpper.trans_lt sumBefore
    have yFk : X N (2 * r) < F k := by dsimp [N] at yBefore; omega
    have block : Nat.greatestFib (X N (2 * r)) = k - 1 := by
      have lower := Nat.le_greatestFib.mpr (show F (k - 1) ≤ X N (2 * r) by omega)
      have upper := Nat.greatestFib_lt.mpr yFk
      omega
    have nonanchor : ∀ j : ℕ, 2 ≤ j → X N (2 * r) ≠ F j := by
      intro j hj he
      by_cases hjk : j < k
      · have hf := Nat.fib_mono (show j ≤ k - 1 by omega)
        change F j ≤ A at hf
        rw [he] at yLower
        omega
      · have hf := Nat.fib_mono (show k ≤ j by omega)
        rw [he] at yFk
        omega
    have capEq : naturalCap (X N (2 * r)) = heightDeficit k (F k - X N (2 * r)) := by
      unfold naturalCap heightDeficit
      rw [block]
      have row : F k - (F k - X N (2 * r)) = X N (2 * r) := by omega
      rw [row]
    obtain ⟨hi, hiz, hci⟩ := right z hz hzj
    have capLower : H ≤ naturalCap (X N (2 * r)) := by
      unfold naturalCap
      rw [block, hx]
      change H ≤ A - C (A + z)
      omega
    have fk13 : F k ≤ 13 * H := by
      omega
    have real13 : (N : ℝ) / 13 ≤ (F (k - 5) : ℝ) := by
      have hn13 : N ≤ 13 * H := by dsimp [N]; omega
      have hn13R : (N : ℝ) ≤ 13 * (H : ℝ) := by exact_mod_cast hn13
      change (N : ℝ) / 13 ≤ (H : ℝ)
      linarith
    exact ⟨nonanchor, yLower, yUpper, sumBefore, predLess,
      yBefore, by omega, capEq, capLower, real13⟩
  refine ⟨R, θ, μ, hR, θEq, entered, least, periodic, beforePeriodic,
    θμ, μdepth, dEq, σle, σdomain, ?_, x1, x2, a1bounds.1, a1bounds.2.1,
    ?_, decrease, terminal, earlyStop, lastStop, last.2.2.2.2.2.2.1, lastBound,
    ?_, gap, ?_, by omega, injectiveRows, cardRows, physical, clock, clockθ, uses⟩
  · change v - σ ≤ J
    omega
  · intro r hr hrr
    have pf := pairFacts r hr hrr
    dsimp only
    exact ⟨pf.1, pf.2.1, pf.2.2.1, pf.2.2.2.1, pf.2.2.2.2.1,
      pf.2.2.2.2.2.1, pf.2.2.2.2.2.2.1, pf.2.2.2.2.2.2.2.1,
      collar, by simpa only [Nat.sub_sub] using le_trans pf.2.2.2.2.2.2.2.1 collar,
      pf.2.2.2.2.2.2.2.2.1, pf.2.2.2.2.2.2.2.2.2.1,
      pf.2.2.2.2.2.2.2.2.2.2.1, pf.2.2.2.2.2.2.2.2.2.2.2⟩
  · simpa only [a, Int.cast_sub, Int.cast_natCast] using lastAffine
  · exact sub_nonneg.mpr (by exact_mod_cast entered.2)

end D5.S1.Recurrence.Invariants.CloitreActualExteriorEntrance
