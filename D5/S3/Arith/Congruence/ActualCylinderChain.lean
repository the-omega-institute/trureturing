/- GID: D5/S3/Arith/Congruence/ActualCylinderChain
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/ActualCylinderChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unrestricted odd-cover chains preserve residual support and force charge. -/

import D5.S3.Arith.Congruence.PurePrefixResidualLaw
import D5.S3.Arith.Congruence.ConditionalComparison.ArithmeticCoordinates
import D5.S3.Arith.Congruence.ConditionalComparison.ThreePrime.DistortionChain

/-!
Actual ordinary covering families are transported by the licensed original
CRT interface. The new live support argument propagates pure-prefix avoidance
through the full-history distortion law on the ambient words, including its
zero-weight points. No bound on the support of a modulus is assumed.

The ending-coordinate construction is adapted from Michael Schroeder's MIT
ThreePrime/Model and ModelSemantics sources; unlike their PrefixModel, the
input here has no sparse field and uses actual exact residual laws. See
Library/Arith/schroeder2026noncoverage.md for source and license. Probability
packaging, exact residual probabilities, and the final charge inequality are
reused directly inside the support proof. This is arbitrary finite symbolic
probability, not an enumeration, checker, reduction or certified instance.
-/

open scoped BigOperators
open Erdos7 Erdos7.CappedGain Erdos7.ThreePrime
open D5.S3.Arith.Congruence.PurePrefixResidualLaw

namespace D5.S3.Arith.Congruence.ActualCylinderChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable def residual {p H : ℕ} (hp : 3 ≤ p) (f : ForbiddenPrefixesOf p H) :
    FiniteLaw (Word p H) := (exists_exact_residual_law p H hp f).2.choose

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {r : ℕ} {p H : Fin r → ℕ}

noncomputable def base (C : κ → Cylinder r p H) (hp : ∀ j, 3 ≤ p j) :
    FiniteLaw (Cylinder.Point r p H) :=
  FiniteLaw.piLaw (fun j => residual (hp j)
    (forbidden C (fun j => by have := hp j; omega) j))

noncomputable def hit (C : κ → Cylinder r p H) (c : κ) (j : Fin r)
    (x : Cylinder.Point r p H) : Bool :=
  decide (HasPrefix (x j) ((C c).digits j) (indexedDepthLe ((C c).depth j)))

open Classical in
noncomputable def bad (C : κ → Cylinder r p H) (k : ℕ) (hk : k < r)
    (x : Fin k → Cylinder.Point r p H) (y : Cylinder.Point r p H) : Bool :=
  decide (∃ c : κ, ¬ (C c).Pure ∧ ((C c).depth ⟨k,hk⟩).val ≠ 0 ∧
    (∀ j : Fin r, k < j.val → ((C c).depth j).val = 0) ∧
    (∀ i : Fin k, hit C c (Fin.castLE (by omega) i) (x i) = true) ∧
    hit C c ⟨k,hk⟩ y = true)

noncomputable def build (C : κ → Cylinder r p H) (hp : ∀ j, 3 ≤ p j)
    (δ : Fin r → ℚ) (hδ : ∀ j, 0 ≤ δ j ∧ δ j < 1) :
    (k : ℕ) → k ≤ r → PhysicalChain (Cylinder.Point r p H) k
  | 0, _ => .nil
  | k+1, hk =>
      (build C hp δ hδ k (by omega)).snoc (base C hp) (bad C k (by omega))
        (δ ⟨k,by omega⟩) (hδ _).1 (hδ _).2

noncomputable def cylinderProbability (C : κ → Cylinder r p H)
    (hp : ∀ j, 3 ≤ p j) (c : κ) (j : Fin r) : ℚ := by
  classical
  let f := forbidden C (fun j => by have := hp j; omega) j
  let d := (C c).depth j
  let u := (C c).digits j
  exact if blocked f d u then 0 else
    (1 / (p j : ℚ)^d.val -
      ∑ e ∈ forbiddenDescendants f d u, 1 / (p j : ℚ)^e.val) /
    (1 - ∑ e ∈ minimalForbiddenDepths f, 1 / (p j : ℚ)^e.val)

open Classical in
/-- Every ordinary finite distinct odd cover gives one actual unrestricted
physical chain with charge at least one. Exact residual-cylinder inequalities
suffice for all of its conditional comparison caps. -/
theorem ordinary_cover_forces_charge_and_caps {L : ℕ}
    (S : OddDistinctCoveringSystem L)
    (δ : Fin S.supportSize → ℚ)
    (hδ : ∀ j, 0 ≤ δ j ∧ δ j < 1) :
    let A := S.toPrimePowerCover
    let C := A.actualCylinder
    let hp : ∀ j, 3 ≤ A.prime j := fun j => by
      have h := (S.orderedPrime_prime j).two_le
      have hn := S.orderedPrime_ne_two j
      change 3 ≤ S.orderedPrime j
      omega
    let P := build C hp δ hδ S.supportSize le_rfl
    1 ≤ P.totalCharge ∧
    ∀ (D : ℕ) (R : Fin S.supportSize → RunSpec D),
      (∀ c j, ((C c).depth j).val ≠ 0 →
        cylinderProbability C hp c j ≤ (1 - δ j) * (R j).survival ((C c).depth j).val) →
      P.BaseCaps Finset.univ (hit C) (fun c j => ((C c).depth j).val) R := by
  classical
  let A := S.toPrimePowerCover
  let C := A.actualCylinder
  let hp : ∀ j, 3 ≤ A.prime j := fun j => by
    have h := (S.orderedPrime_prime j).two_le
    have hn := S.orderedPrime_ne_two j
    change 3 ≤ S.orderedPrime j
    omega
  change 1 ≤ (build C hp δ hδ S.supportSize le_rfl).totalCharge ∧ _
  let f := forbidden C (fun j => by have := hp j; omega)
  let ν := fun j => residual (hp j) (f j)
  have hweight (j : Fin S.supportSize) (w : Word (A.prime j) (A.height j)) :
      (ν j).weight w = if Good (f j) w then
        1 / ((A.prime j : ℚ)^(A.height j) *
          (1 - ∑ e ∈ minimalForbiddenDepths (f j), 1 / (A.prime j : ℚ)^e.val)) else 0 :=
    (exists_exact_residual_law _ _ (hp j) (f j)).2.choose_spec.1 w
  have hcoord (j : Fin S.supportSize)
      (E : Word (A.prime j) (A.height j) → Prop) [DecidablePred E] :
      (base C hp).prob (fun x => E (x j)) = (ν j).prob E :=
    FiniteLaw.piLaw_prob_coordinate ν j E
  have hbase_good (j : Fin S.supportSize) :
      (base C hp).prob (fun x => ¬ Good (f j) (x j)) = 0 := by
    rw [hcoord j (fun w => ¬ Good (f j) w)]
    unfold FiniteLaw.prob FiniteLaw.expect
    apply Finset.sum_eq_zero
    intro w _
    rw [hweight]
    by_cases hg : Good (f j) w <;> simp [hg]
  have hsupport : ∀ (k : ℕ) (hk : k ≤ S.supportSize),
      (build C hp δ hδ k hk).kernels.law.prob
        (fun x => ∀ i : Fin k, Good (f (Fin.castLE hk i)) (x i (Fin.castLE hk i))) = 1 := by
    intro k
    induction k with
    | zero => intro hk; simp [build, PhysicalChain.kernels, KernelChain.law,
        FiniteLaw.prob, FiniteLaw.expect_const]
    | succ k ih =>
      intro hk
      let j : Fin S.supportSize := ⟨k, by omega⟩
      let K := fun x : Fin k → Cylinder.Point S.supportSize A.prime A.height =>
        (base C hp).distort (fun y => bad C k j.isLt x y = true)
          (δ j) (hδ j).1 (hδ j).2
      have hgood (x : Fin k → Cylinder.Point S.supportSize A.prime A.height) :
          (K x).prob (fun y => Good (f j) (y j)) = 1 := by
        have hcap := (base C hp).distort_event_cap
          (fun y => bad C k j.isLt x y = true) (fun y => ¬ Good (f j) (y j))
          (δ j) (hδ j).1 (hδ j).2
        rw [hbase_good, zero_div] at hcap
        have hz : (K x).prob (fun y => ¬ Good (f j) (y j)) = 0 :=
          le_antisymm hcap ((K x).prob_nonneg _)
        have htotal := (K x).prob_add_not (fun y => Good (f j) (y j))
        linarith
      change ((build C hp δ hδ k (by omega)).kernels.snoc K).law.expect
        (fun x => if ∀ i : Fin (k+1),
          Good (f (Fin.castLE hk i)) (x i (Fin.castLE hk i)) then 1 else 0) = 1
      rw [KernelChain.expect_snoc]
      have he (x : Fin k → Cylinder.Point S.supportSize A.prime A.height) :
          (K x).expect (fun y => if ∀ i : Fin (k+1),
            Good (f (Fin.castLE hk i))
              ((Fin.snoc x y : Fin (k+1) → Cylinder.Point S.supportSize A.prime A.height)
                i (Fin.castLE hk i))
              then 1 else 0) =
          if ∀ i : Fin k, Good (f (Fin.castLE (by omega) i))
            (x i (Fin.castLE (by omega) i)) then 1 else 0 := by
        simp_rw [Fin.forall_fin_succ']
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        change (K x).expect (fun y =>
          if (∀ i : Fin k, Good (f (Fin.castLE (by omega) i))
            (x i (Fin.castLE (by omega) i))) ∧ Good (f j) (y j) then 1 else 0) = _
        by_cases hx : ∀ i : Fin k, Good (f (Fin.castLE (by omega) i))
            (x i (Fin.castLE (by omega) i))
        · simpa [hx, FiniteLaw.prob] using hgood x
        · simp only [hx, false_and, if_false, FiniteLaw.expect_zero]
      rw [FiniteLaw.expect_congr _ he]
      exact ih (by omega)
  have hcovered : ∀ (k : ℕ) (hk : k ≤ S.supportSize)
      (x : Fin k → Cylinder.Point S.supportSize A.prime A.height),
      (∃ c, ¬ (C c).Pure ∧
        (∀ j : Fin S.supportSize, k ≤ j.val → ((C c).depth j).val = 0) ∧
        (∀ i : Fin k, hit C c (Fin.castLE hk i) (x i) = true)) →
      (build C hp δ hδ k hk).covered x = true := by
    intro k
    induction k with
    | zero =>
      rintro hk x ⟨c, _, hz, _⟩
      obtain ⟨j,hj⟩ := A.actualCylinder_nontrivial c
      exact (hj (hz j (Nat.zero_le _))).elim
    | succ k ih =>
      rintro hk x ⟨c, hnp, hf, hh⟩
      change ((build C hp δ hδ k (by omega)).covered (Fin.init x) ||
        bad C k (by omega) (Fin.init x) (x (Fin.last k))) = true
      rw [Bool.or_eq_true]
      by_cases hz : ((C c).depth ⟨k,by omega⟩).val = 0
      · left
        apply ih (by omega) (Fin.init x)
        refine ⟨c, hnp, ?_, fun i => hh i.castSucc⟩
        intro j hj
        by_cases he : j.val = k
        · have hjk : j = ⟨k,by omega⟩ := Fin.ext he
          rw [hjk]
          exact hz
        · exact hf j (by omega)
      · right
        apply decide_eq_true
        exact ⟨c, hnp, hz, fun j hj => hf j (by omega),
          fun i => hh i.castSucc, hh (Fin.last k)⟩
  constructor
  · let P := build C hp δ hδ S.supportSize le_rfl
    have hcover_good (x : Fin S.supportSize → Cylinder.Point S.supportSize A.prime A.height)
        (hx : ∀ i, Good (f i) (x i i)) : P.covered x = true := by
      let w : Cylinder.Point S.supportSize A.prime A.height := fun j => x j j
      obtain ⟨c,hc⟩ := A.actualCylinder_covers w
      have hnp : ¬ (C c).Pure := by
        intro hcp
        obtain ⟨j,hj⟩ := A.actualCylinder_nontrivial c
        change ((C c).depth j).val ≠ 0 at hj
        have hgood := hx j
        have havoid : ¬ HasPrefix (w j) ((f j) ((C c).depth j))
            (indexedDepthLe ((C c).depth j)) := by
          cases hd : (C c).depth j using Fin.cases with
          | zero => exact (hj (congrArg Fin.val hd)).elim
          | succ e => exact hgood e
        dsimp only [f] at havoid
        rw [forbidden_eq_digits C _ A.actualCylinder_depthInjective c hcp j hj] at havoid
        exact havoid (hc j)
      apply hcovered S.supportSize le_rfl x
      refine ⟨c, hnp, fun j hj => by omega, ?_⟩
      intro j
      exact decide_eq_true (hc j)
    have hprob := P.kernels.law.prob_mono
      (fun x => ∀ i, Good (f i) (x i i)) (fun x => P.covered x = true) hcover_good
    have hs := hsupport S.supportSize le_rfl
    change P.kernels.law.prob (fun x => ∀ i, Good (f i) (x i i)) = 1 at hs
    rw [hs] at hprob
    exact hprob.trans P.covered_probability_le
  · intro D R hcap
    have hprob (c : A.ActualSurvivor) (j : Fin S.supportSize) :
        (base C hp).prob (fun x => hit C c j x = true) = cylinderProbability C hp c j := by
      simp only [hit, decide_eq_true_eq]
      rw [hcoord j (fun w => HasPrefix w ((C c).digits j) (indexedDepthLe ((C c).depth j)))]
      exact (exists_exact_residual_law _ _ (hp j) (f j)).2.choose_spec.2
        ((C c).depth j) ((C c).digits j)
    have hc : ∀ (k : ℕ) (hk : k ≤ S.supportSize),
        (build C hp δ hδ k hk).BaseCaps Finset.univ
          (fun c i => hit C c (Fin.castLE hk i))
          (fun c i => ((C c).depth (Fin.castLE hk i)).val)
          (fun i => R (Fin.castLE hk i)) := by
      intro k
      induction k with
      | zero => intro hk; trivial
      | succ k ih =>
        intro hk
        constructor
        · exact ih (by omega)
        · intro c _ hd
          rw [hprob]
          exact hcap c ⟨k,by omega⟩ hd
    exact hc S.supportSize le_rfl

#print axioms ordinary_cover_forces_charge_and_caps

end D5.S3.Arith.Congruence.ActualCylinderChain
