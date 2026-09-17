/- GID: D5/S3/Arith/Congruence/ActualCylinderChain
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/ActualCylinderChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Correlated full heads and actual odd-cover tails force averaged charge. -/

import D5.S3.Arith.Congruence.PurePrefixResidualLaw
import D5.S3.Arith.Congruence.ConditionalComparison.ArithmeticCoordinates
import D5.S3.Arith.Congruence.ConditionalComparison.ThreePrime.DistortionChain

/-!
Actual ordinary covering families are transported by the licensed original
CRT interface. An arbitrary law on the complete first b prime-power words may
retain every correlation; its support avoids all head-only original cylinders.
For each head the full-history tail distortion preserves pure-prefix avoidance,
and gluing head and tail gives an actual CRT point. Coverage forces average
charge at least one under that same joint law. No sparse-modulus hypothesis or
injectivity of projected tail cofactors is assumed: original labels remain.

The ending-coordinate construction is adapted from Michael Schroeder's MIT
ThreePrime/Model and ModelSemantics sources; unlike their PrefixModel, the
input here has no sparse field and uses actual exact residual laws. See
Library/Arith/schroeder2026noncoverage.md for source and license. Probability
packaging, exact residual probabilities, and the final charge inequality are
reused directly inside the support proof. This is arbitrary finite symbolic
probability, not an enumeration, checker, reduction or certified instance.
The full head height is required; no lift of an arbitrary truncated modulo-315
law is asserted. A charge budget below one is still needed for noncoverage.
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

abbrev HeadPoint {r : ℕ} (p H : Fin r → ℕ) (b : ℕ) (hb : b ≤ r) :=
  (i : Fin b) → Word (p (Fin.castLE hb i)) (H (Fin.castLE hb i))

def tailIndex {r b : ℕ} (hb : b ≤ r) (i : Fin (r - b)) : Fin r :=
  ⟨b + i.val, by omega⟩

def headMatch {κ : Type*} {r b : ℕ} {p H : Fin r → ℕ}
    (C : κ → Cylinder r p H) (hb : b ≤ r) (c : κ) (x : HeadPoint p H b hb) : Prop :=
  ∀ i : Fin b, HasPrefix (x i) ((C c).digits (Fin.castLE hb i))
    (indexedDepthLe ((C c).depth (Fin.castLE hb i)))

def headSafe {κ : Type*} {r b : ℕ} {p H : Fin r → ℕ}
    (C : κ → Cylinder r p H) (hb : b ≤ r) (x : HeadPoint p H b hb) : Prop :=
  ∀ c, (∀ j : Fin r, b ≤ j.val → ((C c).depth j).val = 0) → ¬ headMatch C hb c x

open Classical in
noncomputable def bad {κ : Type*} [Fintype κ] [DecidableEq κ]
    {r b : ℕ} {p H : Fin r → ℕ} (C : κ → Cylinder r p H) (hb : b ≤ r)
    (head : HeadPoint p H b hb) (k : ℕ) (hk : k < r - b)
    (x : Fin k → Cylinder.Point r p H) (y : Cylinder.Point r p H) : Bool :=
  decide (∃ c, ¬ (C c).Pure ∧ headMatch C hb c head ∧
    ((C c).depth ⟨b+k,by omega⟩).val ≠ 0 ∧
    (∀ j : Fin r, b+k < j.val → ((C c).depth j).val = 0) ∧
    (∀ i : Fin k, hit C c ⟨b+i.val,by omega⟩ (x i) = true) ∧
    hit C c ⟨b+k,by omega⟩ y = true)

noncomputable def build {κ : Type*} [Fintype κ] [DecidableEq κ]
    {r b : ℕ} {p H : Fin r → ℕ} (C : κ → Cylinder r p H) (hp : ∀ j, 3 ≤ p j)
    (hb : b ≤ r) (head : HeadPoint p H b hb)
    (δ : Fin (r - b) → ℚ) (hδ : ∀ i, 0 ≤ δ i ∧ δ i < 1) :
    (k : ℕ) → k ≤ r-b → PhysicalChain (Cylinder.Point r p H) k
  | 0, _ => .nil
  | k+1, hk =>
      (build C hp hb head δ hδ k (by omega)).snoc (base C hp)
        (bad C hb head k (by omega)) (δ ⟨k,by omega⟩) (hδ _).1 (hδ _).2

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
/-- Ordinary odd coverage forces charge under the same arbitrary supported
correlated head law and its full-history tail distortion. -/
theorem ordinary_cover_forces_charge_and_caps {L : ℕ} (S : OddDistinctCoveringSystem L)
    (b : ℕ) (hb : b ≤ S.supportSize)
    (μ : FiniteLaw (HeadPoint S.toPrimePowerCover.prime S.toPrimePowerCover.height b hb))
    (δ : Fin (S.supportSize - b) → ℚ) (hδ : ∀ i, 0 ≤ δ i ∧ δ i < 1) :
  let A := S.toPrimePowerCover
  let C := A.actualCylinder
  let hp : ∀ j, 3 ≤ A.prime j := fun j => by
    have h := (S.orderedPrime_prime j).two_le
    have hn := S.orderedPrime_ne_two j
    change 3 ≤ S.orderedPrime j
    omega
  let P := fun x => build C hp hb x δ hδ (S.supportSize - b) le_rfl
  μ.prob (headSafe C hb) = 1 →
    1 ≤ μ.expect (fun x => (P x).totalCharge) ∧
    ∀ (D : ℕ) (R : Fin (S.supportSize - b) → RunSpec D),
      (∀ c i, ((C c).depth (tailIndex hb i)).val ≠ 0 →
        cylinderProbability C hp c (tailIndex hb i) ≤
          (1-δ i) * (R i).survival ((C c).depth (tailIndex hb i)).val) →
      ∀ x, (P x).BaseCaps Finset.univ
        (fun c i => hit C c (tailIndex hb i))
        (fun c i => ((C c).depth (tailIndex hb i)).val) R := by
  classical
  let A := S.toPrimePowerCover
  let C := A.actualCylinder
  let hp : ∀ j, 3 ≤ A.prime j := fun j => by
    have h := (S.orderedPrime_prime j).two_le
    have hn := S.orderedPrime_ne_two j
    change 3 ≤ S.orderedPrime j
    omega
  let P := fun head => build C hp hb head δ hδ (S.supportSize - b) le_rfl
  change μ.prob (headSafe C hb) = 1 → 1 ≤ μ.expect (fun head => (P head).totalCharge) ∧ _
  intro hμ
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
  have hsupport (head : HeadPoint A.prime A.height b hb) :
      ∀ (k : ℕ) (hk : k ≤ S.supportSize-b),
      (build C hp hb head δ hδ k hk).kernels.law.prob
        (fun x => ∀ i : Fin k, Good (f ⟨b+i.val,by omega⟩)
          (x i ⟨b+i.val,by omega⟩)) = 1 := by
    intro k
    induction k with
    | zero => intro hk; simp [build, PhysicalChain.kernels, KernelChain.law,
        FiniteLaw.prob, FiniteLaw.expect_const]
    | succ k ih =>
      intro hk
      let i : Fin (S.supportSize - b) := ⟨k, by omega⟩
      let j : Fin S.supportSize := ⟨b+k, by omega⟩
      let K := fun x : Fin k → Cylinder.Point S.supportSize A.prime A.height =>
        (base C hp).distort (fun y => bad C hb head k i.isLt x y = true)
          (δ i) (hδ i).1 (hδ i).2
      have hgood (x : Fin k → Cylinder.Point S.supportSize A.prime A.height) :
          (K x).prob (fun y => Good (f j) (y j)) = 1 := by
        have hcap := (base C hp).distort_event_cap
          (fun y => bad C hb head k i.isLt x y = true) (fun y => ¬ Good (f j) (y j))
          (δ i) (hδ i).1 (hδ i).2
        rw [hbase_good, zero_div] at hcap
        have hz : (K x).prob (fun y => ¬ Good (f j) (y j)) = 0 :=
          le_antisymm hcap ((K x).prob_nonneg _)
        have htotal := (K x).prob_add_not (fun y => Good (f j) (y j))
        linarith
      change ((build C hp hb head δ hδ k (by omega)).kernels.snoc K).law.expect
        (fun x => if ∀ i : Fin (k+1),
          Good (f ⟨b+i.val,by omega⟩) (x i ⟨b+i.val,by omega⟩) then 1 else 0) = 1
      rw [KernelChain.expect_snoc]
      have he (x : Fin k → Cylinder.Point S.supportSize A.prime A.height) :
          (K x).expect (fun y => if ∀ i : Fin (k+1),
            Good (f ⟨b+i.val,by omega⟩)
              ((Fin.snoc x y : Fin (k+1) → Cylinder.Point S.supportSize A.prime A.height)
                i ⟨b+i.val,by omega⟩) then 1 else 0) =
          if ∀ i : Fin k, Good (f ⟨b+i.val,by omega⟩)
            (x i ⟨b+i.val,by omega⟩) then 1 else 0 := by
        simp_rw [Fin.forall_fin_succ']
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        change (K x).expect (fun y =>
          if (∀ i : Fin k, Good (f ⟨b+i.val,by omega⟩)
            (x i ⟨b+i.val,by omega⟩)) ∧ Good (f j) (y j) then 1 else 0) = _
        by_cases hx : ∀ i : Fin k, Good (f ⟨b+i.val,by omega⟩)
            (x i ⟨b+i.val,by omega⟩)
        · simpa [hx, FiniteLaw.prob] using hgood x
        · simp only [hx, false_and, if_false, FiniteLaw.expect_zero]
      rw [FiniteLaw.expect_congr _ he]
      exact ih (by omega)
  have hcovered (head : HeadPoint A.prime A.height b hb) (hhead : headSafe C hb head) :
      ∀ (k : ℕ) (hk : k ≤ S.supportSize-b)
      (x : Fin k → Cylinder.Point S.supportSize A.prime A.height),
      (∃ c, ¬ (C c).Pure ∧ headMatch C hb c head ∧
        (∀ j : Fin S.supportSize, b+k ≤ j.val → ((C c).depth j).val = 0) ∧
        (∀ i : Fin k, hit C c ⟨b+i.val,by omega⟩ (x i) = true)) →
      (build C hp hb head δ hδ k hk).covered x = true := by
    intro k
    induction k with
    | zero =>
      rintro hk x ⟨c, _, hm, hz, _⟩
      exact (hhead c (fun j hj => hz j (by omega)) hm).elim
    | succ k ih =>
      rintro hk x ⟨c, hnp, hm, hf, hh⟩
      change ((build C hp hb head δ hδ k (by omega)).covered (Fin.init x) ||
        bad C hb head k (by omega) (Fin.init x) (x (Fin.last k))) = true
      rw [Bool.or_eq_true]
      by_cases hz : ((C c).depth ⟨b+k,by omega⟩).val = 0
      · left
        apply ih (by omega) (Fin.init x)
        refine ⟨c, hnp, hm, ?_, fun i => hh i.castSucc⟩
        intro j hj
        by_cases he : j.val = b+k
        · have hjk : j = ⟨b+k,by omega⟩ := Fin.ext he
          rw [hjk]
          exact hz
        · exact hf j (by omega)
      · right
        apply decide_eq_true
        exact ⟨c, hnp, hm, hz, fun j hj => hf j (by omega),
          fun i => hh i.castSucc, hh (Fin.last k)⟩
  constructor
  · let J := μ.joint (fun head => (P head).kernels.law)
    have hcover_good (head : HeadPoint A.prime A.height b hb)
        (hhead : headSafe C hb head)
        (x : Fin (S.supportSize - b) → Cylinder.Point S.supportSize A.prime A.height)
        (hx : ∀ i, Good (f (tailIndex hb i)) (x i (tailIndex hb i))) :
        (P head).covered x = true := by
      let w : Cylinder.Point S.supportSize A.prime A.height := fun j =>
        if h : j.val < b then head ⟨j.val,h⟩
        else x ⟨j.val-b,by omega⟩ j
      have hheadword (i : Fin b) : w (Fin.castLE hb i) = head i := by
        simp [w, i.isLt]
      have htailword (i : Fin (S.supportSize - b)) :
          w (tailIndex hb i) = x i (tailIndex hb i) := by
        dsimp only [w]
        rw [dif_neg (by dsimp [tailIndex]; omega)]
        congr 1
        apply Fin.ext
        simp [tailIndex]
      obtain ⟨c,hc⟩ := A.actualCylinder_covers w
      have hm : headMatch C hb c head := by
        intro i
        have hi := hc (Fin.castLE hb i)
        rw [hheadword] at hi
        exact hi
      have htail : ∃ j : Fin S.supportSize, b ≤ j.val ∧ ((C c).depth j).val ≠ 0 := by
        by_contra hn
        apply hhead c ?_ hm
        intro j hj
        by_contra hpos
        exact hn ⟨j,hj,hpos⟩
      have hnp : ¬ (C c).Pure := by
        intro hcp
        obtain ⟨j,hjb,hj⟩ := htail
        let i : Fin (S.supportSize - b) := ⟨j.val-b,by omega⟩
        have hij : tailIndex hb i = j := by
          apply Fin.ext
          exact Nat.add_sub_of_le hjb
        have hgood : Good (f j) (w j) := by
          rw [← hij, htailword]
          exact hx i
        have havoid : ¬ HasPrefix (w j) ((f j) ((C c).depth j))
            (indexedDepthLe ((C c).depth j)) := by
          cases hd : (C c).depth j using Fin.cases with
          | zero => exact (hj (congrArg Fin.val hd)).elim
          | succ e => exact hgood e
        dsimp only [f] at havoid
        rw [forbidden_eq_digits C _ A.actualCylinder_depthInjective c hcp j hj] at havoid
        exact havoid (hc j)
      apply hcovered head hhead (S.supportSize - b) le_rfl x
      refine ⟨c, hnp, hm, fun j hj => by omega, ?_⟩
      intro i
      apply decide_eq_true
      have hi := hc (tailIndex hb i)
      rw [htailword] at hi
      exact hi
    have hpoint (head : HeadPoint A.prime A.height b hb) :
        (if headSafe C hb head then (1:ℚ) else 0) ≤
          (P head).kernels.law.prob (fun x => (P head).covered x = true) := by
      by_cases hh : headSafe C hb head
      · rw [if_pos hh]
        have hprob := (P head).kernels.law.prob_mono
          (fun x => ∀ i, Good (f (tailIndex hb i)) (x i (tailIndex hb i)))
          (fun x => (P head).covered x = true) (hcover_good head hh)
        have hs := hsupport head (S.supportSize - b) le_rfl
        change (P head).kernels.law.prob
          (fun x => ∀ i, Good (f (tailIndex hb i)) (x i (tailIndex hb i))) = 1 at hs
        rwa [hs] at hprob
      · rw [if_neg hh]
        exact (P head).kernels.law.prob_nonneg _
    have hJ : 1 ≤ J.prob (fun z => (P z.1).covered z.2 = true) := by
      rw [FiniteLaw.joint_prob]
      have h := μ.expect_mono hpoint
      change μ.prob (headSafe C hb) ≤ _ at h
      rwa [hμ] at h
    exact hJ.trans (by
      rw [FiniteLaw.joint_prob]
      exact μ.expect_mono (fun head => (P head).covered_probability_le))
  · intro D R hcap head
    have hprob (c : A.ActualSurvivor) (j : Fin S.supportSize) :
        (base C hp).prob (fun x => hit C c j x = true) = cylinderProbability C hp c j := by
      simp only [hit, decide_eq_true_eq]
      rw [hcoord j (fun w => HasPrefix w ((C c).digits j) (indexedDepthLe ((C c).depth j)))]
      exact (exists_exact_residual_law _ _ (hp j) (f j)).2.choose_spec.2
        ((C c).depth j) ((C c).digits j)
    have hc : ∀ (k : ℕ) (hk : k ≤ S.supportSize-b),
        (build C hp hb head δ hδ k hk).BaseCaps Finset.univ
          (fun c i => hit C c ⟨b+i.val,by omega⟩)
          (fun c i => ((C c).depth ⟨b+i.val,by omega⟩).val)
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
    exact hc (S.supportSize - b) le_rfl

#print axioms ordinary_cover_forces_charge_and_caps


end D5.S3.Arith.Congruence.ActualCylinderChain
