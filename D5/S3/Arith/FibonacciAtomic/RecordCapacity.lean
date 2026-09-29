/- GID: D5/S3/Arith/FibonacciAtomic/RecordCapacity
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/RecordCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Autonomous records retain every defective Smith coordinate at every precision. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace D5.S3.Arith.FibonacciAtomic.RecordCapacity

universe u

open Matrix

/-- A finite precision state. -/
abbrev State (d p r : ℕ) := Fin d → ZMod (p ^ r)

/-- Smith coordinates whose multipliers are divisible by the chosen prime. -/
abbrev Defect {d : ℕ} (p : ℕ) (s : Fin d → ℕ) := {i // p ∣ s i}

/-- An integer matrix acting at finite precision. -/
def action {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (p r : ℕ) :
    State d p r →+ State d p r :=
  (A.map (Int.castRingHom (ZMod (p ^ r)))).mulVecLin.toAddMonoidHom

/-- Extension by zero outside the defective coordinates. -/
def extend {d : ℕ} (p r : ℕ) (s : Fin d → ℕ) :
    (Defect p s → ZMod (p ^ r)) →+ State d p r where
  toFun x i := if h : p ∣ s i then x ⟨i, h⟩ else 0
  map_zero' := by funext i; dsimp; split <;> rfl
  map_add' x y := by funext i; dsimp; split <;> simp

/-- The defective subgroup expressed in the original input coordinates. -/
def defectInput {d : ℕ} (V : (Matrix (Fin d) (Fin d) ℤ)ˣ)
    (p r : ℕ) (s : Fin d → ℕ) :
    (Defect p s → ZMod (p ^ r)) →+ State d p r :=
  (action V.val p r).comp (extend p r s)

/-- Natural reduction of each coordinate by one precision level. -/
def reduce {ι : Type*} (p r : ℕ) :
    (ι → ZMod (p ^ (r + 1))) →+ (ι → ZMod (p ^ r)) where
  toFun x i := ZMod.castHom (pow_dvd_pow p (Nat.le_succ r)) (ZMod (p ^ r)) (x i)
  map_zero' := by ext i; simp
  map_add' x y := by
    funext i
    exact map_add (ZMod.castHom (pow_dvd_pow p (Nat.le_succ r)) (ZMod (p ^ r))) (x i) (y i)

/-- Record precisely the defective coordinates of the inverse Smith transform. -/
def canonicalRecord {d : ℕ} (V : (Matrix (Fin d) (Fin d) ℤ)ˣ)
    (p r : ℕ) (s : Fin d → ℕ) :
    State d p r →+ (Defect p s → ZMod (p ^ r)) where
  toFun x i := action V.inv p r x i
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

/-- Scalar multiplication boundary at positive precision level `n + 1`. -/
def scalarAction (p n : ℕ) : ZMod (p ^ (n + 1)) →+ ZMod (p ^ (n + 1)) :=
  nsmulAddMonoidHom p

/-- The highest base-`p` digit at positive precision level `n + 1`. -/
def highestDigit (p n : ℕ) (hp : 0 < p) (x : ZMod (p ^ (n + 1))) : Fin p := by
  letI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne'⟩
  exact ⟨x.val / p ^ n, (Nat.div_lt_iff_lt_mul (pow_pos hp n)).mpr
    (by simpa only [pow_succ'] using x.val_lt)⟩

/-- Natural scalar reduction between adjacent positive precision levels. -/
def scalarReduction (p n : ℕ) : ZMod (p ^ (n + 2)) →+* ZMod (p ^ (n + 1)) :=
  ZMod.castHom (pow_dvd_pow p (by omega)) (ZMod (p ^ (n + 1)))

/-- Boundary matrix of the three-node relation cycle. -/
def threeNodeB : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 2, 0; 0, 1, 2; 2, 0, 1]

/-- Exact single-level and cross-level claims for a scalar prime boundary.
The final clause quantifies arbitrary ℕ-indexed towers of finite record sets; the earlier clauses
exhibit the specific highest-digit record and its failed autonomous update. -/
def ScalarRecordExamples (p : ℕ) (hp : p.Prime) : Prop :=
  (∀ n, Nat.card (scalarAction p n).ker = p) ∧
  (∀ n (R : Type u) [Finite R] (η : ZMod (p ^ (n + 1)) → R),
    Function.Injective (fun x => (scalarAction p n x, η x)) → p ≤ Nat.card R) ∧
  (∀ n, Function.Injective (fun x =>
      (scalarAction p n x, highestDigit p n hp.pos x)) ∧ Nat.card (Fin p) = p) ∧
  (∀ n, ¬ ∃ ρ : Fin p → Fin p, ∀ x : ZMod (p ^ (n + 2)),
    ρ (highestDigit p (n + 1) hp.pos x) =
      highestDigit p n hp.pos (scalarReduction p n x)) ∧
  (∀ n (x : ZMod (p ^ (n + 2))),
    (highestDigit p n hp.pos (scalarReduction p n x)).val =
      (scalarAction p (n + 1) x).val / p ^ (n + 1)) ∧
  (∀ (R : ℕ → Type u) [∀ n, Fintype (R n)]
    (η : ∀ n, ZMod (p ^ (n + 1)) → R n) (ρ : ∀ n, R (n + 1) → R n),
    (∀ n, Function.Injective (fun x => (scalarAction p n x, η n x))) →
    (∀ n x, ρ n (η (n + 1) x) = η n (scalarReduction p n x)) →
    ∀ n, p ^ (n + 1) ≤ Fintype.card (R n))

/-- Concrete Smith certificate, exact kernel and record minima, and the
incompatibility of layerwise minimal records with an autonomous infinite tower. -/
def ThreeNodeRecordExamples : Prop :=
  (∃ U V : (Matrix (Fin 3) (Fin 3) ℤ)ˣ,
    U.val * threeNodeB * V.val = diagonal (fun i => ((![1, 1, 9] i : ℕ) : ℤ))) ∧
  (∀ r, Nat.card (action threeNodeB 3 r).ker = 3 ^ min r 2) ∧
  (∀ r (R : Type u) [Finite R] (η : State 3 3 r → R),
    Function.Injective (fun x => (action threeNodeB 3 r x, η x)) →
      3 ^ min r 2 ≤ Nat.card R) ∧
  (∀ r, ∃ η : State 3 3 r → Fin (3 ^ min r 2),
    Function.Injective (fun x => (action threeNodeB 3 r x, η x))) ∧
  (∀ (R : ℕ → Type u) [∀ n, Fintype (R n)]
    (η : ∀ n, State 3 3 (n + 1) → R n) (ρ : ∀ n, R (n + 1) → R n),
    (∀ n, Function.Injective (fun x => (action threeNodeB 3 (n + 1) x, η n x))) →
    (∀ n x, ρ n (η (n + 1) x) = η n (reduce 3 (n + 1) x)) →
    ∀ n, 3 ^ (n + 1) ≤ Fintype.card (R n)) ∧
  (∀ (R : ℕ → Type u) [∀ n, Fintype (R n)]
    (η : ∀ n, State 3 3 (n + 1) → R n) (ρ : ∀ n, R (n + 1) → R n),
    (∀ n, Function.Injective (fun x => (action threeNodeB 3 (n + 1) x, η n x))) →
    (∀ n x, ρ n (η (n + 1) x) = η n (reduce 3 (n + 1) x)) →
    ¬ (∀ n, Fintype.card (R n) = 3 ^ min (n + 1) 2))

/-- Record-only transitions force the sharp full-precision defect bound.
The scalar and three-node examples include their unrestricted minima,
explicit attaining records, and failures of autonomous minimal recording. -/
theorem autonomous_record_capacity :
    (∀ {d p : ℕ} (hp : p.Prime)
    (B : Matrix (Fin d) (Fin d) ℤ)
    (U V : (Matrix (Fin d) (Fin d) ℤ)ˣ) (s : Fin d → ℕ)
    (hSmith : U.val * B * V.val = diagonal (fun i => (s i : ℤ)))
    {R : ℕ → Type u} [∀ r, Fintype (R r)]
    (η : ∀ r, State d p (r + 1) → R r) (ρ : ∀ r, R (r + 1) → R r)
    (hjoint : ∀ r, Function.Injective (fun x => (action B p (r + 1) x, η r x)))
    (haut : ∀ r x, ρ r (η (r + 1) x) = η r (reduce p (r + 1) x)),
    (∀ r, Function.Injective (fun x => η r (defectInput V p (r + 1) s x)) ∧
      p ^ ((r + 1) * Fintype.card (Defect p s)) ≤ Fintype.card (R r)) ∧
    (∀ r, Function.Injective (fun x =>
      (action B p (r + 1) x, canonicalRecord V p (r + 1) s x)) ∧
      Nat.card (Defect p s → ZMod (p ^ (r + 1))) =
        p ^ ((r + 1) * Fintype.card (Defect p s))) ∧
    (∀ r x, reduce p (r + 1) (canonicalRecord V p (r + 2) s x) =
      canonicalRecord V p (r + 1) s (reduce p (r + 1) x))) ∧
    (∀ (q : ℕ) (hq : q.Prime), ScalarRecordExamples.{u} q hq) ∧
    ThreeNodeRecordExamples.{u} := by
  classical
  have tower : ∀ {d p : ℕ} (hp : p.Prime)
    (B : Matrix (Fin d) (Fin d) ℤ)
    (U V : (Matrix (Fin d) (Fin d) ℤ)ˣ) (s : Fin d → ℕ)
    (hSmith : U.val * B * V.val = diagonal (fun i => (s i : ℤ)))
    {R : ℕ → Type u} [∀ r, Fintype (R r)]
    (η : ∀ r, State d p (r + 1) → R r) (ρ : ∀ r, R (r + 1) → R r)
    (hjoint : ∀ r, Function.Injective (fun x => (action B p (r + 1) x, η r x)))
    (haut : ∀ r x, ρ r (η (r + 1) x) = η r (reduce p (r + 1) x)),
      (∀ r, Function.Injective (fun x => η r (defectInput V p (r + 1) s x)) ∧
      p ^ ((r + 1) * Fintype.card (Defect p s)) ≤ Fintype.card (R r)) ∧
    (∀ r, Function.Injective (fun x =>
      (action B p (r + 1) x, canonicalRecord V p (r + 1) s x)) ∧
      Nat.card (Defect p s → ZMod (p ^ (r + 1))) =
        p ^ ((r + 1) * Fintype.card (Defect p s))) ∧
    (∀ r x, reduce p (r + 1) (canonicalRecord V p (r + 2) s x) =
      canonicalRecord V p (r + 1) s (reduce p (r + 1) x)) := by
    intro d p hp B U V s hSmith R instR η ρ hjoint haut
    have hU (r) : Function.Injective (action U.val p r) :=
      Matrix.mulVec_injective_of_isUnit (U.isUnit.map (Int.castRingHom (ZMod (p ^ r))).mapMatrix)
    have hV (r) : Function.Injective (action V.val p r) :=
      Matrix.mulVec_injective_of_isUnit (V.isUnit.map (Int.castRingHom (ZMod (p ^ r))).mapMatrix)
    have hdiag (r) (x : State d p r) :
        action U.val p r (action B p r (action V.val p r x)) =
          fun i => (s i : ZMod (p ^ r)) * x i := by
      have hs := congrArg (fun A : Matrix (Fin d) (Fin d) ℤ =>
        A.map (Int.castRingHom (ZMod (p ^ r)))) hSmith
      simp only [Matrix.map_mul, Matrix.diagonal_map (map_zero _), map_natCast] at hs
      change (U.val.map (Int.castRingHom (ZMod (p ^ r)))) *ᵥ
        ((B.map (Int.castRingHom (ZMod (p ^ r)))) *ᵥ
        ((V.val.map (Int.castRingHom (ZMod (p ^ r)))) *ᵥ x)) = _
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hs]
      exact funext (Matrix.mulVec_diagonal _ _)
    have hinput (r) : Function.Injective (defectInput V p r s) := by
      apply (hV r).comp
      intro x y h
      funext i
      simpa [extend, i.property] using congrFun h i.val
    have hreduce (A : Matrix (Fin d) (Fin d) ℤ) (r) (x : State d p (r + 1)) :
        reduce p r (action A p (r + 1) x) = action A p r (reduce p r x) := by
      funext i
      change (ZMod.castHom (pow_dvd_pow p (Nat.le_succ r)) (ZMod (p ^ r)))
        ((A.map (Int.castRingHom (ZMod (p ^ (r + 1)))) *ᵥ x) i) = _
      rw [RingHom.map_mulVec]
      congr 1
      ext j k
      simp
    have hreduceInput (r) (x : Defect p s → ZMod (p ^ (r + 1))) :
        reduce p r (defectInput V p (r + 1) s x) =
          defectInput V p r s (reduce p r x) := by
      change reduce p r (action V.val p (r + 1) (extend p (r + 1) s x)) = _
      rw [hreduce]
      apply congrArg (action V.val p r)
      funext i
      by_cases hi : p ∣ s i <;> simp [reduce, extend, hi]
    have hsep : ∀ r, Function.Injective (fun x => η r (defectInput V p (r + 1) s x)) := by
      intro r
      induction r with
      | zero =>
        intro x y hxy
        apply hinput 1
        apply hjoint 0
        refine Prod.ext ?_ hxy
        apply hU 1
        change action U.val p 1 (action B p 1 (action V.val p 1 (extend p 1 s x))) =
          action U.val p 1 (action B p 1 (action V.val p 1 (extend p 1 s y)))
        rw [hdiag, hdiag]
        funext i
        by_cases hi : p ∣ s i
        · have hz : (s i : ZMod (p ^ 1)) = 0 :=
            (ZMod.natCast_eq_zero_iff _ _).mpr (by simpa using hi)
          simp [hz]
        · simp [extend, hi]
      | succ r ih =>
        have : NeZero (p ^ (r + 1 + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
        intro x y hxy
        dsimp only at hxy
        have hc : reduce p (r + 1) x = reduce p (r + 1) y := by
          apply ih
          dsimp only
          rw [← hreduceInput, ← hreduceInput, ← haut, ← haut, hxy]
        apply hinput (r + 1 + 1)
        apply hjoint (r + 1)
        refine Prod.ext ?_ hxy
        apply hU (r + 1 + 1)
        change action U.val p _ (action B p _ (action V.val p _ (extend p _ s x))) =
          action U.val p _ (action B p _ (action V.val p _ (extend p _ s y)))
        rw [hdiag, hdiag]
        funext i
        by_cases hi : p ∣ s i
        · let z := x ⟨i, hi⟩ - y ⟨i, hi⟩
          have hz : ZMod.castHom (pow_dvd_pow p (Nat.le_succ (r + 1)))
              (ZMod (p ^ (r + 1))) z = 0 := by
            rw [map_sub, sub_eq_zero]
            exact congrFun hc ⟨i, hi⟩
          have hdiv : p ^ (r + 1) ∣ z.val := by
            simpa only [ZMod.castHom_apply, ZMod.cast_eq_val,
              ZMod.natCast_eq_zero_iff] using hz
          obtain ⟨k, hk⟩ := hdiv
          have hpz : (p : ZMod (p ^ (r + 1 + 1))) * z = 0 := by
            rw [← ZMod.natCast_zmod_val z, ← Nat.cast_mul]
            apply (ZMod.natCast_eq_zero_iff _ _).mpr
            rw [hk, ← mul_assoc, ← pow_succ']
            exact dvd_mul_right _ _
          obtain ⟨a, ha⟩ := hi
          have hi : p ∣ s i := ⟨a, ha⟩
          have hsz : (s i : ZMod (p ^ (r + 1 + 1))) * z = 0 := by
            rw [ha, Nat.cast_mul, mul_comm (p : ZMod (p ^ (r + 1 + 1))), mul_assoc, hpz, mul_zero]
          simpa only [extend, AddMonoidHom.coe_mk, ZeroHom.coe_mk, dif_pos hi,
            z, mul_sub, sub_eq_zero] using hsz
        · simp [extend, hi]
    have hinverse (r) (x : State d p r) : action V.val p r (action V.inv p r x) = x := by
      change (V.val.map (Int.castRingHom (ZMod (p ^ r)))) *ᵥ
        ((V.inv.map (Int.castRingHom (ZMod (p ^ r)))) *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, V.val_inv]
      simp
    refine ⟨?_, ?_, ?_⟩
    · intro r
      have : NeZero (p ^ (r + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      refine ⟨hsep r, ?_⟩
      simpa only [Fintype.card_fun, ZMod.card, ← pow_mul] using
        Fintype.card_le_of_injective _ (hsep r)
    · intro r
      have : NeZero (p ^ (r + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      refine ⟨?_, by simp [Nat.card_eq_fintype_card, ← pow_mul]⟩
      intro x y hxy
      have hB := congrArg Prod.fst hxy
      have hR := congrArg Prod.snd hxy
      have hD : (fun i => (s i : ZMod (p ^ (r + 1))) * action V.inv p (r + 1) x i) =
          (fun i => (s i : ZMod (p ^ (r + 1))) * action V.inv p (r + 1) y i) := by
        rw [← hdiag, ← hdiag, hinverse, hinverse]
        exact congrArg (action U.val p (r + 1)) hB
      have heq : action V.inv p (r + 1) x = action V.inv p (r + 1) y := by
        funext i
        by_cases hi : p ∣ s i
        · exact congrFun hR ⟨i, hi⟩
        · exact ((ZMod.isUnit_natCast_iff_not_dvd_pow hp (Nat.succ_pos r)).mpr hi).mul_left_cancel
            (congrFun hD i)
      simpa only [hinverse] using congrArg (action V.val p (r + 1)) heq
    · intro r x
      funext i
      exact congrFun (hreduce V.inv (r + 1) x) i.val
  have capacity : ∀ (G H : Type) [AddGroup G] [AddGroup H] [Finite G]
      (f : G →+ H),
      (∀ (Q : Type u) [Finite Q] (η : G → Q),
        Function.Injective (fun x => (f x, η x)) → Nat.card f.ker ≤ Nat.card Q) ∧
      (∃ η : G → Fin (Nat.card f.ker), Function.Injective (fun x => (f x, η x))) := by
    intro G H instG instH instFinite f
    refine ⟨?_, ?_⟩
    · intro Q instQ η hη
      apply Nat.card_le_card_of_injective (fun x : f.ker => η x.val)
      intro x y hxy
      apply Subtype.ext
      apply hη
      exact Prod.ext (x.property.trans y.property.symm) hxy
    · let e : G ≃ f.range × f.rangeRestrict.ker :=
        (Equiv.sigmaPreimageEquiv f.rangeRestrict).symm.trans
          (Equiv.sigmaEquivProdOfEquiv fun y =>
            AddMonoidHom.fiberEquivKerOfSurjective f.rangeRestrict_surjective y)
      letI : Fintype f.rangeRestrict.ker := Fintype.ofFinite _
      have hcard : Fintype.card f.rangeRestrict.ker = Nat.card f.ker := by
        rw [← Nat.card_eq_fintype_card, AddMonoidHom.ker_rangeRestrict]
      let b : f.rangeRestrict.ker ≃ Fin (Nat.card f.ker) :=
        Fintype.equivOfCardEq (by simpa using hcard)
      refine ⟨fun x => b (e x).2, ?_⟩
      intro x y hxy
      apply e.injective
      apply Prod.ext
      · change f.rangeRestrict x = f.rangeRestrict y
        exact Subtype.ext (congrArg Prod.fst hxy)
      · exact b.injective (congrArg Prod.snd hxy)
  have scalarResult (p : ℕ) (hp : p.Prime) : ScalarRecordExamples.{u} p hp := by
    have hscalar (n : ℕ) (x : ZMod (p ^ (n + 1))) :
        scalarAction p n x = (p : ZMod (p ^ (n + 1))) * x := by
      change p • x = (p : ZMod (p ^ (n + 1))) * x
      exact nsmul_eq_mul _ _
    have hcount (n : ℕ) : Nat.card (scalarAction p n).ker = p := by
      letI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      change Nat.card (nsmulAddMonoidHom (α := ZMod (p ^ (n + 1))) p).ker = p
      rw [IsAddCyclic.card_nsmulAddMonoidHom_ker, Nat.card_zmod]
      apply Nat.gcd_eq_right
      simpa using (pow_dvd_pow p (show 1 ≤ n + 1 by omega))
    refine ⟨hcount, ?_, ?_, ?_, ?_, ?_⟩
    · intro n Q instQ η hη
      letI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      simpa only [hcount n] using
        (capacity (ZMod (p ^ (n + 1))) (ZMod (p ^ (n + 1))) (scalarAction p n)).1 Q η hη
    · intro n
      refine ⟨?_, by simp⟩
      have hraw : Function.Injective (fun x : ZMod (p ^ (n + 1)) =>
          ((p : ZMod (p ^ (n + 1))) * x, highestDigit p n hp.pos x)) := by
        letI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
        intro x y hxy
        have htop : x.val / p ^ n = y.val / p ^ n :=
          congrArg (fun z => z.2.val) hxy
        have hmul : ((p * x.val : ℕ) : ZMod (p ^ (n + 1))) =
            ((p * y.val : ℕ) : ZMod (p ^ (n + 1))) := by
          simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using congrArg Prod.fst hxy
        have hmod : Nat.ModEq (p * p ^ n) (p * x.val) (p * y.val) := by
          simpa only [pow_succ'] using (ZMod.natCast_eq_natCast_iff _ _ _).mp hmul
        have hrem := Nat.ModEq.mul_left_cancel' hp.ne_zero hmod
        change x.val % p ^ n = y.val % p ^ n at hrem
        apply ZMod.val_injective
        calc
          x.val = x.val % p ^ n + p ^ n * (x.val / p ^ n) :=
            (Nat.mod_add_div _ _).symm
          _ = y.val % p ^ n + p ^ n * (y.val / p ^ n) := by rw [hrem, htop]
          _ = y.val := Nat.mod_add_div _ _
      simpa only [hscalar] using hraw
    · intro n
      letI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      letI : NeZero (p ^ (n + 2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      have hpos : 0 < p ^ n := pow_pos hp.pos n
      have hsmall : p ^ n < p ^ (n + 1) := Nat.pow_lt_pow_right hp.one_lt (by omega)
      have hlarge : p ^ n < p ^ (n + 2) := Nat.pow_lt_pow_right hp.one_lt (by omega)
      rintro ⟨ρ, hρ⟩
      have heq : highestDigit p (n + 1) hp.pos (0 : ZMod (p ^ (n + 2))) =
          highestDigit p (n + 1) hp.pos ((p ^ n : ℕ) : ZMod (p ^ (n + 2))) := by
        apply Fin.ext
        simp only [highestDigit, ZMod.val_zero, Nat.zero_div]
        rw [ZMod.val_natCast_of_lt hlarge, Nat.div_eq_of_lt hsmall]
      have hc := (hρ 0).symm.trans
        ((congrArg ρ heq).trans (hρ ((p ^ n : ℕ) : ZMod (p ^ (n + 2)))))
      have hv := congrArg Fin.val hc
      change (scalarReduction p n 0).val / p ^ n =
        (scalarReduction p n ((p ^ n : ℕ) : ZMod (p ^ (n + 2)))).val / p ^ n at hv
      simp only [map_zero, map_natCast, ZMod.val_zero, Nat.zero_div] at hv
      rw [ZMod.val_natCast_of_lt hsmall, Nat.div_self hpos] at hv
      exact Nat.zero_ne_one hv
    · intro n x
      rw [hscalar]
      letI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      letI : NeZero (p ^ (n + 2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      have hb : ((p : ZMod (p ^ (n + 2))) * x).val =
          p * (x.val % p ^ (n + 1)) := by
        have hc : (p : ZMod (p ^ (n + 2))) * x = ((p * x.val : ℕ) : ZMod (p ^ (n + 2))) := by
          simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
        rw [hc, ZMod.val_natCast]
        calc
          _ = (p * x.val) % (p * p ^ (n + 1)) := by
            apply congrArg (fun modulus => (p * x.val) % modulus)
            simpa only [Nat.add_assoc] using (pow_succ' p (n + 1))
          _ = _ := Nat.mul_mod_mul_left _ _ _
      symm
      calc
        _ = p * (x.val % p ^ (n + 1)) / (p * p ^ n) := by
          simp only [hb, pow_succ' p n]
        _ = (x.val % p ^ (n + 1)) / p ^ n := Nat.mul_div_mul_left _ _ hp.pos
        _ = _ := by simp only [highestDigit, scalarReduction, ZMod.castHom_apply,
          ZMod.cast_eq_val, ZMod.val_natCast]
    · intro Q instQ η ρ hj ha
      have h := tower hp (diagonal (fun _ : Fin 1 => (p : ℤ)))
        1 1 (fun _ => p) (by simp) (fun n x => η n (x 0)) ρ
        (by
          intro n x y hxy
          have hb := congrFun (congrArg Prod.fst hxy) 0
          have he : scalarAction p n (x 0) = scalarAction p n (y 0) := by
            rw [hscalar, hscalar]
            simpa [action, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.diagonal] using hb
          have hr : η n (x 0) = η n (y 0) := congrArg Prod.snd hxy
          have he0 := hj n (Prod.ext he hr)
          funext i
          fin_cases i
          exact he0)
        (by intro n x; exact ha n (x 0))
      intro n
      simpa [Defect] using (h.1 n).2
  have threeResult : ThreeNodeRecordExamples.{u} := by
    let CU : (Matrix (Fin 3) (Fin 3) ℤ)ˣ :=
      {
        val := !![1, 0, 0; 0, 1, 0; -2, 4, 1]
        inv := !![1, 0, 0; 0, 1, 0; 2, -4, 1]
        val_inv := by
          ext i j
          fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
        inv_val := by
          ext i j
          fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
      }
    let CV : (Matrix (Fin 3) (Fin 3) ℤ)ˣ :=
      {
        val := !![1, -2, 4; 0, 1, -2; 0, 0, 1]
        inv := !![1, 2, 0; 0, 1, 2; 0, 0, 1]
        val_inv := by
          ext i j
          fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
        inv_val := by
          ext i j
          fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
      }
    have hs : CU.val * threeNodeB * CV.val =
        diagonal (fun i => ((![1, 1, 9] i : ℕ) : ℤ)) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [CU, CV, threeNodeB, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal]
    let kernelEquiv (r : ℕ) :
        (action threeNodeB 3 r).ker ≃ (nsmulAddMonoidHom (α := ZMod (3 ^ r)) 9).ker :=
      {
        toFun x := ⟨x.val 2, by
          have hx : (threeNodeB.map (Int.castRingHom (ZMod (3 ^ r)))) *ᵥ x.val = 0 := x.property
          have h0 := congrFun hx 0
          have h1 := congrFun hx 1
          have h2 := congrFun hx 2
          norm_num [threeNodeB, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
            Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at h0 h1 h2
          change 9 • x.val 2 = 0
          rw [nsmul_eq_mul]
          linear_combination h2 - 2 * h0 + 4 * h1⟩
        invFun t := ⟨![4 * t.val, -2 * t.val, t.val], by
          have ht0 : 9 • t.val = 0 := t.property
          have ht : (9 : ZMod (3 ^ r)) * t.val = 0 := by
            simpa [nsmul_eq_mul] using ht0
          change (threeNodeB.map (Int.castRingHom (ZMod (3 ^ r)))) *ᵥ
            ![4 * t.val, -2 * t.val, t.val] = 0
          ext i
          fin_cases i <;> norm_num [threeNodeB, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
          all_goals first | (solve | ring) | linear_combination ht⟩
        left_inv x := by
          have hx : (threeNodeB.map (Int.castRingHom (ZMod (3 ^ r)))) *ᵥ x.val = 0 := x.property
          have h0 := congrFun hx 0
          have h1 := congrFun hx 1
          norm_num [threeNodeB, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
          apply Subtype.ext
          funext i
          fin_cases i
          · change 4 * x.val 2 = x.val 0
            linear_combination 2 * h1 - h0
          · change -2 * x.val 2 = x.val 1
            linear_combination -h1
          · rfl
        right_inv t := by apply Subtype.ext; rfl
      }
    have hcount (r : ℕ) : Nat.card (action threeNodeB 3 r).ker = 3 ^ min r 2 := by
      letI : NeZero (3 ^ r) := ⟨pow_ne_zero _ (by decide)⟩
      calc
        Nat.card (action threeNodeB 3 r).ker =
            Nat.card (nsmulAddMonoidHom (α := ZMod (3 ^ r)) 9).ker :=
          Nat.card_congr (kernelEquiv r)
        _ = (3 ^ r).gcd 9 := by rw [IsAddCyclic.card_nsmulAddMonoidHom_ker, Nat.card_zmod]
        _ = 3 ^ min r 2 := by
          rcases le_total r 2 with h | h
          · rw [min_eq_left h]
            apply Nat.gcd_eq_left
            have hd := Nat.pow_dvd_pow 3 h
            norm_num at hd
            exact hd
          · rw [min_eq_right h]
            change (3 ^ r).gcd 9 = 9
            apply Nat.gcd_eq_right
            have hd := Nat.pow_dvd_pow 3 h
            norm_num at hd
            exact hd
    have htower : ∀ (Q : ℕ → Type u) [∀ n, Fintype (Q n)]
        (η : ∀ n, State 3 3 (n + 1) → Q n) (ρ : ∀ n, Q (n + 1) → Q n),
        (∀ n, Function.Injective (fun x => (action threeNodeB 3 (n + 1) x, η n x))) →
        (∀ n x, ρ n (η (n + 1) x) = η n (reduce 3 (n + 1) x)) →
        ∀ n, 3 ^ (n + 1) ≤ Fintype.card (Q n) := by
      intro Q instQ η ρ hj ha
      have h := tower (p := 3) (by decide) threeNodeB CU CV ![1, 1, 9] hs η ρ hj ha
      have hd : Fintype.card (Defect 3 (![1, 1, 9] : Fin 3 → ℕ)) = 1 := by decide
      intro n
      simpa only [hd, Nat.mul_one] using (h.1 n).2
    refine ⟨⟨CU, CV, hs⟩, hcount, ?_, ?_, htower, ?_⟩
    · intro r Q instQ η hη
      letI : NeZero (3 ^ r) := ⟨pow_ne_zero _ (by decide)⟩
      simpa only [hcount r] using
        (capacity (State 3 3 r) (State 3 3 r) (action threeNodeB 3 r)).1 Q η hη
    · intro r
      letI : NeZero (3 ^ r) := ⟨pow_ne_zero _ (by decide)⟩
      rw [← hcount r]
      exact (capacity (State 3 3 r) (State 3 3 r) (action threeNodeB 3 r)).2
    · intro Q instQ η ρ hj ha hminimal
      have hb := htower Q η ρ hj ha 2
      rw [hminimal 2] at hb
      norm_num at hb
  exact ⟨tower, scalarResult, threeResult⟩

#print axioms autonomous_record_capacity

end D5.S3.Arith.FibonacciAtomic.RecordCapacity
