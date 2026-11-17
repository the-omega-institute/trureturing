/- GID: D5/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/BergmanNoncommutativeSemigroup
   mirror-E: none(waiver:noncomputational)
   anchors: [mathlib/module/Mathlib.Algebra.Algebra.NonUnitalHom, mathlib/module/Mathlib.LinearAlgebra.Finsupp.LSum]
   utility: none
   digest: Noncommutative products and right-zero truncations preserve contracted cancellation. -/

import D5.S0.Certificates.Algebra.BergmanCyclicGrading

/-! # Noncommutative semigroups with contracted span cancellation -/

noncomputable section

namespace D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup

open BergmanQuestion15Refutation (Contracted delta product positivePower)
open BergmanQuestion23Refutation (mixedPower)
open BergmanCyclicGrading (positiveProduct)
open BergmanContractedAlgebra
open scoped BigOperators

open private delta_power algebra_nilpotent from
  D5.S0.Certificates.Algebra.BergmanCyclicGrading

/-- Four actual elements, with pq=r as the only nonzero product. -/
inductive FourElement where
  | zero | p | q | r
  deriving DecidableEq
instance : Fintype FourElement := ⟨{.zero, .p, .q, .r}, by intro x; cases x <;> simp⟩
abbrev N := FourElement
instance : Zero N := ⟨.zero⟩
private def nMul : N → N → N
  | .p, .q => .r
  | _, _ => .zero
instance : Mul N := ⟨nMul⟩
instance : SemigroupWithZero N where
  zero_mul a := by cases a <;> rfl
  mul_zero a := by cases a <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl

/-- All pairs, including those with exactly one zero component. -/
abbrev ProductModel := BergmanCyclicSemigroup.Model 6 true × N

/-- The literal degree truncation of the two-element right-zero semigroup.
The index i represents the positive degree i+1. -/
inductive RightZero (n : ℕ) where
  | zero
  | node (i : Fin n) (label : Bool)
  deriving DecidableEq, Fintype
instance {n} : Zero (RightZero n) := ⟨.zero⟩

private def rzMul {n} : RightZero n → RightZero n → RightZero n
  | .node i _, .node j b =>
    if h : i.val + j.val + 1 < n then .node ⟨i.val + j.val + 1, h⟩ b else .zero
  | _, _ => .zero
instance {n} : Mul (RightZero n) := ⟨rzMul⟩

instance {n} : SemigroupWithZero (RightZero n) where
  zero_mul a := by cases a <;> rfl
  mul_zero a := by cases a <;> rfl
  mul_assoc a b c := by
    cases a with
    | zero => rfl
    | node i x =>
      cases b with
      | zero => simp [HMul.hMul, Mul.mul, rzMul]
      | node j y =>
        cases c with
        | zero => simp [HMul.hMul, Mul.mul, rzMul]
        | node k z =>
          simp only [HMul.hMul, Mul.mul, rzMul]
          split_ifs <;> simp_all [rzMul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] <;>
            first | omega | (congr 1 <;> try apply Fin.ext <;> try apply propext <;> omega)

/-- Degree-one elements with the two right-zero labels. -/
def generator (n : ℕ) (hn : 0 < n) (b : Bool) : RightZero n := .node ⟨0, hn⟩ b

private theorem generator_power (n : ℕ) (hn : 0 < n) (b : Bool) (k : ℕ) (hk : k < n) :
    positivePower (generator n hn b) k = .node ⟨k, hk⟩ b := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [positivePower, ih (by omega)]
    simp [generator, HMul.hMul, Mul.mul, rzMul, hk]

private def degree {n} : RightZero n → ℕ
  | .zero => 0
  | .node i _ => i.val + 1

private theorem product_degree {n} (k : ℕ) (a : Fin (k + 1) → RightZero n)
    (h : positiveProduct k a ≠ 0) : k + 1 ≤ degree (positiveProduct k a) := by
  induction k with
  | zero =>
    cases he : a 0 with
    | zero => exact False.elim (h he)
    | node i b => simp [positiveProduct, he, degree]
  | succ k ih =>
    have ht : positiveProduct k (fun i => a i.succ) ≠ 0 :=
      fun he => h (by simp [positiveProduct, he])
    have hh := ih (fun i => a i.succ) ht
    cases he : a 0 with
    | zero => exact False.elim (h (by rw [positiveProduct, he]; exact zero_mul _))
    | node i x =>
      cases hf : positiveProduct k (fun i => a i.succ) with
      | zero => exact False.elim (ht hf)
      | node j y =>
        simp only [hf, degree] at hh
        simp only [positiveProduct, he, hf, HMul.hMul, Mul.mul, rzMul] at h ⊢
        by_cases hc : i.val + j.val + 1 < n
        · simp only [dite_eq_left hc, degree]
          omega
        · simp only [dite_eq_right hc] at h
          exact False.elim (h rfl)


private def rzEquiv (n : ℕ) : RightZero n ≃ Option (Fin n × Bool) where
  toFun
    | .zero => none
    | .node i b => some (i, b)
  invFun
    | none => .zero
    | some (i, b) => .node i b
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x with | none => rfl | some x => cases x; rfl

/-- The difference of the two actual degree-one basis vectors. -/
def difference (F : Type*) [Field F] (n : ℕ) (hn : 0 < n) : Contracted F (RightZero n) :=
  delta F (RightZero n) (generator n hn false) -
    delta F (RightZero n) (generator n hn true)

/-- The complete right-zero family, with arbitrary-product upper bounds and sharp lower bounds. -/
theorem right_zero_family (F : Type*) [Field F] (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (RightZero n) = 2 * n + 1 ∧
    (∃ a b : RightZero n, a * b ≠ b * a) ∧
    positivePower (generator n (by omega) false) (n - 1) ≠ 0 ∧
    positivePower (generator n (by omega) true) (n - 1) ≠ 0 ∧
    positivePower (generator n (by omega) false) (n - 1) ≠
      positivePower (generator n (by omega) true) (n - 1) ∧
    difference F n (by omega) ≠ 0 ∧
    difference F n (by omega) ∈ Submodule.span F
      (Set.range (fun b => delta F (RightZero n) (generator n (by omega) b))) ∧
    difference F n (by omega) * difference F n (by omega) = 0 ∧
    positivePower (difference F n (by omega)) (n - 1) = 0 ∧
    (∀ a : Fin (n + 1) → RightZero n, positiveProduct n a = 0) ∧
    mixedPower (product F (RightZero n)) ⊤ n = ⊥ ∧
    (∀ a : Fin (n + 1) → Contracted F (RightZero n), positiveProduct n a = 0) ∧
    positivePower (delta F (RightZero n) (generator n (by omega) false)) (n - 1) ≠ 0 := by
  have hp (b : Bool) := generator_power n (by omega) b (n - 1) (by omega)
  have hs : difference F n (by omega) * difference F n (by omega) = 0 := by
    simp only [difference, sub_mul, mul_sub, delta_mul]
    simp [generator, HMul.hMul, Mul.mul, rzMul, show 1 < n by omega]
  have hzero : ∀ a : Fin (n + 1) → RightZero n, positiveProduct n a = 0 := by
    intro a
    by_contra h
    have hh := product_degree n a h
    cases he : positiveProduct n a with
    | zero => exact h he
    | node i b => simp only [he, degree] at hh; have := i.isLt; omega
  have halg := algebra_nilpotent (F := F) n hzero
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hs, ?_, hzero, halg.1, halg.2, ?_⟩
  · rw [Fintype.card_congr (rzEquiv n)]
    simp [Fintype.card_prod, Nat.mul_comm]
  · refine ⟨generator n (by omega) false, generator n (by omega) true, ?_⟩
    simp [generator, HMul.hMul, Mul.mul, rzMul, show 1 < n by omega]
  · rw [hp false]; intro h; cases h
  · rw [hp true]; intro h; cases h
  · rw [hp false, hp true]; simp
  · intro h
    have hc := congrArg (fun v : Contracted F (RightZero n) =>
      v ⟨generator n (by omega) false, by simp [generator]⟩) h
    simp [difference, delta, generator] at hc
  · exact Submodule.sub_mem _ (Submodule.subset_span ⟨false, rfl⟩)
      (Submodule.subset_span ⟨true, rfl⟩)
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show 1 ≤ n - 1 by omega)
    rw [hk]
    clear hk
    induction k with
    | zero => exact hs
    | succ k ih => rw [Nat.add_succ, positivePower, ih, zero_mul]
  · rw [delta_power, hp false]
    simp [delta]

/-- The inclusion into the full direct product sends s to (s,0). -/
def includeZero (s : BergmanCyclicSemigroup.Model 6 true) : ProductModel := (s, 0)

/-- Its induced map uses the original contracted multiplication. -/
def embedding (F : Type*) [Field F] :
    Contracted F (BergmanCyclicSemigroup.Model 6 true) →ₙₐ[F] Contracted F ProductModel :=
  mapHom includeZero rfl (fun a b => by simp [includeZero, Prod.mul_def])

private theorem embedding_delta (F : Type*) [Field F]
    (s : BergmanCyclicSemigroup.Model 6 true) :
    embedding F (delta F _ s) = delta F ProductModel (s, 0) :=
  map_delta includeZero rfl s

private theorem embedding_injective (F : Type*) [Field F] :
    Function.Injective (embedding F) := by
  have hi : Function.LeftInverse
      (map (F := F) (Prod.fst : ProductModel → BergmanCyclicSemigroup.Model 6 true))
      (embedding F) := by
    intro a
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single s r =>
      have he : (Finsupp.single s r : Contracted F _) = r • delta F _ s.val := by
        simp [delta, s.property, Finsupp.smul_single]
      rw [he, map_smul, embedding_delta, map_smul, map_delta _ rfl]
  exact hi.injective

private theorem embedding_power (F : Type*) [Field F]
    (u : Contracted F (BergmanCyclicSemigroup.Model 6 true)) (k : ℕ) :
    embedding F (positivePower u k) = positivePower (embedding F u) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [positivePower, (embedding F).map_mul, ih]; rfl

private theorem pair_product {S T : Type*} [Mul S] [Mul T] (k : ℕ)
    (a : Fin (k + 1) → S × T) :
    positiveProduct k a = (positiveProduct k (fun i => (a i).1),
      positiveProduct k (fun i => (a i).2)) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [positiveProduct, ih]; rfl

private theorem include_power (s : BergmanCyclicSemigroup.Model 6 true) (k : ℕ) :
    positivePower (includeZero s) k = includeZero (positivePower s k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [positivePower, ih]; simp [includeZero, positivePower]

/-- The full 196-element product preserves the cyclic witness and has exact common index seven. -/
theorem product_family (F : Type*) [Field F] :
    Fintype.card N = 4 ∧ Fintype.card ProductModel = 196 ∧
    (∃ a b : ProductModel, a * b ≠ b * a) ∧
    Function.Injective (embedding F) ∧
    (∀ s, embedding F (delta F _ s) = delta F ProductModel (s, 0)) ∧
    (∀ a : Fin 7 → ProductModel, positiveProduct 6 a = 0) ∧
    mixedPower (product F ProductModel) ⊤ 6 = ⊥ ∧
    (∀ a : Fin 7 → Contracted F ProductModel, positiveProduct 6 a = 0) ∧
    Function.Injective (fun i : Fin 3 =>
      positivePower (includeZero (BergmanCyclicSemigroup.generator 6 true i)) 5) ∧
    (∀ i : Fin 3, positivePower
      (includeZero (BergmanCyclicSemigroup.generator 6 true i)) 5 ≠ 0) ∧
    positivePower (delta F ProductModel
      (includeZero (BergmanCyclicSemigroup.generator 6 true 0))) 5 ≠ 0 ∧
    (∀ (ω : F), IsPrimitiveRoot ω 3 →
      ∃ u ∈ Submodule.span F (Set.range (fun i =>
          delta F (BergmanCyclicSemigroup.Model 6 true)
            (BergmanCyclicSemigroup.generator 6 true i))),
        u ≠ 0 ∧ positivePower u 5 = 0 ∧
        embedding F u ∈ Submodule.span F (Set.range (fun i =>
          delta F ProductModel (includeZero (BergmanCyclicSemigroup.generator 6 true i)))) ∧
        embedding F u ≠ 0 ∧ positivePower (embedding F u) 5 = 0) := by
  have hn (a b c : N) : a * (b * c) = 0 := by
    cases a <;> cases b <;> cases c <;> rfl
  have hzero : ∀ a : Fin 7 → ProductModel, positiveProduct 6 a = 0 := by
    intro a
    rw [pair_product]
    apply Prod.ext
    · change positiveProduct 6 (fun i => (a i).1) = 0
      exact (BergmanCyclicGrading.nilpotency F 6 (by decide) true).1 _
    · exact hn _ _ _
  have halg := algebra_nilpotent (F := F) 6 hzero
  have hp (i : Fin 3) : positivePower
      (includeZero (BergmanCyclicSemigroup.generator 6 true i)) 5 =
      (BergmanCyclicSemigroup.Model.terminal i, 0) := by
    rw [include_power, BergmanCyclicSemigroup.terminal_powers 6 (by decide)]
    rfl
  refine ⟨by decide, ?_, ?_, embedding_injective F, embedding_delta F,
    hzero, halg.1, halg.2, ?_, ?_, ?_, ?_⟩
  · have hcard := (BergmanCyclicGrading.cardinalities.{0} 6 (by decide)).2.1
    norm_num [ProductModel, Fintype.card_prod, hcard, show Fintype.card N = 4 by decide]
  · refine ⟨(0, FourElement.p), (0, FourElement.q), ?_⟩
    intro h
    have hh := congrArg Prod.snd h
    cases hh
  · intro i j h
    simpa only [hp, Prod.mk.injEq, and_true, BergmanCyclicSemigroup.Model.terminal.injEq]
      using h
  · intro i; rw [hp]; intro h; have hh := congrArg Prod.fst h; cases hh
  · rw [delta_power, hp]
    simp [delta]
  · intro ω hω
    obtain ⟨u, hu, hne, hpow⟩ :=
      BergmanCyclicCoefficients.root_witness 6 (by decide) (by decide) true ω hω
    refine ⟨u, hu, hne, hpow, ?_, ?_, ?_⟩
    · clear hne hpow
      induction hu using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨i, rfl⟩ := hv
        rw [embedding_delta]
        exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add v w _ _ hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
      | smul r v _ hv => simpa only [map_smul] using Submodule.smul_mem _ r hv
    · intro h; exact hne ((embedding_injective F) (by simpa using h))
    · rw [← embedding_power, hpow, map_zero]

end D5.S0.Certificates.Algebra.BergmanNoncommutativeSemigroup
