/- GID: D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff
   generality: I
   mirror-B: D5/B/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Normalized Bell and contextuality inequalities obey the binary n-cycle trade-off. -/

import D5.S3.QuantumContext.NCycleNondisturbingGenerators
import D5.S3.QuantumBounds.MerminMeasurementDependence.Coordinates

/-! The binary generalized Bell scenario of Porto–Ruffolo–Rabelo–Terra Cunha–Kurzyński,
arXiv:2405.02964v2. Context `i` consists of measurements `i` and `finRotate n i`.
Boolean outcomes encode the two signs; `true` in an edge-sign vector means anticorrelation. -/

set_option autoImplicit false

noncomputable section

open Finset
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds (IsRowStochastic deterministicPostprocess)
open D5.S3.Quantum.Entanglement.BinaryDetectionThresholdRefutation (parityBox)

namespace D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff

/-- Joint conditional probabilities for two Alice settings and the cyclic Bob contexts. -/
abbrev Behavior (n : ℕ) := Fin 2 → Fin n → Bool → Bool → Bool → ℝ

/-- Bob's probabilities for the ordered outcomes in each cyclic context. -/
abbrev BobBehavior (n : ℕ) := Fin n → Bool → Bool → ℝ

/-- Alice's probabilities, indexed by setting and outcome. -/
abbrev AliceResponse := Fin 2 → Bool → ℝ

/-- Nondisturbance identifies the shared measurement in consecutive contexts. -/
def IsND {n : ℕ} (r : BobBehavior n) : Prop :=
  (∀ i b c, 0 ≤ r i b c) ∧
  (∀ i, ∑ b, ∑ c, r i b c = 1) ∧
  ∀ i c, ∑ b, r i b c = ∑ d, r (finRotate n i) c d

/-- Nonsignaling and nondisturbance, including the joint Alice/shared-Bob marginal. -/
def IsNSND {n : ℕ} (p : Behavior n) : Prop :=
  (∀ x i a b c, 0 ≤ p x i a b c) ∧
  (∀ x i, ∑ a, ∑ b, ∑ c, p x i a b c = 1) ∧
  (∀ x i a c, ∑ b, p x i a b c = ∑ d, p x (finRotate n i) a c d) ∧
  (∀ x y i b c, ∑ a, p x i a b c = ∑ a, p y i a b c) ∧
  ∀ x i j a, ∑ b, ∑ c, p x i a b c = ∑ b, ∑ c, p x j a b c

/-- The nonsignaling Bob marginal, read at Alice's setting zero. -/
def bobMarginal {n : ℕ} (p : Behavior n) : BobBehavior n :=
  fun i b c => ∑ a, p 0 i a b c

/-- An independent product of an Alice response and a Bob behavior. -/
def productBehavior {n : ℕ} (α : AliceResponse) (r : BobBehavior n) : Behavior n :=
  fun x i a b c => α x a * r i b c

/-- The context probabilities induced by a global deterministic assignment. -/
def deterministic {n : ℕ} (s : Fin n → Bool) : BobBehavior n :=
  fun i b c => deterministicPostprocess (fun j => (s j, s (finRotate n j))) i (b, c)

/-- Generalized locality permits arbitrary nondisturbing hidden Bob behaviors. -/
def IsGeneralizedLocal {n : ℕ} (p : Behavior n) : Prop :=
  p ∈ convexHull ℝ {q | ∃ α r, IsRowStochastic α ∧ IsND r ∧ q = productBehavior α r}

/-- Noncontextuality is the convex hull of global deterministic assignments. -/
def IsNoncontextual {n : ℕ} (r : BobBehavior n) : Prop :=
  r ∈ convexHull ℝ (Set.range (deterministic : (Fin n → Bool) → BobBehavior n))

/-- The affine Bell functional is nonpositive locally and has attained NSND maximum one. -/
def IsNormalizedGBell {n : ℕ} (f : (Behavior n →ₗ[ℝ] ℝ) × ℝ) : Prop :=
  (∀ p, IsGeneralizedLocal p → f.1 p + f.2 ≤ 0) ∧
  (∀ p, IsNSND p → f.1 p + f.2 ≤ 1) ∧
  ∃ p, IsNSND p ∧ f.1 p + f.2 = 1

/-- The affine contextuality functional has attained maximum one over NSND Bob marginals. -/
def IsNormalizedNC {n : ℕ} (t : (BobBehavior n →ₗ[ℝ] ℝ) × ℝ) : Prop :=
  (∀ r, IsNoncontextual r → t.1 r + t.2 ≤ 0) ∧
  (∀ p, IsNSND p → t.1 (bobMarginal p) + t.2 ≤ 1) ∧
  ∃ p, IsNSND p ∧ t.1 (bobMarginal p) + t.2 = 1

/-- The normalized nonlocality–contextuality trade-off for every binary n-cycle. -/
def claim : Prop :=
  ∀ n, 3 ≤ n → ∀ (f : (Behavior n →ₗ[ℝ] ℝ) × ℝ)
    (t : (BobBehavior n →ₗ[ℝ] ℝ) × ℝ),
    IsNormalizedGBell f → IsNormalizedNC t →
    ∀ p, IsNSND p → f.1 p + f.2 + (t.1 (bobMarginal p) + t.2) ≤ 1

private def oddSigns {n : ℕ} (γ : Fin n → Bool) : Prop :=
  (∏ i, if γ i then (-1 : ℝ) else 1) = -1

private def vertex {n : ℕ} (γ : Fin n → Bool) : BobBehavior n :=
  fun i b c => parityBox (fun _ _ => γ i) 0 0 b c

private def generators (n : ℕ) : Set (BobBehavior n) :=
  Set.range deterministic ∪ {r | ∃ γ, oddSigns γ ∧ r = vertex γ}

private lemma bob_nd {n : ℕ} {p : Behavior n} (hp : IsNSND p) :
    IsND (bobMarginal p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i b c
    exact sum_nonneg fun a _ => hp.1 0 i a b c
  · intro i
    change (∑ b, ∑ c, ∑ a, p 0 i a b c) = 1
    simpa only [Fintype.sum_bool, add_assoc, add_comm, add_left_comm] using hp.2.1 0 i
  · intro i c
    change (∑ b, ∑ a, p 0 i a b c) = ∑ d, ∑ a, p 0 (finRotate n i) a c d
    rw [sum_comm, sum_comm (f := fun d a => p 0 (finRotate n i) a c d)]
    exact sum_congr rfl fun a _ => hp.2.2.1 0 i a c

private lemma product_nsnd {n : ℕ} {α : AliceResponse} {r : BobBehavior n}
    (hα : IsRowStochastic α) (hr : IsND r) : IsNSND (productBehavior α r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x i a b c
    exact mul_nonneg (hα.1 x a) (hr.1 i b c)
  · intro x i
    dsimp only [productBehavior]
    simp only [← mul_sum, hr.2.1, mul_one]
    exact hα.2 x
  · intro x i a c
    dsimp only [productBehavior]
    simp_rw [← mul_sum, hr.2.2 i c]
  · intro x y i b c
    dsimp only [productBehavior]
    simp only [← sum_mul, hα.2, one_mul]
  · intro x i j a
    dsimp only [productBehavior]
    simp only [← mul_sum, hr.2.1, mul_one]

private lemma vertex_nd {n : ℕ} (γ : Fin n → Bool) : IsND (vertex γ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i b c
    rw [vertex.eq_1]
    dsimp only [parityBox]
    split_ifs <;> norm_num
  · intro i
    dsimp only [vertex, parityBox]
    cases h : γ i <;> norm_num [Fintype.sum_bool, h]
  · intro i c
    dsimp only [vertex, parityBox]
    cases h : γ i <;> cases k : γ (finRotate n i) <;>
      cases c <;> norm_num [Fintype.sum_bool, h, k]

private lemma bool_sign_sum {ι : Type} (s : Finset ι) (γ : ι → Bool) :
    (∏ i ∈ s, if γ i then (-1 : ℝ) else 1) = if ∑ i ∈ s, γ i then -1 else 1 := by
  classical
  let φ : Bool →+ ZMod 2 :=
    { toFun := fun b => (b.toNat : ZMod 2)
      map_zero' := rfl
      map_add' := by
        intro a b
        cases a <;> cases b <;> decide }
  change (∏ i ∈ s, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (γ i)) =
    D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign (∑ i ∈ s, γ i)
  rw [D5.S3.QuantumBounds.MerminMeasurementDependence.prod_boolSign]
  change D5.S3.QuantumBounds.MerminMeasurementDependence.bitSign (∑ i ∈ s, φ (γ i)) = _
  rw [← map_sum φ γ s]
  exact D5.S3.QuantumBounds.MerminMeasurementDependence.bitSign_boolBit _

private lemma even_signs_assignment {n : ℕ} (γ : Fin n → Bool) (hγ : ∑ i, γ i = false) :
    ∃ s : Fin n → Bool, ∀ i, Bool.xor (s i) (s (finRotate n i)) = γ i := by
  classical
  cases n with
  | zero => exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k =>
    let s : Fin (k + 1) → Bool := fun i => ∑ j ∈ univ.filter (fun j => j.val < i.val), γ j
    refine ⟨s, ?_⟩
    intro i
    by_cases hi : i.val < k
    · have hrot : finRotate (k + 1) i = ⟨i.val + 1, by omega⟩ := by
        simpa only [Fin.eta] using finRotate_of_lt hi
      have hfilter : univ.filter (fun j : Fin (k + 1) => j.val < i.val + 1) =
          insert i (univ.filter (fun j : Fin (k + 1) => j.val < i.val)) := by
        simpa only [Nat.lt_succ_iff, ← Fin.le_iff_val_le_val, ← Fin.lt_def,
          filter_ge_eq_Iic, filter_gt_eq_Iio] using (Iio_insert i).symm
      have hnmem : i ∉ univ.filter (fun j : Fin (k + 1) => j.val < i.val) := by simp
      rw [hrot]
      change Bool.xor (s i) (∑ j ∈ univ.filter (fun j => j.val < i.val + 1), γ j) = γ i
      rw [hfilter, sum_insert hnmem]
      change Bool.xor (s i) (γ i + s i) = γ i
      cases s i <;> cases γ i <;> rfl
    · have hilast : i = Fin.last k := Fin.ext (by simp only [Fin.val_last]; omega)
      subst i
      rw [finRotate_last]
      have hfilter : univ = insert (Fin.last k)
          (univ.filter (fun j : Fin (k + 1) => j.val < k)) := by
        change univ = insert (Fin.last k) (univ.filter fun j => j < Fin.last k)
        rw [filter_gt_eq_Iio, Iio_insert]
        exact Iic_top.symm
      have hnmem : Fin.last k ∉ univ.filter (fun j : Fin (k + 1) => j.val < k) := by simp
      have ht := hγ
      rw [hfilter, sum_insert hnmem] at ht
      have hs0 : s 0 = false := by simp [s, Bool.zero_eq_false]
      rw [hs0, Bool.xor_false]
      change γ (Fin.last k) + s (Fin.last k) = false at ht
      cases h₁ : γ (Fin.last k) <;> cases h₂ : s (Fin.last k) <;>
        simp only [h₁, h₂, Bool.add_eq_xor, Bool.false_xor, Bool.true_xor,
          Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false] at ht ⊢

private lemma even_vertex_noncontextual {n : ℕ} (γ : Fin n → Bool)
    (hγ : ∑ i, γ i = false) : IsNoncontextual (vertex γ) := by
  obtain ⟨s, hs⟩ := even_signs_assignment γ hγ
  change vertex γ ∈ convexHull ℝ (Set.range (deterministic : (Fin n → Bool) → BobBehavior n))
  have heq : vertex γ = (1 / 2 : ℝ) • deterministic s +
      (1 / 2 : ℝ) • deterministic (fun i => !(s i)) := by
    ext i b c
    change vertex γ i b c = (1 / 2 : ℝ) * deterministic s i b c +
      (1 / 2 : ℝ) * deterministic (fun j => !(s j)) i b c
    simp only [vertex, parityBox, deterministic, deterministicPostprocess, Prod.mk.injEq]
    simp only [← hs i]
    have hbinary (u v b c : Bool) :
        (if Bool.xor b c = Bool.xor u v then (1 / 2 : ℝ) else 0) =
          (1 / 2 : ℝ) * (if u = b ∧ v = c then 1 else 0) +
          (1 / 2 : ℝ) * (if (!u) = b ∧ (!v) = c then 1 else 0) := by
      cases u <;> cases v <;> cases b <;> cases c <;> norm_num
    exact hbinary (s i) (s (finRotate n i)) b c
  rw [heq]
  exact (convex_convexHull ℝ (Set.range (deterministic : (Fin n → Bool) → BobBehavior n)))
    (subset_convexHull ℝ _ ⟨s, rfl⟩)
    (subset_convexHull ℝ _ ⟨fun i => !(s i), rfl⟩)
    (by norm_num) (by norm_num) (by norm_num)

private lemma cycle_generators {n : ℕ} (hn : 3 ≤ n)
    (r : BobBehavior n) (hr : IsND r) : r ∈ convexHull ℝ (generators n) := by
  have hd := D5.S3.QuantumContext.NCycleNondisturbingGenerators.decomposition
    n (by omega) r hr.1 hr.2.1 hr.2.2
  change r ∈ convexHull ℝ (Set.range deterministic ∪ Set.range vertex) at hd
  apply convexHull_min ?_ (convex_convexHull ℝ (generators n)) hd
  rintro q (hq | ⟨γ, rfl⟩)
  · exact subset_convexHull ℝ _ (Or.inl hq)
  · by_cases hγ : oddSigns γ
    · exact subset_convexHull ℝ _ (Or.inr ⟨γ, hγ, rfl⟩)
    · have heven : ∑ i, γ i = false := by
        cases he : (∑ i, γ i) with
        | false => rfl
        | true =>
          exfalso
          apply hγ
          unfold oddSigns
          rw [bool_sign_sum, he]
          rfl
      exact convexHull_mono (fun _ h => Or.inl h) (even_vertex_noncontextual γ heven)

private lemma midpoint_noncontextual {n : ℕ}
    (γ η : Fin n → Bool) (hγ : oddSigns γ) (hη : oddSigns η) (hne : γ ≠ η) :
    IsNoncontextual ((1 / 2 : ℝ) • vertex γ + (1 / 2 : ℝ) • vertex η) := by
  classical
  have hsum (δ : Fin n → Bool) (hδ : oddSigns δ) : ∑ i, δ i = true := by
    have h := hδ
    unfold oddSigns at h
    rw [bool_sign_sum] at h
    cases he : (∑ i, δ i) with
    | false => rw [he] at h; norm_num at h
    | true => rfl
  have hex : ∃ j, γ j ≠ η j := Function.ne_iff.mp hne
  obtain ⟨j, hj⟩ := hex
  let δ := Function.update γ j (!(γ j))
  let ε := Function.update η j (!(η j))
  have hflip (ζ : Fin n → Bool) (hζ : ∑ i, ζ i = true) :
      ∑ i, Function.update ζ j (!(ζ j)) i = false := by
    apply Bool.eq_false_of_not_eq_true
    rw [← hζ, sum_eq_sum_iff_single (mem_univ j)
      (fun i _ hij => Function.update_of_ne hij _ _)]
    simp
  have hδ := even_vertex_noncontextual δ (hflip γ (hsum γ hγ))
  have hε := even_vertex_noncontextual ε (hflip η (hsum η hη))
  have heq : (1 / 2 : ℝ) • vertex γ + (1 / 2 : ℝ) • vertex η =
      (1 / 2 : ℝ) • vertex δ + (1 / 2 : ℝ) • vertex ε := by
    ext i b c
    change (1 / 2 : ℝ) * vertex γ i b c + (1 / 2 : ℝ) * vertex η i b c =
      (1 / 2 : ℝ) * vertex δ i b c + (1 / 2 : ℝ) * vertex ε i b c
    by_cases hi : i = j
    · subst i
      dsimp only [vertex, parityBox]
      cases h₁ : γ j <;> cases h₂ : η j <;> cases b <;> cases c <;>
        simp_all [δ, ε, Function.update]
    · dsimp only [vertex, parityBox]
      simp only [δ, ε, Function.update_of_ne hi]
  rw [heq]
  exact (convex_convexHull ℝ _) hδ hε (by norm_num) (by norm_num) (by norm_num)

private lemma unique_positive_generator {n : ℕ}
    (hgen : ∀ r : BobBehavior n, IsND r → r ∈ convexHull ℝ (generators n))
    (hmid : ∀ γ η : Fin n → Bool, oddSigns γ → oddSigns η → γ ≠ η →
      IsNoncontextual ((1 / 2 : ℝ) • vertex γ + (1 / 2 : ℝ) • vertex η))
    (t : (BobBehavior n →ₗ[ℝ] ℝ) × ℝ) (ht : IsNormalizedNC t) :
    ∃ γ : Fin n → Bool, oddSigns γ ∧ t.1 (vertex γ) + t.2 = 1 ∧
      ∀ η, oddSigns η → η ≠ γ → t.1 (vertex η) + t.2 ≤ 0 := by
  classical
  have hvertex (γ : Fin n → Bool) : t.1 (vertex γ) + t.2 ≤ 1 := by
    let α : AliceResponse := fun _ _ => 1 / 2
    have hα : IsRowStochastic α := by
      constructor
      · intros; norm_num [α]
      · intro x; norm_num [α, Fintype.sum_bool]
    have h := ht.2.1 (productBehavior α (vertex γ)) (product_nsnd hα (vertex_nd γ))
    have hm : bobMarginal (productBehavior α (vertex γ)) = vertex γ := by
      ext i b c
      dsimp only [bobMarginal, productBehavior]
      simp only [Fintype.sum_bool, α]
      ring
    rwa [hm] at h
  have hex : ∃ γ : Fin n → Bool, oddSigns γ ∧ t.1 (vertex γ) + t.2 = 1 := by
    by_contra hnone
    push Not at hnone
    obtain ⟨p, hp, hmax⟩ := ht.2.2
    have hsub : generators n ⊆ {r | t.1 r < 1 - t.2} := by
      intro r hr
      rcases hr with ⟨s, rfl⟩ | ⟨γ, hγ, rfl⟩
      · change t.1 (deterministic s) < 1 - t.2
        have h := ht.1 (deterministic s) (subset_convexHull ℝ _ ⟨s, rfl⟩)
        linarith
      · change t.1 (vertex γ) < 1 - t.2
        have hne := hnone γ hγ
        have hle := hvertex γ
        have hlt := lt_of_le_of_ne hle hne
        linarith
    have hconv : Convex ℝ {r : BobBehavior n | t.1 r < 1 - t.2} :=
      (convex_Iio (1 - t.2)).linear_preimage t.1
    have hlt := convexHull_min hsub hconv (hgen _ (bob_nd hp))
    change t.1 (bobMarginal p) < 1 - t.2 at hlt
    linarith
  obtain ⟨γ, hγ, hmax⟩ := hex
  refine ⟨γ, hγ, hmax, ?_⟩
  intro η hη hne
  have hm := ht.1 _ (hmid η γ hη hγ hne)
  simp only [map_add, map_smul, smul_eq_mul] at hm
  linarith

private lemma generator_dominance {n : ℕ}
    (r : BobBehavior n) (hr : r ∈ convexHull ℝ (generators n))
    (t : (BobBehavior n →ₗ[ℝ] ℝ) × ℝ) (ht : IsNormalizedNC t)
    (γ : Fin n → Bool) (hmax : t.1 (vertex γ) + t.2 = 1)
    (hother : ∀ η, oddSigns η → η ≠ γ → t.1 (vertex η) + t.2 ≤ 0) :
    ∃ v : ℝ, 0 ≤ v ∧ t.1 r + t.2 ≤ v ∧
      ∀ i b c, v * vertex γ i b c ≤ r i b c := by
  classical
  obtain ⟨ι, inst, w, z, hw, hsum, hz, heq⟩ := mem_convexHull_iff_exists_fintype.mp hr
  let v : ℝ := ∑ j, if z j = vertex γ then w j else 0
  have hznonneg (j : ι) (i : Fin n) (b c : Bool) : 0 ≤ z j i b c := by
    rcases hz j with ⟨s, hs⟩ | ⟨η, _, he⟩
    · rw [← hs]
      rw [deterministic.eq_1]
      dsimp only [deterministicPostprocess]
      split_ifs <;> norm_num
    · rw [he]
      exact (vertex_nd η).1 i b c
  have hzbound (j : ι) : t.1 (z j) + t.2 ≤ if z j = vertex γ then 1 else 0 := by
    split_ifs with hj
    · rw [hj, hmax]
    · rcases hz j with ⟨s, hs⟩ | ⟨η, hη, he⟩
      · rw [← hs]
        exact ht.1 _ (subset_convexHull ℝ _ ⟨s, rfl⟩)
      · rw [he]
        exact hother η hη (fun h => hj (he.trans (congrArg vertex h)))
  refine ⟨v, sum_nonneg (fun j _ => by split_ifs <;> first | exact hw j | exact le_rfl), ?_, ?_⟩
  · have heval : t.1 r + t.2 = ∑ j, w j * (t.1 (z j) + t.2) := by
      rw [← heq, map_sum]
      simp only [map_smul, smul_eq_mul, mul_add, sum_add_distrib, ← sum_mul, hsum, one_mul]
    rw [heval]
    have hle := sum_le_sum fun j (_ : j ∈ (univ : Finset ι)) =>
      mul_le_mul_of_nonneg_left (hzbound j) (hw j)
    simpa only [mul_ite, mul_one, mul_zero] using hle
  · intro i b c
    have heqpoint := congrArg (fun q : BobBehavior n => q i b c) heq
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at heqpoint
    rw [← heqpoint]
    change (∑ j, if z j = vertex γ then w j else 0) * vertex γ i b c ≤ _
    rw [sum_mul]
    apply sum_le_sum
    intro j hj
    split_ifs with he
    · rw [he]
    · simpa only [zero_mul] using mul_nonneg (hw j) (hznonneg j i b c)

private lemma slice_dominance {n : ℕ}
    (hgen : ∀ r : BobBehavior n, IsND r → r ∈ convexHull ℝ (generators n))
    (p : Behavior n) (hp : IsNSND p) (i₀ : Fin n) (x : Fin 2) (a : Bool)
    (t : (BobBehavior n →ₗ[ℝ] ℝ) × ℝ) (ht : IsNormalizedNC t)
    (γ : Fin n → Bool) (hmax : t.1 (vertex γ) + t.2 = 1)
    (hother : ∀ η, oddSigns η → η ≠ γ → t.1 (vertex η) + t.2 ≤ 0) :
    ∃ w : ℝ, 0 ≤ w ∧
      t.1 (fun i b c => p x i a b c) + (∑ b, ∑ c, p x i₀ a b c) * t.2 ≤ w ∧
      ∀ i b c, w * vertex γ i b c ≤ p x i a b c := by
  let m := ∑ b, ∑ c, p x i₀ a b c
  let q : BobBehavior n := fun i b c => p x i a b c
  have hm : 0 ≤ m := sum_nonneg fun b _ => sum_nonneg fun c _ => hp.1 x i₀ a b c
  have hmass (i : Fin n) : ∑ b, ∑ c, q i b c = m := hp.2.2.2.2 x i i₀ a
  by_cases hm0 : m = 0
  · have hq : q = 0 := by
      ext i b c
      have hb := (sum_eq_zero_iff_of_nonneg (fun b _ =>
        sum_nonneg fun c _ => hp.1 x i a b c)).mp ((hmass i).trans hm0)
      exact (sum_eq_zero_iff_of_nonneg (fun c _ => hp.1 x i a b c)).mp
        (hb b (mem_univ b)) c (mem_univ c)
    refine ⟨0, le_rfl, ?_, ?_⟩
    · change t.1 q + m * t.2 ≤ 0
      simp only [hq, hm0, map_zero, zero_mul, add_zero, le_refl]
    · intro i b c
      have hz := congrArg (fun r : BobBehavior n => r i b c) hq
      change p x i a b c = 0 at hz
      simp only [zero_mul, hz, le_refl]
  · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    let r : BobBehavior n := m⁻¹ • q
    have hr : IsND r := by
      refine ⟨?_, ?_, ?_⟩
      · intro i b c
        exact mul_nonneg (inv_nonneg.mpr hm) (hp.1 x i a b c)
      · intro i
        change (∑ b, ∑ c, m⁻¹ * q i b c) = 1
        simp only [← mul_sum, hmass, inv_mul_cancel₀ hm0]
      · intro i c
        change (∑ b, m⁻¹ * p x i a b c) = ∑ d, m⁻¹ * p x (finRotate n i) a c d
        rw [← mul_sum, ← mul_sum, hp.2.2.1 x i a c]
    obtain ⟨v, hv, hval, hdom⟩ := generator_dominance r (hgen r hr) t ht γ hmax hother
    have hqr : q = m • r := (smul_inv_smul₀ hm0 q).symm
    refine ⟨m * v, mul_nonneg hm hv, ?_, ?_⟩
    · change t.1 q + m * t.2 ≤ m * v
      rw [hqr, map_smul]
      change m * t.1 r + m * t.2 ≤ m * v
      nlinarith [mul_le_mul_of_nonneg_left hval hm]
    · intro i b c
      have h := mul_le_mul_of_nonneg_left (hdom i b c) hm
      have heq := congrArg (fun r : BobBehavior n => r i b c) hqr
      change q i b c = m * r i b c at heq
      change m * v * vertex γ i b c ≤ q i b c
      nlinarith

private lemma common_local_part {n : ℕ} (hn : 3 ≤ n)
    (hgen : ∀ r : BobBehavior n, IsND r → r ∈ convexHull ℝ (generators n))
    (p : Behavior n) (hp : IsNSND p)
    (t : (BobBehavior n →ₗ[ℝ] ℝ) × ℝ) (ht : IsNormalizedNC t)
    (hc : 0 < t.1 (bobMarginal p) + t.2)
    (γ : Fin n → Bool) (hmax : t.1 (vertex γ) + t.2 = 1)
    (hother : ∀ η, oddSigns η → η ≠ γ → t.1 (vertex η) + t.2 ≤ 0) :
    ∃ α : AliceResponse, IsRowStochastic α ∧
      ∀ x i a b c, (t.1 (bobMarginal p) + t.2) *
        (α x a * vertex γ i b c) ≤ p x i a b c := by
  classical
  let i₀ : Fin n := ⟨0, by omega⟩
  have hslices := fun x a => slice_dominance hgen p hp i₀ x a t ht γ hmax hother
  choose w hw hval hdom using hslices
  let total : Fin 2 → ℝ := fun x => ∑ a, w x a
  have htotal (x : Fin 2) : t.1 (bobMarginal p) + t.2 ≤ total x := by
    have h := sum_le_sum fun a (_ : a ∈ (univ : Finset Bool)) => hval x a
    have hq : (∑ a, (fun i b c => p x i a b c : BobBehavior n)) = bobMarginal p := by
      ext i b c
      dsimp only [bobMarginal]
      simpa only [Finset.sum_apply] using hp.2.2.2.1 x 0 i b c
    rw [sum_add_distrib, ← map_sum, ← sum_mul, hp.2.1 x i₀, one_mul, hq] at h
    exact h
  have hpos (x : Fin 2) : 0 < total x := hc.trans_le (htotal x)
  let α : AliceResponse := fun x a => w x a / total x
  have hα : IsRowStochastic α := by
    constructor
    · intro x a
      exact div_nonneg (hw x a) (hpos x).le
    · intro x
      change (∑ a, w x a / total x) = 1
      rw [← sum_div]
      exact div_self (hpos x).ne'
  refine ⟨α, hα, ?_⟩
  intro x i a b c
  have hscale : (t.1 (bobMarginal p) + t.2) * α x a ≤ w x a := by
    change _ * (w x a / total x) ≤ w x a
    rw [← mul_div_assoc]
    exact (div_le_iff₀ (hpos x)).mpr (by nlinarith [mul_le_mul_of_nonneg_right (htotal x) (hw x a)])
  have h := mul_le_mul_of_nonneg_right hscale ((vertex_nd γ).1 i b c)
  calc
    (t.1 (bobMarginal p) + t.2) * (α x a * vertex γ i b c) =
      ((t.1 (bobMarginal p) + t.2) * α x a) * vertex γ i b c := by ring
    _ ≤ w x a * vertex γ i b c := h
    _ ≤ p x i a b c := hdom x a i b c

private lemma dominated_local_tradeoff {n : ℕ}
    (p l : Behavior n) (hp : IsNSND p) (hl : IsNSND l)
    (hloc : IsGeneralizedLocal l) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hdom : ∀ x i a b d, c * l x i a b d ≤ p x i a b d)
    (f : (Behavior n →ₗ[ℝ] ℝ) × ℝ) (hf : IsNormalizedGBell f) :
    f.1 p + f.2 ≤ 1 - c := by
  by_cases he : c = 1
  · subst c
    have heq : l = p := by
      ext x i a b d
      have hle : ∀ a b d, l x i a b d ≤ p x i a b d := by
        intro a b d
        simpa only [one_mul] using hdom x i a b d
      have ha := (sum_eq_sum_iff_of_le (fun a _ => sum_le_sum fun b _ =>
        sum_le_sum fun d _ => hle a b d)).mp ((hl.2.1 x i).trans (hp.2.1 x i).symm)
      have hb := (sum_eq_sum_iff_of_le (fun b _ => sum_le_sum fun d _ => hle a b d)).mp
        (ha a (mem_univ a))
      exact ((sum_eq_sum_iff_of_le (fun d _ => hle a b d)).mp
        (hb b (mem_univ b))) d (mem_univ d)
    rw [← heq]
    simpa using hf.1 l hloc
  · have hpos : 0 < 1 - c := sub_pos.mpr (lt_of_le_of_ne hc1 he)
    let r : Behavior n := fun x i a b d =>
      (1 - c)⁻¹ * (p x i a b d - c * l x i a b d)
    have hr : IsNSND r := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro x i a b d
        exact mul_nonneg (inv_nonneg.mpr hpos.le) (sub_nonneg.mpr (hdom x i a b d))
      · intro x i
        simp only [r, ← mul_sum, sum_sub_distrib, hp.2.1, hl.2.1, mul_one]
        exact inv_mul_cancel₀ hpos.ne'
      · intro x i a d
        simp only [r, ← mul_sum, sum_sub_distrib, hp.2.2.1, hl.2.2.1]
      · intro x y i b d
        simp only [r, ← mul_sum, sum_sub_distrib]
        rw [hp.2.2.2.1 x y i b d, hl.2.2.2.1 x y i b d]
      · intro x i j a
        simp only [r, ← mul_sum, sum_sub_distrib]
        rw [hp.2.2.2.2 x i j a, hl.2.2.2.2 x i j a]
    have hrep : p = c • l + (1 - c) • r := by
      ext x i a b d
      change _ = c * l x i a b d + (1 - c) *
        ((1 - c)⁻¹ * (p x i a b d - c * l x i a b d))
      field_simp
      ring
    have hfl := hf.1 l hloc
    have hfr := hf.2.1 r hr
    have heval : f.1 p + f.2 = c * (f.1 l + f.2) + (1 - c) * (f.1 r + f.2) := by
      rw [hrep, map_add, map_smul, map_smul]
      simp only [smul_eq_mul]
      ring
    rw [heval]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hc.le hfl,
      mul_le_mul_of_nonneg_left hfr hpos.le]

/-- The Porto–Ruffolo–Rabelo–Terra Cunha–Kurzyński n-cycle conjecture. -/
theorem result : claim := by
  intro n hn f t hf ht p hp
  by_cases hc : t.1 (bobMarginal p) + t.2 ≤ 0
  · linarith [hf.2.1 p hp]
  · have hcpos : 0 < t.1 (bobMarginal p) + t.2 := lt_of_not_ge hc
    obtain ⟨γ, _, hmax, hother⟩ := unique_positive_generator
      (cycle_generators hn) midpoint_noncontextual t ht
    obtain ⟨α, hα, hdom⟩ := common_local_part hn
      (cycle_generators hn) p hp t ht hcpos γ hmax hother
    have hlocal : IsGeneralizedLocal (productBehavior α (vertex γ)) :=
      subset_convexHull ℝ _ ⟨α, vertex γ, hα, vertex_nd γ, rfl⟩
    have hbound := dominated_local_tradeoff p (productBehavior α (vertex γ)) hp
      (product_nsnd hα (vertex_nd γ)) hlocal (t.1 (bobMarginal p) + t.2)
      hcpos (ht.2.1 p hp) hdom f hf
    linarith

end D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff
