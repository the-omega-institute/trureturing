/- GID: D5/S3/Topology/JBAlgebra
   generality: G
   mirror-B: D5/B/S3/Topology/JBAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Jordan.Basic]
   utility: none
   digest: JB powers generate an associative closed subspace with commuting ambient operators. -/

module

public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Single-generator structure on the original real normed carrier. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace D5.S3.Topology.JBAlgebra

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The genuine unital JB laws on the specified product and original norm.
Completeness is a separate analytic hypothesis, not needed for powers. -/
structure Data (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : X →ₗ[ℝ] X →ₗ[ℝ] X) (unit : X) : Prop where
  symm : ∀ x y, S x y = S y x
  unit_mul : ∀ x, S unit x = x
  jordan : ∀ x y, S (S x y) (S x x) = S x (S y (S x x))
  product_norm : ∀ x y, ‖S x y‖ ≤ ‖x‖ * ‖y‖
  square_norm : ∀ x, ‖S x x‖ = ‖x‖ ^ 2
  square_mono : ∀ x y, ‖S x x‖ ≤ ‖S x x + S y y‖

variable {S : X →ₗ[ℝ] X →ₗ[ℝ] X} {unit : X}

/-- Natural powers in the specified product, with zeroth power the specified unit. -/
def npow (S : X →ₗ[ℝ] X →ₗ[ℝ] X) (unit a : X) : ℕ → X
  | 0 => unit
  | n + 1 => S a (npow S unit a n)

/-- Continuous left multiplication on the entire original carrier. -/
def lmul (A : Data X S unit) (a : X) : X →L[ℝ] X :=
  (S a).mkContinuous ‖a‖ (fun x => A.product_norm a x)

private def bracket (S : X →ₗ[ℝ] X →ₗ[ℝ] X) (a b v : X) : X :=
  S a (S b v) - S b (S a v)

private theorem bracket_skew (a b v : X) : bracket S a b v = -bracket S b a v := by
  simp only [bracket, neg_sub]

private theorem polarized (A : Data X S unit) (a b c v : X) :
    bracket S a (S b c) v + bracket S b (S c a) v +
      bracket S c (S a b) v = 0 := by
  let _ : NonUnitalNonAssocCommRing X :=
    { (inferInstance : AddCommGroup X) with
      mul := fun x y => S x y
      left_distrib := fun x y z => (S x).map_add y z
      right_distrib := fun x y z => congrArg (fun f : X →ₗ[ℝ] X => f z) (S.map_add x y)
      zero_mul := fun x => congrArg (fun f : X →ₗ[ℝ] X => f x) S.map_zero
      mul_zero := fun x => (S x).map_zero
      mul_comm := A.symm }
  let _ : IsCommJordan X := ⟨A.jordan⟩
  have h := congrArg (fun f : AddMonoid.End X => f v)
    (two_nsmul_lie_lmul_lmul_add_add_eq_zero a b c)
  simp only [two_smul, Ring.lie_def] at h
  change (bracket S a (S b c) v + bracket S b (S c a) v +
    bracket S c (S a b) v) +
    (bracket S a (S b c) v + bracket S b (S c a) v +
    bracket S c (S a b) v) = 0 at h
  have hz : (2 : ℝ) • (bracket S a (S b c) v + bracket S b (S c a) v +
      bracket S c (S a b) v) = 0 := by simpa only [two_smul] using h
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

private theorem powers_structure (A : Data X S unit) (a : X) (N : ℕ) :
    (∀ i j, i + j = N → S (npow S unit a i) (npow S unit a j) = npow S unit a N) ∧
    (∀ i j, i + j = N → ∀ v, bracket S (npow S unit a i) (npow S unit a j) v = 0) := by
  let p := npow S unit a
  have hp0 : p 0 = unit := rfl
  have hp1 : p 1 = a := by
    change S a unit = a
    rw [A.symm, A.unit_mul]
  have hpS (n : ℕ) : p (n + 1) = S a (p n) := rfl
  have hunit (x v : X) : bracket S unit x v = 0 := by
    simp only [bracket, A.unit_mul, sub_self]
  induction N using Nat.strong_induction_on with
  | h N ih =>
    have prod (i j : ℕ) (hij : i + j = N) : S (p i) (p j) = p N := by
      cases j with
      | zero => simpa only [hp0, A.symm (p i) unit, A.unit_mul, Nat.add_zero] using congrArg p hij
      | succ j =>
        by_cases hj : j = 0
        · subst j
          rw [hp1, A.symm (p i) a, ← hpS, hij]
        · have hiN : i + 1 < N := by omega
          have hpij := (ih (i + j) (by omega)).1 i j rfl
          have hc := (ih (i + 1) hiN).2 i 1 rfl (p j)
          change S (p i) (S (p 1) (p j)) - S (p 1) (S (p i) (p j)) = 0 at hc
          rw [hp1, sub_eq_zero] at hc
          rw [hpS, hc, hpij, ← hpS]
          congr 1
    refine ⟨prod, ?_⟩
    intro i j hij v
    change bracket S (p i) (p j) v = 0
    by_cases hN : N ≤ 1
    · have casesIJ : i = 0 ∨ j = 0 := by omega
      rcases casesIJ with rfl | rfl
      · exact hunit _ _
      · rw [hp0, bracket_skew, hunit, neg_zero]
    · have Npos : 0 < N := by omega
      let c (k : ℕ) := bracket S (p k) (p (N - k)) v
      have cyc (r s t : ℕ) (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
          (hst : r + s + t = N) : c r + c s + c t = 0 := by
        have h := polarized A (p r) (p s) (p t) v
        rw [(ih (s + t) (by omega)).1 s t rfl,
          (ih (t + r) (by omega)).1 t r rfl,
          (ih (r + s) (by omega)).1 r s rfl] at h
        simpa only [c, show N - r = s + t by omega,
          show N - s = t + r by omega, show N - t = r + s by omega] using h
      have skew (k : ℕ) (hk : k ≤ N) : c (N - k) = -c k := by
        dsimp only [c]
        rw [Nat.sub_sub_self hk, bracket_skew]
      have mult (k : ℕ) (hk : k < N) : c k = k • c 1 := by
        induction k with
        | zero => simp only [c, hp0, hunit, zero_nsmul]
        | succ k ihk =>
          by_cases hk0 : k = 0
          · subst k
            simp only [zero_add, one_nsmul]
          · have hz := cyc 1 k (N - (k + 1)) (by omega) (by omega) (by omega) (by omega)
            rw [skew (k + 1) (by omega), ihk (by omega)] at hz
            have heq : c (k + 1) = c 1 + k • c 1 := by
              exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hz)).symm
            simpa only [succ_nsmul, add_comm] using heq
      have hlast := mult (N - 1) (by omega)
      rw [skew 1 (by omega)] at hlast
      have hn : N • c 1 = 0 := by
        have hn' : N = (N - 1) + 1 := by omega
        rw [hn', add_nsmul, one_nsmul, ← hlast]
        exact neg_add_cancel _
      have hc1 : c 1 = 0 := by
        have hr : (N : ℝ) • c 1 = 0 := by simpa only [Nat.cast_smul_eq_nsmul] using hn
        exact (smul_eq_zero.mp hr).resolve_left (by exact_mod_cast (Nat.ne_of_gt Npos))
      by_cases hi : i < N
      · have hm := mult i hi
        rw [hc1, nsmul_zero] at hm
        simpa only [c, show N - i = j by omega] using hm
      · have hj : j = 0 := by omega
        subst j
        rw [hp0, bracket_skew, hunit, neg_zero]

/-- Universal power multiplication in the original product. -/
theorem power_mul (A : Data X S unit) (a : X) (m n : ℕ) :
    S (npow S unit a m) (npow S unit a n) = npow S unit a (m + n) :=
  (powers_structure A a (m + n)).1 m n rfl

/-- Powers commute as multiplication operators on all of X, not only on their span. -/
theorem power_lmul_commute (A : Data X S unit) (a : X) (m n : ℕ) :
    Commute (lmul A (npow S unit a m)) (lmul A (npow S unit a n)) := by
  ext v
  exact sub_eq_zero.mp ((powers_structure A a (m + n)).2 m n rfl v)

/-- The actual norm-closed real span of all powers in the same carrier. -/
def generated (S : X →ₗ[ℝ] X →ₗ[ℝ] X) (unit a : X) : Submodule ℝ X :=
  (Submodule.span ℝ (Set.range (npow S unit a))).topologicalClosure

private theorem generated_induction (a : X) {P : X → Prop}
    (closed : IsClosed {x | P x}) (powers : ∀ n, P (npow S unit a n))
    (zero : P 0) (add : ∀ x y, P x → P y → P (x + y))
    (smul : ∀ (r : ℝ) x, P x → P (r • x))
    {x : X} (hx : x ∈ generated S unit a) : P x := by
  have hs : (Submodule.span ℝ (Set.range (npow S unit a)) : Set X) ⊆ {x | P x} := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => obtain ⟨n, rfl⟩ := hz; exact powers n
    | zero => exact zero
    | add x y _ _ hx hy => exact add x y hx hy
    | smul r x _ hx => exact smul r x hx
  exact closure_minimal hs closed hx

/-- The closed span is multiplicatively closed, associative, and its elements
have pairwise commuting left multiplication operators on the whole ambient X. -/
theorem generated_algebra (A : Data X S unit) (a : X) :
    (∀ x ∈ generated S unit a, ∀ y ∈ generated S unit a,
      S x y ∈ generated S unit a) ∧
    (∀ x ∈ generated S unit a, ∀ y ∈ generated S unit a,
      ∀ z ∈ generated S unit a, S (S x y) z = S x (S y z)) ∧
    (∀ x ∈ generated S unit a, ∀ y ∈ generated S unit a,
      Commute (lmul A x) (lmul A y)) := by
  let C := generated S unit a
  have Cclosed : IsClosed (C : Set X) := Submodule.isClosed_topologicalClosure _
  have power_mem (n : ℕ) : npow S unit a n ∈ C :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
  have right_cont (y : X) : Continuous (fun x => S x y) := by
    have h : Continuous (fun x => S y x) := (lmul A y).continuous
    exact h.congr (fun x => (A.symm y x))
  have prod_power (n : ℕ) {y : X} (hy : y ∈ C) : S (npow S unit a n) y ∈ C := by
    refine generated_induction a (P := fun y => S (npow S unit a n) y ∈ C)
      (Cclosed.preimage (lmul A _).continuous) ?_ ?_ ?_ ?_ hy
    · intro m
      rw [power_mul A]
      exact power_mem _
    · simp
    · intro x y hx hy
      simpa only [map_add] using C.add_mem hx hy
    · intro r x hx
      simpa only [map_smul] using C.smul_mem r hx
  have prod_closed {x y : X} (hx : x ∈ C) (hy : y ∈ C) : S x y ∈ C := by
    refine generated_induction a (P := fun x => S x y ∈ C)
      (Cclosed.preimage (right_cont y))
      (fun n => prod_power n hy) ?_ ?_ ?_ hx
    · simp
    · intro x z hx hz
      simpa only [map_add, LinearMap.add_apply] using C.add_mem hx hz
    · intro r x hx
      simpa only [map_smul, LinearMap.smul_apply, RingHom.id_apply] using C.smul_mem r hx
  have commute_power (n : ℕ) {y : X} (hy : y ∈ C) (v : X) :
      S (npow S unit a n) (S y v) = S y (S (npow S unit a n) v) := by
    refine generated_induction a
      (P := fun y => S (npow S unit a n) (S y v) = S y (S (npow S unit a n) v))
      (isClosed_eq ((lmul A _).continuous.comp (right_cont v))
        (right_cont (S (npow S unit a n) v))) ?_ ?_ ?_ ?_ hy
    · intro m
      exact congrArg (fun T : X →L[ℝ] X => T v) (power_lmul_commute A a n m).eq
    · simp
    · intro x y hx hy
      simp only [map_add, LinearMap.add_apply, hx, hy]
    · intro r x hx
      simp only [map_smul, LinearMap.smul_apply, hx]
  have comm {x y : X} (hx : x ∈ C) (hy : y ∈ C) (v : X) :
      S x (S y v) = S y (S x v) := by
    refine generated_induction a (P := fun x => S x (S y v) = S y (S x v))
      (isClosed_eq (right_cont (S y v))
        ((lmul A y).continuous.comp (right_cont v)))
      (fun n => commute_power n hy v) ?_ ?_ ?_ hx
    · simp
    · intro x z hx hz
      simp only [map_add, LinearMap.add_apply, hx, hz]
    · intro r x hx
      simp only [map_smul, LinearMap.smul_apply, hx]
  refine ⟨fun _ hx _ hy => prod_closed hx hy, ?_, ?_⟩
  · intro x hx y hy z hz
    rw [A.symm (S x y) z, comm hz hx y, A.symm z y]
  · intro x hx y hy
    ext v
    exact comm hx hy v



end D5.S3.Topology.JBAlgebra
