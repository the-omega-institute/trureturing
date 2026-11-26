/- GID: D5/S3/HomologicalAlgebra/SplitQuadraticCubic
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A cubic supported on the nonsingular cone has a single affine factor. -/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic

/-! Cubic Boolean polynomials supported on terms containing a full
hyperbolic pair. Vanishing on singular vectors forces a product
of the split quadratic form with an affine linear function. -/

@[expose] public section

open scoped BigOperators
set_option autoImplicit false

namespace D5.S3.HomologicalAlgebra.SplitQuadraticCubic

abbrev Bit := ZMod 2

variable {ι : Type*}

/-- Every coefficient supported on a set without a full hyperbolic pair vanishes.
The argument only uses downward closure of these supports. -/
theorem coefficient_zero_on_pair_free (c : Finset (ι × Bool) → Bit)
    (h : ∀ s : Finset (ι × Bool),
      (∀ i, (i, false) ∈ s → (i, true) ∉ s) → ∑ t ∈ s.powerset, c t = 0)
    (s : Finset (ι × Bool)) (hs : ∀ i, (i, false) ∈ s → (i, true) ∉ s) :
    c s = 0 := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hsum := h s hs
    rw [Finset.sum_eq_single s] at hsum
    · exact hsum
    · intro t ht hts
      have sub := Finset.mem_powerset.mp ht
      exact ih t (lt_of_le_of_ne sub hts) (fun i hf ht' => hs i (sub hf) (sub ht'))
    · exact fun hnot => (hnot (Finset.mem_powerset_self s)).elim

variable [Fintype ι] [DecidableEq ι]

def form (f x : ι → Bit) : Bit := ∑ j, f j * x j

private def pairVector (i k : ι) (t : ι) : Bit :=
  if t = i ∨ t = k then 1 else 0

private theorem sum_pairVector_mul (i k : ι) (hik : i ≠ k) (f : ι → Bit) :
    ∑ t, pairVector i k t * f t = f i + f k := by
  have h : ∀ t ∉ ({i, k} : Finset ι), t ∈ (Finset.univ : Finset ι) →
      pairVector i k t * f t = 0 := by
    intro t ht _
    have hn : ¬(t = i ∨ t = k) := by simpa using ht
    simp [pairVector, hn]
  rw [← Finset.sum_subset (Finset.subset_univ {i,k}) (fun t ht hnot => h t hnot ht)]
  simp [pairVector, hik]

private theorem form_pairVector (f : ι → Bit) (i k : ι) (hik : i ≠ k) :
    form f (pairVector i k) = f i + f k := by
  simp_rw [form, mul_comm (f _)]
  exact sum_pairVector_mul i k hik f

private theorem form_add_single (f x : ι → Bit) (j : ι) :
    form f (x + Pi.single j 1) = form f x + f j := by
  simp only [form, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  simp [Pi.single_apply, mul_ite]

def evaluate (a : ι → Bit) (b c : ι → ι → Bit) (x y : ι → Bit) : Bit :=
  ∑ i, (x i * y i) * (a i + form (b i) x + form (c i) y)

def quadratic (x y : ι → Bit) : Bit := ∑ i, x i * y i

private theorem evaluate_pair (a : ι → Bit) (b c : ι → ι → Bit)
    {i k : ι} (hik : i ≠ k) (x y : ι → Bit)
    (hs : ∀ t, x t * y t = pairVector i k t) :
    evaluate a b c x y =
      (a i + form (b i) x + form (c i) y) + (a k + form (b k) x + form (c k) y) := by
  simp_rw [evaluate, hs]
  exact sum_pairVector_mul i k hik _

private theorem quadratic_pair {i k : ι} (hik : i ≠ k) (x y : ι → Bit)
    (hs : ∀ t, x t * y t = pairVector i k t) : quadratic x y = 0 := by
  simp_rw [quadratic, hs]
  simpa only [mul_one, CharTwo.add_self_eq_zero] using
    sum_pairVector_mul i k hik (fun _ => 1)

omit [Fintype ι] in
private theorem pairVector_sq (i k t : ι) :
    pairVector i k t * pairVector i k t = pairVector i k t := by
  by_cases h : t = i ∨ t = k <;> simp [pairVector, h]

omit [DecidableEq ι] in
private theorem stable_coefficients (a : ι → Bit) (b c : ι → ι → Bit)
    (hvanish : ∀ x y, quadratic x y = 0 → evaluate a b c x y = 0)
    {i k j : ι} (hij : i ≠ j) (hkj : k ≠ j) : b i j = b k j ∧ c i j = c k j := by
  classical
  by_cases hik : i = k
  · simp [hik]
  let u := pairVector i k
  have hu : ∀ t, u t * u t = pairVector i k t := pairVector_sq i k
  have hj : u j = 0 := by simp [u, pairVector, ne_comm, hij, hkj]
  let v := u + Pi.single j 1
  have huv : ∀ t, v t * u t = pairVector i k t := by
    intro t
    by_cases ht : t = j
    · subst t
      change v j * u j = u j
      simp [hj]
    · simpa [v, Pi.single_apply, ht] using hu t
  have hvu : ∀ t, u t * v t = pairVector i k t := fun t => (mul_comm _ _).trans (huv t)
  have hz := hvanish u u (quadratic_pair hik u u hu)
  have hx := hvanish v u (quadratic_pair hik v u huv)
  have hy := hvanish u v (quadratic_pair hik u v hvu)
  rw [evaluate_pair a b c hik u u hu] at hz
  rw [evaluate_pair a b c hik v u huv] at hx
  rw [evaluate_pair a b c hik u v hvu] at hy
  dsimp only [v] at hx hy
  simp only [form_add_single] at hx hy
  constructor
  · apply CharTwo.add_eq_zero.mp
    linear_combination hx - hz
  · apply CharTwo.add_eq_zero.mp
    linear_combination hy - hz

variable [Nontrivial ι]

omit [DecidableEq ι] in
/-- The vanishing cubic factor has only one affine factor after the
quadratic form is removed. -/
theorem factor_of_vanish (a : ι → Bit) (b c : ι → ι → Bit)
    (hb : ∀ i, b i i = 0) (hc : ∀ i, c i i = 0)
    (hvanish : ∀ x y, quadratic x y = 0 → evaluate a b c x y = 0) :
    ∃ a₀ : Bit, ∃ B C : ι → Bit, ∀ x y,
      evaluate a b c x y = quadratic x y * (a₀ + form B x + form C y) := by
  classical
  let peer (j : ι) : ι := Classical.choose (exists_ne j)
  have hpeer (j : ι) : peer j ≠ j := Classical.choose_spec (exists_ne j)
  let B (j : ι) := b (peer j) j
  let C (j : ι) := c (peer j) j
  have hcoef {i j : ι} (hij : i ≠ j) : b i j = B j ∧ c i j = C j :=
    stable_coefficients a b c hvanish hij (hpeer j)
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  let a₀ : Bit := a i₀ + B i₀ + C i₀
  have ha (i : ι) : a i + B i + C i = a₀ := by
    by_cases hi : i = i₀
    · simp [hi, a₀]
    let u := pairVector i i₀
    have hu : ∀ t, u t * u t = pairVector i i₀ t := pairVector_sq i i₀
    have hz := hvanish u u (quadratic_pair hi u u hu)
    rw [evaluate_pair a b c hi u u hu] at hz
    dsimp only [u] at hz
    simp only [form_pairVector _ _ _ hi, hb, hc, zero_add, add_zero,
      (hcoef hi).1, (hcoef hi).2, (hcoef (Ne.symm hi)).1, (hcoef (Ne.symm hi)).2] at hz
    apply CharTwo.add_eq_zero.mp
    dsimp only [a₀]
    linear_combination hz
  refine ⟨a₀, B, C, fun x y => ?_⟩
  have hform (i : ι) :
      form (b i) x + B i * x i = form B x ∧
      form (c i) y + C i * y i = form C y := by
    constructor
    · rw [form, form, ← Finset.sum_erase_add _ _ (Finset.mem_univ i),
        ← Finset.sum_erase_add _ _ (Finset.mem_univ i), hb, zero_mul, add_zero]
      congr 1
      exact Finset.sum_congr rfl fun j hj => by rw [(hcoef (Ne.symm (Finset.ne_of_mem_erase hj))).1]
    · rw [form, form, ← Finset.sum_erase_add _ _ (Finset.mem_univ i),
        ← Finset.sum_erase_add _ _ (Finset.mem_univ i), hc, zero_mul, add_zero]
      congr 1
      exact Finset.sum_congr rfl fun j hj => by rw [(hcoef (Ne.symm (Finset.ne_of_mem_erase hj))).2]
  rw [quadratic, Finset.sum_mul, evaluate]
  apply Finset.sum_congr rfl
  intro i _
  have bit (v : Bit) : v = 0 ∨ v = 1 := by
    revert v
    decide +kernel
  rcases bit (x i) with hx | hx <;> rcases bit (y i) with hy | hy
  all_goals simp only [hx, hy, zero_mul, mul_zero, one_mul]
  have hB := (hform i).1
  have hC := (hform i).2
  rw [hx, mul_one] at hB
  rw [hy, mul_one] at hC
  calc
    _ = (a i + B i + C i) + (form (b i) x + B i) + (form (c i) y + C i) := by
      symm
      calc
        _ = (a i + form (b i) x + form (c i) y) + (B i + B i) + (C i + C i) := by abel
        _ = _ := by simp only [CharTwo.add_self_eq_zero, add_zero]
    _ = _ := by rw [ha, hB, hC]

end D5.S3.HomologicalAlgebra.SplitQuadraticCubic
