/- GID: D5/S3/Estimation/DataProcessing/OrderedCoordinateHistoryInterpreter
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/OrderedCoordinateHistoryInterpreter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Estimation/DataProcessing/FiniteHistoryConditionalExpectation, mathlib/module/Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic]
   utility: none
   digest: Adaptive read-once coordinate histories retain named dependent results and admit staged table interpretation. -/

import D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open MeasureTheory Finset Function
open scoped BigOperators ENNReal Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Estimation.DataProcessing.OrderedCoordinateHistoryInterpreter

variable {I : Type*} {X : I → Type*} [Fintype I] [DecidableEq I]
  [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]

/-- An ordered history retains the actual coordinate and its dependent letter. -/
abbrev History (X : I → Type*) (k : ℕ) :=
  {w : Fin k → Sigma X // Function.Injective (fun j => (w j).1)}

/-- Coordinates not yet read in this history. -/
abbrev Unread {k : ℕ} (h : History X k) := {i : I // ∀ j, (h.val j).1 ≠ i}

/-- The unique empty ordered history. -/
def root : History X 0 := ⟨Fin.elim0, fun a => Fin.elim0 a⟩

instance : Subsingleton (History X 0) :=
  ⟨fun a b => Subtype.ext (funext fun i => Fin.elim0 i)⟩

/-- Append one previously unread coordinate and its letter. -/
def append {k : ℕ} (h : History X k) (i : Unread h) (x : X i.val) : History X (k+1) :=
  ⟨Fin.snoc (α := fun _ : Fin (k+1) => Sigma X) h.val ⟨i.val, x⟩, by
    have he : (fun j => (Fin.snoc (α := fun _ : Fin (k+1) => Sigma X) h.val ⟨i.val, x⟩ j).1) =
        Fin.snoc (fun j => (h.val j).1) i.val := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
    rw [he]
    exact Fin.snoc_injective_of_injective h.property (by rintro ⟨j, hj⟩; exact i.property j hj)⟩

/-- Removing the final coordinate preserves legal read-once histories. -/
def parent {k : ℕ} (h : History X (k+1)) : History X k :=
  ⟨Fin.init h.val, h.property.comp (Fin.castSucc_injective k)⟩

/-- The final coordinate is unread at the parent history. -/
def lastCoord {k : ℕ} (h : History X (k+1)) : Unread (parent h) :=
  ⟨(h.val (Fin.last k)).1, fun j hj =>
    (Fin.castSucc_ne_last j) (h.property hj)⟩

/-- The dependent letter obtained on the final step. -/
def lastLetter {k : ℕ} (h : History X (k+1)) : X (lastCoord h).val :=
  (h.val (Fin.last k)).2

@[simp] theorem parent_append {k : ℕ} (h : History X k) (i : Unread h) (x : X i.val) :
    parent (append h i x) = h := by
  apply Subtype.ext
  change Fin.init (Fin.snoc (α := fun _ : Fin (k+1) => Sigma X) h.val ⟨i.val, x⟩) = h.val
  exact @Fin.init_snoc k (fun _ => Sigma X) ⟨i.val, x⟩ h.val

@[simp] theorem append_parent {k : ℕ} (h : History X (k+1)) :
    append (parent h) (lastCoord h) (lastLetter h) = h :=
  Subtype.ext (Fin.snoc_init_self _)

theorem append_injective (k : ℕ) :
    Function.Injective (fun e : Σ h : History X k, Σ i : Unread h, X i.val =>
      append e.1 e.2.1 e.2.2) := by
  rintro ⟨h, i, x⟩ ⟨g, j, y⟩ he
  have hh : h = g := by simpa using congrArg parent he
  subst g
  have hz : (⟨i.val, x⟩ : Sigma X) = ⟨j.val, y⟩ := by
    simpa only [append, Fin.snoc_last] using
      congrArg (fun w : History X (k+1) => w.val (Fin.last k)) he
  have hi : i = j := Subtype.ext (Sigma.mk.inj hz).1
  subst j
  have hx : x = y := eq_of_heq (Sigma.mk.inj hz).2
  subst y
  rfl

/-- A next-layer history has a unique parent, unread coordinate and dependent result. -/
def extensionEquiv (k : ℕ) :
    (Σ h : History X k, Σ i : Unread h, X i.val) ≃ History X (k+1) where
  toFun e := append e.1 e.2.1 e.2.2
  invFun h := ⟨parent h, lastCoord h, lastLetter h⟩
  left_inv e := append_injective k (append_parent _)
  right_inv := append_parent

private theorem unread_nonempty {k : ℕ} (h : History X k) (hk : k < Fintype.card I) :
    Nonempty (Unread h) := by
  classical
  by_contra hn
  have hs : Function.Surjective (fun j => (h.val j).1) := by
    intro i
    by_contra hi
    exact hn ⟨⟨i, fun j hj => hi ⟨j, hj⟩⟩⟩
  have hc := Fintype.card_le_of_surjective _ hs
  simp only [Fintype.card_fin] at hc
  omega

/-- The named assignment of a complete history erases order without renaming coordinates. -/
def terminalAssignment (h : History X (Fintype.card I)) : (i : I) → X i :=
  let e : Fin (Fintype.card I) ≃ I :=
    Equiv.ofBijective (fun j => (h.val j).1)
      ((Fintype.bijective_iff_injective_and_card _).mpr ⟨h.property, by simp⟩)
  fun i => (e.apply_symm_apply i) ▸ (h.val (e.symm i)).2

/-- All five ordered-history flow constraints, with real capacities and masses. -/
@[ext] structure Flow (r : I → ℝ) where
  mass : (k : ℕ) → History X k → ℝ
  select : (k : ℕ) → (h : History X k) → Unread h → ℝ
  result : (k : ℕ) → (h : History X k) → (i : Unread h) → X i.val → ℝ
  mass_nonneg : ∀ k h, 0 ≤ mass k h
  select_nonneg : ∀ k h i, 0 ≤ select k h i
  result_nonneg : ∀ k h i x, 0 ≤ result k h i x
  root_mass : mass 0 root = 1
  select_sum : ∀ k, k < Fintype.card I → ∀ h, ∑ i, select k h i = mass k h
  result_sum : ∀ k h i, ∑ x, result k h i x = select k h i
  result_cap : ∀ k h i x, result k h i x ≤ r i.val * select k h i
  child_mass : ∀ k h i x, mass (k+1) (append h i x) = result k h i x

/-- Sum over every full ordering with the specified named assignment. -/
def terminalProjection {r : I → ℝ} (p : Flow (X := X) r) (v : (i : I) → X i) : ℝ :=
  ∑ h : History X (Fintype.card I), if terminalAssignment h = v then p.mass _ h else 0

private theorem select_zero {r : I → ℝ} (p : Flow (X := X) r)
    {k : ℕ} (hk : k < Fintype.card I) (h : History X k) (hm : p.mass k h = 0)
    (i : Unread h) : p.select k h i = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => p.select_nonneg k h i)).mp
    ((p.select_sum k hk h).trans hm) i (Finset.mem_univ i)

private theorem result_zero {r : I → ℝ} (p : Flow (X := X) r)
    {k : ℕ} (h : History X k) (i : Unread h) (hf : p.select k h i = 0)
    (x : X i.val) : p.result k h i x = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => p.result_nonneg k h i x)).mp
    ((p.result_sum k h i).trans hf) x (Finset.mem_univ x)

/-- A supported scheduler row; a null node uses the uniform unread-coordinate row. -/
def schedulerRow {r : I → ℝ} (p : Flow (X := X) r)
    {k : ℕ} (h : History X k) (i : Unread h) : ℝ :=
  if p.mass k h = 0 then 1 / Fintype.card (Unread h) else p.select k h i / p.mass k h

/-- A result row; a null selection uses the uniform row of its actual alphabet. -/
def resultRow {r : I → ℝ} (p : Flow (X := X) r)
    {k : ℕ} (h : History X k) (i : Unread h) (x : X i.val) : ℝ :=
  if p.select k h i = 0 then 1 / Fintype.card (X i.val)
    else p.result k h i x / p.select k h i

private theorem scheduler_law {r : I → ℝ} (p : Flow (X := X) r)
    {k : ℕ} (hk : k < Fintype.card I) (h : History X k) :
    (∀ i, 0 ≤ schedulerRow p h i) ∧ ∑ i, schedulerRow p h i = 1 := by
  classical
  letI := unread_nonempty h hk
  by_cases hm : p.mass k h = 0
  · simp only [schedulerRow, hm, if_true]
    constructor
    · intro i; positivity
    · simp [Fintype.card_ne_zero]
  · simp only [schedulerRow, hm, if_false]
    exact ⟨fun i => div_nonneg (p.select_nonneg k h i) (p.mass_nonneg k h), by
      rw [← Finset.sum_div, p.select_sum k hk h, div_self hm]⟩

theorem result_law {r : I → ℝ} (p : Flow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    {k : ℕ} (h : History X k) (i : Unread h) :
    (∀ x, 0 ≤ resultRow p h i x ∧ resultRow p h i x ≤ r i.val) ∧
      ∑ x, resultRow p h i x = 1 := by
  classical
  by_cases hf : p.select k h i = 0
  · simp only [resultRow, hf, if_true]
    exact ⟨fun x => ⟨by positivity, hr i.val⟩, by simp [Fintype.card_ne_zero]⟩
  · simp only [resultRow, hf, if_false]
    have hp : 0 < p.select k h i := lt_of_le_of_ne (p.select_nonneg k h i) (Ne.symm hf)
    exact ⟨fun x => ⟨div_nonneg (p.result_nonneg k h i x) hp.le,
      (div_le_iff₀ hp).mpr (p.result_cap k h i x)⟩, by
      rw [← Finset.sum_div, p.result_sum k h i, div_self hf]⟩

private theorem branch_factor {r : I → ℝ} (p : Flow (X := X) r)
    {k : ℕ} (hk : k < Fintype.card I) (h : History X k) (i : Unread h) (x : X i.val) :
    p.mass k h * schedulerRow p h i * resultRow p h i x = p.mass (k+1) (append h i x) := by
  rw [p.child_mass]
  by_cases hm : p.mass k h = 0
  · rw [hm, zero_mul, zero_mul, result_zero p h i (select_zero p hk h hm i) x]
  · by_cases hf : p.select k h i = 0
    · simp [schedulerRow, hm, hf, result_zero p h i hf x]
    · simp only [schedulerRow, hm, if_false, resultRow, hf]
      field_simp

/-- The complete scheduling innovation at a given nonterminal layer. -/
abbrev ScheduleTable (k : ℕ) := (h : History X k) → Unread h
/-- The separate complete result innovation at that layer. -/
abbrev ResultTable (k : ℕ) := (h : History X k) → (i : Unread h) → X i.val

instance innovationFintype (k : ℕ) :
    Fintype (ScheduleTable (X := X) k × ResultTable (X := X) k) :=
  inferInstance

/-- Run the actual adaptive interpreter using distinct scheduling and result tables. -/
def simulate : (k : ℕ) →
    ((t : Fin k) → ScheduleTable (X := X) t.val) →
    ((t : Fin k) → ResultTable (X := X) t.val) → History X k
  | 0, _, _ => root
  | k+1, a, b =>
      let h := simulate k (Fin.init a) (Fin.init b)
      let i := a (Fin.last k) h
      append h i (b (Fin.last k) h i)

/-- Structural history fibers of the adaptive interpreter. Each step consults only the
current tables at the actual preceding history; no flow mass enters this recursion. -/
theorem simulate_fiber (k : ℕ)
    (a : (t : Fin (k+1)) → ScheduleTable (X := X) t.val)
    (b : (t : Fin (k+1)) → ResultTable (X := X) t.val)
    (h : History X k) (i : Unread h) (x : X i.val) :
    simulate (k+1) a b = append h i x ↔
      simulate k (Fin.init a) (Fin.init b) = h ∧
        a (Fin.last k) h = i ∧ b (Fin.last k) h i = x := by
  classical
  let g := simulate k (Fin.init a) (Fin.init b)
  have he : simulate (k+1) a b =
      extensionEquiv k ⟨g, a (Fin.last k) g, b (Fin.last k) g (a (Fin.last k) g)⟩ := rfl
  rw [he]
  change extensionEquiv k _ = extensionEquiv k ⟨h, i, x⟩ ↔ _
  rw [Equiv.apply_eq_iff_eq]
  constructor
  · intro hh
    have hg : g = h := congrArg Sigma.fst hh
    subst h
    have hi : a (Fin.last k) g = i := by simpa using ((Sigma.mk.inj hh).2.eq |> Sigma.mk.inj).1
    subst i
    have hx : b (Fin.last k) g (a (Fin.last k) g) = x := by
      simpa using (Sigma.mk.inj ((Sigma.mk.inj hh).2.eq)).2
    exact ⟨rfl, rfl, hx⟩
  · rintro ⟨hg, hi, hx⟩
    change g = h at hg
    subst h
    subst i
    subst x
    rfl

/-- Interpret a chronological sequence of separately stored scheduling/result blocks. -/
def interpret (k : ℕ) (w : (t : Fin k) →
    ScheduleTable (X := X) t.val × ResultTable (X := X) t.val) : History X k :=
  simulate k (fun t => (w t).1) (fun t => (w t).2)

theorem interpret_snoc_fiber (k : ℕ)
    (w : (t : Fin k) → ScheduleTable (X := X) t.val × ResultTable (X := X) t.val)
    (z : ScheduleTable (X := X) k × ResultTable (X := X) k)
    (h : History X k) (i : Unread h) (x : X i.val) :
    interpret (k+1) (Fin.snoc w z) = append h i x ↔
      interpret k w = h ∧ z.1 h = i ∧ z.2 h i = x := by
  let v : (t : Fin (k+1)) →
      ScheduleTable (X := X) t.val × ResultTable (X := X) t.val := Fin.snoc w z
  have ha : Fin.init (fun t => (v t).1) = fun t => (w t).1 := by
    funext t
    change (Fin.snoc (α := fun t : Fin (k+1) => ScheduleTable (X := X) t.val × ResultTable (X := X) t.val) w z t.castSucc).1 = (w t).1
    rw [Fin.snoc_castSucc]
  have hb : Fin.init (fun t => (v t).2) = fun t => (w t).2 := by
    funext t
    change (Fin.snoc (α := fun t : Fin (k+1) => ScheduleTable (X := X) t.val × ResultTable (X := X) t.val) w z t.castSucc).2 = (w t).2
    rw [Fin.snoc_castSucc]
  have he := simulate_fiber k (fun t => (v t).1) (fun t => (v t).2) h i x
  rw [ha, hb] at he
  simpa only [v, interpret, Fin.snoc_last] using he

private theorem product_row_marginal {C : Type*} {Y : C → Type*}
    [Fintype C] [DecidableEq C] [∀ c, Fintype (Y c)]
    (row : (c : C) → Y c → ℝ) (hn : ∀ c, ∑ y, row c y = 1)
    (c : C) (f : Y c → ℝ) :
    (∑ a : (c : C) → Y c, (∏ j, row j (a j)) * f (a c)) =
      ∑ y, row c y * f y := by
  classical
  let q := Function.update row c (fun y => row c y * f y)
  have prodq (a : (c : C) → Y c) :
      (∏ j, q j (a j)) = (∏ j, row j (a j)) * f (a c) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c),
      ← Finset.mul_prod_erase _ (fun j => row j (a j)) (Finset.mem_univ c)]
    have he : (∏ j ∈ Finset.univ.erase c, q j (a j)) =
        ∏ j ∈ Finset.univ.erase c, row j (a j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [Finset.mem_erase] at hj
      simp [q, Function.update_of_ne hj.1]
    simp only [q, Function.update_self, he]
    ring
  simp_rw [← prodq]
  rw [← Fintype.prod_sum, ← Finset.mul_prod_erase _ _ (Finset.mem_univ c)]
  have he : (∏ j ∈ Finset.univ.erase c, ∑ y, q j y) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    simp only [Finset.mem_erase] at hj
    simpa [q, Function.update_of_ne hj.1] using hn j
  simp [q, he]

/-- Independent scheduling-table cells have the totalized scheduler rows. -/
def scheduleDensity {r : I → ℝ} (p : Flow (X := X) r) (k : ℕ)
    (a : ScheduleTable (X := X) k) : ℝ := ∏ h, schedulerRow p h (a h)

/-- Independent result-table cells have the totalized dependent result rows. -/
def resultDensity {r : I → ℝ} (p : Flow (X := X) r) (k : ℕ)
    (b : ResultTable (X := X) k) : ℝ := ∏ h, ∏ i, resultRow p h i (b h i)

theorem table_laws {r : I → ℝ} (p : Flow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    {k : ℕ} (hk : k < Fintype.card I) :
    ((∀ a, 0 ≤ scheduleDensity p k a) ∧ ∑ a, scheduleDensity p k a = 1) ∧
    ((∀ b, 0 ≤ resultDensity p k b) ∧ ∑ b, resultDensity p k b = 1) := by
  constructor
  · constructor
    · intro a
      exact Finset.prod_nonneg (fun h _ => (scheduler_law p hk h).1 _)
    · unfold scheduleDensity
      rw [← Fintype.prod_sum]
      simp_rw [(scheduler_law p hk _).2]
      simp
  · constructor
    · intro b
      exact Finset.prod_nonneg (fun h _ =>
        Finset.prod_nonneg (fun i _ => ((result_law p hr h i).1 _).1))
    · unfold resultDensity
      rw [← Fintype.prod_sum (fun (h : History X k)
        (a : (i : Unread h) → X i.val) => ∏ i, resultRow p h i (a i))]
      simp_rw [← Fintype.prod_sum, (result_law p hr _ _).2]
      simp

theorem result_table_marginal {r : I → ℝ} (p : Flow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    {k : ℕ} (h : History X k) (i : Unread h) (f : X i.val → ℝ) :
    (∑ b : ResultTable (X := X) k, resultDensity p k b * f (b h i)) =
      ∑ x, resultRow p h i x * f x := by
  have hn (h : History X k) :
      (∑ a : (i : Unread h) → X i.val, ∏ i, resultRow p h i (a i)) = 1 := by
    rw [← Fintype.prod_sum]
    simp_rw [(result_law p hr _ _).2]
    simp
  rw [show (∑ b, resultDensity p k b * f (b h i)) =
    ∑ a : (i : Unread h) → X i.val, (∏ i, resultRow p h i (a i)) * f (a i) from
      product_row_marginal (Y := fun h : History X k => (i : Unread h) → X i.val)
        (fun h a => ∏ i, resultRow p h i (a i)) hn h
        (fun a => f (a i))]
  exact product_row_marginal (fun i x => resultRow p h i x)
    (fun i => (result_law p hr h i).2) i f

private theorem table_branch {r : I → ℝ} (p : Flow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    {k : ℕ} (hk : k < Fintype.card I)
    (h : History X k) (i : Unread h) (x : X i.val) :
    (∑ z : ScheduleTable (X := X) k × ResultTable (X := X) k,
      (scheduleDensity p k z.1 * resultDensity p k z.2) *
        (if z.1 h = i ∧ z.2 h i = x then 1 else 0)) =
      schedulerRow p h i * resultRow p h i x := by
  classical
  rw [Fintype.sum_prod_type]
  have hb : (∑ b : ResultTable (X := X) k,
      resultDensity p k b * (if b h i = x then 1 else 0)) = resultRow p h i x := by
    simpa using result_table_marginal p hr h i (fun y => if y = x then 1 else 0)
  simp_rw [mul_assoc]
  have he (a : ScheduleTable (X := X) k) :
      (∑ b : ResultTable (X := X) k,
        resultDensity p k b * (if a h = i ∧ b h i = x then 1 else 0)) =
        if a h = i then resultRow p h i x else 0 := by
    by_cases ha : a h = i
    · simpa only [ha, true_and, if_true] using hb
    · simp [ha]
  simp_rw [← Finset.mul_sum, he]
  have ha : (∑ a : ScheduleTable (X := X) k,
      scheduleDensity p k a * (if a h = i then 1 else 0)) = schedulerRow p h i := by
    rw [show (∑ a, scheduleDensity p k a * (if a h = i then 1 else 0)) =
      ∑ j, schedulerRow p h j * (if j = i then 1 else 0) from
        product_row_marginal (fun h i => schedulerRow p h i)
          (fun h => (scheduler_law p hk h).2) h (fun j => if j = i then 1 else 0)]
    simp
  calc
    _ = (∑ a : ScheduleTable (X := X) k,
      scheduleDensity p k a * (if a h = i then 1 else 0)) * resultRow p h i x := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        by_cases he : a h = i <;> simp [he]
    _ = _ := by rw [ha]

/-- Constant innovation-block kernels; the simulator does not enter their definition. -/
def innovationKernel {r : I → ℝ} (p : Flow (X := X) r)
    (k : ℕ) (_ : Unit)
    (_ : FiniteHistoryConditionalExpectation.History
      (fun t => ScheduleTable (X := X) t × ResultTable (X := X) t) k)
    (z : ScheduleTable (X := X) k × ResultTable (X := X) k) : ℝ :=
  scheduleDensity p k z.1 * resultDensity p k z.2

/-- The independent table trace realizes every prescribed ordered node mass. The proof
uses the structural fibers of the adaptive interpreter, including null branches. -/
theorem interpret_mass {r : I → ℝ} (p : Flow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    (k : ℕ) (hk : k ≤ Fintype.card I) (h : History X k) :
    (∑ w : (t : Fin k) → ScheduleTable (X := X) t.val × ResultTable (X := X) t.val,
      FiniteHistoryConditionalExpectation.likelihood (innovationKernel p) k () w *
        (if interpret k w = h then 1 else 0)) = p.mass k h := by
  classical
  induction k with
  | zero =>
      have hh : h = root := Subsingleton.elim _ _
      subst h
      simp [interpret, simulate, FiniteHistoryConditionalExpectation.likelihood, p.root_mass]
  | succ k ih =>
      let e := (extensionEquiv k).symm h
      have hh : h = append e.1 e.2.1 e.2.2 := (extensionEquiv k).apply_symm_apply h |>.symm
      rw [hh]
      rw [← (Fin.snocEquiv (fun t : Fin (k+1) =>
        ScheduleTable (X := X) t.val × ResultTable (X := X) t.val)).sum_comp,
        Fintype.sum_prod_type]
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk,
        FiniteHistoryConditionalExpectation.likelihood, Fin.init_snoc, Fin.snoc_last,
        innovationKernel, interpret_snoc_fiber]
      rw [Finset.sum_comm]
      have step (w : (t : Fin k) →
          ScheduleTable (X := X) t.val × ResultTable (X := X) t.val) :
          (∑ z : ScheduleTable (X := X) k × ResultTable (X := X) k,
            (FiniteHistoryConditionalExpectation.likelihood (innovationKernel p) k () w *
              (scheduleDensity p k z.1 * resultDensity p k z.2)) *
                (if interpret k w = e.1 ∧ z.1 e.1 = e.2.1 ∧ z.2 e.1 e.2.1 = e.2.2
                  then 1 else 0)) =
            FiniteHistoryConditionalExpectation.likelihood (innovationKernel p) k () w *
              (if interpret k w = e.1 then 1 else 0) *
                (schedulerRow p e.1 e.2.1 * resultRow p e.1 e.2.1 e.2.2) := by
        by_cases hw : interpret k w = e.1
        · simp only [hw, true_and, if_true, mul_one]
          rw [show (∑ z : ScheduleTable (X := X) k × ResultTable (X := X) k,
            (FiniteHistoryConditionalExpectation.likelihood (innovationKernel p) k () w *
              (scheduleDensity p k z.1 * resultDensity p k z.2)) *
                (if z.1 e.1 = e.2.1 ∧ z.2 e.1 e.2.1 = e.2.2 then 1 else 0)) =
            FiniteHistoryConditionalExpectation.likelihood (innovationKernel p) k () w *
              (∑ z : ScheduleTable (X := X) k × ResultTable (X := X) k,
                (scheduleDensity p k z.1 * resultDensity p k z.2) *
                  (if z.1 e.1 = e.2.1 ∧ z.2 e.1 e.2.1 = e.2.2 then 1 else 0)) by
            simp only [mul_assoc, Finset.mul_sum]]
          rw [table_branch p hr (by omega) e.1 e.2.1 e.2.2]
        · simp [hw]
      calc
        _ = ∑ w : (t : Fin k) →
            ScheduleTable (X := X) t.val × ResultTable (X := X) t.val,
          (FiniteHistoryConditionalExpectation.likelihood (innovationKernel p) k () w *
            (if interpret k w = e.1 then 1 else 0)) *
              (schedulerRow p e.1 e.2.1 * resultRow p e.1 e.2.1 e.2.2) := by
          apply Fintype.sum_congr
          intro w
          exact step w
        _ = _ := by
          rw [← Finset.sum_mul, ih (by omega), ← mul_assoc,
            branch_factor p (by omega)]

#print axioms interpret_mass
end D5.S3.Estimation.DataProcessing.OrderedCoordinateHistoryInterpreter
