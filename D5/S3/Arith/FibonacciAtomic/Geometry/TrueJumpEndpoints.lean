/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual finite true-jump endpoint families classify truncated ancestral colours. -/

import D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition
import D5.S0.Diagonal.Probability.EquivariantEscape
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Basic

/-! Finite neighbor-sampling experiments on the whole ordered address tree. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints

open MeasureTheory
open scoped BigOperators ENNReal
open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)

/-- Literal finite addresses, with false = L and true = R. -/
abbrev Address := ActualTreeReadoutAcquisition.Address

/-- The three possible incoming seam increments. -/
inductive Increment where
  | zero | plus | minus

def Increment.value : Increment → ℤ
  | .zero => 0
  | .plus => 1
  | .minus => -1

/-- The ordered table in (120.12). -/
def childIncrement : Increment → Bool → Increment
  | .zero, false => .plus
  | .zero, true => .minus
  | .plus, false => .zero
  | .plus, true => .plus
  | .minus, false => .minus
  | .minus, true => .zero

def update (m : ℕ) (s : ZMod m × Increment) (b : Bool) : ZMod m × Increment :=
  let d := childIncrement s.2 b
  (s.1 + (d.value : ZMod m), d)

/-- Colour and incoming increment, computed along the literal address. -/
def code (m : ℕ) (p : Address) : ZMod m × Increment :=
  p.foldl (update m) (0, .zero)

def q (m : ℕ) (p : Address) : ZMod m := (code m p).1
def delta (m : ℕ) (p : Address) : Increment := (code m p).2
def child (p : Address) (b : Bool) : Address := p ++ [b]
def parent (p : Address) : Address := p.take (p.length - 1)

/-- Truncation at the root totalizes iteration; the signature uses no extra ancestors. -/
def ancestor (p : Address) (k : ℕ) : Address := p.take (p.length - k)

def observation (m : ℕ) (p : Address) : ZMod m × ℕ := (q m p, p.length)

/-- Exactly the depth and colours numbered zero through min(h,depth). -/
def signature (m h : ℕ) (p : Address) : ℕ × List (ZMod m) :=
  (p.length, (List.range (min h p.length + 1)).map (fun k => q m (ancestor p k)))

private theorem code_child (m : ℕ) (p : Address) (b : Bool) :
    code m (child p b) = update m (code m p) b := by
  simp [code, child, List.foldl_append]

private theorem q_child (m : ℕ) (p : Address) (b : Bool) :
    q m (child p b) = q m p + ((childIncrement (delta m p) b).value : ZMod m) := by
  simp [q, delta, code_child, update]

theorem delta_child (m : ℕ) (p : Address) (b : Bool) :
    delta m (child p b) = childIncrement (delta m p) b := by
  simp [delta, code_child, update]

theorem ancestor_zero (p : Address) : ancestor p 0 = p := by
  simp [ancestor]

theorem ancestor_past (p : Address) (k : ℕ) (hk : p.length ≤ k) :
    ancestor p k = [] := by
  simp [ancestor, Nat.sub_eq_zero_of_le hk]

private theorem ancestor_child_succ (p : Address) (b : Bool) (k : ℕ) :
    ancestor (child p b) (k + 1) = ancestor p k := by
  simp [ancestor, child, List.take_append, Nat.add_sub_add_right,
    Nat.sub_eq_zero_of_le (Nat.sub_le _ _)]

theorem parent_child (p : Address) (b : Bool) : parent (child p b) = p := by
  simpa [parent, ancestor] using ancestor_child_succ p b 0

private theorem length_parent (p : Address) : (parent p).length = p.length - 1 := by
  simp [parent]

theorem ancestor_parent (p : Address) (k : ℕ) :
    ancestor (parent p) k = ancestor p (k + 1) := by
  unfold ancestor
  rw [length_parent]
  simp only [parent, List.take_take]
  congr 1
  omega

def Same (m h : ℕ) (p p' : Address) : Prop :=
  p.length = p'.length ∧ ∀ k, k ≤ h → q m (ancestor p k) = q m (ancestor p' k)

theorem signature_eq_iff (m h : ℕ) (p p' : Address) :
    signature m h p = signature m h p' ↔ Same m h p p' := by
  constructor
  · intro he
    have hd := congrArg Prod.fst he
    have hc := congrArg Prod.snd he
    change p.length = p'.length at hd
    refine ⟨hd, fun k hk => ?_⟩
    by_cases hn : k ≤ p.length
    · have hi : k < min h p.length + 1 := by omega
      have hi' : k < min h p'.length + 1 := by omega
      have hx := congrArg (fun l : List (ZMod m) => l[k]?) hc
      simpa [signature, List.getElem?_eq_getElem, hi, hi', List.getElem_map,
        List.getElem_range] using hx
    · rw [ancestor_past p k (by omega), ancestor_past p' k (by omega)]
  · rintro ⟨hd, hc⟩
    apply Prod.ext hd
    change (List.range (min h p.length + 1)).map _ =
      (List.range (min h p'.length + 1)).map _
    rw [hd]
    apply List.map_congr_left
    intro k hk
    exact hc k (by have := List.mem_range.mp hk; omega)

theorem incoming (m : ℕ) (p : Address) (hp : p ≠ []) :
    q m p = q m (parent p) + ((delta m p).value : ZMod m) := by
  induction p using List.reverseRecOn with
  | nil => contradiction
  | append_singleton p b _ =>
    change q m (child p b) = q m (parent (child p b)) +
      ((delta m (child p b)).value : ZMod m)
    rw [parent_child, delta_child, q_child]

private theorem same_delta (m h : ℕ) (hm : 3 ≤ m) (p p' : Address)
    (hs : Same m (h + 1) p p') (hp : p ≠ []) (hp' : p' ≠ []) :
    delta m p = delta m p' := by
  have : NeZero m := ⟨by omega⟩
  have : Fact (1 < m) := ⟨by omega⟩
  have hq := hs.2 0 (by omega)
  have ha := hs.2 1 (by omega)
  simp only [ancestor_zero] at hq
  change q m (parent p) = q m (parent p') at ha
  have hv : ((delta m p).value : ZMod m) = ((delta m p').value : ZMod m) := by
    have hi := incoming m p hp
    have hi' := incoming m p' hp'
    rw [hq, ha] at hi
    exact add_left_cancel (hi.symm.trans hi')
  have hx : (delta m p).value = (delta m p').value :=
    Int.cast_injOn_of_ringChar_ne_two (by rw [ZMod.ringChar_zmod_n]; omega)
      (by cases delta m p <;> simp [Increment.value])
      (by cases delta m p' <;> simp [Increment.value]) hv
  cases hd : delta m p <;> cases hd' : delta m p' <;>
    simp_all [Increment.value]

/-- Each of six equiprobable outcomes chooses an actual neighbor.
At the root each child occurs three times; elsewhere each neighbor occurs twice. -/
def move (p : Address) (a : Fin 6) : Address :=
  if p = [] then child p (decide (3 ≤ a.val))
  else if a.val < 2 then parent p else child p (decide (4 ≤ a.val))

private theorem same_move (m h : ℕ) (hm : 3 ≤ m) (p p' : Address)
    (hs : Same m (h + 1) p p') (a : Fin 6) :
    Same m h (move p a) (move p' a) := by
  by_cases hp : p = []
  · subst p
    have hp' : p' = [] := List.eq_nil_of_length_eq_zero (by simpa using hs.1.symm)
    subst p'
    exact ⟨rfl, fun _ _ => rfl⟩
  have hp' : p' ≠ [] := by
    intro he
    have : p.length = 0 := by simpa [he] using hs.1
    exact hp (List.eq_nil_of_length_eq_zero this)
  simp only [move, ite_eq_right_iff.mpr (fun h => (hp h).elim),
    ite_eq_right_iff.mpr (fun h => (hp' h).elim)]
  split_ifs with ha
  · refine ⟨by rw [length_parent, length_parent, hs.1], fun k hk => ?_⟩
    rw [ancestor_parent, ancestor_parent]
    exact hs.2 (k + 1) (by omega)
  · refine ⟨by simp [child, hs.1], fun k hk => ?_⟩
    cases k with
    | zero =>
      simp only [ancestor_zero, q_child]
      rw [same_delta m h hm p p' hs hp hp']
      exact congrArg (· + _) (by simpa only [ancestor_zero] using hs.2 0 (by omega))
    | succ k =>
      rw [ancestor_child_succ, ancestor_child_succ]
      exact hs.2 k (by omega)

/-- The actual degree-two/degree-three neighbor law, independently of colours or budgets. -/
noncomputable def J (p : Address) : PMF Address :=
  if p = [] then (uniformPmf Bool).map (child p)
  else (uniformPmf (Fin 3)).map
    (fun a => if a.val = 0 then parent p else child p (decide (a.val = 2)))

/-- The finite law obtained by successively sampling the actual neighbor kernel. -/
noncomputable def law : ℕ → Address → PMF Address
  | 0, p => PMF.pure p
  | j + 1, p => (J p).bind (law j)

/-- Finite independent random seeds, six equiprobable outcomes at each step. -/
def Seed : ℕ → Type
  | 0 => Unit
  | h + 1 => Fin 6 × Seed h

instance seedFintype (h : ℕ) : Fintype (Seed h) := by
  induction h with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ h ih => exact @instFintypeProd _ _ inferInstance ih

instance seedNonempty (h : ℕ) : Nonempty (Seed h) := by
  induction h with
  | zero => exact ⟨()⟩
  | succ h ih => exact @instNonemptyProd _ _ inferInstance ih

instance seedMeasurable (h : ℕ) : MeasurableSpace (Seed h) := ⊤
instance seedSingletons (h : ℕ) : MeasurableSingletonClass (Seed h) := ⟨fun _ => trivial⟩

local instance addressMeasurable : MeasurableSpace Address := ⊤

/-- The actual finite experiment: sample one neighbor and continue from that vertex. -/
def run : (h : ℕ) → Address → Seed h → Address
  | 0, p, _ => p
  | h + 1, p, s => run h (move p s.1) s.2

/-- Actual endpoint expectations, using the fixed J and the initial endpoint at j=0. -/
noncomputable def B (m : ℕ) (p : Address) (j : ℕ) (f : ZMod m × ℕ → ℝ) : ℝ :=
  ∫ x, f (observation m x) ∂(law j p).toMeasure

private theorem uniform_prod {α β : Type} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] :
    uniformPmf (α × β) = (uniformPmf α).bind
      (fun a => (uniformPmf β).map (fun b => (a, b))) := by
  classical
  ext ⟨a, b⟩ : 1
  simp only [PMF.bind_apply, PMF.map_apply, tsum_fintype, uniformPmf,
    PMF.ofFintype_apply, Prod.mk.injEq, Fintype.card_prod, Nat.cast_mul]
  have inner (a' : α) :
      (∑ b' : β, if a = a' ∧ b = b' then (↑(Fintype.card β) : ℝ≥0∞)⁻¹ else 0) =
        if a = a' then (↑(Fintype.card β) : ℝ≥0∞)⁻¹ else 0 := by
    by_cases ha : a = a' <;> simp [ha]
  simp_rw [inner, mul_ite, mul_zero]
  simp
  exact ENNReal.mul_inv (by simp) (by simp)

private theorem J_six (p : Address) :
    J p = (uniformPmf (Fin 6)).map (move p) := by
  classical
  ext z : 1
  by_cases hp : p = []
  · subst p
    simp [J, PMF.map_apply, tsum_fintype, uniformPmf, move,
      Fin.sum_univ_succ, child]
    by_cases hl : z = [false] <;> by_cases hr : z = [true] <;>
      simp only [hl, hr, ite_true, ite_false, zero_add, add_zero, zero_mul]
    all_goals
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_inv]
      norm_num
  · simp [J, hp, PMF.map_apply, tsum_fintype, uniformPmf, move,
      Fin.sum_univ_succ]
    split_ifs <;>
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    all_goals
      simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_inv]
      norm_num

private theorem law_experiment (h : ℕ) (p : Address) :
    law h p = (uniformPmf (Seed h)).map (run h p) := by
  induction h generalizing p with
  | zero =>
    change PMF.pure p = (uniformPmf Unit).map (Function.const Unit p)
    exact (PMF.map_const _ _).symm
  | succ h ih =>
    change (J p).bind (law h) =
      (uniformPmf (Fin 6 × Seed h)).map (fun s => run h (move p s.1) s.2)
    rw [uniform_prod, PMF.map_bind, J_six, PMF.bind_map]
    apply congrArg ((uniformPmf (Fin 6)).bind)
    funext a
    rw [PMF.map_comp]
    exact ih (move p a)

/-- Backward evaluator derived from the actual neighbor choices. -/
noncomputable def evaluate : ℕ → (Address → ℝ) → Address → ℝ
  | 0, g, p => g p
  | h + 1, g, p => (∑ a : Fin 6, evaluate h g (move p a)) / 6

private theorem uniform_integral {α : Type} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (g : α → ℝ) :
    ∫ a, g a ∂(uniformPmf α).toMeasure =
      (∑ a, g a) / Fintype.card α := by
  rw [PMF.integral_eq_sum]
  simp only [uniformPmf, PMF.ofFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  rw [← Finset.mul_sum]
  exact (div_eq_inv_mul _ _).symm

private theorem experiment_evaluate (h : ℕ) (g : Address → ℝ) (p : Address) :
    (∑ s : Seed h, g (run h p s)) / Fintype.card (Seed h) = evaluate h g p := by
  induction h generalizing p with
  | zero =>
    change (∑ _ : Unit, g p) / Fintype.card Unit = g p
    simp
  | succ h ih =>
    change (∑ s : Fin 6 × Seed h, g (run h (move p s.1) s.2)) /
      Fintype.card (Fin 6 × Seed h) = _
    rw [Fintype.sum_prod_type]
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat,
      evaluate]
    rw [mul_comm (6 : ℝ), div_mul_eq_div_div, Finset.sum_div]
    simp_rw [ih]

private theorem B_evaluate (m h : ℕ) (f : ZMod m × ℕ → ℝ) (p : Address) :
    B m p h f = evaluate h (fun x => f (observation m x)) p := by
  unfold B
  rw [law_experiment, ← PMF.toMeasure_map (run h p) (uniformPmf (Seed h)) measurable_from_top,
    integral_map_of_stronglyMeasurable measurable_from_top
      (measurable_from_top.stronglyMeasurable), uniform_integral]
  exact experiment_evaluate h (fun x => f (observation m x)) p

private theorem evaluate_nonroot (h : ℕ) (g : Address → ℝ) (p : Address) (hp : p ≠ []) :
    evaluate (h + 1) g p =
      (evaluate h g (parent p) + evaluate h g (child p false) +
        evaluate h g (child p true)) / 3 := by
  simp [evaluate, move, hp, Fin.sum_univ_succ]
  ring

/-- Global boundedness on the entire countable observation space. -/
def Bounded {m : ℕ} (f : ZMod m × ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ e, |f e| ≤ C

/-- A cell test; no restriction on possible subsequent addresses is imposed. -/
noncomputable def cell (m : ℕ) (c : ZMod m) (r : ℕ) (e : ZMod m × ℕ) : ℝ :=
  if e = (c, r) then 1 else 0

private theorem cell_bounded (m : ℕ) (c : ZMod m) (r : ℕ) : Bounded (cell m c r) := by
  refine ⟨1, fun e => ?_⟩
  unfold cell
  split_ifs <;> norm_num

private theorem evaluate_below (m h : ℕ) (c : ZMod m) (r : ℕ) (p : Address)
    (hr : r + h < p.length) :
    evaluate h (fun x => cell m c r (observation m x)) p = 0 := by
  induction h generalizing p with
  | zero =>
    have hn : p.length ≠ r := by omega
    simp [evaluate, cell, observation, Prod.mk.injEq, hn]
  | succ h ih =>
    have hp : p ≠ [] := by intro he; simp [he] at hr
    rw [evaluate_nonroot h _ p hp, ih (parent p) (by rw [length_parent]; omega),
      ih (child p false) (by simp only [child, List.length_append, List.length_singleton]; omega),
      ih (child p true) (by simp only [child, List.length_append, List.length_singleton]; omega)]
    norm_num

/-- At minimum reachable depth the only route is the all-parent route.
All k departures occur at nonroot vertices, including when the endpoint is the root. -/
private theorem minimum_depth_evaluate (m k : ℕ) (p : Address) (hk : k ≤ p.length)
    (c : ZMod m) :
    evaluate k (fun x => cell m c (p.length - k) (observation m x)) p =
      if q m (ancestor p k) = c then (1 / 3 : ℝ) ^ k else 0 := by
  induction k generalizing p with
  | zero => simp [evaluate, cell, observation, ancestor_zero]
  | succ k ih =>
    have hp : p ≠ [] := by intro he; simp [he] at hk
    have hkp : k ≤ (parent p).length := by rw [length_parent]; omega
    have hd : (parent p).length - k = p.length - (k + 1) := by rw [length_parent]; omega
    have hl : p.length - (k + 1) + k < (child p false).length := by
      simp only [child, List.length_append, List.length_singleton]
      omega
    have hr : p.length - (k + 1) + k < (child p true).length := by
      simpa only [child, List.length_append, List.length_singleton] using hl
    rw [evaluate_nonroot k _ p hp, evaluate_below m k c _ _ hl,
      evaluate_below m k c _ _ hr, ← hd, ih (parent p) hkp, ancestor_parent]
    split_ifs <;> simp [pow_succ] <;> ring

private theorem minimum_depth_mass (m k : ℕ) (p : Address) (hk : k ≤ p.length)
    (c : ZMod m) :
    B m p k (cell m c (p.length - k)) =
      if q m (ancestor p k) = c then (1 / 3 : ℝ) ^ k else 0 := by
  rw [B_evaluate]
  exact minimum_depth_evaluate m k p hk c

private theorem same_evaluate (m j : ℕ) (hm : 3 ≤ m) (p p' : Address)
    (hs : Same m j p p') (f : ZMod m × ℕ → ℝ) :
    evaluate j (fun x => f (observation m x)) p =
      evaluate j (fun x => f (observation m x)) p' := by
  induction j generalizing p p' with
  | zero =>
    apply congrArg f
    apply Prod.ext
    · simpa only [ancestor_zero, observation] using hs.2 0 (by omega)
    · exact hs.1
  | succ j ih =>
    simp only [evaluate]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    exact ih _ _ (same_move m j hm p p' hs a)

/-- The full inclusive family of bounded real endpoint tests is equivalent to
the literal truncated ancestor signature, for every depth and every finite budget. -/
theorem bounded_endpoints_iff_signature (m : ℕ) (hm : 3 ≤ m) (h : ℕ) (p p' : Address) :
    signature m h p = signature m h p' ↔
      ∀ j : ℕ, j ≤ h → ∀ f : ZMod m × ℕ → ℝ, Bounded f → B m p j f = B m p' j f := by
  constructor
  · intro he j hj f _
    rw [B_evaluate, B_evaluate]
    have hs := (signature_eq_iff m h p p').mp he
    exact same_evaluate m j hm p p' ⟨hs.1, fun k hk => hs.2 k (by omega)⟩ f
  · intro he
    have initial := he 0 (by omega) (cell m (q m p) p.length)
      (cell_bounded m (q m p) p.length)
    rw [B_evaluate, B_evaluate] at initial
    simp only [evaluate, cell, observation, Prod.mk.injEq, and_self, ite_true] at initial
    have ho : q m p' = q m p ∧ p'.length = p.length := by
      by_contra hn
      simp [hn] at initial
    apply (signature_eq_iff m h p p').mpr
    refine ⟨ho.2.symm, fun k hk => ?_⟩
    by_cases hkn : k ≤ p.length
    · have hkn' : k ≤ p'.length := by omega
      have mass := he k hk (cell m (q m (ancestor p k)) (p.length - k))
        (cell_bounded m _ _)
      rw [minimum_depth_mass m k p hkn] at mass
      rw [← ho.2, minimum_depth_mass m k p' hkn'] at mass
      simp only [ite_true] at mass
      by_contra hn
      have hn' : q m (ancestor p' k) ≠ q m (ancestor p k) := Ne.symm hn
      rw [if_neg hn'] at mass
      exact (pow_ne_zero k (by norm_num : (1 / 3 : ℝ) ≠ 0)) mass
    · rw [ancestor_past p k (by omega), ancestor_past p' k (by omega)]

#print axioms bounded_endpoints_iff_signature

end D5.S3.Arith.FibonacciAtomic.Geometry.TrueJumpEndpoints
