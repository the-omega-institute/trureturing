/- GID: D5/S3/Quantum/PureState/QutritDickePruningRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/PureState/QutritDickePruningRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/PureState/QutritDickePruningRefutation.claim; result=D5/S3/Quantum/PureState/QutritDickePruningRefutation.result; claim=D5/S3/Quantum/PureState/QutritDickePruningRefutation.claim
   digest: The pruned qutrit Dicke circuit loses a required amplitude at occupation (1,3,1). -/

import D5.S3.Quantum.Entanglement.OccupancyWordSectors
import D5.S3.Combinatorics.Graph.LegalWords.SignedBoundary

/-! The pruned qutrit circuit can omit an amplitude required by its occupation sector. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.PureState.QutritDickePruningRefutation

noncomputable section

open D5.S3.Combinatorics.Graph.LegalWords.SignedBoundary (vertexDelta)

open D5.S3.Quantum.Entanglement
abbrev State (n : ℕ) := OccupancyWordSectors.Word (Fin 3) n → ℝ
abbrev Occupation := Fin 3 → ℕ

/-- Wire numbers increase from right to left. Out-of-register reads are zero. -/
def wire {n : ℕ} (t : OccupancyWordSectors.Word (Fin 3) n) (r : ℕ) : Fin 3 :=
  if h : r < n then t ⟨r, h⟩ else 0

/-- An out-of-register update acts as the identity. -/
def put {n : ℕ} (t : OccupancyWordSectors.Word (Fin 3) n) (r : ℕ) (a : Fin 3) : OccupancyWordSectors.Word (Fin 3) n :=
  if h : r < n then Function.update t ⟨r, h⟩ a else t

def controlsHold {n : ℕ} (controls : List (ℕ × Fin 3)) (t : OccupancyWordSectors.Word (Fin 3) n) : Bool :=
  controls.all (fun p => decide (p.1 < n) && decide (wire t p.1 = p.2))

/-- Controlled exchange, acting by the inverse basis permutation. -/
def controlledX {n : ℕ} (target : ℕ) (controls : List (ℕ × Fin 3))
    (i j : Fin 3) (f : State n) : State n :=
  fun t => if controlsHold controls t then
    f (put t target (Equiv.swap i j (wire t target))) else f t

/-- The real rotation has rows `(c,-s)` and `(s,c)` in the `(i,j)` subspace. -/
def controlledR {n : ℕ} (target : ℕ) (controls : List (ℕ × Fin 3))
    (i j : Fin 3) (c s : ℝ) (f : State n) : State n :=
  fun t => if controlsHold controls t then
    if wire t target = i then c * f t - s * f (put t target j)
    else if wire t target = j then s * f (put t target i) + c * f t
    else f t
  else f t

/-- The three elementary operations in the paper's `V` circuit, in time order. -/
def V (n m l : ℕ) (i j : Fin 3) (f : State n) : State n :=
  let off := n - m
  let x := controlledX (off + l) [(off, j)] i j
  let cs := [(off + l, j)] ++
    (if 2 ≤ l then [(off + (l - 1), j)] else []) ++
    (if 0 < i.val ∧ l ≤ m - 2 then [(off + (m - 1), i)] else [])
  x (controlledR off cs i j (Real.sqrt ((l : ℝ) / m))
    (-Real.sqrt (1 - (l : ℝ) / m)) (x f))

def I (n m l : ℕ) (f : State n) : State n :=
  V n m l 1 2 (V n m l 0 2 (V n m l 0 1 f))

/-- Both rotations use the common controls, including their boundary omissions. -/
def II (n m l₁ l₂ : ℕ) (f : State n) : State n :=
  let off := n - m
  let x := controlledX (off + l₂) [(off, 2)] 1 2
  let y := controlledX (off + l₁) [(off, 1)] 0 1
  let cs := [(off + l₂, 2)] ++
    (if 2 ≤ l₂ then [(off + (l₂ - 1), 2)] else []) ++
    (if l₂ < l₁ - 1 then [(off + (l₁ - 1), 1)] else [])
  let r₁ := controlledR off ((off + l₁, 0) :: cs) 1 2
    (Real.sqrt ((l₂ : ℝ) / m)) (-Real.sqrt (1 - (l₂ : ℝ) / m))
  let r₂ := controlledR off ((off + l₁, 1) :: cs) 0 1
    (Real.sqrt (((l₁ - l₂ : ℕ) : ℝ) / (m - l₂ : ℕ)))
    (-Real.sqrt (1 - ((l₁ - l₂ : ℕ) : ℝ) / (m - l₂ : ℕ)))
  y (r₂ (y (x (r₁ (x f)))))

def prunedTilde (n m : ℕ) (k : Occupation) (f : State n) : State n :=
  let kt := if k 0 = 0 then k 2 else max (k 1) (k 2)
  (List.Ico (max (kt + m - n) 1) (min kt (m - 1) + 1)).foldl
    (fun g l => I n m l g) f

def prunedTildeTilde (n m : ℕ) (k : Occupation) (f : State n) : State n :=
  let l₁ := k 1 + k 2
  let l₂ := k 2
  (List.Ico (max (l₂ + m - n) 1) (min l₂ (m - 2) + 1)).foldl
    (fun g b => (List.Ico (max (l₁ + m - n) (b + 1)) (min l₁ (m - 1) + 1)).foldl
      (fun h a => II n m a b h) g) f

def prunedW (n m : ℕ) (k : Occupation) (f : State n) : State n :=
  prunedTildeTilde n m k (prunedTilde n m k f)

/-- The largest register block acts first. -/
def prunedU (n : ℕ) (k : Occupation) (f : State n) : State n :=
  (List.Ico 2 (n + 1)).reverse.foldl (fun g m => prunedW n m k g) f

def initialWord (n : ℕ) (k : Occupation) : OccupancyWordSectors.Word (Fin 3) n :=
  fun w => if w.val < k 2 then 2 else if w.val < k 1 + k 2 then 1 else 0

/-- The occupation counts use the existing multiset-of-letters representation. -/
def dicke (n : ℕ) (k : Occupation) : State n :=
  fun t => if ∀ s, (D5.S3.Quantum.Entanglement.OccupancyWordSectors.occupation t).count s = k s
    then 1 / Real.sqrt ((n.factorial / ((k 0).factorial * (k 1).factorial *
      (k 2).factorial) : ℕ) : ℝ) else 0

def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ k₀ k₁ k₂ : ℕ, k₀ + k₁ + k₂ = n →
    prunedU n ![k₀, k₁, k₂] (vertexDelta (initialWord n ![k₀, k₁, k₂])) =
      dicke n ![k₀, k₁, k₂]

private def witnessOccupation : Occupation := ![1, 3, 1]
private def inputWord : OccupancyWordSectors.Word (Fin 3) 5 := ![2, 1, 1, 1, 0]
private def branchWord : OccupancyWordSectors.Word (Fin 3) 5 := ![0, 2, 1, 1, 1]
private def targetWord : OccupancyWordSectors.Word (Fin 3) 5 := ![0, 1, 1, 1, 2]

private theorem wire_put_ne {n : ℕ} (t : OccupancyWordSectors.Word (Fin 3) n) (r q : ℕ) (a : Fin 3)
    (h : r ≠ q) : wire (put t q a) r = wire t r := by
  by_cases hr : r < n <;> by_cases hq : q < n <;>
    unfold wire put <;> simp [hr, hq, Fin.ext_iff, h]

private theorem project_x {n : ℕ} (r : ℕ) (a : Fin 3) (target : ℕ)
    (cs : List (ℕ × Fin 3)) (i j : Fin 3) (f : State n) (h : r ≠ target) :
    Set.indicator {t | wire t r = a} (controlledX target cs i j f) =
      controlledX target cs i j (Set.indicator {t | wire t r = a} f) := by
  funext t
  unfold controlledX
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  by_cases ht : wire t r = a <;> simp [wire_put_ne t r target _ h, ht]

private theorem project_r {n : ℕ} (r : ℕ) (a : Fin 3) (target : ℕ)
    (cs : List (ℕ × Fin 3)) (i j : Fin 3) (c s : ℝ) (f : State n) (h : r ≠ target) :
    Set.indicator {t | wire t r = a} (controlledR target cs i j c s f) =
      controlledR target cs i j c s (Set.indicator {t | wire t r = a} f) := by
  funext t
  unfold controlledR
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  by_cases ht : wire t r = a <;> simp [wire_put_ne t r target _ h, ht]

private theorem scale_x {n : ℕ} (a : ℝ) (target : ℕ)
    (cs : List (ℕ × Fin 3)) (i j : Fin 3) (f : State n) :
    controlledX target cs i j (fun t => a * f t) =
      fun t => a * controlledX target cs i j f t := by
  funext t
  unfold controlledX
  exact (mul_ite _ _ _ _).symm

private theorem scale_r {n : ℕ} (a : ℝ) (target : ℕ)
    (cs : List (ℕ × Fin 3)) (i j : Fin 3) (c s : ℝ) (f : State n) :
    controlledR target cs i j c s (fun t => a * f t) =
      fun t => a * controlledR target cs i j c s f t := by
  funext t
  unfold controlledR
  split_ifs <;> ring

private theorem project_v (n m l r : ℕ) (a i j : Fin 3) (f : State n)
    (h0 : r ≠ n - m) (hl : r ≠ n - m + l) :
    Set.indicator {t | wire t r = a} (V n m l i j f) =
      V n m l i j (Set.indicator {t | wire t r = a} f) := by
  unfold V
  simp only [project_x r a _ _ _ _ _ hl, project_r r a _ _ _ _ _ _ _ h0]

private theorem project_i (n m l r : ℕ) (a : Fin 3) (f : State n)
    (h0 : r ≠ n - m) (hl : r ≠ n - m + l) :
    Set.indicator {t | wire t r = a} (I n m l f) = I n m l (Set.indicator {t | wire t r = a} f) := by
  unfold I
  simp only [project_v n m l r a _ _ _ h0 hl]

private theorem project_ii (n m l₁ l₂ r : ℕ) (a : Fin 3) (f : State n)
    (h0 : r ≠ n - m) (h1 : r ≠ n - m + l₁) (h2 : r ≠ n - m + l₂) :
    Set.indicator {t | wire t r = a} (II n m l₁ l₂ f) =
      II n m l₁ l₂ (Set.indicator {t | wire t r = a} f) := by
  unfold II
  simp only [project_x r a _ _ _ _ _ h1, project_x r a _ _ _ _ _ h2,
    project_r r a _ _ _ _ _ _ _ h0]

private theorem scale_v (n m l : ℕ) (a : ℝ) (i j : Fin 3) (f : State n) :
    V n m l i j (fun t => a * f t) = fun t => a * V n m l i j f t := by
  unfold V
  simp only [scale_x, scale_r]

private theorem scale_i (n m l : ℕ) (a : ℝ) (f : State n) :
    I n m l (fun t => a * f t) = fun t => a * I n m l f t := by
  unfold I
  simp only [scale_v]

private theorem scale_ii (n m l₁ l₂ : ℕ) (a : ℝ) (f : State n) :
    II n m l₁ l₂ (fun t => a * f t) = fun t => a * II n m l₁ l₂ f t := by
  unfold II
  simp only [scale_x, scale_r]

private theorem wire_apply {n : ℕ} (t : OccupancyWordSectors.Word (Fin 3) n) (r : ℕ) :
    wire t r = if h : r < n then t ⟨r, h⟩ else 0 := rfl

private theorem put_apply {n : ℕ} (t : OccupancyWordSectors.Word (Fin 3) n) (r : ℕ) (a : Fin 3) :
    put t r a = if h : r < n then Function.update t ⟨r, h⟩ a else t := rfl

private theorem controls_apply {n : ℕ} (cs : List (ℕ × Fin 3)) (t : OccupancyWordSectors.Word (Fin 3) n) :
    controlsHold cs t = cs.all (fun p => decide (p.1 < n) && decide (wire t p.1 = p.2)) := rfl

private theorem x_apply {n : ℕ} (target : ℕ) (cs : List (ℕ × Fin 3))
    (i j : Fin 3) (f : State n) (t : OccupancyWordSectors.Word (Fin 3) n) :
    controlledX target cs i j f t = if controlsHold cs t then
      f (put t target (Equiv.swap i j (wire t target))) else f t := rfl

private theorem r_apply {n : ℕ} (target : ℕ) (cs : List (ℕ × Fin 3))
    (i j : Fin 3) (c s : ℝ) (f : State n) (t : OccupancyWordSectors.Word (Fin 3) n) :
    controlledR target cs i j c s f t = if controlsHold cs t then
      if wire t target = i then c * f t - s * f (put t target j)
      else if wire t target = j then s * f (put t target i) + c * f t
      else f t
    else f t := rfl

set_option maxHeartbeats 800000 in
-- The pointwise calculation checks all 3^5 register words.
private theorem i53_input : I 5 5 3 (vertexDelta inputWord) = vertexDelta inputWord := by
  funext t
  have ht : t = ![t 0, t 1, t 2, t 3, t 4] := List.ofFn_inj.mp rfl
  rw [ht]
  generalize t 0 = a, t 1 = b, t 2 = c, t 3 = d, t 4 = e
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e
  all_goals
    unfold I V inputWord
    norm_num (config := { implicitDefEqProofs := false })
      [x_apply, r_apply, controls_apply, wire_apply, put_apply, vertexDelta, Pi.single_apply,
      Equiv.swap_apply_def, Function.update_apply, funext_iff, Fin.forall_fin_succ]

set_option maxHeartbeats 800000 in
-- The pointwise calculation checks all 3^5 register words.
private theorem project_w5 :
    Set.indicator {t | wire t 0 = 0} (prunedW 5 5 witnessOccupation (vertexDelta inputWord)) =
      fun t => (1 / Real.sqrt 5) * vertexDelta branchWord t := by
  change Set.indicator {t | wire t 0 = 0} (II 5 5 4 1 (I 5 5 3 (vertexDelta inputWord))) = _
  rw [i53_input]
  funext t
  have ht : t = ![t 0, t 1, t 2, t 3, t 4] := List.ofFn_inj.mp rfl
  rw [ht]
  generalize t 0 = a, t 1 = b, t 2 = c, t 3 = d, t 4 = e
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e
  all_goals
    unfold II inputWord branchWord
    norm_num (config := { implicitDefEqProofs := false })
      [x_apply, r_apply, controls_apply, wire_apply, put_apply, vertexDelta, Pi.single_apply,
      Set.indicator_apply, Set.mem_setOf_eq,
      Equiv.swap_apply_def, Function.update_apply, funext_iff,
      Fin.forall_fin_succ, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4)]
  all_goals ring

set_option maxHeartbeats 800000 in
-- The pointwise calculation checks all 3^5 register words.
private theorem i42_branch :
    I 5 4 2 (vertexDelta branchWord) = vertexDelta branchWord := by
  funext t
  have ht : t = ![t 0, t 1, t 2, t 3, t 4] := List.ofFn_inj.mp rfl
  rw [ht]
  generalize t 0 = a, t 1 = b, t 2 = c, t 3 = d, t 4 = e
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e
  all_goals
    unfold I V branchWord
    norm_num (config := { implicitDefEqProofs := false })
      [x_apply, r_apply, controls_apply, wire_apply, put_apply, vertexDelta, Pi.single_apply,
      Equiv.swap_apply_def, Function.update_apply, funext_iff, Fin.forall_fin_succ]

set_option maxHeartbeats 800000 in
-- The pointwise calculation checks all 3^5 register words.
private theorem i43_branch :
    I 5 4 3 (vertexDelta branchWord) = vertexDelta branchWord := by
  funext t
  have ht : t = ![t 0, t 1, t 2, t 3, t 4] := List.ofFn_inj.mp rfl
  rw [ht]
  generalize t 0 = a, t 1 = b, t 2 = c, t 3 = d, t 4 = e
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e
  all_goals
    unfold I V branchWord
    norm_num (config := { implicitDefEqProofs := false })
      [x_apply, r_apply, controls_apply, wire_apply, put_apply, vertexDelta, Pi.single_apply,
      Equiv.swap_apply_def, Function.update_apply, funext_iff, Fin.forall_fin_succ]

set_option maxHeartbeats 800000 in
-- The pointwise calculation checks all 3^5 register words.
private theorem ii431_branch :
    II 5 4 3 1 (vertexDelta branchWord) = vertexDelta branchWord := by
  funext t
  have ht : t = ![t 0, t 1, t 2, t 3, t 4] := List.ofFn_inj.mp rfl
  rw [ht]
  generalize t 0 = a, t 1 = b, t 2 = c, t 3 = d, t 4 = e
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e
  all_goals
    unfold II branchWord
    norm_num (config := { implicitDefEqProofs := false })
      [x_apply, r_apply, controls_apply, wire_apply, put_apply, vertexDelta, Pi.single_apply,
      Equiv.swap_apply_def, Function.update_apply, funext_iff, Fin.forall_fin_succ]

private theorem w4_branch :
    prunedW 5 4 witnessOccupation (vertexDelta branchWord) = vertexDelta branchWord := by
  change II 5 4 3 1 (I 5 4 3 (I 5 4 2 (vertexDelta branchWord))) = vertexDelta branchWord
  rw [i42_branch, i43_branch, ii431_branch]

private theorem project_w4 (f : State 5) :
    Set.indicator {t | wire t 0 = 0} (prunedW 5 4 witnessOccupation f) =
      prunedW 5 4 witnessOccupation (Set.indicator {t | wire t 0 = 0} f) := by
  change Set.indicator {t | wire t 0 = 0} (II 5 4 3 1 (I 5 4 3 (I 5 4 2 f))) =
    II 5 4 3 1 (I 5 4 3 (I 5 4 2 (Set.indicator {t | wire t 0 = 0} f)))
  rw [project_ii 5 4 3 1 0 0 _ (by decide) (by decide) (by decide),
    project_i 5 4 3 0 0 _ (by decide) (by decide),
    project_i 5 4 2 0 0 _ (by decide) (by decide)]

private theorem w4_scale (a : ℝ) (f : State 5) :
    prunedW 5 4 witnessOccupation (fun t => a * f t) =
      fun t => a * prunedW 5 4 witnessOccupation f t := by
  change II 5 4 3 1 (I 5 4 3 (I 5 4 2 (fun t => a * f t))) =
    fun t => a * II 5 4 3 1 (I 5 4 3 (I 5 4 2 f)) t
  rw [scale_i, scale_i, scale_ii]

private theorem project_tail (r : ℕ) (hr : r ≤ 1) (a : Fin 3) (f : State 5) :
    Set.indicator {t | wire t r = a} (prunedW 5 2 witnessOccupation (prunedW 5 3 witnessOccupation f)) =
      prunedW 5 2 witnessOccupation (prunedW 5 3 witnessOccupation (Set.indicator {t | wire t r = a} f)) := by
  change Set.indicator {t | wire t r = a} (I 5 2 1 (II 5 3 2 1 (I 5 3 2 (I 5 3 1 f)))) =
    I 5 2 1 (II 5 3 2 1 (I 5 3 2 (I 5 3 1 (Set.indicator {t | wire t r = a} f))))
  rw [project_i 5 2 1 r a _ (by omega) (by omega),
    project_ii 5 3 2 1 r a _ (by omega) (by omega) (by omega),
    project_i 5 3 2 r a _ (by omega) (by omega),
    project_i 5 3 1 r a _ (by omega) (by omega)]

private theorem tail_zero (f : State 5)
    (h : ∀ t, wire t 0 = 0 → wire t 1 ≠ 2 → f t = 0) :
    prunedW 5 2 witnessOccupation (prunedW 5 3 witnessOccupation f) targetWord = 0 := by
  have hf : Set.indicator {t | wire t 0 = 0} f =
      Set.indicator {t | wire t 1 = 2} (Set.indicator {t | wire t 0 = 0} f) := by
    funext t
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h0 : wire t 0 = 0 <;> by_cases h1 : wire t 1 = 2 <;>
      simp [h0, h1, h t]
  have h0 := congrFun (project_tail 0 (by decide) 0 f) targetWord
  rw [hf, ← project_tail 1 (by decide)] at h0
  simp only [Set.indicator_apply, Set.mem_setOf_eq] at h0
  exact h0

private theorem output_zero :
    prunedU 5 witnessOccupation (vertexDelta (initialWord 5 witnessOccupation)) targetWord = 0 := by
  have hw5 := project_w5
  have hw4 := project_w4 (prunedW 5 5 witnessOccupation (vertexDelta inputWord))
  rw [hw5, w4_scale, w4_branch] at hw4
  have h : ∀ t, wire t 0 = 0 → wire t 1 ≠ 2 →
      prunedW 5 4 witnessOccupation
        (prunedW 5 5 witnessOccupation (vertexDelta inputWord)) t = 0 := by
    intro t h0 h1
    have ht := congrFun hw4 t
    have hb : t ≠ branchWord := by
      intro he
      subst t
      exact h1 rfl
    have hb0 : vertexDelta branchWord t = 0 := by
      exact Pi.single_eq_of_ne hb 1
    simp only [Set.indicator_apply, Set.mem_setOf_eq] at ht
    simpa only [h0, hb0, ite_true, mul_zero] using ht
  have ht := tail_zero _ h
  have hi : initialWord 5 witnessOccupation = inputWord := by
    funext w
    fin_cases w <;> rfl
  rw [hi]
  exact ht

private theorem target_value :
    dicke 5 witnessOccupation targetWord = 1 / Real.sqrt 20 := by
  have hc : ∀ s, (D5.S3.Quantum.Entanglement.OccupancyWordSectors.occupation
      targetWord).count s = witnessOccupation s := by
    intro s
    fin_cases s <;> decide
  unfold dicke
  rw [ite_eq_left hc]
  rfl

private theorem target_nonzero : dicke 5 witnessOccupation targetWord ≠ 0 := by
  rw [target_value]
  exact one_div_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))

theorem result : ¬ claim := by
  intro hc
  have he := congrFun (hc 5 (by decide) 1 3 1 (by decide)) targetWord
  change prunedU 5 witnessOccupation (vertexDelta (initialWord 5 witnessOccupation)) targetWord =
    dicke 5 witnessOccupation targetWord at he
  exact target_nonzero (he.symm.trans output_zero)

end
end D5.S3.Quantum.PureState.QutritDickePruningRefutation
