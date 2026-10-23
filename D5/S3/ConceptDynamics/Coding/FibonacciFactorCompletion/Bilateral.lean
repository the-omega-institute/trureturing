/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent bilateral letter pasts support complete execution-word parsing. -/


import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Constructions
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

noncomputable def t : ℝ := (Real.sqrt 5 - 1) / 2

noncomputable def g : ℝ := 2 * t - 1

noncomputable def rho : ℝ := g ^ 6

noncomputable def chi : ℝ := g ^ 20

inductive Side | high | low
  deriving DecidableEq, Repr

inductive Model | original | anchored
  deriving DecidableEq, Repr

abbrev Color := Fin 6

def colorsD : List Color := [2, 1, 0, 2, 1, 0]

def colorsE : List Color := [2, 3, 0, 3, 4, 2, 0, 1, 0, 5, 2, 1, 1, 3, 3, 5, 0, 0, 1, 2]

structure Return where
  m : ℕ
  r : ℕ
  m_pos : 0 < m
  r_pos : 0 < r
  deriving DecidableEq

def returnColors (a : Return) : List Color :=
  (List.replicate a.m colorsD).flatten ++ (List.replicate a.r colorsE).flatten

def history (model : Model) (execution : List Return) : List Color :=
  colorsD ++ colorsE ++ (execution.reverse.map returnColors).flatten ++
    (match model with | .original => [] | .anchored => colorsD ++ colorsE)

noncomputable def hSide : Side → ℝ
  | .high => (39 - 6 * g) / 380
  | .low => (46 + 31 * g) / 380

noncomputable def aSide (j : Side) : ℝ := (1 - rho) * hSide j

def listWeight : List Return → ℕ
  | [] => 0
  | a :: rest => 6 * a.m + 20 * a.r + listWeight rest

end D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

/-- Execution letters are distinct from literal source labels and colors. -/
inductive CuLetter | c | u
  deriving DecidableEq, Repr

instance : Fintype CuLetter where
  elems := {CuLetter.c, CuLetter.u}
  complete a := by cases a <;> simp

instance : TopologicalSpace CuLetter := ⊥
instance : DiscreteTopology CuLetter := ⟨rfl⟩

def isC : CuLetter → Bool | CuLetter.c => true | CuLetter.u => false
def isU : CuLetter → Bool | CuLetter.c => false | CuLetter.u => true

def executionWord : List Return → List CuLetter
  | [] => []
  | a :: xs => List.replicate a.r CuLetter.c ++ List.replicate a.m CuLetter.u ++ executionWord xs

def wordWeight : List CuLetter → ℕ
  | [] => 0
  | CuLetter.c :: xs => 20 + wordWeight xs
  | CuLetter.u :: xs => 6 + wordWeight xs

set_option maxHeartbeats 600000 in
-- Maximal initial runs recover both positive return exponents before recursion.
/-- Complete execution words have canonical maximal c/u runs. Their run counts
recover the positive return list uniquely and preserve the original 20/6 weight. -/
theorem complete_execution_word_parser :
    (∀ (a : Return) (xs : List Return),
      (executionWord (a :: xs)).takeWhile isC = List.replicate a.r CuLetter.c) ∧
    (∀ (a : Return) (xs : List Return),
      ((executionWord (a :: xs)).drop a.r).takeWhile isU = List.replicate a.m CuLetter.u) ∧
    Function.Injective executionWord ∧
    (∀ xs : List Return, wordWeight (executionWord xs) = listWeight xs) ∧
    (∀ model : Model, Function.Injective (history model)) := by
  have headU (xs : List Return) : (executionWord xs).takeWhile isU = [] := by
    cases xs with
    | nil => rfl
    | cons a xs =>
      cases hr : a.r with
      | zero => have h := a.r_pos; omega
      | succ r => simp [executionWord, hr, List.replicate_succ, List.takeWhile_cons, isU]
  have cprefix (n : ℕ) (rest : List CuLetter) :
      (List.replicate n CuLetter.c ++ CuLetter.u :: rest).takeWhile isC = List.replicate n CuLetter.c := by
    induction n with
    | zero => simp [List.takeWhile_cons, isC]
    | succ n ih => simp [List.replicate_succ, List.takeWhile_cons, isC, ih]
  have uprefix (n : ℕ) (xs : List Return) :
      (List.replicate n CuLetter.u ++ executionWord xs).takeWhile isU = List.replicate n CuLetter.u := by
    induction n with
    | zero => simpa using headU xs
    | succ n ih => simp [List.replicate_succ, List.takeWhile_cons, isU, ih]
  have firstC (a : Return) (xs : List Return) :
      (executionWord (a :: xs)).takeWhile isC = List.replicate a.r CuLetter.c := by
    cases hm : a.m with
    | zero => have h := a.m_pos; omega
    | succ m =>
      simpa only [executionWord, hm, List.replicate_succ, List.append_assoc,
        List.cons_append] using cprefix a.r (List.replicate m CuLetter.u ++ executionWord xs)
  have afterC (a : Return) (xs : List Return) :
      (executionWord (a :: xs)).drop a.r = List.replicate a.m CuLetter.u ++ executionWord xs := by
    simp [executionWord, List.append_assoc, List.drop_append]
  have firstU (a : Return) (xs : List Return) :
      ((executionWord (a :: xs)).drop a.r).takeWhile isU = List.replicate a.m CuLetter.u := by
    rw [afterC]; exact uprefix a.m xs
  have injective : Function.Injective executionWord := by
    intro xs
    induction xs with
    | nil =>
      intro ys heq
      cases ys with
      | nil => rfl
      | cons b ys =>
        have h := congrArg List.length heq
        simp only [executionWord, List.length_nil, List.length_append, List.length_replicate] at h
        have hr := b.r_pos; omega
    | cons a xs ih =>
      intro ys heq
      cases ys with
      | nil =>
        have h := congrArg List.length heq
        simp only [executionWord, List.length_nil, List.length_append, List.length_replicate] at h
        have hr := a.r_pos; omega
      | cons b ys =>
        have hr : a.r = b.r := by
          have h := congrArg (fun w : List CuLetter => (w.takeWhile isC).length) heq
          simpa only [firstC, List.length_replicate] using h
        have hu : List.replicate a.m CuLetter.u ++ executionWord xs =
            List.replicate b.m CuLetter.u ++ executionWord ys := by
          have h := congrArg (List.drop a.r) heq
          rw [afterC, hr, afterC] at h
          exact h
        have hm : a.m = b.m := by
          have h := congrArg (fun w : List CuLetter => (w.takeWhile isU).length) hu
          simpa only [uprefix, List.length_replicate] using h
        have htail : executionWord xs = executionWord ys := by
          rw [← hm] at hu
          exact List.append_cancel_left hu
        have hab : a = b := by cases a; cases b; simp_all
        exact congrArg₂ List.cons hab (ih htail)
  have appendWeight (w v : List CuLetter) : wordWeight (w ++ v) = wordWeight w + wordWeight v := by
    induction w with
    | nil => simp [wordWeight]
    | cons a w ih => cases a <;> simp [wordWeight, ih, Nat.add_assoc]
  have cweight (n : ℕ) : wordWeight (List.replicate n CuLetter.c) = 20 * n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, wordWeight, ih]; omega
  have uweight (n : ℕ) : wordWeight (List.replicate n CuLetter.u) = 6 * n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, wordWeight, ih]; omega
  let encode (w : List CuLetter) : List Color :=
    (w.map (fun l => match l with | .c => colorsE | .u => colorsD)).flatten
  have encodeAppend (w v : List CuLetter) : encode (w ++ v) = encode w ++ encode v := by
    induction w with
    | nil => simp [encode, executionWord]
    | cons a w ih => cases a <;> simp [encode, ih, List.append_assoc]
  have encodeRepC (n : ℕ) : encode (List.replicate n CuLetter.c) =
      (List.replicate n colorsE).flatten := by
    induction n with
    | zero => simp [encode]
    | succ n ih => simp [List.replicate_succ, encode, ih]
  have encodeRepU (n : ℕ) : encode (List.replicate n CuLetter.u) =
      (List.replicate n colorsD).flatten := by
    induction n with
    | zero => simp [encode]
    | succ n ih => simp [List.replicate_succ, encode, ih]
  have encodeInj : Function.Injective encode := by
    intro w
    induction w with
    | nil =>
      intro v heq
      cases v with
      | nil => simp [encode, executionWord]
      | cons y v => cases y <;> simp [encode, colorsD, colorsE] at heq
    | cons x w ih =>
      intro v heq
      cases v with
      | nil => cases x <;> simp [encode, colorsD, colorsE] at heq
      | cons y v =>
        cases x <;> cases y
        · have h : encode w = encode v := by
            exact List.append_cancel_left (by simpa only [encode, List.map_cons, List.flatten_cons] using heq)
          exact congrArg (List.cons CuLetter.c) (ih h)
        · have h := congrArg (fun l : List Color => l[1]?) heq
          simp [encode, colorsD, colorsE] at h
        · have h := congrArg (fun l : List Color => l[1]?) heq
          simp [encode, colorsD, colorsE] at h
        · have h : encode w = encode v := by
            exact List.append_cancel_left (by simpa only [encode, List.map_cons, List.flatten_cons] using heq)
          exact congrArg (List.cons CuLetter.u) (ih h)
  have externalEncoding (xs : List Return) : encode (executionWord xs).reverse =
      (xs.reverse.map returnColors).flatten := by
    induction xs with
    | nil => simp [encode, executionWord]
    | cons a xs ih =>
      simp [executionWord, List.reverse_append, List.reverse_replicate, encodeAppend,
        encodeRepC, encodeRepU, ih, List.reverse_cons, returnColors, List.append_assoc]
  refine ⟨firstC, firstU, injective, ?_, ?_⟩
  · intro xs
    induction xs with
    | nil => simp [executionWord, wordWeight, listWeight]
    | cons a xs ih =>
      simp [executionWord, appendWeight, cweight, uweight, ih, listWeight]; omega
  · intro model xs ys heq
    have h : (xs.reverse.map returnColors).flatten = (ys.reverse.map returnColors).flatten := by
      unfold history at heq
      exact List.append_cancel_left (List.append_cancel_right heq)
    have hc : encode (executionWord xs).reverse = encode (executionWord ys).reverse := by
      rw [externalEncoding, externalEncoding]; exact h
    have hr := encodeInj hc
    apply injective
    simpa only [List.reverse_reverse] using congrArg List.reverse hr

/-- The auxiliary letter dynamics use the original high-side constants. -/
noncomputable def letterMap : CuLetter → ℝ → ℝ
  | .c, z => chi * z
  | .u, z => aSide .high + rho * z

def letterWeight : CuLetter → ℕ | .c => 20 | .u => 6

/-- Compose exactly the last N letters before i, starting from the supplied seed. -/
noncomputable def finitePast (ω : ℤ → CuLetter) (i : ℤ) : ℕ → ℝ → ℝ
  | 0, z => z
  | N + 1, z => letterMap (ω (i - 1)) (finitePast ω (i - 1) N z)

def pastWeight (ω : ℤ → CuLetter) (i : ℤ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => letterWeight (ω (i - 1)) + pastWeight ω (i - 1) N

/-- A state defined by the finite zero-seed past, independently of actual records. -/
noncomputable def pastState (ω : ℤ → CuLetter) (i : ℤ) : ℝ :=
  ⨆ N : ℕ, finitePast ω i N 0

/-- The guard is checked before the current Kth c transition. -/
def AuxiliaryLanguage (K : ℕ) (d : ℝ) : Set (ℤ → CuLetter) :=
  {ω | (∀ i : ℤ, ¬ ∀ k : Fin (K + 1), ω (i + (k : ℕ)) = .c) ∧
    (∀ i : ℤ, (∀ k : Fin K, ω (i - (k : ℕ)) = .c) →
      chi ^ (K - 1) * d ≤ pastState ω i)}

open Filter Topology in
set_option maxHeartbeats 1000000 in
/-- Finite pasts converge to the unique bounded bilateral trajectory. Exact
weighted contraction, arbitrary seeds and matching-past stability are derived
from the original letter maps. The all-u state is the original fixed point h. -/
theorem bilateral_past_state :
    (∀ (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ) (x y : ℝ),
      finitePast ω i N y - finitePast ω i N x = g ^ pastWeight ω i N * (y - x)) ∧
    (∀ (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ),
      0 ≤ g ^ pastWeight ω i N ∧ g ^ pastWeight ω i N ≤ rho ^ N) ∧
    (∀ (ω : ℤ → CuLetter) (i : ℤ),
      0 ≤ pastState ω i ∧ pastState ω i ≤ hSide .high) ∧
    (∀ (ω : ℤ → CuLetter) (i : ℤ) (z : ℝ), 0 ≤ z → z ≤ hSide .high →
      Tendsto (fun N : ℕ => finitePast ω i N z) atTop (𝓝 (pastState ω i))) ∧
    (∀ (ω : ℤ → CuLetter) (i : ℤ),
      pastState ω (i + 1) = letterMap (ω i) (pastState ω i)) ∧
    (∀ (ω : ℤ → CuLetter) (y : ℤ → ℝ),
      (∀ i, 0 ≤ y i ∧ y i ≤ hSide .high) →
      (∀ i, y (i + 1) = letterMap (ω i) (y i)) → y = pastState ω) ∧
    (∀ (ω ν : ℤ → CuLetter) (i : ℤ) (N : ℕ),
      (∀ k : Fin N, ω (i - 1 - (k : ℕ)) = ν (i - 1 - (k : ℕ))) →
      |pastState ω i - pastState ν i| ≤ hSide .high * rho ^ N) ∧
    (∀ i : ℤ, pastState (fun _ => CuLetter.u) i = hSide .high) ∧
    (∀ i : ℤ, Continuous (fun ω : ℤ → CuLetter => pastState ω i)) ∧
    (∀ (K : ℕ) (d : ℝ), 1 ≤ K →
      (AuxiliaryLanguage K d).Nonempty ∧ IsCompact (AuxiliaryLanguage K d)) ∧
    (∀ (ω : ℤ → CuLetter) (i j : ℤ),
      pastState (fun n => ω (n + j)) i = pastState ω (i + j)) ∧
    (∀ (ω : ℤ → CuLetter) (j : ℤ) (K : ℕ) (d : ℝ),
      ω ∈ AuxiliaryLanguage K d ↔ (fun n => ω (n + j)) ∈ AuxiliaryLanguage K d) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsn := Real.sqrt_nonneg (5 : ℝ)
  have root : g ^ 2 + 4 * g = 1 := by dsimp [g, t]; nlinarith
  have gp : 0 < g := by dsimp [g, t]; nlinarith
  have gq : g < 1 / 4 := by nlinarith
  have g1 : g < 1 := by linarith
  have rp : 0 < rho := pow_pos gp 6
  have cp : 0 < chi := pow_pos gp 20
  have r1 : rho < 1 := pow_lt_one₀ gp.le g1 (by decide : (6 : ℕ) ≠ 0)
  have cr : chi ≤ rho := pow_le_pow_of_le_one gp.le g1.le (by decide)
  have c1 : chi ≤ 1 := le_trans cr r1.le
  let H := hSide .high
  have Hp : 0 < H := by dsimp [H, hSide]; linarith
  have ap : 0 ≤ aSide .high := by dsimp [aSide]; exact mul_nonneg (sub_pos.mpr r1).le Hp.le
  have mapInterval (a : CuLetter) (z : ℝ) (hz : 0 ≤ z ∧ z ≤ H) :
      0 ≤ letterMap a z ∧ letterMap a z ≤ H := by
    cases a <;> dsimp [letterMap]
    · exact ⟨mul_nonneg cp.le hz.1, le_trans (mul_le_mul_of_nonneg_right c1 hz.1) (by simpa using hz.2)⟩
    · constructor
      · exact add_nonneg ap (mul_nonneg rp.le hz.1)
      · have h := mul_le_mul_of_nonneg_left hz.2 rp.le
        dsimp [aSide, H] at *; nlinarith
  have mapMono (a : CuLetter) : Monotone (letterMap a) := by
    intro x y hxy
    cases a <;> dsimp [letterMap]
    · exact mul_le_mul_of_nonneg_left hxy cp.le
    · exact add_le_add_right (mul_le_mul_of_nonneg_left hxy rp.le) _
  have interval (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ) (z : ℝ) (hz : 0 ≤ z ∧ z ≤ H) :
      0 ≤ finitePast ω i N z ∧ finitePast ω i N z ≤ H := by
    induction N generalizing i with
    | zero => exact hz
    | succ N ih => exact mapInterval _ _ (ih (i - 1))
  have difference (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ) (x y : ℝ) :
      finitePast ω i N y - finitePast ω i N x = g ^ pastWeight ω i N * (y - x) := by
    induction N generalizing i with
    | zero => simp [finitePast, pastWeight]
    | succ N ih =>
      simp only [finitePast, pastWeight, pow_add]
      cases ha : ω (i - 1) <;> simp only [ha, letterMap, letterWeight]
      · rw [← mul_sub, ih]; dsimp [chi]; ring
      · rw [add_sub_add_left_eq_sub, ← mul_sub, ih]; dsimp [rho]; ring
  have contraction (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ) :
      0 ≤ g ^ pastWeight ω i N ∧ g ^ pastWeight ω i N ≤ rho ^ N := by
    refine ⟨pow_nonneg gp.le _, ?_⟩
    induction N generalizing i with
    | zero => simp [pastWeight]
    | succ N ih =>
      rw [pastWeight, pow_add, pow_succ]
      have slope : g ^ letterWeight (ω (i - 1)) ≤ rho := by
        cases ω (i - 1) <;> simp only [letterWeight]
        · exact cr
        · rfl
      calc
        g ^ letterWeight (ω (i - 1)) * g ^ pastWeight ω (i - 1) N ≤ rho * rho ^ N :=
          mul_le_mul slope (ih (i - 1)) (pow_nonneg gp.le _) rp.le
        _ = rho ^ N * rho := mul_comm _ _
  have seedMono (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ) : Monotone (finitePast ω i N) := by
    induction N generalizing i with
    | zero => exact monotone_id
    | succ N ih => exact (mapMono _).comp (ih (i - 1))
  have zeroStep (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ) :
      finitePast ω i N 0 ≤ finitePast ω i (N + 1) 0 := by
    induction N generalizing i with
    | zero => exact (interval ω i 1 0 ⟨le_rfl, Hp.le⟩).1
    | succ N ih => exact mapMono _ (ih (i - 1))
  have zeroMono (ω : ℤ → CuLetter) (i : ℤ) : Monotone (fun N => finitePast ω i N 0) :=
    monotone_nat_of_le_succ (zeroStep ω i)
  have bounded (ω : ℤ → CuLetter) (i : ℤ) : BddAbove (Set.range (fun N => finitePast ω i N 0)) := by
    refine ⟨H, ?_⟩
    rintro _ ⟨N, rfl⟩; exact (interval ω i N 0 ⟨le_rfl, Hp.le⟩).2
  have zeroLimit (ω : ℤ → CuLetter) (i : ℤ) :
      Tendsto (fun N : ℕ => finitePast ω i N 0) atTop (𝓝 (pastState ω i)) :=
    tendsto_atTop_ciSup (zeroMono ω i) (bounded ω i)
  have stateInterval (ω : ℤ → CuLetter) (i : ℤ) : 0 ≤ pastState ω i ∧ pastState ω i ≤ H := by
    constructor
    · exact ge_of_tendsto' (zeroLimit ω i) (fun N => (interval ω i N 0 ⟨le_rfl, Hp.le⟩).1)
    · exact le_of_tendsto' (zeroLimit ω i) (fun N => (interval ω i N 0 ⟨le_rfl, Hp.le⟩).2)
  have seedBounds (ω : ℤ → CuLetter) (i : ℤ) (N : ℕ) (z : ℝ) (hz : 0 ≤ z ∧ z ≤ H) :
      finitePast ω i N 0 ≤ finitePast ω i N z ∧
      finitePast ω i N z ≤ finitePast ω i N 0 + H * rho ^ N := by
    refine ⟨seedMono ω i N hz.1, ?_⟩
    have delta := difference ω i N 0 z
    have upper := mul_le_mul (contraction ω i N).2 hz.2 hz.1 (pow_nonneg rp.le N)
    simp only [sub_zero] at delta
    nlinarith
  have errorLimit : Tendsto (fun N : ℕ => H * rho ^ N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one rp.le r1).const_mul H
  have seedLimit (ω : ℤ → CuLetter) (i : ℤ) (z : ℝ) (hz : 0 ≤ z ∧ z ≤ H) :
      Tendsto (fun N : ℕ => finitePast ω i N z) atTop (𝓝 (pastState ω i)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (zeroLimit ω i)
      (by simpa using (zeroLimit ω i).add errorLimit)
    · exact fun N => (seedBounds ω i N z hz).1
    · exact fun N => (seedBounds ω i N z hz).2
  have transition (ω : ℤ → CuLetter) (i : ℤ) :
      pastState ω (i + 1) = letterMap (ω i) (pastState ω i) := by
    have shifted : Tendsto (fun N : ℕ => finitePast ω (i + 1) (N + 1) 0) atTop
        (𝓝 (pastState ω (i + 1))) := (tendsto_add_atTop_iff_nat 1).mpr (zeroLimit ω (i + 1))
    have continuous : Continuous (letterMap (ω i)) := by
      cases h : ω i
      · change Continuous (fun z : ℝ => chi * z); fun_prop
      · change Continuous (fun z : ℝ => aSide .high + rho * z); fun_prop
    have mapped := (continuous.tendsto (pastState ω i)).comp (zeroLimit ω i)
    have eqn : (fun N : ℕ => finitePast ω (i + 1) (N + 1) 0) =
        (fun N : ℕ => letterMap (ω i) (finitePast ω i N 0)) := by
      funext N; simp only [finitePast]; congr 2 <;> omega
    rw [eqn] at shifted
    exact tendsto_nhds_unique shifted mapped
  have unroll (ω : ℤ → CuLetter) (y : ℤ → ℝ)
      (hy : ∀ i, y (i + 1) = letterMap (ω i) (y i)) (i : ℤ) (N : ℕ) :
      y i = finitePast ω i N (y (i - (N : ℤ))) := by
    induction N generalizing i with
    | zero => simp [finitePast]
    | succ N ih =>
      have step := hy (i - 1)
      have idx : i - 1 + 1 = i := by omega
      rw [idx, ih (i - 1)] at step
      have idx' : i - 1 - (N : ℤ) = i - ((N + 1 : ℕ) : ℤ) := by push_cast; ring
      simpa only [finitePast, idx'] using step
  have unique (ω : ℤ → CuLetter) (y : ℤ → ℝ)
      (yb : ∀ i, 0 ≤ y i ∧ y i ≤ H)
      (hy : ∀ i, y (i + 1) = letterMap (ω i) (y i)) : y = pastState ω := by
    funext i
    have sandwich (N : ℕ) : finitePast ω i N 0 ≤ y i ∧
        y i ≤ finitePast ω i N 0 + H * rho ^ N := by
      rw [unroll ω y hy i N]
      exact seedBounds ω i N _ (yb _)
    have limit : Tendsto (fun _ : ℕ => y i) atTop (𝓝 (pastState ω i)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le (zeroLimit ω i)
        (by simpa using (zeroLimit ω i).add errorLimit)
        (fun N => (sandwich N).1) (fun N => (sandwich N).2)
    exact tendsto_nhds_unique tendsto_const_nhds limit
  have samePast (ω ν : ℤ → CuLetter) (i : ℤ) (N : ℕ)
      (hn : ∀ k : Fin N, ω (i - 1 - (k : ℕ)) = ν (i - 1 - (k : ℕ))) (z : ℝ) :
      finitePast ω i N z = finitePast ν i N z := by
    induction N generalizing i with
    | zero => rfl
    | succ N ih =>
      have first := hn ⟨0, by omega⟩
      simp only [Nat.cast_zero, sub_zero] at first
      have rest : ∀ k : Fin N, ω (i - 1 - 1 - (k : ℕ)) = ν (i - 1 - 1 - (k : ℕ)) := by
        intro k
        have h := hn ⟨k.val + 1, by omega⟩
        have idx : i - 1 - 1 - (k : ℕ) = i - 1 - ((k.val + 1 : ℕ) : ℤ) := by
          push_cast; ring
        simpa only [idx] using h
      simp only [finitePast, first, ih (i - 1) rest]
  have stability (ω ν : ℤ → CuLetter) (i : ℤ) (N : ℕ)
      (hn : ∀ k : Fin N, ω (i - 1 - (k : ℕ)) = ν (i - 1 - (k : ℕ))) :
      |pastState ω i - pastState ν i| ≤ H * rho ^ N := by
    have bw := seedBounds ω i N _ (stateInterval ω (i - (N : ℤ)))
    have bv := seedBounds ν i N _ (stateInterval ν (i - (N : ℤ)))
    rw [← unroll ω (pastState ω) (transition ω) i N] at bw
    rw [← unroll ν (pastState ν) (transition ν) i N] at bv
    rw [← samePast ω ν i N hn 0] at bv
    exact abs_le.mpr ⟨by linarith [bw.1, bv.2], by linarith [bw.2, bv.1]⟩
  have allU : ∀ i : ℤ, pastState (fun _ => CuLetter.u) i = H := by
    have fixed : (fun _ : ℤ => H) = pastState (fun _ => CuLetter.u) := by
      apply unique
      · intro i; exact ⟨Hp.le, le_rfl⟩
      · intro i; dsimp [letterMap, H, aSide]; ring
    intro i; exact (congrFun fixed i).symm
  have stateContinuous (i : ℤ) : Continuous (fun ω : ℤ → CuLetter => pastState ω i) := by
    apply continuous_iff_continuousAt.mpr
    intro ω
    apply Metric.continuousAt_iff'.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε Hp) r1
    have close : H * rho ^ N < ε := by
      have hn := (lt_div_iff₀ Hp).mp hN
      nlinarith
    have matching : ∀ᶠ ν : ℤ → CuLetter in 𝓝 ω,
        ∀ k : Fin N, ν (i - 1 - (k : ℕ)) = ω (i - 1 - (k : ℕ)) := by
      apply Filter.eventually_all.mpr
      intro k
      have h := (continuous_apply (i - 1 - (k : ℕ))).tendsto ω
      exact h.eventually ((isOpen_discrete {ω (i - 1 - (k : ℕ))}).mem_nhds (by simp))
    filter_upwards [matching] with ν hν
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (stability ν ω i N hν) close
  have runOpen (position : ℕ → ℤ) (n : ℕ) :
      IsOpen {ω : ℤ → CuLetter | ∀ k : Fin n, ω (position k) = .c} := by
    have h := isOpen_iInter_of_finite (fun k : Fin n =>
      (isOpen_discrete ({CuLetter.c} : Set CuLetter)).preimage
        (continuous_apply (position k) : Continuous (fun ω : ℤ → CuLetter => ω (position k))))
    convert h using 1
    ext ω; simp
  have languageClosed (K : ℕ) (d : ℝ) : IsClosed (AuxiliaryLanguage K d) := by
    have noRun (i : ℤ) : IsClosed {ω : ℤ → CuLetter |
        ¬ ∀ k : Fin (K + 1), ω (i + (k : ℕ)) = .c} :=
      (runOpen (fun k => i + (k : ℤ)) (K + 1)).isClosed_compl
    have guard (i : ℤ) : IsClosed {ω : ℤ → CuLetter |
        (∀ k : Fin K, ω (i - (k : ℕ)) = .c) → chi ^ (K - 1) * d ≤ pastState ω i} := by
      have closedBound : IsClosed {ω : ℤ → CuLetter | chi ^ (K - 1) * d ≤ pastState ω i} :=
        isClosed_le (continuous_const : Continuous (fun _ : ℤ → CuLetter => chi ^ (K - 1) * d))
          (stateContinuous i)
      have h := (runOpen (fun k => i - (k : ℤ)) K).isClosed_compl.union
        closedBound
      convert h using 1
      ext ω; simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq]; tauto
    have closed := (isClosed_iInter noRun).inter (isClosed_iInter guard)
    convert closed using 1
    ext ω; simp [AuxiliaryLanguage]
  have stateShift (ω : ℤ → CuLetter) (i j : ℤ) :
      pastState (fun n => ω (n + j)) i = pastState ω (i + j) := by
    have fixed := unique (fun n => ω (n + j)) (fun n => pastState ω (n + j))
      (fun n => stateInterval ω (n + j)) (by
        intro n
        have idx : n + 1 + j = n + j + 1 := by ring
        change pastState ω (n + 1 + j) = letterMap (ω (n + j)) (pastState ω (n + j))
        rw [idx]; exact transition ω (n + j))
    exact (congrFun fixed i).symm
  have shiftForward (ω : ℤ → CuLetter) (j : ℤ) (K : ℕ) (d : ℝ)
      (hω : ω ∈ AuxiliaryLanguage K d) : (fun n => ω (n + j)) ∈ AuxiliaryLanguage K d := by
    constructor
    · intro i hc
      apply hω.1 (i + j)
      intro k
      have hh := hc k
      change ω (i + (k : ℕ) + j) = .c at hh
      have idx : i + j + (k : ℕ) = i + (k : ℕ) + j := by ring
      simpa only [idx] using hh
    · intro i hc
      rw [stateShift]
      apply hω.2 (i + j)
      intro k
      have hh := hc k
      change ω (i - (k : ℕ) + j) = .c at hh
      have idx : i + j - (k : ℕ) = i - (k : ℕ) + j := by ring
      simpa only [idx] using hh
  refine ⟨difference, contraction, stateInterval, ?_, transition, unique, stability,
    allU, stateContinuous, ?_, stateShift, ?_⟩
  · intro ω i z hz0 hzH; exact seedLimit ω i z ⟨hz0, hzH⟩
  · intro K d hK
    constructor
    · refine ⟨fun _ => .u, ?_, ?_⟩
      · intro i hc
        have bad := hc ⟨0, by omega⟩
        cases bad
      · intro i hc
        have bad := hc ⟨0, by omega⟩
        cases bad
    · exact (languageClosed K d).isCompact
  · intro ω j K d
    constructor
    · exact shiftForward ω j K d
    · intro h
      have hh := shiftForward (fun n => ω (n + j)) (-j) K d h
      simpa only [add_assoc, neg_add_cancel, add_zero] using hh



end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral

namespace D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

noncomputable def returnMap (j : Side) (a : Return) (D : ℝ) : ℝ :=
  hSide j - rho ^ a.m * (hSide j - chi ^ a.r * D)

def GuardTrace (K : ℕ) (d : ℝ) (strict : Bool) (j : Side) :
    List Return → ℝ → Prop
  | [], _ => True
  | a :: rest, D => a.r ≤ K ∧
      (a.r = K → if strict then d < D else d ≤ D) ∧
      GuardTrace K d strict j rest (returnMap j a D)

end D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral

set_option maxHeartbeats 1000000 in
/-- Any finite binary word ending in u has a unique leading u run followed by
positive complete c/u returns. The first and last runs may be truncated. -/
theorem finite_run_decomposition (w : List CuLetter)
    (hend : w = [] ∨ w.getLast? = some CuLetter.u) :
    ∃! p : ℕ × List Return,
      w = List.replicate p.1 CuLetter.u ++ executionWord p.2 := by
  have existence (v : List CuLetter) (hv : v = [] ∨ v.getLast? = some CuLetter.u) :
      ∃ a : ℕ, ∃ xs : List Return,
        v = List.replicate a CuLetter.u ++ executionWord xs := by
    induction v with
    | nil => exact ⟨0, [], rfl⟩
    | cons l v ih =>
      cases v with
      | nil =>
        cases l
        · simp at hv
        · exact ⟨1, [], rfl⟩
      | cons y v =>
        have ht : (y :: v).getLast? = some CuLetter.u := by
          simpa using hv
        obtain ⟨a, xs, heq⟩ := ih (Or.inr ht)
        cases l
        · cases a with
          | zero =>
            cases xs with
            | nil => simp [executionWord] at heq
            | cons b xs =>
              let b' : Return := ⟨b.m, b.r + 1, b.m_pos, by omega⟩
              refine ⟨0, b' :: xs, ?_⟩
              simp only [List.replicate_zero, List.nil_append] at heq ⊢
              rw [heq]
              simp [executionWord, b', List.replicate_succ]
          | succ a =>
            let b : Return := ⟨a + 1, 1, by omega, by decide⟩
            refine ⟨0, b :: xs, ?_⟩
            rw [heq]
            simp [executionWord, b]
        · refine ⟨a + 1, xs, ?_⟩
          rw [heq]
          simp [List.replicate_succ]
  have first (a : ℕ) (xs : List Return) :
      (List.replicate a CuLetter.u ++ executionWord xs).takeWhile isU =
        List.replicate a CuLetter.u := by
    have hxs : (executionWord xs).takeWhile isU = [] := by
      cases xs with
      | nil => rfl
      | cons b xs =>
        obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt b.r_pos)
        simp [executionWord, hr, List.replicate_succ, isU]
    induction a with
    | zero => simpa using hxs
    | succ a ih => simp [List.replicate_succ, List.takeWhile_cons, isU, ih]
  obtain ⟨a, xs, h⟩ := existence w hend
  refine ⟨(a, xs), h, ?_⟩
  rintro ⟨b, ys⟩ hy
  have ha : b = a := by
    have hh := congrArg (fun v : List CuLetter => (v.takeWhile isU).length) (hy.symm.trans h)
    simpa only [first, List.length_replicate] using hh
  have hxs : ys = xs := by
    apply complete_execution_word_parser.2.2.1
    rw [ha] at hy
    exact List.append_cancel_left (hy.symm.trans h)
  simp only [Prod.mk.injEq]
  exact ⟨ha, hxs⟩


set_option maxHeartbeats 1000000 in
/-- An independently occurring complete word, with only its final u allowed to
be a terminal fill, inherits the exact cap and before-Kth-c return guards. -/
theorem occurrence_run_guards (K : ℕ) (d : ℝ) (hK : 1 ≤ K)
    (ω : ℤ → CuLetter) (hω : ω ∈ AuxiliaryLanguage K d)
    (i : ℤ) (xs : List Return)
    (letters : ∀ k : Fin (executionWord xs).length,
      (k.val + 1 < (executionWord xs).length ∨ (executionWord xs)[k.val] = .c) →
      ω (i + (k : ℕ)) = (executionWord xs)[k.val]) :
    GuardTrace K d false .high xs (pastState ω i) := by
  rcases bilateral_past_state with ⟨_, _, _, _, transition, _⟩
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have gp : 0 < g := by dsimp [g, t]; nlinarith
  have cp : 0 < chi := pow_pos gp 20
  have runC (j : ℤ) (n : ℕ)
      (hc : ∀ k : Fin n, ω (j + (k : ℕ)) = .c) :
      pastState ω (j + (n : ℤ)) = chi ^ n * pastState ω j := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hc0 : ∀ k : Fin n, ω (j + (k : ℕ)) = .c := fun k => hc ⟨k, by omega⟩
      have idx : j + ((n + 1 : ℕ) : ℤ) = (j + (n : ℤ)) + 1 := by omega
      rw [idx, transition, hc ⟨n, by omega⟩]
      change chi * pastState ω (j + (n : ℤ)) = _
      rw [ih hc0, pow_succ]; ring
  have runU (j : ℤ) (n : ℕ)
      (hu : ∀ k : Fin n, ω (j + (k : ℕ)) = .u) :
      pastState ω (j + (n : ℤ)) = hSide .high -
        rho ^ n * (hSide .high - pastState ω j) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hu0 : ∀ k : Fin n, ω (j + (k : ℕ)) = .u := fun k => hu ⟨k, by omega⟩
      have idx : j + ((n + 1 : ℕ) : ℤ) = (j + (n : ℤ)) + 1 := by omega
      rw [idx, transition, hu ⟨n, by omega⟩]
      change aSide .high + rho * pastState ω (j + (n : ℤ)) = _
      rw [ih hu0, pow_succ]; dsimp [aSide]; ring
  induction xs generalizing i with
  | nil => trivial
  | cons a xs ih =>
    have len : (executionWord (a :: xs)).length = a.r + a.m + (executionWord xs).length := by
      simp [executionWord]; omega
    have cletters : ∀ k : Fin a.r, ω (i + (k : ℕ)) = .c := by
      intro k
      have atC : (executionWord (a :: xs))[k.val]'(by omega) = .c := by
        simp (discharger := omega) [executionWord, List.append_assoc, List.getElem_append, k.isLt]
      have hh := letters ⟨k, by omega⟩ (Or.inr atC)
      exact hh.trans atC
    have cap : a.r ≤ K := by
      by_contra hn
      exact hω.1 i (fun k => cletters ⟨k, by omega⟩)
    have guard : a.r = K → d ≤ pastState ω i := by
      intro hr
      have atGuard : ∀ k : Fin K, ω (i + ((K - 1 : ℕ) : ℤ) - (k : ℕ)) = .c := by
        intro k
        have idx : i + ((K - 1 : ℕ) : ℤ) - (k : ℕ) =
            i + ((K - 1 - k.val : ℕ) : ℤ) := by omega
        rw [idx]; exact cletters ⟨K - 1 - k.val, by omega⟩
      have hg := hω.2 (i + ((K - 1 : ℕ) : ℤ)) atGuard
      have hc : ∀ k : Fin (K - 1), ω (i + (k : ℕ)) = .c :=
        fun k => cletters ⟨k, by omega⟩
      rw [runC i (K - 1) hc] at hg
      exact (mul_le_mul_iff_right₀ (pow_pos cp (K - 1))).mp hg
    refine ⟨cap, guard, ?_⟩
    cases xs with
    | nil => trivial
    | cons b xs =>
      have tailLen : 0 < (executionWord (b :: xs)).length := by
        simp [executionWord]; have hb := b.r_pos; omega
      have uletters : ∀ k : Fin a.m, ω (i + (a.r : ℤ) + (k : ℕ)) = .u := by
        intro k
        have hh := letters ⟨a.r + k, by omega⟩ (Or.inl (by change a.r + k.val + 1 < _; omega))
        have idx : i + ((a.r + k.val : ℕ) : ℤ) = i + (a.r : ℤ) + (k : ℕ) := by omega
        rw [idx] at hh
        simpa (discharger := omega) [executionWord, List.append_assoc, List.getElem_append, k.isLt] using hh
      have after := runU (i + a.r) a.m uletters
      rw [runC i a.r cletters] at after
      have returnState : pastState ω (i + ((a.r + a.m : ℕ) : ℤ)) =
          returnMap .high a (pastState ω i) := by
        simpa [returnMap, add_assoc, Nat.cast_add] using after
      have tailLetters : ∀ k : Fin (executionWord (b :: xs)).length,
          (k.val + 1 < (executionWord (b :: xs)).length ∨ (executionWord (b :: xs))[k.val] = .c) →
          ω (i + ((a.r + a.m : ℕ) : ℤ) + (k : ℕ)) = (executionWord (b :: xs))[k.val] := by
        intro k hk
        have atTail : (executionWord (a :: b :: xs))[a.r + a.m + k.val]'(by omega) =
            (executionWord (b :: xs))[k.val] := by
          have hr : ¬ a.r + a.m + k.val < a.r := by omega
          have hm : ¬ a.r + a.m + k.val - a.r < a.m := by omega
          have sub : a.r + a.m + k.val - a.r - a.m = k.val := by omega
          simp [executionWord, List.getElem_append, List.append_assoc, hr, hm, sub]
        have hh := letters ⟨a.r + a.m + k, by omega⟩ (by
          rcases hk with hk | hk
          · exact Or.inl (by change a.r + a.m + k.val + 1 < _; omega)
          · exact Or.inr (atTail.trans hk))
        have idx : i + ((a.r + a.m + k.val : ℕ) : ℤ) =
            i + ((a.r + a.m : ℕ) : ℤ) + (k : ℕ) := by omega
        simp only [Fin.val_mk] at hh
        rw [idx, atTail] at hh
        exact hh
      have hh := ih (i + ((a.r + a.m : ℕ) : ℤ)) tailLetters
      rwa [returnState] at hh

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion

namespace D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

noncomputable def T2 : ℝ := 1 - t

noncomputable def lam : ℝ := T2 / 10

noncomputable def execute (j : Side) : List Return → ℝ → ℝ
  | [], D => D
  | a :: rest, D => execute j rest (returnMap j a D)

end D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

/-- Exact active costs, evaluated on one execution from its fixed literal tail. -/
def StrictControl (j : Side) (b : ℝ) : List Return → ℝ → Prop
  | [], _ => True
  | a :: rest, D => lam - g ^ 2 * chi ^ a.r * D < b ∧
      StrictControl j b rest (returnMap j a D)

set_option maxHeartbeats 1000000
open Filter Topology
open scoped Topology

/-- A consumed structural interface to the existing recursive guard. -/
theorem uniform_guard_trace_iff_split
    (K : ℕ) (d : ℝ) (strict : Bool) (j : Side)
    (execution : List Return) (D : ℝ) :
    GuardTrace K d strict j execution D ↔
      ∀ (before : List Return) (a : Return) (after : List Return),
        execution = before ++ a :: after →
          a.r ≤ K ∧ (a.r = K →
            if strict then d < execute j before D
            else d ≤ execute j before D) := by
  induction execution generalizing D with
  | nil =>
      constructor
      · intro _ before a after hsplit
        have hlen := congrArg List.length hsplit
        simp only [List.length_nil, List.length_append, List.length_cons] at hlen
        omega
      · intro _
        exact True.intro
  | cons first rest ih =>
      constructor
      · rintro ⟨hcap, hguard, hrest⟩ before a after hsplit
        cases before with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at hsplit
            rcases hsplit with ⟨rfl, rfl⟩
            exact ⟨hcap, hguard⟩
        | cons first' before =>
            simp only [List.cons_append, List.cons.injEq] at hsplit
            rcases hsplit with ⟨rfl, hsplit⟩
            simpa only [execute] using
              (ih (returnMap j first D)).mp hrest before a after hsplit
      · intro h
        have hfirst := h [] first rest rfl
        refine ⟨hfirst.1, hfirst.2, (ih (returnMap j first D)).mpr ?_⟩
        intro before a after hsplit
        have hsplit' : first :: rest = (first :: before) ++ a :: after := by
          simpa only [List.cons_append] using congrArg (List.cons first) hsplit
        simpa only [execute] using h (first :: before) a after hsplit'

theorem exact_control_iff_split (j : Side) (budget : ℝ)
    (execution : List Return) (D : ℝ) :
    StrictControl j budget execution D ↔
      ∀ (before : List Return) (a : Return) (after : List Return),
        execution = before ++ a :: after →
          lam - g ^ 2 * chi ^ a.r * execute j before D < budget := by
  induction execution generalizing D with
  | nil =>
      constructor
      · intro _ before a after hsplit
        have hlen := congrArg List.length hsplit
        simp only [List.length_nil, List.length_append, List.length_cons] at hlen
        omega
      · intro _
        trivial
  | cons first rest ih =>
      constructor
      · rintro ⟨hfirst, hrest⟩ before a after hsplit
        cases before with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at hsplit
            rcases hsplit with ⟨rfl, rfl⟩
            exact hfirst
        | cons first' before =>
            simp only [List.cons_append, List.cons.injEq] at hsplit
            rcases hsplit with ⟨rfl, hsplit⟩
            simpa only [execute] using
              (ih (returnMap j first D)).mp hrest before a after hsplit
      · intro h
        refine ⟨h [] first rest rfl, (ih (returnMap j first D)).mpr ?_⟩
        intro before a after hsplit
        have hsplit' : first :: rest = (first :: before) ++ a :: after := by
          simpa only [List.cons_append] using congrArg (List.cons first) hsplit
        simpa only [execute] using h (first :: before) a after hsplit'

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
