/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Completion
   generality: G
   anchors: []
   utility: none
   digest: Actual guarded lists and bilateral factors retain completion and inverse maps. -/

import D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
import D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
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
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply

/-- A finite auxiliary word at the origin, with u at every other position. -/
def uPadding (w : List CuLetter) (i : ℤ) : CuLetter :=
  if 0 ≤ i then w[i.toNat]?.getD .u else .u

set_option maxHeartbeats 1000000 in
/-- Weak complete actual lists embed literally in the independent bilateral
language. Padding is auxiliary only; its states strictly dominate the actual
complete-boundary states, and the exact original weight is preserved. -/
theorem auxiliary_lower_padding (K : ℕ) (d : ℝ) (model : Model)
    (xs : List Return) (hK : 1 ≤ K)
    (hw : GuardTrace K d false .high xs (initial .high model)) :
    let ω := uPadding (executionWord xs)
    pastState ω 0 = hSide .high ∧
    (∀ p : ℕ, p ≤ xs.length →
      execute .high (xs.take p) (initial .high model) <
        pastState ω ((executionWord (xs.take p)).length : ℤ)) ∧
    ω ∈ AuxiliaryLanguage K d ∧ Occurs ω (executionWord xs) ∧
    AuxiliaryFactor K d (executionWord xs) ∧
    wordWeight (executionWord xs) = listWeight xs := by
  classical
  rcases bilateral_past_state with
    ⟨_, _, bounds, seedLimit, transition, _, stability, allU, _⟩
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have gp : 0 < g := by dsimp [g, t]; nlinarith
  have cp : 0 < chi := pow_pos gp 20
  have rp : 0 < rho := pow_pos gp 6
  let H := hSide .high
  have Hp : 0 ≤ H := le_trans (bounds (fun _ => .u) 0).1 (bounds (fun _ => .u) 0).2
  have fixed : letterMap .u H = H := by dsimp [letterMap, H, aSide]; ring
  have append (as bs : List Return) : executionWord (as ++ bs) =
      executionWord as ++ executionWord bs := by
    induction as with
    | nil => rfl
    | cons a as ih => simp [executionWord, ih, List.append_assoc]
  have total (w : List CuLetter) (n : ℕ) (hn : n < w.length) :
      uPadding w (n : ℤ) = w[n] := by
    simp [uPadding, List.getElem?_eq_getElem hn]
  have outLeft (w : List CuLetter) (i : ℤ) (hi : i < 0) : uPadding w i = .u := by
    simp [uPadding, not_le.mpr hi]
  have outRight (w : List CuLetter) (i : ℤ) (hi : (w.length : ℤ) ≤ i) :
      uPadding w i = .u := by
    have hn : w.length ≤ i.toNat := by omega
    simp [uPadding, show 0 ≤ i by omega, List.getElem?_eq_none hn]
  let ω := uPadding (executionWord xs)
  have zeroPast (i : ℤ) (hi : i ≤ 0) (N : ℕ) : finitePast ω i N H = H := by
    induction N generalizing i with
    | zero => rfl
    | succ N ih =>
      rw [finitePast, ih (i - 1) (by omega)]
      rw [show ω (i - 1) = .u from outLeft _ _ (by omega)]
      exact fixed
  have stateZero : pastState ω 0 = H := by
    have hlim := seedLimit ω 0 H Hp le_rfl
    have eq : (fun N : ℕ => finitePast ω 0 N H) = fun _ => H := by
      funext N; exact zeroPast 0 le_rfl N
    rw [eq] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  have runC (ν : ℤ → CuLetter) (i : ℤ) (n : ℕ)
      (hc : ∀ k : Fin n, ν (i + (k : ℕ)) = .c) :
      pastState ν (i + (n : ℤ)) = chi ^ n * pastState ν i := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hc0 : ∀ k : Fin n, ν (i + (k : ℕ)) = .c := fun k => hc ⟨k, by omega⟩
      have idx : i + ((n + 1 : ℕ) : ℤ) = (i + (n : ℤ)) + 1 := by omega
      rw [idx, transition, hc ⟨n, by omega⟩]
      change chi * pastState ν (i + (n : ℤ)) = _
      rw [ih hc0, pow_succ]; ring
  have runU (ν : ℤ → CuLetter) (i : ℤ) (n : ℕ)
      (hu : ∀ k : Fin n, ν (i + (k : ℕ)) = .u) :
      pastState ν (i + (n : ℤ)) = H - rho ^ n * (H - pastState ν i) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hu0 : ∀ k : Fin n, ν (i + (k : ℕ)) = .u := fun k => hu ⟨k, by omega⟩
      have idx : i + ((n + 1 : ℕ) : ℤ) = (i + (n : ℤ)) + 1 := by omega
      rw [idx, transition, hu ⟨n, by omega⟩]
      change aSide .high + rho * pastState ν (i + (n : ℤ)) = _
      rw [ih hu0, pow_succ]; dsimp [H, aSide]; ring
  have segment (ν : ℤ → CuLetter) (i : ℤ) (ys : List Return)
      (letters : ∀ k : Fin (executionWord ys).length,
        ν (i + (k : ℕ)) = (executionWord ys)[k]) :
      pastState ν (i + ((executionWord ys).length : ℤ)) =
        execute .high ys (pastState ν i) := by
    induction ys generalizing i with
    | nil => simp [executionWord, execute]
    | cons a ys ih =>
      have len : (executionWord (a :: ys)).length = a.r + a.m + (executionWord ys).length := by
        simp [executionWord]; omega
      have cletters : ∀ k : Fin a.r, ν (i + (k : ℕ)) = .c := by
        intro k
        have hh := letters ⟨k, by rw [len]; omega⟩
        simpa (discharger := omega) [executionWord, List.append_assoc, List.getElem_append, k.isLt] using hh
      have uletters : ∀ k : Fin a.m, ν (i + (a.r : ℤ) + (k : ℕ)) = .u := by
        intro k
        have hh := letters ⟨a.r + k, by rw [len]; omega⟩
        have idx : i + ((a.r + (k : ℕ) : ℕ) : ℤ) = i + (a.r : ℤ) + (k : ℕ) := by omega
        rw [idx] at hh
        simpa (discharger := omega) [executionWord, List.append_assoc, List.getElem_append, k.isLt] using hh
      have after := runU ν (i + a.r) a.m uletters
      rw [runC ν i a.r cletters] at after
      have returnState : pastState ν (i + ((a.r + a.m : ℕ) : ℤ)) =
          returnMap .high a (pastState ν i) := by
        simpa [returnMap, H, add_assoc, Nat.cast_add] using after
      have tailLetters : ∀ k : Fin (executionWord ys).length,
          ν (i + ((a.r + a.m : ℕ) : ℤ) + (k : ℕ)) = (executionWord ys)[k] := by
        intro k
        have hh := letters ⟨a.r + a.m + k, by rw [len]; omega⟩
        have idx : i + ((a.r + a.m + (k : ℕ) : ℕ) : ℤ) =
            i + ((a.r + a.m : ℕ) : ℤ) + (k : ℕ) := by omega
        rw [idx] at hh
        have hr : ¬ a.r + a.m + (k : ℕ) < a.r := by omega
        have hm : ¬ a.r + a.m + (k : ℕ) - a.r < a.m := by omega
        have sub : a.r + a.m + (k : ℕ) - a.r - a.m = (k : ℕ) := by omega
        simpa [executionWord, List.getElem_append, List.append_assoc, hr, hm, sub] using hh
      have hh := ih (i + ((a.r + a.m : ℕ) : ℤ)) tailLetters
      rw [returnState] at hh
      simpa [len, Nat.cast_add, add_assoc, execute] using hh
  have prefixState (pre rest : List Return) (heq : xs = pre ++ rest) :
      pastState ω ((executionWord pre).length : ℤ) = execute .high pre H := by
    have letters : ∀ k : Fin (executionWord pre).length, ω (0 + (k : ℕ)) = (executionWord pre)[k] := by
      intro k
      have e : executionWord xs = executionWord pre ++ executionWord rest := by rw [heq, append]
      have hh := total (executionWord xs) k (by rw [e]; simp; omega)
      simpa [ω, e, List.getElem_append, k.isLt] using hh
    simpa [stateZero] using segment ω 0 pre letters
  have ordered (ys : List Return) (D E : ℝ) (hDE : D < E) :
      execute .high ys D < execute .high ys E := by
    induction ys generalizing D E with
    | nil => exact hDE
    | cons a ys ih =>
      apply ih
      have pos := mul_pos (pow_pos rp a.m) (pow_pos cp a.r)
      have h := mul_pos pos (sub_pos.mpr hDE)
      dsimp [returnMap]; nlinarith
  have initH : initial .high model < H :=
    (actual_complete_boundary_geometry model []).1 .high 0 |>.2
  have coupling (p : ℕ) (hp : p ≤ xs.length) :
      execute .high (xs.take p) (initial .high model) <
        pastState ω ((executionWord (xs.take p)).length : ℤ) := by
    rw [prefixState (xs.take p) (xs.drop p) (List.take_append_drop p xs).symm]
    exact ordered _ _ _ initH
  have traceSplit (pre rest : List Return) (D : ℝ)
      (ht : GuardTrace K d false .high (pre ++ rest) D) :
      GuardTrace K d false .high rest (execute .high pre D) := by
    induction pre generalizing D with
    | nil => exact ht
    | cons a pre ih => exact ih _ ht.2.2
  have locate (ys : List Return) (n : ℕ) (hn : n < (executionWord ys).length)
      (hc : (executionWord ys)[n] = .c) :
      ∃ pre a rest k, ys = pre ++ a :: rest ∧ k < a.r ∧
        n = (executionWord pre).length + k := by
    induction ys generalizing n with
    | nil => simp [executionWord] at hn
    | cons a ys ih =>
      by_cases hr : n < a.r
      · exact ⟨[], a, ys, n, rfl, hr, by simp [executionWord]⟩
      · by_cases hm : n < a.r + a.m
        · have he : (executionWord (a :: ys))[n] = .u := by
            have hsub : n - a.r < a.m := by omega
            simp [executionWord, List.append_assoc, List.getElem_append, hr, hsub]
          rw [he] at hc; cases hc
        · have hn' : n - (a.r + a.m) < (executionWord ys).length := by
            simp only [executionWord, List.length_append, List.length_replicate] at hn; omega
          have hc' : (executionWord ys)[n - (a.r + a.m)] = .c := by
            have hsub : ¬ n - a.r < a.m := by omega
            simpa [executionWord, List.append_assoc, List.getElem_append, hr, hsub,
              Nat.sub_sub] using hc
          obtain ⟨pre, b, rest, k, heq, hk, hidx⟩ := ih _ hn' hc'
          refine ⟨a :: pre, b, rest, k, by simp [heq], hk, ?_⟩
          simp only [executionWord, List.length_append, List.length_replicate]; omega
  have lastU (ys : List Return) (hys : ys ≠ []) :
      (executionWord ys)[(executionWord ys).length - 1]'(by
        cases ys with
        | nil => contradiction
        | cons a rest => simp [executionWord]; have := a.m_pos; omega) = .u := by
    induction ys with
    | nil => contradiction
    | cons a ys ih =>
      by_cases he : ys = []
      · subst ys
        have hm := a.m_pos
        simp (discharger := omega) [executionWord, List.getElem_append]
        omega
      · have hl : 0 < (executionWord ys).length := by
          cases ys with
          | nil => contradiction
          | cons b rest => simp [executionWord]; have := b.m_pos; omega
        simpa (discharger := omega) [executionWord, List.append_assoc, List.getElem_append, hl,
          Nat.add_sub_assoc] using ih he
  have cPosition (i : ℤ) (hc : ω i = .c) :
      ∃ pre a rest k, xs = pre ++ a :: rest ∧ k < a.r ∧
        i = ((executionWord pre).length : ℤ) + (k : ℕ) := by
    have hi : 0 ≤ i := by
      by_contra hh; have hu := outLeft (executionWord xs) i (by omega)
      change ω i = .u at hu; rw [hu] at hc; cases hc
    have hin : i.toNat < (executionWord xs).length := by
      by_contra hh
      have hu := outRight (executionWord xs) i (by omega)
      change ω i = .u at hu; rw [hu] at hc; cases hc
    have hh : (executionWord xs)[i.toNat] = .c := by
      have h : ω i = (executionWord xs)[i.toNat] := by
        simpa [ω, Int.toNat_of_nonneg hi] using total (executionWord xs) i.toNat hin
      exact h.symm.trans hc
    obtain ⟨pre, a, rest, k, heq, hk, hidx⟩ := locate xs i.toNat hin hh
    exact ⟨pre, a, rest, k, heq, hk, by omega⟩
  have runData (pre : List Return) (a : Return) (rest : List Return)
      (heq : xs = pre ++ a :: rest) :
      (∀ k : Fin a.r, ω ((executionWord pre).length + (k : ℕ)) = .c) ∧
      ω ((executionWord pre).length + (a.r : ℤ)) = .u ∧
      ω (((executionWord pre).length : ℤ) - 1) = .u := by
    have e : executionWord xs = executionWord pre ++
        (List.replicate a.r .c ++ List.replicate a.m .u ++ executionWord rest) := by
      rw [heq, append, executionWord]
    have len : (executionWord xs).length =
        (executionWord pre).length + a.r + a.m + (executionWord rest).length := by simp [e]; omega
    refine ⟨?_, ?_, ?_⟩
    · intro k
      have h := total (executionWord xs) ((executionWord pre).length + k) (by rw [len]; omega)
      simpa (discharger := omega) [ω, e, List.getElem_append, List.append_assoc, k.isLt] using h
    · have h := total (executionWord xs) ((executionWord pre).length + a.r) (by
        rw [len]; have := a.m_pos; omega)
      simpa (discharger := omega) [ω, e, List.getElem_append, List.append_assoc, a.m_pos] using h
    · by_cases hp : pre = []
      · subst pre; simpa [executionWord] using outLeft (executionWord xs) (-1) (by omega)
      · have hl : 0 < (executionWord pre).length := by
          cases pre with
          | nil => contradiction
          | cons b ys => simp [executionWord]; have := b.m_pos; omega
        have h := total (executionWord xs) ((executionWord pre).length - 1) (by rw [len]; omega)
        have idx : (((executionWord pre).length - 1 : ℕ) : ℤ) =
            ((executionWord pre).length : ℤ) - 1 := by omega
        rw [idx] at h
        simpa (discharger := omega) [ω, e, List.getElem_append, lastU pre hp] using h
  have language : ω ∈ AuxiliaryLanguage K d := by
    constructor
    · intro i hc
      obtain ⟨pre, a, rest, k, heq, hk, hidx⟩ := cPosition i (by simpa using hc ⟨0, by omega⟩)
      have ht := traceSplit pre (a :: rest) _ (by simpa [heq] using hw)
      have hcap := ht.1
      have hu := (runData pre a rest heq).2.1
      have hbad := hc ⟨a.r - k, by omega⟩
      have idx : i + ((a.r - k : ℕ) : ℤ) =
          ((executionWord pre).length : ℤ) + a.r := by omega
      rw [idx, hu] at hbad; cases hbad
    · intro i hc
      obtain ⟨pre, a, rest, k, heq, hk, hidx⟩ := cPosition i (by simpa using hc ⟨0, by omega⟩)
      have ht := traceSplit pre (a :: rest) _ (by simpa [heq] using hw)
      have hcap := ht.1
      have rd := runData pre a rest heq
      have hback : K - 1 ≤ k := by
        by_contra hh
        have hbad := hc ⟨k + 1, by omega⟩
        have idx : i - ((k + 1 : ℕ) : ℤ) = ((executionWord pre).length : ℤ) - 1 := by omega
        rw [idx, rd.2.2] at hbad; cases hbad
      have kr : k = K - 1 ∧ a.r = K := by omega
      have guard := ht.2.1 kr.2
      simp only [Bool.false_eq_true, if_false] at guard
      have value := runC ω ((executionWord pre).length : ℤ) k
        (fun j => rd.1 ⟨j, by omega⟩)
      rw [← hidx] at value
      rw [value, kr.1]
      apply mul_le_mul_of_nonneg_left _ (pow_pos cp (K - 1)).le
      have st := prefixState pre (a :: rest) heq
      rw [st]
      exact guard.trans (ordered pre _ _ initH).le
  have occurrence : Occurs ω (executionWord xs) := by
    refine ⟨0, ?_⟩; intro k; simpa using total (executionWord xs) k k.isLt
  exact ⟨stateZero, coupling, language, occurrence, ⟨ω, language, occurrence⟩,
    complete_execution_word_parser.2.2.2.1 xs⟩


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


set_option maxHeartbeats 1500000 in
/-- Every genuine c-containing factor has a canonically parsed strict actual
completion from either original start, with the prescribed first-run insertion
and the exact ending-class weight overhead. -/
theorem auxiliary_factor_upper_completion (o : Ownership) (b : ℝ) (K : ℕ)
    (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K))) :
    ∃ R : Return, R.r = 1 ∧
      ∀ (model : Model) (w : List CuLetter),
        AuxiliaryFactor K ((lam - b) / g ^ 2 / chi ^ K) w → CuLetter.c ∈ w →
        ∃ (a : ℕ) (first : Return) (rest : List Return),
          let filled := if w.getLast? = some CuLetter.c then w ++ [CuLetter.u] else w
          let reset : Return := ⟨R.m + a, 1, by have := R.m_pos; omega, by decide⟩
          let extra : Return := ⟨first.m + 1, first.r, by omega, first.r_pos⟩
          filled = List.replicate a CuLetter.u ++ executionWord (first :: rest) ∧
          (∀ (a' : ℕ) (xs' : List Return),
            filled = List.replicate a' CuLetter.u ++ executionWord xs' →
            a' = a ∧ xs' = first :: rest) ∧
          ActualPairSupply model o b .strict (reset :: extra :: rest) ∧
          executionWord (reset :: extra :: rest) =
            CuLetter.c :: (List.replicate (R.m + a) CuLetter.u ++
              List.replicate first.r CuLetter.c ++
              List.replicate (first.m + 1) CuLetter.u ++ executionWord rest) ∧
          listWeight (reset :: extra :: rest) = wordWeight w + (20 + 6 * R.m) +
            (if w.getLast? = some CuLetter.c then 12 else 6) := by
  classical
  let d := (lam - b) / g ^ 2 / chi ^ K
  rcases actual_reset_first_return o b K hK hqb hbp with
    ⟨R, hr, hB, hStrict, hWeak, hTransfer, hWeight, hIncrease⟩
  refine ⟨R, hr, ?_⟩
  intro model w hw hc
  rcases hw with ⟨ω, hω, i, occurrence⟩
  let filled := if w.getLast? = some CuLetter.c then w ++ [CuLetter.u] else w
  have endCases (v : List CuLetter) (hv : v ≠ []) :
      v.getLast? = some CuLetter.c ∨ v.getLast? = some CuLetter.u := by
    induction v with
    | nil => contradiction
    | cons l v ih =>
      cases v with
      | nil => cases l <;> simp
      | cons y v => simpa using ih (by simp)
  have wne : w ≠ [] := by intro hn; simp [hn] at hc
  have filledEnd : filled.getLast? = some CuLetter.u := by
    rcases endCases w wne with he | he
    · simp [filled, he]
    · simp [filled, he]
  rcases finite_run_decomposition filled (Or.inr filledEnd) with ⟨⟨a, xs⟩, parse, unique⟩
  have cf : CuLetter.c ∈ filled := by dsimp [filled]; split <;> simp_all
  cases xs with
  | nil =>
    rw [parse] at cf
    simp [executionWord] at cf
  | cons first rest =>
    let reset : Return := ⟨R.m + a, 1, by have := R.m_pos; omega, by decide⟩
    let extra : Return := ⟨first.m + 1, first.r, by omega, first.r_pos⟩
    have plen : filled.length = a + (executionWord (first :: rest)).length := by
      rw [parse]; simp
    have originalLetter (n : ℕ) (hn : n < filled.length)
        (hnc : n + 1 < filled.length ∨ filled[n] = .c) :
        ∃ hnw : n < w.length, filled[n] = w[n] := by
      by_cases he : w.getLast? = some CuLetter.c
      · have feq : filled = w ++ [CuLetter.u] := by simp [filled, he]
        have flen : filled.length = w.length + 1 := by simp [feq]
        by_cases hnw : n < w.length
        · refine ⟨hnw, ?_⟩; simp [feq, List.getElem_append, hnw]
        · have neq : n = w.length := by omega
          have fu : filled[n] = .u := by simp [feq, List.getElem_append, hnw, neq]
          rcases hnc with hnc | hnc
          · omega
          · rw [fu] at hnc; cases hnc
      · have feq : filled = w := by simp [filled, he]
        refine ⟨by simpa [feq] using hn, ?_⟩
        simp [feq]
    have letters : ∀ k : Fin (executionWord (first :: rest)).length,
        (k.val + 1 < (executionWord (first :: rest)).length ∨
          (executionWord (first :: rest))[k.val] = .c) →
        ω (i + (a : ℤ) + (k : ℕ)) = (executionWord (first :: rest))[k.val] := by
      intro k hk
      have atParsed : filled[a + k.val]'(by omega) = (executionWord (first :: rest))[k.val] := by
        simp [parse, List.getElem_append, show ¬ a + k.val < a by omega,
          show a + k.val - a = k.val by omega]
      have hcond : a + k.val + 1 < filled.length ∨ filled[a + k.val] = .c := by
        rcases hk with hk | hk
        · exact Or.inl (by omega)
        · exact Or.inr (atParsed.trans hk)
      obtain ⟨hnw, heq⟩ := originalLetter (a + k.val) (by omega) hcond
      have hh := occurrence ⟨a + k.val, hnw⟩
      have idx : i + ((a + k.val : ℕ) : ℤ) = i + (a : ℤ) + (k : ℕ) := by omega
      simpa only [idx] using hh.trans (heq.symm.trans atParsed)
    have trace := occurrence_run_guards K d (by omega) ω hω (i + a) (first :: rest) letters
    rcases bilateral_past_state with ⟨_, _, bounds, _⟩
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    have hs0 := Real.sqrt_nonneg (5 : ℝ)
    have gp : 0 < g := by dsimp [g, t]; nlinarith
    have g1 : g < 1 := by dsimp [g, t]; nlinarith
    have cp : 0 < chi := pow_pos gp 20
    have rp : 0 < rho := pow_pos gp 6
    have c1 : chi < 1 := pow_lt_one₀ gp.le g1 (by decide)
    have r1 : rho < 1 := pow_lt_one₀ gp.le g1 (by decide)
    have hp : 0 < hSide .high := by dsimp [hSide]; nlinarith
    have ap : 0 < aSide .high := mul_pos (sub_pos.mpr r1) hp
    have initialBounds := (actual_complete_boundary_geometry model []).1 .high 0
    simp only [List.take_nil, execute] at initialBounds
    have initialPos : 0 < initial .high model := lt_trans ap initialBounds.1
    have gap : 0 ≤ hSide .high - chi * initial .high model := by
      have hh := mul_le_mul_of_nonneg_right c1.le initialPos.le
      linarith [initialBounds.2]
    have pm : rho ^ (R.m + a) ≤ rho ^ R.m :=
      pow_le_pow_of_le_one rp.le r1.le (by omega)
    have merged : returnMap .high R (initial .high model) ≤
        returnMap .high reset (initial .high model) := by
      have hh := mul_le_mul_of_nonneg_right pm gap
      dsimp [returnMap, reset]; rw [hr]; simp only [pow_one]; linarith
    let z := returnMap .high reset (initial .high model)
    have bz : hSide .high - rho ^ R.m * (hSide .high - chi * aSide .high) < z :=
      lt_of_lt_of_le (hStrict _ initialBounds.1) merged
    have dz : d < z := by
      have dd := lt_of_le_of_lt (le_max_right
        (max (xSide .high) (ySide .high)) d) hB
      exact lt_trans dd bz
    have za : aSide .high ≤ z := by
      have hh := (actual_complete_boundary_geometry model [reset]).1 .high 1
      simpa [execute, z] using hh.1.le
    have ordered (a0 : Return) (D E : ℝ) (hDE : D < E) :
        returnMap .high a0 D < returnMap .high a0 E := by
      have hh := mul_pos (mul_pos (pow_pos rp a0.m) (pow_pos cp a0.r)) (sub_pos.mpr hDE)
      dsimp [returnMap]; nlinarith
    have improve (ys : List Return) (D E : ℝ) (hDE : D < E)
        (hh : GuardTrace K d false .high ys D) : GuardTrace K d true .high ys E := by
      induction ys generalizing D E with
      | nil => trivial
      | cons a0 ys ih =>
        refine ⟨hh.1, ?_, ih _ _ (ordered a0 D E hDE) hh.2.2⟩
        intro heq
        have hg := hh.2.1 heq
        simp only [Bool.false_eq_true, if_false] at hg
        simp only [if_true]; linarith
    have firstOutput : returnMap .high first (pastState ω (i + a)) <
        returnMap .high extra z := by
      have hi := (hIncrease first.m first.r z (by have := first.m_pos; omega)
        (by have := first.r_pos; omega) trace.1 za).2
      have weak : returnMap .high first (pastState ω (i + a)) ≤
          returnMap .high first (hSide .high) := by
        have hh := mul_nonneg (mul_pos (pow_pos rp first.m) (pow_pos cp first.r)).le
          (sub_nonneg.mpr (bounds ω (i + a)).2)
        dsimp [returnMap]; nlinarith
      have strong : returnMap .high first (hSide .high) < returnMap .high extra z := by
        dsimp [returnMap, extra] at *; linarith only [hi]
      exact lt_of_le_of_lt weak strong
    have actualTrace : GuardTrace K d true .high (reset :: extra :: rest) (initial .high model) := by
      refine ⟨by dsimp [reset]; omega, ?_, ?_⟩
      · intro heq; dsimp [reset] at heq; omega
      · refine ⟨trace.1, ?_, improve rest _ _ firstOutput trace.2.2⟩
        intro heq; exact dz
    have actual := (actual_strict_record_supply model o b (reset :: extra :: rest)
      K hK hqb hbp).1.mpr actualTrace
    have appendWeight (v v' : List CuLetter) : wordWeight (v ++ v') = wordWeight v + wordWeight v' := by
      induction v with
      | nil => simp [wordWeight]
      | cons l v ih => cases l <;> simp [wordWeight, ih, Nat.add_assoc]
    have uWeight (n : ℕ) : wordWeight (List.replicate n CuLetter.u) = 6 * n := by
      induction n with
      | zero => rfl
      | succ n ih => simp [List.replicate_succ, wordWeight, ih]; omega
    have parsedWeight : wordWeight filled = 6 * a + listWeight (first :: rest) := by
      rw [parse, appendWeight, uWeight, complete_execution_word_parser.2.2.2.1]
    refine ⟨a, first, rest, parse, ?_, actual, ?_, ?_⟩
    · intro a' xs' hparse
      have hh := unique (a', xs') hparse
      exact Prod.mk.inj hh
    · simp [executionWord, reset, extra, List.append_assoc]
    · have fw : wordWeight filled = wordWeight w +
          (if w.getLast? = some CuLetter.c then 6 else 0) := by
        dsimp [filled]; split <;> simp [appendWeight, wordWeight]
      dsimp [reset, extra, listWeight] at *
      split <;> simp_all <;> omega

/-- At a fixed original variable weight, the actual eventually-empty address on
 either side determines the execution list. The fixed stem and paid anchor are
 removed from equal-length observed prefixes, without reversing block letters. -/
theorem actual_source_address_injection (j : Side) (model : Model)
    (xs ys : List Return) (hweight : listWeight xs = listWeight ys)
    (hsource : source j model xs = source j model ys) : xs = ys := by
  let encode (w : List CuLetter) : List Label :=
    (w.map (fun l => match l with | .c => C | .u => block j)).flatten
  have encodeAppend (w v : List CuLetter) : encode (w ++ v) = encode w ++ encode v := by
    simp [encode, List.map_append, List.flatten_append]
  have encodeRepC (n : ℕ) : encode (List.replicate n CuLetter.c) = repeatWord C n := by
    induction n with
    | zero => simp [encode, repeatWord]
    | succ n ih =>
      rw [List.replicate_succ]
      change _ ++ encode _ = _ ++ _
      rw [ih]
  have encodeRepU (n : ℕ) : encode (List.replicate n CuLetter.u) = repeatWord (block j) n := by
    induction n with
    | zero => simp [encode, repeatWord]
    | succ n ih =>
      rw [List.replicate_succ]
      change _ ++ encode _ = _ ++ _
      rw [ih]
  have encodeInj : Function.Injective encode := by
    intro w
    induction w with
    | nil =>
      intro v heq
      cases v with
      | nil => rfl
      | cons l v => cases l <;> cases j <;> simp [encode, block, U, V, C] at heq
    | cons l w ih =>
      intro v heq
      cases v with
      | nil => cases l <;> cases j <;> simp [encode, block, U, V, C] at heq
      | cons k v =>
        cases l <;> cases k
        · have h : encode w = encode v := by
            exact List.append_cancel_left
              (by simpa only [encode, List.map_cons, List.flatten_cons] using heq)
          exact congrArg (List.cons CuLetter.c) (ih h)
        · cases j
          · have h := congrArg (fun x : List Label => x[1]?) heq
            simp [encode, block, U, C] at h
          · have h := congrArg (fun x : List Label => x[0]?) heq
            simp [encode, block, V, C] at h
        · cases j
          · have h := congrArg (fun x : List Label => x[1]?) heq
            simp [encode, block, U, C] at h
          · have h := congrArg (fun x : List Label => x[0]?) heq
            simp [encode, block, V, C] at h
        · have h : encode w = encode v := by
            exact List.append_cancel_left
              (by simpa only [encode, List.map_cons, List.flatten_cons] using heq)
          exact congrArg (List.cons CuLetter.u) (ih h)
  have encoded (zs : List Return) : encode (executionWord zs).reverse = externalWord j zs := by
    induction zs with
    | nil => simp [encode, executionWord, externalWord]
    | cons a zs ih =>
      simp [executionWord, List.reverse_append, List.reverse_replicate, encodeAppend,
        encodeRepC, encodeRepU, ih, externalWord, List.reverse_cons, returnWord,
        List.map_append, List.flatten_append, List.append_assoc]
  have plen : (observedPrefix j model xs).length = (observedPrefix j model ys).length := by
    rw [(paired_source_reconstruction j model xs).2.2.2.2.1,
      (paired_source_reconstruction j model ys).2.2.2.2.1, hweight]
  have hpref : observedPrefix j model xs = observedPrefix j model ys := by
    apply List.ext_getElem plen
    intro p hp hq
    have h := congrFun hsource p
    simpa only [source, address, sourcePrefix, List.getElem?_append_left hp,
      List.getElem?_append_left hq, List.getElem?_eq_getElem hp,
      List.getElem?_eq_getElem hq, Option.getD_some] using h
  have ext : externalWord j xs = externalWord j ys := by
    unfold observedPrefix at hpref
    exact List.append_cancel_left (List.append_cancel_right hpref)
  have enc : encode (executionWord xs).reverse = encode (executionWord ys).reverse := by
    rw [encoded, encoded]; exact ext
  apply complete_execution_word_parser.2.2.1
  have h := encodeInj enc
  simpa only [List.reverse_reverse] using congrArg List.reverse h



end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
