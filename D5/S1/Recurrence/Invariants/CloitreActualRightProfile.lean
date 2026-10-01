/- GID: D5/S1/Recurrence/Invariants/CloitreActualRightProfile
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/CloitreActualRightProfile
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional right Fibonacci profiles for the actual Cloitre sequence. -/

import D5.S1.Recurrence.GoldenFibDivisibility
import D5.S1.Phase.SelfReference.GoldenShellRecurrence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2000

namespace D5.S1.Recurrence.Invariants.CloitreActualRightProfile

local notation "F" => Nat.fib
local notation "G" => D5.S1.Phase.SelfReference.GoldenShellRecurrence.g

private abbrev Prefix (m : ℕ) := Fin m → ℕ

private def readAt {m : ℕ} (p : Prefix m) (x : ℕ) : ℕ :=
  if h : 1 ≤ x ∧ x ≤ m then p ⟨x - 1, by omega⟩ else 0

private def next (m : ℕ) (p : Prefix m) : ℕ :=
  if m < 2 then 1 else
    let N := m + 1
    let R := readAt p
    let d := R m
    let g := ((fun x => N - R x)^[d]) m
    R g + R (N - g)

private def append {m : ℕ} (p : Prefix m) : Prefix (m + 1) :=
  fun i => if h : i.val < m then p ⟨i.val, h⟩ else next m p

private def builtPrefix : (m : ℕ) → Prefix m
  | 0 => fun i => Fin.elim0 i
  | m + 1 => append (builtPrefix m)

/-- Positive-index Cloitre sequence; zero is an exterior convention. -/
def C (n : ℕ) : ℕ := readAt (builtPrefix n) n

/-- The previously defined positive indices. -/
def D (N : ℕ) : Set ℕ := Set.Icc 1 (N - 1)

/-- The actual inner map, with fixed outer index. -/
def T (N x : ℕ) : ℕ := N - C x

/-- Actual orbit with its prescribed origin. -/
def X (N i : ℕ) : ℕ := (T N)^[i] (N - 1)

/-- Actual value-dependent iteration depth. -/
def d (N : ℕ) : ℕ := C (N - 1)

/-- The actual selected endpoint. -/
def g (N : ℕ) : ℕ := X N (d N)

/-- The right Fibonacci collar. -/
def I (q t : ℕ) : Set ℕ := Set.Icc (F (q - 1)) (F (q - 1) + t)

/-- Earliest periodic entry on the actual orbit precedes the actual depth. -/
def DepthEntry (N : ℕ) : Prop :=
  ∃ μ : ℕ, X N μ ∈ Function.periodicPts (T N) ∧
    (∀ i : ℕ, i < μ → X N i ∉ Function.periodicPts (T N)) ∧ μ ≤ d N

/-- Conditional finite foundations for the source's global bounds and depth entry. -/
structure SourceFoundations : Prop where
  ratioSeed : ∀ n : ℕ, 16384 ≤ n → n ≤ 131071 → 22877 * C n ≤ 15225 * n
  goldenBase : ∀ n : ℕ, 1 ≤ n → n ≤ 65535 →
    G n ≤ C n ∧ (C n = G n →
      (∃ j : ℕ, 2 ≤ j ∧ (n = F j ∨ n = F j + 1)) ∨
      (∃ j : ℕ, 3 ≤ j ∧ Odd j ∧ n + 1 = F j) ∨
      n = 11 ∨ n = 24 ∨ n = 25 ∨ n = 59)
  smallDepth : ∀ N : ℕ, 3 ≤ N → N ≤ 52 → DepthEntry N

/-- Full golden-bound, collar and actual-depth premise bundle. -/
structure Hyp21_1 (U : ℕ → ℕ) : Prop where
  foundations : SourceFoundations
  bounds : ∀ n : ℕ, 1 ≤ n → 1 ≤ C n ∧ G n ≤ C n ∧ C n ≤ U n ∧ U n ≤ n
  u1 : U 1 = 1
  uPiece : ∀ j n : ℕ, 3 ≤ j → F j ≤ n → n < F (j + 1) →
    U n = min (n - F (j - 2)) (F j)
  uMono : ∀ a b : ℕ, 1 ≤ a → a ≤ b → U a ≤ U b
  uStep : ∀ n : ℕ, 1 ≤ n → U n ≤ U (n + 1) ∧ U (n + 1) ≤ U n + 1
  anchors : ∀ j : ℕ, 2 ≤ j →
    U (F j) = F (j - 1) ∧ C (F j) = F (j - 1) ∧ G (F j) = F (j - 1)
  plusOne : ∀ j : ℕ, 3 ≤ j →
    G (F j + 1) = F (j - 1) + 1 ∧ C (F j + 1) = F (j - 1) + 1
  collarDomain : ∀ q t : ℕ, 6 ≤ q → I q t ⊆ D (F q + t)
  collarInvariant : ∀ q t : ℕ, 6 ≤ q → Set.MapsTo (T (F q + t)) (I q t) (I q t)
  capture : ∀ q t x : ℕ, 6 ≤ q → x ∈ D (F q + t) →
    ∃ i : ℕ, (T (F q + t))^[i] x ∈ I q t
  cyclesInside : ∀ q t x : ℕ, 6 ≤ q → x ∈ D (F q + t) →
    x ∈ Function.periodicPts (T (F q + t)) → x ∈ I q t
  depthEntry : ∀ N : ℕ, 3 ≤ N → DepthEntry N

set_option maxHeartbeats 1200000 in
-- Prefix construction and orbit agreement require nested inductions.
/-- The actual finite-prefix construction keeps every orbit in its legal domain
and satisfies its prescribed split recurrence without conditional hypotheses. -/
theorem actual_foundations :
    (∀ N i : ℕ, 3 ≤ N → X N i ∈ D N) ∧
    (∀ N : ℕ, 3 ≤ N → C N = C (g N) + C (N - g N)) := by
  have oldRead : ∀ m x, 1 ≤ x → x ≤ m →
      readAt (builtPrefix (m + 1)) x = readAt (builtPrefix m) x := by
    intro m x hx hxm
    unfold readAt
    rw [dif_pos (show 1 ≤ x ∧ x ≤ m + 1 from ⟨hx, by omega⟩),
      dif_pos (show 1 ≤ x ∧ x ≤ m from ⟨hx, hxm⟩)]
    simp only [builtPrefix, append, dif_pos (show x - 1 < m by omega)]
  have lastRead : ∀ m, readAt (builtPrefix (m + 1)) (m + 1) = next m (builtPrefix m) := by
    intro m
    simp [readAt, builtPrefix, append]
  have prefixBounds : ∀ m x, 1 ≤ x → x ≤ m →
      1 ≤ readAt (builtPrefix m) x ∧ readAt (builtPrefix m) x ≤ x := by
    intro m
    induction m with
    | zero => intro x hx hxm; omega
    | succ m ih =>
      intro x hx hxm
      by_cases hxm' : x ≤ m
      · rw [oldRead m x hx hxm']; exact ih x hx hxm'
      · have ex : x = m + 1 := by omega
        subst x
        rw [lastRead]
        by_cases hm : m < 2
        · simp [next, hm]
        · let R := readAt (builtPrefix m)
          let f := fun x => m + 1 - R x
          have inv : Set.MapsTo f (Set.Icc 1 m) (Set.Icc 1 m) := by
            intro y hy
            change 1 ≤ y ∧ y ≤ m at hy
            have hb := ih y hy.1 hy.2
            change 1 ≤ m + 1 - R y ∧ m + 1 - R y ≤ m
            change 1 ≤ R y ∧ R y ≤ y at hb
            omega
          have hi : m ∈ Set.Icc 1 m := ⟨by omega, le_rfl⟩
          have hg := inv.iterate (R m) hi
          change 1 ≤ f^[R m] m ∧ f^[R m] m ≤ m at hg
          have hc : m + 1 - f^[R m] m ∈ Set.Icc 1 m := by
            constructor <;> omega
          have hb1 := ih (f^[R m] m) hg.1 hg.2
          have hb2 := ih (m + 1 - f^[R m] m) hc.1 hc.2
          simp only [next, if_neg hm]
          change 1 ≤ R (f^[R m] m) + R (m + 1 - f^[R m] m) ∧
            R (f^[R m] m) + R (m + 1 - f^[R m] m) ≤ m + 1
          change 1 ≤ R (f^[R m] m) ∧ R (f^[R m] m) ≤ f^[R m] m at hb1
          change 1 ≤ R (m + 1 - f^[R m] m) ∧
            R (m + 1 - f^[R m] m) ≤ m + 1 - f^[R m] m at hb2
          omega
  have agreement : ∀ m x, 1 ≤ x → x ≤ m → readAt (builtPrefix m) x = C x := by
    intro m
    induction m with
    | zero => intro x hx hxm; omega
    | succ m ih =>
      intro x hx hxm
      by_cases hxm' : x ≤ m
      · rw [oldRead m x hx hxm']; exact ih x hx hxm'
      · have ex : x = m + 1 := by omega
        subst x
        rfl
  have actualBounds : ∀ x, 1 ≤ x → 1 ≤ C x ∧ C x ≤ x := by
    intro x hx
    exact prefixBounds x x hx le_rfl
  have domainInv : ∀ N, 3 ≤ N → Set.MapsTo (T N) (D N) (D N) := by
    intro N hN x hx
    have hb := actualBounds x hx.1
    change 1 ≤ N - C x ∧ N - C x ≤ N - 1
    change 1 ≤ x ∧ x ≤ N - 1 at hx
    omega
  have orbitDomain : ∀ N i, 3 ≤ N → X N i ∈ D N := by
    intro N i hN
    exact (domainInv N hN).iterate i ⟨by omega, le_rfl⟩
  have actualRecurrence : ∀ N, 3 ≤ N → C N = C (g N) + C (N - g N) := by
    intro N hN
    let m := N - 1
    have hNm : N = m + 1 := by dsimp [m]; omega
    let R := readAt (builtPrefix m)
    let f := fun x => N - R x
    have inv : Set.MapsTo f (D N) (D N) := by
      intro x hx
      have hb := prefixBounds m x hx.1 hx.2
      change 1 ≤ N - R x ∧ N - R x ≤ N - 1
      change 1 ≤ R x ∧ R x ≤ x at hb
      change 1 ≤ x ∧ x ≤ N - 1 at hx
      omega
    have guard : ∀ i, f^[i] m ∈ D N := by
      intro i
      exact inv.iterate i ⟨by dsimp [m]; omega, le_rfl⟩
    have orbitEq : ∀ i, f^[i] m = X N i := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [Function.iterate_succ_apply']
        change N - R (f^[i] m) = (T N)^[i + 1] (N - 1)
        rw [Function.iterate_succ_apply']
        have hg := guard i
        have he := agreement m (f^[i] m) hg.1 hg.2
        change R (f^[i] m) = C (f^[i] m) at he
        rw [he, ih]
        rfl
    have depthEq : R m = d N := agreement m m (by dsimp [m]; omega) le_rfl
    have selEq : f^[R m] m = g N := by rw [depthEq, orbitEq]; rfl
    have hg := guard (R m)
    have hc : N - f^[R m] m ∈ D N := by
      change 1 ≤ N - f^[R m] m ∧ N - f^[R m] m ≤ N - 1
      change 1 ≤ f^[R m] m ∧ f^[R m] m ≤ N - 1 at hg
      omega
    have e1 := agreement m (f^[R m] m) hg.1 hg.2
    have e2 := agreement m (N - f^[R m] m) hc.1 hc.2
    change R (f^[R m] m) = C (f^[R m] m) at e1
    change R (N - f^[R m] m) = C (N - f^[R m] m) at e2
    conv_lhs => rw [hNm]; unfold C; rw [lastRead]
    simp only [next, if_neg (show ¬m < 2 by dsimp [m]; omega)]
    rw [← hNm]
    change R (f^[R m] m) + R (N - f^[R m] m) = _
    rw [e1, e2, selEq]
  exact ⟨orbitDomain, actualRecurrence⟩

set_option maxHeartbeats 1200000 in
-- Nested prefix, offset and orbit inductions share substantial arithmetic side conditions.
/-- Every fixed nonnegative offset has the complete right Fibonacci profile. -/
theorem full21_3 (U : ℕ → ℕ) (h : Hyp21_1 U) :
    ∀ t k : ℕ, 6 * t + 6 ≤ k → C (F k + t) = F (k - 1) + t := by
  obtain ⟨orbitDomain, actualRecurrence⟩ := actual_foundations
  have goldenMono : Monotone G := by
    intro a b hab
    unfold D5.S1.Phase.SelfReference.GoldenShellRecurrence.g
    apply Nat.floor_mono
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast Nat.add_le_add_right hab 1
    · exact le_of_lt (inv_pos.mpr Real.goldenRatio_pos)
  have uLift : ∀ n v, 1 ≤ n → U (n + v) ≤ U n + v := by
    intro n v hn
    induction v with
    | zero => simp
    | succ v ih =>
      have hs := (h.uStep (n + v) (by omega)).2
      simpa only [Nat.add_assoc] using (show U (n + v + 1) ≤ U n + (v + 1) by omega)
  have profileBounds : ∀ j v, 6 ≤ j → 1 ≤ v →
      F (j - 1) + 1 ≤ C (F j + v) ∧ C (F j + v) ≤ F (j - 1) + v := by
    intro j v hj hv
    have hf : 1 ≤ F j := by have := Nat.le_fib_add_one j; omega
    have hb := h.bounds (F j + v) (by omega)
    have hu := uLift (F j) v hf
    rw [(h.anchors j (by omega)).1] at hu
    have hl := goldenMono (show F j + 1 ≤ F j + v by omega)
    rw [(h.plusOne j (by omega)).1] at hl
    omega
  have selectedPeriodic : ∀ N, 3 ≤ N → g N ∈ Function.periodicPts (T N) := by
    intro N hN
    obtain ⟨μ, hp, _, hμ⟩ := h.depthEntry N hN
    obtain ⟨r, hr, hpr⟩ := hp
    refine ⟨r, hr, ?_⟩
    have ht := hpr.apply_iterate (d N - μ)
    have he : (T N)^[d N - μ] (X N μ) = g N := by
      unfold X g
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rwa [he] at ht
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro k hk
    by_cases ht : t = 0
    · subst t
      simpa using (h.anchors k (by omega)).2.1
    have htpos : 1 ≤ t := by omega
    have small : ∀ u j, u < t → 6 * t ≤ j → C (F j + u) = F (j - 1) + u := by
      intro u j hu hj
      exact ih u hu j (by omega)
    have coupled : ∀ q, 6 * t + 2 ≤ q → C (F q + t) < F (q - 1) + t →
        C (F (q - 2) + t) < F (q - 3) + t ∧ (F (q - 1) + t - 1) % 2 = 1 := by
      intro q hq hdef
      let A := F (q - 1)
      let B := F (q - 2)
      let E := F (q - 3)
      let N := F q + t
      have hq6 : 6 ≤ q := by omega
      have hA : 1 ≤ A := by have := Nat.le_fib_add_one (q - 1); dsimp [A]; omega
      have hB : t < B := by have := Nat.le_fib_add_one (q - 2); dsimp [B]; omega
      have hB2 : 1 < B := by omega
      have fAB : F q = A + B := by
        have ff := Nat.fib_add_two (n := q - 2)
        rw [show q - 2 + 2 = q by omega, show q - 2 + 1 = q - 1 by omega] at ff
        dsimp [A, B]
        omega
      have fBE : A = B + E := by
        have ff := Nat.fib_add_two (n := q - 3)
        rw [show q - 3 + 2 = q - 1 by omega, show q - 3 + 1 = q - 2 by omega] at ff
        dsimp [A, B, E]
        omega
      have nEq : N = A + B + t := by dsimp [N]; omega
      have hN : 3 ≤ N := by omega
      have hAanchor : C A = B := by
        have hh := (h.anchors (q - 1) (by omega)).2.1
        simpa only [Nat.sub_sub] using hh
      have hBanchor : C B = E := by
        have hh := (h.anchors (q - 2) (by omega)).2.1
        simpa only [Nat.sub_sub] using hh
      have hbA := profileBounds (q - 1) t (by omega) htpos
      change B + 1 ≤ C (A + t) ∧ C (A + t) ≤ B + t at hbA
      let e := B + t - C (A + t)
      have he : e < t := by dsimp [e]; omega
      have endMap : T N (A + t) = A + e := by unfold T; dsimp [e]; omega
      have reflect : ∀ u, u < t → T N (A + u) = A + t - u := by
        intro u hu
        have hh := small u (q - 1) hu (by omega)
        change C (A + u) = B + u at hh
        unfold T
        rw [hh]
        omega
      have interior : ∀ u, 0 < u → u < t → Function.IsPeriodicPt (T N) 2 (A + u) := by
        intro u hu hut
        change T N (T N (A + u)) = A + u
        rw [reflect u hut]
        have heq : A + t - u = A + (t - u) := by omega
        rw [heq, reflect (t - u) (by omega)]
        omega
      have hp := selectedPeriodic N hN
      have hgD := orbitDomain N (d N) hN
      change g N ∈ D N at hgD
      have hgI := h.cyclesInside q t (g N) hq6 hgD hp
      change A ≤ g N ∧ g N ≤ A + t at hgI
      let s := g N - A
      have hs : s ≤ t := by dsimp [s]; omega
      have gs : g N = A + s := by dsimp [s]; omega
      have cs : N - g N = B + (t - s) := by omega
      have splitEq := actualRecurrence N hN
      rw [cs, gs] at splitEq
      have innerZero : 0 < s → s < t → C N = A + t := by
        intro hs0 hst
        have hh1 := small s (q - 1) hst (by omega)
        have hh2 := small (t - s) (q - 2) (by omega) (by omega)
        change C (A + s) = B + s at hh1
        change C (B + (t - s)) = E + (t - s) at hh2
        rw [hh1, hh2] at splitEq
        omega
      have eZero : e = 0 := by
        by_contra henz
        have he0 : 0 < e := by omega
        have notA : A ∉ Function.periodicPts (T N) := by
          intro hpA
          have step2 : (T N)^[2] A = A + e := by
            change T N (T N (A + 0)) = A + e
            rw [reflect 0 htpos]
            simpa using endMap
          have hp2 : Function.IsPeriodicPt (T N) 2 ((T N)^[2] A) := by
            rw [step2]
            exact interior e he0 he
          have back := Function.isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate hpA hp2
          have : A + e = A := step2.symm.trans back.eq
          omega
        have notUpper : A + t ∉ Function.periodicPts (T N) := by
          intro hpU
          have hp2 : Function.IsPeriodicPt (T N) 2 ((T N)^[1] (A + t)) := by
            change Function.IsPeriodicPt (T N) 2 (T N (A + t))
            rw [endMap]
            exact interior e he0 he
          have back := Function.isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate hpU hp2
          have eq2 : (T N)^[2] (A + t) = A + t - e := by
            change T N (T N (A + t)) = _
            rw [endMap, reflect e he]
          have := eq2.symm.trans back.eq
          omega
        have hs0 : 0 < s := by
          by_contra hh
          have es : s = 0 := by omega
          apply notA
          simpa [gs, es] using hp
        have hst : s < t := by
          by_contra hh
          have es : s = t := by omega
          apply notUpper
          simpa [gs, es] using hp
        have hz := innerZero hs0 hst
        change C N < A + t at hdef
        omega
      have upperValue : C (A + t) = B + t := by dsimp [e] at eZero; omega
      have allReflect : ∀ u, u ≤ t → T N (A + u) = A + t - u := by
        intro u hu
        by_cases hut : u < t
        · exact reflect u hut
        · have eu : u = t := by omega
          subst u
          rw [endMap, eZero]
          omega
      have sZero : s = 0 := by
        by_contra hsn
        have hs0 : 0 < s := by omega
        by_cases hst : s < t
        · have hz := innerZero hs0 hst
          change C N < A + t at hdef
          omega
        · have es : s = t := by omega
          rw [es, Nat.sub_self, Nat.add_zero, upperValue, hBanchor] at splitEq
          change C N < A + t at hdef
          omega
      have selectedA : g N = A := by omega
      have lowerDeficit : C (B + t) < E + t := by
        rw [sZero, Nat.add_zero, Nat.sub_zero, hAanchor] at splitEq
        change C N < A + t at hdef
        omega
      have leftMap : ∀ x, x ∈ D N → x ≤ A → A + t ≤ T N x := by
        intro x hx hxa
        have hb := (h.bounds x hx.1).2.2.1
        have hu := h.uMono x A hx.1 hxa
        have ha := (h.anchors (q - 1) (by omega)).1
        change U A = B at ha
        unfold T
        omega
      have rightMap : ∀ x, x ∈ D N → A + t < x → T N x < A + t := by
        intro x hx hax
        have hb := (h.bounds x hx.1).2.1
        have hm := goldenMono (show A + 1 ≤ x by omega)
        have ha := (h.plusOne (q - 1) (by omega)).1
        change G (A + 1) = B + 1 at ha
        unfold T
        omega
      let P := fun (i x : ℕ) =>
        (i % 2 = 0 ∧ A + t ≤ x) ∨ (i % 2 = 1 ∧ x ≤ A) ∨ (A < x ∧ x < A + t)
      have phase : ∀ i, P i (X N i) := by
        intro i
        induction i with
        | zero =>
          left
          change 0 % 2 = 0 ∧ A + t ≤ N - 1
          omega
        | succ i hi =>
          have hx := orbitDomain N i hN
          have step : X N (i + 1) = T N (X N i) := Function.iterate_succ_apply' (T N) i (N - 1)
          change P (i + 1) (X N (i + 1))
          rw [step]
          rcases hi with ⟨hpar, hxhi⟩ | ⟨hpar, hxlo⟩ | ⟨hxlo, hxhi⟩
          · by_cases hxe : X N i = A + t
            · have hm := allReflect t le_rfl
              rw [hxe, hm]
              right; left
              constructor <;> omega
            · have hm := rightMap (X N i) hx (by omega)
              by_cases hlow : T N (X N i) ≤ A
              · right; left
                constructor <;> omega
              · right; right
                constructor <;> omega
          · have hm := leftMap (X N i) hx hxlo
            left
            constructor <;> omega
          · have hex : X N i = A + (X N i - A) := by omega
            have hm := allReflect (X N i - A) (by omega)
            rw [hex, hm]
            right; right
            constructor <;> omega
      have depthOdd : d N % 2 = 1 := by
        have hh := phase (d N)
        change P (d N) (g N) at hh
        rw [selectedA] at hh
        dsimp [P] at hh
        rcases hh with ⟨_, hb⟩ | ⟨hp, _⟩ | ⟨hb, _⟩ <;> omega
      have depthValue : d N = A + t - 1 := by
        have hh := small (t - 1) q (by omega) (by omega)
        change C (F q + (t - 1)) = A + (t - 1) at hh
        unfold d
        have heq : N - 1 = F q + (t - 1) := by dsimp [N]; omega
        rw [heq, hh]
        omega
      constructor
      · exact lowerDeficit
      · rwa [depthValue] at depthOdd
    have hb := profileBounds k t (by omega) htpos
    apply Nat.le_antisymm hb.2
    by_contra hn
    have hd : C (F k + t) < F (k - 1) + t := by omega
    have h1 := coupled k (by omega) hd
    have h2 := coupled (k - 2) (by omega) h1.1
    have h3 := coupled (k - 4) (by omega) (by
      simpa only [Nat.sub_sub] using h2.1)
    have par1 : (F (k - 1) + t - 1) % 2 = 1 := h1.2
    have par2 : (F (k - 3) + t - 1) % 2 = 1 := by
      simpa only [Nat.sub_sub] using h2.2
    have par3 : (F (k - 5) + t - 1) % 2 = 1 := by
      simpa only [Nat.sub_sub] using h3.2
    have parity : ∀ j, F j % 2 = 0 ↔ j % 3 = 0 := by
      intro j
      have hh := D5.S1.Recurrence.GoldenFibDivisibility.fib_dvd_iff 3 j (by omega)
      norm_num [Nat.dvd_iff_mod_eq_zero] at hh
      exact hh
    have p1 := parity (k - 1)
    have p2 := parity (k - 3)
    have p3 := parity (k - 5)
    omega

end D5.S1.Recurrence.Invariants.CloitreActualRightProfile
