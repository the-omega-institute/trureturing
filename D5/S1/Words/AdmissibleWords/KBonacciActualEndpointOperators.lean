/- GID: D5/S1/Words/AdmissibleWords/KBonacciActualEndpointOperators
   generality: I
   mirror-B: D5/B/S1/Words/AdmissibleWords/KBonacciActualEndpointOperators
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Actual Boolean words determine endpoint operator families and their exact counts. -/

import D5.S0.Automata.TypedPartialDFAOOverBase
import D5.S0.Tower.DBonacci.Substitution
import Mathlib.Tactic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
noncomputable section

namespace D5.S1.Words.AdmissibleWords.KBonacciActualEndpointOperators

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Tower.DBonacci.Names
open scoped BigOperators

/-- Actual tail runs classify the one-window family, its positive generated semigroup,
and its empty-inclusive monoid, with faithful absorbing-rejection transfers. -/
theorem actual_endpoint_operators {K : Type*} [Field K] (k : ℕ) (hk : 2 ≤ k) :
    letI : DecidableEq K := Classical.decEq K
    let z : Fin k := ⟨0, by omega⟩
    let base : PartialDFA Bool (Fin k) :=
      { start := z
        step := fun s b => if b then
          if h : s.val + 1 < k then some ⟨s.val + 1, h⟩ else none
          else some z }
    let run := base.evalFrom
    let leading := fun w : List Bool => (w.takeWhile id).length
    let trailing := fun w : List Bool => (w.reverse.takeWhile id).length
    let live : List Bool → Matrix (Fin k) (Fin k) K := fun w =>
      (fun i s : Fin k => if run s w = some i then (1 : K) else 0)
    let endpoint : Fin k → Fin k → Matrix (Fin k) (Fin k) K := fun p t =>
      (fun i s : Fin k => if i = t ∧ s.val + p.val < k then (1 : K) else 0)
    let window := fun p t : Fin k => List.replicate p.val true ++
      List.replicate (k + 1 - p.val - t.val) false ++ List.replicate t.val true
    let domain := (Finset.univ : Finset (Fin k × Fin k)).filter
      (fun q => q.1.val + q.2.val ≤ k)
    let one := insert (0 : Matrix (Fin k) (Fin k) K)
      (domain.image (fun q => endpoint q.1 q.2))
    let positive := insert (0 : Matrix (Fin k) (Fin k) K)
      (Finset.univ.image (fun q : Fin k × Fin k => endpoint q.1 q.2))
    let monoid := insert (1 : Matrix (Fin k) (Fin k) K) positive
    let total : List Bool → Matrix (Option (Fin k)) (Option (Fin k)) K := fun w i s =>
      if s.bind (fun a => run a w) = i then 1 else 0
    let lift : Matrix (Fin k) (Fin k) K → Matrix (Option (Fin k)) (Option (Fin k)) K :=
      fun A i s => match i, s with
        | some i, some s => A i s
        | some _, none => 0
        | none, some s => 1 - ∑ i, A i s
        | none, none => 1
    (∀ n (w : Fin n → Bool) (s : Fin k),
      (run s (List.ofFn w)).isSome = runAdmissible (k - 1) (k - 1 - s.val) n w) ∧
    (∀ n (w : Fin n → Bool), DBonacciAdmissible k n w ↔ run z (List.ofFn w) ≠ none) ∧
    (∀ n (w : Fin n → Bool), (List.ofFn w).length = n ∧
      ∀ i : Fin n, (List.ofFn w)[i.val]'(by simpa using i.isLt) = w i) ∧
    (∀ w : List Bool, (List.ofFn w.get).length = w.length ∧ List.ofFn w.get = w) ∧
    (∀ w : List Bool, false ∈ w → run z w ≠ none →
      ∃ p t : Fin k, leading w = p.val ∧ trailing w = t.val ∧
        p.val + t.val < w.length ∧
        (∀ s : Fin k, run s w = if s.val + p.val < k then some t else none) ∧
        live w = endpoint p t) ∧
    (∀ w : List Bool, run z w = none → ∀ s, run s w = none) ∧
    (∀ w : List Bool, k ≤ w.length → run z w ≠ none → false ∈ w) ∧
    (∀ u v : List Bool, live (u ++ v) = live v * live u) ∧
    (∀ p₁ t₁ p₂ t₂ : Fin k, endpoint p₂ t₂ * endpoint p₁ t₁ =
      if t₁.val + p₂.val < k then endpoint p₁ t₂ else 0) ∧
    (∀ (u v : List Bool) (p₁ t₁ p₂ t₂ : Fin k),
      false ∈ u → false ∈ v → run z u ≠ none → run z v ≠ none →
      leading u = p₁.val → trailing u = t₁.val →
      leading v = p₂.val → trailing v = t₂.val →
      (live (u ++ v) = if t₁.val + p₂.val < k then endpoint p₁ t₂ else 0) ∧
      (∀ s, run s (u ++ v) =
        if t₁.val + p₂.val < k ∧ s.val + p₁.val < k then some t₂ else none)) ∧
    (∀ p t : Fin k, p.val + t.val ≤ k →
      (window p t).length = k + 1 ∧ leading (window p t) = p.val ∧
      trailing (window p t) = t.val ∧ run z (window p t) = some t ∧
      live (window p t) = endpoint p t) ∧
    (∀ p t : Fin k,
      (∃ w : List Bool, w.length = k + 1 ∧ run z w ≠ none ∧
        leading w = p.val ∧ trailing w = t.val) ↔ p.val + t.val ≤ k) ∧
    (∀ p t : Fin k, (window p z ++ window z t).length = 2 * (k + 1) ∧
      live (window p z ++ window z t) = endpoint p t) ∧
    run z (List.replicate (k + 1) true) = none ∧
    live (List.replicate (k + 1) true) = 0 ∧
    (∀ p t : Fin k, endpoint p t ≠ 0 ∧ (endpoint p t).rank ≤ 1) ∧
    Function.Injective (fun q : Fin k × Fin k => endpoint q.1 q.2) ∧
    (∀ A : Matrix (Fin k) (Fin k) K,
      (∃ w : List Bool, w.length = k + 1 ∧ live w = A) ↔ A ∈ one) ∧
    (∀ A : Matrix (Fin k) (Fin k) K,
      (∃ r : ℕ, 0 < r ∧ ∃ w : List Bool, w.length = r * (k + 1) ∧ live w = A) ↔
        A ∈ positive) ∧
    (∀ A : Matrix (Fin k) (Fin k) K,
      (∃ r : ℕ, ∃ w : List Bool, w.length = r * (k + 1) ∧ live w = A) ↔ A ∈ monoid) ∧
    (∀ A ∈ positive, ∀ B ∈ positive, B * A ∈ positive) ∧
    (∀ A ∈ monoid, ∀ B ∈ monoid, B * A ∈ monoid) ∧
    (∀ A ∈ positive, A.rank ≤ 1 ∧ A ≠ 1) ∧
    (3 ≤ k →
      let top : Fin k := ⟨k - 1, by omega⟩
      live (window top z) ∈ one ∧ live (window z top) ∈ one ∧
        live (window top z ++ window z top) ∉ one) ∧
    (k = 3 →
      let top : Fin k := ⟨k - 1, by omega⟩
      window top z = [true, true, false, false] ∧
        window z top = [false, false, true, true]) ∧
    domain.card = (k ^ 2 + 3 * k - 2) / 2 ∧
    (domain.image (fun q => endpoint q.1 q.2)).card = (k ^ 2 + 3 * k - 2) / 2 ∧
    one.card = (k ^ 2 + 3 * k - 2) / 2 + 1 ∧
    positive.card = k ^ 2 + 1 ∧ monoid.card = k ^ 2 + 2 ∧
    Function.Injective lift ∧ lift 1 = 1 ∧
    (∀ A B, lift (B * A) = lift B * lift A) ∧
    (∀ w, total w = lift (live w)) ∧
    (∀ w, total w none none = 1 ∧ ∀ s : Fin k, total w (some s) none = 0) ∧
    (∀ u v, total (u ++ v) = total v * total u) ∧
    lift 0 = (fun i _ => if i = none then (1 : K) else 0) ∧ lift 0 ≠ 0 ∧
    (∀ A : Matrix (Option (Fin k)) (Option (Fin k)) K,
      (∃ w : List Bool, w.length = k + 1 ∧ total w = A) ↔ A ∈ one.image lift) ∧
    (∀ A : Matrix (Option (Fin k)) (Option (Fin k)) K,
      (∃ r : ℕ, 0 < r ∧ ∃ w : List Bool, w.length = r * (k + 1) ∧ total w = A) ↔
        A ∈ positive.image lift) ∧
    (∀ A : Matrix (Option (Fin k)) (Option (Fin k)) K,
      (∃ r : ℕ, ∃ w : List Bool, w.length = r * (k + 1) ∧ total w = A) ↔
        A ∈ monoid.image lift) ∧
    (one.image lift).card = (k ^ 2 + 3 * k - 2) / 2 + 1 ∧
    (positive.image lift).card = k ^ 2 + 1 ∧ (monoid.image lift).card = k ^ 2 + 2 ∧
    (∀ A ∈ positive.image lift, ∀ B ∈ positive.image lift, B * A ∈ positive.image lift) ∧
    (∀ A ∈ monoid.image lift, ∀ B ∈ monoid.image lift, B * A ∈ monoid.image lift) ∧
    (∀ n (w : Fin n → Bool), DBonacciAdmissible k n w →
      DBonacciAdmissible k (n + 1) (Fin.snoc w false) ∧
      (List.ofFn (Fin.snoc w false)).length = n + 1 ∧
      run z (List.ofFn (Fin.snoc w false)) = some z) ∧
    (3 ≤ k →
      let top : Fin k := ⟨k - 1, by omega⟩
      total (window top z) ∈ one.image lift ∧ total (window z top) ∈ one.image lift ∧
        total (window top z ++ window z top) ∉ one.image lift) := by
  classical
  dsimp only
  let z : Fin k := ⟨0, by omega⟩
  let base : PartialDFA Bool (Fin k) :=
    { start := z
      step := fun s b => if b then
        if h : s.val + 1 < k then some ⟨s.val + 1, h⟩ else none
        else some z }
  let run := base.evalFrom
  let leading := fun w : List Bool => (w.takeWhile id).length
  let trailing := fun w : List Bool => (w.reverse.takeWhile id).length
  let live : List Bool → Matrix (Fin k) (Fin k) K := fun w =>
    (fun i s : Fin k => if run s w = some i then (1 : K) else 0)
  let endpoint : Fin k → Fin k → Matrix (Fin k) (Fin k) K := fun p t =>
    (fun i s : Fin k => if i = t ∧ s.val + p.val < k then (1 : K) else 0)
  let window := fun p t : Fin k => List.replicate p.val true ++
    List.replicate (k + 1 - p.val - t.val) false ++ List.replicate t.val true
  let domain := (Finset.univ : Finset (Fin k × Fin k)).filter
    (fun q => q.1.val + q.2.val ≤ k)
  let one := insert (0 : Matrix (Fin k) (Fin k) K)
    (domain.image (fun q => endpoint q.1 q.2))
  let positive := insert (0 : Matrix (Fin k) (Fin k) K)
    (Finset.univ.image (fun q : Fin k × Fin k => endpoint q.1 q.2))
  let monoid := insert (1 : Matrix (Fin k) (Fin k) K) positive
  let total : List Bool → Matrix (Option (Fin k)) (Option (Fin k)) K := fun w i s =>
    if s.bind (fun a => run a w) = i then 1 else 0
  let lift : Matrix (Fin k) (Fin k) K → Matrix (Option (Fin k)) (Option (Fin k)) K :=
    fun A i s => match i, s with
      | some i, some s => A i s
      | some _, none => 0
      | none, some s => 1 - ∑ i, A i s
      | none, none => 1
  have hnil (s : Fin k) : run s [] = some s := rfl
  have hfalse (s : Fin k) (w : List Bool) : run s (false :: w) = run z w := rfl
  have htrue (s : Fin k) (w : List Bool) : run s (true :: w) =
      if h : s.val + 1 < k then run ⟨s.val + 1, h⟩ w else none := by
    by_cases hs : s.val + 1 < k <;>
      simp [run, PartialDFA.evalFrom, runTransition, base, hs]
  have happ (s : Fin k) (u v : List Bool) : run s (u ++ v) =
      (run s u).bind (fun t => run t v) := base.evalFrom_append s u v
  have hones : ∀ (n : ℕ) (s : Fin k), run s (List.replicate n true) =
      if h : s.val + n < k then some ⟨s.val + n, h⟩ else none := by
    intro n
    induction n with
    | zero => intro s; simp [hnil, s.isLt]
    | succ n ih =>
      intro s
      rw [List.replicate_succ, htrue]
      by_cases hs : s.val + 1 < k
      · rw [dif_pos hs, ih]
        by_cases ht : s.val + (n + 1) < k
        · have hh : s.val + 1 + n < k := by omega
          simp only [Fin.val_mk, dif_pos hh, dif_pos ht, Option.some.injEq, Fin.mk.injEq]
          omega
        · have hh : ¬s.val + 1 + n < k := by omega
          simp only [Fin.val_mk, dif_neg hh, dif_neg ht]
      · have hh : ¬s.val + (n + 1) < k := by omega
        rw [dif_neg hs, dif_neg hh]
  have hscan : ∀ n (w : Fin n → Bool) (s : Fin k),
      (run s (List.ofFn w)).isSome = runAdmissible (k - 1) (k - 1 - s.val) n w := by
    intro n
    induction n with
    | zero => intro w s; rfl
    | succ n ih =>
      intro w s
      rw [List.ofFn_succ]
      cases hb : w 0 with
      | false =>
        rw [hfalse, ih]
        cases hf : k - 1 - s.val <;> simp [runAdmissible, hb, z] <;> rfl
      | true =>
        rw [htrue]
        by_cases hs : s.val + 1 < k
        · rw [dif_pos hs, ih]
          obtain ⟨f, hf⟩ : ∃ f, k - 1 - s.val = f + 1 := by
            exact ⟨k - 1 - s.val - 1, by omega⟩
          simp only [Fin.val_mk, hf, runAdmissible, hb, ↓reduceIte]
          congr 1
          omega
        · rw [dif_neg hs]
          have hf : k - 1 - s.val = 0 := by have := s.isLt; omega
          simp [hf, runAdmissible, hb]
  have hsplit : ∀ w : List Bool, false ∈ w →
      ∃ p v, w = List.replicate p true ++ false :: v ∧ leading w = p := by
    intro w
    induction w with
    | nil => simp
    | cons b w ih =>
      cases b with
      | false => intro _; exact ⟨0, w, by simp [leading]⟩
      | true =>
        intro hw
        obtain ⟨p, v, he, hp⟩ := ih (by simpa using hw)
        refine ⟨p + 1, v, ?_, ?_⟩
        · simp [List.replicate_succ, he]
        · simp [leading] at hp ⊢; omega
  have hlegalScan (n : ℕ) (w : Fin n → Bool) :
      DBonacciAdmissible k n w ↔ run z (List.ofFn w) ≠ none := by
    cases k with
    | zero => omega
    | succ d =>
      have he : (run z (List.ofFn w)).isSome = runAdmissible d d n w := by
        simpa [z] using hscan n w z
      change runAdmissible d d n w = true ↔ _
      rw [← he]
      cases run z (List.ofFn w) <;> simp
  have htakeFalse : ∀ (v u : List Bool),
      (v ++ false :: u).takeWhile id = v.takeWhile id := by
    intro v
    induction v with
    | nil => intro u; simp
    | cons b v ih => cases b <;> intro u <;> simp [ih]
  have hnormal : ∀ w : List Bool, false ∈ w → run z w ≠ none →
      ∃ p t : Fin k, leading w = p.val ∧ trailing w = t.val ∧
        p.val + t.val < w.length ∧
        (∀ s : Fin k, run s w = if s.val + p.val < k then some t else none) ∧
        live w = endpoint p t := by
    intro w hw hlegal
    obtain ⟨p, v, he, hp⟩ := hsplit w hw
    have hpbound : p < k := by
      by_contra h
      apply hlegal
      rw [he, happ, hones]
      simp [z, Nat.not_lt.mpr (Nat.le_of_not_gt h)]
    obtain ⟨t, u, hr, ht⟩ := hsplit w.reverse (by simpa using hw)
    have hsuffix : w = (u.reverse ++ [false]) ++ List.replicate t true := by
      have h := congrArg List.reverse hr
      simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using h
    have htbound : t < k := by
      by_contra h
      apply hlegal
      rw [hsuffix, happ, happ]
      cases hpre : run z u.reverse <;>
        simp [hpre, hfalse, hnil, hones, z, Nat.not_lt.mpr (Nat.le_of_not_gt h)]
    let tf : Fin k := ⟨t, htbound⟩
    have hterminal : run z w = some tf := by
      rw [hsuffix, happ, happ]
      cases hpre : run z u.reverse with
      | none =>
        exfalso
        apply hlegal
        rw [hsuffix, happ, happ, hpre]
        rfl
      | some a => simp [hfalse, hnil, hones, z, htbound, tf]
    have hbody : run z v = some tf := by
      have h := hterminal
      rw [he, happ, hones] at h
      simpa [z, hpbound, hfalse] using h
    have hall (s : Fin k) : run s w = if s.val + p < k then some tf else none := by
      rw [he, happ, hones]
      split_ifs <;> simp [hfalse, hbody]
    have hlen : p + t < w.length := by
      have htrail : trailing w = (v.reverse.takeWhile id).length := by
        rw [he]
        simp only [trailing, List.reverse_append, List.reverse_cons, List.reverse_replicate]
        rw [List.append_assoc]
        exact congrArg List.length (htakeFalse v.reverse (List.replicate p true))
      have hle := (List.takeWhile_sublist (l := v.reverse) id).length_le
      have hl := congrArg List.length he
      simp only [List.length_append, List.length_replicate, List.length_cons] at hl
      simp only [List.length_reverse] at hle
      change trailing w = t at ht
      omega
    refine ⟨⟨p, hpbound⟩, tf, hp, ht, hlen, hall, ?_⟩
    funext i s
    dsimp only [live, endpoint]
    rw [hall]
    by_cases hs : s.val + p < k
    · simp [hs, eq_comm]
    · simp [hs]
  have hallones (w : List Bool) (hw : false ∉ w) : w = List.replicate w.length true := by
    apply List.eq_replicate_length.mpr
    intro b hb
    cases b with
    | false => exact False.elim (hw hb)
    | true => rfl
  have hbad (w : List Bool) (hw : run z w = none) (s : Fin k) : run s w = none := by
    by_cases hz : false ∈ w
    · obtain ⟨p, v, he, _⟩ := hsplit w hz
      rw [he, happ, hones]
      split_ifs with hs
      · have hp : p < k := by omega
        have hb := hw
        rw [he, happ, hones] at hb
        have hb' : run z v = none := by simpa [z, hp, hfalse] using hb
        simpa [hfalse] using hb'
      · rfl
    · have he := hallones w hz
      have hn : ¬w.length < k := by
        intro hn
        rw [he, hones] at hw
        simp [z, hn] at hw
      rw [he, hones, dif_neg (by omega)]
  have hzero (w : List Bool) (hw : run z w = none) : live w = 0 := by
    funext i s
    simp [live, hbad w hw s]
  have hmul (u v : List Bool) : live (u ++ v) = live v * live u := by
    funext i s
    rw [Matrix.mul_apply]
    cases hr : run s u with
    | none => simp [live, happ, hr]
    | some t =>
      rw [Finset.sum_eq_single t]
      · simp [live, happ, hr]
      · intro j _ hj
        simp [live, hr, Ne.symm hj]
      · simp
  have hendpointmul (p₁ t₁ p₂ t₂ : Fin k) : endpoint p₂ t₂ * endpoint p₁ t₁ =
      if t₁.val + p₂.val < k then endpoint p₁ t₂ else 0 := by
    funext i s
    rw [Matrix.mul_apply, Finset.sum_eq_single t₁]
    · by_cases h₁ : s.val + p₁.val < k <;> by_cases h₂ : t₁.val + p₂.val < k <;>
        by_cases hi : i = t₂ <;> simp [endpoint, h₁, h₂, hi]
    · intro j _ hj
      simp [endpoint, hj]
    · simp
  have hcompose (u v : List Bool) (p₁ t₁ p₂ t₂ : Fin k)
      (hu : false ∈ u) (hv : false ∈ v) (hlu : run z u ≠ none) (hlv : run z v ≠ none)
      (hpu : leading u = p₁.val) (htu : trailing u = t₁.val)
      (hpv : leading v = p₂.val) (htv : trailing v = t₂.val) :
      (live (u ++ v) = if t₁.val + p₂.val < k then endpoint p₁ t₂ else 0) ∧
      (∀ s, run s (u ++ v) =
        if t₁.val + p₂.val < k ∧ s.val + p₁.val < k then some t₂ else none) := by
    obtain ⟨p, t, hp, ht, _, hr, heU⟩ := hnormal u hu hlu
    have he₁ : p = p₁ := Fin.ext (hp.symm.trans hpu)
    have he₂ : t = t₁ := Fin.ext (ht.symm.trans htu)
    subst p; subst t
    obtain ⟨p, t, hp, ht, _, hs, heV⟩ := hnormal v hv hlv
    have he₁ : p = p₂ := Fin.ext (hp.symm.trans hpv)
    have he₂ : t = t₂ := Fin.ext (ht.symm.trans htv)
    subst p; subst t
    constructor
    · rw [hmul, heV, heU, hendpointmul]
    · intro s
      by_cases h₁ : s.val + p₁.val < k <;> by_cases h₂ : t₁.val + p₂.val < k <;>
        simp [happ, hr, hs, h₁, h₂]
  have hzeros : ∀ n (s : Fin k), 0 < n → run s (List.replicate n false) = some z := by
    intro n
    induction n with
    | zero => intro s hn; omega
    | succ n ih =>
      intro s _
      rw [List.replicate_succ, hfalse]
      cases n with
      | zero => rfl
      | succ n => exact ih z (by omega)
  have hwindow (p t : Fin k) (hpt : p.val + t.val ≤ k) :
      (window p t).length = k + 1 ∧ leading (window p t) = p.val ∧
      trailing (window p t) = t.val ∧ run z (window p t) = some t ∧
      live (window p t) = endpoint p t := by
    have hp := p.isLt
    have ht := t.isLt
    have hc : 0 < k + 1 - p.val - t.val := by omega
    have hl : (window p t).length = k + 1 := by simp [window]; omega
    have hlead : leading (window p t) = p.val := by
      simp [leading, window, List.takeWhile_append, List.takeWhile_replicate,
        Nat.ne_of_gt hc, Ne.symm (Nat.ne_of_gt hc)]
    have htrail : trailing (window p t) = t.val := by
      simp [trailing, window, List.reverse_append, List.takeWhile_append,
        List.takeWhile_replicate, Nat.ne_of_gt hc, Ne.symm (Nat.ne_of_gt hc)]
    have hr (s : Fin k) : run s (window p t) =
        if s.val + p.val < k then some t else none := by
      dsimp only [window]
      rw [happ, happ, hones]
      split_ifs with hs
      · simp only [Option.bind_some]
        rw [hzeros _ _ hc]
        simp only [Option.bind_some]
        rw [hones]
        simpa [z, t.isLt]
      · rfl
    refine ⟨hl, hlead, htrail, ?_, ?_⟩
    · simpa [z, p.isLt] using hr z
    · funext i s
      by_cases hs : s.val + p.val < k <;> simp [live, endpoint, hr, hs, eq_comm]
  have hcontains (w : List Bool) (hl : k ≤ w.length) (hw : run z w ≠ none) : false ∈ w := by
    by_contra hz
    apply hw
    rw [hallones w hz, hones]
    simp [z, show ¬w.length < k by omega]
  have hdomain (p t : Fin k) :
      (∃ w : List Bool, w.length = k + 1 ∧ run z w ≠ none ∧
        leading w = p.val ∧ trailing w = t.val) ↔ p.val + t.val ≤ k := by
    constructor
    · rintro ⟨w, hl, hw, hp, ht⟩
      obtain ⟨a, b, ha, hb, hab, _, _⟩ := hnormal w (hcontains w (by omega) hw) hw
      omega
    · intro hpt
      obtain ⟨hl, hp, ht, hr, _⟩ := hwindow p t hpt
      exact ⟨window p t, hl, by rw [hr]; simp, hp, ht⟩
  have hnonzero (p t : Fin k) : endpoint p t ≠ 0 := by
    intro he
    have h := congrFun (congrFun he t) z
    simpa [endpoint, z, p.isLt] using h
  have hrank (p t : Fin k) : (endpoint p t).rank ≤ 1 := by
    have he : endpoint p t = Matrix.vecMulVec
        (fun i : Fin k => if i = t then (1 : K) else 0)
        (fun s : Fin k => if s.val + p.val < k then (1 : K) else 0) := by
      funext i s
      by_cases hi : i = t <;> by_cases hs : s.val + p.val < k <;>
        simp [endpoint, Matrix.vecMulVec, hi, hs]
    rw [he]
    exact Matrix.rank_vecMulVec_le _ _
  have hinj : Function.Injective (fun q : Fin k × Fin k => endpoint q.1 q.2) := by
    rintro ⟨p, t⟩ ⟨p', t'⟩ he
    have ht : t = t' := by
      by_contra ht
      have h := congrFun (congrFun he t) z
      simpa [endpoint, z, p.isLt, p'.isLt, ht] using h
    subst t'
    have hp : p = p' := by
      have hnotlt (a b : Fin k) (hab : endpoint a t = endpoint b t) : ¬a.val < b.val := by
        intro hlt
        let s : Fin k := ⟨k - b.val, by have := b.isLt; omega⟩
        have h₁ : s.val + a.val < k := by dsimp [s]; have := b.isLt; omega
        have h₂ : ¬s.val + b.val < k := by dsimp [s]; have := b.isLt; omega
        have h := congrFun (congrFun hab t) s
        simpa [endpoint, h₁, h₂] using h
      have h₁ := hnotlt p p' he
      have h₂ := hnotlt p' p he.symm
      apply Fin.ext
      omega
    exact Prod.ext hp rfl
  let reject := List.replicate (k + 1) true
  have hrejection : reject.length = k + 1 ∧ live reject = 0 := by
    refine ⟨by simp [reject], hzero reject ?_⟩
    simp [reject, hones, z]
  have hone (A : Matrix (Fin k) (Fin k) K) :
      (∃ w : List Bool, w.length = k + 1 ∧ live w = A) ↔ A ∈ one := by
    constructor
    · rintro ⟨w, hl, rfl⟩
      by_cases hw : run z w = none
      · simp [one, hzero w hw]
      · obtain ⟨p, t, hp, ht, hlen, _, he⟩ := hnormal w (hcontains w (by omega) hw) hw
        have hpt : p.val + t.val ≤ k := by omega
        rw [he]
        simp only [one, Finset.mem_insert, Finset.mem_image]
        exact Or.inr ⟨(p, t), by simp [domain, hpt], rfl⟩
    · intro hA
      rcases Finset.mem_insert.mp hA with he | he
      · exact ⟨reject, hrejection.1, hrejection.2.trans he.symm⟩
      · obtain ⟨⟨p, t⟩, hpt, rfl⟩ := Finset.mem_image.mp he
        have hs : p.val + t.val ≤ k := by simpa [domain] using hpt
        exact ⟨window p t, (hwindow p t hs).1, (hwindow p t hs).2.2.2.2⟩
  have htwo (p t : Fin k) :
      (window p z ++ window z t).length = 2 * (k + 1) ∧
        live (window p z ++ window z t) = endpoint p t := by
    obtain ⟨hl₁, hp₁, ht₁, hr₁, _⟩ := hwindow p z (by have := p.isLt; dsimp [z]; omega)
    obtain ⟨hl₂, hp₂, ht₂, hr₂, _⟩ := hwindow z t (by have := t.isLt; dsimp [z]; omega)
    refine ⟨by simp [hl₁, hl₂]; omega, ?_⟩
    have hc := hcompose (window p z) (window z t) p z z t
      (hcontains _ (by omega) (by rw [hr₁]; simp))
      (hcontains _ (by omega) (by rw [hr₂]; simp))
      (by rw [hr₁]; simp) (by rw [hr₂]; simp) hp₁ ht₁ hp₂ ht₂
    simpa [z, show 0 < k by omega] using hc.1
  have hpositive (A : Matrix (Fin k) (Fin k) K) :
      (∃ r : ℕ, 0 < r ∧ ∃ w : List Bool, w.length = r * (k + 1) ∧ live w = A) ↔
        A ∈ positive := by
    constructor
    · rintro ⟨r, hr, w, hl, rfl⟩
      have hn : k ≤ w.length := by rw [hl]; nlinarith
      by_cases hw : run z w = none
      · simp [positive, hzero w hw]
      · obtain ⟨p, t, _, _, _, _, he⟩ := hnormal w (hcontains w hn hw) hw
        rw [he]
        simp only [positive, Finset.mem_insert, Finset.mem_image]
        exact Or.inr ⟨(p, t), Finset.mem_univ _, rfl⟩
    · intro hA
      rcases Finset.mem_insert.mp hA with he | he
      · exact ⟨1, by omega, reject, by simpa using hrejection.1, hrejection.2.trans he.symm⟩
      · obtain ⟨⟨p, t⟩, _, rfl⟩ := Finset.mem_image.mp he
        exact ⟨2, by omega, window p z ++ window z t, (htwo p t).1, (htwo p t).2⟩
  have hidentity : live [] = 1 := by
    funext i s
    simp [live, hnil, Matrix.one_apply, eq_comm]
  have hmonoid (A : Matrix (Fin k) (Fin k) K) :
      (∃ r : ℕ, ∃ w : List Bool, w.length = r * (k + 1) ∧ live w = A) ↔ A ∈ monoid := by
    constructor
    · rintro ⟨r, w, hl, he⟩
      cases r with
      | zero =>
        have hw : w = [] := List.length_eq_zero_iff.mp (by simpa using hl)
        subst w
        simp [monoid, ← he, hidentity]
      | succ r => exact Finset.mem_insert_of_mem ((hpositive A).mp ⟨r + 1, by omega, w, hl, he⟩)
    · intro hA
      rcases Finset.mem_insert.mp hA with hA | hA
      · exact ⟨0, [], by simp, hidentity.trans hA.symm⟩
      · obtain ⟨r, _, w, hl, he⟩ := (hpositive A).mpr hA
        exact ⟨r, w, hl, he⟩
  have hclosed (A : Matrix (Fin k) (Fin k) K) (hA : A ∈ positive)
      (B : Matrix (Fin k) (Fin k) K) (hB : B ∈ positive) : B * A ∈ positive := by
    obtain ⟨r, hr, u, hu, rfl⟩ := (hpositive A).mpr hA
    obtain ⟨s, hs, v, hv, rfl⟩ := (hpositive B).mpr hB
    apply (hpositive _).mp
    refine ⟨r + s, by omega, u ++ v, ?_, hmul u v⟩
    simp [hu, hv, Nat.add_mul]
  have hmonoidclosed (A : Matrix (Fin k) (Fin k) K) (hA : A ∈ monoid)
      (B : Matrix (Fin k) (Fin k) K) (hB : B ∈ monoid) : B * A ∈ monoid := by
    obtain ⟨r, u, hu, rfl⟩ := (hmonoid A).mpr hA
    obtain ⟨s, v, hv, rfl⟩ := (hmonoid B).mpr hB
    apply (hmonoid _).mp
    refine ⟨r + s, u ++ v, ?_, hmul u v⟩
    simp [hu, hv, Nat.add_mul]
  have hlowrank (A : Matrix (Fin k) (Fin k) K) (hA : A ∈ positive) :
      A.rank ≤ 1 ∧ A ≠ 1 := by
    have hr : A.rank ≤ 1 := by
      rcases Finset.mem_insert.mp hA with rfl | hA
      · simp
      · obtain ⟨⟨p, t⟩, _, rfl⟩ := Finset.mem_image.mp hA
        exact hrank p t
    refine ⟨hr, ?_⟩
    intro he
    rw [he, Matrix.rank_one, Fintype.card_fin] at hr
    omega
  have hnonclosed (hk₃ : 3 ≤ k) :
      let top : Fin k := ⟨k - 1, by omega⟩
      live (window top z) ∈ one ∧ live (window z top) ∈ one ∧
        live (window top z ++ window z top) ∉ one := by
    let top : Fin k := ⟨k - 1, by omega⟩
    refine ⟨(hone _).mp ⟨_, (hwindow top z (by dsimp [top, z]; omega)).1, rfl⟩,
      (hone _).mp ⟨_, (hwindow z top (by dsimp [top, z]; omega)).1, rfl⟩, ?_⟩
    rw [(htwo top top).2]
    intro he
    rcases Finset.mem_insert.mp he with he | he
    · exact hnonzero top top he
    · obtain ⟨⟨p, t⟩, hpt, he⟩ := Finset.mem_image.mp he
      have h := @hinj (p, t) (top, top) he
      have hp : p = top := congrArg Prod.fst h
      have ht : t = top := congrArg Prod.snd h
      have hs : p.val + t.val ≤ k := by simpa [domain] using hpt
      simp only [hp, ht, top, Fin.val_mk] at hs
      omega
  have hthree (he : k = 3) :
      let top : Fin k := ⟨k - 1, by omega⟩
      window top z = [true, true, false, false] ∧
        window z top = [false, false, true, true] := by
    subst k
    simp [window, z, List.replicate_succ]
  have hcount : domain.card = (k ^ 2 + 3 * k - 2) / 2 := by
    have hfiber : domain.card = ∑ p : Fin k,
        ((Finset.univ : Finset (Fin k)).filter (fun t => p.val + t.val ≤ k)).card := by
      simp only [domain, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
    have hrow (p : Fin k) :
        ((Finset.univ : Finset (Fin k)).filter (fun t => p.val + t.val ≤ k)).card =
          min k (k + 1 - p.val) := by
      have he : ((Finset.univ : Finset (Fin k)).filter (fun t => p.val + t.val ≤ k)) =
          Finset.univ.filter (fun t : Fin k => t.val < k + 1 - p.val) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := p.isLt
        omega
      rw [he, Fin.card_filter_val_lt]
    rw [hfiber]
    simp_rw [hrow]
    have hsum : (∑ p : Fin k, min k (k + 1 - p.val)) + 1 =
        ∑ p : Fin k, (k + 1 - p.val) := by
      have he (p : Fin k) : min k (k + 1 - p.val) + (if p.val = 0 then 1 else 0) =
          k + 1 - p.val := by
        have := p.isLt
        split_ifs <;> omega
      have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin k))) rfl (fun p _ => he p)
      rw [Finset.sum_add_distrib] at h
      have hz : (∑ p : Fin k, if p.val = 0 then 1 else 0) = 1 := by
        rw [Finset.sum_eq_single z]
        · simp [z]
        · intro p _ hp
          have hne : p.val ≠ 0 := by intro he; apply hp; exact Fin.ext he
          simp [hne]
        · simp
      simpa [hz] using h
    have hreverse : (∑ p : Fin k, (k + 1 - p.val)) = ∑ i ∈ Finset.range k, (i + 2) := by
      rw [Fin.sum_univ_eq_sum_range]
      rw [← Finset.sum_range_reflect (fun i => k + 1 - i) k]
      apply Finset.sum_congr rfl
      intro i hi
      have := Finset.mem_range.mp hi
      omega
    have hgauss := Finset.sum_range_id_mul_two k
    have hsum' : (∑ p : Fin k, min k (k + 1 - p.val)) * 2 = k ^ 2 + 3 * k - 2 := by
      rw [hreverse, Finset.sum_add_distrib] at hsum
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
      have hpred : k - 1 + 1 = k := by omega
      have hsub : k ^ 2 + 3 * k - 2 + 2 = k ^ 2 + 3 * k := by
        have hh : 2 ≤ k ^ 2 + 3 * k := by nlinarith
        omega
      nlinarith
    rw [← hsum']
    simp
  have hnotzero : (0 : Matrix (Fin k) (Fin k) K) ∉
      Finset.univ.image (fun q : Fin k × Fin k => endpoint q.1 q.2) := by
    intro h
    obtain ⟨⟨p, t⟩, _, he⟩ := Finset.mem_image.mp h
    exact hnonzero p t he
  have honecount : one.card = (k ^ 2 + 3 * k - 2) / 2 + 1 := by
    have hn : (0 : Matrix (Fin k) (Fin k) K) ∉ domain.image (fun q => endpoint q.1 q.2) := by
      intro h
      obtain ⟨⟨p, t⟩, _, he⟩ := Finset.mem_image.mp h
      exact hnonzero p t he
    rw [Finset.card_insert_of_notMem hn, Finset.card_image_of_injective _ hinj, hcount]
  have hpositivecount : positive.card = k ^ 2 + 1 := by
    rw [Finset.card_insert_of_notMem hnotzero, Finset.card_image_of_injective _ hinj]
    simp [pow_two]
  have hmonoidcount : monoid.card = k ^ 2 + 2 := by
    have hn : (1 : Matrix (Fin k) (Fin k) K) ∉ positive := by
      intro h
      exact (hlowrank 1 h).2 rfl
    rw [Finset.card_insert_of_notMem hn, hpositivecount]
  have hliftinj : Function.Injective lift := by
    intro A B he
    funext i s
    exact congrFun (congrFun he (some i)) (some s)
  have hliftone : lift 1 = 1 := by
    funext i s
    cases i <;> cases s <;> simp [lift, Matrix.one_apply]
  have hliftmul (A B : Matrix (Fin k) (Fin k) K) : lift (B * A) = lift B * lift A := by
    funext i s
    rw [Matrix.mul_apply]
    cases i <;> cases s <;>
      simp [lift, Matrix.mul_apply, Fintype.sum_option, sub_mul, Finset.sum_sub_distrib,
        Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have htotal (w : List Bool) : total w = lift (live w) := by
    funext i s
    cases s with
    | none => cases i <;> simp [total, lift]
    | some s =>
      cases hr : run s w with
      | none => cases i <;> simp [total, lift, live, hr]
      | some t => cases i <;> simp [total, lift, live, hr, eq_comm]
  have htotalmul (u v : List Bool) : total (u ++ v) = total v * total u := by
    rw [htotal, hmul, hliftmul, ← htotal, ← htotal]
  have hliftzero : lift 0 = (fun i _ => if i = none then (1 : K) else 0) := by
    funext i s
    cases i <;> cases s <;> simp [lift]
  have hrejectionNZ : lift 0 ≠ 0 := by
    intro he
    have h := congrFun (congrFun he none) none
    simpa [lift] using h
  have htotalone (A : Matrix (Option (Fin k)) (Option (Fin k)) K) :
      (∃ w : List Bool, w.length = k + 1 ∧ total w = A) ↔ A ∈ one.image lift := by
    constructor
    · rintro ⟨w, hl, rfl⟩
      rw [htotal]
      exact Finset.mem_image.mpr ⟨live w, (hone _).mp ⟨w, hl, rfl⟩, rfl⟩
    · intro hA
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨w, hl, he⟩ := (hone B).mpr hB
      exact ⟨w, hl, by rw [htotal, he]⟩
  have htotalpositive (A : Matrix (Option (Fin k)) (Option (Fin k)) K) :
      (∃ r : ℕ, 0 < r ∧ ∃ w : List Bool, w.length = r * (k + 1) ∧ total w = A) ↔
        A ∈ positive.image lift := by
    constructor
    · rintro ⟨r, hr, w, hl, rfl⟩
      rw [htotal]
      exact Finset.mem_image.mpr ⟨live w, (hpositive _).mp ⟨r, hr, w, hl, rfl⟩, rfl⟩
    · intro hA
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨r, hr, w, hl, he⟩ := (hpositive B).mpr hB
      exact ⟨r, hr, w, hl, by rw [htotal, he]⟩
  have htotalmonoid (A : Matrix (Option (Fin k)) (Option (Fin k)) K) :
      (∃ r : ℕ, ∃ w : List Bool, w.length = r * (k + 1) ∧ total w = A) ↔
        A ∈ monoid.image lift := by
    constructor
    · rintro ⟨r, w, hl, rfl⟩
      rw [htotal]
      exact Finset.mem_image.mpr ⟨live w, (hmonoid _).mp ⟨r, w, hl, rfl⟩, rfl⟩
    · intro hA
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨r, w, hl, he⟩ := (hmonoid B).mpr hB
      exact ⟨r, w, hl, by rw [htotal, he]⟩
  have htotalclosed (A : Matrix (Option (Fin k)) (Option (Fin k)) K)
      (hA : A ∈ positive.image lift) (B : Matrix (Option (Fin k)) (Option (Fin k)) K)
      (hB : B ∈ positive.image lift) : B * A ∈ positive.image lift := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hB
    rw [← hliftmul]
    exact Finset.mem_image.mpr ⟨b * a, hclosed a ha b hb, rfl⟩
  have htotalmonoidclosed (A : Matrix (Option (Fin k)) (Option (Fin k)) K)
      (hA : A ∈ monoid.image lift) (B : Matrix (Option (Fin k)) (Option (Fin k)) K)
      (hB : B ∈ monoid.image lift) : B * A ∈ monoid.image lift := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hB
    rw [← hliftmul]
    exact Finset.mem_image.mpr ⟨b * a, hmonoidclosed a ha b hb, rfl⟩
  have happendZero (n : ℕ) (w : Fin n → Bool) (hw : DBonacciAdmissible k n w) :
      DBonacciAdmissible k (n + 1) (Fin.snoc w false) ∧
      (List.ofFn (Fin.snoc w false)).length = n + 1 ∧
      run z (List.ofFn (Fin.snoc w false)) = some z := by
    refine ⟨D5.S0.Tower.DBonacci.Substitution.admissible_snoc_false k n w hw, by simp, ?_⟩
    have he : List.ofFn (Fin.snoc w false) = List.ofFn w ++ [false] := by
      rw [List.ofFn_succ_last]
      simp
    rw [he, happ]
    cases hr : run z (List.ofFn w) with
    | none => exact False.elim ((hlegalScan n w).mp hw hr)
    | some t => simp [hfalse, hnil]
  have htotalnonclosed (hk₃ : 3 ≤ k) :
      let top : Fin k := ⟨k - 1, by omega⟩
      total (window top z) ∈ one.image lift ∧ total (window z top) ∈ one.image lift ∧
        total (window top z ++ window z top) ∉ one.image lift := by
    let top : Fin k := ⟨k - 1, by omega⟩
    obtain ⟨h₁, h₂, h₃⟩ := hnonclosed hk₃
    simp only [htotal]
    refine ⟨Finset.mem_image.mpr ⟨_, h₁, rfl⟩, Finset.mem_image.mpr ⟨_, h₂, rfl⟩, ?_⟩
    intro he
    obtain ⟨A, hA, he⟩ := Finset.mem_image.mp he
    have h := hliftinj he
    rw [h] at hA
    exact h₃ hA
  exact ⟨hscan, hlegalScan, fun n w => ⟨by simp, by intro i; simp⟩,
    fun w => ⟨by simp, List.ofFn_get w⟩, hnormal, hbad, hcontains, hmul, hendpointmul,
    hcompose, hwindow, hdomain, htwo,
    by
      change run z (List.replicate (k + 1) true) = none
      rw [hones]
      simp [z],
    hrejection.2,
    fun p t => ⟨hnonzero p t, hrank p t⟩, hinj,
    hone, hpositive, hmonoid, hclosed, hmonoidclosed, hlowrank, hnonclosed, hthree,
    hcount, by rw [Finset.card_image_of_injective _ hinj, hcount],
    honecount, hpositivecount, hmonoidcount, hliftinj, hliftone, hliftmul,
    htotal, by intro w; simp [total], htotalmul, hliftzero, hrejectionNZ,
    htotalone, htotalpositive, htotalmonoid,
    by rw [Finset.card_image_of_injective _ hliftinj, honecount],
    by rw [Finset.card_image_of_injective _ hliftinj, hpositivecount],
    by rw [Finset.card_image_of_injective _ hliftinj, hmonoidcount],
    htotalclosed, htotalmonoidclosed, happendZero, htotalnonclosed⟩

#print axioms actual_endpoint_operators

end D5.S1.Words.AdmissibleWords.KBonacciActualEndpointOperators
