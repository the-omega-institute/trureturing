/- GID: D5/S3/ConceptDynamics/Experiment/SelfCalibratingRulings
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiment/SelfCalibratingRulings
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive eigenvector rulings obstruct any third linear relation read. -/

import D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords
import D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix Topology
open Filter

namespace D5.S3.ConceptDynamics.Experiment.SelfCalibratingRulings

/-- Strictly positive real relation matrices of rank one. -/
abbrev Source := {R : Matrix (Fin 2) (Fin 2) ℝ //
  (∀ i j, 0 < R i j) ∧ R 0 0 * R 1 1 = R 0 1 * R 1 0}

/-- A selected query retains the paid previous word and the new segment. -/
abbrev Query := List Bool × List Bool

/-- Terminal labels retain the reconstructed initial relation and the unread tail. -/
abbrev Label := Matrix (Fin 2) (Fin 2) ℝ × List Bool

/-- Native histories retain exact real responses and literal selected queries. -/
abbrev History := PassivePolicyNormalization.Hist (fun _ : Query => ℝ)

/-- The real matrix of a chronological literal word. -/
def matrix (w : List Bool) : Matrix (Fin 2) (Fin 2) ℝ :=
  (Arith.FibonacciAtomic.SelfCalibratingRawWords.word w).map (fun z : ℤ => (z : ℝ))

/-- An exact linear relation read. -/
def observe (A : Matrix (Fin 2) (Fin 2) ℝ) (R : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Matrix.trace (A * R)

/-- A query reads its actual cumulative word on the fixed initial relation. -/
def read (q : Query) (R : Source) : ℝ := observe (matrix (q.1 ++ q.2)) R.val

/-- Every selected query extends the actual preceding literal word. -/
def Chronological : List Bool → History → Prop
  | _, [] => True
  | before, a :: h => a.1.1 = before ∧ Chronological (a.1.1 ++ a.1.2) h

/-- Literal action charges include the unread terminal segment. -/
def actualCost (h : History) (out : Label) : ℕ :=
  (h.map (fun a => a.1.2.length)).sum + out.2.length

/-- Unrestricted history selectors recover every positive source in at most three reads. -/
def OriginalValid (P : History → Sum Query Label) : Prop :=
  P [] = .inl ([], []) ∧ ∀ R : Source, ∃ fuel h out,
    PassivePolicyNormalization.execute read P fuel [] R = some (h, out) ∧
      Chronological [] h ∧ h.length ≤ 3 ∧ out.1 = R.val

/-- Two independent positive rank-one rulings keep the eigenvector reads fixed and
produce a collision for every selected third linear read. -/
theorem positive_ruling_collision
    (A B : Matrix (Fin 2) (Fin 2) ℝ) (c l : Fin 2 → ℝ) (lam : ℝ)
    (hc : ∀ i, 0 < c i) (hl : ∀ i, 0 < l i)
    (hAc : A *ᵥ c = lam • c) (hlA : l ᵥ* A = lam • l) :
    ∃ R₀ R₁ : Source, R₀ ≠ R₁ ∧
      Matrix.trace R₀.val = c 0 * l 0 + c 1 * l 1 ∧
      Matrix.trace R₁.val = c 0 * l 0 + c 1 * l 1 ∧
      observe A R₀.val = lam * (c 0 * l 0 + c 1 * l 1) ∧
      observe A R₁.val = lam * (c 0 * l 0 + c 1 * l 1) ∧
      observe B R₀.val = observe B R₁.val := by
  let w : Fin 2 → ℝ := ![c 1, -c 0]
  let z : Fin 2 → ℝ := ![l 1, -l 0]
  let X := Matrix.vecMulVec c w
  let Z := Matrix.vecMulVec z l
  let a := observe B X
  let b := observe B Z
  have weights : ∃ v u : ℝ, a * v = b * u ∧ (v ≠ 0 ∨ u ≠ 0) := by
    by_cases ha : a = 0
    · exact ⟨1, 0, by simp [ha], Or.inl one_ne_zero⟩
    · by_cases hb : b = 0
      · exact ⟨0, 1, by simp [hb], Or.inr one_ne_zero⟩
      · exact ⟨b, a, mul_comm _ _, Or.inl hb⟩
  obtain ⟨v, u, hweights, hne⟩ := weights
  have positive : ∀ᶠ t : ℝ in 𝓝 0,
      (∀ i, 0 < l i + v * t * w i) ∧ (∀ i, 0 < c i + u * t * z i) := by
    have hl' : ∀ i, ∀ᶠ t : ℝ in 𝓝 0, 0 < l i + v * t * w i := by
      intro i
      have ht : ContinuousAt (fun t : ℝ => l i + v * t * w i) 0 := by fun_prop
      exact ht.eventually (lt_mem_nhds (by simpa using hl i))
    have hc' : ∀ i, ∀ᶠ t : ℝ in 𝓝 0, 0 < c i + u * t * z i := by
      intro i
      have ht : ContinuousAt (fun t : ℝ => c i + u * t * z i) 0 := by fun_prop
      exact ht.eventually (lt_mem_nhds (by simpa using hc i))
    exact (Filter.eventually_all.mpr hl').and (Filter.eventually_all.mpr hc')
  obtain ⟨eps, heps, hsmall⟩ := Metric.eventually_nhds_iff.mp positive
  let t := eps / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have ht' : dist t 0 < eps := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    dsimp [t]
    linarith
  obtain ⟨hl', hc'⟩ := hsmall ht'
  let R₀ : Source := ⟨Matrix.vecMulVec c (fun i => l i + v * t * w i),
    (by constructor
        · intro i j; exact mul_pos (hc i) (hl' j)
        · simp only [Matrix.vecMulVec_apply]; ring)⟩
  let R₁ : Source := ⟨Matrix.vecMulVec (fun i => c i + u * t * z i) l,
    (by constructor
        · intro i j; exact mul_pos (hc' i) (hl j)
        · simp only [Matrix.vecMulVec_apply]; ring)⟩
  have different : R₀ ≠ R₁ := by
    intro he
    have e₀ := congrArg (fun R : Source => R.val 0 0) he
    have e₁ := congrArg (fun R : Source => R.val 0 1) he
    change c 0 * (l 0 + v * t * c 1) = (c 0 + u * t * l 1) * l 0 at e₀
    change c 0 * (l 1 + v * t * -c 0) = (c 0 + u * t * l 1) * l 1 at e₁
    have hzero : u * t * l 1 * (c 0 * l 0 + c 1 * l 1) = 0 := by
      linear_combination -(c 0 * e₀ + c 1 * e₁)
    have hx : 0 < c 0 * l 0 + c 1 * l 1 := add_pos (mul_pos (hc 0) (hl 0)) (mul_pos (hc 1) (hl 1))
    have hu : u = 0 := by
      rcases (mul_eq_zero.mp hzero) with h | h
      · rcases (mul_eq_zero.mp h) with h | h
        · exact (mul_eq_zero.mp h).resolve_right (ne_of_gt ht)
        · exact False.elim ((ne_of_gt (hl 1)) h)
      · exact False.elim ((ne_of_gt hx) h)
    have hv : v = 0 := by
      rw [hu] at e₀
      have hv' : v * t * c 0 * c 1 = 0 := by nlinarith [e₀]
      have hprod : 0 < t * c 0 * c 1 := mul_pos (mul_pos ht (hc 0)) (hc 1)
      have : v * (t * c 0 * c 1) = 0 := by nlinarith [hv']
      exact (mul_eq_zero.mp this).resolve_right (ne_of_gt hprod)
    exact hne.elim (fun h => h hv) (fun h => h hu)
  have Ac₀ := congrFun hAc 0
  have Ac₁ := congrFun hAc 1
  have lA₀ := congrFun hlA 0
  have lA₁ := congrFun hlA 1
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    Pi.smul_apply, smul_eq_mul] at Ac₀ Ac₁ lA₀ lA₁
  refine ⟨R₀, R₁, different, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [R₀, w]; simp [Matrix.trace, Matrix.vecMulVec_apply, Fin.sum_univ_two]; ring
  · dsimp [R₁, z]; simp [Matrix.trace, Matrix.vecMulVec_apply, Fin.sum_univ_two]; ring
  · dsimp [observe, R₀, w]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.head_fin_const]
    linear_combination (l 0 + v * t * c 1) * Ac₀ + (l 1 - v * t * c 0) * Ac₁
  · dsimp [observe, R₁, z]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.head_fin_const]
    linear_combination (c 0 + u * t * l 1) * lA₀ + (c 1 - u * t * l 0) * lA₁
  · dsimp [a, b, X, Z, observe, w, z] at hweights
    dsimp [observe, R₀, R₁, w, z]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.head_fin_const, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] at hweights ⊢
    linear_combination t * hweights

/-- Every actual second cumulative matrix selected by a globally correct
three-read history policy is a nontrivial integral shear. -/
theorem second_query_shear
    (P : History → Sum Query Label) (hp : OriginalValid P) (x : ℝ) (hx : 0 < x)
    : (∃ (paidWord : List Bool) (k : ℕ),
    P [⟨([], []), x⟩] = .inl ([], paidWord) ∧ 0 < k ∧
      (matrix paidWord = !![1, (k : ℝ); 0, 1] ∨
       matrix paidWord = !![1, 0; (k : ℝ), 1])) ∧
      (∀ R : Source, ∃ c l : Fin 2 → ℝ,
        (∀ i, 0 < c i) ∧ (∀ i, 0 < l i) ∧ R.val = Matrix.vecMulVec c l ∧
        ∀ w : List Bool, observe (matrix w) R.val = l ⬝ᵥ (matrix w *ᵥ c)) := by
  constructor
  ·
    have eigen_obstruction (paidWord : List Bool) (c l : Fin 2 → ℝ) (lam : ℝ)
        (hc : ∀ i, 0 < c i) (hl : ∀ i, 0 < l i)
        (hAc : matrix paidWord *ᵥ c = lam • c)
        (hlA : l ᵥ* matrix paidWord = lam • l)
        (hq : P [⟨([], []), c 0 * l 0 + c 1 * l 1⟩] = .inl ([], paidWord)) : False := by
      let x := c 0 * l 0 + c 1 * l 1
      let y := lam * x
      let h₂ : History := [⟨([], []), x⟩, ⟨([], paidWord), y⟩]
      have truncate : ∀ n : ℕ, ∀ (h : History) (R : Source) (tr : History) (out : Label)
          (m : ℕ), PassivePolicyNormalization.execute read P n h R = some (tr, out) →
          tr.length < m → PassivePolicyNormalization.execute read P m h R = some (tr, out) := by
        intro n
        induction n with
        | zero => intro h R tr out m hr; simp [PassivePolicyNormalization.execute] at hr
        | succ n ih =>
          intro h R tr out m hr hm
          cases m with
          | zero => omega
          | succ m =>
            cases hP : P h with
            | inr out' =>
              simp only [PassivePolicyNormalization.execute, hP, Option.some.injEq,
                Prod.mk.injEq] at hr
              obtain ⟨rfl, rfl⟩ := hr
              simp [PassivePolicyNormalization.execute, hP]
            | inl q =>
              simp only [PassivePolicyNormalization.execute, hP, Option.map_eq_some_iff] at hr
              obtain ⟨⟨s, out'⟩, hs, he⟩ := hr
              cases he
              simp only [List.length_cons, Nat.succ_lt_succ_iff] at hm
              simp only [PassivePolicyNormalization.execute, hP]
              rw [ih _ _ _ _ _ hs hm]
              rfl
      have run₄ (R : Source) : ∃ tr out,
          PassivePolicyNormalization.execute read P 4 [] R = some (tr, out) ∧ out.1 = R.val := by
        obtain ⟨n, tr, out, hr, _, hn, he⟩ := hp.2 R
        exact ⟨tr, out, truncate _ _ _ _ _ _ hr (by omega), he⟩
      have correct (R : Source) (tr : History) (out : Label)
          (hr : PassivePolicyNormalization.execute read P 4 [] R = some (tr, out)) :
          out.1 = R.val := by
        obtain ⟨s, out', hs, he⟩ := run₄ R
        rw [hr] at hs
        have hout : out = out' := (Prod.mk.inj (Option.some.inj hs)).2
        exact hout ▸ he
      have empty : matrix [] = 1 := by
        ext i j; fin_cases i <;> fin_cases j <;>
          norm_num [matrix, Arith.FibonacciAtomic.SelfCalibratingRawWords.word]
      have first (R : Source) : read ([], []) R = Matrix.trace R.val := by
        simp [read, observe, empty]
      have second (R : Source) : read ([], paidWord) R = observe (matrix paidWord) R.val := by
        simp [read]
      cases hP₂ : P h₂ with
      | inr out =>
        dsimp only [h₂, x, y] at hP₂
        obtain ⟨R₀, R₁, hne, hx₀, hx₁, hy₀, hy₁, _⟩ :=
          positive_ruling_collision (matrix paidWord) 1 c l lam hc hl hAc hlA
        have runs (R : Source) (hx : Matrix.trace R.val = x)
            (hy : observe (matrix paidWord) R.val = y) :
            PassivePolicyNormalization.execute read P 4 [] R = some (h₂, out) := by
          simp [PassivePolicyNormalization.execute, hp.1, first, second, hx, hy, hq, hP₂, h₂, x, y]
        have h₀ := correct R₀ h₂ out (runs R₀ hx₀ hy₀)
        have h₁ := correct R₁ h₂ out (runs R₁ hx₁ hy₁)
        exact hne (Subtype.ext (h₀.symm.trans h₁))
      | inl q =>
        dsimp only [h₂, x, y] at hP₂
        obtain ⟨R₀, R₁, hne, hx₀, hx₁, hy₀, hy₁, ht⟩ :=
          positive_ruling_collision (matrix paidWord) (matrix (q.1 ++ q.2)) c l lam
            hc hl hAc hlA
        let h₃ := h₂ ++ [⟨q, read q R₀⟩]
        have hread : read q R₀ = read q R₁ := ht
        obtain ⟨tr, out, hr, he⟩ := run₄ R₀
        cases hP₃ : P h₃ with
        | inl q' =>
          dsimp only [h₃, h₂, x, y] at hP₃
          simp only [List.cons_append, List.nil_append] at hP₃
          simp [PassivePolicyNormalization.execute, hp.1, first, second, hx₀, hy₀,
            hq, hP₂, hP₃, h₂, h₃, x, y] at hr
        | inr label =>
          dsimp only [h₃, h₂, x, y] at hP₃
          simp only [List.cons_append, List.nil_append] at hP₃
          have runs (R : Source) (hx : Matrix.trace R.val = x)
              (hy : observe (matrix paidWord) R.val = y) (ht' : read q R = read q R₀) :
              PassivePolicyNormalization.execute read P 4 [] R = some (h₃, label) := by
            simp [PassivePolicyNormalization.execute, hp.1, first, second, hx, hy,
              ht', hq, hP₂, hP₃, h₂, h₃, x, y]
          have h₀ := correct R₀ h₃ label (runs R₀ hx₀ hy₀ rfl)
          have h₁ := correct R₁ h₃ label (runs R₁ hx₁ hy₁ hread.symm)
          exact hne (Subtype.ext (h₀.symm.trans h₁))
    have empty : matrix [] = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [matrix, Arith.FibonacciAtomic.SelfCalibratingRawWords.word]
    have first (R : Source) : read ([], []) R = Matrix.trace R.val := by
      simp [read, observe, empty]
    let c : Fin 2 → ℝ := ![1, 1]
    let l : Fin 2 → ℝ := ![x/2, x/2]
    have hc : ∀ i, 0 < c i := by intro i; fin_cases i <;> norm_num [c]
    have hl : ∀ i, 0 < l i := by
      intro i; fin_cases i <;> simpa [l] using half_pos hx
    have hs : c 0*l 0+c 1*l 1 = x := by simp [c,l]
    obtain ⟨R₀, R₁, hne, hx₀, hx₁, _, _, _⟩ :=
      positive_ruling_collision 1 1 c l 1 hc hl (by simp) (by simp)
    rw [hs] at hx₀ hx₁
    have selected : ∃ paidWord, P [⟨([], []), x⟩] = .inl ([], paidWord) := by
      cases hsel : P [⟨([], []), x⟩] with
      | inr out =>
        have stopped (R : Source) (hRx : Matrix.trace R.val = x) : out.1 = R.val := by
          obtain ⟨n, tr, out', hr, _, _, he⟩ := hp.2 R
          cases n with
          | zero => simp [PassivePolicyNormalization.execute] at hr
          | succ n =>
            cases n with
            | zero => simp [PassivePolicyNormalization.execute, hp.1] at hr
            | succ n =>
              simp [PassivePolicyNormalization.execute, hp.1, first, hRx, hsel] at hr
              rw [← hr.2] at he
              exact he
        exact False.elim (hne (Subtype.ext ((stopped R₀ hx₀).symm.trans (stopped R₁ hx₁))))
      | inl q =>
        have before : q.1 = [] := by
          obtain ⟨n, tr, out, hr, hchron, _, _⟩ := hp.2 R₀
          cases n with
          | zero => simp [PassivePolicyNormalization.execute] at hr
          | succ n =>
            cases n with
            | zero => simp [PassivePolicyNormalization.execute, hp.1] at hr
            | succ n =>
              simp only [PassivePolicyNormalization.execute, hp.1, first, hx₀,
                List.nil_append, hsel] at hr
              obtain ⟨⟨tail, label⟩, htail, he⟩ := Option.map_eq_some_iff.mp hr
              cases he
              obtain ⟨⟨tail', label'⟩, _, he'⟩ := Option.map_eq_some_iff.mp htail
              cases he'
              exact hchron.2.1
        refine ⟨q.2, ?_⟩
        exact congrArg Sum.inl (Prod.ext before rfl)
    obtain ⟨paidWord, hq⟩ := selected
    have zero : matrix paidWord 0 1 = 0 ∨ matrix paidWord 1 0 = 0 := by
      by_contra h
      push Not at h
      have hn : ∀ i j, 0 ≤ matrix paidWord i j := by
        intro i j
        change 0 ≤ (Arith.FibonacciAtomic.SelfCalibratingRawWords.word paidWord i j : ℝ)
        exact_mod_cast (Arith.FibonacciAtomic.SelfCalibratingRawWords.raw_word_signed_bound
          paidWord).2.1 i j
      let A := matrix paidWord
      let alpha := A 0 0
      let beta := A 0 1
      let gamma := A 1 0
      let eta := A 1 1
      have hb : 0 < beta := lt_of_le_of_ne (hn 0 1) h.1.symm
      have hg : 0 < gamma := lt_of_le_of_ne (hn 1 0) h.2.symm
      let disc := (alpha - eta) ^ 2 + 4 * beta * gamma
      let root := Real.sqrt disc
      let lam := (alpha + eta + root) / 2
      have hd : 0 ≤ disc := by dsimp [disc]; positivity
      have hrsq : root ^ 2 = disc := Real.sq_sqrt hd
      have hrg : alpha - eta < root := Real.lt_sqrt_of_sq_lt (by
        dsimp [disc]; nlinarith [mul_pos hb hg])
      have hrl : eta - alpha < root := Real.lt_sqrt_of_sq_lt (by
        dsimp [disc]; nlinarith [mul_pos hb hg])
      have hla : alpha < lam := by dsimp [lam]; linarith
      have hle : eta < lam := by dsimp [lam]; linarith
      have hchar : (lam - alpha) * (lam - eta) = beta * gamma := by
        dsimp [lam, disc] at *
        nlinarith [hrsq]
      let c : Fin 2 → ℝ := ![beta, lam - alpha]
      let S := beta * gamma + (lam - alpha) ^ 2
      let scale := x / S
      let l : Fin 2 → ℝ := ![scale * gamma, scale * (lam - alpha)]
      have hS : 0 < S := by dsimp [S]; nlinarith [mul_pos hb hg, sq_nonneg (lam - alpha)]
      have hs : 0 < scale := div_pos hx hS
      have hc : ∀ i, 0 < c i := by intro i; fin_cases i <;> simp [c] <;> linarith
      have hl : ∀ i, 0 < l i := by
        intro i; fin_cases i <;> simp [l]
        · exact mul_pos hs hg
        · exact mul_pos hs (sub_pos.mpr hla)
      have hAc : A *ᵥ c = lam • c := by
        ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, c]
        · change alpha * beta + beta * (lam - alpha) = lam * beta; ring
        · change gamma * beta + eta * (lam - alpha) = lam * (lam - alpha)
          nlinarith [hchar]
      have hlA : l ᵥ* A = lam • l := by
        ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, l]
        · change scale * gamma * alpha + scale * (lam - alpha) * gamma =
            lam * (scale * gamma); ring
        · change scale * gamma * beta + scale * (lam - alpha) * eta =
            lam * (scale * (lam - alpha))
          linear_combination -scale * hchar
      have htrace : c 0 * l 0 + c 1 * l 1 = x := by
        dsimp [c, l, scale, S]
        field_simp [ne_of_gt hS]
      exact eigen_obstruction paidWord c l lam hc hl hAc hlA
        (by rw [htrace]; exact hq)
  
    have packet := Arith.FibonacciAtomic.SelfCalibratingRawWords.raw_word_signed_bound paidWord
    let W := Arith.FibonacciAtomic.SelfCalibratingRawWords.word paidWord
    have hn : ∀ i j, 0 ≤ W i j := packet.2.1
    have hz : W 0 1 = 0 ∨ W 1 0 = 0 := by
      change (W 0 1 : ℝ) = 0 ∨ (W 1 0 : ℝ) = 0 at zero
      exact_mod_cast zero
    have hdet : W 0 0 * W 1 1 - W 0 1 * W 1 0 = (-1 : ℤ) ^ paidWord.length := by
      simpa only [Matrix.det_fin_two] using packet.2.2.1
    have hsgn : (-1 : ℤ) ^ paidWord.length = 1 ∨
        (-1 : ℤ) ^ paidWord.length = -1 := by
      rcases Nat.even_or_odd paidWord.length with he | ho
      · left; exact he.neg_one_pow
      · right; exact ho.neg_one_pow
    have hprod : W 0 0 * W 1 1 = 1 := by
      rcases hz with hz | hz <;> simp only [hz, zero_mul, mul_zero, sub_zero] at hdet
      all_goals rcases hsgn with hs | hs
      all_goals rw [hs] at hdet
      all_goals first | exact hdet | nlinarith [mul_nonneg (hn 0 0) (hn 1 1)]
    have hd₀ : W 0 0 = 1 := by
      have hp₀ : 0 < W 0 0 := by nlinarith [hn 1 1]
      have hp₁ : 0 < W 1 1 := by nlinarith [hn 0 0]
      nlinarith
    have hd₁ : W 1 1 = 1 := by rw [hd₀, one_mul] at hprod; exact hprod
    have nonidentity : matrix paidWord ≠ 1 := by
      intro hi
      let c : Fin 2 → ℝ := ![1, 1]
      let l : Fin 2 → ℝ := ![x / 2, x / 2]
      have hc : ∀ i, 0 < c i := by intro i; fin_cases i <;> norm_num [c]
      have hl : ∀ i, 0 < l i := by
        intro i; fin_cases i <;> simpa [l] using half_pos hx
      apply eigen_obstruction paidWord c l 1 hc hl
      · simp [hi]
      · simp [hi]
      · convert hq using 1 <;> simp [c, l] <;> ring
    have ident (hb : W 0 1 = 0) (hc : W 1 0 = 0) : matrix paidWord = 1 := by
      have hw : W = 1 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [hd₀, hd₁, hb, hc]
      change W.map (fun z : ℤ => (z : ℝ)) = 1
      rw [hw]
      ext i j; fin_cases i <;> fin_cases j <;> norm_num
    rcases hz with hb | hc
    · have hp : 0 < W 1 0 := lt_of_le_of_ne (hn 1 0) (by
        intro he; exact nonidentity (ident hb he.symm))
      refine ⟨paidWord, (W 1 0).toNat, hq, by omega, Or.inr ?_⟩
      have hk : (((W 1 0).toNat : ℕ) : ℤ) = W 1 0 := Int.toNat_of_nonneg (hn 1 0)
      have hw : W = !![1, 0; ((W 1 0).toNat : ℤ), 1] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [hd₀, hd₁, hb, hk]
      change W.map (fun z : ℤ => (z : ℝ)) = _
      conv_lhs => rw [hw]
      ext i j; fin_cases i <;> fin_cases j
      · change ((1 : ℤ) : ℝ) = 1; norm_num
      · change ((0 : ℤ) : ℝ) = 0; norm_num
      · change (((W 1 0).toNat : ℤ) : ℝ) = ((W 1 0).toNat : ℝ)
        exact Int.cast_natCast _
      · change ((1 : ℤ) : ℝ) = 1; norm_num
    · have hp : 0 < W 0 1 := lt_of_le_of_ne (hn 0 1) (by
        intro he; exact nonidentity (ident he.symm hc))
      refine ⟨paidWord, (W 0 1).toNat, hq, by omega, Or.inl ?_⟩
      have hk : (((W 0 1).toNat : ℕ) : ℤ) = W 0 1 := Int.toNat_of_nonneg (hn 0 1)
      have hw : W = !![1, ((W 0 1).toNat : ℤ); 0, 1] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [hd₀, hd₁, hc, hk]
      change W.map (fun z : ℤ => (z : ℝ)) = _
      conv_lhs => rw [hw]
      ext i j; fin_cases i <;> fin_cases j
      · change ((1 : ℤ) : ℝ) = 1; norm_num
      · change (((W 0 1).toNat : ℤ) : ℝ) = ((W 0 1).toNat : ℝ)
        exact Int.cast_natCast _
      · change ((0 : ℤ) : ℝ) = 0; norm_num
      · change ((1 : ℤ) : ℝ) = 1; norm_num
  · intro R
    let c : Fin 2 → ℝ := ![R.val 0 0,R.val 1 0]
    let l : Fin 2 → ℝ := ![1,R.val 0 1/R.val 0 0]
    have hp : 0 < R.val 0 0 := R.property.1 0 0
    have hc : ∀ i, 0 < c i := by
      intro i; fin_cases i
      · exact R.property.1 0 0
      · exact R.property.1 1 0
    have hl : ∀ i, 0 < l i := by
      intro i; fin_cases i
      · norm_num [l]
      · exact div_pos (R.property.1 0 1) hp
    have factor : R.val = Matrix.vecMulVec c l := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [c,l,Matrix.vecMulVec_apply]
      · field_simp [ne_of_gt hp]
      · field_simp [ne_of_gt hp]
        nlinarith [R.property.2]
    refine ⟨c,l,hc,hl,factor,?_⟩
    intro w
    rw [factor]
    simp only [observe,Matrix.mul_vecMulVec,Matrix.trace_vecMulVec,dotProduct_comm]

#print axioms positive_ruling_collision
#print axioms second_query_shear

end D5.S3.ConceptDynamics.Experiment.SelfCalibratingRulings
